import TetraStereo.Engine.RingGroupedReport

open TetraStereo.OneCenter TetraStereo.Engine

-- Decode only the explicit atom and single-bond rows of the controlled V2000 fixture.
private def fields (line : String) := (line.splitOn " ").filter (· != "")

private def coordinate (text : String) : Except String ℚ := do
  let n ← (← Lean.Json.parse text).getNum?
  return (n.mantissa : ℚ) / 10 ^ n.exponent

private def atomRow (line : String) : Except String (AtomSpec × CartesianPoint3) := do
  let x :: y :: z :: symbol :: _ := fields line | throw "malformed cage atom"
  let element ← match symbol with
    | "H" => pure Element.H
    | "C" => pure Element.C
    | _ => throw "unexpected cage element"
  return (AtomSpec.aliphatic element, ⟨← coordinate x, ← coordinate y, ← coordinate z⟩)

private def bondRow (line : String) : Except String RawBond := do
  let a :: b :: "1" :: _ := fields line | throw "expected a single bond"
  let some i := a.toNat? | throw "malformed bond endpoint"
  let some j := b.toNat? | throw "malformed bond endpoint"
  unless 0 < i && 0 < j && i ≤ 22 && j ≤ 22 do throw "bond endpoint out of range"
  return ⟨i-1,j-1,.single⟩

private def fixture : Except String (RawMolecule × List CartesianPoint3) := do
  let lines := (include_str "Figure14AllOut.mol").splitOn "\n"
  unless (fields lines[3]!).take 2 == ["22","23"] && lines[49]! == "M  END" do
    throw "unexpected Figure 14 model size"
  let atoms ← ((lines.drop 4).take 22).mapM atomRow
  let bonds ← ((lines.drop 26).take 23).mapM bondRow
  return (⟨atoms.map Prod.fst,bonds,[],[]⟩,atoms.map Prod.snd)

private def check (m : RawMolecule) (positions : List CartesianPoint3)
    (topIn bottomIn : Bool) : IO Unit := do
  let xyz := if topIn then positions.modify 8 (fun p => {p with z := 27/100}) else positions
  let xyz := if bottomIn then xyz.modify 9 (fun p => {p with z := -27/100}) else xyz
  let some i := LocalizedChemicalRing.admitRawSpatial? m ⟨xyz⟩ | throw (IO.userError "structural admission")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "coordinate admission")
  let heads := (RingGroupedReport.centres i).filter (fun a => a.val < 2)
  unless heads.map Fin.val == [0,1] do throw (IO.userError "missing bridgehead")
  let rows := RingGroupedReport.forAtoms? i heads
  unless rows == some [(0,none),(1,none)] do throw (IO.userError s!"unexpected frozen result {repr rows}")
  IO.println s!"grouped frozen, topIn={topIn}, bottomIn={bottomIn}, two completed bridgehead refusals"
  (← IO.getStdout).flush

def main : IO Unit := do
  let (m,positions) ← IO.ofExcept fixture
  for topIn in [false, true] do
    for bottomIn in [false, true] do
      check m positions topIn bottomIn
