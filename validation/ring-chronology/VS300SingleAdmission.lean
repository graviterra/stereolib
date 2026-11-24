import TetraStereo.Engine.RingBondRecordOrder

open TetraStereo.OneCenter TetraStereo.Engine

-- Exact coordinate input for the neutral, single-bond VS300 derivative.
private def fields (line : String) := (line.splitOn " ").filter (· != "")

private def coord (text : String) : Except String ℚ := do
  let n ← (← Lean.Json.parse text).getNum?
  return (n.mantissa : ℚ) / 10 ^ n.exponent

private def atom (line : String) : Except String (AtomSpec × CartesianPoint3) := do
  let x :: y :: z :: symbol :: "0" :: "0" :: _ := fields line | throw "expected a neutral unlabeled atom"
  let e ← match symbol with
    | "C" => pure Element.C
    | "N" => pure Element.N
    | "O" => pure Element.O
    | "H" => pure Element.H
    | _ => throw "unexpected element"
  return (AtomSpec.aliphatic e, ⟨← coord x, ← coord y, ← coord z⟩)

private def bond (line : String) : Except String RawBond := do
  let a :: b :: "1" :: _ := fields line | throw "expected single bond"
  let some i := a.toNat? | throw "invalid bond endpoint"
  let some j := b.toNat? | throw "invalid bond endpoint"
  unless 0 < i && i ≤ 66 && 0 < j && j ≤ 66 do throw "out-of-range bond endpoint"
  return ⟨i-1,j-1,.single⟩

private def parse (text : String) : Except String (RawMolecule × List CartesianPoint3) := do
  let lines := text.splitOn "\n"
  unless (fields lines[3]!).take 2 == ["66","71"] && lines[141]! == "M  END" do
    throw "unexpected model size"
  let atoms ← ((lines.drop 4).take 66).mapM atom
  let bonds ← ((lines.drop 70).take 71).mapM bond
  return (⟨atoms.map Prod.fst, bonds, [], []⟩, atoms.map Prod.snd)

private def admit (file : String) : IO LocalizedChemicalRing.Input := do
  let (m, xyz) ← IO.ofExcept (parse (← IO.FS.readFile file))
  let some i := LocalizedChemicalRing.admitRawSpatial? m ⟨xyz⟩ | throw (IO.userError "structural admission")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "coordinate admission")
  let centres := i.certified.canonicalTetrahedralCenters.map (fun c => c.val.val)
  unless [9,38,60].all centres.contains do throw (IO.userError "target centre missing")
  return i

private def certificate (i j : LocalizedChemicalRing.Input) :
    Option (PLift (RingGroupedReport.report? j = RingGroupedReport.report? i)) :=
  if h : i.molecule.atoms = j.molecule.atoms ∧ i.molecule.bonds.Perm j.molecule.bonds ∧
      i.spatial.positions = j.spatial.positions ∧ LocalizedChemicalRing.coordinatesAdmitted i = true then
    some ⟨RingBondRecordOrder.full ⟨h.1, h.2.1, h.2.2.1⟩ h.2.2.2⟩
  else none

def main (files : List String) : IO Unit := do
  let [base, a, b, c] := files | throw (IO.userError "expected the four exported presentations")
  let i ← admit base
  for file in [a,b,c] do
    let j ← admit file
    unless (certificate i j).isSome do throw (IO.userError "report equality certificate failed")
    IO.println s!"{file}: admitted, certified complete report equal to {base}"
