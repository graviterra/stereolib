import TetraStereo.Engine.RingGroupedReport
import TetraStereo.Examples.LocalizedChemicalRingSpiroProjection
import TetraStereo.Examples.RingPairedAuxiliary
import TetraStereo.Examples.CentresRingSpiroCasing

open TetraStereo.OneCenter TetraStereo.Engine TetraStereo.Examples

assert_kernel_only TetraStereo.Engine.RingGroupedCentre.Arms.edge_source
assert_kernel_only TetraStereo.Engine.RingGroupedMark.OnGeometry.reflect
assert_kernel_only TetraStereo.Engine.RingGroupedOrders.partition
assert_kernel_only TetraStereo.Engine.RingGroupedTrials.Decision.ordinary_refusal
assert_kernel_only TetraStereo.Engine.RingGroupedPublication.molecular_iff

private def check (name : String) (i : LocalizedChemicalRing.Input) (expected : List (Nat × String × String)) : IO Unit := do
  IO.println s!"Checking {name}"
  (← IO.getStdout).flush
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "coordinate gate failed")
  let some report := RingGroupedReport.carbonReport? i | throw (IO.userError "unresolved molecular report")
  let actual := report.map fun (n,v) => (n,CentresRing.labelCode (v.map Prod.fst),CentresRing.labelCode (v.map Prod.snd))
  unless actual == expected do throw (IO.userError s!"expected {repr expected}, obtained {repr actual}")
  IO.println s!"{name} verified {repr actual}"
  (← IO.getStdout).flush

private def simple (ligands : List Element) : IO LocalizedChemicalRing.Input := do
  let m : RawMolecule := {
    atoms := (Element.C :: ligands).map AtomSpec.aliphatic
    bonds := (List.range 4).map fun k => ⟨0,k+1,.single⟩}
  let positions : SpatialConfiguration := ⟨[⟨0,0,0⟩,⟨1,1,1⟩,⟨1,-1,-1⟩,⟨-1,1,-1⟩,⟨-1,-1,1⟩]⟩
  let some i := LocalizedChemicalRing.admitRawSpatial? m positions | throw (IO.userError "fixture admission failed")
  return i

private def refusal (name : String) (ligands : List Element) (count : Nat) : IO Unit := do
  let i ← simple ligands
  let some a := (RingGroupedReport.carbons i).head? | throw (IO.userError "missing carbon")
  let q := RingGroupedReport.origin i a
  let some ⟨_,issued⟩ := RingGroupedPublication.certify? i q (fun _ => some none) | throw (IO.userError "missing local decision")
  match issued with
  | .absent _ => throw (IO.userError "unrecognized carbon")
  | .centre _ arms _ d _ _ _ =>
    unless (RingGroupedOrders.marks arms).length == count do throw (IO.userError "incorrect eligible ligand count")
    match d with
    | .ordinary _ o =>
      unless count == 2 && o.hands.isNone do throw (IO.userError "incorrect ordinary refusal")
    | .promoted _ ts _ =>
      unless decide (count ≥ 3) && ts.length == count && ts.all (fun t => t.2.outcome.hands.isNone) do
        throw (IO.userError "missing promoted trial or strict order in a symmetric fixture")
  let absent := CentresRing.labelCode none
  check name i [(0,absent,absent)]

def main (args : List String) : IO Unit := do
  unless args == [] || args == ["--small"] || args == ["--paired"] || args == ["--spiro"] || args == ["--promotion"] do
    throw (IO.userError "expected --small, --paired, --spiro, --promotion, or no arguments")
  if args == [] || args == ["--small"] then
    refusal "CH2FCl" [.H,.H,.F,.Cl] 2
    refusal "CH3F" [.H,.H,.H,.F] 3
    refusal "CH2Cl2" [.H,.H,.Cl,.Cl] 4
    refusal "CH4" [.H,.H,.H,.H] 4
  if args == [] || args == ["--paired"] then
    check "paired arms" (RingPairedAuxiliary.input false) [(0,"s","s"),(3,"R","S"),(4,"R","S"),(5,"S","R"),(6,"S","R")]
    check "paired arms after coordinate exchange" (RingPairedAuxiliary.input true) [(0,"R","S"),(3,"R","S"),(4,"S","R"),(5,"S","R"),(6,"S","R")]
  if args == [] || args == ["--spiro"] then
    let some i := LocalizedChemicalRing.admitRawSpatial? CentresRingSpiroCasing.molecule CentresRingSpiroCasing.spatial
      | throw (IO.userError "spiro admission failed")
    check "fluorospiro" i [(0,"S","R"),(1,"R","S"),(2,"S","R"),(3,"R","S"),(4,"S","R")]

  if args == [] || args == ["--promotion"] then
    let .ok (some i) := LocalizedChemicalRing.admitSmilesSpatial?
      LocalizedChemicalRingSpiroProjection.smiles LocalizedChemicalRingSpiroProjection.spatial
      | throw (IO.userError "dioxaspiro admission failed")
    check "dioxaspiro" i [(0,"R","S"),(2,"-","-"),(3,"-","-"),(4,"-","-"),(6,"-","-"),(7,"-","-"),(8,"-","-")]
