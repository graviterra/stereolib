import TetraStereo.Engine.RingGroupedReport
import TetraStereo.Examples.BlueBookHexachlorocyclohexaneSeries
import TetraStereo.Examples.BlueBookHexachlorocyclohexaneProof
import TetraStereo.Examples.CentresRingSpiroCasing

open TetraStereo.OneCenter TetraStereo.Engine TetraStereo.Examples
open BlueBookHexachlorocyclohexane BlueBookHexachlorocyclohexaneSeries

assert_kernel_only TetraStereo.Engine.RingGroupedReport.total
assert_kernel_only TetraStereo.Engine.RingGroupedReport.Source.report_iff
assert_kernel_only TetraStereo.Examples.BlueBookHexachlorocyclohexaneSeries.seven_published_reports
assert_kernel_only TetraStereo.Examples.BlueBookHexachlorocyclohexane.published_report

private def checkAt (mask : Fin 64) (site : Fin 6) (expected : Letter) : IO Unit := do
  let some points := (List.range 18).mapM (faces mask) | throw (IO.userError "incomplete coordinates")
  let some i := LocalizedChemicalRing.admitRawSpatial? molecule ⟨points⟩ | throw (IO.userError "admission failed")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "coordinate gate failed")
  let some a := (RingGroupedReport.carbons i).find? (fun a => a.val == site.val) | throw (IO.userError "no root")
  let some [(n,some (x,y))] := RingGroupedReport.forAtoms? i [a] | throw (IO.userError "missing assignment")
  let code := fun z => CentresRing.labelCode (some z)
  let mate := match expected with
    | .chiral h => .chiral h.swap
    | .pseudoasymmetric h => .pseudoasymmetric h
  IO.println s!"mask {mask} atom {n} original/mirror {code x}/{code y}, independent {code expected}/{code mate}"
  (← IO.getStdout).flush
  unless n == site.val && x == expected && y == mate do throw (IO.userError "chemical discrepancy")

assert_kernel_only TetraStereo.Examples.CentresRingSpiroCasing.same_molecule

private def readRows (g : RawMolecule) (p : SpatialConfiguration) : IO (List (Nat × String × String)) := do
  let some i := LocalizedChemicalRing.admitRawSpatial? g p | throw (IO.userError "structural admission failed")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "coordinate admission failed")
  let some rows := RingGroupedReport.carbonReport? i | throw (IO.userError "missing carbon report")
  return rows.map fun (n,v) => (n,CentresRing.labelCode (v.map Prod.fst),CentresRing.labelCode (v.map Prod.snd))

private def checkFluorospiro : IO Unit := do
  let orig ← readRows CentresRingSpiroCasing.molecule CentresRingSpiroCasing.spatial
  let actual ← readRows CentresRingSpiroCasing.renumbered CentresRingSpiroCasing.moved
  let mirrored ← readRows CentresRingSpiroCasing.renumbered (CentresRingSpiroCasing.reflected CentresRingSpiroCasing.moved)
  let wanted : List (Nat × String × String) := [(0,"S","R"),(1,"R","S"),(2,"S","R"),(3,"R","S"),(4,"S","R")]
  unless orig == wanted && actual.map Prod.fst == [0,1,2,3,4] && mirrored.map Prod.fst == [0,1,2,3,4] do
    throw (IO.userError s!"inventory or original report mismatch: {repr (orig,actual,mirrored)}")
  for (n,x,y) in orig do
    unless actual.lookup (CentresRingSpiroCasing.rename n) == some (x,y) && mirrored.lookup (CentresRingSpiroCasing.rename n) == some (y,x) do
      throw (IO.userError s!"mismatch at original atom {n}: {repr (actual,mirrored)}")
  IO.println s!"All five transported carbons passed: original {repr orig}, renumbered {repr actual}, separately reflected {repr mirrored}."

/-- Cross-check one published locant in each of eight ring configurations, or all five
fluorospiro carbons after an atom exchange and a fresh reflected admission. -/
def main (args : List String) : IO Unit := do
  unless args == [] || args == ["--hexachloro"] || args == ["--fluorospiro"] do
    throw (IO.userError "expected --hexachloro, --fluorospiro, or no arguments")
  if args == [] || args == ["--hexachloro"] then
    checkAt 37 0 (.chiral .R)
    for row in series do
      let some (site,letter) := (row.locants.zip row.expected).head?
        | throw (IO.userError "empty published case")
      checkAt row.mask site letter
  if args == [] || args == ["--fluorospiro"] then checkFluorospiro
