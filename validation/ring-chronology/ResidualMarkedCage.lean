import TetraStereo.Engine.RingTrialInventoryOrder
import TetraStereo.Engine.RingOrdinaryPairVerdict
open TetraStereo.OneCenter TetraStereo.Engine

/-! The central carbon connects to all four vertices of a fluorinated carbon
square. For the specified coordinates, nominating atom 4 leaves atoms 1 and 3
tied although no frozen, mark-preserving branch exchange exists. -/
private def cage : RawMolecule := {
  atoms := ([.C,.C,.C,.C,.C,.F,.F,.F,.F] : List Element).map AtomSpec.aliphatic
  bonds := [(0,1),(0,2),(0,3),(0,4),(1,2),(2,3),(3,4),(4,1),(1,5),(2,6),(3,7),(4,8)].map
    fun (a,b) => ⟨a,b,.single⟩ }

private def geometry : SpatialConfiguration := ⟨(List.range 9).map fun j =>
  let t : ℚ := j
  let sign : ℚ := if j == 5 || j == 6 then -1 else 1
  ⟨sign*t,sign*t*t,sign*t*t*t⟩⟩

def main : IO Unit := do
  let some i := LocalizedChemicalRing.admitRawSpatial? cage geometry | throw (IO.userError "raw admission")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "geometry")
  let some root := (RingGroupedReport.centres i).find? (fun a => a.val == 0) | throw (IO.userError "root")
  let f := RingGroupedReport.origin i root
  let some fr := RingNestedActivePair.frame? i f | throw (IO.userError "frame")
  let slot (id : Nat) := (List.finRange 4).find? (fun s => RingGroupedTrials.atom fr s == id)
  let some m := slot 4 | throw (IO.userError "nominated atom")
  let some a := slot 1 | throw (IO.userError "first arm")
  let some b := slot 3 | throw (IO.userError "second arm")
  let rows := RingSphereStore.rows i root (RingActiveDistanceSchedule.height i + 1)
  let read := RingSphereQueue.reader root (RingSphereQueue.viewOf rows)
  let some trials := RingResidualPairDecision.diagnose? fr read | throw (IO.userError "schedule")
  let some trial := trials.find? (fun t => t.nomination == some m) | throw (IO.userError "missing nomination")
  unless trials.all (fun t => t.nomination.isSome) do throw (IO.userError "unexpected unmarked trial")
  for rev in [false,true] do
    let some ordinary := RingOrdinaryPairVerdict.onReader? fr read rev
      | throw (IO.userError "missing ordinary comparisons before nomination")
    unless ordinary[a.val][b.val] == .tie do throw (IO.userError "ordinary arms differ")
    let verdict := (trial.table rev)[a.val][b.val]
    let result := RingResidualPairDecision.classify fr read trial.nomination a b verdict
    unless result == .noExchangeTie do throw (IO.userError s!"marked comparison {repr result}")
    let some x := RingTrialInventoryOrder.observation? fr read rev trial.nomination a | throw (IO.userError "first inventory")
    let some y := RingTrialInventoryOrder.observation? fr read rev trial.nomination b | throw (IO.userError "second inventory")
    unless decide (x = y) do throw (IO.userError "different signed inventories or mark words")
  IO.println "Mark 4 leaves ligands 1 and 3 tied without an exchange on both geometries."
