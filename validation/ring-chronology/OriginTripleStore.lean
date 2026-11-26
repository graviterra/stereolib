import TetraStereo.Engine.RingOriginTwinStore

/-! A methyl group hangs from a bicyclic junction. All three terminal hydrogens
stay outside the original root, and the graph-only duplicate-order test fails
at real occurrences of their parent. These sites require a marked-trial proof. -/
open TetraStereo.OneCenter TetraStereo.Engine

def main : IO Unit := do
  let m : RawMolecule := {
    atoms := [.C,.C,.B,.O,.S,.F,.Cl,.C,.H,.H,.H].map AtomSpec.aliphatic
    bonds := [(0,1),(0,2),(1,2),(1,3),(3,4),(4,2),(0,5),(0,6),(1,7),(7,8),(7,9),(7,10)].map
      (fun (a,b) => ⟨a,b,.single⟩) }
  let coords : List CartesianPoint3 := [⟨0,0,0⟩,⟨1,0,0⟩,⟨0,1,0⟩,⟨2,1,0⟩,⟨1,2,1⟩,
    ⟨0,0,1⟩,⟨-1,-1,-1⟩,⟨2,-1,1⟩,⟨3,-1,1⟩,⟨2,-2,1⟩,⟨2,-1,2⟩]
  let g : SpatialConfiguration := ⟨coords⟩
  let some i := LocalizedChemicalRing.admitRawSpatial? m g | throw (IO.userError "admission")
  unless LocalizedChemicalRing.coordinatesAdmitted i && (RingHydrogenCompletion.plan m).isEmpty do
    throw (IO.userError "expected admitted hydrogen-complete geometry")
  let some r := (List.finRange i.certified.certified.input.molecule.atomCount)[0]? | throw (IO.userError "root")
  let subjects := (RingActiveDistanceSchedule.sites i).filter fun f =>
    f.val.root == r && f.val.node.current?.any (fun a => a.val == 7) &&
    decide (RingEligibleGraph.candidate (RingPyramidalPublication.eligible i) r f) && !RingOriginOrderCheck.focus f
  unless !subjects.isEmpty do throw (IO.userError "missing occurrence")
  for f in subjects do
    unless (RingAtomicMetricPublication.early? i f).isNone && !RingOriginTwinAtomicRefusal.simple i f do
      throw (IO.userError "expected unresolved triple")
  unless RingOriginTwinStore.structuralFromRaw? m g [0] == some true do throw (IO.userError "raw check")
  let rows := RingSphereStore.rows i r (RingActiveDistanceSchedule.height i + 1)
  for f in subjects do
    unless (rows.lookup f) == some (some none) do throw (IO.userError "expected completed refusal")
  IO.println s!"{subjects.length} methyl occurrences require the triple proof; all are completed public refusals"
