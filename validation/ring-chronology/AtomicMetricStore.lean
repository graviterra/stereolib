import TetraStereo.Engine.RingAtomicMetricPublication

/-! An eligible carbon lies on the bicyclic junction. Its incident atoms have
distinct atomic numbers even on paths that change the order of ring origins. -/
open TetraStereo.OneCenter TetraStereo.Engine

def main : IO Unit := do
  let m : RawMolecule := {
    atoms := [.C,.C,.B,.O,.S,.F,.C,.F,.Cl,.Br,.Cl].map AtomSpec.aliphatic
    bonds := [(0,1),(0,2),(1,2),(1,3),(3,4),(4,2),(0,5),(0,6),(6,7),(6,8),(6,9),(1,10)].map
      (fun (a,b) => ⟨a,b,.single⟩) }
  let coords : List CartesianPoint3 := [⟨0,0,0⟩,⟨1,0,0⟩,⟨0,1,0⟩,⟨2,1,0⟩,⟨1,2,1⟩,
    ⟨0,0,1⟩,⟨-1,-1,-1⟩,⟨-2,-1,-1⟩,⟨-1,-2,-1⟩,⟨-1,-1,-2⟩,⟨1,0,1⟩]
  let g : SpatialConfiguration := ⟨coords⟩
  let some i := LocalizedChemicalRing.admitRawSpatial? m g | throw (IO.userError "admission")
  unless LocalizedChemicalRing.coordinatesAdmitted i && (RingHydrogenCompletion.plan m).isEmpty do
    throw (IO.userError "expected admitted hydrogen-complete input")
  let some root := (List.finRange i.certified.certified.input.molecule.atomCount)[0]? |
    throw (IO.userError "missing atom 0")
  if RingOriginOrderCheck.check i root then throw (IO.userError "graph condition unexpectedly held")
  unless RingAtomicMetricPublication.check i root do throw (IO.userError "mixed certificate failed")
  let sites := (RingActiveDistanceSchedule.sites i).filter fun f =>
    decide (RingEligibleGraph.candidate (RingPyramidalPublication.eligible i) root f)
  let mut rescued := 0
  for f in sites do
    unless RingOriginOrderCheck.focus f do
      let some s := RingAtomicMetricPublication.early? i f | throw (IO.userError "missing atomic signature")
      unless s.letters.isSome do throw (IO.userError "unexpected refusal")
      IO.println s!"auxiliary {f.val.node.history.reverse.map Fin.val} gives {repr s.letters}"
      rescued := rescued + 1
  unless rescued > 0 do throw (IO.userError "expected at least one strict auxiliary")
  let n := RingActiveDistanceSchedule.height i + 1
  let publicRows := RingSphereStore.rows i root n
  let activeRows := RingOriginMetricReport.rows i root n
  unless publicRows == activeRows && !publicRows.isEmpty do throw (IO.userError "sphere rows")
  let native := RingHydrogenReport.fromRaw? m g [0]
  let active := RingOriginMetricReport.fromRaw? m g [0]
  unless native == active && (native.bind List.head?).any (fun row => row.2.isSome) do
    throw (IO.userError s!"unexpected raw results {repr native} {repr active}")
  IO.println s!"{rescued} graph failures covered; {publicRows.length} rows agree; raw {repr native}"
