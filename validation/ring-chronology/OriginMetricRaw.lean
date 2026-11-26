import TetraStereo.Engine.RingOriginMetricReport

/-! End-to-end raw checks on synthetic single-bond rings. The carbon and
phosphorus cases exercise separate publication paths. -/
open TetraStereo.OneCenter TetraStereo.Engine

private def molecule (atoms : List Element) (edges : List (Nat × Nat)) : RawMolecule where
  atoms := atoms.map AtomSpec.aliphatic
  bonds := edges.map fun (a,b) => ⟨a,b,.single⟩

private def run (name : String) (m : RawMolecule) (positions : List CartesianPoint3) : IO Unit := do
  let request := [0,1,0]
  let mut previous : Option RS := none
  for reflected in [false,true] do
    let g : SpatialConfiguration := ⟨if reflected then positions.map CartesianPoint3.reflectX else positions⟩
    let native := RingHydrogenReport.fromRaw? m g request
    let moved := RingOriginMetricReport.fromRaw? m g request
    unless native == moved do throw (IO.userError s!"{name}: raw result changed")
    let some [(0,some (.chiral h,.chiral k)),(1,none),(0,some (.chiral h',.chiral k'))] := moved
      | throw (IO.userError s!"{name}: unexpected raw rows {repr moved}")
    unless h == h' && k == k' && k == h.swap do throw (IO.userError s!"{name}: repeat or mirror column")
    if let some orig := previous then
      unless h == orig.swap do throw (IO.userError s!"{name}: reflection")
    previous := some h
    IO.println s!"{name} reflected={reflected}: atom 0 {repr h}, atom 1 unassigned, repeated row matched"
  let miss := RingOriginMetricReport.fromRaw? m ⟨positions⟩ [m.atomCount]
  unless miss.isNone do throw (IO.userError s!"{name}: invalid atom ID was accepted")

/-- Two triangles sharing the middle S–P bond. When reached along
S–S–O–P, the two sulfur arms at P are duplicates of different occurrences. -/
private def bicyclic (reflected : Bool) : IO Unit := do
  let m := molecule [.S,.S,.O,.P,.F] [(0,1),(1,2),(2,3),(3,0),(3,1),(1,4)]
  let ps : List CartesianPoint3 := [⟨0,0,0⟩,⟨1,0,0⟩,⟨0,1,0⟩,⟨0,0,1⟩,⟨2,1,1⟩]
  let g : SpatialConfiguration := ⟨if reflected then ps.map CartesianPoint3.reflectX else ps⟩
  unless (RingHydrogenCompletion.plan m).isEmpty do throw (IO.userError "expected hydrogen-complete graph")
  let some i := LocalizedChemicalRing.admitRawSpatial? m g | throw (IO.userError "bicyclic admission")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "bicyclic geometry")
  let some root := (List.finRange i.certified.certified.input.molecule.atomCount)[0]?
    | throw (IO.userError "missing original root")
  let some q := (RingEligibleGraph.queue i (RingPyramidalPublication.eligible i) root 3).find?
      (fun t => t.val.node.history.map Fin.val == [3,2,1,0])
    | throw (IO.userError "missing S–S–O–P occurrence")
  let batches := RingActiveDistanceSchedule.height i + 1 - 3
  let read := fun (rows : List (RingActivePairs.Site i × RingActiveDistanceSchedule.Cell)) =>
    (rows.find? (fun row => row.1 == q)).map Prod.snd
  let native := read (RingSphereStore.rows i root batches)
  let active := read (RingOriginMetricReport.rows i root batches)
  let some (some (some (.chiral hand,.chiral mirror))) := native
    | throw (IO.userError s!"missing public P hand {repr native}")
  unless hand == (if reflected then RS.S else RS.R) && mirror == hand.swap && active == some (some (some (.chiral mirror,.chiral hand))) do
    throw (IO.userError s!"expected opposite stored P hands, got {repr native} and {repr active}")
  let ids := List.range m.atomCount
  let publicReport := RingHydrogenReport.fromRaw? m g ids
  let activeReport := RingOriginMetricReport.fromRaw? m g ids
  unless publicReport.isSome && publicReport == activeReport do
    throw (IO.userError s!"unexpected whole-graph reports {repr publicReport}, {repr activeReport}")
  IO.println s!"bicyclic auxiliary P reflected={reflected}: public {repr hand}, active {repr mirror}; all {ids.length} raw rows agree"

def main : IO Unit := do
  let coords : List CartesianPoint3 := [⟨0,0,0⟩,⟨1,0,0⟩,⟨0,1,0⟩,⟨0,0,1⟩]
  run "tetrahedral C" (molecule [.C,.O,.S,.F,.Cl] [(0,1),(1,2),(2,0),(0,3),(0,4)])
    (coords ++ [⟨-1,-1,-1⟩])
  run "pyramidal P" (molecule [.P,.O,.S,.F] [(0,1),(1,2),(2,0),(0,3)]) coords
  for reflected in [false,true] do bicyclic reflected
