import TetraStereo.Engine.RingFullPathReport

open TetraStereo.OneCenter TetraStereo.Engine

-- Two triangles share carbon 0. Only the shared atom is tetrahedral.
private def spiro (partner : Element) : RawMolecule :=
  { atoms := [Element.C,.S,partner,.S,partner].map AtomSpec.aliphatic
    bonds := ([(0,1),(1,2),(2,0),(0,3),(3,4),(4,0)] : List (Nat × Nat)).map
      fun (a,b) => ⟨a,b,.single⟩ }

private def coords : SpatialConfiguration :=
  ⟨[⟨0,0,0⟩,⟨1,1,1⟩,⟨1,-1,-1⟩,⟨-1,1,-1⟩,⟨-1,-1,1⟩]⟩

/-- 1-chloro-2-fluorocyclopropane with explicit hydrogen atoms. The
rational moment curve supplies a nondegenerate test frame at each carbon. -/
private def ring : RawMolecule where
  atoms := ([.C,.C,.C,.F,.H,.Cl,.H,.H,.H] : List Element).map AtomSpec.aliphatic
  bonds := ([(0,1),(1,2),(2,0),(0,3),(0,4),(1,5),(1,6),(2,7),(2,8)] :
    List (Nat × Nat)).map fun (a,b) => ⟨a,b,.single⟩

private def verify (name : String) (mol : RawMolecule) (xyz : SpatialConfiguration)
    (expected : RingGroupedReport.Report) (deeper : Bool) : IO Unit := do
  let some i := LocalizedChemicalRing.admitRawSpatial? mol xyz | throw (IO.userError "molecular admission")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "coordinate admission")
  let roots := RingGroupedReport.centres i
  if deeper then
    let some a := roots.head? | throw (IO.userError "missing root")
    unless (RingActiveDistanceSchedule.sites i).any (fun q => decide (RingSphereQueue.candidate a q)) do
      throw (IO.userError "missing recursive auxiliary centre")
  let out := RingFullPathReport.forAtoms? i roots
  unless out == some expected do throw (IO.userError s!"{name}: unexpected full-path report {repr out}")
  IO.println s!"{name}: {repr out}"
  (← IO.getStdout).flush

def main : IO Unit := do
  let assigned : Option RingNestedActivePair.Labels := some (.chiral .R,.chiral .S)
  verify "C-O-S spiro" (spiro .O) coords [(0,assigned)] false
  verify "C-S-S spiro" (spiro .S) coords [(0,none)] false
  let geometry : SpatialConfiguration := ⟨(List.range 9).map fun n =>
    let t : ℚ := n
    ⟨t,t*t,t*t*t⟩⟩
  verify "1-chloro-2-fluorocyclopropane" ring geometry [(0,assigned),(1,assigned),(2,none)] true
