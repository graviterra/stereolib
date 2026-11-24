import TetraStereo.Engine.PublicAPI

open TetraStereo.OneCenter TetraStereo.Engine

/-- 1-chloro-2-fluorocyclopropane with explicit hydrogen atoms. The
rational moment curve supplies a nondegenerate test frame at each carbon. -/
private def ring : RawMolecule where
  atoms := ([.C,.C,.C,.F,.H,.Cl,.H,.H,.H] : List Element).map AtomSpec.aliphatic
  bonds := ([(0,1),(1,2),(2,0),(0,3),(0,4),(1,5),(1,6),(2,7),(2,8)] :
    List (Nat × Nat)).map fun (a,b) => ⟨a,b,.single⟩

def main : IO Unit := do
  let geometry : SpatialConfiguration := ⟨(List.range 9).map fun n =>
    let t : ℚ := n
    ⟨t,t*t,t*t*t⟩⟩
  let some i := LocalizedChemicalRing.admitRawSpatial? ring geometry
    | throw (IO.userError "ring admission failed")
  unless LocalizedChemicalRing.coordinatesAdmitted i do throw (IO.userError "degenerate frame")
  let atoms := RingGroupedReport.centres i
  let fast := atoms.map fun a => (RingSphereQueue.early? i (RingGroupedReport.origin i a)).isSome
  unless fast == [true,true,false] do throw (IO.userError s!"unexpected constitutional decisions {fast}")
  let expected : RingGroupedReport.Report := [(0,some (.chiral .R,.chiral .S)),
    (1,some (.chiral .R,.chiral .S)),(2,none)]
  let actual := RingSphereQueue.stagedReport i atoms
  unless actual == some expected && actual == RingGroupedReport.forAtoms? i atoms do
    throw (IO.userError s!"unexpected report {repr actual}")
  let zero := atoms.map fun a => (RingZeroMassReport.zeroEarly? i (RingGroupedReport.origin i a)).isSome
  unless zero == fast && RingZeroMassReport.recursiveReport i (atoms.reverse ++ atoms) ==
      some (expected.reverse ++ expected) do throw (IO.userError "recursive zero-mass report mismatch")
  unless ringRecursiveZeroMassReport? i (atoms.reverse ++ atoms) == some (expected.reverse ++ expected) do
    throw (IO.userError "rebuilt stereo publication changed a requested descriptor or completed refusal")
  IO.println "All six requested rows, including repeated roots and refusals, agreed with recursive zero-mass exits."
  IO.println "Two constitutional exits (R/S, R/S); one sparse auxiliary pass (completed refusal)."
