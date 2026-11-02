import TetraStereo.OneCenter.IUPACP93CanonicalFullereneC76FiniteAuditCore
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false



namespace TetraStereo.OneCenter.BlueBookP93.Cyclic

/-- Pure face-adjacency neighbors, definitionally aligned with the generic transcription's
forward-or-reverse face predicate. -/
def iupacP93CanonicalFullereneC76FaceAdjacencyNeighbors (atom : Nat) : Finset Nat :=
  (Finset.range 76).filter fun neighbor =>
    neighbor ≠ atom ∧
      (iupacP93CanonicalFullereneC76Faces.any fun face =>
        iupacP93CanonicalFullereneC76HasNamedFaceEdge face atom neighbor) = true

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Every bounded source locant has exactly three face-adjacent cage neighbors. -/
theorem iupacP93CanonicalFullereneC76_faceAdjacencyDegree
    (atom : Nat) (atomBound : atom < 76) :
    (iupacP93CanonicalFullereneC76FaceAdjacencyNeighbors atom).card = 3 := by
  interval_cases atom <;> decide

end TetraStereo.OneCenter.BlueBookP93.Cyclic
