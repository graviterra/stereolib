import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Authoritative public occurrence routing

The chemist-facing descriptor discovery path now uses the fully authoritative occurrence-local
Rules 1--5 construction and the complete Rule-6 comparator.  Bounded implementations remain only
as explicit fast paths whose failure is followed by the authoritative traversal.
-/

theorem tetrahedralOccurrenceFact?_eq_fullyAuthoritative
    (mol : RawMolecule) (fuel center : Nat) :
    tetrahedralOccurrenceFact? mol fuel center =
      tetrahedralOccurrenceFactAuthoritative? mol fuel center :=
  rfl

theorem compareOccurrenceBranchesThroughRule6?_eq_fullyAuthoritative
    (mol : RawMolecule) (fuel center reference left right : Nat) :
    compareOccurrenceBranchesThroughRule6? mol fuel center reference left right =
      compareOccurrenceBranchesThroughRule6FullyAuthoritative?
        mol fuel center reference left right :=
  rfl

/-- One unavailable expected occurrence aborts authoritative batch construction. -/
theorem discoverOccurrenceAuxBatchesAuthoritative?_singleton_failure
    (label? : OccurrenceAuxState → RawMolecule.CanonicalBranchNode → Option OccurrenceAuxFact)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (failed : label? state node = none) :
    discoverOccurrenceAuxBatchesAuthoritative? label? 1 [node] state = none := by
  simp [discoverOccurrenceAuxBatchesAuthoritative?, failed]

end TetraStereo.OneCenter
