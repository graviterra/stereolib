import TetraStereo.OneCenter.DeclarativeCIPRule1aExact

set_option autoImplicit false

namespace TetraStereo.OneCenter

noncomputable section

open DeclarativeCIP

namespace DeclarativeCIP

/-!
# Finite schedules for the independent first-difference hierarchy

The normative hierarchy relation quantifies over semantic addresses rather than executing a list
comparison.  This file proves the generic finite bridge needed by every production traversal: if a
list enumerates addresses in strict sphere-major order and every address outside it ties, scanning
that list to the first strict observation is exactly `FirstDifferenceOutcome`.
-/

/-- Scan a finite semantic-address schedule and stop at its first strict observation. -/
def firstStrictOnHierarchySchedule :
    List (List ℕ) → (List ℕ → Ordering) → Ordering
  | [], _ => .eq
  | position :: positions, observation =>
      match observation position with
      | .eq => firstStrictOnHierarchySchedule positions observation
      | decision => decision

/-- A strictly sphere-major schedule whose omitted addresses all tie realizes the independent
first-difference relation. -/
theorem firstStrictOnHierarchySchedule_is_firstDifference
    (observation : List ℕ → Ordering) : ∀ positions,
    positions.Pairwise HierarchyAddressBefore →
      (∀ position, position ∉ positions → observation position = .eq) →
      FirstDifferenceOutcome (fun position outcome => observation position = outcome)
        (firstStrictOnHierarchySchedule positions observation)
  | [], _, outside => by
      change ∀ position, observation position = .eq
      intro position
      exact outside position (by simp)
  | position :: positions, ordered, outside => by
      have orderParts := List.pairwise_cons.mp ordered
      have headBefore : ∀ other ∈ positions,
          HierarchyAddressBefore position other := orderParts.1
      have tailOrdered : positions.Pairwise HierarchyAddressBefore := orderParts.2
      cases observed : observation position with
      | lt =>
          simp only [firstStrictOnHierarchySchedule, observed]
          refine ⟨position, observed, ?_⟩
          intro earlier earlierBefore
          apply outside earlier
          simp only [List.mem_cons, not_or]
          constructor
          · intro equal
            subst earlier
            exact (lt_irrefl (HierarchyAddressKey position) earlierBefore).elim
          · intro present
            have forward := headBefore earlier present
            unfold HierarchyAddressBefore at earlierBefore forward
            exact ((not_lt_of_ge (le_of_lt forward)) earlierBefore).elim
      | gt =>
          simp only [firstStrictOnHierarchySchedule, observed]
          refine ⟨position, observed, ?_⟩
          intro earlier earlierBefore
          apply outside earlier
          simp only [List.mem_cons, not_or]
          constructor
          · intro equal
            subst earlier
            exact (lt_irrefl (HierarchyAddressKey position) earlierBefore).elim
          · intro present
            have forward := headBefore earlier present
            unfold HierarchyAddressBefore at earlierBefore forward
            exact ((not_lt_of_ge (le_of_lt forward)) earlierBefore).elim
      | eq =>
          have outsideTail : ∀ other, other ∉ positions → observation other = .eq := by
            intro other absent
            by_cases equal : other = position
            · simpa [equal] using observed
            · exact outside other (by simp [equal, absent])
          simpa [firstStrictOnHierarchySchedule, observed] using
            firstStrictOnHierarchySchedule_is_firstDifference observation positions
              tailOrdered outsideTail

/-- Functional form of the schedule theorem. -/
theorem firstDifference_iff_firstStrictOnHierarchySchedule
    (observation : List ℕ → Ordering) (positions : List (List ℕ))
    (ordered : positions.Pairwise HierarchyAddressBefore)
    (outside : ∀ position, position ∉ positions → observation position = .eq)
    (outcome : Ordering) :
    FirstDifferenceOutcome (fun position result => observation position = result) outcome ↔
      firstStrictOnHierarchySchedule positions observation = outcome := by
  have canonical := firstStrictOnHierarchySchedule_is_firstDifference
    observation positions ordered outside
  constructor
  · intro observed
    exact (FirstDifferenceOutcome.functional
      (fun _ first second hfirst hsecond => hfirst.symm.trans hsecond)
      observed canonical).symm
  · intro equal
    rw [← equal]
    exact canonical

/-- Comparing two value lists read at the same schedule is precisely the schedule's first-strict
scan of their pointwise comparator. -/
theorem compareLex_map_eq_firstStrictOnHierarchySchedule
    {α : Type*} (compareValue : α → α → Ordering)
    (left right : List ℕ → α) : ∀ positions,
    List.compareLex compareValue (positions.map left) (positions.map right) =
      firstStrictOnHierarchySchedule positions
        (fun position => compareValue (left position) (right position))
  | [] => rfl
  | position :: positions => by
      simp only [List.map_cons, List.compareLex, firstStrictOnHierarchySchedule]
      cases compared : compareValue (left position) (right position) <;>
        simp [compareLex_map_eq_firstStrictOnHierarchySchedule compareValue left right positions]

/-- A finite, ordered, common-address comparison is equivalent to the independent relational
first-difference judgment whenever omitted addresses compare equal. -/
theorem compareLex_map_iff_firstDifference
    {α : Type*} (compareValue : α → α → Ordering)
    (left right : List ℕ → α) (positions : List (List ℕ))
    (ordered : positions.Pairwise HierarchyAddressBefore)
    (outside : ∀ position, position ∉ positions →
      compareValue (left position) (right position) = .eq)
    (outcome : Ordering) :
    List.compareLex compareValue (positions.map left) (positions.map right) = outcome ↔
      FirstDifferenceOutcome
        (fun position result => compareValue (left position) (right position) = result)
        outcome := by
  rw [compareLex_map_eq_firstStrictOnHierarchySchedule]
  exact (firstDifference_iff_firstStrictOnHierarchySchedule
    (fun position => compareValue (left position) (right position))
    positions ordered outside outcome).symm

end DeclarativeCIP

end

end TetraStereo.OneCenter
