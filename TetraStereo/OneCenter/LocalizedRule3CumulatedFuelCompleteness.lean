import TetraStereo.OneCenter.LocalizedRule3CumulatedDescriptor
import TetraStereo.OneCenter.LocalizedRerootFuelCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Fuel completeness for cumulated-axis traversal

The physical zipper budget, not an unproved atom-count heuristic, bounds a terminal-to-terminal
cumulated-axis walk.  The only chemical/topological premise retained here is open nonbranching
resolution: every reachable cursor is a true physical terminal or has one real order-two
continuation.  A ring-closing zero-copy edge is therefore not smuggled into the terminal case. Under that
premise, the same `2 * (carrierFuel + 1)` diameter bound used elsewhere is sufficient, and fuel
can never be the reason a valid walk refuses.
-/

namespace CertifiedLocalizedCIPInput

/-- Every path-valid cursor within the selected structural budget is either a proved physical
terminal or has exactly one real continuation.  Cyclic closure and branching are excluded as
explicit topology outcomes, not by looking only at real children. -/
def LocalizedRule3CumulatedAxisResolvedWithin
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (maximumBudget : Nat) : Prop :=
  ∀ cursor : input.LocalizedRerootCursor carrierFuel,
    input.LocalizedRerootCursorValid cursor →
    input.localizedRerootCursorBudget cursor ≤ maximumBudget →
    input.localizedRule3AxisTopology? cursor = some .terminal ∨
      ∃ next, input.localizedRule3AxisTopology? cursor = some (.linear next)

/-- A nonbranching physical cumulated-axis walk succeeds whenever its decreasing zipper budget is
covered by the supplied traversal index. -/
theorem exists_walkLocalizedRule3CumulatedAxis?_of_budget_le
    (input : CertifiedLocalizedCIPInput) {carrierFuel maximumBudget : Nat}
    (resolved : input.LocalizedRule3CumulatedAxisResolvedWithin
      (carrierFuel := carrierFuel) maximumBudget) :
    ∀ traversalFuel (cursor : input.LocalizedRerootCursor carrierFuel),
      traversalFuel ≤ maximumBudget →
      input.LocalizedRerootCursorValid cursor →
      input.localizedRerootCursorBudget cursor ≤ traversalFuel →
      ∃ path, input.walkLocalizedRule3CumulatedAxis? traversalFuel cursor = some path
  | 0, cursor, bounded, valid, covered => by
      obtain terminal | step := resolved cursor valid (by omega)
      ·
        exact ⟨[cursor], by
          simp [walkLocalizedRule3CumulatedAxis?, terminal]⟩
      · obtain ⟨next, topologyComputed⟩ := step
        have topologyDerived := input.localizedRule3AxisTopology?_sound
          cursor (.linear next) topologyComputed
        cases topologyDerived with
        | linear frame real =>
        rcases frame with ⟨children, _childrenComputed, childrenDerived, membership⟩
        have nextCharacterized := (membership next).mp (by simp)
        have nextValid := input.localizedRerootChild_valid
          cursor next children childrenDerived nextCharacterized.1
        have decreases := input.localizedRerootChild_budget_lt
          cursor next children valid childrenDerived nextCharacterized.1
        omega
  | traversalFuel + 1, cursor, bounded, valid, covered => by
      obtain terminal | step := resolved cursor valid (by omega)
      ·
        exact ⟨[cursor], by
          simp [walkLocalizedRule3CumulatedAxis?, terminal]⟩
      · obtain ⟨next, topologyComputed⟩ := step
        have topologyDerived := input.localizedRule3AxisTopology?_sound
          cursor (.linear next) topologyComputed
        cases topologyDerived with
        | linear frame real =>
        rcases frame with ⟨children, _childrenComputed, childrenDerived, membership⟩
        have nextCharacterized := (membership next).mp (by simp)
        have nextValid := input.localizedRerootChild_valid
          cursor next children childrenDerived nextCharacterized.1
        have decreases := input.localizedRerootChild_budget_lt
          cursor next children valid childrenDerived nextCharacterized.1
        obtain ⟨tail, tailComputed⟩ :=
          input.exists_walkLocalizedRule3CumulatedAxis?_of_budget_le
            resolved traversalFuel next (by omega) nextValid (by omega)
        exact ⟨cursor :: tail, by
          simp [walkLocalizedRule3CumulatedAxis?, topologyComputed, tailComputed]⟩

/-- The production cumulene traversal index is the proved zipper-diameter bound. -/
theorem exists_walkLocalizedRule3CumulatedAxis?_at_traversalFuel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (resolved : input.LocalizedRule3CumulatedAxisResolvedWithin
      (carrierFuel := carrierFuel)
      (input.localizedRule3CumulatedTraversalFuel carrierFuel))
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ path, input.walkLocalizedRule3CumulatedAxis?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) cursor = some path := by
  apply input.exists_walkLocalizedRule3CumulatedAxis?_of_budget_le
    resolved (input.localizedRule3CumulatedTraversalFuel carrierFuel) cursor
    (by rfl) valid
  simpa [localizedRule3CumulatedTraversalFuel,
    localizedOccurrenceRerootEvaluationFuel] using
      input.localizedRerootCursorBudget_le_twice cursor

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
