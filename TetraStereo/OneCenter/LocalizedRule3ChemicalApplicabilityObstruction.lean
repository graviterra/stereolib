import TetraStereo.OneCenter.LocalizedRerootDescriptorBearingRule3ChemicalApplicability

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Rule-3 chemical-applicability readiness obstruction

This module exposes the over-constraint hidden in the existing readiness premise
`LocalizedDescriptorBearingRule3ChemicalApplicabilityThrough`: once the queried bound reaches the
uniform two-cursor reference-expansion threshold `2 * (carrierFuel + 1) + 1`, every occurrence is
forced into a nonrecursive chemical case.

The argument is purely structural and budget-theoretic.  A cursor with no incoming coordinate is
trivially path-valid, and every cursor budget is bounded by twice the carrier depth
(`localizedRerootCursorBudget_le_twice`).  Specializing the premise at exactly
`2 * (carrierFuel + 1) + 1` therefore lands on the successor branch of the classification.  The
deep recursive branch requires `2 * (carrierFuel + 1) < 2 * (carrierFuel + 1)`, which is
impossible, so the shallow nonrecursive branch is extracted for every occurrence.

No molecule fixture is required, and no claim is made that any particular runtime evaluation
fails.  The result only shows that a readiness hypothesis demanding the full recursive chemical
classification at or above the reference threshold cannot be discharged by the deep recursive
branch, so any genuinely recursive/geometric Rule-3 occurrence contradicts the premise.  This is
the obstruction that guides the readiness repair.
-/

namespace CertifiedLocalizedCIPInput

namespace LocalizedDescriptorBearingRule3ChemicalApplicabilityThrough

/-- At the uniform two-cursor reference-expansion threshold the deep recursive branch of the
chemical classification is impossible for a budget-bounded cursor, so the premise forces the
nonrecursive chemical case for every occurrence. -/
theorem nonrecursive_everywhere
    (input : CertifiedLocalizedCIPInput) {carrierFuel maximumFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (chemical : input.LocalizedDescriptorBearingRule3ChemicalApplicabilityThrough
      target view maximumFuel)
    (large : 2 * (carrierFuel + 1) + 1 ≤ maximumFuel)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    input.LocalizedDescriptorBearingRule3NonrecursiveChemicalApplicability occurrence := by
  let cursor : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := occurrence, previous? := none }
  have cursorValid : input.LocalizedRerootCursorValid cursor := by
    simp [LocalizedRerootCursorValid, cursor]
  have cursorBudget : input.localizedRerootCursorBudget cursor ≤
      2 * (carrierFuel + 1) + 1 := by
    have base := input.localizedRerootCursorBudget_le_twice cursor
    omega
  have classified :=
    chemical (2 * (carrierFuel + 1) + 1) large cursor cursorValid cursorBudget
  rcases classified with ⟨_shallow, nonrecursive⟩ | ⟨covers, _⟩
  · exact nonrecursive
  · exfalso
    omega

/-- The conservative production evaluation fuel `span * span`, where
`span := 2 * (carrierFuel + 1) + 1`, is at least `span`, so a chemical-classification readiness
premise at that fuel is already over-constrained in the same way. -/
theorem nonrecursive_everywhere_of_evaluationFuel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (chemical : input.LocalizedDescriptorBearingRule3ChemicalApplicabilityThrough
      target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel))
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    input.LocalizedDescriptorBearingRule3NonrecursiveChemicalApplicability occurrence :=
  nonrecursive_everywhere input target view chemical
    (by
      dsimp [localizedDescriptorBearingRule3EvaluationFuel]
      exact Nat.le_mul_of_pos_right _ (by omega : 0 < 2 * (carrierFuel + 1) + 1))
    occurrence

end LocalizedDescriptorBearingRule3ChemicalApplicabilityThrough

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
