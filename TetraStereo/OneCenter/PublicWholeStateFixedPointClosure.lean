/-
Copyright (c) 2026 TetraStereo contributors.
Released under Apache 2.0 license as described in the file LICENSE.

# Exact public whole-state Rule-3--5 fixed-point closure

The accepted public model module
`TetraStereo.OneCenter.PublicWholeStateRule3Through5Model` proves that the existing unique
restricted model is pointwise equal to the *whole-state* descriptor
`aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead? (aromaticCanonicalWholeStateReader
state)` at rule fuel `2 * (carrierFuel + 1)`, but its final uniqueness theorem still conjoins the
supplied restricted `CIPModel` hypothesis with that pointwise equality.

This module removes that conjunction.  It proves, literally and for **every** source-canonical
occurrence target, that the whole-state descriptor equation

```
∀ target, state target =
  aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
    (aromaticCanonicalWholeStateReader state) target (2 * (carrierFuel + 1))
```

is equivalent to the restricted `CIPModel` fixed point of the accepted public legacy
Rule-3--5 semantics, and then transfers the shipped existence/uniqueness theorem across that
equivalence.  The resulting state satisfies *only* the whole-state equation: no `CIPModel`
conjunct, no supplied model, and no extra hypothesis remains in the target.

Both success (`some label`) and fail-closed refusal (`none`) outcomes are covered, because the
equation is an equality in the full `Option AromaticCanonicalAuxiliaryLabel` type and the
descriptor equality used in the transport is itself a whole-`Option` equality.

## Scope

Structural mathematics only.  This module does not claim descriptor success, chemical correctness,
or any completeness statement, and it makes no assertion about any corrected Rule-4a-prefixed
backend (owned elsewhere).  It only repackages the exact accepted public computations and their
already-proved unique restricted model.
-/

import TetraStereo.OneCenter.PublicWholeStateRule3Through5Model

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-- The literal public whole-state Rule-3--5 fixed-point equation at the common fuel
`2 * (carrierFuel + 1)`.  Every source-canonical occurrence target stores exactly the whole-state
descriptor outcome, including the refusal `none` case.  This is a transparent abbreviation of the
equation used verbatim in the theorems below. -/
def AromaticCanonicalOccurrenceRule3Through5WholeStateFixedPoint
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel) : Prop :=
  ∀ target : source.AromaticCanonicalOccurrence carrierFuel,
    state target =
      source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
        (source.aromaticCanonicalWholeStateReader state) target
        (2 * (carrierFuel + 1))

/-- The whole-state fixed-point predicate is definitionally the displayed equation. -/
theorem aromaticCanonicalOccurrenceRule3Through5WholeStateFixedPoint_iff
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel) :
    source.AromaticCanonicalOccurrenceRule3Through5WholeStateFixedPoint carrierFuel state ↔
      ∀ target : source.AromaticCanonicalOccurrence carrierFuel,
        state target =
          source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
            (source.aromaticCanonicalWholeStateReader state) target
            (2 * (carrierFuel + 1)) :=
  Iff.rfl

/-- **Literal equivalence of the restricted model and the whole-state equation.**  For the accepted
public legacy Rule-3--5 semantics at rule fuel `2 * (carrierFuel + 1)`, the shipped restricted
`CIPModel` fixed point is equivalent to the whole-state descriptor equation for every target.

Forward: the accepted model-locality theorem identifies the stored label with the whole-state
descriptor at the common fuel.

Reverse: the declarative-outcome correspondence turns the equation into the restricted
declarative derivation, and the proved whole-`Option` descriptor equality rewrites the restricted
descriptor back to the whole-state descriptor, closing with the equation itself. -/
theorem cipModel_iff_wholeState_fixedPoint
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel) :
    (source.aromaticCanonicalOccurrenceSystem
      (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel (2 * (carrierFuel + 1)))).CIPModel state ↔
      ∀ target : source.AromaticCanonicalOccurrence carrierFuel,
        state target =
          source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
            (source.aromaticCanonicalWholeStateReader state) target
            (2 * (carrierFuel + 1)) := by
  constructor
  · intro model target
    exact
      source.aromaticCanonicalOccurrenceRule3Through5Model_eq_descriptorWithRead?_of_wholeState
        state model target
  · intro fixed target
    change source.DeclarativeAromaticCanonicalOccurrenceRule3Through5Outcome
      (2 * (carrierFuel + 1)) state target (state target)
    exact
      (source.declarativeAromaticCanonicalOccurrenceRule3Through5Outcome_iff
        (2 * (carrierFuel + 1)) state target (state target)).mpr (by
          rw [← source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_at_twice
            target state]
          exact (fixed target).symm)

/-- **Unique state satisfying only the actual whole-state fixed-point equation.**  At the common
fuel `2 * (carrierFuel + 1)`, for every source-canonical occurrence target and with the full
`Option` outcome (acceptance or fail-closed refusal), there is exactly one auxiliary state whose
stored label equals the whole-state Rule-3--5 descriptor at that state.

The target contains no supplied model, no `CIPModel` conjunct and no additional hypothesis.  The
proof transports the shipped unique restricted model through `cipModel_iff_wholeState_fixedPoint`:
the forward direction exhibits the witness from its model, and the reverse direction converts any
competing whole-state fixed point into a restricted model before invoking shipped uniqueness. -/
theorem existsUnique_wholeState_fixedPoint
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat) :
    ∃! state : source.AromaticCanonicalAuxiliaryState carrierFuel,
      ∀ target : source.AromaticCanonicalOccurrence carrierFuel,
        state target =
          source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
            (source.aromaticCanonicalWholeStateReader state) target
            (2 * (carrierFuel + 1)) := by
  obtain ⟨state, model, unique⟩ :=
    source.existsUnique_aromaticCanonicalOccurrenceRule3Through5Model
      carrierFuel (2 * (carrierFuel + 1))
  refine ⟨state, ?_, ?_⟩
  · intro target
    exact
      source.aromaticCanonicalOccurrenceRule3Through5Model_eq_descriptorWithRead?_of_wholeState
        state model target
  · intro other otherFixed
    exact unique other
      ((source.cipModel_iff_wholeState_fixedPoint carrierFuel other).mpr otherFixed)

/-- Any whole-state fixed point is the generated legacy scheduler reference state.  This is the
public scheduler decode of the accepted legacy Rule-3--5 backend; it is **not** the corrected
Rule-4a-prefixed backend, which is owned elsewhere.  The proof applies shipped uniqueness to both
the given fixed point and the scheduler-closure model. -/
theorem wholeState_fixedPoint_eq_scheduledAuxiliaryState
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (fixed : ∀ target : source.AromaticCanonicalOccurrence carrierFuel,
      state target =
        source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
          (source.aromaticCanonicalWholeStateReader state) target
          (2 * (carrierFuel + 1))) :
    state =
      source.aromaticCanonicalScheduledAuxiliaryState
        (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
          carrierFuel (2 * (carrierFuel + 1))) := by
  obtain ⟨canonical, _canonicalModel, unique⟩ :=
    source.existsUnique_aromaticCanonicalOccurrenceRule3Through5Model
      carrierFuel (2 * (carrierFuel + 1))
  have stateEq : state = canonical :=
    unique state
      ((source.cipModel_iff_wholeState_fixedPoint carrierFuel state).mpr fixed)
  have scheduledEq :
      source.aromaticCanonicalScheduledAuxiliaryState
          (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
            carrierFuel (2 * (carrierFuel + 1))) = canonical :=
    unique _
      (source.aromaticCanonicalScheduledAuxiliaryState_cipModel
        (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
          carrierFuel (2 * (carrierFuel + 1))))
  exact stateEq.trans scheduledEq.symm

end AuthoritativeChemicalInput
end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.AromaticCanonicalOccurrenceRule3Through5WholeStateFixedPoint
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5WholeStateFixedPoint_iff
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.cipModel_iff_wholeState_fixedPoint
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.existsUnique_wholeState_fixedPoint
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.wholeState_fixedPoint_eq_scheduledAuxiliaryState
