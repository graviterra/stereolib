import TetraStereo.OneCenter.LocalizedUniversalRule3NumericBound
import TetraStereo.OneCenter.LocalizedUniversalDescriptorEvaluation
import TetraStereo.OneCenter.LocalizedReferenceInput
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput








































































































/-! ## The production fuel policy -/

/-- Executable production fuel policy: the larger of the legacy descriptor-bearing production fuel
and the input-derived universal Rule-3 bound.  Both summands are `Nat`-valued functions of the input
and carrier fuel, so `Nat.max` is executable and the policy is input-derived.  No inequality between
the two summands is asserted. -/
def productionUniversalRule3EvaluationFuel (input : CertifiedLocalizedCIPInput)
    (carrierFuel : Nat) : Nat :=
  max (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)
    (input.universalRule3EvaluationBound carrierFuel)

/-- The policy is at least the legacy production fuel. -/
theorem localizedDescriptorBearingRule3EvaluationFuel_le_productionUniversal
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) :
    localizedDescriptorBearingRule3EvaluationFuel carrierFuel ≤
      input.productionUniversalRule3EvaluationFuel carrierFuel := by
  unfold productionUniversalRule3EvaluationFuel
  exact Nat.le_max_left _ _

/-- The policy is at least the input-derived universal bound. -/
theorem universalRule3EvaluationBound_le_productionUniversal
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) :
    input.universalRule3EvaluationBound carrierFuel ≤
      input.productionUniversalRule3EvaluationFuel carrierFuel := by
  unfold productionUniversalRule3EvaluationFuel
  exact Nat.le_max_right _ _

/-- Both lower bounds at once, the two facts the runtime proofs consume. -/
theorem productionUniversalRule3EvaluationFuel_spec
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) :
    localizedDescriptorBearingRule3EvaluationFuel carrierFuel ≤
        input.productionUniversalRule3EvaluationFuel carrierFuel ∧
      input.universalRule3EvaluationBound carrierFuel ≤
        input.productionUniversalRule3EvaluationFuel carrierFuel :=
  ⟨input.localizedDescriptorBearingRule3EvaluationFuel_le_productionUniversal carrierFuel,
    input.universalRule3EvaluationBound_le_productionUniversal carrierFuel⟩

/-- The executable shape of the policy: the maximum of the legacy fuel and the quadratic
occurrence-count bound.  This is a runtime read of the occurrence carrier length only. -/
theorem productionUniversalRule3EvaluationFuel_eq (input : CertifiedLocalizedCIPInput)
    (carrierFuel : Nat) :
    input.productionUniversalRule3EvaluationFuel carrierFuel =
      max (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)
        (2 * (input.universalRule3OccurrenceCount carrierFuel *
              (input.universalRule3OccurrenceCount carrierFuel + 1)) + 1) := by
  simp [productionUniversalRule3EvaluationFuel, universalRule3EvaluationBound,
    universalRule3CursorCard]

/-! ## The actual frame evaluator at the policy fuel -/

/-- **Unconditional frame agreement.**  At the production universal policy fuel, the actual
executable extended Rule-3 frame evaluator equals the universal outcome frame, for every root list,
target and dependency view.  The proof is the universal-bound agreement theorem plus
`Nat.le_max_right`; no inequality between the legacy fuel and the occurrence bound is used. -/
theorem buildLocalizedExtendedShortCircuitRule3FrameExec?_productionUniversalFuel_eq_universalOutcome
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (roots : List (input.LocalizedRerootCursor carrierFuel))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view
        (input.productionUniversalRule3EvaluationFuel carrierFuel) roots =
      (prepareUniversalRule3EvaluationOutcome input roots target view).2 :=
  input.buildLocalizedExtendedShortCircuitRule3FrameExec?_eq_universalOutcome_of_universalBound_le
    roots target view _ (input.universalRule3EvaluationBound_le_productionUniversal carrierFuel)

/-- **Success-adaptive adapter leaf.**  If the actual frame evaluator at the legacy production fuel
returns a frame, then the universal outcome is exactly that same frame.  The proof uses only
success monotonicity from the legacy fuel to the policy fuel and the unconditional agreement above.
No inequality between the legacy fuel and the universal bound appears, and no success of the legacy
fuel is assumed beyond the explicit `computed` hypothesis. -/
theorem prepareUniversalRule3EvaluationOutcome_eq_some_of_productionFrame_some
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (roots : List (input.LocalizedRerootCursor carrierFuel))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view
      (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) roots = some frame) :
    (prepareUniversalRule3EvaluationOutcome input roots target view).2 = some frame := by
  have atPolicy :
      input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view
        (input.productionUniversalRule3EvaluationFuel carrierFuel) roots = some frame :=
    input.buildLocalizedExtendedShortCircuitRule3FrameExec?_success_monotone_of_le
      target view roots
      (input.localizedDescriptorBearingRule3EvaluationFuel_le_productionUniversal carrierFuel)
      frame computed
  rw [input.buildLocalizedExtendedShortCircuitRule3FrameExec?_productionUniversalFuel_eq_universalOutcome
    roots target view] at atPolicy
  exact atPolicy

/-! ## The parameterized descriptor at the policy fuel -/

/-- The actual descriptor pipeline run at the production universal policy fuel.  It is the same
`descriptorAt?` used by the production pipeline: the same center and base readers, the same
extended Rule-3 frame evaluator at the policy budget, and the unchanged Rules-4a--5, tracked-order,
geometry and classification tail. -/
def productionUniversalDescriptor? (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) : Option LocalizedAuxiliaryLabel :=
  input.descriptorAt? target view
    (input.productionUniversalRule3EvaluationFuel carrierFuel)

/-- **Main descriptor agreement.**  At every target and view, the actual parameterized descriptor
at the policy fuel equals the universal descriptor.  This is the proof connecting the new actual
call to the already-proved universal evaluator.  The required budget comparison is discharged by
`Nat.le_trans` of the preparation bound against the universal bound and the universal bound against
the policy maximum.  No assumption on the legacy fuel is used. -/
theorem productionUniversalDescriptor?_eq_universalDescriptor?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    input.productionUniversalDescriptor? target view = input.universalDescriptor? target view := by
  unfold productionUniversalDescriptor?
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none =>
      rw [input.descriptorAt?_eq_none_of_center_none target view
        (input.productionUniversalRule3EvaluationFuel carrierFuel) centerComputed]
      exact (input.universalDescriptor?_eq_none_of_center_none target view
        centerComputed).symm
  | some center =>
      cases baseComputed : input.localizedNoDoubleFourLigandFrameExec? target with
      | none =>
          rw [input.descriptorAt?_eq_none_of_base_none target view
            (input.productionUniversalRule3EvaluationFuel carrierFuel) baseComputed]
          exact (input.universalDescriptor?_eq_none_of_base_none target view
            baseComputed).symm
      | some base =>
          exact (input.universalDescriptor?_eq_descriptorAt?_of_bound_le
            target view base baseComputed
            (input.productionUniversalRule3EvaluationFuel carrierFuel)
            (Nat.le_trans
              (input.prepareUniversalRule3EvaluationOutcome_bound_le_universal
                base.cursors target view)
              (input.universalRule3EvaluationBound_le_productionUniversal
                carrierFuel))).symm

/-- The adapter succeeds exactly when the universal descriptor succeeds. -/
theorem productionUniversalDescriptor?_eq_some_iff_universalDescriptor?_eq_some
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel) :
    input.productionUniversalDescriptor? target view = some descriptor ↔
      input.universalDescriptor? target view = some descriptor := by
  have agree := input.productionUniversalDescriptor?_eq_universalDescriptor? target view
  constructor
  · intro computed
    rwa [agree] at computed
  · intro computed
    rwa [← agree] at computed

/-- The adapter refuses exactly when the universal descriptor refuses. -/
theorem productionUniversalDescriptor?_eq_none_iff_universalDescriptor?_eq_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    input.productionUniversalDescriptor? target view = none ↔
      input.universalDescriptor? target view = none := by
  have agree := input.productionUniversalDescriptor?_eq_universalDescriptor? target view
  constructor
  · intro computed
    rwa [agree] at computed
  · intro computed
    rwa [← agree] at computed

/-- The operational success predicate of the adapter is exactly the universal one. -/
theorem productionUniversalDescriptor?_isSome_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    (input.productionUniversalDescriptor? target view).isSome =
      (input.universalDescriptor? target view).isSome := by
  have agree := input.productionUniversalDescriptor?_eq_universalDescriptor? target view
  exact congrArg Option.isSome agree

/-- **Legacy positive preservation.**  Every positive legacy production descriptor is reproduced
with the same label by the adapter at the policy fuel.  The proof rewrites the adapter to the
universal descriptor and applies the existing unconditional preservation theorem
`universalDescriptor?_eq_some_of_productionDescriptor?_eq_some`. -/
theorem productionUniversalDescriptor?_eq_some_of_productionDescriptor?_eq_some
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
      target view = some descriptor) :
    input.productionUniversalDescriptor? target view = some descriptor := by
  rw [input.productionUniversalDescriptor?_eq_universalDescriptor? target view]
  exact input.universalDescriptor?_eq_some_of_productionDescriptor?_eq_some
    target view descriptor computed

/-- Combined backward-compatibility statement: a positive legacy production descriptor is
reproduced by the adapter, and retains its independent legacy declarative meaning.  This is the
precise sense in which the policy preserves actual production semantics and admission. -/
theorem productionUniversalDescriptor?_preserves_production
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
      target view = some descriptor) :
    input.productionUniversalDescriptor? target view = some descriptor ∧
      input.DeclarativeLocalizedOccurrenceExtendedShortCircuitRule3Through5Descriptor
        target view descriptor :=
  ⟨input.productionUniversalDescriptor?_eq_some_of_productionDescriptor?_eq_some
      target view descriptor computed,
    input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_sound
      target view descriptor computed⟩

/-- **Soundness of the adapter.**  A positive adapter result at the policy fuel carries the
independent universal declarative meaning at that budget.  This is the declarative certificate for
outcomes that the legacy fuel refused. -/
theorem productionUniversalDescriptor?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.productionUniversalDescriptor? target view = some descriptor) :
    input.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
      (input.productionUniversalRule3EvaluationFuel carrierFuel) descriptor := by
  unfold productionUniversalDescriptor? at computed
  exact input.descriptorAt?_sound target view _ descriptor computed

/-! ## Budget monotonicity of the parameterized descriptor (general adapter leaf)

The descriptor pipeline shares its center and base readers across budgets; only the Rule-3 frame
budget changes.  Therefore a successful descriptor at a low budget is reproduced with the identical
label at every higher budget.  This is independent of the universal machinery and applies to any
pair of budgets. -/

/-- **General success monotonicity** of `descriptorAt?` in its evaluation budget.  The proof splits
the center and base readers, unfolds the shared descriptor tail, and applies the Rule-3 frame
success monotonicity at the only budget-dependent stage. -/
theorem descriptorAt?_success_monotone_of_le
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    {lowFuel highFuel : Nat} (le : lowFuel ≤ highFuel)
    (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.descriptorAt? target view lowFuel = some descriptor) :
    input.descriptorAt? target view highFuel = some descriptor := by
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none =>
      rw [input.descriptorAt?_eq_none_of_center_none target view lowFuel centerComputed] at computed
      cases computed
  | some center =>
      cases baseComputed : input.localizedNoDoubleFourLigandFrameExec? target with
      | none =>
          rw [input.descriptorAt?_eq_none_of_base_none target view lowFuel baseComputed] at computed
          cases computed
      | some base =>
          rw [input.descriptorAt?_eq_descriptorFromFrame?_of_some
            target view center base lowFuel centerComputed baseComputed] at computed
          rw [input.descriptorAt?_eq_descriptorFromFrame?_of_some
            target view center base highFuel centerComputed baseComputed]
          cases lowFrame : input.buildLocalizedExtendedShortCircuitRule3FrameExec?
              target view lowFuel base.cursors with
          | none =>
              rw [lowFrame] at computed
              rw [input.descriptorFromFrame?_none target view center base] at computed
              cases computed
          | some frame =>
              rw [lowFrame] at computed
              have highFrame :
                  input.buildLocalizedExtendedShortCircuitRule3FrameExec?
                    target view highFuel base.cursors = some frame :=
                input.buildLocalizedExtendedShortCircuitRule3FrameExec?_success_monotone_of_le
                  target view base.cursors le frame lowFrame
              rw [highFrame]
              exact computed

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput

namespace TetraStereo.OneCenter.LocalizedExtendedShortCircuit

open CertifiedLocalizedCIPInput

/-!
## The public evaluator adapter

`LocalizedExtendedShortCircuitPipeline.evaluator` is the actual public production evaluator; its
fuel is `carrierFuel input = input.molecule.atomCount + 1`.  The definition below is the same
restricted evaluator, routed through the universal-floored fuel policy and the parameterized
descriptor.  It is not a second solver: it calls the same `descriptorAt?` / extended Rule-3 frame
evaluator / descriptor tail, only at the policy budget.  Every positive result is either a
reproduced legacy production result (same label and same legacy declarative witness) or a
universal completion certified at the policy budget.
-/

/-- Production evaluator at the universal-floored fuel policy. -/
def universalFuelEvaluator (input : LocalizedReference.Input) (fuel : Nat) :
    input.certified.LocalizedRestrictedEvaluator fuel :=
  fun target view => input.certified.productionUniversalDescriptor? target view

/-- The adapter is definitionally the parameterized descriptor at the policy fuel. -/
theorem universalFuelEvaluator_eq_descriptorAt? (input : LocalizedReference.Input) (fuel : Nat) :
    universalFuelEvaluator input fuel =
      fun target view => input.certified.descriptorAt? target view
        (input.certified.productionUniversalRule3EvaluationFuel fuel) := by
  funext target view
  rfl

/-- The adapter is the universal descriptor at every target and view. -/
theorem universalFuelEvaluator_apply_eq_universalDescriptor (input : LocalizedReference.Input) (fuel : Nat)
    (target : input.certified.LocalizedCIPOccurrence fuel)
    (view : input.certified.LocalizedDependencyView target) :
    universalFuelEvaluator input fuel target view =
      input.certified.universalDescriptor? target view :=
  input.certified.productionUniversalDescriptor?_eq_universalDescriptor? target view

/-- The adapter, viewed as a function, is exactly the universal descriptor evaluator. -/
theorem universalFuelEvaluator_eq_universalDescriptor (input : LocalizedReference.Input) (fuel : Nat) :
    universalFuelEvaluator input fuel =
      fun target view => input.certified.universalDescriptor? target view := by
  funext target view
  exact universalFuelEvaluator_apply_eq_universalDescriptor input fuel target view

/-- **Positive preservation for the production descriptor.**  Every positive outcome of the legacy
production descriptor function — the body of the existing public production evaluator before any
integration patch — is reproduced with the same label by `universalFuelEvaluator`.  The statement is
phrased against the descriptor function rather than the pipeline's `evaluator` def, so it remains
valid whether or not the caller applies the proposed one-line evaluator patch. -/
theorem universalFuelEvaluator_eq_some_of_productionDescriptor?_eq_some
    (input : LocalizedReference.Input) (fuel : Nat)
    (target : input.certified.LocalizedCIPOccurrence fuel)
    (view : input.certified.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.certified.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
      target view = some descriptor) :
    universalFuelEvaluator input fuel target view = some descriptor :=
  input.certified.productionUniversalDescriptor?_eq_some_of_productionDescriptor?_eq_some
    target view descriptor computed

/-- Positive outcomes of the public adapter carry the universal declarative meaning at the policy
budget. -/
theorem universalFuelEvaluator_positive_sound (input : LocalizedReference.Input) (fuel : Nat)
    (target : input.certified.LocalizedCIPOccurrence fuel)
    (view : input.certified.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel)
    (computed : universalFuelEvaluator input fuel target view = some descriptor) :
    input.certified.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
      (input.certified.productionUniversalRule3EvaluationFuel fuel) descriptor :=
  input.certified.productionUniversalDescriptor?_sound target view descriptor computed

end TetraStereo.OneCenter.LocalizedExtendedShortCircuit

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.productionUniversalRule3EvaluationFuel_spec
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedExtendedShortCircuitRule3FrameExec?_productionUniversalFuel_eq_universalOutcome
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.prepareUniversalRule3EvaluationOutcome_eq_some_of_productionFrame_some
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.productionUniversalDescriptor?_eq_universalDescriptor?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.productionUniversalDescriptor?_preserves_production
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.productionUniversalDescriptor?_sound
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.descriptorAt?_success_monotone_of_le
assert_kernel_only TetraStereo.OneCenter.LocalizedExtendedShortCircuit.universalFuelEvaluator_eq_universalDescriptor
assert_kernel_only TetraStereo.OneCenter.LocalizedExtendedShortCircuit.universalFuelEvaluator_positive_sound
