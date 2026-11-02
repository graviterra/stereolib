import TetraStereo.KernelOnly
import TetraStereo.OneCenter.LocalizedUniversalSemanticClosure
import TetraStereo.OneCenter.LocalizedUniversalRule3NumericBound

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

open TetraStereo.Certificate.WeightedDemand

















































/-! ## Operational success implies an acyclic computed base -/










theorem exists_computedBase_acyclic_of_universalDescriptor?_eq_some
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.universalDescriptor? target view = some descriptor) :
    ∃ base : input.LocalizedOccurrenceFourLigandFrame carrierFuel,
      input.localizedNoDoubleFourLigandFrameExec? target = some base ∧
        Acyclic (input.preflightExtendedWeightedDemandGraph carrierFuel) base.cursors := by
  obtain ⟨base, baseComputed, _meaning⟩ :=
    input.universalDescriptor?_sound target view descriptor computed
  refine ⟨base, baseComputed, ?_⟩
  cases prepared : input.preparePreflightExtendedDemandPlan base.cursors with
  | ok plan =>
      exact (input.preparePreflightExtendedDemandPlan_success_iff_acyclic base.cursors).mp
        ⟨plan, prepared⟩
  | error failure =>
      have refused := input.universalDescriptor?_eq_none_of_prepare_error
        target view base baseComputed failure prepared
      rw [refused] at computed
      cases computed

/-! ## Independent derivations imply an acyclic computed base -/

/-- **Main concrete closure.**  Every independent declarative universal descriptor at *any*
Rule-3 evaluation budget, for the selected occurrence and its dependency view, produces the
actual computed four-ligand base and acyclicity of the preflight-pruned demand graph reachable
from that base's cursors.

The declarative premise is not derived here: the theorem states that an existing independent
derivation induces the executable termination certificate.  It is not an input-only
applicability statement. -/
theorem exists_computedBase_acyclic_of_declarativeUniversalDescriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evaluationBudget : Nat) (descriptor : LocalizedAuxiliaryLabel)
    (derived : input.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
      evaluationBudget descriptor) :
    ∃ base : input.LocalizedOccurrenceFourLigandFrame carrierFuel,
      input.localizedNoDoubleFourLigandFrameExec? target = some base ∧
        Acyclic (input.preflightExtendedWeightedDemandGraph carrierFuel) base.cursors := by
  have universal : input.universalDescriptor? target view = some descriptor :=
    (input.universalDescriptor?_eq_some_iff_exists_declarativeUniversalDescriptor_of_derived
      target view descriptor).mpr ⟨evaluationBudget, derived⟩
  exact input.exists_computedBase_acyclic_of_universalDescriptor?_eq_some
    target view descriptor universal

/-! ## The computed bound is the input-derived numeric budget's lower range -/

/-- The same independent derivation, now with the full quantitative certificate for the actual
computed base:

* the four-ligand base is the one actually returned by the executable reader;
* the preflight-pruned demand graph on its cursors is acyclic;
* the preparation's own computed bound is at most the input-derived numeric budget
  `universalRule3EvaluationBound carrierFuel`;
* the independent declarative meaning holds at that *computed* bound.

The last two components are `universalDescriptor?_sound` together with the numeric bound
`prepareUniversalRule3EvaluationOutcome_bound_le_universal`. -/
theorem exists_computedBase_acyclic_and_bound_le_of_declarativeUniversalDescriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evaluationBudget : Nat) (descriptor : LocalizedAuxiliaryLabel)
    (derived : input.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
      evaluationBudget descriptor) :
    ∃ base : input.LocalizedOccurrenceFourLigandFrame carrierFuel,
      input.localizedNoDoubleFourLigandFrameExec? target = some base ∧
        Acyclic (input.preflightExtendedWeightedDemandGraph carrierFuel) base.cursors ∧
        (prepareUniversalRule3EvaluationOutcome input base.cursors target view).1 ≤
          input.universalRule3EvaluationBound carrierFuel ∧
        input.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
          (prepareUniversalRule3EvaluationOutcome input base.cursors target view).1
          descriptor := by
  have universal : input.universalDescriptor? target view = some descriptor :=
    (input.universalDescriptor?_eq_some_iff_exists_declarativeUniversalDescriptor_of_derived
      target view descriptor).mpr ⟨evaluationBudget, derived⟩
  obtain ⟨base, baseComputed, meaning⟩ :=
    input.universalDescriptor?_sound target view descriptor universal
  have acyclic :
      Acyclic (input.preflightExtendedWeightedDemandGraph carrierFuel) base.cursors := by
    cases prepared : input.preparePreflightExtendedDemandPlan base.cursors with
    | ok plan =>
        exact (input.preparePreflightExtendedDemandPlan_success_iff_acyclic base.cursors).mp
          ⟨plan, prepared⟩
    | error failure =>
        have refused := input.universalDescriptor?_eq_none_of_prepare_error
          target view base baseComputed failure prepared
        rw [refused] at universal
        cases universal
  exact ⟨base, baseComputed, acyclic,
    input.prepareUniversalRule3EvaluationOutcome_bound_le_universal
      base.cursors target view,
    meaning⟩

/-! ## Actual evaluator termination at the input-derived budget -/

/-- The independent derivation makes the actual extended Rule-3 frame evaluator return a frame on
the computed base at the explicit input-derived budget `universalRule3EvaluationBound carrierFuel`.

The proof observes that the universal descriptor is successful, so the prepared optional frame
cannot be `none`; equality at the universal budget
(`buildLocalizedExtendedShortCircuitRule3FrameExec?_universalBound_eq_universalOutcome`) then
transports that success to the actual evaluator. -/
theorem exists_computedBase_acyclic_and_frame_some_at_universalBound_of_declarativeUniversalDescriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evaluationBudget : Nat) (descriptor : LocalizedAuxiliaryLabel)
    (derived : input.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
      evaluationBudget descriptor) :
    ∃ (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
      (frame : input.LocalizedRule3CanonicalKeyFrame),
      input.localizedNoDoubleFourLigandFrameExec? target = some base ∧
        Acyclic (input.preflightExtendedWeightedDemandGraph carrierFuel) base.cursors ∧
        input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view
          (input.universalRule3EvaluationBound carrierFuel) base.cursors = some frame := by
  have universal : input.universalDescriptor? target view = some descriptor :=
    (input.universalDescriptor?_eq_some_iff_exists_declarativeUniversalDescriptor_of_derived
      target view descriptor).mpr ⟨evaluationBudget, derived⟩
  obtain ⟨base, baseComputed, _meaning⟩ :=
    input.universalDescriptor?_sound target view descriptor universal
  have acyclic :
      Acyclic (input.preflightExtendedWeightedDemandGraph carrierFuel) base.cursors := by
    cases prepared : input.preparePreflightExtendedDemandPlan base.cursors with
    | ok plan =>
        exact (input.preparePreflightExtendedDemandPlan_success_iff_acyclic base.cursors).mp
          ⟨plan, prepared⟩
    | error failure =>
        have refused := input.universalDescriptor?_eq_none_of_prepare_error
          target view base baseComputed failure prepared
        rw [refused] at universal
        cases universal
  have frameSome :
      ∃ frame : input.LocalizedRule3CanonicalKeyFrame,
        (prepareUniversalRule3EvaluationOutcome input base.cursors target view).2 = some frame := by
    cases prepared : (prepareUniversalRule3EvaluationOutcome input base.cursors target view).2 with
    | none =>
        exfalso
        have frameNone :
            (prepareUniversalRule3EvaluationOutcome input base.cursors target view).2 = none :=
          prepared
        have refused : input.universalDescriptor? target view = none := by
          unfold universalDescriptor? universalDescriptorOutcome
          cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
          | none => simp
          | some center =>
              cases baseCase : input.localizedNoDoubleFourLigandFrameExec? target with
              | none => simp
              | some found =>
                  rw [baseComputed] at baseCase
                  cases baseCase
                  unfold descriptorFromFrame?
                  simp [frameNone]
        rw [refused] at universal
        cases universal
    | some frame => exact ⟨frame, rfl⟩
  obtain ⟨frame, frameEq⟩ := frameSome
  refine ⟨base, frame, baseComputed, acyclic, ?_⟩
  rw [input.buildLocalizedExtendedShortCircuitRule3FrameExec?_universalBound_eq_universalOutcome
    base.cursors target view, frameEq]

/-! ## Production equality under the explicit budget inequality -/

/-- Under the explicit side condition that the input-derived universal budget fits inside the
fixed production fuel, the universal descriptor equals the existing production descriptor at the
selected target and view.  No unconditional production-fuel domination is asserted. -/
theorem universalDescriptor?_eq_productionDescriptor?_of_universalBound_le
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (enough : input.universalRule3EvaluationBound carrierFuel ≤
      localizedDescriptorBearingRule3EvaluationFuel carrierFuel) :
    input.universalDescriptor? target view =
      input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? target view := by
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none =>
      rw [input.universalDescriptor?_eq_none_of_center_none target view centerComputed]
      unfold localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
        localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?
      simp [centerComputed]
  | some center =>
      cases baseComputed : input.localizedNoDoubleFourLigandFrameExec? target with
      | none =>
          rw [input.universalDescriptor?_eq_none_of_base_none target view baseComputed]
          unfold localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
            localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?
          simp [centerComputed, baseComputed]
      | some base =>
          have agree := input.universalDescriptor?_eq_descriptorAt?_of_bound_le
            target view base baseComputed
            (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)
            (Nat.le_trans
              (input.prepareUniversalRule3EvaluationOutcome_bound_le_universal
                base.cursors target view)
              enough)
          rw [agree, input.descriptorAt?_production target view]

/-! ## Typed examples with the actual signatures -/

/-- Typed example: the core closure at the actual signature. -/
example (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evaluationBudget : Nat) (descriptor : LocalizedAuxiliaryLabel)
    (derived : input.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
      evaluationBudget descriptor) :
    ∃ base : input.LocalizedOccurrenceFourLigandFrame carrierFuel,
      input.localizedNoDoubleFourLigandFrameExec? target = some base ∧
        Acyclic (input.preflightExtendedWeightedDemandGraph carrierFuel) base.cursors :=
  input.exists_computedBase_acyclic_of_declarativeUniversalDescriptor
    target view evaluationBudget descriptor derived

/-- Typed example: the quantitative computed-bound certificate at the actual signature. -/
example (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evaluationBudget : Nat) (descriptor : LocalizedAuxiliaryLabel)
    (derived : input.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
      evaluationBudget descriptor) :
    ∃ base : input.LocalizedOccurrenceFourLigandFrame carrierFuel,
      input.localizedNoDoubleFourLigandFrameExec? target = some base ∧
        Acyclic (input.preflightExtendedWeightedDemandGraph carrierFuel) base.cursors ∧
        (prepareUniversalRule3EvaluationOutcome input base.cursors target view).1 ≤
          input.universalRule3EvaluationBound carrierFuel ∧
        input.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
          (prepareUniversalRule3EvaluationOutcome input base.cursors target view).1
          descriptor :=
  input.exists_computedBase_acyclic_and_bound_le_of_declarativeUniversalDescriptor
    target view evaluationBudget descriptor derived

/-- Typed example: actual evaluator success at the input-derived budget, at the actual
signature. -/
example (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evaluationBudget : Nat) (descriptor : LocalizedAuxiliaryLabel)
    (derived : input.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
      evaluationBudget descriptor) :
    ∃ (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
      (frame : input.LocalizedRule3CanonicalKeyFrame),
      input.localizedNoDoubleFourLigandFrameExec? target = some base ∧
        Acyclic (input.preflightExtendedWeightedDemandGraph carrierFuel) base.cursors ∧
        input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view
          (input.universalRule3EvaluationBound carrierFuel) base.cursors = some frame :=
  input.exists_computedBase_acyclic_and_frame_some_at_universalBound_of_declarativeUniversalDescriptor
    target view evaluationBudget descriptor derived

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-! ## Kernel-authority assertions for the decisive endpoints

`assert_kernel_only` (from `TetraStereo.KernelOnly`) allows exactly the standard logical
principles `propext`, `Classical.choice` and `Quot.sound`; it rejects `sorryAx`, project axioms
and native/compiler trust.  The five endpoints below are the decisive declarations of this
module.  The examples are anonymous and are checked by elaboration only. -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_computedBase_acyclic_of_universalDescriptor?_eq_some
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_computedBase_acyclic_of_declarativeUniversalDescriptor
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_computedBase_acyclic_and_bound_le_of_declarativeUniversalDescriptor
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_computedBase_acyclic_and_frame_some_at_universalBound_of_declarativeUniversalDescriptor
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.universalDescriptor?_eq_productionDescriptor?_of_universalBound_le
