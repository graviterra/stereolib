import TetraStereo.OneCenter.LocalizedWholeStateExtendedDescriptorClosure
import TetraStereo.OneCenter.LocalizedPlanarAxisGeometryDomain
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false



















































namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

open TetraStereo.Certificate.WeightedDemand

/-! ## The actual full-state universal entry point -/











noncomputable def wholeStateUniversalDescriptorOutcome
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel) :
    Nat × Option LocalizedAuxiliaryLabel :=
  match input.localizedOccurrenceDescriptorCenter? target with
  | none => (0, none)
  | some _center =>
      match input.localizedNoDoubleFourLigandFrameExec? target with
      | none => (0, none)
      | some base =>
          let outcome := prepareUniversalRule3EvaluationOutcome input base.cursors target
            (input.localizedDependencyView state target)
          (outcome.1, input.descriptorAtWholeState? target state outcome.1)

/-- The actual full-state universal descriptor: the second component of
`wholeStateUniversalDescriptorOutcome`.  Its value is computed by `descriptorAtWholeState?` at the
preparation bound, hence by both full-reader stages (Rule 3 and Rules 4a--5). -/
noncomputable def wholeStateUniversalEvaluator
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel) :
    Option LocalizedAuxiliaryLabel :=
  (input.wholeStateUniversalDescriptorOutcome target state).2

/-! ## Exact agreement with the existing universal descriptor -/

/-- In the present centre/base branch the outcome is the prepared bound paired with the actual
whole-state descriptor evaluated at exactly that bound. -/
theorem wholeStateUniversalDescriptorOutcome_eq_prepared
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (center : input.TetrahedralCenter)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (centerComputed : input.localizedOccurrenceDescriptorCenter? target = some center)
    (baseComputed : input.localizedNoDoubleFourLigandFrameExec? target = some base) :
    input.wholeStateUniversalDescriptorOutcome target state =
      ((prepareUniversalRule3EvaluationOutcome input base.cursors target
          (input.localizedDependencyView state target)).1,
        input.descriptorAtWholeState? target state
          (prepareUniversalRule3EvaluationOutcome input base.cursors target
            (input.localizedDependencyView state target)).1) := by
  unfold wholeStateUniversalDescriptorOutcome
  simp [centerComputed, baseComputed]










theorem wholeStateUniversalDescriptorOutcome_snd_eq_universalDescriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll
      (carrierFuel := carrierFuel)) :
    (input.wholeStateUniversalDescriptorOutcome target state).2 =
      input.universalDescriptor? target (input.localizedDependencyView state target) := by
  unfold wholeStateUniversalDescriptorOutcome
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none =>
      simp [centerComputed,
        input.universalDescriptor?_eq_none_of_center_none target
          (input.localizedDependencyView state target) centerComputed]
  | some center =>
      cases baseComputed : input.localizedNoDoubleFourLigandFrameExec? target with
      | none =>
          simp [centerComputed, baseComputed,
            input.universalDescriptor?_eq_none_of_base_none target
              (input.localizedDependencyView state target) baseComputed]
      | some base =>
          dsimp only
          exact (input.universalDescriptor?_eq_descriptorAtWholeState?_of_bound_le
            target state geometry base baseComputed
            (prepareUniversalRule3EvaluationOutcome input base.cursors target
              (input.localizedDependencyView state target)).1
            (Nat.le_refl _)).symm

/-- The evaluator form of the exact agreement theorem. -/
theorem wholeStateUniversalEvaluator_eq_universalDescriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll
      (carrierFuel := carrierFuel)) :
    input.wholeStateUniversalEvaluator target state =
      input.universalDescriptor? target (input.localizedDependencyView state target) :=
  input.wholeStateUniversalDescriptorOutcome_snd_eq_universalDescriptor
    target state geometry

/-! ## Preservation of the crisp refusal branches -/

/-- A refused actual whole-state Rule-3 frame is an exact refusal of the whole-state descriptor at
the same budget, for every present descriptor centre and four-ligand base. -/
theorem descriptorAtWholeState?_eq_none_of_frame_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (evaluationBudget : Nat)
    (baseComputed : input.localizedNoDoubleFourLigandFrameExec? target = some base)
    (refused : input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target
      (input.localizedDependencyView state target)
      (input.localizedWholeStateReader state) evaluationBudget base.cursors = none) :
    input.descriptorAtWholeState? target state evaluationBudget = none := by
  unfold descriptorAtWholeState? descriptorFromFrameWholeState?
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none => simp
  | some center =>
      cases baseCase : input.localizedNoDoubleFourLigandFrameExec? target with
      | none => simp
      | some found =>
          rw [baseComputed] at baseCase
          cases baseCase
          simp [refused]

/-- An absent descriptor centre is an exact full-state refusal. -/
theorem wholeStateUniversalEvaluator_eq_none_of_center_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (missing : input.localizedOccurrenceDescriptorCenter? target = none) :
    input.wholeStateUniversalEvaluator target state = none := by
  unfold wholeStateUniversalEvaluator wholeStateUniversalDescriptorOutcome
  simp [missing]

/-- An absent four-ligand base is an exact full-state refusal. -/
theorem wholeStateUniversalEvaluator_eq_none_of_base_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (missing : input.localizedNoDoubleFourLigandFrameExec? target = none) :
    input.wholeStateUniversalEvaluator target state = none := by
  unfold wholeStateUniversalEvaluator wholeStateUniversalDescriptorOutcome
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none => simp
  | some center => simp [missing]





theorem wholeStateUniversalEvaluator_eq_none_of_prepare_error
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (baseComputed : input.localizedNoDoubleFourLigandFrameExec? target = some base)
    (failure : DiscoveryFailure (input.LocalizedRerootCursor carrierFuel))
    (failed : input.preparePreflightExtendedDemandPlan base.cursors = .error failure)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll
      (carrierFuel := carrierFuel)) :
    input.wholeStateUniversalEvaluator target state = none := by
  have prepareEq :
      prepareUniversalRule3EvaluationOutcome input base.cursors target
        (input.localizedDependencyView state target) = (0, none) := by
    simp [prepareUniversalRule3EvaluationOutcome, failed]
  have execNone : input.buildLocalizedExtendedShortCircuitRule3FrameExec?
      target (input.localizedDependencyView state target) 0 base.cursors = none :=
    input.preparePreflightExtendedDemandPlan_error_allFuelRefusal base.cursors failure failed
      target (input.localizedDependencyView state target) 0
  have wholeNone : input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target
      (input.localizedDependencyView state target)
      (input.localizedWholeStateReader state) 0 base.cursors = none := by
    have correspondence :=
      input.buildLocalizedExtendedShortCircuitRule3Frame_wholeState_option_correspondence
        target state geometry 0 base.cursors
    rw [execNone] at correspondence
    cases wholeCase : input.buildLocalizedExtendedShortCircuitRule3FrameWithRead? target
        (input.localizedDependencyView state target)
        (input.localizedWholeStateReader state) 0 base.cursors with
    | none => rfl
    | some frame =>
        simp only [wholeCase, LocalizedRule3FrameOptionPhysicalCorrespondence] at correspondence
  have descriptorNone : input.descriptorAtWholeState? target state 0 = none :=
    input.descriptorAtWholeState?_eq_none_of_frame_none target state base 0 baseComputed wholeNone
  unfold wholeStateUniversalEvaluator wholeStateUniversalDescriptorOutcome
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none => rfl
  | some center =>
      cases baseCase : input.localizedNoDoubleFourLigandFrameExec? target with
      | none => rfl
      | some found =>
          rw [baseComputed] at baseCase
          cases baseCase
          simp [prepareEq, descriptorNone]






theorem wholeStateUniversalEvaluator_eq_universalDescriptor_of_axisCoordinateGeometryAll
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (domain : input.LocalizedRule3AxisCoordinateGeometryDomainAll) :
    input.wholeStateUniversalEvaluator target state =
      input.universalDescriptor? target (input.localizedDependencyView state target) :=
  input.wholeStateUniversalEvaluator_eq_universalDescriptor target state
    (input.localizedRule3ExtendedNodeConditionalGeometryDomainAll_of_axisCoordinateGeometryAll
      domain carrierFuel)

/-! ## Exact finite-budget and declarative characterizations -/

/-- **Exact success characterization against the actual full-state pipeline.**  The new evaluator
returns a descriptor exactly when some finite Rule-3 budget makes the actual whole-state descriptor
pipeline return that same descriptor.  No frame-success or base premise is used. -/
theorem wholeStateUniversalEvaluator_eq_some_iff_exists_descriptorAtWholeState?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll
      (carrierFuel := carrierFuel))
    (descriptor : LocalizedAuxiliaryLabel) :
    input.wholeStateUniversalEvaluator target state = some descriptor ↔
      ∃ evaluationBudget : Nat,
        input.descriptorAtWholeState? target state evaluationBudget = some descriptor := by
  constructor
  · intro computed
    rw [input.wholeStateUniversalEvaluator_eq_universalDescriptor target state geometry] at computed
    obtain ⟨base, evaluationBudget, _baseComputed, atSome⟩ :=
      input.universalDescriptor?_some_imp_exists_descriptorAt?_some
        target (input.localizedDependencyView state target) descriptor computed
    refine ⟨evaluationBudget, ?_⟩
    rw [input.descriptorAtWholeState?_eq_descriptorAt?_of_conditionalGeometry
      target state geometry evaluationBudget]
    exact atSome
  · rintro ⟨evaluationBudget, computed⟩
    rw [input.wholeStateUniversalEvaluator_eq_universalDescriptor target state geometry]
    have atView : input.descriptorAt? target
        (input.localizedDependencyView state target) evaluationBudget = some descriptor := by
      rw [← input.descriptorAtWholeState?_eq_descriptorAt?_of_conditionalGeometry
        target state geometry evaluationBudget]
      exact computed
    exact input.universalDescriptor?_eq_some_of_descriptorAt?_eq_some_of_agreement
      target (input.localizedDependencyView state target)
      (input.universalFrameAgreement target (input.localizedDependencyView state target))
      descriptor evaluationBudget atView

/-- **Exact refusal characterization against the actual full-state pipeline.**  The new evaluator
refuses exactly when every finite Rule-3 budget refuses in the actual whole-state pipeline.  This is
an operational refusal statement; it is not a chemical nonexistence claim. -/
theorem wholeStateUniversalEvaluator_eq_none_iff_forall_descriptorAtWholeState?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll
      (carrierFuel := carrierFuel)) :
    input.wholeStateUniversalEvaluator target state = none ↔
      ∀ evaluationBudget : Nat,
        input.descriptorAtWholeState? target state evaluationBudget = none := by
  constructor
  · intro computed evaluationBudget
    rw [input.wholeStateUniversalEvaluator_eq_universalDescriptor target state geometry] at computed
    have atView :=
      (input.universalDescriptor?_eq_none_iff_forall_descriptorAt?_eq_none
        target (input.localizedDependencyView state target)).mp computed evaluationBudget
    rw [input.descriptorAtWholeState?_eq_descriptorAt?_of_conditionalGeometry
      target state geometry evaluationBudget]
    exact atView
  · intro allNone
    rw [input.wholeStateUniversalEvaluator_eq_universalDescriptor target state geometry]
    apply (input.universalDescriptor?_eq_none_iff_forall_descriptorAt?_eq_none
      target (input.localizedDependencyView state target)).mpr
    intro evaluationBudget
    have wholeNone := allNone evaluationBudget
    rw [input.descriptorAtWholeState?_eq_descriptorAt?_of_conditionalGeometry
      target state geometry evaluationBudget] at wholeNone
    exact wholeNone

/-- **Exact independent declarative meaning of a positive full-state outcome.**  A positive value of
the new evaluator is exactly the existence of a finite Rule-3 budget carrying the existing
independent `DeclarativeLocalizedOccurrenceUniversalDescriptor` at the state's own dependency view.
No new declarative relation is introduced. -/
theorem wholeStateUniversalEvaluator_eq_some_iff_exists_declarativeUniversalDescriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll
      (carrierFuel := carrierFuel))
    (descriptor : LocalizedAuxiliaryLabel) :
    input.wholeStateUniversalEvaluator target state = some descriptor ↔
      ∃ evaluationBudget : Nat,
        input.DeclarativeLocalizedOccurrenceUniversalDescriptor target
          (input.localizedDependencyView state target) evaluationBudget descriptor := by
  rw [input.wholeStateUniversalEvaluator_eq_universalDescriptor target state geometry]
  exact input.universalDescriptor?_eq_some_iff_exists_declarativeUniversalDescriptor_of_derived
    target (input.localizedDependencyView state target) descriptor

/-- **Exact independent declarative refusal.**  A refusal of the new evaluator is exactly the
absence of any finite Rule-3 budget and label carrying the existing independent declarative
universal descriptor at the state's own dependency view. -/
theorem wholeStateUniversalEvaluator_eq_none_iff_forall_not_declarativeUniversalDescriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (geometry : input.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll
      (carrierFuel := carrierFuel)) :
    input.wholeStateUniversalEvaluator target state = none ↔
      ∀ (evaluationBudget : Nat) (descriptor : LocalizedAuxiliaryLabel),
        ¬ input.DeclarativeLocalizedOccurrenceUniversalDescriptor target
          (input.localizedDependencyView state target) evaluationBudget descriptor := by
  rw [input.wholeStateUniversalEvaluator_eq_universalDescriptor target state geometry]
  exact input.universalDescriptor?_eq_none_iff_forall_not_declarativeUniversalDescriptor_of_derived
    target (input.localizedDependencyView state target)

end CertifiedLocalizedCIPInput

/-! ## The actual full-state universal model -/

namespace LocalizedUniversalReference

open CertifiedLocalizedCIPInput





noncomputable def wholeStateUniversalStep (input : Input) :
    input.certified.LocalizedAuxiliaryState (carrierFuel input) →
      input.certified.LocalizedAuxiliaryState (carrierFuel input) :=
  fun state target => input.certified.wholeStateUniversalEvaluator target state

/-- The actual full-state universal model: at every carrier target the full-state universal
evaluator reproduces the stored outcome. -/
def WholeStateUniversalModel (input : Input)
    (state : input.certified.LocalizedAuxiliaryState (carrierFuel input)) : Prop :=
  ∀ target : Occurrence input,
    input.certified.wholeStateUniversalEvaluator target state = state target

/-- The model is exactly a fixed point of the actual full-state operator. -/
theorem wholeStateUniversalModel_iff_step_fixed
    (input : Input)
    (state : input.certified.LocalizedAuxiliaryState (carrierFuel input)) :
    WholeStateUniversalModel input state ↔
      wholeStateUniversalStep input state = state := by
  constructor
  · intro model
    funext target
    exact model target
  · intro fixed target
    exact congrFun fixed target

/-- **Equivalence with the existing independent semantic model.**  Under the explicit independent
conditional geometry domain, the actual full-state equation holds exactly when the stored outcomes
are the declaratively derivable labels at the state's own views in the sense of
`IndependentSemanticReferenceModel`.  No candidate state is assumed to be the reference state. -/
theorem wholeStateUniversalModel_iff_independentSemanticReferenceModel
    (input : Input)
    (state : input.certified.LocalizedAuxiliaryState (carrierFuel input))
    (geometry : input.certified.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll
      (carrierFuel := carrierFuel input)) :
    WholeStateUniversalModel input state ↔
      IndependentSemanticReferenceModel input state := by
  constructor
  · intro model target descriptor
    have operational : input.certified.wholeStateUniversalEvaluator target state =
        input.certified.universalDescriptor? target
          (input.certified.localizedDependencyView state target) :=
      input.certified.wholeStateUniversalEvaluator_eq_universalDescriptor
        target state geometry
    calc
      state target = some descriptor ↔
          input.certified.wholeStateUniversalEvaluator target state = some descriptor := by
        rw [model target]
      _ ↔ input.certified.universalDescriptor? target
            (input.certified.localizedDependencyView state target) = some descriptor := by
        rw [operational]
      _ ↔ ∃ evaluationBudget : Nat,
            input.certified.DeclarativeLocalizedOccurrenceUniversalDescriptor target
              (input.certified.localizedDependencyView state target)
              evaluationBudget descriptor :=
        input.certified.universalDescriptor?_eq_some_iff_exists_declarativeUniversalDescriptor_of_derived
          target (input.certified.localizedDependencyView state target) descriptor
  · intro model target
    have stateEq : state = referenceState input :=
      independentSemanticReferenceModel_unique input model
    rw [stateEq]
    rw [input.certified.wholeStateUniversalEvaluator_eq_universalDescriptor
      target (referenceState input) geometry]
    exact (evaluator_eq_universalDescriptor_apply input (carrierFuel input) target
      (input.certified.localizedDependencyView (referenceState input) target)).symm.trans
      (reference_equation input target)

/-- The generated universal reference state is an actual full-state fixed point. -/
theorem wholeStateUniversalModel_referenceState
    (input : Input)
    (geometry : input.certified.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll
      (carrierFuel := carrierFuel input)) :
    WholeStateUniversalModel input (referenceState input) := by
  intro target
  rw [input.certified.wholeStateUniversalEvaluator_eq_universalDescriptor
    target (referenceState input) geometry]
  exact (evaluator_eq_universalDescriptor_apply input (carrierFuel input) target
    (input.certified.localizedDependencyView (referenceState input) target)).symm.trans
    (reference_equation input target)

/-- **Uniqueness of the actual full-state model.**  Any state satisfying the genuine full-state
equation is the generated universal reference state.  The candidate is not assumed to be a
reference model; the proof derives the independent declarative model from the full-state equation
and uses the existing uniqueness theorem. -/
theorem wholeStateUniversalModel_eq_referenceState
    (input : Input)
    (state : input.certified.LocalizedAuxiliaryState (carrierFuel input))
    (geometry : input.certified.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll
      (carrierFuel := carrierFuel input))
    (model : WholeStateUniversalModel input state) :
    state = referenceState input :=
  independentSemanticReferenceModel_unique input
    ((wholeStateUniversalModel_iff_independentSemanticReferenceModel
      input state geometry).mp model)

/-- **Existence and uniqueness of the actual full-state universal model** under the independent
conditional geometry domain.  The witness is the generated operational `referenceState`; uniqueness
holds among all auxiliary states of the carrier. -/
theorem existsUnique_wholeStateUniversalModel
    (input : Input)
    (geometry : input.certified.LocalizedRule3ExtendedNodeConditionalGeometryDomainAll
      (carrierFuel := carrierFuel input)) :
    ∃! state : input.certified.LocalizedAuxiliaryState (carrierFuel input),
      WholeStateUniversalModel input state :=
  ⟨referenceState input, wholeStateUniversalModel_referenceState input geometry,
    fun state model =>
      wholeStateUniversalModel_eq_referenceState input state geometry model⟩



theorem wholeStateUniversalModel_iff_independentSemanticReferenceModel_of_axisCoordinateGeometryAll
    (input : Input)
    (state : input.certified.LocalizedAuxiliaryState (carrierFuel input))
    (domain : input.certified.LocalizedRule3AxisCoordinateGeometryDomainAll) :
    WholeStateUniversalModel input state ↔
      IndependentSemanticReferenceModel input state :=
  wholeStateUniversalModel_iff_independentSemanticReferenceModel input state
    (input.certified.localizedRule3ExtendedNodeConditionalGeometryDomainAll_of_axisCoordinateGeometryAll
      domain (carrierFuel input))

/-- **Coordinate-domain form of existence and uniqueness** of the actual full-state universal
model. -/
theorem existsUnique_wholeStateUniversalModel_of_axisCoordinateGeometryAll
    (input : Input)
    (domain : input.certified.LocalizedRule3AxisCoordinateGeometryDomainAll) :
    ∃! state : input.certified.LocalizedAuxiliaryState (carrierFuel input),
      WholeStateUniversalModel input state :=
  existsUnique_wholeStateUniversalModel input
    (input.certified.localizedRule3ExtendedNodeConditionalGeometryDomainAll_of_axisCoordinateGeometryAll
      domain (carrierFuel input))

end LocalizedUniversalReference

end TetraStereo.OneCenter

-- Kernel-authority certificates for the exported surface.

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.wholeStateUniversalDescriptorOutcome
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.wholeStateUniversalEvaluator
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.wholeStateUniversalDescriptorOutcome_eq_prepared
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.wholeStateUniversalDescriptorOutcome_snd_eq_universalDescriptor
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.wholeStateUniversalEvaluator_eq_universalDescriptor
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.wholeStateUniversalEvaluator_eq_universalDescriptor_of_axisCoordinateGeometryAll
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.descriptorAtWholeState?_eq_none_of_frame_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.wholeStateUniversalEvaluator_eq_none_of_center_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.wholeStateUniversalEvaluator_eq_none_of_base_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.wholeStateUniversalEvaluator_eq_none_of_prepare_error
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.wholeStateUniversalEvaluator_eq_some_iff_exists_descriptorAtWholeState?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.wholeStateUniversalEvaluator_eq_none_iff_forall_descriptorAtWholeState?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.wholeStateUniversalEvaluator_eq_some_iff_exists_declarativeUniversalDescriptor
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.wholeStateUniversalEvaluator_eq_none_iff_forall_not_declarativeUniversalDescriptor
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.wholeStateUniversalStep
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.WholeStateUniversalModel
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.wholeStateUniversalModel_iff_step_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.wholeStateUniversalModel_iff_independentSemanticReferenceModel
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.wholeStateUniversalModel_referenceState
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.wholeStateUniversalModel_eq_referenceState
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.existsUnique_wholeStateUniversalModel
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.wholeStateUniversalModel_iff_independentSemanticReferenceModel_of_axisCoordinateGeometryAll
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.existsUnique_wholeStateUniversalModel_of_axisCoordinateGeometryAll
