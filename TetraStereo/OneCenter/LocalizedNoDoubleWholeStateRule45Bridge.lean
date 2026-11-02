import TetraStereo.OneCenter.LocalizedSingleBondDescriptorModelBridge
import TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity
import TetraStereo.OneCenter.LocalizedWholeStateDescriptorLocality
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false




















































namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput








theorem preparedUniversalDescriptor_eq_productionExtendedDescriptor_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    input.universalDescriptor? target view =
      input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? target view := by
  unfold universalDescriptor?
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none =>
      unfold universalDescriptorOutcome
        localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
        localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?
      simp only [instMonadOption, centerComputed, Option.bind_none]
  | some center =>
      cases baseComputed : input.localizedNoDoubleFourLigandFrameExec? target with
      | none =>
          unfold universalDescriptorOutcome
            localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
            localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?
          simp only [instMonadOption, centerComputed, baseComputed, Option.bind_none,
            Option.bind_some]
      | some base =>
          have frameComputed : input.localizedOccurrenceFourLigandFrame? target = some base := by
            rw [← input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?
              target]
            exact baseComputed
          have baseMeaning :=
            input.localizedOccurrenceFourLigandFrame?_sound target base frameComputed
          obtain ⟨keys, keysSome⟩ :=
            input.exists_buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame_of_noDoubleRecords
              noDouble target view base baseMeaning
          have frameSome :=
            input.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?_frame_computed
              target view base keys keysSome
          have buildIsSome :
              (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view
                (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)
                base.cursors).isSome = true := by
            rw [frameSome]
            rfl
          have preparedEq :
              (prepareUniversalRule3EvaluationOutcome input base.cursors target view).2 =
                some keys.rule3Frame := by
            rw [← input.universalFrameAgreement target view base baseComputed
              (localizedDescriptorBearingRule3EvaluationFuel carrierFuel) buildIsSome]
            exact frameSome
          rw [input.universalDescriptorOutcome_eq_prepared target view center base
            centerComputed baseComputed]
          dsimp only
          rw [preparedEq]
          rw [← input.descriptorAt?_production target view]
          unfold descriptorAt?
          simp only [instMonadOption, centerComputed, baseComputed, frameSome,
            Option.bind_some]




theorem preparedUniversalDescriptor_eq_rule45Descriptor_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    input.universalDescriptor? target view =
      input.localizedOccurrenceRule45Descriptor? target view :=
  (input.preparedUniversalDescriptor_eq_productionExtendedDescriptor_of_noDoubleRecords
      noDouble target view).trans
    (input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_eq_rule45Descriptor_of_noDoubleRecords
      noDouble target view)

/-- **Whole-state output versus the prepared universal descriptor** on a single-bond source.  The
geometry domain required by the full-state closure is derived from the source restriction, so the
equality is unconditional in every other respect. -/
theorem wholeStateUniversalEvaluator_eq_universalDescriptor_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel) :
    input.wholeStateUniversalEvaluator target state =
      input.universalDescriptor? target (input.localizedDependencyView state target) :=
  input.wholeStateUniversalEvaluator_eq_universalDescriptor target state
    (input.localizedRule3ExtendedNodeConditionalGeometryDomainAll_of_noDoubleRecords
      noDouble carrierFuel)

/-- **Whole-state output versus the actual production extended descriptor** at the state's own
dependency view. -/
theorem wholeStateUniversalEvaluator_eq_productionExtendedDescriptor_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel) :
    input.wholeStateUniversalEvaluator target state =
      input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? target
        (input.localizedDependencyView state target) :=
  (input.wholeStateUniversalEvaluator_eq_universalDescriptor_of_noDoubleRecords
      noDouble target state).trans
    (input.preparedUniversalDescriptor_eq_productionExtendedDescriptor_of_noDoubleRecords
      noDouble target (input.localizedDependencyView state target))

/-- **Whole-state output versus the bare Rules-4a--5 descriptor** at the state's own dependency
view.  This is the pointwise equation consumed by the model join below. -/
theorem wholeStateUniversalEvaluator_eq_rule45Descriptor_via_extended_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel) :
    input.wholeStateUniversalEvaluator target state =
      input.localizedOccurrenceRule45Descriptor? target
        (input.localizedDependencyView state target) :=
  (input.wholeStateUniversalEvaluator_eq_productionExtendedDescriptor_of_noDoubleRecords
      noDouble target state).trans
    (input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?_eq_rule45Descriptor_of_noDoubleRecords
      noDouble target (input.localizedDependencyView state target))

end CertifiedLocalizedCIPInput

/-! ## The actual whole-state universal model is a bare Rule-45 model -/

namespace LocalizedUniversalReference

open CertifiedLocalizedCIPInput

/-- **The actual whole-state universal model is exactly the canonical Rule-45 whole-state fixed
point.**  The forward direction rewrites each local output to the bare Rules-4a--5 descriptor at
the state's own view and uses the unconditional whole-state/restricted descriptor locality; the
reverse direction is the same pointwise equation read backwards. -/
theorem wholeStateUniversalModel_iff_bareRule45FixedPoint_of_noDoubleRecords
    (input : Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (state : input.certified.LocalizedAuxiliaryState (carrierFuel input)) :
    WholeStateUniversalModel input state ↔
      input.certified.LocalizedWholeStateRule45FixedPoint (carrierFuel input) state := by
  unfold WholeStateUniversalModel
  unfold CertifiedLocalizedCIPInput.LocalizedWholeStateRule45FixedPoint
  unfold CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateStep
  constructor
  · intro model
    funext target
    change input.certified.localizedOccurrenceRule45WholeStateDescriptor? target state =
      state target
    rw [input.certified.localizedOccurrenceRule45WholeStateDescriptor?_eq_restricted target state]
    exact
      (CertifiedLocalizedCIPInput.wholeStateUniversalEvaluator_eq_rule45Descriptor_via_extended_of_noDoubleRecords
        input.certified noDouble target state).symm.trans (model target)
  · intro fixed target
    have fixedTarget :
        input.certified.localizedOccurrenceRule45WholeStateDescriptor? target state =
          state target :=
      congrFun fixed target
    rw [input.certified.localizedOccurrenceRule45WholeStateDescriptor?_eq_restricted target state]
      at fixedTarget
    exact
      (CertifiedLocalizedCIPInput.wholeStateUniversalEvaluator_eq_rule45Descriptor_via_extended_of_noDoubleRecords
        input.certified noDouble target state).trans fixedTarget

/-- **The actual whole-state universal model is exactly the canonical Rule-45 `CIPModel`.**  This
is the whole-state fixed-point/CIPModel equivalence of `LocalizedWholeStateDescriptorLocality`,
whose descriptor-agreement premise is discharged unconditionally. -/
theorem wholeStateUniversalModel_iff_bareRule45CIPModel_of_noDoubleRecords
    (input : Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (state : input.certified.LocalizedAuxiliaryState (carrierFuel input)) :
    WholeStateUniversalModel input state ↔
      (input.certified.localizedAuxiliaryOccurrenceSystem
        (input.certified.localizedOccurrenceRule45AuxiliarySemantics
          (carrierFuel input))).CIPModel state :=
  (wholeStateUniversalModel_iff_bareRule45FixedPoint_of_noDoubleRecords
      input noDouble state).trans
    (input.certified.localizedOccurrenceRule45WholeStateFixedPoint_iff_cipModel_unconditional
      (carrierFuel input) state)

/-- **The actual whole-state universal model is exactly the bare executable Rule-45 fixed point.**
The whole-state Step is the restricted executable Step of the bare Rules-4a--5 evaluator, with no
descriptor-agreement premise left. -/
theorem wholeStateUniversalModel_iff_bareRule45ExecutableStep_fixed_of_noDoubleRecords
    (input : Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (state : input.certified.LocalizedAuxiliaryState (carrierFuel input)) :
    WholeStateUniversalModel input state ↔
      input.certified.localizedExecutableStep (fuel := carrierFuel input)
        input.certified.localizedOccurrenceRule45Descriptor? state = state := by
  rw [wholeStateUniversalModel_iff_bareRule45FixedPoint_of_noDoubleRecords input noDouble state]
  unfold CertifiedLocalizedCIPInput.LocalizedWholeStateRule45FixedPoint
  rw [input.certified.localizedOccurrenceRule45WholeStateStep_eq_executableStep
    (carrierFuel input)
    (input.certified.localizedWholeStateRule45DescriptorAgreement (carrierFuel input))]

/-- **The actual whole-state universal model is exactly the production extended executable step
fixed point.**  No new operator is introduced: `localizedExecutableStep` is the existing lift of a
restricted evaluator, applied to the actual production extended descriptor. -/
theorem wholeStateUniversalModel_iff_productionExtendedStep_fixed_of_noDoubleRecords
    (input : Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (state : input.certified.LocalizedAuxiliaryState (carrierFuel input)) :
    WholeStateUniversalModel input state ↔
      input.certified.localizedExecutableStep (fuel := carrierFuel input)
        input.certified.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? state =
        state := by
  unfold WholeStateUniversalModel
  unfold CertifiedLocalizedCIPInput.localizedExecutableStep
  constructor
  · intro model
    funext target
    exact
      (CertifiedLocalizedCIPInput.wholeStateUniversalEvaluator_eq_productionExtendedDescriptor_of_noDoubleRecords
        input.certified noDouble target state).symm.trans (model target)
  · intro fixed target
    have atTarget := congrFun fixed target
    exact
      (CertifiedLocalizedCIPInput.wholeStateUniversalEvaluator_eq_productionExtendedDescriptor_of_noDoubleRecords
        input.certified noDouble target state).trans atTarget

/-! ## The generated reference state satisfies the bare models -/

/-- The generated reference state is a fixed point of the canonical Rule-45 whole-state Step. -/
theorem referenceState_bareRule45FixedPoint_of_noDoubleRecords
    (input : Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords) :
    input.certified.LocalizedWholeStateRule45FixedPoint (carrierFuel input)
      (referenceState input) :=
  (wholeStateUniversalModel_iff_bareRule45FixedPoint_of_noDoubleRecords input noDouble
    (referenceState input)).mp
    (LocalizedWholeStateModelNonvacuity.wholeStateUniversalModel_referenceState_of_noDoubleRecords
      input noDouble)

/-- The generated reference state is a canonical Rule-45 `CIPModel`. -/
theorem referenceState_bareRule45CIPModel_of_noDoubleRecords
    (input : Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords) :
    (input.certified.localizedAuxiliaryOccurrenceSystem
      (input.certified.localizedOccurrenceRule45AuxiliarySemantics
        (carrierFuel input))).CIPModel (referenceState input) :=
  (wholeStateUniversalModel_iff_bareRule45CIPModel_of_noDoubleRecords input noDouble
    (referenceState input)).mp
    (LocalizedWholeStateModelNonvacuity.wholeStateUniversalModel_referenceState_of_noDoubleRecords
      input noDouble)

/-- The generated reference state is a fixed point of the bare executable Rule-45 step. -/
theorem referenceState_bareRule45ExecutableStep_fixed_of_noDoubleRecords
    (input : Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords) :
    input.certified.localizedExecutableStep (fuel := carrierFuel input)
      input.certified.localizedOccurrenceRule45Descriptor? (referenceState input) =
        referenceState input :=
  (wholeStateUniversalModel_iff_bareRule45ExecutableStep_fixed_of_noDoubleRecords input noDouble
    (referenceState input)).mp
    (LocalizedWholeStateModelNonvacuity.wholeStateUniversalModel_referenceState_of_noDoubleRecords
      input noDouble)

/-- The generated reference state is a fixed point of the production extended executable step. -/
theorem referenceState_productionExtendedStep_fixed_of_noDoubleRecords
    (input : Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords) :
    input.certified.localizedExecutableStep (fuel := carrierFuel input)
      input.certified.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
      (referenceState input) = referenceState input :=
  (wholeStateUniversalModel_iff_productionExtendedStep_fixed_of_noDoubleRecords input noDouble
    (referenceState input)).mp
    (LocalizedWholeStateModelNonvacuity.wholeStateUniversalModel_referenceState_of_noDoubleRecords
      input noDouble)

/-- **Pointwise bare Rule-45 model of the generated reference state.**  Each occurrence is exactly
what the bare Rules-4a--5 descriptor computes from the reference state's own dependency view. -/
theorem referenceState_eq_bareRule45Descriptor_of_noDoubleRecords
    (input : Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : Occurrence input) :
    referenceState input target =
      input.certified.localizedOccurrenceRule45Descriptor? target
        (input.certified.localizedDependencyView (referenceState input) target) :=
  (LocalizedWholeStateModelNonvacuity.wholeStateUniversalModel_referenceState_of_noDoubleRecords
      input noDouble target).symm.trans
    (CertifiedLocalizedCIPInput.wholeStateUniversalEvaluator_eq_rule45Descriptor_via_extended_of_noDoubleRecords
      input.certified noDouble target (referenceState input))

/-- **Pointwise production extended descriptor model of the generated reference state.** -/
theorem referenceState_eq_productionExtendedDescriptor_of_noDoubleRecords
    (input : Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : Occurrence input) :
    referenceState input target =
      input.certified.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? target
        (input.certified.localizedDependencyView (referenceState input) target) :=
  (LocalizedWholeStateModelNonvacuity.wholeStateUniversalModel_referenceState_of_noDoubleRecords
      input noDouble target).symm.trans
    (CertifiedLocalizedCIPInput.wholeStateUniversalEvaluator_eq_productionExtendedDescriptor_of_noDoubleRecords
      input.certified noDouble target (referenceState input))

/-- **Pointwise prepared universal descriptor model of the generated reference state.**  This
statement is unconditional: it is the reference equation composed with the existing identification
of the pipeline evaluator with the universal descriptor. -/
theorem referenceState_eq_preparedUniversalDescriptor
    (input : Input) (target : Occurrence input) :
    referenceState input target =
      input.certified.universalDescriptor? target
        (input.certified.localizedDependencyView (referenceState input) target) := by
  have equation := reference_equation input target
  rw [evaluator_eq_universalDescriptor_apply input (carrierFuel input) target
    (input.certified.localizedDependencyView (referenceState input) target)] at equation
  exact equation.symm

/-! ## Uniqueness of the bare models -/

/-- Any canonical Rule-45 `CIPModel` of the carrier is the generated reference state, with no
geometry assumption and no candidate-reference premise. -/
theorem eq_referenceState_of_bareRule45CIPModel_of_noDoubleRecords
    (input : Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {state : input.certified.LocalizedAuxiliaryState (carrierFuel input)}
    (model : (input.certified.localizedAuxiliaryOccurrenceSystem
      (input.certified.localizedOccurrenceRule45AuxiliarySemantics
        (carrierFuel input))).CIPModel state) :
    state = referenceState input :=
  LocalizedWholeStateModelNonvacuity.wholeStateUniversalModel_eq_referenceState_of_noDoubleRecords
    input state noDouble
    ((wholeStateUniversalModel_iff_bareRule45CIPModel_of_noDoubleRecords input noDouble state).mpr
      model)

/-- Any fixed point of the bare executable Rule-45 step is the generated reference state. -/
theorem eq_referenceState_of_bareRule45ExecutableStep_fixed_of_noDoubleRecords
    (input : Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {state : input.certified.LocalizedAuxiliaryState (carrierFuel input)}
    (fixed : input.certified.localizedExecutableStep (fuel := carrierFuel input)
      input.certified.localizedOccurrenceRule45Descriptor? state = state) :
    state = referenceState input :=
  LocalizedWholeStateModelNonvacuity.wholeStateUniversalModel_eq_referenceState_of_noDoubleRecords
    input state noDouble
    ((wholeStateUniversalModel_iff_bareRule45ExecutableStep_fixed_of_noDoubleRecords input noDouble
      state).mpr fixed)

/-- Any fixed point of the production extended executable step is the generated reference
state. -/
theorem eq_referenceState_of_productionExtendedStep_fixed_of_noDoubleRecords
    (input : Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {state : input.certified.LocalizedAuxiliaryState (carrierFuel input)}
    (fixed : input.certified.localizedExecutableStep (fuel := carrierFuel input)
      input.certified.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? state =
        state) :
    state = referenceState input :=
  LocalizedWholeStateModelNonvacuity.wholeStateUniversalModel_eq_referenceState_of_noDoubleRecords
    input state noDouble
    ((wholeStateUniversalModel_iff_productionExtendedStep_fixed_of_noDoubleRecords input noDouble
      state).mpr fixed)

end LocalizedUniversalReference

end TetraStereo.OneCenter

-- Kernel-authority certificates for the exported surface.

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.preparedUniversalDescriptor_eq_productionExtendedDescriptor_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.preparedUniversalDescriptor_eq_rule45Descriptor_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.wholeStateUniversalEvaluator_eq_universalDescriptor_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.wholeStateUniversalEvaluator_eq_productionExtendedDescriptor_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.wholeStateUniversalEvaluator_eq_rule45Descriptor_via_extended_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.wholeStateUniversalModel_iff_bareRule45FixedPoint_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.wholeStateUniversalModel_iff_bareRule45CIPModel_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.wholeStateUniversalModel_iff_bareRule45ExecutableStep_fixed_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.wholeStateUniversalModel_iff_productionExtendedStep_fixed_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.referenceState_bareRule45FixedPoint_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.referenceState_bareRule45CIPModel_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.referenceState_bareRule45ExecutableStep_fixed_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.referenceState_productionExtendedStep_fixed_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.referenceState_eq_bareRule45Descriptor_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.referenceState_eq_productionExtendedDescriptor_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.referenceState_eq_preparedUniversalDescriptor
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.eq_referenceState_of_bareRule45CIPModel_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.eq_referenceState_of_bareRule45ExecutableStep_fixed_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.eq_referenceState_of_productionExtendedStep_fixed_of_noDoubleRecords
