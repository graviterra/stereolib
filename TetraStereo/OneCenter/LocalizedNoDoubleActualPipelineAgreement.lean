import TetraStereo.OneCenter.LocalizedNoDoubleWholeStateRule45Bridge
import TetraStereo.OneCenter.LocalizedPreparedReferencePipeline
import TetraStereo.OneCenter.LocalizedUniversalReferencePipeline
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option linter.unusedVariables false












































namespace TetraStereo.OneCenter

namespace LocalizedUniversalReference

open CertifiedLocalizedCIPInput Certificate.Dependency

/-! ## The two executable evaluators coincide -/





theorem evaluator_eq_extendedEvaluator_of_noDoubleRecords
    (input : Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (fuel : Nat) :
    evaluator input fuel = LocalizedExtendedShortCircuit.evaluator input fuel := by
  funext target view
  rw [evaluator_eq_universalDescriptor_apply input fuel target view]
  exact input.certified.preparedUniversalDescriptor_eq_productionExtendedDescriptor_of_noDoubleRecords
    noDouble target view

/-- Pointwise (application) form of `evaluator_eq_extendedEvaluator_of_noDoubleRecords`.  This is
the rewrite form for a single evaluator call at a given target and view. -/
theorem evaluator_apply_eq_extendedEvaluator_of_noDoubleRecords
    (input : Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (fuel : Nat) (target : input.certified.LocalizedCIPOccurrence fuel)
    (view : input.certified.LocalizedDependencyView target) :
    evaluator input fuel target view =
      LocalizedExtendedShortCircuit.evaluator input fuel target view :=
  congrFun (congrFun
    (evaluator_eq_extendedEvaluator_of_noDoubleRecords input noDouble fuel) target) view

/-! ## The actual generated reference states coincide -/

/-- **Generated reference-state agreement under the no-double source restriction.**  Both pipelines
state `reference_eq_boundedIteration` against the same bounded occurrence iteration, so evaluator
agreement gives equality of the actual generated states.  There is no supplied reader or
fixed-point hypothesis. -/
theorem referenceState_eq_extendedReferenceState_of_noDoubleRecords
    (input : Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords) :
    referenceState input = LocalizedExtendedShortCircuit.referenceState input := by
  rw [reference_eq_boundedIteration input,
    LocalizedExtendedShortCircuit.reference_eq_boundedIteration input,
    evaluator_eq_extendedEvaluator_of_noDoubleRecords input noDouble (carrierFuel input)]

/-- Pointwise form of `referenceState_eq_extendedReferenceState_of_noDoubleRecords`, for a single
occurrence of the shared carrier. -/
theorem referenceState_apply_eq_extendedReferenceState_of_noDoubleRecords
    (input : Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : Occurrence input) :
    referenceState input target = LocalizedExtendedShortCircuit.referenceState input target :=
  congrFun (referenceState_eq_extendedReferenceState_of_noDoubleRecords input noDouble) target

/-! ## Lookups of the facts returned by the runnable entry points -/

/-- **Any accepted or generated evaluation result reads the universal-reference state.**  This is
the existing checked-pipeline uniqueness `evaluation_eq_reference` composed with state agreement;
it covers both branches of `LocalizedExtendedShortCircuit.evaluate` without case analysis. -/
theorem evaluation_facts_eq_referenceState_of_noDoubleRecords
    (input : Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (result : LocalizedExtendedShortCircuit.Evaluation input) :
    lookup result.facts = referenceState input :=
  (LocalizedExtendedShortCircuit.evaluation_eq_reference input result).trans
    (referenceState_eq_extendedReferenceState_of_noDoubleRecords input noDouble).symm

/-- **The actual universal-reference entry point reads the production extended reference state.**
This is `evaluate_state` composed with state agreement, for either branch of `evaluate`. -/
theorem evaluate_facts_eq_extendedReferenceState_of_noDoubleRecords
    (input : Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (nodes : Nodes input) :
    lookup (evaluate input nodes).facts =
      LocalizedExtendedShortCircuit.referenceState input :=
  (evaluate_state input nodes).trans
    (referenceState_eq_extendedReferenceState_of_noDoubleRecords input noDouble)

end LocalizedUniversalReference

/-! ## Explicit corollaries for the two plain runnable entry points -/

namespace LocalizedExtendedShortCircuit

open CertifiedLocalizedCIPInput Certificate.Dependency

/-- **Both branches of the checked-pipeline `evaluate` read the universal-reference state.** -/
theorem evaluate_facts_eq_universalReferenceState_of_noDoubleRecords
    (input : Input) (nodes : Nodes input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords) :
    lookup (evaluate input nodes).facts =
      LocalizedUniversalReference.referenceState input :=
  LocalizedUniversalReference.evaluation_facts_eq_referenceState_of_noDoubleRecords
    input noDouble (evaluate input nodes)

end LocalizedExtendedShortCircuit

/-! ## The prepared producer -/

namespace LocalizedExtendedShortCircuit.PreparedPipeline

open CertifiedLocalizedCIPInput Certificate.Dependency

/-- **The actual prepared reference producer generates the universal-reference state.**  The
prepared state is the plain extended reference state (`preparedReferenceState_eq`, unconditional),
which on this source class is the universal-reference state.  The prepared producer used here is
the existing `preparedReferenceState` over `Prepared.Preparation`; it is not a second solver and
does not call the universal descriptor directly. -/
theorem preparedReferenceState_eq_universalReferenceState_of_noDoubleRecords
    (input : Input) (prep : Prepared.Preparation input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords) :
    preparedReferenceState input prep = LocalizedUniversalReference.referenceState input :=
  (preparedReferenceState_eq input prep).trans
    (LocalizedUniversalReference.referenceState_eq_extendedReferenceState_of_noDoubleRecords
      input noDouble).symm

/-- **The prepared fallback producer reads the universal-reference state.** -/
theorem preparedReferenceEvaluation_facts_eq_universalReferenceState_of_noDoubleRecords
    (input : Input) (prep : Prepared.Preparation input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords) :
    lookup (preparedReferenceEvaluation input prep).facts =
      LocalizedUniversalReference.referenceState input :=
  LocalizedUniversalReference.evaluation_facts_eq_referenceState_of_noDoubleRecords
    input noDouble (preparedReferenceEvaluation input prep)

/-- **Both branches of `evaluatePrepared` read the universal-reference state.**  The accepted branch
comes from the checked-pipeline uniqueness theorem, the rejected branch from the prepared fallback;
`evaluatePrepared` is a single definition, so the generic evaluation statement covers both. -/
theorem evaluatePrepared_facts_eq_universalReferenceState_of_noDoubleRecords
    (input : Input) (prep : Prepared.Preparation input) (nodes : Nodes input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords) :
    lookup (evaluatePrepared input prep nodes).facts =
      LocalizedUniversalReference.referenceState input :=
  LocalizedUniversalReference.evaluation_facts_eq_referenceState_of_noDoubleRecords
    input noDouble (evaluatePrepared input prep nodes)




theorem evaluate_facts_eq_universalReferenceState_of_noDoubleRecords
    (input : Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords) :
    lookup (evaluate input).facts =
      LocalizedUniversalReference.referenceState input :=
  LocalizedUniversalReference.evaluation_facts_eq_referenceState_of_noDoubleRecords
    input noDouble (evaluate input)

end LocalizedExtendedShortCircuit.PreparedPipeline

/-! ## The cached entry points -/

namespace LocalizedExtendedShortCircuit.Cached

open CertifiedLocalizedCIPInput Certificate.Dependency

/-- **Both branches of the cached `evaluate` read the universal-reference state.** -/
theorem evaluate_facts_eq_universalReferenceState_of_noDoubleRecords
    (input : Input) (nodes : Nodes input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords) :
    lookup (LocalizedExtendedShortCircuit.Cached.evaluate input nodes).facts =
      LocalizedUniversalReference.referenceState input :=
  LocalizedUniversalReference.evaluation_facts_eq_referenceState_of_noDoubleRecords
    input noDouble (LocalizedExtendedShortCircuit.Cached.evaluate input nodes)

/-- **The cached reference fallback reads the universal-reference state.** -/
theorem referenceUsingCache_facts_eq_universalReferenceState_of_noDoubleRecords
    (input : Input) (cache : RuntimeCache input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords) :
    lookup (referenceUsingCache input cache).facts =
      LocalizedUniversalReference.referenceState input :=
  LocalizedUniversalReference.evaluation_facts_eq_referenceState_of_noDoubleRecords
    input noDouble (referenceUsingCache input cache)

end LocalizedExtendedShortCircuit.Cached

end TetraStereo.OneCenter

-- Kernel-authority certificates for the exported surface.

assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.evaluator_eq_extendedEvaluator_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.evaluator_apply_eq_extendedEvaluator_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.referenceState_eq_extendedReferenceState_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.referenceState_apply_eq_extendedReferenceState_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.evaluation_facts_eq_referenceState_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.evaluate_facts_eq_extendedReferenceState_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedExtendedShortCircuit.evaluate_facts_eq_universalReferenceState_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedExtendedShortCircuit.PreparedPipeline.preparedReferenceState_eq_universalReferenceState_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedExtendedShortCircuit.PreparedPipeline.preparedReferenceEvaluation_facts_eq_universalReferenceState_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedExtendedShortCircuit.PreparedPipeline.evaluatePrepared_facts_eq_universalReferenceState_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedExtendedShortCircuit.PreparedPipeline.evaluate_facts_eq_universalReferenceState_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedExtendedShortCircuit.Cached.evaluate_facts_eq_universalReferenceState_of_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedExtendedShortCircuit.Cached.referenceUsingCache_facts_eq_universalReferenceState_of_noDoubleRecords
