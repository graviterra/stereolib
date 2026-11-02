import TetraStereo.OneCenter.LocalizedOriginalSpatialObservableCompletion
import TetraStereo.OneCenter.LocalizedExtendedNodeSemanticCompletion
import TetraStereo.OneCenter.LocalizedNodeTopologyCompletion
import TetraStereo.OneCenter.LocalizedUniversalDescriptorCompleteness
import TetraStereo.OneCenter.LocalizedUniversalReferencePipeline

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

































































/-! ## 1. Normalizing the two comparison interfaces

The descriptor converse consumes the same-cursor form; the endpoint and original-node components
consume the two-cursor record form.  The two are not assumed simultaneously: the latter follows
from the former because every successfully built key is declaratively derived. -/

/-- The endpoint two-cursor comparison-record agreement follows from the same-cursor
comparison-record agreement.  Given built keys `firstBuilt`/`secondBuilt` at the two cursors, both
are declaratively derived by builder soundness; one same-cursor invariance step at each cursor
replaces them by the corresponding derived keys. -/
theorem LocalizedRule45CompoundComparisonRecordAgreement_of_sameCursorAgreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat)
    (agreement : input.LocalizedRerootCompoundRule45ComparisonAgreement target view fuel) :
    input.LocalizedRule45CompoundComparisonRecordAgreement target view fuel := by
  intro firstCursor secondCursor firstKey secondKey firstDerived secondDerived
    firstBuilt secondBuilt firstComputed secondComputed
  have firstBuiltDerived : input.DeclarativeLocalizedRerootCompoundRule45Key target view fuel
      firstCursor firstBuilt :=
    input.buildLocalizedRerootCompoundRule45Key?_sound target view fuel firstCursor firstBuilt
      firstComputed
  have secondBuiltDerived : input.DeclarativeLocalizedRerootCompoundRule45Key target view fuel
      secondCursor secondBuilt :=
    input.buildLocalizedRerootCompoundRule45Key?_sound target view fuel secondCursor secondBuilt
      secondComputed
  -- Replace the built first key by the derived first key against the built second key.
  have forward :
      input.compareLocalizedRerootCompoundThroughRule5 firstBuilt secondBuilt =
        input.compareLocalizedRerootCompoundThroughRule5 firstKey secondBuilt :=
    (agreement firstCursor firstBuilt firstKey firstBuiltDerived firstDerived secondBuilt).1
  -- Replace the built second key by the derived second key against the derived first key.
  have backward :
      input.compareLocalizedRerootCompoundThroughRule5 firstKey secondKey =
        input.compareLocalizedRerootCompoundThroughRule5 firstKey secondBuilt :=
    (agreement secondCursor secondKey secondBuilt secondDerived secondBuiltDerived firstKey).2
  exact forward.trans backward.symm

/-! ## 2. The one-step node-completion interface

The three observation-level fields come from the genuine spatial/cyclic/odd producers of
`LocalizedOriginalSpatialObservableCompletion`; the six topological fields are discharged inside
`LocalizedExtendedNodeSemanticCompletion` by
`localizedOriginalNodeObservableCompletionObligations_of_observations`.  The odd-cumulene topology
recognizer is discharged by
`localizedRule3OddCumuleneEndpointCursorFrame?_eq_some_at_traversalFuel_of_declarative` inside the
odd producer. -/

/-- `LocalizedRule3ExtendedShortCircuitNodeComplete` from the endpoint comparison-record agreement,
by composing the three observation completeness producers with the extended-node constructor.
The frame fuel and the predecessor frame completeness proof are introduced as demanded by the
interface; no whole-frame completeness is assumed ahead of the induction. -/
theorem localizedRule3ExtendedShortCircuitNodeComplete_of_endpointComparisonAgreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule45Agreement : input.LocalizedRule45CompoundComparisonRecordAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)) :
    LocalizedRule3ExtendedShortCircuitNodeComplete input target view := by
  intro frameFuel frameComplete
  exact input.localizedRule3ExtendedShortCircuitNodeCompleteAt_of_components
    frameFuel target view frameComplete rule45Agreement
    (fun occurrence result derived =>
      input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?_observation_complete_extended
        target occurrence view frameFuel frameComplete rule45Agreement result derived)
    (fun occurrence result derived =>
      input.localizedRule3RequiredMonocyclicEZWith?_observation_complete_extended
        target occurrence view frameFuel frameComplete rule45Agreement result derived)
    (fun occurrence result derived =>
      input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?_observation_complete_extended
        target occurrence view frameFuel frameComplete rule45Agreement result derived)

/-- The one-step node-completion interface from the single residual same-cursor Rules-4a--5
comparison agreement.  This is the composition of the endpoint and spatial components with the
green topology fields; the endpoint two-cursor form is derived, not assumed. -/
theorem localizedRule3ExtendedShortCircuitNodeComplete_of_sameCursorAgreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (agreement : input.LocalizedRerootCompoundRule45ComparisonAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)) :
    LocalizedRule3ExtendedShortCircuitNodeComplete input target view :=
  input.localizedRule3ExtendedShortCircuitNodeComplete_of_endpointComparisonAgreement
    target view
    (input.LocalizedRule45CompoundComparisonRecordAgreement_of_sameCursorAgreement
      target view (localizedOccurrenceRerootEvaluationFuel carrierFuel) agreement)

/-- Mutual Rule-3 key and frame completeness at every fuel, with the node seam discharged by the
component composition above.  This is the semantic node construction: the only retained premise is
the same-cursor Rules-4a--5 comparison agreement. -/
theorem localizedExtendedShortCircuitRule3_mutual_complete_of_sameCursorAgreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (agreement : input.LocalizedRerootCompoundRule45ComparisonAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)) :
    ∀ fuel,
      LocalizedRerootExtendedShortCircuitRule3KeyCompleteAt input target view fuel ∧
        LocalizedExtendedShortCircuitRule3FrameCompleteAt input target view fuel :=
  input.localizedExtendedShortCircuitRule3_mutual_complete target view
    (input.localizedRule3ExtendedShortCircuitNodeComplete_of_sameCursorAgreement
      target view agreement)

/-! ## 3. Exact-label completeness and refusal of the universal descriptor

Both directions are assembled here from the *stable* pieces: the unconditional positive soundness
`universalDescriptor?_sound` and the main converse
`universalDescriptor?_eq_some_of_declarativeUniversalDescriptor`, instantiated with the composed
node-completion interface above.  The result keeps exactly the same-cursor Rules-4a--5 comparison
agreement as the residual premise. -/

/-- **Exact-label iff.**  For a fixed label, `universalDescriptor?` returns that label exactly when
some Rule-3 evaluation budget carries the independent declarative universal descriptor of that
label.  Forward is positive soundness; backward is the converse applied to the composed node
construction. -/
theorem universalDescriptor?_eq_some_iff_exists_declarativeUniversalDescriptor_of_sameCursorAgreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (agreement : input.LocalizedRerootCompoundRule45ComparisonAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel))
    (descriptor : LocalizedAuxiliaryLabel) :
    input.universalDescriptor? target view = some descriptor ↔
      ∃ evaluationBudget : Nat,
        input.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
          evaluationBudget descriptor := by
  constructor
  · intro computed
    obtain ⟨_base, _baseComputed, meaning⟩ :=
      input.universalDescriptor?_sound target view descriptor computed
    exact ⟨_, meaning⟩
  · rintro ⟨evaluationBudget, meaning⟩
    exact input.universalDescriptor?_eq_some_of_declarativeUniversalDescriptor
      target view
      (input.localizedRule3ExtendedShortCircuitNodeComplete_of_sameCursorAgreement
        target view agreement)
      agreement evaluationBudget descriptor meaning

/-- **Refusal iff the absence of every independent derivation.**  `universalDescriptor?` returns
`none` exactly when no Rule-3 evaluation budget and no label carry the declarative universal
descriptor.  This is an operational refusal statement, not an independent chemical nonexistence
claim beyond the stated declarative relation. -/
theorem universalDescriptor?_eq_none_iff_forall_not_declarativeUniversalDescriptor_of_sameCursorAgreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (agreement : input.LocalizedRerootCompoundRule45ComparisonAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel)) :
    input.universalDescriptor? target view = none ↔
      ∀ (evaluationBudget : Nat) (descriptor : LocalizedAuxiliaryLabel),
        ¬ input.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
          evaluationBudget descriptor := by
  constructor
  · intro refused evaluationBudget descriptor meaning
    have universal := input.universalDescriptor?_eq_some_of_declarativeUniversalDescriptor
      target view
      (input.localizedRule3ExtendedShortCircuitNodeComplete_of_sameCursorAgreement
        target view agreement)
      agreement evaluationBudget descriptor meaning
    rw [refused] at universal
    cases universal
  · intro noMeaning
    cases universal : input.universalDescriptor? target view with
    | none => rfl
    | some descriptor =>
        obtain ⟨_base, _baseComputed, meaning⟩ :=
          input.universalDescriptor?_sound target view descriptor universal
        exact False.elim (noMeaning _ descriptor meaning)

end CertifiedLocalizedCIPInput

/-! ## 4. The universal reference state

`reference_equation` states that the policy evaluator at the generated reference state reads
back exactly the reference state.  Rewriting it with the evaluated function equality
`evaluator_eq_universalDescriptor` turns the left-hand side into the unconditional universal
descriptor; composing with the exact-label iff above yields the reference-state statement.  The
reference state is the universal one; it is not the old production-budget state. -/

namespace LocalizedUniversalReference

/-- **Universal reference-state exact-label iff.**  The generated universal reference state assigns
a label at a target exactly when some Rule-3 evaluation budget carries the independent declarative
universal descriptor of that label at the reference state's own dependency view.  The sole residual
hypothesis is the same-cursor Rules-4a--5 comparison agreement at that view. -/
theorem referenceState_eq_some_iff_exists_declarativeUniversalDescriptor
    (input : Input) (target : Occurrence input)
    (agreement : input.certified.LocalizedRerootCompoundRule45ComparisonAgreement target
      (input.certified.localizedDependencyView (referenceState input) target)
      (CertifiedLocalizedCIPInput.localizedOccurrenceRerootEvaluationFuel (carrierFuel input)))
    (descriptor : CertifiedLocalizedCIPInput.LocalizedAuxiliaryLabel) :
    referenceState input target = some descriptor ↔
      ∃ evaluationBudget : Nat,
        input.certified.DeclarativeLocalizedOccurrenceUniversalDescriptor target
          (input.certified.localizedDependencyView (referenceState input) target)
          evaluationBudget descriptor := by
  have equation := reference_equation input target
  rw [evaluator_eq_universalDescriptor_apply input (carrierFuel input) target
    (input.certified.localizedDependencyView (referenceState input) target)] at equation
  rw [← equation]
  exact input.certified.universalDescriptor?_eq_some_iff_exists_declarativeUniversalDescriptor_of_sameCursorAgreement
    target (input.certified.localizedDependencyView (referenceState input) target)
    agreement descriptor

/-- **Universal reference-state refusal iff the absence of every independent derivation.**  The
reference state refuses a target exactly when no Rule-3 evaluation budget and no label carry the
declarative universal descriptor at the reference state's own dependency view. -/
theorem referenceState_eq_none_iff_forall_not_declarativeUniversalDescriptor
    (input : Input) (target : Occurrence input)
    (agreement : input.certified.LocalizedRerootCompoundRule45ComparisonAgreement target
      (input.certified.localizedDependencyView (referenceState input) target)
      (CertifiedLocalizedCIPInput.localizedOccurrenceRerootEvaluationFuel (carrierFuel input))) :
    referenceState input target = none ↔
      ∀ (evaluationBudget : Nat)
        (descriptor : CertifiedLocalizedCIPInput.LocalizedAuxiliaryLabel),
        ¬ input.certified.DeclarativeLocalizedOccurrenceUniversalDescriptor target
          (input.certified.localizedDependencyView (referenceState input) target)
          evaluationBudget descriptor := by
  have equation := reference_equation input target
  rw [evaluator_eq_universalDescriptor_apply input (carrierFuel input) target
    (input.certified.localizedDependencyView (referenceState input) target)] at equation
  rw [← equation]
  exact input.certified.universalDescriptor?_eq_none_iff_forall_not_declarativeUniversalDescriptor_of_sameCursorAgreement
    target (input.certified.localizedDependencyView (referenceState input) target)
    agreement

end LocalizedUniversalReference

end TetraStereo.OneCenter
