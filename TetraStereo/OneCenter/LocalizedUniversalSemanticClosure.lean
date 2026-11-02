import TetraStereo.OneCenter.LocalizedUniversalSemanticComposition
import TetraStereo.OneCenter.LocalizedRule4aRankedProjection
import TetraStereo.OneCenter.LocalizedRule4aRankPopulation
import TetraStereo.OneCenter.LocalizedRule4bReferenceAgreement
import TetraStereo.OneCenter.LocalizedRule45DeclarativeAgreement

set_option autoImplicit false

/-!
# Unconditional closure of the localized universal semantics

`LocalizedUniversalSemanticComposition` reduces every node/spatial/topology obligation to the
single same-cursor Rules-4a--5 comparison agreement `LocalizedRerootCompoundRule45ComparisonAgreement`.
This module discharges that agreement from the two independently proved Rule-4a ranked-label
invariants:

* `declarative_rule4a_rankedLabels_projection_eq` (cross-cursor projection invariance), and
* `declarative_rule4a_rankedLabels_population_perm` (same-cursor rank-population invariance),

together with the green same-cursor observable uniqueness
`declarative_cumulative_key_observable_unique` and the generic selector core
`localizedRule4bReferencesFromRankedLabels_eq_of_rankedChiralAgrees`.

The resulting compound agreement is unconditional: it holds at every target, every dependency
view and every evaluation fuel of the existing localized formal input domain.  Consequently the
exact-label iff, the refusal form and the reference-state statements of
`LocalizedUniversalSemanticComposition` lose their last hypothesis.

We also isolate the independent semantic content of the generated reference state as a
per-target/label fixed-point predicate and prove existence (`referenceState` realises it) and
uniqueness among all states of the carrier.  Finally, every checked/accepted or generated
evaluation result is shown to compute that same state, so the independent statements apply to
both pipeline branches.

## Scope

Everything here is relative to the existing localized formal input domain (`Input`, hence a
certified `CertifiedLocalizedCIPInput`) and its provided configuration.  No chemical
applicability claim beyond that domain, no fixed production Rule-3 budget completeness claim and
no claim about unmodeled IUPAC content is made.  The Rule-3 budget is existentially quantified in
the completeness direction and is the universal evaluator's computed budget in the soundness
direction.
-/

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput

namespace CertifiedLocalizedCIPInput

/-! ## Rule-4b selected-reference agreement from the two ranked-label invariants

The selector reads only the hierarchy-rank-addressed `rankedLabels`.  Invariant (A) fixes the
Rule-4a projected layers, hence the rank skeleton and the first occupied chiral rank; invariant (B)
fixes the uppercase `R`/`S` population at every depth and rank.  The generic selector core then
yields equality of the selected reference lists. -/

/-- Two independent Rule-4a derivations at the same cursor and fuel select the same P-92.5.2.1
Rule-4b reference list.  This combines the cross-cursor projection invariant with the same-cursor
rank-population invariant; no exact label equality is used or claimed. -/
theorem declarative_rule4a_referenceList_agreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (leftKey rightKey : input.LocalizedRerootCumulativeRule45Key)
    (leftDerived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      .rule4a target view fuel cursor leftKey)
    (rightDerived : input.DeclarativeLocalizedRerootCumulativeRule45Key
      .rule4a target view fuel cursor rightKey) :
    localizedRule4bReferencesFromRankedLabels leftKey.rankedLabels =
      localizedRule4bReferencesFromRankedLabels rightKey.rankedLabels := by
  apply localizedRule4bReferencesFromRankedLabels_eq_of_rankedChiralAgrees
  · exact input.declarative_rule4a_rankedLabels_projection_eq target view fuel cursor cursor
      leftKey rightKey leftDerived rightDerived
      (input.declarative_cumulative_key_observable_unique .rule4a target view fuel cursor
        leftKey rightKey leftDerived rightDerived)
  · intro depth rank
    exact input.declarative_rule4a_rankedLabels_population_perm target view fuel cursor
      leftDerived rightDerived depth rank

/-! ## The compound Rules-4a--5 comparison agreement, unconditionally -/

/-- **Unconditional compound comparison agreement.**  Any two independently derived compound
Rules-4a--5 keys at the same cursor, target, view and fuel have identical through-Rule-5
comparison behaviour in both argument positions against every third key.  The two selected
reference lists agree by `declarative_rule4a_referenceList_agreement`, and the green two-sided
transport `compareLocalizedRerootCompoundThroughRule5_congr_of_referenceListAgreement` converts
that lower-layer equality into the complete comparison record. -/
theorem localizedRerootCompoundRule45ComparisonAgreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) :
    input.LocalizedRerootCompoundRule45ComparisonAgreement target view fuel := by
  intro cursor left right leftDerived rightDerived other
  have referenceAgreement :
      LocalizedRerootCompoundRule45ReferenceListAgreement input left right :=
    input.declarative_rule4a_referenceList_agreement (fuel := fuel) target view cursor
      left.prior.rule4aKey right.prior.rule4aKey leftDerived.1.1 rightDerived.1.1
  have referencesAgree : left.prior.references = right.prior.references :=
    input.references_eq_of_referenceListAgreement target view cursor left right
      leftDerived rightDerived referenceAgreement
  exact input.compareLocalizedRerootCompoundThroughRule5_congr_of_declarative
    target view cursor left right other leftDerived rightDerived referencesAgree

/-! ## Exact-label universal descriptor completeness and refusal

`LocalizedUniversalSemanticComposition` proves both directions conditional on the comparison
agreement at the production Rule-45 evaluation fuel.  The agreement is now available at every
fuel, so the condition is discharged. -/

/-- **Unconditional exact-label iff.**  For every target, dependency view and label,
`universalDescriptor?` returns that label exactly when some Rule-3 evaluation budget carries the
independent declarative universal descriptor of that label.  The budget is existentially
quantified in the completeness direction. -/
theorem universalDescriptor?_eq_some_iff_exists_declarativeUniversalDescriptor_of_derived
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel) :
    input.universalDescriptor? target view = some descriptor ↔
      ∃ evaluationBudget : Nat,
        input.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
          evaluationBudget descriptor :=
  input.universalDescriptor?_eq_some_iff_exists_declarativeUniversalDescriptor_of_sameCursorAgreement
    target view
    (input.localizedRerootCompoundRule45ComparisonAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel))
    descriptor

/-- **Unconditional refusal iff no independent derivation.**  `universalDescriptor?` returns
`none` exactly when no Rule-3 evaluation budget and no label carry the declarative universal
descriptor at that view.  This is an operational refusal statement; it is not a chemical
nonexistence claim beyond the declarative relation. -/
theorem universalDescriptor?_eq_none_iff_forall_not_declarativeUniversalDescriptor_of_derived
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    input.universalDescriptor? target view = none ↔
      ∀ (evaluationBudget : Nat) (descriptor : LocalizedAuxiliaryLabel),
        ¬ input.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
          evaluationBudget descriptor :=
  input.universalDescriptor?_eq_none_iff_forall_not_declarativeUniversalDescriptor_of_sameCursorAgreement
    target view
    (input.localizedRerootCompoundRule45ComparisonAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel))

end CertifiedLocalizedCIPInput

/-! ## The universal reference state, unconditionally

The universal reference state is the generated operational fixed point, not the old production
`LocalizedExtendedShortCircuit.referenceState`.  The statements below are read at the reference
state's own dependency view. -/

namespace LocalizedUniversalReference

open CertifiedLocalizedCIPInput
open TetraStereo.Certificate.Dependency

/-- **Unconditional universal reference-state exact-label iff.**  The generated universal
reference state assigns a label at a target exactly when some Rule-3 evaluation budget carries the
independent declarative universal descriptor of that label at the state's own dependency view. -/
theorem referenceState_eq_some_iff_exists_declarativeUniversalDescriptor_unconditional
    (input : Input) (target : Occurrence input)
    (descriptor : LocalizedAuxiliaryLabel) :
    referenceState input target = some descriptor ↔
      ∃ evaluationBudget : Nat,
        input.certified.DeclarativeLocalizedOccurrenceUniversalDescriptor target
          (input.certified.localizedDependencyView (referenceState input) target)
          evaluationBudget descriptor :=
  referenceState_eq_some_iff_exists_declarativeUniversalDescriptor input target
    (input.certified.localizedRerootCompoundRule45ComparisonAgreement target
      (input.certified.localizedDependencyView (referenceState input) target)
      (localizedOccurrenceRerootEvaluationFuel (carrierFuel input)))
    descriptor

/-- **Unconditional universal reference-state refusal iff.**  The reference state refuses a target
exactly when no budget and no label carry the declarative universal descriptor at its own
dependency view. -/
theorem referenceState_eq_none_iff_forall_not_declarativeUniversalDescriptor_unconditional
    (input : Input) (target : Occurrence input) :
    referenceState input target = none ↔
      ∀ (evaluationBudget : Nat) (descriptor : LocalizedAuxiliaryLabel),
        ¬ input.certified.DeclarativeLocalizedOccurrenceUniversalDescriptor target
          (input.certified.localizedDependencyView (referenceState input) target)
          evaluationBudget descriptor :=
  referenceState_eq_none_iff_forall_not_declarativeUniversalDescriptor input target
    (input.certified.localizedRerootCompoundRule45ComparisonAgreement target
      (input.certified.localizedDependencyView (referenceState input) target)
      (localizedOccurrenceRerootEvaluationFuel (carrierFuel input)))

/-! ## The independent semantic fixed point

The predicate below is stated purely in terms of the independent declarative relation at the
state's own views.  It contains no executable key, no certificate and no production budget: a
state is a model when the label it stores at every target is exactly the label that is
declaratively derivable there from its own dependency values. -/

/-- Independent semantic reference model: at every target, the stored outcome is `some label`
exactly when some Rule-3 evaluation budget carries the declarative universal descriptor of that
label at the state's own dependency view.  This is a semantic fixed-point property, not the
operational evaluator equation. -/
def IndependentSemanticReferenceModel (input : Input)
    (state : input.certified.LocalizedAuxiliaryState (carrierFuel input)) : Prop :=
  ∀ (target : Occurrence input) (descriptor : LocalizedAuxiliaryLabel),
    state target = some descriptor ↔
      ∃ evaluationBudget : Nat,
        input.certified.DeclarativeLocalizedOccurrenceUniversalDescriptor target
          (input.certified.localizedDependencyView state target)
          evaluationBudget descriptor

/-- The generated universal reference state realises the independent semantic model. -/
theorem referenceState_realizes_independentSemanticReferenceModel (input : Input) :
    IndependentSemanticReferenceModel input (referenceState input) := by
  intro target descriptor
  exact referenceState_eq_some_iff_exists_declarativeUniversalDescriptor_unconditional
    input target descriptor

/-- **Uniqueness of the independent semantic model.**  Any state whose stored outcomes are exactly
the declaratively derivable labels at its own views is the generated universal reference state.

The proof reads the unconditional exact-label iff at the candidate state's own view and concludes
the operational equation `universalDescriptor? = state`; the existing fixed-point uniqueness
`reference_state_unique` then identifies the state.  The policy evaluator is rewritten to the
universal descriptor with `evaluator_eq_universalDescriptor`; no definitional unfolding of the
evaluator body is used. -/
theorem independentSemanticReferenceModel_unique (input : Input)
    {state : input.certified.LocalizedAuxiliaryState (carrierFuel input)}
    (model : IndependentSemanticReferenceModel input state) :
    state = referenceState input := by
  have operational : ∀ target : Occurrence input,
      input.certified.universalDescriptor? target
        (input.certified.localizedDependencyView state target) = state target := by
    intro target
    have pointwise : ∀ descriptor : LocalizedAuxiliaryLabel,
        input.certified.universalDescriptor? target
            (input.certified.localizedDependencyView state target) = some descriptor ↔
          state target = some descriptor := by
      intro descriptor
      rw [input.certified.universalDescriptor?_eq_some_iff_exists_declarativeUniversalDescriptor_of_derived
        target (input.certified.localizedDependencyView state target) descriptor]
      exact (model target descriptor).symm
    cases universal : input.certified.universalDescriptor? target
        (input.certified.localizedDependencyView state target) with
    | some descriptor => exact ((pointwise descriptor).mp universal).symm
    | none =>
        have stateNone : state target = none := by
          cases stateEq : state target with
          | none => rfl
          | some descriptor =>
              have universalSome := (pointwise descriptor).mpr stateEq
              rw [universal] at universalSome
              cases universalSome
        rw [stateNone]
  apply reference_state_unique input
  intro target
  show evaluator input (carrierFuel input) target
    (input.certified.localizedDependencyView state target) = state target
  rw [evaluator_eq_universalDescriptor_apply input (carrierFuel input) target
    (input.certified.localizedDependencyView state target)]
  exact operational target

/-- The generated reference state is the unique state satisfying the independent semantic model. -/
theorem existsUnique_independentSemanticReferenceModel (input : Input) :
    ∃! state : input.certified.LocalizedAuxiliaryState (carrierFuel input),
      IndependentSemanticReferenceModel input state :=
  ⟨referenceState input, referenceState_realizes_independentSemanticReferenceModel input,
    fun _state model => independentSemanticReferenceModel_unique input model⟩

/-! ## Both pipeline branches compute the independent reference state

`evaluation_eq_reference` and `evaluate_state` already identify every accepted and generated
result with the universal reference state.  Composing them with the unconditional reference-state
statement transfers the independent semantics to both branches. -/

/-- **Every evaluation result, accepted or generated, has the independent exact-label semantics.**
The dependency view is the result's own. -/
theorem evaluation_lookup_eq_some_iff_exists_declarativeUniversalDescriptor
    (input : Input) (result : Evaluation input) (target : Occurrence input)
    (descriptor : LocalizedAuxiliaryLabel) :
    lookup result.facts target = some descriptor ↔
      ∃ evaluationBudget : Nat,
        input.certified.DeclarativeLocalizedOccurrenceUniversalDescriptor target
          (input.certified.localizedDependencyView (lookup result.facts) target)
          evaluationBudget descriptor := by
  rw [evaluation_eq_reference input result]
  exact referenceState_eq_some_iff_exists_declarativeUniversalDescriptor_unconditional
    input target descriptor

/-- **Every evaluation result, accepted or generated, refuses exactly the underivable labels.**
The dependency view is the result's own. -/
theorem evaluation_lookup_eq_none_iff_forall_not_declarativeUniversalDescriptor
    (input : Input) (result : Evaluation input) (target : Occurrence input) :
    lookup result.facts target = none ↔
      ∀ (evaluationBudget : Nat) (descriptor : LocalizedAuxiliaryLabel),
        ¬ input.certified.DeclarativeLocalizedOccurrenceUniversalDescriptor target
          (input.certified.localizedDependencyView (lookup result.facts) target)
          evaluationBudget descriptor := by
  rw [evaluation_eq_reference input result]
  exact referenceState_eq_none_iff_forall_not_declarativeUniversalDescriptor_unconditional
    input target

/-- **Both branches of the runnable evaluator share the independent exact-label semantics.** -/
theorem evaluate_lookup_eq_some_iff_exists_declarativeUniversalDescriptor
    (input : Input) (nodes : Nodes input) (target : Occurrence input)
    (descriptor : LocalizedAuxiliaryLabel) :
    lookup (evaluate input nodes).facts target = some descriptor ↔
      ∃ evaluationBudget : Nat,
        input.certified.DeclarativeLocalizedOccurrenceUniversalDescriptor target
          (input.certified.localizedDependencyView
            (lookup (evaluate input nodes).facts) target)
          evaluationBudget descriptor := by
  rw [evaluate_state input nodes]
  exact referenceState_eq_some_iff_exists_declarativeUniversalDescriptor_unconditional
    input target descriptor

/-- An accepted checked candidate has the independent exact-label semantics. -/
theorem checked_lookup_eq_some_iff_exists_declarativeUniversalDescriptor
    (input : Input) (nodes : Nodes input) (facts : Facts input)
    (accepted : checkProposals? input nodes = some facts)
    (target : Occurrence input) (descriptor : LocalizedAuxiliaryLabel) :
    lookup facts target = some descriptor ↔
      ∃ evaluationBudget : Nat,
        input.certified.DeclarativeLocalizedOccurrenceUniversalDescriptor target
          (input.certified.localizedDependencyView (lookup facts) target)
          evaluationBudget descriptor := by
  rw [checked_eq_reference input nodes facts accepted]
  exact referenceState_eq_some_iff_exists_declarativeUniversalDescriptor_unconditional
    input target descriptor

end LocalizedUniversalReference

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedUniversalReference.evaluate_lookup_eq_some_iff_exists_declarativeUniversalDescriptor
