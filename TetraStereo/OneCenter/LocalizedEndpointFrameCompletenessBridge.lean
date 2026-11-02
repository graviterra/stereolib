import TetraStereo.OneCenter.LocalizedEndpointSemanticCompletion
import TetraStereo.OneCenter.LocalizedPhysicalReferenceUniqueness
import TetraStereo.OneCenter.LocalizedMutualObservableCompletion
import TetraStereo.OneCenter.LocalizedConstitutionalOriginalRule3Coherence

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput


















































/-! ## The comparison-visible projection of one key

The frame callback interface compares frames through
`LocalizedRule3CanonicalKeyFrameObservableRel`, i.e. equality of the mapped numeric projections.
`LocalizedRule3ExtendedFrameTopologyEquivalent` gives pointwise topology equivalence in the
`derived, compiled` orientation; the relation needed by the callback is oriented `realized,
derived`.  The next two lemmas perform exactly that reversal. -/

/-- Pointwise topology equivalence of two key lists gives equality of their numeric observable
projections in the `compiled ↦ derived` orientation used by
`LocalizedRule3CanonicalKeyFrameObservableRel`. -/
theorem map_localizedRerootRule3SpatialKeyObservable_eq_of_forall₂_symm
    (input : CertifiedLocalizedCIPInput)
    (derived compiled : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (related : List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input)
      derived compiled) :
    compiled.map input.localizedRerootRule3SpatialKeyObservable =
      derived.map input.localizedRerootRule3SpatialKeyObservable :=
  (input.map_localizedRerootRule3SpatialKeyObservable_eq_of_forall₂
    derived compiled related).symm

/-- A frame-level topology equivalence yields the observable frame relation consumed by the
endpoint callback completeness interface, oriented `compiled ↦ derived`. -/
theorem canonicalKeyFrameObservableRel_of_topologyEquivalent
    (input : CertifiedLocalizedCIPInput)
    (derived compiled : input.LocalizedRule3CanonicalKeyFrame)
    (equivalent : LocalizedRule3ExtendedFrameTopologyEquivalent input derived compiled) :
    input.LocalizedRule3CanonicalKeyFrameObservableRel compiled derived := by
  unfold LocalizedRule3CanonicalKeyFrameObservableRel
  exact input.map_localizedRerootRule3SpatialKeyObservable_eq_of_forall₂_symm
    derived.keys compiled.keys equivalent.2.1

/-! ## Interface (1): canonical endpoint reference selections

`LocalizedRule3EndpointKeyFrameCanonicalReferences` asks, for every independently derived endpoint
key frame, that the two cursors selected by the executable lookup at the frame's physical candidates
are canonical.  The declarative endpoint relation already carries the two *declarative* reference
selections; `canonicalLocalizedRule3ReferenceCursor_of_declarative` upgrades each of them using
general physical-reference uniqueness. -/

/-- Every independently derived endpoint key frame selects canonical physical reference cursors.
This holds for an arbitrary caller-supplied Rule-3 frame meaning: the Rule-3 frame component is
never inspected.  No endpoint-shape hypothesis is used. -/
theorem localizedRule3EndpointKeyFrameCanonicalReferences
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel) :
    input.LocalizedRule3EndpointKeyFrameCanonicalReferences
      target view Rule3FrameMeaning endpoint partner endpointCursor := by
  intro frame derived
  exact
    ⟨input.canonicalLocalizedRule3ReferenceCursor_of_declarative
        endpointCursor frame.firstCursor frame.endpointFrame.first derived.2.1,
      input.canonicalLocalizedRule3ReferenceCursor_of_declarative
        endpointCursor frame.secondCursor frame.endpointFrame.second derived.2.2.1⟩

/-! ## Constitutional projection of the extended short-circuit key

The structural fact behind coherence: the constitutional component of any independently derived
extended short-circuit key is itself independently derived at the same cursor and fuel.  The proof
mirrors `descriptorRule3Key_constitutional_derived` and
`shortCircuitRule3Key_constitutional_derived`; the two frame-node premises in the successor branch
(the independent extended node meaning) are irrelevant to the constitutional projection, which only
depends on the child keys and the descending ranking. -/

/-- Every independent extended short-circuit key derivation contains a pure constitutional
derivation.  No endpoint readiness, computed success, exclusion choice, or assumption on descriptor
values is needed. -/
theorem extendedShortCircuitRule3Key_constitutional_derived
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel excluded cursor key,
      input.DeclarativeLocalizedRerootExtendedShortCircuitRule3Key
        target view fuel excluded cursor key →
      input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key.constitutional := by
  intro fuel
  induction fuel with
  | zero =>
      intro excluded cursor key meaning
      obtain ⟨children, frame, empty, _, rfl⟩ := meaning
      exact .terminal frame empty
  | succ fuel ih =>
      intro excluded cursor key meaning
      obtain ⟨children, observation, frame, _, terminal | branch⟩ := meaning
      · obtain ⟨empty, rfl⟩ := terminal
        exact .terminal frame empty
      · obtain ⟨childKeys, sorted, nonempty, derivations, ranking, descending, rfl⟩ := branch
        refine .branch frame nonempty ?_ (ranking.map (·.constitutional))
          (input.rule3_descending_constitutional sorted descending)
        exact projected_rule3_constitutional_key_list input
          (R := fun cursor key =>
            input.DeclarativeLocalizedRerootExtendedShortCircuitRule3Key
              target view fuel excluded cursor key)
          (fun cursor key derived => ih excluded cursor key derived)
          children childKeys derivations

/-! ## Interface (3): constitutional coherence of the extended frame meaning

Coherence asks that the two keys of an independently meaningful frame carry constitutional
derivations at the frame's own cursors.  For the extended frame meaning at fuel `frameFuel + 1`, the
rebuilt-key component of the frame derivation is a pointwise `List.Forall₂` of extended key
derivations; at `frameFuel = 0` the meaning is `False`. -/

/-- A two-element pointwise relation exposes its two components. -/
private theorem forall₂_pair_components
    {α β : Type*} {R : α → β → Prop} {first second : α} {third fourth : β}
    (related : List.Forall₂ R [first, second] [third, fourth]) :
    R first third ∧ R second fourth := by
  cases related with
  | cons head tail =>
      cases tail with
      | cons headTail tailTail =>
          cases tailTail
          exact ⟨head, headTail⟩

/-- The extended short-circuit frame meaning is constitutionally coherent.  The derivation of the
frame already contains independent key derivations for both endpoint keys; the previous section
extracts their constitutional projections.  Nothing about the compiled frame, the callback, or the
observations payload is used. -/
theorem localizedRule3FrameMeaningConstitutionalCoherent_extended
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frameFuel : Nat) :
    input.LocalizedRule3FrameMeaningConstitutionalCoherent
      (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame
        target view frameFuel) := by
  cases frameFuel with
  | zero =>
      intro cursors frame meaningful
      unfold DeclarativeLocalizedExtendedShortCircuitRule3Frame at meaningful
      exact False.elim meaningful
  | succ fuel =>
      intro cursors frame meaningful firstCursor secondCursor firstKey secondKey
        cursorsEq keysEq
      obtain ⟨_, _, _, _, keysDerived⟩ := meaningful
      rw [cursorsEq, keysEq] at keysDerived
      obtain ⟨firstDerived, secondDerived⟩ := forall₂_pair_components keysDerived
      exact
        ⟨⟨fuel, input.extendedShortCircuitRule3Key_constitutional_derived
            target view fuel frame.excluded firstCursor firstKey firstDerived⟩,
          ⟨fuel, input.extendedShortCircuitRule3Key_constitutional_derived
            target view fuel frame.excluded secondCursor secondKey secondDerived⟩⟩

/-! ## Interface (2): callback completeness from predecessor frame completeness

`LocalizedExtendedShortCircuitRule3FrameCompleteAt` states exactly that every independent frame at
the given fuel has a successful compiled frame carrying the frame topology invariant.  The invariant
contains the pointwise topology equivalence of the rebuilt keys; the observation projection of that
relation is the observable frame relation required by the callback interface. -/

/-- The actual extended short-circuit frame builder is complete for its independent frame meaning up
to comparison-visible key projection, whenever predecessor frame completeness holds at the same
fuel. -/
theorem localizedRule3FrameCallbackCompleteness_extended
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frameFuel : Nat)
    (frameComplete : LocalizedExtendedShortCircuitRule3FrameCompleteAt
      input target view frameFuel) :
    input.LocalizedRule3FrameCallbackCompleteness
      (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel)
      (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel) := by
  intro cursors frame meaningful
  obtain ⟨compiled, compiledComputed, equivalent⟩ :=
    frameComplete cursors frame meaningful
  exact ⟨compiled, compiledComputed,
    input.canonicalKeyFrameObservableRel_of_topologyEquivalent frame compiled equivalent⟩

/-! ## The endpoint converse instantiated for the extended short-circuit compiler

All three component interfaces of `localizedRule3ShortCircuitEndpointPriority?_eq_of_declarative`
are now supplied by the concrete extended compiler.  Only the predecessor frame-completeness
hypothesis and the exact-payload Rules-4a--5 builder agreement remain. -/











theorem localizedRule3ShortCircuitEndpointPriority?_eq_of_declarative_extended
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frameFuel : Nat)
    (frameComplete : LocalizedExtendedShortCircuitRule3FrameCompleteAt
      input target view frameFuel)
    (rule45Agreement : input.LocalizedRule45EndpointBuilderAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel))
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (result : input.LocalizedRule3ShortCircuitEndpointResult)
    (derived : input.DeclarativeLocalizedRule3ShortCircuitEndpointResult
      target view
      (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel)
      endpoint partner endpointCursor result) :
    input.localizedRule3ShortCircuitEndpointPriority?
        target view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
        endpoint partner endpointCursor = some result :=
  input.localizedRule3ShortCircuitEndpointPriority?_eq_of_declarative
    target view
    (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
    (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel)
    (input.localizedRule3FrameCallbackCompleteness_extended
      target view frameFuel frameComplete)
    (input.localizedRule3FrameMeaningConstitutionalCoherent_extended
      target view frameFuel)
    endpoint partner endpointCursor
    (input.localizedRule3EndpointKeyFrameCanonicalReferences
      target view
      (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel)
      endpoint partner endpointCursor)
    rule45Agreement result derived

/-- Endpoint converse in the canonical-agreement form of the Rules-4a--5 premise: if every
independently derived Rules-4a--5 key is canonical, the exact-payload premise is discharged and the
only remaining hypothesis is predecessor frame completeness.  This is the form in which the still
external `u_rule45_semantic_agreement` lemma is expected to arrive. -/
theorem localizedRule3ShortCircuitEndpointPriority?_eq_of_declarative_extended_of_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frameFuel : Nat)
    (frameComplete : LocalizedExtendedShortCircuitRule3FrameCompleteAt
      input target view frameFuel)
    (rule45Canonical : input.LocalizedRule45DeclarativeCanonicalAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel))
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (result : input.LocalizedRule3ShortCircuitEndpointResult)
    (derived : input.DeclarativeLocalizedRule3ShortCircuitEndpointResult
      target view
      (input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view frameFuel)
      endpoint partner endpointCursor result) :
    input.localizedRule3ShortCircuitEndpointPriority?
        target view
        (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view frameFuel)
        endpoint partner endpointCursor = some result :=
  input.localizedRule3ShortCircuitEndpointPriority?_eq_of_declarative_extended
    target view frameFuel frameComplete
    (input.LocalizedRule45EndpointBuilderAgreement_of_canonical
      target view (localizedOccurrenceRerootEvaluationFuel carrierFuel) rule45Canonical)
    endpoint partner endpointCursor result derived

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
