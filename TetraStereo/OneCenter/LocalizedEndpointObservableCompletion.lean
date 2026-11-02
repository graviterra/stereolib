import TetraStereo.OneCenter.LocalizedEndpointFrameCompletenessBridge
import TetraStereo.OneCenter.LocalizedRule45DeclarativeAgreement

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter




























namespace CertifiedLocalizedCIPInput

/-! ## The minimal lower interface: Rule-45 comparison-record agreement -/









def LocalizedRule45CompoundComparisonRecordAgreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) : Prop :=
  ∀ (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
      (firstKey secondKey : input.LocalizedRerootCompoundRule45Key),
    input.DeclarativeLocalizedRerootCompoundRule45Key target view fuel firstCursor firstKey →
    input.DeclarativeLocalizedRerootCompoundRule45Key target view fuel secondCursor secondKey →
    ∀ firstBuilt secondBuilt,
      input.buildLocalizedRerootCompoundRule45Key? target view fuel firstCursor = some firstBuilt →
      input.buildLocalizedRerootCompoundRule45Key? target view fuel secondCursor = some secondBuilt →
      input.compareLocalizedRerootCompoundThroughRule5 firstBuilt secondBuilt =
        input.compareLocalizedRerootCompoundThroughRule5 firstKey secondKey

/-- The exact executable builder agreement of `LocalizedEndpointSemanticCompletion` discharges the
comparison-record agreement: if the executable reproduces both keys literally, it certainly
reproduces their comparison record. -/
theorem LocalizedRule45CompoundComparisonRecordAgreement_of_builder
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat)
    (builder : input.LocalizedRule45EndpointBuilderAgreement target view fuel) :
    input.LocalizedRule45CompoundComparisonRecordAgreement target view fuel := by
  intro firstCursor secondCursor firstKey secondKey firstDerived secondDerived
    firstBuilt secondBuilt firstComputed secondComputed
  have firstEq : firstBuilt = firstKey :=
    Option.some.inj (firstComputed.symm.trans (builder firstCursor firstKey firstDerived))
  have secondEq : secondBuilt = secondKey :=
    Option.some.inj (secondComputed.symm.trans (builder secondCursor secondKey secondDerived))
  rw [firstEq, secondEq]








theorem LocalizedRule45CompoundComparisonRecordAgreement_of_referenceListAgreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat)
    (referenceAgreement : ∀ (cursor : input.LocalizedRerootCursor carrierFuel)
        (derived built : input.LocalizedRerootCompoundRule45Key),
      input.DeclarativeLocalizedRerootCompoundRule45Key target view fuel cursor derived →
      input.buildLocalizedRerootCompoundRule45Key? target view fuel cursor = some built →
      LocalizedRerootCompoundRule45ReferenceListAgreement input built derived) :
    input.LocalizedRule45CompoundComparisonRecordAgreement target view fuel := by
  intro firstCursor secondCursor firstKey secondKey firstDerived secondDerived
    firstBuilt secondBuilt firstComputed secondComputed
  have firstCongr := input.compareLocalizedRerootCompoundThroughRule5_congr_of_compiled
    target view firstCursor firstBuilt firstKey secondBuilt
    firstComputed firstDerived
    (referenceAgreement firstCursor firstKey firstBuilt firstDerived firstComputed)
  have secondCongr := input.compareLocalizedRerootCompoundThroughRule5_congr_of_compiled
    target view secondCursor secondBuilt secondKey firstKey
    secondComputed secondDerived
    (referenceAgreement secondCursor secondKey secondBuilt secondDerived secondComputed)
  calc
    input.compareLocalizedRerootCompoundThroughRule5 firstBuilt secondBuilt
        = input.compareLocalizedRerootCompoundThroughRule5 firstKey secondBuilt := firstCongr.1
    _ = input.compareLocalizedRerootCompoundThroughRule5 firstKey secondKey := secondCongr.2

/-- The `.ordering` of the comparison record is exactly the lawful Rules-4a--5 key comparator, so a
record agreement yields the comparator agreement the endpoint priority actually consumes. -/
theorem compareLocalizedRerootCompoundRule45Keys_eq_of_recordAgreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat)
    (agreement : input.LocalizedRule45CompoundComparisonRecordAgreement target view fuel)
    (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (firstKey secondKey : input.LocalizedRerootCompoundRule45Key)
    (firstDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel firstCursor firstKey)
    (secondDerived : input.DeclarativeLocalizedRerootCompoundRule45Key
      target view fuel secondCursor secondKey)
    (firstBuilt secondBuilt : input.LocalizedRerootCompoundRule45Key)
    (firstComputed : input.buildLocalizedRerootCompoundRule45Key?
      target view fuel firstCursor = some firstBuilt)
    (secondComputed : input.buildLocalizedRerootCompoundRule45Key?
      target view fuel secondCursor = some secondBuilt) :
    input.compareLocalizedRerootCompoundRule45Keys firstBuilt secondBuilt =
      input.compareLocalizedRerootCompoundRule45Keys firstKey secondKey := by
  have recordEq : input.compareLocalizedRerootCompoundThroughRule5 firstBuilt secondBuilt =
      input.compareLocalizedRerootCompoundThroughRule5 firstKey secondKey :=
    agreement firstCursor secondCursor firstKey secondKey
      firstDerived secondDerived firstBuilt secondBuilt firstComputed secondComputed
  calc
    input.compareLocalizedRerootCompoundRule45Keys firstBuilt secondBuilt
        = (input.compareLocalizedRerootCompoundThroughRule5 firstBuilt secondBuilt).ordering :=
          (input.compareLocalizedRerootCompoundThroughRule5_ordering
            firstBuilt secondBuilt).symm
    _ = (input.compareLocalizedRerootCompoundThroughRule5 firstKey secondKey).ordering :=
          congrArg ConstitutionalRule5Comparison.ordering recordEq
    _ = input.compareLocalizedRerootCompoundRule45Keys firstKey secondKey :=
          input.compareLocalizedRerootCompoundThroughRule5_ordering firstKey secondKey

/-! ## Comparison factorization with Rule-45 comparison agreement -/

/-- The cumulative Rules-1a--5 key comparison is unchanged when both Rule-3 projections are
observably equal and the Rules-4a--5 *comparison* agrees; the Rule-45 keys themselves may differ.
This is the observable generalization of
`compareLocalizedOccurrenceRule3Through5Keys_eq_of_observable`. -/
theorem compareLocalizedOccurrenceRule3Through5Keys_eq_of_observable_and_rule45Compare
    (input : CertifiedLocalizedCIPInput)
    (left right otherLeft otherRight : input.LocalizedOccurrenceRule3Through5Key)
    (rule3Left : input.localizedRerootRule3SpatialKeyObservable left.rule3 =
      input.localizedRerootRule3SpatialKeyObservable otherLeft.rule3)
    (rule3Right : input.localizedRerootRule3SpatialKeyObservable right.rule3 =
      input.localizedRerootRule3SpatialKeyObservable otherRight.rule3)
    (rule45Compared : input.compareLocalizedRerootCompoundRule45Keys left.rule45 right.rule45 =
      input.compareLocalizedRerootCompoundRule45Keys otherLeft.rule45 otherRight.rule45) :
    input.compareLocalizedOccurrenceRule3Through5Keys left right =
      input.compareLocalizedOccurrenceRule3Through5Keys otherLeft otherRight := by
  simp only [compareLocalizedOccurrenceRule3Through5Keys, compareLex, Ordering.byKey]
  rw [input.compareLocalizedRerootRecursiveRule3SpatialKeys_eq_of_observable_eq
    left.rule3 right.rule3 otherLeft.rule3 otherRight.rule3 rule3Left rule3Right,
    rule45Compared]

/-- Observable Rule-3 data and agreeing Rule-45 comparisons determine the complete endpoint
priority; the Rule-45 fields are not required to be equal. -/
theorem localizedRule3EndpointPriority_eq_of_rule3Observable_and_rule45Compare
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRule3EndpointKeyFrame)
    (firstEq : left.first = right.first)
    (secondEq : left.second = right.second)
    (rule3First : input.localizedRerootRule3SpatialKeyObservable left.firstKey.rule3 =
      input.localizedRerootRule3SpatialKeyObservable right.firstKey.rule3)
    (rule3Second : input.localizedRerootRule3SpatialKeyObservable left.secondKey.rule3 =
      input.localizedRerootRule3SpatialKeyObservable right.secondKey.rule3)
    (rule45Compared : input.compareLocalizedRerootCompoundRule45Keys
        left.firstKey.rule45 left.secondKey.rule45 =
      input.compareLocalizedRerootCompoundRule45Keys
        right.firstKey.rule45 right.secondKey.rule45) :
    input.localizedRule3EndpointPriority left =
      input.localizedRule3EndpointPriority right := by
  have compared :=
    input.compareLocalizedOccurrenceRule3Through5Keys_eq_of_observable_and_rule45Compare
      left.firstKey left.secondKey right.firstKey right.secondKey
      rule3First rule3Second rule45Compared
  unfold localizedRule3EndpointPriority
  rw [firstEq, secondEq, compared]

/-! ## Observable full-endpoint-frame construction -/

/-- Observable full-endpoint-frame construction: given an independently derived endpoint key frame
and canonical references, there is an actual compiled endpoint frame at the same cursors whose
complete endpoint priority agrees with the independent one.  The Rule-3 keys are only
comparison-visible (numeric projection) equal and the Rules-4a--5 keys only comparison-equal; the
frames themselves are never asserted equal.  This is the lower lemma for the original spatial and
cyclic readers, which consume the full frame compilation rather than the short-circuit endpoint
priority. -/
theorem exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith_observable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (callbackComplete : input.LocalizedRule3FrameCallbackCompleteness
      Rule3FrameMeaning rule3FrameOf)
    (rule45Agreement : input.LocalizedRule45CompoundComparisonRecordAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel))
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (frameDerived : input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
      target view Rule3FrameMeaning endpoint partner endpointCursor frame)
    (firstReference : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor frame.firstCursor frame.endpointFrame.first)
    (secondReference : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor frame.secondCursor frame.endpointFrame.second) :
    ∃ actualFrame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel,
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
          target view rule3FrameOf endpoint partner endpointCursor = some actualFrame ∧
        actualFrame.firstCursor = frame.firstCursor ∧
        actualFrame.secondCursor = frame.secondCursor ∧
        input.localizedRule3EndpointPriority actualFrame.endpointFrame =
          input.localizedRule3EndpointPriority frame.endpointFrame := by
  obtain ⟨firstCursorComputed, secondCursorComputed⟩ :=
    LocalizedRule3EndpointKeyFrameCanonicalReferences.cursor_eq input
      endpointCursor frame.firstCursor frame.secondCursor
      frame.endpointFrame.first frame.endpointFrame.second firstReference secondReference
  have candidatesEq :
      input.localizedRule3ExplicitSubstituents endpoint partner =
        [frame.endpointFrame.first, frame.endpointFrame.second] := frameDerived.1
  have frameMeaning := frameDerived.2.2.2.1
  have frameKeys := frameDerived.2.2.2.2.1
  have first45Derived := frameDerived.2.2.2.2.2.1
  have second45Derived := frameDerived.2.2.2.2.2.2
  obtain ⟨realized, realizedComputed, realizedObservable⟩ :=
    callbackComplete [frame.firstCursor, frame.secondCursor] frame.rule3Frame frameMeaning
  have keyLengths : realized.keys.length = frame.rule3Frame.keys.length := by
    simpa using congrArg List.length realizedObservable
  have frameKeyLength : frame.rule3Frame.keys.length = 2 := by
    rw [frameKeys]
    rfl
  have realizedKeyLength : realized.keys.length = 2 := by
    omega
  obtain ⟨realizedFirst, realizedSecond, realizedKeys⟩ :=
    List.length_eq_two.mp realizedKeyLength
  have observedKeys := realizedObservable
  unfold LocalizedRule3CanonicalKeyFrameObservableRel at observedKeys
  rw [realizedKeys, frameKeys] at observedKeys
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at observedKeys
  obtain ⟨observedFirst, observedSecond⟩ := observedKeys
  have firstValid : input.LocalizedRerootCursorValid frame.firstCursor :=
    firstReference.valid input endpointCursor frame.firstCursor frame.endpointFrame.first
  have secondValid : input.LocalizedRerootCursorValid frame.secondCursor :=
    secondReference.valid input endpointCursor frame.secondCursor frame.endpointFrame.second
  obtain ⟨first45Built, first45ComputedRaw⟩ :=
    input.exists_buildLocalizedRerootCompoundRule45Key?_at_twice
      target view frame.firstCursor firstValid
  obtain ⟨second45Built, second45ComputedRaw⟩ :=
    input.exists_buildLocalizedRerootCompoundRule45Key?_at_twice
      target view frame.secondCursor secondValid
  have first45Computed :
      input.buildLocalizedRerootCompoundRule45Key? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel)
          frame.firstCursor = some first45Built := by
    simpa [localizedOccurrenceRerootEvaluationFuel] using first45ComputedRaw
  have second45Computed :
      input.buildLocalizedRerootCompoundRule45Key? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel)
          frame.secondCursor = some second45Built := by
    simpa [localizedOccurrenceRerootEvaluationFuel] using second45ComputedRaw
  have rule45Compared :
      input.compareLocalizedRerootCompoundRule45Keys first45Built second45Built =
        input.compareLocalizedRerootCompoundRule45Keys
          frame.endpointFrame.firstKey.rule45 frame.endpointFrame.secondKey.rule45 :=
    input.compareLocalizedRerootCompoundRule45Keys_eq_of_recordAgreement
      target view (localizedOccurrenceRerootEvaluationFuel carrierFuel)
      rule45Agreement frame.firstCursor frame.secondCursor
      frame.endpointFrame.firstKey.rule45 frame.endpointFrame.secondKey.rule45
      first45Derived second45Derived first45Built second45Built
      first45Computed second45Computed
  have builtComputed :
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        target view rule3FrameOf endpoint partner endpointCursor =
      some
        { firstCursor := frame.firstCursor
          secondCursor := frame.secondCursor
          rule3Frame := realized
          endpointFrame :=
            { first := frame.endpointFrame.first
              second := frame.endpointFrame.second
              firstKey := { rule3 := realizedFirst, rule45 := first45Built }
              secondKey := { rule3 := realizedSecond, rule45 := second45Built } } } := by
    unfold buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
    simp only [candidatesEq, firstCursorComputed, secondCursorComputed, Option.pure_def,
      Option.bind_eq_bind, Option.bind_some, realizedComputed, realizedKeys,
      first45Computed, second45Computed]
  have priorityEq :=
    input.localizedRule3EndpointPriority_eq_of_rule3Observable_and_rule45Compare
      { first := frame.endpointFrame.first
        second := frame.endpointFrame.second
        firstKey := { rule3 := realizedFirst, rule45 := first45Built }
        secondKey := { rule3 := realizedSecond, rule45 := second45Built } }
      frame.endpointFrame
      rfl rfl observedFirst observedSecond rule45Compared
  exact
    ⟨{ firstCursor := frame.firstCursor
       secondCursor := frame.secondCursor
       rule3Frame := realized
       endpointFrame :=
         { first := frame.endpointFrame.first
           second := frame.endpointFrame.second
           firstKey := { rule3 := realizedFirst, rule45 := first45Built }
           secondKey := { rule3 := realizedSecond, rule45 := second45Built } } },
      builtComputed, rfl, rfl, priorityEq⟩

/-! ## Converse for the deferred full-key constructor -/

/-- The post-callback endpoint computation of the short-circuit selector reproduces the extracted
priority of an independently derived full endpoint frame.  The callback may return a different
frame and the executable Rules-4a--5 builder may return different keys; only the numeric Rule-3
observations and the Rule-45 comparison record are transported. -/
private theorem deferredShortCircuitEndpointResult_fullKey_eq_observable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (callbackComplete : input.LocalizedRule3FrameCallbackCompleteness
      Rule3FrameMeaning rule3FrameOf)
    (rule45Agreement : input.LocalizedRule45CompoundComparisonRecordAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel))
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (frameDerived : input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
      target view Rule3FrameMeaning endpoint partner endpointCursor frame)
    (firstReference : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor frame.firstCursor frame.endpointFrame.first)
    (secondReference : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor frame.secondCursor frame.endpointFrame.second) :
    (do
      let built ← input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        target view rule3FrameOf endpoint partner endpointCursor
      some ({ priority := input.localizedRule3EndpointPriority built.endpointFrame,
              firstCandidate := frame.endpointFrame.first } :
        input.LocalizedRule3ShortCircuitEndpointResult)) =
      some ({ priority := input.localizedRule3EndpointPriority frame.endpointFrame,
              firstCandidate := frame.endpointFrame.first } :
        input.LocalizedRule3ShortCircuitEndpointResult) := by
  obtain ⟨actualFrame, actualComputed, _firstCursorEq, _secondCursorEq, priorityEq⟩ :=
    input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith_observable
      target view rule3FrameOf Rule3FrameMeaning callbackComplete
      rule45Agreement endpoint partner endpointCursor frame frameDerived
      firstReference secondReference
  rw [actualComputed]
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, priorityEq]

/-- The deferred full-key constructor is reproduced exactly by the executable short-circuit
selector under the comparison-record agreement.  The constitutional branch is the same as in
`LocalizedEndpointSemanticCompletion`; the deferred branch only transports numeric Rule-3
observations and the Rule-45 comparison record. -/
theorem localizedRule3ShortCircuitEndpointPriority?_eq_of_declarative_fullKey_observable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (callbackComplete : input.LocalizedRule3FrameCallbackCompleteness
      Rule3FrameMeaning rule3FrameOf)
    (coherent : input.LocalizedRule3FrameMeaningConstitutionalCoherent Rule3FrameMeaning)
    (rule45Agreement : input.LocalizedRule45CompoundComparisonRecordAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel))
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (frameDerived : input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
      target view Rule3FrameMeaning endpoint partner endpointCursor frame)
    (deferred : input.compareLocalizedRerootCursorConstitutionalRoot
      frame.firstCursor frame.secondCursor = Ordering.eq)
    (firstReference : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor frame.firstCursor frame.endpointFrame.first)
    (secondReference : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor frame.secondCursor frame.endpointFrame.second) :
    input.localizedRule3ShortCircuitEndpointPriority?
        target view rule3FrameOf endpoint partner endpointCursor =
      some { priority := input.localizedRule3EndpointPriority frame.endpointFrame,
             firstCandidate := frame.endpointFrame.first } := by
  obtain ⟨firstCursorComputed, secondCursorComputed⟩ :=
    LocalizedRule3EndpointKeyFrameCanonicalReferences.cursor_eq input
      endpointCursor frame.firstCursor frame.secondCursor
      frame.endpointFrame.first frame.endpointFrame.second firstReference secondReference
  have candidatesEq :
      input.localizedRule3ExplicitSubstituents endpoint partner =
        [frame.endpointFrame.first, frame.endpointFrame.second] := frameDerived.1
  unfold localizedRule3ShortCircuitEndpointPriority?
  rw [candidatesEq]
  simp only [firstCursorComputed, secondCursorComputed, Option.pure_def,
    Option.bind_eq_bind, Option.bind_some, deferred]
  cases constitutionalComputed :
      input.compareLocalizedConstitutionalCursors? frame.firstCursor frame.secondCursor with
  | none =>
      exact deferredShortCircuitEndpointResult_fullKey_eq_observable
        input target view rule3FrameOf Rule3FrameMeaning callbackComplete
        rule45Agreement endpoint partner endpointCursor frame frameDerived
        firstReference secondReference
  | some order =>
      cases order with
      | eq =>
          exact deferredShortCircuitEndpointResult_fullKey_eq_observable
            input target view rule3FrameOf Rule3FrameMeaning callbackComplete
            rule45Agreement endpoint partner endpointCursor frame frameDerived
            firstReference secondReference
      | gt =>
          have firstConstitutional := (coherent [frame.firstCursor, frame.secondCursor]
            frame.rule3Frame frameDerived.2.2.2.1
            frame.firstCursor frame.secondCursor
            frame.endpointFrame.firstKey.rule3 frame.endpointFrame.secondKey.rule3
            rfl frameDerived.2.2.2.2.1).1
          have secondConstitutional := (coherent [frame.firstCursor, frame.secondCursor]
            frame.rule3Frame frameDerived.2.2.2.1
            frame.firstCursor frame.secondCursor
            frame.endpointFrame.firstKey.rule3 frame.endpointFrame.secondKey.rule3
            rfl frameDerived.2.2.2.2.1).2
          obtain ⟨firstConstitutionalFuel, firstConstitutionalDerived⟩ := firstConstitutional
          obtain ⟨secondConstitutionalFuel, secondConstitutionalDerived⟩ := secondConstitutional
          obtain ⟨execFirst, execSecond, execFirstComputed, execSecondComputed, execCompared⟩ :=
            input.compareLocalizedConstitutionalCursors?_computations
              frame.firstCursor frame.secondCursor Ordering.gt constitutionalComputed
          have firstObservable :
              constitutionalObservable execFirst =
                constitutionalObservable frame.endpointFrame.firstKey.rule3.constitutional :=
            input.declarative_constitutional_observable_unique
              (2 * (carrierFuel + 1) + 1) firstConstitutionalFuel frame.firstCursor
              execFirst frame.endpointFrame.firstKey.rule3.constitutional
              (input.buildLocalizedRerootRuleMajorKeyExec?_sound
                (2 * (carrierFuel + 1) + 1) frame.firstCursor execFirst execFirstComputed)
              firstConstitutionalDerived
          have secondObservable :
              constitutionalObservable execSecond =
                constitutionalObservable frame.endpointFrame.secondKey.rule3.constitutional :=
            input.declarative_constitutional_observable_unique
              (2 * (carrierFuel + 1) + 1) secondConstitutionalFuel frame.secondCursor
              execSecond frame.endpointFrame.secondKey.rule3.constitutional
              (input.buildLocalizedRerootRuleMajorKeyExec?_sound
                (2 * (carrierFuel + 1) + 1) frame.secondCursor execSecond execSecondComputed)
              secondConstitutionalDerived
          have comparedEq : OfficialRuleMajorKey.compare execFirst execSecond =
              OfficialRuleMajorKey.compare
                frame.endpointFrame.firstKey.rule3.constitutional
                frame.endpointFrame.secondKey.rule3.constitutional :=
            ruleMajor_compare_congr execFirst execSecond
              frame.endpointFrame.firstKey.rule3.constitutional
              frame.endpointFrame.secondKey.rule3.constitutional
              firstObservable secondObservable
          have constitutionalStrict : OfficialRuleMajorKey.compare
              frame.endpointFrame.firstKey.rule3.constitutional
              frame.endpointFrame.secondKey.rule3.constitutional = Ordering.gt := by
            rw [← comparedEq]
            exact execCompared
          have priorityEq := input.localizedRule3EndpointPriority_of_constitutional_gt
            frame.endpointFrame constitutionalStrict
          simp only [constitutionalComputed, priorityEq]
      | lt =>
          have firstConstitutional := (coherent [frame.firstCursor, frame.secondCursor]
            frame.rule3Frame frameDerived.2.2.2.1
            frame.firstCursor frame.secondCursor
            frame.endpointFrame.firstKey.rule3 frame.endpointFrame.secondKey.rule3
            rfl frameDerived.2.2.2.2.1).1
          have secondConstitutional := (coherent [frame.firstCursor, frame.secondCursor]
            frame.rule3Frame frameDerived.2.2.2.1
            frame.firstCursor frame.secondCursor
            frame.endpointFrame.firstKey.rule3 frame.endpointFrame.secondKey.rule3
            rfl frameDerived.2.2.2.2.1).2
          obtain ⟨firstConstitutionalFuel, firstConstitutionalDerived⟩ := firstConstitutional
          obtain ⟨secondConstitutionalFuel, secondConstitutionalDerived⟩ := secondConstitutional
          obtain ⟨execFirst, execSecond, execFirstComputed, execSecondComputed, execCompared⟩ :=
            input.compareLocalizedConstitutionalCursors?_computations
              frame.firstCursor frame.secondCursor Ordering.lt constitutionalComputed
          have firstObservable :
              constitutionalObservable execFirst =
                constitutionalObservable frame.endpointFrame.firstKey.rule3.constitutional :=
            input.declarative_constitutional_observable_unique
              (2 * (carrierFuel + 1) + 1) firstConstitutionalFuel frame.firstCursor
              execFirst frame.endpointFrame.firstKey.rule3.constitutional
              (input.buildLocalizedRerootRuleMajorKeyExec?_sound
                (2 * (carrierFuel + 1) + 1) frame.firstCursor execFirst execFirstComputed)
              firstConstitutionalDerived
          have secondObservable :
              constitutionalObservable execSecond =
                constitutionalObservable frame.endpointFrame.secondKey.rule3.constitutional :=
            input.declarative_constitutional_observable_unique
              (2 * (carrierFuel + 1) + 1) secondConstitutionalFuel frame.secondCursor
              execSecond frame.endpointFrame.secondKey.rule3.constitutional
              (input.buildLocalizedRerootRuleMajorKeyExec?_sound
                (2 * (carrierFuel + 1) + 1) frame.secondCursor execSecond execSecondComputed)
              secondConstitutionalDerived
          have comparedEq : OfficialRuleMajorKey.compare execFirst execSecond =
              OfficialRuleMajorKey.compare
                frame.endpointFrame.firstKey.rule3.constitutional
                frame.endpointFrame.secondKey.rule3.constitutional :=
            ruleMajor_compare_congr execFirst execSecond
              frame.endpointFrame.firstKey.rule3.constitutional
              frame.endpointFrame.secondKey.rule3.constitutional
              firstObservable secondObservable
          have constitutionalStrict : OfficialRuleMajorKey.compare
              frame.endpointFrame.firstKey.rule3.constitutional
              frame.endpointFrame.secondKey.rule3.constitutional = Ordering.lt := by
            rw [← comparedEq]
            exact execCompared
          have priorityEq := input.localizedRule3EndpointPriority_of_constitutional_lt
            frame.endpointFrame constitutionalStrict
          simp only [constitutionalComputed, priorityEq]

/-! ## The combined observable completion theorem -/

/-- Genuine local converse of `DeclarativeLocalizedRule3ShortCircuitEndpointResult` under the
comparison-record agreement: any independent endpoint derivation is reproduced by the executable
short-circuit selector, with the same priority and the same first candidate.  The strict
constructors are exactly the green strict branches; the full-key constructor needs callback
completeness up to numeric Rule-3 observation, constitutional coherence, canonical reference
selections, and the Rule-45 comparison-record agreement — never exact key equality. -/
theorem localizedRule3ShortCircuitEndpointPriority?_eq_of_declarative_observable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (callbackComplete : input.LocalizedRule3FrameCallbackCompleteness
      Rule3FrameMeaning rule3FrameOf)
    (coherent : input.LocalizedRule3FrameMeaningConstitutionalCoherent Rule3FrameMeaning)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (canonicalReferences : input.LocalizedRule3EndpointKeyFrameCanonicalReferences
      target view Rule3FrameMeaning endpoint partner endpointCursor)
    (rule45Agreement : input.LocalizedRule45CompoundComparisonRecordAgreement target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel))
    (result : input.LocalizedRule3ShortCircuitEndpointResult)
    (derived : input.DeclarativeLocalizedRule3ShortCircuitEndpointResult
      target view Rule3FrameMeaning endpoint partner endpointCursor result) :
    input.localizedRule3ShortCircuitEndpointPriority?
        target view rule3FrameOf endpoint partner endpointCursor = some result := by
  cases derived with
  | @rootRule1aStrict first second firstCursor secondCursor priority actualPair
      firstReference secondReference fresh =>
      exact input.localizedRule3ShortCircuitEndpointPriority?_eq_of_declarative_rootRule1aStrict
        target view rule3FrameOf Rule3FrameMeaning endpoint partner endpointCursor
        actualPair firstReference secondReference fresh
  | @constitutionalStrict first second firstCursor secondCursor priority firstKey secondKey fuel
      actualPair firstReference secondReference firstDerived secondDerived strict =>
      exact input.localizedRule3ShortCircuitEndpointPriority?_eq_of_declarative_constitutionalStrict
        target view rule3FrameOf Rule3FrameMeaning endpoint partner endpointCursor
        actualPair firstReference secondReference firstDerived secondDerived strict
  | fullKey frame frameDerived deferred =>
      obtain ⟨firstReference, secondReference⟩ := canonicalReferences frame frameDerived
      exact input.localizedRule3ShortCircuitEndpointPriority?_eq_of_declarative_fullKey_observable
        target view rule3FrameOf Rule3FrameMeaning callbackComplete coherent
        rule45Agreement endpoint partner endpointCursor frame frameDerived deferred
        firstReference secondReference

/-! ## The extended short-circuit compiler instantiation

`LocalizedEndpointFrameCompletenessBridge` discharges the three component interfaces of the
combined theorem for the *actual* extended short-circuit frame compiler
`buildLocalizedExtendedShortCircuitRule3FrameExec?` and its independent meaning
`DeclarativeLocalizedExtendedShortCircuitRule3Frame`.  Reusing those proofs verbatim, the only
retained premises are predecessor frame completeness and the weakened Rule-45 comparison-record
agreement — no exact-payload builder agreement. -/

/-- Genuine endpoint converse for the actual extended short-circuit frame compiler under the
comparison-record agreement.  Any independent endpoint derivation whose shared Rule-3 frame meaning
is `DeclarativeLocalizedExtendedShortCircuitRule3Frame` at `frameFuel` is reproduced by the
executable short-circuit selector running on `buildLocalizedExtendedShortCircuitRule3FrameExec?` at
the same fuel, with the same priority and the same first candidate.

The two retained premises are: predecessor frame completeness at `frameFuel` (used for the shared
frame callback), and the Rule-45 comparison-record agreement at the endpoint evaluation fuel.  No
equality of the independently derived and executable Rules-4a--5 keys, their payloads, or the
assembled frames is asserted. -/
theorem localizedRule3ShortCircuitEndpointPriority?_eq_of_declarative_observable_extended
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frameFuel : Nat)
    (frameComplete : LocalizedExtendedShortCircuitRule3FrameCompleteAt
      input target view frameFuel)
    (rule45Agreement : input.LocalizedRule45CompoundComparisonRecordAgreement target view
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
  input.localizedRule3ShortCircuitEndpointPriority?_eq_of_declarative_observable
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

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
