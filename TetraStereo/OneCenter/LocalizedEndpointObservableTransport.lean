import TetraStereo.OneCenter.LocalizedExtendedFrameCompleteness
import TetraStereo.OneCenter.LocalizedRule3ShortCircuitEndpoint
import TetraStereo.OneCenter.LocalizedRule3ShortCircuitSpatial
import TetraStereo.OneCenter.LocalizedRule3ShortCircuitOddSpatial

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-!
# Observable transport of the endpoint priority through callback frame keys

`LocalizedExtendedFrameCompleteness` proves that the cumulative Rule-3 key comparator is exactly
`compareLocalizedRerootRule3SpatialKeyObservable` applied to the numeric projection
`localizedRerootRule3SpatialKeyObservable`.  Two independently compiled callback frames therefore
need not be literally equal: under a tied sibling sort their `observations` payloads (and all
provenance state) may differ while every comparison-visible projection agrees.

This module transports the endpoint computation across that failure of literal frame equality.
The relation used is deliberately small:

* `LocalizedRule3CanonicalKeyFrameObservableRel` compares only
  `keys.map localizedRerootRule3SpatialKeyObservable`;
* `LocalizedRule3FrameCallbackObservableRel` is a full `Option` matching relation: `none/none` or
  `some/some` with observable-related frames.  In particular it never asserts that two successes
  are the same frame;
* `LocalizedRule3EndpointObservableRel` records the extracted endpoint data that actually feeds the
  priority: the two physical candidates, both Rule-3 observable projections, and both Rules-4a--5
  keys.  The last two are equal because the endpoint compiler calls the *same* actual Rules-4a--5
  function on the *same* target, view, fuel and canonical cursors; only the Rule-3 callback differs.

Proved here:

* the extracted `localizedRule3EndpointPriority` of a successful endpoint compilation is unchanged;
* the extracted `firstCandidate` (the endpoint frame's `first`) and `second` are unchanged;
* the minimal `LocalizedRule3ShortCircuitEndpointResult` projection is unchanged;
* the full `Option` result of `localizedRule3ShortCircuitEndpointPriority?` is equal for pointwise
  observably related callbacks;
* the ordinary and odd-cumulene minimal spatial `Option` results are equal, and the projected
  `LocalizedRule3SpatialNodeResult` observations agree whenever both sides succeed.

Boundary: this is congruence of the *existing executable selector* under observable callback
equivalence, not independent semantic completeness.  Nothing here claims that the full endpoint
compiler returns the same frame, that independently compiled frames are literally equal, or that a
declarative derivation implies executable success with exactly that frame.
-/

/-! ## Frame, callback and endpoint relations -/

/-- Two canonical Rule-3 frames are observably related when their numeric key projections agree in
order.  `rawKeys`, `coupled`, `excluded` and the `observations` payloads are not constrained. -/
def LocalizedRule3CanonicalKeyFrameObservableRel
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRule3CanonicalKeyFrame) : Prop :=
  left.keys.map (input.localizedRerootRule3SpatialKeyObservable) =
    right.keys.map (input.localizedRerootRule3SpatialKeyObservable)

/-- Pointwise callback relation: full `Option` matching, with observably related frames on the two
success branches.  A refusal on one side is related only to a refusal on the other. -/
def LocalizedRule3FrameCallbackObservableRel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) : Prop :=
  ∀ cursors,
    match before cursors, after cursors with
    | none, none => True
    | some left, some right =>
        input.LocalizedRule3CanonicalKeyFrameObservableRel left right
    | _, _ => False

/-- The extracted endpoint data that determines the complete endpoint priority.  The physical
candidates and the two Rule-3 observable projections may be transported; the Rules-4a--5 keys are
required equal because the actual Rules-4a--5 builder is callback-independent. -/
def LocalizedRule3EndpointObservableRel
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRule3EndpointKeyFrame) : Prop :=
  left.first = right.first ∧
    left.second = right.second ∧
    input.localizedRerootRule3SpatialKeyObservable left.firstKey.rule3 =
      input.localizedRerootRule3SpatialKeyObservable right.firstKey.rule3 ∧
    input.localizedRerootRule3SpatialKeyObservable left.secondKey.rule3 =
      input.localizedRerootRule3SpatialKeyObservable right.secondKey.rule3 ∧
    left.firstKey.rule45 = right.firstKey.rule45 ∧
    left.secondKey.rule45 = right.secondKey.rule45

/-! ## Comparison factorization -/

/-- Two Rule-3 spatial key comparisons agree whenever the corresponding observable projections
agree.  This is the comparison-factorization step supplied by
`LocalizedExtendedFrameCompleteness`. -/
theorem compareLocalizedRerootRecursiveRule3SpatialKeys_eq_of_observable_eq
    (input : CertifiedLocalizedCIPInput)
    (left right otherLeft otherRight : input.LocalizedRerootRecursiveRule3SpatialKey)
    (leftObservable : input.localizedRerootRule3SpatialKeyObservable left =
      input.localizedRerootRule3SpatialKeyObservable otherLeft)
    (rightObservable : input.localizedRerootRule3SpatialKeyObservable right =
      input.localizedRerootRule3SpatialKeyObservable otherRight) :
    input.compareLocalizedRerootRecursiveRule3SpatialKeys left right =
      input.compareLocalizedRerootRecursiveRule3SpatialKeys otherLeft otherRight := by
  simp only [input.compareLocalizedRerootRecursiveRule3SpatialKeys_eq_compareObservable,
    leftObservable, rightObservable]

/-- The cumulative Rules-1a--5 key comparison is unchanged when both Rule-3 projections are
observably equal and both Rules-4a--5 keys are literally equal. -/
theorem compareLocalizedOccurrenceRule3Through5Keys_eq_of_observable
    (input : CertifiedLocalizedCIPInput)
    (left right otherLeft otherRight : input.LocalizedOccurrenceRule3Through5Key)
    (rule3Left : input.localizedRerootRule3SpatialKeyObservable left.rule3 =
      input.localizedRerootRule3SpatialKeyObservable otherLeft.rule3)
    (rule3Right : input.localizedRerootRule3SpatialKeyObservable right.rule3 =
      input.localizedRerootRule3SpatialKeyObservable otherRight.rule3)
    (rule45Left : left.rule45 = otherLeft.rule45)
    (rule45Right : right.rule45 = otherRight.rule45) :
    input.compareLocalizedOccurrenceRule3Through5Keys left right =
      input.compareLocalizedOccurrenceRule3Through5Keys otherLeft otherRight := by
  simp only [compareLocalizedOccurrenceRule3Through5Keys, compareLex, Ordering.byKey]
  rw [input.compareLocalizedRerootRecursiveRule3SpatialKeys_eq_of_observable_eq
    left.rule3 right.rule3 otherLeft.rule3 otherRight.rule3 rule3Left rule3Right,
    rule45Left, rule45Right]

/-- Observable endpoint data determines the complete endpoint priority. -/
theorem localizedRule3EndpointPriority_eq_of_observableRel
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRule3EndpointKeyFrame)
    (rel : input.LocalizedRule3EndpointObservableRel left right) :
    input.localizedRule3EndpointPriority left =
      input.localizedRule3EndpointPriority right := by
  rcases rel with ⟨firstEq, secondEq, rule3First, rule3Second, rule45First, rule45Second⟩
  have compared := input.compareLocalizedOccurrenceRule3Through5Keys_eq_of_observable
    left.firstKey left.secondKey right.firstKey right.secondKey
    rule3First rule3Second rule45First rule45Second
  unfold localizedRule3EndpointPriority
  rw [firstEq, secondEq, compared]

/-! ## Decomposition of the endpoint compiler at its callback boundary

The only callback-dependent subterm of the parameterized endpoint compiler is the shared Rule-3
frame.  Every Rules-4a--5 call is made on the canonical cursors selected by the endpoint, which are
callback-independent.  The private `finishEndpointFrame?` below isolates the post-callback part so
that the congruence proof never has to claim equality of the embedded full frames. -/

private noncomputable def finishEndpointFrame?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat)
    (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (first second : input.Atom)
    (rule3Frame : input.LocalizedRule3CanonicalKeyFrame) :
    Option (input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel) :=
  match rule3Frame.keys with
  | [firstRule3, secondRule3] => do
      let firstRule45 ← input.buildLocalizedRerootCompoundRule45Key?
        target view fuel firstCursor
      let secondRule45 ← input.buildLocalizedRerootCompoundRule45Key?
        target view fuel secondCursor
      some
        { firstCursor
          secondCursor
          rule3Frame
          endpointFrame :=
            { first
              second
              firstKey := { rule3 := firstRule3, rule45 := firstRule45 }
              secondKey := { rule3 := secondRule3, rule45 := secondRule45 } } }
  | _ => none

/-- The parameterized endpoint compiler is exactly the canonical cursor selection followed by the
shared Rule-3 callback and `finishEndpointFrame?`. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_eq_bind
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel) :
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        target view rule3FrameOf endpoint partner endpointCursor =
      (match input.localizedRule3ExplicitSubstituents endpoint partner with
       | [first, second] =>
           Option.bind (input.localizedRule3ReferenceCursor? endpointCursor first)
             fun firstCursor =>
           Option.bind (input.localizedRule3ReferenceCursor? endpointCursor second)
             fun secondCursor =>
           Option.bind (rule3FrameOf [firstCursor, secondCursor])
             fun rule3Frame =>
           finishEndpointFrame? input target view
             (localizedOccurrenceRerootEvaluationFuel carrierFuel)
             firstCursor secondCursor first second rule3Frame
       | _ => none) := by
  unfold buildLocalizedRule3OccurrenceEndpointKeyFrameWith? finishEndpointFrame?
  rfl

/-- The post-callback computation respects observable key equivalence: with equal-length key lists
the `[firstRule3, secondRule3]` pattern succeeds on both sides or on neither, the actual Rules-4a--5
calls are literally the same, and the emitted endpoint frames are observably related. -/
private theorem finishEndpointFrame?_option_rel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat)
    (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (first second : input.Atom)
    (leftFrame rightFrame : input.LocalizedRule3CanonicalKeyFrame)
    (observable : input.LocalizedRule3CanonicalKeyFrameObservableRel leftFrame rightFrame) :
    match
      finishEndpointFrame? input target view fuel firstCursor secondCursor first second leftFrame,
      finishEndpointFrame? input target view fuel firstCursor secondCursor first second rightFrame
    with
    | none, none => True
    | some left, some right =>
        input.LocalizedRule3EndpointObservableRel left.endpointFrame right.endpointFrame
    | _, _ => False := by
  have lengthEq : leftFrame.keys.length = rightFrame.keys.length := by
    simpa using congrArg List.length observable
  unfold finishEndpointFrame?
  cases leftKeysEq : leftFrame.keys with
  | nil =>
      have rightKeysNil : rightFrame.keys = [] := by
        have h := lengthEq
        rw [leftKeysEq] at h
        simpa using h.symm
      simp [leftKeysEq, rightKeysNil]
  | cons firstRule3 tail =>
      cases tail with
      | nil =>
          have rightLength : rightFrame.keys.length = 1 := by
            have h := lengthEq
            rw [leftKeysEq] at h
            simpa using h.symm
          cases rightKeysEq : rightFrame.keys with
          | nil => simp [rightKeysEq] at rightLength
          | cons rightFirst rightTail =>
              cases rightTail with
              | nil => simp [leftKeysEq, rightKeysEq]
              | cons rightSecond rightRest =>
                  simp [rightKeysEq] at rightLength
      | cons secondRule3 tailRest =>
          cases tailRest with
          | nil =>
              have rightLength : rightFrame.keys.length = 2 := by
                have h := lengthEq
                rw [leftKeysEq] at h
                simpa using h.symm
              cases rightKeysEq : rightFrame.keys with
              | nil => simp [rightKeysEq] at rightLength
              | cons rightFirst rightTail =>
                  cases rightTail with
                  | nil => simp [rightKeysEq] at rightLength
                  | cons rightSecond rightRest =>
                      cases rightRest with
                      | nil =>
                          have observedList :
                              List.map input.localizedRerootRule3SpatialKeyObservable
                                  [firstRule3, secondRule3] =
                                List.map input.localizedRerootRule3SpatialKeyObservable
                                  [rightFirst, rightSecond] := by
                            simpa only [LocalizedRule3CanonicalKeyFrameObservableRel,
                              leftKeysEq, rightKeysEq] using observable
                          have observedKeys :
                              input.localizedRerootRule3SpatialKeyObservable firstRule3 =
                                  input.localizedRerootRule3SpatialKeyObservable rightFirst ∧
                                input.localizedRerootRule3SpatialKeyObservable secondRule3 =
                                  input.localizedRerootRule3SpatialKeyObservable rightSecond := by
                            simp only [List.map_cons, List.map_nil, List.cons.injEq,
                              and_true, true_and] at observedList
                            exact observedList
                          rcases observedKeys with ⟨observedFirst, observedSecond⟩
                          simp only [leftKeysEq, rightKeysEq]
                          cases firstRule45Computed :
                              input.buildLocalizedRerootCompoundRule45Key?
                                target view fuel firstCursor with
                          | none => simp [firstRule45Computed]
                          | some firstRule45 =>
                              cases secondRule45Computed :
                                  input.buildLocalizedRerootCompoundRule45Key?
                                    target view fuel secondCursor with
                              | none =>
                                  simp [firstRule45Computed, secondRule45Computed]
                              | some secondRule45 =>
                                  simp [firstRule45Computed, secondRule45Computed,
                                    LocalizedRule3EndpointObservableRel,
                                    observedFirst, observedSecond]
                      | cons thirdRight rightRest =>
                          simp [rightKeysEq] at rightLength
          | cons thirdRule3 tailRest =>
              have rightLength : 3 ≤ rightFrame.keys.length := by
                have h := lengthEq
                rw [leftKeysEq] at h
                rw [← h]
                simp
              cases rightKeysEq : rightFrame.keys with
              | nil => simp [rightKeysEq] at rightLength
              | cons rightFirst rightTail =>
                  cases rightTail with
                  | nil => simp [rightKeysEq] at rightLength
                  | cons rightSecond rightRest =>
                      cases rightRest with
                      | nil => simp [rightKeysEq] at rightLength
                      | cons rightThird rightRest =>
                          simp [leftKeysEq, rightKeysEq]

/-- Pointwise observable callback equivalence gives the full `Option` matching relation for the
parameterized endpoint compiler: both refuse, or both succeed with observably related extracted
endpoint frames.  The full embedded frames are never claimed equal. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_option_rel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (rel : input.LocalizedRule3FrameCallbackObservableRel before after)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel) :
    match
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        target view before endpoint partner endpointCursor,
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        target view after endpoint partner endpointCursor
    with
    | none, none => True
    | some left, some right =>
        input.LocalizedRule3EndpointObservableRel left.endpointFrame right.endpointFrame
    | _, _ => False := by
  rw [buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_eq_bind (rule3FrameOf := before),
    buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_eq_bind (rule3FrameOf := after)]
  generalize candidatesIdentity :
      input.localizedRule3ExplicitSubstituents endpoint partner = candidates
  cases candidates with
  | nil => simp [candidatesIdentity]
  | cons first rest =>
      cases rest with
      | nil => simp [candidatesIdentity]
      | cons second tail =>
          cases tail with
          | cons third more => simp [candidatesIdentity]
          | nil =>
              cases firstCursorComputed :
                  input.localizedRule3ReferenceCursor? endpointCursor first with
              | none => simp [candidatesIdentity, firstCursorComputed]
              | some firstCursor =>
                  cases secondCursorComputed :
                      input.localizedRule3ReferenceCursor? endpointCursor second with
                  | none =>
                      simp [candidatesIdentity, firstCursorComputed, secondCursorComputed]
                  | some secondCursor =>
                      cases beforeComputed : before [firstCursor, secondCursor] with
                      | none =>
                          cases afterComputed : after [firstCursor, secondCursor] with
                          | none =>
                              simp [candidatesIdentity, firstCursorComputed,
                                secondCursorComputed, beforeComputed, afterComputed]
                          | some rightFrame =>
                              have contradiction := rel [firstCursor, secondCursor]
                              rw [beforeComputed, afterComputed] at contradiction
                              exact contradiction.elim
                      | some leftFrame =>
                          cases afterComputed : after [firstCursor, secondCursor] with
                          | none =>
                              have contradiction := rel [firstCursor, secondCursor]
                              rw [beforeComputed, afterComputed] at contradiction
                              exact contradiction.elim
                          | some rightFrame =>
                              have frameRel :
                                  input.LocalizedRule3CanonicalKeyFrameObservableRel
                                    leftFrame rightFrame := by
                                have related := rel [firstCursor, secondCursor]
                                simpa [beforeComputed, afterComputed] using related
                              simpa [candidatesIdentity, firstCursorComputed,
                                secondCursorComputed, beforeComputed, afterComputed] using
                                finishEndpointFrame?_option_rel input target view
                                  (localizedOccurrenceRerootEvaluationFuel carrierFuel)
                                  firstCursor secondCursor first second
                                  leftFrame rightFrame frameRel

/-! ## Extracted endpoint transport -/

/-- The complete endpoint priority extracted from a successful parameterized compilation is
unchanged under pointwise observable callback equivalence. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_priority_eq_of_callback_observableRel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (rel : input.LocalizedRule3FrameCallbackObservableRel before after)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (leftFrame rightFrame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (leftComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
      target view before endpoint partner endpointCursor = some leftFrame)
    (rightComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
      target view after endpoint partner endpointCursor = some rightFrame) :
    input.localizedRule3EndpointPriority leftFrame.endpointFrame =
      input.localizedRule3EndpointPriority rightFrame.endpointFrame := by
  have optionRel := input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_option_rel
    target view before after rel endpoint partner endpointCursor
  rw [leftComputed, rightComputed] at optionRel
  exact input.localizedRule3EndpointPriority_eq_of_observableRel
    leftFrame.endpointFrame rightFrame.endpointFrame optionRel

/-- The first physical candidate retained by a successful parameterized compilation is unchanged
under pointwise observable callback equivalence. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_firstCandidate_eq_of_callback_observableRel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (rel : input.LocalizedRule3FrameCallbackObservableRel before after)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (leftFrame rightFrame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (leftComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
      target view before endpoint partner endpointCursor = some leftFrame)
    (rightComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
      target view after endpoint partner endpointCursor = some rightFrame) :
    leftFrame.endpointFrame.first = rightFrame.endpointFrame.first := by
  have optionRel := input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_option_rel
    target view before after rel endpoint partner endpointCursor
  rw [leftComputed, rightComputed] at optionRel
  exact optionRel.1

/-- The second physical candidate retained by a successful parameterized compilation is unchanged
under pointwise observable callback equivalence. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_secondCandidate_eq_of_callback_observableRel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (rel : input.LocalizedRule3FrameCallbackObservableRel before after)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (leftFrame rightFrame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (leftComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
      target view before endpoint partner endpointCursor = some leftFrame)
    (rightComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
      target view after endpoint partner endpointCursor = some rightFrame) :
    leftFrame.endpointFrame.second = rightFrame.endpointFrame.second := by
  have optionRel := input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_option_rel
    target view before after rel endpoint partner endpointCursor
  rw [leftComputed, rightComputed] at optionRel
  exact optionRel.2.1

/-- The minimal endpoint result extracted from a successful parameterized compilation is unchanged
under pointwise observable callback equivalence.  Only this extracted priority and candidate are
compared; the embedded full key frames are deliberately not claimed equal. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_minimalResult_eq_of_callback_observableRel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (rel : input.LocalizedRule3FrameCallbackObservableRel before after)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (leftFrame rightFrame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (leftComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
      target view before endpoint partner endpointCursor = some leftFrame)
    (rightComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
      target view after endpoint partner endpointCursor = some rightFrame) :
    ({ priority := input.localizedRule3EndpointPriority leftFrame.endpointFrame,
       firstCandidate := leftFrame.endpointFrame.first } :
        input.LocalizedRule3ShortCircuitEndpointResult) =
      { priority := input.localizedRule3EndpointPriority rightFrame.endpointFrame,
        firstCandidate := rightFrame.endpointFrame.first } := by
  have priorityEq :=
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_priority_eq_of_callback_observableRel
      target view before after rel endpoint partner endpointCursor
      leftFrame rightFrame leftComputed rightComputed
  have firstEq :=
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_firstCandidate_eq_of_callback_observableRel
      target view before after rel endpoint partner endpointCursor
      leftFrame rightFrame leftComputed rightComputed
  rw [priorityEq, firstEq]

/-! ## The short-circuit selector -/

/-- The deferred branch of the short-circuit selector is unchanged whenever the shared endpoint
compiler has the matching `Option` relation and the extracted priorities agree. -/
private theorem deferredShortCircuitEndpointOption_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (rel : input.LocalizedRule3FrameCallbackObservableRel before after)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (first : input.Atom) :
    (do
      let frame ← input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        target view before endpoint partner endpointCursor
      some ({ priority := input.localizedRule3EndpointPriority frame.endpointFrame,
               firstCandidate := first } :
        input.LocalizedRule3ShortCircuitEndpointResult)) =
      (do
        let frame ← input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
          target view after endpoint partner endpointCursor
        some ({ priority := input.localizedRule3EndpointPriority frame.endpointFrame,
                firstCandidate := first } :
          input.LocalizedRule3ShortCircuitEndpointResult)) := by
  have optionRel := input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_option_rel
    target view before after rel endpoint partner endpointCursor
  cases beforeComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
      target view before endpoint partner endpointCursor with
  | none =>
      have afterNone : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
          target view after endpoint partner endpointCursor = none := by
        rw [beforeComputed] at optionRel
        cases afterComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
            target view after endpoint partner endpointCursor with
        | none => rfl
        | some frame => simp [afterComputed] at optionRel
      simp [beforeComputed, afterNone]
  | some leftFrame =>
      rw [beforeComputed] at optionRel
      cases afterComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
          target view after endpoint partner endpointCursor with
      | none => simp [afterComputed] at optionRel
      | some rightFrame =>
          have endpointRel : input.LocalizedRule3EndpointObservableRel
              leftFrame.endpointFrame rightFrame.endpointFrame := by
            simpa [afterComputed] using optionRel
          have priorityEq := input.localizedRule3EndpointPriority_eq_of_observableRel
            leftFrame.endpointFrame rightFrame.endpointFrame endpointRel
          simp [beforeComputed, afterComputed, priorityEq]

/-- The full `Option` result of the short-circuit endpoint selector is equal under pointwise
observable callback equivalence.  Every non-deferred branch is callback-independent; the deferred
branch transports only the extracted endpoint priority, never the embedded frame. -/
theorem localizedRule3ShortCircuitEndpointPriority?_eq_of_callback_observableRel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (rel : input.LocalizedRule3FrameCallbackObservableRel before after)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel) :
    input.localizedRule3ShortCircuitEndpointPriority?
        target view before endpoint partner endpointCursor =
      input.localizedRule3ShortCircuitEndpointPriority?
        target view after endpoint partner endpointCursor := by
  unfold localizedRule3ShortCircuitEndpointPriority?
  generalize candidatesIdentity :
      input.localizedRule3ExplicitSubstituents endpoint partner = candidates
  cases candidates with
  | nil => simp [candidatesIdentity]
  | cons first rest =>
      cases rest with
      | nil => simp [candidatesIdentity]
      | cons second tail =>
          cases tail with
          | cons third more => simp [candidatesIdentity]
          | nil =>
              cases firstCursorComputed :
                  input.localizedRule3ReferenceCursor? endpointCursor first with
              | none => simp [candidatesIdentity, firstCursorComputed]
              | some firstCursor =>
                  cases secondCursorComputed :
                      input.localizedRule3ReferenceCursor? endpointCursor second with
                  | none =>
                      simp [candidatesIdentity, firstCursorComputed, secondCursorComputed]
                  | some secondCursor =>
                      cases rootComparison :
                          input.compareLocalizedRerootCursorConstitutionalRoot
                            firstCursor secondCursor with
                      | gt =>
                          simp [candidatesIdentity, firstCursorComputed,
                            secondCursorComputed, rootComparison]
                      | lt =>
                          simp [candidatesIdentity, firstCursorComputed,
                            secondCursorComputed, rootComparison]
                      | eq =>
                          cases constitutionalComputed :
                              input.compareLocalizedConstitutionalCursors?
                                firstCursor secondCursor with
                          | none =>
                              simpa [candidatesIdentity, firstCursorComputed,
                                secondCursorComputed, rootComparison,
                                constitutionalComputed] using
                                deferredShortCircuitEndpointOption_eq
                                  input target view before after rel endpoint partner
                                  endpointCursor first
                          | some order =>
                              cases order with
                              | gt =>
                                  simp [candidatesIdentity, firstCursorComputed,
                                    secondCursorComputed, rootComparison,
                                    constitutionalComputed]
                              | lt =>
                                  simp [candidatesIdentity, firstCursorComputed,
                                    secondCursorComputed, rootComparison,
                                    constitutionalComputed]
                              | eq =>
                                  simpa [candidatesIdentity, firstCursorComputed,
                                    secondCursorComputed, rootComparison,
                                    constitutionalComputed] using
                                    deferredShortCircuitEndpointOption_eq
                                      input target view before after rel endpoint partner
                                      endpointCursor first

/-! ## Minimal spatial results and node observations -/

/-- The ordinary minimal spatial `Option` result is equal under pointwise observable callback
equivalence. -/
theorem localizedRule3ShortCircuitSpatialUnitWith?_eq_of_callback_observableRel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (rel : input.LocalizedRule3FrameCallbackObservableRel before after) :
    input.localizedRule3ShortCircuitSpatialUnitWith? target occurrence view before =
      input.localizedRule3ShortCircuitSpatialUnitWith? target occurrence view after := by
  unfold localizedRule3ShortCircuitSpatialUnitWith?
  cases topologyComputed : input.localizedRule3PhysicalEndpointCursorFrame? occurrence with
  | none => simp [topologyComputed]
  | some topology =>
      have leftEq :=
        input.localizedRule3ShortCircuitEndpointPriority?_eq_of_callback_observableRel
          target view before after rel topology.left topology.right topology.leftCursor
      have rightEq :=
        input.localizedRule3ShortCircuitEndpointPriority?_eq_of_callback_observableRel
          target view before after rel topology.right topology.left topology.rightCursor
      simp [topologyComputed, leftEq, rightEq]

/-- The odd-cumulene minimal spatial `Option` result is equal under pointwise observable callback
equivalence.  The executable cursor recovery is replaced by its proved-equal original, and only the
two endpoint selectors are transported. -/
theorem localizedRule3ShortCircuitOddSpatialUnitWithExec?_eq_of_callback_observableRel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (rel : input.LocalizedRule3FrameCallbackObservableRel before after) :
    input.localizedRule3ShortCircuitOddSpatialUnitWithExec?
        target occurrence view before =
      input.localizedRule3ShortCircuitOddSpatialUnitWithExec?
        target occurrence view after := by
  unfold localizedRule3ShortCircuitOddSpatialUnitWithExec?
  simp only [localizedRule3OddCumuleneEndpointCursorFrameExec?_eq_original,
    ← localizedRule3ShortCircuitEndpointPriority?_eq_localizedRule3ShortCircuitEndpointPriorityExec?]
  cases topologyComputed : input.localizedRule3OddCumuleneEndpointCursorFrame?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
  | none => simp [topologyComputed]
  | some topology =>
      have leftEq :=
        input.localizedRule3ShortCircuitEndpointPriority?_eq_of_callback_observableRel
          target view before after rel topology.initial.left topology.initial.right
          topology.initial.leftCursor
      have rightEq :=
        input.localizedRule3ShortCircuitEndpointPriority?_eq_of_callback_observableRel
          target view before after rel topology.right topology.rightPartner
          topology.rightCursor
      simp [topologyComputed, leftEq, rightEq]

/-- The projected Rule-3 node observation of a successful ordinary minimal spatial computation is
reproduced under pointwise observable callback equivalence. -/
theorem localizedRule3ShortCircuitSpatialObservation_eq_of_callback_observableRel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (rel : input.LocalizedRule3FrameCallbackObservableRel before after)
    (result : input.LocalizedRule3ShortCircuitSpatialResult carrierFuel)
    (computed : input.localizedRule3ShortCircuitSpatialUnitWith?
      target occurrence view before = some result) :
    ∃ result',
      input.localizedRule3ShortCircuitSpatialUnitWith?
          target occurrence view after = some result' ∧
        input.localizedRule3ShortCircuitSpatialObservation result =
          input.localizedRule3ShortCircuitSpatialObservation result' := by
  refine ⟨result, ?_, rfl⟩
  rw [← input.localizedRule3ShortCircuitSpatialUnitWith?_eq_of_callback_observableRel
    target occurrence view before after rel]
  exact computed

/-- The projected Rule-3 node observation of a successful odd-cumulene minimal spatial computation
is reproduced under pointwise observable callback equivalence. -/
theorem localizedRule3ShortCircuitOddSpatialObservation_eq_of_callback_observableRel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (rel : input.LocalizedRule3FrameCallbackObservableRel before after)
    (result : input.LocalizedRule3ShortCircuitOddSpatialResult carrierFuel)
    (computed : input.localizedRule3ShortCircuitOddSpatialUnitWithExec?
      target occurrence view before = some result) :
    ∃ result',
      input.localizedRule3ShortCircuitOddSpatialUnitWithExec?
          target occurrence view after = some result' ∧
        input.localizedRule3ShortCircuitOddSpatialObservation result =
          input.localizedRule3ShortCircuitOddSpatialObservation result' := by
  refine ⟨result, ?_, rfl⟩
  rw [← input.localizedRule3ShortCircuitOddSpatialUnitWithExec?_eq_of_callback_observableRel
    target occurrence view before after rel]
  exact computed

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
