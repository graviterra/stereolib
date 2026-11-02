import TetraStereo.OneCenter.LocalizedEndpointObservableTransport
import TetraStereo.OneCenter.LocalizedRule3DeclarativePriorityAgreement

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-!
# Independent semantic completion of the Rule-3 short-circuit endpoint

`LocalizedEndpointObservableTransport` proves *congruence*: the executable short-circuit selector is
unchanged under a pointwise observable relation between two callbacks.  That is a statement about
the executable compared with itself.  This module proves the genuinely different *semantic
completion* direction: an independent, purely declarative derivation
`DeclarativeLocalizedRule3ShortCircuitEndpointResult` determines the executable answer, including
both its priority and its first candidate.

The strict constructors (`rootRule1aStrict` and `constitutionalStrict`) are decided before the
shared Rule-3 callback is ever consulted, so their converse needs no callback hypotheses at all.
The proof reuses the independent constitutional uniqueness of
`LocalizedRule3DeclarativePriorityAgreement` and the first-sphere head comparison lemmas of
`OfficialRuleMajorKey`; in particular it derives, rather than assumes, the agreement between the
root-atomic-number shortcut and the complete constitutional comparison.

The `fullKey` constructor genuinely reaches the callback.  Its converse needs three local
interfaces, each of which is supplied by the recursive frame induction and none of which is the
desired conclusion:

* `LocalizedRule3FrameCallbackCompleteness` — the callback returns *some* frame whose
  comparison-visible key projections numerically agree with every independently meaningful frame.
  The frames themselves are never required to be equal.
* `LocalizedRule3FrameMeaningConstitutionalCoherent` — every key of an independently meaningful
  shared Rule-3 frame carries an independently derived constitutional projection at its cursor.
* `LocalizedRule45EndpointBuilderAgreement` — the executable Rules-4a--5 builder reproduces the
  independently derived Rules-4a--5 key at a cursor.  This is the exact transport form of the
  still-external `u_rule45_semantic_agreement`; the bridge lemma
  `LocalizedRule45EndpointBuilderAgreement_of_canonical` shows that a proof that declarative
  Rules-4a--5 derivations are canonical discharges it.

Canonical reference selections (`localizedRule3ReferenceCursor?_eq_some_iff`) pin the two cursors
that the executable selects to the cursors of the independent frame; this is recorded as the
interface `LocalizedRule3EndpointKeyFrameCanonicalReferences`.

Nothing here assumes the desired priority agreement, fabricates a stereo frame, or claims an exact
payload equality between independently compiled frames.
-/

/-! ## Local callback and coherence interfaces -/

/-- The shared Rule-3 callback is complete for its independent meaning *up to comparison-visible
key agreement*: for every independently meaningful frame it realises some frame whose numeric key
projection is pointwise equal.  Raw payloads, provenance and lower observations are not compared. -/
def LocalizedRule3FrameCallbackCompleteness
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) : Prop :=
  ∀ cursors frame, Rule3FrameMeaning cursors frame →
    ∃ realized,
      rule3FrameOf cursors = some realized ∧
        input.LocalizedRule3CanonicalKeyFrameObservableRel realized frame

/-- Coherence of an independent shared-frame meaning: the constitutional projection of each of the
two endpoint keys is itself independently derived at the corresponding cursor.  The existential
fuels keep independent derivations at possibly different recursion budgets. -/
def LocalizedRule3FrameMeaningConstitutionalCoherent
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel) : Prop :=
  ∀ cursors frame, Rule3FrameMeaning cursors frame →
    ∀ (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
      (firstKey secondKey : input.LocalizedRerootRecursiveRule3SpatialKey),
      cursors = [firstCursor, secondCursor] →
      frame.keys = [firstKey, secondKey] →
      (∃ fuel,
        input.DeclarativeLocalizedRerootRuleMajorKey fuel firstCursor firstKey.constitutional) ∧
      (∃ fuel,
        input.DeclarativeLocalizedRerootRuleMajorKey fuel secondCursor secondKey.constitutional)

/-- The executable Rules-4a--5 builder reproduces a given independent Rules-4a--5 key.  This is the
precise component equality consumed by the `fullKey` transport below. -/
def LocalizedRule45EndpointBuilderAgreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) : Prop :=
  ∀ (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCompoundRule45Key),
    input.DeclarativeLocalizedRerootCompoundRule45Key target view fuel cursor key →
      input.buildLocalizedRerootCompoundRule45Key? target view fuel cursor = some key

/-- Semantic agreement in its canonical form: every independently derived Rules-4a--5 key is
canonical.  This is the shape of the still-external `u_rule45_semantic_agreement` lemma. -/
def LocalizedRule45DeclarativeCanonicalAgreement
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) : Prop :=
  ∀ (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCompoundRule45Key),
    input.DeclarativeLocalizedRerootCompoundRule45Key target view fuel cursor key →
      input.CanonicalLocalizedRerootCompoundRule45Key target view fuel cursor key

/-- Canonical reference selections for an independently derived endpoint frame.  The singleton
check of `localizedRule3ReferenceCursor?` is exactly canonicality, so this interface pins the two
cursors the executable selects to the frame's own cursors. -/
def LocalizedRule3EndpointKeyFrameCanonicalReferences
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel) : Prop :=
  ∀ frame,
    input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
      target view Rule3FrameMeaning endpoint partner endpointCursor frame →
      input.CanonicalLocalizedRule3ReferenceCursor
          endpointCursor frame.firstCursor frame.endpointFrame.first ∧
        input.CanonicalLocalizedRule3ReferenceCursor
          endpointCursor frame.secondCursor frame.endpointFrame.second

/-- Declarative-canonicity of Rules-4a--5 discharges the executable builder agreement through the
exact success criterion of `buildLocalizedRerootCompoundRule45Key?`. -/
theorem LocalizedRule45EndpointBuilderAgreement_of_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat)
    (agreement : input.LocalizedRule45DeclarativeCanonicalAgreement target view fuel) :
    input.LocalizedRule45EndpointBuilderAgreement target view fuel := by
  intro cursor key derived
  exact (input.buildLocalizedRerootCompoundRule45Key?_eq_some_iff_canonical
    target view fuel cursor key).mpr (agreement cursor key derived)

/-- Canonical reference selections yield the exact cursor computations of the executable
selector. -/
theorem LocalizedRule3EndpointKeyFrameCanonicalReferences.cursor_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (first second : input.Atom)
    (firstReference : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor firstCursor first)
    (secondReference : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor secondCursor second) :
    input.localizedRule3ReferenceCursor? endpointCursor first = some firstCursor ∧
      input.localizedRule3ReferenceCursor? endpointCursor second = some secondCursor :=
  ⟨(input.localizedRule3ReferenceCursor?_eq_some_iff endpointCursor firstCursor first).mpr
      firstReference,
    (input.localizedRule3ReferenceCursor?_eq_some_iff endpointCursor secondCursor second).mpr
      secondReference⟩

/-! ## Root shortcut versus complete constitutional comparison

The executable root shortcut compares atomic numbers.  An independently derived constitutional
key records its cursor's atomic number as the first Rule-1a sphere, so a strict root difference is
already a strict difference of the complete constitutional comparison.  These two lemmas are what
prevent the shortcut and the complete comparison from disagreeing. -/

theorem declarative_ruleMajor_compare_gt_of_root_gt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel}
    {firstKey secondKey : OfficialRuleMajorKey input.Atom}
    {firstFuel secondFuel : Nat}
    (firstDerived : input.DeclarativeLocalizedRerootRuleMajorKey
      firstFuel firstCursor firstKey)
    (secondDerived : input.DeclarativeLocalizedRerootRuleMajorKey
      secondFuel secondCursor secondKey)
    (rootStrict : input.compareLocalizedRerootCursorConstitutionalRoot
      firstCursor secondCursor = Ordering.gt) :
    OfficialRuleMajorKey.compare firstKey secondKey = Ordering.gt := by
  have firstHead := input.declarative_constitutional_rule1a_head
    firstCursor firstFuel firstKey firstDerived
  have secondHead := input.declarative_constitutional_rule1a_head
    secondCursor secondFuel secondKey secondDerived
  have higher : input.localizedRerootCursorRootAtomicNumber secondCursor <
      input.localizedRerootCursorRootAtomicNumber firstCursor := by
    have compared : compare (input.localizedRerootCursorRootAtomicNumber firstCursor)
        (input.localizedRerootCursorRootAtomicNumber secondCursor) = Ordering.gt := by
      simpa [compareLocalizedRerootCursorConstitutionalRoot] using rootStrict
    exact compare_gt_iff_gt.mp compared
  have rule1a := MoleculeGraph.officialRuleMajorKey_compare_rule1a_gt_of_heads_gt
    firstHead secondHead higher
  simp only [OfficialRuleMajorKey.compare, compareLex, Ordering.byKey, rule1a,
    Ordering.gt_then]

theorem declarative_ruleMajor_compare_lt_of_root_lt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel}
    {firstKey secondKey : OfficialRuleMajorKey input.Atom}
    {firstFuel secondFuel : Nat}
    (firstDerived : input.DeclarativeLocalizedRerootRuleMajorKey
      firstFuel firstCursor firstKey)
    (secondDerived : input.DeclarativeLocalizedRerootRuleMajorKey
      secondFuel secondCursor secondKey)
    (rootStrict : input.compareLocalizedRerootCursorConstitutionalRoot
      firstCursor secondCursor = Ordering.lt) :
    OfficialRuleMajorKey.compare firstKey secondKey = Ordering.lt := by
  have firstHead := input.declarative_constitutional_rule1a_head
    firstCursor firstFuel firstKey firstDerived
  have secondHead := input.declarative_constitutional_rule1a_head
    secondCursor secondFuel secondKey secondDerived
  have lower : input.localizedRerootCursorRootAtomicNumber firstCursor <
      input.localizedRerootCursorRootAtomicNumber secondCursor := by
    have compared : compare (input.localizedRerootCursorRootAtomicNumber firstCursor)
        (input.localizedRerootCursorRootAtomicNumber secondCursor) = Ordering.lt := by
      simpa [compareLocalizedRerootCursorConstitutionalRoot] using rootStrict
    exact compare_lt_iff_lt.mp compared
  have rule1a := MoleculeGraph.officialRuleMajorKey_compare_rule1a_lt_of_heads_lt
    firstHead secondHead lower
  simp only [OfficialRuleMajorKey.compare, compareLex, Ordering.byKey, rule1a,
    Ordering.lt_then]

/-! ## Converse for the strict constructors -/

/-- The fresh-root constructor of the declarative endpoint result is reproduced exactly by the
executable short-circuit selector: same priority, same first candidate, no callback consulted. -/
theorem localizedRule3ShortCircuitEndpointPriority?_eq_of_declarative_rootRule1aStrict
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (_Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    {first second : input.Atom}
    {firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel}
    {priority : input.LocalizedRule3EndpointPriority}
    (actualPair : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstReference : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor firstCursor first)
    (secondReference : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor secondCursor second)
    (fresh : input.DeclarativeLocalizedRule3RootObservation
      first second firstCursor secondCursor priority) :
    input.localizedRule3ShortCircuitEndpointPriority?
        target view rule3FrameOf endpoint partner endpointCursor =
      some { priority := priority, firstCandidate := first } := by
  obtain ⟨firstCursorComputed, secondCursorComputed⟩ :=
    LocalizedRule3EndpointKeyFrameCanonicalReferences.cursor_eq input
      endpointCursor firstCursor secondCursor first second firstReference secondReference
  unfold localizedRule3ShortCircuitEndpointPriority?
  rw [actualPair]
  simp only [firstCursorComputed, secondCursorComputed, Option.pure_def,
    Option.bind_eq_bind, Option.bind_some]
  cases fresh with
  | firstSenior strict => simp only [strict]
  | secondSenior strict => simp only [strict]

/-- The strict complete-constitutional constructor is reproduced exactly by the executable
short-circuit selector.  When the roots tie, the executable's own complete constitutional keys
compare with the same strict direction as the independent keys, by independent constitutional
uniqueness; when a root already decides, the shortcut and the independent complete comparison
cannot disagree by the head-comparison lemmas above. -/
theorem localizedRule3ShortCircuitEndpointPriority?_eq_of_declarative_constitutionalStrict
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (_Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    {first second : input.Atom}
    {firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel}
    {priority : input.LocalizedRule3EndpointPriority}
    {firstKey secondKey : OfficialRuleMajorKey input.Atom}
    {fuel : Nat}
    (actualPair : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstReference : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor firstCursor first)
    (secondReference : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor secondCursor second)
    (firstDerived : input.DeclarativeLocalizedRerootRuleMajorKey fuel firstCursor firstKey)
    (secondDerived : input.DeclarativeLocalizedRerootRuleMajorKey fuel secondCursor secondKey)
    (strict : (OfficialRuleMajorKey.compare firstKey secondKey = Ordering.gt ∧
        priority = .senior first) ∨
      (OfficialRuleMajorKey.compare firstKey secondKey = Ordering.lt ∧
        priority = .senior second)) :
    input.localizedRule3ShortCircuitEndpointPriority?
        target view rule3FrameOf endpoint partner endpointCursor =
      some { priority := priority, firstCandidate := first } := by
  obtain ⟨firstCursorComputed, secondCursorComputed⟩ :=
    LocalizedRule3EndpointKeyFrameCanonicalReferences.cursor_eq input
      endpointCursor firstCursor secondCursor first second firstReference secondReference
  have firstValid := firstReference.valid input endpointCursor firstCursor first
  have secondValid := secondReference.valid input endpointCursor secondCursor second
  unfold localizedRule3ShortCircuitEndpointPriority?
  rw [actualPair]
  simp only [firstCursorComputed, secondCursorComputed, Option.pure_def,
    Option.bind_eq_bind, Option.bind_some]
  generalize rootComparison :
    input.compareLocalizedRerootCursorConstitutionalRoot firstCursor secondCursor = outcome
  cases outcome with
  | gt =>
      have keyGt := input.declarative_ruleMajor_compare_gt_of_root_gt
        firstDerived secondDerived rootComparison
      rcases strict with ⟨compared, priorityEq⟩ | ⟨compared, priorityEq⟩
      · simp only [rootComparison, priorityEq]
      · rw [keyGt] at compared
        cases compared
  | lt =>
      have keyLt := input.declarative_ruleMajor_compare_lt_of_root_lt
        firstDerived secondDerived rootComparison
      rcases strict with ⟨compared, priorityEq⟩ | ⟨compared, priorityEq⟩
      · rw [keyLt] at compared
        cases compared
      · simp only [rootComparison, priorityEq]
  | eq =>
      obtain ⟨order, constitutionalComputed⟩ :=
        input.compareLocalizedConstitutionalCursors?_total
          firstCursor secondCursor firstValid secondValid
      obtain ⟨execFirst, execSecond, execFirstComputed, execSecondComputed, execCompared⟩ :=
        input.compareLocalizedConstitutionalCursors?_computations
          firstCursor secondCursor order constitutionalComputed
      have firstObservable :
          constitutionalObservable execFirst = constitutionalObservable firstKey :=
        input.declarative_constitutional_observable_unique
          (2 * (carrierFuel + 1) + 1) fuel firstCursor execFirst firstKey
          (input.buildLocalizedRerootRuleMajorKeyExec?_sound
            (2 * (carrierFuel + 1) + 1) firstCursor execFirst execFirstComputed)
          firstDerived
      have secondObservable :
          constitutionalObservable execSecond = constitutionalObservable secondKey :=
        input.declarative_constitutional_observable_unique
          (2 * (carrierFuel + 1) + 1) fuel secondCursor execSecond secondKey
          (input.buildLocalizedRerootRuleMajorKeyExec?_sound
            (2 * (carrierFuel + 1) + 1) secondCursor execSecond execSecondComputed)
          secondDerived
      have comparedEq : OfficialRuleMajorKey.compare execFirst execSecond =
          OfficialRuleMajorKey.compare firstKey secondKey :=
        ruleMajor_compare_congr execFirst execSecond firstKey secondKey
          firstObservable secondObservable
      rcases strict with ⟨compared, priorityEq⟩ | ⟨compared, priorityEq⟩
      · have orderEq : order = Ordering.gt :=
          (execCompared.symm.trans comparedEq).trans compared
        subst order
        simp only [rootComparison, constitutionalComputed, orderEq, priorityEq]
      · have orderEq : order = Ordering.lt :=
          (execCompared.symm.trans comparedEq).trans compared
        subst order
        simp only [rootComparison, constitutionalComputed, orderEq, priorityEq]

/-! ## Converse for the deferred full-key constructor -/

/-- The post-callback endpoint computation of the short-circuit selector reproduces the extracted
priority of an independently derived full endpoint frame.  The callback may return a different
frame; only its comparison-visible Rule-3 projections and the independently derived Rules-4a--5
keys matter, and the latter are reproduced exactly by builder agreement. -/
private theorem deferredShortCircuitEndpointResult_fullKey_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (callbackComplete : input.LocalizedRule3FrameCallbackCompleteness
      Rule3FrameMeaning rule3FrameOf)
    (rule45Agreement : input.LocalizedRule45EndpointBuilderAgreement target view
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
  have first45Computed :
      input.buildLocalizedRerootCompoundRule45Key? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel)
          frame.firstCursor = some frame.endpointFrame.firstKey.rule45 :=
    rule45Agreement frame.firstCursor frame.endpointFrame.firstKey.rule45 first45Derived
  have second45Computed :
      input.buildLocalizedRerootCompoundRule45Key? target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel)
          frame.secondCursor = some frame.endpointFrame.secondKey.rule45 :=
    rule45Agreement frame.secondCursor frame.endpointFrame.secondKey.rule45 second45Derived
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
              firstKey :=
                { rule3 := realizedFirst
                  rule45 := frame.endpointFrame.firstKey.rule45 }
              secondKey :=
                { rule3 := realizedSecond
                  rule45 := frame.endpointFrame.secondKey.rule45 } } } := by
    unfold buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
    simp only [candidatesEq, firstCursorComputed, secondCursorComputed, Option.pure_def,
      Option.bind_eq_bind, Option.bind_some, realizedComputed, realizedKeys,
      first45Computed, second45Computed]
  have endpointObservable : input.LocalizedRule3EndpointObservableRel
      { first := frame.endpointFrame.first
        second := frame.endpointFrame.second
        firstKey :=
          { rule3 := realizedFirst
            rule45 := frame.endpointFrame.firstKey.rule45 }
        secondKey :=
          { rule3 := realizedSecond
            rule45 := frame.endpointFrame.secondKey.rule45 } }
      frame.endpointFrame := by
    unfold LocalizedRule3EndpointObservableRel
    exact ⟨rfl, rfl, observedFirst, observedSecond, rfl, rfl⟩
  have priorityEq := input.localizedRule3EndpointPriority_eq_of_observableRel
    _ frame.endpointFrame endpointObservable
  rw [builtComputed]
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, priorityEq]

/-- The deferred full-key constructor is reproduced exactly by the executable short-circuit
selector.  The executable may take the constitutional branch (then coherence and independent
constitutional uniqueness identify its decision with the complete endpoint priority) or the
deferred branch (then callback completeness and Rules-4a--5 builder agreement identify its
extracted priority).  In either case the first candidate is the frame's first candidate. -/
theorem localizedRule3ShortCircuitEndpointPriority?_eq_of_declarative_fullKey
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (callbackComplete : input.LocalizedRule3FrameCallbackCompleteness
      Rule3FrameMeaning rule3FrameOf)
    (coherent : input.LocalizedRule3FrameMeaningConstitutionalCoherent Rule3FrameMeaning)
    (rule45Agreement : input.LocalizedRule45EndpointBuilderAgreement target view
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
      exact deferredShortCircuitEndpointResult_fullKey_eq
        input target view rule3FrameOf Rule3FrameMeaning callbackComplete
        rule45Agreement endpoint partner endpointCursor frame frameDerived
        firstReference secondReference
  | some order =>
      cases order with
      | eq =>
          exact deferredShortCircuitEndpointResult_fullKey_eq
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

/-! ## The combined semantic completion theorem -/

/-- Genuine local converse of `DeclarativeLocalizedRule3ShortCircuitEndpointResult`: any
independent endpoint derivation is reproduced by the executable short-circuit selector, with the
same priority and the same first candidate.  The strict constructors need only canonical reference
selections, which they already carry; the full-key constructor additionally uses the three local
interfaces documented at the head of this module. -/
theorem localizedRule3ShortCircuitEndpointPriority?_eq_of_declarative
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
    (rule45Agreement : input.LocalizedRule45EndpointBuilderAgreement target view
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
      exact input.localizedRule3ShortCircuitEndpointPriority?_eq_of_declarative_fullKey
        target view rule3FrameOf Rule3FrameMeaning callbackComplete coherent
        rule45Agreement endpoint partner endpointCursor frame frameDerived deferred
        firstReference secondReference

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
