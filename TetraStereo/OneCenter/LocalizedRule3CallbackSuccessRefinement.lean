import TetraStereo.OneCenter.LocalizedMutualObservableCompletion
import TetraStereo.OneCenter.LocalizedEndpointObservableTransport
import TetraStereo.OneCenter.LocalizedRule3CallbackRefinement
import TetraStereo.OneCenter.LocalizedExtendedFallbackNoRead
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# One-way observational callback refinement for the actual extended Rule-3 node

This module proves the missing one-way callback-success lemma for the **actual** short
extended Rule-3 node `localizedRule3ExtendedShortCircuitNodeWithExec?`
(`LocalizedRule3ShortCircuitOddNode`).  Unlike the exact callback *agreement* results used by the
fully guarded recursion, the new statement only assumes that the refined callback succeeds with a
frame that is topology-equivalent to the old successful frame on the exact, executable request
list actually emitted by the node.  Old refusals may become new successes, and the two callbacks
need not agree anywhere else.

## The stable relation

```
LocalizedRule3CallbackFrameRefinesOn input requests before after :=
  ∀ cursors ∈ requests, ∀ oldFrame,
    before cursors = some oldFrame →
      ∃ newFrame,
        after cursors = some newFrame ∧
        LocalizedRule3ExtendedFrameTopologyEquivalent input oldFrame newFrame
```

`LocalizedRule3ExtendedFrameTopologyEquivalent` (from `LocalizedMutualObservableCompletion`)
preserves the comparison-visible Rule-3 projection pointwise, the full constitutional constitution,
the coupled flag and the excluded physical-unit membership.  It is strictly weaker than frame
equality: raw key payloads, key order and diagnostic observation payloads may differ.

## Main results

* `buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_refines` — the actual endpoint compiler
  preserves every successful compilation, with the same two selected reference cursors, pointwise
  topologically equivalent common Rule-3 keys, identical Rules-4/5 keys and observable-related
  endpoint frames.  Only the deferred full-frame branch ever reads the callback.
* `localizedRule3ShortCircuitEndpointPriorityExec?_refines` — every successful actual short
  endpoint priority is preserved exactly.  Strict root and strict complete-constitutional outcomes
  emit no request at all; the deferred branch transports the endpoint priority through the
  observable relation.
* `localizedRule3ShortCircuitSpatialUnitWithExec?_refines` /
  `localizedRule3ShortCircuitOddSpatialUnitWithExec?_refines` — the actual ordinary and planar-odd
  short-circuit spatial units, and hence their observations, are preserved exactly.
* `localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec?_observation_refines` /
  `localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec?_observation_refines` /
  `localizedRule3RequiredMonocyclicEZWithExec?_observation_refines` — the original eager spatial
  units, the planar-odd unit and the required-monocyclic E/Z unit preserve their exact projected
  node observation, because every successful selected priority, comparison record and reference
  atom is already fixed by the old success.  No geometry domain is needed: the priority-keyed unit
  and its geometry record are reused unchanged.
* `localizedDescriptorBearingRule3NodeWithExec?_callback_refines` and
  `localizedRule3ShortCircuitNodeWithExec?_callback_refines` — every successful outer `some` result
  of the original and ordinary short-circuit node is preserved, including `some none`, both
  route paths and the callback-free joint route-certificate fallback. These one-way theorems
  make no claim about an old outer `none`.
* `localizedRule3ExtendedShortCircuitNodeWithExec?_callback_refines` — the final theorem for the
  actual extended node on the actual `rule3ExtendedNodeCallbackRequests`: every successful old
  `Option (Option LocalizedRule3SpatialNodeResult)` is preserved with the same old observation.
  The nonordinary odd route uses the exact odd short spatial unit; the ordinary fallback delegates
  to the short node theorem.
* `localizedRule3ExtendedShortCircuitNodeWithExec?_callback_refines_of_exclusion_equivalent`
  transports the successful result to a membership-equivalent exclusion list (only membership is
  read), and `localizedRule3ExtendedShortCircuitNodeWithExec?_optionSuccessRefines` exposes the
  final statement in `OptionSuccessRefines` form for the fully guarded builder.
* `localizedRule3ShortCircuitEndpointPriorityExec?_refines`,
  `localizedRule3ShortCircuitSpatialUnitWithExec?_refines` /
  `localizedRule3ShortCircuitOddSpatialUnitWithExec?_refines` — the actual short endpoint priority
  and the actual ordinary/planar-odd short spatial units are preserved exactly on their actual,
  restricted request lists.

All exported declarations carry a direct `assert_kernel_only` guard at the end of the module.
-/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

/-! ## The stable relation and its basic algebra -/

/-- **Stable one-way observational callback refinement.**  On every cursor list in `requests`, an
old successful frame must be matched by a new successful frame related by the existing extended
frame topology equivalence.  No condition is placed on old refusals or on cursors outside the
list. -/
def LocalizedRule3CallbackFrameRefinesOn
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (requests : List (List (input.LocalizedRerootCursor carrierFuel)))
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) : Prop :=
  ∀ cursors ∈ requests, ∀ oldFrame,
    before cursors = some oldFrame →
      ∃ newFrame,
        after cursors = some newFrame ∧
        input.LocalizedRule3ExtendedFrameTopologyEquivalent oldFrame newFrame

/-- One-way refinement restricts to any sub-list of requests. -/
theorem LocalizedRule3CallbackFrameRefinesOn.mono
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {requests requests' : List (List (input.LocalizedRerootCursor carrierFuel))}
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (subset : ∀ request ∈ requests', request ∈ requests)
    (refines : input.LocalizedRule3CallbackFrameRefinesOn requests before after) :
    input.LocalizedRule3CallbackFrameRefinesOn requests' before after :=
  fun cursors member => refines cursors (subset cursors member)

/-! ## Topology equivalence projects to the comparison-observable relation -/

private theorem forall₂_spatialKeyTopology_refl
    (input : CertifiedLocalizedCIPInput) :
    ∀ keys : List input.LocalizedRerootRecursiveRule3SpatialKey,
      List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) keys keys
  | [] => List.Forall₂.nil
  | _ :: rest =>
      List.Forall₂.cons (LocalizedRule3SpatialKeyTopologyEquivalent.refl input _)
        (forall₂_spatialKeyTopology_refl input rest)

/-- Extended frame topology equivalence is reflexive. -/
theorem LocalizedRule3ExtendedFrameTopologyEquivalent_refl
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedRule3CanonicalKeyFrame) :
    input.LocalizedRule3ExtendedFrameTopologyEquivalent frame frame :=
  ⟨forall₂_spatialKeyTopology_refl input frame.rawKeys,
    forall₂_spatialKeyTopology_refl input frame.keys,
    rfl,
    fun _ => Iff.rfl⟩

/-- Exact callback agreement on the request list is a special case of one-way refinement: the old
successful frame is itself the new frame, and extended frame topology equivalence is reflexive. -/
theorem LocalizedRule3CallbackFrameRefinesOn.of_agrees
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (requests : List (List (input.LocalizedRerootCursor carrierFuel)))
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (agree : input.Rule3CallbackAgreesOn requests before after) :
    input.LocalizedRule3CallbackFrameRefinesOn requests before after := by
  intro cursors member oldFrame computed
  refine ⟨oldFrame, ?_, ?_⟩
  · have same := agree cursors member
    rw [← same]
    exact computed
  · exact input.LocalizedRule3ExtendedFrameTopologyEquivalent_refl oldFrame

/-- The common-key component of extended frame topology equivalence, exposed as the pointwise
relation needed by the endpoint compiler. -/
theorem LocalizedRule3ExtendedFrameTopologyEquivalent.keys_forall₂
    (input : CertifiedLocalizedCIPInput)
    {old new : input.LocalizedRule3CanonicalKeyFrame}
    (rel : input.LocalizedRule3ExtendedFrameTopologyEquivalent old new) :
    List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input) old.keys new.keys :=
  rel.2.1

/-- Extended frame topology equivalence projects to equality of the comparison-visible
observable lists. -/
theorem LocalizedRule3ExtendedFrameTopologyEquivalent.keys_observable_eq
    (input : CertifiedLocalizedCIPInput)
    {old new : input.LocalizedRule3CanonicalKeyFrame}
    (rel : input.LocalizedRule3ExtendedFrameTopologyEquivalent old new) :
    old.keys.map input.localizedRerootRule3SpatialKeyObservable =
      new.keys.map input.localizedRerootRule3SpatialKeyObservable :=
  input.map_localizedRerootRule3SpatialKeyObservable_eq_of_forall₂
    old.keys new.keys rel.2.1

/-! ## Endpoint compilation refinement -/

/-- One-way relation between two successful occurrence-local endpoint compilations: the same two
selected canonical cursors, topologically equivalent common Rule-3 keys, and observable-related
endpoint frames (identical first/second atoms and Rules-4/5 keys).  Diagnostic full Rule-3 key
payloads are deliberately not compared. -/
def LocalizedRule3OccurrenceEndpointRefines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (old new : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel) : Prop :=
  old.firstCursor = new.firstCursor ∧
    old.secondCursor = new.secondCursor ∧
    List.Forall₂ (LocalizedRule3SpatialKeyTopologyEquivalent input)
      old.rule3Frame.keys new.rule3Frame.keys ∧
    input.LocalizedRule3EndpointObservableRel old.endpointFrame new.endpointFrame

/-- The selected endpoint priority of a refined endpoint compilation is exactly preserved. -/
theorem LocalizedRule3OccurrenceEndpointRefines.priority_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {old new : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel}
    (rel : input.LocalizedRule3OccurrenceEndpointRefines old new) :
    input.localizedRule3EndpointPriority old.endpointFrame =
      input.localizedRule3EndpointPriority new.endpointFrame :=
  input.localizedRule3EndpointPriority_eq_of_observableRel
    old.endpointFrame new.endpointFrame rel.2.2.2

/-- **Endpoint compilation success refinement.**  On the two canonical cursor requests actually
emitted by an endpoint, every successful old compilation is matched by a successful new one:
the selected cursors are unchanged, the common Rule-3 keys are pointwise topology-equivalent, and
the endpoint frames are observable-related.  All Rules-4/5 key builds are callback-independent and
therefore identical. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (firstComputed : input.localizedRule3ReferenceCursorExec? endpointCursor first = some firstCursor)
    (secondComputed : input.localizedRule3ReferenceCursorExec? endpointCursor second = some secondCursor)
    (frameRefines : ∀ oldFrame,
      before [firstCursor, secondCursor] = some oldFrame →
        ∃ newFrame,
          after [firstCursor, secondCursor] = some newFrame ∧
          input.LocalizedRule3ExtendedFrameTopologyEquivalent oldFrame newFrame)
    (old : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (computed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
      target view before endpoint partner endpointCursor = some old) :
    ∃ new : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel,
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
        target view after endpoint partner endpointCursor = some new ∧
      input.LocalizedRule3OccurrenceEndpointRefines old new := by
  unfold buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec? at computed
  rw [candidates] at computed
  simp [firstComputed, secondComputed] at computed
  cases beforeComputed : before [firstCursor, secondCursor] with
  | none =>
      simp [beforeComputed] at computed
  | some beforeFrame =>
      simp [beforeComputed] at computed
      generalize keysIdentity : beforeFrame.keys = beforeKeys at computed
      cases beforeKeys with
      | nil =>
          simp [keysIdentity] at computed
      | cons b1 rest1 =>
          cases rest1 with
          | nil =>
              simp [keysIdentity] at computed
          | cons b2 rest2 =>
              cases rest2 with
              | cons b3 rest3 =>
                  simp [keysIdentity] at computed
              | nil =>
                  cases firstRule45Computed : input.buildLocalizedRerootCompoundRule45KeyExec?
                      target view (localizedOccurrenceRerootEvaluationFuel carrierFuel)
                      firstCursor with
                  | none =>
                      simp [keysIdentity, firstRule45Computed] at computed
                  | some firstRule45 =>
                      cases secondRule45Computed : input.buildLocalizedRerootCompoundRule45KeyExec?
                          target view (localizedOccurrenceRerootEvaluationFuel carrierFuel)
                          secondCursor with
                      | none =>
                          simp [keysIdentity, firstRule45Computed,
                            secondRule45Computed] at computed
                      | some secondRule45 =>
                          simp [keysIdentity, firstRule45Computed,
                            secondRule45Computed] at computed
                          subst old
                          obtain ⟨afterFrame, afterComputed, frameRel⟩ :=
                            frameRefines beforeFrame beforeComputed
                          have keysRel := frameRel.keys_forall₂
                          rw [keysIdentity] at keysRel
                          obtain ⟨a1, afterRest1, rel1, afterRestRel, afterKeys1⟩ :=
                            List.forall₂_cons_left_iff.mp keysRel
                          obtain ⟨a2, afterRest2, rel2, afterRestNil, afterRestEq⟩ :=
                            List.forall₂_cons_left_iff.mp afterRestRel
                          have afterRest2Nil : afterRest2 = [] :=
                            List.forall₂_nil_left_iff.mp afterRestNil
                          subst afterRest2Nil
                          have afterKeys : afterFrame.keys = [a1, a2] := by
                            rw [afterKeys1, afterRestEq]
                          refine ⟨
                            { firstCursor := firstCursor
                              secondCursor := secondCursor
                              rule3Frame := afterFrame
                              endpointFrame :=
                                { first := first
                                  second := second
                                  firstKey :=
                                    { rule3 := a1, rule45 := firstRule45 }
                                  secondKey :=
                                    { rule3 := a2, rule45 := secondRule45 } } },
                            ?_, ?_⟩
                          · unfold buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
                            simp [candidates, firstComputed, secondComputed,
                              afterComputed, afterKeys, firstRule45Computed,
                              secondRule45Computed]
                          · refine ⟨rfl, rfl, ?_, ?_⟩
                            · change List.Forall₂
                                (LocalizedRule3SpatialKeyTopologyEquivalent input)
                                beforeFrame.keys afterFrame.keys
                              rw [keysIdentity, afterKeys]
                              exact List.Forall₂.cons rel1
                                (List.Forall₂.cons rel2 List.Forall₂.nil)
                            · exact ⟨rfl, rfl, rel1.1, rel2.1, rfl, rfl⟩

/-- Executable endpoint compilation exposes its candidate pair, its two actual cursor requests
and its shared Rule-3 key boundary, exactly as the parameterized twin does. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_computations
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (computed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
      target view rule3FrameOf endpoint partner endpointCursor = some frame) :
    input.LocalizedRule3OccurrenceEndpointKeyFrameComputations
      target view rule3FrameOf endpoint partner endpointCursor frame := by
  have original : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
      target view rule3FrameOf endpoint partner endpointCursor = some frame :=
    (input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_eq_buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
      target view rule3FrameOf endpoint partner endpointCursor).trans computed
  have parts := input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_computations
    target view rule3FrameOf endpoint partner endpointCursor frame original
  exact
    { candidates := parts.candidates
      firstCursor := parts.firstCursor
      secondCursor := parts.secondCursor
      rule3Frame := parts.rule3Frame
      keys := parts.keys }

/-- Helper for the deferred branch of the short endpoint compiler: the full endpoint compilation
is refined on the one request that the short endpoint can emit, and the selected priority is
transported through the observable endpoint relation.  The frame's selected cursors and candidate
atoms are identified with the caller's, because both are deterministic functions of the same
substituent pair. -/
private theorem localizedRule3ShortCircuitEndpointPriorityExec?_deferred_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom) (cursor : input.LocalizedRerootCursor carrierFuel)
    (first second : input.Atom)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (firstComputed : input.localizedRule3ReferenceCursorExec? cursor first = some firstCursor)
    (secondComputed : input.localizedRule3ReferenceCursorExec? cursor second = some secondCursor)
    (root : input.compareLocalizedRerootCursorConstitutionalRoot firstCursor secondCursor =
      Ordering.eq)
    (constitutional : input.compareLocalizedConstitutionalCursors? firstCursor secondCursor =
      none ∨ ∃ order, order ≠ Ordering.gt ∧ order ≠ Ordering.lt ∧
        input.compareLocalizedConstitutionalCursors? firstCursor secondCursor = some order)
    (refines : input.LocalizedRule3CallbackFrameRefinesOn
      (input.rule3ShortEndpointCallbackRequests endpoint partner cursor) before after)
    (old : input.LocalizedRule3ShortCircuitEndpointResult)
    (computed : (do
      let frame ← input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
        target view before endpoint partner cursor
      some { priority := input.localizedRule3EndpointPriority frame.endpointFrame,
             firstCandidate := first } : Option input.LocalizedRule3ShortCircuitEndpointResult) =
        some old) :
    (do
      let frame ← input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
        target view after endpoint partner cursor
      some { priority := input.localizedRule3EndpointPriority frame.endpointFrame,
             firstCandidate := first } : Option input.LocalizedRule3ShortCircuitEndpointResult) =
        some old := by
  cases frameComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
      target view before endpoint partner cursor with
  | none => simp [frameComputed] at computed
  | some frame =>
      simp [frameComputed] at computed
      subst old
      have parts := input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_computations
        target view before endpoint partner cursor frame frameComputed
      have atoms : frame.endpointFrame.first = first ∧ frame.endpointFrame.second = second := by
        have pair : [frame.endpointFrame.first, frame.endpointFrame.second] = [first, second] :=
          parts.candidates.symm.trans candidates
        simpa using pair
      have firstComputed' : input.localizedRule3ReferenceCursor? cursor first = some firstCursor := by
        rw [input.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?]
        exact firstComputed
      have secondComputed' : input.localizedRule3ReferenceCursor? cursor second = some secondCursor := by
        rw [input.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?]
        exact secondComputed
      have frameFirst : frame.firstCursor = firstCursor := by
        have selected := parts.firstCursor
        rw [atoms.1] at selected
        exact Option.some.inj (selected.symm.trans firstComputed')
      have frameSecond : frame.secondCursor = secondCursor := by
        have selected := parts.secondCursor
        rw [atoms.2] at selected
        exact Option.some.inj (selected.symm.trans secondComputed')
      have firstSelected : input.localizedRule3ReferenceCursorExec? cursor
          frame.endpointFrame.first = some frame.firstCursor := by
        have selected := parts.firstCursor
        rw [input.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?] at selected
        exact selected
      have secondSelected : input.localizedRule3ReferenceCursorExec? cursor
          frame.endpointFrame.second = some frame.secondCursor := by
        have selected := parts.secondCursor
        rw [input.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?] at selected
        exact selected
      have member : [frame.firstCursor, frame.secondCursor] ∈
          input.rule3ShortEndpointCallbackRequests endpoint partner cursor := by
        rcases constitutional with hnone | ⟨order, hgt, hlt, hsome⟩
        · simp [rule3ShortEndpointCallbackRequests, parts.candidates, firstSelected,
            secondSelected, frameFirst, frameSecond, root, hnone]
        · cases order with
          | lt => exact absurd rfl hlt
          | eq =>
              simp [rule3ShortEndpointCallbackRequests, parts.candidates, firstSelected,
                secondSelected, frameFirst, frameSecond, root, hsome]
          | gt => exact absurd rfl hgt
      have member' : [firstCursor, secondCursor] ∈
          input.rule3ShortEndpointCallbackRequests endpoint partner cursor := by
        rw [← frameFirst, ← frameSecond]
        exact member
      obtain ⟨newFrame, newFrameComputed, frameRel⟩ :=
        input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_refines
          target view before after endpoint partner first second cursor
          candidates firstCursor secondCursor firstComputed secondComputed
          (fun oldFrame h => refines [firstCursor, secondCursor] member' oldFrame h)
          frame frameComputed
      have priorityEq := frameRel.priority_eq
      simp [newFrameComputed, ← priorityEq]

/-- **Short endpoint priority success refinement.**  Every successful actual short endpoint
priority is preserved exactly, on exactly the request list `rule3ShortEndpointCallbackRequests`.
Strict root and strict complete-constitutional outcomes consult no callback at all; only the
deferred full-frame branch transports the selected priority. -/
theorem localizedRule3ShortCircuitEndpointPriorityExec?_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom) (cursor : input.LocalizedRerootCursor carrierFuel)
    (refines : input.LocalizedRule3CallbackFrameRefinesOn
      (input.rule3ShortEndpointCallbackRequests endpoint partner cursor) before after)
    (old : input.LocalizedRule3ShortCircuitEndpointResult)
    (computed : input.localizedRule3ShortCircuitEndpointPriorityExec?
      target view before endpoint partner cursor = some old) :
    input.localizedRule3ShortCircuitEndpointPriorityExec?
      target view after endpoint partner cursor = some old := by
  unfold localizedRule3ShortCircuitEndpointPriorityExec? at computed ⊢
  split
  · rename_i first second candidates
    rw [candidates] at computed
    cases firstComputed : input.localizedRule3ReferenceCursorExec? cursor first with
    | none => simp [firstComputed] at computed
    | some firstCursor =>
      cases secondComputed : input.localizedRule3ReferenceCursorExec? cursor second with
      | none => simp [firstComputed, secondComputed] at computed
      | some secondCursor =>
        simp only [firstComputed, secondComputed, bind, Option.bind_some] at computed ⊢
        cases root : input.compareLocalizedRerootCursorConstitutionalRoot firstCursor secondCursor with
        | gt => simpa only [root] using computed
        | lt => simpa only [root] using computed
        | eq =>
          cases constitutional : input.compareLocalizedConstitutionalCursors? firstCursor secondCursor with
          | some order =>
            cases order with
            | gt => simpa only [root, constitutional] using computed
            | lt => simpa only [root, constitutional] using computed
            | eq =>
              have computed' : (do
                let frame ← input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
                  target view before endpoint partner cursor
                some { priority := input.localizedRule3EndpointPriority frame.endpointFrame,
                       firstCandidate := first } :
                  Option input.LocalizedRule3ShortCircuitEndpointResult) = some old := by
                simpa only [root, constitutional] using computed
              have result :=
                input.localizedRule3ShortCircuitEndpointPriorityExec?_deferred_refines
                  target view before after endpoint partner cursor first second candidates
                  firstCursor secondCursor firstComputed secondComputed root
                  (Or.inr ⟨Ordering.eq, by simp, by simp, constitutional⟩)
                  refines old computed'
              simpa only [root, constitutional] using result
          | none =>
              have computed' : (do
                let frame ← input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
                  target view before endpoint partner cursor
                some { priority := input.localizedRule3EndpointPriority frame.endpointFrame,
                       firstCandidate := first } :
                  Option input.LocalizedRule3ShortCircuitEndpointResult) = some old := by
                simpa only [root, constitutional] using computed
              have result :=
                input.localizedRule3ShortCircuitEndpointPriorityExec?_deferred_refines
                  target view before after endpoint partner cursor first second candidates
                  firstCursor secondCursor firstComputed secondComputed root
                  (Or.inl constitutional) refines old computed'
              simpa only [root, constitutional] using result
  · simp at computed

/-- **Ordinary short-circuit spatial unit success refinement.**  On the actual short spatial
request list every successful unit is preserved exactly: both short endpoint priorities are
preserved, and the priority-keyed geometry unit is callback-independent. -/
theorem localizedRule3ShortCircuitSpatialUnitWithExec?_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (topologyComputed : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence =
      some topology)
    (refines : input.LocalizedRule3CallbackFrameRefinesOn
      (input.rule3ShortSpatialCallbackRequests occurrence) before after)
    (old : input.LocalizedRule3ShortCircuitSpatialResult carrierFuel)
    (computed : input.localizedRule3ShortCircuitSpatialUnitWithExec?
      target occurrence view before = some old) :
    input.localizedRule3ShortCircuitSpatialUnitWithExec?
      target occurrence view after = some old := by
  unfold localizedRule3ShortCircuitSpatialUnitWithExec? at computed ⊢
  rw [topologyComputed] at computed ⊢
  have leftSubset : ∀ cursors,
      cursors ∈ input.rule3ShortEndpointCallbackRequests topology.left topology.right
        topology.leftCursor →
      cursors ∈ input.rule3ShortSpatialCallbackRequests occurrence := by
    intro cursors member
    simp only [rule3ShortSpatialCallbackRequests, topologyComputed, List.mem_append]
    exact Or.inl member
  have rightSubset : ∀ cursors,
      cursors ∈ input.rule3ShortEndpointCallbackRequests topology.right topology.left
        topology.rightCursor →
      cursors ∈ input.rule3ShortSpatialCallbackRequests occurrence := by
    intro cursors member
    simp only [rule3ShortSpatialCallbackRequests, topologyComputed, List.mem_append]
    exact Or.inr member
  cases leftComputed : input.localizedRule3ShortCircuitEndpointPriorityExec?
      target view before topology.left topology.right topology.leftCursor with
  | none => simp [leftComputed] at computed
  | some left =>
      cases rightComputed : input.localizedRule3ShortCircuitEndpointPriorityExec?
          target view before topology.right topology.left topology.rightCursor with
      | none => simp [leftComputed, rightComputed] at computed
      | some right =>
          cases unitComputed : input.localizedRule3ShortCircuitSpatialUnit?
              topology.left topology.right left right with
          | none => simp [leftComputed, rightComputed, unitComputed] at computed
          | some unit =>
              simp [leftComputed, rightComputed, unitComputed] at computed
              subst old
              have leftRefined := input.localizedRule3ShortCircuitEndpointPriorityExec?_refines
                target view before after topology.left topology.right topology.leftCursor
                (fun cursors member => refines cursors (leftSubset cursors member))
                left leftComputed
              have rightRefined := input.localizedRule3ShortCircuitEndpointPriorityExec?_refines
                target view before after topology.right topology.left topology.rightCursor
                (fun cursors member => refines cursors (rightSubset cursors member))
                right rightComputed
              simp [leftRefined, rightRefined, unitComputed]

/-- **Planar-odd short-circuit spatial unit success refinement.**  The same one-way argument on
the exact odd-route request list: both strict-priority endpoints are preserved exactly and the
extended priority-keyed geometry unit is callback-independent. -/
theorem localizedRule3ShortCircuitOddSpatialUnitWithExec?_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (topologyComputed : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some topology)
    (refines : input.LocalizedRule3CallbackFrameRefinesOn
      (input.rule3ShortOddCallbackRequests occurrence) before after)
    (old : input.LocalizedRule3ShortCircuitOddSpatialResult carrierFuel)
    (computed : input.localizedRule3ShortCircuitOddSpatialUnitWithExec?
      target occurrence view before = some old) :
    input.localizedRule3ShortCircuitOddSpatialUnitWithExec?
      target occurrence view after = some old := by
  unfold localizedRule3ShortCircuitOddSpatialUnitWithExec? at computed ⊢
  rw [topologyComputed] at computed ⊢
  have leftSubset : ∀ cursors,
      cursors ∈ input.rule3ShortEndpointCallbackRequests topology.initial.left
        topology.initial.right topology.initial.leftCursor →
      cursors ∈ input.rule3ShortOddCallbackRequests occurrence := by
    intro cursors member
    simp only [rule3ShortOddCallbackRequests, topologyComputed, List.mem_append]
    exact Or.inl member
  have rightSubset : ∀ cursors,
      cursors ∈ input.rule3ShortEndpointCallbackRequests topology.right
        topology.rightPartner topology.rightCursor →
      cursors ∈ input.rule3ShortOddCallbackRequests occurrence := by
    intro cursors member
    simp only [rule3ShortOddCallbackRequests, topologyComputed, List.mem_append]
    exact Or.inr member
  cases leftComputed : input.localizedRule3ShortCircuitEndpointPriorityExec?
      target view before topology.initial.left topology.initial.right
        topology.initial.leftCursor with
  | none => simp [leftComputed] at computed
  | some left =>
      cases rightComputed : input.localizedRule3ShortCircuitEndpointPriorityExec?
          target view before topology.right topology.rightPartner topology.rightCursor with
      | none => simp [leftComputed, rightComputed] at computed
      | some right =>
          cases unitComputed : input.localizedRule3ExtendedSpatialUnitOfPriorities?
              topology.initial.left topology.right left.priority right.priority with
          | none => simp [leftComputed, rightComputed, unitComputed] at computed
          | some unit =>
              simp [leftComputed, rightComputed, unitComputed] at computed
              subst old
              have leftRefined := input.localizedRule3ShortCircuitEndpointPriorityExec?_refines
                target view before after topology.initial.left topology.initial.right
                topology.initial.leftCursor
                (fun cursors member => refines cursors (leftSubset cursors member))
                left leftComputed
              have rightRefined := input.localizedRule3ShortCircuitEndpointPriorityExec?_refines
                target view before after topology.right topology.rightPartner topology.rightCursor
                (fun cursors member => refines cursors (rightSubset cursors member))
                right rightComputed
              simp [leftRefined, rightRefined, unitComputed]

/-! ## Original eager spatial units preserve their projected observation

The eager units store the two full endpoint compilations, but the node consumes only their
priority and the nonstereogenic fallback atom.  The one-way endpoint relation fixes both, so the
after unit can keep the old priority-keyed geometry record and still project to the same
observation.  No geometry domain or exact diagnostic key payload is needed. -/

/-- **Original ordinary spatial unit observation refinement.**  Every successful eager ordinary
unit has a successful after unit with exactly the same node observation, on the full endpoint
request list `rule3OrdinaryCallbackRequests`. -/
theorem localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec?_observation_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (refines : input.LocalizedRule3CallbackFrameRefinesOn
      (input.rule3OrdinaryCallbackRequests occurrence) before after)
    (old : input.LocalizedRule3OccurrenceDescriptorBearingSpatialResult carrierFuel)
    (computed : input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec?
      target occurrence view before = some old) :
    ∃ new : input.LocalizedRule3OccurrenceDescriptorBearingSpatialResult carrierFuel,
      input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec?
        target occurrence view after = some new ∧
      input.localizedRule3DescriptorBearingObservation new =
        input.localizedRule3DescriptorBearingObservation old := by
  unfold localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec? at computed ⊢
  cases topologyComputed : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence with
  | none => simp [topologyComputed] at computed
  | some topology =>
      simp only [topologyComputed, bind, Option.bind_some] at computed
      cases leftComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
          target view before topology.left topology.right topology.leftCursor with
      | none => simp [leftComputed] at computed
      | some left =>
          simp only [leftComputed, bind, Option.bind_some] at computed
          cases rightComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
              target view before topology.right topology.left topology.rightCursor with
          | none => simp [rightComputed] at computed
          | some right =>
              simp only [rightComputed, bind, Option.bind_some] at computed
              cases unitComputed : input.localizedRule3DescriptorBearingSpatialUnitExec?
                  topology.left topology.right left.endpointFrame right.endpointFrame with
              | none => simp [unitComputed] at computed
              | some unit =>
                  simp only [unitComputed, bind, Option.bind_some] at computed
                  have oldEq : old =
                      { topology := topology
                        leftCompilation := left
                        rightCompilation := right
                        unit := unit } := by
                    simpa using (Option.some.inj computed).symm
                  subst old
                  have leftParts :=
                    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_computations
                      target view before topology.left topology.right topology.leftCursor
                      left leftComputed
                  have leftFirstExec : input.localizedRule3ReferenceCursorExec?
                      topology.leftCursor left.endpointFrame.first = some left.firstCursor := by
                    have h := leftParts.firstCursor
                    rw [input.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?] at h
                    exact h
                  have leftSecondExec : input.localizedRule3ReferenceCursorExec?
                      topology.leftCursor left.endpointFrame.second = some left.secondCursor := by
                    have h := leftParts.secondCursor
                    rw [input.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?] at h
                    exact h
                  have leftMember : [left.firstCursor, left.secondCursor] ∈
                      input.rule3OrdinaryCallbackRequests occurrence := by
                    simp [rule3OrdinaryCallbackRequests, topologyComputed,
                      rule3EndpointCallbackRequests, leftParts.candidates,
                      leftFirstExec, leftSecondExec]
                  obtain ⟨left', leftComputed', leftRel⟩ :=
                    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_refines
                      target view before after topology.left topology.right
                      left.endpointFrame.first left.endpointFrame.second topology.leftCursor
                      leftParts.candidates left.firstCursor left.secondCursor
                      leftFirstExec leftSecondExec
                      (fun oldFrame h => refines [left.firstCursor, left.secondCursor]
                        leftMember oldFrame h)
                      left leftComputed
                  have rightParts :=
                    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_computations
                      target view before topology.right topology.left topology.rightCursor
                      right rightComputed
                  have rightFirstExec : input.localizedRule3ReferenceCursorExec?
                      topology.rightCursor right.endpointFrame.first = some right.firstCursor := by
                    have h := rightParts.firstCursor
                    rw [input.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?] at h
                    exact h
                  have rightSecondExec : input.localizedRule3ReferenceCursorExec?
                      topology.rightCursor right.endpointFrame.second = some right.secondCursor := by
                    have h := rightParts.secondCursor
                    rw [input.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?] at h
                    exact h
                  have rightMember : [right.firstCursor, right.secondCursor] ∈
                      input.rule3OrdinaryCallbackRequests occurrence := by
                    simp [rule3OrdinaryCallbackRequests, topologyComputed,
                      rule3EndpointCallbackRequests, rightParts.candidates,
                      rightFirstExec, rightSecondExec]
                  obtain ⟨right', rightComputed', rightRel⟩ :=
                    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_refines
                      target view before after topology.right topology.left
                      right.endpointFrame.first right.endpointFrame.second topology.rightCursor
                      rightParts.candidates right.firstCursor right.secondCursor
                      rightFirstExec rightSecondExec
                      (fun oldFrame h => refines [right.firstCursor, right.secondCursor]
                        rightMember oldFrame h)
                      right rightComputed
                  have unitComputed' : input.localizedRule3DescriptorBearingSpatialUnitExec?
                      topology.left topology.right left'.endpointFrame right'.endpointFrame =
                        some unit := by
                    have framesEq : input.localizedRule3DescriptorBearingSpatialUnitExec?
                          topology.left topology.right left.endpointFrame right.endpointFrame =
                        input.localizedRule3DescriptorBearingSpatialUnitExec?
                          topology.left topology.right left'.endpointFrame right'.endpointFrame := by
                      unfold localizedRule3DescriptorBearingSpatialUnitExec?
                      rw [← leftRel.priority_eq, ← rightRel.priority_eq]
                    exact framesEq.symm.trans unitComputed
                  refine ⟨
                    { topology := topology
                      leftCompilation := left'
                      rightCompilation := right'
                      unit := unit }, ?_, ?_⟩
                  · simp only [topologyComputed, leftComputed', rightComputed',
                      unitComputed', bind, Option.bind_some]
                  · dsimp only [localizedRule3DescriptorBearingObservation]
                    rw [leftRel.2.2.2.1, rightRel.2.2.2.1]

/-- **Original planar-odd spatial unit observation refinement.**  The same argument on the full
odd endpoint list `rule3OddCallbackRequests`, with the extended priority-keyed unit. -/
theorem localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec?_observation_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (refines : input.LocalizedRule3CallbackFrameRefinesOn
      (input.rule3OddCallbackRequests occurrence) before after)
    (old : input.LocalizedRule3OddCumuleneDescriptorBearingSpatialResult carrierFuel)
    (computed : input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec?
      target occurrence view before = some old) :
    ∃ new : input.LocalizedRule3OddCumuleneDescriptorBearingSpatialResult carrierFuel,
      input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec?
        target occurrence view after = some new ∧
      input.localizedRule3OddCumuleneDescriptorBearingObservation new =
        input.localizedRule3OddCumuleneDescriptorBearingObservation old := by
  unfold localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec? at computed ⊢
  cases topologyComputed : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
  | none => simp [topologyComputed] at computed
  | some topology =>
      simp only [topologyComputed, bind, Option.bind_some] at computed
      cases leftComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
          target view before topology.initial.left topology.initial.right
            topology.initial.leftCursor with
      | none => simp [leftComputed] at computed
      | some left =>
          simp only [leftComputed, bind, Option.bind_some] at computed
          cases rightComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
              target view before topology.right topology.rightPartner topology.rightCursor with
          | none => simp [rightComputed] at computed
          | some right =>
              simp only [rightComputed, bind, Option.bind_some] at computed
              cases unitComputed : input.localizedRule3ExtendedDescriptorBearingSpatialUnitExec?
                  topology.initial.left topology.right left.endpointFrame right.endpointFrame with
              | none => simp [unitComputed] at computed
              | some unit =>
                  simp only [unitComputed, bind, Option.bind_some] at computed
                  have oldEq : old =
                      { topology := topology
                        leftCompilation := left
                        rightCompilation := right
                        unit := unit } := by
                    simpa using (Option.some.inj computed).symm
                  subst old
                  have leftParts :=
                    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_computations
                      target view before topology.initial.left topology.initial.right
                      topology.initial.leftCursor left leftComputed
                  have leftFirstExec : input.localizedRule3ReferenceCursorExec?
                      topology.initial.leftCursor left.endpointFrame.first =
                        some left.firstCursor := by
                    have h := leftParts.firstCursor
                    rw [input.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?] at h
                    exact h
                  have leftSecondExec : input.localizedRule3ReferenceCursorExec?
                      topology.initial.leftCursor left.endpointFrame.second =
                        some left.secondCursor := by
                    have h := leftParts.secondCursor
                    rw [input.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?] at h
                    exact h
                  have leftMember : [left.firstCursor, left.secondCursor] ∈
                      input.rule3OddCallbackRequests occurrence := by
                    simp [rule3OddCallbackRequests, topologyComputed,
                      rule3EndpointCallbackRequests, leftParts.candidates,
                      leftFirstExec, leftSecondExec]
                  obtain ⟨left', leftComputed', leftRel⟩ :=
                    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_refines
                      target view before after topology.initial.left topology.initial.right
                      left.endpointFrame.first left.endpointFrame.second
                      topology.initial.leftCursor
                      leftParts.candidates left.firstCursor left.secondCursor
                      leftFirstExec leftSecondExec
                      (fun oldFrame h => refines [left.firstCursor, left.secondCursor]
                        leftMember oldFrame h)
                      left leftComputed
                  have rightParts :=
                    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_computations
                      target view before topology.right topology.rightPartner
                      topology.rightCursor right rightComputed
                  have rightFirstExec : input.localizedRule3ReferenceCursorExec?
                      topology.rightCursor right.endpointFrame.first = some right.firstCursor := by
                    have h := rightParts.firstCursor
                    rw [input.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?] at h
                    exact h
                  have rightSecondExec : input.localizedRule3ReferenceCursorExec?
                      topology.rightCursor right.endpointFrame.second = some right.secondCursor := by
                    have h := rightParts.secondCursor
                    rw [input.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?] at h
                    exact h
                  have rightMember : [right.firstCursor, right.secondCursor] ∈
                      input.rule3OddCallbackRequests occurrence := by
                    simp [rule3OddCallbackRequests, topologyComputed,
                      rule3EndpointCallbackRequests, rightParts.candidates,
                      rightFirstExec, rightSecondExec]
                  obtain ⟨right', rightComputed', rightRel⟩ :=
                    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_refines
                      target view before after topology.right topology.rightPartner
                      right.endpointFrame.first right.endpointFrame.second topology.rightCursor
                      rightParts.candidates right.firstCursor right.secondCursor
                      rightFirstExec rightSecondExec
                      (fun oldFrame h => refines [right.firstCursor, right.secondCursor]
                        rightMember oldFrame h)
                      right rightComputed
                  have unitComputed' : input.localizedRule3ExtendedDescriptorBearingSpatialUnitExec?
                      topology.initial.left topology.right left'.endpointFrame
                        right'.endpointFrame = some unit := by
                    have framesEq :
                        input.localizedRule3ExtendedDescriptorBearingSpatialUnitExec?
                            topology.initial.left topology.right left.endpointFrame
                            right.endpointFrame =
                          input.localizedRule3ExtendedDescriptorBearingSpatialUnitExec?
                            topology.initial.left topology.right left'.endpointFrame
                            right'.endpointFrame := by
                      unfold localizedRule3ExtendedDescriptorBearingSpatialUnitExec?
                      rw [← leftRel.priority_eq, ← rightRel.priority_eq]
                    exact framesEq.symm.trans unitComputed
                  refine ⟨
                    { topology := topology
                      leftCompilation := left'
                      rightCompilation := right'
                      unit := unit }, ?_, ?_⟩
                  · simp only [topologyComputed, leftComputed', rightComputed',
                      unitComputed', bind, Option.bind_some]
                  · dsimp only [localizedRule3OddCumuleneDescriptorBearingObservation]
                    rw [leftRel.2.2.2.1, rightRel.2.2.2.1]

/-- **Original required-monocyclic E/Z observation refinement.**  On the ring request list the
route and policy decisions are callback-independent; only the two endpoint compilations read the
callback.  The priority-keyed unit, the monocyclic geometry and the required descriptor are
therefore exactly the same old values on both sides. -/
theorem localizedRule3RequiredMonocyclicEZWithExec?_observation_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (refines : input.LocalizedRule3CallbackFrameRefinesOn
      (input.rule3RingCallbackRequests occurrence) before after)
    (old : input.LocalizedRule3RequiredMonocyclicEZResult carrierFuel)
    (computed : input.localizedRule3RequiredMonocyclicEZWithExec?
      target occurrence view before = some old) :
    ∃ new : input.LocalizedRule3RequiredMonocyclicEZResult carrierFuel,
      input.localizedRule3RequiredMonocyclicEZWithExec?
        target occurrence view after = some new ∧
      input.localizedRule3RequiredMonocyclicEZObservation new =
        input.localizedRule3RequiredMonocyclicEZObservation old := by
  unfold localizedRule3RequiredMonocyclicEZWithExec? at computed ⊢
  cases routeComputed : input.localizedRule3CyclicAuthorityRouteExec? occurrence with
  | none => simp [routeComputed] at computed
  | some route =>
      cases route with
      | fullyCyclicCumulene => simp [routeComputed] at computed
      | ordinaryMonocyclicPolicyGap => simp [routeComputed] at computed
      | ordinaryNonmonocyclic => simp [routeComputed] at computed
      | ordinaryMonocyclicPolicy initial closure policyResult =>
          simp only [routeComputed, bind, Option.bind_some] at computed
          cases policyEq : policyResult.policy with
          | permanentlyOmit => simp [policyEq] at computed
          | requireEZ =>
              simp only [policyEq, bind, Option.bind_some] at computed
              cases leftComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
                  target view before initial.left initial.right initial.leftCursor with
              | none => simp [leftComputed] at computed
              | some left =>
                  simp only [leftComputed, bind, Option.bind_some] at computed
                  cases rightComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
                      target view before initial.right initial.left initial.rightCursor with
                  | none => simp [rightComputed] at computed
                  | some right =>
                      simp only [rightComputed, bind, Option.bind_some] at computed
                      cases unitComputed : input.localizedRule3DescriptorBearingSpatialUnitExec?
                          initial.left initial.right left.endpointFrame right.endpointFrame with
                      | none => simp [unitComputed] at computed
                      | some unit =>
                          simp only [unitComputed, bind, Option.bind_some] at computed
                          cases geometryComputed :
                              monocyclicSeniorLigandGeometryOfRule3? unit.geometry with
                          | none => simp [geometryComputed] at computed
                          | some cyclicGeometry =>
                              cases descriptorComputed :
                                  BlueBookP93.Cyclic.requiredMonocyclicEZDescriptor?
                                    policyResult.carrier.ring.card
                                    policyResult.doubleBondCount cyclicGeometry with
                              | none => simp [geometryComputed, descriptorComputed] at computed
                              | some descriptor =>
                                  simp only [geometryComputed, descriptorComputed, bind,
                                    Option.bind_some] at computed
                                  have oldEq : old =
                                      { initial := initial
                                        closure := closure
                                        policyResult := policyResult
                                        leftCompilation := left
                                        rightCompilation := right
                                        unit := unit
                                        descriptor := descriptor } := by
                                    simpa using (Option.some.inj computed).symm
                                  subst old
                                  have leftParts :=
                                    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_computations
                                      target view before initial.left initial.right
                                      initial.leftCursor left leftComputed
                                  have leftFirstExec : input.localizedRule3ReferenceCursorExec?
                                      initial.leftCursor left.endpointFrame.first =
                                        some left.firstCursor := by
                                    have h := leftParts.firstCursor
                                    rw [input.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?] at h
                                    exact h
                                  have leftSecondExec : input.localizedRule3ReferenceCursorExec?
                                      initial.leftCursor left.endpointFrame.second =
                                        some left.secondCursor := by
                                    have h := leftParts.secondCursor
                                    rw [input.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?] at h
                                    exact h
                                  have leftMember : [left.firstCursor, left.secondCursor] ∈
                                      input.rule3RingCallbackRequests occurrence := by
                                    simp [rule3RingCallbackRequests, routeComputed, policyEq,
                                      rule3EndpointCallbackRequests, leftParts.candidates,
                                      leftFirstExec, leftSecondExec]
                                  obtain ⟨left', leftComputed', leftRel⟩ :=
                                    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_refines
                                      target view before after initial.left initial.right
                                      left.endpointFrame.first left.endpointFrame.second
                                      initial.leftCursor
                                      leftParts.candidates left.firstCursor left.secondCursor
                                      leftFirstExec leftSecondExec
                                      (fun oldFrame h => refines [left.firstCursor, left.secondCursor]
                                        leftMember oldFrame h)
                                      left leftComputed
                                  have rightParts :=
                                    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_computations
                                      target view before initial.right initial.left
                                      initial.rightCursor right rightComputed
                                  have rightFirstExec : input.localizedRule3ReferenceCursorExec?
                                      initial.rightCursor right.endpointFrame.first =
                                        some right.firstCursor := by
                                    have h := rightParts.firstCursor
                                    rw [input.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?] at h
                                    exact h
                                  have rightSecondExec : input.localizedRule3ReferenceCursorExec?
                                      initial.rightCursor right.endpointFrame.second =
                                        some right.secondCursor := by
                                    have h := rightParts.secondCursor
                                    rw [input.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?] at h
                                    exact h
                                  have rightMember : [right.firstCursor, right.secondCursor] ∈
                                      input.rule3RingCallbackRequests occurrence := by
                                    simp [rule3RingCallbackRequests, routeComputed, policyEq,
                                      rule3EndpointCallbackRequests, rightParts.candidates,
                                      rightFirstExec, rightSecondExec]
                                  obtain ⟨right', rightComputed', rightRel⟩ :=
                                    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_refines
                                      target view before after initial.right initial.left
                                      right.endpointFrame.first right.endpointFrame.second
                                      initial.rightCursor
                                      rightParts.candidates right.firstCursor right.secondCursor
                                      rightFirstExec rightSecondExec
                                      (fun oldFrame h => refines [right.firstCursor, right.secondCursor]
                                        rightMember oldFrame h)
                                      right rightComputed
                                  have unitComputed' : input.localizedRule3DescriptorBearingSpatialUnitExec?
                                      initial.left initial.right left'.endpointFrame
                                        right'.endpointFrame = some unit := by
                                    have framesEq :
                                        input.localizedRule3DescriptorBearingSpatialUnitExec?
                                            initial.left initial.right left.endpointFrame
                                            right.endpointFrame =
                                          input.localizedRule3DescriptorBearingSpatialUnitExec?
                                            initial.left initial.right left'.endpointFrame
                                            right'.endpointFrame := by
                                      unfold localizedRule3DescriptorBearingSpatialUnitExec?
                                      rw [← leftRel.priority_eq, ← rightRel.priority_eq]
                                    exact framesEq.symm.trans unitComputed
                                  refine ⟨
                                    { initial := initial
                                      closure := closure
                                      policyResult := policyResult
                                      leftCompilation := left'
                                      rightCompilation := right'
                                      unit := unit
                                      descriptor := descriptor }, ?_, ?_⟩
                                  · simp only [routeComputed, policyEq, leftComputed',
                                      rightComputed', unitComputed', geometryComputed,
                                      descriptorComputed, bind, Option.bind_some]
                                  · dsimp only [localizedRule3RequiredMonocyclicEZObservation]
                                    rw [leftRel.2.2.2.1, rightRel.2.2.2.1]

/-- **Original eager node one-way callback refinement.**  Every successful full node result,
including the outer `none`/`some none` distinction, is preserved exactly on
`rule3OriginalNodeCallbackRequests`.  All route decisions are callback-independent.  An old
success that reached a spatial unit stays on that route and keeps its projected observation; an
old omission (`some none`) stays an omission because the policy is callback-independent; and an
old outer refusal cannot be `some`.  No joint-success assumption is used: the joint `none`
fallback is simply re-evaluated to the same callback-free value. -/
theorem localizedDescriptorBearingRule3NodeWithExec?_callback_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (refines : input.LocalizedRule3CallbackFrameRefinesOn
      (input.rule3OriginalNodeCallbackRequests occurrence) before after)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (old : Option input.LocalizedRule3SpatialNodeResult)
    (computed : input.localizedDescriptorBearingRule3NodeWithExec?
      target occurrence view before excluded = some old) :
    input.localizedDescriptorBearingRule3NodeWithExec?
      target occurrence view after excluded = some old := by
  unfold localizedDescriptorBearingRule3NodeWithExec? at computed ⊢
  by_cases edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence
  · simp only [dif_pos edge] at computed ⊢
    cases entry : input.localizedRule3CumulatedAxisEntryExec? occurrence with
    | none => simp [entry] at computed
    | some value =>
        cases value with
        | internal =>
            simp only [entry] at computed ⊢
            exact computed
        | ringClosure =>
            simp only [entry] at computed ⊢
            cases required : input.localizedRule3RequiredMonocyclicEZWithExec?
                target occurrence view before with
            | some result =>
                have refinesRing : input.LocalizedRule3CallbackFrameRefinesOn
                    (input.rule3RingCallbackRequests occurrence) before after :=
                  fun cursors member => refines cursors (by
                    simpa only [rule3OriginalNodeCallbackRequests, if_pos edge, entry]
                      using member)
                obtain ⟨newResult, requiredAfter, observationEq⟩ :=
                  input.localizedRule3RequiredMonocyclicEZWithExec?_observation_refines
                    target occurrence view before after refinesRing result required
                simp only [required, bind, Option.bind_some] at computed
                simp only [requiredAfter, bind, Option.bind_some]
                rw [observationEq]
                by_cases fresh :
                    (input.localizedRule3RequiredMonocyclicEZObservation result).physicalUnitId ∈
                      excluded
                · simpa [fresh] using computed
                · simpa [fresh] using computed
            | none =>
                cases route : input.localizedRule3CyclicAuthorityRouteExec? occurrence with
                | none => simp [required, route] at computed
                | some policyRoute =>
                    cases policyRoute with
                    | fullyCyclicCumulene => simp [required, route] at computed
                    | ordinaryMonocyclicPolicyGap => simp [required, route] at computed
                    | ordinaryNonmonocyclic => simp [required, route] at computed
                    | ordinaryMonocyclicPolicy initial closure policyResult =>
                        cases policyEq : policyResult.policy with
                        | permanentlyOmit =>
                            simp only [required, route, policyEq] at computed
                            have oldEq : old = none := by
                              simpa using (Option.some.inj computed).symm
                            subst old
                            have afterRequired :
                                input.localizedRule3RequiredMonocyclicEZWithExec?
                                  target occurrence view after = none := by
                              unfold localizedRule3RequiredMonocyclicEZWithExec?
                              simp [route, policyEq]
                            simp [afterRequired, route, policyEq]
                        | requireEZ => simp [required, route, policyEq] at computed
        | branched =>
            simp only [entry] at computed ⊢
            cases unitComputed :
                input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec?
                  target occurrence view before with
            | none => simp [unitComputed] at computed
            | some result =>
                have refinesOrdinary : input.LocalizedRule3CallbackFrameRefinesOn
                    (input.rule3OrdinaryCallbackRequests occurrence) before after :=
                  fun cursors member => refines cursors (by
                    simpa only [rule3OriginalNodeCallbackRequests, if_pos edge, entry]
                      using member)
                obtain ⟨newResult, unitAfter, observationEq⟩ :=
                  input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec?_observation_refines
                    target occurrence view before after refinesOrdinary result unitComputed
                simp only [unitComputed, bind, Option.bind_some] at computed
                simp only [unitAfter, bind, Option.bind_some]
                rw [observationEq]
                by_cases fresh :
                    (input.localizedRule3DescriptorBearingObservation result).physicalUnitId ∈
                      excluded
                · simpa [fresh] using computed
                · simpa [fresh] using computed
        | terminalStart =>
            simp only [entry] at computed ⊢
            cases axis : input.localizedRule3CumulatedEndpointCursorFrameExec?
                (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
            | none => simp [axis] at computed
            | some topology =>
                simp only [axis] at computed ⊢
                by_cases ordinary : topology.doubleBondCount = 1
                · simp only [dif_pos ordinary] at computed ⊢
                  cases unitComputed :
                      input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec?
                        target occurrence view before with
                  | none => simp [unitComputed] at computed
                  | some result =>
                      have refinesOrdinary : input.LocalizedRule3CallbackFrameRefinesOn
                          (input.rule3OrdinaryCallbackRequests occurrence) before after :=
                        fun cursors member => refines cursors (by
                          simpa only [rule3OriginalNodeCallbackRequests, if_pos edge,
                            entry, axis, if_pos ordinary] using member)
                      obtain ⟨newResult, unitAfter, observationEq⟩ :=
                        input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec?_observation_refines
                          target occurrence view before after refinesOrdinary result unitComputed
                      simp only [unitComputed, bind, Option.bind_some] at computed
                      simp only [unitAfter, bind, Option.bind_some]
                      rw [observationEq]
                      by_cases fresh :
                          (input.localizedRule3DescriptorBearingObservation result).physicalUnitId ∈
                            excluded
                      · simpa [fresh] using computed
                      · simpa [fresh] using computed
                · simp only [dif_neg ordinary] at computed ⊢
                  by_cases planar : Odd topology.doubleBondCount
                  · simp only [dif_pos planar] at computed ⊢
                    cases unitComputed :
                        input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec?
                          target occurrence view before with
                    | none => simp [unitComputed] at computed
                    | some result =>
                        have refinesOdd : input.LocalizedRule3CallbackFrameRefinesOn
                            (input.rule3OddCallbackRequests occurrence) before after :=
                          fun cursors member => refines cursors (by
                            simpa only [rule3OriginalNodeCallbackRequests, if_pos edge,
                              entry, axis, if_neg ordinary, if_pos planar] using member)
                        obtain ⟨newResult, unitAfter, observationEq⟩ :=
                          input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec?_observation_refines
                            target occurrence view before after refinesOdd result unitComputed
                        simp only [unitComputed, bind, Option.bind_some] at computed
                        simp only [unitAfter, bind, Option.bind_some]
                        rw [observationEq]
                        by_cases fresh :
                            (input.localizedRule3OddCumuleneDescriptorBearingObservation
                              result).physicalUnitId ∈ excluded
                        · simpa [fresh] using computed
                        · simpa [fresh] using computed
                  · simp only [dif_neg planar] at computed ⊢
                    exact computed
  · simp only [dif_neg edge] at computed ⊢
    exact computed

/-- **Ordinary short-circuit node one-way callback refinement.**  On the actual successor demand
`rule3NodeCallbackRequests` the whole nested `Option` is preserved.  The original route uses the
eager node theorem; the ordinary short route reads only the two short endpoint priorities, whose
actual unit is preserved exactly, and the exclusion test then sees the same observation. -/
theorem localizedRule3ShortCircuitNodeWithExec?_callback_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (refines : input.LocalizedRule3CallbackFrameRefinesOn
      (input.rule3NodeCallbackRequests occurrence) before after)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (old : Option input.LocalizedRule3SpatialNodeResult)
    (computed : input.localizedRule3ShortCircuitNodeWithExec?
      target occurrence view before excluded = some old) :
    input.localizedRule3ShortCircuitNodeWithExec?
      target occurrence view after excluded = some old := by
  unfold localizedRule3ShortCircuitNodeWithExec? at computed ⊢
  cases route : input.localizedRule3OrdinaryRouteCertificate? occurrence with
  | none =>
      have reduced : input.localizedDescriptorBearingRule3NodeWithExec?
          target occurrence view before excluded = some old := by
        simpa only [route] using computed
      exact input.localizedDescriptorBearingRule3NodeWithExec?_callback_refines
        target occurrence view before after
        (fun cursors member => refines cursors (by
          simpa only [rule3NodeCallbackRequests, route] using member))
        excluded old reduced
  | some certificate =>
      have refinesShort : input.LocalizedRule3CallbackFrameRefinesOn
          (input.rule3ShortSpatialCallbackRequests occurrence) before after :=
        fun cursors member => refines cursors (by
          simpa only [rule3NodeCallbackRequests, route] using member)
      simp only [route] at computed ⊢
      cases unitComputed : input.localizedRule3ShortCircuitSpatialUnitWithExec?
          target occurrence view before with
      | none => simp [unitComputed] at computed
      | some unit =>
          cases topologyComputed : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence with
          | none =>
              unfold localizedRule3ShortCircuitSpatialUnitWithExec? at unitComputed
              simp [topologyComputed] at unitComputed
          | some topology =>
              have refined := input.localizedRule3ShortCircuitSpatialUnitWithExec?_refines
                target occurrence view before after topology topologyComputed
                refinesShort unit unitComputed
              simp only [unitComputed, bind, Option.bind_some] at computed
              simp only [refined, bind, Option.bind_some]
              exact computed

/-- **Extended short-circuit node one-way callback refinement.**  The final theorem for the actual
short extended node: on `rule3ExtendedNodeCallbackRequests`, every successful old node result is
preserved exactly with the same old observation.  Both route paths are covered: the nonordinary
odd route uses the exact odd short spatial unit; the ordinary fallback delegates to the short
node theorem, including its joint route-certificate `none` fallback, which is callback-free and
therefore re-evaluated identically. -/
theorem localizedRule3ExtendedShortCircuitNodeWithExec?_callback_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (refines : input.LocalizedRule3CallbackFrameRefinesOn
      (input.rule3ExtendedNodeCallbackRequests occurrence) before after)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (old : Option input.LocalizedRule3SpatialNodeResult)
    (computed : input.localizedRule3ExtendedShortCircuitNodeWithExec?
      target occurrence view before excluded = some old) :
    input.localizedRule3ExtendedShortCircuitNodeWithExec?
      target occurrence view after excluded = some old := by
  unfold localizedRule3ExtendedShortCircuitNodeWithExec? at computed ⊢
  cases routed : input.localizedRule3OddRouteCertificate? occurrence with
  | none =>
      have reduced : input.localizedRule3ShortCircuitNodeWithExec?
          target occurrence view before excluded = some old := by
        simpa only [routed] using computed
      exact input.localizedRule3ShortCircuitNodeWithExec?_callback_refines
        target occurrence view before after
        (fun cursors member => refines cursors (by
          simpa only [rule3ExtendedNodeCallbackRequests, routed] using member))
        excluded old reduced
  | some certificate =>
      have refinesOdd : input.LocalizedRule3CallbackFrameRefinesOn
          (input.rule3ShortOddCallbackRequests occurrence) before after :=
        fun cursors member => refines cursors (by
          simpa only [rule3ExtendedNodeCallbackRequests, routed] using member)
      simp only [routed] at computed ⊢
      cases unitComputed : input.localizedRule3ShortCircuitOddSpatialUnitWithExec?
          target occurrence view before with
      | none => simp [unitComputed] at computed
      | some unit =>
          cases topologyComputed : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
              (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
          | none =>
              unfold localizedRule3ShortCircuitOddSpatialUnitWithExec? at unitComputed
              simp [topologyComputed] at unitComputed
          | some topology =>
              have refined := input.localizedRule3ShortCircuitOddSpatialUnitWithExec?_refines
                target occurrence view before after topology topologyComputed
                refinesOdd unit unitComputed
              simp only [unitComputed, bind, Option.bind_some] at computed
              simp only [refined, bind, Option.bind_some]
              exact computed

/-- The final node refinement with membership-equivalent exclusion lists.  Only membership is
read by the node, so the successful old result transports to the after run at a different but
membership-equivalent exclusion list. -/
theorem localizedRule3ExtendedShortCircuitNodeWithExec?_callback_refines_of_exclusion_equivalent
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (refines : input.LocalizedRule3CallbackFrameRefinesOn
      (input.rule3ExtendedNodeCallbackRequests occurrence) before after)
    {excluded excluded' : List input.LocalizedRule3PhysicalUnitId}
    (equivalent : input.LocalizedRule3ExclusionEquivalent excluded excluded')
    (old : Option input.LocalizedRule3SpatialNodeResult)
    (computed : input.localizedRule3ExtendedShortCircuitNodeWithExec?
      target occurrence view before excluded = some old) :
    input.localizedRule3ExtendedShortCircuitNodeWithExec?
      target occurrence view after excluded' = some old := by
  have beforeEq := input.localizedRule3ExtendedShortCircuitNodeWithExec?_exclusion_extensional
    target occurrence view before equivalent
  rw [beforeEq] at computed
  exact input.localizedRule3ExtendedShortCircuitNodeWithExec?_callback_refines
    target occurrence view before after refines excluded' old computed

/-- The final node theorem in `OptionSuccessRefines` form: the fully guarded builder can consume
it directly as the one-way success relation between the old and new node computations. -/
theorem localizedRule3ExtendedShortCircuitNodeWithExec?_optionSuccessRefines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (refines : input.LocalizedRule3CallbackFrameRefinesOn
      (input.rule3ExtendedNodeCallbackRequests occurrence) before after)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    OptionSuccessRefines
      (input.localizedRule3ExtendedShortCircuitNodeWithExec?
        target occurrence view before excluded)
      (input.localizedRule3ExtendedShortCircuitNodeWithExec?
        target occurrence view after excluded) :=
  fun old computed =>
    input.localizedRule3ExtendedShortCircuitNodeWithExec?_callback_refines
      target occurrence view before after refines excluded old computed

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3CallbackFrameRefinesOn
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3CallbackFrameRefinesOn.of_agrees
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3CallbackFrameRefinesOn.mono
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3ExtendedFrameTopologyEquivalent_refl
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3ExtendedFrameTopologyEquivalent.keys_forall₂
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3ExtendedFrameTopologyEquivalent.keys_observable_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3OccurrenceEndpointRefines
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRule3OccurrenceEndpointRefines.priority_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_refines
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_computations
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityExec?_refines
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialUnitWithExec?_refines
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitOddSpatialUnitWithExec?_refines
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec?_observation_refines
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec?_observation_refines
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3RequiredMonocyclicEZWithExec?_observation_refines
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedDescriptorBearingRule3NodeWithExec?_callback_refines
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitNodeWithExec?_callback_refines
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedShortCircuitNodeWithExec?_callback_refines
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedShortCircuitNodeWithExec?_callback_refines_of_exclusion_equivalent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ExtendedShortCircuitNodeWithExec?_optionSuccessRefines
