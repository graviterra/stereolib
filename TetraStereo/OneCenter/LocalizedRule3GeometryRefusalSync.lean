import TetraStereo.OneCenter.LocalizedRule3GeometryDefinedness
import TetraStereo.OneCenter.LocalizedRule3ShortCircuitOddNode
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false















































namespace TetraStereo.OneCenter

universe u

/-- The `Option` bind produced by an executable `do` block is the primitive bind; applying a
`some` value is definitional.  Same private helper as the accepted endpoint layers. -/
private theorem option_some_bind_apply
    {α β : Type u} (value : α) (continuation : α → Option β) :
    (some value : Option α) >>= continuation = continuation value :=
  rfl

namespace CertifiedLocalizedCIPInput

/-! ## Request-local callback agreement predicates -/

/-- Two arbitrary callbacks agree on `isSome` at every request of an actual, input-derived request
list.  Refused and successful answers are distinguished exactly; nothing about the success value,
the frame or the keys is required. -/
def Rule3CallbackIsSomeAgreesOn (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (requests : List (List (input.LocalizedRerootCursor fuel)))
    (before after : List (input.LocalizedRerootCursor fuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) : Prop :=
  ∀ cursors ∈ requests, (before cursors).isSome = (after cursors).isSome

/-- Whenever a callback succeeds at a request of an actual, input-derived request list, its frame
carries exactly two Rule-3 keys.  This is the honest conditional shape the endpoint compiler
demands; it does not assert success anywhere. -/
def Rule3CallbackFrameShapeOn (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (requests : List (List (input.LocalizedRerootCursor fuel)))
    (callback : List (input.LocalizedRerootCursor fuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) : Prop :=
  ∀ cursors ∈ requests, ∀ frame, callback cursors = some frame → frame.keys.length = 2

/-! ## The endpoint compiler's observable `isSome` is the callback's `isSome` -/

/-- At one pinned candidate pair and one pinned pair of selected reference cursors, the parametric
endpoint compiler succeeds exactly when the shared callback succeeds.  The callback result is the
only branch source: a refused callback returns `none`, and a successful frame with two keys always
completes because the two compound through-Rule-5 keys exist at the proved budget for the two
actually selected (hence valid) cursors.  The reader is arbitrary and never inspected. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_isSome_eq_of_frameShape
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second : input.Atom)
    (endpointCursor firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor first = some firstCursor)
    (secondSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor second = some secondCursor)
    (shape : ∀ frame, rule3FrameOf [firstCursor, secondCursor] = some frame →
      frame.keys.length = 2) :
    (input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
        target view read rule3FrameOf endpoint partner endpointCursor).isSome =
      (rule3FrameOf [firstCursor, secondCursor]).isSome := by
  have firstValid : input.LocalizedRerootCursorValid firstCursor :=
    input.localizedRule3ReferenceCursorExec?_valid endpointCursor firstCursor first firstSelected
  have secondValid : input.LocalizedRerootCursorValid secondCursor :=
    input.localizedRule3ReferenceCursorExec?_valid endpointCursor secondCursor second secondSelected
  rw [input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_of_selected
    target view read rule3FrameOf endpoint partner first second endpointCursor
    firstCursor secondCursor candidates firstSelected secondSelected]
  generalize callbackResult : rule3FrameOf [firstCursor, secondCursor] = result
  cases result with
  | none => rfl
  | some rule3Frame =>
      have keysLength := shape rule3Frame callbackResult
      simp only [option_some_bind_apply]
      generalize keysResult : rule3Frame.keys = keys at keysLength ⊢
      cases keys with
      | nil => simp at keysLength
      | cons firstRule3 rest =>
          cases rest with
          | nil => simp at keysLength
          | cons secondRule3 rest =>
              cases rest with
              | cons thirdRule3 rest => simp at keysLength
              | nil =>
                  obtain ⟨firstRule45, firstComputed⟩ :=
                    input.exists_buildLocalizedRerootCompoundRule45KeyWithRead?_at_twice
                      read firstCursor firstValid
                  obtain ⟨secondRule45, secondComputed⟩ :=
                    input.exists_buildLocalizedRerootCompoundRule45KeyWithRead?_at_twice
                      read secondCursor secondValid
                  simp only [show localizedOccurrenceRerootEvaluationFuel carrierFuel =
                    2 * (carrierFuel + 1) from rfl, firstComputed,
                    option_some_bind_apply, secondComputed, option_some_bind_apply]
                  rfl

/-! ## The synchronized short endpoint seam

The selector is destructed in exactly the executable dispatch order.  The candidate-shape failure,
both reference-selection failures and both strict comparison outcomes are callback-independent and
therefore agree on `isSome` without any hypothesis.  Only the completely tied branch reaches the
deferred endpoint compiler, and there the callback `isSome` agreement decides the outcome: both
callbacks refuse, or both succeed with a two-key frame and the universal compound keys complete on
both sides. -/

/-- **Synchronized short endpoint success/refusal equality, pinned-pair form.**  At one actual
candidate pair and one actual pair of selected reference cursors, two arbitrary label readers and
two arbitrary Rule-3 frame callbacks give the same `isSome` for the parametric short endpoint
selector, provided the callbacks agree on `isSome` at that one pair and each callback's successful
frames carry exactly two keys there.  Strict root/constitutional branches return `some` for every
callback; every structural failure is shared. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_isSome_eq_of_pairShape
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (readOne readTwo : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second : input.Atom)
    (endpointCursor firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor first = some firstCursor)
    (secondSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor second = some secondCursor)
    (pairIsSome : (before [firstCursor, secondCursor]).isSome =
      (after [firstCursor, secondCursor]).isSome)
    (beforeShape : ∀ frame, before [firstCursor, secondCursor] = some frame →
      frame.keys.length = 2)
    (afterShape : ∀ frame, after [firstCursor, secondCursor] = some frame →
      frame.keys.length = 2) :
    (input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view readOne before endpoint partner endpointCursor).isSome =
      (input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view readTwo after endpoint partner endpointCursor).isSome := by
  unfold localizedRule3ShortCircuitEndpointPriorityWithRead?
  rw [candidates]
  dsimp only
  rw [firstSelected, secondSelected]
  simp only [option_some_bind_apply, Option.bind_some]
  have buildOneIsSome :=
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_isSome_eq_of_frameShape
      target view readOne before endpoint partner first second endpointCursor
      firstCursor secondCursor candidates firstSelected secondSelected beforeShape
  have buildTwoIsSome :=
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_isSome_eq_of_frameShape
      target view readTwo after endpoint partner first second endpointCursor
      firstCursor secondCursor candidates firstSelected secondSelected afterShape
  cases root : input.compareLocalizedRerootCursorConstitutionalRoot firstCursor secondCursor with
  | gt => rfl
  | lt => rfl
  | eq =>
      cases constitutional : input.compareLocalizedConstitutionalCursors?
          firstCursor secondCursor with
      | some ordering =>
          cases ordering with
          | gt => rfl
          | lt => rfl
          | eq =>
              have buildIsSome :
                  (input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
                    target view readOne before endpoint partner endpointCursor).isSome =
                  (input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
                    target view readTwo after endpoint partner endpointCursor).isSome := by
                rw [buildOneIsSome, buildTwoIsSome, pairIsSome]
              cases hOne : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
                  target view readOne before endpoint partner endpointCursor with
              | none =>
                  cases hTwo : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
                      target view readTwo after endpoint partner endpointCursor with
                  | none => rfl
                  | some secondValue =>
                      rw [hOne, hTwo] at buildIsSome
                      simp at buildIsSome
              | some firstValue =>
                  cases hTwo : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
                      target view readTwo after endpoint partner endpointCursor with
                  | none =>
                      rw [hOne, hTwo] at buildIsSome
                      simp at buildIsSome
                  | some secondValue => rfl
      | none =>
          have buildIsSome :
              (input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
                target view readOne before endpoint partner endpointCursor).isSome =
              (input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
                target view readTwo after endpoint partner endpointCursor).isSome := by
            rw [buildOneIsSome, buildTwoIsSome, pairIsSome]
          cases hOne : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
              target view readOne before endpoint partner endpointCursor with
          | none =>
              cases hTwo : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
                  target view readTwo after endpoint partner endpointCursor with
              | none => rfl
              | some secondValue =>
                  rw [hOne, hTwo] at buildIsSome
                  simp at buildIsSome
          | some firstValue =>
              cases hTwo : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
                  target view readTwo after endpoint partner endpointCursor with
              | none =>
                  rw [hOne, hTwo] at buildIsSome
                  simp at buildIsSome
              | some secondValue => rfl

/-- **Synchronized short endpoint success/refusal equality, actual-request form.**  The callback
premises are posed on the actual executable demand list
`rule3ShortEndpointCallbackRequests endpoint partner endpointCursor`.  The candidate-shape failure,
both reference-selection failures and the strict root/complete-constitutional decisions are
dispatched without touching the callback, so they contribute no request and are equal without any
hypothesis.  In the completely tied branch the list is exactly the selected pair and the pinned-pair
theorem applies.  The desired selector success is never assumed. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_isSome_eq_of_callbackShape
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (readOne readTwo : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (isSomeAgree : input.Rule3CallbackIsSomeAgreesOn
      (input.rule3ShortEndpointCallbackRequests endpoint partner endpointCursor) before after)
    (beforeShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ShortEndpointCallbackRequests endpoint partner endpointCursor) before)
    (afterShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ShortEndpointCallbackRequests endpoint partner endpointCursor) after) :
    (input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view readOne before endpoint partner endpointCursor).isSome =
      (input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view readTwo after endpoint partner endpointCursor).isSome := by
  cases candidates : input.localizedRule3ExplicitSubstituents endpoint partner with
  | nil =>
      simp [localizedRule3ShortCircuitEndpointPriorityWithRead?, candidates]
  | cons first rest =>
      cases rest with
      | nil =>
          simp [localizedRule3ShortCircuitEndpointPriorityWithRead?, candidates]
      | cons second rest =>
          cases rest with
          | cons third rest =>
              simp [localizedRule3ShortCircuitEndpointPriorityWithRead?, candidates]
          | nil =>
              cases firstSelected : input.localizedRule3ReferenceCursorExec?
                  endpointCursor first with
              | none =>
                  simp [localizedRule3ShortCircuitEndpointPriorityWithRead?, candidates,
                    firstSelected]
              | some firstCursor =>
                  cases secondSelected : input.localizedRule3ReferenceCursorExec?
                      endpointCursor second with
                  | none =>
                      simp [localizedRule3ShortCircuitEndpointPriorityWithRead?, candidates,
                        firstSelected, secondSelected]
                  | some secondCursor =>
                      cases root : input.compareLocalizedRerootCursorConstitutionalRoot
                          firstCursor secondCursor with
                      | gt =>
                          rw [
                            input.localizedRule3ShortCircuitEndpointPriorityWithRead?_strict_gt
                              target view readOne before endpoint partner first second
                              endpointCursor candidates firstCursor secondCursor firstSelected
                              secondSelected root,
                            input.localizedRule3ShortCircuitEndpointPriorityWithRead?_strict_gt
                              target view readTwo after endpoint partner first second
                              endpointCursor candidates firstCursor secondCursor firstSelected
                              secondSelected root]
                      | lt =>
                          rw [
                            input.localizedRule3ShortCircuitEndpointPriorityWithRead?_strict_lt
                              target view readOne before endpoint partner first second
                              endpointCursor candidates firstCursor secondCursor firstSelected
                              secondSelected root,
                            input.localizedRule3ShortCircuitEndpointPriorityWithRead?_strict_lt
                              target view readTwo after endpoint partner first second
                              endpointCursor candidates firstCursor secondCursor firstSelected
                              secondSelected root]
                      | eq =>
                          cases constitutional :
                              input.compareLocalizedConstitutionalCursors?
                                firstCursor secondCursor with
                          | some ordering =>
                              cases ordering with
                              | gt =>
                                  rw [
                                    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_constitutional_gt
                                      target view readOne before endpoint partner first
                                      second endpointCursor candidates firstCursor secondCursor
                                      firstSelected secondSelected root constitutional,
                                    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_constitutional_gt
                                      target view readTwo after endpoint partner first
                                      second endpointCursor candidates firstCursor secondCursor
                                      firstSelected secondSelected root constitutional]
                              | lt =>
                                  rw [
                                    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_constitutional_lt
                                      target view readOne before endpoint partner first
                                      second endpointCursor candidates firstCursor secondCursor
                                      firstSelected secondSelected root constitutional,
                                    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_constitutional_lt
                                      target view readTwo after endpoint partner first
                                      second endpointCursor candidates firstCursor secondCursor
                                      firstSelected secondSelected root constitutional]
                              | eq =>
                                  exact input.localizedRule3ShortCircuitEndpointPriorityWithRead?_isSome_eq_of_pairShape
                                    target view readOne readTwo before after
                                    endpoint partner first second endpointCursor firstCursor
                                    secondCursor candidates firstSelected secondSelected
                                    (isSomeAgree [firstCursor, secondCursor] (by
                                      simp [rule3ShortEndpointCallbackRequests, candidates,
                                        firstSelected, secondSelected, root, constitutional]))
                                    (beforeShape [firstCursor, secondCursor] (by
                                      simp [rule3ShortEndpointCallbackRequests, candidates,
                                        firstSelected, secondSelected, root, constitutional]))
                                    (afterShape [firstCursor, secondCursor] (by
                                      simp [rule3ShortEndpointCallbackRequests, candidates,
                                        firstSelected, secondSelected, root, constitutional]))
                          | none =>
                              exact input.localizedRule3ShortCircuitEndpointPriorityWithRead?_isSome_eq_of_pairShape
                                target view readOne readTwo before after
                                endpoint partner first second endpointCursor firstCursor
                                secondCursor candidates firstSelected secondSelected
                                (isSomeAgree [firstCursor, secondCursor] (by
                                  simp [rule3ShortEndpointCallbackRequests, candidates,
                                    firstSelected, secondSelected, root, constitutional]))
                                (beforeShape [firstCursor, secondCursor] (by
                                  simp [rule3ShortEndpointCallbackRequests, candidates,
                                    firstSelected, secondSelected, root, constitutional]))
                                (afterShape [firstCursor, secondCursor] (by
                                  simp [rule3ShortEndpointCallbackRequests, candidates,
                                    firstSelected, secondSelected, root, constitutional]))

/-! ## The ordinary projected physical identity: full `Option` equality

The two wrappers share the physical topology recovery equation and the two candidate pairs.  The
endpoint `isSome` agreement decides whether both wrappers refuse at the same selector, and the
candidate-pair readiness covers whichever priorities either reader selects in the surviving
`some` branch.  Consequently the two `Option.map (physicalUnitId ∘ spatialObservation)` values are
equal in **both** the `none` and the `some` branch. -/

/-- A refused left endpoint selector makes the ordinary projected physical identity `none` for the
same actual topology recovery. -/
theorem localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (found : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some topology)
    (computed : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.left topology.right topology.leftCursor = none) :
    input.localizedRule3ShortCircuitSpatialPhysicalUnit?
        target occurrence view read rule3FrameOf = none := by
  unfold localizedRule3ShortCircuitSpatialPhysicalUnit?
    localizedRule3ShortCircuitSpatialUnitWithRead?
  rw [found, option_some_bind_apply, computed]
  simp

/-- A refused right endpoint selector, after a successful left selector, makes the ordinary
projected physical identity `none`. -/
theorem localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (found : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some topology)
    (leftEndpoint : input.LocalizedRule3ShortCircuitEndpointResult)
    (leftComputed : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.left topology.right topology.leftCursor =
        some leftEndpoint)
    (computed : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.right topology.left topology.rightCursor = none) :
    input.localizedRule3ShortCircuitSpatialPhysicalUnit?
        target occurrence view read rule3FrameOf = none := by
  unfold localizedRule3ShortCircuitSpatialPhysicalUnit?
    localizedRule3ShortCircuitSpatialUnitWithRead?
  rw [found, option_some_bind_apply, leftComputed, option_some_bind_apply, computed]
  simp

/-- **Full ordinary projected physical identity equality from callback shape.**  The two wrappers
agree as complete `Option` values, not merely on success: a synchronized callback refusal is a
synchronized wrapper refusal, and a synchronized callback acceptance produces the canonical
unordered physical identity on both sides.  The two readers and callbacks may differ, so the E/Z
geometry and the two endpoint priorities may differ; candidate-pair readiness covers every
priority either reader can select. -/
theorem localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_of_callbackShape
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (readOne readTwo : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (topology : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (found : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some topology)
    (leftFirst leftSecond rightFirst rightSecond : input.Atom)
    (leftFirstCursor leftSecondCursor rightFirstCursor rightSecondCursor :
      input.LocalizedRerootCursor carrierFuel)
    (leftCandidates : input.localizedRule3ExplicitSubstituents
      topology.left topology.right = [leftFirst, leftSecond])
    (rightCandidates : input.localizedRule3ExplicitSubstituents
      topology.right topology.left = [rightFirst, rightSecond])
    (leftFirstSelected : input.localizedRule3ReferenceCursorExec?
      topology.leftCursor leftFirst = some leftFirstCursor)
    (leftSecondSelected : input.localizedRule3ReferenceCursorExec?
      topology.leftCursor leftSecond = some leftSecondCursor)
    (rightFirstSelected : input.localizedRule3ReferenceCursorExec?
      topology.rightCursor rightFirst = some rightFirstCursor)
    (rightSecondSelected : input.localizedRule3ReferenceCursorExec?
      topology.rightCursor rightSecond = some rightSecondCursor)
    (isSomeAgree : input.Rule3CallbackIsSomeAgreesOn
      (input.rule3ShortSpatialCallbackRequests occurrence) before after)
    (beforeShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ShortSpatialCallbackRequests occurrence) before)
    (afterShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ShortSpatialCallbackRequests occurrence) after)
    (doubleBond : input.moleculeGraph.bond topology.left topology.right = 2)
    (candidateReady : input.LocalizedRule3AxisCandidateGeometryReadiness
      topology.left topology.right leftFirst leftSecond rightFirst rightSecond) :
    input.localizedRule3ShortCircuitSpatialPhysicalUnit?
        target occurrence view readOne before =
      input.localizedRule3ShortCircuitSpatialPhysicalUnit?
        target occurrence view readTwo after := by
  have leftIsSomeAgree : input.Rule3CallbackIsSomeAgreesOn
      (input.rule3ShortEndpointCallbackRequests
        topology.left topology.right topology.leftCursor) before after := by
    intro cursors member
    exact isSomeAgree cursors
      (by simp [rule3ShortSpatialCallbackRequests, found, member])
  have leftBeforeShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ShortEndpointCallbackRequests
        topology.left topology.right topology.leftCursor) before := by
    intro cursors member frame succeeds
    exact beforeShape cursors
      (by simp [rule3ShortSpatialCallbackRequests, found, member]) frame succeeds
  have leftAfterShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ShortEndpointCallbackRequests
        topology.left topology.right topology.leftCursor) after := by
    intro cursors member frame succeeds
    exact afterShape cursors
      (by simp [rule3ShortSpatialCallbackRequests, found, member]) frame succeeds
  have rightIsSomeAgree : input.Rule3CallbackIsSomeAgreesOn
      (input.rule3ShortEndpointCallbackRequests
        topology.right topology.left topology.rightCursor) before after := by
    intro cursors member
    exact isSomeAgree cursors
      (by simp [rule3ShortSpatialCallbackRequests, found, member])
  have rightBeforeShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ShortEndpointCallbackRequests
        topology.right topology.left topology.rightCursor) before := by
    intro cursors member frame succeeds
    exact beforeShape cursors
      (by simp [rule3ShortSpatialCallbackRequests, found, member]) frame succeeds
  have rightAfterShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ShortEndpointCallbackRequests
        topology.right topology.left topology.rightCursor) after := by
    intro cursors member frame succeeds
    exact afterShape cursors
      (by simp [rule3ShortSpatialCallbackRequests, found, member]) frame succeeds
  have leftIsSomeEq :=
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_isSome_eq_of_callbackShape
      target view readOne readTwo before after topology.left topology.right
      topology.leftCursor leftIsSomeAgree leftBeforeShape leftAfterShape
  have rightIsSomeEq :=
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_isSome_eq_of_callbackShape
      target view readOne readTwo before after topology.right topology.left
      topology.rightCursor rightIsSomeAgree rightBeforeShape rightAfterShape
  by_cases leftOneNone : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view readOne before topology.left topology.right topology.leftCursor = none
  · have leftTwoNone : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view readTwo after topology.left topology.right topology.leftCursor = none := by
      have refused : (input.localizedRule3ShortCircuitEndpointPriorityWithRead?
          target view readTwo after topology.left topology.right
          topology.leftCursor).isSome = false := by
        rw [← leftIsSomeEq, leftOneNone]
        rfl
      cases reduced : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
          target view readTwo after topology.left topology.right topology.leftCursor with
      | none => rfl
      | some value => simp [reduced] at refused
    rw [input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
        target occurrence view readOne before topology found leftOneNone,
      input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
        target occurrence view readTwo after topology found leftTwoNone]
  · obtain ⟨leftOneEndpoint, leftOneSome⟩ : ∃ value,
        input.localizedRule3ShortCircuitEndpointPriorityWithRead?
          target view readOne before topology.left topology.right
            topology.leftCursor = some value := by
      cases reduced : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
          target view readOne before topology.left topology.right topology.leftCursor with
      | none => simp [reduced] at leftOneNone
      | some value => exact ⟨value, rfl⟩
    have leftTwoSome : ∃ value, input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view readTwo after topology.left topology.right
          topology.leftCursor = some value := by
      have accepted : (input.localizedRule3ShortCircuitEndpointPriorityWithRead?
          target view readTwo after topology.left topology.right
          topology.leftCursor).isSome = true := by
        rw [← leftIsSomeEq, leftOneSome]
        rfl
      cases reduced : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
          target view readTwo after topology.left topology.right topology.leftCursor with
      | none => simp [reduced] at accepted
      | some value => exact ⟨value, rfl⟩
    obtain ⟨leftTwoEndpoint, leftTwoSome⟩ := leftTwoSome
    by_cases rightOneNone : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view readOne before topology.right topology.left topology.rightCursor = none
    · have rightTwoNone : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
          target view readTwo after topology.right topology.left topology.rightCursor = none := by
        have refused : (input.localizedRule3ShortCircuitEndpointPriorityWithRead?
            target view readTwo after topology.right topology.left
            topology.rightCursor).isSome = false := by
          rw [← rightIsSomeEq, rightOneNone]
          rfl
        cases reduced : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
            target view readTwo after topology.right topology.left topology.rightCursor with
        | none => rfl
        | some value => simp [reduced] at refused
      rw [input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none
          target occurrence view readOne before topology found leftOneEndpoint leftOneSome
          rightOneNone,
        input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none
          target occurrence view readTwo after topology found leftTwoEndpoint leftTwoSome
          rightTwoNone]
    · obtain ⟨rightOneEndpoint, rightOneSome⟩ : ∃ value,
          input.localizedRule3ShortCircuitEndpointPriorityWithRead?
            target view readOne before topology.right topology.left
              topology.rightCursor = some value := by
        cases reduced : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
            target view readOne before topology.right topology.left topology.rightCursor with
        | none => simp [reduced] at rightOneNone
        | some value => exact ⟨value, rfl⟩
      have rightTwoSome : ∃ value, input.localizedRule3ShortCircuitEndpointPriorityWithRead?
          target view readTwo after topology.right topology.left
            topology.rightCursor = some value := by
        have accepted : (input.localizedRule3ShortCircuitEndpointPriorityWithRead?
            target view readTwo after topology.right topology.left
            topology.rightCursor).isSome = true := by
          rw [← rightIsSomeEq, rightOneSome]
          rfl
        cases reduced : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
            target view readTwo after topology.right topology.left topology.rightCursor with
        | none => simp [reduced] at accepted
        | some value => exact ⟨value, rfl⟩
      obtain ⟨rightTwoEndpoint, rightTwoSome⟩ := rightTwoSome
      have leftOneMember : ∀ reference, leftOneEndpoint.priority = .senior reference →
          reference = leftFirst ∨ reference = leftSecond :=
        input.localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
          target view readOne before topology.left topology.right leftFirst leftSecond
          topology.leftCursor leftCandidates leftOneEndpoint leftOneSome
      have rightOneMember : ∀ reference, rightOneEndpoint.priority = .senior reference →
          reference = rightFirst ∨ reference = rightSecond :=
        input.localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
          target view readOne before topology.right topology.left rightFirst rightSecond
          topology.rightCursor rightCandidates rightOneEndpoint rightOneSome
      have leftTwoMember : ∀ reference, leftTwoEndpoint.priority = .senior reference →
          reference = leftFirst ∨ reference = leftSecond :=
        input.localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
          target view readTwo after topology.left topology.right leftFirst leftSecond
          topology.leftCursor leftCandidates leftTwoEndpoint leftTwoSome
      have rightTwoMember : ∀ reference, rightTwoEndpoint.priority = .senior reference →
          reference = rightFirst ∨ reference = rightSecond :=
        input.localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
          target view readTwo after topology.right topology.left rightFirst rightSecond
          topology.rightCursor rightCandidates rightTwoEndpoint rightTwoSome
      have readyOne : input.LocalizedRule3AxisGeometryReadiness
          topology.left topology.right leftOneEndpoint.priority rightOneEndpoint.priority :=
        input.localizedRule3AxisGeometryReadiness_of_candidates
          topology.left topology.right leftFirst leftSecond rightFirst rightSecond
          leftOneEndpoint.priority rightOneEndpoint.priority candidateReady
          leftOneMember rightOneMember
      have readyTwo : input.LocalizedRule3AxisGeometryReadiness
          topology.left topology.right leftTwoEndpoint.priority rightTwoEndpoint.priority :=
        input.localizedRule3AxisGeometryReadiness_of_candidates
          topology.left topology.right leftFirst leftSecond rightFirst rightSecond
          leftTwoEndpoint.priority rightTwoEndpoint.priority candidateReady
          leftTwoMember rightTwoMember
      rw [input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_some_of_endpoints
          target occurrence view readOne before topology found leftOneEndpoint
          rightOneEndpoint leftOneSome rightOneSome doubleBond readyOne,
        input.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_some_of_endpoints
          target occurrence view readTwo after topology found leftTwoEndpoint
          rightTwoEndpoint leftTwoSome rightTwoSome doubleBond readyTwo]

/-! ## The odd-cumulene projected physical identity: full `Option` equality

The odd wrapper has no adjacent double-bond test and reads the extended skeleton instead of the
short one, but the dispatch is identical: odd topology recovery, the two endpoint selectors, then
the extended unit.  The same synchronized-refusal argument therefore gives the full `Option`
equality, again in both branches, with the odd actual request list. -/

/-- A refused initial-endpoint selector makes the odd projected physical identity `none`. -/
theorem localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (found : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some topology)
    (computed : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.initial.left topology.initial.right
      topology.initial.leftCursor = none) :
    input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?
        target occurrence view read rule3FrameOf = none := by
  unfold localizedRule3ShortCircuitOddSpatialPhysicalUnit?
    localizedRule3ShortCircuitOddSpatialUnitWithRead?
  rw [found, option_some_bind_apply, computed]
  simp

/-- A refused final-endpoint selector, after a successful initial selector, makes the odd projected
physical identity `none`. -/
theorem localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (found : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some topology)
    (leftEndpoint : input.LocalizedRule3ShortCircuitEndpointResult)
    (leftComputed : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.initial.left topology.initial.right
      topology.initial.leftCursor = some leftEndpoint)
    (computed : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view read rule3FrameOf topology.right topology.rightPartner
      topology.rightCursor = none) :
    input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?
        target occurrence view read rule3FrameOf = none := by
  unfold localizedRule3ShortCircuitOddSpatialPhysicalUnit?
    localizedRule3ShortCircuitOddSpatialUnitWithRead?
  rw [found, option_some_bind_apply, leftComputed, option_some_bind_apply, computed]
  simp

/-- **Full odd-cumulene projected physical identity equality from callback shape.**  Same structure
as the ordinary case: synchronized refusal is a synchronized `none`, and synchronized acceptance
produces the canonical unordered identity through the extended skeleton.  Readiness is required
only of the independent candidate-pair domain, covering all endpoint priorities either reader can
select; the two readers may differ. -/
theorem localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_of_callbackShape
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (readOne readTwo : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (found : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some topology)
    (leftFirst leftSecond rightFirst rightSecond : input.Atom)
    (leftFirstCursor leftSecondCursor rightFirstCursor rightSecondCursor :
      input.LocalizedRerootCursor carrierFuel)
    (leftCandidates : input.localizedRule3ExplicitSubstituents
      topology.initial.left topology.initial.right = [leftFirst, leftSecond])
    (rightCandidates : input.localizedRule3ExplicitSubstituents
      topology.right topology.rightPartner = [rightFirst, rightSecond])
    (leftFirstSelected : input.localizedRule3ReferenceCursorExec?
      topology.initial.leftCursor leftFirst = some leftFirstCursor)
    (leftSecondSelected : input.localizedRule3ReferenceCursorExec?
      topology.initial.leftCursor leftSecond = some leftSecondCursor)
    (rightFirstSelected : input.localizedRule3ReferenceCursorExec?
      topology.rightCursor rightFirst = some rightFirstCursor)
    (rightSecondSelected : input.localizedRule3ReferenceCursorExec?
      topology.rightCursor rightSecond = some rightSecondCursor)
    (isSomeAgree : input.Rule3CallbackIsSomeAgreesOn
      (input.rule3ShortOddCallbackRequests occurrence) before after)
    (beforeShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ShortOddCallbackRequests occurrence) before)
    (afterShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ShortOddCallbackRequests occurrence) after)
    (candidateReady : input.LocalizedRule3AxisCandidateGeometryReadiness
      topology.initial.left topology.right leftFirst leftSecond rightFirst rightSecond) :
    input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?
        target occurrence view readOne before =
      input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?
        target occurrence view readTwo after := by
  have leftIsSomeAgree : input.Rule3CallbackIsSomeAgreesOn
      (input.rule3ShortEndpointCallbackRequests
        topology.initial.left topology.initial.right topology.initial.leftCursor)
      before after := by
    intro cursors member
    exact isSomeAgree cursors
      (by simp [rule3ShortOddCallbackRequests, found, member])
  have leftBeforeShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ShortEndpointCallbackRequests
        topology.initial.left topology.initial.right topology.initial.leftCursor)
      before := by
    intro cursors member frame succeeds
    exact beforeShape cursors
      (by simp [rule3ShortOddCallbackRequests, found, member]) frame succeeds
  have leftAfterShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ShortEndpointCallbackRequests
        topology.initial.left topology.initial.right topology.initial.leftCursor)
      after := by
    intro cursors member frame succeeds
    exact afterShape cursors
      (by simp [rule3ShortOddCallbackRequests, found, member]) frame succeeds
  have rightIsSomeAgree : input.Rule3CallbackIsSomeAgreesOn
      (input.rule3ShortEndpointCallbackRequests
        topology.right topology.rightPartner topology.rightCursor) before after := by
    intro cursors member
    exact isSomeAgree cursors
      (by simp [rule3ShortOddCallbackRequests, found, member])
  have rightBeforeShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ShortEndpointCallbackRequests
        topology.right topology.rightPartner topology.rightCursor) before := by
    intro cursors member frame succeeds
    exact beforeShape cursors
      (by simp [rule3ShortOddCallbackRequests, found, member]) frame succeeds
  have rightAfterShape : input.Rule3CallbackFrameShapeOn
      (input.rule3ShortEndpointCallbackRequests
        topology.right topology.rightPartner topology.rightCursor) after := by
    intro cursors member frame succeeds
    exact afterShape cursors
      (by simp [rule3ShortOddCallbackRequests, found, member]) frame succeeds
  have leftIsSomeEq :=
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_isSome_eq_of_callbackShape
      target view readOne readTwo before after topology.initial.left topology.initial.right
      topology.initial.leftCursor leftIsSomeAgree leftBeforeShape leftAfterShape
  have rightIsSomeEq :=
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_isSome_eq_of_callbackShape
      target view readOne readTwo before after topology.right topology.rightPartner
      topology.rightCursor rightIsSomeAgree rightBeforeShape rightAfterShape
  by_cases leftOneNone : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
      target view readOne before topology.initial.left topology.initial.right
      topology.initial.leftCursor = none
  · have leftTwoNone : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view readTwo after topology.initial.left topology.initial.right
        topology.initial.leftCursor = none := by
      have refused : (input.localizedRule3ShortCircuitEndpointPriorityWithRead?
          target view readTwo after topology.initial.left topology.initial.right
          topology.initial.leftCursor).isSome = false := by
        rw [← leftIsSomeEq, leftOneNone]
        rfl
      cases reduced : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
          target view readTwo after topology.initial.left topology.initial.right
          topology.initial.leftCursor with
      | none => rfl
      | some value => simp [reduced] at refused
    rw [input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
        target occurrence view readOne before topology found leftOneNone,
      input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
        target occurrence view readTwo after topology found leftTwoNone]
  · obtain ⟨leftOneEndpoint, leftOneSome⟩ : ∃ value,
        input.localizedRule3ShortCircuitEndpointPriorityWithRead?
          target view readOne before topology.initial.left topology.initial.right
            topology.initial.leftCursor = some value := by
      cases reduced : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
          target view readOne before topology.initial.left topology.initial.right
          topology.initial.leftCursor with
      | none => simp [reduced] at leftOneNone
      | some value => exact ⟨value, rfl⟩
    have leftTwoSome : ∃ value, input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view readTwo after topology.initial.left topology.initial.right
          topology.initial.leftCursor = some value := by
      have accepted : (input.localizedRule3ShortCircuitEndpointPriorityWithRead?
          target view readTwo after topology.initial.left topology.initial.right
          topology.initial.leftCursor).isSome = true := by
        rw [← leftIsSomeEq, leftOneSome]
        rfl
      cases reduced : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
          target view readTwo after topology.initial.left topology.initial.right
          topology.initial.leftCursor with
      | none => simp [reduced] at accepted
      | some value => exact ⟨value, rfl⟩
    obtain ⟨leftTwoEndpoint, leftTwoSome⟩ := leftTwoSome
    by_cases rightOneNone : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view readOne before topology.right topology.rightPartner
        topology.rightCursor = none
    · have rightTwoNone : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
          target view readTwo after topology.right topology.rightPartner
          topology.rightCursor = none := by
        have refused : (input.localizedRule3ShortCircuitEndpointPriorityWithRead?
            target view readTwo after topology.right topology.rightPartner
            topology.rightCursor).isSome = false := by
          rw [← rightIsSomeEq, rightOneNone]
          rfl
        cases reduced : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
            target view readTwo after topology.right topology.rightPartner
            topology.rightCursor with
        | none => rfl
        | some value => simp [reduced] at refused
      rw [input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none
          target occurrence view readOne before topology found leftOneEndpoint leftOneSome
          rightOneNone,
        input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none
          target occurrence view readTwo after topology found leftTwoEndpoint leftTwoSome
          rightTwoNone]
    · obtain ⟨rightOneEndpoint, rightOneSome⟩ : ∃ value,
          input.localizedRule3ShortCircuitEndpointPriorityWithRead?
            target view readOne before topology.right topology.rightPartner
              topology.rightCursor = some value := by
        cases reduced : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
            target view readOne before topology.right topology.rightPartner
            topology.rightCursor with
        | none => simp [reduced] at rightOneNone
        | some value => exact ⟨value, rfl⟩
      have rightTwoSome : ∃ value, input.localizedRule3ShortCircuitEndpointPriorityWithRead?
          target view readTwo after topology.right topology.rightPartner
            topology.rightCursor = some value := by
        have accepted : (input.localizedRule3ShortCircuitEndpointPriorityWithRead?
            target view readTwo after topology.right topology.rightPartner
            topology.rightCursor).isSome = true := by
          rw [← rightIsSomeEq, rightOneSome]
          rfl
        cases reduced : input.localizedRule3ShortCircuitEndpointPriorityWithRead?
            target view readTwo after topology.right topology.rightPartner
            topology.rightCursor with
        | none => simp [reduced] at accepted
        | some value => exact ⟨value, rfl⟩
      obtain ⟨rightTwoEndpoint, rightTwoSome⟩ := rightTwoSome
      have leftOneMember : ∀ reference, leftOneEndpoint.priority = .senior reference →
          reference = leftFirst ∨ reference = leftSecond :=
        input.localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
          target view readOne before topology.initial.left topology.initial.right
          leftFirst leftSecond topology.initial.leftCursor leftCandidates
          leftOneEndpoint leftOneSome
      have rightOneMember : ∀ reference, rightOneEndpoint.priority = .senior reference →
          reference = rightFirst ∨ reference = rightSecond :=
        input.localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
          target view readOne before topology.right topology.rightPartner
          rightFirst rightSecond topology.rightCursor rightCandidates
          rightOneEndpoint rightOneSome
      have leftTwoMember : ∀ reference, leftTwoEndpoint.priority = .senior reference →
          reference = leftFirst ∨ reference = leftSecond :=
        input.localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
          target view readTwo after topology.initial.left topology.initial.right
          leftFirst leftSecond topology.initial.leftCursor leftCandidates
          leftTwoEndpoint leftTwoSome
      have rightTwoMember : ∀ reference, rightTwoEndpoint.priority = .senior reference →
          reference = rightFirst ∨ reference = rightSecond :=
        input.localizedRule3ShortCircuitEndpointPriorityWithRead?_senior_mem_candidates
          target view readTwo after topology.right topology.rightPartner
          rightFirst rightSecond topology.rightCursor rightCandidates
          rightTwoEndpoint rightTwoSome
      have readyOne : input.LocalizedRule3AxisGeometryReadiness
          topology.initial.left topology.right leftOneEndpoint.priority
          rightOneEndpoint.priority :=
        input.localizedRule3AxisGeometryReadiness_of_candidates
          topology.initial.left topology.right leftFirst leftSecond rightFirst rightSecond
          leftOneEndpoint.priority rightOneEndpoint.priority candidateReady
          leftOneMember rightOneMember
      have readyTwo : input.LocalizedRule3AxisGeometryReadiness
          topology.initial.left topology.right leftTwoEndpoint.priority
          rightTwoEndpoint.priority :=
        input.localizedRule3AxisGeometryReadiness_of_candidates
          topology.initial.left topology.right leftFirst leftSecond rightFirst rightSecond
          leftTwoEndpoint.priority rightTwoEndpoint.priority candidateReady
          leftTwoMember rightTwoMember
      rw [input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_some_of_endpoints
          target occurrence view readOne before topology found leftOneEndpoint
          rightOneEndpoint leftOneSome rightOneSome readyOne,
        input.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_some_of_endpoints
          target occurrence view readTwo after topology found leftTwoEndpoint
          rightTwoEndpoint leftTwoSome rightTwoSome readyTwo]

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.Rule3CallbackIsSomeAgreesOn
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.Rule3CallbackFrameShapeOn
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_isSome_eq_of_frameShape
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_isSome_eq_of_pairShape
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_isSome_eq_of_callbackShape
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialPhysicalUnit?_eq_of_callbackShape
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_leftEndpoint_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_none_of_rightEndpoint_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitOddSpatialPhysicalUnit?_eq_of_callbackShape
