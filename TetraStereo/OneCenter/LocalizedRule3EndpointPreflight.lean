import TetraStereo.OneCenter.LocalizedRule3ShortCircuitSpatial
import TetraStereo.OneCenter.LocalizedRule3ShortCircuitOddSpatial

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Endpoint-readiness preflight for the Rule-3 short-circuit callbacks

The short-circuit occurrence wrappers can request a Rule-3 key-frame callback while processing
the left endpoint before checking the right endpoint.  When either endpoint inevitably refuses
because its explicit
substituent pair does not resolve to two reference cursors --- the whole `Option` computation is
`none`, so the callback request is dead work and can form a spurious callback cycle.  This module
proves, constructively and for *every* callback and view, that the refusal is already implied by a
Boolean preflight computed from the input and the occurrence alone.

The preflight predicates are

* `rule3EndpointPairReady input endpoint partner cursor`: the endpoint has exactly two explicit
  substituents and `localizedRule3ReferenceCursorExec?` resolves both at `cursor`;
* `ordinaryPairReady input occurrence`: the executable physical endpoint frame exists and *both* of
  its endpoint pairs are ready;
* `oddPairReady input occurrence`: the executable odd-cumulene endpoint frame exists and *both* of
  its endpoint pairs (left initial pair, right partner pair) are ready.

Each predicate is `false` whenever its executable topology recovery is `none`.  The three
`_eq_none_of_pairNotReady` theorems then show that the corresponding executable short-circuit
compiler returns `none` with no hypothesis whatsoever on the callback: the failing endpoint bind
forces the final result independently of callbacks, even if the other endpoint recurses first.
A guarded evaluator can check readiness before doing that work.  No successful result and no
callback soundness assumption is used.
-/

namespace CertifiedLocalizedCIPInput

/-- Boolean endpoint readiness preflight: the endpoint has exactly two explicit substituents and
the executable occurrence-local reference lookup resolves both of them at `endpointCursor`.  Any
other substituent count, or any failed lookup, answers `false`. -/
def rule3EndpointPairReady
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor fuel) : Bool :=
  match input.localizedRule3ExplicitSubstituents endpoint partner with
  | [first, second] =>
      (input.localizedRule3ReferenceCursorExec? endpointCursor first).isSome &&
        (input.localizedRule3ReferenceCursorExec? endpointCursor second).isSome
  | _ => false

/-- Ordinary double-bond pair readiness, computed from the input and the occurrence only: the
executable physical endpoint frame must exist and both oriented endpoint pairs (left, right) and
(right, left) must be ready.  A missing topology answers `false`. -/
def ordinaryPairReady
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) : Bool :=
  match input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence with
  | none => false
  | some topology =>
      input.rule3EndpointPairReady topology.left topology.right topology.leftCursor &&
        input.rule3EndpointPairReady topology.right topology.left topology.rightCursor

/-- Odd-cumulene pair readiness, computed from the input and the occurrence only: the executable
odd-cumulene endpoint frame must exist and both endpoint pairs must be ready, the initial left
endpoint at its left cursor and the right endpoint at its partner cursor.  A missing topology
answers `false`. -/
def oddPairReady
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) : Bool :=
  match input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
  | none => false
  | some topology =>
      input.rule3EndpointPairReady topology.initial.left topology.initial.right
          topology.initial.leftCursor &&
        input.rule3EndpointPairReady topology.right topology.rightPartner
          topology.rightCursor

/-- A not-ready endpoint pair makes the executable short-circuit endpoint selector `none`, for
*every* view and *every* Rule-3 frame callback.  The proof never inspects the callback: the failed
reference lookup annihilates the `Option` bind before the deferred branch is reached. -/
theorem rule3ShortEndpoint_eq_none_of_pairNotReady
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (notReady : input.rule3EndpointPairReady endpoint partner endpointCursor = false) :
    input.localizedRule3ShortCircuitEndpointPriorityExec?
      target view callback endpoint partner endpointCursor = none := by
  unfold rule3EndpointPairReady at notReady
  unfold localizedRule3ShortCircuitEndpointPriorityExec?
  cases hsub : input.localizedRule3ExplicitSubstituents endpoint partner with
  | nil => simp
  | cons first rest =>
      cases rest with
      | nil => simp
      | cons second rest =>
          cases rest with
          | cons third rest' => simp
          | nil =>
              simp [hsub] at notReady ⊢
              cases firstRef : input.localizedRule3ReferenceCursorExec?
                  endpointCursor first with
              | none => simp
              | some firstCursor =>
                  cases secondRef : input.localizedRule3ReferenceCursorExec?
                      endpointCursor second with
                  | none => simp
                  | some secondCursor =>
                      rw [firstRef, secondRef] at notReady
                      simp at notReady

/-- A not-ready endpoint pair makes the eager executable occurrence endpoint key-frame compiler
`none`, for *every* view and *every* Rule-3 frame callback.  In particular the deferred full
compiler is not demanded on such an endpoint. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_eq_none_of_pairNotReady
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (notReady : input.rule3EndpointPairReady endpoint partner endpointCursor = false) :
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
      target view rule3FrameOf endpoint partner endpointCursor = none := by
  unfold rule3EndpointPairReady at notReady
  unfold buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
  cases hsub : input.localizedRule3ExplicitSubstituents endpoint partner with
  | nil => simp
  | cons first rest =>
      cases rest with
      | nil => simp
      | cons second rest =>
          cases rest with
          | cons third rest' => simp
          | nil =>
              simp [hsub] at notReady ⊢
              cases firstRef : input.localizedRule3ReferenceCursorExec?
                  endpointCursor first with
              | none => simp
              | some firstCursor =>
                  cases secondRef : input.localizedRule3ReferenceCursorExec?
                      endpointCursor second with
                  | none => simp
                  | some secondCursor =>
                      rw [firstRef, secondRef] at notReady
                      simp at notReady

/-- If the ordinary endpoint pair is not ready, the executable occurrence short-circuit spatial
compiler is `none` for *every* view and *every* Rule-3 frame callback.  The failing endpoint bind
annihilates the whole computation, even if the other endpoint would have demanded the callback. -/
theorem localizedRule3ShortCircuitSpatialUnitWithExec?_eq_none_of_pairNotReady
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (notReady : input.ordinaryPairReady occurrence = false) :
    input.localizedRule3ShortCircuitSpatialUnitWithExec?
      target occurrence view callback = none := by
  unfold ordinaryPairReady at notReady
  unfold localizedRule3ShortCircuitSpatialUnitWithExec?
  cases topologyComputed : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence with
  | none => simp
  | some topology =>
      simp [topologyComputed] at notReady ⊢
      cases leftReady : input.rule3EndpointPairReady topology.left topology.right
          topology.leftCursor with
      | false =>
          have leftNone := input.rule3ShortEndpoint_eq_none_of_pairNotReady
            target view callback topology.left topology.right topology.leftCursor leftReady
          simp [leftNone]
      | true =>
          have rightNotReady : input.rule3EndpointPairReady topology.right topology.left
              topology.rightCursor = false := by
            simpa [leftReady] using notReady
          have rightNone := input.rule3ShortEndpoint_eq_none_of_pairNotReady
            target view callback topology.right topology.left topology.rightCursor
            rightNotReady
          simp [rightNone]

/-- If the odd-cumulene endpoint pair is not ready, the executable occurrence odd spatial compiler
is `none` for *every* view and *every* Rule-3 frame callback.  The right-endpoint failure again
annihilates the whole computation, including a left endpoint that would have recursed. -/
theorem localizedRule3ShortCircuitOddSpatialUnitWithExec?_eq_none_of_pairNotReady
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (notReady : input.oddPairReady occurrence = false) :
    input.localizedRule3ShortCircuitOddSpatialUnitWithExec?
      target occurrence view callback = none := by
  unfold oddPairReady at notReady
  unfold localizedRule3ShortCircuitOddSpatialUnitWithExec?
  cases topologyComputed : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
  | none => simp
  | some topology =>
      simp [topologyComputed] at notReady ⊢
      cases leftReady : input.rule3EndpointPairReady topology.initial.left
          topology.initial.right topology.initial.leftCursor with
      | false =>
          have leftNone := input.rule3ShortEndpoint_eq_none_of_pairNotReady
            target view callback topology.initial.left topology.initial.right
            topology.initial.leftCursor leftReady
          simp [leftNone]
      | true =>
          have rightNotReady : input.rule3EndpointPairReady topology.right
              topology.rightPartner topology.rightCursor = false := by
            simpa [leftReady] using notReady
          have rightNone := input.rule3ShortEndpoint_eq_none_of_pairNotReady
            target view callback topology.right topology.rightPartner topology.rightCursor
            rightNotReady
          simp [rightNone]

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
