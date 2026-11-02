import TetraStereo.OneCenter.LocalizedRule3OriginalTargetDemand
import TetraStereo.OneCenter.LocalizedRule3DemandRestrictedEndpoint
import TetraStereo.OneCenter.LocalizedRerootShortCircuitRule3Key
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Per-request whole-state read support for the demand-restricted Rule-3 endpoint

`LocalizedRule3DemandRestrictedEndpoint` turns the input-derived callback-demand analysis into full
`Option` congruence of the parametric Rule-3 endpoint, selector and spatial wrappers.  Its
whole-state compositions (`..._wholeState_eq_restricted_of_outwardRequests` and friends) require a
single common outward start cursor for the whole retained request list
(`Rule3RequestsReachableFrom`).  That common start is strictly too strong for the actual requests:
the two endpoint orientations of a perceived open even axis emit their requests below different
reference cursors, so no single outward cursor reaches both.

This module removes the common start.  The honest premise is per request cursor:

```
∀ cursors ∈ requests, ∀ cursor ∈ cursors, OutwardRerootCursor input target cursor
```

`LocalizedRerootReadersAgreeOnRequests_of_outwardCursors` turns it into agreement of the
unrestricted whole-state reader with the restricted dependency reader on the executable-reachable
support of every retained request, using `outward_reachable_cursor` and
`localizedDependencyLabel_eq_state_of_dependency`.  The endpoint, short-circuit selector and
ordinary spatial wrapper compositions are then immediate specializations of the existing
demand-sensitive congruence theorems.

### Actual composition

`rule3ActualRequest_outward O T deeper` from `LocalizedRule3OriginalTargetDemand` proves exactly
the per-request premise for the actual spatial request list of a physical occurrence `O`.  The
corollaries at the end of this file therefore prove, for `deeper : LocalizedDepthDependency O T`
and an **arbitrary** supplied Rule-3 callback, full `Option` equality between

* the ordinary spatial wrapper (and each of its two endpoint selector calls) built from the whole
  auxiliary state, and
* the executable spatial wrapper (resp. executable selector) built from the restricted dependency
  view,

and then instantiate the callback to the actual restricted production builder
`buildLocalizedShortCircuitRule3FrameExec? T view budget`.

### Scope

Only the **direct Rule-4/5 label read** at the retained reference cursors is replaced.  The
recursive Rule-3 callback is the same supplied callback on both sides; nothing here claims
equality of whole-state and restricted recursive callback computations, termination, or any
successful key/callback premise.

## Kernel authority

Every exported definition and theorem is guarded by `assert_kernel_only` at the end of the file.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-! ## The unrestricted whole-state reader -/

/-- The unrestricted label reader of an auxiliary state: read the occurrence of the cursor
directly out of the whole state, with no dependency restriction. -/
def localizedWholeStateReader
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (state : input.LocalizedAuxiliaryState fuel) :
    input.LocalizedRerootCursor fuel → Option LocalizedAuxiliaryLabel :=
  fun cursor => state cursor.occurrence

/-- The whole-state reader is definitionally the unrestricted occurrence read. -/
theorem localizedWholeStateReader_apply
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (state : input.LocalizedAuxiliaryState fuel)
    (cursor : input.LocalizedRerootCursor fuel) :
    input.localizedWholeStateReader state cursor = state cursor.occurrence :=
  rfl

/-! ## Per-request reader bridge -/

/-- **Per-request whole-state read support.**  If every cursor occurring in every retained request
is outward of the descriptor target `T`, then the unrestricted whole-state reader and the restricted
dependency reader agree on every cursor executable-reachable from any requested cursor.

Unlike `LocalizedRerootReadersAgreeOnRequests_of_outwardReachable`, this premise mentions no single
common start cursor: each request may have its own outward cursors.  The reachability closure is
handled per request cursor by `outward_reachable_cursor`, and the label agreement is the structural
identity `localizedDependencyLabel_eq_state_of_dependency`. -/
theorem LocalizedRerootReadersAgreeOnRequests_of_outwardCursors
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (requests : List (List (input.LocalizedRerootCursor carrierFuel)))
    (outward : ∀ cursors ∈ requests, ∀ cursor ∈ cursors,
      OutwardRerootCursor input target cursor) :
    input.LocalizedRerootReadersAgreeOnRequests
      (input.localizedWholeStateReader state)
      (fun cursor => input.localizedDependencyLabel target
        (input.localizedDependencyView state target) cursor)
      requests := by
  intro cursors member cursor cursorMember child reachable
  have cursorOutward : OutwardRerootCursor input target cursor :=
    outward cursors member cursor cursorMember
  have childOutward : OutwardRerootCursor input target child :=
    input.outward_reachable_cursor target cursor child cursorOutward reachable
  show state child.occurrence =
    input.localizedDependencyLabel target (input.localizedDependencyView state target) child
  exact (input.localizedDependencyLabel_eq_state_of_dependency target state child
    childOutward.2.1).symm

/-! ## Endpoint compiler -/

/-- **Per-request whole-state endpoint agreement.**  The endpoint compiled from the whole auxiliary
state equals the endpoint compiled from the restricted dependency view, with the same Rule-3
callback and full `Option` agreement, as soon as every cursor in every retained endpoint request is
outward of the target. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_wholeState_eq_restricted_of_outwardCursors
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (outward : ∀ cursors ∈ input.rule3EndpointCallbackRequests endpoint partner endpointCursor,
      ∀ cursor ∈ cursors, OutwardRerootCursor input target cursor) :
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
        target (input.localizedDependencyView state target)
        (input.localizedWholeStateReader state) rule3FrameOf endpoint partner endpointCursor =
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
        target (input.localizedDependencyView state target)
        (fun cursor => input.localizedDependencyLabel target
          (input.localizedDependencyView state target) cursor)
        rule3FrameOf endpoint partner endpointCursor :=
  input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_congr_of_actualRequests
    target (input.localizedDependencyView state target)
    (input.localizedWholeStateReader state)
    (fun cursor => input.localizedDependencyLabel target
      (input.localizedDependencyView state target) cursor)
    rule3FrameOf rule3FrameOf endpoint partner endpointCursor
    (by intro cursors _member; rfl)
    (input.LocalizedRerootReadersAgreeOnRequests_of_outwardCursors
      target state _ outward)

/-- **Per-request whole-state endpoint agreement against the actual executable.** -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_wholeState_eq_Exec?_of_outwardCursors
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (outward : ∀ cursors ∈ input.rule3EndpointCallbackRequests endpoint partner endpointCursor,
      ∀ cursor ∈ cursors, OutwardRerootCursor input target cursor) :
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
        target (input.localizedDependencyView state target)
        (input.localizedWholeStateReader state) rule3FrameOf endpoint partner endpointCursor =
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
        target (input.localizedDependencyView state target) rule3FrameOf endpoint partner
        endpointCursor :=
  input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_of_actualRequests
    target (input.localizedDependencyView state target)
    (input.localizedWholeStateReader state) rule3FrameOf endpoint partner endpointCursor
    (input.LocalizedRerootReadersAgreeOnRequests_of_outwardCursors target state _ outward)

/-! ## One endpoint orientation of the recovered physical topology

The spatial request list is the concatenation of the two endpoint request lists.  When the physical
endpoint frame of the occurrence is `some frame`, each orientation's requests are retained in the
spatial list, so the spatial outward premise discharges the request-level premises of the endpoint
and selector theorems above for either orientation. -/

/-- **Left-orientation short-selector requests are retained in the spatial request list.**  This is
the list the spatial wrapper actually demands, so it is the one the actual locality theorem
supports. -/
theorem rule3ShortEndpointCallbackRequests_left_mem_spatial
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some frame)
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (member : cursors ∈ input.rule3ShortEndpointCallbackRequests
      frame.left frame.right frame.leftCursor) :
    cursors ∈ input.rule3ShortSpatialCallbackRequests occurrence := by
  simp only [rule3ShortSpatialCallbackRequests, computed]
  exact List.mem_append_left _ member

/-- **Right-orientation short-selector requests are retained in the spatial request list.** -/
theorem rule3ShortEndpointCallbackRequests_right_mem_spatial
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some frame)
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (member : cursors ∈ input.rule3ShortEndpointCallbackRequests
      frame.right frame.left frame.rightCursor) :
    cursors ∈ input.rule3ShortSpatialCallbackRequests occurrence := by
  simp only [rule3ShortSpatialCallbackRequests, computed]
  exact List.mem_append_right _ member

/-! ## Short-circuit selector -/

/-- **Per-request whole-state selector agreement.**  The strict root and strict complete
constitutional branches decide without any read; the two fallback branches reduce to the endpoint
congruence, so the same per-request outward premise suffices for the full selector. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_wholeState_eq_restricted_of_outwardCursors
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (outward : ∀ cursors ∈ input.rule3ShortEndpointCallbackRequests endpoint partner endpointCursor,
      ∀ cursor ∈ cursors, OutwardRerootCursor input target cursor) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target (input.localizedDependencyView state target)
        (input.localizedWholeStateReader state) rule3FrameOf endpoint partner endpointCursor =
      input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target (input.localizedDependencyView state target)
        (fun cursor => input.localizedDependencyLabel target
          (input.localizedDependencyView state target) cursor)
        rule3FrameOf endpoint partner endpointCursor :=
  input.localizedRule3ShortCircuitEndpointPriorityWithRead?_congr_of_actualRequests
    target (input.localizedDependencyView state target)
    (input.localizedWholeStateReader state)
    (fun cursor => input.localizedDependencyLabel target
      (input.localizedDependencyView state target) cursor)
    rule3FrameOf rule3FrameOf endpoint partner endpointCursor
    (by intro cursors _member; rfl)
    (input.LocalizedRerootReadersAgreeOnRequests_of_outwardCursors
      target state _ outward)

/-- **Per-request whole-state selector agreement against the actual executable.** -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_wholeState_eq_Exec?_of_outwardCursors
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (outward : ∀ cursors ∈ input.rule3ShortEndpointCallbackRequests endpoint partner endpointCursor,
      ∀ cursor ∈ cursors, OutwardRerootCursor input target cursor) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target (input.localizedDependencyView state target)
        (input.localizedWholeStateReader state) rule3FrameOf endpoint partner endpointCursor =
      input.localizedRule3ShortCircuitEndpointPriorityExec?
        target (input.localizedDependencyView state target) rule3FrameOf endpoint partner
        endpointCursor :=
  input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_localizedRule3ShortCircuitEndpointPriorityExec?_of_actualRequests
    target (input.localizedDependencyView state target)
    (input.localizedWholeStateReader state) rule3FrameOf endpoint partner endpointCursor
    (input.LocalizedRerootReadersAgreeOnRequests_of_outwardCursors target state _ outward)

/-- **Left-orientation selector agreement from spatial locality.**  This is the exact selector the
spatial wrapper calls for its left endpoint, so the whole-state left endpoint is the executable
one. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_wholeState_eq_Exec?_of_spatialOutward_left
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some frame)
    (outward : ∀ cursors ∈ input.rule3ShortSpatialCallbackRequests occurrence,
      ∀ cursor ∈ cursors, OutwardRerootCursor input target cursor) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target (input.localizedDependencyView state target)
        (input.localizedWholeStateReader state) rule3FrameOf
        frame.left frame.right frame.leftCursor =
      input.localizedRule3ShortCircuitEndpointPriorityExec?
        target (input.localizedDependencyView state target) rule3FrameOf
        frame.left frame.right frame.leftCursor :=
  input.localizedRule3ShortCircuitEndpointPriorityWithRead?_wholeState_eq_Exec?_of_outwardCursors
    target state rule3FrameOf frame.left frame.right frame.leftCursor
    (by
      intro cursors member cursor cursorMember
      exact outward cursors
        (input.rule3ShortEndpointCallbackRequests_left_mem_spatial occurrence frame computed cursors
          member) cursor cursorMember)

/-- **Right-orientation selector agreement from spatial locality.** -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_wholeState_eq_Exec?_of_spatialOutward_right
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence = some frame)
    (outward : ∀ cursors ∈ input.rule3ShortSpatialCallbackRequests occurrence,
      ∀ cursor ∈ cursors, OutwardRerootCursor input target cursor) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target (input.localizedDependencyView state target)
        (input.localizedWholeStateReader state) rule3FrameOf
        frame.right frame.left frame.rightCursor =
      input.localizedRule3ShortCircuitEndpointPriorityExec?
        target (input.localizedDependencyView state target) rule3FrameOf
        frame.right frame.left frame.rightCursor :=
  input.localizedRule3ShortCircuitEndpointPriorityWithRead?_wholeState_eq_Exec?_of_outwardCursors
    target state rule3FrameOf frame.right frame.left frame.rightCursor
    (by
      intro cursors member cursor cursorMember
      exact outward cursors
        (input.rule3ShortEndpointCallbackRequests_right_mem_spatial occurrence frame computed cursors
          member) cursor cursorMember)

/-! ## Ordinary spatial wrapper -/

/-- **Per-request whole-state spatial agreement.**  The ordinary short-circuit spatial wrapper
compiled from the whole auxiliary state equals the wrapper compiled from the restricted dependency
view, with the same arbitrary Rule-3 callback and full `Option` agreement, as soon as every cursor
occurring in every retained spatial request is outward of the descriptor target.  The physical
occurrence of the wrapper is never identified with the descriptor target. -/
theorem localizedRule3ShortCircuitSpatialUnitWithRead?_wholeState_eq_restricted_of_outwardCursors
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (outward : ∀ cursors ∈ input.rule3ShortSpatialCallbackRequests occurrence,
      ∀ cursor ∈ cursors, OutwardRerootCursor input target cursor) :
    input.localizedRule3ShortCircuitSpatialUnitWithRead?
        target occurrence (input.localizedDependencyView state target)
        (input.localizedWholeStateReader state) rule3FrameOf =
      input.localizedRule3ShortCircuitSpatialUnitWithRead?
        target occurrence (input.localizedDependencyView state target)
        (fun cursor => input.localizedDependencyLabel target
          (input.localizedDependencyView state target) cursor) rule3FrameOf :=
  input.localizedRule3ShortCircuitSpatialUnitWithRead?_congr_of_actualRequests
    target occurrence (input.localizedDependencyView state target)
    (input.localizedWholeStateReader state)
    (fun cursor => input.localizedDependencyLabel target
      (input.localizedDependencyView state target) cursor)
    rule3FrameOf rule3FrameOf
    (by intro cursors _member; rfl)
    (input.LocalizedRerootReadersAgreeOnRequests_of_outwardCursors
      target state _ outward)

/-- **Per-request whole-state spatial agreement against the actual executable.**  Full `Option`
equality, including every fail-closed `none`, of the whole-state spatial wrapper and the executable
spatial wrapper built from the restricted dependency view, for an arbitrary supplied Rule-3
callback. -/
theorem localizedRule3ShortCircuitSpatialUnitWithRead?_wholeState_eq_Exec?_of_outwardCursors
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (outward : ∀ cursors ∈ input.rule3ShortSpatialCallbackRequests occurrence,
      ∀ cursor ∈ cursors, OutwardRerootCursor input target cursor) :
    input.localizedRule3ShortCircuitSpatialUnitWithRead?
        target occurrence (input.localizedDependencyView state target)
        (input.localizedWholeStateReader state) rule3FrameOf =
      input.localizedRule3ShortCircuitSpatialUnitWithExec?
        target occurrence (input.localizedDependencyView state target) rule3FrameOf :=
  input.localizedRule3ShortCircuitSpatialUnitWithRead?_eq_localizedRule3ShortCircuitSpatialUnitWithExec?_of_actualRequests
    target occurrence (input.localizedDependencyView state target)
    (input.localizedWholeStateReader state) rule3FrameOf
    (input.LocalizedRerootReadersAgreeOnRequests_of_outwardCursors target state _ outward)

/-! ## Actual composition with the original-target request locality -/

/-- **Actual production composition.**  For a physical occurrence `O` of a perceived open even
axis and an original descriptor target `T` strictly shallower in the same rooted carrier
(`LocalizedDepthDependency O T`), the ordinary spatial wrapper over the whole auxiliary state is
exactly the executable spatial wrapper over the restricted dependency view — same arbitrary
supplied Rule-3 callback, full `Option` agreement.

The per-request outward premise is discharged by `rule3ActualRequest_outward`; no successful key,
comparison, callback result or descriptor premise is used.  The physical occurrence `O` and the
descriptor target `T` remain distinct. -/
theorem localizedRule3ShortCircuitSpatialUnitWithRead?_wholeState_eq_Exec?_of_deeper
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O T : input.LocalizedCIPOccurrence carrierFuel)
    (deeper : input.LocalizedDepthDependency O T)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    input.localizedRule3ShortCircuitSpatialUnitWithRead?
        T O (input.localizedDependencyView state T)
        (input.localizedWholeStateReader state) rule3FrameOf =
      input.localizedRule3ShortCircuitSpatialUnitWithExec?
        T O (input.localizedDependencyView state T) rule3FrameOf :=
  input.localizedRule3ShortCircuitSpatialUnitWithRead?_wholeState_eq_Exec?_of_outwardCursors
    T O state rule3FrameOf (input.rule3ActualRequest_outward O T deeper)

/-- **Actual left-orientation caller composition.**  The exact selector call the ordinary spatial
wrapper makes for its left endpoint, under the actual recovered physical topology of `O`, returns
the executable selector from the whole state.  The outward premise is
`rule3ActualRequest_outward O T deeper`; the topology hypothesis is the actual recovery equation,
not an assumed success of any key or callback. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_wholeState_eq_Exec?_of_deeper_left
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O T : input.LocalizedCIPOccurrence carrierFuel)
    (deeper : input.LocalizedDepthDependency O T)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec? O = some frame) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        T (input.localizedDependencyView state T)
        (input.localizedWholeStateReader state) rule3FrameOf
        frame.left frame.right frame.leftCursor =
      input.localizedRule3ShortCircuitEndpointPriorityExec?
        T (input.localizedDependencyView state T) rule3FrameOf
        frame.left frame.right frame.leftCursor :=
  input.localizedRule3ShortCircuitEndpointPriorityWithRead?_wholeState_eq_Exec?_of_spatialOutward_left
    T O state rule3FrameOf frame computed (input.rule3ActualRequest_outward O T deeper)

/-- **Actual right-orientation caller composition.**  The analogous exact selector call for the
right endpoint. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_wholeState_eq_Exec?_of_deeper_right
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O T : input.LocalizedCIPOccurrence carrierFuel)
    (deeper : input.LocalizedDepthDependency O T)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec? O = some frame) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        T (input.localizedDependencyView state T)
        (input.localizedWholeStateReader state) rule3FrameOf
        frame.right frame.left frame.rightCursor =
      input.localizedRule3ShortCircuitEndpointPriorityExec?
        T (input.localizedDependencyView state T) rule3FrameOf
        frame.right frame.left frame.rightCursor :=
  input.localizedRule3ShortCircuitEndpointPriorityWithRead?_wholeState_eq_Exec?_of_spatialOutward_right
    T O state rule3FrameOf frame computed (input.rule3ActualRequest_outward O T deeper)

/-- **Actual production composition at the shipped restricted callback.**  Instantiating the
arbitrary callback of `..._of_deeper` with the actual restricted ordinary short-circuit frame
builder `buildLocalizedShortCircuitRule3FrameExec? T view budget` keeps the same full `Option`
equality.  The callback is literally the same term on both sides; no property of the callback is
assumed. -/
theorem localizedRule3ShortCircuitSpatialUnitWithRead?_wholeState_eq_Exec?_of_deeper_shortCircuitFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O T : input.LocalizedCIPOccurrence carrierFuel)
    (deeper : input.LocalizedDepthDependency O T)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (budget : Nat) :
    input.localizedRule3ShortCircuitSpatialUnitWithRead?
        T O (input.localizedDependencyView state T)
        (input.localizedWholeStateReader state)
        (input.buildLocalizedShortCircuitRule3FrameExec?
          T (input.localizedDependencyView state T) budget) =
      input.localizedRule3ShortCircuitSpatialUnitWithExec?
        T O (input.localizedDependencyView state T)
        (input.buildLocalizedShortCircuitRule3FrameExec?
          T (input.localizedDependencyView state T) budget) :=
  input.localizedRule3ShortCircuitSpatialUnitWithRead?_wholeState_eq_Exec?_of_deeper
    O T deeper state _

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedWholeStateReader
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedWholeStateReader_apply
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRerootReadersAgreeOnRequests_of_outwardCursors
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_wholeState_eq_restricted_of_outwardCursors
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_wholeState_eq_Exec?_of_outwardCursors
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortEndpointCallbackRequests_left_mem_spatial
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortEndpointCallbackRequests_right_mem_spatial
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_wholeState_eq_restricted_of_outwardCursors
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_wholeState_eq_Exec?_of_outwardCursors
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_wholeState_eq_Exec?_of_spatialOutward_left
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_wholeState_eq_Exec?_of_spatialOutward_right
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialUnitWithRead?_wholeState_eq_restricted_of_outwardCursors
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialUnitWithRead?_wholeState_eq_Exec?_of_outwardCursors
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_wholeState_eq_Exec?_of_deeper_left
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_wholeState_eq_Exec?_of_deeper_right
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialUnitWithRead?_wholeState_eq_Exec?_of_deeper
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialUnitWithRead?_wholeState_eq_Exec?_of_deeper_shortCircuitFrame
