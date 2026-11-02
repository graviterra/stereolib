import TetraStereo.OneCenter.LocalizedRule3ShortCircuitSpatial

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- Equality is required only at the finite callback requests listed by the input-derived
demand analysis. Complete optional results, including refusal, are compared. -/
def Rule3CallbackAgreesOn (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (requests : List (List (input.LocalizedRerootCursor fuel)))
    (before after : List (input.LocalizedRerootCursor fuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) : Prop :=
  ∀ cursors ∈ requests, before cursors = after cursors

/-- The full endpoint compiler can request only its two actual canonical reference cursors.
Missing references and malformed candidate counts produce no callback demand. -/
def rule3EndpointCallbackRequests (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpoint partner : input.Atom) (cursor : input.LocalizedRerootCursor fuel) :
    List (List (input.LocalizedRerootCursor fuel)) :=
  match input.localizedRule3ExplicitSubstituents endpoint partner with
  | [first, second] =>
    match input.localizedRule3ReferenceCursorExec? cursor first with
    | none => []
    | some firstCursor =>
      match input.localizedRule3ReferenceCursorExec? cursor second with
      | none => []
      | some secondCursor => [[firstCursor, secondCursor]]
  | _ => []

/-- Strict root or complete constitutional comparisons suppress the recursive endpoint demand.
A constitutional tie or refusal retains exactly the full endpoint's possible request. -/
def rule3ShortEndpointCallbackRequests (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpoint partner : input.Atom) (cursor : input.LocalizedRerootCursor fuel) :
    List (List (input.LocalizedRerootCursor fuel)) :=
  match input.localizedRule3ExplicitSubstituents endpoint partner with
  | [first, second] =>
    match input.localizedRule3ReferenceCursorExec? cursor first with
    | none => []
    | some firstCursor =>
      match input.localizedRule3ReferenceCursorExec? cursor second with
      | none => []
      | some secondCursor =>
        match input.compareLocalizedRerootCursorConstitutionalRoot firstCursor secondCursor with
        | .gt | .lt => []
        | .eq =>
          match input.compareLocalizedConstitutionalCursors? firstCursor secondCursor with
          | some .gt | some .lt => []
          | _ => [[firstCursor, secondCursor]]
  | _ => []

theorem rule3Endpoint_callback_local
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor fuel) → Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom) (cursor : input.LocalizedRerootCursor fuel)
    (agree : input.Rule3CallbackAgreesOn (input.rule3EndpointCallbackRequests endpoint partner cursor) before after) :
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec? target view before endpoint partner cursor =
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec? target view after endpoint partner cursor := by
  unfold buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
  split
  · rename_i first second candidates
    cases firstComputed : input.localizedRule3ReferenceCursorExec? cursor first with
    | none => simp
    | some firstCursor =>
      cases secondComputed : input.localizedRule3ReferenceCursorExec? cursor second with
      | none => simp
      | some secondCursor =>
        have requested := agree [firstCursor, secondCursor] (by
          simp [rule3EndpointCallbackRequests, candidates, firstComputed, secondComputed])
        simp [requested]
  · rfl

theorem rule3ShortEndpoint_callback_local
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor fuel) → Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom) (cursor : input.LocalizedRerootCursor fuel)
    (agree : input.Rule3CallbackAgreesOn (input.rule3ShortEndpointCallbackRequests endpoint partner cursor) before after) :
    input.localizedRule3ShortCircuitEndpointPriorityExec? target view before endpoint partner cursor =
      input.localizedRule3ShortCircuitEndpointPriorityExec? target view after endpoint partner cursor := by
  unfold localizedRule3ShortCircuitEndpointPriorityExec?
  split
  · rename_i first second candidates
    cases firstComputed : input.localizedRule3ReferenceCursorExec? cursor first with
    | none => simp
    | some firstCursor =>
      cases secondComputed : input.localizedRule3ReferenceCursorExec? cursor second with
      | none => simp
      | some secondCursor =>
        simp only [bind, Option.bind_some]
        cases root : input.compareLocalizedRerootCursorConstitutionalRoot firstCursor secondCursor with
        | gt => rfl
        | lt => rfl
        | eq =>
          have fullAgree (deferred : input.rule3ShortEndpointCallbackRequests endpoint partner cursor =
              input.rule3EndpointCallbackRequests endpoint partner cursor) :
              input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec? target view before endpoint partner cursor =
                input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec? target view after endpoint partner cursor :=
            input.rule3Endpoint_callback_local target view before after endpoint partner cursor (deferred ▸ agree)
          cases constitutional : input.compareLocalizedConstitutionalCursors? firstCursor secondCursor with
          | none =>
            rw [fullAgree (by simp [rule3ShortEndpointCallbackRequests, rule3EndpointCallbackRequests,
              candidates, firstComputed, secondComputed, root, constitutional])]
          | some order =>
            cases order with
            | gt => rfl
            | lt => rfl
            | eq =>
              rw [fullAgree (by simp [rule3ShortEndpointCallbackRequests, rule3EndpointCallbackRequests,
                candidates, firstComputed, secondComputed, root, constitutional])]
  · rfl

/-- The ordinary spatial wrapper may request either endpoint pair. Both are included even when
the first endpoint fails before the second is evaluated. -/
def rule3ShortSpatialCallbackRequests (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) : List (List (input.LocalizedRerootCursor fuel)) :=
  match input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence with
  | none => []
  | some topology =>
    input.rule3ShortEndpointCallbackRequests topology.left topology.right topology.leftCursor ++
      input.rule3ShortEndpointCallbackRequests topology.right topology.left topology.rightCursor

theorem rule3ShortSpatial_callback_local
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor fuel) → Option input.LocalizedRule3CanonicalKeyFrame)
    (agree : input.Rule3CallbackAgreesOn (input.rule3ShortSpatialCallbackRequests occurrence) before after) :
    input.localizedRule3ShortCircuitSpatialUnitWithExec? target occurrence view before =
      input.localizedRule3ShortCircuitSpatialUnitWithExec? target occurrence view after := by
  unfold localizedRule3ShortCircuitSpatialUnitWithExec?
  cases found : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence with
  | none => simp
  | some topology =>
    have left := input.rule3ShortEndpoint_callback_local target view before after
      topology.left topology.right topology.leftCursor (by
        intro cursors member
        exact agree cursors (by simp [rule3ShortSpatialCallbackRequests, found, member]))
    have right := input.rule3ShortEndpoint_callback_local target view before after
      topology.right topology.left topology.rightCursor (by
        intro cursors member
        exact agree cursors (by simp [rule3ShortSpatialCallbackRequests, found, member]))
    simp [left, right]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
