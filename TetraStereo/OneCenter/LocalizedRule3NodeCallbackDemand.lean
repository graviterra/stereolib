import TetraStereo.OneCenter.LocalizedRule3EndpointCallbackDemand
import TetraStereo.OneCenter.LocalizedRule3ShortCircuitNode

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

def rule3OrdinaryCallbackRequests (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) : List (List (input.LocalizedRerootCursor fuel)) :=
  match input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence with
  | none => []
  | some topology =>
    input.rule3EndpointCallbackRequests topology.left topology.right topology.leftCursor ++
      input.rule3EndpointCallbackRequests topology.right topology.left topology.rightCursor

def rule3OddCallbackRequests (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) : List (List (input.LocalizedRerootCursor fuel)) :=
  match input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel fuel) occurrence with
  | none => []
  | some topology =>
    input.rule3EndpointCallbackRequests topology.initial.left topology.initial.right topology.initial.leftCursor ++
      input.rule3EndpointCallbackRequests topology.right topology.rightPartner topology.rightCursor

def rule3RingCallbackRequests (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) : List (List (input.LocalizedRerootCursor fuel)) :=
  match input.localizedRule3CyclicAuthorityRouteExec? occurrence with
  | some (.ordinaryMonocyclicPolicy initial _ policy) =>
    match policy.policy with
    | .permanentlyOmit => []
    | .requireEZ =>
      input.rule3EndpointCallbackRequests initial.left initial.right initial.leftCursor ++
        input.rule3EndpointCallbackRequests initial.right initial.left initial.rightCursor
  | _ => []

theorem rule3Ordinary_callback_local
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor fuel) → Option input.LocalizedRule3CanonicalKeyFrame)
    (agree : input.Rule3CallbackAgreesOn (input.rule3OrdinaryCallbackRequests occurrence) before after) :
    input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec? target occurrence view before =
      input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec? target occurrence view after := by
  unfold localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec?
  cases found : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence with
  | none => simp
  | some topology =>
    have left := input.rule3Endpoint_callback_local target view before after
      topology.left topology.right topology.leftCursor (by
        intro cursors member
        exact agree cursors (by simp [rule3OrdinaryCallbackRequests, found, member]))
    have right := input.rule3Endpoint_callback_local target view before after
      topology.right topology.left topology.rightCursor (by
        intro cursors member
        exact agree cursors (by simp [rule3OrdinaryCallbackRequests, found, member]))
    simp [left, right]

theorem rule3Odd_callback_local
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor fuel) → Option input.LocalizedRule3CanonicalKeyFrame)
    (agree : input.Rule3CallbackAgreesOn (input.rule3OddCallbackRequests occurrence) before after) :
    input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec? target occurrence view before =
      input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec? target occurrence view after := by
  unfold localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec?
  cases found : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel fuel) occurrence with
  | none => simp
  | some topology =>
    have left := input.rule3Endpoint_callback_local target view before after
      topology.initial.left topology.initial.right topology.initial.leftCursor (by
        intro cursors member
        exact agree cursors (by simp [rule3OddCallbackRequests, found, member]))
    have right := input.rule3Endpoint_callback_local target view before after
      topology.right topology.rightPartner topology.rightCursor (by
        intro cursors member
        exact agree cursors (by simp [rule3OddCallbackRequests, found, member]))
    simp [left, right]

theorem rule3Ring_callback_local
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor fuel) → Option input.LocalizedRule3CanonicalKeyFrame)
    (agree : input.Rule3CallbackAgreesOn (input.rule3RingCallbackRequests occurrence) before after) :
    input.localizedRule3RequiredMonocyclicEZWithExec? target occurrence view before =
      input.localizedRule3RequiredMonocyclicEZWithExec? target occurrence view after := by
  unfold localizedRule3RequiredMonocyclicEZWithExec?
  cases found : input.localizedRule3CyclicAuthorityRouteExec? occurrence with
  | none => simp
  | some route =>
    cases route with
    | fullyCyclicCumulene => rfl
    | ordinaryMonocyclicPolicyGap => rfl
    | ordinaryNonmonocyclic => rfl
    | ordinaryMonocyclicPolicy initial closure policy =>
      cases policyEq : policy.policy with
      | permanentlyOmit => simp [policyEq]
      | requireEZ =>
        have left := input.rule3Endpoint_callback_local target view before after
          initial.left initial.right initial.leftCursor (by
            intro cursors member
            exact agree cursors (by simp [rule3RingCallbackRequests, found, policyEq, member]))
        have right := input.rule3Endpoint_callback_local target view before after
          initial.right initial.left initial.rightCursor (by
            intro cursors member
            exact agree cursors (by simp [rule3RingCallbackRequests, found, policyEq, member]))
        simp [policyEq, left, right]

/-- Enumerate the full original node's potential requests along its actual topology route.
No callback result, geometry success, target label or recursive bound is supplied. -/
def rule3OriginalNodeCallbackRequests (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) : List (List (input.LocalizedRerootCursor fuel)) :=
  if input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence then
    match input.localizedRule3CumulatedAxisEntryExec? occurrence with
    | none => []
    | some (.internal _ _) => []
    | some (.branched _ _ _ _) => input.rule3OrdinaryCallbackRequests occurrence
    | some (.ringClosure _ _) => input.rule3RingCallbackRequests occurrence
    | some (.terminalStart _) =>
      match input.localizedRule3CumulatedEndpointCursorFrameExec?
          (input.localizedRule3CumulatedTraversalFuel fuel) occurrence with
      | none => []
      | some axis =>
        if axis.doubleBondCount = 1 then input.rule3OrdinaryCallbackRequests occurrence
        else if Odd axis.doubleBondCount then input.rule3OddCallbackRequests occurrence
        else []
  else []

theorem rule3OriginalNode_callback_local
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor fuel) → Option input.LocalizedRule3CanonicalKeyFrame)
    (agree : input.Rule3CallbackAgreesOn (input.rule3OriginalNodeCallbackRequests occurrence) before after)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.localizedDescriptorBearingRule3NodeWithExec? target occurrence view before excluded =
      input.localizedDescriptorBearingRule3NodeWithExec? target occurrence view after excluded := by
  unfold localizedDescriptorBearingRule3NodeWithExec?
  by_cases edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence
  · simp only [dif_pos edge]
    cases entry : input.localizedRule3CumulatedAxisEntryExec? occurrence with
    | none => rfl
    | some value =>
      cases value with
      | internal => rfl
      | branched =>
        rw [input.rule3Ordinary_callback_local target occurrence view before after (by
          simpa only [rule3OriginalNodeCallbackRequests, if_pos edge, entry] using agree)]
      | ringClosure =>
        rw [input.rule3Ring_callback_local target occurrence view before after (by
          simpa only [rule3OriginalNodeCallbackRequests, if_pos edge, entry] using agree)]
      | terminalStart =>
        dsimp only
        cases axis : input.localizedRule3CumulatedEndpointCursorFrameExec?
            (input.localizedRule3CumulatedTraversalFuel fuel) occurrence with
        | none => rfl
        | some topology =>
          dsimp only
          by_cases ordinary : topology.doubleBondCount = 1
          · simp only [dif_pos ordinary]
            rw [input.rule3Ordinary_callback_local target occurrence view before after (by
              simpa only [rule3OriginalNodeCallbackRequests, if_pos edge, entry, axis, if_pos ordinary] using agree)]
          · simp only [dif_neg ordinary]
            by_cases odd : Odd topology.doubleBondCount
            · simp only [dif_pos odd]
              rw [input.rule3Odd_callback_local target occurrence view before after (by
                simpa only [rule3OriginalNodeCallbackRequests, if_pos edge, entry, axis,
                  if_neg ordinary, if_pos odd] using agree)]
            · simp only [dif_neg odd]
  · simp only [dif_neg edge]

/-- The successor uses the precise short-circuit demands for ordinary nodes, retaining original
route demands everywhere else. It is uniform in the auxiliary view and exclusion list. -/
def rule3NodeCallbackRequests (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) : List (List (input.LocalizedRerootCursor fuel)) :=
  match input.localizedRule3OrdinaryRouteCertificate? occurrence with
  | none => input.rule3OriginalNodeCallbackRequests occurrence
  | some _ => input.rule3ShortSpatialCallbackRequests occurrence

theorem rule3Node_callback_local
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor fuel) → Option input.LocalizedRule3CanonicalKeyFrame)
    (agree : input.Rule3CallbackAgreesOn (input.rule3NodeCallbackRequests occurrence) before after)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.localizedRule3ShortCircuitNodeWithExec? target occurrence view before excluded =
      input.localizedRule3ShortCircuitNodeWithExec? target occurrence view after excluded := by
  unfold localizedRule3ShortCircuitNodeWithExec?
  cases route : input.localizedRule3OrdinaryRouteCertificate? occurrence with
  | none =>
    exact input.rule3OriginalNode_callback_local target occurrence view before after
      (by simpa only [rule3NodeCallbackRequests, route] using agree) excluded
  | some certificate =>
    rw [input.rule3ShortSpatial_callback_local target occurrence view before after
      (by simpa only [rule3NodeCallbackRequests, route] using agree)]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
