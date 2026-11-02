import TetraStereo.OneCenter.LocalizedRule3OddRoute
import TetraStereo.OneCenter.LocalizedRule3ShortCircuitOddSpatial
import TetraStereo.OneCenter.LocalizedRule3NodeCallbackDemand

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- Extend the existing node evaluator at the exact nonordinary odd-axis route. Strict
constitutional endpoint priorities avoid unnecessary recursive stereo comparisons. -/
def localizedRule3ExtendedShortCircuitNodeWithExec?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor fuel) → Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    Option (Option input.LocalizedRule3SpatialNodeResult) :=
  match input.localizedRule3OddRouteCertificate? occurrence with
  | none => input.localizedRule3ShortCircuitNodeWithExec? target occurrence view callback excluded
  | some _ => do
      let result ← input.localizedRule3ShortCircuitOddSpatialUnitWithExec? target occurrence view callback
      let observation := input.localizedRule3ShortCircuitOddSpatialObservation result
      pure (if excluded.contains observation.physicalUnitId then none else some observation)

/-- Independent node meaning: retain every previous derivation and add an odd-axis derivation
using existing topology, independent endpoint priorities and exact spatial geometry. -/
inductive DeclarativeLocalizedRule3ExtendedShortCircuitNodeWith
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (FrameMeaning : input.LocalizedRule3FrameMeaning fuel)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    Option input.LocalizedRule3SpatialNodeResult → Prop where
  | previous {observation}
      (derived : input.DeclarativeLocalizedRule3ShortCircuitNodeWith
        target view FrameMeaning excluded occurrence observation) :
      input.DeclarativeLocalizedRule3ExtendedShortCircuitNodeWith
        target view FrameMeaning excluded occurrence observation
  | odd (route : input.LocalizedRule3OddRoute occurrence)
      (result : input.LocalizedRule3ShortCircuitOddSpatialResult fuel)
      (derived : input.DeclarativeLocalizedRule3ShortCircuitOddSpatialResult
        target occurrence view FrameMeaning result) :
      input.DeclarativeLocalizedRule3ExtendedShortCircuitNodeWith
        target view FrameMeaning excluded occurrence
        (if excluded.contains (input.localizedRule3ShortCircuitOddSpatialObservation result).physicalUnitId
          then none else some (input.localizedRule3ShortCircuitOddSpatialObservation result))

theorem localizedRule3ExtendedShortCircuitNodeWithExec?_sound
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor fuel) → Option input.LocalizedRule3CanonicalKeyFrame)
    (FrameMeaning : input.LocalizedRule3FrameMeaning fuel)
    (callbackSound : ∀ cursors frame, callback cursors = some frame → FrameMeaning cursors frame)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (observation : Option input.LocalizedRule3SpatialNodeResult)
    (computed : input.localizedRule3ExtendedShortCircuitNodeWithExec?
      target occurrence view callback excluded = some observation) :
    input.DeclarativeLocalizedRule3ExtendedShortCircuitNodeWith
      target view FrameMeaning excluded occurrence observation := by
  unfold localizedRule3ExtendedShortCircuitNodeWithExec? at computed
  cases routed : input.localizedRule3OddRouteCertificate? occurrence with
  | none =>
      simp only [routed] at computed
      exact DeclarativeLocalizedRule3ExtendedShortCircuitNodeWith.previous
        (input.localizedRule3ShortCircuitNodeWithExec?_sound target occurrence view callback
          FrameMeaning callbackSound excluded observation computed)
  | some certificate =>
      cases spatial : input.localizedRule3ShortCircuitOddSpatialUnitWithExec?
          target occurrence view callback with
      | none => simp [routed, spatial] at computed
      | some result =>
          simp [routed, spatial] at computed
          subst observation
          simpa using (DeclarativeLocalizedRule3ExtendedShortCircuitNodeWith.odd
            (excluded := excluded) certificate.valid result
            (input.localizedRule3ShortCircuitOddSpatialUnitWithExec?_sound
              target occurrence view callback FrameMeaning callbackSound result spatial))

def rule3ShortOddCallbackRequests (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) : List (List (input.LocalizedRerootCursor fuel)) :=
  match input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel fuel) occurrence with
  | none => []
  | some topology =>
      input.rule3ShortEndpointCallbackRequests topology.initial.left topology.initial.right topology.initial.leftCursor ++
        input.rule3ShortEndpointCallbackRequests topology.right topology.rightPartner topology.rightCursor

theorem rule3ShortOddSpatial_callback_local
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor fuel) → Option input.LocalizedRule3CanonicalKeyFrame)
    (agree : input.Rule3CallbackAgreesOn (input.rule3ShortOddCallbackRequests occurrence) before after) :
    input.localizedRule3ShortCircuitOddSpatialUnitWithExec? target occurrence view before =
      input.localizedRule3ShortCircuitOddSpatialUnitWithExec? target occurrence view after := by
  unfold localizedRule3ShortCircuitOddSpatialUnitWithExec?
  cases found : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel fuel) occurrence with
  | none => simp
  | some topology =>
      have left := input.rule3ShortEndpoint_callback_local target view before after
        topology.initial.left topology.initial.right topology.initial.leftCursor (by
          intro cursors member
          exact agree cursors (by simp [rule3ShortOddCallbackRequests, found, member]))
      have right := input.rule3ShortEndpoint_callback_local target view before after
        topology.right topology.rightPartner topology.rightCursor (by
          intro cursors member
          exact agree cursors (by simp [rule3ShortOddCallbackRequests, found, member]))
      simp [left, right]

/-- Actual requests of the extended evaluator; other routes retain the old demand analysis. -/
def rule3ExtendedNodeCallbackRequests (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) : List (List (input.LocalizedRerootCursor fuel)) :=
  match input.localizedRule3OddRouteCertificate? occurrence with
  | none => input.rule3NodeCallbackRequests occurrence
  | some _ => input.rule3ShortOddCallbackRequests occurrence

theorem rule3ExtendedNode_callback_local
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor fuel) → Option input.LocalizedRule3CanonicalKeyFrame)
    (agree : input.Rule3CallbackAgreesOn (input.rule3ExtendedNodeCallbackRequests occurrence) before after)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.localizedRule3ExtendedShortCircuitNodeWithExec? target occurrence view before excluded =
      input.localizedRule3ExtendedShortCircuitNodeWithExec? target occurrence view after excluded := by
  unfold localizedRule3ExtendedShortCircuitNodeWithExec?
  cases routed : input.localizedRule3OddRouteCertificate? occurrence with
  | none =>
      exact input.rule3Node_callback_local target occurrence view before after
        (by simpa only [rule3ExtendedNodeCallbackRequests, routed] using agree) excluded
  | some certificate =>
      rw [input.rule3ShortOddSpatial_callback_local target occurrence view before after
        (by simpa only [rule3ExtendedNodeCallbackRequests, routed] using agree)]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
