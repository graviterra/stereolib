import TetraStereo.OneCenter.LocalizedOriginalNodeObservableCompletion
import TetraStereo.OneCenter.LocalizedCyclicSemanticCompletion
import TetraStereo.OneCenter.LocalizedRule3RouteCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

















































/-- Observation-level compilation interface of the ordinary/spatial unit.  This is exactly the
`spatialObservationComplete` field of
`LocalizedOriginalNodeObservableCompletionObligations`, named so that the topological constructor
and its `NodeCompleteAt` corollary can be stated without repeating the body. -/
abbrev LocalizedRule3NodeSpatialObservationComplete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel) : Prop :=
  ∀ result,
    input.DeclarativeLocalizedRule3OccurrenceDescriptorBearingSpatialUnitWith
        target occurrence view Rule3FrameMeaning result →
      ∃ compiled,
        input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
            target occurrence view rule3FrameOf = some compiled ∧
          input.localizedRule3DescriptorBearingObservation compiled =
            input.localizedRule3DescriptorBearingObservation result

/-- Observation-level compilation interface of the required monocyclic `E/Z` unit. -/
abbrev LocalizedRule3NodeCyclicObservationComplete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel) : Prop :=
  ∀ result,
    input.DeclarativeLocalizedRule3RequiredMonocyclicEZWith
        target occurrence view Rule3FrameMeaning result →
      ∃ compiled,
        input.localizedRule3RequiredMonocyclicEZWith?
            target occurrence view rule3FrameOf = some compiled ∧
          input.localizedRule3RequiredMonocyclicEZObservation compiled =
            input.localizedRule3RequiredMonocyclicEZObservation result

/-- Observation-level compilation interface of the odd-cumulene unit. -/
abbrev LocalizedRule3NodeOddCumuleneObservationComplete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel) : Prop :=
  ∀ result,
    input.DeclarativeLocalizedRule3OddCumuleneDescriptorBearingSpatialUnitWith
        target occurrence view Rule3FrameMeaning result →
      ∃ compiled,
        input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
            target occurrence view rule3FrameOf = some compiled ∧
          input.localizedRule3OddCumuleneDescriptorBearingObservation compiled =
            input.localizedRule3OddCumuleneDescriptorBearingObservation result

/-! ## The four new topological component lemmas

Terminal and ring-closing entries are discharged directly by the imported reflection theorems;
the statements below provide the two remaining entry shapes and the two non-entry fields. -/

/-- A proved internal entry is returned by the executable entry classifier at the same physical
frame and the same linear continuation.  The executable physical endpoint recovery returns the
declared frame, and the declared linear parent-side topology is recognized by the executable
topology classifier. -/
theorem localizedRule3CumulatedAxisEntry?_internal_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {occurrence : input.LocalizedCIPOccurrence carrierFuel}
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    {previousAxis : input.LocalizedRerootCursor carrierFuel}
    (derived : input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence
      (.internal initial previousAxis)) :
    input.localizedRule3CumulatedAxisEntry? occurrence =
      some (.internal initial previousAxis) := by
  cases derived with
  | internal physical continuation =>
      have physicalComputed :=
        input.localizedRule3PhysicalEndpointCursorFrame?_eq_some_of_declarative
          occurrence initial physical
      have continuationComputed :=
        input.localizedRule3AxisTopology?_eq_linear_of_declarative continuation
      simp [localizedRule3CumulatedAxisEntry?, physicalComputed, continuationComputed]

/-- A proved branched entry is recognized as *some* branched entry at the same physical frame.
Only the topology *category* is reflected: the executable continuation payload is existential and
is never identified with the declarative one, matching the observation-level weakening of
`LocalizedOriginalNodeObservableCompletionObligations`. -/
theorem localizedRule3CumulatedAxisEntry?_branched_observable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {occurrence : input.LocalizedCIPOccurrence carrierFuel}
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    {first second : input.LocalizedRerootCursor carrierFuel}
    {rest : List (input.LocalizedRerootCursor carrierFuel)}
    (derived : input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence
      (.branched initial first second rest)) :
    ∃ actualFirst actualSecond actualRest,
      input.localizedRule3CumulatedAxisEntry? occurrence =
        some (.branched initial actualFirst actualSecond actualRest) := by
  cases derived with
  | branched physical branchTopology =>
      obtain ⟨actualFirst, actualSecond, actualRest, topologyComputed⟩ :=
        input.localizedRule3AxisTopology?_branched_of_declarative branchTopology
      have physicalComputed :=
        input.localizedRule3PhysicalEndpointCursorFrame?_eq_some_of_declarative
          occurrence initial physical
      exact ⟨actualFirst, actualSecond, actualRest, by
        simp [localizedRule3CumulatedAxisEntry?, physicalComputed, topologyComputed]⟩

/-- A proved terminal-to-terminal endpoint frame is walked exactly by the executable traversal at
the production traversal fuel.  The compiled frame is the declared frame itself, so its physical
double-bond count (the length of the rightward walk) agrees definitionally.  This is the
`axisDoubleBondCountComplete` field of the observation obligations. -/
theorem localizedRule3CumulatedEndpointCursorFrame?_doubleBondCount_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {occurrence : input.LocalizedCIPOccurrence carrierFuel}
    {axis : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel}
    (derived :
      input.DeclarativeLocalizedRule3CumulatedEndpointCursorFrame occurrence axis) :
    ∃ compiled,
      input.localizedRule3CumulatedEndpointCursorFrame?
          (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some compiled ∧
        compiled.doubleBondCount = axis.doubleBondCount :=
  ⟨axis,
    input.localizedRule3CumulatedEndpointCursorFrame?_eq_some_at_traversalFuel_of_declarative
      occurrence axis derived,
    rfl⟩

/-- A proved permanently-omitted monocycle is recognized by the executable cyclic route as an
ordinary-monocyclic-policy route with the same policy *category*.  This is the
`omissionCategoryComplete` field of the observation obligations, and it follows from the
unconditional cyclic-route recognition without any endpoint, geometry or descriptor premise. -/
theorem localizedRule3CyclicAuthorityRoute?_omissionCategory_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {occurrence : input.LocalizedCIPOccurrence carrierFuel}
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    {closure : input.LocalizedRerootCursor carrierFuel}
    {policyResult : input.LocalizedMonocyclicDoubleBondPolicyResult}
    (derived : input.DeclarativeLocalizedRule3CyclicAuthorityRoute occurrence
      (.ordinaryMonocyclicPolicy initial closure policyResult))
    (omitted : policyResult.policy =
      BlueBookP93.Cyclic.DoubleBondDescriptorPolicy.permanentlyOmit) :
    ∃ actualInitial actualClosure actualPolicyResult,
      input.localizedRule3CyclicAuthorityRoute? occurrence =
          some (.ordinaryMonocyclicPolicy actualInitial actualClosure actualPolicyResult) ∧
        actualPolicyResult.policy =
          BlueBookP93.Cyclic.DoubleBondDescriptorPolicy.permanentlyOmit :=
  ⟨initial, closure, policyResult,
    input.localizedRule3CyclicAuthorityRoute?_complete occurrence
      (.ordinaryMonocyclicPolicy initial closure policyResult) derived,
    omitted⟩

/-! ## The constructor of the full nine-field obligations -/

/-- **Topological constructor.**  For an arbitrary target, occurrence, dependency view, Rule-3
frame callback and frame meaning, the six purely topological component obligations are discharged
unconditionally from the lower-layer reflection theorems.  The only parameters beyond the fixed
context are the three observation-compilation interfaces of the ordinary, cyclic and odd spatial
units.

Neither `rule3FrameOf` nor `Rule3FrameMeaning` occurs in any of the six discharged fields: the
statement is callback-independent, so it applies to the executable predecessor-frame builder, to
the extended callback, or to any independent frame meaning without change. -/
theorem localizedOriginalNodeObservableCompletionObligations_of_observations
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (spatialObservationComplete :
      input.LocalizedRule3NodeSpatialObservationComplete
        target occurrence view rule3FrameOf Rule3FrameMeaning)
    (cyclicObservationComplete :
      input.LocalizedRule3NodeCyclicObservationComplete
        target occurrence view rule3FrameOf Rule3FrameMeaning)
    (oddCumuleneObservationComplete :
      input.LocalizedRule3NodeOddCumuleneObservationComplete
        target occurrence view rule3FrameOf Rule3FrameMeaning) :
    input.LocalizedOriginalNodeObservableCompletionObligations
      target occurrence view rule3FrameOf Rule3FrameMeaning where
  terminalEntryComplete := fun _initial derived =>
    input.localizedRule3CumulatedAxisEntry?_eq_terminalStart_of_declarative derived
  internalEntryComplete := fun _initial _previousAxis derived =>
    input.localizedRule3CumulatedAxisEntry?_internal_complete derived
  ringEntryComplete := fun _initial _closure derived =>
    input.localizedRule3CumulatedAxisEntry?_eq_ringClosure_of_declarative derived
  branchedEntryObservable := fun _initial _first _second _rest derived =>
    input.localizedRule3CumulatedAxisEntry?_branched_observable derived
  axisDoubleBondCountComplete := fun _axis derived =>
    input.localizedRule3CumulatedEndpointCursorFrame?_doubleBondCount_complete derived
  spatialObservationComplete := spatialObservationComplete
  cyclicObservationComplete := cyclicObservationComplete
  oddCumuleneObservationComplete := oddCumuleneObservationComplete
  omissionCategoryComplete := fun _initial _closure _policyResult derived omitted =>
    input.localizedRule3CyclicAuthorityRoute?_omissionCategory_complete derived omitted

/-! ## The original-node `NodeCompleteAt` corollary -/










theorem localizedOriginalNodeObservableCompleteAt_of_observations
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (spatialObservationComplete : ∀ occurrence,
      input.LocalizedRule3NodeSpatialObservationComplete
        target occurrence view rule3FrameOf Rule3FrameMeaning)
    (cyclicObservationComplete : ∀ occurrence,
      input.LocalizedRule3NodeCyclicObservationComplete
        target occurrence view rule3FrameOf Rule3FrameMeaning)
    (oddCumuleneObservationComplete : ∀ occurrence,
      input.LocalizedRule3NodeOddCumuleneObservationComplete
        target occurrence view rule3FrameOf Rule3FrameMeaning) :
    input.LocalizedOriginalNodeObservableCompleteAt
      target view rule3FrameOf Rule3FrameMeaning :=
  input.localizedOriginalNodeObservableCompleteAt_of_obligations
    target view rule3FrameOf Rule3FrameMeaning
    (fun occurrence =>
      input.localizedOriginalNodeObservableCompletionObligations_of_observations
        target occurrence view rule3FrameOf Rule3FrameMeaning
        (spatialObservationComplete occurrence)
        (cyclicObservationComplete occurrence)
        (oddCumuleneObservationComplete occurrence))

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
