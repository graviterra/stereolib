import TetraStereo.OneCenter.LocalizedRule3ExclusionExtensionality

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter


























namespace CertifiedLocalizedCIPInput

/-- Embed an odd-cumulene endpoint frame into the general cumulated endpoint frame.  Both carry
the same maximal nonbranching rightward axis and the same terminal cursors, so the projection is
field-wise the identity; only the additional odd-count evidence is dropped. -/
def oddCumuleneEndpointCursorFrameToCumulated
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel) :
    input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel :=
  { initial := frame.initial
    rightward := frame.rightward
    rightPartnerCursor := frame.rightPartnerCursor
    rightCursor := frame.rightCursor
    rightPartner := frame.rightPartner
    right := frame.right }

/-- The independent odd-cumulene topology is a complete terminal-start axis: the terminal left
topology and the walked rightward axis assemble the general endpoint frame, with the reverse
witness extended by the left cursor. -/
theorem declarativeOddCumuleneEndpointCursorFrame_toCumulated
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (derived : input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame occurrence frame) :
    input.DeclarativeLocalizedRule3CumulatedEndpointCursorFrame occurrence
      (input.oddCumuleneEndpointCursorFrameToCumulated frame) := by
  rcases derived with ⟨physical, terminal, walk, reversed, rightPartner, right, _above, _odd⟩
  refine ⟨
    DeclarativeLocalizedRule3CumulatedAxisEntry.terminalStart physical terminal,
    walk,
    ?_,
    rightPartner,
    right⟩
  rcases reversed with ⟨rest, reversedEq⟩
  refine ⟨rest ++ [frame.initial.leftCursor], ?_⟩
  simp [oddCumuleneEndpointCursorFrameToCumulated, reversedEq]

/-- Every ordinary-monocyclic-policy authority route carries the occurrence-local ring-closure
entry that produced it. -/
theorem ringClosureEntry_of_ordinaryMonocyclicPolicy
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    {closure : input.LocalizedRerootCursor carrierFuel}
    {policyResult : input.LocalizedMonocyclicDoubleBondPolicyResult}
    (route : input.DeclarativeLocalizedRule3CyclicAuthorityRoute occurrence
      (.ordinaryMonocyclicPolicy initial closure policyResult)) :
    input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence
      (.ringClosure initial closure) := by
  cases route with
  | ordinaryMonocyclicPolicy moleculeRoute _policy =>
      cases moleculeRoute with
      | ordinaryCyclicDoubleBondSystem entry _notFullyCyclic => exact entry

/-- A required monocyclic descriptor exposes the ring-closure entry through its authority route. -/
theorem requiredMonocyclicEZWith_ringClosureEntry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (result : input.LocalizedRule3RequiredMonocyclicEZResult carrierFuel)
    (derived : input.DeclarativeLocalizedRule3RequiredMonocyclicEZWith
      target occurrence view Rule3FrameMeaning result) :
    input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence
      (.ringClosure result.initial result.closure) :=
  input.ringClosureEntry_of_ordinaryMonocyclicPolicy occurrence derived.1

/-- Component completeness obligations of the callback-parameterized original node reader.  Each
field is the precise declarative-to-executable recognition that the corresponding reader of the
original node evaluator still needs; the structural, internal-axis, omission and even-axis routes
need only the first three topology fields. -/
structure LocalizedDescriptorBearingRule3NodeWithCompletionObligations
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel) : Prop where
  entryComplete : ∀ entry, input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence entry →
    input.localizedRule3CumulatedAxisEntry? occurrence = some entry
  axisComplete : ∀ axis, input.DeclarativeLocalizedRule3CumulatedEndpointCursorFrame occurrence axis →
    input.localizedRule3CumulatedEndpointCursorFrame?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some axis
  cyclicRouteComplete : ∀ route, input.DeclarativeLocalizedRule3CyclicAuthorityRoute occurrence route →
    input.localizedRule3CyclicAuthorityRoute? occurrence = some route
  spatialComplete : ∀ result,
    input.DeclarativeLocalizedRule3OccurrenceDescriptorBearingSpatialUnitWith
      target occurrence view Rule3FrameMeaning result →
    input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
      target occurrence view rule3FrameOf = some result
  cyclicComplete : ∀ result,
    input.DeclarativeLocalizedRule3RequiredMonocyclicEZWith
      target occurrence view Rule3FrameMeaning result →
    input.localizedRule3RequiredMonocyclicEZWith? target occurrence view rule3FrameOf = some result
  oddComplete : ∀ result,
    input.DeclarativeLocalizedRule3OddCumuleneDescriptorBearingSpatialUnitWith
      target occurrence view Rule3FrameMeaning result →
    input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
      target occurrence view rule3FrameOf = some result

/-- Core converse: every independent original-node derivation is a successful run of the
classical original node reader at the same observation, given the six component obligations. -/
theorem localizedDescriptorBearingRule3NodeWith?_complete_core
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (obligations : input.LocalizedDescriptorBearingRule3NodeWithCompletionObligations
      target occurrence view rule3FrameOf Rule3FrameMeaning)
    {observation : Option input.LocalizedRule3SpatialNodeResult}
    (derived : input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
      target view Rule3FrameMeaning excluded occurrence observation) :
    input.localizedDescriptorBearingRule3NodeWith? target occurrence view rule3FrameOf excluded =
      some observation := by
  classical
  cases derived with
  | structural notEdge =>
      simp [localizedDescriptorBearingRule3NodeWith?, notEdge]
  | @internalCumulatedAxis initial previousAxis edge entry =>
      have entryComputed := obligations.entryComplete (.internal initial previousAxis) entry
      simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed]
  | @omittedMonocycle initial closure policyResult edge route omitted =>
      have entryComputed := obligations.entryComplete (.ringClosure initial closure)
        (input.ringClosureEntry_of_ordinaryMonocyclicPolicy occurrence route)
      have routeComputed := obligations.cyclicRouteComplete
        (.ordinaryMonocyclicPolicy initial closure policyResult) route
      exact input.localizedDescriptorBearingRule3NodeWith?_of_omittedMonocycle
        target occurrence view rule3FrameOf excluded initial closure initial closure
        policyResult edge entryComputed routeComputed omitted
  | @excludedCyclicUnit result observation edge cyclic observationEq excludedIdentity =>
      have entryComputed := obligations.entryComplete (.ringClosure result.initial result.closure)
        (input.requiredMonocyclicEZWith_ringClosureEntry
          target occurrence view Rule3FrameMeaning result cyclic)
      have resultComputed := obligations.cyclicComplete result cyclic
      have obsEq : input.localizedRule3RequiredMonocyclicEZObservation result = observation :=
        observationEq.symm
      simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed, resultComputed,
        obsEq, excludedIdentity]
  | @retainedCyclicGeometry result observation edge cyclic observationEq freshIdentity =>
      have entryComputed := obligations.entryComplete (.ringClosure result.initial result.closure)
        (input.requiredMonocyclicEZWith_ringClosureEntry
          target occurrence view Rule3FrameMeaning result cyclic)
      have resultComputed := obligations.cyclicComplete result cyclic
      have obsEq : input.localizedRule3RequiredMonocyclicEZObservation result = observation :=
        observationEq.symm
      simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed, resultComputed,
        obsEq, freshIdentity]
  | @evenCumulatedAxis axis edge topology notOrdinary notPlanar =>
      have entryComputed := obligations.entryComplete (.terminalStart axis.initial) topology.1
      have axisComputed := obligations.axisComplete axis topology
      simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed, axisComputed,
        notOrdinary, notPlanar]
  | @excludedUnit result observation edge axis topology ordinary spatial observationEq excludedIdentity =>
      have entryComputed := obligations.entryComplete (.terminalStart axis.initial) topology.1
      have axisComputed := obligations.axisComplete axis topology
      have resultComputed := obligations.spatialComplete result spatial
      have obsEq : input.localizedRule3DescriptorBearingObservation result = observation :=
        observationEq.symm
      simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed, axisComputed,
        ordinary, resultComputed, obsEq, excludedIdentity]
  | @retainedGeometry result observation edge axis topology ordinary spatial observationEq freshIdentity =>
      have entryComputed := obligations.entryComplete (.terminalStart axis.initial) topology.1
      have axisComputed := obligations.axisComplete axis topology
      have resultComputed := obligations.spatialComplete result spatial
      have obsEq : input.localizedRule3DescriptorBearingObservation result = observation :=
        observationEq.symm
      simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed, axisComputed,
        ordinary, resultComputed, obsEq, freshIdentity]
  | @excludedBranchedUnit initial first second rest result observation edge entry spatial
      observationEq excludedIdentity =>
      have entryComputed := obligations.entryComplete (.branched initial first second rest) entry
      have resultComputed := obligations.spatialComplete result spatial
      have obsEq : input.localizedRule3DescriptorBearingObservation result = observation :=
        observationEq.symm
      simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed, resultComputed,
        obsEq, excludedIdentity]
  | @retainedBranchedGeometry initial first second rest result observation edge entry spatial
      observationEq freshIdentity =>
      have entryComputed := obligations.entryComplete (.branched initial first second rest) entry
      have resultComputed := obligations.spatialComplete result spatial
      have obsEq : input.localizedRule3DescriptorBearingObservation result = observation :=
        observationEq.symm
      simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed, resultComputed,
        obsEq, freshIdentity]
  | @excludedOddCumulene result observation edge odd observationEq excludedIdentity =>
      have oddTopology : input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame
          occurrence result.topology := odd.1
      have cumulatedDerived : input.DeclarativeLocalizedRule3CumulatedEndpointCursorFrame
          occurrence (input.oddCumuleneEndpointCursorFrameToCumulated result.topology) :=
        input.declarativeOddCumuleneEndpointCursorFrame_toCumulated occurrence
          result.topology oddTopology
      have entryComputed := obligations.entryComplete (.terminalStart result.topology.initial)
        cumulatedDerived.1
      have axisComputed := obligations.axisComplete
        (input.oddCumuleneEndpointCursorFrameToCumulated result.topology) cumulatedDerived
      have resultComputed := obligations.oddComplete result odd
      have notOrdinary :
          (input.oddCumuleneEndpointCursorFrameToCumulated result.topology).doubleBondCount ≠ 1 := by
        rcases oddTopology with ⟨_physical, _terminal, _walk, _reversed, _rp, _r, above, _oddCount⟩
        exact Nat.ne_of_gt above
      have planar :
          Odd (input.oddCumuleneEndpointCursorFrameToCumulated result.topology).doubleBondCount := by
        rcases oddTopology with ⟨_physical, _terminal, _walk, _reversed, _rp, _r, _above, oddCount⟩
        exact oddCount
      have obsEq :
          input.localizedRule3OddCumuleneDescriptorBearingObservation result = observation :=
        observationEq.symm
      simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed, axisComputed,
        notOrdinary, planar, resultComputed, obsEq, excludedIdentity]
  | @retainedOddCumulene result observation edge odd observationEq freshIdentity =>
      have oddTopology : input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame
          occurrence result.topology := odd.1
      have cumulatedDerived : input.DeclarativeLocalizedRule3CumulatedEndpointCursorFrame
          occurrence (input.oddCumuleneEndpointCursorFrameToCumulated result.topology) :=
        input.declarativeOddCumuleneEndpointCursorFrame_toCumulated occurrence
          result.topology oddTopology
      have entryComputed := obligations.entryComplete (.terminalStart result.topology.initial)
        cumulatedDerived.1
      have axisComputed := obligations.axisComplete
        (input.oddCumuleneEndpointCursorFrameToCumulated result.topology) cumulatedDerived
      have resultComputed := obligations.oddComplete result odd
      have notOrdinary :
          (input.oddCumuleneEndpointCursorFrameToCumulated result.topology).doubleBondCount ≠ 1 := by
        rcases oddTopology with ⟨_physical, _terminal, _walk, _reversed, _rp, _r, above, _oddCount⟩
        exact Nat.ne_of_gt above
      have planar :
          Odd (input.oddCumuleneEndpointCursorFrameToCumulated result.topology).doubleBondCount := by
        rcases oddTopology with ⟨_physical, _terminal, _walk, _reversed, _rp, _r, _above, oddCount⟩
        exact oddCount
      have obsEq :
          input.localizedRule3OddCumuleneDescriptorBearingObservation result = observation :=
        observationEq.symm
      simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed, axisComputed,
        notOrdinary, planar, resultComputed, obsEq, freshIdentity]

/-- Executable converse: the compiled original node reader returns the exact optional observation
of every independent derivation, under the same six component obligations. -/
theorem localizedDescriptorBearingRule3NodeWithExec?_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (obligations : input.LocalizedDescriptorBearingRule3NodeWithCompletionObligations
      target occurrence view rule3FrameOf Rule3FrameMeaning)
    {observation : Option input.LocalizedRule3SpatialNodeResult}
    (derived : input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
      target view Rule3FrameMeaning excluded occurrence observation) :
    input.localizedDescriptorBearingRule3NodeWithExec?
      target occurrence view rule3FrameOf excluded = some observation := by
  rw [localizedDescriptorBearingRule3NodeWithExec?_eq_original]
  exact input.localizedDescriptorBearingRule3NodeWith?_complete_core
    target occurrence view rule3FrameOf Rule3FrameMeaning excluded obligations derived

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
