import TetraStereo.OneCenter.LocalizedOriginalNodeSemanticCompletion
import TetraStereo.OneCenter.LocalizedRule3ExtendedNodePreservation

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput


















































/-- Observation-level component interfaces of the callback-parameterized original node reader.

Every field is stated at the granularity actually inspected by `localizedDescriptorBearingRule3NodeWith?`.
No field assumes a desired node output, and no field identifies a compiled component record with a
derived one except where the reader itself requires exactness (the terminal/internal/ring entry
frames and the physical double-bond count). -/
structure LocalizedOriginalNodeObservableCompletionObligations
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel) : Prop where
  /-- A proved terminal-start entry is the entry the classifier returns. -/
  terminalEntryComplete : ∀ initial,
    input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence (.terminalStart initial) →
      input.localizedRule3CumulatedAxisEntry? occurrence = some (.terminalStart initial)
  /-- A proved internal entry is the entry the classifier returns. -/
  internalEntryComplete : ∀ initial previousAxis,
    input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence (.internal initial previousAxis) →
      input.localizedRule3CumulatedAxisEntry? occurrence = some (.internal initial previousAxis)
  /-- A proved ring-closing entry is the entry the classifier returns. -/
  ringEntryComplete : ∀ initial closure,
    input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence (.ringClosure initial closure) →
      input.localizedRule3CumulatedAxisEntry? occurrence = some (.ringClosure initial closure)
  /-- A proved branched entry is recognized as *some* branched entry at the same physical frame.
  The reader discards the enumerated continuations, so they need not coincide. -/
  branchedEntryObservable : ∀ initial first second rest,
    input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence
        (.branched initial first second rest) →
      ∃ actualFirst actualSecond actualRest,
        input.localizedRule3CumulatedAxisEntry? occurrence =
          some (.branched initial actualFirst actualSecond actualRest)
  /-- A proved terminal-start axis is walked to an actual frame with the same double-bond count.
  Only that count is inspected by the node reader. -/
  axisDoubleBondCountComplete : ∀ axis,
    input.DeclarativeLocalizedRule3CumulatedEndpointCursorFrame occurrence axis →
      ∃ compiled,
        input.localizedRule3CumulatedEndpointCursorFrame?
            (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some compiled ∧
          compiled.doubleBondCount = axis.doubleBondCount
  /-- A proved ordinary/spatial unit is compiled to an actual result carrying the same projected
  observation. -/
  spatialObservationComplete : ∀ result,
    input.DeclarativeLocalizedRule3OccurrenceDescriptorBearingSpatialUnitWith
        target occurrence view Rule3FrameMeaning result →
      ∃ compiled,
        input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
            target occurrence view rule3FrameOf = some compiled ∧
          input.localizedRule3DescriptorBearingObservation compiled =
            input.localizedRule3DescriptorBearingObservation result
  /-- A proved required monocyclic `E/Z` unit is compiled to an actual result carrying the same
  projected observation. -/
  cyclicObservationComplete : ∀ result,
    input.DeclarativeLocalizedRule3RequiredMonocyclicEZWith
        target occurrence view Rule3FrameMeaning result →
      ∃ compiled,
        input.localizedRule3RequiredMonocyclicEZWith?
            target occurrence view rule3FrameOf = some compiled ∧
          input.localizedRule3RequiredMonocyclicEZObservation compiled =
            input.localizedRule3RequiredMonocyclicEZObservation result
  /-- A proved odd-cumulene unit is compiled to an actual result carrying the same projected
  observation. -/
  oddCumuleneObservationComplete : ∀ result,
    input.DeclarativeLocalizedRule3OddCumuleneDescriptorBearingSpatialUnitWith
        target occurrence view Rule3FrameMeaning result →
      ∃ compiled,
        input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
            target occurrence view rule3FrameOf = some compiled ∧
          input.localizedRule3OddCumuleneDescriptorBearingObservation compiled =
            input.localizedRule3OddCumuleneDescriptorBearingObservation result
  /-- A proved permanently-omitted monocycle is recognized by the actual cyclic route as an
  ordinary-monocyclic-policy route with the same policy *category*. -/
  omissionCategoryComplete : ∀ initial closure policyResult,
    input.DeclarativeLocalizedRule3CyclicAuthorityRoute occurrence
        (.ordinaryMonocyclicPolicy initial closure policyResult) →
      policyResult.policy = .permanentlyOmit →
      ∃ actualInitial actualClosure actualPolicyResult,
        input.localizedRule3CyclicAuthorityRoute? occurrence =
            some (.ordinaryMonocyclicPolicy actualInitial actualClosure actualPolicyResult) ∧
          actualPolicyResult.policy = .permanentlyOmit

/-- The old exact-payload obligations of `LocalizedOriginalNodeSemanticCompletion` discharge the
observation-level interfaces. This records that the corrected statement is strictly weaker: no new
component assumption has been introduced. -/
def LocalizedOriginalNodeObservableCompletionObligations.ofExact
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (exact : input.LocalizedDescriptorBearingRule3NodeWithCompletionObligations
      target occurrence view rule3FrameOf Rule3FrameMeaning) :
    input.LocalizedOriginalNodeObservableCompletionObligations
      target occurrence view rule3FrameOf Rule3FrameMeaning where
  terminalEntryComplete := fun initial derived =>
    exact.entryComplete (.terminalStart initial) derived
  internalEntryComplete := fun initial previousAxis derived =>
    exact.entryComplete (.internal initial previousAxis) derived
  ringEntryComplete := fun initial closure derived =>
    exact.entryComplete (.ringClosure initial closure) derived
  branchedEntryObservable := fun initial first second rest derived =>
    ⟨first, second, rest,
      exact.entryComplete (.branched initial first second rest) derived⟩
  axisDoubleBondCountComplete := fun axis derived =>
    ⟨axis, exact.axisComplete axis derived, rfl⟩
  spatialObservationComplete := fun result derived =>
    ⟨result, exact.spatialComplete result derived, rfl⟩
  cyclicObservationComplete := fun result derived =>
    ⟨result, exact.cyclicComplete result derived, rfl⟩
  oddCumuleneObservationComplete := fun result derived =>
    ⟨result, exact.oddComplete result derived, rfl⟩
  omissionCategoryComplete := fun initial closure policyResult derived omitted =>
    ⟨initial, closure, policyResult,
      exact.cyclicRouteComplete (.ordinaryMonocyclicPolicy initial closure policyResult) derived,
      omitted⟩

/-- Core observation-level converse: every independent original-node derivation is a successful
run of the classical original-node reader at the exact same optional observation, under the
observation-level component interfaces. -/
theorem localizedDescriptorBearingRule3NodeWith?_observable_complete_core
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (obligations : input.LocalizedOriginalNodeObservableCompletionObligations
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
      have entryComputed := obligations.internalEntryComplete initial previousAxis entry
      simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed]
  | @omittedMonocycle initial closure policyResult edge route omitted =>
      have entryComputed := obligations.ringEntryComplete initial closure
        (input.ringClosureEntry_of_ordinaryMonocyclicPolicy occurrence route)
      obtain ⟨actualInitial, actualClosure, actualPolicyResult, routeComputed,
        actualOmitted⟩ :=
        obligations.omissionCategoryComplete initial closure policyResult route omitted
      exact input.localizedDescriptorBearingRule3NodeWith?_of_omittedMonocycle
        target occurrence view rule3FrameOf excluded initial closure actualInitial actualClosure
        actualPolicyResult edge entryComputed routeComputed actualOmitted
  | @excludedCyclicUnit result observation edge cyclic observationEq excludedIdentity =>
      have entryComputed := obligations.ringEntryComplete result.initial result.closure
        (input.requiredMonocyclicEZWith_ringClosureEntry
          target occurrence view Rule3FrameMeaning result cyclic)
      obtain ⟨compiled, resultComputed, obsEq⟩ :=
        obligations.cyclicObservationComplete result cyclic
      have obsIdentity :
          input.localizedRule3RequiredMonocyclicEZObservation compiled = observation :=
        obsEq.trans observationEq.symm
      simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed, resultComputed,
        obsIdentity, excludedIdentity]
  | @retainedCyclicGeometry result observation edge cyclic observationEq freshIdentity =>
      have entryComputed := obligations.ringEntryComplete result.initial result.closure
        (input.requiredMonocyclicEZWith_ringClosureEntry
          target occurrence view Rule3FrameMeaning result cyclic)
      obtain ⟨compiled, resultComputed, obsEq⟩ :=
        obligations.cyclicObservationComplete result cyclic
      have obsIdentity :
          input.localizedRule3RequiredMonocyclicEZObservation compiled = observation :=
        obsEq.trans observationEq.symm
      simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed, resultComputed,
        obsIdentity, freshIdentity]
  | @evenCumulatedAxis axis edge topology notOrdinary notPlanar =>
      have entryComputed := obligations.terminalEntryComplete axis.initial topology.1
      obtain ⟨compiledAxis, axisComputed, countEq⟩ :=
        obligations.axisDoubleBondCountComplete axis topology
      have notOrdinaryCompiled : compiledAxis.doubleBondCount ≠ 1 := by
        rw [countEq]; exact notOrdinary
      have notPlanarCompiled : ¬ Odd compiledAxis.doubleBondCount := by
        rw [countEq]; exact notPlanar
      simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed, axisComputed,
        notOrdinaryCompiled, notPlanarCompiled]
  | @excludedUnit result observation edge axis topology ordinary spatial observationEq
      excludedIdentity =>
      have entryComputed := obligations.terminalEntryComplete axis.initial topology.1
      obtain ⟨compiledAxis, axisComputed, countEq⟩ :=
        obligations.axisDoubleBondCountComplete axis topology
      have ordinaryCompiled : compiledAxis.doubleBondCount = 1 := by
        rw [countEq]; exact ordinary
      obtain ⟨compiled, resultComputed, obsEq⟩ :=
        obligations.spatialObservationComplete result spatial
      have obsIdentity : input.localizedRule3DescriptorBearingObservation compiled = observation :=
        obsEq.trans observationEq.symm
      simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed, axisComputed,
        ordinaryCompiled, resultComputed, obsIdentity, excludedIdentity]
  | @retainedGeometry result observation edge axis topology ordinary spatial observationEq
      freshIdentity =>
      have entryComputed := obligations.terminalEntryComplete axis.initial topology.1
      obtain ⟨compiledAxis, axisComputed, countEq⟩ :=
        obligations.axisDoubleBondCountComplete axis topology
      have ordinaryCompiled : compiledAxis.doubleBondCount = 1 := by
        rw [countEq]; exact ordinary
      obtain ⟨compiled, resultComputed, obsEq⟩ :=
        obligations.spatialObservationComplete result spatial
      have obsIdentity : input.localizedRule3DescriptorBearingObservation compiled = observation :=
        obsEq.trans observationEq.symm
      simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed, axisComputed,
        ordinaryCompiled, resultComputed, obsIdentity, freshIdentity]
  | @excludedBranchedUnit initial first second rest result observation edge entry spatial
      observationEq excludedIdentity =>
      obtain ⟨actualFirst, actualSecond, actualRest, entryComputed⟩ :=
        obligations.branchedEntryObservable initial first second rest entry
      obtain ⟨compiled, resultComputed, obsEq⟩ :=
        obligations.spatialObservationComplete result spatial
      have obsIdentity : input.localizedRule3DescriptorBearingObservation compiled = observation :=
        obsEq.trans observationEq.symm
      simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed, resultComputed,
        obsIdentity, excludedIdentity]
  | @retainedBranchedGeometry initial first second rest result observation edge entry spatial
      observationEq freshIdentity =>
      obtain ⟨actualFirst, actualSecond, actualRest, entryComputed⟩ :=
        obligations.branchedEntryObservable initial first second rest entry
      obtain ⟨compiled, resultComputed, obsEq⟩ :=
        obligations.spatialObservationComplete result spatial
      have obsIdentity : input.localizedRule3DescriptorBearingObservation compiled = observation :=
        obsEq.trans observationEq.symm
      simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed, resultComputed,
        obsIdentity, freshIdentity]
  | @excludedOddCumulene result observation edge odd observationEq excludedIdentity =>
      have oddTopology :
          input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame occurrence result.topology :=
        odd.1
      have cumulatedDerived :
          input.DeclarativeLocalizedRule3CumulatedEndpointCursorFrame occurrence
            (input.oddCumuleneEndpointCursorFrameToCumulated result.topology) :=
        input.declarativeOddCumuleneEndpointCursorFrame_toCumulated occurrence
          result.topology oddTopology
      have entryComputed := obligations.terminalEntryComplete result.topology.initial
        cumulatedDerived.1
      obtain ⟨compiledAxis, axisComputed, countEq⟩ :=
        obligations.axisDoubleBondCountComplete
          (input.oddCumuleneEndpointCursorFrameToCumulated result.topology) cumulatedDerived
      have countIdentity : compiledAxis.doubleBondCount = result.topology.doubleBondCount := by
        rw [countEq]; rfl
      rcases oddTopology with
        ⟨_physical, _terminal, _walk, _reversed, _rp, _r, above, oddCount⟩
      have notOrdinaryCompiled : compiledAxis.doubleBondCount ≠ 1 := by
        rw [countIdentity]; exact Nat.ne_of_gt above
      have planarCompiled : Odd compiledAxis.doubleBondCount := by
        rw [countIdentity]; exact oddCount
      obtain ⟨compiled, resultComputed, obsEq⟩ :=
        obligations.oddCumuleneObservationComplete result odd
      have obsIdentity :
          input.localizedRule3OddCumuleneDescriptorBearingObservation compiled = observation :=
        obsEq.trans observationEq.symm
      simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed, axisComputed,
        notOrdinaryCompiled, planarCompiled, resultComputed, obsIdentity, excludedIdentity]
  | @retainedOddCumulene result observation edge odd observationEq freshIdentity =>
      have oddTopology :
          input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame occurrence result.topology :=
        odd.1
      have cumulatedDerived :
          input.DeclarativeLocalizedRule3CumulatedEndpointCursorFrame occurrence
            (input.oddCumuleneEndpointCursorFrameToCumulated result.topology) :=
        input.declarativeOddCumuleneEndpointCursorFrame_toCumulated occurrence
          result.topology oddTopology
      have entryComputed := obligations.terminalEntryComplete result.topology.initial
        cumulatedDerived.1
      obtain ⟨compiledAxis, axisComputed, countEq⟩ :=
        obligations.axisDoubleBondCountComplete
          (input.oddCumuleneEndpointCursorFrameToCumulated result.topology) cumulatedDerived
      have countIdentity : compiledAxis.doubleBondCount = result.topology.doubleBondCount := by
        rw [countEq]; rfl
      rcases oddTopology with
        ⟨_physical, _terminal, _walk, _reversed, _rp, _r, above, oddCount⟩
      have notOrdinaryCompiled : compiledAxis.doubleBondCount ≠ 1 := by
        rw [countIdentity]; exact Nat.ne_of_gt above
      have planarCompiled : Odd compiledAxis.doubleBondCount := by
        rw [countIdentity]; exact oddCount
      obtain ⟨compiled, resultComputed, obsEq⟩ :=
        obligations.oddCumuleneObservationComplete result odd
      have obsIdentity :
          input.localizedRule3OddCumuleneDescriptorBearingObservation compiled = observation :=
        obsEq.trans observationEq.symm
      simp [localizedDescriptorBearingRule3NodeWith?, edge, entryComputed, axisComputed,
        notOrdinaryCompiled, planarCompiled, resultComputed, obsIdentity, freshIdentity]

/-- Executable observation-level converse: the compiled original-node reader returns the exact
optional observation of every independent derivation, under the observation-level interfaces. -/
theorem localizedDescriptorBearingRule3NodeWithExec?_observable_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (obligations : input.LocalizedOriginalNodeObservableCompletionObligations
      target occurrence view rule3FrameOf Rule3FrameMeaning)
    {observation : Option input.LocalizedRule3SpatialNodeResult}
    (derived : input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
      target view Rule3FrameMeaning excluded occurrence observation) :
    input.localizedDescriptorBearingRule3NodeWithExec?
      target occurrence view rule3FrameOf excluded = some observation := by
  rw [localizedDescriptorBearingRule3NodeWithExec?_eq_original]
  exact input.localizedDescriptorBearingRule3NodeWith?_observable_complete_core
    target occurrence view rule3FrameOf Rule3FrameMeaning excluded obligations derived

/-- Exclusion-equivalent executable converse: a derivation stated against `derivedExcluded`
transports to any membership-equivalent compiled exclusion list, and the executable reader then
returns the same optional node observation. -/
theorem localizedDescriptorBearingRule3NodeWithExec?_observable_complete_of_exclusionEquivalent
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    {derivedExcluded compiledExcluded : List input.LocalizedRule3PhysicalUnitId}
    (equivalent : LocalizedRule3ExclusionEquivalent input derivedExcluded compiledExcluded)
    (obligations : input.LocalizedOriginalNodeObservableCompletionObligations
      target occurrence view rule3FrameOf Rule3FrameMeaning)
    {observation : Option input.LocalizedRule3SpatialNodeResult}
    (derived : input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
      target view Rule3FrameMeaning derivedExcluded occurrence observation) :
    input.localizedDescriptorBearingRule3NodeWithExec?
      target occurrence view rule3FrameOf compiledExcluded = some observation := by
  have transported :=
    declarativeLocalizedDescriptorBearingRule3NodeWith_exclusion_transport
      input target view Rule3FrameMeaning equivalent occurrence derived
  exact input.localizedDescriptorBearingRule3NodeWithExec?_observable_complete
    target occurrence view rule3FrameOf Rule3FrameMeaning compiledExcluded obligations transported









def LocalizedOriginalNodeObservableCompleteAt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel) : Prop :=
  ∀ (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (excluded compiledExcluded : List input.LocalizedRule3PhysicalUnitId),
    LocalizedRule3ExclusionEquivalent input excluded compiledExcluded →
    ∀ observation : Option input.LocalizedRule3SpatialNodeResult,
      input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
        target view Rule3FrameMeaning excluded occurrence observation →
      input.localizedDescriptorBearingRule3NodeWithExec?
        target occurrence view rule3FrameOf compiledExcluded = some observation

/-- Per-occurrence observation-level obligations close the original `NodeCompleteAt` interface. -/
theorem localizedOriginalNodeObservableCompleteAt_of_obligations
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (obligations : ∀ occurrence,
      input.LocalizedOriginalNodeObservableCompletionObligations
        target occurrence view rule3FrameOf Rule3FrameMeaning) :
    input.LocalizedOriginalNodeObservableCompleteAt target view rule3FrameOf Rule3FrameMeaning := by
  intro occurrence excluded compiledExcluded equivalent observation derived
  exact input.localizedDescriptorBearingRule3NodeWithExec?_observable_complete_of_exclusionEquivalent
    target occurrence view rule3FrameOf Rule3FrameMeaning equivalent
    (obligations occurrence) derived

/-- Specialization of the original `NodeCompleteAt` interface to the executable predecessor-frame
builder and its original declarative frame meaning. These are the callback and meaning used by
`localizedDescriptorBearingRule3NodeExec?`, not the extended frame definitions appearing in
`LocalizedRule3ExtendedShortCircuitNodeCompleteAt`. Extended integration must instantiate the
preceding generic theorem with the actual extended callback and its component obligations. -/
theorem localizedOriginalNodeObservableCompleteAt_frameExec_of_obligations
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (frameFuel : Nat)
    (obligations : ∀ occurrence,
      input.LocalizedOriginalNodeObservableCompletionObligations
        target occurrence view
        (input.buildLocalizedDescriptorBearingRule3FrameExec? target view frameFuel)
        (input.DeclarativeLocalizedDescriptorBearingRule3Frame target view frameFuel)) :
    input.LocalizedOriginalNodeObservableCompleteAt target view
      (input.buildLocalizedDescriptorBearingRule3FrameExec? target view frameFuel)
      (input.DeclarativeLocalizedDescriptorBearingRule3Frame target view frameFuel) :=
  input.localizedOriginalNodeObservableCompleteAt_of_obligations
    target view _ _ obligations

/-! ## Integration with the short-circuit and extended node evaluators

The preservation theorems of `LocalizedRule3ShortNodePreservation` and
`LocalizedRule3ExtendedNodePreservation` convert a successful run of the classical original reader
into a successful run of the short-circuit (respectively extended) evaluator at the *same*
callback and exclusion list, with the same observation. Composing them with the observation-level
converse above yields the original-constructor component of those evaluators.

These theorems are intentionally conditional on the observation-level obligations and are only
stated for original declarative derivations. The independent `.ordinary` and `.odd` constructors
of the short-circuit/extended node relations, and the passage from the declarative predecessor
frame callback to the executable one, are not claimed here. -/

/-- Original derivations reach the short-circuit evaluator at the same observation, for the
classical predecessor-frame callback. -/
theorem localizedRule3ShortCircuitNodeWithExec?_observable_complete_of_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (budget : Nat)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (obligations : input.LocalizedOriginalNodeObservableCompletionObligations
      target occurrence view
      (input.buildLocalizedDescriptorBearingRule3Frame? target view budget)
      (input.DeclarativeLocalizedDescriptorBearingRule3Frame target view budget))
    {observation : Option input.LocalizedRule3SpatialNodeResult}
    (derived : input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
      target view
      (input.DeclarativeLocalizedDescriptorBearingRule3Frame target view budget)
      excluded occurrence observation) :
    input.localizedRule3ShortCircuitNodeWithExec?
      target occurrence view
      (input.buildLocalizedDescriptorBearingRule3Frame? target view budget) excluded =
        some observation :=
  input.shortNode_preserves_original_callback target occurrence view budget excluded observation
    (input.localizedDescriptorBearingRule3NodeWith?_observable_complete_core
      target occurrence view
      (input.buildLocalizedDescriptorBearingRule3Frame? target view budget)
      (input.DeclarativeLocalizedDescriptorBearingRule3Frame target view budget)
      excluded obligations derived)

/-- Original derivations reach the extended short-circuit evaluator at the same observation, for
the classical predecessor-frame callback. -/
theorem localizedRule3ExtendedShortCircuitNodeWithExec?_observable_complete_of_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (budget : Nat)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (obligations : input.LocalizedOriginalNodeObservableCompletionObligations
      target occurrence view
      (input.buildLocalizedDescriptorBearingRule3Frame? target view budget)
      (input.DeclarativeLocalizedDescriptorBearingRule3Frame target view budget))
    {observation : Option input.LocalizedRule3SpatialNodeResult}
    (derived : input.DeclarativeLocalizedDescriptorBearingRule3NodeWith
      target view
      (input.DeclarativeLocalizedDescriptorBearingRule3Frame target view budget)
      excluded occurrence observation) :
    input.localizedRule3ExtendedShortCircuitNodeWithExec?
      target occurrence view
      (input.buildLocalizedDescriptorBearingRule3Frame? target view budget) excluded =
        some observation :=
  input.extendedShortNode_preserves_original_callback
    target occurrence view budget excluded observation
    (input.localizedDescriptorBearingRule3NodeWith?_observable_complete_core
      target occurrence view
      (input.buildLocalizedDescriptorBearingRule3Frame? target view budget)
      (input.DeclarativeLocalizedDescriptorBearingRule3Frame target view budget)
      excluded obligations derived)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
