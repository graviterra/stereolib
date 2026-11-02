import TetraStereo.OneCenter.LocalizedOddCumulenePerceptionCompleteness
import TetraStereo.OneCenter.LocalizedEvenCumuleneAxialAssignmentCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Conditional assignment completeness for planar odd cumulenes

The occurrence carrier, maximal open-chain perception, odd parity, terminal orientation, and
finite traversal bound are already unconditional.  This module discharges the remaining
production endpoint construction for the family-neutral maximal-chain carrier and then proves
existence of the final P-93.4.2.3 `E/Z` assignment from explicit chemical dependency and exact
spatial evidence.
-/

namespace CertifiedLocalizedCIPInput

/-- Parity-neutral name for the production endpoint-resolution package shared by planar odd and
axial even cumulenes. -/
abbrev LocalizedCumulatedProductionEndpointResolved
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel) : Prop :=
  input.LocalizedEvenCumuleneProductionEndpointResolved
    target view endpoint partner endpointCursor

/-- Parity-neutral name for finite support of all reachable descriptor-bearing Rule-3
dependencies. -/
abbrev LocalizedCumulatedProductionEndpointDependenciesResolved
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) : Prop :=
  input.LocalizedEvenCumuleneProductionEndpointDependenciesResolved target view

/-- At the initial terminal of any exact maximal open chain, two explicit substituents and
finite reachable dependency support construct the complete production endpoint frame. -/
theorem exists_productionEndpointResolved_axialRootInitialLeft
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (axialRoot : input.LocalizedAxialRoot)
    (first second : input.Atom)
    (candidates : input.localizedRule3ExplicitSubstituents
      axialRoot.1.terminal axialRoot.1.firstAxis = [first, second])
    (dependencies : input.LocalizedCumulatedProductionEndpointDependenciesResolved
      target view) :
    input.LocalizedCumulatedProductionEndpointResolved target view
      axialRoot.1.terminal axialRoot.1.firstAxis
      (input.localizedAxialRootInitialPhysicalEndpointCursorFrame
        carrierFuel axialRoot).leftCursor := by
  have firstPresent : first ∈ input.localizedRule3ExplicitSubstituents
      axialRoot.1.terminal axialRoot.1.firstAxis := by simp [candidates]
  have secondPresent : second ∈ input.localizedRule3ExplicitSubstituents
      axialRoot.1.terminal axialRoot.1.firstAxis := by simp [candidates]
  obtain ⟨firstCursor, firstCanonical⟩ :=
    input.exists_canonicalRule3ReferenceCursor_axialRootInitialLeft
      carrierFuel axialRoot first firstPresent
  obtain ⟨secondCursor, secondCanonical⟩ :=
    input.exists_canonicalRule3ReferenceCursor_axialRootInitialLeft
      carrierFuel axialRoot second secondPresent
  have resolved :=
    LocalizedDescriptorBearingRule3ReachableSupportThrough.resolved
      input target view dependencies
  exact ⟨first, second, firstCursor, secondCursor, candidates,
    firstCanonical, secondCanonical, resolved⟩

/-- The concrete endpoint callback is total from the parity-neutral endpoint-resolution
package. -/
theorem exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_cumulated_resolved
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (resolved : input.LocalizedCumulatedProductionEndpointResolved
      target view endpoint partner endpointCursor) :
    ∃ frame,
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
          target view
          (input.buildLocalizedDescriptorBearingRule3Frame? target view
            (localizedDescriptorBearingRule3EvaluationFuel carrierFuel))
          endpoint partner endpointCursor = some frame := by
  simpa [localizedEvenCumuleneAxialRule3EvaluationFuel,
    localizedDescriptorBearingRule3EvaluationFuel] using
    input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_production_resolved
      target view endpoint partner endpointCursor resolved

/-- Exact remaining spatial applicability for two completely compiled terminal frames.  The
predicate is stated only in independent endpoint-key, rational-geometry, and P-93 relations; it
does not assume that the production spatial evaluator succeeds. -/
def LocalizedOddCumuleneProductionSpatialEvidence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (leftCompilation rightCompilation :
      input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel) : Prop :=
  ∃ unit terminalGeometry descriptor,
    input.DeclarativeLocalizedRule3ExtendedDescriptorBearingSpatialUnit
      topology.initial.left topology.initial.right
      topology.rightPartner topology.right
      leftCompilation.endpointFrame rightCompilation.endpointFrame
      (fun reference key => ∃ cursor,
        input.DeclarativeLocalizedRule3ReferenceCursor
          topology.initial.leftCursor cursor reference ∧
        ((cursor = leftCompilation.firstCursor ∧
            key = leftCompilation.endpointFrame.firstKey) ∨
         (cursor = leftCompilation.secondCursor ∧
            key = leftCompilation.endpointFrame.secondKey)))
      (fun reference key => ∃ cursor,
        input.DeclarativeLocalizedRule3ReferenceCursor
          topology.rightCursor cursor reference ∧
        ((cursor = rightCompilation.firstCursor ∧
            key = rightCompilation.endpointFrame.firstKey) ∨
         (cursor = rightCompilation.secondCursor ∧
            key = rightCompilation.endpointFrame.secondKey)))
      unit ∧
    Rule3GeometryRefinesOddCumuleneTerminalGeometry unit.geometry terminalGeometry ∧
    BlueBookP93.Acyclic.OddCumuleneEZAssignment terminalGeometry descriptor

/-- Once topology and both complete endpoint frames are fixed, construction of the retained
descriptor-bearing source is exactly the independent extended-unit spatial semantics. -/
theorem localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?_eq_some_iff_of_compilations
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (leftCompilation rightCompilation :
      input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (unit : input.LocalizedRule3DescriptorBearingSpatialUnitResult)
    (topologyComputed : input.localizedRule3OddCumuleneEndpointCursorFrame?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence = some topology)
    (leftComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
      target view rule3FrameOf topology.initial.left topology.initial.right
        topology.initial.leftCursor = some leftCompilation)
    (rightComputed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
      target view rule3FrameOf topology.right topology.rightPartner
        topology.rightCursor = some rightCompilation)
    (leftValid : input.DeclarativeLocalizedRule3EndpointKeyFrame
      topology.initial.left topology.initial.right
      (fun reference key => ∃ cursor,
        input.DeclarativeLocalizedRule3ReferenceCursor
          topology.initial.leftCursor cursor reference ∧
        ((cursor = leftCompilation.firstCursor ∧
            key = leftCompilation.endpointFrame.firstKey) ∨
         (cursor = leftCompilation.secondCursor ∧
            key = leftCompilation.endpointFrame.secondKey)))
      leftCompilation.endpointFrame)
    (rightValid : input.DeclarativeLocalizedRule3EndpointKeyFrame
      topology.right topology.rightPartner
      (fun reference key => ∃ cursor,
        input.DeclarativeLocalizedRule3ReferenceCursor
          topology.rightCursor cursor reference ∧
        ((cursor = rightCompilation.firstCursor ∧
            key = rightCompilation.endpointFrame.firstKey) ∨
         (cursor = rightCompilation.secondCursor ∧
            key = rightCompilation.endpointFrame.secondKey)))
      rightCompilation.endpointFrame) :
    input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
        target occurrence view rule3FrameOf =
      some { topology, leftCompilation, rightCompilation, unit } ↔
    input.DeclarativeLocalizedRule3ExtendedDescriptorBearingSpatialUnit
      topology.initial.left topology.initial.right topology.rightPartner topology.right
      leftCompilation.endpointFrame rightCompilation.endpointFrame
      (fun reference key => ∃ cursor,
        input.DeclarativeLocalizedRule3ReferenceCursor
          topology.initial.leftCursor cursor reference ∧
        ((cursor = leftCompilation.firstCursor ∧
            key = leftCompilation.endpointFrame.firstKey) ∨
         (cursor = leftCompilation.secondCursor ∧
            key = leftCompilation.endpointFrame.secondKey)))
      (fun reference key => ∃ cursor,
        input.DeclarativeLocalizedRule3ReferenceCursor
          topology.rightCursor cursor reference ∧
        ((cursor = rightCompilation.firstCursor ∧
            key = rightCompilation.endpointFrame.firstKey) ∨
         (cursor = rightCompilation.secondCursor ∧
            key = rightCompilation.endpointFrame.secondKey)))
      unit := by
  have exactUnit :=
    input.localizedRule3ExtendedDescriptorBearingSpatialUnit?_eq_some_iff
      topology.initial.left topology.initial.right topology.rightPartner topology.right
      leftCompilation.endpointFrame rightCompilation.endpointFrame _ _
      leftValid rightValid unit
  cases unitComputed : input.localizedRule3ExtendedDescriptorBearingSpatialUnit?
      topology.initial.left topology.right leftCompilation.endpointFrame
        rightCompilation.endpointFrame <;>
    simpa [localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?,
      topologyComputed, leftComputed, rightComputed, unitComputed] using exactUnit

/-- Once the complete descriptor-bearing source is fixed, final odd-cumulene emission is exactly
the independent P-93.4.2.3 terminal-geometry assignment. -/
theorem localizedRule3OddCumuleneEZWith?_eq_some_iff_of_source
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (source : input.LocalizedRule3OddCumuleneDescriptorBearingSpatialResult carrierFuel)
    (descriptor : BlueBookP93.Acyclic.Descriptor)
    (sourceComputed :
      input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
        target occurrence view rule3FrameOf = some source) :
    input.localizedRule3OddCumuleneEZWith? target occurrence view rule3FrameOf =
        some { source, descriptor } ↔
      ∃ terminalGeometry,
        Rule3GeometryRefinesOddCumuleneTerminalGeometry
          source.unit.geometry terminalGeometry ∧
        BlueBookP93.Acyclic.OddCumuleneEZAssignment terminalGeometry descriptor := by
  have exactDescriptor := oddCumuleneEZDescriptorOfRule3?_eq_some_iff
    source.unit.geometry descriptor
  cases descriptorComputed : oddCumuleneEZDescriptorOfRule3? source.unit.geometry <;>
    simpa [localizedRule3OddCumuleneEZWith?, sourceComputed,
      descriptorComputed] using exactDescriptor

/-- Concrete chemical applicability after all carrier construction has been discharged.  It asks
only for exactly two explicit substituents at each terminal and explicit finite support for every
reachable descriptor-bearing dependency. -/
def LocalizedOddCumuleneProductionDependencyEvidence
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedOddCumuleneChain)
    (view : input.LocalizedDependencyView
      (input.localizedAxialRootOccurrence
        input.certified.input.molecule.atomCount
        (input.localizedOddCumuleneAxialRoot axis))) : Prop :=
  ∀ (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame
      input.certified.input.molecule.atomCount)
    (embedding : input.LocalizedAxialOccurrencePathEmbedding
      input.certified.input.molecule.atomCount
      (input.localizedAxialRootOccurrence
        input.certified.input.molecule.atomCount
        (input.localizedOddCumuleneAxialRoot axis))
      (input.localizedAxialRootFirstChildOccurrence
        input.certified.input.molecule.atomCount
        (input.localizedOddCumuleneAxialRoot axis))
      axis.1.path.tail),
    topology.initial = input.localizedAxialRootInitialPhysicalEndpointCursorFrame
        input.certified.input.molecule.atomCount
        (input.localizedOddCumuleneAxialRoot axis) →
    topology.rightward = embedding.cursors →
    topology.rightCursor ∈ embedding.cursors →
    topology.rightPartnerCursor ∈ embedding.cursors →
    topology.rightCursor.previous? = some topology.rightPartnerCursor.occurrence →
    ∃ leftFirst leftSecond rightFirst rightSecond,
      input.localizedRule3ExplicitSubstituents
          topology.initial.left topology.initial.right = [leftFirst, leftSecond] ∧
      input.localizedRule3ExplicitSubstituents
          topology.right topology.rightPartner = [rightFirst, rightSecond] ∧
      input.LocalizedCumulatedProductionEndpointDependenciesResolved
        (input.localizedAxialRootOccurrence
          input.certified.input.molecule.atomCount
          (input.localizedOddCumuleneAxialRoot axis)) view

/-- Independent strict terminal-priority and geometry evidence for whichever canonical topology
and complete endpoint frames the deterministic production construction returns. -/
def LocalizedOddCumuleneProductionSpatialEvidenceAtAtomCount
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedOddCumuleneChain)
    (view : input.LocalizedDependencyView
      (input.localizedAxialRootOccurrence
        input.certified.input.molecule.atomCount
        (input.localizedOddCumuleneAxialRoot axis))) : Prop :=
  ∀ (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame
      input.certified.input.molecule.atomCount)
    (leftCompilation rightCompilation : input.LocalizedRule3OccurrenceEndpointKeyFrame
      input.certified.input.molecule.atomCount),
    input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame
        (input.localizedAxialRootFirstChildOccurrence
          input.certified.input.molecule.atomCount
          (input.localizedOddCumuleneAxialRoot axis)) topology →
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        (input.localizedAxialRootOccurrence
          input.certified.input.molecule.atomCount
          (input.localizedOddCumuleneAxialRoot axis))
        view
        (input.buildLocalizedDescriptorBearingRule3Frame?
          (input.localizedAxialRootOccurrence
            input.certified.input.molecule.atomCount
            (input.localizedOddCumuleneAxialRoot axis))
          view (localizedDescriptorBearingRule3EvaluationFuel
            input.certified.input.molecule.atomCount))
        topology.initial.left topology.initial.right topology.initial.leftCursor =
      some leftCompilation →
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        (input.localizedAxialRootOccurrence
          input.certified.input.molecule.atomCount
          (input.localizedOddCumuleneAxialRoot axis))
        view
        (input.buildLocalizedDescriptorBearingRule3Frame?
          (input.localizedAxialRootOccurrence
            input.certified.input.molecule.atomCount
            (input.localizedOddCumuleneAxialRoot axis))
          view (localizedDescriptorBearingRule3EvaluationFuel
            input.certified.input.molecule.atomCount))
        topology.right topology.rightPartner topology.rightCursor =
      some rightCompilation →
    input.LocalizedOddCumuleneProductionSpatialEvidence
      topology leftCompilation rightCompilation

/-- Every perceived canonical open odd cumulene emits its occurrence-local P-93.4.2.3 `E/Z`
result at atom-count depth once the remaining explicit dependency support and independent strict
terminal geometry are present.  No topology, path, parity, reference-cursor, or traversal-fuel
premise remains. -/
theorem exists_localizedRule3OddCumuleneEZ_of_evidence_at_atomCount
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedOddCumuleneChain)
    (view : input.LocalizedDependencyView
      (input.localizedAxialRootOccurrence
        input.certified.input.molecule.atomCount
        (input.localizedOddCumuleneAxialRoot axis)))
    (dependencyEvidence :
      input.LocalizedOddCumuleneProductionDependencyEvidence axis view)
    (spatialEvidence :
      input.LocalizedOddCumuleneProductionSpatialEvidenceAtAtomCount axis view) :
    ∃ result,
      input.localizedRule3OddCumuleneEZWith?
          (input.localizedAxialRootOccurrence
            input.certified.input.molecule.atomCount
            (input.localizedOddCumuleneAxialRoot axis))
          (input.localizedAxialRootFirstChildOccurrence
            input.certified.input.molecule.atomCount
            (input.localizedOddCumuleneAxialRoot axis))
          view
          (input.buildLocalizedDescriptorBearingRule3Frame?
            (input.localizedAxialRootOccurrence
              input.certified.input.molecule.atomCount
              (input.localizedOddCumuleneAxialRoot axis))
            view (localizedDescriptorBearingRule3EvaluationFuel
              input.certified.input.molecule.atomCount)) = some result ∧
        input.DeclarativeLocalizedRule3OddCumuleneEZWith
          (input.localizedAxialRootOccurrence
            input.certified.input.molecule.atomCount
            (input.localizedOddCumuleneAxialRoot axis))
          (input.localizedAxialRootFirstChildOccurrence
            input.certified.input.molecule.atomCount
            (input.localizedOddCumuleneAxialRoot axis))
          view
          (input.DeclarativeLocalizedDescriptorBearingRule3Frame
            (input.localizedAxialRootOccurrence
              input.certified.input.molecule.atomCount
              (input.localizedOddCumuleneAxialRoot axis))
            view (localizedDescriptorBearingRule3EvaluationFuel
              input.certified.input.molecule.atomCount)) result := by
  unfold LocalizedOddCumuleneProductionSpatialEvidenceAtAtomCount at spatialEvidence
  let carrierFuel := input.certified.input.molecule.atomCount
  let axialRoot := input.localizedOddCumuleneAxialRoot axis
  let target := input.localizedAxialRootOccurrence carrierFuel axialRoot
  let occurrence := input.localizedAxialRootFirstChildOccurrence carrierFuel axialRoot
  let frameOf := input.buildLocalizedDescriptorBearingRule3Frame?
    target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)
  let frameMeaning := input.DeclarativeLocalizedDescriptorBearingRule3Frame
    target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)
  obtain ⟨topology, embedding, topologyComputed, topologyDerived, initial,
      rightward, rightPresent, rightPartnerPresent, rightPrevious⟩ :=
    input.exists_localizedRule3OddCumuleneEndpointCursorFrameWithEmbedding_at_atomCount axis
  obtain ⟨leftFirst, leftSecond, rightFirst, rightSecond,
      leftCandidates, rightCandidates, dependencies⟩ :=
    dependencyEvidence topology embedding initial rightward rightPresent
      rightPartnerPresent rightPrevious
  have leftResolvedCanonical :=
    input.exists_productionEndpointResolved_axialRootInitialLeft
      target view axialRoot leftFirst leftSecond (by simpa [initial] using leftCandidates)
      dependencies
  have leftResolved : input.LocalizedCumulatedProductionEndpointResolved
      target view topology.initial.left topology.initial.right
        topology.initial.leftCursor := by
    simpa [initial] using leftResolvedCanonical
  rcases topologyDerived with ⟨physical, leftTerminal, walk, reversed,
    rightPartnerCurrent, rightCurrent, lengthLower, oddLength⟩
  have rightResolved := embedding.exists_productionEndpointResolved input
    target view topology.rightCursor topology.rightPartnerCursor
    topology.right topology.rightPartner rightFirst rightSecond rightPresent
    rightPrevious rightCurrent rightPartnerCurrent rightCandidates dependencies
  obtain ⟨leftCompilation, leftComputed⟩ :=
    input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_cumulated_resolved
      target view topology.initial.left topology.initial.right
      topology.initial.leftCursor leftResolved
  obtain ⟨rightCompilation, rightComputed⟩ :=
    input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_cumulated_resolved
      target view topology.right topology.rightPartner topology.rightCursor rightResolved
  have frameSound : ∀ cursors frame,
      frameOf cursors = some frame → frameMeaning cursors frame := by
    intro cursors frame computed
    exact input.buildLocalizedDescriptorBearingRule3Frame?_sound
      target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)
      cursors frame computed
  have leftDerived :=
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_sound
      target view frameOf frameMeaning frameSound topology.initial.left
      topology.initial.right topology.initial.leftCursor leftCompilation leftComputed
  have rightDerived :=
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_sound
      target view frameOf frameMeaning frameSound topology.right
      topology.rightPartner topology.rightCursor rightCompilation rightComputed
  have leftValid :=
    DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith.endpointFrame
      input target view frameMeaning topology.initial.left topology.initial.right
      topology.initial.leftCursor leftCompilation leftDerived
  have rightValid :=
    DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith.endpointFrame
      input target view frameMeaning topology.right topology.rightPartner
      topology.rightCursor rightCompilation rightDerived
  obtain ⟨unit, terminalGeometry, descriptor, unitDerived, refines, assigned⟩ :=
    spatialEvidence topology leftCompilation rightCompilation
      ⟨physical, leftTerminal, walk, reversed, rightPartnerCurrent, rightCurrent,
        lengthLower, oddLength⟩ leftComputed rightComputed
  have unitComputed :=
    (input.localizedRule3ExtendedDescriptorBearingSpatialUnit?_eq_some_iff
      topology.initial.left topology.initial.right topology.rightPartner topology.right
      leftCompilation.endpointFrame rightCompilation.endpointFrame _ _
      leftValid rightValid unit).mpr unitDerived
  have descriptorComputed :=
    (oddCumuleneEZDescriptorOfRule3?_eq_some_iff unit.geometry descriptor).mpr
      ⟨terminalGeometry, refines, assigned⟩
  let source : input.LocalizedRule3OddCumuleneDescriptorBearingSpatialResult carrierFuel :=
    { topology, leftCompilation, rightCompilation, unit }
  let result : input.LocalizedRule3OddCumuleneEZResult carrierFuel :=
    { source, descriptor }
  have topologyComputed' :
      input.localizedRule3OddCumuleneEndpointCursorFrame?
        (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence =
          some topology := by
    simpa [carrierFuel, axialRoot, occurrence] using topologyComputed
  have leftComputed' :
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        target view frameOf topology.initial.left topology.initial.right
          topology.initial.leftCursor = some leftCompilation := by
    simpa [frameOf] using leftComputed
  have rightComputed' :
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        target view frameOf topology.right topology.rightPartner
          topology.rightCursor = some rightCompilation := by
    simpa [frameOf] using rightComputed
  have sourceComputed :
      input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
        target occurrence view frameOf = some source := by
    simp [localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?,
      topologyComputed', leftComputed', rightComputed', unitComputed, source]
  have descriptorComputed' :
      oddCumuleneEZDescriptorOfRule3? source.unit.geometry = some descriptor := by
    simpa [source] using descriptorComputed
  have resultComputed : input.localizedRule3OddCumuleneEZWith?
      target occurrence view frameOf = some result := by
    simp [localizedRule3OddCumuleneEZWith?, sourceComputed,
      descriptorComputed', result]
  refine ⟨result, ?_, ?_⟩
  · simpa [carrierFuel, axialRoot, target, occurrence, frameOf] using resultComputed
  · simpa [carrierFuel, axialRoot, target, occurrence, frameOf, frameMeaning] using
      input.localizedRule3OddCumuleneEZWith?_sound
        target occurrence view frameOf frameMeaning frameSound result resultComputed

/-- Chemically meaningful readiness of one perceived odd cumulene in a supplied complete
auxiliary state.  Structural carrier facts and fuel are absent: readiness consists precisely of
endpoint constitution/dependency support and strict independently stated terminal geometry. -/
def LocalizedOddCumuleneEZProductionReadyAtAtomCount
    (input : CertifiedLocalizedCIPInput)
    (state : input.LocalizedAuxiliaryState input.certified.input.molecule.atomCount)
    (axis : input.LocalizedOddCumuleneChain) : Prop :=
  let target := input.localizedAxialRootOccurrence
    input.certified.input.molecule.atomCount
    (input.localizedOddCumuleneAxialRoot axis)
  let view := input.localizedDependencyView state target
  input.LocalizedOddCumuleneProductionDependencyEvidence axis view ∧
    input.LocalizedOddCumuleneProductionSpatialEvidenceAtAtomCount axis view

/-- Exact executable-source readiness for one odd-cumulene assignment.  The earlier source
compiler has resolved topology and both complete endpoint frames; the remaining condition is only
the independent P-93 terminal-geometry relation.  This deliberately differs from
`LocalizedOddCumuleneEZProductionReadyAtAtomCount`, which is an upstream, computation-free
sufficient chemical package. -/
def LocalizedOddCumuleneEZExecutableSourceReadyAtWithState
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (axis : input.LocalizedOddCumuleneChain) : Prop :=
  let axialRoot := input.localizedOddCumuleneAxialRoot axis
  let target := input.localizedAxialRootOccurrence fuel axialRoot
  let occurrence := input.localizedAxialRootFirstChildOccurrence fuel axialRoot
  let view := input.localizedDependencyView state target
  let frameOf := input.buildLocalizedDescriptorBearingRule3Frame?
    target view (localizedDescriptorBearingRule3EvaluationFuel fuel)
  ∃ source, input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
      target occurrence view frameOf = some source ∧
    ∃ terminalGeometry descriptor,
      Rule3GeometryRefinesOddCumuleneTerminalGeometry
        source.unit.geometry terminalGeometry ∧
      BlueBookP93.Acyclic.OddCumuleneEZAssignment terminalGeometry descriptor

/-- Executable-source readiness is exactly existence of a public one-axis assignment.  This is
the exact readiness biconditional; its P-93 half is independent, while the resolved-source half is
kept distinct from the stronger upstream chemical support package. -/
theorem localizedOddCumuleneEZExecutableSourceReadyAtWithState_iff_exists_assignment
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (axis : input.LocalizedOddCumuleneChain) :
    input.LocalizedOddCumuleneEZExecutableSourceReadyAtWithState fuel state axis ↔
      ∃ assignment, input.localizedOddCumuleneEZSpatialAssignmentAtWithState?
        fuel state axis = some assignment := by
  let axialRoot := input.localizedOddCumuleneAxialRoot axis
  let target := input.localizedAxialRootOccurrence fuel axialRoot
  let occurrence := input.localizedAxialRootFirstChildOccurrence fuel axialRoot
  let view := input.localizedDependencyView state target
  let frameOf := input.buildLocalizedDescriptorBearingRule3Frame?
    target view (localizedDescriptorBearingRule3EvaluationFuel fuel)
  change (∃ source,
      input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
          target occurrence view frameOf = some source ∧
        ∃ terminalGeometry descriptor,
          Rule3GeometryRefinesOddCumuleneTerminalGeometry
            source.unit.geometry terminalGeometry ∧
          BlueBookP93.Acyclic.OddCumuleneEZAssignment terminalGeometry descriptor) ↔
    ∃ assignment, input.localizedOddCumuleneEZSpatialAssignmentAtWithState?
      fuel state axis = some assignment
  constructor
  · rintro ⟨source, sourceComputed, terminalGeometry, descriptor,
      refines, assigned⟩
    have descriptorComputed :=
      (oddCumuleneEZDescriptorOfRule3?_eq_some_iff source.unit.geometry descriptor).mpr
        ⟨terminalGeometry, refines, assigned⟩
    let result : input.LocalizedRule3OddCumuleneEZResult fuel := { source, descriptor }
    have resultComputed : input.localizedRule3OddCumuleneEZWith?
        target occurrence view frameOf = some result := by
      simp [localizedRule3OddCumuleneEZWith?, sourceComputed,
        descriptorComputed, result]
    let assignment : input.LocalizedOddCumuleneEZSpatialAssignment fuel :=
      { axis, result }
    have resultComputed' : input.localizedRule3OddCumuleneEZWith?
        (input.localizedAxialRootOccurrence fuel
          (input.localizedOddCumuleneAxialRoot axis))
        (input.localizedAxialRootFirstChildOccurrence fuel
          (input.localizedOddCumuleneAxialRoot axis))
        (input.localizedDependencyView state
          (input.localizedAxialRootOccurrence fuel
            (input.localizedOddCumuleneAxialRoot axis)))
        (input.buildLocalizedDescriptorBearingRule3Frame?
          (input.localizedAxialRootOccurrence fuel
            (input.localizedOddCumuleneAxialRoot axis))
          (input.localizedDependencyView state
            (input.localizedAxialRootOccurrence fuel
              (input.localizedOddCumuleneAxialRoot axis)))
          (localizedDescriptorBearingRule3EvaluationFuel fuel)) = some result := by
      simpa [axialRoot, target, occurrence, view, frameOf] using resultComputed
    have assignmentComputed :
        input.localizedOddCumuleneEZSpatialAssignmentAtWithState?
          fuel state axis = some assignment := by
      simp [localizedOddCumuleneEZSpatialAssignmentAtWithState?,
        resultComputed', assignment]
    exact ⟨assignment, assignmentComputed⟩
  · rintro ⟨assignment, assignmentComputed⟩
    unfold localizedOddCumuleneEZSpatialAssignmentAtWithState? at assignmentComputed
    dsimp only at assignmentComputed
    cases resultComputed : input.localizedRule3OddCumuleneEZWith?
        target occurrence view frameOf with
    | none =>
        simp [axialRoot, target, occurrence, view, frameOf,
          resultComputed] at assignmentComputed
    | some result =>
        simp [axialRoot, target, occurrence, view, frameOf,
          resultComputed] at assignmentComputed
        subst assignment
        have sourceComputed :=
          input.localizedRule3OddCumuleneEZWith?_source
            target occurrence view frameOf result resultComputed
        let frameMeaning := input.DeclarativeLocalizedDescriptorBearingRule3Frame
          target view (localizedDescriptorBearingRule3EvaluationFuel fuel)
        have frameSound : ∀ cursors frame,
            frameOf cursors = some frame → frameMeaning cursors frame := by
          intro cursors frame computed
          exact input.buildLocalizedDescriptorBearingRule3Frame?_sound
            target view (localizedDescriptorBearingRule3EvaluationFuel fuel)
            cursors frame computed
        have finalDerived := input.localizedRule3OddCumuleneEZWith?_sound
          target occurrence view frameOf frameMeaning frameSound result resultComputed
        rcases finalDerived.2 with
          ⟨terminalGeometry, refines, assigned, _recommended⟩
        exact ⟨result.source, sourceComputed, terminalGeometry,
          result.descriptor, refines, assigned⟩

/-- Exact fail-closed boundary: one-axis refusal occurs precisely when executable-source
readiness is absent. -/
theorem localizedOddCumuleneEZSpatialAssignmentAtWithState?_eq_none_iff_not_executableSourceReady
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (axis : input.LocalizedOddCumuleneChain) :
    input.localizedOddCumuleneEZSpatialAssignmentAtWithState?
        fuel state axis = none ↔
      ¬ input.LocalizedOddCumuleneEZExecutableSourceReadyAtWithState fuel state axis := by
  constructor
  · intro computed ready
    obtain ⟨assignment, successful⟩ :=
      (input.localizedOddCumuleneEZExecutableSourceReadyAtWithState_iff_exists_assignment
        fuel state axis).mp ready
    rw [computed] at successful
    contradiction
  · intro notReady
    cases computed : input.localizedOddCumuleneEZSpatialAssignmentAtWithState?
        fuel state axis with
    | none => rfl
    | some assignment =>
        exfalso
        apply notReady
        exact
          (input.localizedOddCumuleneEZExecutableSourceReadyAtWithState_iff_exists_assignment
            fuel state axis).mpr ⟨assignment, computed⟩

/-- Readiness constructs an actual one-axis public assignment and its complete independent
meaning at the canonical atom-count carrier depth. -/
theorem exists_localizedOddCumuleneEZSpatialAssignmentAtWithState?_of_ready_at_atomCount
    (input : CertifiedLocalizedCIPInput)
    (state : input.LocalizedAuxiliaryState input.certified.input.molecule.atomCount)
    (axis : input.LocalizedOddCumuleneChain)
    (ready : input.LocalizedOddCumuleneEZProductionReadyAtAtomCount state axis) :
    ∃ assignment,
      input.localizedOddCumuleneEZSpatialAssignmentAtWithState?
          input.certified.input.molecule.atomCount state axis = some assignment ∧
        input.DeclarativeLocalizedOddCumuleneEZSpatialAssignmentWithState
          input.certified.input.molecule.atomCount state assignment := by
  let carrierFuel := input.certified.input.molecule.atomCount
  let axialRoot := input.localizedOddCumuleneAxialRoot axis
  let target := input.localizedAxialRootOccurrence carrierFuel axialRoot
  let occurrence := input.localizedAxialRootFirstChildOccurrence carrierFuel axialRoot
  let view := input.localizedDependencyView state target
  change input.LocalizedOddCumuleneProductionDependencyEvidence axis view ∧
      input.LocalizedOddCumuleneProductionSpatialEvidenceAtAtomCount axis view at ready
  obtain ⟨dependencies, spatial⟩ := ready
  obtain ⟨result, resultComputed, _resultDerived⟩ :=
    input.exists_localizedRule3OddCumuleneEZ_of_evidence_at_atomCount
      axis view dependencies spatial
  let assignment : input.LocalizedOddCumuleneEZSpatialAssignment carrierFuel :=
    { axis, result }
  have assignmentComputed :
      input.localizedOddCumuleneEZSpatialAssignmentAtWithState?
        carrierFuel state axis = some assignment := by
    simp [localizedOddCumuleneEZSpatialAssignmentAtWithState?,
      carrierFuel, axialRoot, target, view, resultComputed, assignment]
  refine ⟨assignment, ?_, ?_⟩
  · simpa [carrierFuel] using assignmentComputed
  · simpa [carrierFuel] using
      input.localizedOddCumuleneEZSpatialAssignmentAtWithState?_sound
        carrierFuel state axis assignment assignmentComputed

/-- The upstream independent production-readiness package entails the exact executable-source
readiness judgment. -/
theorem executableSourceReady_of_productionReady_at_atomCount
    (input : CertifiedLocalizedCIPInput)
    (state : input.LocalizedAuxiliaryState input.certified.input.molecule.atomCount)
    (axis : input.LocalizedOddCumuleneChain)
    (ready : input.LocalizedOddCumuleneEZProductionReadyAtAtomCount state axis) :
    input.LocalizedOddCumuleneEZExecutableSourceReadyAtWithState
      input.certified.input.molecule.atomCount state axis := by
  obtain ⟨assignment, computed, _derived⟩ :=
    input.exists_localizedOddCumuleneEZSpatialAssignmentAtWithState?_of_ready_at_atomCount
      state axis ready
  exact
    (input.localizedOddCumuleneEZExecutableSourceReadyAtWithState_iff_exists_assignment
      input.certified.input.molecule.atomCount state axis).mpr ⟨assignment, computed⟩

/-- A fail-closed one-axis result proves that the independent production-readiness evidence is
absent.  Thus `none` cannot be caused by topology or an insufficient traversal bound for a
perceived odd chain at atom count. -/
theorem not_ready_of_localizedOddCumuleneEZSpatialAssignmentAtWithState?_eq_none
    (input : CertifiedLocalizedCIPInput)
    (state : input.LocalizedAuxiliaryState input.certified.input.molecule.atomCount)
    (axis : input.LocalizedOddCumuleneChain)
    (computed : input.localizedOddCumuleneEZSpatialAssignmentAtWithState?
      input.certified.input.molecule.atomCount state axis = none) :
    ¬ input.LocalizedOddCumuleneEZProductionReadyAtAtomCount state axis := by
  intro ready
  obtain ⟨assignment, successful, _derived⟩ :=
    input.exists_localizedOddCumuleneEZSpatialAssignmentAtWithState?_of_ready_at_atomCount
      state axis ready
  rw [computed] at successful
  contradiction

/-- The state-parameterized whole-molecule analyzer contains the complete result constructed for
every ready perceived odd cumulene. -/
theorem exists_mem_analyzeLocalizedOddCumuleneEZWithState_of_ready_at_atomCount
    (input : CertifiedLocalizedCIPInput)
    (state : input.LocalizedAuxiliaryState input.certified.input.molecule.atomCount)
    (axis : input.LocalizedOddCumuleneChain)
    (ready : input.LocalizedOddCumuleneEZProductionReadyAtAtomCount state axis) :
    ∃ assignment,
      assignment ∈ input.analyzeLocalizedOddCumuleneEZWithState
        input.certified.input.molecule.atomCount state ∧
      assignment.axis = axis ∧
      input.DeclarativeLocalizedOddCumuleneEZSpatialAssignmentWithState
        input.certified.input.molecule.atomCount state assignment := by
  obtain ⟨assignment, emitted, derived⟩ :=
    input.exists_localizedOddCumuleneEZSpatialAssignmentAtWithState?_of_ready_at_atomCount
      state axis ready
  have axisIdentity :=
    input.localizedOddCumuleneEZSpatialAssignmentAtWithState?_axis
      input.certified.input.molecule.atomCount state axis assignment emitted
  have present :=
    (input.mem_analyzeLocalizedOddCumuleneEZWithState_iff
      input.certified.input.molecule.atomCount state assignment).mpr (by
        rw [axisIdentity]
        exact emitted)
  exact ⟨assignment, present, axisIdentity, derived⟩

/-- Exact molecule-list readiness: a canonical odd chain is executable-source ready precisely
when the state-parameterized analyzer contains an assignment retaining that chain. -/
theorem localizedOddCumuleneEZExecutableSourceReadyAtWithState_iff_exists_mem_analyze
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel)
    (axis : input.LocalizedOddCumuleneChain) :
    input.LocalizedOddCumuleneEZExecutableSourceReadyAtWithState fuel state axis ↔
      ∃ assignment,
        assignment ∈ input.analyzeLocalizedOddCumuleneEZWithState fuel state ∧
        assignment.axis = axis := by
  constructor
  · intro ready
    obtain ⟨assignment, emitted⟩ :=
      (input.localizedOddCumuleneEZExecutableSourceReadyAtWithState_iff_exists_assignment
        fuel state axis).mp ready
    have axisIdentity :=
      input.localizedOddCumuleneEZSpatialAssignmentAtWithState?_axis
        fuel state axis assignment emitted
    have present :=
      (input.mem_analyzeLocalizedOddCumuleneEZWithState_iff
        fuel state assignment).mpr (by
          rw [axisIdentity]
          exact emitted)
    exact ⟨assignment, present, axisIdentity⟩
  · rintro ⟨assignment, present, axisIdentity⟩
    have emitted :=
      (input.mem_analyzeLocalizedOddCumuleneEZWithState_iff
        fuel state assignment).mp present
    apply
      (input.localizedOddCumuleneEZExecutableSourceReadyAtWithState_iff_exists_assignment
        fuel state axis).mpr
    refine ⟨assignment, ?_⟩
    rwa [axisIdentity] at emitted

/-- Whole-molecule odd-cumulene analysis emits no duplicate proof-bearing assignments. -/
theorem analyzeLocalizedOddCumuleneEZWithState_nodup
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (state : input.LocalizedAuxiliaryState fuel) :
    (input.analyzeLocalizedOddCumuleneEZWithState fuel state).Nodup := by
  classical
  unfold analyzeLocalizedOddCumuleneEZWithState
  apply List.Nodup.filterMap
  · intro left right assignment leftComputed rightComputed
    have leftAxis :=
      input.localizedOddCumuleneEZSpatialAssignmentAtWithState?_axis
        fuel state left assignment leftComputed
    have rightAxis :=
      input.localizedOddCumuleneEZSpatialAssignmentAtWithState?_axis
        fuel state right assignment rightComputed
    exact leftAxis.symm.trans rightAxis
  · exact input.localizedOddCumuleneChains_nodup.attach

/-- Scheduled molecule-wide analysis contains the independently correct result of every ready
canonical odd chain. -/
theorem exists_mem_analyzeLocalizedOddCumuleneEZ_of_ready_at_atomCount
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedOddCumuleneChain)
    (ready : input.LocalizedOddCumuleneEZProductionReadyAtAtomCount
      (input.localizedDescriptorBearingRule3Through5SchedulerState
        input.certified.input.molecule.atomCount) axis) :
    ∃ assignment,
      assignment ∈ input.analyzeLocalizedOddCumuleneEZ
        input.certified.input.molecule.atomCount ∧
      assignment.axis = axis ∧
      input.DeclarativeLocalizedOddCumuleneEZSpatialAssignment
        input.certified.input.molecule.atomCount assignment := by
  simpa [analyzeLocalizedOddCumuleneEZ,
    DeclarativeLocalizedOddCumuleneEZSpatialAssignment] using
    input.exists_mem_analyzeLocalizedOddCumuleneEZWithState_of_ready_at_atomCount
      (input.localizedDescriptorBearingRule3Through5SchedulerState
        input.certified.input.molecule.atomCount) axis ready

/-- Exact executable-source readiness under the canonical causal Rules-1a--5 scheduler state. -/
def LocalizedOddCumuleneEZExecutableSourceReady
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedOddCumuleneChain) : Prop :=
  input.LocalizedOddCumuleneEZExecutableSourceReadyAtWithState fuel
    (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) axis

/-- Scheduled molecule-list membership is exactly executable-source readiness for the retained
canonical odd chain. -/
theorem localizedOddCumuleneEZExecutableSourceReady_iff_exists_mem_analyze
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedOddCumuleneChain) :
    input.LocalizedOddCumuleneEZExecutableSourceReady fuel axis ↔
      ∃ assignment,
        assignment ∈ input.analyzeLocalizedOddCumuleneEZ fuel ∧
        assignment.axis = axis := by
  exact input.localizedOddCumuleneEZExecutableSourceReadyAtWithState_iff_exists_mem_analyze
    fuel (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) axis

/-- The scheduled analyzer contains at most one assignment retaining any fixed canonical odd
chain. -/
theorem analyzeLocalizedOddCumuleneEZ_assignment_unique_for_axis
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedOddCumuleneChain)
    (left right : input.LocalizedOddCumuleneEZSpatialAssignment fuel)
    (leftPresent : left ∈ input.analyzeLocalizedOddCumuleneEZ fuel)
    (rightPresent : right ∈ input.analyzeLocalizedOddCumuleneEZ fuel)
    (leftAxis : left.axis = axis)
    (rightAxis : right.axis = axis) :
    left = right := by
  have leftComputed :=
    (input.mem_analyzeLocalizedOddCumuleneEZWithState_iff fuel
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) left).mp
        leftPresent
  have rightComputed :=
    (input.mem_analyzeLocalizedOddCumuleneEZWithState_iff fuel
      (input.localizedDescriptorBearingRule3Through5SchedulerState fuel) right).mp
        rightPresent
  rw [leftAxis] at leftComputed
  rw [rightAxis] at rightComputed
  exact Option.some.inj (leftComputed.symm.trans rightComputed)

/-- The scheduled whole-molecule odd-cumulene result list is duplicate-free. -/
theorem analyzeLocalizedOddCumuleneEZ_nodup
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    (input.analyzeLocalizedOddCumuleneEZ fuel).Nodup := by
  exact input.analyzeLocalizedOddCumuleneEZWithState_nodup fuel
    (input.localizedDescriptorBearingRule3Through5SchedulerState fuel)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
