import TetraStereo.OneCenter.LocalizedEvenCumuleneAxialPerceptionCompleteness
import TetraStereo.OneCenter.LocalizedRerootDescriptorBearingRule3FuelCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Conditional end-to-end completeness for perceived even cumulenes

Topology discovery, occurrence embedding, zipper traversal, terminal recognition, and even-parity
recognition are unconditional for every perceived canonical open even axis.  Final descriptor
emission is intentionally conditional on the remaining chemical facts: two canonical endpoint
compilations and a strict, spatially nondegenerate axial assignment.  Those are not implementation
failure conditions—tied endpoint ligands or zero/missing geometry mean that no `Rₐ/Sₐ` descriptor
is justified.
-/

namespace CertifiedLocalizedCIPInput

/-- The actual finite descriptor-bearing Rule-3 evaluator makes a complete endpoint frame once
the two physical references are canonical, every queried node resolves through the conservative
index. Coupled-unit ambiguity is intrinsically a four-ligand condition and is proved impossible
for this two-cursor endpoint frame. Rules 4a--5 require no additional premise: their existing
reroot-fuel theorem applies to the path-valid canonical reference cursors. -/
theorem exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_at_conservativeFuel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (endpoint partner first second : input.Atom)
    (endpointCursor firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstReference : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor firstCursor first)
    (secondReference : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor secondCursor second)
    (resolved : input.LocalizedDescriptorBearingRule3ReachableResolvedThrough target view
      (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)) :
    ∃ frame,
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
          target view
          (input.buildLocalizedDescriptorBearingRule3Frame? target view
            (localizedDescriptorBearingRule3EvaluationFuel carrierFuel))
          endpoint partner endpointCursor = some frame := by
  have firstValid := firstReference.valid input endpointCursor firstCursor first
  have secondValid := secondReference.valid input endpointCursor secondCursor second
  obtain ⟨rule3Frame, rule3FrameComputed⟩ :=
    input.exists_buildLocalizedDescriptorBearingRule3Frame?_two_at_conservativeFuel
      target view resolved firstCursor secondCursor firstValid secondValid
  have keyCount : rule3Frame.keys.length = 2 := by
    simpa using input.buildLocalizedDescriptorBearingRule3Frame?_keys_length_eq
      target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)
      [firstCursor, secondCursor] rule3Frame rule3FrameComputed
  exact input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_two_canonical_references
    target view
    (input.buildLocalizedDescriptorBearingRule3Frame? target view
      (localizedDescriptorBearingRule3EvaluationFuel carrierFuel))
    endpoint partner first second endpointCursor firstCursor secondCursor
    candidates firstReference secondReference
    ⟨rule3Frame, rule3FrameComputed, keyCount⟩

/-- Independent finite conditions under which one endpoint of the production even-cumulene
compiler is structurally and chemically resolvable through complete Rules 1a--5. -/
def LocalizedEvenCumuleneProductionEndpointResolved
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel) : Prop :=
  ∃ first second firstCursor secondCursor,
    input.localizedRule3ExplicitSubstituents endpoint partner = [first, second] ∧
      input.CanonicalLocalizedRule3ReferenceCursor endpointCursor firstCursor first ∧
      input.CanonicalLocalizedRule3ReferenceCursor endpointCursor secondCursor second ∧
      input.LocalizedDescriptorBearingRule3ReachableResolvedThrough target view
        (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)

/-- Once the exact endpoint has two explicit substituents, the perceived-axis occurrence
embedding constructs both canonical physical reference cursors automatically.  Only resolution
of descriptor-bearing node dependencies remains as chemical evidence. -/
def LocalizedEvenCumuleneProductionEndpointDependenciesResolved
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) : Prop :=
  input.LocalizedDescriptorBearingRule3ReachableSupportThrough target view
    (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)

/-- The superseded all-occurrence resolution premise cannot hold for an even cumulene: its
distinguished first axis child is a real order-two edge, while the old premise also demanded that
the fuel-zero structural reader resolve that geometrical occurrence. -/
theorem not_localizedDescriptorBearingRule3ResolvedThrough_evenAxial_at_atomCount
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain)
    (view : input.LocalizedDependencyView
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis))
    (maximumFuel : Nat) :
    ¬ input.LocalizedDescriptorBearingRule3ResolvedThrough
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis)
      view maximumFuel := by
  have physical := input.localizedEvenAxialFirstChildOccurrence_physical
    input.certified.input.molecule.atomCount axis
  have edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge
      (input.localizedEvenAxialFirstChildOccurrence
        input.certified.input.molecule.atomCount axis) :=
    ⟨physical.1, axis.1.root.firstAxis, axis.1.root.terminal,
      physical.2.1, physical.2.2.1, physical.2.2.2⟩
  exact input.not_localizedDescriptorBearingRule3ResolvedThrough_of_doubleBondEdge
    (input.localizedEvenAxialRootOccurrence
      input.certified.input.molecule.atomCount axis)
    (input.localizedEvenAxialFirstChildOccurrence
      input.certified.input.molecule.atomCount axis)
    view edge

/-- At the canonical initial endpoint, exact two-substituent perception plus dependency
resolution suffices for the former endpoint-resolution package. -/
theorem exists_productionEndpointResolved_evenAxialInitialLeft
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain)
    (view : input.LocalizedDependencyView
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis))
    (first second : input.Atom)
    (candidates : input.localizedRule3ExplicitSubstituents
      axis.1.root.terminal axis.1.root.firstAxis = [first, second])
    (dependencies : input.LocalizedEvenCumuleneProductionEndpointDependenciesResolved
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis) view) :
    input.LocalizedEvenCumuleneProductionEndpointResolved
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis)
      view axis.1.root.terminal axis.1.root.firstAxis
      (input.localizedEvenAxialInitialPhysicalEndpointCursorFrame
        input.certified.input.molecule.atomCount axis).leftCursor := by
  have firstPresent : first ∈ input.localizedRule3ExplicitSubstituents
      axis.1.root.terminal axis.1.root.firstAxis := by simp [candidates]
  have secondPresent : second ∈ input.localizedRule3ExplicitSubstituents
      axis.1.root.terminal axis.1.root.firstAxis := by simp [candidates]
  obtain ⟨firstCursor, firstCanonical⟩ :=
    input.exists_canonicalRule3ReferenceCursor_evenAxialInitialLeft
      input.certified.input.molecule.atomCount axis first firstPresent
  obtain ⟨secondCursor, secondCanonical⟩ :=
    input.exists_canonicalRule3ReferenceCursor_evenAxialInitialLeft
      input.certified.input.molecule.atomCount axis second secondPresent
  have resolved :=
    LocalizedDescriptorBearingRule3ReachableSupportThrough.resolved
      input
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis)
      view dependencies
  exact ⟨first, second, firstCursor, secondCursor, candidates,
    firstCanonical, secondCanonical, resolved⟩

/-- At the opposite endpoint carried by the perceived-axis embedding, exact two-substituent
perception likewise constructs both canonical reference cursors automatically. -/
theorem LocalizedAxialOccurrencePathEmbedding.exists_productionEndpointResolved
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {previousOccurrence firstOccurrence : input.LocalizedCIPOccurrence fuel}
    {atomPath : List input.Atom}
    (embedding : input.LocalizedAxialOccurrencePathEmbedding
      fuel previousOccurrence firstOccurrence atomPath)
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (endpointCursor partnerCursor : input.LocalizedRerootCursor fuel)
    (endpoint partner first second : input.Atom)
    (endpointPresent : endpointCursor ∈ embedding.cursors)
    (incoming : endpointCursor.previous? = some partnerCursor.occurrence)
    (endpointCurrent : endpointCursor.occurrence.1.node.current? = some endpoint)
    (partnerCurrent : partnerCursor.occurrence.1.node.current? = some partner)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner =
      [first, second])
    (dependencies : input.LocalizedEvenCumuleneProductionEndpointDependenciesResolved
      target view) :
    input.LocalizedEvenCumuleneProductionEndpointResolved
      target view endpoint partner endpointCursor := by
  have firstPresent : first ∈
      input.localizedRule3ExplicitSubstituents endpoint partner := by simp [candidates]
  have secondPresent : second ∈
      input.localizedRule3ExplicitSubstituents endpoint partner := by simp [candidates]
  obtain ⟨firstCursor, firstCanonical⟩ :=
    embedding.exists_canonicalRule3ReferenceCursor input endpointCursor endpointPresent
      partnerCursor.occurrence endpoint partner first incoming partnerCurrent
      endpointCurrent firstPresent
  obtain ⟨secondCursor, secondCanonical⟩ :=
    embedding.exists_canonicalRule3ReferenceCursor input endpointCursor endpointPresent
      partnerCursor.occurrence endpoint partner second incoming partnerCurrent
      endpointCurrent secondPresent
  have resolved :=
    LocalizedDescriptorBearingRule3ReachableSupportThrough.resolved
      input target view dependencies
  exact ⟨first, second, firstCursor, secondCursor, candidates,
    firstCanonical, secondCanonical, resolved⟩

/-- The concrete production endpoint callback is total under the independent resolved-endpoint
conditions. -/
theorem exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_production_resolved
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (resolved : input.LocalizedEvenCumuleneProductionEndpointResolved
      target view endpoint partner endpointCursor) :
    ∃ frame,
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
          target view
          (input.buildLocalizedDescriptorBearingRule3Frame? target view
            (localizedEvenCumuleneAxialRule3EvaluationFuel carrierFuel))
          endpoint partner endpointCursor = some frame := by
  rcases resolved with ⟨first, second, firstCursor, secondCursor,
    candidates, firstReference, secondReference, nodesResolved⟩
  simpa [localizedEvenCumuleneAxialRule3EvaluationFuel,
    localizedDescriptorBearingRule3EvaluationFuel] using
    input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_at_conservativeFuel
      target view endpoint partner first second endpointCursor firstCursor secondCursor
      candidates firstReference secondReference nodesResolved

/-- The concrete production compiler is end-to-end complete for every perceived canonical open
even axis whose two endpoints satisfy the independent finite resolution conditions and whose
resulting strict senior references possess nondegenerate P-92 spatial evidence. -/
theorem exists_localizedEvenCumuleneAxialAssignment?_evenAxial_at_atomCount
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain)
    (view : input.LocalizedDependencyView
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis))
    (endpointEvidence : ∀ topology : input.LocalizedRule3CumulatedEndpointCursorFrame
        input.certified.input.molecule.atomCount,
      input.DeclarativeLocalizedEvenCumuleneEndpointCursorFrame
          (input.localizedEvenAxialFirstChildOccurrence
            input.certified.input.molecule.atomCount axis) topology →
      input.LocalizedEvenCumuleneProductionEndpointResolved
          (input.localizedEvenAxialRootOccurrence
            input.certified.input.molecule.atomCount axis)
          view topology.initial.left topology.initial.right topology.initial.leftCursor ∧
        input.LocalizedEvenCumuleneProductionEndpointResolved
          (input.localizedEvenAxialRootOccurrence
            input.certified.input.molecule.atomCount axis)
          view topology.right topology.rightPartner topology.rightCursor)
    (spatialEvidence : ∀
      (topology : input.LocalizedRule3CumulatedEndpointCursorFrame
        input.certified.input.molecule.atomCount)
      (leftCompilation rightCompilation : input.LocalizedRule3OccurrenceEndpointKeyFrame
        input.certified.input.molecule.atomCount),
      input.DeclarativeLocalizedEvenCumuleneEndpointCursorFrame
          (input.localizedEvenAxialFirstChildOccurrence
            input.certified.input.molecule.atomCount axis) topology →
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
          (input.localizedEvenAxialRootOccurrence
            input.certified.input.molecule.atomCount axis)
          view
          (input.buildLocalizedDescriptorBearingRule3Frame?
            (input.localizedEvenAxialRootOccurrence
              input.certified.input.molecule.atomCount axis)
            view (localizedEvenCumuleneAxialRule3EvaluationFuel
              input.certified.input.molecule.atomCount))
          topology.initial.left topology.initial.right topology.initial.leftCursor =
        some leftCompilation →
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
          (input.localizedEvenAxialRootOccurrence
            input.certified.input.molecule.atomCount axis)
          view
          (input.buildLocalizedDescriptorBearingRule3Frame?
            (input.localizedEvenAxialRootOccurrence
              input.certified.input.molecule.atomCount axis)
            view (localizedEvenCumuleneAxialRule3EvaluationFuel
              input.certified.input.molecule.atomCount))
          topology.right topology.rightPartner topology.rightCursor =
        some rightCompilation →
      ∃ assignment,
        input.DeclarativeLocalizedAxialAssignmentOfEndpointFrames
          topology.initial.left topology.right
          leftCompilation.endpointFrame rightCompilation.endpointFrame assignment) :
    ∃ result,
      input.localizedEvenCumuleneAxialAssignment?
          (input.localizedEvenAxialRootOccurrence
            input.certified.input.molecule.atomCount axis)
          (input.localizedEvenAxialFirstChildOccurrence
            input.certified.input.molecule.atomCount axis)
          view = some result ∧
        input.DeclarativeLocalizedEvenCumuleneAxialAssignment
          (input.localizedEvenAxialRootOccurrence
            input.certified.input.molecule.atomCount axis)
          (input.localizedEvenAxialFirstChildOccurrence
            input.certified.input.molecule.atomCount axis)
          view result := by
  obtain ⟨topology, topologyComputed, topologyDerived⟩ :=
    input.exists_localizedEvenCumuleneEndpointCursorFrame_at_atomCount axis
  obtain ⟨leftResolved, rightResolved⟩ := endpointEvidence topology topologyDerived
  obtain ⟨leftCompilation, leftComputed⟩ :=
    input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_production_resolved
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis)
      view topology.initial.left topology.initial.right topology.initial.leftCursor leftResolved
  obtain ⟨rightCompilation, rightComputed⟩ :=
    input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_production_resolved
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis)
      view topology.right topology.rightPartner topology.rightCursor rightResolved
  obtain ⟨assignment, assignmentDerived⟩ := spatialEvidence topology
    leftCompilation rightCompilation topologyDerived leftComputed rightComputed
  have assignmentComputed :=
    (input.localizedAxialAssignmentOfEndpointFrames?_eq_some_iff
      topology.initial.left topology.right leftCompilation.endpointFrame
      rightCompilation.endpointFrame assignment).mpr assignmentDerived
  let result : input.LocalizedEvenCumuleneAxialResult
      input.certified.input.molecule.atomCount :=
    { topology, leftCompilation, rightCompilation, assignment }
  have computed :
      input.localizedEvenCumuleneAxialAssignment?
          (input.localizedEvenAxialRootOccurrence
            input.certified.input.molecule.atomCount axis)
          (input.localizedEvenAxialFirstChildOccurrence
            input.certified.input.molecule.atomCount axis)
          view = some result := by
    simp [localizedEvenCumuleneAxialAssignment?,
      localizedEvenCumuleneAxialAssignmentWith?, topologyComputed,
      leftComputed, rightComputed, assignmentComputed, result]
  exact ⟨result, computed,
    input.localizedEvenCumuleneAxialAssignment?_sound
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis)
      (input.localizedEvenAxialFirstChildOccurrence
        input.certified.input.molecule.atomCount axis)
      view result computed⟩

/-- Concrete chemical applicability data after occurrence construction has been discharged.  It
asks only for the exact two explicit substituents at each endpoint and for the remaining
explicit support of the valid descriptor-bearing node queries, quantified over the canonical
cursors that the carrier theorem constructs. -/
def LocalizedEvenCumuleneProductionDependencyEvidence
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain)
    (view : input.LocalizedDependencyView
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis)) : Prop :=
  ∀ (topology : input.LocalizedRule3CumulatedEndpointCursorFrame
      input.certified.input.molecule.atomCount)
    (embedding : input.LocalizedAxialOccurrencePathEmbedding
      input.certified.input.molecule.atomCount
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis)
      (input.localizedEvenAxialFirstChildOccurrence
        input.certified.input.molecule.atomCount axis)
      axis.1.path.tail),
    topology.initial = input.localizedEvenAxialInitialPhysicalEndpointCursorFrame
        input.certified.input.molecule.atomCount axis →
    topology.rightward = embedding.cursors →
    topology.rightCursor ∈ embedding.cursors →
    topology.rightPartnerCursor ∈ embedding.cursors →
    topology.rightCursor.previous? = some topology.rightPartnerCursor.occurrence →
    ∃ leftFirst leftSecond rightFirst rightSecond,
      input.localizedRule3ExplicitSubstituents
          axis.1.root.terminal axis.1.root.firstAxis = [leftFirst, leftSecond] ∧
      input.localizedRule3ExplicitSubstituents
          topology.right topology.rightPartner = [rightFirst, rightSecond] ∧
      input.LocalizedEvenCumuleneProductionEndpointDependenciesResolved
        (input.localizedEvenAxialRootOccurrence
          input.certified.input.molecule.atomCount axis) view

/-- Production completeness with reference-cursor assumptions removed.  Perceived-axis topology,
carrier embedding, endpoint reference existence, reference uniqueness, and traversal fuel are all
constructed internally.  The retained hypotheses are genuine chemical applicability: exactly
two explicit substituents per terminal, explicit support of every reachable descriptor dependency,
and strict
nondegenerate P-92 spatial evidence. -/
theorem exists_localizedEvenCumuleneAxialAssignment?_of_dependencyEvidence_at_atomCount
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain)
    (view : input.LocalizedDependencyView
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis))
    (dependencyEvidence : input.LocalizedEvenCumuleneProductionDependencyEvidence axis view)
    (spatialEvidence : ∀
      (topology : input.LocalizedRule3CumulatedEndpointCursorFrame
        input.certified.input.molecule.atomCount)
      (leftCompilation rightCompilation : input.LocalizedRule3OccurrenceEndpointKeyFrame
        input.certified.input.molecule.atomCount),
      input.DeclarativeLocalizedEvenCumuleneEndpointCursorFrame
          (input.localizedEvenAxialFirstChildOccurrence
            input.certified.input.molecule.atomCount axis) topology →
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
          (input.localizedEvenAxialRootOccurrence
            input.certified.input.molecule.atomCount axis)
          view
          (input.buildLocalizedDescriptorBearingRule3Frame?
            (input.localizedEvenAxialRootOccurrence
              input.certified.input.molecule.atomCount axis)
            view (localizedEvenCumuleneAxialRule3EvaluationFuel
              input.certified.input.molecule.atomCount))
          topology.initial.left topology.initial.right topology.initial.leftCursor =
        some leftCompilation →
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
          (input.localizedEvenAxialRootOccurrence
            input.certified.input.molecule.atomCount axis)
          view
          (input.buildLocalizedDescriptorBearingRule3Frame?
            (input.localizedEvenAxialRootOccurrence
              input.certified.input.molecule.atomCount axis)
            view (localizedEvenCumuleneAxialRule3EvaluationFuel
              input.certified.input.molecule.atomCount))
          topology.right topology.rightPartner topology.rightCursor =
        some rightCompilation →
      ∃ assignment,
        input.DeclarativeLocalizedAxialAssignmentOfEndpointFrames
          topology.initial.left topology.right
          leftCompilation.endpointFrame rightCompilation.endpointFrame assignment) :
    ∃ result,
      input.localizedEvenCumuleneAxialAssignment?
          (input.localizedEvenAxialRootOccurrence
            input.certified.input.molecule.atomCount axis)
          (input.localizedEvenAxialFirstChildOccurrence
            input.certified.input.molecule.atomCount axis)
          view = some result ∧
        input.DeclarativeLocalizedEvenCumuleneAxialAssignment
          (input.localizedEvenAxialRootOccurrence
            input.certified.input.molecule.atomCount axis)
          (input.localizedEvenAxialFirstChildOccurrence
            input.certified.input.molecule.atomCount axis)
          view result := by
  obtain ⟨topology, embedding, topologyComputed, topologyDerived, initial,
      rightward, rightPresent, rightPartnerPresent, rightPrevious⟩ :=
    input.exists_localizedEvenCumuleneEndpointCursorFrameWithEmbedding_at_atomCount axis
  obtain ⟨leftFirst, leftSecond, rightFirst, rightSecond,
      leftCandidates, rightCandidates, dependencies⟩ :=
    dependencyEvidence topology embedding initial rightward rightPresent
      rightPartnerPresent rightPrevious
  have leftResolvedCanonical :=
    input.exists_productionEndpointResolved_evenAxialInitialLeft
      axis view leftFirst leftSecond leftCandidates dependencies
  have leftResolved : input.LocalizedEvenCumuleneProductionEndpointResolved
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis)
      view topology.initial.left topology.initial.right topology.initial.leftCursor := by
    simpa [initial] using leftResolvedCanonical
  have rightResolved := embedding.exists_productionEndpointResolved input
    (input.localizedEvenAxialRootOccurrence
      input.certified.input.molecule.atomCount axis)
    view topology.rightCursor topology.rightPartnerCursor
    topology.right topology.rightPartner rightFirst rightSecond rightPresent
    rightPrevious topologyDerived.1.2.2.2.2
    topologyDerived.1.2.2.2.1 rightCandidates dependencies
  obtain ⟨leftCompilation, leftComputed⟩ :=
    input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_production_resolved
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis)
      view topology.initial.left topology.initial.right topology.initial.leftCursor leftResolved
  obtain ⟨rightCompilation, rightComputed⟩ :=
    input.exists_buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_of_production_resolved
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis)
      view topology.right topology.rightPartner topology.rightCursor rightResolved
  obtain ⟨assignment, assignmentDerived⟩ := spatialEvidence topology
    leftCompilation rightCompilation topologyDerived leftComputed rightComputed
  have assignmentComputed :=
    (input.localizedAxialAssignmentOfEndpointFrames?_eq_some_iff
      topology.initial.left topology.right leftCompilation.endpointFrame
      rightCompilation.endpointFrame assignment).mpr assignmentDerived
  let result : input.LocalizedEvenCumuleneAxialResult
      input.certified.input.molecule.atomCount :=
    { topology, leftCompilation, rightCompilation, assignment }
  have computed :
      input.localizedEvenCumuleneAxialAssignment?
          (input.localizedEvenAxialRootOccurrence
            input.certified.input.molecule.atomCount axis)
          (input.localizedEvenAxialFirstChildOccurrence
            input.certified.input.molecule.atomCount axis)
          view = some result := by
    simp [localizedEvenCumuleneAxialAssignment?,
      localizedEvenCumuleneAxialAssignmentWith?, topologyComputed,
      leftComputed, rightComputed, assignmentComputed, result]
  exact ⟨result, computed,
    input.localizedEvenCumuleneAxialAssignment?_sound
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis)
      (input.localizedEvenAxialFirstChildOccurrence
        input.certified.input.molecule.atomCount axis)
      view result computed⟩

/-- For every perceived canonical open even cumulene, the full parameterized compiler emits a
kernel-verified result once canonical Rules-1a--5 endpoint evidence and an independently valid
strict-priority/P-92 spatial assignment are supplied.  No topology, path, or fuel premise remains. -/
theorem exists_localizedEvenCumuleneAxialAssignmentWith?_evenAxial_at_atomCount
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain)
    (view : input.LocalizedDependencyView
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis))
    (rule3FrameOf : List (input.LocalizedRerootCursor
      input.certified.input.molecule.atomCount) →
        Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning
      input.certified.input.molecule.atomCount)
    (rule3FrameSound : ∀ cursors frame,
      rule3FrameOf cursors = some frame → Rule3FrameMeaning cursors frame)
    (rule3FrameComplete : ∀ cursors frame,
      Rule3FrameMeaning cursors frame → rule3FrameOf cursors = some frame)
    (chemicalEvidence : ∀ topology : input.LocalizedRule3CumulatedEndpointCursorFrame
        input.certified.input.molecule.atomCount,
      input.DeclarativeLocalizedEvenCumuleneEndpointCursorFrame
          (input.localizedEvenAxialFirstChildOccurrence
            input.certified.input.molecule.atomCount axis) topology →
      ∃ leftCompilation rightCompilation assignment,
        input.CanonicalLocalizedRule3OccurrenceEndpointKeyFrameWith
          (input.localizedEvenAxialRootOccurrence
            input.certified.input.molecule.atomCount axis)
          view Rule3FrameMeaning topology.initial.left topology.initial.right
          topology.initial.leftCursor leftCompilation ∧
        input.CanonicalLocalizedRule3OccurrenceEndpointKeyFrameWith
          (input.localizedEvenAxialRootOccurrence
            input.certified.input.molecule.atomCount axis)
          view Rule3FrameMeaning topology.right topology.rightPartner
          topology.rightCursor rightCompilation ∧
        input.DeclarativeLocalizedAxialAssignmentOfEndpointFrames
          topology.initial.left topology.right
          leftCompilation.endpointFrame rightCompilation.endpointFrame assignment) :
    ∃ result,
      input.localizedEvenCumuleneAxialAssignmentWith?
          (input.localizedEvenAxialRootOccurrence
            input.certified.input.molecule.atomCount axis)
          (input.localizedEvenAxialFirstChildOccurrence
            input.certified.input.molecule.atomCount axis)
          view rule3FrameOf = some result ∧
        input.DeclarativeLocalizedEvenCumuleneAxialAssignmentWith
          (input.localizedEvenAxialRootOccurrence
            input.certified.input.molecule.atomCount axis)
          (input.localizedEvenAxialFirstChildOccurrence
            input.certified.input.molecule.atomCount axis)
          view Rule3FrameMeaning result := by
  obtain ⟨topology, topologyComputed, topologyDerived⟩ :=
    input.exists_localizedEvenCumuleneEndpointCursorFrame_at_atomCount axis
  obtain ⟨leftCompilation, rightCompilation, assignment,
    leftCanonical, rightCanonical, assignmentDerived⟩ :=
      chemicalEvidence topology topologyDerived
  have leftComputed :=
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_complete_of_canonical
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis)
      view rule3FrameOf Rule3FrameMeaning rule3FrameComplete
      topology.initial.left topology.initial.right topology.initial.leftCursor
      leftCompilation leftCanonical
  have rightComputed :=
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_complete_of_canonical
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis)
      view rule3FrameOf Rule3FrameMeaning rule3FrameComplete
      topology.right topology.rightPartner topology.rightCursor
      rightCompilation rightCanonical
  have assignmentComputed :=
    (input.localizedAxialAssignmentOfEndpointFrames?_eq_some_iff
      topology.initial.left topology.right leftCompilation.endpointFrame
      rightCompilation.endpointFrame assignment).mpr assignmentDerived
  let result : input.LocalizedEvenCumuleneAxialResult
      input.certified.input.molecule.atomCount :=
    { topology, leftCompilation, rightCompilation, assignment }
  have computed :
      input.localizedEvenCumuleneAxialAssignmentWith?
          (input.localizedEvenAxialRootOccurrence
            input.certified.input.molecule.atomCount axis)
          (input.localizedEvenAxialFirstChildOccurrence
            input.certified.input.molecule.atomCount axis)
          view rule3FrameOf = some result := by
    simp [localizedEvenCumuleneAxialAssignmentWith?, topologyComputed,
      leftComputed, rightComputed, assignmentComputed, result]
  exact ⟨result, computed,
    input.localizedEvenCumuleneAxialAssignmentWith?_sound
      (input.localizedEvenAxialRootOccurrence
        input.certified.input.molecule.atomCount axis)
      (input.localizedEvenAxialFirstChildOccurrence
        input.certified.input.molecule.atomCount axis)
      view rule3FrameOf Rule3FrameMeaning rule3FrameSound result computed⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
