import TetraStereo.OneCenter.LocalizedOddCumuleneAnalysis
import TetraStereo.OneCenter.LocalizedAxialOccurrencePathEmbedding

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Perception-to-odd-cumulene endpoint completeness

This module proves that every canonical molecule-wide odd-cumulene chain is reproduced exactly by
the occurrence-local Rule-3 zipper walker at atom-count carrier depth.  Thus topology discovery,
parity classification, and traversal fuel are unconditional for perceived odd chains; only the
later chemically meaningful endpoint-priority and spatial-evidence obligations may refuse a final
descriptor.
-/

namespace CertifiedLocalizedCIPInput

/-- Every perceived canonical open odd cumulene has a proof-bearing occurrence embedding whose
cursor observations are exactly the retained non-root molecular path and whose production walk
executes at atom-count depth. -/
theorem exists_localizedOddCumuleneOccurrencePathEmbedding_executes_at_atomCount
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedOddCumuleneChain) :
    ∃ embedding : input.LocalizedAxialOccurrencePathEmbedding
        input.certified.input.molecule.atomCount
        (input.localizedAxialRootOccurrence
          input.certified.input.molecule.atomCount
          (input.localizedOddCumuleneAxialRoot axis))
        (input.localizedAxialRootFirstChildOccurrence
          input.certified.input.molecule.atomCount
          (input.localizedOddCumuleneAxialRoot axis))
        axis.1.path.tail,
      input.walkLocalizedRule3CumulatedAxis?
          (input.localizedRule3CumulatedTraversalFuel
            input.certified.input.molecule.atomCount)
          (input.localizedAxialRootInitialPhysicalEndpointCursorFrame
            input.certified.input.molecule.atomCount
            (input.localizedOddCumuleneAxialRoot axis)).rightCursor =
        some embedding.cursors := by
  exact input.exists_localizedAxialRootOccurrencePathEmbedding_executes_at_atomCount
    (input.localizedOddCumuleneAxialRoot axis) axis.1.path
    (input.mem_localizedOddCumuleneChains_implies_declarative axis.1 axis.2).1

/-- Every perceived canonical open odd cumulene is accepted by the occurrence-local odd endpoint
constructor together with the exact molecular-path embedding from which the endpoint cursors were
constructed. -/
theorem exists_localizedRule3OddCumuleneEndpointCursorFrameWithEmbedding_at_atomCount
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedOddCumuleneChain) :
    ∃ frame : input.LocalizedRule3OddCumuleneEndpointCursorFrame
        input.certified.input.molecule.atomCount,
      ∃ embedding : input.LocalizedAxialOccurrencePathEmbedding
          input.certified.input.molecule.atomCount
          (input.localizedAxialRootOccurrence
            input.certified.input.molecule.atomCount
            (input.localizedOddCumuleneAxialRoot axis))
          (input.localizedAxialRootFirstChildOccurrence
            input.certified.input.molecule.atomCount
            (input.localizedOddCumuleneAxialRoot axis))
          axis.1.path.tail,
      input.localizedRule3OddCumuleneEndpointCursorFrame?
          (input.localizedRule3CumulatedTraversalFuel
            input.certified.input.molecule.atomCount)
          (input.localizedAxialRootFirstChildOccurrence
            input.certified.input.molecule.atomCount
            (input.localizedOddCumuleneAxialRoot axis)) = some frame ∧
      input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame
        (input.localizedAxialRootFirstChildOccurrence
          input.certified.input.molecule.atomCount
          (input.localizedOddCumuleneAxialRoot axis)) frame ∧
      frame.initial =
        input.localizedAxialRootInitialPhysicalEndpointCursorFrame
          input.certified.input.molecule.atomCount
          (input.localizedOddCumuleneAxialRoot axis) ∧
      frame.rightward = embedding.cursors ∧
      frame.rightCursor ∈ embedding.cursors ∧
      frame.rightPartnerCursor ∈ embedding.cursors ∧
      frame.rightCursor.previous? = some frame.rightPartnerCursor.occurrence := by
  let carrierFuel := input.certified.input.molecule.atomCount
  let traversalFuel := input.localizedRule3CumulatedTraversalFuel carrierFuel
  let axialRoot := input.localizedOddCumuleneAxialRoot axis
  let initial := input.localizedAxialRootInitialPhysicalEndpointCursorFrame
    carrierFuel axialRoot
  obtain ⟨embedding, walkComputed⟩ :=
    input.exists_localizedOddCumuleneOccurrencePathEmbedding_executes_at_atomCount axis
  let cursorPath := embedding.cursors
  have atoms : cursorPath.map
      (fun cursor => cursor.occurrence.1.node.current?) =
        axis.1.path.tail.map some :=
    embedding.atoms
  have axisValid :=
    input.mem_localizedOddCumuleneChains_implies_declarative axis.1 axis.2
  have cursorLength : cursorPath.length = axis.1.path.tail.length := by
    have mappedLengths := congrArg List.length atoms
    simpa using mappedLengths
  have sameBondCount : cursorPath.length = axis.1.doubleBondCount := by
    unfold LocalizedOddCumuleneChainFrame.doubleBondCount
    rw [cursorLength]
    simp only [List.length_tail]
  have admissible : 1 < cursorPath.length ∧ Odd cursorPath.length := by
    rw [sameBondCount]
    exact ⟨axisValid.2.1, axisValid.2.2.1⟩
  have currentSome : ∀ cursor, cursor ∈ cursorPath →
      ∃ atom, cursor.occurrence.1.node.current? = some atom := by
    intro cursor present
    have observedPresent : cursor.occurrence.1.node.current? ∈
        cursorPath.map (fun candidate => candidate.occurrence.1.node.current?) :=
      List.mem_map.mpr ⟨cursor, present, rfl⟩
    rw [atoms] at observedPresent
    rw [List.mem_map] at observedPresent
    rcases observedPresent with ⟨atom, _atomPresent, observedIdentity⟩
    exact ⟨atom, observedIdentity.symm⟩
  cases reverseIdentity : cursorPath.reverse with
  | nil =>
      have reverseLength : cursorPath.length = 0 := by
        have := congrArg List.length reverseIdentity
        simpa using this
      omega
  | cons right reverseTail =>
      cases reverseTail with
      | nil =>
          have reverseLength : cursorPath.length = 1 := by
            have := congrArg List.length reverseIdentity
            simpa using this
          omega
      | cons rightPartner more =>
          have rightPresent : right ∈ cursorPath := by
            have : right ∈ cursorPath.reverse := by simp [reverseIdentity]
            simpa using this
          have rightPartnerPresent : rightPartner ∈ cursorPath := by
            have : rightPartner ∈ cursorPath.reverse := by simp [reverseIdentity]
            simpa using this
          obtain ⟨rightAtom, rightObserved⟩ := currentSome right rightPresent
          obtain ⟨rightPartnerAtom, rightPartnerObserved⟩ :=
            currentSome rightPartner rightPartnerPresent
          have reverseIncoming : cursorPath.reverse.IsChain
              (fun later earlier =>
                later.previous? = some earlier.occurrence) := by
            exact List.isChain_reverse.mpr embedding.incoming
          rw [reverseIdentity] at reverseIncoming
          have rightPrevious : right.previous? = some rightPartner.occurrence :=
            reverseIncoming.rel_head
          let frame : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel :=
            { initial := initial
              rightward := cursorPath
              rightPartnerCursor := rightPartner
              rightCursor := right
              rightPartner := rightPartnerAtom
              right := rightAtom }
          have frameComputed : input.localizedRule3OddCumuleneEndpointCursorFrame?
              traversalFuel
              (input.localizedAxialRootFirstChildOccurrence carrierFuel axialRoot) =
                some frame := by
            change input.walkLocalizedRule3CumulatedAxis? traversalFuel
                initial.rightCursor = some cursorPath at walkComputed
            simp [localizedRule3OddCumuleneEndpointCursorFrame?,
              input.localizedRule3PhysicalEndpointCursorFrame?_axialRootFirstChild
                carrierFuel axialRoot,
              input.localizedRule3AxisTopology?_axialRootInitialLeft_terminal
                carrierFuel axialRoot,
              walkComputed, reverseIdentity, admissible,
              rightPartnerObserved, rightObserved, frame, initial,
              traversalFuel, carrierFuel, axialRoot]
          refine ⟨frame, embedding, frameComputed, ?_, rfl, rfl,
            rightPresent, rightPartnerPresent, rightPrevious⟩
          exact input.localizedRule3OddCumuleneEndpointCursorFrame?_sound
            traversalFuel
            (input.localizedAxialRootFirstChildOccurrence carrierFuel axialRoot)
            frame frameComputed

/-- Topology and traversal fuel are unconditionally sufficient for every perceived canonical
open odd cumulene at atom-count carrier depth. -/
theorem exists_localizedRule3OddCumuleneEndpointCursorFrame_at_atomCount
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedOddCumuleneChain) :
    ∃ frame,
      input.localizedRule3OddCumuleneEndpointCursorFrame?
          (input.localizedRule3CumulatedTraversalFuel
            input.certified.input.molecule.atomCount)
          (input.localizedAxialRootFirstChildOccurrence
            input.certified.input.molecule.atomCount
            (input.localizedOddCumuleneAxialRoot axis)) = some frame ∧
      input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame
        (input.localizedAxialRootFirstChildOccurrence
          input.certified.input.molecule.atomCount
          (input.localizedOddCumuleneAxialRoot axis)) frame := by
  obtain ⟨frame, _embedding, computed, derived, _initial, _rightward,
      _rightPresent, _rightPartnerPresent, _rightPrevious⟩ :=
    input.exists_localizedRule3OddCumuleneEndpointCursorFrameWithEmbedding_at_atomCount axis
  exact ⟨frame, computed, derived⟩

/-- In every final scheduled odd-cumulene assignment at the canonical atom-count carrier, the
stored occurrence topology observes exactly the non-root atoms of the retained molecule-wide
chain.  This rules out a merely co-rooted but different odd path in the final result certificate. -/
theorem analyzeLocalizedOddCumuleneEZ_atomCount_member_topology_matches_axis
    (input : CertifiedLocalizedCIPInput)
    (assignment : input.LocalizedOddCumuleneEZSpatialAssignment
      input.certified.input.molecule.atomCount)
    (present : assignment ∈ input.analyzeLocalizedOddCumuleneEZ
      input.certified.input.molecule.atomCount) :
    assignment.result.source.topology.rightward.map
        (fun cursor => cursor.occurrence.1.node.current?) =
      assignment.axis.1.path.tail.map some := by
  cases assignment with
  | mk axis assignedResult =>
      let carrierFuel := input.certified.input.molecule.atomCount
      let state := input.localizedDescriptorBearingRule3Through5SchedulerState carrierFuel
      have presentWithState :
          { axis := axis, result := assignedResult } ∈
            input.analyzeLocalizedOddCumuleneEZWithState carrierFuel state := by
        simpa [analyzeLocalizedOddCumuleneEZ, carrierFuel, state] using present
      have assignmentComputed :=
        (input.mem_analyzeLocalizedOddCumuleneEZWithState_iff carrierFuel state
          { axis := axis, result := assignedResult }).mp presentWithState
      unfold localizedOddCumuleneEZSpatialAssignmentAtWithState? at assignmentComputed
      dsimp only at assignmentComputed
      let axialRoot := input.localizedOddCumuleneAxialRoot axis
      let target := input.localizedAxialRootOccurrence carrierFuel axialRoot
      let occurrence := input.localizedAxialRootFirstChildOccurrence carrierFuel axialRoot
      let view := input.localizedDependencyView state target
      let frameOf := input.buildLocalizedDescriptorBearingRule3Frame?
        target view (localizedDescriptorBearingRule3EvaluationFuel carrierFuel)
      cases finalComputed : input.localizedRule3OddCumuleneEZWith?
          target occurrence view frameOf with
      | none =>
          simp [carrierFuel, state, axialRoot, target, occurrence, view, frameOf,
            finalComputed] at assignmentComputed
      | some result =>
          simp [carrierFuel, state, axialRoot, target, occurrence, view, frameOf,
            finalComputed] at assignmentComputed
          subst assignedResult
          have sourceComputed := input.localizedRule3OddCumuleneEZWith?_source
            target occurrence view frameOf result finalComputed
          have topologyComputed :=
            input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?_topology
              target occurrence view frameOf result.source sourceComputed
          obtain ⟨frame, embedding, frameComputed, _frameDerived, _initial,
              rightward, _rightPresent, _rightPartnerPresent, _rightPrevious⟩ :=
            input.exists_localizedRule3OddCumuleneEndpointCursorFrameWithEmbedding_at_atomCount
              axis
          have frameIdentity : frame = result.source.topology :=
            Option.some.inj (frameComputed.symm.trans (by
              simpa [carrierFuel, axialRoot, occurrence] using topologyComputed))
          rw [← frameIdentity, rightward]
          exact embedding.atoms

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
