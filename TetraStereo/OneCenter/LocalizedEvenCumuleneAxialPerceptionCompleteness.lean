import TetraStereo.OneCenter.LocalizedAxialOccurrencePathEmbedding
import TetraStereo.OneCenter.LocalizedEvenCumuleneAxialDescriptor

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Perception-to-even-cumulene endpoint completeness

The molecule-level open-even-axis carrier now reaches the exact occurrence zipper and the generic
cumulated endpoint constructor without a caller-supplied topology premise.  This module transfers
the perceived path's nonordinary even parity to the resulting endpoint frame.
-/

namespace CertifiedLocalizedCIPInput

/-- Every perceived canonical open even cumulene is accepted together with the proof-bearing
occurrence embedding from which its endpoint cursors were constructed. -/
theorem exists_localizedEvenCumuleneEndpointCursorFrameWithEmbedding_at_atomCount
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain) :
    ∃ frame : input.LocalizedRule3CumulatedEndpointCursorFrame
        input.certified.input.molecule.atomCount,
      ∃ embedding : input.LocalizedAxialOccurrencePathEmbedding
          input.certified.input.molecule.atomCount
          (input.localizedEvenAxialRootOccurrence
            input.certified.input.molecule.atomCount axis)
          (input.localizedEvenAxialFirstChildOccurrence
            input.certified.input.molecule.atomCount axis)
          axis.1.path.tail,
      input.localizedEvenCumuleneEndpointCursorFrame?
          (input.localizedRule3CumulatedTraversalFuel
            input.certified.input.molecule.atomCount)
          (input.localizedEvenAxialFirstChildOccurrence
            input.certified.input.molecule.atomCount axis) = some frame ∧
      input.DeclarativeLocalizedEvenCumuleneEndpointCursorFrame
        (input.localizedEvenAxialFirstChildOccurrence
          input.certified.input.molecule.atomCount axis) frame ∧
      frame.initial =
        input.localizedEvenAxialInitialPhysicalEndpointCursorFrame
          input.certified.input.molecule.atomCount axis ∧
      frame.rightward = embedding.cursors ∧
      frame.rightCursor ∈ embedding.cursors ∧
      frame.rightPartnerCursor ∈ embedding.cursors ∧
      frame.rightCursor.previous? = some frame.rightPartnerCursor.occurrence := by
  obtain ⟨frame, embedding, frameComputed, initial, rightward, rightPresent,
      rightPartnerPresent, rightPrevious⟩ :=
    input.exists_localizedRule3CumulatedEndpointCursorFrameWithEmbedding_evenAxial_at_atomCount
      axis
  have observations : frame.rightward.map
      (fun cursor => cursor.occurrence.1.node.current?) =
        axis.1.path.tail.map some := by
    rw [rightward]
    exact embedding.atoms
  have axisValid := (input.mem_localizedEvenAxialChains_iff axis.1).mp axis.2
  have sameLength : frame.rightward.length = axis.1.path.tail.length := by
    have mappedLengths := congrArg List.length observations
    simpa using mappedLengths
  have sameBondCount : frame.doubleBondCount = axis.1.doubleBondCount := by
    unfold LocalizedRule3CumulatedEndpointCursorFrame.doubleBondCount
      LocalizedEvenAxialChainFrame.doubleBondCount
    rw [sameLength]
    simp only [List.length_tail]
  have parity : 1 < frame.doubleBondCount ∧ Even frame.doubleBondCount := by
    rw [sameBondCount]
    exact ⟨axisValid.2.1, axisValid.2.2.1⟩
  have evenComputed : input.localizedEvenCumuleneEndpointCursorFrame?
      (input.localizedRule3CumulatedTraversalFuel
        input.certified.input.molecule.atomCount)
      (input.localizedEvenAxialFirstChildOccurrence
        input.certified.input.molecule.atomCount axis) = some frame := by
    simp [localizedEvenCumuleneEndpointCursorFrame?, frameComputed, parity]
  exact ⟨frame, embedding, evenComputed,
    input.localizedEvenCumuleneEndpointCursorFrame?_sound
      (input.localizedRule3CumulatedTraversalFuel
        input.certified.input.molecule.atomCount)
      (input.localizedEvenAxialFirstChildOccurrence
        input.certified.input.molecule.atomCount axis)
      frame evenComputed,
    initial, rightward, rightPresent, rightPartnerPresent, rightPrevious⟩

/-- Every perceived canonical open even cumulene is accepted by the production even-endpoint
constructor at atom-count carrier depth, with an independently sound endpoint frame. -/
theorem exists_localizedEvenCumuleneEndpointCursorFrame_at_atomCount
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain) :
    ∃ frame,
      input.localizedEvenCumuleneEndpointCursorFrame?
          (input.localizedRule3CumulatedTraversalFuel
            input.certified.input.molecule.atomCount)
          (input.localizedEvenAxialFirstChildOccurrence
            input.certified.input.molecule.atomCount axis) = some frame ∧
      input.DeclarativeLocalizedEvenCumuleneEndpointCursorFrame
        (input.localizedEvenAxialFirstChildOccurrence
          input.certified.input.molecule.atomCount axis) frame := by
  obtain ⟨frame, _embedding, computed, derived, _initial, _rightward,
      _rightPresent, _rightPartnerPresent, _rightPrevious⟩ :=
    input.exists_localizedEvenCumuleneEndpointCursorFrameWithEmbedding_at_atomCount axis
  exact ⟨frame, computed, derived⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
