import TetraStereo.OneCenter.LocalizedChemicalRingActualGraphRelabel
import TetraStereo.OneCenter.LocalizedChemicalRingStateTransport
import TetraStereo.OneCenter.LocalizedMarkedRetainedMolecularRule5
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-! Relabelling of actual retained Rules-1–5 comparisons. The source graphs are the actual
recursive expansions; their relabelling is constructed, and descriptor-map agreement is the
proved transport of the retained reader. Intermediate context atoms need not be stereocenters. -/

namespace TetraStereo.OneCenter.LocalizedChemicalRingRetainedKeyTransport

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree LocalizedChemicalRingActualGraphRelabel
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedMolecularRule5

variable (input : CertifiedLocalizedCIPInput)

theorem readsAgree_transport (e : input.moleculeGraph.Aut)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : OccurrenceUnit input.Atom) (graph : RootedDigraph input.Atom) :
    ReadsAgree input.moleculeGraph e (input.transportDescriptorMap e descriptorMap)
      descriptorMap unit graph := by
  intro _ _ occ _ _ _
  exact input.transportDescriptorMap_transportDetected e descriptorMap occ

theorem completeKey_relabel (e : input.moleculeGraph.Aut)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : OccurrenceUnit input.Atom) {left right : RootedDigraph input.Atom}
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (rel : RootedDigraph.Relabel (e : Equiv.Perm input.Atom) left right) (W D : Nat) :
    retainedCompleteLigandRule5KeyAt input.moleculeGraph
      (input.transportDescriptorMap e descriptorMap) (mapOccurrence (e : Equiv.Perm input.Atom) unit)
      right W D = retainedCompleteLigandRule5KeyAt input.moleculeGraph descriptorMap unit left W D := by
  unfold retainedCompleteLigandRule5KeyAt
  rw [retainedCompleteLigandPriorKeyAt_relabel input.moleculeGraph unit e parentUnique
    _ _ (readsAgree_transport input e descriptorMap unit left) rel,
    retainedCompleteRule5ReadingsAt_relabel input.moleculeGraph unit e parentUnique
    _ _ (readsAgree_transport input e descriptorMap unit left) rel]

theorem realized_completeKey_relabel (single : input.moleculeGraph.SimpleBonded)
    (e : input.moleculeGraph.Aut)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : OccurrenceUnit input.Atom) {fuel : Nat}
    {readL readR : input.LocalizedRerootCursor fuel → Option LocalizedAuxiliaryLabel}
    {left right : LocalizedCumulativeDecoratedTree input fuel}
    (realL : LocalizedCumulativeTreeRealizes input readL left)
    (realR : LocalizedCumulativeTreeRealizes input readR right)
    (same : input.transportCursor single e left.source = right.source)
    (aligned : input.cursorPreviousRootAligned left.source) (W D : Nat) :
    retainedCompleteLigandRule5KeyAt input.moleculeGraph
      (input.transportDescriptorMap e descriptorMap) (mapOccurrence (e : Equiv.Perm input.Atom) unit)
      (ruleMajorTreeGraph right) W D =
    retainedCompleteLigandRule5KeyAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph left) W D := by
  obtain ⟨rel⟩ := realized_graph_relabel single e realL realR same aligned
  exact completeKey_relabel input e descriptorMap unit
    (fun _ _ _ ha hb => (toOfficialSourceTree left).declarativeAddressing.parent_unique ha hb) rel W D

theorem transportedMap_tetrahedral (e : input.moleculeGraph.Aut)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetra : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral) :
    ∀ unit value, input.transportDescriptorMap e descriptorMap unit = some value → value.IsTetrahedral := by
  intro unit value observed
  exact tetra _ value observed

/-- Actual complete ordinary comparison is invariant under molecular relabelling and the
corresponding transported descriptor map. All six stage graphs and a common finite window
are constructed inside the proof; no canonical ordering or key equality is a premise. -/
theorem actual_pair_ordering_transport (single : input.moleculeGraph.SimpleBonded)
    (e : input.moleculeGraph.Aut)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetra : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (parent left right : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (aligned : input.cursorPreviousRootAligned parent)
    (childL : left ∈ input.executableLocalizedRerootChildren parent)
    (childR : right ∈ input.executableLocalizedRerootChildren parent)
    (a b a' b' : input.LocalizedRerootCompoundRule45Key)
    (ha : input.buildActualRuleMajorCompoundRule45KeyExec? parent.occurrence
      (input.molecularView descriptorMap parent.occurrence) (2 * (retainedCarrierFuel input + 1)) left = some a)
    (hb : input.buildActualRuleMajorCompoundRule45KeyExec? parent.occurrence
      (input.molecularView descriptorMap parent.occurrence) (2 * (retainedCarrierFuel input + 1)) right = some b)
    (ha' : input.buildActualRuleMajorCompoundRule45KeyExec? (input.transportOccurrence single e parent.occurrence)
      (input.molecularView (input.transportDescriptorMap e descriptorMap)
        (input.transportOccurrence single e parent.occurrence))
      (2 * (retainedCarrierFuel input + 1)) (input.transportCursor single e left) = some a')
    (hb' : input.buildActualRuleMajorCompoundRule45KeyExec? (input.transportOccurrence single e parent.occurrence)
      (input.molecularView (input.transportDescriptorMap e descriptorMap)
        (input.transportOccurrence single e parent.occurrence))
      (2 * (retainedCarrierFuel input + 1)) (input.transportCursor single e right) = some b') :
    (input.compareLocalizedRerootCompoundThroughRule5 a' b').ordering =
      (input.compareLocalizedRerootCompoundThroughRule5 a b).ordering := by
  let imageMap := input.transportDescriptorMap e descriptorMap
  let parent' := input.transportCursor single e parent
  have childL' : input.transportCursor single e left ∈ input.executableLocalizedRerootChildren parent' :=
    (input.executableLocalizedRerootChildren_transport_mem_iff single e aligned left).mp childL
  have childR' : input.transportCursor single e right ∈ input.executableLocalizedRerootChildren parent' :=
    (input.executableLocalizedRerootChildren_transport_mem_iff single e aligned right).mp childR
  obtain ⟨sL⟩ := input.exists_ruleMajorContextStages_at_actualChild _
    (input.localizedDependencyLabel parent.occurrence (input.molecularView descriptorMap parent.occurrence))
    parent left childL
  obtain ⟨sR⟩ := input.exists_ruleMajorContextStages_at_actualChild _
    (input.localizedDependencyLabel parent.occurrence (input.molecularView descriptorMap parent.occurrence))
    parent right childR
  obtain ⟨sL'⟩ := input.exists_ruleMajorContextStages_at_actualChild _
    (input.localizedDependencyLabel parent'.occurrence (input.molecularView imageMap parent'.occurrence))
    parent' (input.transportCursor single e left) childL'
  obtain ⟨sR'⟩ := input.exists_ruleMajorContextStages_at_actualChild _
    (input.localizedDependencyLabel parent'.occurrence (input.molecularView imageMap parent'.occurrence))
    parent' (input.transportCursor single e right) childR'
  let W := max (max sL.widthBound sR.widthBound) (max sL'.widthBound sR'.widthBound)
  let D := max (max sL.depthBound sR.depthBound) (max sL'.depthBound sR'.depthBound)
  have wl : sL.widthBound ≤ W := by dsimp [W]; omega
  have wr : sR.widthBound ≤ W := by dsimp [W]; omega
  have wl' : sL'.widthBound ≤ W := by dsimp [W]; omega
  have wr' : sR'.widthBound ≤ W := by dsimp [W]; omega
  have dl : sL.depthBound ≤ D := by dsimp [D]; omega
  have dr : sR.depthBound ≤ D := by dsimp [D]; omega
  have dl' : sL'.depthBound ≤ D := by dsimp [D]; omega
  have dr' : sR'.depthBound ≤ D := by dsimp [D]; omega
  have original := (retainedMolecularCompound_throughRule5 descriptorMap tetra single parent
    (input.molecularFrameUnit parent.occurrence.1) rfl left right childL childR sL sR
    wl dl wr dr ha hb).1
  have image := (retainedMolecularCompound_throughRule5 imageMap
    (transportedMap_tetrahedral input e descriptorMap tetra) single parent'
    (input.molecularFrameUnit parent'.occurrence.1) rfl _ _ childL' childR' sL' sR'
    wl' dl' wr' dr' ha' hb').1
  have unitEq : input.molecularFrameUnit parent'.occurrence.1 =
      mapOccurrence (e : Equiv.Perm input.Atom) (input.molecularFrameUnit parent.occurrence.1) := by
    exact input.molecularFrameUnit_transport single e parent.occurrence
  have keyL := realized_completeKey_relabel input single e descriptorMap
    (input.molecularFrameUnit parent.occurrence.1)
    (LocalizedRuleMajorSortTrace.realizes_of_trace sL.a.trace)
    (LocalizedRuleMajorSortTrace.realizes_of_trace sL'.a.trace)
    (by rw [sL.a.sourceEq, sL'.a.sourceEq])
    (by rw [sL.a.sourceEq]; exact input.executableLocalizedRerootChildren_cursorAligned parent left childL) W D
  have keyR := realized_completeKey_relabel input single e descriptorMap
    (input.molecularFrameUnit parent.occurrence.1)
    (LocalizedRuleMajorSortTrace.realizes_of_trace sR.a.trace)
    (LocalizedRuleMajorSortTrace.realizes_of_trace sR'.a.trace)
    (by rw [sR.a.sourceEq, sR'.a.sourceEq])
    (by rw [sR.a.sourceEq]; exact input.executableLocalizedRerootChildren_cursorAligned parent right childR) W D
  rw [unitEq, keyL, keyR] at image
  exact image.trans original.symm

end TetraStereo.OneCenter.LocalizedChemicalRingRetainedKeyTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRetainedKeyTransport.readsAgree_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRetainedKeyTransport.realized_completeKey_relabel
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRetainedKeyTransport.actual_pair_ordering_transport
