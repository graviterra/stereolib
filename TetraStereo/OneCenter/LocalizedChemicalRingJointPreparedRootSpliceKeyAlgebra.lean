import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootArmLocality
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPriorMirrorKey
import TetraStereo.OneCenter.DeclarativeCIPRetainedWindowIndependence
import TetraStereo.OneCenter.LocalizedMarkedRetainedFuelSaturation
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Common-window assembly for the original/mirror splice. Actual stage graphs are
isomorphic across auxiliary states; their independently chosen window bounds need not agree.
The only locality inputs concern each arm separately at a fixed window. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSpliceKeyAlgebra

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData)
open LocalizedChemicalRingJointPreparedRootArmLocality

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node)

theorem frame_graph_iso (first second : OccurrenceAuxState) (slot : Fin 4) :
    Nonempty (RootedDigraph.Iso
      ((rootFrame input mol single c node data first).actualArmGraphs slot)
      ((rootFrame input mol single c node data second).actualArmGraphs slot)) := by
  apply LocalizedMarkedRetainedFuelSaturation.graphIso_of_sameSource_crossFuel input _ _ _ _ _ _
    ((rootFrame input mol single c node data first).stages slot).a.trace
    ((rootFrame input mol single c node data second).stages slot).a.trace
  rw [((rootFrame input mol single c node data first).stages slot).a.sourceEq,
    ((rootFrame input mol single c node data second).stages slot).a.sourceEq,
    rootFrame_eq, rootFrame_eq]

theorem frame_cover (state : OccurrenceAuxState) (slot : Fin 4) :
    WindowCovers ((rootFrame input mol single c node data state).actualArmGraphs slot)
      (rootFrame input mol single c node data state).W
      (rootFrame input mol single c node data state).D :=
  ⟨(((rootFrame input mol single c node data state).stages slot).a_width_le).trans
      ((rootFrame input mol single c node data state).widthBound slot),
    (((rootFrame input mol single c node data state).stages slot).a_depth_le).trans
      ((rootFrame input mol single c node data state).depthBound slot)⟩

/-- A distinct original prior tie becomes a full tie in a state that reads the original
map on the left arm and its reflection on the right arm. Locality is per-arm, not global. -/
theorem rawKeys_eq_of_arm_locality (original spliced : OccurrenceAuxState) (left right : Fin 4)
    (priorTie : (ofLex (rawStateKeys input single original data.target data.real
        ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl left)).1 =
      (ofLex (rawStateKeys input single original data.target data.real
        ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl right)).1)
    (different : rawStateKeys input single original data.target data.real
        ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl left ≠
      rawStateKeys input single original data.target data.real
        ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl right)
    (localLeft : ∀ W D,
      retainedCompleteLigandRule5KeyAt input.moleculeGraph (rawStateDescriptorMap input spliced)
        (input.molecularFrameUnit data.target.1)
        ((rootFrame input mol single c node data spliced).actualArmGraphs left) W D =
      retainedCompleteLigandRule5KeyAt input.moleculeGraph (rawStateDescriptorMap input original)
        (input.molecularFrameUnit data.target.1)
        ((rootFrame input mol single c node data spliced).actualArmGraphs left) W D)
    (localRight : ∀ W D,
      retainedCompleteLigandRule5KeyAt input.moleculeGraph (rawStateDescriptorMap input spliced)
        (input.molecularFrameUnit data.target.1)
        ((rootFrame input mol single c node data spliced).actualArmGraphs right) W D =
      retainedCompleteLigandRule5KeyAt input.moleculeGraph
        (rawStateDescriptorMap input original).reflect
        (input.molecularFrameUnit data.target.1)
        ((rootFrame input mol single c node data spliced).actualArmGraphs right) W D) :
    rawStateKeys input single spliced data.target data.real
        ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl left =
      rawStateKeys input single spliced data.target data.real
        ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl right := by
  let unit : DetectedOccurrence input.moleculeGraph :=
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩
  let first := rootFrame input mol single c node data original
  let second := rootFrame input mol single c node data spliced
  let W := max first.W second.W
  let D := max first.D second.D
  obtain ⟨isoLeft⟩ := frame_graph_iso input mol single c node data original spliced left
  obtain ⟨isoRight⟩ := frame_graph_iso input mol single c node data original spliced right
  have sourceWindow := retainedCompleteLigandRule5KeyAt_orderAgrees_window input.moleculeGraph
    (rawStateDescriptorMap input original) unit
    (frame_cover input mol single c node data original left)
    (windowCovers_mono (frame_cover input mol single c node data original left)
      (show first.W ≤ W from Nat.le_max_left _ _) (show first.D ≤ D from Nat.le_max_left _ _))
    (frame_cover input mol single c node data original right)
    (windowCovers_mono (frame_cover input mol single c node data original right)
      (show first.W ≤ W from Nat.le_max_left _ _) (show first.D ≤ D from Nat.le_max_left _ _))
  have targetWindow := retainedCompleteLigandRule5KeyAt_orderAgrees_window input.moleculeGraph
    (rawStateDescriptorMap input spliced) unit
    (frame_cover input mol single c node data spliced left)
    (windowCovers_mono (frame_cover input mol single c node data spliced left)
      (show second.W ≤ W from Nat.le_max_right _ _) (show second.D ≤ D from Nat.le_max_right _ _))
    (frame_cover input mol single c node data spliced right)
    (windowCovers_mono (frame_cover input mol single c node data spliced right)
      (show second.W ≤ W from Nat.le_max_right _ _) (show second.D ≤ D from Nat.le_max_right _ _))
  have commonPrior := sourceWindow.2.2.mp priorTie
  have commonDifferent := fun equal => different (sourceWindow.1.2.mpr equal)
  have cross := LocalizedChemicalRingJointPreparedPriorMirrorKey.original_left_eq_reflected_right_of_distinct_prior_tie
    input.moleculeGraph (rawStateDescriptorMap input original) unit
    (first.actualArmGraphs left) (first.actualArmGraphs right) W D commonPrior commonDifferent
  apply targetWindow.1.2.mpr
  calc
    retainedCompleteLigandRule5KeyAt input.moleculeGraph (rawStateDescriptorMap input spliced)
        unit (second.actualArmGraphs left) W D =
      retainedCompleteLigandRule5KeyAt input.moleculeGraph (rawStateDescriptorMap input original)
        unit (second.actualArmGraphs left) W D := localLeft W D
    _ = retainedCompleteLigandRule5KeyAt input.moleculeGraph (rawStateDescriptorMap input original)
        unit (first.actualArmGraphs left) W D :=
      retainedCompleteLigandRule5KeyAt_iso input.moleculeGraph _ unit isoLeft W D
    _ = retainedCompleteLigandRule5KeyAt input.moleculeGraph
        (rawStateDescriptorMap input original).reflect unit (first.actualArmGraphs right) W D := cross
    _ = retainedCompleteLigandRule5KeyAt input.moleculeGraph
        (rawStateDescriptorMap input original).reflect unit (second.actualArmGraphs right) W D :=
      (retainedCompleteLigandRule5KeyAt_iso input.moleculeGraph _ unit isoRight W D).symm
    _ = retainedCompleteLigandRule5KeyAt input.moleculeGraph (rawStateDescriptorMap input spliced)
        unit (second.actualArmGraphs right) W D := (localRight W D).symm

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSpliceKeyAlgebra

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSpliceKeyAlgebra.frame_graph_iso
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSpliceKeyAlgebra.frame_cover
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSpliceKeyAlgebra.rawKeys_eq_of_arm_locality
