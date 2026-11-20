import TetraStereo.OneCenter.LocalizedChemicalRingSourceCutWindows
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual deep priorities at one source-only molecular window.
The common window removes the need to transport a compiled or sibling-selected bound through
the cut isomorphism. Only the node and parent carrier identities remain for that transport.
The actual joint marker is unchanged, with its own layout held fixed.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedUniformCutPrior

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedMarkedRetainedVirtualTarget LocalizedMarkedRetainedCanonicalFrame
open LocalizedMarkedRetainedCanonicalMarker (nodeSource)
open LocalizedRetainedSourceCutFrames LocalizedChemicalRingSourceCutWindows
open LocalizedChemicalRingJointPreparedDeepCutPrior
open LocalizedChemicalRingJointMarkerKey LocalizedCumulativeDecoratedTree

noncomputable section

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
  (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))

/-- The molecular-cut prior at the same source-only window throughout the molecule.
No compiled data, child enumeration, or fallback key is used in this definition. -/
def uniformSourceDeepKey
    (parent child : input.LocalizedRerootCursor (retainedCarrierFuel input)) :
    CompleteLigandRule5Key :=
  retainedCompleteLigandRule5KeyAt input.moleculeGraph
    (cutMap descriptorMap target.1.address.length) (parentUnit parent)
    (sourceChildCut input single parent child)
    (allCutWidth input.moleculeGraph) (allCutDepth input.moleculeGraph)

/-- Actual sibling order and ties equal the uniform molecular-cut comparison.
Coverage and source admissibility are derived from the actual child relation. -/
theorem deepKey_orderAgrees_uniformSource
    (fallback : CompleteLigandRule5Key)
    (parent left right : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (leftMember : left ∈ input.executableLocalizedRerootChildren parent)
    (rightMember : right ∈ input.executableLocalizedRerootChildren parent) :
    OrderAgrees (deepKey descriptorMap target fallback parent left)
      (deepKey descriptorMap target fallback parent right)
      (uniformSourceDeepKey input single descriptorMap target parent left)
      (uniformSourceDeepKey input single descriptorMap target parent right) := by
  have actual := deepKey_orderAgrees_sourceDeepKey input single descriptorMap target fallback
    parent left right leftMember rightMember
  simp only [sourceDeepKey, if_pos leftMember, if_pos rightMember] at actual
  have uniform := prior_orderAgrees_allCutWindow input.moleculeGraph
    (cutMap descriptorMap target.1.address.length) (parentUnit parent)
    left.occurrence.1.root right.occurrence.1.root
    (input.occurrenceCarrierNode single left.occurrence)
    (input.occurrenceCarrierNode single parent.occurrence)
    (input.occurrenceCarrierNode single right.occurrence)
    (input.occurrenceCarrierNode single parent.occurrence)
    (sourceCutAdmissible_of_executableChild input single parent left leftMember)
    (sourceCutAdmissible_of_executableChild input single parent right rightMember)
    (sourceParentWindow_covers input single parent left leftMember)
    (sourceParentWindow_covers input single parent right rightMember)
  exact ⟨actual.1.trans uniform.1, actual.2.trans uniform.2⟩

/-- Structural node/parent cursors supply the molecular-cut prior; no stage keys or windows
are retained. The cut-isomorphism bridge can replace those two cursors by molecular carriers. -/
def uniformSourcePrior
    (tree : LocalizedCumulativeDecoratedTree input (retainedCarrierFuel input))
    (node : (ruleMajorTreeGraph tree).Node) : CompleteLigandRule5Key :=
  uniformSourceDeepKey input single descriptorMap target
    (parentSource tree node) (nodeSource input tree node)

/-- Every actual joint marker is the marker with uniformly windowed molecular-cut priorities.
This is an equality, with all sibling comparison agreements derived. -/
theorem jointMarkerKey_eq_uniformSource
    (fallback : CompleteLigandRule5Key)
    (tree : LocalizedCumulativeDecoratedTree input (retainedCarrierFuel input))
    {read : input.LocalizedRerootCursor (retainedCarrierFuel input) →
      Option LocalizedAuxiliaryLabel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (marks : (ruleMajorTreeGraph tree).Node → List Nat) (W D n : Nat)
    (node : (ruleMajorTreeGraph tree).Node) :
    jointMarkerKey (ruleMajorTreeGraph tree) (deepPrior descriptorMap target fallback tree)
        marks W D n node =
      jointMarkerKey (ruleMajorTreeGraph tree)
        (uniformSourcePrior input single descriptorMap target tree) marks W D n node := by
  apply LocalizedChemicalRingJointMarkerPriorOrderCongruence.jointMarkerKey_eq_of_sibling_order
  intro parent left right leftEdge rightEdge
  unfold deepPrior uniformSourcePrior
  rw [parentSource_of_child tree leftEdge, parentSource_of_child tree rightEdge]
  exact deepKey_orderAgrees_uniformSource input single descriptorMap target fallback
    (nodeSource input tree parent) (nodeSource input tree left) (nodeSource input tree right)
    (child_edge tree realizes leftEdge) (child_edge tree realizes rightEdge)

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedUniformCutPrior

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedUniformCutPrior.deepKey_orderAgrees_uniformSource
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedUniformCutPrior.jointMarkerKey_eq_uniformSource

assert_closure_excludes
  TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedUniformCutPrior.uniformSourceDeepKey
  [TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalFrame.childStages,
   TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalFrame.parentWidth,
   TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalFrame.parentDepth,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextArm,
   TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.buildJoint?]
