import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerPriorOrderCongruence
import TetraStereo.OneCenter.LocalizedChemicalRingAnyParentWindowIndependence
import TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalFrame
import TetraStereo.OneCenter.LocalizedRetainedSourceCutFrames
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-! Deep joint priorities from molecular predecessor cuts.
The source keys and their common sibling windows use only carrier nodes, source cuts,
and a candidate descriptor map. No stage tree or compiled window occurs in those definitions.
The bridge derives their sibling order agreement with the actual deep priors; it applies
at every internal parent, whether or not that parent is a detected stereocenter.
This removes compilation from the deep-prior construction, not from the whole auxiliary model.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDeepCutPrior

open CertifiedLocalizedCIPInput DeclarativeCIP
open Rule4aTableBridge
open DeclarativeCIP.RetainedOccurrenceCarrier DeclarativeCIP.RetainedCutArm
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedMarkedRetainedCanonicalFrame
open LocalizedMarkedRetainedCanonicalMarker
open LocalizedMarkedRetainedVirtualTarget
open LocalizedRetainedSourceCutFrames
open LocalizedChemicalRingJointMarkerKey
open LocalizedCumulativeDecoratedTree
open scoped Classical
noncomputable section

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)

/-- The molecular predecessor cut for a child of any retained parent. -/
def sourceChildCut (parent child : input.LocalizedRerootCursor (retainedCarrierFuel input)) :
    RootedDigraph input.Atom :=
  sourceCutArm input.moleculeGraph child.occurrence.1.root
    (input.occurrenceCarrierNode single child.occurrence)
    (input.occurrenceCarrierNode single parent.occurrence)

/-- Common native windows of the molecular child cuts. -/
def sourceParentWidth (parent : input.LocalizedRerootCursor (retainedCarrierFuel input)) : Nat :=
  ((input.executableLocalizedRerootChildren parent).map
    (fun child => (sourceChildCut input single parent child).width)).foldr max 0

def sourceParentDepth (parent : input.LocalizedRerootCursor (retainedCarrierFuel input)) : Nat :=
  ((input.executableLocalizedRerootChildren parent).map
    (fun child => (sourceChildCut input single parent child).height)).foldr max 0

theorem sourceParentWindow_covers
    (parent child : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (member : child ∈ input.executableLocalizedRerootChildren parent) :
    WindowCovers (sourceChildCut input single parent child)
      (sourceParentWidth input single parent) (sourceParentDepth input single parent) :=
  ⟨le_foldr_max (List.mem_map_of_mem member), le_foldr_max (List.mem_map_of_mem member)⟩

variable (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (fallback : CompleteLigandRule5Key)

/-- Source deep prior, with candidate reads restricted to strict descendants of the target.
The arbitrary root fallback is not used in any sibling comparison. -/
def sourceDeepKey (parent child : input.LocalizedRerootCursor (retainedCarrierFuel input)) :
    CompleteLigandRule5Key :=
  if child ∈ input.executableLocalizedRerootChildren parent then
    retainedCompleteLigandRule5KeyAt input.moleculeGraph
      (cutMap descriptorMap target.1.address.length) (parentUnit parent)
      (sourceChildCut input single parent child)
      (sourceParentWidth input single parent) (sourceParentDepth input single parent)
  else fallback

/-- The actual child-stage representation is faithful to the molecular cut; all focus
and incoming-node identities are derived from the executable child relation. -/
theorem childStages_sourceCut_iso
    (parent child : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (member : child ∈ input.executableLocalizedRerootChildren parent) :
    Nonempty (RootedDigraph.Iso (sourceChildCut input single parent child)
      (ruleMajorTreeGraph (childStages descriptorMap target parent child member).a.tree)) := by
  obtain ⟨_previous, focus, incoming, anchor, focusEq, incomingEq, faithful⟩ :=
    input.executableChild_retainedContextArmFaithful_of_carrierFuel single parent child member
      (childStages descriptorMap target parent child member).a
  have sourceEq := sourceCutArm_eq input.moleculeGraph child.occurrence.1.root anchor
  rw [focusEq, incomingEq] at sourceEq
  rw [sourceChildCut, sourceEq]
  exact faithful

/-- Actual deep priors and source-cut priors agree on strict comparisons AND ties.
No comparator agreement, successful sorting, or auxiliary-label correctness is assumed. -/
theorem deepKey_orderAgrees_sourceDeepKey
    (parent left right : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (leftMember : left ∈ input.executableLocalizedRerootChildren parent)
    (rightMember : right ∈ input.executableLocalizedRerootChildren parent) :
    OrderAgrees
      (deepKey descriptorMap target fallback parent left)
      (deepKey descriptorMap target fallback parent right)
      (sourceDeepKey input single descriptorMap target fallback parent left)
      (sourceDeepKey input single descriptorMap target fallback parent right) := by
  let isoL := Classical.choice
    (childStages_sourceCut_iso input single descriptorMap target parent left leftMember)
  let isoR := Classical.choice
    (childStages_sourceCut_iso input single descriptorMap target parent right rightMember)
  have leftCover : WindowCovers (sourceChildCut input single parent left)
      (parentWidth descriptorMap target parent) (parentDepth descriptorMap target parent) :=
    LocalizedRecursiveAuxiliarySourceWindows.windowCovers_of_iso isoL
      ⟨(childStages descriptorMap target parent left leftMember).a_width_le.trans
          (childStages_width_le descriptorMap target parent left leftMember),
        (childStages descriptorMap target parent left leftMember).a_depth_le.trans
          (childStages_depth_le descriptorMap target parent left leftMember)⟩
  have rightCover : WindowCovers (sourceChildCut input single parent right)
      (parentWidth descriptorMap target parent) (parentDepth descriptorMap target parent) :=
    LocalizedRecursiveAuxiliarySourceWindows.windowCovers_of_iso isoR
      ⟨(childStages descriptorMap target parent right rightMember).a_width_le.trans
          (childStages_width_le descriptorMap target parent right rightMember),
        (childStages descriptorMap target parent right rightMember).a_depth_le.trans
          (childStages_depth_le descriptorMap target parent right rightMember)⟩
  simp only [deepKey, sourceDeepKey, dif_pos leftMember, dif_pos rightMember,
    if_pos leftMember, if_pos rightMember]
  rw [retainedCompleteLigandRule5KeyAt_iso input.moleculeGraph
      (cutMap descriptorMap target.1.address.length) (parentUnit parent) isoL,
    retainedCompleteLigandRule5KeyAt_iso input.moleculeGraph
      (cutMap descriptorMap target.1.address.length) (parentUnit parent) isoR]
  exact (LocalizedChemicalRingAnyParentWindowIndependence.retainedCompleteLigandRule5KeyAt_orderAgrees_window
    input.moleculeGraph (cutMap descriptorMap target.1.address.length) (parentUnit parent)
    leftCover (sourceParentWindow_covers input single parent left leftMember)
    rightCover (sourceParentWindow_covers input single parent right rightMember)).1

/-- The source-cut prior at a represented node; the surrounding tree supplies only its
structural parent and source cursor, not a compiled child key or observation window. -/
def sourceDeepPrior (tree : LocalizedCumulativeDecoratedTree input (retainedCarrierFuel input))
    (node : (ruleMajorTreeGraph tree).Node) : CompleteLigandRule5Key :=
  sourceDeepKey input single descriptorMap target fallback
    (parentSource tree node) (nodeSource input tree node)

/-- The actual deep-prior marker equals the source-cut-prior marker at every node.
Sibling order agreement is derived rather than supplied, including at noncenter parents. -/
theorem jointMarkerKey_deepPrior_eq_source
    (tree : LocalizedCumulativeDecoratedTree input (retainedCarrierFuel input))
    {read : input.LocalizedRerootCursor (retainedCarrierFuel input) → Option LocalizedAuxiliaryLabel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (marks : (ruleMajorTreeGraph tree).Node → List Nat) (W D n : Nat)
    (node : (ruleMajorTreeGraph tree).Node) :
    jointMarkerKey (ruleMajorTreeGraph tree) (deepPrior descriptorMap target fallback tree)
        marks W D n node =
      jointMarkerKey (ruleMajorTreeGraph tree)
        (sourceDeepPrior input single descriptorMap target fallback tree) marks W D n node := by
  apply LocalizedChemicalRingJointMarkerPriorOrderCongruence.jointMarkerKey_eq_of_sibling_order
  intro parent left right leftEdge rightEdge
  unfold deepPrior sourceDeepPrior
  rw [parentSource_of_child tree leftEdge, parentSource_of_child tree rightEdge]
  exact deepKey_orderAgrees_sourceDeepKey input single descriptorMap target fallback
    (nodeSource input tree parent) (nodeSource input tree left) (nodeSource input tree right)
    (child_edge tree realizes leftEdge) (child_edge tree realizes rightEdge)

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDeepCutPrior

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDeepCutPrior.sourceParentWindow_covers
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDeepCutPrior.childStages_sourceCut_iso
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDeepCutPrior.deepKey_orderAgrees_sourceDeepKey
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDeepCutPrior.jointMarkerKey_deepPrior_eq_source

assert_closure_excludes
  TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDeepCutPrior.sourceDeepKey
  [TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalFrame.childStages,
   TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalFrame.parentWidth,
   TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalFrame.parentDepth,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextArm,
   TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.buildJoint?]
