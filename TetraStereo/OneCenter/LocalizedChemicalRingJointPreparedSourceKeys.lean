import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCompiledSourceMarker
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! Complete source-cut comparison keys for the prepared ring evaluator.
The specification uses molecular cuts, a candidate descriptor map and ordered references.
Its ordinary window is a molecular maximum; its marker layout is an explicit parameter.
The refinement proves agreement of actual comparisons, including ties, and successful sorting.
No generated-label meaning or chemical reference-policy claim is made here.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceKeys

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open DeclarativeCIP.RetainedOccurrenceCarrier
open LocalizedRetainedSourceCutFrames LocalizedChemicalRingSourceCutWindows
open LocalizedChemicalRingSourceCutMarker
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedVirtualTarget
open LocalizedChemicalRingJointMarkerRanking LocalizedChemicalRingJointMarkerOperations
open LocalizedChemicalRingJointPreparedCompiledSourceMarker

noncomputable section
open scoped Classical

/-- Complete source key: ordinary molecular priority, then the joint ordered-reference marker.
The candidate map is cut at the target path length for the internal marker priorities. -/
def sourceCutKey {Atom : Type} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : OccurrenceUnit Atom) (root : Atom) (focus incoming : CarrierNode Atom)
    (references : List Atom) (W D : Nat) : RefinedKey :=
  toLex (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit
      (sourceCutArm molecule root focus incoming) (allCutWidth molecule) (allCutDepth molecule),
    sourceCutMarker molecule root
      (fun query => if unit.path.length < query.1.path.length then descriptorMap query else none)
      focus incoming references W D)

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)

/-- Source keys in a molecular four-ligand frame, without a frame compilation or raw state. -/
def sourceKeys (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (references : List input.Atom) (W D : Nat) (slot : Fin 4) : RefinedKey :=
  sourceCutKey input.moleculeGraph descriptorMap (input.molecularFrameUnit target.1)
    (frame.cursorAt slot).occurrence.1.root
    (input.occurrenceCarrierNode single (frame.cursorAt slot).occurrence)
    (input.occurrenceCarrierNode single target) references W D

private theorem complete_compare_eq_of_orderAgrees
    {a b c d : CompleteLigandRule5Key} (agrees : OrderAgrees a b c d) :
    compare a b = compare c d := by
  cases actual : compare a b with
  | lt =>
      exact ((completeLigandRule5Key_compare_lt_iff c d).mpr
        (agrees.1.mp ((completeLigandRule5Key_compare_lt_iff a b).mp actual))).symm
  | eq =>
      exact ((completeLigandRule5Key_compare_eq_iff c d).mpr
        (agrees.2.mp ((completeLigandRule5Key_compare_eq_iff a b).mp actual))).symm
  | gt =>
      exact ((cmp_gt_iff compare completeLigandRule5Key_compare_lt_iff
        completeLigandRule5Key_compare_eq_iff c d).mpr
        (agrees.symm_args.1.mp ((cmp_gt_iff compare completeLigandRule5Key_compare_lt_iff
          completeLigandRule5Key_compare_eq_iff a b).mp actual))).symm

variable (state : OccurrenceAuxState)
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.1 = unit.1)

private def slotCut (slot : Fin 4) : RootedDigraph input.Atom :=
  let frame := rawStateFrames input single state target real unit targetUnit
  sourceCutArm input.moleculeGraph (frame.frame.cursorAt slot).occurrence.1.root
    (input.occurrenceCarrierNode single (frame.frame.cursorAt slot).occurrence)
    (input.occurrenceCarrierNode single target)

private theorem slotCut_iso (slot : Fin 4) :
    Nonempty (RootedDigraph.Iso (slotCut input single state target real unit targetUnit slot)
      ((rawStateFrames input single state target real unit targetUnit).actualArmGraphs slot)) := by
  let frame := rawStateFrames input single state target real unit targetUnit
  obtain ⟨_previous, focus, incoming, anchor, focusEq, incomingEq, faithful⟩ :=
    input.executableChild_retainedContextArmFaithful_of_carrierFuel single
      ⟨target, none⟩ (frame.frame.cursorAt slot) (frame.childAt slot) (frame.stages slot).a
  have sourceEq := sourceCutArm_eq input.moleculeGraph
    (frame.frame.cursorAt slot).occurrence.1.root anchor
  rw [focusEq, incomingEq] at sourceEq
  change Nonempty (RootedDigraph.Iso
    (sourceCutArm input.moleculeGraph (frame.frame.cursorAt slot).occurrence.1.root
      (input.occurrenceCarrierNode single (frame.frame.cursorAt slot).occurrence)
      (input.occurrenceCarrierNode single target)) (ruleMajorTreeGraph (frame.stages slot).a.tree))
  rw [sourceEq]
  exact faithful

/-- The actual ordinary priority compares exactly as the source cut at the global molecular
window. The source window and all cut correspondences are derived, including ring slots. -/
theorem ordinary_compare_eq_source (left right : Fin 4) :
    compare (rawStateKeys input single state target real unit targetUnit left)
        (rawStateKeys input single state target real unit targetUnit right) =
      compare
        (retainedCompleteLigandRule5KeyAt input.moleculeGraph (rawStateDescriptorMap input state)
          unit (slotCut input single state target real unit targetUnit left)
          (allCutWidth input.moleculeGraph) (allCutDepth input.moleculeGraph))
        (retainedCompleteLigandRule5KeyAt input.moleculeGraph (rawStateDescriptorMap input state)
          unit (slotCut input single state target real unit targetUnit right)
          (allCutWidth input.moleculeGraph) (allCutDepth input.moleculeGraph)) := by
  let frame := rawStateFrames input single state target real unit targetUnit
  let iso (slot : Fin 4) := Classical.choice
    (slotCut_iso input single state target real unit targetUnit slot)
  have cover (slot : Fin 4) :
      WindowCovers (slotCut input single state target real unit targetUnit slot) frame.W frame.D :=
    LocalizedRecursiveAuxiliarySourceWindows.windowCovers_of_iso (iso slot)
      ⟨(frame.stages slot).a_width_le.trans (frame.widthBound slot),
        (frame.stages slot).a_depth_le.trans (frame.depthBound slot)⟩
  have admitted (slot : Fin 4) := sourceCutAdmissible_of_executableChild input single
    ⟨target, none⟩ (frame.frame.cursorAt slot) (frame.childAt slot)
  have agrees := prior_orderAgrees_allCutWindow input.moleculeGraph
    (rawStateDescriptorMap input state) unit
    (frame.frame.cursorAt left).occurrence.1.root
    (frame.frame.cursorAt right).occurrence.1.root
    (input.occurrenceCarrierNode single (frame.frame.cursorAt left).occurrence)
    (input.occurrenceCarrierNode single target)
    (input.occurrenceCarrierNode single (frame.frame.cursorAt right).occurrence)
    (input.occurrenceCarrierNode single target)
    (admitted left) (admitted right) (cover left) (cover right)
  change compare
    (retainedCompleteLigandRule5KeyAt input.moleculeGraph (rawStateDescriptorMap input state)
      unit (frame.actualArmGraphs left) frame.W frame.D)
    (retainedCompleteLigandRule5KeyAt input.moleculeGraph (rawStateDescriptorMap input state)
      unit (frame.actualArmGraphs right) frame.W frame.D) = _
  rw [retainedCompleteLigandRule5KeyAt_iso input.moleculeGraph (rawStateDescriptorMap input state)
      unit (iso left),
    retainedCompleteLigandRule5KeyAt_iso input.moleculeGraph (rawStateDescriptorMap input state)
      unit (iso right)]
  exact complete_compare_eq_of_orderAgrees agrees

variable (references : List input.Atom) (W D : Nat)

/-- Every actual joint comparison, including equality, is the source-key comparison. -/
theorem refined_compare_eq_source (left right : Fin 4) :
    compare (refinedKey input single state target real unit targetUnit references W D left)
        (refinedKey input single state target real unit targetUnit references W D right) =
      compare
        (sourceKeys input single (rawStateDescriptorMap input state) target
          (rawStateFrames input single state target real unit targetUnit).frame references W D left)
        (sourceKeys input single (rawStateDescriptorMap input state) target
          (rawStateFrames input single state target real unit targetUnit).frame references W D right) := by
  have pathLength : unit.1.path.length = target.1.address.length := by
    rw [← targetUnit]
    exact frameUnit_path_length target
  unfold refinedKey sourceKeys sourceCutKey
  rw [targetUnit]
  change (compare (rawStateKeys input single state target real unit targetUnit left)
    (rawStateKeys input single state target real unit targetUnit right)).then
      (compare _ _) = (compare _ _).then (compare _ _)
  rw [ordinary_compare_eq_source input single state target real unit targetUnit left right,
    compiled_marker_eq_sourceCutMarker input single state target real unit targetUnit references W D left,
    compiled_marker_eq_sourceCutMarker input single state target real unit targetUnit references W D right]
  simp only [pathLength]
  rfl

/-- Actual callback success and exact source priority are derived for every slot pair. -/
theorem jointBefore_eq_source (left right : Fin 4) :
    jointBefore input state target
        (rawStateFrames input single state target real unit targetUnit).frame
        references W D left right =
      some (compare
        (sourceKeys input single (rawStateDescriptorMap input state) target
          (rawStateFrames input single state target real unit targetUnit).frame references W D left)
        (sourceKeys input single (rawStateDescriptorMap input state) target
          (rawStateFrames input single state target real unit targetUnit).frame references W D right)) := by
  rw [jointBefore_eq_refined input single state target real unit targetUnit references W D,
    refined_compare_eq_source input single state target real unit targetUnit references W D]

/-- The actual sort returns the descending source-key order, without assuming sort success. -/
theorem joint_sort_eq_source :
    sortBy? (jointBefore input state target
        (rawStateFrames input single state target real unit targetUnit).frame references W D)
        (List.finRange 4) =
      some (keyOrder (sourceKeys input single (rawStateDescriptorMap input state) target
        (rawStateFrames input single state target real unit targetUnit).frame references W D)
        (List.finRange 4)) :=
  sortBy?_eq_keyOrder compare refined_compare_lt_iff _ _ _
    (jointBefore_eq_source input single state target real unit targetUnit references W D)

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceKeys

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceKeys.ordinary_compare_eq_source
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceKeys.refined_compare_eq_source
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceKeys.jointBefore_eq_source
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceKeys.joint_sort_eq_source

assert_closure_excludes TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceKeys.sourceKeys
  [TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages,
   TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextArm,
   TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.buildJoint?,
   TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState,
   TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.rawStateFrames]
