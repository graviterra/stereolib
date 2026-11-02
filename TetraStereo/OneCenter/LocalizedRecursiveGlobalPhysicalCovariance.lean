import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport
import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness
import TetraStereo.OneCenter.LocalizedCyclicPhysicalBranchReaderTransport
import TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance
import TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-!
# Root-changing recursive physical covariance

The accepted recursive transport induction normally fixes its source root so that one rooted
physical domain can calibrate both source and image centers.  This adapter instead accepts
calibrated coordinates at every detected center.  That lets a molecular automorphism move the root
while retaining the same recursive proof for actual pseudo occurrences.
-/

namespace TetraStereo.OneCenter.LocalizedRecursiveGlobalPhysicalCovariance

noncomputable section

open TetraStereo.OneCenter
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport
open TetraStereo.OneCenter.LocalizedCyclicGeneralRigidPriority
open TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance
open TetraStereo.OneCenter.LocalizedCyclicPhysicalBranchReaderTransport
open TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport
open TetraStereo.OneCenter.LocalizedCyclicPhysicalStageTransport
open TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
open TetraStereo.OneCenter.AcyclicCutBranchAutomorphism
open TetraStereo.OneCenter.LocalizedRetainedMirrorDescriptorCorrectness
open CertifiedLocalizedCIPInput LocalizedRuleMajorReference DeclarativeCIP
open scoped Classical

variable {input : LocalizedRuleMajorReference.Input}
variable {rootTarget : Occurrence input}
  {rootUnit : DetectedOccurrence input.certified.moleculeGraph}
  {rootTargetUnit : input.certified.molecularFrameUnit rootTarget.1 = rootUnit.1}

/-- One recursive step with calibrated source and image coordinates supplied at every detected
center. Unlike the rooted-domain adapter, the graph automorphism may move the source root. -/
theorem law_step_allCenters
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (rootFrames.stages i).a.key.constitutional.rule1a
      (rootFrames.stages j).a.key.constitutional.rule1a = .eq)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (calibrated : ∀ center : input.certified.detectedMultiCenterMolecule.Center,
      ActualPhysicalCalibratedCoordinates input.certified
        input.certified.detectedMultiCenterMolecule cfg center)
    (e : input.certified.moleculeGraph.Aut) (mirror : Bool)
    (start : input.certified.LocalizedRerootCursor (carrierFuel input))
    (startReach : Relation.ReflTransGen (CertifiedLocalizedCIPInput.E input.certified)
      (rootFrames.frame.cursorAt i) start)
    (signLaw : SignLawFrom e cfg mirror start)
    (target : Occurrence input) (reach : ReachFrom start target)
    (ih : ∀ z, input.certified.LocalizedDepthDependency z target → ReachFrom start z →
      Law singleBonded e mirror z) :
    Law singleBonded e mirror target := by
  obtain ⟨cursor, cursorEq, fromStart⟩ := reach
  have reachable := startReach.trans fromStart
  obtain ⟨⟨previous, previousEq, shorter⟩, inside, nonroot, rooted⟩ :=
    cursor_facts rootFrames rootAddress rootReal i cursor reachable
  rw [cursorEq] at shorter inside nonroot rooted
  by_cases real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom
  swap
  · have source := referenceState_none_of_not_real input target real
    have image := referenceState_none_of_not_real input
      (input.certified.transportOccurrence singleBonded e target) (by
        rw [input.certified.transportOccurrence_provenance singleBonded e target]
        exact real)
    unfold Law
    rw [source, image]
    rfl
  by_cases detected : IsDetectedCenter input.certified.moleculeGraph
      (input.certified.molecularFrameUnit target.1).atom
  swap
  · obtain ⟨source, image⟩ :=
      LocalizedCyclicPhysicalBranchReaderTransport.realNondetected_state_transport_none input
        singleBonded e target real detected
    unfold Law
    rw [source, image]
    rfl
  let unit : DetectedOccurrence input.certified.moleculeGraph :=
    ⟨input.certified.molecularFrameUnit target.1, detected⟩
  let frames := cyclicContextFrameCompilation input singleBonded target real unit rfl
  have centerMeaning := (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff target
    frames.center).mp frames.centerComputed
  have cursorReal : cursor.occurrence.1.node.provenance = .realAtom := by
    rw [cursorEq]
    exact real
  have signAtCenter := signLaw cursor fromStart cursorReal
    (input.certified.physicalSourceCenter frames.center)
    (by rw [cursorEq]; exact centerMeaning.2)
  have imageUnitEq := transportOccurrence_unit input singleBonded e target unit rfl
  have imageReal := transportOccurrence_real input singleBonded e target real
  let imageFrames := cyclicContextFrameCompilation input singleBonded
    (input.certified.transportOccurrence singleBonded e target) imageReal
    (input.certified.transportDetectedOccurrence e unit) imageUnitEq
  by_cases twin : ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule frames.center
  · have rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root := by
      rw [← rooted]
      exact (input.certified.moleculeGraph.mem_tetrahedralCenterSet rootFrames.center.1).mp
        rootFrames.center.2
    have sourceNone := twinState_none input singleBonded target real unit rfl rootTetrahedral twin
    have imageTwin : ActualPhysicalTerminalTwinCenter input.certified
        input.certified.detectedMultiCenterMolecule imageFrames.center := by
      rw [image_center singleBonded e frames imageFrames]
      exact LocalizedCyclicPhysicalTerminalTwinTransport.actualPhysicalTerminalTwinCenter_transport
        (input.certified.physicalDetectedAut e) twin
    have imageRootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter
        (input.certified.transportOccurrence singleBonded e target).1.root := by
      rw [input.certified.transportOccurrence_root]
      exact (input.certified.moleculeGraph.isTetrahedralCenter_apply_aut_iff
        e target.1.root).mpr rootTetrahedral
    have imageNone := twinState_none input singleBonded
      (input.certified.transportOccurrence singleBonded e target) imageReal
      (input.certified.transportDetectedOccurrence e unit) imageUnitEq imageRootTetrahedral imageTwin
    unfold Law
    rw [sourceNone, imageNone]
    rfl
  obtain ⟨sourcePointAt, sourceObserved, _sourceNonzero, sourceSign⟩ := calibrated frames.center
  obtain ⟨imagePointAt, imageObserved, _imageNonzero, imageSign⟩ := calibrated imageFrames.center
  let framesW : ContextFrameCompilation input target unit rfl :=
    { frames with
      W := max frames.W imageFrames.W
      D := max frames.D imageFrames.D
      widthBound := fun k => (frames.widthBound k).trans (le_max_left _ _)
      depthBound := fun k => (frames.depthBound k).trans (le_max_left _ _) }
  let imageFramesW : ContextFrameCompilation input
      (input.certified.transportOccurrence singleBonded e target)
      (input.certified.transportDetectedOccurrence e unit) imageUnitEq :=
    { imageFrames with
      W := max frames.W imageFrames.W
      D := max frames.D imageFrames.D
      widthBound := fun k => (imageFrames.widthBound k).trans (le_max_right _ _)
      depthBound := fun k => (imageFrames.depthBound k).trans (le_max_right _ _) }
  have realI := (rootFrame_cursor_facts singleBonded rootFrames rootAddress rootReal i).1
  have realJ := (rootFrame_cursor_facts singleBonded rootFrames rootAddress rootReal j).1
  have armDistinct : (rootFrames.frame.cursorAt i).occurrence ≠
      (rootFrames.frame.cursorAt j).occurrence := by
    intro same
    have currents := congrArg
      (fun occurrence : Occurrence input => occurrence.1.node.current?) same
    simp only at currents
    rw [rootFrames.ligandAt i, rootFrames.ligandAt j] at currents
    exact distinct (rootFrames.detectedLigandPermutation.injective
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt_injective rootFrames.center
        (Option.some.inj currents)))
  have oldI := (input.certified.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized
    (contextOccurrenceRead input rootTarget) _ _).symm.trans (rootFrames.stages i).a.built
  have oldJ := (input.certified.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized
    (contextOccurrenceRead input rootTarget) _ _).symm.trans (rootFrames.stages j).a.built
  obtain ⟨parent, _parentClass, others⟩ :=
    parentSlot_separated_of_rootArmRule1aTie input.certified singleBonded
      { occurrence := rootTarget, previous? := none } rootAddress
      (rootFrames.frame.cursorAt i) (rootFrames.frame.cursorAt j) (rootFrames.childAt i)
      (rootFrames.childAt j) armDistinct realI realJ (contextOccurrenceRead input rootTarget)
      (contextOccurrenceRead input rootTarget) (rootFrames.stages i).a.key
      (rootFrames.stages j).a.key oldI oldJ tie target real inside framesW.frame
      (LocalizedCyclicGeneralRigidGeneratedLabels.frame_computed framesW) nonroot
  have outwardReads : ∀ slot, slot ≠ parent →
      ReadsAgree input.certified.moleculeGraph e (descriptorMap input)
        (mirroredMap input.certified.moleculeGraph mirror (descriptorMap input)) unit
        (framesW.canonicalCutGraphs singleBonded slot) := by
    intro slot ne
    have outSlot := (others slot ne).1
    have deeperSlot : target.1.address.length <
        (framesW.frame.cursorAt slot).occurrence.1.address.length := by
      obtain ⟨k, addressEq⟩ := outSlot
      rw [addressEq]
      simp
    have step : CertifiedLocalizedCIPInput.E input.certified cursor
        (framesW.frame.cursorAt slot) :=
      frame_outward_mem_children singleBonded framesW cursor cursorEq previous previousEq
        shorter outSlot
    have armReads : ReadsAgree input.certified.moleculeGraph e (descriptorMap input)
        (mirroredMap input.certified.moleculeGraph mirror (descriptorMap input)) unit
        (framesW.actualArmGraphs slot) := by
      intro node steps occ _nodeReal ancestors context
      obtain ⟨source, sourceReach, sourceUnit⟩ :=
        actualArm_read_source singleBonded framesW slot node steps occ ancestors context
      have dependency := (input.certified.outward_reachable_dependency target
        (framesW.frame.cursorAt slot) source (framesW.childAt slot) deeperSlot sourceReach).1
      have sourceRoot : ReachFrom start source.occurrence :=
        ⟨source, rfl, (fromStart.tail step).trans sourceReach⟩
      exact covariant_of_law singleBonded e mirror source.occurrence occ sourceUnit
        (ih source.occurrence dependency sourceRoot)
    let iso : RootedDigraph.Iso (framesW.canonicalCutGraphs singleBonded slot)
        (framesW.actualArmGraphs slot) :=
      Classical.choice (framesW.canonicalLigandCut singleBonded slot).faithful
    exact readsAgree_of_iso e (descriptorMap input)
      (mirroredMap input.certified.moleculeGraph mirror (descriptorMap input)) unit iso.symm armReads
  have sourceAvailable : ∀ slot, framesW.actualCoordinates slot =
      some (sourcePointAt (framesW.detectedLigandPermutation slot)) := fun slot =>
    sourceObserved _
  have imageFramesW_center : imageFramesW.center = imageFrames.center := rfl
  have imageCenterEq := image_center singleBonded e framesW imageFramesW
  have imageAvailable : ∀ slot, imageFramesW.actualCoordinates slot =
      some (imagePointAt (imageFramesW.detectedLigandPermutation slot)) := by
    intro slot
    show input.certified.spatialPointAt?
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt imageFramesW.center
        (imageFramesW.detectedLigandPermutation slot)) = _
    rw [imageFramesW_center]
    exact imageObserved _
  have imageSign' : rationalVolumeSign (slotVolume imagePointAt) =
      input.certified.detectedMultiCenterMolecule.configurationSign cfg imageFramesW.center := by
    rw [imageFramesW_center]
    exact imageSign
  have sign := slotVolume_sign_of_calibrated singleBonded e framesW imageFramesW cfg mirror
    signAtCenter sourcePointAt imagePointAt sourceSign imageSign'
  exact law_of_calibrated singleBonded e mirror framesW imageFramesW rfl rfl parent
    (fun slot ne => (others slot ne).2) outwardReads _ _ sourceAvailable imageAvailable sign

/-- Recursive transport from a branch cursor, with a graph automorphism that may move the
physical root. -/
theorem law_of_reachFrom_allCenters
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootFrames : ContextFrameCompilation input rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = .realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (rootFrames.stages i).a.key.constitutional.rule1a
      (rootFrames.stages j).a.key.constitutional.rule1a = .eq)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (calibrated : ∀ center : input.certified.detectedMultiCenterMolecule.Center,
      ActualPhysicalCalibratedCoordinates input.certified
        input.certified.detectedMultiCenterMolecule cfg center)
    (e : input.certified.moleculeGraph.Aut) (mirror : Bool)
    (start : input.certified.LocalizedRerootCursor (carrierFuel input))
    (startReach : Relation.ReflTransGen (CertifiedLocalizedCIPInput.E input.certified)
      (rootFrames.frame.cursorAt i) start)
    (signLaw : SignLawFrom e cfg mirror start)
    (target : Occurrence input) (reach : ReachFrom start target) :
    Law singleBonded e mirror target := by
  have main : ∀ z, ReachFrom start z → Law singleBonded e mirror z := by
    intro z
    refine @WellFounded.induction _ _
      (input.certified.localizedDepthDependency_wellFounded (carrierFuel input))
      (fun z => ReachFrom start z → Law singleBonded e mirror z) z ?_
    intro z ih reachZ
    exact law_step_allCenters singleBonded rootFrames rootAddress rootReal distinct tie cfg
      calibrated e mirror start startReach signLaw z reachZ
      (fun w dependency reachW => ih w dependency reachW)
  exact main target reach

end
end TetraStereo.OneCenter.LocalizedRecursiveGlobalPhysicalCovariance

assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveGlobalPhysicalCovariance.law_step_allCenters
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveGlobalPhysicalCovariance.law_of_reachFrom_allCenters
