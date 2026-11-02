import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport
import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain
import TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-!
# Root-changing covariance of actual complete outcomes

This adapter transports the actual complete root outcome under a molecular automorphism that can
move the root. Its only reader premise is agreement on all four retained root cuts. The recursive
fixture adapter supplies that four-cut agreement by the all-occurrence transport induction.
-/

namespace TetraStereo.OneCenter.LocalizedRecursiveGlobalRootCovariance

noncomputable section

open TetraStereo.OneCenter
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport
open TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance
open TetraStereo.OneCenter.LocalizedCyclicPhysicalStageTransport
open TetraStereo.OneCenter.LocalizedRetainedMirrorDescriptorCorrectness
open TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
open TetraStereo.OneCenter.AcyclicCutBranchAutomorphism
open CertifiedLocalizedCIPInput LocalizedRuleMajorReference DeclarativeCIP
open DeclarativeCIP.RetainedOccurrenceCarrier DeclarativeCIP.RetainedCutArm
open DeclarativeCIP.RetainedCutAutomorphism
open scoped Classical

variable {input : LocalizedRuleMajorReference.Input}

/-- Transport the actual root's complete Rule-5 outcome when every retained cut read is
covariant. The physical sign law is supplied as the exact four-slot volume equation. -/
theorem referenceState_transport_of_rootCutReads
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    {target : Occurrence input} {unit : DetectedOccurrence input.certified.moleculeGraph}
    {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}
    (frames : ContextFrameCompilation input target unit targetUnit)
    (e : input.certified.moleculeGraph.Aut) (mirror : Bool)
    (imageFrames : ContextFrameCompilation input
      (input.certified.transportOccurrence singleBonded e target)
      (input.certified.transportDetectedOccurrence e unit)
      (transportOccurrence_unit input singleBonded e target unit targetUnit))
    (sameW : imageFrames.W = frames.W) (sameD : imageFrames.D = frames.D)
    (reads : ∀ slot, ReadsAgree input.certified.moleculeGraph e (descriptorMap input)
      (mirroredMap input.certified.moleculeGraph mirror (descriptorMap input)) unit
      (frames.canonicalCutGraphs singleBonded slot))
    (sourcePoints imagePoints : Fin 4 → CartesianPoint3)
    (sourceAvailable : ∀ slot, frames.actualCoordinates slot = some (sourcePoints slot))
    (imageAvailable : ∀ slot, imageFrames.actualCoordinates slot = some (imagePoints slot))
    (sign : rationalVolumeSign (slotVolume imagePoints) =
      physicalMirrorFactor mirror * permHandedness (slotTransport singleBonded e frames).slotPerm *
        rationalVolumeSign (slotVolume sourcePoints)) :
    referenceState input (input.certified.transportOccurrence singleBonded e target) =
      (referenceState input target).map (retainedPhysicalLetter mirror) := by
  have sourceActual : CompleteRootOutcome
      (fun slot => retainedCompleteLigandRule5KeyAt input.certified.moleculeGraph
        (descriptorMap input) unit (frames.canonicalCutGraphs singleBonded slot)
        frames.W frames.D) sourcePoints (referenceState input target) := by
    have outcome := frames.referenceState_canonicalCutOutcome singleBonded
    unfold retainedCutArmOutcome at outcome
    exact (retainedContextualOutcomeAt_iff_completeRootOutcome input.certified.moleculeGraph
      (descriptorMap input) unit (frames.canonicalCutGraphs singleBonded) frames.W frames.D
      sourceAvailable _).1 outcome
  have transported := (cuts_completeRootOutcome_transport input.certified.moleculeGraph e mirror
    (slotTransport singleBonded e frames).slotPerm
    (descriptorMap input) (descriptorMap input) unit
    (fun slot => (frames.frame.cursorAt slot).occurrence.1.root)
    (fun slot => (frames.canonicalLigandCut singleBonded slot).focus)
    (fun slot => some (frames.canonicalLigandCut singleBonded slot).incoming)
    (fun slot => (frames.canonicalLigandCut singleBonded slot).anchor)
    reads sourcePoints imagePoints frames.W frames.D (referenceState input target) sign).2 sourceActual
  let σ := (slotTransport singleBonded e frames).slotPerm
  have imageKeys : (fun slot => retainedCompleteLigandRule5KeyAt input.certified.moleculeGraph
      (descriptorMap input) (mapDetected input.certified.moleculeGraph e unit)
      (cutRetainedArm input.certified.moleculeGraph
        ((e : Equiv.Perm input.certified.Atom)
          (frames.frame.cursorAt (σ⁻¹ slot)).occurrence.1.root)
        (imageNode e (frames.canonicalLigandCut singleBonded (σ⁻¹ slot)).focus)
        ((some (frames.canonicalLigandCut singleBonded (σ⁻¹ slot)).incoming).map (imageNode e))
        (cutAnchor_image e (frames.canonicalLigandCut singleBonded (σ⁻¹ slot)).focus
          (some (frames.canonicalLigandCut singleBonded (σ⁻¹ slot)).incoming)
          (frames.canonicalLigandCut singleBonded (σ⁻¹ slot)).anchor)) frames.W frames.D) =
    retainedContextualFrameKeysAt input.certified.moleculeGraph (descriptorMap input)
      (input.certified.transportDetectedOccurrence e unit)
      (imageFrames.canonicalCutGraphs singleBonded) imageFrames.W imageFrames.D := by
    funext slot
    have sent : input.certified.transportCursor singleBonded e
        (frames.frame.cursorAt (σ⁻¹ slot)) =
        imageFrames.frame.cursorAt slot := by
      rw [← image_cursorAt singleBonded e frames imageFrames (σ⁻¹ slot)]
      exact congrArg imageFrames.frame.cursorAt (Equiv.apply_symm_apply σ slot)
    rw [mapDetected_eq_transportDetectedOccurrence input.certified e unit, sameW, sameD]
    exact congrArg (fun graph => retainedCompleteLigandRule5KeyAt input.certified.moleculeGraph
      (descriptorMap input) (input.certified.transportDetectedOccurrence e unit) graph
      frames.W frames.D)
      (image_canonicalCut_eq singleBonded e frames imageFrames sent)
  have transported' : CompleteRootOutcome
      (retainedContextualFrameKeysAt input.certified.moleculeGraph (descriptorMap input)
        (input.certified.transportDetectedOccurrence e unit)
        (imageFrames.canonicalCutGraphs singleBonded) imageFrames.W imageFrames.D)
      imagePoints ((referenceState input target).map (retainedPhysicalLetter mirror)) := by
    rw [← imageKeys]
    exact transported
  have imageActual : CompleteRootOutcome
      (retainedContextualFrameKeysAt input.certified.moleculeGraph (descriptorMap input)
        (input.certified.transportDetectedOccurrence e unit)
        (imageFrames.canonicalCutGraphs singleBonded) imageFrames.W imageFrames.D)
      imagePoints (referenceState input (input.certified.transportOccurrence singleBonded e target)) := by
    have outcome := imageFrames.referenceState_canonicalCutOutcome singleBonded
    unfold retainedCutArmOutcome at outcome
    exact (retainedContextualOutcomeAt_iff_completeRootOutcome input.certified.moleculeGraph
      (descriptorMap input) _ (imageFrames.canonicalCutGraphs singleBonded)
      imageFrames.W imageFrames.D imageAvailable _).1 outcome
  exact completeRootOutcome_unique imageActual transported'

end
end TetraStereo.OneCenter.LocalizedRecursiveGlobalRootCovariance

assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveGlobalRootCovariance.referenceState_transport_of_rootCutReads
