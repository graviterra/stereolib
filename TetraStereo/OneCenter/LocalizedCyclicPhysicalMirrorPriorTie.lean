import TetraStereo.OneCenter.LocalizedCyclicRootPhysicalSetup
import TetraStereo.OneCenter.LocalizedRetainedCutDescriptorTransport
import TetraStereo.OneCenter.LocalizedCyclicPhysicalStageTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

/-! Transport of the actual retained prior comparison along a molecular symmetry.
The intermediate transport lemma isolates the canonical-cut identity; the physical
reader premise is discharged by the cyclic generated-reader bridge. -/

namespace TetraStereo.OneCenter.LocalizedCyclicPhysicalMirrorPriorTie

open CertifiedLocalizedCIPInput LocalizedRuleMajorReference DeclarativeCIP
open DeclarativeCIP.RetainedOccurrenceCarrier DeclarativeCIP.RetainedCutArm
open DeclarativeCIP.RetainedCutAutomorphism
open RootedTetrahedralBranchSymmetry

noncomputable section

/-- A detected molecular automorphism already contains its full chemical graph
automorphism. No loss of bond orders or formal charge occurs in this projection. -/
def detectedGraphAut (input : CertifiedLocalizedCIPInput)
    (e : input.detectedMultiCenterMolecule.Aut) : input.moleculeGraph.Aut :=
  ⟨e.1, e.2.1⟩

theorem physicalDetectedAut_detectedGraphAut (input : CertifiedLocalizedCIPInput)
    (e : input.detectedMultiCenterMolecule.Aut) :
    input.physicalDetectedAut (detectedGraphAut input e) = e :=
  Subtype.ext rfl

/-- Physical branch transport supplies the graph automorphism required by the
actual occurrence transport, with exactly the same physical sign law. -/
theorem exists_detectedBranchTransport_of_branchTransport
    (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (root : input.detectedMultiCenterMolecule.Center) (i j : Fin 4) (mirror : Bool)
    (physical : BranchTransport input.detectedMultiCenterMolecule cfg root i j mirror) :
    ∃ e : input.moleculeGraph.Aut, input.DetectedBranchTransport e cfg root i j mirror := by
  obtain ⟨e, fixed, sent, signs⟩ := physical
  refine ⟨detectedGraphAut input e, ?_⟩
  constructor
  · simpa only [physicalDetectedAut_detectedGraphAut] using fixed
  · simpa only [physicalDetectedAut_detectedGraphAut] using sent
  · simpa only [physicalDetectedAut_detectedGraphAut] using signs

private theorem cut_eq_of_carriers {Atom : Type*} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) {root root' : Atom} (rootEq : root = root')
    (focus : Nodes molecule root) (incoming : Nodes molecule root)
    (anchor : CutAnchor focus (some incoming))
    (focus' : Nodes molecule root') (incoming' : Nodes molecule root')
    (anchor' : CutAnchor focus' (some incoming'))
    (focusEq : focus.1 = focus'.1) (incomingEq : incoming.1 = incoming'.1) :
    cutRetainedArm molecule root focus (some incoming) anchor =
      cutRetainedArm molecule root' focus' (some incoming') anchor' := by
  subst root'
  have hf : focus = focus' := Subtype.ext focusEq
  have hi : incoming = incoming' := Subtype.ext incomingEq
  subst focus'
  subst incoming'
  rfl

variable {input : LocalizedRuleMajorReference.Input}
  {target : Occurrence input}
  {unit : DetectedOccurrence input.certified.moleculeGraph}
  {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}

include targetUnit in
/-- Transport of the target fixes its complete detected unit, including its history. -/
theorem mapDetected_eq_of_target_fixed
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (e : input.certified.moleculeGraph.Aut)
    (fixed : input.certified.transportOccurrence singleBonded e target = target) :
    mapDetected input.certified.moleculeGraph e unit = unit := by
  apply Subtype.ext
  have h := input.certified.molecularFrameUnit_transport singleBonded e target
  rw [fixed, targetUnit] at h
  exact h.symm

/-- The image cut is exactly the canonical cut of the transported frame slot. This
uses complete carrier histories and the actual cursor transport. -/
theorem image_canonicalCut_eq
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (e : input.certified.moleculeGraph.Aut) {i j : Fin 4}
    (fixed : input.certified.transportOccurrence singleBonded e target = target)
    (sent : input.certified.transportCursor singleBonded e (frames.frame.cursorAt i) =
      frames.frame.cursorAt j) :
    cutRetainedArm input.certified.moleculeGraph
        ((e : Equiv.Perm input.certified.Atom) (frames.frame.cursorAt i).occurrence.1.root)
        (imageNode e (frames.canonicalLigandCut singleBonded i).focus)
        ((some (frames.canonicalLigandCut singleBonded i).incoming).map (imageNode e))
        (cutAnchor_image e (frames.canonicalLigandCut singleBonded i).focus
          (some (frames.canonicalLigandCut singleBonded i).incoming)
          (frames.canonicalLigandCut singleBonded i).anchor) =
      frames.canonicalCutGraphs singleBonded j := by
  have occurrenceSent := congrArg (fun c => c.occurrence) sent
  change input.certified.transportOccurrence singleBonded e
    (frames.frame.cursorAt i).occurrence = (frames.frame.cursorAt j).occurrence at occurrenceSent
  have rootSent := congrArg (fun c => c.occurrence.1.root) sent
  change (e : Equiv.Perm input.certified.Atom)
    (frames.frame.cursorAt i).occurrence.1.root =
    (frames.frame.cursorAt j).occurrence.1.root at rootSent
  apply cut_eq_of_carriers input.certified.moleculeGraph rootSent
  · rw [imageNode_carrier, (frames.canonicalLigandCut singleBonded i).focusCarrier,
      (frames.canonicalLigandCut singleBonded j).focusCarrier]
    rw [mapCarrier_eq_mapCarrierNode, input.certified.occurrenceCarrierNode_transport,
      occurrenceSent]
  · rw [imageNode_carrier, (frames.canonicalLigandCut singleBonded i).incomingCarrier,
      (frames.canonicalLigandCut singleBonded j).incomingCarrier]
    rw [mapCarrier_eq_mapCarrierNode, input.certified.occurrenceCarrierNode_transport, fixed]

/-- Actual prior comparison from a reflected reached-reader relation on the canonical
cut and an actual cursor transport. The physical theorem discharges these hypotheses. -/
theorem priorTie_of_readsAgree_and_cursor_transport
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (e : input.certified.moleculeGraph.Aut) {i j : Fin 4}
    (fixed : input.certified.transportOccurrence singleBonded e target = target)
    (sent : input.certified.transportCursor singleBonded e (frames.frame.cursorAt i) =
      frames.frame.cursorAt j)
    (reads : ReadsAgree input.certified.moleculeGraph e (descriptorMap input)
      (descriptorMap input).reflect unit (frames.canonicalCutGraphs singleBonded i)) :
    input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (frames.compounds i).prior (frames.compounds j).prior = .eq := by
  have mirrored := cut_priorKey_mirror e
    (frames.canonicalLigandCut singleBonded i).focus
    (some (frames.canonicalLigandCut singleBonded i).incoming)
    (frames.canonicalLigandCut singleBonded i).anchor
    (descriptorMap input) (descriptorMap input) unit reads frames.W frames.D
  rw [mapDetected_eq_of_target_fixed (targetUnit := targetUnit) singleBonded e fixed,
    image_canonicalCut_eq singleBonded frames e fixed sent] at mirrored
  have keyIso (slot : Fin 4) :=
    retainedCompleteLigandPriorKeyAt_iso input.certified.moleculeGraph
      (descriptorMap input) unit
      (Classical.choice (frames.canonicalLigandCut singleBonded slot).faithful)
      frames.W frames.D
  have tied : (ofLex (frames.retainedKeys i)).1 =
      (ofLex (frames.retainedKeys j)).1 := by
    change retainedCompleteLigandPriorKeyAt input.certified.moleculeGraph
      (descriptorMap input) unit (frames.actualArmGraphs i) frames.W frames.D =
      retainedCompleteLigandPriorKeyAt input.certified.moleculeGraph
      (descriptorMap input) unit (frames.actualArmGraphs j) frames.W frames.D
    exact (keyIso i).trans (mirrored.symm.trans (keyIso j).symm)
  rw [frames.retainedActual_priorComparison singleBonded, tied]
  simp

/-- Physical mirror transport gives an actual prior tie. Generated-reader
reflection and actual target/cursor transport are derived, not supplied. -/
theorem priorTie_of_mirrorTransport
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (frames : ContextFrameCompilation input target unit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = .realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg frames.center)
    (mirror : MirrorTransport input.certified.detectedMultiCenterMolecule cfg frames.center
      (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j)) :
    input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (frames.compounds i).prior (frames.compounds j).prior = .eq := by
  obtain ⟨e, transport⟩ := exists_detectedBranchTransport_of_branchTransport input.certified
    cfg frames.center (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j)
    true mirror
  exact priorTie_of_readsAgree_and_cursor_transport singleBonded frames e
    (LocalizedCyclicRootArmReachability.rootOccurrence_fixed singleBonded frames
      rootAddress real e transport)
    (LocalizedCyclicRootArmReachability.rootSlot_transport singleBonded frames
      rootAddress real e transport)
    (LocalizedCyclicPhysicalStageTransport.canonicalCut_readsAgree_of_actualRootArm
      singleBonded charge frames rootAddress real cfg domain e distinct transport)

open LocalizedCyclicMatchedReadingPhysicalTransport

/-- The physical converse at the evaluator's own final occurrence for a detected
root center. No reader, reference, key tie or comparison law is assumed. -/
theorem finalRoot_priorTie_of_mirrorTransport
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (center : input.certified.TetrahedralCenter) {i j : Fin 4} (distinct : i ≠ j)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg center)
    (mirror : MirrorTransport input.certified.detectedMultiCenterMolecule cfg center
      ((finalRootFrames input singleBonded center).detectedLigandPermutation i)
      ((finalRootFrames input singleBonded center).detectedLigandPermutation j)) :
    input.certified.compareLocalizedRerootCompoundRule4bcKeys
      ((finalRootFrames input singleBonded center).compounds i).prior
      ((finalRootFrames input singleBonded center).compounds j).prior = .eq := by
  have centerEq := finalRootFrames_center input singleBonded center
  apply priorTie_of_mirrorTransport singleBonded charge (finalRootFrames input singleBonded center)
    (input.certified.localizedFinalOccurrenceExecutable_address (carrierFuel input) center)
    (finalOccurrence_provenance_real input center) distinct cfg
  · simpa only [centerEq] using domain
  · simpa only [centerEq] using mirror

end
end TetraStereo.OneCenter.LocalizedCyclicPhysicalMirrorPriorTie

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalMirrorPriorTie.mapDetected_eq_of_target_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalMirrorPriorTie.detectedGraphAut
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalMirrorPriorTie.physicalDetectedAut_detectedGraphAut
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalMirrorPriorTie.exists_detectedBranchTransport_of_branchTransport
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalMirrorPriorTie.image_canonicalCut_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalMirrorPriorTie.priorTie_of_readsAgree_and_cursor_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalMirrorPriorTie.priorTie_of_mirrorTransport
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalMirrorPriorTie.finalRoot_priorTie_of_mirrorTransport
