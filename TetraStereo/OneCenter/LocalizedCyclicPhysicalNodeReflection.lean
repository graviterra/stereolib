import TetraStereo.OneCenter.LocalizedCyclicRootArmReachability
import TetraStereo.OneCenter.LocalizedCyclicPhysicalBranchReaderTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

/-! Physical mirror covariance of the generated state at a real detected occurrence
inside an actual constitutionally tied root arm. The actual arm build equations,
rigid calibration and terminal-twin cases supply the state values. -/

namespace TetraStereo.OneCenter.LocalizedCyclicPhysicalNodeReflection

open CertifiedLocalizedCIPInput LocalizedRuleMajorReference DeclarativeCIP
open LocalizedCyclicMatchedReadingPhysicalTransport
open LocalizedCyclicPhysicalBranchReaderTransport RootedTetrahedralBranchSymmetry

noncomputable section

variable {input : LocalizedRuleMajorReference.Input}
  {target : Occurrence input}
  {rootUnit : DetectedOccurrence input.certified.moleculeGraph}
  {targetUnit : input.certified.molecularFrameUnit target.1 = rootUnit.1}

/-- All real detected nodes are either refused terminal twins or actual uppercase
states whose letters swap under the physical mirror. The comparison premise is the
actual Rule-1a arm comparison; its physical derivation is supplied by stage transport. -/
theorem state_mirror_of_actualRootArmRule1aTie
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (frames : ContextFrameCompilation input target rootUnit targetUnit)
    (rootAddress : target.1.address = [])
    (real : target.1.node.provenance = .realAtom)
    {i j : Fin 4} (distinct : i ≠ j)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg frames.center)
    (e : input.certified.moleculeGraph.Aut)
    (transport : input.certified.DetectedBranchTransport e cfg frames.center
      (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j) true)
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (frames.stages i).a.key.constitutional.rule1a
      (frames.stages j).a.key.constitutional.rule1a = .eq)
    (occurrence : Occurrence input)
    (occurrenceReal : occurrence.1.node.provenance = .realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (unitEq : input.certified.molecularFrameUnit occurrence.1 = unit.1)
    (inside : input.certified.RootBranchContains (frames.frame.cursorAt i).occurrence occurrence)
    (nonroot : occurrence.1.address ≠ [])
    (rooted : frames.center.1 = occurrence.1.root)
    (reached : LigandBranchReaches input.certified.detectedMultiCenterMolecule frames.center
      (frames.detectedLigandPermutation i) unit.1.atom) :
    (referenceState input occurrence = none ∧
      referenceState input (input.certified.transportOccurrence singleBonded e occurrence) = none) ∨
      ∃ raw : RS, referenceState input occurrence = some (.chiral raw) ∧
        referenceState input (input.certified.transportOccurrence singleBonded e occurrence) =
          some (.chiral (RS.swap raw)) := by
  let occurrenceFrames := cyclicContextFrameCompilation input singleBonded occurrence
    occurrenceReal unit unitEq
  by_cases twin : ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule occurrenceFrames.center
  · exact Or.inl (terminalTwin_state_transport_none input singleBonded cfg frames.center
      domain e _ _ true transport occurrence occurrenceReal unit unitEq rooted twin)
  · have realI := (rootFrame_cursor_facts singleBonded frames rootAddress real i).1
    have realJ := (rootFrame_cursor_facts singleBonded frames rootAddress real j).1
    have armDistinct : (frames.frame.cursorAt i).occurrence ≠
        (frames.frame.cursorAt j).occurrence := by
      intro same
      have currents := congrArg
        (fun occurrence : Occurrence input => occurrence.1.node.current?) same
      simp only at currents
      rw [frames.ligandAt i, frames.ligandAt j] at currents
      exact distinct (frames.detectedLigandPermutation.injective
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt_injective frames.center
          (Option.some.inj currents)))
    have oldI := (input.certified.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized
      (contextOccurrenceRead input target) _ _).symm.trans (frames.stages i).a.built
    have oldJ := (input.certified.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized
      (contextOccurrenceRead input target) _ _).symm.trans (frames.stages j).a.built
    have centerReached : LigandBranchReaches input.certified.detectedMultiCenterMolecule
        frames.center (frames.detectedLigandPermutation i) occurrenceFrames.center.1 := by
      rw [occurrenceFrames.centerEq]
      exact reached
    obtain ⟨sourceRaw, imageRaw, source, image, swapped⟩ :=
      realDetected_state_transport_of_tiedRootArm input singleBonded charge
        { occurrence := target, previous? := none } rootAddress
        (frames.frame.cursorAt i) (frames.frame.cursorAt j) (frames.childAt i) (frames.childAt j)
        armDistinct realI realJ (contextOccurrenceRead input target) (contextOccurrenceRead input target)
        (frames.stages i).a.key (frames.stages j).a.key oldI oldJ tie cfg frames.center domain e
        (frames.detectedLigandPermutation i) (frames.detectedLigandPermutation j) true transport
        occurrence occurrenceReal unit unitEq inside nonroot rooted twin centerReached
    refine Or.inr ⟨sourceRaw, source, ?_⟩
    simpa only [Bool.true_eq, ↓reduceIte, swapped] using image

end
end TetraStereo.OneCenter.LocalizedCyclicPhysicalNodeReflection

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPhysicalNodeReflection.state_mirror_of_actualRootArmRule1aTie
