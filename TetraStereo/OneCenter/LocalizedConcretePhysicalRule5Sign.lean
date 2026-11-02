import TetraStereo.OneCenter.LocalizedPhysicalRule5PrefixClosure
import TetraStereo.OneCenter.LocalizedConcretePseudoExecution
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false







































namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open RootedTetrahedralBranchSymmetry

noncomputable section

namespace LocalizedConcretePhysicalRule5Sign

open TetraStereo.OneCenter.LocalizedPhysicalDomainNonvacuity
open TetraStereo.Certificate.Dependency

/-! ## A. Actual detected attachments of the two physical arm branches -/




theorem detected_ligandAtomAt_left
    (τ : m.Center → Equiv.Perm (Fin 4))
    (hτ : m.reindexFrames τ = input.certified.detectedMultiCenterMolecule)
    (rootD : input.certified.detectedMultiCenterMolecule.Center)
    (hrootD : rootD = hτ ▸ root) :
    input.certified.detectedMultiCenterMolecule.ligandAtomAt rootD ((τ root)⁻¹ 0) = atom1 := by
  rw [hrootD,
    LocalizedConcretePseudoExecution.reindexFrames_ligandAtomAt_cast τ hτ root ((τ root)⁻¹ 0)]
  have hcancel : (τ root) ((τ root)⁻¹ 0) = 0 := Equiv.apply_symm_apply (τ root) 0
  rw [hcancel]
  exact (ligandAtomAt_root 0).trans rootLigand_zero

/-- The detected ligand atom at the second physical arm slot `(tau root)⁻¹ 1` is the actual second
carbon arm `atom2`. -/
theorem detected_ligandAtomAt_right
    (τ : m.Center → Equiv.Perm (Fin 4))
    (hτ : m.reindexFrames τ = input.certified.detectedMultiCenterMolecule)
    (rootD : input.certified.detectedMultiCenterMolecule.Center)
    (hrootD : rootD = hτ ▸ root) :
    input.certified.detectedMultiCenterMolecule.ligandAtomAt rootD ((τ root)⁻¹ 1) = atom2 := by
  rw [hrootD,
    LocalizedConcretePseudoExecution.reindexFrames_ligandAtomAt_cast τ hτ root ((τ root)⁻¹ 1)]
  have hcancel : (τ root) ((τ root)⁻¹ 1) = 1 := Equiv.apply_symm_apply (τ root) 1
  rw [hcancel]
  exact (ligandAtomAt_root 1).trans rootLigand_one

/-! ## B. The actual physical unique-nearest marks on the detected inventory -/




theorem detected_nearest_branch_zero
    (τ : m.Center → Equiv.Perm (Fin 4))
    (hτ : m.reindexFrames τ = input.certified.detectedMultiCenterMolecule)
    (rootD : input.certified.detectedMultiCenterMolecule.Center)
    (hrootD : rootD = hτ ▸ root) :
    PhysicalBranchUniqueNearest input ⟨rootD.1, rootD.2⟩
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt rootD ((τ root)⁻¹ 0))
      atom1 0 := by
  have hroot :=
    LocalizedConcretePseudoExecution.detectedRoot_center_eq_rootTetrahedral τ hτ rootD hrootD
  have hlig := detected_ligandAtomAt_left τ hτ rootD hrootD
  rw [hroot, hlig]
  exact nearest_branch_zero

/-- **Second carbon arm is the actual unique nearest physical mark on detected branch
`(tau root)⁻¹ 1`, at distance `0`.** -/
theorem detected_nearest_branch_one
    (τ : m.Center → Equiv.Perm (Fin 4))
    (hτ : m.reindexFrames τ = input.certified.detectedMultiCenterMolecule)
    (rootD : input.certified.detectedMultiCenterMolecule.Center)
    (hrootD : rootD = hτ ▸ root) :
    PhysicalBranchUniqueNearest input ⟨rootD.1, rootD.2⟩
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt rootD ((τ root)⁻¹ 1))
      atom2 0 := by
  have hroot :=
    LocalizedConcretePseudoExecution.detectedRoot_center_eq_rootTetrahedral τ hτ rootD hrootD
  have hlig := detected_ligandAtomAt_right τ hτ rootD hrootD
  rw [hroot, hlig]
  exact nearest_branch_one


















theorem actualPair_of_mirrorTransport
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (cfgD : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfgD c)
    (i j : Fin 4)
    (transport : BranchTransport input.certified.detectedMultiCenterMolecule cfgD c i j true)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) center distance) :
    ∃ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (alpha : Equiv.Perm (Fin 4))
      (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
        (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
      (oObservedLeft : (frame.cursorAt (alpha.symm i)).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i))
      (oObservedRight : (frame.cursorAt (alpha.symm j)).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c j))
      (r : RS)
      (leftReading rightReading : input.certified.LocalizedRerootRule5Reading)
      (priorReading : input.certified.LocalizedRerootRule4bcReading)
      (keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key),
      (actualSlotCompoundKey input c frame frameComputed (alpha.symm i)).rule5Readings =
          [leftReading] ∧
        (actualSlotCompoundKey input c frame frameComputed (alpha.symm j)).rule5Readings =
          [rightReading] ∧
        LocalizedRule5SwapAndSignal.MirrorReading input.certified leftReading rightReading ∧
        input.certified.compareLocalizedRerootCompoundRule4bcKeys
            (actualSlotCompoundKey input c frame frameComputed (alpha.symm i)).prior
            (actualSlotCompoundKey input c frame frameComputed (alpha.symm j)).prior =
          Ordering.eq ∧
        (input.certified.compareLocalizedRerootCompoundThroughRule5
            (actualSlotCompoundKey input c frame frameComputed (alpha.symm i))
            (actualSlotCompoundKey input c frame frameComputed (alpha.symm j))).ordering =
          (if r = RS.R then Ordering.gt else Ordering.lt) ∧
        (input.certified.compareLocalizedRerootCompoundThroughRule5
            (actualSlotCompoundKey input c frame frameComputed (alpha.symm i))
            (actualSlotCompoundKey input c frame frameComputed (alpha.symm j))).pseudo = true ∧
        input.certified.buildLocalizedRerootCompoundRule45Key?
            (ActualReaderPhysicalBranchInverse.topTarget input c)
            (referenceDependencyView input c)
            (localizedOccurrenceRerootEvaluationFuel
              (LocalizedUniversalReference.carrierFuel input))
            (frame.cursorAt (alpha.symm i)) =
          some (actualSlotCompoundKey input c frame frameComputed (alpha.symm i)) ∧
        (actualSlotCompoundKey input c frame frameComputed (alpha.symm i)).prior.references =
          [r] ∧
        (actualSlotCompoundKey input c frame frameComputed (alpha.symm i)).prior.readings =
          [priorReading] ∧
        priorReading.reference? = some r ∧
        leftReading.prior = priorReading ∧
        input.certified.buildLocalizedRerootCumulativeRule45Key?
            (localizedRule5StageFor (some r) .R)
            (ActualReaderPhysicalBranchInverse.topTarget input c)
            (referenceDependencyView input c)
            (localizedOccurrenceRerootEvaluationFuel
              (LocalizedUniversalReference.carrierFuel input))
            (frame.cursorAt (alpha.symm i)) = some keyR ∧
        input.certified.buildLocalizedRerootCumulativeRule45Key?
            (localizedRule5StageFor (some r) .S)
            (ActualReaderPhysicalBranchInverse.topTarget input c)
            (referenceDependencyView input c)
            (localizedOccurrenceRerootEvaluationFuel
              (LocalizedUniversalReference.carrierFuel input))
            (frame.cursorAt (alpha.symm i)) = some keyS ∧
        leftReading.commonR = keyR ∧
        leftReading.commonS = keyS ∧
        keyR.labels.length = keyS.labels.length ∧
        (∀ d, d ≤ distance →
          keyR.labels.getD d [] = keyS.labels.getD d []) ∧
        branchMarkedDescriptor input c frame frameComputed (alpha.symm i) simpleBonded acyclic
            (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) oObservedLeft center =
          some r ∧
        LocalizedUniqueNearestRule5Direction.actualTreeMark input simpleBonded acyclic
            (actualSlotTree input c frame frameComputed (alpha.symm i)) center = some r ∧
        OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
            keyR.descriptor keyS.descriptor =
          (if r = RS.R then Ordering.gt else Ordering.lt) ∧
        (∀ e, e < distance →
          LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
            ((keyR.labels.getD e []).map Prod.snd) = []) ∧
        LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
            ((keyR.labels.getD distance []).map Prod.snd) = [r] ∧
        (∃ occurrence : LocalizedUniversalReference.Occurrence input,
          occurrence.1.root = c.1 ∧
            occurrence.1.node.current? = some center ∧
              LocalizedUniversalReference.referenceState input occurrence = some (.chiral r)) :=
  LocalizedPhysicalRule5PrefixClosure.exists_pair_throughRule5_signed_pseudo_of_physicalMirrorTransport_noPrefix
    input simpleBonded acyclic constantFormalCharge input_noDoubleRecords cfgD c domain i j
    transport (center := center) (distance := distance) unique












theorem actualRootPseudo_lowercase
    (τ : m.Center → Equiv.Perm (Fin 4))
    (hτ : m.reindexFrames τ = input.certified.detectedMultiCenterMolecule)
    (cfgD : input.certified.detectedMultiCenterMolecule.Configuration)
    (rootD : input.certified.detectedMultiCenterMolecule.Center)
    (hrootD : rootD = hτ ▸ root)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfgD rootD)
    (distinct : MultiCenterMolecule.PairwiseProperDistinguishable
      input.certified.detectedMultiCenterMolecule cfgD rootD)
    (branch : ∀ i : Fin 4, PhysicalBranchDomain input rootTetrahedral
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt rootD i))
    (count : physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule
      cfgD rootD = 1) :
    (∃ descriptor : LocalizedTetrahedralRSPseudoDescriptor,
        LocalizedUniversalReference.referenceState input
            (ActualReaderPhysicalBranchInverse.topTarget input rootD) = some descriptor ∧
          descriptor.IsLowercase) ∧
      (∀ nodes : LocalizedUniversalReference.Nodes input,
        ∃ descriptor : LocalizedTetrahedralRSPseudoDescriptor,
          lookup
              (LocalizedUniversalReference.evaluate input nodes).facts
              (ActualReaderPhysicalBranchInverse.topTarget input rootD) = some descriptor ∧
            descriptor.IsLowercase) := by
  obtain ⟨plain, evaluate, _production⟩ :=
    LocalizedConcretePseudoExecution.actualPhysicalExecution_of_detectedRoot
      τ hτ cfgD rootD hrootD domain distinct branch
  refine ⟨?_, ?_⟩
  · obtain ⟨descriptor, stateEq, lowercaseIff⟩ := plain
    exact ⟨descriptor, stateEq, lowercaseIff.mpr count⟩
  · intro nodes
    obtain ⟨descriptor, evalEq, lowercaseIff⟩ := evaluate nodes
    exact ⟨descriptor, evalEq, lowercaseIff.mpr count⟩

/-! ## E. The concrete signed fixture: no physical premise left -/



























theorem actualFixture_physicalRule5Signed_pseudo_lowercase :
    ∃ (τ : m.Center → Equiv.Perm (Fin 4))
      (hτ : m.reindexFrames τ = input.certified.detectedMultiCenterMolecule)
      (cfgD : input.certified.detectedMultiCenterMolecule.Configuration)
      (rootD : input.certified.detectedMultiCenterMolecule.Center),
      cfgD = hτ ▸ m.reindexConfiguration τ cfg ∧
      rootD = hτ ▸ root ∧
      ActualGeneralRigidPhysicalDomain input.certified
        input.certified.detectedMultiCenterMolecule cfgD rootD ∧
      MultiCenterMolecule.PairwiseProperDistinguishable
        input.certified.detectedMultiCenterMolecule cfgD rootD ∧
      Enantiomorphic input.certified.detectedMultiCenterMolecule cfgD rootD
        ((τ root)⁻¹ 0) ((τ root)⁻¹ 1) ∧
      (∀ i j : Fin 4,
        Enantiomorphic input.certified.detectedMultiCenterMolecule cfgD rootD i j ↔
          (i = (τ root)⁻¹ 0 ∧ j = (τ root)⁻¹ 1) ∨
            (i = (τ root)⁻¹ 1 ∧ j = (τ root)⁻¹ 0)) ∧
      physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule
        cfgD rootD = 1 ∧
      PairwiseDisjointLigandBranches input.certified.detectedMultiCenterMolecule rootD ∧
      (∀ i : Fin 4, PhysicalBranchDomain input rootTetrahedral
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt rootD i)) ∧
      PhysicalBranchUniqueNearest input ⟨rootD.1, rootD.2⟩
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt rootD ((τ root)⁻¹ 0))
        atom1 0 ∧
      PhysicalBranchUniqueNearest input ⟨rootD.1, rootD.2⟩
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt rootD ((τ root)⁻¹ 1))
        atom2 0 ∧
      (∃ (i j : Fin 4), i = (τ root)⁻¹ 0 ∧ j = (τ root)⁻¹ 1 ∧
        ∃ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
            (LocalizedUniversalReference.carrierFuel input))
          (alpha : Equiv.Perm (Fin 4))
          (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
            (ActualReaderPhysicalBranchInverse.topTarget input rootD) = some frame)
          (oObservedLeft : (frame.cursorAt (alpha.symm i)).occurrence.1.node.current? =
            some (input.certified.detectedMultiCenterMolecule.ligandAtomAt rootD i))
          (oObservedRight : (frame.cursorAt (alpha.symm j)).occurrence.1.node.current? =
            some (input.certified.detectedMultiCenterMolecule.ligandAtomAt rootD j))
          (r : RS)
          (leftReading rightReading : input.certified.LocalizedRerootRule5Reading)
          (priorReading : input.certified.LocalizedRerootRule4bcReading)
          (keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key),
          (actualSlotCompoundKey input rootD frame frameComputed (alpha.symm i)).rule5Readings =
              [leftReading] ∧
            (actualSlotCompoundKey input rootD frame frameComputed (alpha.symm j)).rule5Readings =
              [rightReading] ∧
            LocalizedRule5SwapAndSignal.MirrorReading input.certified leftReading rightReading ∧
            input.certified.compareLocalizedRerootCompoundRule4bcKeys
                (actualSlotCompoundKey input rootD frame frameComputed (alpha.symm i)).prior
                (actualSlotCompoundKey input rootD frame frameComputed (alpha.symm j)).prior =
              Ordering.eq ∧
            (input.certified.compareLocalizedRerootCompoundThroughRule5
                (actualSlotCompoundKey input rootD frame frameComputed (alpha.symm i))
                (actualSlotCompoundKey input rootD frame frameComputed (alpha.symm j))).ordering =
              (if r = RS.R then Ordering.gt else Ordering.lt) ∧
            (input.certified.compareLocalizedRerootCompoundThroughRule5
                (actualSlotCompoundKey input rootD frame frameComputed (alpha.symm i))
                (actualSlotCompoundKey input rootD frame frameComputed (alpha.symm j))).pseudo = true ∧
            input.certified.buildLocalizedRerootCompoundRule45Key?
                (ActualReaderPhysicalBranchInverse.topTarget input rootD)
                (referenceDependencyView input rootD)
                (localizedOccurrenceRerootEvaluationFuel
                  (LocalizedUniversalReference.carrierFuel input))
                (frame.cursorAt (alpha.symm i)) =
              some (actualSlotCompoundKey input rootD frame frameComputed (alpha.symm i)) ∧
            (actualSlotCompoundKey input rootD frame frameComputed (alpha.symm i)).prior.references =
              [r] ∧
            (actualSlotCompoundKey input rootD frame frameComputed (alpha.symm i)).prior.readings =
              [priorReading] ∧
            priorReading.reference? = some r ∧
            leftReading.prior = priorReading ∧
            input.certified.buildLocalizedRerootCumulativeRule45Key?
                (localizedRule5StageFor (some r) .R)
                (ActualReaderPhysicalBranchInverse.topTarget input rootD)
                (referenceDependencyView input rootD)
                (localizedOccurrenceRerootEvaluationFuel
                  (LocalizedUniversalReference.carrierFuel input))
                (frame.cursorAt (alpha.symm i)) = some keyR ∧
            input.certified.buildLocalizedRerootCumulativeRule45Key?
                (localizedRule5StageFor (some r) .S)
                (ActualReaderPhysicalBranchInverse.topTarget input rootD)
                (referenceDependencyView input rootD)
                (localizedOccurrenceRerootEvaluationFuel
                  (LocalizedUniversalReference.carrierFuel input))
                (frame.cursorAt (alpha.symm i)) = some keyS ∧
            leftReading.commonR = keyR ∧
            leftReading.commonS = keyS ∧
            keyR.labels.length = keyS.labels.length ∧
            (∀ d, d ≤ 0 →
              keyR.labels.getD d [] = keyS.labels.getD d []) ∧
            branchMarkedDescriptor input rootD frame frameComputed (alpha.symm i) simpleBonded acyclic
                (input.certified.detectedMultiCenterMolecule.ligandAtomAt rootD i) oObservedLeft atom1 =
              some r ∧
            LocalizedUniqueNearestRule5Direction.actualTreeMark input simpleBonded acyclic
                (actualSlotTree input rootD frame frameComputed (alpha.symm i)) atom1 = some r ∧
            OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
                keyR.descriptor keyS.descriptor =
              (if r = RS.R then Ordering.gt else Ordering.lt) ∧
            (∀ e, e < 0 →
              LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
                ((keyR.labels.getD e []).map Prod.snd) = []) ∧
            LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
                ((keyR.labels.getD 0 []).map Prod.snd) = [r] ∧
            (∃ occurrence : LocalizedUniversalReference.Occurrence input,
              occurrence.1.root = rootD.1 ∧
                occurrence.1.node.current? = some atom1 ∧
                  LocalizedUniversalReference.referenceState input occurrence = some (.chiral r))) ∧
      (∃ descriptor : LocalizedTetrahedralRSPseudoDescriptor,
          LocalizedUniversalReference.referenceState input
              (ActualReaderPhysicalBranchInverse.topTarget input rootD) = some descriptor ∧
            descriptor.IsLowercase) ∧
      (∀ nodes : LocalizedUniversalReference.Nodes input,
        ∃ descriptor : LocalizedTetrahedralRSPseudoDescriptor,
          lookup
              (LocalizedUniversalReference.evaluate input nodes).facts
              (ActualReaderPhysicalBranchInverse.topTarget input rootD) = some descriptor ∧
            descriptor.IsLowercase) := by
  classical
  obtain ⟨τ, hτ, cfgD, rootD, hcfgD, hrootD, domain, distinct, enantiomorphic, classification,
    count, disjoint, branchDomains⟩ :=
    LocalizedPhysicalDomainNonvacuity.detected_physicalWitness_actual
  -- The actual source-branch nearest mark on the detected inventory.
  have uniqueLeft := detected_nearest_branch_zero τ hτ rootD hrootD
  have uniqueRight := detected_nearest_branch_one τ hτ rootD hrootD
  -- The witness mirror transport is the physical `BranchTransport ... true`.
  have transport : BranchTransport input.certified.detectedMultiCenterMolecule cfgD rootD
      ((τ root)⁻¹ 0) ((τ root)⁻¹ 1) true :=
    enantiomorphic.2.1

  have pair := actualPair_of_mirrorTransport rootD cfgD domain ((τ root)⁻¹ 0) ((τ root)⁻¹ 1)
    transport (center := atom1) (distance := 0) uniqueLeft

  have rootOut := actualRootPseudo_lowercase τ hτ cfgD rootD hrootD domain distinct
    branchDomains count
  refine ⟨τ, hτ, cfgD, rootD, hcfgD, hrootD, domain, distinct, enantiomorphic, classification,
    count, disjoint, branchDomains, uniqueLeft, uniqueRight, ?_, rootOut.1, rootOut.2⟩
  exact ⟨(τ root)⁻¹ 0, (τ root)⁻¹ 1, rfl, rfl, pair⟩

end LocalizedConcretePhysicalRule5Sign

end

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only
  TetraStereo.OneCenter.LocalizedConcretePhysicalRule5Sign.detected_ligandAtomAt_left
assert_kernel_only
  TetraStereo.OneCenter.LocalizedConcretePhysicalRule5Sign.detected_ligandAtomAt_right
assert_kernel_only
  TetraStereo.OneCenter.LocalizedConcretePhysicalRule5Sign.detected_nearest_branch_zero
assert_kernel_only
  TetraStereo.OneCenter.LocalizedConcretePhysicalRule5Sign.detected_nearest_branch_one
assert_kernel_only
  TetraStereo.OneCenter.LocalizedConcretePhysicalRule5Sign.actualPair_of_mirrorTransport
assert_kernel_only
  TetraStereo.OneCenter.LocalizedConcretePhysicalRule5Sign.actualRootPseudo_lowercase
assert_kernel_only
  TetraStereo.OneCenter.LocalizedConcretePhysicalRule5Sign.actualFixture_physicalRule5Signed_pseudo_lowercase
