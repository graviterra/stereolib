import TetraStereo.OneCenter.LocalizedPhysicalRule5SignedExecution
import TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open RootedTetrahedralBranchSymmetry

noncomputable section






















































namespace LocalizedPhysicalRule5PrefixClosure









theorem actualStage_labels_prefix_eq_of_physicalUniqueNearest
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩)
    {oAtom : input.certified.Atom}
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    (own : Option RS)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance)
    {keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key}
    (builtR : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .R)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt slot) = some keyR)
    (builtS : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .S)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt slot) = some keyS) :
    keyR.labels.length = keyS.labels.length ∧
      ∀ d, d ≤ distance →
        keyR.labels.getD d [] = keyS.labels.getD d [] :=
  LocalizedActualNearestStagePrefixCovariance.actualKey_labels_prefix_of_physicalBranchUniqueNearest
    input c frame frameComputed slot singleBonded acyclic hcharge noDouble cfg domain oObserved
    own builtR builtS unique









theorem prefixStable_of_physicalDomain
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩) :
    ∀ (slot' : Fin 4)
      (frame' : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (frameComputed' : input.certified.localizedOccurrenceFourLigandFrame?
        (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame')
      (oAtom' : input.certified.Atom)
      (oObserved' : (frame'.cursorAt slot').occurrence.1.node.current? = some oAtom')
      {center' : input.certified.Atom} {distance' : Nat},
      PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom' center' distance' →
      ∀ (r : RS)
      (keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key),
      input.certified.buildLocalizedRerootCumulativeRule45Key?
        (localizedRule5StageFor (some r) .R)
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (referenceDependencyView input c)
        (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (frame'.cursorAt slot') = some keyR →
      input.certified.buildLocalizedRerootCumulativeRule45Key?
        (localizedRule5StageFor (some r) .S)
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (referenceDependencyView input c)
        (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (frame'.cursorAt slot') = some keyS →
      keyR.labels.length = keyS.labels.length ∧
        ∀ d, d ≤ distance' →
          keyR.labels.getD d [] = keyS.labels.getD d [] := by
  intro slot' frame' frameComputed' oAtom' oObserved' center' distance' unique' r keyR keyS
    builtR builtS
  exact actualStage_labels_prefix_eq_of_physicalUniqueNearest input c frame' frameComputed' slot'
    singleBonded acyclic hcharge noDouble cfg domain oObserved' (some r) unique' builtR builtS

/-! ## C. The physical-atom signed endpoint without the residual premise -/
















theorem exists_actualSlot_compoundReading_stageFor_signed_of_physicalAtom_noPrefix
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (oAtom : input.certified.Atom)
    (adjacent : input.certified.moleculeGraph.Adj c.1 oAtom)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfgPhys : input.certified.detectedMultiCenterMolecule.Configuration)
    (physicalDomain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfgPhys c)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance) :
    ∃ (slot : Fin 4)
      (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
        (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
      (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
      (r : RS)
      (priorReading : input.certified.LocalizedRerootRule4bcReading)
      (reading : input.certified.LocalizedRerootRule5Reading)
      (keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key),
      input.certified.buildLocalizedRerootCompoundRule45Key?
            (ActualReaderPhysicalBranchInverse.topTarget input c)
            (referenceDependencyView input c)
            (localizedOccurrenceRerootEvaluationFuel
              (LocalizedUniversalReference.carrierFuel input))
            (frame.cursorAt slot) =
          some (actualSlotCompoundKey input c frame frameComputed slot) ∧
        (actualSlotCompoundKey input c frame frameComputed slot).prior.references = [r] ∧
        (actualSlotCompoundKey input c frame frameComputed slot).prior.readings = [priorReading] ∧
        priorReading.reference? = some r ∧
        (actualSlotCompoundKey input c frame frameComputed slot).rule5Readings = [reading] ∧
        reading.prior = priorReading ∧
        input.certified.buildLocalizedRerootCumulativeRule45Key?
            (localizedRule5StageFor (some r) .R)
            (ActualReaderPhysicalBranchInverse.topTarget input c)
            (referenceDependencyView input c)
            (localizedOccurrenceRerootEvaluationFuel
              (LocalizedUniversalReference.carrierFuel input))
            (frame.cursorAt slot) = some keyR ∧
        input.certified.buildLocalizedRerootCumulativeRule45Key?
            (localizedRule5StageFor (some r) .S)
            (ActualReaderPhysicalBranchInverse.topTarget input c)
            (referenceDependencyView input c)
            (localizedOccurrenceRerootEvaluationFuel
              (LocalizedUniversalReference.carrierFuel input))
            (frame.cursorAt slot) = some keyS ∧
        reading.commonR = keyR ∧
        reading.commonS = keyS ∧
        LocalizedUniqueNearestRule5Direction.actualTreeMark input singleBonded acyclic
          (actualSlotTree input c frame frameComputed slot) center = some r ∧
        branchMarkedDescriptor input c frame frameComputed slot singleBonded acyclic
          oAtom oObserved center = some r ∧
        (∀ e, e < distance →
          LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
            ((keyR.labels.getD e []).map Prod.snd) = []) ∧
        LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
          ((keyR.labels.getD distance []).map Prod.snd) = [r] ∧
        OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
            keyR.descriptor keyS.descriptor =
          (if r = RS.R then Ordering.gt else Ordering.lt) ∧
        (∃ occurrence : LocalizedUniversalReference.Occurrence input,
          occurrence.1.root = c.1 ∧
            occurrence.1.node.current? = some center ∧
              LocalizedUniversalReference.referenceState input occurrence = some (.chiral r)) := by
  classical
  exact
    LocalizedPhysicalRule5SignedExecution.exists_actualSlot_compoundReading_stageFor_signed_of_physicalAtom
      input c oAtom adjacent singleBonded acyclic hcharge noDouble cfgPhys physicalDomain unique
      (prefixStable_of_physicalDomain input c singleBonded acyclic hcharge noDouble
        (input.certified.canonicalReindexConfiguration cfgPhys)
        (actualGeneralRigidGlobalPhysicalDomain_of_actualGeneralRigidPhysicalDomain
          input.certified cfgPhys c physicalDomain))

/-! ## D. The physical mirror-pair endpoint without the residual premise, with the actual
build and common-reading identities retained -/




















theorem exists_pair_throughRule5_signed_pseudo_of_physicalMirrorTransport_noPrefix
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (i j : Fin 4)
    (transport : BranchTransport input.certified.detectedMultiCenterMolecule cfg c i j true)
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
        branchMarkedDescriptor input c frame frameComputed (alpha.symm i) singleBonded acyclic
            (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) oObservedLeft center =
          some r ∧
        LocalizedUniqueNearestRule5Direction.actualTreeMark input singleBonded acyclic
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
              LocalizedUniversalReference.referenceState input occurrence = some (.chiral r)) := by
  classical
  -- The calibrated global physical domain at the canonical re-indexed configuration.
  have domainGlobal : ActualGeneralRigidGlobalPhysicalDomain input.certified
      (input.certified.canonicalReindexConfiguration cfg) ⟨c.1, c.2⟩ :=
    actualGeneralRigidGlobalPhysicalDomain_of_actualGeneralRigidPhysicalDomain
      input.certified cfg c domain

  have prefixActual := prefixStable_of_physicalDomain input c singleBonded acyclic hcharge noDouble
    (input.certified.canonicalReindexConfiguration cfg) domainGlobal

  obtain ⟨frame, alpha, frameComputed, oObservedLeft, oObservedRight, r, leftReading,
    rightReading, _keyR₀, _keyS₀, leftList, rightList, mirrorReading, priorTie, ordering,
    pseudo, referencesPair, _branchMarked₀, _mark₀, _signed₀, _uniqueKey₀, occurrence⟩ :=
    LocalizedPhysicalRule5SignedExecution.exists_pair_throughRule5_signed_pseudo_of_physicalMirrorTransport
      input singleBonded acyclic hcharge noDouble cfg c domain i j transport unique prefixActual
  -- The witness-retaining one-branch endpoint at the actual left slot.
  obtain ⟨r', priorReading, reading, keyR, keyS, compoundBuilt, references, readingsSingleton,
    referenceSome, keyReadingsSingleton, priorEq, builtR, builtS, commonREq, commonSEq, markSlot,
    branchMarked, earlierKey, uniqueKey, signed⟩ :=
    LocalizedPhysicalRule5SignedExecution.actualSlot_compoundReading_stageFor_signed_of_physicalUniqueNearest_witness
      input c frame frameComputed (alpha.symm i) singleBonded acyclic hcharge noDouble
      (input.certified.canonicalReindexConfiguration cfg) domainGlobal
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) oObservedLeft unique
      prefixActual
  -- The actual singleton reference list identifies the selected references.
  have rEq : r' = r := by
    have lists : [r'] = [r] := references.symm.trans referencesPair
    simpa using lists
  -- The actual singleton Rule-5 reading list identifies the left readings.
  have readingEq : reading = leftReading := by
    have lists : [reading] = [leftReading] := keyReadingsSingleton.symm.trans leftList
    simpa using lists
  -- Transport the witness facts along the identified selected reference and left reading.
  -- (`subst` cannot eliminate `r'` through the `Decidable` instance of the sign `if`, so the
  -- affected hypotheses are rewritten individually.)
  rw [rEq] at references referenceSome builtR builtS branchMarked markSlot uniqueKey signed
  rw [readingEq] at keyReadingsSingleton priorEq commonREq commonSEq

  have prefixPair :=
    actualStage_labels_prefix_eq_of_physicalUniqueNearest input c frame frameComputed
      (alpha.symm i) singleBonded acyclic hcharge noDouble
      (input.certified.canonicalReindexConfiguration cfg) domainGlobal oObservedLeft (some r)
      unique builtR builtS
  exact ⟨frame, alpha, frameComputed, oObservedLeft, oObservedRight, r, leftReading,
    rightReading, priorReading, keyR, keyS, leftList, rightList, mirrorReading, priorTie,
    ordering, pseudo, compoundBuilt, references, readingsSingleton, referenceSome, priorEq,
    builtR, builtS, commonREq, commonSEq, prefixPair.1, prefixPair.2, branchMarked, markSlot,
    signed, earlierKey, uniqueKey, occurrence⟩

end LocalizedPhysicalRule5PrefixClosure

end

end TetraStereo.OneCenter

/-! ## Kernel-only guards -/

assert_kernel_only
  TetraStereo.OneCenter.LocalizedPhysicalRule5PrefixClosure.actualStage_labels_prefix_eq_of_physicalUniqueNearest
assert_kernel_only
  TetraStereo.OneCenter.LocalizedPhysicalRule5PrefixClosure.prefixStable_of_physicalDomain
assert_kernel_only
  TetraStereo.OneCenter.LocalizedPhysicalRule5PrefixClosure.exists_actualSlot_compoundReading_stageFor_signed_of_physicalAtom_noPrefix
assert_kernel_only
  TetraStereo.OneCenter.LocalizedPhysicalRule5PrefixClosure.exists_pair_throughRule5_signed_pseudo_of_physicalMirrorTransport_noPrefix
