import TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction
import TetraStereo.OneCenter.LocalizedActualKeyTiePhysicalTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput

noncomputable section

































namespace CertifiedLocalizedCIPInput

/-- **Singleton reading-list compilation.**  If the per-reading builder succeeds on one prior
reading, the reading-list builder succeeds on the singleton list with the singleton reading. -/
theorem buildLocalizedRerootRule5Readings?_singleton_eq_some
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading)
    (reading : input.LocalizedRerootRule5Reading)
    (computed : input.buildLocalizedRerootRule5Reading?
      target view fuel cursor prior = some reading) :
    input.buildLocalizedRerootRule5Readings? target view fuel cursor [prior] =
      some [reading] := by
  simp [buildLocalizedRerootRule5Readings?, computed]

/-- **Successful reading from its two actual common-reference builds.**  The `R` and `S` fields of
the reading are exactly the outputs of the cumulative builders at the stages selected by the prior
reading's own reference. -/
theorem buildLocalizedRerootRule5Reading?_eq_some_of_commonBuilds
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading)
    (commonR commonS : input.LocalizedRerootCumulativeRule45Key)
    (builtR : input.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor prior.reference? .R) target view fuel cursor = some commonR)
    (builtS : input.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor prior.reference? .S) target view fuel cursor = some commonS) :
    input.buildLocalizedRerootRule5Reading? target view fuel cursor prior =
      some { prior := prior, commonR := commonR, commonS := commonS } := by
  simp [buildLocalizedRerootRule5Reading?, builtR, builtS]

end CertifiedLocalizedCIPInput

/-! ## Actual singleton compound reading at an actual frame cursor -/
















theorem actualSlot_compoundReading_singleton_aligned_of_physicalUniqueNearest
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
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance) :
    ∃ (r : RS)
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
        (actualSlotCompoundKey input c frame frameComputed slot).prior.readings =
            [priorReading] ∧
          priorReading.reference? = some r ∧
            (actualSlotCompoundKey input c frame frameComputed slot).rule5Readings =
                [reading] ∧
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
                        keyR.descriptor ≠ keyS.descriptor := by
  have compoundBuilt : input.certified.buildLocalizedRerootCompoundRule45Key?
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt slot) =
        some (actualSlotCompoundKey input c frame frameComputed slot) :=
    actualSlotCompoundBuilt input c frame frameComputed slot
  have components :=
    buildLocalizedRerootCompoundRule45Key?_prior_built input.certified
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt slot) (actualSlotCompoundKey input c frame frameComputed slot)
      compoundBuilt
  obtain ⟨r, marked⟩ :=
    exists_markedBranchUniqueNearest_of_physicalBranchUniqueNearest input c frame
      frameComputed slot singleBonded acyclic hcharge noDouble cfg domain oAtom oObserved
      unique
  obtain ⟨_rankedSingleton, referencesSingleton, priorReading, readingsSingleton,
    referenceSome⟩ :=
    actualSlot_markedBranchUniqueNearest_references_singleton input c frame frameComputed
      slot singleBonded acyclic hcharge noDouble cfg domain oAtom oObserved marked
  obtain ⟨keyR, keyS, builtR, builtS, descriptorNe⟩ :=
    LocalizedUniqueNearestRule5Direction.exists_actualSlot_stageFor_keys_descriptor_ne_of_physicalUniqueNearest
      input c frame frameComputed slot singleBonded acyclic hcharge noDouble cfg domain
      oAtom oObserved (some r) unique
  have builtR' : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor priorReading.reference? .R)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt slot) = some keyR := by
    rw [referenceSome]
    exact builtR
  have builtS' : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor priorReading.reference? .S)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt slot) = some keyS := by
    rw [referenceSome]
    exact builtS
  let reading : input.certified.LocalizedRerootRule5Reading :=
    { prior := priorReading, commonR := keyR, commonS := keyS }
  have readingBuilt : input.certified.buildLocalizedRerootRule5Reading?
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt slot) priorReading = some reading :=
    buildLocalizedRerootRule5Reading?_eq_some_of_commonBuilds input.certified
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt slot) priorReading keyR keyS builtR' builtS'
  have singletonBuilt : input.certified.buildLocalizedRerootRule5Readings?
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt slot) [priorReading] = some [reading] :=
    buildLocalizedRerootRule5Readings?_singleton_eq_some input.certified
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt slot) priorReading reading readingBuilt
  have readingsBuilt' : input.certified.buildLocalizedRerootRule5Readings?
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt slot) [priorReading] =
        some (actualSlotCompoundKey input c frame frameComputed slot).rule5Readings := by
    simpa only [readingsSingleton] using components.2
  have keyReadingsEq :
      (actualSlotCompoundKey input c frame frameComputed slot).rule5Readings = [reading] :=
    Option.some.inj (readingsBuilt'.symm.trans singletonBuilt)
  exact ⟨r, priorReading, reading, keyR, keyS, compoundBuilt, referencesSingleton,
    readingsSingleton, referenceSome, keyReadingsEq, rfl, builtR, builtS, rfl, rfl,
    descriptorNe⟩

/-! ## Final physical wrapper from the detected input -/

















theorem exists_actualFrame_compoundReading_descriptor_ne_of_physicalDomain
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfgPhys : input.certified.detectedMultiCenterMolecule.Configuration)
    (physicalDomain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfgPhys c)
    {center : input.certified.Atom} {distance : Nat}
    (branchDomain : ∀ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (_frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
        (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
      (oAtom : input.certified.Atom),
      (frame.cursorAt slot).occurrence.1.node.current? = some oAtom →
        PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance) :
    ∃ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
        (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
      (oAtom : input.certified.Atom)
      (r : RS)
      (priorReading : input.certified.LocalizedRerootRule4bcReading)
      (reading : input.certified.LocalizedRerootRule5Reading)
      (keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key),
      (frame.cursorAt slot).occurrence.1.node.current? = some oAtom ∧
        PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance ∧
        input.certified.buildLocalizedRerootCompoundRule45Key?
            (ActualReaderPhysicalBranchInverse.topTarget input c)
            (referenceDependencyView input c)
            (localizedOccurrenceRerootEvaluationFuel
              (LocalizedUniversalReference.carrierFuel input))
            (frame.cursorAt slot) =
          some (actualSlotCompoundKey input c frame frameComputed slot) ∧
          (actualSlotCompoundKey input c frame frameComputed slot).prior.references = [r] ∧
            (actualSlotCompoundKey input c frame frameComputed slot).prior.readings =
                [priorReading] ∧
              priorReading.reference? = some r ∧
                (actualSlotCompoundKey input c frame frameComputed slot).rule5Readings =
                    [reading] ∧
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
                            keyR.descriptor ≠ keyS.descriptor := by
  obtain ⟨frame, alpha, frameComputed, ligandLink⟩ :=
    input.certified.exists_canonicalFrameSlotLink
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      singleBonded acyclic (globalCarrierFuel_adequate input) ⟨c.1, c.2⟩
      (ActualReaderPhysicalBranchInverse.topTarget_current input c)
  let oAtom := input.certified.canonicalLigandAtom ⟨c.1, c.2⟩ (alpha slot)
  have oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom :=
    ligandLink slot
  have unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance :=
    branchDomain frame frameComputed oAtom oObserved
  have domain : ActualGeneralRigidGlobalPhysicalDomain input.certified
      (input.certified.canonicalReindexConfiguration cfgPhys) ⟨c.1, c.2⟩ :=
    actualGeneralRigidGlobalPhysicalDomain_of_actualGeneralRigidPhysicalDomain
      input.certified cfgPhys c physicalDomain
  obtain ⟨r, priorReading, reading, keyR, keyS, compoundBuilt, referencesSingleton,
    readingsSingleton, referenceSome, keyReadingsSingleton, priorEq, builtR, builtS,
    commonREq, commonSEq, descriptorNe⟩ :=
    actualSlot_compoundReading_singleton_aligned_of_physicalUniqueNearest input c frame
      frameComputed slot singleBonded acyclic hcharge noDouble
      (input.certified.canonicalReindexConfiguration cfgPhys) domain oAtom oObserved unique
  exact ⟨frame, frameComputed, oAtom, r, priorReading, reading, keyR, keyS,
    oObserved, unique, compoundBuilt,
    referencesSingleton, readingsSingleton, referenceSome, keyReadingsSingleton, priorEq,
    builtR, builtS, commonREq, commonSEq, descriptorNe⟩

/-! ## Physical-atom wrapper: branch attachment supplied, frame and slot derived -/









theorem exists_actualSlot_compoundReading_descriptor_ne_of_physicalAtom
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
      (r : RS)
      (priorReading : input.certified.LocalizedRerootRule4bcReading)
      (reading : input.certified.LocalizedRerootRule5Reading)
      (keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key),
      (frame.cursorAt slot).occurrence.1.node.current? = some oAtom ∧
        input.certified.buildLocalizedRerootCompoundRule45Key?
            (ActualReaderPhysicalBranchInverse.topTarget input c)
            (referenceDependencyView input c)
            (localizedOccurrenceRerootEvaluationFuel
              (LocalizedUniversalReference.carrierFuel input))
            (frame.cursorAt slot) =
          some (actualSlotCompoundKey input c frame frameComputed slot) ∧
          (actualSlotCompoundKey input c frame frameComputed slot).prior.references = [r] ∧
            (actualSlotCompoundKey input c frame frameComputed slot).prior.readings =
                [priorReading] ∧
              priorReading.reference? = some r ∧
                (actualSlotCompoundKey input c frame frameComputed slot).rule5Readings =
                    [reading] ∧
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
                            keyR.descriptor ≠ keyS.descriptor := by
  let center : input.certified.TetrahedralCenter := ⟨c.1, c.2⟩
  obtain ⟨frame, alpha, frameComputed, ligandLink⟩ :=
    input.certified.exists_canonicalFrameSlotLink
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      singleBonded acyclic (globalCarrierFuel_adequate input) center
      (ActualReaderPhysicalBranchInverse.topTarget_current input c)
  obtain ⟨index, ligandEq⟩ :=
    (input.certified.detectedOneCenterMolecule center).ligandAtom_surjective
      oAtom (by simpa [center] using adjacent)
  have ligandEq' : input.certified.canonicalLigandAtom center index = oAtom := ligandEq
  let slot : Fin 4 := alpha.symm index
  have oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom := by
    simpa [slot, ligandEq'] using ligandLink slot
  have domain : ActualGeneralRigidGlobalPhysicalDomain input.certified
      (input.certified.canonicalReindexConfiguration cfgPhys) ⟨c.1, c.2⟩ :=
    actualGeneralRigidGlobalPhysicalDomain_of_actualGeneralRigidPhysicalDomain
      input.certified cfgPhys c physicalDomain
  obtain ⟨r, priorReading, reading, keyR, keyS, compoundBuilt, referencesSingleton,
    readingsSingleton, referenceSome, keyReadingsSingleton, priorEq, builtR, builtS,
    commonREq, commonSEq, descriptorNe⟩ :=
    actualSlot_compoundReading_singleton_aligned_of_physicalUniqueNearest input c frame
      frameComputed slot singleBonded acyclic hcharge noDouble
      (input.certified.canonicalReindexConfiguration cfgPhys) domain oAtom oObserved unique
  exact ⟨slot, frame, frameComputed, r, priorReading, reading, keyR, keyS,
    oObserved, compoundBuilt,
    referencesSingleton, readingsSingleton, referenceSome, keyReadingsSingleton, priorEq,
    builtR, builtS, commonREq, commonSEq, descriptorNe⟩

end

end TetraStereo.OneCenter

/-! ## Kernel-only guards -/

assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule5Readings?_singleton_eq_some
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule5Reading?_eq_some_of_commonBuilds
assert_kernel_only
  TetraStereo.OneCenter.actualSlot_compoundReading_singleton_aligned_of_physicalUniqueNearest
assert_kernel_only
  TetraStereo.OneCenter.exists_actualFrame_compoundReading_descriptor_ne_of_physicalDomain
assert_kernel_only
  TetraStereo.OneCenter.exists_actualSlot_compoundReading_descriptor_ne_of_physicalAtom
