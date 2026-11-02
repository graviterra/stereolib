import TetraStereo.OneCenter.LocalizedGuardedRule5Projection
import TetraStereo.OneCenter.LocalizedPhysicalStageExtensionClosure
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

























































namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput

variable {input : LocalizedUniversalReference.Input}

/-! ## The actual compound build of a physical slot -/











theorem physical_compoundKey_withRead_built (setup : ActualSlotPhysicalSetup input) :
    input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?
        (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c)
        (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        setup.tree.source = some setup.key := by
  rw [dependencyReader_eq_productionReader setup]
  rw [input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?_eq_localizedDependencyLabel
    (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
    (referenceDependencyView input setup.c)
    (localizedOccurrenceRerootEvaluationFuel
      (LocalizedUniversalReference.carrierFuel input)) setup.tree.source]
  rw [setup.tree_source]
  exact setup.compoundBuilt

/-! ## Reference cardinality on a physical branch -/






theorem physical_priorReferences_length_le_one
    (setup : ActualSlotPhysicalSetup input)
    (branchDomain : PhysicalBranchDomain input setup.root setup.oAtom) :
    setup.key.prior.references.length ≤ 1 := by
  rcases branchDomain with empty | ⟨center, distance, unique⟩
  · rw [(physical_empty_selected_references setup empty).2.1]
    simp
  · obtain ⟨descriptor, _marked, _ranked, references, _reading, _descriptorEq⟩ :=
      physical_selected_reference_of_unique setup unique
    rw [references]
    simp









theorem physical_noReads_of_emptyReferences
    (setup : ActualSlotPhysicalSetup input)
    (branchDomain : PhysicalBranchDomain input setup.root setup.oAtom)
    (emptyReferences : setup.key.prior.references = []) :
    ∀ cursor : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input),
      Relation.ReflTransGen (E input.certified) setup.tree.source cursor →
        ActualReaderPhysicalBranchInverse.dependencyReader input setup.c cursor = none := by
  rcases branchDomain with empty | ⟨center, distance, unique⟩
  · exact physical_noReads setup empty
  · obtain ⟨descriptor, _marked, _ranked, references, _reading, _descriptorEq⟩ :=
      physical_selected_reference_of_unique setup unique
    exact absurd emptyReferences (by rw [references]; simp)

/-! ## The guarded physical last-component projection -/












theorem physical_compoundRule5Readings_eq_lastProjection
    (leftSetup rightSetup : ActualSlotPhysicalSetup input)
    (leftDomain : PhysicalBranchDomain input leftSetup.root leftSetup.oAtom)
    (rightDomain : PhysicalBranchDomain input rightSetup.root rightSetup.oAtom)
    (priorTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
      leftSetup.key.prior rightSetup.key.prior = Ordering.eq)
    (probe : RS) :
    input.certified.compareLocalizedRerootCompoundRule5Readings probe
        leftSetup.key.rule5Readings rightSetup.key.rule5Readings =
      List.compareLex
        (Ordering.byKey
          (lastProjection ∘ input.certified.localizedRerootRule5Descriptor probe)
          (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat))
        leftSetup.key.rule5Readings rightSetup.key.rule5Readings :=
  compareLocalizedRerootCompoundRule5Readings_eq_lastProjection input.certified
    (ActualReaderPhysicalBranchInverse.dependencyReader input leftSetup.c)
    (ActualReaderPhysicalBranchInverse.dependencyReader input rightSetup.c)
    leftSetup.tree.source rightSetup.tree.source
    leftSetup.tree.source rightSetup.tree.source
    leftSetup.key rightSetup.key
    (physical_compoundKey_withRead_built leftSetup)
    (physical_compoundKey_withRead_built rightSetup)
    Relation.ReflTransGen.refl
    Relation.ReflTransGen.refl
    (physicalReader_noPseudo leftSetup)
    (physicalReader_noPseudo rightSetup)
    (physical_noReads_of_emptyReferences leftSetup leftDomain)
    (physical_noReads_of_emptyReferences rightSetup rightDomain)
    (physical_priorReferences_length_le_one leftSetup leftDomain)
    (physical_priorReferences_length_le_one rightSetup rightDomain)
    priorTie probe

/-- **Guarded physical through-Rule-5 ordering.**  Under the actual compound Rules-4b/4c prior tie,
the executable through-Rule-5 ordering of the two actual compound keys is exactly the common-`R`
Rule-5 reading-list comparison.  This is the execution-level reading of the projection theorem. -/
theorem physical_compoundThroughRule5_ordering_eq_commonR
    (leftSetup rightSetup : ActualSlotPhysicalSetup input)
    (priorTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
      leftSetup.key.prior rightSetup.key.prior = Ordering.eq) :
    (input.certified.compareLocalizedRerootCompoundThroughRule5
        leftSetup.key rightSetup.key).ordering =
      input.certified.compareLocalizedRerootCompoundRule5Readings
        .R leftSetup.key.rule5Readings rightSetup.key.rule5Readings :=
  compareLocalizedRerootCompoundThroughRule5_ordering_eq_commonR input.certified
    leftSetup.key rightSetup.key priorTie

/-- **Guarded physical execution projection.**  Under the actual compound Rules-4b/4c prior tie,
the executable through-Rule-5 ordering of the two actual physical compound keys is exactly the
lexicographic comparison of the last-component projections of their actual Rule-5 reading lists,
taken under the common `R` probe. -/
theorem physical_compoundThroughRule5_ordering_eq_lastProjection_commonR
    (leftSetup rightSetup : ActualSlotPhysicalSetup input)
    (leftDomain : PhysicalBranchDomain input leftSetup.root leftSetup.oAtom)
    (rightDomain : PhysicalBranchDomain input rightSetup.root rightSetup.oAtom)
    (priorTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
      leftSetup.key.prior rightSetup.key.prior = Ordering.eq) :
    (input.certified.compareLocalizedRerootCompoundThroughRule5
        leftSetup.key rightSetup.key).ordering =
      List.compareLex
        (Ordering.byKey
          (lastProjection ∘ input.certified.localizedRerootRule5Descriptor .R)
          (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat))
        leftSetup.key.rule5Readings rightSetup.key.rule5Readings :=
  compareLocalizedRerootCompoundThroughRule5_ordering_eq_lastProjection_commonR input.certified
    (ActualReaderPhysicalBranchInverse.dependencyReader input leftSetup.c)
    (ActualReaderPhysicalBranchInverse.dependencyReader input rightSetup.c)
    leftSetup.tree.source rightSetup.tree.source
    leftSetup.tree.source rightSetup.tree.source
    leftSetup.key rightSetup.key
    (physical_compoundKey_withRead_built leftSetup)
    (physical_compoundKey_withRead_built rightSetup)
    Relation.ReflTransGen.refl
    Relation.ReflTransGen.refl
    (physicalReader_noPseudo leftSetup)
    (physicalReader_noPseudo rightSetup)
    (physical_noReads_of_emptyReferences leftSetup leftDomain)
    (physical_noReads_of_emptyReferences rightSetup rightDomain)
    (physical_priorReferences_length_le_one leftSetup leftDomain)
    (physical_priorReferences_length_le_one rightSetup rightDomain)
    priorTie

/-! ## The complete evaluator comparison at the actual derived frame slots

The two physical branches of one detected centre share the executable frame of the final occurrence:
the frame builder is a function of the target only, so two successful slots of the same target force
equal frames.  Consequently the occurrence pair evaluator `compareLocalizedOccurrenceThroughRule5At?`
runs on **one** actual frame with two actual slots, and its result is the comparison record of the
two actual compound keys.  This is the executable evaluator form of the projection theorem; it adds
no assumption beyond the two indexed setups. -/

/-- **The derived frames of two slots of one centre coincide.**  Both setups record a successful
build of the same executable frame query, so the frames and their success equations agree. -/
theorem physical_indexedSetups_frame_eq
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (physicalDomain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    {leftAtom rightAtom : input.certified.Atom}
    (leftSetup : ActualSlotPhysicalSetupOf input c cfg physicalDomain leftAtom)
    (rightSetup : ActualSlotPhysicalSetupOf input c cfg physicalDomain rightAtom) :
    leftSetup.frame = rightSetup.frame := by
  have same : some leftSetup.frame = some rightSetup.frame := by
    rw [← leftSetup.frameComputed, ← rightSetup.frameComputed]
  exact Option.some.inj same





theorem physical_occurrenceThroughRule5At?_eq
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (physicalDomain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    {leftAtom rightAtom : input.certified.Atom}
    (leftSetup : ActualSlotPhysicalSetupOf input c cfg physicalDomain leftAtom)
    (rightSetup : ActualSlotPhysicalSetupOf input c cfg physicalDomain rightAtom) :
    input.certified.compareLocalizedOccurrenceThroughRule5At?
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (referenceDependencyView input c)
        leftSetup.frame leftSetup.slot rightSetup.slot =
      some (localizedOccurrenceRule45ComparisonRecord
        (input.certified.compareLocalizedRerootCompoundThroughRule5
          leftSetup.toSetup.key rightSetup.toSetup.key)) := by
  have frameEq : leftSetup.frame = rightSetup.frame :=
    physical_indexedSetups_frame_eq c cfg physicalDomain leftSetup rightSetup
  have leftBuilt :
      input.certified.buildLocalizedRerootCompoundRule45Key?
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (referenceDependencyView input c)
        (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (leftSetup.frame.cursorAt leftSetup.slot) = some leftSetup.toSetup.key :=
    leftSetup.toSetup.compoundBuilt
  have rightBuilt :
      input.certified.buildLocalizedRerootCompoundRule45Key?
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (referenceDependencyView input c)
        (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (leftSetup.frame.cursorAt rightSetup.slot) = some rightSetup.toSetup.key := by
    rw [frameEq]
    exact rightSetup.toSetup.compoundBuilt
  simp only [compareLocalizedOccurrenceThroughRule5At?, leftBuilt, rightBuilt]
  rfl

/-! ## The physical facade from the original physical data

The final entry point derives both indexed setups from the original common centre, configuration and
physical domain together with two actually bonded attachment atoms and the two reader-independent
branch domains.  No frame success, compound build success or selection output is supplied by the
caller. -/



















theorem physical_guardedRule5Closure_of_physical
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (physicalDomain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (leftAtom rightAtom : input.certified.Atom)
    (leftAdjacent : input.certified.moleculeGraph.Adj c.1 leftAtom)
    (rightAdjacent : input.certified.moleculeGraph.Adj c.1 rightAtom)
    (leftDomain : PhysicalBranchDomain input c leftAtom)
    (rightDomain : PhysicalBranchDomain input c rightAtom) :
    ∃ (leftSetup : ActualSlotPhysicalSetupOf input c cfg physicalDomain leftAtom)
      (rightSetup : ActualSlotPhysicalSetupOf input c cfg physicalDomain rightAtom),
      ActualSlotPhysicalSetup.PhysicalReferenceObservationClosure leftSetup.toSetup leftDomain ∧
        ActualSlotPhysicalSetup.PhysicalReferenceObservationClosure
            rightSetup.toSetup rightDomain ∧
          input.certified.buildLocalizedRerootCompoundRule45Key?
              (ActualReaderPhysicalBranchInverse.topTarget input c)
              (referenceDependencyView input c)
              (localizedOccurrenceRerootEvaluationFuel
                (LocalizedUniversalReference.carrierFuel input))
              leftSetup.toSetup.tree.source = some leftSetup.toSetup.key ∧
            input.certified.buildLocalizedRerootCompoundRule45Key?
                (ActualReaderPhysicalBranchInverse.topTarget input c)
                (referenceDependencyView input c)
                (localizedOccurrenceRerootEvaluationFuel
                  (LocalizedUniversalReference.carrierFuel input))
                rightSetup.toSetup.tree.source = some rightSetup.toSetup.key ∧
              leftSetup.frame = rightSetup.frame ∧
                input.certified.compareLocalizedOccurrenceThroughRule5At?
                    (ActualReaderPhysicalBranchInverse.topTarget input c)
                    (referenceDependencyView input c)
                    leftSetup.frame leftSetup.slot rightSetup.slot =
                  some (localizedOccurrenceRule45ComparisonRecord
                    (input.certified.compareLocalizedRerootCompoundThroughRule5
                      leftSetup.toSetup.key rightSetup.toSetup.key)) ∧
                  (∀ probe : RS,
                    input.certified.compareLocalizedRerootCompoundRule4bcKeys
                        leftSetup.toSetup.key.prior rightSetup.toSetup.key.prior =
                      Ordering.eq →
                    input.certified.compareLocalizedRerootCompoundRule5Readings probe
                        leftSetup.toSetup.key.rule5Readings
                        rightSetup.toSetup.key.rule5Readings =
                      List.compareLex
                        (Ordering.byKey
                          (lastProjection ∘
                            input.certified.localizedRerootRule5Descriptor probe)
                          (OfficialRuleMajorKey.compareSparseLayers
                            OfficialRuleMajorKey.compareNat))
                        leftSetup.toSetup.key.rule5Readings
                        rightSetup.toSetup.key.rule5Readings) ∧
                    (input.certified.compareLocalizedRerootCompoundRule4bcKeys
                        leftSetup.toSetup.key.prior rightSetup.toSetup.key.prior =
                      Ordering.eq →
                    (input.certified.compareLocalizedRerootCompoundThroughRule5
                        leftSetup.toSetup.key rightSetup.toSetup.key).ordering =
                      List.compareLex
                        (Ordering.byKey
                          (lastProjection ∘
                            input.certified.localizedRerootRule5Descriptor .R)
                          (OfficialRuleMajorKey.compareSparseLayers
                            OfficialRuleMajorKey.compareNat))
                        leftSetup.toSetup.key.rule5Readings
                        rightSetup.toSetup.key.rule5Readings) := by
  obtain ⟨leftSetup, leftClosure⟩ :=
    physicalReferenceObservation_closure_of_physical input c singleBonded acyclic hcharge
      noDouble cfg physicalDomain leftAtom leftAdjacent leftDomain
  obtain ⟨rightSetup, rightClosure⟩ :=
    physicalReferenceObservation_closure_of_physical input c singleBonded acyclic hcharge
      noDouble cfg physicalDomain rightAtom rightAdjacent rightDomain
  have leftBuild :
      input.certified.buildLocalizedRerootCompoundRule45Key?
          (ActualReaderPhysicalBranchInverse.topTarget input c)
          (referenceDependencyView input c)
          (localizedOccurrenceRerootEvaluationFuel
            (LocalizedUniversalReference.carrierFuel input))
          leftSetup.toSetup.tree.source = some leftSetup.toSetup.key := by
    rw [leftSetup.toSetup.tree_source]
    exact leftClosure.1
  have rightBuild :
      input.certified.buildLocalizedRerootCompoundRule45Key?
          (ActualReaderPhysicalBranchInverse.topTarget input c)
          (referenceDependencyView input c)
          (localizedOccurrenceRerootEvaluationFuel
            (LocalizedUniversalReference.carrierFuel input))
          rightSetup.toSetup.tree.source = some rightSetup.toSetup.key := by
    rw [rightSetup.toSetup.tree_source]
    exact rightClosure.1
  exact ⟨leftSetup, rightSetup, leftClosure, rightClosure, leftBuild, rightBuild,
    physical_indexedSetups_frame_eq c cfg physicalDomain leftSetup rightSetup,
    physical_occurrenceThroughRule5At?_eq c cfg physicalDomain leftSetup rightSetup,
    fun probe tie => physical_compoundRule5Readings_eq_lastProjection
      leftSetup.toSetup rightSetup.toSetup leftDomain rightDomain tie probe,
    fun tie => physical_compoundThroughRule5_ordering_eq_lastProjection_commonR
      leftSetup.toSetup rightSetup.toSetup leftDomain rightDomain tie⟩

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.physical_compoundKey_withRead_built
assert_kernel_only TetraStereo.OneCenter.physical_priorReferences_length_le_one
assert_kernel_only TetraStereo.OneCenter.physical_noReads_of_emptyReferences
assert_kernel_only TetraStereo.OneCenter.physical_compoundRule5Readings_eq_lastProjection
assert_kernel_only TetraStereo.OneCenter.physical_compoundThroughRule5_ordering_eq_commonR
assert_kernel_only TetraStereo.OneCenter.physical_compoundThroughRule5_ordering_eq_lastProjection_commonR
assert_kernel_only TetraStereo.OneCenter.physical_indexedSetups_frame_eq
assert_kernel_only TetraStereo.OneCenter.physical_occurrenceThroughRule5At?_eq
assert_kernel_only TetraStereo.OneCenter.physical_guardedRule5Closure_of_physical
