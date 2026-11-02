import TetraStereo.OneCenter.LocalizedPhysicalRootDescriptorExecution
import TetraStereo.OneCenter.LocalizedActualPhysicalKeySeparation
import TetraStereo.OneCenter.LocalizedPhysicalCompoundForwardTransport
import TetraStereo.OneCenter.PhysicalEnantiomorphicPairCountReindexing
import TetraStereo.OneCenter.LocalizedAcyclicPhysicalPseudoFidelity
import TetraStereo.OneCenter.LocalizedEmptyReferencePhysicalPriorInverse
import TetraStereo.OneCenter.LocalizedPhysicalDomainAdapters
import TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalKeySeparation
import TetraStereo.OneCenter.LocalizedActualPhysicalReferenceSelection
import TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance
import TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalKeyTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false











































namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open RootedTetrahedralBranchSymmetry

/-! ## The explicit prior-tie / physical-enantiomorphic bridge -/









def ActualFrameCompoundPhysicalBridge
    (input : LocalizedUniversalReference.Input)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration) (c : m.Center)
    (target : LocalizedUniversalReference.Occurrence input)
    (view : input.certified.LocalizedDependencyView target)
    (center : input.certified.detectedMultiCenterMolecule.Center) : Prop :=
  ∀ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame),
    input.certified.localizedOccurrenceFourLigandFrame? target = some frame →
      (∀ index : Fin 4,
        (frame.cursorAt index).occurrence.1.node.current? =
          some (input.certified.detectedMultiCenterMolecule.ligandAtomAt center (alpha index))) →
        ∀ i j : Fin 4,
          compoundPriorTieRelation input.certified
              (frame.compoundKeyAt input.certified target view derived) i j ↔
            Enantiomorphic m cfg c (alpha i) (alpha j)

/-! ## Count reindexing through the actual frame permutation -/






theorem sourceEnantiomorphicPairCount_compoundPriorTieRelation_eq_frameEnumeratedPairCount
    (input : CertifiedLocalizedCIPInput)
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center)
    (alpha : Equiv.Perm (Fin 4))
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (bridge : ∀ i j : Fin 4,
      compoundPriorTieRelation input keys i j ↔ Enantiomorphic m cfg c (alpha i) (alpha j)) :
    sourceEnantiomorphicPairCount (compoundPriorTieRelation input keys) =
      frameEnumeratedEnantiomorphicPairCount m cfg c alpha := by
  show sourceEnantiomorphicPairCount (compoundPriorTieRelation input keys) =
    @sourceEnantiomorphicPairCount
      (fun i j : Fin 4 => Enantiomorphic m cfg c (alpha i) (alpha j))
      (frameEnumeratedEnantiomorphicDecidableRel m cfg c alpha)
  exact sourceEnantiomorphicPairCount_congr _ _ (fun i j _ => bridge i j)




theorem sourceEnantiomorphicPairCount_compoundPriorTieRelation_eq_physicalCount
    (input : CertifiedLocalizedCIPInput)
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center)
    (alpha : Equiv.Perm (Fin 4))
    (keys : Fin 4 → input.LocalizedRerootCompoundRule45Key)
    (bridge : ∀ i j : Fin 4,
      compoundPriorTieRelation input keys i j ↔ Enantiomorphic m cfg c (alpha i) (alpha j)) :
    sourceEnantiomorphicPairCount (compoundPriorTieRelation input keys) =
      physicalEnantiomorphicPairCount m cfg c :=
  (sourceEnantiomorphicPairCount_compoundPriorTieRelation_eq_frameEnumeratedPairCount
      input m cfg c alpha keys bridge).trans
    (frameEnumeratedEnantiomorphicPairCount_eq m cfg c alpha)
















theorem exists_referenceState_descriptor_lowercase_iff_physicalCount_of_priorTieBridge
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input)
    {oAtom : input.certified.Atom}
    (oObserved : target.1.node.current? = some oAtom)
    (center : input.certified.detectedMultiCenterMolecule.Center)
    (centerEq : center.1 = oAtom)
    (centerReal : input.certified.RealTetrahedralCenterNode target.1.node
      ⟨center.1, center.2⟩)
    (data : input.certified.ActualCompoundKeyData target
      (input.certified.localizedDependencyView
        (LocalizedUniversalReference.referenceState input) target))
    (realNode : input.certified.ActualFrameRealNodeCoordinates target)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration) (c : m.Center)
    (bridge : ActualFrameCompoundPhysicalBridge input m cfg c target
      (input.certified.localizedDependencyView
        (LocalizedUniversalReference.referenceState input) target) center) :
    ∃ descriptor : LocalizedTetrahedralRSPseudoDescriptor,
      LocalizedUniversalReference.referenceState input target = some descriptor ∧
        (descriptor.IsLowercase ↔ physicalEnantiomorphicPairCount m cfg c = 1) := by
  classical
  obtain ⟨frame, alpha, derived, tracked, normalizedRS, pointsAt, frameComputed, ligandLink,
    _safeComputed, descriptorEq, _rational, _spatial, _physical, _nonzero⟩ :=
    CertifiedLocalizedCIPInput.exists_referenceState_classify_of_detectedPhysicalRoot
      input noDouble target singleBonded acyclic enough oObserved center centerEq centerReal
      data realNode
  let referenceView :=
    input.certified.localizedDependencyView
      (LocalizedUniversalReference.referenceState input) target
  let keys := frame.compoundKeyAt input.certified target referenceView derived
  have bridgeHere : ∀ i j : Fin 4,
      compoundPriorTieRelation input.certified keys i j ↔
        Enantiomorphic m cfg c (alpha i) (alpha j) :=
    bridge frame alpha derived frameComputed ligandLink
  have countEq :=
    sourceEnantiomorphicPairCount_compoundPriorTieRelation_eq_physicalCount
      input.certified m cfg c alpha keys bridgeHere
  refine ⟨classifyTetrahedralRSPseudo normalizedRS
      (physicalEnantiomorphicPairCount m cfg c), ?_, ?_⟩
  · rw [descriptorEq, countEq]
  · exact isLowercase_classify_iff normalizedRS (physicalEnantiomorphicPairCount m cfg c)











theorem exists_referenceState_descriptor_lowercase_iff_physicalCount_of_frame
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (separated : input.certified.CompoundKeyOffDiagonalStrict
      (frame.compoundKeyAt input.certified target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target) derived))
    (maxTwo : input.certified.PriorTieClassAtMostTwo
      (frame.compoundKeyAt input.certified target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target) derived))
    (mirror : input.certified.PriorTieMirrorReadings
      (frame.compoundKeyAt input.certified target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target) derived))
    (center : input.certified.TetrahedralCenter)
    (centerReal : input.certified.RealTetrahedralCenterNode target.1.node center)
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint?
        (frame.cursorAt index) = some (pointsAt index))
    (nonzero : CartesianPoint3.orientedVolume
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration) (c : m.Center)
    (alpha : Equiv.Perm (Fin 4))
    (bridge : ∀ i j : Fin 4,
      compoundPriorTieRelation input.certified
          (frame.compoundKeyAt input.certified target
            (input.certified.localizedDependencyView
              (LocalizedUniversalReference.referenceState input) target) derived) i j ↔
        Enantiomorphic m cfg c (alpha i) (alpha j)) :
    ∃ descriptor : LocalizedTetrahedralRSPseudoDescriptor,
      LocalizedUniversalReference.referenceState input target = some descriptor ∧
        (descriptor.IsLowercase ↔ physicalEnantiomorphicPairCount m cfg c = 1) := by
  classical
  let view := input.certified.localizedDependencyView
    (LocalizedUniversalReference.referenceState input) target
  let keys := frame.compoundKeyAt input.certified target view derived
  obtain ⟨tracked, normalizedRS, _safeComputed, descriptorEq, _lowercaseCount, _rational⟩ :=
    input.certified.localizedOccurrenceRule45Descriptor?_eq_classify_and_isLowercase_iff
      target view frame derived keys
      (fun index => frame.compoundKeyAt_built input.certified target view derived index)
      separated maxTwo mirror center centerReal pointsAt spatial nonzero
  have readback :=
    LocalizedUniversalReference.referenceState_eq_bareRule45Descriptor_of_noDoubleRecords
      input noDouble target
  have countEq :=
    sourceEnantiomorphicPairCount_compoundPriorTieRelation_eq_physicalCount
      input.certified m cfg c alpha keys bridge
  refine ⟨classifyTetrahedralRSPseudo normalizedRS
      (physicalEnantiomorphicPairCount m cfg c), ?_, ?_⟩
  · rw [readback, descriptorEq, countEq]
  · exact isLowercase_classify_iff normalizedRS (physicalEnantiomorphicPairCount m cfg c)








theorem framePriorTie_implies_enantiomorphic
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (distinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport
      input.certified.detectedMultiCenterMolecule cfg c i j)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (referenceOf : Fin 4 → RS)
    (references : ∀ index : Fin 4,
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references =
        [referenceOf index])
    {i j : Fin 4} (different : i ≠ j)
    (priorTie : compoundPriorTieRelation input.certified
      (frame.compoundKeyAt input.certified
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (LocalizedActualPhysicalKeySeparation.actualPhysicalView input c) derived) i j) :
    Enantiomorphic input.certified.detectedMultiCenterMolecule cfg c (alpha i) (alpha j) :=
  LocalizedActualPhysicalKeySeparation.actualFrame_singleton_priorTie_enantiomorphic_of_physicalDistinct
    input noDouble singleBonded acyclic charge cfg c domain distinct frame alpha frameComputed
    slotSpec derived i j different (referenceOf i) (referenceOf j)
    (references i) (references j) priorTie.2







theorem framePriorTie_implies_enantiomorphic_of_zeroOrOne
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (distinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport
      input.certified.detectedMultiCenterMolecule cfg c i j)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (zeroOrOne : ∀ index : Fin 4,
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references = [] ∨
        ∃ reference : RS,
          (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references =
            [reference])
    {i j : Fin 4} (different : i ≠ j)
    (priorTie : compoundPriorTieRelation input.certified
      (frame.compoundKeyAt input.certified
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (LocalizedActualPhysicalKeySeparation.actualPhysicalView input c) derived) i j) :
    Enantiomorphic input.certified.detectedMultiCenterMolecule cfg c (alpha i) (alpha j) :=
  LocalizedEmptyReferencePhysicalPriorInverse.actualFrame_zeroOrOne_priorTie_enantiomorphic_of_physicalDistinct
    input noDouble singleBonded acyclic charge cfg c domain distinct frame alpha frameComputed
    slotSpec derived i j different zeroOrOne priorTie.2

/-! ## Reverse half: the exact selector-correlation obligation -/















def ActualFrameMirrorSelectorCorrelation
    (input : LocalizedUniversalReference.Input)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (i j : Fin 4) : Prop :=
  i ≠ j →
    LocalizedPhysicalCompoundSelectorShape
      ((LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived
          (alpha.symm i)).prior.references)
      ((LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived
          (alpha.symm j)).prior.references)
      true →
    MirrorTransport input.certified.detectedMultiCenterMolecule cfg c i j →
      compoundPriorTieRelation input.certified
        (frame.compoundKeyAt input.certified
          (ActualReaderPhysicalBranchInverse.topTarget input c)
          (LocalizedActualPhysicalKeySeparation.actualPhysicalView input c) derived)
        (alpha.symm i) (alpha.symm j)





theorem frame_enantiomorphic_implies_priorTie_of_selectorCorrelation
    (input : LocalizedUniversalReference.Input)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (correlation : ∀ i j : Fin 4,
      ActualFrameMirrorSelectorCorrelation input cfg c frame alpha derived i j)
    {i j : Fin 4}
    (enantiomorphic : Enantiomorphic input.certified.detectedMultiCenterMolecule cfg c i j)
    (shape : LocalizedPhysicalCompoundSelectorShape
      ((LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived
          (alpha.symm i)).prior.references)
      ((LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived
          (alpha.symm j)).prior.references)
      true) :
    compoundPriorTieRelation input.certified
      (frame.compoundKeyAt input.certified
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (LocalizedActualPhysicalKeySeparation.actualPhysicalView input c) derived)
      (alpha.symm i) (alpha.symm j) :=
  correlation i j enantiomorphic.1 shape enantiomorphic.2.1











theorem actualCompoundKeyData_of_singletonSelection
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (distinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport
      input.certified.detectedMultiCenterMolecule cfg c i j)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (referenceOf : Fin 4 → RS)
    (references : ∀ index : Fin 4,
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references =
        [referenceOf index]) :
    input.certified.ActualCompoundKeyData
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (LocalizedActualPhysicalKeySeparation.actualPhysicalView input c) := by
  have separated : input.certified.CompoundKeyOffDiagonalStrict
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived) :=
    LocalizedActualPhysicalKeySeparation.frameSlotKeys_compoundKeyOffDiagonalStrict_of_physicalDistinct
      input noDouble singleBonded acyclic charge cfg c domain distinct frame alpha frameComputed
      slotSpec derived
  have readerSparse : ∀ cursor, LocalizedRule4bSparseLabel
      (ActualReaderPhysicalBranchInverse.dependencyReader input c cursor) :=
    LocalizedActualPhysicalKeySeparation.actualDependencyReader_sparse
      input singleBonded acyclic noDouble cfg c domain
  have maxTwo : input.certified.PriorTieClassAtMostTwo
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived) :=
    actual_priorTieClassAtMostTwo input.certified singleBonded acyclic
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) readerSparse
      (fun index => frame.cursorAt index)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived)
      (fun index => LocalizedActualPhysicalKeySeparation.frameSlotKey_withRead_built
        input c frame derived index)
      referenceOf references separated
  have mirror : input.certified.PriorTieMirrorReadings
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived) :=
    actual_priorTieMirrorReadings input.certified singleBonded acyclic
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) readerSparse
      (fun index => frame.cursorAt index)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived)
      (fun index => LocalizedActualPhysicalKeySeparation.frameSlotKey_withRead_built
        input c frame derived index)
      referenceOf references separated
  exact input.certified.actualCompoundKeyData_of_frame
    (ActualReaderPhysicalBranchInverse.topTarget input c)
    (LocalizedActualPhysicalKeySeparation.actualPhysicalView input c)
    frame derived frameComputed separated maxTwo mirror





theorem frame_compoundPhysicalBridge_of_singletonSelection
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (distinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport
      input.certified.detectedMultiCenterMolecule cfg c i j)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (referenceOf : Fin 4 → RS)
    (references : ∀ index : Fin 4,
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references =
        [referenceOf index])
    (shape : ∀ i j : Fin 4, i ≠ j →
      MirrorTransport input.certified.detectedMultiCenterMolecule cfg c (alpha i) (alpha j) →
      LocalizedPhysicalCompoundSelectorShape
        ((LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived i).prior.references)
        ((LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived j).prior.references)
        true)
    (correlation : ∀ i j : Fin 4,
      ActualFrameMirrorSelectorCorrelation input cfg c frame alpha derived i j) :
    ∀ i j : Fin 4,
      compoundPriorTieRelation input.certified
          (frame.compoundKeyAt input.certified
            (ActualReaderPhysicalBranchInverse.topTarget input c)
            (LocalizedActualPhysicalKeySeparation.actualPhysicalView input c) derived) i j ↔
        Enantiomorphic input.certified.detectedMultiCenterMolecule cfg c (alpha i) (alpha j) := by
  intro i j
  constructor
  · intro priorTie
    exact framePriorTie_implies_enantiomorphic input noDouble singleBonded acyclic charge cfg c
      domain distinct frame alpha frameComputed slotSpec derived referenceOf references
      priorTie.1 priorTie
  · intro enantiomorphic
    have reverse := correlation (alpha i) (alpha j) enantiomorphic.1
      (by
        simpa only [Equiv.symm_apply_apply] using
          shape i j (fun same => enantiomorphic.1 (congrArg alpha same))
            enantiomorphic.2.1)
      enantiomorphic.2.1
    simpa using reverse





theorem frame_compoundPhysicalBridge_of_zeroOrOne
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (distinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport
      input.certified.detectedMultiCenterMolecule cfg c i j)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (zeroOrOne : ∀ index : Fin 4,
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references = [] ∨
        ∃ reference : RS,
          (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references =
            [reference])
    (shape : ∀ i j : Fin 4, i ≠ j →
      MirrorTransport input.certified.detectedMultiCenterMolecule cfg c (alpha i) (alpha j) →
      LocalizedPhysicalCompoundSelectorShape
        ((LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived i).prior.references)
        ((LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived j).prior.references)
        true)
    (correlation : ∀ i j : Fin 4,
      ActualFrameMirrorSelectorCorrelation input cfg c frame alpha derived i j) :
    ∀ i j : Fin 4,
      compoundPriorTieRelation input.certified
          (frame.compoundKeyAt input.certified
            (ActualReaderPhysicalBranchInverse.topTarget input c)
            (LocalizedActualPhysicalKeySeparation.actualPhysicalView input c) derived) i j ↔
        Enantiomorphic input.certified.detectedMultiCenterMolecule cfg c (alpha i) (alpha j) := by
  intro i j
  constructor
  · intro priorTie
    exact framePriorTie_implies_enantiomorphic_of_zeroOrOne input noDouble singleBonded acyclic
      charge cfg c domain distinct frame alpha frameComputed slotSpec derived zeroOrOne
      priorTie.1 priorTie
  · intro enantiomorphic
    have reverse := correlation (alpha i) (alpha j) enantiomorphic.1
      (by
        simpa only [Equiv.symm_apply_apply] using
          shape i j (fun same => enantiomorphic.1 (congrArg alpha same))
            enantiomorphic.2.1)
      enantiomorphic.2.1
    simpa using reverse










theorem actualFrameMirrorSelectorCorrelation_of_physicalForward
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame) :
    ∀ i j : Fin 4,
      ActualFrameMirrorSelectorCorrelation input cfg c frame alpha derived i j := by
  intro i j different shape transport
  obtain ⟨frame', alpha', frameComputed', slotSpec', _, _, forward⟩ :=
    localizedPhysicalCompound_detected_priorTie_and_commonReading input singleBonded acyclic
      noDouble cfg c i j true transport domain
  have hOcc : localizedPhysicalTopOccurrence input
      input.certified.detectedMultiCenterMolecule domain.graphEq c =
      ActualReaderPhysicalBranchInverse.topTarget input c := by
    have hcenter : localizedPhysicalTopCenter input
        input.certified.detectedMultiCenterMolecule domain.graphEq c =
        (⟨c.1, c.2⟩ : input.certified.TetrahedralCenter) :=
      Subtype.ext rfl
    unfold localizedPhysicalTopOccurrence ActualReaderPhysicalBranchInverse.topTarget
    rw [hcenter]
  have frameEq : frame' = frame := by
    have h := frameComputed'
    rw [hOcc] at h
    exact Option.some.inj (h.symm.trans frameComputed)
  have alphaEq : alpha' = alpha := by
    apply Equiv.ext
    intro index
    apply input.certified.detectedMultiCenterMolecule.ligandAtomAt_injective c
    have h := slotSpec' index
    rw [frameEq] at h
    exact Option.some.inj (h.symm.trans (slotSpec index))
  have shape' : LocalizedPhysicalCompoundSelectorShape
      ((localizedPhysicalCompoundFrameKeyOfComputed input
        input.certified.detectedMultiCenterMolecule domain.graphEq c frame' frameComputed'
        (alpha'.symm i)).prior.references)
      ((localizedPhysicalCompoundFrameKeyOfComputed input
        input.certified.detectedMultiCenterMolecule domain.graphEq c frame' frameComputed'
        (alpha'.symm j)).prior.references) true := by
    simpa [localizedPhysicalCompoundFrameKeyOfComputed,
      LocalizedActualPhysicalKeySeparation.frameSlotKey,
      localizedPhysicalCompoundFrameView,
      LocalizedActualPhysicalKeySeparation.actualPhysicalView,
      hOcc, frameEq, alphaEq] using shape
  obtain ⟨_, _, _, _, priorTie, _⟩ := forward shape'
  refine ⟨?_, ?_⟩
  · intro same
    exact different (alpha.symm.injective same)
  · simpa [compoundPriorTieRelation, priorKeyTie,
      localizedPhysicalCompoundFrameKeyOfComputed,
      LocalizedActualPhysicalKeySeparation.frameSlotKey,
      localizedPhysicalCompoundFrameView,
      LocalizedActualPhysicalKeySeparation.actualPhysicalView,
      hOcc, frameEq, alphaEq] using priorTie






theorem exists_referenceState_descriptor_lowercase_iff_physicalCount_of_singletonSelection
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (distinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport
      input.certified.detectedMultiCenterMolecule cfg c i j)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (referenceOf : Fin 4 → RS)
    (references : ∀ index : Fin 4,
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references =
        [referenceOf index])
    (shape : ∀ i j : Fin 4, i ≠ j →
      MirrorTransport input.certified.detectedMultiCenterMolecule cfg c (alpha i) (alpha j) →
      LocalizedPhysicalCompoundSelectorShape
        ((LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived i).prior.references)
        ((LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived j).prior.references)
        true)
    (center : input.certified.TetrahedralCenter)
    (centerReal : input.certified.RealTetrahedralCenterNode
      (ActualReaderPhysicalBranchInverse.topTarget input c).1.node center)
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint?
        (frame.cursorAt index) = some (pointsAt index))
    (nonzero : CartesianPoint3.orientedVolume
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0) :
    ∃ descriptor : LocalizedTetrahedralRSPseudoDescriptor,
      LocalizedUniversalReference.referenceState input
          (ActualReaderPhysicalBranchInverse.topTarget input c) = some descriptor ∧
        (descriptor.IsLowercase ↔
          physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule cfg c = 1) := by
  have separated : input.certified.CompoundKeyOffDiagonalStrict
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived) :=
    LocalizedActualPhysicalKeySeparation.frameSlotKeys_compoundKeyOffDiagonalStrict_of_physicalDistinct
      input noDouble singleBonded acyclic charge cfg c domain distinct frame alpha frameComputed
      slotSpec derived
  have readerSparse : ∀ cursor, LocalizedRule4bSparseLabel
      (ActualReaderPhysicalBranchInverse.dependencyReader input c cursor) :=
    LocalizedActualPhysicalKeySeparation.actualDependencyReader_sparse
      input singleBonded acyclic noDouble cfg c domain
  have maxTwo : input.certified.PriorTieClassAtMostTwo
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived) :=
    actual_priorTieClassAtMostTwo input.certified singleBonded acyclic
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) readerSparse
      (fun index => frame.cursorAt index)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived)
      (fun index => LocalizedActualPhysicalKeySeparation.frameSlotKey_withRead_built
        input c frame derived index)
      referenceOf references separated
  have mirror : input.certified.PriorTieMirrorReadings
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived) :=
    actual_priorTieMirrorReadings input.certified singleBonded acyclic
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) readerSparse
      (fun index => frame.cursorAt index)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived)
      (fun index => LocalizedActualPhysicalKeySeparation.frameSlotKey_withRead_built
        input c frame derived index)
      referenceOf references separated
  have correlation : ∀ i j : Fin 4,
      ActualFrameMirrorSelectorCorrelation input cfg c frame alpha derived i j :=
    actualFrameMirrorSelectorCorrelation_of_physicalForward input noDouble singleBonded acyclic
      cfg c domain frame alpha frameComputed slotSpec derived
  have bridge := frame_compoundPhysicalBridge_of_singletonSelection
    input noDouble singleBonded acyclic charge cfg c domain distinct frame alpha frameComputed
    slotSpec derived referenceOf references shape correlation
  exact exists_referenceState_descriptor_lowercase_iff_physicalCount_of_frame
    input noDouble (ActualReaderPhysicalBranchInverse.topTarget input c) frame derived
    separated maxTwo mirror center centerReal pointsAt spatial nonzero
    input.certified.detectedMultiCenterMolecule cfg c alpha bridge












theorem actual_priorTieClassAtMostTwo_of_zeroOrOne
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (distinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport
      input.certified.detectedMultiCenterMolecule cfg c i j)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (zeroOrOne : ∀ index : Fin 4,
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references = [] ∨
        ∃ reference : RS,
          (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references =
            [reference])
    (separated : input.certified.CompoundKeyOffDiagonalStrict
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived)) :
    input.certified.PriorTieClassAtMostTwo
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived) := by
  let keys := LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived
  let read := ActualReaderPhysicalBranchInverse.dependencyReader input c
  have readerSparse : ∀ cursor, LocalizedRule4bSparseLabel (read cursor) :=
    LocalizedActualPhysicalKeySeparation.actualDependencyReader_sparse
      input singleBonded acyclic noDouble cfg c domain
  have built : ∀ index : Fin 4,
      input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?
        read (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (frame.cursorAt index) = some (keys index) :=
    fun index => LocalizedActualPhysicalKeySeparation.frameSlotKey_withRead_built
      input c frame derived index
  intro i j k hij hik
  by_cases hji : j = i
  · exact Or.inr (Or.inl hji)
  by_cases hki : k = i
  · exact Or.inr (Or.inr hki)
  by_cases hjk : j = k
  · exact Or.inl hjk
  exfalso
  obtain ⟨iSingleton, jSingleton⟩ :=
    LocalizedEmptyReferencePhysicalPriorInverse.actualFrame_zeroOrOne_priorTie_singletons
      input noDouble singleBonded acyclic charge cfg c domain distinct frame alpha frameComputed
      slotSpec derived i j (Ne.symm hji) zeroOrOne hij
  obtain ⟨_, kSingleton⟩ :=
    LocalizedEmptyReferencePhysicalPriorInverse.actualFrame_zeroOrOne_priorTie_singletons
      input noDouble singleBonded acyclic charge cfg c domain distinct frame alpha frameComputed
      slotSpec derived i k (Ne.symm hki) zeroOrOne hik
  obtain ⟨refI, refIeq⟩ := iSingleton
  obtain ⟨refJ, refJeq⟩ := jSingleton
  obtain ⟨refK, refKeq⟩ := kSingleton
  have ijNe : refI ≠ refJ :=
    actual_singleton_prior_tie_references_ne_of_offDiagonalStrict input.certified singleBonded acyclic
      read readerSparse (frame.cursorAt i) (frame.cursorAt j)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      refI refJ (keys i) (keys j) (built i) (built j) refIeq refJeq hij
      (separated i j (Ne.symm hji))
  have ikNe : refI ≠ refK :=
    actual_singleton_prior_tie_references_ne_of_offDiagonalStrict input.certified singleBonded acyclic
      read readerSparse (frame.cursorAt i) (frame.cursorAt k)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      refI refK (keys i) (keys k) (built i) (built k) refIeq refKeq hik
      (separated i k (Ne.symm hki))
  have hjiTie : priorKeyTie input.certified keys j i := by
    haveI : Std.TransCmp input.certified.compareLocalizedRerootCompoundRule4bcKeys :=
      input.certified.compareLocalizedRerootCompoundRule4bcKeys_transCmp
    exact Std.OrientedCmp.eq_symm
      (cmp := input.certified.compareLocalizedRerootCompoundRule4bcKeys)
      (a := (keys i).prior) (b := (keys j).prior) hij
  have hjkTie : priorKeyTie input.certified keys j k := by
    haveI : Std.TransCmp input.certified.compareLocalizedRerootCompoundRule4bcKeys :=
      input.certified.compareLocalizedRerootCompoundRule4bcKeys_transCmp
    exact Std.TransCmp.eq_trans hjiTie hik
  have jkNe : refJ ≠ refK :=
    actual_singleton_prior_tie_references_ne_of_offDiagonalStrict input.certified singleBonded acyclic
      read readerSparse (frame.cursorAt j) (frame.cursorAt k)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      refJ refK (keys j) (keys k) (built j) (built k) refJeq refKeq hjkTie
      (separated j k hjk)
  have sameJK : refJ = refK := by
    cases refI <;> cases refJ <;> cases refK <;> simp_all
  exact jkNe sameJK





theorem actual_priorTieMirrorReadings_of_zeroOrOne
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (distinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport
      input.certified.detectedMultiCenterMolecule cfg c i j)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (zeroOrOne : ∀ index : Fin 4,
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references = [] ∨
        ∃ reference : RS,
          (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references =
            [reference])
    (separated : input.certified.CompoundKeyOffDiagonalStrict
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived)) :
    input.certified.PriorTieMirrorReadings
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived) := by
  let keys := LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived
  let read := ActualReaderPhysicalBranchInverse.dependencyReader input c
  have readerSparse : ∀ cursor, LocalizedRule4bSparseLabel (read cursor) :=
    LocalizedActualPhysicalKeySeparation.actualDependencyReader_sparse
      input singleBonded acyclic noDouble cfg c domain
  have built : ∀ index : Fin 4,
      input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?
        read (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (frame.cursorAt index) = some (keys index) :=
    fun index => LocalizedActualPhysicalKeySeparation.frameSlotKey_withRead_built
      input c frame derived index
  intro i j different tied
  obtain ⟨iSingleton, jSingleton⟩ :=
    LocalizedEmptyReferencePhysicalPriorInverse.actualFrame_zeroOrOne_priorTie_singletons
      input noDouble singleBonded acyclic charge cfg c domain distinct frame alpha frameComputed
      slotSpec derived i j different zeroOrOne tied
  obtain ⟨refI, refIeq⟩ := iSingleton
  obtain ⟨refJ, refJeq⟩ := jSingleton
  have refNe : refI ≠ refJ :=
    actual_singleton_prior_tie_references_ne_of_offDiagonalStrict input.certified singleBonded acyclic
      read readerSparse (frame.cursorAt i) (frame.cursorAt j)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      refI refJ (keys i) (keys j) (built i) (built j) refIeq refJeq tied
      (separated i j different)
  exact actual_singleton_prior_tie_mirrorReadings input.certified singleBonded acyclic read readerSparse
    (frame.cursorAt i) (frame.cursorAt j)
    (localizedOccurrenceRerootEvaluationFuel
      (LocalizedUniversalReference.carrierFuel input))
    refI refJ (keys i) (keys j) (built i) (built j) refIeq refJeq tied refNe





theorem actualCompoundKeyData_of_zeroOrOne
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (distinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport
      input.certified.detectedMultiCenterMolecule cfg c i j)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (zeroOrOne : ∀ index : Fin 4,
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references = [] ∨
        ∃ reference : RS,
          (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references =
            [reference]) :
    input.certified.ActualCompoundKeyData
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (LocalizedActualPhysicalKeySeparation.actualPhysicalView input c) := by
  have separated : input.certified.CompoundKeyOffDiagonalStrict
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived) :=
    LocalizedActualPhysicalKeySeparation.frameSlotKeys_compoundKeyOffDiagonalStrict_of_physicalDistinct
      input noDouble singleBonded acyclic charge cfg c domain distinct frame alpha frameComputed
      slotSpec derived
  have maxTwo : input.certified.PriorTieClassAtMostTwo
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived) :=
    actual_priorTieClassAtMostTwo_of_zeroOrOne input noDouble singleBonded acyclic charge cfg c
      domain distinct frame alpha frameComputed slotSpec derived zeroOrOne separated
  have mirror : input.certified.PriorTieMirrorReadings
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived) :=
    actual_priorTieMirrorReadings_of_zeroOrOne input noDouble singleBonded acyclic charge cfg c
      domain distinct frame alpha frameComputed slotSpec derived zeroOrOne separated
  exact input.certified.actualCompoundKeyData_of_frame
    (ActualReaderPhysicalBranchInverse.topTarget input c)
    (LocalizedActualPhysicalKeySeparation.actualPhysicalView input c)
    frame derived frameComputed separated maxTwo mirror








theorem exists_referenceState_descriptor_lowercase_iff_physicalCount_of_zeroOrOne
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (distinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport
      input.certified.detectedMultiCenterMolecule cfg c i j)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (zeroOrOne : ∀ index : Fin 4,
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references = [] ∨
        ∃ reference : RS,
          (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references =
            [reference])
    (shape : ∀ i j : Fin 4, i ≠ j →
      MirrorTransport input.certified.detectedMultiCenterMolecule cfg c (alpha i) (alpha j) →
      LocalizedPhysicalCompoundSelectorShape
        ((LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived i).prior.references)
        ((LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived j).prior.references)
        true)
    (center : input.certified.TetrahedralCenter)
    (centerReal : input.certified.RealTetrahedralCenterNode
      (ActualReaderPhysicalBranchInverse.topTarget input c).1.node center)
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint?
        (frame.cursorAt index) = some (pointsAt index))
    (nonzero : CartesianPoint3.orientedVolume
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0) :
    ∃ descriptor : LocalizedTetrahedralRSPseudoDescriptor,
      LocalizedUniversalReference.referenceState input
          (ActualReaderPhysicalBranchInverse.topTarget input c) = some descriptor ∧
        (descriptor.IsLowercase ↔
          physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule cfg c = 1) := by
  have separated : input.certified.CompoundKeyOffDiagonalStrict
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived) :=
    LocalizedActualPhysicalKeySeparation.frameSlotKeys_compoundKeyOffDiagonalStrict_of_physicalDistinct
      input noDouble singleBonded acyclic charge cfg c domain distinct frame alpha frameComputed
      slotSpec derived
  have maxTwo : input.certified.PriorTieClassAtMostTwo
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived) :=
    actual_priorTieClassAtMostTwo_of_zeroOrOne input noDouble singleBonded acyclic charge cfg c
      domain distinct frame alpha frameComputed slotSpec derived zeroOrOne separated
  have mirror : input.certified.PriorTieMirrorReadings
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived) :=
    actual_priorTieMirrorReadings_of_zeroOrOne input noDouble singleBonded acyclic charge cfg c
      domain distinct frame alpha frameComputed slotSpec derived zeroOrOne separated
  have correlation : ∀ i j : Fin 4,
      ActualFrameMirrorSelectorCorrelation input cfg c frame alpha derived i j :=
    actualFrameMirrorSelectorCorrelation_of_physicalForward input noDouble singleBonded acyclic
      cfg c domain frame alpha frameComputed slotSpec derived
  have bridge := frame_compoundPhysicalBridge_of_zeroOrOne
    input noDouble singleBonded acyclic charge cfg c domain distinct frame alpha frameComputed
    slotSpec derived zeroOrOne shape correlation
  exact exists_referenceState_descriptor_lowercase_iff_physicalCount_of_frame
    input noDouble (ActualReaderPhysicalBranchInverse.topTarget input c) frame derived
    separated maxTwo mirror center centerReal pointsAt spatial nonzero
    input.certified.detectedMultiCenterMolecule cfg c alpha bridge










theorem exists_referenceState_descriptor_lowercase_iff_physicalCount_of_zeroOrOne_canonicalGeometry
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (distinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport
      input.certified.detectedMultiCenterMolecule cfg c i j)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (zeroOrOne : ∀ index : Fin 4,
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references = [] ∨
        ∃ reference : RS,
          (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references =
            [reference])
    (shape : ∀ i j : Fin 4, i ≠ j →
      MirrorTransport input.certified.detectedMultiCenterMolecule cfg c (alpha i) (alpha j) →
      LocalizedPhysicalCompoundSelectorShape
        ((LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived i).prior.references)
        ((LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived j).prior.references)
        true)
    (coordinates : input.certified.ActualCanonicalRootCoordinates
      (⟨c.1, c.2⟩ : input.certified.TetrahedralCenter)) :
    ∃ descriptor : LocalizedTetrahedralRSPseudoDescriptor,
      LocalizedUniversalReference.referenceState input
          (ActualReaderPhysicalBranchInverse.topTarget input c) = some descriptor ∧
        (descriptor.IsLowercase ↔
          physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule cfg c = 1) := by
  classical
  let center : input.certified.TetrahedralCenter := ⟨c.1, c.2⟩
  have targetCurrent : (ActualReaderPhysicalBranchInverse.topTarget input c).1.node.current? =
      some center.1 := by
    simpa [center] using ActualReaderPhysicalBranchInverse.topTarget_current input c
  have realNode : input.certified.ActualFrameRealNodeCoordinates
      (ActualReaderPhysicalBranchInverse.topTarget input c) :=
    input.certified.actualFrameRealNodeCoordinates_of_actualCanonicalRootCoordinates
      (ActualReaderPhysicalBranchInverse.topTarget input c) singleBonded acyclic enough center
      targetCurrent coordinates
  obtain ⟨pointsAt, spatial, nonzero⟩ :=
    input.certified.actualFrameSpatialCoordinates_of_realNode
      (ActualReaderPhysicalBranchInverse.topTarget input c) realNode frame frameComputed
  have centerReal : input.certified.RealTetrahedralCenterNode
      (ActualReaderPhysicalBranchInverse.topTarget input c).1.node center := by
    constructor
    · simp [center, ActualReaderPhysicalBranchInverse.topTarget,
        CertifiedLocalizedCIPInput.localizedFinalOccurrence, OfficialCIPNode.root]
    · exact targetCurrent
  exact exists_referenceState_descriptor_lowercase_iff_physicalCount_of_zeroOrOne
    input noDouble singleBonded acyclic charge cfg c domain distinct frame alpha frameComputed
    slotSpec derived zeroOrOne shape center centerReal pointsAt spatial nonzero















theorem referenceState_prepared_and_production_descriptor
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (descriptor : LocalizedTetrahedralRSPseudoDescriptor)
    (stateEq : LocalizedUniversalReference.referenceState input target = some descriptor) :
    input.certified.universalDescriptor? target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target) = some descriptor ∧
      input.certified.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target) = some descriptor := by
  constructor
  · rw [← LocalizedUniversalReference.referenceState_eq_preparedUniversalDescriptor input target]
    exact stateEq
  · rw [← LocalizedUniversalReference.referenceState_eq_productionExtendedDescriptor_of_noDoubleRecords
      input noDouble target]
    exact stateEq

/-- **Actual evaluator values for the canonical-geometry root-Z endpoint.**  This is the same
physical theorem as `..._of_zeroOrOne_canonicalGeometry`, with the resulting descriptor additionally
identified as the value of the actual prepared universal descriptor and of the actual production
extended Rules-3--5 descriptor at the generated state's dependency view. -/
theorem exists_prepared_and_production_descriptor_iff_physicalCount_of_zeroOrOne_canonicalGeometry
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (distinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport
      input.certified.detectedMultiCenterMolecule cfg c i j)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (zeroOrOne : ∀ index : Fin 4,
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references = [] ∨
        ∃ reference : RS,
          (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references =
            [reference])
    (shape : ∀ i j : Fin 4, i ≠ j →
      MirrorTransport input.certified.detectedMultiCenterMolecule cfg c (alpha i) (alpha j) →
      LocalizedPhysicalCompoundSelectorShape
        ((LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived i).prior.references)
        ((LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived j).prior.references)
        true)
    (coordinates : input.certified.ActualCanonicalRootCoordinates
      (⟨c.1, c.2⟩ : input.certified.TetrahedralCenter)) :
    ∃ descriptor : LocalizedTetrahedralRSPseudoDescriptor,
      LocalizedUniversalReference.referenceState input
          (ActualReaderPhysicalBranchInverse.topTarget input c) = some descriptor ∧
        input.certified.universalDescriptor?
            (ActualReaderPhysicalBranchInverse.topTarget input c)
            (input.certified.localizedDependencyView
              (LocalizedUniversalReference.referenceState input)
              (ActualReaderPhysicalBranchInverse.topTarget input c)) = some descriptor ∧
          input.certified.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
              (ActualReaderPhysicalBranchInverse.topTarget input c)
              (input.certified.localizedDependencyView
                (LocalizedUniversalReference.referenceState input)
                (ActualReaderPhysicalBranchInverse.topTarget input c)) = some descriptor ∧
            (descriptor.IsLowercase ↔
              physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule cfg c = 1) := by
  obtain ⟨descriptor, stateEq, lowercase⟩ :=
    exists_referenceState_descriptor_lowercase_iff_physicalCount_of_zeroOrOne_canonicalGeometry
      input noDouble singleBonded acyclic charge enough cfg c domain distinct frame alpha
      frameComputed slotSpec derived zeroOrOne shape coordinates
  obtain ⟨prepared, production⟩ :=
    referenceState_prepared_and_production_descriptor input noDouble
      (ActualReaderPhysicalBranchInverse.topTarget input c) descriptor stateEq
  exact ⟨descriptor, stateEq, prepared, production, lowercase⟩



















theorem actual_priorTieClassAtMostTwo_of_zeroOrOne_generalDomain
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (distinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport
      input.certified.detectedMultiCenterMolecule cfg c i j)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (zeroOrOne : ∀ index : Fin 4,
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references = [] ∨
        ∃ reference : RS,
          (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references =
            [reference])
    (separated : input.certified.CompoundKeyOffDiagonalStrict
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived)) :
    input.certified.PriorTieClassAtMostTwo
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived) := by
  let keys := LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived
  let read := ActualReaderPhysicalBranchInverse.dependencyReader input c
  have readerSparse : ∀ cursor, LocalizedRule4bSparseLabel (read cursor) :=
    LocalizedGeneralRigidPhysicalKeySeparation.actualDependencyReader_sparse_of_physicalDomain
      input singleBonded acyclic charge noDouble cfg c domain
  have built : ∀ index : Fin 4,
      input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?
        read (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (frame.cursorAt index) = some (keys index) :=
    fun index => LocalizedActualPhysicalKeySeparation.frameSlotKey_withRead_built
      input c frame derived index
  intro i j k hij hik
  by_cases hji : j = i
  · exact Or.inr (Or.inl hji)
  by_cases hki : k = i
  · exact Or.inr (Or.inr hki)
  by_cases hjk : j = k
  · exact Or.inl hjk
  exfalso
  obtain ⟨iSingleton, jSingleton, _⟩ :=
    LocalizedGeneralRigidPhysicalKeySeparation.actualFrame_zeroOrOne_priorTie_enantiomorphic_and_singletons_of_physicalDomain
      input singleBonded acyclic charge noDouble cfg c domain distinct frame alpha frameComputed
      slotSpec derived i j (Ne.symm hji) zeroOrOne hij
  obtain ⟨_, kSingleton, _⟩ :=
    LocalizedGeneralRigidPhysicalKeySeparation.actualFrame_zeroOrOne_priorTie_enantiomorphic_and_singletons_of_physicalDomain
      input singleBonded acyclic charge noDouble cfg c domain distinct frame alpha frameComputed
      slotSpec derived i k (Ne.symm hki) zeroOrOne hik
  obtain ⟨refI, refIeq⟩ := iSingleton
  obtain ⟨refJ, refJeq⟩ := jSingleton
  obtain ⟨refK, refKeq⟩ := kSingleton
  have ijNe : refI ≠ refJ :=
    actual_singleton_prior_tie_references_ne_of_offDiagonalStrict input.certified singleBonded acyclic
      read readerSparse (frame.cursorAt i) (frame.cursorAt j)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      refI refJ (keys i) (keys j) (built i) (built j) refIeq refJeq hij
      (separated i j (Ne.symm hji))
  have ikNe : refI ≠ refK :=
    actual_singleton_prior_tie_references_ne_of_offDiagonalStrict input.certified singleBonded acyclic
      read readerSparse (frame.cursorAt i) (frame.cursorAt k)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      refI refK (keys i) (keys k) (built i) (built k) refIeq refKeq hik
      (separated i k (Ne.symm hki))
  have hjiTie : priorKeyTie input.certified keys j i := by
    haveI : Std.TransCmp input.certified.compareLocalizedRerootCompoundRule4bcKeys :=
      input.certified.compareLocalizedRerootCompoundRule4bcKeys_transCmp
    exact Std.OrientedCmp.eq_symm
      (cmp := input.certified.compareLocalizedRerootCompoundRule4bcKeys)
      (a := (keys i).prior) (b := (keys j).prior) hij
  have hjkTie : priorKeyTie input.certified keys j k := by
    haveI : Std.TransCmp input.certified.compareLocalizedRerootCompoundRule4bcKeys :=
      input.certified.compareLocalizedRerootCompoundRule4bcKeys_transCmp
    exact Std.TransCmp.eq_trans hjiTie hik
  have jkNe : refJ ≠ refK :=
    actual_singleton_prior_tie_references_ne_of_offDiagonalStrict input.certified singleBonded acyclic
      read readerSparse (frame.cursorAt j) (frame.cursorAt k)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      refJ refK (keys j) (keys k) (built j) (built k) refJeq refKeq hjkTie
      (separated j k hjk)
  have sameJK : refJ = refK := by
    cases refI <;> cases refJ <;> cases refK <;> simp_all
  exact jkNe sameJK




theorem actual_priorTieMirrorReadings_of_zeroOrOne_generalDomain
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (distinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport
      input.certified.detectedMultiCenterMolecule cfg c i j)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (zeroOrOne : ∀ index : Fin 4,
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references = [] ∨
        ∃ reference : RS,
          (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references =
            [reference])
    (separated : input.certified.CompoundKeyOffDiagonalStrict
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived)) :
    input.certified.PriorTieMirrorReadings
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived) := by
  let keys := LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived
  let read := ActualReaderPhysicalBranchInverse.dependencyReader input c
  have readerSparse : ∀ cursor, LocalizedRule4bSparseLabel (read cursor) :=
    LocalizedGeneralRigidPhysicalKeySeparation.actualDependencyReader_sparse_of_physicalDomain
      input singleBonded acyclic charge noDouble cfg c domain
  have built : ∀ index : Fin 4,
      input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?
        read (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (frame.cursorAt index) = some (keys index) :=
    fun index => LocalizedActualPhysicalKeySeparation.frameSlotKey_withRead_built
      input c frame derived index
  intro i j different tied
  obtain ⟨iSingleton, jSingleton, _⟩ :=
    LocalizedGeneralRigidPhysicalKeySeparation.actualFrame_zeroOrOne_priorTie_enantiomorphic_and_singletons_of_physicalDomain
      input singleBonded acyclic charge noDouble cfg c domain distinct frame alpha frameComputed
      slotSpec derived i j different zeroOrOne tied
  obtain ⟨refI, refIeq⟩ := iSingleton
  obtain ⟨refJ, refJeq⟩ := jSingleton
  have refNe : refI ≠ refJ :=
    actual_singleton_prior_tie_references_ne_of_offDiagonalStrict input.certified singleBonded acyclic
      read readerSparse (frame.cursorAt i) (frame.cursorAt j)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      refI refJ (keys i) (keys j) (built i) (built j) refIeq refJeq tied
      (separated i j different)
  exact actual_singleton_prior_tie_mirrorReadings input.certified singleBonded acyclic read readerSparse
    (frame.cursorAt i) (frame.cursorAt j)
    (localizedOccurrenceRerootEvaluationFuel
      (LocalizedUniversalReference.carrierFuel input))
    refI refJ (keys i) (keys j) (built i) (built j) refIeq refJeq tied refNe



theorem framePriorTie_implies_enantiomorphic_of_zeroOrOne_generalDomain
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (distinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport
      input.certified.detectedMultiCenterMolecule cfg c i j)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (zeroOrOne : ∀ index : Fin 4,
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references = [] ∨
        ∃ reference : RS,
          (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references =
            [reference])
    {i j : Fin 4} (different : i ≠ j)
    (priorTie : compoundPriorTieRelation input.certified
      (frame.compoundKeyAt input.certified
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (LocalizedActualPhysicalKeySeparation.actualPhysicalView input c) derived) i j) :
    Enantiomorphic input.certified.detectedMultiCenterMolecule cfg c (alpha i) (alpha j) :=
  (LocalizedGeneralRigidPhysicalKeySeparation.actualFrame_zeroOrOne_priorTie_enantiomorphic_and_singletons_of_physicalDomain
    input singleBonded acyclic charge noDouble cfg c domain distinct frame alpha frameComputed
    slotSpec derived i j different zeroOrOne priorTie.2).2.2















theorem exists_referenceState_descriptor_lowercase_iff_physicalCount_of_zeroOrOne_generalDomain
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (distinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport
      input.certified.detectedMultiCenterMolecule cfg c i j)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (zeroOrOne : ∀ index : Fin 4,
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references = [] ∨
        ∃ reference : RS,
          (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references =
            [reference])
    (shape : ∀ i j : Fin 4, i ≠ j →
      MirrorTransport input.certified.detectedMultiCenterMolecule cfg c (alpha i) (alpha j) →
      LocalizedPhysicalCompoundSelectorShape
        ((LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived i).prior.references)
        ((LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived j).prior.references)
        true)
    (correlation : ∀ i j : Fin 4,
      ActualFrameMirrorSelectorCorrelation input cfg c frame alpha derived i j)
    (coordinates : input.certified.ActualCanonicalRootCoordinates
      (⟨c.1, c.2⟩ : input.certified.TetrahedralCenter)) :
    ∃ descriptor : LocalizedTetrahedralRSPseudoDescriptor,
      LocalizedUniversalReference.referenceState input
          (ActualReaderPhysicalBranchInverse.topTarget input c) = some descriptor ∧
        (descriptor.IsLowercase ↔
          physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule cfg c = 1) := by
  classical
  let center : input.certified.TetrahedralCenter := ⟨c.1, c.2⟩
  have separated : input.certified.CompoundKeyOffDiagonalStrict
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived) :=
    LocalizedGeneralRigidPhysicalKeySeparation.compoundKeyOffDiagonalStrict_of_physicalRootDistinct_of_physicalDomain
      input noDouble singleBonded acyclic charge cfg c domain distinct frame alpha frameComputed
      slotSpec derived
  have maxTwo : input.certified.PriorTieClassAtMostTwo
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived) :=
    actual_priorTieClassAtMostTwo_of_zeroOrOne_generalDomain input noDouble singleBonded acyclic
      charge cfg c domain distinct frame alpha frameComputed slotSpec derived zeroOrOne separated
  have mirror : input.certified.PriorTieMirrorReadings
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived) :=
    actual_priorTieMirrorReadings_of_zeroOrOne_generalDomain input noDouble singleBonded acyclic
      charge cfg c domain distinct frame alpha frameComputed slotSpec derived zeroOrOne separated
  have bridge : ∀ i j : Fin 4,
      compoundPriorTieRelation input.certified
          (frame.compoundKeyAt input.certified
            (ActualReaderPhysicalBranchInverse.topTarget input c)
            (LocalizedActualPhysicalKeySeparation.actualPhysicalView input c) derived) i j ↔
        Enantiomorphic input.certified.detectedMultiCenterMolecule cfg c (alpha i) (alpha j) := by
    intro i j
    constructor
    · intro priorTie
      exact framePriorTie_implies_enantiomorphic_of_zeroOrOne_generalDomain input noDouble
        singleBonded acyclic charge cfg c domain distinct frame alpha frameComputed slotSpec derived
        zeroOrOne priorTie.1 priorTie
    · intro enantiomorphic
      have reverse := correlation (alpha i) (alpha j) enantiomorphic.1
        (by
          simpa only [Equiv.symm_apply_apply] using
            shape i j (fun same => enantiomorphic.1 (congrArg alpha same))
              enantiomorphic.2.1)
        enantiomorphic.2.1
      simpa using reverse
  have targetCurrent : (ActualReaderPhysicalBranchInverse.topTarget input c).1.node.current? =
      some center.1 := by
    simpa [center] using ActualReaderPhysicalBranchInverse.topTarget_current input c
  have realNode : input.certified.ActualFrameRealNodeCoordinates
      (ActualReaderPhysicalBranchInverse.topTarget input c) :=
    input.certified.actualFrameRealNodeCoordinates_of_actualCanonicalRootCoordinates
      (ActualReaderPhysicalBranchInverse.topTarget input c) singleBonded acyclic enough center
      targetCurrent coordinates
  obtain ⟨pointsAt, spatial, nonzero⟩ :=
    input.certified.actualFrameSpatialCoordinates_of_realNode
      (ActualReaderPhysicalBranchInverse.topTarget input c) realNode frame frameComputed
  have centerReal : input.certified.RealTetrahedralCenterNode
      (ActualReaderPhysicalBranchInverse.topTarget input c).1.node center := by
    constructor
    · simp [center, ActualReaderPhysicalBranchInverse.topTarget,
        CertifiedLocalizedCIPInput.localizedFinalOccurrence, OfficialCIPNode.root]
    · exact targetCurrent
  exact exists_referenceState_descriptor_lowercase_iff_physicalCount_of_frame
    input noDouble (ActualReaderPhysicalBranchInverse.topTarget input c) frame derived
    separated maxTwo mirror center centerReal pointsAt spatial nonzero
    input.certified.detectedMultiCenterMolecule cfg c alpha bridge






















theorem actualSlotCompoundKey_eq_frameSlotKey
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (slot : Fin 4) :
    actualSlotCompoundKey input c frame frameComputed slot =
      LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived slot := by
  show frame.compoundKeyAt input.certified
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (actualSlotDerived input c frame frameComputed) slot =
    frame.compoundKeyAt input.certified
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      derived slot
  exact congrArg
    (fun d : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
        (ActualReaderPhysicalBranchInverse.topTarget input c) frame =>
      frame.compoundKeyAt input.certified
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (referenceDependencyView input c) d slot)
    (Subsingleton.elim (actualSlotDerived input c frame frameComputed) derived)






theorem frameSlotKey_references_zero_or_singleton_of_physicalDomain
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (branchDomains : ∀ index : Fin 4,
      PhysicalBranchDomain input ⟨c.1, c.2⟩
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt c index)) :
    ∀ index : Fin 4,
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references = [] ∨
        ∃ reference : RS,
          (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references =
            [reference] := by
  intro index
  let oAtom : input.certified.Atom :=
    input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)
  have oObserved : (frame.cursorAt index).occurrence.1.node.current? = some oAtom := by
    simpa [oAtom] using slotSpec index
  have branchDomain : PhysicalBranchDomain input ⟨c.1, c.2⟩ oAtom := by
    simpa [oAtom] using branchDomains (alpha index)
  have selection := actualSlot_physicalBranchDomain_references_zero_or_singleton_of_physicalDomain
    input c frame frameComputed index singleBonded acyclic charge noDouble cfg domain
    oAtom oObserved branchDomain
  rcases selection with unmarked | ⟨center, distance, descriptor, unique, markedDescriptor,
      rankedSingle, referencesSingle, reading, readings, referenceSome⟩
  · left
    simpa [actualSlotCompoundKey_eq_frameSlotKey input c frame frameComputed derived index] using
      unmarked.2.1
  · right
    exact ⟨descriptor, by
      simpa [actualSlotCompoundKey_eq_frameSlotKey input c frame frameComputed derived index] using
        referencesSingle⟩






theorem frameSlotKey_selectorShape_of_mirrorTransport
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (branchDomains : ∀ index : Fin 4,
      PhysicalBranchDomain input ⟨c.1, c.2⟩
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt c index)) :
    ∀ i j : Fin 4, i ≠ j →
      MirrorTransport input.certified.detectedMultiCenterMolecule cfg c (alpha i) (alpha j) →
      LocalizedPhysicalCompoundSelectorShape
        ((LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived i).prior.references)
        ((LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived j).prior.references)
        true := by
  intro i j _different transport
  obtain ⟨e, hc, hi, signLaw⟩ := transport
  let oAtomLeft : input.certified.Atom :=
    input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha i)
  let oAtomRight : input.certified.Atom :=
    input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha j)
  have oObservedLeft : (frame.cursorAt i).occurrence.1.node.current? = some oAtomLeft := by
    simpa [oAtomLeft] using slotSpec i
  have oObservedRight : (frame.cursorAt j).occurrence.1.node.current? = some oAtomRight := by
    simpa [oAtomRight] using slotSpec j
  have leftDomain : PhysicalBranchDomain input ⟨c.1, c.2⟩ oAtomLeft := by
    simpa [oAtomLeft] using branchDomains (alpha i)
  have shapeRanked :=
    LocalizedPhysicalReferenceCovariance.localizedPhysicalCompoundSelectorShape_references_of_physicalBranchTransport_of_physicalDomain
      input singleBonded acyclic charge noDouble c cfg domain
      frame frameComputed i j oAtomLeft oAtomRight oObservedLeft oObservedRight
      (i := alpha i) (j := alpha j) (e := e) hc hi true signLaw rfl rfl leftDomain
  simpa only [actualSlotCompoundKey_eq_frameSlotKey input c frame frameComputed derived i,
    actualSlotCompoundKey_eq_frameSlotKey input c frame frameComputed derived j] using
    shapeRanked










theorem actualFrameMirrorSelectorCorrelation_of_physicalForward_generalDomain
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame) :
    ∀ i j : Fin 4,
      ActualFrameMirrorSelectorCorrelation input cfg c frame alpha derived i j := by
  intro i j different shape transport
  obtain ⟨frame', alpha', frameComputed', slotSpec', _, _, forward⟩ :=
    localizedGeneralRigidPhysicalCompound_transport_priorTie_and_commonReading
      input singleBonded acyclic charge noDouble cfg c i j true transport domain
  have hOcc : localizedPhysicalTopOccurrence input
      input.certified.detectedMultiCenterMolecule domain.graphEq c =
      ActualReaderPhysicalBranchInverse.topTarget input c := by
    have hcenter : localizedPhysicalTopCenter input
        input.certified.detectedMultiCenterMolecule domain.graphEq c =
        (⟨c.1, c.2⟩ : input.certified.TetrahedralCenter) :=
      Subtype.ext rfl
    unfold localizedPhysicalTopOccurrence ActualReaderPhysicalBranchInverse.topTarget
    rw [hcenter]
  have frameEq : frame' = frame := by
    have h := frameComputed'
    rw [hOcc] at h
    exact Option.some.inj (h.symm.trans frameComputed)
  have alphaEq : alpha' = alpha := by
    apply Equiv.ext
    intro index
    apply input.certified.detectedMultiCenterMolecule.ligandAtomAt_injective c
    have h := slotSpec' index
    rw [frameEq] at h
    exact Option.some.inj (h.symm.trans (slotSpec index))
  have shape' : LocalizedPhysicalCompoundSelectorShape
      ((localizedPhysicalCompoundFrameKeyOfComputed input
        input.certified.detectedMultiCenterMolecule domain.graphEq c frame' frameComputed'
        (alpha'.symm i)).prior.references)
      ((localizedPhysicalCompoundFrameKeyOfComputed input
        input.certified.detectedMultiCenterMolecule domain.graphEq c frame' frameComputed'
        (alpha'.symm j)).prior.references) true := by
    simpa [localizedPhysicalCompoundFrameKeyOfComputed,
      LocalizedActualPhysicalKeySeparation.frameSlotKey,
      localizedPhysicalCompoundFrameView,
      LocalizedActualPhysicalKeySeparation.actualPhysicalView,
      hOcc, frameEq, alphaEq] using shape
  obtain ⟨_, _, _, _, priorTie, _⟩ := forward shape'
  refine ⟨?_, ?_⟩
  · intro same
    exact different (alpha.symm.injective same)
  · simpa [compoundPriorTieRelation, priorKeyTie,
      localizedPhysicalCompoundFrameKeyOfComputed,
      LocalizedActualPhysicalKeySeparation.frameSlotKey,
      localizedPhysicalCompoundFrameView,
      LocalizedActualPhysicalKeySeparation.actualPhysicalView,
      hOcc, frameEq, alphaEq] using priorTie














theorem exists_referenceState_descriptor_lowercase_iff_physicalCount_of_physicalDomain
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (distinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport
      input.certified.detectedMultiCenterMolecule cfg c i j)
    (branchDomains : ∀ index : Fin 4,
      PhysicalBranchDomain input ⟨c.1, c.2⟩
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt c index))
    (coordinates : input.certified.ActualCanonicalRootCoordinates
      (⟨c.1, c.2⟩ : input.certified.TetrahedralCenter)) :
    ∃ descriptor : LocalizedTetrahedralRSPseudoDescriptor,
      LocalizedUniversalReference.referenceState input
          (ActualReaderPhysicalBranchInverse.topTarget input c) = some descriptor ∧
        (descriptor.IsLowercase ↔
          physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule cfg c = 1) := by
  classical
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input :=
    globalCarrierFuel_adequate input
  have targetCurrent : (ActualReaderPhysicalBranchInverse.topTarget input c).1.node.current? =
      some c.1 :=
    ActualReaderPhysicalBranchInverse.topTarget_current input c
  obtain ⟨frame, alpha, frameComputed, slotSpec⟩ :=
    input.certified.exists_localizedOccurrenceFourLigandFrame_and_ligandPermutation_detected
      singleBonded acyclic enough (ActualReaderPhysicalBranchInverse.topTarget input c)
      targetCurrent c rfl
  have derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame :=
    (input.certified.localizedOccurrenceFourLigandFrame?_eq_some_iff
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame).mp frameComputed
  have zeroOrOne : ∀ index : Fin 4,
      (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references = [] ∨
        ∃ reference : RS,
          (LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived index).prior.references =
            [reference] :=
    frameSlotKey_references_zero_or_singleton_of_physicalDomain input noDouble singleBonded acyclic
      charge cfg c domain frame alpha frameComputed slotSpec derived branchDomains
  have shape : ∀ i j : Fin 4, i ≠ j →
      MirrorTransport input.certified.detectedMultiCenterMolecule cfg c (alpha i) (alpha j) →
      LocalizedPhysicalCompoundSelectorShape
        ((LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived i).prior.references)
        ((LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame derived j).prior.references)
        true :=
    frameSlotKey_selectorShape_of_mirrorTransport input noDouble singleBonded acyclic charge cfg c
      domain frame alpha frameComputed slotSpec derived branchDomains
  have correlation : ∀ i j : Fin 4,
      ActualFrameMirrorSelectorCorrelation input cfg c frame alpha derived i j :=
    actualFrameMirrorSelectorCorrelation_of_physicalForward_generalDomain input noDouble
      singleBonded acyclic charge cfg c domain frame alpha frameComputed slotSpec derived
  exact exists_referenceState_descriptor_lowercase_iff_physicalCount_of_zeroOrOne_generalDomain
    input noDouble singleBonded acyclic charge enough cfg c domain distinct frame alpha frameComputed
    slotSpec derived zeroOrOne shape correlation coordinates

/-- **Actual evaluator values for the physical-only endpoint.**  This is the same physical theorem
as `..._of_physicalDomain`, with the resulting descriptor additionally identified as the value of
the actual prepared universal descriptor and of the actual production extended Rules-3--5 descriptor
at the generated state's dependency view. -/
theorem exists_prepared_and_production_descriptor_iff_physicalCount_of_physicalDomain
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (distinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport
      input.certified.detectedMultiCenterMolecule cfg c i j)
    (branchDomains : ∀ index : Fin 4,
      PhysicalBranchDomain input ⟨c.1, c.2⟩
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt c index))
    (coordinates : input.certified.ActualCanonicalRootCoordinates
      (⟨c.1, c.2⟩ : input.certified.TetrahedralCenter)) :
    ∃ descriptor : LocalizedTetrahedralRSPseudoDescriptor,
      LocalizedUniversalReference.referenceState input
          (ActualReaderPhysicalBranchInverse.topTarget input c) = some descriptor ∧
        input.certified.universalDescriptor?
            (ActualReaderPhysicalBranchInverse.topTarget input c)
            (input.certified.localizedDependencyView
              (LocalizedUniversalReference.referenceState input)
              (ActualReaderPhysicalBranchInverse.topTarget input c)) = some descriptor ∧
          input.certified.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
              (ActualReaderPhysicalBranchInverse.topTarget input c)
              (input.certified.localizedDependencyView
                (LocalizedUniversalReference.referenceState input)
                (ActualReaderPhysicalBranchInverse.topTarget input c)) = some descriptor ∧
            (descriptor.IsLowercase ↔
              physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule cfg c = 1) := by
  obtain ⟨descriptor, stateEq, lowercase⟩ :=
    exists_referenceState_descriptor_lowercase_iff_physicalCount_of_physicalDomain
      input noDouble singleBonded acyclic charge cfg c domain distinct branchDomains coordinates
  obtain ⟨prepared, production⟩ :=
    referenceState_prepared_and_production_descriptor input noDouble
      (ActualReaderPhysicalBranchInverse.topTarget input c) descriptor stateEq
  exact ⟨descriptor, stateEq, prepared, production, lowercase⟩

/-- **Actual evaluator facts lookup for the physical-only endpoint.**  The generated
`referenceState` is definitionally the lookup of the generated certificate facts, and
`evaluate_state` proves every evaluation result (accepted or generated) computes that same unique
state.  This corollary therefore exposes the top-level `evaluate` facts lookup directly: for any
proposed node list the evaluated facts carry the descriptor at the final root, and its lowercase
flag is exactly the physical enantiomorphic pair count being one. -/
theorem exists_evaluate_descriptor_lowercase_iff_physicalCount_of_physicalDomain
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (distinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport
      input.certified.detectedMultiCenterMolecule cfg c i j)
    (branchDomains : ∀ index : Fin 4,
      PhysicalBranchDomain input ⟨c.1, c.2⟩
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt c index))
    (coordinates : input.certified.ActualCanonicalRootCoordinates
      (⟨c.1, c.2⟩ : input.certified.TetrahedralCenter))
    (nodes : LocalizedUniversalReference.Nodes input) :
    ∃ descriptor : LocalizedTetrahedralRSPseudoDescriptor,
      TetraStereo.Certificate.Dependency.lookup
          (LocalizedUniversalReference.evaluate input nodes).facts
          (ActualReaderPhysicalBranchInverse.topTarget input c) = some descriptor ∧
        (descriptor.IsLowercase ↔
          physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule cfg c = 1) := by
  obtain ⟨descriptor, stateEq, lowercase⟩ :=
    exists_referenceState_descriptor_lowercase_iff_physicalCount_of_physicalDomain
      input noDouble singleBonded acyclic charge cfg c domain distinct branchDomains coordinates
  refine ⟨descriptor, ?_, lowercase⟩
  rw [LocalizedUniversalReference.evaluate_state input nodes]
  exact stateEq

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.ActualFrameCompoundPhysicalBridge
assert_kernel_only TetraStereo.OneCenter.sourceEnantiomorphicPairCount_compoundPriorTieRelation_eq_frameEnumeratedPairCount
assert_kernel_only TetraStereo.OneCenter.sourceEnantiomorphicPairCount_compoundPriorTieRelation_eq_physicalCount
assert_kernel_only TetraStereo.OneCenter.exists_referenceState_descriptor_lowercase_iff_physicalCount_of_priorTieBridge
assert_kernel_only TetraStereo.OneCenter.exists_referenceState_descriptor_lowercase_iff_physicalCount_of_frame
assert_kernel_only TetraStereo.OneCenter.framePriorTie_implies_enantiomorphic
assert_kernel_only TetraStereo.OneCenter.ActualFrameMirrorSelectorCorrelation
assert_kernel_only TetraStereo.OneCenter.frame_enantiomorphic_implies_priorTie_of_selectorCorrelation
assert_kernel_only TetraStereo.OneCenter.actualCompoundKeyData_of_singletonSelection
assert_kernel_only TetraStereo.OneCenter.frame_compoundPhysicalBridge_of_singletonSelection
assert_kernel_only TetraStereo.OneCenter.exists_referenceState_descriptor_lowercase_iff_physicalCount_of_singletonSelection
assert_kernel_only TetraStereo.OneCenter.framePriorTie_implies_enantiomorphic_of_zeroOrOne
assert_kernel_only TetraStereo.OneCenter.frame_compoundPhysicalBridge_of_zeroOrOne
assert_kernel_only TetraStereo.OneCenter.actualFrameMirrorSelectorCorrelation_of_physicalForward
assert_kernel_only TetraStereo.OneCenter.actual_priorTieClassAtMostTwo_of_zeroOrOne
assert_kernel_only TetraStereo.OneCenter.actual_priorTieMirrorReadings_of_zeroOrOne
assert_kernel_only TetraStereo.OneCenter.actualCompoundKeyData_of_zeroOrOne
assert_kernel_only TetraStereo.OneCenter.exists_referenceState_descriptor_lowercase_iff_physicalCount_of_zeroOrOne
assert_kernel_only TetraStereo.OneCenter.exists_referenceState_descriptor_lowercase_iff_physicalCount_of_zeroOrOne_canonicalGeometry
assert_kernel_only TetraStereo.OneCenter.referenceState_prepared_and_production_descriptor
assert_kernel_only TetraStereo.OneCenter.exists_prepared_and_production_descriptor_iff_physicalCount_of_zeroOrOne_canonicalGeometry
assert_kernel_only TetraStereo.OneCenter.actual_priorTieClassAtMostTwo_of_zeroOrOne_generalDomain
assert_kernel_only TetraStereo.OneCenter.actual_priorTieMirrorReadings_of_zeroOrOne_generalDomain
assert_kernel_only TetraStereo.OneCenter.framePriorTie_implies_enantiomorphic_of_zeroOrOne_generalDomain
assert_kernel_only TetraStereo.OneCenter.exists_referenceState_descriptor_lowercase_iff_physicalCount_of_zeroOrOne_generalDomain
assert_kernel_only TetraStereo.OneCenter.actualSlotCompoundKey_eq_frameSlotKey
assert_kernel_only TetraStereo.OneCenter.frameSlotKey_references_zero_or_singleton_of_physicalDomain
assert_kernel_only TetraStereo.OneCenter.frameSlotKey_selectorShape_of_mirrorTransport
assert_kernel_only TetraStereo.OneCenter.actualFrameMirrorSelectorCorrelation_of_physicalForward_generalDomain
assert_kernel_only TetraStereo.OneCenter.exists_referenceState_descriptor_lowercase_iff_physicalCount_of_physicalDomain
assert_kernel_only TetraStereo.OneCenter.exists_prepared_and_production_descriptor_iff_physicalCount_of_physicalDomain
assert_kernel_only TetraStereo.OneCenter.exists_evaluate_descriptor_lowercase_iff_physicalCount_of_physicalDomain
