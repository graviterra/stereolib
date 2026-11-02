import TetraStereo.OneCenter.LocalizedActualPhysicalKeySeparation
import TetraStereo.OneCenter.LocalizedEmptyReferencePhysicalPriorInverse
import TetraStereo.OneCenter.LocalizedGeneralRigidCalibratedRootReader
import TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalBranchInverse
import TetraStereo.OneCenter.LocalizedPhysicalDomainAdapters
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false






















































namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree
open LocalizedActualPhysicalKeySeparation
open LocalizedEmptyReferencePhysicalPriorInverse

namespace LocalizedGeneralRigidPhysicalKeySeparation

/-! ## The final original-root target of the detected center is the final occurrence of the root -/

/-- The final original-root target generated from the detected center `c` is the final occurrence
generated from any tetrahedral center whose atom is `c`'s atom.  `localizedFinalOccurrence` only
reads the center atom, so the two centers agree definitionally up to the subtype proof. -/
theorem topTarget_eq_finalOccurrence_of_rootAtom
    (input : LocalizedUniversalReference.Input)
    (root : input.certified.TetrahedralCenter)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (rootAt : root.1 = c.1) :
    ActualReaderPhysicalBranchInverse.topTarget input c =
      input.certified.localizedFinalOccurrence
        (LocalizedUniversalReference.carrierFuel input) root := by
  unfold ActualReaderPhysicalBranchInverse.topTarget
  have centerEq : (⟨c.1, c.2⟩ : input.certified.TetrahedralCenter) = root :=
    Subtype.ext rootAt.symm
  rw [centerEq]

/-! ## Reader sparsity from the general-rigid strict-dependency classification -/









theorem actualDependencyReader_sparse_generalRigid
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfgCan : input.certified.detectedMultiCenterMolecule.Configuration)
    (root : input.certified.TetrahedralCenter)
    (domainCan : ActualGeneralRigidGlobalPhysicalDomain input.certified cfgCan root)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (rootAt : root.1 = c.1) :
    ∀ cursor : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input),
      LocalizedRule4bSparseLabel
        (ActualReaderPhysicalBranchInverse.dependencyReader input c cursor) := by
  intro cursor
  by_cases dependency : input.certified.LocalizedDepthDependency cursor.occurrence
      (ActualReaderPhysicalBranchInverse.topTarget input c)
  · have dependencyRoot : input.certified.LocalizedDepthDependency cursor.occurrence
        (input.certified.localizedFinalOccurrence
          (LocalizedUniversalReference.carrierFuel input) root) := by
      rw [← topTarget_eq_finalOccurrence_of_rootAtom input root c rootAt]
      exact dependency
    have sparse := actualStrictDependency_referenceState_sparseLabel_generalRigid input
      singleBonded acyclic hcharge noDouble cfgCan root domainCan root rfl cursor dependencyRoot
    have readerEq : ActualReaderPhysicalBranchInverse.dependencyReader input c cursor =
        LocalizedUniversalReference.referenceState input cursor.occurrence := by
      unfold ActualReaderPhysicalBranchInverse.dependencyReader
      exact input.certified.localizedDependencyLabel_eq_state_of_dependency
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (LocalizedUniversalReference.referenceState input) cursor dependency
    rw [readerEq]
    exact sparse
  · have readerNone : ActualReaderPhysicalBranchInverse.dependencyReader input c cursor =
        none := by
      unfold ActualReaderPhysicalBranchInverse.dependencyReader
      unfold CertifiedLocalizedCIPInput.localizedDependencyLabel
      rw [dif_neg dependency]
    rw [readerNone]
    exact Or.inl rfl





theorem actualDependencyReader_sparse_of_physicalDomain
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c) :
    ∀ cursor : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input),
      LocalizedRule4bSparseLabel
        (ActualReaderPhysicalBranchInverse.dependencyReader input c cursor) :=
  actualDependencyReader_sparse_generalRigid input singleBonded acyclic hcharge noDouble
    (input.certified.canonicalReindexConfiguration cfg) c
    (input.certified.actualGeneralRigidGlobalPhysicalDomain_of_actualGeneralRigidPhysicalDomain
      cfg c domain) c rfl

/-! ## The general physical branch inverse interface -/









def GeneralRigidPhysicalBranchTransport
    (input : LocalizedUniversalReference.Input)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4)) : Prop :=
  ∀ (i j : Fin 4), i ≠ j →
    ∀ (tL tR : LocalizedCumulativeDecoratedTree input.certified
        (LocalizedUniversalReference.carrierFuel input)),
      tL.source = frame.cursorAt (alpha.symm i) →
        tR.source = frame.cursorAt (alpha.symm j) →
          LocalizedCumulativeTreeRealizes input.certified
              (ActualReaderPhysicalBranchInverse.dependencyReader input c) tL →
            LocalizedCumulativeTreeRealizes input.certified
                (ActualReaderPhysicalBranchInverse.dependencyReader input c) tR →
              LocalizedCumulativeDecoratedTree.shape tL =
                  LocalizedCumulativeDecoratedTree.shape tR →
                ∀ mirror : Bool,
                  (∀ (path : List Nat)
                    (nodeL nodeR : LocalizedCumulativeDecoratedTree input.certified
                      (LocalizedUniversalReference.carrierFuel input)),
                    subtreeAt? tL path = some nodeL →
                      subtreeAt? tR path = some nodeR →
                        nodeR.label = labelMirror mirror nodeL.label) →
                  RootedTetrahedralBranchSymmetry.BranchTransport
                    input.certified.detectedMultiCenterMolecule cfg c i j mirror









theorem generalRigidPhysicalBranchTransport_of_physicalDomain
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
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index))) :
    GeneralRigidPhysicalBranchTransport input cfg c frame alpha := by
  intro i j hij tL tR sourceL sourceR realizesL realizesR hshape mirror labels
  have frameComputed' : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualGeneralRigidPhysicalBranchInverse.topTarget input c) = some frame := by
    simpa [ActualGeneralRigidPhysicalBranchInverse.topTarget] using frameComputed
  have realizesL' : LocalizedCumulativeTreeRealizes input.certified
      (ActualGeneralRigidPhysicalBranchInverse.dependencyReader input c) tL := by
    simpa [ActualGeneralRigidPhysicalBranchInverse.dependencyReader] using realizesL
  have realizesR' : LocalizedCumulativeTreeRealizes input.certified
      (ActualGeneralRigidPhysicalBranchInverse.dependencyReader input c) tR := by
    simpa [ActualGeneralRigidPhysicalBranchInverse.dependencyReader] using realizesR
  exact ActualGeneralRigidPhysicalBranchInverse.actualGeneralReaderPhysicalBranchTransport_of_physicalDomain
    input noDouble singleBonded acyclic charge cfg c domain i j hij frame alpha
    frameComputed' slotSpec tL tR sourceL sourceR realizesL' realizesR' hshape mirror labels

/-! ## A full actual compound tie at two distinct frame slots is a physical proper transport -/







theorem actualFrameCompoundTie_physicalProperTransport_generalRigid
    (input : LocalizedUniversalReference.Input)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (inverse : GeneralRigidPhysicalBranchTransport input cfg c frame alpha)
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (left right : Fin 4) (different : left ≠ right)
    (tie : input.certified.compareLocalizedRerootCompoundRule45Keys
      (frameSlotKey input c frame derived left)
      (frameSlotKey input c frame derived right) = Ordering.eq) :
    RootedTetrahedralBranchSymmetry.ProperTransport
      input.certified.detectedMultiCenterMolecule cfg c (alpha left) (alpha right) := by
  classical
  obtain ⟨leftPrior, leftPriors, rightPrior, rightPriors, leftHead, leftTail, rightHead,
    rightTail, tL, tR, _leftPriorReadings, _rightPriorReadings, _leftRule5Readings,
    _rightRule5Readings, _leftHeadPrior, _rightHeadPrior, _leftCommonRBuilt, _rightCommonRBuilt,
    _headDescriptorEq, tLsource, tRsource, realizesL, realizesR, hshape, _observationEq,
    labelsRaw⟩ :=
    actual_compoundRule5_tie_sameLabels input.certified
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (actualPhysicalView input c)
      (frame.cursorAt left) (frame.cursorAt right)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frameSlotKey input c frame derived left)
      (frameSlotKey input c frame derived right)
      (frameSlotKey_built input c frame derived left)
      (frameSlotKey_built input c frame derived right)
      tie
  have sourceL : tL.source = frame.cursorAt (alpha.symm (alpha left)) := by
    rw [tLsource]
    rw [Equiv.symm_apply_apply]
  have sourceR : tR.source = frame.cursorAt (alpha.symm (alpha right)) := by
    rw [tRsource]
    rw [Equiv.symm_apply_apply]
  have realizesL' : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) tL := by
    simpa [ActualReaderPhysicalBranchInverse.dependencyReader, actualPhysicalView] using realizesL
  have realizesR' : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) tR := by
    simpa [ActualReaderPhysicalBranchInverse.dependencyReader, actualPhysicalView] using realizesR
  have labelsSame : ∀ (path : List Nat)
      (nodeL nodeR : LocalizedCumulativeDecoratedTree input.certified
        (LocalizedUniversalReference.carrierFuel input)),
      subtreeAt? tL path = some nodeL →
        subtreeAt? tR path = some nodeR →
          nodeR.label = labelMirror false nodeL.label := by
    intro path nodeL nodeR foundL foundR
    simpa using labelsRaw path nodeL nodeR foundL foundR
  have hij : alpha left ≠ alpha right :=
    fun equality => different (alpha.injective equality)
  exact inverse (alpha left) (alpha right) hij tL tR sourceL sourceR realizesL' realizesR'
    hshape false labelsSame

/-! ## Off-diagonal strictness of the actual frame keys -/

/-- **Actual compound keys are pairwise off-diagonal strict under physical root
proper-distinguishability.**  A tie between two distinct frame slots would produce a proper
transport between the corresponding physical slots by the central composition, contradicting
pairwise root proper-distinguishability. -/
theorem compoundKeyOffDiagonalStrict_of_physicalRootDistinct_generalRigid
    (input : LocalizedUniversalReference.Input)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (distinct : ∀ i j : Fin 4, i ≠ j →
      ¬ RootedTetrahedralBranchSymmetry.ProperTransport
        input.certified.detectedMultiCenterMolecule cfg c i j)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (inverse : GeneralRigidPhysicalBranchTransport input cfg c frame alpha)
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame) :
    CertifiedLocalizedCIPInput.CompoundKeyOffDiagonalStrict input.certified
      (frameSlotKey input c frame derived) := by
  intro left right different tie
  have tie' : input.certified.compareLocalizedRerootCompoundRule45Keys
      (frameSlotKey input c frame derived left)
      (frameSlotKey input c frame derived right) = Ordering.eq := by
    simpa [CertifiedLocalizedCIPInput.compoundKeyComparison, Ordering.byKey] using tie
  exact distinct (alpha left) (alpha right)
    (fun equality => different (alpha.injective equality))
    (actualFrameCompoundTie_physicalProperTransport_generalRigid input cfg c
      frame alpha inverse derived left right different tie')

/-! ## Singleton prior ties: same own reference gives a physical proper transport -/






theorem actualFrame_singleton_priorTie_sameReference_properTransport_generalRigid
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
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (inverse : GeneralRigidPhysicalBranchTransport input cfg c frame alpha)
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (left right : Fin 4) (different : left ≠ right)
    (leftReference rightReference : RS)
    (leftReferences : (frameSlotKey input c frame derived left).prior.references =
      [leftReference])
    (rightReferences : (frameSlotKey input c frame derived right).prior.references =
      [rightReference])
    (priorTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (frameSlotKey input c frame derived left).prior
      (frameSlotKey input c frame derived right).prior = Ordering.eq)
    (sameReference : leftReference = rightReference) :
    RootedTetrahedralBranchSymmetry.ProperTransport
      input.certified.detectedMultiCenterMolecule cfg c (alpha left) (alpha right) := by
  have leftComputed :
      input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?
        (ActualReaderPhysicalBranchInverse.dependencyReader input c)
        (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (frame.cursorAt left) = some (frameSlotKey input c frame derived left) :=
    frameSlotKey_withRead_built input c frame derived left
  have rightComputed :
      input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?
        (ActualReaderPhysicalBranchInverse.dependencyReader input c)
        (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (frame.cursorAt right) = some (frameSlotKey input c frame derived right) :=
    frameSlotKey_withRead_built input c frame derived right
  have readerSparse : ∀ cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input),
      LocalizedRule4bSparseLabel
        (ActualReaderPhysicalBranchInverse.dependencyReader input c cursor) :=
    actualDependencyReader_sparse_of_physicalDomain input singleBonded acyclic hcharge noDouble
      cfg c domain
  have compoundTie :=
    actual_singleton_prior_tie_compound_eq_of_sameReference
      input.certified singleBonded acyclic
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) readerSparse
      (frame.cursorAt left) (frame.cursorAt right)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      leftReference rightReference
      (frameSlotKey input c frame derived left)
      (frameSlotKey input c frame derived right)
      leftComputed rightComputed leftReferences rightReferences priorTie sameReference
  exact actualFrameCompoundTie_physicalProperTransport_generalRigid input cfg c
    frame alpha inverse derived left right different compoundTie

/-! ## Singleton prior ties: distinct own references give a physical mirror transport -/





theorem actualFrame_singleton_priorTie_differentReference_mirrorTransport_generalRigid
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
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (inverse : GeneralRigidPhysicalBranchTransport input cfg c frame alpha)
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (left right : Fin 4) (different : left ≠ right)
    (leftReference rightReference : RS)
    (leftReferences : (frameSlotKey input c frame derived left).prior.references =
      [leftReference])
    (rightReferences : (frameSlotKey input c frame derived right).prior.references =
      [rightReference])
    (priorTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (frameSlotKey input c frame derived left).prior
      (frameSlotKey input c frame derived right).prior = Ordering.eq)
    (differentReference : leftReference ≠ rightReference) :
    RootedTetrahedralBranchSymmetry.MirrorTransport
      input.certified.detectedMultiCenterMolecule cfg c (alpha left) (alpha right) := by
  have leftComputed :
      input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?
        (ActualReaderPhysicalBranchInverse.dependencyReader input c)
        (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (frame.cursorAt left) = some (frameSlotKey input c frame derived left) :=
    frameSlotKey_withRead_built input c frame derived left
  have rightComputed :
      input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?
        (ActualReaderPhysicalBranchInverse.dependencyReader input c)
        (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (frame.cursorAt right) = some (frameSlotKey input c frame derived right) :=
    frameSlotKey_withRead_built input c frame derived right
  have readerSparse : ∀ cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input),
      LocalizedRule4bSparseLabel
        (ActualReaderPhysicalBranchInverse.dependencyReader input c cursor) :=
    actualDependencyReader_sparse_of_physicalDomain input singleBonded acyclic hcharge noDouble
      cfg c domain
  obtain ⟨leftPriorReading, rightPriorReading, _leftReading, _rightReading,
    _leftReadingsEq, _rightReadingsEq, _leftRule5Eq, _rightRule5Eq,
    leftRule4bBuilt, rightRule4bBuilt, _leftCommonRBuilt, _rightCommonRBuilt,
    _leftCommonSBuilt, _rightCommonSBuilt, descriptorTie⟩ :=
    actual_singleton_prior_tie_builds input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c)
      (frame.cursorAt left) (frame.cursorAt right)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      leftReference rightReference
      (frameSlotKey input c frame derived left)
      (frameSlotKey input c frame derived right)
      leftComputed rightComputed leftReferences rightReferences priorTie
  have leftRule4aBuilt :=
    buildLocalizedRerootCompoundRule45KeyWithRead?_prior_rule4aKey input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt left) (frameSlotKey input c frame derived left) leftComputed
  have rightRule4aBuilt :=
    buildLocalizedRerootCompoundRule45KeyWithRead?_prior_rule4aKey input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt right) (frameSlotKey input c frame derived right) rightComputed
  obtain ⟨rule4aTie, -, -, -⟩ :=
    (input.certified.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff
      (frameSlotKey input c frame derived left).prior
      (frameSlotKey input c frame derived right).prior).mp priorTie
  obtain ⟨tL, tR, tLSource, tRSource, realizesL, realizesR, hshape, _labelTableEq,
    pathLabels⟩ :=
    actual_rule4b_key_tie_labelTableTransport input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) readerSparse
      (frame.cursorAt left) (frame.cursorAt right)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      leftReference rightReference
      (frameSlotKey input c frame derived left).prior.rule4aKey
      (frameSlotKey input c frame derived right).prior.rule4aKey
      leftPriorReading.rule4bKey rightPriorReading.rule4bKey
      leftRule4aBuilt rightRule4aBuilt leftRule4bBuilt rightRule4bBuilt
      rule4aTie descriptorTie
  have flagEq : referenceMirror leftReference rightReference = true :=
    referenceMirror_eq_true_iff.mpr differentReference
  have labelsMirror : ∀ (path : List Nat)
      (nodeL nodeR : LocalizedCumulativeDecoratedTree input.certified
        (LocalizedUniversalReference.carrierFuel input)),
      subtreeAt? tL path = some nodeL →
        subtreeAt? tR path = some nodeR →
          nodeR.label = labelMirror true nodeL.label := by
    intro path nodeL nodeR foundL foundR
    have h := pathLabels path nodeL nodeR foundL foundR
    rw [flagEq] at h
    simpa using h
  have sourceL : tL.source = frame.cursorAt (alpha.symm (alpha left)) := by
    rw [tLSource]
    rw [Equiv.symm_apply_apply]
  have sourceR : tR.source = frame.cursorAt (alpha.symm (alpha right)) := by
    rw [tRSource]
    rw [Equiv.symm_apply_apply]
  have hij : alpha left ≠ alpha right :=
    fun equality => different (alpha.injective equality)
  exact inverse (alpha left) (alpha right) hij tL tR sourceL sourceR realizesL realizesR
    hshape true labelsMirror

/-! ## Enantiomorphism under physical root proper-distinguishability -/

/-- **Singleton prior tie under physical root proper-distinguishability is an enantiomorphic
pair.**  Same own references would force a proper transport, contradicting distinguishability;
hence the references differ, the prior tie yields a mirror transport, and the two physical ligand
slots are enantiomorphic. -/
theorem actualFrame_singleton_priorTie_enantiomorphic_of_physicalDistinct_generalRigid
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
    (distinct : ∀ i j : Fin 4, i ≠ j →
      ¬ RootedTetrahedralBranchSymmetry.ProperTransport
        input.certified.detectedMultiCenterMolecule cfg c i j)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (inverse : GeneralRigidPhysicalBranchTransport input cfg c frame alpha)
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (left right : Fin 4) (different : left ≠ right)
    (leftReference rightReference : RS)
    (leftReferences : (frameSlotKey input c frame derived left).prior.references =
      [leftReference])
    (rightReferences : (frameSlotKey input c frame derived right).prior.references =
      [rightReference])
    (priorTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (frameSlotKey input c frame derived left).prior
      (frameSlotKey input c frame derived right).prior = Ordering.eq) :
    RootedTetrahedralBranchSymmetry.Enantiomorphic
      input.certified.detectedMultiCenterMolecule cfg c (alpha left) (alpha right) := by
  have hij : alpha left ≠ alpha right :=
    fun equality => different (alpha.injective equality)
  by_cases sameReference : leftReference = rightReference
  · exfalso
    exact distinct (alpha left) (alpha right) hij
      (actualFrame_singleton_priorTie_sameReference_properTransport_generalRigid input
        singleBonded acyclic hcharge noDouble cfg c domain frame alpha inverse derived left
        right different leftReference rightReference leftReferences rightReferences priorTie
        sameReference)
  · exact ⟨hij,
      actualFrame_singleton_priorTie_differentReference_mirrorTransport_generalRigid input
        singleBonded acyclic hcharge noDouble cfg c domain frame alpha inverse derived left
        right different leftReference rightReference leftReferences rightReferences priorTie
        sameReference,
      distinct (alpha left) (alpha right) hij⟩

/-! ## Empty/empty prior ties are physical proper transports -/











theorem actualFrame_empty_priorTie_properTransport_generalRigid
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
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (inverse : GeneralRigidPhysicalBranchTransport input cfg c frame alpha)
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (left right : Fin 4) (different : left ≠ right)
    (leftReferences : (frameSlotKey input c frame derived left).prior.references = [])
    (rightReferences : (frameSlotKey input c frame derived right).prior.references = [])
    (priorTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (frameSlotKey input c frame derived left).prior
      (frameSlotKey input c frame derived right).prior = Ordering.eq) :
    RootedTetrahedralBranchSymmetry.ProperTransport
      input.certified.detectedMultiCenterMolecule cfg c (alpha left) (alpha right) := by
  classical
  let fuel := localizedOccurrenceRerootEvaluationFuel
    (LocalizedUniversalReference.carrierFuel input)
  have leftPriorBuilt : input.certified.buildLocalizedRerootCompoundRule4bcKey?
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (actualPhysicalView input c) fuel (frame.cursorAt left) =
      some (frameSlotKey input c frame derived left).prior :=
    (buildLocalizedRerootCompoundRule45Key?_prior_built input.certified
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (actualPhysicalView input c) fuel (frame.cursorAt left)
      (frameSlotKey input c frame derived left)
      (frameSlotKey_built input c frame derived left)).1
  have rightPriorBuilt : input.certified.buildLocalizedRerootCompoundRule4bcKey?
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (actualPhysicalView input c) fuel (frame.cursorAt right) =
      some (frameSlotKey input c frame derived right).prior :=
    (buildLocalizedRerootCompoundRule45Key?_prior_built input.certified
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (actualPhysicalView input c) fuel (frame.cursorAt right)
      (frameSlotKey input c frame derived right)
      (frameSlotKey_built input c frame derived right)).1
  have readerSparse : ∀ cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input),
      LocalizedRule4bSparseLabel
        (input.certified.localizedDependencyLabel
          (ActualReaderPhysicalBranchInverse.topTarget input c)
          (actualPhysicalView input c) cursor) := by
    intro cursor
    simpa [ActualReaderPhysicalBranchInverse.dependencyReader, actualPhysicalView] using
      actualDependencyReader_sparse_of_physicalDomain input singleBonded acyclic hcharge noDouble
        cfg c domain cursor
  have leftAllNone : LocalizedLabelLayersAllNone
      (frameSlotKey input c frame derived left).prior.rule4aKey.labels :=
    input.certified.buildLocalizedRerootCompoundRule4bcKey?_rule4aKey_labels_allNone_of_references_eq_nil
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (actualPhysicalView input c) fuel (frame.cursorAt left)
      (frameSlotKey input c frame derived left).prior leftPriorBuilt readerSparse
      leftReferences
  have rightAllNone : LocalizedLabelLayersAllNone
      (frameSlotKey input c frame derived right).prior.rule4aKey.labels :=
    input.certified.buildLocalizedRerootCompoundRule4bcKey?_rule4aKey_labels_allNone_of_references_eq_nil
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (actualPhysicalView input c) fuel (frame.cursorAt right)
      (frameSlotKey input c frame derived right).prior rightPriorBuilt readerSparse
      rightReferences
  have rule4aTie : input.certified.compareLocalizedRerootCumulativeRule45Keys
      (frameSlotKey input c frame derived left).prior.rule4aKey
      (frameSlotKey input c frame derived right).prior.rule4aKey = Ordering.eq :=
    ((input.certified.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff
      (frameSlotKey input c frame derived left).prior
      (frameSlotKey input c frame derived right).prior).mp priorTie).1
  have leftRule4aWithRead :
      input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
        (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
        (frame.cursorAt left) =
      some (frameSlotKey input c frame derived left).prior.rule4aKey :=
    input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?_prior_rule4aKey
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
      (frame.cursorAt left) (frameSlotKey input c frame derived left)
      (frameSlotKey_withRead_built input c frame derived left)
  have rightRule4aWithRead :
      input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
        (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
        (frame.cursorAt right) =
      some (frameSlotKey input c frame derived right).prior.rule4aKey :=
    input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?_prior_rule4aKey
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
      (frame.cursorAt right) (frameSlotKey input c frame derived right)
      (frameSlotKey_withRead_built input c frame derived right)
  obtain ⟨tL, tLsource, tLmatch, tLrealizes, _⟩ :=
    exists_decoratedTree_of_buildWithRead_fullMatch input.certified .rule4a
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
      (frame.cursorAt left) (frameSlotKey input c frame derived left).prior.rule4aKey
      leftRule4aWithRead
  obtain ⟨tR, tRsource, tRmatch, tRrealizes, _⟩ :=
    exists_decoratedTree_of_buildWithRead_fullMatch input.certified .rule4a
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
      (frame.cursorAt right) (frameSlotKey input c frame derived right).prior.rule4aKey
      rightRule4aWithRead
  have tablesEq : tL.tables .rule4a = tR.tables .rule4a :=
    (compareLocalizedRerootCumulativeRule45Keys_eq_iff_treeTables_eq input.certified .rule4a
      (frameSlotKey input c frame derived left).prior.rule4aKey
      (frameSlotKey input c frame derived right).prior.rule4aKey
      tL tR tLmatch.tableMatch tRmatch.tableMatch).mp rule4aTie
  have hshape : LocalizedCumulativeDecoratedTree.shape tL =
      LocalizedCumulativeDecoratedTree.shape tR :=
    table_shape_eq_of_tables_eq .rule4a tL tR tablesEq
  have leftAllNoneTable : LocalizedLabelLayersAllNone tL.labelTable := by
    rw [labelTable_eq_labels_of_fullMatch tLmatch]
    exact leftAllNone
  have rightAllNoneTable : LocalizedLabelLayersAllNone tR.labelTable := by
    rw [labelTable_eq_labels_of_fullMatch tRmatch]
    exact rightAllNone
  have labelsSame : ∀ (path : List Nat)
      (nodeL nodeR : LocalizedCumulativeDecoratedTree input.certified
        (LocalizedUniversalReference.carrierFuel input)),
      subtreeAt? tL path = some nodeL →
        subtreeAt? tR path = some nodeR →
          nodeR.label = labelMirror false nodeL.label := by
    intro path nodeL nodeR foundL foundR
    rw [labelTable_allNone_node_label tL leftAllNoneTable path nodeL foundL,
      labelTable_allNone_node_label tR rightAllNoneTable path nodeR foundR]
    simp
  have sourceL : tL.source = frame.cursorAt (alpha.symm (alpha left)) := by
    rw [tLsource]
    rw [Equiv.symm_apply_apply]
  have sourceR : tR.source = frame.cursorAt (alpha.symm (alpha right)) := by
    rw [tRsource]
    rw [Equiv.symm_apply_apply]
  have hij : alpha left ≠ alpha right :=
    fun equality => different (alpha.injective equality)
  exact inverse (alpha left) (alpha right) hij tL tR sourceL sourceR tLrealizes tRrealizes
    hshape false labelsSame

/-! ## Zero-or-one selections with a tied prior are both singleton -/






theorem actualFrame_zeroOrOne_priorTie_singletons_generalRigid
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
    (distinct : ∀ i j : Fin 4, i ≠ j →
      ¬ RootedTetrahedralBranchSymmetry.ProperTransport
        input.certified.detectedMultiCenterMolecule cfg c i j)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (inverse : GeneralRigidPhysicalBranchTransport input cfg c frame alpha)
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (left right : Fin 4) (different : left ≠ right)
    (zeroOrOne : ∀ index : Fin 4,
      (frameSlotKey input c frame derived index).prior.references = [] ∨
        ∃ reference : RS,
          (frameSlotKey input c frame derived index).prior.references = [reference])
    (priorTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (frameSlotKey input c frame derived left).prior
      (frameSlotKey input c frame derived right).prior = Ordering.eq) :
    (∃ leftReference : RS,
        (frameSlotKey input c frame derived left).prior.references = [leftReference]) ∧
      (∃ rightReference : RS,
        (frameSlotKey input c frame derived right).prior.references = [rightReference]) := by
  have hij : alpha left ≠ alpha right :=
    fun equality => different (alpha.injective equality)
  constructor
  · rcases zeroOrOne left with leftEmpty | leftSingleton
    · rcases zeroOrOne right with rightEmpty | rightSingleton
      · exfalso
        exact distinct (alpha left) (alpha right) hij
          (actualFrame_empty_priorTie_properTransport_generalRigid input singleBonded acyclic
            hcharge noDouble cfg c domain frame alpha inverse derived left right different
            leftEmpty rightEmpty priorTie)
      · exfalso
        obtain ⟨rightReference, rightReferences⟩ := rightSingleton
        exact absurd priorTie
          (actualFrame_empty_left_singleton_right_prior_notTie input c frame derived
            left right rightReference leftEmpty rightReferences)
    · exact leftSingleton
  · rcases zeroOrOne right with rightEmpty | rightSingleton
    · rcases zeroOrOne left with leftEmpty | leftSingleton
      · exfalso
        exact distinct (alpha left) (alpha right) hij
          (actualFrame_empty_priorTie_properTransport_generalRigid input singleBonded acyclic
            hcharge noDouble cfg c domain frame alpha inverse derived left right different
            leftEmpty rightEmpty priorTie)
      · exfalso
        obtain ⟨leftReference, leftReferences⟩ := leftSingleton
        exact absurd priorTie
          (actualFrame_singleton_left_empty_right_prior_notTie input c frame derived
            left right leftReference leftReferences rightEmpty)
    · exact rightSingleton

/-! ## The heterogeneous prior-tie enantiomorphism endpoint -/

/-- **Zero-or-one own references and a tied prior give a physical enantiomorphism.**  The
classification forces both selections to be singleton; the general-domain singleton
enantiomorphism theorem then produces the physical `Enantiomorphic` relation between the
corresponding ligand slots.  The selection hypothesis is heterogeneous: empty-selection (ordinary
achiral) keys remain in scope. -/
theorem actualFrame_zeroOrOne_priorTie_enantiomorphic_of_physicalDistinct_generalRigid
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
    (distinct : ∀ i j : Fin 4, i ≠ j →
      ¬ RootedTetrahedralBranchSymmetry.ProperTransport
        input.certified.detectedMultiCenterMolecule cfg c i j)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (inverse : GeneralRigidPhysicalBranchTransport input cfg c frame alpha)
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (left right : Fin 4) (different : left ≠ right)
    (zeroOrOne : ∀ index : Fin 4,
      (frameSlotKey input c frame derived index).prior.references = [] ∨
        ∃ reference : RS,
          (frameSlotKey input c frame derived index).prior.references = [reference])
    (priorTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (frameSlotKey input c frame derived left).prior
      (frameSlotKey input c frame derived right).prior = Ordering.eq) :
    RootedTetrahedralBranchSymmetry.Enantiomorphic
      input.certified.detectedMultiCenterMolecule cfg c (alpha left) (alpha right) := by
  obtain ⟨leftSingleton, rightSingleton⟩ :=
    actualFrame_zeroOrOne_priorTie_singletons_generalRigid input singleBonded acyclic hcharge
      noDouble cfg c domain distinct frame alpha inverse derived left right different zeroOrOne
      priorTie
  obtain ⟨leftReference, leftReferences⟩ := leftSingleton
  obtain ⟨rightReference, rightReferences⟩ := rightSingleton
  exact actualFrame_singleton_priorTie_enantiomorphic_of_physicalDistinct_generalRigid input
    singleBonded acyclic hcharge noDouble cfg c domain distinct frame alpha inverse derived left
    right different leftReference rightReference leftReferences rightReferences priorTie






theorem exists_distinct_singleton_references_enantiomorphic_of_priorTie_generalRigid
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
    (distinct : ∀ i j : Fin 4, i ≠ j →
      ¬ RootedTetrahedralBranchSymmetry.ProperTransport
        input.certified.detectedMultiCenterMolecule cfg c i j)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (inverse : GeneralRigidPhysicalBranchTransport input cfg c frame alpha)
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (left right : Fin 4) (different : left ≠ right)
    (zeroOrOne : ∀ index : Fin 4,
      (frameSlotKey input c frame derived index).prior.references = [] ∨
        ∃ reference : RS,
          (frameSlotKey input c frame derived index).prior.references = [reference])
    (priorTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (frameSlotKey input c frame derived left).prior
      (frameSlotKey input c frame derived right).prior = Ordering.eq) :
    ∃ leftReference rightReference : RS,
      (frameSlotKey input c frame derived left).prior.references = [leftReference] ∧
        (frameSlotKey input c frame derived right).prior.references = [rightReference] ∧
          leftReference ≠ rightReference ∧
            RootedTetrahedralBranchSymmetry.Enantiomorphic
              input.certified.detectedMultiCenterMolecule cfg c (alpha left) (alpha right) := by
  obtain ⟨leftSingleton, rightSingleton⟩ :=
    actualFrame_zeroOrOne_priorTie_singletons_generalRigid input singleBonded acyclic hcharge
      noDouble cfg c domain distinct frame alpha inverse derived left right different zeroOrOne
      priorTie
  obtain ⟨leftReference, leftReferences⟩ := leftSingleton
  obtain ⟨rightReference, rightReferences⟩ := rightSingleton
  have enantiomorphic :=
    actualFrame_singleton_priorTie_enantiomorphic_of_physicalDistinct_generalRigid input
      singleBonded acyclic hcharge noDouble cfg c domain distinct frame alpha inverse derived
      left right different leftReference rightReference leftReferences rightReferences priorTie
  have hij : alpha left ≠ alpha right :=
    fun equality => different (alpha.injective equality)
  by_cases sameReference : leftReference = rightReference
  · exfalso
    exact distinct (alpha left) (alpha right) hij
      (actualFrame_singleton_priorTie_sameReference_properTransport_generalRigid input
        singleBonded acyclic hcharge noDouble cfg c domain frame alpha inverse derived left
        right different leftReference rightReference leftReferences rightReferences priorTie
        sameReference)
  · exact ⟨leftReference, rightReference, leftReferences, rightReferences, sameReference,
      enantiomorphic⟩














theorem actualFrameCompoundTie_physicalProperTransport_of_physicalDomain
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
    (left right : Fin 4) (different : left ≠ right)
    (tie : input.certified.compareLocalizedRerootCompoundRule45Keys
      (frameSlotKey input c frame derived left)
      (frameSlotKey input c frame derived right) = Ordering.eq) :
    RootedTetrahedralBranchSymmetry.ProperTransport
      input.certified.detectedMultiCenterMolecule cfg c (alpha left) (alpha right) :=
  actualFrameCompoundTie_physicalProperTransport_generalRigid input cfg c frame alpha
    (generalRigidPhysicalBranchTransport_of_physicalDomain input noDouble singleBonded acyclic
      charge cfg c domain frame alpha frameComputed slotSpec)
    derived left right different tie



theorem compoundKeyOffDiagonalStrict_of_physicalRootDistinct_of_physicalDomain
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
    (distinct : ∀ i j : Fin 4, i ≠ j →
      ¬ RootedTetrahedralBranchSymmetry.ProperTransport
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
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame) :
    CertifiedLocalizedCIPInput.CompoundKeyOffDiagonalStrict input.certified
      (frameSlotKey input c frame derived) :=
  compoundKeyOffDiagonalStrict_of_physicalRootDistinct_generalRigid input cfg c distinct frame
    alpha
    (generalRigidPhysicalBranchTransport_of_physicalDomain input noDouble singleBonded acyclic
      charge cfg c domain frame alpha frameComputed slotSpec)
    derived







theorem exists_actualFrame_compoundKeyOffDiagonalStrict_of_physicalDistinct_of_physicalDomain
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
    (distinct : ∀ i j : Fin 4, i ≠ j →
      ¬ RootedTetrahedralBranchSymmetry.ProperTransport
        input.certified.detectedMultiCenterMolecule cfg c i j) :
    ∃ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
        (ActualReaderPhysicalBranchInverse.topTarget input c) frame),
      input.certified.localizedOccurrenceFourLigandFrame?
          (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame ∧
        CertifiedLocalizedCIPInput.CompoundKeyOffDiagonalStrict input.certified
          (frameSlotKey input c frame derived) := by
  classical
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input :=
    globalCarrierFuel_adequate input
  obtain ⟨frame, alpha, frameComputed, slotSpec⟩ :=
    input.certified.exists_localizedOccurrenceFourLigandFrame_and_ligandPermutation_detected
      singleBonded acyclic enough
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (ActualReaderPhysicalBranchInverse.topTarget_current input c) c rfl
  let derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame :=
    (input.certified.localizedOccurrenceFourLigandFrame?_eq_some_iff
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame).mp frameComputed
  exact ⟨frame, derived, frameComputed,
    compoundKeyOffDiagonalStrict_of_physicalRootDistinct_of_physicalDomain input noDouble
      singleBonded acyclic charge cfg c domain distinct frame alpha frameComputed slotSpec
      derived⟩




theorem actualFrame_zeroOrOne_priorTie_enantiomorphic_and_singletons_of_physicalDomain
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
    (distinct : ∀ i j : Fin 4, i ≠ j →
      ¬ RootedTetrahedralBranchSymmetry.ProperTransport
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
    (left right : Fin 4) (different : left ≠ right)
    (zeroOrOne : ∀ index : Fin 4,
      (frameSlotKey input c frame derived index).prior.references = [] ∨
        ∃ reference : RS,
          (frameSlotKey input c frame derived index).prior.references = [reference])
    (priorTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (frameSlotKey input c frame derived left).prior
      (frameSlotKey input c frame derived right).prior = Ordering.eq) :
    (∃ leftReference : RS,
        (frameSlotKey input c frame derived left).prior.references = [leftReference]) ∧
      (∃ rightReference : RS,
        (frameSlotKey input c frame derived right).prior.references = [rightReference]) ∧
        RootedTetrahedralBranchSymmetry.Enantiomorphic
          input.certified.detectedMultiCenterMolecule cfg c (alpha left) (alpha right) := by
  have inverse : GeneralRigidPhysicalBranchTransport input cfg c frame alpha :=
    generalRigidPhysicalBranchTransport_of_physicalDomain input noDouble singleBonded acyclic
      hcharge cfg c domain frame alpha frameComputed slotSpec
  obtain ⟨leftSingleton, rightSingleton⟩ :=
    actualFrame_zeroOrOne_priorTie_singletons_generalRigid input singleBonded acyclic hcharge
      noDouble cfg c domain distinct frame alpha inverse derived left right different zeroOrOne
      priorTie
  exact ⟨leftSingleton, rightSingleton,
    actualFrame_zeroOrOne_priorTie_enantiomorphic_of_physicalDistinct_generalRigid input
      singleBonded acyclic hcharge noDouble cfg c domain distinct frame alpha inverse derived
      left right different zeroOrOne priorTie⟩



theorem exists_distinct_singleton_references_enantiomorphic_of_priorTie_of_physicalDomain
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
    (distinct : ∀ i j : Fin 4, i ≠ j →
      ¬ RootedTetrahedralBranchSymmetry.ProperTransport
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
    (left right : Fin 4) (different : left ≠ right)
    (zeroOrOne : ∀ index : Fin 4,
      (frameSlotKey input c frame derived index).prior.references = [] ∨
        ∃ reference : RS,
          (frameSlotKey input c frame derived index).prior.references = [reference])
    (priorTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (frameSlotKey input c frame derived left).prior
      (frameSlotKey input c frame derived right).prior = Ordering.eq) :
    ∃ leftReference rightReference : RS,
      (frameSlotKey input c frame derived left).prior.references = [leftReference] ∧
        (frameSlotKey input c frame derived right).prior.references = [rightReference] ∧
          leftReference ≠ rightReference ∧
            RootedTetrahedralBranchSymmetry.Enantiomorphic
              input.certified.detectedMultiCenterMolecule cfg c (alpha left) (alpha right) :=
  exists_distinct_singleton_references_enantiomorphic_of_priorTie_generalRigid input
    singleBonded acyclic hcharge noDouble cfg c domain distinct frame alpha
    (generalRigidPhysicalBranchTransport_of_physicalDomain input noDouble singleBonded acyclic
      hcharge cfg c domain frame alpha frameComputed slotSpec)
    derived left right different zeroOrOne priorTie

/-! ## Kernel-authority guards -/

assert_kernel_only
  TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalKeySeparation.topTarget_eq_finalOccurrence_of_rootAtom
assert_kernel_only
  TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalKeySeparation.actualDependencyReader_sparse_generalRigid
assert_kernel_only
  TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalKeySeparation.actualDependencyReader_sparse_of_physicalDomain
assert_kernel_only
  TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalKeySeparation.GeneralRigidPhysicalBranchTransport
assert_kernel_only
  TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalKeySeparation.generalRigidPhysicalBranchTransport_of_physicalDomain
assert_kernel_only
  TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalKeySeparation.actualFrameCompoundTie_physicalProperTransport_generalRigid
assert_kernel_only
  TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalKeySeparation.compoundKeyOffDiagonalStrict_of_physicalRootDistinct_generalRigid
assert_kernel_only
  TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalKeySeparation.actualFrame_singleton_priorTie_sameReference_properTransport_generalRigid
assert_kernel_only
  TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalKeySeparation.actualFrame_singleton_priorTie_differentReference_mirrorTransport_generalRigid
assert_kernel_only
  TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalKeySeparation.actualFrame_singleton_priorTie_enantiomorphic_of_physicalDistinct_generalRigid
assert_kernel_only
  TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalKeySeparation.actualFrame_empty_priorTie_properTransport_generalRigid
assert_kernel_only
  TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalKeySeparation.actualFrame_zeroOrOne_priorTie_singletons_generalRigid
assert_kernel_only
  TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalKeySeparation.actualFrame_zeroOrOne_priorTie_enantiomorphic_of_physicalDistinct_generalRigid
assert_kernel_only
  TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalKeySeparation.exists_distinct_singleton_references_enantiomorphic_of_priorTie_generalRigid
assert_kernel_only
  TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalKeySeparation.actualFrameCompoundTie_physicalProperTransport_of_physicalDomain
assert_kernel_only
  TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalKeySeparation.compoundKeyOffDiagonalStrict_of_physicalRootDistinct_of_physicalDomain
assert_kernel_only
  TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalKeySeparation.exists_actualFrame_compoundKeyOffDiagonalStrict_of_physicalDistinct_of_physicalDomain
assert_kernel_only
  TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalKeySeparation.actualFrame_zeroOrOne_priorTie_enantiomorphic_and_singletons_of_physicalDomain
assert_kernel_only
  TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalKeySeparation.exists_distinct_singleton_references_enantiomorphic_of_priorTie_of_physicalDomain

end LocalizedGeneralRigidPhysicalKeySeparation

end TetraStereo.OneCenter
