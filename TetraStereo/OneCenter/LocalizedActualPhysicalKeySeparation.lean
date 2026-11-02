import TetraStereo.OneCenter.LocalizedFullCompoundTieLabelDecoding
import TetraStereo.OneCenter.LocalizedDecodedTreeRule5Rereading
import TetraStereo.OneCenter.LocalizedActualReaderPhysicalBranchInverse
import TetraStereo.OneCenter.LocalizedActualRigidFrameCompleteness
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

































namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree

namespace LocalizedActualPhysicalKeySeparation

/-! ## The actual dependency view of the final original-root target -/

/-- The actual dependency view at the final original-root target, over the generated reference
state.  This is exactly the view used by `ActualReaderPhysicalBranchInverse.dependencyReader`. -/
noncomputable def actualPhysicalView (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center) :
    input.certified.LocalizedDependencyView
      (ActualReaderPhysicalBranchInverse.topTarget input c) :=
  input.certified.localizedDependencyView (LocalizedUniversalReference.referenceState input)
    (ActualReaderPhysicalBranchInverse.topTarget input c)




theorem dependencyReader_eq_localizedDependencyLabel
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center) :
    ActualReaderPhysicalBranchInverse.dependencyReader input c =
      fun cursor =>
        input.certified.localizedDependencyLabel
          (ActualReaderPhysicalBranchInverse.topTarget input c)
          (actualPhysicalView input c) cursor :=
  rfl

/-! ## A full actual compound tie at two distinct frame slots is a physical proper transport -/











theorem actualFrameCompoundTie_physicalProperTransport
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
      ((frame.compoundKeyAt input.certified
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (actualPhysicalView input c) derived) left)
      ((frame.compoundKeyAt input.certified
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (actualPhysicalView input c) derived) right) = Ordering.eq) :
    RootedTetrahedralBranchSymmetry.ProperTransport
      input.certified.detectedMultiCenterMolecule cfg c (alpha left) (alpha right) := by
  classical

  obtain ⟨leftPrior, leftPriors, rightPrior, rightPriors, leftHead, leftTail, rightHead,
    rightTail, tL, tR, _leftPriorReadings, _rightPriorReadings, _leftRule5Readings,
    _rightRule5Readings, _leftHeadPrior, _rightHeadPrior, _leftCommonRBuilt, _rightCommonRBuilt,
    _headDescriptorEq, tLsource, tRsource, realizesL, realizesR, hshape, _observationEq,
    labelsRaw⟩ :=
    TetraStereo.OneCenter.actual_compoundRule5_tie_sameLabels
      input.certified
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (actualPhysicalView input c)
      (frame.cursorAt left) (frame.cursorAt right)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      ((frame.compoundKeyAt input.certified
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (actualPhysicalView input c) derived) left)
      ((frame.compoundKeyAt input.certified
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (actualPhysicalView input c) derived) right)
      (frame.compoundKeyAt_built input.certified
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (actualPhysicalView input c) derived left)
      (frame.compoundKeyAt_built input.certified
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (actualPhysicalView input c) derived right)
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
  -- The physical slot indices are distinct because `alpha` is injective.
  have hij : alpha left ≠ alpha right :=
    fun equality => different (alpha.injective equality)

  exact ActualReaderPhysicalBranchInverse.actualReaderPhysicalBranchTransport
    input noDouble singleBonded acyclic charge cfg c (alpha left) (alpha right) hij
    domain frame alpha frameComputed slotSpec tL tR sourceL sourceR realizesL' realizesR'
    hshape false labelsSame

/-! ## Off-diagonal strictness of the actual frame keys -/

/-- **Actual compound keys of the final frame are pairwise off-diagonal strict under physical
root proper-distinguishability.**  If no two distinct physical ligand branches of the root admit a
proper transport, then no two distinct frame slots can have tied actual compound keys: such a tie
would produce a proper transport between the corresponding physical slots by the central
composition, contradicting distinguishability.

The physical hypothesis is exactly `∀ i j, i ≠ j → ¬ ProperTransport m cfg c i j`; no
unique-nearest, sparse or singleton premise is used. -/
theorem compoundKeyOffDiagonalStrict_of_physicalRootDistinct
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
      (frame.compoundKeyAt input.certified
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (actualPhysicalView input c) derived) := by
  intro left right different tie
  have tie' : input.certified.compareLocalizedRerootCompoundRule45Keys
      ((frame.compoundKeyAt input.certified
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (actualPhysicalView input c) derived) left)
      ((frame.compoundKeyAt input.certified
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (actualPhysicalView input c) derived) right) = Ordering.eq := by
    simpa [CertifiedLocalizedCIPInput.compoundKeyComparison, Ordering.byKey] using tie
  exact distinct (alpha left) (alpha right)
    (fun equality => different (alpha.injective equality))
    (actualFrameCompoundTie_physicalProperTransport input noDouble singleBonded acyclic charge
      cfg c domain frame alpha frameComputed slotSpec derived left right different tie')

/-! ## The derived-frame endpoint: no frame or key success is assumed -/









theorem exists_actualFrame_compoundKeyOffDiagonalStrict_of_physicalDistinct
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
          (frame.compoundKeyAt input.certified
            (ActualReaderPhysicalBranchInverse.topTarget input c)
            (actualPhysicalView input c) derived) := by
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
    compoundKeyOffDiagonalStrict_of_physicalRootDistinct input noDouble singleBonded acyclic
      charge cfg c domain distinct frame alpha frameComputed slotSpec derived⟩

/-! ## Sparse reader derivation from the global physical domain -/

section SparseReader




theorem actualStrictDependency_sparseSource
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c) :
    ∀ cursor : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input),
      input.certified.LocalizedDepthDependency cursor.occurrence
        (ActualReaderPhysicalBranchInverse.topTarget input c) →
        ActualPhysicalSparseSource input cursor.occurrence := by
  intro cursor dependency
  rcases actualStrictDependency_classification input singleBonded acyclic noDouble
    input.certified.detectedMultiCenterMolecule cfg c domain
    (detectedMultiCenter_centers input.certified) ⟨c.1, c.2⟩ rfl cursor dependency with
    ⟨noncandidate, _none⟩ | ⟨twins, _none⟩ |
    ⟨_center, _rs, _tracked, frame, _alpha, _pointAt, _current, _notTwin, frameComputed,
      _match, separated, _spatial, _observed, _calibration, _pseudo, _state, _sign⟩
  · exact Or.inl noncandidate
  · exact Or.inr (Or.inr twins)
  · exact Or.inr (Or.inl ⟨frame, frameComputed, separated⟩)






theorem actualDependencyReader_sparse
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c) :
    ∀ cursor, LocalizedRule4bSparseLabel
      (ActualReaderPhysicalBranchInverse.dependencyReader input c cursor) := by
  intro cursor
  have rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter
      (ActualReaderPhysicalBranchInverse.topTarget input c).1.root := by
    rw [ActualReaderPhysicalBranchInverse.topTarget_root]
    exact (input.certified.moleculeGraph.mem_tetrahedralCenterSet c.1).mp c.2
  have sparse := localizedDependencyLabel_sparse_of_actualPhysicalSparseSource input
    singleBonded acyclic noDouble
    (ActualReaderPhysicalBranchInverse.topTarget input c) rootTetrahedral
    (actualStrictDependency_sparseSource input singleBonded acyclic noDouble cfg c domain) cursor
  simpa [ActualReaderPhysicalBranchInverse.dependencyReader, actualPhysicalView] using sparse

end SparseReader

/-! ## The actual production key of one frame slot -/

/-- The actual production compound key of one frame slot at the final original-root target,
over the actual reference-state view. -/
noncomputable def frameSlotKey (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (index : Fin 4) : input.certified.LocalizedRerootCompoundRule45Key :=
  frame.compoundKeyAt input.certified
    (ActualReaderPhysicalBranchInverse.topTarget input c)
    (actualPhysicalView input c) derived index

/-- The production builder at the production fuel returns exactly the slot key. -/
theorem frameSlotKey_built (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (index : Fin 4) :
    input.certified.buildLocalizedRerootCompoundRule45Key?
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (actualPhysicalView input c)
        (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (frame.cursorAt index) =
      some (frameSlotKey input c frame derived index) :=
  frame.compoundKeyAt_built input.certified
    (ActualReaderPhysicalBranchInverse.topTarget input c)
    (actualPhysicalView input c) derived index

/-- The slot key's defining actual through-Rule-5 build, as a `WithRead` build of the generated
dependency reader.  This is the bridge that lets the singleton prior-tie analysis consume the
production `compoundKeyAt` keys. -/
theorem frameSlotKey_withRead_built (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (index : Fin 4) :
    input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?
        (ActualReaderPhysicalBranchInverse.dependencyReader input c)
        (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (frame.cursorAt index) =
      some (frameSlotKey input c frame derived index) := by
  change input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?
      (fun cursor =>
        input.certified.localizedDependencyLabel
          (ActualReaderPhysicalBranchInverse.topTarget input c)
          (actualPhysicalView input c) cursor)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt index) =
    some (frameSlotKey input c frame derived index)
  rw [buildLocalizedRerootCompoundRule45KeyWithRead?_eq_localizedDependencyLabel
    input.certified (ActualReaderPhysicalBranchInverse.topTarget input c)
    (actualPhysicalView input c)]
  exact frameSlotKey_built input c frame derived index

/-- Packaged form of the strictness result: the four actual production slot keys, viewed as the
`Fin 4`-indexed key table consumed by `compoundKeyRank`, are pairwise off-diagonal strict. -/
theorem frameSlotKeys_compoundKeyOffDiagonalStrict_of_physicalDistinct
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
  compoundKeyOffDiagonalStrict_of_physicalRootDistinct input noDouble singleBonded acyclic
    charge cfg c domain distinct frame alpha frameComputed slotSpec derived

/-! ## Singleton prior ties: same own reference gives a physical proper transport -/






theorem actualFrame_singleton_priorTie_sameReference_properTransport
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
  let leftKey := frameSlotKey input c frame derived left
  let rightKey := frameSlotKey input c frame derived right
  have leftComputed : input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?
      (ActualReaderPhysicalBranchInverse.dependencyReader input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt left) = some leftKey :=
    frameSlotKey_withRead_built input c frame derived left
  have rightComputed : input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?
      (ActualReaderPhysicalBranchInverse.dependencyReader input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt right) = some rightKey :=
    frameSlotKey_withRead_built input c frame derived right
  have readerSparse : ∀ cursor, LocalizedRule4bSparseLabel
      (ActualReaderPhysicalBranchInverse.dependencyReader input c cursor) :=
    actualDependencyReader_sparse input singleBonded acyclic noDouble cfg c domain
  have compoundTie :=
    TetraStereo.OneCenter.actual_singleton_prior_tie_compound_eq_of_sameReference
      input.certified singleBonded acyclic
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) readerSparse
      (frame.cursorAt left) (frame.cursorAt right)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      leftReference rightReference leftKey rightKey leftComputed rightComputed
      leftReferences rightReferences priorTie sameReference
  exact actualFrameCompoundTie_physicalProperTransport input noDouble singleBonded acyclic
    charge cfg c domain frame alpha frameComputed slotSpec derived left right different
    compoundTie

/-! ## Singleton prior ties: distinct own references give a physical mirror transport -/






theorem actualFrame_singleton_priorTie_differentReference_mirrorTransport
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
  let leftKey := frameSlotKey input c frame derived left
  let rightKey := frameSlotKey input c frame derived right
  have leftComputed : input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?
      (ActualReaderPhysicalBranchInverse.dependencyReader input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt left) = some leftKey :=
    frameSlotKey_withRead_built input c frame derived left
  have rightComputed : input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?
      (ActualReaderPhysicalBranchInverse.dependencyReader input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt right) = some rightKey :=
    frameSlotKey_withRead_built input c frame derived right
  have readerSparse : ∀ cursor, LocalizedRule4bSparseLabel
      (ActualReaderPhysicalBranchInverse.dependencyReader input c cursor) :=
    actualDependencyReader_sparse input singleBonded acyclic noDouble cfg c domain

  obtain ⟨leftPriorReading, rightPriorReading, _leftReading, _rightReading,
    _leftReadingsEq, _rightReadingsEq, _leftRule5Eq, _rightRule5Eq,
    leftRule4bBuilt, rightRule4bBuilt, _leftCommonRBuilt, _rightCommonRBuilt,
    _leftCommonSBuilt, _rightCommonSBuilt, descriptorTie⟩ :=
    TetraStereo.OneCenter.actual_singleton_prior_tie_builds input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c)
      (frame.cursorAt left) (frame.cursorAt right)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      leftReference rightReference leftKey rightKey leftComputed rightComputed
      leftReferences rightReferences priorTie
  -- The `.rule4a` constituents of the two compound builds.
  have leftRule4aBuilt :=
    buildLocalizedRerootCompoundRule45KeyWithRead?_prior_rule4aKey input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt left) leftKey leftComputed
  have rightRule4aBuilt :=
    buildLocalizedRerootCompoundRule45KeyWithRead?_prior_rule4aKey input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt right) rightKey rightComputed
  obtain ⟨rule4aTie, -, -, -⟩ :=
    (input.certified.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff
      leftKey.prior rightKey.prior).mp priorTie

  obtain ⟨tL, tR, tLSource, tRSource, realizesL, realizesR, hshape, _labelTableEq,
    pathLabels⟩ :=
    TetraStereo.OneCenter.actual_rule4b_key_tie_labelTableTransport input.certified
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
      leftKey.prior.rule4aKey rightKey.prior.rule4aKey
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
  exact ActualReaderPhysicalBranchInverse.actualReaderPhysicalBranchTransport
    input noDouble singleBonded acyclic charge cfg c (alpha left) (alpha right) hij
    domain frame alpha frameComputed slotSpec tL tR sourceL sourceR realizesL realizesR
    hshape true labelsMirror

/-! ## Enantiomorphism under physical root proper-distinguishability -/

/-- **Singleton prior tie under physical root proper-distinguishability is an enantiomorphic pair.**
Same own references would force a proper transport, contradicting distinguishability; hence the
references differ, the prior tie yields a mirror transport, and the two physical ligand slots are
enantiomorphic. -/
theorem actualFrame_singleton_priorTie_enantiomorphic_of_physicalDistinct
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
      (actualFrame_singleton_priorTie_sameReference_properTransport input noDouble
        singleBonded acyclic charge cfg c domain frame alpha frameComputed slotSpec derived
        left right different leftReference rightReference leftReferences rightReferences
        priorTie sameReference)
  · exact ⟨hij,
      actualFrame_singleton_priorTie_differentReference_mirrorTransport input noDouble
        singleBonded acyclic charge cfg c domain frame alpha frameComputed slotSpec derived
        left right different leftReference rightReference leftReferences rightReferences
        priorTie sameReference,
      distinct (alpha left) (alpha right) hij⟩

end LocalizedActualPhysicalKeySeparation

/-! ## Kernel-authority guards -/

assert_kernel_only
  TetraStereo.OneCenter.LocalizedActualPhysicalKeySeparation.actualPhysicalView
assert_kernel_only
  TetraStereo.OneCenter.LocalizedActualPhysicalKeySeparation.dependencyReader_eq_localizedDependencyLabel
assert_kernel_only
  TetraStereo.OneCenter.LocalizedActualPhysicalKeySeparation.actualFrameCompoundTie_physicalProperTransport
assert_kernel_only
  TetraStereo.OneCenter.LocalizedActualPhysicalKeySeparation.compoundKeyOffDiagonalStrict_of_physicalRootDistinct
assert_kernel_only
  TetraStereo.OneCenter.LocalizedActualPhysicalKeySeparation.exists_actualFrame_compoundKeyOffDiagonalStrict_of_physicalDistinct
assert_kernel_only
  TetraStereo.OneCenter.LocalizedActualPhysicalKeySeparation.actualStrictDependency_sparseSource
assert_kernel_only
  TetraStereo.OneCenter.LocalizedActualPhysicalKeySeparation.actualDependencyReader_sparse
assert_kernel_only
  TetraStereo.OneCenter.LocalizedActualPhysicalKeySeparation.frameSlotKey
assert_kernel_only
  TetraStereo.OneCenter.LocalizedActualPhysicalKeySeparation.frameSlotKeys_compoundKeyOffDiagonalStrict_of_physicalDistinct
assert_kernel_only
  TetraStereo.OneCenter.LocalizedActualPhysicalKeySeparation.frameSlotKey_built
assert_kernel_only
  TetraStereo.OneCenter.LocalizedActualPhysicalKeySeparation.frameSlotKey_withRead_built
assert_kernel_only
  TetraStereo.OneCenter.LocalizedActualPhysicalKeySeparation.actualFrame_singleton_priorTie_sameReference_properTransport
assert_kernel_only
  TetraStereo.OneCenter.LocalizedActualPhysicalKeySeparation.actualFrame_singleton_priorTie_differentReference_mirrorTransport
assert_kernel_only
  TetraStereo.OneCenter.LocalizedActualPhysicalKeySeparation.actualFrame_singleton_priorTie_enantiomorphic_of_physicalDistinct

end TetraStereo.OneCenter
