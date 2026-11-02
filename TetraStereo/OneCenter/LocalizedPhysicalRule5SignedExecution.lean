import TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction
import TetraStereo.OneCenter.LocalizedActualNearestCompoundReadings
import TetraStereo.OneCenter.LocalizedPhysicalPseudoEndToEnd
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open RootedTetrahedralBranchSymmetry

noncomputable section




















































































namespace LocalizedPhysicalRule5SignedExecution

/-! ## A. The actual slot tree's derived mark is the branch mark -/

/-- **The derived actual mark of the actual Rule-4a production tree at a cut-branch atom is the
actual branch mark.**  The position recovered from the cut-branch equivalence carries `center`;
`actualSlotTree_reader` identifies the branch mark with the tree label at that position, and
`actualTreeMark_reader` identifies the tree label with the derived mark.  The two `some`-
membership descriptions then coincide for every descriptor, which determines the optional values
by case analysis. -/
theorem actualTreeMark_actualSlotTree_eq_branchMarkedDescriptor
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    {center : input.certified.Atom}
    (centerMem : center ∈ AcyclicCutBranchAutomorphism.CutBranch
      input.certified.moleculeGraph c.1 oAtom) :
    LocalizedUniqueNearestRule5Direction.actualTreeMark input singleBonded acyclic
        (actualSlotTree input c frame frameComputed slot) center =
      branchMarkedDescriptor input c frame frameComputed slot singleBonded acyclic
        oAtom oObserved center := by
  classical
  let p : Position (actualSlotTree input c frame frameComputed slot) :=
    (actualSlotCutEquiv input c frame frameComputed slot singleBonded acyclic
      oAtom oObserved).symm ⟨center, centerMem⟩
  have pAtom : positionAtom singleBonded acyclic p = center :=
    actualSlotCutEquiv_symm_apply input c frame frameComputed slot singleBonded acyclic
      oAtom oObserved centerMem
  have bridge : ∀ d : RS,
      branchMarkedDescriptor input c frame frameComputed slot singleBonded acyclic
          oAtom oObserved center = some d ↔
        LocalizedUniqueNearestRule5Direction.actualTreeMark input singleBonded acyclic
          (actualSlotTree input c frame frameComputed slot) center = some d := by
    intro d
    have reader := actualSlotTree_reader input c frame frameComputed slot singleBonded
      acyclic oAtom oObserved p d
    have markReader :=
      LocalizedUniqueNearestRule5Direction.actualTreeMark_reader input c frame
        frameComputed slot singleBonded acyclic
        (actualSlotTree_realizes input c frame frameComputed slot)
        (actualSlotTree_previousEq input c frame frameComputed slot)
        (actualSlotTree_valid input c frame frameComputed slot)
        (actualSlotTree_previousShorter input c frame frameComputed slot)
        (actualSlotTree_sameRoot input c frame frameComputed slot)
        (actualSlotTree_oObserved input c frame frameComputed slot oObserved)
        (actualSlot_incomingEdge input c frame frameComputed slot oObserved) p d
    rw [pAtom] at reader markReader
    exact reader.symm.trans markReader
  cases hb : branchMarkedDescriptor input c frame frameComputed slot singleBonded acyclic
      oAtom oObserved center with
  | none =>
      cases hm : LocalizedUniqueNearestRule5Direction.actualTreeMark input singleBonded acyclic
          (actualSlotTree input c frame frameComputed slot) center with
      | none => rfl
      | some d =>
          have hsome := (bridge d).mpr hm
          rw [hb] at hsome
          exact absurd hsome (by simp)
  | some d => exact (bridge d).mp hb

/-! ## B. The actual selected reference is the branch mark -/







theorem branchMarkedDescriptor_eq_selectedReference
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
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance)
    {r : RS}
    (references : (actualSlotCompoundKey input c frame frameComputed slot).prior.references = [r]) :
    branchMarkedDescriptor input c frame frameComputed slot singleBonded acyclic
        oAtom oObserved center = some r := by
  obtain ⟨descriptor, marked⟩ :=
    exists_markedBranchUniqueNearest_of_physicalBranchUniqueNearest input c frame frameComputed
      slot singleBonded acyclic hcharge noDouble cfg domain oAtom oObserved unique
  obtain ⟨_selection, referencesDescriptor, _reading⟩ :=
    actualSlot_markedBranchUniqueNearest_references_singleton input c frame frameComputed slot
      singleBonded acyclic hcharge noDouble cfg domain oAtom oObserved marked
  have rEq : r = descriptor := by
    have listEq : [r] = [descriptor] := references.symm.trans referencesDescriptor
    simpa using listEq
  rw [rEq]
  exact marked.2.1

/-! ## C. Witness-retaining signed execution at the actual frame cursor -/













theorem actualSlot_compoundReading_stageFor_signed_of_physicalUniqueNearest_witness
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
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance)
    (prefixStable : ∀ (slot' : Fin 4)
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
          keyR.labels.getD d [] = keyS.labels.getD d []) :
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
        (if r = RS.R then Ordering.gt else Ordering.lt) := by
  obtain ⟨r, priorReading, reading, keyR, keyS, compoundBuilt, references, readings,
    referenceSome, keyReadings, priorEq, builtR, builtS, commonREq, commonSEq,
    _descriptorNe⟩ :=
    actualSlot_compoundReading_singleton_aligned_of_physicalUniqueNearest input c frame
      frameComputed slot singleBonded acyclic hcharge noDouble cfg domain oAtom oObserved unique
  -- The actual selected reference is the branch mark at the physical nearest centre.
  have branchMarked : branchMarkedDescriptor input c frame frameComputed slot singleBonded
      acyclic oAtom oObserved center = some r :=
    branchMarkedDescriptor_eq_selectedReference input c frame frameComputed slot singleBonded
      acyclic hcharge noDouble cfg domain oAtom oObserved unique references
  -- The actual Rule-4a slot tree carries that mark.
  have markSlot : LocalizedUniqueNearestRule5Direction.actualTreeMark input singleBonded acyclic
      (actualSlotTree input c frame frameComputed slot) center = some r := by
    rw [actualTreeMark_actualSlotTree_eq_branchMarkedDescriptor input c frame frameComputed
      slot singleBonded acyclic oAtom oObserved unique.1, branchMarked]
  -- Decode the actual common-`R` stage build.
  obtain ⟨treeR, sourceEqR, _tableMatchR, labelTableR, realizesR⟩ :=
    exists_decoratedTree_of_buildLocalizedRerootCumulativeRule45Key? input.certified
      (localizedRule5StageFor (some r) .R)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt slot) keyR builtR
  have realizesReaderR : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeR := realizesR
  obtain ⟨descriptorR, earlierR, uniqueR, markR⟩ :=
    LocalizedUniqueNearestRule5Direction.tree_observations_of_physicalBranchUniqueNearest
      input c frame frameComputed slot singleBonded acyclic hcharge noDouble cfg domain
      (oAtom := oAtom) oObserved (tree := treeR) (sourceEq := sourceEqR)
      (realizes := realizesReaderR) unique
  -- Fixed-root occurrence injectivity identifies the two derived marks at the centre.
  have markEq :
      LocalizedUniqueNearestRule5Direction.actualTreeMark input singleBonded acyclic
          (actualSlotTree input c frame frameComputed slot) center =
        LocalizedUniqueNearestRule5Direction.actualTreeMark input singleBonded acyclic
          treeR center :=
    LocalizedUniqueNearestRule5Direction.actualTreeMark_eq_of_marks_some input c frame
      frameComputed slot singleBonded acyclic
      (actualSlotTree_source input c frame frameComputed slot) sourceEqR
      (actualSlotTree_realizes input c frame frameComputed slot) realizesReaderR
      oObserved (actualSlot_incomingEdge input c frame frameComputed slot oObserved)
      markSlot markR
  have descriptorEq : descriptorR = r := by
    have someEq : some descriptorR = some r := by
      rw [← markR, ← markSlot]
      exact markEq.symm
    exact Option.some.inj someEq
  -- Transfer the derived tree observations to the actual label table of the `commonR` key.
  have labelEq : ∀ e, (keyR.labels.getD e []).map Prod.snd =
      LocalizedCumulativeDecoratedTree.observationsAtDepth (fun node => node.label) e treeR := by
    intro e
    have mapped := LocalizedCumulativeDecoratedTree.labelTable_getD_map_snd treeR e
    rw [labelTableR] at mapped
    exact mapped
  have earlierKey : ∀ e, e < distance →
      LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
        ((keyR.labels.getD e []).map Prod.snd) = [] := by
    intro e before
    rw [labelEq e]
    exact earlierR e before
  have uniqueKey : LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
      ((keyR.labels.getD distance []).map Prod.snd) = [r] := by
    rw [labelEq distance, uniqueR, descriptorEq]
  have leftLt : distance < keyR.labels.length := by
    apply LocalizedActualUniqueNearestRule5Direction.getD_ne_nil_imp_lt_length
    intro empty
    rw [empty] at uniqueKey
    simp [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations] at uniqueKey
  obtain ⟨lengthEq, rowPrefix⟩ :=
    prefixStable slot frame frameComputed oAtom oObserved unique r keyR keyS builtR builtS
  have signed :=
    LocalizedActualUniqueNearestRule5Direction.buildLocalizedRerootCumulativeRule45Key?_stageFor_descriptor_signed_of_labelPrefix
      input.certified (some r) (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt slot) keyR keyS builtR builtS distance r lengthEq leftLt
      rowPrefix earlierKey uniqueKey
  exact ⟨r, priorReading, reading, keyR, keyS, compoundBuilt, references, readings,
    referenceSome, keyReadings, priorEq, builtR, builtS, commonREq, commonSEq,
    markSlot, branchMarked, earlierKey, uniqueKey, signed⟩

/-! ## D. Occurrence provenance of the selected reference -/






theorem exists_referenceState_occurrence_at_physicalNearestCenter
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
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance)
    {r : RS}
    (references : (actualSlotCompoundKey input c frame frameComputed slot).prior.references = [r]) :
    ∃ occurrence : LocalizedUniversalReference.Occurrence input,
      occurrence.1.root = c.1 ∧
        occurrence.1.node.current? = some center ∧
          LocalizedUniversalReference.referenceState input occurrence = some (.chiral r) := by
  classical
  have branchMarked : branchMarkedDescriptor input c frame frameComputed slot singleBonded
      acyclic oAtom oObserved center = some r :=
    branchMarkedDescriptor_eq_selectedReference input c frame frameComputed slot singleBonded
      acyclic hcharge noDouble cfg domain oAtom oObserved unique references
  have markSlot : LocalizedUniqueNearestRule5Direction.actualTreeMark input singleBonded acyclic
      (actualSlotTree input c frame frameComputed slot) center = some r := by
    rw [actualTreeMark_actualSlotTree_eq_branchMarkedDescriptor input c frame frameComputed
      slot singleBonded acyclic oAtom oObserved unique.1, branchMarked]
  obtain ⟨p, pAtom, pState⟩ :=
    (LocalizedUniqueNearestRule5Direction.actualTreeMark_eq_some_iff input c singleBonded
      acyclic (actualSlotTree_realizes input c frame frameComputed slot)
      (actualSlotTree_previousEq input c frame frameComputed slot)
      (actualSlotTree_sameRoot input c frame frameComputed slot)
      (actualSlotTree_oObserved input c frame frameComputed slot oObserved)
      (actualSlot_incomingEdge input c frame frameComputed slot oObserved) center r).mp markSlot
  refine ⟨(positionSource p).occurrence, ?_, ?_, pState⟩
  · have rootEq := positionSource_root_eq_of_realized
      (actualSlotTree_realizes input c frame frameComputed slot) p
    rw [rootEq, actualSlotTree_source,
      input.certified.localizedOccurrenceFourLigandFrame_cursor_root
        (ActualReaderPhysicalBranchInverse.topTarget input c) frame frameComputed
        (frame.cursorAt slot) (List.get_mem frame.cursors _),
      ActualReaderPhysicalBranchInverse.topTarget_root]
  · rw [positionAtom_spec singleBonded acyclic p, pAtom]

/-! ## E. Physical-atom adapter: the frame and slot are derived, not supplied -/













theorem exists_actualSlot_compoundReading_stageFor_signed_of_physicalAtom
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
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance)
    (prefixStable : ∀ (slot' : Fin 4)
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
          keyR.labels.getD d [] = keyS.labels.getD d []) :
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
  let centerT : input.certified.TetrahedralCenter := ⟨c.1, c.2⟩
  obtain ⟨frame, alpha, frameComputed, ligandLink⟩ :=
    input.certified.exists_canonicalFrameSlotLink
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      singleBonded acyclic (globalCarrierFuel_adequate input) centerT
      (ActualReaderPhysicalBranchInverse.topTarget_current input c)
  obtain ⟨index, ligandEq⟩ :=
    (input.certified.detectedOneCenterMolecule centerT).ligandAtom_surjective
      oAtom (by simpa [centerT] using adjacent)
  have ligandEq' : input.certified.canonicalLigandAtom centerT index = oAtom := ligandEq
  let slot : Fin 4 := alpha.symm index
  have oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom := by
    simpa [slot, ligandEq'] using ligandLink slot
  have domain : ActualGeneralRigidGlobalPhysicalDomain input.certified
      (input.certified.canonicalReindexConfiguration cfgPhys) ⟨c.1, c.2⟩ :=
    actualGeneralRigidGlobalPhysicalDomain_of_actualGeneralRigidPhysicalDomain
      input.certified cfgPhys c physicalDomain
  obtain ⟨r, priorReading, reading, keyR, keyS, compoundBuilt, referencesSingleton,
    readingsSingleton, referenceSome, keyReadingsSingleton, priorEq, builtR, builtS,
    commonREq, commonSEq, markSlot, branchMarked, earlierKey, uniqueKey, signed⟩ :=
    actualSlot_compoundReading_stageFor_signed_of_physicalUniqueNearest_witness input c frame
      frameComputed slot singleBonded acyclic hcharge noDouble
      (input.certified.canonicalReindexConfiguration cfgPhys) domain oAtom oObserved unique
      prefixStable
  obtain ⟨occurrence, occurrenceRoot, occurrenceCurrent, occurrenceState⟩ :=
    exists_referenceState_occurrence_at_physicalNearestCenter input c frame frameComputed slot
      singleBonded acyclic hcharge noDouble
      (input.certified.canonicalReindexConfiguration cfgPhys) domain oAtom oObserved unique
      referencesSingleton
  exact ⟨slot, frame, frameComputed, oObserved, r, priorReading, reading, keyR, keyS,
    compoundBuilt, referencesSingleton, readingsSingleton, referenceSome, keyReadingsSingleton,
    priorEq, builtR, builtS, commonREq, commonSEq, markSlot, branchMarked, earlierKey, uniqueKey,
    signed, ⟨occurrence, occurrenceRoot, occurrenceCurrent, occurrenceState⟩⟩









/-- **Derived-frame irrelevance of a compound slot key.**  Two declarative witnesses of the same
computed frame at the same occurrence give the same slot key.  Both keys are the production
builder output at the same target, view and cursor (`compoundKeyAt_built`), so this is exact
determinism of the builder, not proof irrelevance of a supplied key. -/
theorem compoundKeyAt_derived_irrel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived₁ derived₂ : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (index : Fin 4) :
    frame.compoundKeyAt input target view derived₁ index =
      frame.compoundKeyAt input target view derived₂ index :=
  Option.some.inj
    ((frame.compoundKeyAt_built input target view derived₁ index).symm.trans
      (frame.compoundKeyAt_built input target view derived₂ index))

/-- **Target transport of a compound slot key over the generated reference state.**  The slot key
at the first occurrence with the state-restricted view equals the slot key at the second occurrence
with the same state-restricted view, whenever the occurrences themselves are equal.  The proof
eliminates the occurrence equality; the view is literally the state restriction at the occurrence,
so no view alignment is assumed. -/
theorem compoundKeyAt_eq_of_target_eq_views
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {t₁ t₂ : input.LocalizedCIPOccurrence carrierFuel} (h : t₂ = t₁)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (derived₂ : input.DeclarativeLocalizedOccurrenceFourLigandFrame t₂ frame)
    (derived₁ : input.DeclarativeLocalizedOccurrenceFourLigandFrame t₁ frame)
    (index : Fin 4) :
    frame.compoundKeyAt input t₁ (input.localizedDependencyView state t₁) derived₁ index =
      frame.compoundKeyAt input t₂ (input.localizedDependencyView state t₂) derived₂ index := by
  subst h
  exact compoundKeyAt_derived_irrel input _ _ frame _ _ index

/-! ## F. Two-branch signed execution from a physical mirror transport -/














theorem exists_pair_throughRule5_signed_pseudo_of_physicalMirrorTransport
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
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) center distance)
    (prefixStable : ∀ (slot' : Fin 4)
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
          keyR.labels.getD d [] = keyS.labels.getD d []) :
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
        (actualSlotCompoundKey input c frame frameComputed (alpha.symm i)).prior.references = [r] ∧
        branchMarkedDescriptor input c frame frameComputed (alpha.symm i) singleBonded acyclic
            (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) oObservedLeft center =
          some r ∧
        LocalizedUniqueNearestRule5Direction.actualTreeMark input singleBonded acyclic
            (actualSlotTree input c frame frameComputed (alpha.symm i)) center = some r ∧
        OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
            keyR.descriptor keyS.descriptor =
          (if r = RS.R then Ordering.gt else Ordering.lt) ∧
        LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
            ((keyR.labels.getD distance []).map Prod.snd) = [r] ∧
        (∃ occurrence : LocalizedUniversalReference.Occurrence input,
          occurrence.1.root = c.1 ∧
            occurrence.1.node.current? = some center ∧
              LocalizedUniversalReference.referenceState input occurrence = some (.chiral r)) := by
  classical

  have hOcc : localizedPhysicalTopOccurrence input
      input.certified.detectedMultiCenterMolecule domain.graphEq c =
      ActualReaderPhysicalBranchInverse.topTarget input c := by
    have hcenter : localizedPhysicalTopCenter input
        input.certified.detectedMultiCenterMolecule domain.graphEq c =
        (⟨c.1, c.2⟩ : input.certified.TetrahedralCenter) :=
      Subtype.ext rfl
    unfold localizedPhysicalTopOccurrence ActualReaderPhysicalBranchInverse.topTarget
    rw [hcenter]

  obtain ⟨frame', alpha', frameComputed', slotSpec', _, _, forward⟩ :=
    localizedGeneralRigidPhysicalCompound_transport_priorTie_and_commonReading
      input singleBonded acyclic hcharge noDouble cfg c i j true transport domain
  have frameComputedTop : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame' := by
    simpa [hOcc] using frameComputed'
  have oObservedLeft : (frame'.cursorAt (alpha'.symm i)).occurrence.1.node.current? =
      some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) := by
    simpa using slotSpec' (alpha'.symm i)
  have oObservedRight : (frame'.cursorAt (alpha'.symm j)).occurrence.1.node.current? =
      some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c j) := by
    simpa using slotSpec' (alpha'.symm j)
  -- The global domain of the one-branch signed endpoint.
  have domainGlobal : ActualGeneralRigidGlobalPhysicalDomain input.certified
      (input.certified.canonicalReindexConfiguration cfg) ⟨c.1, c.2⟩ :=
    actualGeneralRigidGlobalPhysicalDomain_of_actualGeneralRigidPhysicalDomain
      input.certified cfg c domain
  have derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame' :=
    (input.certified.localizedOccurrenceFourLigandFrame?_eq_some_iff
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame').mp frameComputedTop
  obtain ⟨e, centerFixed, ligandMaps, signLaw⟩ := transport

  -- physical domain (unique-nearest alternative) and the physical transport.
  have shapeActual : LocalizedPhysicalCompoundSelectorShape
      (actualSlotCompoundKey input c frame' frameComputedTop (alpha'.symm i)).prior.references
      (actualSlotCompoundKey input c frame' frameComputedTop (alpha'.symm j)).prior.references
      true :=
    LocalizedPhysicalReferenceCovariance.localizedPhysicalCompoundSelectorShape_references_of_physicalBranchTransport_of_physicalDomain
      input singleBonded acyclic hcharge noDouble c cfg domain frame' frameComputedTop
      (alpha'.symm i) (alpha'.symm j)
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i)
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt c j)
      oObservedLeft oObservedRight (i := i) (j := j) (e := e)
      centerFixed ligandMaps true signLaw rfl rfl (Or.inr ⟨center, distance, unique⟩)

  have shapeFrame : LocalizedPhysicalCompoundSelectorShape
      ((LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame' derived
        (alpha'.symm i)).prior.references)
      ((LocalizedActualPhysicalKeySeparation.frameSlotKey input c frame' derived
        (alpha'.symm j)).prior.references) true := by
    simpa only [actualSlotCompoundKey_eq_frameSlotKey input c frame' frameComputedTop derived
        (alpha'.symm i),
      actualSlotCompoundKey_eq_frameSlotKey input c frame' frameComputedTop derived
        (alpha'.symm j)] using shapeActual

  have shapeF197 : LocalizedPhysicalCompoundSelectorShape
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
      hOcc] using shapeFrame

  obtain ⟨leftReading, rightReading, leftRule5Eq, rightRule5Eq, priorTieF197, relation⟩ :=
    forward shapeF197

  -- the occurrence target (`localizedPhysicalTopOccurrence` versus the actual top target), which is
  -- bridged by `hOcc`; the generated dependency view depends on the reference state, not on the
  -- target, and the two declarative frame witnesses are the same computed frame.
  have keyEqLeft : actualSlotCompoundKey input c frame' frameComputedTop (alpha'.symm i) =
      localizedPhysicalCompoundFrameKeyOfComputed input
        input.certified.detectedMultiCenterMolecule domain.graphEq c frame' frameComputed'
        (alpha'.symm i) := by
    simp only [actualSlotCompoundKey, localizedPhysicalCompoundFrameKeyOfComputed,
      referenceDependencyView, localizedPhysicalCompoundFrameView]
    exact compoundKeyAt_eq_of_target_eq_views input.certified hOcc
      (LocalizedUniversalReference.referenceState input) frame'
      (input.certified.localizedOccurrenceFourLigandFrame?_sound
        (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
          domain.graphEq c) frame' frameComputed')
      (actualSlotDerived input c frame' frameComputedTop) (alpha'.symm i)
  have keyEqRight : actualSlotCompoundKey input c frame' frameComputedTop (alpha'.symm j) =
      localizedPhysicalCompoundFrameKeyOfComputed input
        input.certified.detectedMultiCenterMolecule domain.graphEq c frame' frameComputed'
        (alpha'.symm j) := by
    simp only [actualSlotCompoundKey, localizedPhysicalCompoundFrameKeyOfComputed,
      referenceDependencyView, localizedPhysicalCompoundFrameView]
    exact compoundKeyAt_eq_of_target_eq_views input.certified hOcc
      (LocalizedUniversalReference.referenceState input) frame'
      (input.certified.localizedOccurrenceFourLigandFrame?_sound
        (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
          domain.graphEq c) frame' frameComputed')
      (actualSlotDerived input c frame' frameComputedTop) (alpha'.symm j)
  have leftList :
      (actualSlotCompoundKey input c frame' frameComputedTop (alpha'.symm i)).rule5Readings =
        [leftReading] := by
    rw [keyEqLeft]
    exact leftRule5Eq
  have rightList :
      (actualSlotCompoundKey input c frame' frameComputedTop (alpha'.symm j)).rule5Readings =
        [rightReading] := by
    rw [keyEqRight]
    exact rightRule5Eq
  -- The one-branch signed endpoint at the left slot.
  obtain ⟨r, priorReading, reading, keyR, keyS, compoundBuilt, referencesSingleton,
    readingsSingleton, referenceSome, keyReadingsSingleton, priorEq, builtR, builtS,
    commonREq, commonSEq, markSlot, branchMarked, earlierKey, uniqueKey, signed⟩ :=
    actualSlot_compoundReading_stageFor_signed_of_physicalUniqueNearest_witness input c frame'
      frameComputedTop (alpha'.symm i) singleBonded acyclic hcharge noDouble
      (input.certified.canonicalReindexConfiguration cfg) domainGlobal
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) oObservedLeft unique
      prefixStable
  -- The two singleton reading lists share the same production key, so the readings agree.
  have readingEq : reading = leftReading := by
    have lists : [reading] = [leftReading] := by
      rw [← keyReadingsSingleton]
      exact leftList
    simpa using lists
  have mirrorReading : LocalizedRule5SwapAndSignal.MirrorReading input.certified
      leftReading rightReading := by
    simpa [LocalizedCompoundCommonReadingRelation] using relation
  have priorTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (actualSlotCompoundKey input c frame' frameComputedTop (alpha'.symm i)).prior
      (actualSlotCompoundKey input c frame' frameComputedTop (alpha'.symm j)).prior =
        Ordering.eq := by
    rw [keyEqLeft, keyEqRight]
    exact priorTieF197
  have signedReading : OfficialRuleMajorKey.compareSparseLayers
      compareLocalizedCumulativeRule45Priority
      leftReading.commonR.descriptor leftReading.commonS.descriptor =
        (if r = RS.R then Ordering.gt else Ordering.lt) := by
    rw [← readingEq, commonREq, commonSEq]
    exact signed
  have signedR :=
    LocalizedActualUniqueNearestRule5Direction.compareRule5Readings_R_sign_of_singleton_mirror
      input.certified
      (actualSlotCompoundKey input c frame' frameComputedTop (alpha'.symm i))
      (actualSlotCompoundKey input c frame' frameComputedTop (alpha'.symm j))
      leftReading rightReading leftList rightList mirrorReading
      (if r = RS.R then Ordering.gt else Ordering.lt) signedReading
  have strict : (if r = RS.R then Ordering.gt else Ordering.lt) ≠ Ordering.eq := by
    split <;> simp
  have throughResult :=
    LocalizedActualUniqueNearestRule5Direction.throughRule5_signed_pseudo_of_singleton_mirror
      input.certified
      (actualSlotCompoundKey input c frame' frameComputedTop (alpha'.symm i))
      (actualSlotCompoundKey input c frame' frameComputedTop (alpha'.symm j))
      leftReading rightReading leftList rightList mirrorReading priorTie
      (if r = RS.R then Ordering.gt else Ordering.lt) signedR strict
  obtain ⟨occurrence, occurrenceRoot, occurrenceCurrent, occurrenceState⟩ :=
    exists_referenceState_occurrence_at_physicalNearestCenter input c frame' frameComputedTop
      (alpha'.symm i) singleBonded acyclic hcharge noDouble
      (input.certified.canonicalReindexConfiguration cfg) domainGlobal
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) oObservedLeft unique
      referencesSingleton
  exact ⟨frame', alpha', frameComputedTop, oObservedLeft, oObservedRight, r, leftReading,
    rightReading, keyR, keyS, leftList, rightList, mirrorReading, priorTie,
    throughResult.1, throughResult.2, referencesSingleton, branchMarked, markSlot, signed,
    uniqueKey, ⟨occurrence, occurrenceRoot, occurrenceCurrent, occurrenceState⟩⟩

end LocalizedPhysicalRule5SignedExecution

end

end TetraStereo.OneCenter

/-! ## Kernel-only guards -/

assert_kernel_only
  TetraStereo.OneCenter.LocalizedPhysicalRule5SignedExecution.actualTreeMark_actualSlotTree_eq_branchMarkedDescriptor
assert_kernel_only
  TetraStereo.OneCenter.LocalizedPhysicalRule5SignedExecution.branchMarkedDescriptor_eq_selectedReference
assert_kernel_only
  TetraStereo.OneCenter.LocalizedPhysicalRule5SignedExecution.actualSlot_compoundReading_stageFor_signed_of_physicalUniqueNearest_witness
assert_kernel_only
  TetraStereo.OneCenter.LocalizedPhysicalRule5SignedExecution.exists_referenceState_occurrence_at_physicalNearestCenter
assert_kernel_only
  TetraStereo.OneCenter.LocalizedPhysicalRule5SignedExecution.exists_actualSlot_compoundReading_stageFor_signed_of_physicalAtom
assert_kernel_only
  TetraStereo.OneCenter.LocalizedPhysicalRule5SignedExecution.exists_pair_throughRule5_signed_pseudo_of_physicalMirrorTransport
assert_kernel_only
  TetraStereo.OneCenter.LocalizedPhysicalRule5SignedExecution.compoundKeyAt_derived_irrel
assert_kernel_only
  TetraStereo.OneCenter.LocalizedPhysicalRule5SignedExecution.compoundKeyAt_eq_of_target_eq_views
