import TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels
import TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureRootSymmetry
import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness
import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain
import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport
import TetraStereo.OneCenter.LocalizedCyclicRootIndependentJudgment
import TetraStereo.OneCenter.LocalizedCyclicRootPhysicalSetup
import TetraStereo.OneCenter.LocalizedCyclicRootArmReachability
import TetraStereo.OneCenter.LocalizedRetainedCompleteMirrorCovariance
import TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode
import TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-!
# The actual symmetric-fixture root evaluation

This module joins the root's actual compiled frame to its physical recursive domain. Descriptor
return is derived from injectivity of the actual canonical-cut keys; the final physical-letter
theorem then identifies the returned descriptor as lowercase because the detected root has one
physical enantiomorphic pair.
-/

namespace TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureEvaluation

noncomputable section

open TetraStereo.OneCenter
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureDomain
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureRootSymmetry
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport
open TetraStereo.OneCenter.LocalizedCyclicRootPhysicalSetup
open TetraStereo.OneCenter.LocalizedCyclicRootIndependentJudgment
open TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
open TetraStereo.OneCenter.AcyclicCutBranchAutomorphism
open TetraStereo.OneCenter.DeclarativeCIP
open TetraStereo.OneCenter.LocalizedCyclicMatchedReadingDecode
open TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport
open TetraStereo.OneCenter.LocalizedRetainedMirrorDescriptorCorrectness
open TetraStereo.OneCenter.LocalizedCyclicRootArmReachability
open CertifiedLocalizedCIPInput
open LocalizedRuleMajorReference
open scoped Classical

private theorem fixtureSimpleBonded : symmetricCertified.moleculeGraph.SimpleBonded := by
  change graph.SimpleBonded
  exact simple_bonded

private theorem fixtureConstantCharge :
    ConstantFormalCharge symmetricCertified.moleculeGraph := by
  refine ⟨0, ?_⟩
  intro atom
  fin_cases atom <;> decide

private theorem rootGeometry :
    RootPhysicalGeometry symmetricCertified
      symmetricCertified.detectedMultiCenterMolecule detectedCfg rootTetra := by
  exact detectedCoordinates_at rootTetra

private theorem rootDomain :
    RecursiveAuxiliaryPhysicalDomain symmetricCertified detectedCfg rootTetra :=
  detectedDomainAtEveryRoot rootTetra

private theorem rootPairs :
    ConstitutionalPairsEnantiomorphic symmetricCertified.detectedMultiCenterMolecule
      detectedCfg rootTetra :=
  detectedConstitutionalPairsEnantiomorphic rootTetra

private theorem rootPairCount :
    physicalEnantiomorphicPairCount symmetricCertified.detectedMultiCenterMolecule
      detectedCfg rootTetra = 1 :=
  detectedPairCountAtEveryRoot rootTetra

private theorem fixtureAtomCount :
    symmetricCertified.certified.input.molecule.atomCount = 9 := rfl

private def fixtureAtom (i : Fin 9) : symmetricCertified.Atom :=
  ⟨i.val, by rw [fixtureAtomCount]; exact i.isLt⟩

private theorem fixtureAtom_eq (i : Fin 9) : fixtureAtom i = i := by
  apply Fin.ext
  rfl

private theorem fixture_spatialAdj (i j : Fin 9) :
    symmetricCertified.moleculeGraph.Adj (fixtureAtom i) (fixtureAtom j) ↔ graph.Adj i j := by
  rw [fixtureAtom_eq, fixtureAtom_eq]

abbrev rootClosingTarget : Occurrence fixtureReference :=
  (rootFrames.frame.cursorAt rootClosingSlot).occurrence

private theorem rootFrames_center_eq_rootTetra : rootFrames.center = rootTetra := by
  apply Subtype.ext
  rw [rootFrames.centerEq]
  simp [rootUnit, finalCenterUnit, OccurrenceUnit.atom, rootTetra]

private theorem rootArmSwap_fixed0 :
    (rootArmSwap : Equiv.Perm symmetricCertified.Atom) (fixtureAtom 0) = fixtureAtom 0 := by
  change swap24Fun (fixtureAtom 0) = fixtureAtom 0
  decide

private theorem rootArmSwap_maps2 :
    (rootArmSwap : Equiv.Perm symmetricCertified.Atom) (fixtureAtom ⟨2, by decide⟩) =
      fixtureAtom ⟨4, by decide⟩ := by
  apply Fin.ext
  change (swap24Fun (2 : Fin 9)).val = 4
  decide

private theorem rootArm_atom :
    rootFrames.actualLigandAtoms rootArmSlot = fixtureAtom ⟨2, by decide⟩ :=
  rootArmSlot_atom.trans rfl

private theorem rootClosing_atom :
    rootFrames.actualLigandAtoms rootClosingSlot = fixtureAtom ⟨4, by decide⟩ :=
  rootClosingSlot_atom.trans rfl

private theorem rootFrame_actualLigandAtoms_injective :
    Function.Injective rootFrames.actualLigandAtoms := by
  intro i j equal
  apply rootFrames.detectedLigandPermutation.injective
  apply symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt_injective
  simpa [ContextFrameCompilation.actualLigandAtoms] using equal

private theorem rootFrame_slot_observation (slot : Fin 4) :
    (symmetricCertified.moleculeGraph.atomZ (rootFrames.actualLigandAtoms slot) = 1 ∧
      rootFrames.actualLigandAtoms slot = fixtureAtom 5) ∨
    (symmetricCertified.moleculeGraph.atomZ (rootFrames.actualLigandAtoms slot) = 6 ∧
      (rootFrames.actualLigandAtoms slot = fixtureAtom 2 ∨
        rootFrames.actualLigandAtoms slot = fixtureAtom 4)) ∨
    (symmetricCertified.moleculeGraph.atomZ (rootFrames.actualLigandAtoms slot) = 17 ∧
      rootFrames.actualLigandAtoms slot = fixtureAtom 1) := by
  let atom := rootFrames.actualLigandAtoms slot
  have ligandEq : rootFrames.actualLigandAtoms slot =
      symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
        (rootFrames.detectedLigandPermutation slot) := by
    rfl
  have adjacent : symmetricCertified.moleculeGraph.Adj rootFrames.center.1 atom := by
    change symmetricCertified.moleculeGraph.Adj rootFrames.center.1
      (symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
        (rootFrames.detectedLigandPermutation slot))
    exact symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt_adj rootFrames.center
      (rootFrames.detectedLigandPermutation slot)
  have adjacent' : graph.Adj 0 atom := by
    rw [← fixture_spatialAdj 0 atom]
    simpa [rootFrames_center_eq_rootTetra, rootTetra, fixtureAtom] using adjacent
  rcases (adj_root atom).mp adjacent' with h1 | h2 | h4 | h5
  · have atomEq : rootFrames.actualLigandAtoms slot = fixtureAtom 1 := by
      simpa [atom, fixtureAtom] using h1
    refine Or.inr (Or.inr ⟨?_, atomEq⟩)
    rw [atomEq]
    exact (atomZ_cases 1).2.1.mpr (Or.inl rfl)
  · have atomEq : rootFrames.actualLigandAtoms slot = fixtureAtom 2 := by
      simpa [atom, fixtureAtom] using h2
    refine Or.inr (Or.inl ⟨?_, Or.inl atomEq⟩)
    rw [atomEq]
    exact (atomZ_cases 2).1.mpr (Or.inr (Or.inl rfl))
  · have atomEq : rootFrames.actualLigandAtoms slot = fixtureAtom 4 := by
      simpa [atom, fixtureAtom] using h4
    refine Or.inr (Or.inl ⟨?_, Or.inr atomEq⟩)
    rw [atomEq]
    exact (atomZ_cases 4).1.mpr (Or.inr (Or.inr rfl))
  · have atomEq : rootFrames.actualLigandAtoms slot = fixtureAtom 5 := by
      simpa [atom, fixtureAtom] using h5
    refine Or.inl ⟨?_, atomEq⟩
    rw [atomEq]
    exact (atomZ_cases 5).2.2.mpr (Or.inl rfl)

private theorem rootFrame_slot_atom_eq_of_atomZ_eq (i j : Fin 4)
    (equalZ : symmetricCertified.moleculeGraph.atomZ (rootFrames.actualLigandAtoms i) =
      symmetricCertified.moleculeGraph.atomZ (rootFrames.actualLigandAtoms j)) :
    i = j ∨ (i = rootArmSlot ∧ j = rootClosingSlot) ∨
      (i = rootClosingSlot ∧ j = rootArmSlot) := by
  rcases rootFrame_slot_observation i with ⟨leftZ1, leftAtom1⟩ |
    ⟨leftZ6, leftAtoms6⟩ | ⟨leftZ17, leftAtom17⟩
  · rcases rootFrame_slot_observation j with ⟨rightZ1, rightAtom1⟩ |
      ⟨rightZ6, rightAtoms6⟩ | ⟨rightZ17, rightAtom17⟩
    · exact Or.inl (rootFrame_actualLigandAtoms_injective (leftAtom1.trans rightAtom1.symm))
    · have impossible : (1 : ℕ) = 6 := leftZ1.symm.trans (equalZ.trans rightZ6)
      norm_num at impossible
    · have impossible : (1 : ℕ) = 17 := leftZ1.symm.trans (equalZ.trans rightZ17)
      norm_num at impossible
  · rcases rootFrame_slot_observation j with ⟨rightZ1, rightAtom1⟩ |
      ⟨rightZ6, rightAtoms6⟩ | ⟨rightZ17, rightAtom17⟩
    · have impossible : (6 : ℕ) = 1 := leftZ6.symm.trans (equalZ.trans rightZ1)
      norm_num at impossible
    · rcases leftAtoms6 with left2 | left4 <;> rcases rightAtoms6 with right2 | right4
      · exact Or.inl (rootFrame_actualLigandAtoms_injective (left2.trans right2.symm))
      · exact Or.inr (Or.inl ⟨rootFrame_actualLigandAtoms_injective
          (left2.trans rootArmSlot_atom.symm), rootFrame_actualLigandAtoms_injective
          (right4.trans rootClosingSlot_atom.symm)⟩)
      · exact Or.inr (Or.inr ⟨rootFrame_actualLigandAtoms_injective
          (left4.trans rootClosingSlot_atom.symm), rootFrame_actualLigandAtoms_injective
          (right2.trans rootArmSlot_atom.symm)⟩)
      · exact Or.inl (rootFrame_actualLigandAtoms_injective (left4.trans right4.symm))
    · have impossible : (6 : ℕ) = 17 := leftZ6.symm.trans (equalZ.trans rightZ17)
      norm_num at impossible
  · rcases rootFrame_slot_observation j with ⟨rightZ1, rightAtom1⟩ |
      ⟨rightZ6, rightAtoms6⟩ | ⟨rightZ17, rightAtom17⟩
    · have impossible : (17 : ℕ) = 1 := leftZ17.symm.trans (equalZ.trans rightZ1)
      norm_num at impossible
    · have impossible : (17 : ℕ) = 6 := leftZ17.symm.trans (equalZ.trans rightZ6)
      norm_num at impossible
    · exact Or.inl (rootFrame_actualLigandAtoms_injective (leftAtom17.trans rightAtom17.symm))

private theorem rootFrame_rule1aTie_atomZ_eq (i j : Fin 4)
    (tie : symmetricCertified.compareLocalizedRerootCompoundRule45Keys
      (rootFrames.compounds i) (rootFrames.compounds j) = Ordering.eq) :
    symmetricCertified.moleculeGraph.atomZ (rootFrames.actualLigandAtoms i) =
      symmetricCertified.moleculeGraph.atomZ (rootFrames.actualLigandAtoms j) := by
  obtain ⟨priorTie, _⟩ := fullTie_rule45Tie_prior_and_readings symmetricCertified _ _ tie
  have rule4aTie :=
    ((symmetricCertified.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff _ _).mp
      priorTie).1
  obtain ⟨armL⟩ := nonempty_rootArm rootFrames .rule4a i
  obtain ⟨armR⟩ := nonempty_rootArm rootFrames .rule4a j
  have constitutionalTie := armTie_of_rule4aTie rootFrames armL armR rule4aTie
  have columns := (officialRuleMajorKey_compare_eq_iff _ _).mp constitutionalTie
  have rule1aTie := (compareSparseLayers_compareNat_eq_iff _ _).mpr columns.1
  have rootZ := actual_rule1a_tie_rootAtomicNumber_eq symmetricCertified armL.built armR.built
    rule1aTie
  have currentL : (rootFrames.frame.cursorAt i).occurrence.1.node.current? =
      some (rootFrames.actualLigandAtoms i) := by
    simpa [ContextFrameCompilation.actualLigandAtoms] using rootFrames.ligandAt i
  have currentR : (rootFrames.frame.cursorAt j).occurrence.1.node.current? =
      some (rootFrames.actualLigandAtoms j) := by
    simpa [ContextFrameCompilation.actualLigandAtoms] using rootFrames.ligandAt j
  rw [← cursorRootAtomicNumber_eq_atomZ_of_current symmetricCertified _ currentL,
    ← cursorRootAtomicNumber_eq_atomZ_of_current symmetricCertified _ currentR]
  exact rootZ

private theorem rootTarget_address_empty : rootTarget.1.address = [] := by
  simp [rootTarget]

private theorem rootTarget_real :
    rootTarget.1.node.provenance = OfficialCIPNodeProvenance.realAtom :=
  finalOccurrence_provenance_real fixtureReference rootTetra

private theorem rootCompoundTie_of_canonicalCutKeys_eq {i j : Fin 4}
    (keys : canonicalCutKeys fixtureReference fixtureSimpleBonded rootTetra i =
      canonicalCutKeys fixtureReference fixtureSimpleBonded rootTetra j) :
    symmetricCertified.compareLocalizedRerootCompoundRule45Keys
      (rootFrames.compounds i) (rootFrames.compounds j) = Ordering.eq := by
  have keyCmp : compare
      (canonicalCutKeys fixtureReference fixtureSimpleBonded rootTetra i)
      (canonicalCutKeys fixtureReference fixtureSimpleBonded rootTetra j) = Ordering.eq :=
    (completeLigandRule5Key_compare_eq_iff _ _).mpr keys
  have retainedEq := canonicalCutKeys_eq_retainedKeys
    (input := fixtureReference) fixtureSimpleBonded rootTetra
  dsimp [canonicalCutKeys, LocalizedCyclicRootIndependentJudgment.canonicalCutKeys] at keyCmp
  rw [retainedEq] at keyCmp
  have ordering := rootFrames.retainedActual_fullOrdering fixtureSimpleBonded i j
  rw [CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5_ordering] at ordering
  calc
    symmetricCertified.compareLocalizedRerootCompoundRule45Keys
        (rootFrames.compounds i) (rootFrames.compounds j) =
      compare (rootFrames.retainedKeys i) (rootFrames.retainedKeys j) := ordering
    _ = Ordering.eq := keyCmp

/-- The fixture's accepted root mirror, followed through the recursive auxiliary reader, reflects
the actual C2 descriptor at the transported C4 occurrence. -/
theorem rootArm_actualState_reflectedAtClosing
    {raw : RS}
    (armState : referenceState fixtureReference rootArmTarget = some (.chiral raw)) :
    referenceState fixtureReference rootClosingTarget = some (.chiral (RS.swap raw)) := by
  have frameCenter : rootFrames.center = rootTetra := rootFrames_center_eq_rootTetra
  let actualMirror : symmetricCertified.detectedMultiCenterMolecule.Aut :=
    symmetricCertified.physicalDetectedAut rootArmSwap
  have fixed : symmetricCertified.detectedMultiCenterMolecule.centerPerm actualMirror rootTetra =
      rootTetra := by
    apply Subtype.ext
    change (rootArmSwap : Equiv.Perm symmetricCertified.Atom) rootTetra.1 = rootTetra.1
    change (rootArmSwap : Equiv.Perm symmetricCertified.Atom) (fixtureAtom 0) = fixtureAtom 0
    exact rootArmSwap_fixed0
  let leftIndex := rootFrames.detectedLigandPermutation rootArmSlot
  let rightIndex := rootFrames.detectedLigandPermutation rootClosingSlot
  have indicesNe : leftIndex ≠ rightIndex := by
    intro same
    exact rootArmSlot_ne_rootClosingSlot (rootFrames.detectedLigandPermutation.injective same)
  have sent : symmetricCertified.detectedMultiCenterMolecule.ligandPermAt actualMirror rootTetra
      leftIndex = rightIndex := by
    apply symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt_injective
    have action := symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt_ligandPermAt
      actualMirror rootTetra leftIndex
    rw [fixed] at action
    have sourceAtom :
        symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt rootTetra leftIndex =
          rootFrames.actualLigandAtoms rootArmSlot := by
      rw [← frameCenter]
      rfl
    have imageAtom :
        symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt rootTetra rightIndex =
          rootFrames.actualLigandAtoms rootClosingSlot := by
      rw [← frameCenter]
      rfl
    calc
      symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt rootTetra
          (symmetricCertified.detectedMultiCenterMolecule.ligandPermAt actualMirror rootTetra
            leftIndex) =
          (actualMirror : Equiv.Perm symmetricCertified.Atom)
            (symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt rootTetra leftIndex) := action
      _ = (rootArmSwap : Equiv.Perm symmetricCertified.Atom)
            (symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt rootTetra leftIndex) := by
        change (symmetricCertified.moleculeGraph.detectedMultiCenterAutOfGraphAut rootArmSwap :
          Equiv.Perm symmetricCertified.Atom) _ = _
        rfl
      _ = (rootArmSwap : Equiv.Perm symmetricCertified.Atom)
            (fixtureAtom ⟨2, by decide⟩) := by rw [sourceAtom, rootArm_atom]
      _ = fixtureAtom ⟨4, by decide⟩ := rootArmSwap_maps2
      _ = rootFrames.actualLigandAtoms rootClosingSlot := rootClosing_atom.symm
      _ = symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt rootTetra rightIndex :=
        imageAtom.symm
  have enantiomorphic := rootPairs actualMirror fixed leftIndex rightIndex indicesNe sent
  have graphMirror := enantiomorphic.2.1
  obtain ⟨mirrorAut, mirrorFixed, mirrorSent, mirrorSigns⟩ := graphMirror
  let graphAut :=
    LocalizedCyclicPhysicalMirrorPriorTie.detectedGraphAut symmetricCertified mirrorAut
  have transport : symmetricCertified.DetectedBranchTransport graphAut detectedCfg rootTetra
      leftIndex rightIndex true := ⟨mirrorFixed, mirrorSent, mirrorSigns⟩
  have recursiveDomain : RecursiveAuxiliaryPhysicalDomain symmetricCertified detectedCfg
      rootFrames.center := by
    simpa [frameCenter] using detectedDomainAtEveryRoot rootTetra
  have rootAddress : rootTarget.1.address = [] := by simp [rootTarget]
  have rootReal : rootTarget.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
    exact finalOccurrence_provenance_real fixtureReference rootTetra
  have reach : LocalizedRecursiveAuxiliaryPhysicalTransport.Reach rootFrames rootArmSlot
      rootArmTarget := by
    refine ⟨rootFrames.frame.cursorAt rootArmSlot, rfl, Relation.ReflTransGen.refl⟩
  have transport' : symmetricCertified.DetectedBranchTransport graphAut detectedCfg
      rootFrames.center (rootFrames.detectedLigandPermutation rootArmSlot)
      (rootFrames.detectedLigandPermutation rootClosingSlot) true := by
    simpa [frameCenter] using transport
  have law := LocalizedRecursiveAuxiliaryPhysicalTransport.law_of_reach
    fixtureSimpleBonded rootFrames rootAddress rootReal detectedCfg recursiveDomain graphAut
    rootArmSlot_ne_rootClosingSlot true transport'
    rootArmTarget reach
  have targetHistoryFixed : ∀ x ∈ rootTarget.1.node.history,
      (graphAut : Equiv.Perm symmetricCertified.Atom) x = x := by
    intro x member
    have history : rootTarget.1.node.history = [rootTarget.1.root] := by
      change (OfficialCIPNode.root rootTetra.1).history = [rootTetra.1]
      simp [OfficialCIPNode.root]
    rw [history, List.mem_singleton] at member
    subst x
    change (mirrorAut : Equiv.Perm symmetricCertified.Atom) rootTarget.1.root = rootTarget.1.root
    have rootEq : rootTarget.1.root = rootTetra.1 := by
      change (fixtureReference.certified.localizedFinalOccurrenceExecutable
        (carrierFuel fixtureReference) rootTetra).1.root = rootTetra.1
      exact fixtureReference.certified.localizedFinalOccurrenceExecutable_root
        (carrierFuel fixtureReference) rootTetra
    rw [rootEq]
    exact congrArg Subtype.val mirrorFixed
  have occurrenceFrameComputed :
      fixtureReference.certified.localizedOccurrenceFourLigandFrame? rootTarget =
        some rootFrames.frame := by
    have h := rootFrames.frameComputed
    rw [fixtureReference.certified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?
      rootTarget] at h
    exact h
  have outward := fixtureReference.certified.localizedOccurrenceFourLigandFrame_root_all_outward
    rootTarget rootFrames.frame occurrenceFrameComputed rootAddress
  have sentSlots :
      (graphAut : Equiv.Perm symmetricCertified.Atom)
          (symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
            (rootFrames.detectedLigandPermutation rootArmSlot)) =
        symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
          (rootFrames.detectedLigandPermutation rootClosingSlot) := by
    have action := symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt_ligandPermAt
      mirrorAut rootTetra leftIndex
    rw [mirrorFixed] at action
    have atomSent :
        (mirrorAut : Equiv.Perm symmetricCertified.Atom)
            (symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt rootTetra leftIndex) =
          symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt rootTetra rightIndex := by
      rw [mirrorSent] at action
      exact action.symm
    change (mirrorAut : Equiv.Perm symmetricCertified.Atom)
      (symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
        (rootFrames.detectedLigandPermutation rootArmSlot)) = _
    simpa [frameCenter, leftIndex, rightIndex] using atomSent
  have slotCursorTransport :=
    LocalizedRecursiveAuxiliaryPhysicalCorrectness.transportCursor_slot_of_history
      fixtureSimpleBonded rootFrames rootReal graphAut
      (outward rootArmSlot).2 (outward rootClosingSlot).2 targetHistoryFixed sentSlots
  have transportedOccurrence :
      symmetricCertified.transportOccurrence fixtureSimpleBonded graphAut rootArmTarget =
        rootClosingTarget := by
    calc
      symmetricCertified.transportOccurrence fixtureSimpleBonded graphAut rootArmTarget =
          (symmetricCertified.transportCursor fixtureSimpleBonded graphAut
            (rootFrames.frame.cursorAt rootArmSlot)).occurrence := by
        simp only [symmetricCertified.transportCursor_occurrence]
      _ = rootClosingTarget := by
        simpa [rootClosingTarget] using congrArg
          (fun cursor : symmetricCertified.LocalizedRerootCursor
            (carrierFuel fixtureReference) => cursor.occurrence) slotCursorTransport
  unfold LocalizedRecursiveAuxiliaryPhysicalTransport.Law at law
  change referenceState fixtureReference
      (fixtureReference.certified.transportOccurrence fixtureSimpleBonded graphAut rootArmTarget) =
      Option.map (retainedPhysicalLetter true)
        (referenceState fixtureReference rootArmTarget) at law
  have transportedOccurrence' :
      fixtureReference.certified.transportOccurrence fixtureSimpleBonded graphAut rootArmTarget =
        rootClosingTarget := by
    simpa [fixtureReference] using transportedOccurrence
  rw [transportedOccurrence'] at law
  rw [armState] at law
  simpa [LocalizedRecursiveAuxiliaryPhysicalTransport.Law,
    retainedPhysicalLetter] using law

/-- A tie of the actual root compound keys forces equality of the root labels in their first
common-`R` Rule-5 context arms. The labels are left as actual decorated-tree root observations so
that a fixture-specific generated-state fact can be applied without decoding deeper addresses. -/
theorem fullTie_commonR_rootLabels_eq
    (frames : ContextFrameCompilation fixtureReference rootTarget rootUnit rootTargetUnit)
    (rootAddress : rootTarget.1.address = [])
    (rootReal : rootTarget.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {i j : Fin 4}
    (fullTie : symmetricCertified.compareLocalizedRerootCompoundRule45Keys
      (frames.compounds i) (frames.compounds j) = Ordering.eq) :
    ∃ (left right : symmetricCertified.LocalizedRerootRule5Reading),
      left ∈ (frames.compounds i).rule5Readings ∧
      right ∈ (frames.compounds j).rule5Readings ∧
      referenceState fixtureReference (frames.frame.cursorAt i).occurrence =
        referenceState fixtureReference (frames.frame.cursorAt j).occurrence := by
  obtain ⟨priorTie, readingsTie⟩ :=
    fullTie_rule45Tie_prior_and_readings symmetricCertified _ _ fullTie
  obtain ⟨headL, tailL, eqL⟩ :=
    fullTie_list_exists_cons_of_ne_nil (compound_rule5Readings_ne_nil' frames i)
  obtain ⟨headR, tailR, eqR⟩ :=
    fullTie_list_exists_cons_of_ne_nil (compound_rule5Readings_ne_nil' frames j)
  have consTie : symmetricCertified.compareLocalizedRerootCompoundRule5Readings .R
      (headL :: tailL) (headR :: tailR) = Ordering.eq := by
    rw [← eqL, ← eqR]
    exact readingsTie
  have heads := fullTie_compareRule5Readings_cons_cons_eq symmetricCertified .R headL headR
    tailL tailR consTie
  have commonR : headL.commonR.descriptor = headR.commonR.descriptor := by
    simpa only [localizedRerootRule5Descriptor] using heads
  have leftMember : headL ∈ (frames.compounds i).rule5Readings := by
    rw [eqL]
    exact List.mem_cons_self
  have rightMember : headR ∈ (frames.compounds j).rule5Readings := by
    rw [eqR]
    exact List.mem_cons_self
  obtain ⟨armL⟩ := nonempty_rootArm frames
    (localizedRule5StageFor headL.prior.reference? .R) i
  obtain ⟨armR⟩ := nonempty_rootArm frames
    (localizedRule5StageFor headR.prior.reference? .R) j
  have keyL := arm_key_eq_of_built armL (compound_commonR_built frames i leftMember)
  have keyR := arm_key_eq_of_built armR (compound_commonR_built frames j rightMember)
  have descriptors : armL.key.descriptor = armR.key.descriptor := by
    rw [keyL, keyR]
    exact commonR
  have leftAt : armL.tree.decoratedSubtreeAt? [] = some armL.tree := rfl
  have rightAt : armR.tree.decoratedSubtreeAt? [] = some armR.tree := rfl
  have labels := commonReading_labels_eq armL armR descriptors [] armL.tree armR.tree
    leftAt rightAt
  have leftFacts := arm_subtree_branch_facts frames rootAddress rootReal i armL leftAt
  have rightFacts := arm_subtree_branch_facts frames rootAddress rootReal j armR rightAt
  have leftState : armL.tree.label =
      referenceState fixtureReference (frames.frame.cursorAt i).occurrence := by
    calc
      armL.tree.label = contextOccurrenceRead fixtureReference rootTarget armL.tree.source :=
        arm_label_eq_read armL [] armL.tree leftAt
      _ = referenceState fixtureReference armL.tree.source.occurrence := by
        change symmetricCertified.localizedDependencyLabel rootTarget
          (symmetricCertified.localizedDependencyView (referenceState fixtureReference) rootTarget)
          armL.tree.source = _
        exact symmetricCertified.localizedDependencyLabel_eq_state_of_dependency rootTarget
          (referenceState fixtureReference) armL.tree.source leftFacts.2.2.2
      _ = referenceState fixtureReference (frames.frame.cursorAt i).occurrence := by
        rw [armL.sourceEq]
  have rightState : armR.tree.label =
      referenceState fixtureReference (frames.frame.cursorAt j).occurrence := by
    calc
      armR.tree.label = contextOccurrenceRead fixtureReference rootTarget armR.tree.source :=
        arm_label_eq_read armR [] armR.tree rightAt
      _ = referenceState fixtureReference armR.tree.source.occurrence := by
        change symmetricCertified.localizedDependencyLabel rootTarget
          (symmetricCertified.localizedDependencyView (referenceState fixtureReference) rootTarget)
          armR.tree.source = _
        exact symmetricCertified.localizedDependencyLabel_eq_state_of_dependency rootTarget
          (referenceState fixtureReference) armR.tree.source rightFacts.2.2.2
      _ = referenceState fixtureReference (frames.frame.cursorAt j).occurrence := by
        rw [armR.sourceEq]
  exact ⟨headL, headR, leftMember, rightMember,
    leftState.symm.trans (labels.trans rightState)⟩

/-- The actual four retained root keys are injective. First-sphere observations separate H and Cl
from the two carbon arms; the latter pair is separated by its actual common-R root labels. -/
theorem root0_canonicalCutKeys_injective :
    Function.Injective (canonicalCutKeys fixtureReference fixtureSimpleBonded rootTetra) := by
  intro i j keys
  by_contra different
  have fullTie := rootCompoundTie_of_canonicalCutKeys_eq keys
  have equalZ := rootFrame_rule1aTie_atomZ_eq i j fullTie
  rcases rootFrame_slot_atom_eq_of_atomZ_eq i j equalZ with same | pair | pair
  · exact different same
  · rcases pair with ⟨leftArm, rightClosing⟩
    subst i
    subst j
    obtain ⟨_left, _right, _memL, _memR, statesEq⟩ :=
      fullTie_commonR_rootLabels_eq rootFrames rootTarget_address_empty rootTarget_real fullTie
    have actualStates : referenceState fixtureReference rootArmTarget =
        referenceState fixtureReference rootClosingTarget := by
      simpa [rootArmTarget, rootClosingTarget] using statesEq
    obtain ⟨raw, armState⟩ := rootArm_actualState_isChiral
    have closingState := rootArm_actualState_reflectedAtClosing armState
    rw [armState, closingState] at actualStates
    cases raw <;> simp [RS.swap] at actualStates
  · rcases pair with ⟨leftClosing, rightArm⟩
    subst i
    subst j
    obtain ⟨_left, _right, _memL, _memR, statesEq⟩ :=
      fullTie_commonR_rootLabels_eq rootFrames rootTarget_address_empty rootTarget_real fullTie
    have actualStates : referenceState fixtureReference rootArmTarget =
        referenceState fixtureReference rootClosingTarget := by
      simpa [rootArmTarget, rootClosingTarget] using statesEq.symm
    obtain ⟨raw, armState⟩ := rootArm_actualState_isChiral
    have closingState := rootArm_actualState_reflectedAtClosing armState
    rw [armState, closingState] at actualStates
    cases raw <;> simp [RS.swap] at actualStates

/-- Actual `referenceState` returns a descriptor once the actual retained complete keys are
injective. The only remaining fixture-specific premise is the C2/C4 Rule-5 separation. -/
theorem root0_referenceState_isSome_of_keys_injective
    (injective : Function.Injective (canonicalCutKeys fixtureReference fixtureSimpleBonded
      rootTetra)) :
    ∃ descriptor : LocalizedAuxiliaryLabel,
      referenceState fixtureReference rootTarget = some descriptor := by
  let frames := finalRootFrames fixtureReference fixtureSimpleBonded rootTetra
  obtain ⟨pointAt, _observed, _volume, _sign, frameCoordinates, volume⟩ :=
    frames_coordinates (singleBonded := fixtureSimpleBonded) (center := rootTetra) rootGeometry
  let points : Fin 4 → CartesianPoint3 :=
    fun slot => pointAt (frames.detectedLigandPermutation slot)
  have judgmentExists :=
    (LocalizedRetainedCompleteMirrorCovariance.completeRootDescriptorJudgment_exists_iff
      (canonicalCutKeys fixtureReference fixtureSimpleBonded rootTetra) points).2
      ⟨injective, volume⟩
  obtain ⟨descriptor, judgment⟩ := judgmentExists
  have retained : RetainedContextualDescriptorJudgmentAt
      symmetricCertified.moleculeGraph (descriptorMap fixtureReference)
      (finalCenterUnit fixtureReference rootTetra)
      (frames.canonicalCutGraphs fixtureSimpleBonded) frames.W frames.D
      frames.actualCoordinates descriptor := by
    refine ⟨points, ?_, ?_⟩
    · intro slot
      exact frameCoordinates slot
    · simpa [canonicalCutKeys, LocalizedCyclicRootIndependentJudgment.canonicalCutKeys,
        frames, points] using judgment
  exact ⟨descriptor, (frames.referenceState_some_iff_canonicalCutJudgment
    fixtureSimpleBonded descriptor).2 retained⟩

/-- Any descriptor returned by the actual root is lowercase, since the physical detected
configuration has exactly one enantiomorphic pair at that root. -/
theorem root0_returned_descriptor_isLowercase
    {descriptor : LocalizedAuxiliaryLabel}
    (returned : referenceState fixtureReference rootTarget = some descriptor) :
    descriptor.IsLowercase := by
  have physical := finalRoot_physical_letter_of_pairs
    (input := fixtureReference) (singleBonded := fixtureSimpleBonded)
    (center := rootTetra) fixtureConstantCharge detectedCfg rootDomain rootPairs rootGeometry
    returned
  exact physical.2.1.mpr rootPairCount

/-- The production root returns its actual lowercase pseudo descriptor with injectivity proved for
the accepted nine-atom fixture. -/
theorem root0_actualState_isLowercase :
    ∃ descriptor : LocalizedAuxiliaryLabel,
      referenceState fixtureReference rootTarget = some descriptor ∧ descriptor.IsLowercase := by
  obtain ⟨descriptor, returned⟩ :=
    root0_referenceState_isSome_of_keys_injective root0_canonicalCutKeys_injective
  exact ⟨descriptor, returned, root0_returned_descriptor_isLowercase returned⟩

/-- The actual detected-center report contains the proved lowercase descriptor at root 0. -/
theorem root0_analyze_reports_lowercase :
    ∃ descriptor : LocalizedAuxiliaryLabel,
      (rootTetra.val.val, some descriptor) ∈ analyze fixtureReference ∧
        descriptor.IsLowercase := by
  obtain ⟨descriptor, returned, lowercase⟩ := root0_actualState_isLowercase
  refine ⟨descriptor, ?_, lowercase⟩
  rw [LocalizedRuleMajorReference.analyze_eq_referenceReport fixtureReference]
  apply List.mem_map.mpr
  refine ⟨rootTetra, ?_, ?_⟩
  · exact (fixtureReference.certified.mem_canonicalTetrahedralCenters_iff rootTetra).mpr
      rootTetra.2
  · apply Prod.ext
    · rfl
    · simpa [rootTarget] using returned

end
end TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureEvaluation

assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureEvaluation.rootArm_actualState_reflectedAtClosing
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureEvaluation.fullTie_commonR_rootLabels_eq
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureEvaluation.root0_canonicalCutKeys_injective
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureEvaluation.root0_referenceState_isSome_of_keys_injective
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureEvaluation.root0_returned_descriptor_isLowercase
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureEvaluation.root0_actualState_isLowercase
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureEvaluation.root0_analyze_reports_lowercase
