import TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels
import TetraStereo.OneCenter.LocalizedActualFrameChildClassification
import TetraStereo.OneCenter.LocalizedRootBranchAuxiliaryLocality
import TetraStereo.OneCenter.LocalizedSparseAddressReconstruction
import TetraStereo.OneCenter.LocalizedCumulativeAssemblyRecovery
import TetraStereo.OneCenter.LocalizedRule3DeclarativePriorityAgreement
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-!
# Actual Rule-1a observations for the symmetric cyclic auxiliary arm

This module starts the exact auxiliary-letter proof from the actual occurrence frame.  It anchors
the frame's parent cursor at the stored root occurrence and classifies all remaining frame slots
as outward cursors before exposing any Rule-1a layers.
-/

namespace TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureAuxiliaryLetter

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.LocalizedRuleMajorReference
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels
open TetraStereo.OneCenter.LocalizedCyclicGeneralRigidPriority
open TetraStereo.OneCenter.OfficialCIPNode
open TetraStereo.OneCenter.DeclarativeCIP
open scoped Classical

noncomputable section

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

private theorem fixtureSimpleBonded : symmetricCertified.moleculeGraph.SimpleBonded := by
  intro left right adjacent
  let i : Fin 9 := ⟨left.val, by
    change left.val < symmetricCertified.certified.input.molecule.atomCount
    exact left.isLt⟩
  let j : Fin 9 := ⟨right.val, by
    change right.val < symmetricCertified.certified.input.molecule.atomCount
    exact right.isLt⟩
  have leftEq : left = fixtureAtom i := Fin.ext rfl
  have rightEq : right = fixtureAtom j := Fin.ext rfl
  rw [leftEq, rightEq, fixture_spatialAdj] at adjacent
  exact simple_bonded _ _ adjacent

private theorem rootTarget_address_empty : rootTarget.1.address = [] := by
  simp [rootTarget]

private theorem rootTarget_real :
    rootTarget.1.node.provenance = OfficialCIPNodeProvenance.realAtom :=
  finalOccurrence_provenance_real fixtureReference rootTetra

private theorem rootTarget_current :
    rootTarget.1.node.current? = some rootTetra.1 := by
  simp [rootTarget, rootTetra, OfficialCIPNode.root]

private theorem rootFrames_center_eq_rootTetra : rootFrames.center = rootTetra := by
  apply Subtype.ext
  rw [rootFrames.centerEq]
  simp [rootUnit, finalCenterUnit, OccurrenceUnit.atom, rootTetra]

private theorem rootArmTarget_address :
    rootArmTarget.1.address =
      [symmetricCertified.localizedLigandRootSlot rootFrames.center
        (symmetricCertified.canonicalLigandReindex rootFrames.center
          (rootFrames.detectedLigandPermutation rootArmSlot))] := by
  have cursorEq := LocalizedCyclicRootArmReachability.rootSlot_eq_canonicalLigandCursor
    fixtureSimpleBonded rootFrames rootTarget_address_empty rootTarget_real rootArmSlot
  have addressEq := congrArg
    (fun cursor : symmetricCertified.LocalizedRerootCursor (carrierFuel fixtureReference) =>
      cursor.occurrence.1.address) cursorEq
  simpa [symmetricCertified.localizedLigandRootCursor_address] using addressEq

private theorem rootArmTarget_nonroot : rootArmTarget.1.address ≠ [] := by
  rw [rootArmTarget_address]
  simp

/-- The frame's parent slot is the actual root occurrence, not a newly extended ring copy. -/
theorem rootArmContext_parentCursor_eq_root :
    ∃ parentIndex : Fin 4,
      rootArmContextFrames.frame.cursorAt parentIndex =
        { occurrence := rootTarget, previous? := some rootArmTarget } ∧
      (∀ other : Fin 4, other ≠ parentIndex →
        OutwardRerootCursor symmetricCertified rootArmTarget
          (rootArmContextFrames.frame.cursorAt other)) := by
  obtain ⟨parentIndex, certificate, cursorEq, _parentClass, others⟩ :=
    symmetricCertified.actualFrame_parentIndex rootArmTarget rootArmContextFrames.frame
      (LocalizedCyclicGeneralRigidGeneratedLabels.frame_computed rootArmContextFrames)
      rootArmTarget_nonroot
  have contextRoot : rootArmTarget.1.root = rootTarget.1.root := by
    have rootEq := symmetricCertified.localizedOccurrenceFourLigandFrame_cursor_root
      rootTarget rootFrames.frame
      (LocalizedCyclicGeneralRigidGeneratedLabels.frame_computed rootFrames)
      (rootFrames.frame.cursorAt rootArmSlot)
      (List.get_mem rootFrames.frame.cursors (Fin.cast rootFrames.frame.length_eq.symm rootArmSlot))
    change (rootFrames.frame.cursorAt rootArmSlot).occurrence.1.root = rootTarget.1.root at rootEq
    exact rootEq
  have parentRoot : certificate.parent.1.root = rootTarget.1.root :=
    certificate.parent_root.trans contextRoot
  have parentAddress : certificate.parent.1.address = [] := by
    rw [certificate.parent_address, rootArmTarget_address]
    simp
  have parentDerived :=
    (symmetricCertified.mem_localizedOccurrences_iff (carrierFuel fixtureReference)
      certificate.parent.1).mp certificate.parent.2
  have rootDerived :=
    (symmetricCertified.mem_localizedOccurrences_iff (carrierFuel fixtureReference)
      rootTarget.1).mp rootTarget.2
  have occurrenceEq := symmetricCertified.declarativeLocalizedOccurrence_functional_at_root_address
    parentDerived rootDerived parentRoot parentAddress
  have occurrenceSubtypeEq : certificate.parent = rootTarget := Subtype.ext occurrenceEq
  refine ⟨parentIndex, cursorEq.trans (congrArg (fun occurrence =>
    ({ occurrence := occurrence, previous? := some rootArmTarget } :
      symmetricCertified.LocalizedRerootCursor (carrierFuel fixtureReference)))
        occurrenceSubtypeEq), ?_⟩
  intro other different
  exact (others other different).2

/-- The parent slot's first-sphere observation is the original root carbon (atom 0). -/
theorem rootArmContext_parentCursor_current :
    ∃ parentIndex : Fin 4,
      (rootArmContextFrames.frame.cursorAt parentIndex).occurrence.1.node.current? =
        some rootTetra.1 := by
  obtain ⟨parentIndex, cursorEq, _others⟩ := rootArmContext_parentCursor_eq_root
  exact ⟨parentIndex, by rw [cursorEq]; exact rootTarget_current⟩

private theorem rootTetra_atom0 : rootTetra.1 = fixtureAtom ⟨0, by decide⟩ := by
  apply Fin.ext
  rfl

private theorem armCenter_atom2 :
    rootArmContextFrames.center.1 = fixtureAtom ⟨2, by decide⟩ := by
  rw [rootArmContextFrames.centerEq, rootArmUnit_atom]
  rfl

private theorem arm_slot (index : Fin 9)
    (adjacent : graph.Adj ⟨2, by decide⟩ index) :
    ∃ slot : Fin 4,
      rootArmContextFrames.actualLigandAtoms slot = fixtureAtom index := by
  have adjacentCenter : fixtureReference.certified.moleculeGraph.Adj rootArmContextFrames.center.1
      (fixtureAtom index) := by
    rw [armCenter_atom2]
    exact (fixture_spatialAdj ⟨2, by decide⟩ index).2 adjacent
  obtain ⟨canonical, atomEq⟩ :=
    fixtureReference.certified.detectedMultiCenterMolecule.ligandAtomAt_surjective
      rootArmContextFrames.center (fixtureAtom index) adjacentCenter
  refine ⟨rootArmContextFrames.detectedLigandPermutation.symm canonical, ?_⟩
  change fixtureReference.certified.detectedMultiCenterMolecule.ligandAtomAt
      rootArmContextFrames.center
      (rootArmContextFrames.detectedLigandPermutation
        (rootArmContextFrames.detectedLigandPermutation.symm canonical)) = fixtureAtom index
  rw [Equiv.apply_symm_apply]
  exact atomEq

private noncomputable def parent0Slot : Fin 4 := Classical.choose
  (arm_slot ⟨0, by decide⟩ ((adj_arm 0).mpr (by simp)))

private theorem parent0Slot_atom :
    rootArmContextFrames.actualLigandAtoms parent0Slot = fixtureAtom ⟨0, by decide⟩ :=
  Classical.choose_spec (arm_slot ⟨0, by decide⟩ ((adj_arm 0).mpr (by simp)))

private noncomputable def outward4Slot : Fin 4 := Classical.choose
  (arm_slot ⟨4, by decide⟩ ((adj_arm 4).mpr (by simp)))

private theorem outward4Slot_atom :
    rootArmContextFrames.actualLigandAtoms outward4Slot = fixtureAtom ⟨4, by decide⟩ :=
  Classical.choose_spec (arm_slot ⟨4, by decide⟩ ((adj_arm 4).mpr (by simp)))

private theorem armCursor_current (slot : Fin 4) :
    (rootArmContextFrames.frame.cursorAt slot).occurrence.1.node.current? =
      some (rootArmContextFrames.actualLigandAtoms slot) :=
  rootArmContextFrames.ligandAt slot

private theorem armActualLigandAtoms_injective :
    Function.Injective rootArmContextFrames.actualLigandAtoms := by
  intro left right equal
  apply rootArmContextFrames.detectedLigandPermutation.injective
  apply symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt_injective
  simpa [ContextFrameCompilation.actualLigandAtoms] using equal

/-- The rootward parent index in the actual arm frame is the atom-0 ligand slot. -/
theorem rootArmContext_parentIndex_atom0 :
    ∃ parentIndex : Fin 4,
      parentIndex = parent0Slot ∧
      rootArmContextFrames.frame.cursorAt parentIndex =
        { occurrence := rootTarget, previous? := some rootArmTarget } ∧
      (∀ other : Fin 4, other ≠ parentIndex →
        OutwardRerootCursor symmetricCertified rootArmTarget
          (rootArmContextFrames.frame.cursorAt other)) := by
  obtain ⟨parentIndex, parentEq, others⟩ := rootArmContext_parentCursor_eq_root
  have parentCurrent :
      (rootArmContextFrames.frame.cursorAt parentIndex).occurrence.1.node.current? =
        some rootTetra.1 := by
    rw [parentEq]
    exact rootTarget_current
  have ligandEq : rootArmContextFrames.actualLigandAtoms parentIndex =
      fixtureAtom ⟨0, by decide⟩ := by
    have observed := armCursor_current parentIndex
    rw [parentCurrent, rootTetra_atom0] at observed
    exact (Option.some.inj observed).symm
  exact ⟨parentIndex, armActualLigandAtoms_injective (ligandEq.trans parent0Slot_atom.symm),
    parentEq, others⟩

/-- The atom-4 ligand is an outward occurrence, distinct from the actual rootward parent. -/
theorem rootArmContext_outward4_isOutward :
    OutwardRerootCursor symmetricCertified rootArmTarget
      (rootArmContextFrames.frame.cursorAt outward4Slot) := by
  obtain ⟨parentIndex, _sameSlot, _parentEq, others⟩ := rootArmContext_parentIndex_atom0
  have distinct : outward4Slot ≠ parentIndex := by
    intro same
    have atoms := congrArg rootArmContextFrames.actualLigandAtoms same
    have impossible : fixtureAtom ⟨4, by decide⟩ = fixtureAtom ⟨0, by decide⟩ := by
      calc
        fixtureAtom ⟨4, by decide⟩ = rootArmContextFrames.actualLigandAtoms outward4Slot :=
          outward4Slot_atom.symm
        _ = rootArmContextFrames.actualLigandAtoms parentIndex := atoms
        _ = rootArmContextFrames.actualLigandAtoms parent0Slot := by rw [_sameSlot]
        _ = fixtureAtom ⟨0, by decide⟩ := parent0Slot_atom
    have valueEq := congrArg Fin.val impossible
    norm_num [fixtureAtom] at valueEq
  exact others outward4Slot distinct

end

end TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureAuxiliaryLetter

assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureAuxiliaryLetter.rootArmContext_parentCursor_eq_root
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureAuxiliaryLetter.rootArmContext_parentCursor_current
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureAuxiliaryLetter.rootArmContext_parentIndex_atom0
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureAuxiliaryLetter.rootArmContext_outward4_isOutward
