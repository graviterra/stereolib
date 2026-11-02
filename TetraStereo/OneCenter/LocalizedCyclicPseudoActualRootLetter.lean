import TetraStereo.OneCenter.LocalizedCyclicPseudoActualEvaluation
import TetraStereo.OneCenter.LocalizedCyclicPseudoPhysicalPairs
import TetraStereo.OneCenter.LocalizedRetainedContextAllOccurrences
import TetraStereo.KernelOnly
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-!
# Geometry and physical support for the cyclic fixture root

This module proves the actual root coordinates and their raw `S` reading for the specified order
`F, C2, C4, H`, together with the physical domain, pair count and ring witness. It does not identify
that order as runtime priority. The importing `LocalizedCyclicPseudoComputableReader` derives the
full compound comparisons and assembles the actual current `referenceState` result using these
geometry facts and the retained-key judgment.
-/

namespace TetraStereo.OneCenter.LocalizedCyclicPseudoActualRootLetter

open TetraStereo.OneCenter
open CartesianPoint3
open CertifiedLocalizedCIPInput
open LocalizedCyclicPseudoInputWitness
open LocalizedCyclicPseudoSpatialWitness
open LocalizedCyclicPseudoPhysicalDomain
open LocalizedCyclicPseudoPhysicalPairs
open LocalizedCyclicPseudoActualEvaluation
open LocalizedCyclicPseudoRootComponentEvaluation
open LocalizedRuleMajorReference
open RootedTetrahedralBranchSymmetry

noncomputable section

/-- The coordinate-calibrated actual root frame has the canonical source orientation. -/
theorem actual_root_configuration_sign :
    physicalMolecule.configurationSign physicalCfg
      LocalizedCyclicPseudoPhysicalDomain.rootCenter = 1 := by
  change physicalMolecule.configurationSign physicalCfg
    (centerFromCanon LocalizedCyclicPseudoSpatialWitness.rootCenter) = 1
  rw [configurationSign_physicalCfg LocalizedCyclicPseudoSpatialWitness.rootCenter]
  exact LocalizedCyclicPseudoSpatialWitness.root_configurationSign

/-- The physical root's unique enantiomorphic pair is the pair of ring-carbon branches. -/
theorem actual_root_physical_pair_count :
    physicalEnantiomorphicPairCount physicalMolecule physicalCfg
      LocalizedCyclicPseudoPhysicalDomain.rootCenter = 1 :=
  LocalizedCyclicPseudoPhysicalPairs.actual_root_physical_pair_count

/-- Every pair of distinct actual root ligands is properly distinguishable. -/
theorem actual_root_pairwise_proper_distinguishable :
    MultiCenterMolecule.PairwiseProperDistinguishable physicalMolecule physicalCfg
      LocalizedCyclicPseudoPhysicalDomain.rootCenter :=
  LocalizedCyclicPseudoPhysicalPairs.actual_pairwise_proper_distinguishable

private def sourcePoint (i : Fin 9) : CartesianPoint3 :=
  positions[i.val]'(by simp [positions])

private theorem sourcePoint_lookup (i : Fin 9) :
    positions[i.val]? = some (sourcePoint i) := by
  exact List.getElem?_eq_getElem (by simp [positions])

private theorem actualSpatialPoint (i : Fin 9) :
    pseudoSpatialCertified.spatialPointAt? (atomEquiv i) = some (sourcePoint i) := by
  rw [spatialPointAt?_eq_some_iff]
  refine ⟨⟨positions⟩, rfl, ?_⟩
  change positions[(atomEquiv i).val]? = some (sourcePoint i)
  rw [show (atomEquiv i).val = i.val by rfl]
  exact sourcePoint_lookup i

/-- The four production root-frame slots read the certified coordinates at their actual atoms. -/
theorem actual_root_coordinate_slots :
    rootFrames.actualCoordinates rootFluorineSlot = some P1 ∧
    rootFrames.actualCoordinates rootArmSlot = some P2 ∧
    rootFrames.actualCoordinates rootClosingSlot = some P4 ∧
    rootFrames.actualCoordinates rootHydrogenSlot = some P5 := by
  have correspondence := root_actual_frame_correspondence
  refine ⟨?_, ?_, ?_, ?_⟩
  · change pseudoSpatialCertified.spatialPointAt?
      (rootFrames.actualLigandAtoms rootFluorineSlot) = some P1
    have atomEq : rootFrames.actualLigandAtoms rootFluorineSlot =
        atomEquiv ⟨1, by decide⟩ := by
      rw [correspondence.1]
      apply Fin.ext
      rfl
    rw [atomEq]
    change pseudoSpatialCertified.spatialPointAt? (atomEquiv ⟨1, by decide⟩) = some P1
    simpa [sourcePoint, positions, P1, point] using actualSpatialPoint ⟨1, by decide⟩
  · change pseudoSpatialCertified.spatialPointAt?
      (rootFrames.actualLigandAtoms rootArmSlot) = some P2
    have atomEq : rootFrames.actualLigandAtoms rootArmSlot =
        atomEquiv ⟨2, by decide⟩ := by
      rw [correspondence.2.1]
      apply Fin.ext
      rfl
    rw [atomEq]
    change pseudoSpatialCertified.spatialPointAt? (atomEquiv ⟨2, by decide⟩) = some P2
    simpa [sourcePoint, positions, P2, point] using actualSpatialPoint ⟨2, by decide⟩
  · change pseudoSpatialCertified.spatialPointAt?
      (rootFrames.actualLigandAtoms rootClosingSlot) = some P4
    have atomEq : rootFrames.actualLigandAtoms rootClosingSlot =
        atomEquiv ⟨4, by decide⟩ := by
      rw [correspondence.2.2.1]
      apply Fin.ext
      rfl
    rw [atomEq]
    change pseudoSpatialCertified.spatialPointAt? (atomEquiv ⟨4, by decide⟩) = some P4
    simpa [sourcePoint, positions, P4, point] using actualSpatialPoint ⟨4, by decide⟩
  · change pseudoSpatialCertified.spatialPointAt?
      (rootFrames.actualLigandAtoms rootHydrogenSlot) = some P5
    have atomEq : rootFrames.actualLigandAtoms rootHydrogenSlot =
        atomEquiv ⟨5, by decide⟩ := by
      rw [correspondence.2.2.2.1]
      apply Fin.ext
      rfl
    rw [atomEq]
    change pseudoSpatialCertified.spatialPointAt? (atomEquiv ⟨5, by decide⟩) = some P5
    simpa [sourcePoint, positions, P5, point] using actualSpatialPoint ⟨5, by decide⟩

private theorem actualLigandAtoms_injective : Function.Injective rootFrames.actualLigandAtoms := by
  intro i j equal
  apply rootFrames.detectedLigandPermutation.injective
  exact pseudoSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt_injective
    rootFrames.center equal

private theorem rootFluorineSlot_val :
    (rootFrames.actualLigandAtoms rootFluorineSlot).val = 1 := by
  rw [rootFluorineSlot_atom]
  rfl

private theorem rootArmSlot_val :
    (rootFrames.actualLigandAtoms rootArmSlot).val = 2 := by
  rw [rootArmSlot_atom]
  rfl

private theorem rootClosingSlot_val :
    (rootFrames.actualLigandAtoms rootClosingSlot).val = 4 := by
  rw [rootClosingSlot_atom]
  rfl

private theorem rootHydrogenSlot_val :
    (rootFrames.actualLigandAtoms rootHydrogenSlot).val = 5 := by
  rw [rootHydrogenSlot_atom]
  rfl

theorem actual_root_slots_distinct :
    rootFluorineSlot ≠ rootArmSlot ∧ rootFluorineSlot ≠ rootClosingSlot ∧
    rootFluorineSlot ≠ rootHydrogenSlot ∧ rootArmSlot ≠ rootClosingSlot ∧
    rootArmSlot ≠ rootHydrogenSlot ∧ rootClosingSlot ≠ rootHydrogenSlot := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have v := congrArg (fun s => (rootFrames.actualLigandAtoms s).val) h
    change (rootFrames.actualLigandAtoms rootFluorineSlot).val =
      (rootFrames.actualLigandAtoms rootArmSlot).val at v
    rw [rootFluorineSlot_val, rootArmSlot_val] at v
    norm_num at v
  · intro h
    have v := congrArg (fun s => (rootFrames.actualLigandAtoms s).val) h
    change (rootFrames.actualLigandAtoms rootFluorineSlot).val =
      (rootFrames.actualLigandAtoms rootClosingSlot).val at v
    rw [rootFluorineSlot_val, rootClosingSlot_val] at v
    norm_num at v
  · intro h
    have v := congrArg (fun s => (rootFrames.actualLigandAtoms s).val) h
    change (rootFrames.actualLigandAtoms rootFluorineSlot).val =
      (rootFrames.actualLigandAtoms rootHydrogenSlot).val at v
    rw [rootFluorineSlot_val, rootHydrogenSlot_val] at v
    norm_num at v
  · intro h
    have v := congrArg (fun s => (rootFrames.actualLigandAtoms s).val) h
    change (rootFrames.actualLigandAtoms rootArmSlot).val =
      (rootFrames.actualLigandAtoms rootClosingSlot).val at v
    rw [rootArmSlot_val, rootClosingSlot_val] at v
    norm_num at v
  · intro h
    have v := congrArg (fun s => (rootFrames.actualLigandAtoms s).val) h
    change (rootFrames.actualLigandAtoms rootArmSlot).val =
      (rootFrames.actualLigandAtoms rootHydrogenSlot).val at v
    rw [rootArmSlot_val, rootHydrogenSlot_val] at v
    norm_num at v
  · intro h
    have v := congrArg (fun s => (rootFrames.actualLigandAtoms s).val) h
    change (rootFrames.actualLigandAtoms rootClosingSlot).val =
      (rootFrames.actualLigandAtoms rootHydrogenSlot).val at v
    rw [rootClosingSlot_val, rootHydrogenSlot_val] at v
    norm_num at v

private theorem four_distinct_perm {a b c d : Fin 4}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    [a, b, c, d].Perm (List.finRange 4) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp_all <;> decide

def actualRootPriorityOrder : List (Fin 4) :=
  [rootFluorineSlot, rootArmSlot, rootClosingSlot, rootHydrogenSlot]

theorem actualRootPriorityOrder_perm :
    actualRootPriorityOrder.Perm (List.finRange 4) := by
  rcases actual_root_slots_distinct with ⟨hab, hac, had, hbc, hbd, hcd⟩
  exact four_distinct_perm hab hac had hbc hbd hcd

def actualRootPoints (slot : Fin 4) : CartesianPoint3 :=
  sourcePoint (atomEquiv.symm (rootFrames.actualLigandAtoms slot))

theorem actual_root_coordinates (slot : Fin 4) :
    rootFrames.actualCoordinates slot = some (actualRootPoints slot) := by
  change pseudoSpatialCertified.spatialPointAt? (rootFrames.actualLigandAtoms slot) = _
  rw [← atomEquiv.apply_symm_apply (rootFrames.actualLigandAtoms slot)]
  exact actualSpatialPoint _

private theorem actualRootPoints_on_order :
    actualRootPriorityOrder.map actualRootPoints = [P1, P2, P4, P5] := by
  have coordinates := actual_root_coordinate_slots
  have p1 : actualRootPoints rootFluorineSlot = P1 := by
    have indexEq : atomEquiv.symm
        (rootFrames.actualLigandAtoms rootFluorineSlot) = ⟨1, by decide⟩ := by
      rw [rootFluorineSlot_atom]
      apply Fin.ext
      rfl
    unfold actualRootPoints
    rw [indexEq]
    simp [sourcePoint, positions, P1, point]
  have p2 : actualRootPoints rootArmSlot = P2 := by
    have indexEq : atomEquiv.symm
        (rootFrames.actualLigandAtoms rootArmSlot) = ⟨2, by decide⟩ := by
      rw [rootArmSlot_atom]
      apply Fin.ext
      rfl
    unfold actualRootPoints
    rw [indexEq]
    simp [sourcePoint, positions, P2, point]
  have p4 : actualRootPoints rootClosingSlot = P4 := by
    have indexEq : atomEquiv.symm
        (rootFrames.actualLigandAtoms rootClosingSlot) = ⟨4, by decide⟩ := by
      rw [rootClosingSlot_atom]
      apply Fin.ext
      rfl
    unfold actualRootPoints
    rw [indexEq]
    simp [sourcePoint, positions, P4, point]
  have p5 : actualRootPoints rootHydrogenSlot = P5 := by
    have indexEq : atomEquiv.symm
        (rootFrames.actualLigandAtoms rootHydrogenSlot) = ⟨5, by decide⟩ := by
      rw [rootHydrogenSlot_atom]
      apply Fin.ext
      rfl
    unfold actualRootPoints
    rw [indexEq]
    simp [sourcePoint, positions, P5, point]
  simp [actualRootPriorityOrder, p1, p2, p4, p5]

theorem actual_root_geometric_order_is_S :
    RationalTetrahedralDescriptor (actualRootPriorityOrder.map actualRootPoints) RS.S := by
  rw [actualRootPoints_on_order]
  exact ⟨P1, P2, P4, P5, rfl, by rw [root_volume]; norm_num⟩

/-- The actual certified molecular graph contains the ring triangle through the root and the two
carbon ligands. This endpoint records the cyclic domain explicitly; no acyclicity premise is
being used in the runtime reconstruction. -/
theorem actual_fixture_contains_ring_triangle :
    ∃ a b c : pseudoSpatialCertified.Atom,
      a ≠ b ∧ b ≠ c ∧ c ≠ a ∧
      pseudoSpatialCertified.moleculeGraph.Adj a b ∧
      pseudoSpatialCertified.moleculeGraph.Adj b c ∧
      pseudoSpatialCertified.moleculeGraph.Adj c a := by
  refine ⟨atomEquiv 0, atomEquiv 2, atomEquiv 4, by decide, by decide, by decide,
    ?_, ?_, ?_⟩
  · exact (actualAdj 0 2).mpr ((adj_root 2).mpr (Or.inr (Or.inl rfl)))
  · exact (actualAdj 2 4).mpr ((adj_arm 4).mpr (Or.inr (Or.inr (Or.inl rfl))))
  · exact (actualAdj 4 0).mpr ((adj_closing 0).mpr (Or.inl rfl))

/-- The fixture's nonvacuous physical root facts, all on one actual graph/configuration/domain. -/
theorem actual_root_physical_nonvacuity :
    ActualGeneralRigidPhysicalDomain pseudoSpatialCertified physicalMolecule physicalCfg
      LocalizedCyclicPseudoPhysicalDomain.rootCenter ∧
    physicalEnantiomorphicPairCount physicalMolecule physicalCfg
      LocalizedCyclicPseudoPhysicalDomain.rootCenter = 1 ∧
    MultiCenterMolecule.PairwiseProperDistinguishable physicalMolecule physicalCfg
      LocalizedCyclicPseudoPhysicalDomain.rootCenter ∧
    (∃ a b c : pseudoSpatialCertified.Atom,
      a ≠ b ∧ b ≠ c ∧ c ≠ a ∧
      pseudoSpatialCertified.moleculeGraph.Adj a b ∧
      pseudoSpatialCertified.moleculeGraph.Adj b c ∧
      pseudoSpatialCertified.moleculeGraph.Adj c a) := by
  exact ⟨LocalizedCyclicPseudoPhysicalDomain.actual_physical_domain,
    actual_root_physical_pair_count, actual_root_pairwise_proper_distinguishable,
    actual_fixture_contains_ring_triangle⟩

end
end TetraStereo.OneCenter.LocalizedCyclicPseudoActualRootLetter

assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoActualRootLetter.actual_root_configuration_sign
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoActualRootLetter.actual_root_physical_pair_count
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoActualRootLetter.actual_root_pairwise_proper_distinguishable
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoActualRootLetter.actual_root_geometric_order_is_S
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoActualRootLetter.actual_fixture_contains_ring_triangle
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoActualRootLetter.actualRootPriorityOrder
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoActualRootLetter.actualRootPoints
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoActualRootLetter.actual_root_physical_nonvacuity
