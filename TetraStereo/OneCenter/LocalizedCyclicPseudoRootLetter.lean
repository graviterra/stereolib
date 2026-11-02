import TetraStereo.OneCenter.LocalizedCyclicPseudoGeneratedLabels
import TetraStereo.OneCenter.PhysicalEnantiomorphicPairCountReindexing
import TetraStereo.OneCenter.LocalizedActualUniqueNearestRule5Direction
import TetraStereo.OneCenter.LocalizedPseudoasymmetricClassification
import TetraStereo.KernelOnly
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

/-!
# Geometric classification support for the cyclic pseudoasymmetry candidate

The two ring carbons tie on their one-step constitutional keys. Their derived geometric
letters are `R` at atom 2 and `S` at atom 4. The generic reference-stage sign calculation
compares the same supplied chiral label under different reference stages; it is not a
comparison of the actual competing ligand readings. The coordinate order `F, C2, C4, H` is the canonical
root order and has raw letter `S`; the swapped carbon order has raw letter `R`. Exactly one
physical enantiomorphic pair exists, the pair of those two carbons, so the classification of
raw `S` is lowercase `s`.

This is the classification of those derived facts. It does not execute `referenceState` on
the nine-atom carrier: generated labels, the actual full comparison, and its runtime pair
count remain unproved here. It does not close the general ring theorem. `pseudoCfg` remains
the separate canonical-frame calibration.
-/

namespace TetraStereo.OneCenter.LocalizedCyclicPseudoRootLetter

open TetraStereo.OneCenter
open CartesianPoint3
open CertifiedLocalizedCIPInput
open LocalizedCyclicPseudoGeneratedLabels
open LocalizedCyclicPseudoInputWitness
open LocalizedCyclicPseudoSpatialWitness
open RootedTetrahedralBranchSymmetry

private def rootSlotPerm : Equiv.Perm (Fin 4) := Equiv.swap 1 2

private theorem mirror_root_fixed :
    canon.centerPerm canonMirror rootCenter = rootCenter :=
  (centerPerm_eq_iff canon canonMirror rootCenter).mpr rfl

private theorem mirror_root_perm :
    canon.ligandPermAt canonMirror rootCenter = rootSlotPerm := by
  ext index
  apply congrArg Fin.val
  apply canon.ligandAtomAt_injective rootCenter
  have transported := canon.ligandAtomAt_ligandPermAt (e := canonMirror) (c := rootCenter) index
  rw [mirror_root_fixed] at transported
  rw [transported]
  fin_cases index <;>
    simp [canonMirror, mirrorFun, rootSlotPerm, Equiv.swap_apply_def, root_ligands]

private theorem identity_slot (automorphism : canon.Aut) (identity : automorphism = 1)
    (slot : Fin 4) : canon.ligandPermAt automorphism rootCenter slot = slot := by
  rw [identity, canon.ligandPermAt_one]
  simp [Equiv.Perm.one_apply]

private theorem not_enantiomorphic_slot (i j : Fin 4) (idNe : i ≠ j)
    (mirrorNe : rootSlotPerm i ≠ j) :
    ¬ Enantiomorphic canon pseudoCfg rootCenter i j := by
  intro enantiomorphic
  rcases enantiomorphic with ⟨_, ⟨automorphism, _, sends, _⟩, _⟩
  rcases canon_automorphism_dichotomy automorphism with identity | mirrored
  · rw [identity_slot automorphism identity i] at sends
    exact idNe sends
  · rw [mirrored, mirror_root_perm] at sends
    exact mirrorNe sends

theorem root_enantiomorphic_iff (i j : Fin 4) :
    Enantiomorphic canon pseudoCfg rootCenter i j ↔
      (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) := by
  fin_cases i
  · fin_cases j
    · exact iff_of_false (fun enantiomorphic => enantiomorphic.1 rfl) (by decide)
    · exact iff_of_false (not_enantiomorphic_slot 0 1 (by decide) (by decide)) (by decide)
    · exact iff_of_false (not_enantiomorphic_slot 0 2 (by decide) (by decide)) (by decide)
    · exact iff_of_false (not_enantiomorphic_slot 0 3 (by decide) (by decide)) (by decide)
  · fin_cases j
    · exact iff_of_false (not_enantiomorphic_slot 1 0 (by decide) (by decide)) (by decide)
    · exact iff_of_false (fun enantiomorphic => enantiomorphic.1 rfl) (by decide)
    · exact iff_of_true enantiomorphic_ring_carbons (by decide)
    · exact iff_of_false (not_enantiomorphic_slot 1 3 (by decide) (by decide)) (by decide)
  · fin_cases j
    · exact iff_of_false (not_enantiomorphic_slot 2 0 (by decide) (by decide)) (by decide)
    · exact iff_of_true
        (enantiomorphic_symm canon pseudoCfg rootCenter enantiomorphic_ring_carbons) (by decide)
    · exact iff_of_false (fun enantiomorphic => enantiomorphic.1 rfl) (by decide)
    · exact iff_of_false (not_enantiomorphic_slot 2 3 (by decide) (by decide)) (by decide)
  · fin_cases j
    · exact iff_of_false (not_enantiomorphic_slot 3 0 (by decide) (by decide)) (by decide)
    · exact iff_of_false (not_enantiomorphic_slot 3 1 (by decide) (by decide)) (by decide)
    · exact iff_of_false (not_enantiomorphic_slot 3 2 (by decide) (by decide)) (by decide)
    · exact iff_of_false (fun enantiomorphic => enantiomorphic.1 rfl) (by decide)

theorem root_physical_pair_count :
    physicalEnantiomorphicPairCount canon pseudoCfg rootCenter = 1 := by
  rw [physicalEnantiomorphicPairCount_eq_one_iff]
  refine ⟨1, 2, by decide, enantiomorphic_ring_carbons, ?_⟩
  intro otherFirst otherSecond _different enantiomorphic
  rcases (root_enantiomorphic_iff otherFirst otherSecond).1 enantiomorphic with pair | pair
  · exact Or.inl pair
  · exact Or.inr pair

theorem orientedVolume_swap_middle (a b c d : CartesianPoint3) :
    orientedVolume a c b d = -orientedVolume a b c d := by
  simp only [orientedVolume]
  ring

theorem root_raw_S :
    descriptorOfOrientedVolume? (orientedVolume P1 P2 P4 P5) = some RS.S := by
  rw [descriptorOfOrientedVolume?_eq_some_S_iff, root_volume]
  norm_num

theorem root_swapped_raw_R :
    descriptorOfOrientedVolume? (orientedVolume P1 P4 P2 P5) = some RS.R := by
  rw [descriptorOfOrientedVolume?_eq_some_R_iff, orientedVolume_swap_middle P1 P2 P4 P5,
    root_volume]
  norm_num

theorem derived_R_reading_gt :
    compareLocalizedCumulativeRule45Priority
      (localizedCumulativeRule45Priority (localizedRule5StageFor none RS.R)
        (some (.chiral RS.R)))
      (localizedCumulativeRule45Priority (localizedRule5StageFor none RS.S)
        (some (.chiral RS.R))) = Ordering.gt := by
  rw [LocalizedActualUniqueNearestRule5Direction.comparePriority_stageFor_R_S_chiral_sign]
  decide

theorem derived_S_reading_lt :
    compareLocalizedCumulativeRule45Priority
      (localizedCumulativeRule45Priority (localizedRule5StageFor none RS.R)
        (some (.chiral RS.S)))
      (localizedCumulativeRule45Priority (localizedRule5StageFor none RS.S)
        (some (.chiral RS.S))) = Ordering.lt := by
  rw [LocalizedActualUniqueNearestRule5Direction.comparePriority_stageFor_R_S_chiral_sign]
  decide

theorem root_lowercase :
    classifyTetrahedralRSPseudo RS.S
      (physicalEnantiomorphicPairCount canon pseudoCfg rootCenter) =
    LocalizedTetrahedralRSPseudoDescriptor.pseudoasymmetric PseudoRS.s := by
  rw [root_physical_pair_count]
  simp [classifyTetrahedralRSPseudo, pseudoRSOfRS]

theorem root_derived_letter :
    OfficialRuleMajorKey.compare rootCarbon2Key rootCarbon4Key = Ordering.eq ∧
    OfficialRuleMajorKey.compare rootFluorineKey rootCarbon2Key = Ordering.gt ∧
    OfficialRuleMajorKey.compare rootCarbon4Key rootHydrogenKey = Ordering.gt ∧
    descriptorOfOrientedVolume? (orientedVolume P3 P4 P0 P6) = some RS.R ∧
    descriptorOfOrientedVolume? (orientedVolume P8 P2 P0 P7) = some RS.S ∧
    canon.ligandAtomAt rootCenter 1 = 2 ∧
    canon.ligandAtomAt rootCenter 2 = 4 ∧
    Enantiomorphic canon pseudoCfg rootCenter 1 2 ∧
    physicalEnantiomorphicPairCount canon pseudoCfg rootCenter = 1 ∧
    descriptorOfOrientedVolume? (orientedVolume P1 P2 P4 P5) = some RS.S ∧
    classifyTetrahedralRSPseudo RS.S 1 =
      LocalizedTetrahedralRSPseudoDescriptor.pseudoasymmetric PseudoRS.s := by
  refine ⟨root_carbon_constitutional_tie, root_constitutional_shell.1,
    root_constitutional_shell.2.2.2.1, arm_descriptor.2, closing_descriptor.2,
    root_ligands.2.1, root_ligands.2.2.1, enantiomorphic_ring_carbons,
    root_physical_pair_count, root_raw_S, ?_⟩
  simp [classifyTetrahedralRSPseudo, pseudoRSOfRS]

end TetraStereo.OneCenter.LocalizedCyclicPseudoRootLetter

assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoRootLetter.root_enantiomorphic_iff
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoRootLetter.root_physical_pair_count
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoRootLetter.root_raw_S
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoRootLetter.root_swapped_raw_R
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoRootLetter.derived_R_reading_gt
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoRootLetter.derived_S_reading_lt
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoRootLetter.root_lowercase
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoRootLetter.root_derived_letter
