import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherExchangeSign
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitArmSymmetry
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringSymmetry
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitKeySeparation
import TetraStereo.OneCenter.LocalizedChemicalRingComponentOrientationSupport
import TetraStereo.OneCenter.LocalizedChemicalRingRankedCorrectionTransport
import TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

/-!
Independent proper distinguishability of all four root branches of the 46-atom graph.
Every O18 exchange reverses center 26, even when it also exchanges the O16 pair.
Once the O18 pair is fixed, an O16 exchange reverses center 2. Both centers are reached
from each root branch after deleting the root, so a proper branch transport fixes every
root ligand. The result holds for every physical configuration and uses no runtime data.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootPhysicalDistinguishability

open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceOrbitAllCalibration LocalizedChemicalRingReferenceOrbitKeySeparation
open LocalizedChemicalRingReferenceOrbitArmSymmetry LocalizedChemicalRingReferenceOrbitCoveringSymmetry
open LocalizedChemicalRingReferenceOrbitOtherExchangeSign LocalizedChemicalRingReferenceOrbitStabilizer
open LocalizedChemicalRingComponentOrientationSupport LocalizedChemicalRingRankedCorrectionTransport
open LocalizedPhysicalMarkedParityCompleteness RootedTetrahedralBranchSymmetry
open RetainedCoherentSymmetry LocalizedCyclicMatchedReadingPhysicalTransport

noncomputable section

private theorem isotope16 (a : Fin 46) :
    graph.atomMass a = graph.atomMass (28 : Fin 46) → a = 28 ∨ a = 29 := by
  fin_cases a <;> decide +kernel

private theorem isotope18 (a : Fin 46) :
    graph.atomMass a = graph.atomMass (30 : Fin 46) → a = 30 ∨ a = 31 := by
  fin_cases a <;> decide +kernel

private theorem armSwap_other_center : physical.centerPerm physicalAut otherCurrent = otherCurrent :=
  Subtype.ext rfl

private theorem armSwap_other_proper (configuration : physical.Configuration) :
    relativeSign physical configuration physicalAut otherCurrent = 1 := by
  apply relativeSign_of_frame_fixed physical configuration physicalAut otherCurrent rfl
  have finite : ∀ a : Fin 46, graph.Adj 26 a → physicalAut.val a = a := by
    decide +kernel
  exact finite

/-- No inherited-reference fixation is needed for the negative center-26 sign. -/
theorem any_other_exchange_negative (configuration : physical.Configuration) (e : physical.Aut)
    (entry : e.val (30 : Fin 46) = (31 : Fin 46)) :
    physical.centerPerm e otherCurrent = otherCurrent ∧
      relativeSign physical configuration e otherCurrent = -1 := by
  let g : graph.Aut := ⟨e.val, e.2.1⟩
  rcases isotope16 (e.val (28 : Fin 46)) (MoleculeGraph.Aut.atomMass_eq (m := graph) g 28) with
    fixed28 | moved28
  · exact other_exchange_negative configuration e 28 (Or.inl rfl) fixed28 entry
  · have moved29 : e.val (29 : Fin 46) = (28 : Fin 46) := by
      rcases isotope16 (e.val (29 : Fin 46)) (MoleculeGraph.Aut.atomMass_eq (m := graph) g 29) with
        moved29 | fixed29
      · exact moved29
      · have same := e.val.injective (moved28.trans fixed29.symm)
        exact False.elim ((by decide : (28 : Fin 46) ≠ 29) same)
    have productFix : (e * physicalAut).val (28 : Fin 46) = (28 : Fin 46) := moved29
    have productEntry : (e * physicalAut).val (30 : Fin 46) = (31 : Fin 46) := entry
    obtain ⟨productCenter, productSign⟩ := other_exchange_negative configuration
      (e * physicalAut) 28 (Or.inl rfl) productFix productEntry
    refine ⟨?_, ?_⟩
    · simpa only [centerPerm_mul_apply, armSwap_other_center] using productCenter
    · rw [relativeSign_mul, armSwap_other_center, armSwap_other_proper, mul_one] at productSign
      exact productSign

private theorem root_neighbors (a : Fin 46) :
    graph.Adj 0 a → a = 28 ∨ a = 29 ∨ a = 30 ∨ a = 31 := by
  fin_cases a <;> decide +kernel

/-- Proper signs at just two physical anchors force the complete root frame fixed. -/
theorem root_frame_fixed_of_proper_anchors (configuration : physical.Configuration)
    (e : physical.Aut) (rootFixed : e.val (0 : Fin 46) = (0 : Fin 46))
    (proper2 : relativeSign physical configuration e current = 1)
    (proper26 : relativeSign physical configuration e otherCurrent = 1) :
    physical.centerPerm e rootCenter = rootCenter ∧ physical.ligandPermAt e rootCenter = 1 := by
  let g : graph.Aut := ⟨e.val, e.2.1⟩
  have fixed30 : e.val (30 : Fin 46) = (30 : Fin 46) := by
    rcases isotope18 (e.val (30 : Fin 46)) (MoleculeGraph.Aut.atomMass_eq (m := graph) g 30) with
      fixed | moved
    · exact fixed
    · have negative := (any_other_exchange_negative configuration e moved).2
      rw [proper26] at negative
      norm_num at negative
  have fixed31 : e.val (31 : Fin 46) = (31 : Fin 46) := by
    apply fixed_of_signature graph g [30] 31
    · intro a member
      have same : a = (30 : Fin 46) := List.mem_singleton.mp member
      simpa only [same] using fixed30
    · unfold SignatureUnique
      decide +kernel
  have fixed28 : e.val (28 : Fin 46) = (28 : Fin 46) := by
    rcases isotope16 (e.val (28 : Fin 46)) (MoleculeGraph.Aut.atomMass_eq (m := graph) g 28) with
      fixed | moved
    · exact fixed
    · have negative := (reference_exchange_current_negative configuration e rootFixed moved fixed30).2
      rw [proper2] at negative
      norm_num at negative
  have fixed29 : e.val (29 : Fin 46) = (29 : Fin 46) := by
    apply fixed_of_signature graph g [28] 29
    · intro a member
      have same : a = (28 : Fin 46) := List.mem_singleton.mp member
      simpa only [same] using fixed28
    · unfold SignatureUnique
      decide +kernel
  apply frame_fixed physical e rootCenter rootFixed
  intro a adjacent
  rcases root_neighbors a adjacent with rfl | rfl | rfl | rfl
  · exact fixed28
  · exact fixed29
  · exact fixed30
  · exact fixed31

private abbrev deleted := residualGraph graph [(0 : Fin 46)]

private theorem neighbor_reaches26 (a : Fin 46) (neighbor : graph.Adj 0 a) :
    deleted.Reachable a 26 := by
  have from27 : deleted.Reachable 27 26 :=
    (show deleted.Adj 27 26 from ⟨by decide, by decide, by decide +kernel⟩).reachable
  rcases root_neighbors a neighbor with rfl | rfl | rfl | rfl
  · exact (show deleted.Adj 28 32 from ⟨by decide, by decide, by decide +kernel⟩).reachable.trans
      ((show deleted.Adj 32 27 from ⟨by decide, by decide, by decide +kernel⟩).reachable.trans from27)
  · exact (show deleted.Adj 29 33 from ⟨by decide, by decide, by decide +kernel⟩).reachable.trans
      ((show deleted.Adj 33 27 from ⟨by decide, by decide, by decide +kernel⟩).reachable.trans from27)
  · exact (show deleted.Adj 30 34 from ⟨by decide, by decide, by decide +kernel⟩).reachable.trans
      (show deleted.Adj 34 26 from ⟨by decide, by decide, by decide +kernel⟩).reachable
  · exact (show deleted.Adj 31 35 from ⟨by decide, by decide, by decide +kernel⟩).reachable.trans
      (show deleted.Adj 35 26 from ⟨by decide, by decide, by decide +kernel⟩).reachable

/-- Both anchor centers lie in every source branch, with the root deleted throughout. -/
theorem branch_reaches_anchors (i : Fin 4) :
    LigandBranchReaches physical rootCenter i current.1 ∧
      LigandBranchReaches physical rootCenter i otherCurrent.1 := by
  have outside : physical.ligandAtomAt rootCenter i ∉ [rootCenter.1] := by
    simpa only [List.mem_singleton] using ligandAtomAt_ne_center physical rootCenter i
  have reach26 := neighbor_reaches26 (physical.ligandAtomAt rootCenter i)
    (physical.ligandAtomAt_adj rootCenter i)
  have reach2 : deleted.Reachable (physical.ligandAtomAt rootCenter i) 2 :=
    reach26.trans ((show deleted.Adj 26 1 from ⟨by decide, by decide, by decide +kernel⟩).reachable.trans
      (show deleted.Adj 1 2 from ⟨by decide, by decide, by decide +kernel⟩).reachable)
  exact ⟨inComponent_implies_ligandBranchReaches physical rootCenter i current.1 ⟨outside, reach2⟩,
    inComponent_implies_ligandBranchReaches physical rootCenter i otherCurrent.1 ⟨outside, reach26⟩⟩

/-- Independent physical root distinction, including overlapping cyclic branches. -/
theorem root_proper_distinct (configuration : physical.Configuration) :
    physical.PairwiseProperDistinguishable configuration rootCenter := by
  intro i j different transport
  obtain ⟨e, rootFixed, sent, signs⟩ := transport
  have proper2 : relativeSign physical configuration e current = 1 := by
    apply (relativeSign_eq_iff physical configuration e current 1).mpr
    exact signs current (branch_reaches_anchors i).1
  have proper26 : relativeSign physical configuration e otherCurrent = 1 := by
    apply (relativeSign_eq_iff physical configuration e otherCurrent 1).mpr
    exact signs otherCurrent (branch_reaches_anchors i).2
  have frame := (root_frame_fixed_of_proper_anchors configuration e
    (congrArg Subtype.val rootFixed) proper2 proper26).2
  exact different (by simpa only [frame, Equiv.Perm.one_apply] using sent)

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootPhysicalDistinguishability

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootPhysicalDistinguishability.any_other_exchange_negative
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootPhysicalDistinguishability.root_frame_fixed_of_proper_anchors
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootPhysicalDistinguishability.branch_reaches_anchors
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootPhysicalDistinguishability.root_proper_distinct
