import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactData
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactUnmarkedOrder

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingDoubleC3Input
open LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier (input)
open LocalizedChemicalRingJointPreparedDoubleC3ExactData
open LocalizedChemicalRingJointPreparedDoubleC3ExactC3Separation (left_boron_keys_equal)
open LocalizedChemicalRingJointPreparedDoubleC3ExactFirstSphere (left_boron_lt_oxygen)
open LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyOrder (keyOrder_single_max)
open LocalizedChemicalRingJointPreparedExecution (keys generated)
open LocalizedChemicalRingJointMarkerFrameExecution (slotKeys contextOrder?_eq)
open LocalizedChemicalRingJointMarkerRanking (RefinedKey refined_compare_lt_iff refined_compare_eq_iff)
open LocalizedChemicalRingJointMarkerOperations (jointOperations contextOrder?)
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedMarkedRetainedOrdinaryRanking (keyOrder adjacentBy cmp_gt_iff)
open LocalizedGenericMarkedRecalculation (Geometry)

noncomputable section

abbrev key0 : Fin 4 → RefinedKey := slotKeys input mol single_bonded center leftCenter data [] []

theorem key0_boron_ties : key0 1 = key0 2 ∧ key0 2 = key0 3 := by
  have empty (geom : Geometry) : generated input mol 0 geom leftCenter [] = [] :=
    childrenUnder_factsOfStep_zero (rawStepPrepared? (jointOperations input mol)) mol geom [] leftCenter []
  have actual := left_boron_keys_equal center data 0 (fun _ => none) 1 2 3
    (reference_slot 1) (reference_slot 2) (reference_slot 3)
  simpa only [keys, empty] using actual

theorem key0_boron_lt_oxygen (i : Fin 4) (different : i ≠ 0) : key0 i < key0 0 := by
  apply left_boron_lt_oxygen center data [] [] 0 i (reference_slot 0)
  fin_cases i
  · exact False.elim (different rfl)
  · exact Or.inl (reference_slot 1)
  · exact Or.inr (Or.inl (reference_slot 2))
  · exact Or.inr (Or.inr (reference_slot 3))

theorem sort_key0 : keyOrder key0 (List.finRange 4) = List.finRange 4 := by
  obtain ⟨tie12, tie23⟩ := key0_boron_ties
  have tied (i j : Fin 4) (hi : i ≠ 0) (hj : j ≠ 0) : key0 i = key0 j := by
    fin_cases i <;> fin_cases j <;> simp_all
  have actual := keyOrder_single_max key0 0 key0_boron_lt_oxygen tied
  have tail : (List.finRange 4).filter (fun i => i ≠ (0 : Fin 4)) = [1, 2, 3] := by rfl
  rw [tail] at actual
  exact actual

theorem adjacent_key0 : adjacentBy (fun i j => some (compare (key0 i) (key0 j)))
    (List.finRange 4) = [some .gt, some .eq, some .eq] := by
  have c01 := (cmp_gt_iff compare refined_compare_lt_iff refined_compare_eq_iff _ _).mpr
    (key0_boron_lt_oxygen 1 (by decide))
  have c12 := (refined_compare_eq_iff _ _).mpr key0_boron_ties.1
  have c23 := (refined_compare_eq_iff _ _).mpr key0_boron_ties.2
  change [some (compare (key0 0) (key0 1)), some (compare (key0 1) (key0 2)),
    some (compare (key0 2) (key0 3))] = _
  rw [c01, c12, c23]

/-- Exact actual unmarked local partition; all comparison outcomes are derived. -/
theorem context_order_nil : contextOrder? input mol [] leftCenter [] =
    some ([0, 1, 2, 3], [some .gt, some .eq, some .eq]) := by
  have actual := contextOrder?_eq input mol single_bonded center leftCenter data [] []
  change contextOrder? input mol [] leftCenter [] =
    some ((keyOrder key0 (List.finRange 4)).map data.read.index,
      adjacentBy (fun i j => some (compare (key0 i) (key0 j)))
        (keyOrder key0 (List.finRange 4))) at actual
  have indexFun : data.read.index = fun i => i.val := funext data_index
  simp only [sort_key0, adjacent_key0, indexFun] at actual
  exact actual

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactUnmarkedOrder

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactUnmarkedOrder.key0_boron_ties
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactUnmarkedOrder.key0_boron_lt_oxygen
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactUnmarkedOrder.sort_key0
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactUnmarkedOrder.adjacent_key0
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactUnmarkedOrder.context_order_nil
