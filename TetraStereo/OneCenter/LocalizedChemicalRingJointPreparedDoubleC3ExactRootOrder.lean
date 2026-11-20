import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootData
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFirstSphere
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootOrderPin
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactGeometry
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootOrder

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingDoubleC3Input
open LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier (input)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootData
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootOrderPin (twoFacts actual_root_O_before)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootFirstSphere
open LocalizedChemicalRingJointMarkerFrameExecution (slotKeys contextOrder?_eq)
open LocalizedChemicalRingJointMarkerOperations (contextOrder?)
open LocalizedMarkedRetainedOrdinaryRanking (rawStateBefore_eq_keys rawStateKeys keyOrder adjacentBy cmp_gt_iff)
open LocalizedChemicalRingJointMarkerRanking (RefinedKey refined_compare_lt_iff refined_compare_eq_iff)
open LocalizedMarkedRetainedStateReader (rawStateDescriptorMap_tetrahedral)

noncomputable section

abbrev key : Fin 4 → RefinedKey := slotKeys input mol single_bonded center root data twoFacts []

theorem key_0_lt_3 : key 0 < key 3 := by
  apply actual_key_lt_of_atomic_number_lt root center data twoFacts [] 0 3
  rw [reference_slot, reference_slot]
  decide

theorem key_2_lt_1 : key 2 < key 1 := by
  apply actual_key_lt_of_atomic_number_lt root center data twoFacts [] 2 1
  rw [reference_slot, reference_slot]
  decide

theorem key_3_lt_2 : key 3 < key 2 := by
  have actual := actual_root_O_before
  rw [← data_target] at actual
  have compiled := rawStateBefore_eq_keys input single_bonded twoFacts data.target data.real unit rfl 2 3
  rw [execution_frame twoFacts] at compiled
  have comparison : compare
      (rawStateKeys input single_bonded twoFacts data.target data.real unit rfl 2)
      (rawStateKeys input single_bonded twoFacts data.target data.real unit rfl 3) = .gt :=
    Option.some.inj (compiled.symm.trans actual)
  have lower := (completeLigandRule5Key_compare_gt_iff _ _).mp comparison
  change Prod.Lex (· < ·) (· < ·) _ _
  exact Prod.Lex.left _ _ lower

theorem sort_key : keyOrder key (List.finRange 4) = [1, 2, 3, 0] := by
  let code : Fin 4 → Nat := ![0, 3, 2, 1]
  have h02 := lt_trans key_0_lt_3 key_3_lt_2
  have h31 := lt_trans key_3_lt_2 key_2_lt_1
  have h01 := lt_trans h02 key_2_lt_1
  have matrix : ∀ i j, key j ≤ key i ↔ code j ≤ code i := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [code, le_of_lt key_0_lt_3, le_of_lt key_3_lt_2, le_of_lt key_2_lt_1,
        le_of_lt h02, le_of_lt h31, le_of_lt h01, not_le_of_gt key_0_lt_3,
        not_le_of_gt key_3_lt_2, not_le_of_gt key_2_lt_1, not_le_of_gt h02,
        not_le_of_gt h31, not_le_of_gt h01]
  have same : keyOrder key (List.finRange 4) = keyOrder code (List.finRange 4) := by
    unfold keyOrder
    congr 1
    funext i j
    exact propext (matrix i j)
  rw [same]
  decide +kernel

theorem adjacent_key : adjacentBy (fun i j => some (compare (key i) (key j)))
    [1, 2, 3, 0] = [some .gt, some .gt, some .gt] := by
  have c12 := (cmp_gt_iff compare refined_compare_lt_iff refined_compare_eq_iff _ _).mpr key_2_lt_1
  have c23 := (cmp_gt_iff compare refined_compare_lt_iff refined_compare_eq_iff _ _).mpr key_3_lt_2
  have c30 := (cmp_gt_iff compare refined_compare_lt_iff refined_compare_eq_iff _ _).mpr key_0_lt_3
  change [some (compare (key 1) (key 2)), some (compare (key 2) (key 3)),
    some (compare (key 3) (key 0))] = _
  rw [c12, c23, c30]


/-- Actual raw root ordering under the explicit two-fact state, in raw frame positions. -/
theorem context_order_twoFacts : contextOrder? input mol twoFacts root [] =
    some ([1, 2, 3, 0], [some .gt, some .gt, some .gt]) := by
  have actual := contextOrder?_eq input mol single_bonded center root data twoFacts []
  change contextOrder? input mol twoFacts root [] =
    some ((keyOrder key (List.finRange 4)).map data.read.index,
      adjacentBy (fun i j => some (compare (key i) (key j)))
        (keyOrder key (List.finRange 4))) at actual
  have indexFun : data.read.index = fun i => i.val := funext data_index
  simpa only [sort_key, adjacent_key, indexFun, List.map_cons, List.map_nil] using actual

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootOrder

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootOrder.key_0_lt_3
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootOrder.key_2_lt_1
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootOrder.key_3_lt_2
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootOrder.sort_key
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootOrder.adjacent_key

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootOrder.context_order_twoFacts
