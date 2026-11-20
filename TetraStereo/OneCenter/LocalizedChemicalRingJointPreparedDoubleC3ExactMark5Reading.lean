import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactMark5
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactGeometry
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactLocalExecution
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactMark5Reading

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingDoubleC3Input
open LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier (input)
open LocalizedChemicalRingJointPreparedDoubleC3ExactData
open LocalizedChemicalRingJointPreparedDoubleC3ExactMark5
open LocalizedChemicalRingJointPreparedDoubleC3ExactGeometry
open LocalizedChemicalRingJointPreparedDoubleC3ExactLocalExecution
open LocalizedChemicalRingJointPreparedDoubleC3ExactDescendants (left_prepared_children_empty)
open LocalizedChemicalRingJointMarkerFrameExecution (contextOrder?_eq)
open LocalizedChemicalRingJointMarkerRanking (refined_compare_lt_iff refined_compare_eq_iff)
open LocalizedChemicalRingJointMarkerOperations (jointOperations contextOrder?)
open LocalizedMarkedRetainedOrdinaryRanking (keyOrder adjacentBy cmp_gt_iff)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingMultiMarkRecursion (markedReadingJoint?)
open LocalizedGenericMarkedRecalculation (readback? mirror readback_mirror)

noncomputable section

theorem sort_key5 : keyOrder key5 (List.finRange 4) = List.finRange 4 := by
  have h20 := lt_trans key5_2_lt_1 key5_1_lt_0
  have h31 := lt_trans key5_3_lt_2 key5_2_lt_1
  have h30 := lt_trans h31 key5_1_lt_0
  have sorted : (List.finRange 4).Pairwise (fun a b => key5 b ≤ key5 a) := by
    change ([0, 1, 2, 3] : List (Fin 4)).Pairwise (fun a b => key5 b ≤ key5 a)
    simp [List.pairwise_cons, le_of_lt key5_1_lt_0, le_of_lt key5_2_lt_1,
      le_of_lt key5_3_lt_2, le_of_lt h20, le_of_lt h31, le_of_lt h30]
  exact sorted.insertionSort_eq

theorem adjacent_key5 : adjacentBy (fun i j => some (compare (key5 i) (key5 j)))
    (List.finRange 4) = [some .gt, some .gt, some .gt] := by
  have c01 := (cmp_gt_iff compare refined_compare_lt_iff refined_compare_eq_iff _ _).mpr key5_1_lt_0
  have c12 := (cmp_gt_iff compare refined_compare_lt_iff refined_compare_eq_iff _ _).mpr key5_2_lt_1
  have c23 := (cmp_gt_iff compare refined_compare_lt_iff refined_compare_eq_iff _ _).mpr key5_3_lt_2
  change [some (compare (key5 0) (key5 1)), some (compare (key5 1) (key5 2)),
    some (compare (key5 2) (key5 3))] = _
  rw [c01, c12, c23]

theorem context_order_mark5 : contextOrder? input mol [] leftCenter [5] =
    some ([0, 1, 2, 3], [some .gt, some .gt, some .gt]) := by
  have actual := contextOrder?_eq input mol single_bonded center leftCenter data [] [(5 : Fin 25)]
  change contextOrder? input mol [] leftCenter [5] =
    some ((keyOrder key5 (List.finRange 4)).map data.read.index,
      adjacentBy (fun i j => some (compare (key5 i) (key5 j)))
        (keyOrder key5 (List.finRange 4))) at actual
  have indexFun : data.read.index = fun i => i.val := funext data_index
  simp only [sort_key5, adjacent_key5, indexFun] at actual
  exact actual

/-- An actual local selected fallback reads R; no auxiliary label has been supplied. -/
theorem marked5_reading : markedReadingJoint? mol (jointOperations input mol)
    (inputGeometry input) [] leftCenter [5] 5 = some .R := by
  have actual := marked_reading_of_strict_context_order input mol (inputGeometry input) []
    leftCenter [5] 5 [4, 5, 6, 7] [0, 1, 2, 3] [some .gt, some .gt, some .gt]
    raw_frames.2.1 context_order_mark5 (by decide)
  change markedReadingJoint? mol (jointOperations input mol) (inputGeometry input) []
    leftCenter [5] 5 = readback? (inputGeometry input) [4, 5, 6, 7] at actual
  exact actual.trans left_canonical_reading

theorem marked5_mirror_reading : markedReadingJoint? mol (jointOperations input mol)
    (mirror (inputGeometry input)) [] leftCenter [5] 5 = some .S := by
  have actual := marked_reading_of_strict_context_order input mol (mirror (inputGeometry input)) []
    leftCenter [5] 5 [4, 5, 6, 7] [0, 1, 2, 3] [some .gt, some .gt, some .gt]
    raw_frames.2.1 context_order_mark5 (by decide)
  change markedReadingJoint? mol (jointOperations input mol) (mirror (inputGeometry input)) []
    leftCenter [5] 5 = readback? (mirror (inputGeometry input)) [4, 5, 6, 7] at actual
  rw [readback_mirror, left_canonical_reading] at actual
  exact actual

/-- The prepared evaluator's own selected-reference5 fallback reads R at every recursion depth. -/
theorem prepared_fallback5 (depth : Nat) :
    evaluateFallback? mol (jointOperations input mol) (inputGeometry input) [] leftCenter []
      (childrenUnder mol (preparedFacts mol (jointOperations input mol) depth)
        (inputGeometry input) [] leftCenter) 5 = some .R := by
  unfold evaluateFallback?
  rw [left_prepared_children_empty]
  change markedReadingJoint? mol (jointOperations input mol) (inputGeometry input) []
    leftCenter [5] 5 = some .R
  exact marked5_reading


theorem prepared_fallback5_mirror (depth : Nat) :
    evaluateFallback? mol (jointOperations input mol) (mirror (inputGeometry input)) [] leftCenter []
      (childrenUnder mol (preparedFacts mol (jointOperations input mol) depth)
        (mirror (inputGeometry input)) [] leftCenter) 5 = some .S := by
  unfold evaluateFallback?
  rw [left_prepared_children_empty]
  change markedReadingJoint? mol (jointOperations input mol) (mirror (inputGeometry input)) []
    leftCenter [5] 5 = some .S
  exact marked5_mirror_reading

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactMark5Reading

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactMark5Reading.sort_key5
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactMark5Reading.adjacent_key5
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactMark5Reading.context_order_mark5
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactMark5Reading.marked5_reading
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactMark5Reading.marked5_mirror_reading
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactMark5Reading.prepared_fallback5

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactMark5Reading.prepared_fallback5_mirror
