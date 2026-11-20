import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactData
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactSparsePin
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactSingletonFrame
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactImmediateMark
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactMark5

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingDoubleC3Input
open LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier (input)
open LocalizedChemicalRingJointPreparedDoubleC3ExactCarrierFrame (frame)
open LocalizedChemicalRingJointPreparedDoubleC3ExactData
open LocalizedChemicalRingJointPreparedDoubleC3ExactC3Separation (left_boron_keys_equal)
open LocalizedChemicalRingJointPreparedDoubleC3ExactFirstSphere (left_boron_lt_oxygen)
open LocalizedChemicalRingJointPreparedDoubleC3ExactSparsePin (actual_sparse_mark5_6_before_7)
open LocalizedChemicalRingJointPreparedDoubleC3ExactSingletonFrame
open LocalizedChemicalRingJointPreparedDoubleC3ExactImmediateMark
open LocalizedChemicalRingJointPreparedExecution (keys generated)
open LocalizedChemicalRingJointMarkerFrameExecution (slotKeys)
open LocalizedChemicalRingJointMarkerRanking (RefinedKey jointBefore_eq_refined
  refined_compare_lt_iff refined_compare_eq_iff)
open LocalizedChemicalRingJointMarkerOperations (jointOperations jointBefore)
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedMarkedRetainedOrdinaryRanking (cmp_gt_iff)
open LocalizedMarkedRetainedStateReader
open LocalizedMarkedRetainedPromotedKey (ordinaryKey? referenceBit)
open LocalizedMarkedRetainedPromotedRanking (slot_valid)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseBefore)
open LocalizedChemicalRingJointMarkerSingleton (compareJoint_singleton_eq_sparse)
open LocalizedGenericMarkedRecalculation (Geometry)

noncomputable section

abbrev key5 : Fin 4 → RefinedKey := slotKeys input mol single_bonded center leftCenter data [] [(5 : Fin 25)]

theorem ordinary_1_2_tie :
    (input.compareLocalizedRerootCompoundThroughRule5 (execution.compounds 1)
      (execution.compounds 2)).ordering = .eq := by
  have empty (geom : Geometry) : generated input mol 0 geom leftCenter [] = [] :=
    childrenUnder_factsOfStep_zero (rawStepPrepared? (jointOperations input mol)) mol geom [] leftCenter []
  obtain ⟨tie12, _⟩ := left_boron_keys_equal center data 0 (fun _ => none) 1 2 3
    (reference_slot 1) (reference_slot 2) (reference_slot 3)
  have tie : slotKeys input mol single_bonded center leftCenter data [] [] 1 =
      slotKeys input mol single_bonded center leftCenter data [] [] 2 := by
    simpa only [keys, empty] using tie12
  have prior := congrArg (fun key : RefinedKey => (ofLex key).1) tie
  change execution.retainedKeys unit 1 = execution.retainedKeys unit 2 at prior
  have compared := execution.fullOrdering (rawStateDescriptorMap_tetrahedral input [])
    single_bonded unit rfl 1 2
  rw [prior, (completeLigandRule5Key_compare_eq_iff _ _).mpr rfl] at compared
  exact compared

private theorem ordinary_built (slot : Fin 4) :
    ordinaryKey? input data.target (rawStateView input [] data.target)
      (execution.frame.cursorAt slot) = some (execution.compounds slot) := by
  unfold ordinaryKey?
  rw [rawStateView_eq_molecularView]
  exact execution.compoundBuilt slot

theorem joint_mark5_1_before_2 :
    LocalizedChemicalRingJointMarkerKey.compareJointAt? input data.target
      (rawStateView input [] data.target) [(5 : Fin 25)] 26 54
      (execution.frame.cursorAt 1) (execution.frame.cursorAt 2) = some .gt := by
  apply compareJoint_gt_of_ordinary_tie_and_root_bits input data.target
    (rawStateView input [] data.target) (5 : Fin 25) 26 54 _ _
    (slot_valid input single_bonded [] data.target data.real unit rfl 1)
    (slot_valid input single_bonded [] data.target data.real unit rfl 2)
    (execution.compounds 1) (execution.compounds 2)
    (ordinary_built 1) (ordinary_built 2) ordinary_1_2_tie
  rw [execution_frame]
  simp [referenceBit, LocalizedChemicalRingJointPreparedDoubleC3ExactCarrierFrame.frame_atoms]

private theorem key_compare_of_sparse (i j : Fin 4)
    (sparse : sparseBefore input [] data.target (5 : Fin 25) 26 54 frame i j = some .gt) :
    compare (key5 i) (key5 j) = .gt := by
  have guarded := jointBefore_singleton_eq_sparseBefore input single_bonded [] data.target
    data.real unit rfl (5 : Fin 25) 26 54 i j
  rw [execution_frame] at guarded
  have actual := guarded.trans sparse
  have compiled := jointBefore_eq_refined input single_bonded [] data.target data.real unit rfl
    [(5 : Fin 25)] 26 54 i j
  rw [execution_frame] at compiled
  exact Option.some.inj (compiled.symm.trans actual)

theorem key5_2_lt_1 : key5 2 < key5 1 := by
  have marked := joint_mark5_1_before_2
  rw [execution_frame, compareJoint_singleton_eq_sparse] at marked
  have compared := key_compare_of_sparse 1 2 marked
  exact (cmp_gt_iff compare refined_compare_lt_iff refined_compare_eq_iff _ _).mp compared

theorem key5_3_lt_2 : key5 3 < key5 2 := by
  have sparse := actual_sparse_mark5_6_before_7
  rw [← data_target] at sparse
  have compared := key_compare_of_sparse 2 3 sparse
  exact (cmp_gt_iff compare refined_compare_lt_iff refined_compare_eq_iff _ _).mp compared

theorem key5_1_lt_0 : key5 1 < key5 0 :=
  left_boron_lt_oxygen center data [] [(5 : Fin 25)] 0 1 (reference_slot 0)
    (Or.inl (reference_slot 1))

/-- Exact generated-comparator strict order under the actual local reference5. -/
theorem mark5_chain : key5 3 < key5 2 ∧ key5 2 < key5 1 ∧ key5 1 < key5 0 :=
  ⟨key5_3_lt_2, key5_2_lt_1, key5_1_lt_0⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactMark5

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactMark5.ordinary_1_2_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactMark5.joint_mark5_1_before_2
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactMark5.key5_2_lt_1
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactMark5.key5_3_lt_2
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactMark5.key5_1_lt_0
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactMark5.mark5_chain
