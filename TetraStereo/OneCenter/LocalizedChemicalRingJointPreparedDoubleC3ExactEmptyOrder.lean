import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyPartition
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyOrder

open LocalizedMarkedRetainedOrdinaryRanking (keyOrder)

/-- Descending stable sorting of one strict maximum and three equal keys is determined by
that comparison matrix. No sort execution over the original keys is required. -/
theorem keyOrder_single_max {K : Type} [LinearOrder K] (key : Fin 4 → K) (pivot : Fin 4)
    (strict : ∀ i, i ≠ pivot → key i < key pivot)
    (tied : ∀ i j, i ≠ pivot → j ≠ pivot → key i = key j) :
    keyOrder key (List.finRange 4) =
      pivot :: (List.finRange 4).filter (fun i => i ≠ pivot) := by
  let code : Fin 4 → Nat := fun i => if i = pivot then 1 else 0
  have matrix : ∀ i j, key j ≤ key i ↔ code j ≤ code i := by
    intro i j
    by_cases hi : i = pivot
    · subst i
      by_cases hj : j = pivot
      · subst j
        simp
      · have less := strict j hj
        simp [code, hj, le_of_lt less]
    · by_cases hj : j = pivot
      · subst j
        have less := strict i hi
        simp [code, hi, not_le_of_gt less]
      · rw [tied i j hi hj]
        simp [code, hi, hj]
  have sortEq : keyOrder key (List.finRange 4) = keyOrder code (List.finRange 4) := by
    unfold keyOrder
    congr 1
    funext i j
    exact propext (matrix i j)
  rw [sortEq]
  unfold keyOrder
  dsimp only [code]
  fin_cases pivot <;> decide +kernel

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyOrder

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactEmptyOrder.keyOrder_single_max
