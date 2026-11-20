import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactCarrierFrame
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactCachedEmptySparse
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-! One local sparse comparison after all empty-state detection/dependency tests have been
removed by theorem. No prepared recursion or dense marker table is evaluated. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactSparsePin

open LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier
open LocalizedChemicalRingJointPreparedDoubleC3ExactCarrierFrame (frame)
open LocalizedChemicalRingJointPreparedDoubleC3ExactCachedEmptySparse
open LocalizedMarkedRetainedSparsePromotedKey (sparseCompareAt?)
open LocalizedMarkedRetainedStateReader (rawStateView)

private theorem sparse_mark5_6_before_7 :
    compareAt (5 : Fin 25) 26 54 (frame.cursorAt 2) (frame.cursorAt 3) = some .gt := by
  unfold compareAt
  decide +kernel

/-- Actual strict marked order of the two unmarked boron arms, fixing reference atom5. -/
theorem actual_sparse_mark5_6_before_7 :
    sparseCompareAt? input target (rawStateView input [] target) (5 : Fin 25) 26 54
      (frame.cursorAt 2) (frame.cursorAt 3) = some .gt := by
  rw [← compareAt_eq target]
  exact sparse_mark5_6_before_7

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactSparsePin

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactSparsePin.actual_sparse_mark5_6_before_7
