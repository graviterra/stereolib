import TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Geometry
import TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 1024

/-! Exact rational-coordinate readings of explicit local enumerations.
These are geometry facts only; generated priority orders are separate obligations. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactGeometry

open LocalizedChemicalRingDoubleC3Input
open LocalizedGenericMarkedRecalculation (readback?)
open LocalizedChemicalRingPhysicalSense (inputGeometry)

theorem left_canonical_reading :
    readback? (inputGeometry (certified true)) [4, 5, 6, 7] = some .R := by decide +kernel

theorem right_canonical_reading :
    readback? (inputGeometry (certified true)) [15, 16, 17, 18] = some .S := by decide +kernel

theorem root_left_before_right_reading :
    readback? (inputGeometry (certified true)) [2, 4, 15, 1] = some .S := by decide +kernel

theorem root_right_before_left_reading :
    readback? (inputGeometry (certified true)) [2, 15, 4, 1] = some .R := by decide +kernel

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactGeometry

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactGeometry.left_canonical_reading
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactGeometry.right_canonical_reading
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactGeometry.root_left_before_right_reading
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactGeometry.root_right_before_left_reading
