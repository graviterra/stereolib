import TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleCompiler
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-! Kernel checks of actual retained comparison calls on the symmetric cyclic input.
These are local occurrence computations, with an empty auxiliary state. -/

namespace TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleExecution

open LocalizedChemicalRingCyclicExampleInput

theorem root_ordinary : ops.ordinary [] root =
    some ([0, 1, 2, 3], [some .gt, some .eq, some .gt]) := by
  rw [← LocalizedChemicalRingCyclicExampleCompiler.ordinary_eq]
  decide +kernel

theorem arm2_ordinary : ops.ordinary [] arm2 =
    some ([1, 0, 2, 3], [some .gt, some .gt, some .gt]) := by
  rw [← LocalizedChemicalRingCyclicExampleCompiler.ordinary_eq]
  decide +kernel

end TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleExecution

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleExecution.root_ordinary
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleExecution.arm2_ordinary
