import TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleMarkedCompiler
import TetraStereo.OneCenter.LocalizedChemicalRingCyclicExamplePhysical
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

/-! Finite verification of the actual distant-reference assignment at the cyclic root.
The computational representation is proved equal to both actual operation callbacks.
No input descriptor state is supplied. -/

namespace TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleRoot

open LocalizedChemicalRingCyclicExampleInput

theorem root_lowercase :
    LocalizedPhysicalMarkedDistantEvaluator.assignCenter? mol ops geom 0 = some (.pseudoasymmetric .r) ∨
    LocalizedPhysicalMarkedDistantEvaluator.assignCenter? mol ops geom 0 = some (.pseudoasymmetric .s) := by
  rw [← LocalizedChemicalRingCyclicExampleMarkedCompiler.operations_eq]
  decide +kernel

theorem root_letter :
    LocalizedPhysicalMarkedDistantEvaluator.assignCenter? mol ops geom 0 =
      some (.pseudoasymmetric .s) := by
  rw [← LocalizedChemicalRingCyclicExampleMarkedCompiler.operations_eq]
  decide +kernel

theorem whole_report : LocalizedPhysicalMarkedDistantEvaluator.assign mol ops geom =
    [(0, .pseudoasymmetric .s), (2, .pseudoasymmetric .s), (4, .pseudoasymmetric .s)] := by
  rw [← LocalizedChemicalRingCyclicExampleMarkedCompiler.operations_eq]
  decide +kernel

end TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleRoot

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleRoot.root_lowercase
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleRoot.root_letter
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleRoot.whole_report
