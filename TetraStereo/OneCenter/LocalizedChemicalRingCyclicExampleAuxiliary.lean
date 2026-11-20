import TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleExecution
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-! An actual generated auxiliary descriptor on the cyclic molecule, at every recursion depth
and inherited reference. The strict ordinary comparison is kernel-checked from the input;
the computation neither supplies a descriptor state nor assumes a successful ranking. -/

namespace TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleAuxiliary

open LocalizedChemicalRingCyclicExampleInput LocalizedChemicalRingCyclicExampleExecution
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? readback? mirror)

theorem arm2_frame : frameAtoms? mol arm2 = some [0, 3, 4, 6] := by decide +kernel

theorem arm2_readback : readback? geom [3, 0, 4, 6] = some .R := by decide +kernel

theorem arm2_rawStep (geometry : Geometry) (ctx : Option Nat)
    (under : Nat → OccurrenceAuxState) :
    LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geometry [] ctx arm2 under =
      readback? geometry [3, 0, 4, 6] := by
  unfold LocalizedPhysicalMarkedDistantReference.rawStep?
  rw [arm2_frame]
  simp only [Option.bind_eq_bind, Option.bind_some, arm2_ordinary]
  rfl

theorem arm2_descriptor (depth : Nat) (ctx : Option Nat) :
    LocalizedPhysicalMarkedDistantEvaluator.descriptor? mol ops depth geom [] ctx arm2 =
      some (.chiral .R) := by
  unfold LocalizedPhysicalMarkedDistantEvaluator.descriptor?
    LocalizedPhysicalMarkedDistantEvaluator.descriptorWith?
    LocalizedPhysicalMarkedDistantEvaluator.rawWith?
  rw [arm2_rawStep, arm2_rawStep, LocalizedGenericMarkedRecalculation.readback_mirror,
    arm2_readback]
  rfl

end TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleAuxiliary

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleAuxiliary.arm2_rawStep
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCyclicExampleAuxiliary.arm2_descriptor
