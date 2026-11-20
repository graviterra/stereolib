import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactLeftDescriptor
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRightFlip
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootState
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The two root auxiliary facts are derived before any root comparison is used. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFacts

open LocalizedChemicalRingDoubleC3Input
open LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier (input)
open LocalizedChemicalRingJointPreparedDoubleC3ExactLeftDescriptor (left_descriptor)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRightFlip (right_descriptor_flip)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootState (root_prepared_children_eq_local)
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedChemicalRingOrientationReadback (flipDescriptorBy flipDescriptor)
open LocalizedGenericMarkedRecalculation (Geometry structuralDepth factOf)

noncomputable section

def twoFacts : OccurrenceAuxState :=
  [factOf leftCenter (.chiral .R), factOf rightCenter (.chiral .S)]

theorem right_descriptor (depth : Nat) :
    preparedDescriptor? mol (jointOperations input mol) depth (inputGeometry input) [] [] rightCenter =
      some (.chiral .S) := by
  have exchange := right_descriptor_flip depth []
  have notOne : (-1 : ℝ) ≠ 1 := by norm_num
  simpa [left_descriptor, flipDescriptorBy, flipDescriptor, notOne, RS.swap] using exchange

abbrev rootUnder (geom : Geometry) :=
  childrenUnder mol (preparedFacts mol (jointOperations input mol) (structuralDepth mol root))
    geom [] root

theorem actual_root_facts : rootUnder (inputGeometry input) [] = twoFacts := by
  have depth : structuralDepth mol root = 23 + 2 := by decide +kernel
  change childrenUnder mol
    (preparedFacts mol (jointOperations input mol) (structuralDepth mol root))
    (inputGeometry input) [] root [] = twoFacts
  rw [depth, root_prepared_children_eq_local]
  dsimp only
  rw [left_descriptor, right_descriptor]
  rfl

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFacts

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFacts.right_descriptor
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFacts.actual_root_facts
