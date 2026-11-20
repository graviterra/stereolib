import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3Pseudo
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactLocal
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactData
import TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransportExecution
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedGeometryFlip
import TetraStereo.OneCenter.LocalizedChemicalRingSemanticSymmetry
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual left/right local descriptor transport under the cage exchange. The proof uses
calibrated frame readback and empty descendants, without a global coordinate equality. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRightFlip
open CertifiedLocalizedCIPInput
open LocalizedChemicalRingDoubleC3Input
open LocalizedChemicalRingDoubleC3Domain
open LocalizedChemicalRingDoubleC3Physical
open LocalizedChemicalRingJointPreparedDoubleC3Pseudo
open LocalizedChemicalRingJointPreparedDoubleC3ExactDescendants
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingJointMarkerOperations
open LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingRelabel
open LocalizedChemicalRingOrientationReadback
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? mirror)

noncomputable section

abbrev sigma : Nat → Nat := relabelOf input (detectedExchange : Equiv.Perm input.Atom)

/-- Exposes only the underlying permutation of the accepted transported automorphism. -/
theorem exchange_coe : (detectedExchange : Equiv.Perm input.Atom) = exchange := by
  have transport {m n : MultiCenterMolecule input.Atom} (same : m = n) (e : m.Aut) :
      ((Eq.mp (congrArg (fun m : MultiCenterMolecule input.Atom => ↥m.Aut) same) e : n.Aut) :
        Equiv.Perm input.Atom) = e := by
    cases same
    rfl
  rw [detectedExchange, transport frameChange_spec]
  rfl

theorem image_left : mapNode sigma leftCenter = rightCenter := by
  simp only [sigma, exchange_coe]
  rfl

/-- Entire actual right local descriptor, at transported accumulated context. -/
theorem right_descriptor_flip (depth : Nat) (M : List Nat) :
    preparedDescriptor? mol (jointOperations input mol) depth (inputGeometry input) []
        (M.map sigma) rightCenter =
      flipDescriptorBy (-1)
        (preparedDescriptor? mol (jointOperations input mol) depth (inputGeometry input) []
          M leftCenter) := by
  let e : input.moleculeGraph.Aut :=
    ⟨detectedExchange, MultiCenterMolecule.Aut.mem_molAut input.detectedMultiCenterMolecule detectedExchange⟩
  have sym := LocalizedChemicalRingSemanticSymmetry.structuralSymmetry_of_aut input mol
    (structure_agreement true) admissible supported detectedExchange
  have transported := LocalizedChemicalRingJointOperationTransportExecution.actual_preparedDescriptor_map
    input mol (structure_agreement true) admissible supported single_bonded e sym
    depth (inputGeometry input) M leftCenter LocalizedChemicalRingDoubleC3Refusal.left_reached
  change preparedDescriptor? mol (jointOperations input mol) depth (inputGeometry input) []
      (M.map sigma) (mapNode sigma leftCenter) = _ at transported
  rw [image_left] at transported
  rw [transported]
  apply LocalizedChemicalRingJointPreparedGeometryFlip.preparedDescriptor_flip mol
    (jointOperations input mol) (-1) (pullback sigma (inputGeometry input))
    (inputGeometry input) depth leftCenter [4, 5, 6, 7] raw_frames.2.1
  · intro L subset
    have read := LocalizedChemicalRingOrientationReadback.readback_pullback_frame input mol
      (structure_agreement true) admissible supported single_bonded cfg detectedExchange calibrated
      LocalizedChemicalRingJointPreparedDoubleC3ExactData.center leftCenter rfl
      LocalizedChemicalRingDoubleC3Refusal.left_reached [4, 5, 6, 7] raw_frames.2.1 L subset
    simpa only [detected_exchange_negative] using read
  · intro L
    rw [left_prepared_children_empty, left_prepared_children_empty]
  · intro L
    rw [left_prepared_children_empty, left_prepared_children_empty]

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRightFlip

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRightFlip.exchange_coe
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRightFlip.image_left
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRightFlip.right_descriptor_flip
