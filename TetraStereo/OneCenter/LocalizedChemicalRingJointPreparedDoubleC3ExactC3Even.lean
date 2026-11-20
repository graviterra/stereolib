import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactData
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactC3Covariance
import TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Domain
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPhysicalTransport
import TetraStereo.OneCenter.LocalizedChemicalRingSemanticSymmetry
import TetraStereo.KernelOnly

set_option autoImplicit false
/-! Even C3 symmetry equates the actual selected local fallbacks at arbitrary depth
and on both geometry sides. No descriptor value is assumed. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactC3Even
open CertifiedLocalizedCIPInput
open LocalizedChemicalRingDoubleC3Input
open LocalizedChemicalRingDoubleC3Physical
open LocalizedChemicalRingDoubleC3Domain (cfg calibrated)
open LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier (input)
open LocalizedChemicalRingJointPreparedDoubleC3ExactData (center data reference_slot)
open LocalizedChemicalRingJointPreparedDoubleC3ExactC3Covariance
open LocalizedChemicalRingResidualThreeCycleRefusal (slotAction referenceAt_action center_fixed local_even_of_cube)
open LocalizedChemicalRingInheritedRefusalCases (referenceAt observedGeometry)
open LocalizedChemicalRingJointPreparedExecution (fallback)
open LocalizedChemicalRingPhysicalSense (relabelOf)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)

noncomputable section
abbrev rho : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 2 3

theorem rotation_slot_action : slotAction input mol actualLeftRotation center leftCenter data = rho := by
  have fixed := center_fixed input mol actualLeftRotation center leftCenter
    LocalizedChemicalRingDoubleC3Refusal.left_reached rfl left_rotation_fixes_history
  apply Equiv.ext
  intro i
  apply data.ligandOf.injective
  apply input.detectedMultiCenterMolecule.ligandAtomAt_injective center
  change referenceAt input mol center leftCenter data
      (slotAction input mol actualLeftRotation center leftCenter data i) =
    referenceAt input mol center leftCenter data (rho i)
  rw [referenceAt_action input mol actualLeftRotation center leftCenter data fixed]
  rw [reference_slot, reference_slot]
  fin_cases i <;> rfl

theorem rotation_even : relativeSign input.detectedMultiCenterMolecule cfg actualLeftRotation center = 1 := by
  apply local_even_of_cube input mol actualLeftRotation center leftCenter data
    LocalizedChemicalRingDoubleC3Refusal.left_reached rfl left_rotation_fixes_history cfg
  rw [rotation_slot_action]
  decide +kernel

theorem fallback_rotation (depth : Nat) (reflected : Bool) (i : Fin 4) :
    fallback input mol center leftCenter data depth (observedGeometry input reflected) [] (rho i) =
      fallback input mol center leftCenter data depth (observedGeometry input reflected) [] i := by
  let e : input.moleculeGraph.Aut :=
    ⟨actualLeftRotation, MultiCenterMolecule.Aut.mem_molAut input.detectedMultiCenterMolecule actualLeftRotation⟩
  have sym := LocalizedChemicalRingSemanticSymmetry.structuralSymmetry_of_aut input mol
    (structure_agreement true) admissible supported actualLeftRotation
  apply LocalizedChemicalRingJointPreparedPhysicalTransport.actual_fallback_eq_of_even_slot
    input mol (structure_agreement true) admissible supported single_bonded cfg e actualLeftRotation rfl sym
    calibrated center leftCenter rfl LocalizedChemicalRingDoubleC3Refusal.left_reached data reflected
    (left_descendant_geometry_agreement _ _) depth [] left_rotation_fixes_history
    (by simp) i (rho i) _ rotation_even
  change relabelOf input (actualLeftRotation : Equiv.Perm input.Atom)
      (referenceAt input mol center leftCenter data i).val =
    (referenceAt input mol center leftCenter data (rho i)).val
  rw [LocalizedChemicalRingPhysicalSense.relabelOf_val, reference_slot, reference_slot]
  fin_cases i <;> rfl

theorem fallback2_eq1 (depth : Nat) (reflected : Bool) :
    fallback input mol center leftCenter data depth (observedGeometry input reflected) [] 2 =
      fallback input mol center leftCenter data depth (observedGeometry input reflected) [] 1 :=
  fallback_rotation depth reflected 1

theorem fallback3_eq2 (depth : Nat) (reflected : Bool) :
    fallback input mol center leftCenter data depth (observedGeometry input reflected) [] 3 =
      fallback input mol center leftCenter data depth (observedGeometry input reflected) [] 2 :=
  fallback_rotation depth reflected 2
end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactC3Even

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactC3Even.rotation_slot_action
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactC3Even.rotation_even
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactC3Even.fallback_rotation
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactC3Even.fallback2_eq1
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactC3Even.fallback3_eq2
