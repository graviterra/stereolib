import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootKeyCovariance
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactLocal
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The actual prepared keys at the DoubleC3 left occurrence are invariant under its
threefold molecular rotation. Descendant geometry agreement follows from absent frames. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactC3Covariance

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingDoubleC3Input LocalizedChemicalRingDoubleC3Physical
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt)
open LocalizedChemicalRingJointPreparedExecution (keys)
open LocalizedChemicalRingJointPreparedRootKeyCovariance (actual_slot_key_action)
open LocalizedChemicalRingSenseTransport (AgreeOn)
open LocalizedChemicalRingPhysicalSense (relabelOf)
open LocalizedChemicalRingRelabel (pullback)
open LocalizedMarkedTerminalReferenceScope (StrictDescendant)
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms?)

noncomputable section

/-- The actual spatial input uses the same graph rotation. -/
def actualLeftRotation : (certified true).detectedMultiCenterMolecule.Aut :=
  (certified true).moleculeGraph.detectedMultiCenterAutOfGraphAut leftGraphRotation

/-- No geometry can affect a strict-descendant reading of the left auxiliary occurrence. -/
theorem left_descendant_geometry_agreement (first second : Geometry) :
    AgreeOn (StrictDescendant mol leftCenter) mol first second := by
  intro node descent atoms frame
  rw [LocalizedChemicalRingDoubleC3Refusal.left_descendants_no_frames node descent] at frame
  cases frame

/-- The threefold graph rotation fixes the complete raw history of this occurrence. -/
theorem left_rotation_fixes_history (value : Nat) (member : value ∈ leftCenter.history) :
    relabelOf (certified true)
      (actualLeftRotation : Equiv.Perm (certified true).Atom) value = value := by
  simp only [leftCenter, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

/-- The actual generated same-context keys are constant along the physical C3 slot action.
No ordinary-key correspondence, generated label or successful comparison is assumed. -/
theorem left_actual_keys_rotation
    (c : (certified true).detectedMultiCenterMolecule.Center)
    (data : OccurrenceData (certified true) mol c leftCenter)
    (depth : Nat) (geom : Geometry) :
    ∃ p : Equiv.Perm (Fin 4),
      (∀ i, referenceAt (certified true) mol c leftCenter data (p i) =
        (actualLeftRotation : Equiv.Perm (certified true).Atom)
          (referenceAt (certified true) mol c leftCenter data i)) ∧
      ∀ i, keys (certified true) mol single_bonded c leftCenter data depth geom [] (p i) =
        keys (certified true) mol single_bonded c leftCenter data depth geom [] i :=
  actual_slot_key_action (certified true) mol (structure_agreement true) admissible supported
    single_bonded actualLeftRotation c leftCenter data
    LocalizedChemicalRingDoubleC3Refusal.left_reached left_rotation_fixes_history []
    (by simp) depth geom (left_descendant_geometry_agreement _ _)

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactC3Covariance

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactC3Covariance.left_descendant_geometry_agreement
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactC3Covariance.left_rotation_fixes_history
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactC3Covariance.left_actual_keys_rotation

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactC3Covariance.actualLeftRotation
