import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherCoveringPath
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitAllCalibration
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceStabilizerSuccess
import TetraStereo.OneCenter.LocalizedChemicalRingSelectedFactCompleteness
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
The second covering path gives an actual generated observation at center 26 for every
inherited reference, on original and reflected geometry. The selected raw descent,
adequate structural budget, actual calibration and history rigidity supply success.
No auxiliary label, successful ordering or agreement between different states is assumed.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherObservation

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceOrbitOtherCoveringPath LocalizedChemicalRingReferenceOrbitAllCalibration
open LocalizedChemicalRingInheritedRefusalCases LocalizedChemicalRingReferenceStabilizerSuccess
open LocalizedChemicalRingOrientationInduction (descriptorWith_mirror_none_iff)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedChemicalRingBoundaryWitnessExecution (snapshotWith)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedGenericMarkedRecalculation (structuralDepth mirror)

noncomputable section

def otherData : OccurrenceData certified mol otherCurrent otherNode :=
  Classical.choice (occurrenceData_exists certified mol structure_agreement admissible supported
    single_bonded otherCurrent otherNode other_reached rfl rfl)

/-- The actual inherited descriptor succeeds at the second covering query at every depth. -/
theorem other_descriptor_exists_at (mark : Fin 46) (depth : Nat) :
    ∃ value, LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations certified mol)
      depth (inputGeometry certified) [] (some mark.val) otherNode = some value := by
  exact LocalizedChemicalRingReferenceStabilizerSuccess.descriptor_exists certified mol
    structure_agreement admissible supported single_bonded cfg otherCurrent other_calibrated
    otherNode otherData (Classical.choice (other_tied_branch otherCurrent otherData)) depth mark
    ⟨0, constant_charge⟩ (fun e fixed _ => other_history_rigid e fixed)

/-- Reflection preserves existence of the actual mirror-paired descriptor. -/
theorem other_mirror_descriptor_exists_at (mark : Fin 46) (depth : Nat) :
    ∃ value, LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations certified mol)
      depth (mirror (inputGeometry certified)) [] (some mark.val) otherNode = some value := by
  cases observed : LocalizedChemicalRingInheritedFallback.descriptor? mol
      (sparseOperations certified mol) depth (mirror (inputGeometry certified)) []
      (some mark.val) otherNode with
  | none =>
      have refused : LocalizedChemicalRingInheritedFallback.descriptor? mol
          (sparseOperations certified mol) depth (inputGeometry certified) []
          (some mark.val) otherNode = none :=
        (descriptorWith_mirror_none_iff mol (sparseOperations certified mol)
          LocalizedChemicalRingInheritedFallback.rawStep? depth (inputGeometry certified)
          [] (some mark.val) otherNode).mp observed
      obtain ⟨value, computed⟩ := other_descriptor_exists_at mark depth
      rw [computed] at refused
      cases refused
  | some value => exact ⟨value, rfl⟩

/-- The actual selected arm emits a present center-26 observation for any original mark. -/
theorem other_snapshot_label_present_at (mark : Fin 46) :
    ((snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? certified mol
      (structuralDepth mol (canonicalCenterRoot 0)) (inputGeometry certified)
      (canonicalCenterRoot 0) mark.val).factAt? otherNode).map factLabel ≠ none := by
  intro absent
  have refused := LocalizedChemicalRingSelectedFactCompleteness.candidate_absence_refusal
    certified mol (structuralDepth mol (canonicalCenterRoot 0)) (inputGeometry certified)
    (canonicalCenterRoot 0) (nodeOf [0, 30]) otherNode mark.val
    other_selected_first_child other_raw_descent other_structural_budget absent
  obtain ⟨value, computed⟩ := other_descriptor_exists_at mark
    (structuralDepth mol (canonicalCenterRoot 0) + (canonicalCenterRoot 0).history.length -
      otherNode.history.length)
  rw [computed] at refused
  cases refused

/-- The observation is present in the mark's own reflected root snapshot as well. -/
theorem other_mirror_snapshot_label_present_at (mark : Fin 46) :
    ((snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? certified mol
      (structuralDepth mol (canonicalCenterRoot 0)) (mirror (inputGeometry certified))
      (canonicalCenterRoot 0) mark.val).factAt? otherNode).map factLabel ≠ none := by
  intro absent
  have refused := LocalizedChemicalRingSelectedFactCompleteness.candidate_absence_refusal
    certified mol (structuralDepth mol (canonicalCenterRoot 0)) (mirror (inputGeometry certified))
    (canonicalCenterRoot 0) (nodeOf [0, 30]) otherNode mark.val
    other_selected_first_child other_raw_descent other_structural_budget absent
  obtain ⟨value, computed⟩ := other_mirror_descriptor_exists_at mark
    (structuralDepth mol (canonicalCenterRoot 0) + (canonicalCenterRoot 0).history.length -
      otherNode.history.length)
  rw [computed] at refused
  cases refused

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherObservation

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherObservation.other_descriptor_exists_at
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherObservation.other_mirror_descriptor_exists_at
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherObservation.other_snapshot_label_present_at
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherObservation.other_mirror_snapshot_label_present_at
