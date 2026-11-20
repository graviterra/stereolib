import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitAnyReferenceObservation
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
The same actual covering query succeeds under reflected geometry for every inherited
reference, and its label is present in that reference's reflected root snapshot.
Reflection preserves refusal of the mirror-paired descriptor constructor. No equality
between original and reflected snapshots, or between labels for different marks, is used.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitMirrorObservation

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCoveringPath
open LocalizedChemicalRingReferenceOrbitBranch LocalizedChemicalRingReferenceOrbitAnyReferenceObservation
open LocalizedChemicalRingOrientationInduction (descriptorWith_mirror_none_iff)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedChemicalRingBoundaryWitnessExecution (snapshotWith)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedGenericMarkedRecalculation (structuralDepth mirror)

noncomputable section

/-- Actual reflected descriptor success is derived from the accepted original execution. -/
theorem covering_mirror_descriptor_exists_at (mark : Fin 46) (depth : Nat) :
    ∃ value, LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations certified mol)
      depth (mirror (inputGeometry certified)) [] (some mark.val) coveringNode = some value := by
  cases observed : LocalizedChemicalRingInheritedFallback.descriptor? mol
      (sparseOperations certified mol) depth (mirror (inputGeometry certified)) []
      (some mark.val) coveringNode with
  | none =>
      have refused : LocalizedChemicalRingInheritedFallback.descriptor? mol
          (sparseOperations certified mol) depth (inputGeometry certified) []
          (some mark.val) coveringNode = none :=
        (descriptorWith_mirror_none_iff mol (sparseOperations certified mol)
          LocalizedChemicalRingInheritedFallback.rawStep? depth (inputGeometry certified)
          [] (some mark.val) coveringNode).mp observed
      obtain ⟨value, computed⟩ := covering_descriptor_exists_at mark depth
      rw [computed] at refused
      cases refused
  | some value => exact ⟨value, rfl⟩

/-- The actual selected path supplies a present observation in each reflected snapshot. -/
theorem covering_mirror_snapshot_label_present_at (mark : Fin 46) :
    ((snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? certified mol
      (structuralDepth mol (canonicalCenterRoot 0)) (mirror (inputGeometry certified))
      (canonicalCenterRoot 0) mark.val).factAt? coveringNode).map factLabel ≠ none := by
  intro absent
  have refused := LocalizedChemicalRingSelectedFactCompleteness.candidate_absence_refusal
    certified mol (structuralDepth mol (canonicalCenterRoot 0)) (mirror (inputGeometry certified))
    (canonicalCenterRoot 0) (nodeOf [0, 28]) coveringNode mark.val
    shortcut_selected_first_child covering_raw_descent covering_structural_budget absent
  obtain ⟨value, computed⟩ := covering_mirror_descriptor_exists_at mark
    (structuralDepth mol (canonicalCenterRoot 0) + (canonicalCenterRoot 0).history.length -
      coveringNode.history.length)
  rw [computed] at refused
  cases refused

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitMirrorObservation

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitMirrorObservation.covering_mirror_descriptor_exists_at
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitMirrorObservation.covering_mirror_snapshot_label_present_at
