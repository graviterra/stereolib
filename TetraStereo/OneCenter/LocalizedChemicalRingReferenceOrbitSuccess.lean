import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCalibration
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitStabilizer
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitBranch
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceStabilizerSuccess
import TetraStereo.OneCenter.LocalizedChemicalRingSelectedFactCompleteness
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
Actual inherited-reference descriptor success at the alternate occurrence in the
46-atom cyclic fixture. The actual reached occurrence, root-arm key tie, coordinate
calibration and trivial history/reference stabilizer are proved from this input.
No auxiliary labels, successful comparisons, selected references or output letters
are supplied. This proves success at this occurrence, not its descriptor's chemical
meaning or the full molecular report.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitSuccess

open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceOrbitStabilizer LocalizedChemicalRingReferenceOrbitBranch
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedGenericMarkedRecalculation (structuralDepth factOf)
open LocalizedChemicalRingBoundaryWitnessExecution (snapshotWith)
open LocalizedMarkedRetainedStateReader (factLabel)

noncomputable section
open scoped Classical

private theorem charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge graph :=
  ⟨0, constant_charge⟩

/-- A proved actual output at every call depth, including the budget used by its
ancestor's generated forest. No whole-state execution or desired value is assumed. -/
theorem shortcut_descriptor_exists (depth : Nat) :
    ∃ value, LocalizedChemicalRingInheritedFallback.descriptor? mol
      (sparseOperations certified mol) depth (inputGeometry certified) []
      (some reference.val) shortcutNode = some value := by
  let branch := Classical.choice (shortcut_tied_branch current shortcutData)
  exact LocalizedChemicalRingReferenceStabilizerSuccess.descriptor_exists certified mol
    structure_agreement admissible supported single_bonded cfg current calibrated
    shortcutNode shortcutData branch depth reference charge raw_shortcut_stabilizer

/-- The actual root snapshot selects this first child and visits the entire shortcut.
The generated descriptor at the exact remaining budget is emitted by that forest. -/
theorem shortcut_descriptor_emitted :
    ∃ value, LocalizedChemicalRingInheritedFallback.descriptor? mol
      (sparseOperations certified mol)
      (structuralDepth mol (canonicalCenterRoot 0) + (canonicalCenterRoot 0).history.length -
        shortcutNode.history.length)
      (inputGeometry certified) [] (some reference.val) shortcutNode = some value ∧
      factOf shortcutNode value ∈ snapshotWith LocalizedChemicalRingInheritedFallback.rawStep?
        certified mol (structuralDepth mol (canonicalCenterRoot 0)) (inputGeometry certified)
        (canonicalCenterRoot 0) reference.val := by
  obtain ⟨value, computed⟩ := shortcut_descriptor_exists
    (structuralDepth mol (canonicalCenterRoot 0) + (canonicalCenterRoot 0).history.length -
      shortcutNode.history.length)
  refine ⟨value, computed, ?_⟩
  exact LocalizedChemicalRingSelectedFactCompleteness.snapshot_contains
    LocalizedChemicalRingInheritedFallback.rawStep? certified mol
    (structuralDepth mol (canonicalCenterRoot 0)) (inputGeometry certified)
    (canonicalCenterRoot 0) (nodeOf [0, 28]) shortcutNode reference.val
    shortcut_selected_first_child shortcut_raw_descent shortcut_structural_budget value computed

/-- The actual optional observation at this full history is present. It cannot be
silently treated as an absent label by a root comparison using this generated snapshot. -/
theorem shortcut_snapshot_label_present :
    ((snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? certified mol
      (structuralDepth mol (canonicalCenterRoot 0)) (inputGeometry certified)
      (canonicalCenterRoot 0) reference.val).factAt? shortcutNode).map factLabel ≠ none := by
  intro absent
  have refused := LocalizedChemicalRingSelectedFactCompleteness.candidate_absence_refusal
    certified mol (structuralDepth mol (canonicalCenterRoot 0)) (inputGeometry certified)
    (canonicalCenterRoot 0) (nodeOf [0, 28]) shortcutNode reference.val
    shortcut_selected_first_child shortcut_raw_descent shortcut_structural_budget absent
  obtain ⟨value, computed⟩ := shortcut_descriptor_exists
    (structuralDepth mol (canonicalCenterRoot 0) + (canonicalCenterRoot 0).history.length -
      shortcutNode.history.length)
  rw [computed] at refused
  cases refused

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitSuccess

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitSuccess.shortcut_descriptor_exists

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitSuccess.shortcut_descriptor_emitted
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitSuccess.shortcut_snapshot_label_present
