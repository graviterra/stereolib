import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringPath
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-!
The accepted covering history alone fixes the entire molecular graph: its atom 34
identifies reference 30 by its isotope/adjacency signature. Descriptor success and
snapshot-label presence consequently hold for every actual inherited reference atom.
No reference eligibility, readback agreement between different marks, or report is asserted.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitAnyReferenceObservation

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceOrbitCoveringPath LocalizedChemicalRingReferenceOrbitBranch
open LocalizedChemicalRingReferenceOrbitStabilizer LocalizedChemicalRingReferenceStabilizerSuccess
open LocalizedChemicalRingPhysicalSense (inputGeometry relabelOf relabelOf_val)
open LocalizedChemicalRingBoundaryWitnessExecution (snapshotWith)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedGenericMarkedRecalculation (structuralDepth)

noncomputable section

/-- The full covering history is a rigidity certificate without an additional marked atom. -/
theorem covering_history_rigid (e : physical.Aut)
    (historyFixed : ∀ value ∈ coveringNode.history, relabelOf certified e.val value = value) :
    e = 1 := by
  have fixed : ∀ a ∈ coveringPath, e.val a = a := by
    intro a present
    have inHistory : a.val ∈ coveringNode.history :=
      List.mem_reverse.mpr (List.mem_map.mpr ⟨a, present, rfl⟩)
    have observed := historyFixed a.val inHistory
    rw [relabelOf_val] at observed
    exact Fin.ext observed
  have referenceFixed : e.val reference = reference := by
    apply fixed_of_signature graph ⟨e.val, e.2.1⟩ [34] 30
    · intro a present
      have same : a = (34 : Fin 46) := List.mem_singleton.mp present
      subst a
      exact fixed _ (by decide +kernel)
    · unfold SignatureUnique
      decide +kernel
  exact raw_covering_stabilizer e historyFixed referenceFixed

/-- Actual candidate descriptor success at every depth and every inherited reference. -/
theorem covering_descriptor_exists_at (mark : Fin 46) (depth : Nat) :
    ∃ value, LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations certified mol)
      depth (inputGeometry certified) [] (some mark.val) coveringNode = some value := by
  exact LocalizedChemicalRingReferenceStabilizerSuccess.descriptor_exists certified mol
    structure_agreement admissible supported single_bonded cfg current calibrated coveringNode
    coveringData (Classical.choice covering_tied_branch) depth mark ⟨0, constant_charge⟩
    (fun e fixed _ => covering_history_rigid e fixed)

/-- The same selected raw path emits a present observation in each marked root snapshot.
Different marks may still produce different labels; only their presence is established. -/
theorem covering_snapshot_label_present_at (mark : Fin 46) :
    ((snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? certified mol
      (structuralDepth mol (canonicalCenterRoot 0)) (inputGeometry certified)
      (canonicalCenterRoot 0) mark.val).factAt? coveringNode).map factLabel ≠ none := by
  intro absent
  have refused := LocalizedChemicalRingSelectedFactCompleteness.candidate_absence_refusal
    certified mol (structuralDepth mol (canonicalCenterRoot 0)) (inputGeometry certified)
    (canonicalCenterRoot 0) (nodeOf [0, 28]) coveringNode mark.val
    shortcut_selected_first_child covering_raw_descent covering_structural_budget absent
  obtain ⟨value, computed⟩ := covering_descriptor_exists_at mark
    (structuralDepth mol (canonicalCenterRoot 0) + (canonicalCenterRoot 0).history.length -
      coveringNode.history.length)
  rw [computed] at refused
  cases refused

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitAnyReferenceObservation

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitAnyReferenceObservation.covering_history_rigid
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitAnyReferenceObservation.covering_descriptor_exists_at
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitAnyReferenceObservation.covering_snapshot_label_present_at
