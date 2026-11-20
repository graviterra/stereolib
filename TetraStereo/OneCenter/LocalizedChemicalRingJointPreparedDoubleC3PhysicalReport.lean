import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedReport
import TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Domain
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The full physical classification/report theorem is inhabited by the 25-atom cyclic
input with dependent non-root centers. The report has precisely three detected entries and
its root is lowercase, derived from independent physical pair count one. No auxiliary label
or output is supplied and no whole-state execution is used. The specific r/s letter is not asserted. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3PhysicalReport

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingDoubleC3Input LocalizedChemicalRingDoubleC3Domain
open LocalizedChemicalRingJointPreparedReport

noncomputable section

theorem report_indices : (analyze input mol).map Prod.fst = [0, 3, 14] := by
  rw [analyze_center_indices]
  unfold canonicalTetrahedralCenters
  simp only [List.map_map, Function.comp_def, List.attach_map_val]
  change (graph.tetrahedralCenterSet.sort (· ≤ ·)).map Fin.val = [0, 3, 14]
  rw [detected_inventory]
  have sorted : ({0, 3, 14} : Finset (Fin 25)).sort (· ≤ ·) = [0, 3, 14] := by
    rw [Finset.sort_insert (r := (· ≤ ·))
      (by intro b _; exact Nat.zero_le b.val) (by decide)]
    rw [Finset.sort_insert (r := (· ≤ ·))
      (by intro b h; have same : b = (14 : Fin 25) := by simpa using h
          subst b; decide) (by decide), Finset.sort_singleton]
  rw [sorted]
  rfl

theorem report_length : (analyze input mol).length = 3 := by
  rw [analyze_length]
  change graph.tetrahedralCenterSet.card = 3
  rw [detected_inventory]
  decide +kernel

/-- Concrete cyclic nonvacuity of the assembled physical theorem on the actual report. -/
theorem root_report_lowercase : ∃ raw,
    (0, some (.pseudoasymmetric raw)) ∈ analyze input mol := by
  obtain ⟨descriptor, member, physical⟩ := detected_entry_physical input mol
    (structure_agreement true) admissible supported single_bonded ⟨0, constant_charge⟩
    cfg calibrated detectedRoot proper_distinct
  have lower : descriptor.IsLowercase := physical.mpr mirror_pair_count
  cases descriptor with
  | chiral raw => exact False.elim lower
  | pseudoasymmetric raw => exact ⟨raw, member⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3PhysicalReport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3PhysicalReport.report_indices
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3PhysicalReport.report_length
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3PhysicalReport.root_report_lowercase
