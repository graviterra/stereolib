import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelPhysicalReport
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3PhysicalReport
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Concrete cyclic nonvacuity of the independent recursive source model and actual report.
The same 25-atom, three-detected-center input inhabits the full source-model existence theorem.
Its root has a lowercase descriptor in both that unique model and the actual report, derived
from physical pair count one. No auxiliary labels, successful comparisons or output are supplied.
The choice between r and s is left to the uniquely specified source equations, not asserted here.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3SourceModel

open LocalizedChemicalRingDoubleC3Input LocalizedChemicalRingDoubleC3Domain
open LocalizedChemicalRingJointPreparedSourceModel
open LocalizedChemicalRingJointPreparedSourceModelExistence
open LocalizedChemicalRingJointPreparedSourceModelPhysicalReport
open LocalizedChemicalRingJointPreparedReport
open LocalizedChemicalRingPhysicalSense (inputGeometry)

noncomputable section

/-- The cyclic input, including its dependent non-root centers, has exactly one source model. -/
theorem unique_source_model :
    ∃! candidate : Profile input mol, SourceModel input mol single_bonded candidate :=
  existsUnique_sourceModel input mol (structure_agreement true) admissible supported single_bonded

/-- Every solution of the independent equations gives the actual cyclic root's lowercase
descriptor. Existence of that solution is supplied by `unique_source_model`, not assumed globally. -/
theorem root_source_and_report {candidate : Profile input mol}
    (model : SourceModel input mol single_bonded candidate) :
    ∃ raw,
      candidate (inputGeometry input) []
        (finalQuery input mol (structure_agreement true) detectedRoot) =
          some (.pseudoasymmetric raw) ∧
      (0, some (.pseudoasymmetric raw)) ∈ analyze input mol := by
  obtain ⟨descriptor, source, member, physical⟩ := sourceModel_detected_entry input mol
    (structure_agreement true) admissible supported single_bonded ⟨0, constant_charge⟩
    cfg calibrated model detectedRoot proper_distinct
  have lower : descriptor.IsLowercase := physical.mpr mirror_pair_count
  cases descriptor with
  | chiral raw => exact False.elim lower
  | pseudoasymmetric raw => exact ⟨raw, source, member⟩

/-- A concrete end-to-end instance: unique independent recursive meaning, exact three-entry
detected inventory, and a generated pseudoasymmetric cyclic root in the actual report. -/
theorem cyclic_source_report :
    ∃ candidate : Profile input mol,
      SourceModel input mol single_bonded candidate ∧
      (∀ other : Profile input mol, SourceModel input mol single_bonded other → other = candidate) ∧
      (analyze input mol).map Prod.fst = [0, 3, 14] ∧
      ∃ raw,
        candidate (inputGeometry input) []
          (finalQuery input mol (structure_agreement true) detectedRoot) =
            some (.pseudoasymmetric raw) ∧
        (0, some (.pseudoasymmetric raw)) ∈ analyze input mol := by
  obtain ⟨candidate, model, unique⟩ := unique_source_model
  exact ⟨candidate, model, unique,
    LocalizedChemicalRingJointPreparedDoubleC3PhysicalReport.report_indices,
    root_source_and_report model⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3SourceModel

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3SourceModel.unique_source_model
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3SourceModel.root_source_and_report
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3SourceModel.cyclic_source_report
