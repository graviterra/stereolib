import TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationCage
import TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCurrentCageReport
import TetraStereo.OneCenter.LocalizedChemicalRingAllRootCancellationReport
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Same-input final cancellation-report contrast. Both reports enumerate the actual detected
centers and preserve operational failure versus completed refusal. CURRENT's cancellation
report is tied to its actual report by the checked all-root cancellation theorem. The frozen
single-current report generates its own auxiliary profile independently. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationReport

open LocalizedHiddenParityMarkedProbe
open LocalizedRecursiveAuxiliaryPhysicalCompletion
open LocalizedRecursiveAuxiliaryObservationSeparation
open LocalizedChemicalRingReferencePolicyCageInput
open LocalizedChemicalRingReferencePolicyCurrentCageReport (input current_root_source_and_report)
open LocalizedChemicalRingReferencePolicyFrozenCancellation
open LocalizedChemicalRingReferencePolicyFrozenCancellationCage (assignCenter_root)
open LocalizedChemicalRingJointPreparedSourceModel
open LocalizedChemicalRingJointPreparedSourceModelExistence
open LocalizedChemicalRingJointPreparedReport (analyze)
open LocalizedChemicalRingSourcePromotionCancellation (sourceCancellationDescriptor)
open LocalizedChemicalRingAllRootCancellationReport (rootSourceModel_cancellation_equation)
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData)
open LocalizedChemicalRingJointPreparedRootInput (root_data)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedGenericMarkedRecalculationCage (geomOf)

noncomputable section

abbrev Outcome := Option (Option LocalizedTetrahedralRSPseudoDescriptor)
abbrev Report := List (Nat × Outcome)

def rootData (center : input.detectedMultiCenterMolecule.Center) :
    OccurrenceData input cageRaw center (canonicalCenterRoot center.1.val) :=
  Classical.choose (root_data input cageRaw (structure_agreement positions positions_length)
    admissible supported (simpleBondedWith positions positions_length) center)

theorem rootData_address (center : input.detectedMultiCenterMolecule.Center) :
    (rootData center).target.1.address = [] :=
  Classical.choose_spec (root_data input cageRaw (structure_agreement positions positions_length)
    admissible supported (simpleBondedWith positions positions_length) center)

/-- CURRENT cancellation evaluated from the independently generated source profile and actual
root frame at every detected center. -/
def currentCancellationReport (candidate : Profile input cageRaw) : Report :=
  input.canonicalTetrahedralCenters.map fun center =>
    (center.1.val, sourceCancellationDescriptor input (simpleBondedWith positions positions_length)
      (profileFamily input cageRaw candidate
        (finalQuery input cageRaw (structure_agreement positions positions_length) center))
      (rootData center).target (rootData center).frame (inputGeometry input) [])

/-- Independent frozen cancellation uses precisely the same detected-center inventory. -/
def frozenCancellationReport : Report :=
  input.canonicalTetrahedralCenters.map fun center =>
    (center.1.val, assignCenter cageRaw 16 (geomOf positions positions_length) center.1.val)

/-- Preserve the complete CURRENT actual report, including refusals. -/
def liftedActualReport : Report :=
  (analyze input cageRaw).map fun entry => (entry.1, some entry.2)

/-- The all-root theorem establishes the actual CURRENT cancellation report, not merely a
supplied-map aggregation comparison. -/
theorem currentCancellationReport_eq_actual {candidate : Profile input cageRaw}
    (model : SourceModel input cageRaw (simpleBondedWith positions positions_length) candidate) :
    currentCancellationReport candidate = liftedActualReport := by
  unfold currentCancellationReport liftedActualReport analyze
  rw [List.map_map]
  apply List.map_congr_left
  intro center _
  dsimp only [Function.comp_apply]
  apply Prod.ext
  · rfl
  · have cancellation := rootSourceModel_cancellation_equation input
      (simpleBondedWith positions positions_length) cageRaw
      (structure_agreement positions positions_length) admissible supported
      (constantChargeWith positions positions_length) (detectedCfgWith positions positions_length)
      (detectedCoordinatesWith positions positions_length inNondegenerate) model
      (finalQuery input cageRaw (structure_agreement positions positions_length) center)
      center rfl (rootData center) (rootData_address center) []
    rw [cancellation]
    exact congrArg some (assignCenter_eq_sourceModel input cageRaw
      (structure_agreement positions positions_length) admissible supported
      (simpleBondedWith positions positions_length) model (inputGeometry input) center).symm

/-- Actual CURRENT cancellation succeeds at center0; independent frozen cancellation gives a
completed refusal there. The final reports differ with exactly the same detected inventory. -/
theorem actual_final_cancellation_reports_disagree :
    ∃ candidate : Profile input cageRaw,
      SourceModel input cageRaw (simpleBondedWith positions positions_length) candidate ∧
      currentCancellationReport candidate ≠ frozenCancellationReport := by
  obtain ⟨candidate, raw, model, _, member⟩ := current_root_source_and_report
  refine ⟨candidate, model, ?_⟩
  rw [currentCancellationReport_eq_actual model]
  have currentMember : (0, some (some (LocalizedTetrahedralRSPseudoDescriptor.chiral raw))) ∈
      liftedActualReport := by
    unfold liftedActualReport
    exact List.mem_map.mpr ⟨(0, some (.chiral raw)), member, rfl⟩
  have absent : (0, some (some (LocalizedTetrahedralRSPseudoDescriptor.chiral raw))) ∉
      frozenCancellationReport := by
    intro frozenMember
    unfold frozenCancellationReport at frozenMember
    obtain ⟨center, _, equality⟩ := List.mem_map.mp frozenMember
    have atom : center.1.val = 0 := congrArg Prod.fst equality
    have outcome := congrArg Prod.snd equality
    change assignCenter cageRaw 16 (geomOf positions positions_length) center.1.val =
      some (some (.chiral raw)) at outcome
    rw [atom, assignCenter_root positions positions_length inNondegenerate] at outcome
    cases outcome
  intro equality
  exact absent (equality ▸ currentMember)

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationReport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationReport.Outcome
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationReport.Report
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationReport.rootData
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationReport.rootData_address
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationReport.currentCancellationReport
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationReport.frozenCancellationReport
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationReport.liftedActualReport
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationReport.currentCancellationReport_eq_actual
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCancellationReport.actual_final_cancellation_reports_disagree
