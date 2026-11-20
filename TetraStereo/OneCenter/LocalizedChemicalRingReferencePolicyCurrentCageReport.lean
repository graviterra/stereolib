import TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCageInput
import TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyFrozenCage
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelPhysicalReport
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! CURRENT's independently generated accumulated-reference profile and the separately generated
frozen consensus profile disagree at the final root of the same 15-atom input. CURRENT's
successful descriptor is obtained from the physical/source-model endpoint, not an assumed letter
or supplied auxiliary state. Exact letter equality with the replacing-reference evaluator is
not asserted. This is not a journal2018 cancellation-policy equivalence claim. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCurrentCageReport

open LocalizedHiddenParityMarkedProbe
open LocalizedRecursiveAuxiliaryPhysicalCompletion
open LocalizedRecursiveAuxiliaryObservationSeparation
open LocalizedChemicalRingJointPreparedSourceModel
open LocalizedChemicalRingJointPreparedSourceModelExistence (finalQuery)
open LocalizedChemicalRingJointPreparedSourceModelPhysicalReport
open LocalizedChemicalRingJointPreparedReport
open LocalizedChemicalRingReferencePolicyCageInput
open LocalizedChemicalRingReferencePolicyFrozenCage
open LocalizedGenericMarkedRecalculationCage (geomOf)
open LocalizedChemicalRingPhysicalSense (inputGeometry)

noncomputable section

abbrev input : CertifiedLocalizedCIPInput :=
  LocalizedChemicalRingReferencePolicyCageInput.certified positions positions_length

/-- The unique independently generated CURRENT model assigns a chiral root and the actual
CURRENT report contains that same descriptor. Its absolute letter is derived, not chosen. -/
theorem current_root_source_and_report :
    ∃ candidate : Profile input cageRaw, ∃ raw,
      SourceModel input cageRaw (simpleBondedWith positions positions_length) candidate ∧
      candidate (inputGeometry input) []
        (finalQuery input cageRaw (structure_agreement positions positions_length)
          (rootWith positions positions_length)) = some (.chiral raw) ∧
      (0, some (.chiral raw)) ∈ analyze input cageRaw := by
  obtain ⟨candidate, model, _⟩ := unique_current_source_model positions positions_length
  obtain ⟨descriptor, source, member, physical⟩ := sourceModel_detected_entry
    input cageRaw (structure_agreement positions positions_length) admissible supported
    (simpleBondedWith positions positions_length) (constantChargeWith positions positions_length)
    (detectedCfgWith positions positions_length)
    (detectedCoordinatesWith positions positions_length inNondegenerate) model
    (rootWith positions positions_length)
    (detectedPairwiseWith positions positions_length inMismatch)
  have notLower : ¬ descriptor.IsLowercase := by
    intro lower
    have count := physical.mp lower
    have zero : physicalEnantiomorphicPairCount input.detectedMultiCenterMolecule
        (detectedCfgWith positions positions_length) (rootWith positions positions_length) = 0 :=
      detectedPairCountWith_zero positions positions_length
    rw [zero] at count
    cases count
  cases descriptor with
  | chiral raw => exact ⟨candidate, raw, model, source, member⟩
  | pseudoasymmetric raw => exact False.elim (notLower (by trivial))

/-- These are independently generated final-profile endpoints on the same certified molecule:
CURRENT succeeds; the neutral frozen consensus profile refuses. -/
theorem current_and_frozen_final_profiles_disagree :
    ∃ candidate : Profile input cageRaw,
      SourceModel input cageRaw (simpleBondedWith positions positions_length) candidate ∧
      candidate (inputGeometry input) []
        (finalQuery input cageRaw (structure_agreement positions positions_length)
          (rootWith positions positions_length)) ≠
        frozenAssignCenter? cageRaw 16 (geomOf positions positions_length) 0 := by
  obtain ⟨candidate, raw, model, source, _⟩ := current_root_source_and_report
  refine ⟨candidate, model, ?_⟩
  rw [source, frozenAssign_root positions positions_length inNondegenerate]
  simp

/-- Success-only projection makes CURRENT's detected report comparable to the older generic
report's pair type. The original report, including refusals, is preserved. -/
def successfulCurrentReport : List (Nat × LocalizedTetrahedralRSPseudoDescriptor) :=
  (analyze input cageRaw).filterMap fun entry => entry.2.map fun descriptor => (entry.1, descriptor)

/-- The actual CURRENT detected report and the independent frozen index report differ even
after removing CURRENT's refusal entries: their center0 success inventories disagree. -/
theorem current_and_frozen_final_reports_disagree :
    successfulCurrentReport ≠ frozenAssign cageRaw 16 (geomOf positions positions_length) := by
  obtain ⟨_, raw, _, _, member⟩ := current_root_source_and_report
  have currentMember : (0, LocalizedTetrahedralRSPseudoDescriptor.chiral raw) ∈
      successfulCurrentReport := by
    unfold successfulCurrentReport
    apply List.mem_filterMap.mpr
    exact ⟨(0, some (.chiral raw)), member, rfl⟩
  have absent : (0, LocalizedTetrahedralRSPseudoDescriptor.chiral raw) ∉
      frozenAssign cageRaw 16 (geomOf positions positions_length) := by
    intro frozenMember
    unfold frozenAssign at frozenMember
    obtain ⟨center, _, returned⟩ := List.mem_filterMap.mp frozenMember
    cases value : frozenAssignCenter? cageRaw 16 (geomOf positions positions_length) center with
    | none => simp [value] at returned
    | some descriptor =>
      simp only [value, Option.map_some, Option.some.injEq, Prod.mk.injEq] at returned
      rcases returned with ⟨rfl, rfl⟩
      rw [frozenAssign_root positions positions_length inNondegenerate] at value
      cases value
  intro equality
  exact absent (equality ▸ currentMember)

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCurrentCageReport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCurrentCageReport.input
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCurrentCageReport.current_root_source_and_report
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCurrentCageReport.current_and_frozen_final_profiles_disagree
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCurrentCageReport.successfulCurrentReport
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCurrentCageReport.current_and_frozen_final_reports_disagree
