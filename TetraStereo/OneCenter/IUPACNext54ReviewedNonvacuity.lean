import TetraStereo.OneCenter.IUPACNext54GlobalProductionAdapter
import TetraStereo.OneCenter.IUPACNext54P92DigraphRule1aNonvacuity

set_option autoImplicit false

/-!
# Unconditional reviewed nonvacuity for the descriptor-bearing next-54 family

The exact 46-row production partition already reduces the descriptor-bearing next-54 scope to
four mathematical families.  This module supplies a witness for every family row and transports
that single theorem into the assembled global reviewed program.  No next-54 witness relation is
accepted from a caller.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

namespace Next54ProductionFamilyRow

/-- Every one of the 46 descriptor-bearing next-54 references has a structurally well-formed
input and a judged observation. -/
theorem reference_nonvacuous (row : Next54ProductionFamilyRow) :
    ∃ input, ∃ observation : row.reference.Observation,
      input.StructurallyWellFormed ∧
        row.reference.Applicable input ∧
          row.reference.Judges input observation := by
  cases row with
  | p92Foundational child =>
      rcases child.reference_nonvacuous with ⟨observation, applicable, judged⟩
      exact ⟨Next54P92FoundationalAuthorityRow.witnessInput, observation,
        Next54P92FoundationalAuthorityRow.witnessInput_structurallyWellFormed,
        applicable, judged⟩
  | p92DigraphRule1a child =>
      exact child.reference_nonvacuous
  | p93Residual child =>
      rcases child.reference_nonvacuous with ⟨observation, applicable, judged⟩
      exact ⟨Next54P93ResidualAuthorityRow.witnessInput, observation,
        Next54P93ResidualAuthorityRow.witnessInput_structurallyWellFormed,
        applicable, judged⟩
  | ir9Residual child =>
      rcases child.toAuthorityRow.reference_nonvacuous with
        ⟨observation, applicable, judged⟩
      exact ⟨next54IR9WitnessInput, observation,
        next54IR9WitnessInput_structurallyWellFormed, applicable, judged⟩

end Next54ProductionFamilyRow

/-- The assembled global reviewed table obtains all 46 next-54 witnesses from the fixed family
partition.  The only inputs are the reviewed programs themselves; there is no next-54
nonvacuity argument. -/
theorem assembledGlobalReviewedSemantics_next54_nonvacuous
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics) :
    ∀ row : Next54DescriptorBearingReviewedRow,
      ∃ input, ∃ observation :
          ((assembleGlobalReviewedSemantics policies negative).reviewed.row
            row.provision).reference.Observation,
        (assembleGlobalReviewedSemantics policies negative).reviewed.ChemicallyAdmitted input ∧
          ((assembleGlobalReviewedSemantics policies negative).reviewed.row
            row.provision).reference.Applicable input ∧
          ((assembleGlobalReviewedSemantics policies negative).reviewed.row
            row.provision).reference.Judges input observation := by
  intro reviewedRow
  let familyRow := Next54ProductionFamilyRow.familyRowOf reviewedRow
  have provisionEq : familyRow.provision = reviewedRow.provision :=
    Next54ProductionFamilyRow.familyRowOf_provision reviewedRow
  rw [← provisionEq]
  rcases familyRow.reference_nonvacuous with
    ⟨input, observation, wellFormed, applicable, judged⟩
  have referenceEq := familyRow.globalReviewedReference_eq
    (assembleGlobalReviewedSemantics policies negative)
  have admitted :
      (assembleGlobalReviewedSemantics policies negative).reviewed.ChemicallyAdmitted input := by
    simpa [assembleGlobalReviewedSemantics, assembledGlobalReviewedTable] using wellFormed
  let globalObservation := cast
    (congrArg ProvisionReference.Observation referenceEq.symm) observation
  refine ⟨input, globalObservation, admitted,
    (ProvisionReference.applicable_congr referenceEq input).mpr applicable, ?_⟩
  apply (ProvisionReference.judges_cast_congr
    referenceEq input globalObservation).mpr
  simpa [globalObservation] using judged

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54ProductionFamilyRow.reference_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.assembledGlobalReviewedSemantics_next54_nonvacuous
