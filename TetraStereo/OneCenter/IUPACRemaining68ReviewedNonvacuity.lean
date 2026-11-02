import TetraStereo.OneCenter.IUPACRemaining71GlobalKernelDispatch

set_option autoImplicit false

/-!
# Exact 68-row source-program nonvacuity boundary

The remaining-71 family contains 56 P-93 rows, 12 P-94 rows, and three frozen authority-data
lookups.  The authority-data rows already have concrete table witnesses, so they are generated
here and removed from the caller boundary.  The resulting sum type is exactly the 68 rows whose
nonvacuity still depends on the canonical P-93/P-94 source program.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

inductive Remaining68SourceProgramRow where
  | p93General (row : Remaining71P93GeneralAuthorityRow)
  | p93Noncarbon (row : Remaining71P93NoncarbonAuthorityRow)
  | p93Acyclic (row : Remaining71P93AcyclicAuthorityRow)
  | p93Cyclic (row : Remaining71P93CyclicAuthorityRow)
  | p94 (row : Remaining71P94AuthorityRow)
  deriving DecidableEq, Repr

namespace Remaining68SourceProgramRow

def all : List Remaining68SourceProgramRow :=
  Remaining71P93GeneralAuthorityRow.all.map .p93General ++
    Remaining71P93NoncarbonAuthorityRow.all.map .p93Noncarbon ++
      Remaining71P93AcyclicAuthorityRow.all.map .p93Acyclic ++
        Remaining71P93CyclicAuthorityRow.all.map .p93Cyclic ++
          Remaining71P94AuthorityRow.all.map .p94

def toRemaining71 : Remaining68SourceProgramRow → Remaining71ReviewedRow
  | .p93General row => .p93General row
  | .p93Noncarbon row => .p93Noncarbon row
  | .p93Acyclic row => .p93Acyclic row
  | .p93Cyclic row => .p93Cyclic row
  | .p94 row => .p94 row

def provision (row : Remaining68SourceProgramRow) : IUPACNormativeProvision :=
  row.toRemaining71.provision

@[simp] theorem all_length : all.length = 68 := by
  simp [all, Remaining71P93GeneralAuthorityRow.all,
    Remaining71P93NoncarbonAuthorityRow.all,
    Remaining71P93AcyclicAuthorityRow.all,
    Remaining71P93CyclicAuthorityRow.all,
    Remaining71P94AuthorityRow.all]

@[simp] theorem all_provisions_exact :
    all.map provision =
      Remaining71P93DescriptorKernelRow.provisions ++ p94SemanticsSlice := by
  have generalExact := Remaining71P93GeneralAuthorityRow.all_provisions_exact
  have noncarbonExact := Remaining71P93NoncarbonAuthorityRow.all_provisions_exact
  have acyclicExact := Remaining71P93AcyclicAuthorityRow.all_provisions_exact
  have cyclicExact := Remaining71P93CyclicAuthorityRow.all_provisions_exact
  have p94Exact := Remaining71P94AuthorityRow.all_provisions_exact
  rw [Remaining71P93DescriptorKernelRow.provisions_exact]
  simp only [all, provision, toRemaining71, List.map_append, List.map_map,
    Function.comp_def, Remaining71ReviewedRow.provision, generalExact,
    noncarbonExact, acyclicExact, cyclicExact, p94Exact,
    remainingP93DescriptorProvisions]

end Remaining68SourceProgramRow

abbrev ParameterizedRemaining68ReviewedNonvacuity
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics) : Prop :=
  ∀ row : Remaining68SourceProgramRow,
    ∃ input, ∃ observation :
        ((assembleGlobalReviewedSemantics policies negative).reviewed.row
          row.provision).reference.Observation,
      (assembleGlobalReviewedSemantics policies negative).reviewed.ChemicallyAdmitted input ∧
        ((assembleGlobalReviewedSemantics policies negative).reviewed.row
          row.provision).reference.Applicable input ∧
        ((assembleGlobalReviewedSemantics policies negative).reviewed.row
          row.provision).reference.Judges input observation

/-- Each of the three authority-data rows is witnessed by an actual entry in the frozen periodic,
CIAAW-2021, or AME-2020 table. -/
theorem assembledGlobalReviewedSemantics_authorityData_nonvacuous
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics)
    (row : Remaining71AuthorityDataRow) :
    ∃ input, ∃ observation :
        ((assembleGlobalReviewedSemantics policies negative).reviewed.row
          row.provision).reference.Observation,
      (assembleGlobalReviewedSemantics policies negative).reviewed.ChemicallyAdmitted input ∧
        ((assembleGlobalReviewedSemantics policies negative).reviewed.row
          row.provision).reference.Applicable input ∧
        ((assembleGlobalReviewedSemantics policies negative).reviewed.row
          row.provision).reference.Judges input observation := by
  rcases row.reference_nonvacuous with ⟨observation, applicable, judged⟩
  have referenceEq :
      ((assembleGlobalReviewedSemantics policies negative).reviewed.row
        row.provision).reference = row.reference := by
    simpa using congrArg ReviewedProvisionSemantics.reference
      (globalReviewedSemantics_remaining71AuthorityData_exact
        (assembleGlobalReviewedSemantics policies negative) row)
  have admitted :
      (assembleGlobalReviewedSemantics policies negative).reviewed.ChemicallyAdmitted
        Remaining71AuthorityDataRow.witnessInput := by
    simp [assembleGlobalReviewedSemantics, assembledGlobalReviewedTable]
  let globalObservation := cast
    (congrArg ProvisionReference.Observation referenceEq.symm) observation
  refine ⟨Remaining71AuthorityDataRow.witnessInput, globalObservation, admitted,
    (ProvisionReference.applicable_congr referenceEq _).mpr applicable, ?_⟩
  apply (ProvisionReference.judges_cast_congr
    referenceEq Remaining71AuthorityDataRow.witnessInput globalObservation).mpr
  simpa [globalObservation] using judged

/-- Generate the full remaining-71 nonvacuity family from exactly the 68 P-93/P-94 source rows;
authority data is inserted internally from frozen tables. -/
theorem assembledGlobalReviewedSemantics_remaining71_nonvacuous_of_remaining68
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics)
    (remaining68 : ParameterizedRemaining68ReviewedNonvacuity policies negative) :
    ∀ row : Remaining71ReviewedRow,
      ∃ input, ∃ observation :
          ((assembleGlobalReviewedSemantics policies negative).reviewed.row
            row.provision).reference.Observation,
        (assembleGlobalReviewedSemantics policies negative).reviewed.ChemicallyAdmitted input ∧
          ((assembleGlobalReviewedSemantics policies negative).reviewed.row
            row.provision).reference.Applicable input ∧
          ((assembleGlobalReviewedSemantics policies negative).reviewed.row
            row.provision).reference.Judges input observation := by
  intro row
  cases row with
  | p93General child => exact remaining68 (.p93General child)
  | p93Noncarbon child => exact remaining68 (.p93Noncarbon child)
  | p93Acyclic child => exact remaining68 (.p93Acyclic child)
  | p93Cyclic child => exact remaining68 (.p93Cyclic child)
  | p94 child => exact remaining68 (.p94 child)
  | authorityData child =>
      exact assembledGlobalReviewedSemantics_authorityData_nonvacuous
        policies negative child

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining68SourceProgramRow.all_length
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining68SourceProgramRow.all_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.assembledGlobalReviewedSemantics_authorityData_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.assembledGlobalReviewedSemantics_remaining71_nonvacuous_of_remaining68
