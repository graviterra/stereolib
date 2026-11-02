import TetraStereo.OneCenter.IUPACP94SourcePackageNonvacuity
import TetraStereo.OneCenter.IUPACRemaining68ReviewedNonvacuity

set_option autoImplicit false

/-!
# Exact 56-row P-93 source-program nonvacuity boundary

The P-94 source-package schema has one mathematical nonvacuity theorem for its complete twelve-row
family.  This module fixes that schema policy inside the reviewed positive program and removes all
twelve P-94 witnesses from the caller boundary.  The only remaining positive witness family is
therefore the exact 56-row P-93 kernel partition.

This is deliberately a schema-stage reduction, not the release source program: the P-93 policies
and the non-descriptor source-meaning program remain explicit, and the P-94 schema policy still
requires a later frozen-package coherence/totality theorem before it can be called canonical.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

/-- Exactly the policy fields owned by the remaining 56 P-93 rows.  P-94 is not a field here: it
is fixed by `toRemaining71WithP94Schema`. -/
structure Remaining56P93ReviewedPolicies where
  general : P93GeneralAuthorityPolicy
  noncarbon : P93NoncarbonTetrahedralAuthorityPolicy
  acyclic : P93AcyclicAuthorityPolicy
  cyclic : P93CyclicReviewedPolicies

namespace Remaining56P93ReviewedPolicies

/-- Insert the one proof-carrying P-94 schema policy into the remaining-71 reviewed program. -/
def toRemaining71WithP94Schema
    (policies : Remaining56P93ReviewedPolicies) : Remaining71ReviewedPolicies where
  p93General := policies.general
  p93Noncarbon := policies.noncarbon
  p93Acyclic := policies.acyclic
  p93Cyclic := policies.cyclic
  p94 := p94SourcePackageSchemaPolicy

/-- Lift the fixed-P-94 remaining program into the whole descriptor-bearing policy record. -/
def toDescriptorBearingWithP94Schema
    (policies : Remaining56P93ReviewedPolicies) : DescriptorBearingReviewedPolicies where
  remaining71 := policies.toRemaining71WithP94Schema

end Remaining56P93ReviewedPolicies

abbrev ParameterizedRemaining56P93ReviewedNonvacuity
    (policies : Remaining56P93ReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics) : Prop :=
  let globalPolicies := policies.toDescriptorBearingWithP94Schema
  ∀ row : Remaining71P93DescriptorKernelRow,
    ∃ input, ∃ observation :
        ((assembleGlobalReviewedSemantics globalPolicies negative).reviewed.row
          row.provision).reference.Observation,
      (assembleGlobalReviewedSemantics globalPolicies negative).reviewed.ChemicallyAdmitted input ∧
        ((assembleGlobalReviewedSemantics globalPolicies negative).reviewed.row
          row.provision).reference.Applicable input ∧
        ((assembleGlobalReviewedSemantics globalPolicies negative).reviewed.row
          row.provision).reference.Judges input observation

/-- All twelve P-94 rows are generated internally from the concrete source-package family
theorem, then transported into the exact global reviewed join. -/
theorem assembledGlobalReviewedSemantics_p94Schema_nonvacuous
    (policies : Remaining56P93ReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics)
    (row : Remaining71P94AuthorityRow) :
    let globalPolicies := policies.toDescriptorBearingWithP94Schema
    ∃ input, ∃ observation :
        ((assembleGlobalReviewedSemantics globalPolicies negative).reviewed.row
          row.provision).reference.Observation,
      (assembleGlobalReviewedSemantics globalPolicies negative).reviewed.ChemicallyAdmitted input ∧
        ((assembleGlobalReviewedSemantics globalPolicies negative).reviewed.row
          row.provision).reference.Applicable input ∧
        ((assembleGlobalReviewedSemantics globalPolicies negative).reviewed.row
          row.provision).reference.Judges input observation := by
  dsimp only
  rcases
      P94SourcePackageNonvacuity.Remaining71P94AuthorityRow.schema_reference_nonvacuous row with
    ⟨input, observation, admitted, applicable, judged⟩
  let globalPolicies := policies.toDescriptorBearingWithP94Schema
  have referenceEq :
      ((assembleGlobalReviewedSemantics globalPolicies negative).reviewed.row
        row.provision).reference = row.reference p94SourcePackageSchemaPolicy := by
    simpa [globalPolicies, Remaining56P93ReviewedPolicies.toDescriptorBearingWithP94Schema,
      Remaining56P93ReviewedPolicies.toRemaining71WithP94Schema] using
        congrArg ReviewedProvisionSemantics.reference
          (globalReviewedSemantics_remaining71P94_exact
            (assembleGlobalReviewedSemantics globalPolicies negative) row)
  have globalAdmitted :
      (assembleGlobalReviewedSemantics globalPolicies negative).reviewed.ChemicallyAdmitted
        input := by
    simpa [assembleGlobalReviewedSemantics, assembledGlobalReviewedTable] using admitted
  let globalObservation := cast
    (congrArg ProvisionReference.Observation referenceEq.symm) observation
  refine ⟨input, globalObservation, globalAdmitted,
    (ProvisionReference.applicable_congr referenceEq _).mpr applicable, ?_⟩
  apply (ProvisionReference.judges_cast_congr
    referenceEq input globalObservation).mpr
  simpa [globalObservation] using judged

/-- Generate the former 68-row frontier from exactly the 56 P-93 rows.  Every P-94 branch is
closed by `schema_reference_nonvacuous`; there is no P-94 witness argument. -/
theorem assembledGlobalReviewedSemantics_remaining68_nonvacuous_of_remaining56P93
    (policies : Remaining56P93ReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics)
    (remaining56 : ParameterizedRemaining56P93ReviewedNonvacuity policies negative) :
    ParameterizedRemaining68ReviewedNonvacuity
      policies.toDescriptorBearingWithP94Schema negative := by
  intro row
  cases row with
  | p93General child => exact remaining56 (.general child)
  | p93Noncarbon child => exact remaining56 (.noncarbon child)
  | p93Acyclic child => exact remaining56 (.acyclic child)
  | p93Cyclic child => exact remaining56 (.cyclic child)
  | p94 child =>
      exact assembledGlobalReviewedSemantics_p94Schema_nonvacuous policies negative child

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.assembledGlobalReviewedSemantics_p94Schema_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.assembledGlobalReviewedSemantics_remaining68_nonvacuous_of_remaining56P93
