import TetraStereo.OneCenter.P94MolecularCompleteInOutRequestScheduler
import TetraStereo.OneCenter.P94CarbohydrateFiveRingTwist

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP94.P94MolecularCompleteCarbohydrateReport

open CoordinateTwistInOut
open P94MolecularAggregator
open P94MolecularBicyclicFramework
open P94MolecularCompleteInOutRequestScheduler
open P94CarbohydrateFiveRingTwist

/-!
# Combined molecule-wide P-94 report with carbohydrate five-ring twist

The existing complete molecular report covers automatically scheduled ordinary ring families and
finite twist/in-out ledgers.  The carbohydrate-specific five-ring twist module has a separate
finite applicability authority because an unannotated molecular graph cannot determine whether
carbohydrate nomenclature applies.  This module combines those two independently specified public
surfaces and deduplicates the union by `(unit, descriptor)`.

The resulting membership theorem is an exact disjunction.  Thus the combined report preserves an
assignment supplied by either source, creates no assignment outside those sources, and emits every
supported public assignment exactly once even when both sources produce the same pair.
-/

def IndependentMolecularAssignmentWithCarbohydrate
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework) (molecule : RawMolecule)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment) : Prop :=
  IndependentMolecularAssignmentFromCompleteInOutLedgers
      premises molecule plan assignment ∨
    IndependentMolecularCarbohydrateFiveRingTwistAssignment
      molecule authority plan.spatial assignment

noncomputable def molecularAssignmentsWithCarbohydrate
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (authority : IndependentCarbohydrateFiveRingAuthority) :
    List P94ConformationAssignment :=
  (molecularAssignmentsFromCompleteInOutLedgers premises certified plan ++
    molecularCarbohydrateFiveRingTwistAssignments
      certified authority plan.spatial).dedup

theorem molecularAssignmentsWithCarbohydrate_mem_iff_independent
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment) :
    assignment ∈ molecularAssignmentsWithCarbohydrate
        premises certified plan authority ↔
      IndependentMolecularAssignmentWithCarbohydrate premises
        certified.result.parsed plan authority assignment := by
  classical
  simp only [molecularAssignmentsWithCarbohydrate, List.mem_dedup, List.mem_append,
    molecularAssignmentsFromCompleteInOutLedgers_mem_iff_independent,
    molecularCarbohydrateFiveRingTwistAssignments_mem_iff,
    IndependentMolecularAssignmentWithCarbohydrate]

theorem baseAssignment_mem_molecularAssignmentsWithCarbohydrate
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment)
    (present : assignment ∈
      molecularAssignmentsFromCompleteInOutLedgers premises certified plan) :
    assignment ∈ molecularAssignmentsWithCarbohydrate
        premises certified plan authority := by
  apply (molecularAssignmentsWithCarbohydrate_mem_iff_independent
    premises certified plan authority assignment).mpr
  exact Or.inl
    ((molecularAssignmentsFromCompleteInOutLedgers_mem_iff_independent
      premises certified plan assignment).mp present)

theorem carbohydrateAssignment_mem_molecularAssignmentsWithCarbohydrate
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment)
    (present : assignment ∈
      molecularCarbohydrateFiveRingTwistAssignments certified authority plan.spatial) :
    assignment ∈ molecularAssignmentsWithCarbohydrate
        premises certified plan authority := by
  apply (molecularAssignmentsWithCarbohydrate_mem_iff_independent
    premises certified plan authority assignment).mpr
  exact Or.inr
    ((molecularCarbohydrateFiveRingTwistAssignments_mem_iff
      certified authority plan.spatial assignment).mp present)

theorem molecularAssignmentsWithCarbohydrate_nodup
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (authority : IndependentCarbohydrateFiveRingAuthority) :
    (molecularAssignmentsWithCarbohydrate premises certified plan authority).Nodup := by
  classical
  exact List.nodup_dedup _

theorem molecularAssignmentWithCarbohydrate_count_eq_one_iff
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment) :
    List.count assignment
        (molecularAssignmentsWithCarbohydrate premises certified plan authority) = 1 ↔
      IndependentMolecularAssignmentWithCarbohydrate premises
        certified.result.parsed plan authority assignment := by
  rw [← molecularAssignmentsWithCarbohydrate_mem_iff_independent]
  constructor
  · intro countOne
    by_contra absent
    have countZero := List.count_eq_zero_of_not_mem absent
    omega
  · exact List.count_eq_one_of_mem
      (molecularAssignmentsWithCarbohydrate_nodup premises certified plan authority)

theorem molecularAssignmentWithCarbohydrate_count_eq_zero_iff
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (authority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment) :
    List.count assignment
        (molecularAssignmentsWithCarbohydrate premises certified plan authority) = 0 ↔
      ¬IndependentMolecularAssignmentWithCarbohydrate premises
        certified.result.parsed plan authority assignment := by
  rw [List.count_eq_zero,
    molecularAssignmentsWithCarbohydrate_mem_iff_independent]

end BlueBookP94.P94MolecularCompleteCarbohydrateReport
end TetraStereo.OneCenter
