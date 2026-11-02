import TetraStereo.OneCenter.P94MolecularCompleteCarbohydrateReport

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP94.P94MolecularAuthoritativeRingSelection

open CoordinateRing
open CoordinateTwistInOut
open P94MolecularAggregator
open P94MolecularRingCycleScheduler
open P94MolecularRequestScheduler
open P94MolecularBicyclicFramework
open P94MolecularCompleteInOutRequestScheduler
open P94CarbohydrateFiveRingTwist

/-!
# Source-backed selection of P-94 molecular ring requests

The graph scheduler exhausts every chordless induced molecular cycle.  That is the correct finite
carrier universe, but overlapping cycles in fused and bridged systems do not by themselves encode
which rings an external nomenclature authority intends to treat as P-94 conformation carriers.
This module makes that applicability boundary explicit and exact.

An independent finite authority selects only requests already proved to belong to the exhaustive
scheduler.  The final report replaces the former all-chordless-cycle ring branch with this selected
branch, while retaining the scheduled twist and molecule-wide in/out inputs and the independently
applicable carbohydrate five-ring branch.  Its public membership theorem is the exact disjunction
of those four sources.
-/

/-! ## Exact finite ring applicability -/

structure IndependentP94RingSelectionAuthority where
  Applies : RawMolecule → AutomaticCoordinateRingInput → Prop
  inputs : RawMolecule → Finset AutomaticCoordinateRingInput
  mem_inputs_iff : ∀ molecule input, input ∈ inputs molecule ↔ Applies molecule input
  applies_scheduled : ∀ molecule input, Applies molecule input →
    input ∈ scheduledAutomaticCoordinateRingInputs molecule

def selectedAutomaticCoordinateRingInputs
    (authority : IndependentP94RingSelectionAuthority) (molecule : RawMolecule) :
    Finset AutomaticCoordinateRingInput :=
  authority.inputs molecule

theorem mem_selectedAutomaticCoordinateRingInputs_iff
    (authority : IndependentP94RingSelectionAuthority) (molecule : RawMolecule)
    (input : AutomaticCoordinateRingInput) :
    input ∈ selectedAutomaticCoordinateRingInputs authority molecule ↔
      authority.Applies molecule input :=
  authority.mem_inputs_iff molecule input

theorem selectedAutomaticCoordinateRingInput_mem_scheduled
    (authority : IndependentP94RingSelectionAuthority) (molecule : RawMolecule)
    (input : AutomaticCoordinateRingInput)
    (selected : input ∈ selectedAutomaticCoordinateRingInputs authority molecule) :
    input ∈ scheduledAutomaticCoordinateRingInputs molecule :=
  authority.applies_scheduled molecule input
    ((mem_selectedAutomaticCoordinateRingInputs_iff authority molecule input).mp selected)

/-- Basis-neutral compatibility authority recovering the previous policy that every scheduled
chordless-cycle request is applicable.  Source-specific authorities may select a strict subset. -/
noncomputable def allScheduledRingAuthority : IndependentP94RingSelectionAuthority where
  Applies := fun molecule input =>
    input ∈ scheduledAutomaticCoordinateRingInputs molecule
  inputs := scheduledAutomaticCoordinateRingInputs
  mem_inputs_iff := fun _ _ => Iff.rfl
  applies_scheduled := fun _ _ present => present

theorem allScheduledRingAuthority_applies_iff
    (molecule : RawMolecule) (input : AutomaticCoordinateRingInput) :
    allScheduledRingAuthority.Applies molecule input ↔
      input ∈ scheduledAutomaticCoordinateRingInputs molecule :=
  Iff.rfl

/-! ## Authority-filtered automatic ring report -/

def IndependentAuthoritativeMolecularRingAssignment
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (authority : IndependentP94RingSelectionAuthority)
    (assignment : P94ConformationAssignment) : Prop :=
  ∃ input, authority.Applies molecule input ∧
    ∃ output,
      AutomaticCoordinateRingEvidenceJudgment molecule spatial input output ∧
      IndependentP94ConformationAssignment molecule [output] assignment

noncomputable def authoritativeMolecularRingAssignments
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (authority : IndependentP94RingSelectionAuthority) :
    List P94ConformationAssignment :=
  ((selectedAutomaticCoordinateRingInputs authority certified.result.parsed).toList.flatMap
    (automaticCoordinateRingAssignments certified spatial)).dedup

theorem authoritativeMolecularRingAssignments_mem_iff
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (authority : IndependentP94RingSelectionAuthority)
    (assignment : P94ConformationAssignment) :
    assignment ∈ authoritativeMolecularRingAssignments certified spatial authority ↔
      IndependentAuthoritativeMolecularRingAssignment
        certified.result.parsed spatial authority assignment := by
  classical
  simp only [authoritativeMolecularRingAssignments, List.mem_dedup,
    List.mem_flatMap, Finset.mem_toList,
    mem_selectedAutomaticCoordinateRingInputs_iff]
  simp_rw [automaticCoordinateRingAssignments_mem_iff certified spatial]
  rfl

theorem authoritativeMolecularRingAssignments_nodup
    (certified : CertifiedChemistryNormalizationResult)
    (spatial : SpatialConfiguration)
    (authority : IndependentP94RingSelectionAuthority) :
    (authoritativeMolecularRingAssignments certified spatial authority).Nodup := by
  classical
  exact List.nodup_dedup _

/-! ## Complete molecule report with selected rings -/

noncomputable def scheduledMolecularTwistInputsFromLedgers {State : Type*}
    [DecidableEq State] (plan : MolecularCompleteInOutLedgerPlan State) :
    List (CoordinateTwistInput State) :=
  plan.twistLedgers.flatMap scheduledCoordinateTwistInputs

def IndependentMolecularAssignmentWithAuthoritativeRings
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (molecule : RawMolecule) (plan : MolecularCompleteInOutLedgerPlan State)
    (ringAuthority : IndependentP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment) : Prop :=
  ((IndependentAuthoritativeMolecularRingAssignment
        molecule plan.spatial ringAuthority assignment ∨
      (∃ input ∈ scheduledMolecularTwistInputsFromLedgers plan,
        ∃ output,
          CoordinateTwistEvidenceJudgment molecule input output ∧
          IndependentP94ConformationAssignment molecule [output] assignment)) ∨
    (∃ input ∈ scheduledMolecularCompleteInOutInputs molecule
      plan.atomSpatialStates plan.lonePairStates,
    ∃ output,
      CoordinateInOutEvidenceJudgment premises molecule input output ∧
      IndependentP94ConformationAssignment molecule [output] assignment)) ∨
    IndependentMolecularCarbohydrateFiveRingTwistAssignment
      molecule carbohydrateAuthority plan.spatial assignment

noncomputable def molecularAssignmentsWithAuthoritativeRings
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (ringAuthority : IndependentP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    List P94ConformationAssignment :=
  (authoritativeMolecularRingAssignments certified plan.spatial ringAuthority ++
    (scheduledMolecularTwistInputsFromLedgers plan).flatMap
      (coordinateTwistAssignments certified) ++
    (scheduledMolecularCompleteInOutInputs certified.result.parsed
      plan.atomSpatialStates plan.lonePairStates).flatMap
      (coordinateInOutAssignments certified premises) ++
    molecularCarbohydrateFiveRingTwistAssignments
      certified carbohydrateAuthority plan.spatial).dedup

theorem molecularAssignmentsWithAuthoritativeRings_mem_iff_independent
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (ringAuthority : IndependentP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment) :
    assignment ∈ molecularAssignmentsWithAuthoritativeRings premises certified plan
        ringAuthority carbohydrateAuthority ↔
      IndependentMolecularAssignmentWithAuthoritativeRings premises
        certified.result.parsed plan ringAuthority carbohydrateAuthority assignment := by
  classical
  simp only [molecularAssignmentsWithAuthoritativeRings, List.mem_dedup,
    List.mem_append, authoritativeMolecularRingAssignments_mem_iff,
    List.mem_flatMap,
    molecularCarbohydrateFiveRingTwistAssignments_mem_iff]
  simp_rw [coordinateTwistAssignments_mem_iff certified]
  simp_rw [coordinateInOutAssignments_mem_iff certified premises]
  rfl

theorem molecularAssignmentsWithAuthoritativeRings_nodup
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (ringAuthority : IndependentP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    (molecularAssignmentsWithAuthoritativeRings premises certified plan
      ringAuthority carbohydrateAuthority).Nodup := by
  classical
  exact List.nodup_dedup _

theorem molecularAssignmentWithAuthoritativeRings_count_eq_one_iff
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (ringAuthority : IndependentP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment) :
    List.count assignment (molecularAssignmentsWithAuthoritativeRings premises certified plan
        ringAuthority carbohydrateAuthority) = 1 ↔
      IndependentMolecularAssignmentWithAuthoritativeRings premises
        certified.result.parsed plan ringAuthority carbohydrateAuthority assignment := by
  rw [← molecularAssignmentsWithAuthoritativeRings_mem_iff_independent]
  constructor
  · intro countOne
    by_contra absent
    have countZero := List.count_eq_zero_of_not_mem absent
    omega
  · exact List.count_eq_one_of_mem
      (molecularAssignmentsWithAuthoritativeRings_nodup premises certified plan
        ringAuthority carbohydrateAuthority)

theorem molecularAssignmentWithAuthoritativeRings_count_eq_zero_iff
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (ringAuthority : IndependentP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment) :
    List.count assignment (molecularAssignmentsWithAuthoritativeRings premises certified plan
        ringAuthority carbohydrateAuthority) = 0 ↔
      ¬IndependentMolecularAssignmentWithAuthoritativeRings premises
        certified.result.parsed plan ringAuthority carbohydrateAuthority assignment := by
  rw [List.count_eq_zero,
    molecularAssignmentsWithAuthoritativeRings_mem_iff_independent]

end BlueBookP94.P94MolecularAuthoritativeRingSelection
end TetraStereo.OneCenter
