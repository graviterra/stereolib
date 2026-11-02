import TetraStereo.OneCenter.P94MolecularLonePairInOutObservationScheduler

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP94.P94MolecularCompleteInOutRequestScheduler

open CoordinateTwistInOut
open P94MolecularAggregator
open P94MolecularRequestScheduler
open P94MolecularBicyclicFramework
open P94MolecularLonePair
open P94MolecularBridgeheadAxisInterior
open P94MolecularLonePairInOutObservationScheduler

/-!
# Molecule-wide complete P-94.3.2.6 request scheduling

The atom/lone-pair observation scheduler is exhaustive once a bicyclic bridge unit is named.  This
module removes that final unit-selection seam for the represented theta-framework domain.  It
takes the finite union of all three bridges in every graph-derived theta framework, constructs the
complete supplied observation ledger for each such unit, and emits every ordered observation pair.

An accepted pair whose two observations are represented by the supplied physical-atom or
lone-pair geometry ledgers is therefore present without a caller choosing a framework, bridge,
bridgehead, participant, interior reference, or pair.  Invalid finite products remain ordinary
refused requests in the already verified whole-molecule transaction.
-/

/-! ## Every bridge unit of every valid theta framework -/

noncomputable def thetaBridgeUnits (molecule : RawMolecule) :
    Finset P94ConformationUnit :=
  (thetaFrameworks molecule).biUnion ThetaFramework.bridgeUnits

theorem mem_thetaBridgeUnits_iff (molecule : RawMolecule)
    (unit : P94ConformationUnit) :
    unit ∈ thetaBridgeUnits molecule ↔
      ∃ framework : ThetaFramework, framework.ValidFor molecule unit := by
  simp [thetaBridgeUnits, ThetaFramework.ValidFor, ThetaFramework.NamesBridge,
    mem_thetaFrameworks_iff]

/-! ## Complete in/out ledgers and requests across the molecule -/

noncomputable def scheduledMolecularCompleteInOutLedgers (molecule : RawMolecule)
    (atomSpatialStates : List SpatialConfiguration)
    (lonePairStates : List LonePairGeometryState) :
    List (CoordinateInOutLedger ThetaFramework) :=
  (thetaBridgeUnits molecule).toList.map fun unit =>
    scheduledCompleteInOutLedger molecule unit atomSpatialStates lonePairStates

noncomputable def scheduledMolecularCompleteInOutInputs (molecule : RawMolecule)
    (atomSpatialStates : List SpatialConfiguration)
    (lonePairStates : List LonePairGeometryState) :
    List (CoordinateInOutInput ThetaFramework) :=
  (scheduledMolecularCompleteInOutLedgers molecule atomSpatialStates lonePairStates).flatMap
    scheduledCoordinateInOutInputs

theorem mem_scheduledMolecularCompleteInOutInputs_iff (molecule : RawMolecule)
    (atomSpatialStates : List SpatialConfiguration)
    (lonePairStates : List LonePairGeometryState)
    (input : CoordinateInOutInput ThetaFramework) :
    input ∈ scheduledMolecularCompleteInOutInputs molecule atomSpatialStates lonePairStates ↔
      ∃ unit, (∃ framework : ThetaFramework, framework.ValidFor molecule unit) ∧
        input ∈ scheduledCompleteInOutInputs molecule unit
          atomSpatialStates lonePairStates := by
  simp only [scheduledMolecularCompleteInOutInputs,
    scheduledMolecularCompleteInOutLedgers, List.mem_flatMap, List.mem_map,
    Finset.mem_toList]
  constructor
  · rintro ⟨unitLedger, ⟨unit, unitPresent, rfl⟩, inputPresent⟩
    exact ⟨unit, (mem_thetaBridgeUnits_iff molecule unit).mp unitPresent, inputPresent⟩
  · rintro ⟨unit, frameworkPresent, inputPresent⟩
    refine ⟨scheduledCompleteInOutLedger molecule unit atomSpatialStates lonePairStates,
      ⟨unit, (mem_thetaBridgeUnits_iff molecule unit).mpr frameworkPresent, rfl⟩, ?_⟩
    exact inputPresent

/-- Every accepted in/out pair represented by the two finite observation ledgers is included in
the molecule-wide request list. -/
theorem acceptedCoveredInOutInput_mem_scheduled
    (molecule : RawMolecule) (ledger : CertifiedLonePairLedger molecule)
    (atomSpatialStates : List SpatialConfiguration)
    (lonePairStates : List LonePairGeometryState)
    (input : CoordinateInOutInput ThetaFramework)
    (output : CoordinateInOutEvidence ThetaFramework)
    (firstCovered : ObservationCoveredByFiniteLedgers
      atomSpatialStates lonePairStates input.first)
    (secondCovered : ObservationCoveredByFiniteLedgers
      atomSpatialStates lonePairStates input.second)
    (judged : CoordinateInOutEvidenceJudgment
      (graphElectronicAxisBridgePremises molecule ledger) molecule input output) :
    input ∈ scheduledMolecularCompleteInOutInputs molecule
      atomSpatialStates lonePairStates := by
  rcases judged with
    ⟨_kind, _unitValid, frameworkJudged, _sameFramework, _sameBridgehead,
      _sameParticipant, _firstBridge, _secondBridge,
      firstDirection, secondDirection, firstJudged, secondJudged,
      _directionsDiffer, _outputIdentity⟩
  have frameworkValid : input.first.framework.ValidFor molecule input.unit :=
    (graphElectronicAxisBridgePremises_bicyclicFramework_iff
      molecule ledger molecule input.unit input.first.framework).mp frameworkJudged
  apply (mem_scheduledMolecularCompleteInOutInputs_iff
    molecule atomSpatialStates lonePairStates input).mpr
  refine ⟨input.unit, ⟨input.first.framework, frameworkValid⟩, ?_⟩
  apply (mem_scheduledCompleteInOutInputs_iff molecule input.unit
    atomSpatialStates lonePairStates input).mpr
  exact ⟨input.first,
    acceptedCoveredObservation_mem_scheduled molecule ledger input.unit
      atomSpatialStates lonePairStates input.first firstDirection firstCovered firstJudged,
    input.second,
    acceptedCoveredObservation_mem_scheduled molecule ledger input.unit
      atomSpatialStates lonePairStates input.second secondDirection secondCovered secondJudged,
    rfl⟩

/-! ## Direct composition with the verified whole-molecule transaction -/

structure MolecularCompleteInOutLedgerPlan (State : Type*) where
  spatial : SpatialConfiguration
  twistLedgers : List (CoordinateTwistLedger State)
  atomSpatialStates : List SpatialConfiguration
  lonePairStates : List LonePairGeometryState

noncomputable def MolecularCompleteInOutLedgerPlan.toLedgerPlan {State : Type*}
    (molecule : RawMolecule) (plan : MolecularCompleteInOutLedgerPlan State) :
    MolecularEvidenceLedgerPlan State ThetaFramework :=
  { spatial := plan.spatial
    twistLedgers := plan.twistLedgers
    inOutLedgers := scheduledMolecularCompleteInOutLedgers molecule
      plan.atomSpatialStates plan.lonePairStates }

theorem completeInOutEvidencePlan_inOutInputs {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (plan : MolecularCompleteInOutLedgerPlan State) :
    (plan.toLedgerPlan molecule).toEvidencePlan.inOutInputs =
      scheduledMolecularCompleteInOutInputs molecule
        plan.atomSpatialStates plan.lonePairStates :=
  rfl

noncomputable def molecularOutcomesFromCompleteInOutLedgers
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State) :
    List (MolecularOutcome State ThetaFramework) :=
  molecularOutcomesFromLedgers premises certified
    (plan.toLedgerPlan certified.result.parsed)

theorem molecularOutcomesFromCompleteInOutLedgers_all_correct
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State) :
    ∀ outcome ∈ molecularOutcomesFromCompleteInOutLedgers premises certified plan,
      outcome.Correct premises certified.result.parsed plan.spatial := by
  exact molecularOutcomesFromLedgers_all_correct premises certified
    (plan.toLedgerPlan certified.result.parsed)

abbrev IndependentMolecularAssignmentFromCompleteInOutLedgers
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework) (molecule : RawMolecule)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (assignment : P94ConformationAssignment) : Prop :=
  IndependentMolecularAssignmentFromLedgers premises molecule
    (plan.toLedgerPlan molecule) assignment

noncomputable def molecularAssignmentsFromCompleteInOutLedgers
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State) :
    List P94ConformationAssignment :=
  molecularAssignmentsFromLedgers premises certified
    (plan.toLedgerPlan certified.result.parsed)

theorem molecularAssignmentsFromCompleteInOutLedgers_mem_iff_independent
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (assignment : P94ConformationAssignment) :
    assignment ∈ molecularAssignmentsFromCompleteInOutLedgers premises certified plan ↔
      IndependentMolecularAssignmentFromCompleteInOutLedgers premises
        certified.result.parsed plan assignment :=
  molecularAssignmentsFromLedgers_mem_iff_independent premises certified
    (plan.toLedgerPlan certified.result.parsed) assignment

theorem molecularAssignmentsFromCompleteInOutLedgers_nodup
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State) :
    (molecularAssignmentsFromCompleteInOutLedgers premises certified plan).Nodup :=
  molecularAssignmentsFromLedgers_nodup premises certified
    (plan.toLedgerPlan certified.result.parsed)

theorem molecularAssignmentFromCompleteInOutLedgers_count_eq_one_iff
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (assignment : P94ConformationAssignment) :
    List.count assignment
        (molecularAssignmentsFromCompleteInOutLedgers premises certified plan) = 1 ↔
      IndependentMolecularAssignmentFromCompleteInOutLedgers premises
        certified.result.parsed plan assignment :=
  molecularAssignmentFromLedgers_count_eq_one_iff premises certified
    (plan.toLedgerPlan certified.result.parsed) assignment

theorem molecularAssignmentFromCompleteInOutLedgers_count_eq_zero_iff
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (assignment : P94ConformationAssignment) :
    List.count assignment
        (molecularAssignmentsFromCompleteInOutLedgers premises certified plan) = 0 ↔
      ¬IndependentMolecularAssignmentFromCompleteInOutLedgers premises
        certified.result.parsed plan assignment :=
  molecularAssignmentFromLedgers_count_eq_zero_iff premises certified
    (plan.toLedgerPlan certified.result.parsed) assignment

end BlueBookP94.P94MolecularCompleteInOutRequestScheduler
end TetraStereo.OneCenter
