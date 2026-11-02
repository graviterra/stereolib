import TetraStereo.OneCenter.P94MolecularHybridRingSelection

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP94.P94MolecularHybridOutcomeLedger

open CoordinateRing
open CoordinateTwistInOut
open P94MolecularAggregator
open P94MolecularRingCycleScheduler
open P94MolecularRequestScheduler
open P94MolecularBicyclicFramework
open P94MolecularCompleteInOutRequestScheduler
open P94CarbohydrateFiveRingTwist
open P94MolecularAuthoritativeRingSelection
open P94MolecularHybridRingSelection

/-!
# Exact accepted/refused ledger for the hybrid P-94 molecule report

The hybrid assignment report has four independent sources: authority-selected ring requests,
scheduled twist requests, molecule-wide scheduled in/out requests, and independently applicable
carbohydrate five-ring units.  This module gives that final surface one typed transaction.

Every finite request occurrence is retained in exactly one accepted/refused outcome.  Correctness
is stated directly against the independent geometry judgment for its family; refusal means that no
such judgment exists.  The public assignment report remains the deduplicated report proved in the
hybrid-selection module, while this ledger records request-level provenance and coherent refusal.
-/

inductive HybridMolecularRequest (State : Type*) where
  | ring (input : AutomaticCoordinateRingInput)
  | twist (input : CoordinateTwistInput State)
  | inOut (input : CoordinateInOutInput ThetaFramework)
  | carbohydrate (unit : P94ConformationUnit)

inductive HybridMolecularOutcome (State : Type*) where
  | ringAccepted (input : AutomaticCoordinateRingInput) (output : CoordinateRingEvidence)
  | twistAccepted (input : CoordinateTwistInput State) (output : CoordinateTwistEvidence State)
  | inOutAccepted (input : CoordinateInOutInput ThetaFramework)
      (output : CoordinateInOutEvidence ThetaFramework)
  | carbohydrateAccepted (unit : P94ConformationUnit) (output : CoordinateRingEvidence)
  | refused (request : HybridMolecularRequest State)

def HybridMolecularOutcome.request {State : Type*} :
    HybridMolecularOutcome State → HybridMolecularRequest State
  | .ringAccepted input _ => .ring input
  | .twistAccepted input _ => .twist input
  | .inOutAccepted input _ => .inOut input
  | .carbohydrateAccepted unit _ => .carbohydrate unit
  | .refused request => request

def HybridMolecularOutcome.Correct {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    HybridMolecularOutcome State → Prop
  | .ringAccepted input output =>
      AutomaticCoordinateRingEvidenceJudgment molecule spatial input output
  | .twistAccepted input output => CoordinateTwistEvidenceJudgment molecule input output
  | .inOutAccepted input output =>
      CoordinateInOutEvidenceJudgment premises molecule input output
  | .carbohydrateAccepted unit output =>
      AutomaticCarbohydrateFiveRingTwistEvidenceJudgment
        carbohydrateAuthority molecule spatial unit output
  | .refused (.ring input) => ¬AutomaticCoordinateRingWitness molecule spatial input
  | .refused (.twist input) =>
      ¬∃ output, CoordinateTwistEvidenceJudgment molecule input output
  | .refused (.inOut input) =>
      ¬∃ output, CoordinateInOutEvidenceJudgment premises molecule input output
  | .refused (.carbohydrate unit) =>
      ¬∃ output, AutomaticCarbohydrateFiveRingTwistEvidenceJudgment
        carbohydrateAuthority molecule spatial unit output

noncomputable def analyzeHybridRequest {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    HybridMolecularRequest State → HybridMolecularOutcome State
  | .ring input =>
      match automaticCoordinateRingEvidence? molecule spatial input with
      | some output => .ringAccepted input output
      | none => .refused (.ring input)
  | .twist input =>
      match coordinateTwistEvidence? molecule input with
      | some output => .twistAccepted input output
      | none => .refused (.twist input)
  | .inOut input =>
      match coordinateInOutEvidence? premises molecule input with
      | some output => .inOutAccepted input output
      | none => .refused (.inOut input)
  | .carbohydrate unit =>
      match automaticCarbohydrateFiveRingTwistEvidence?
          carbohydrateAuthority molecule spatial unit with
      | some output => .carbohydrateAccepted unit output
      | none => .refused (.carbohydrate unit)

theorem analyzeHybridRequest_outcome_request {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (request : HybridMolecularRequest State) :
    (analyzeHybridRequest premises molecule spatial carbohydrateAuthority request).request =
      request := by
  cases request <;> simp only [analyzeHybridRequest] <;> split <;> rfl

theorem analyzeHybridRequest_correct {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (request : HybridMolecularRequest State) :
    (analyzeHybridRequest premises molecule spatial carbohydrateAuthority request).Correct
      premises molecule spatial carbohydrateAuthority := by
  cases request with
  | ring input =>
      simp only [analyzeHybridRequest]
      cases computed : automaticCoordinateRingEvidence? molecule spatial input with
      | none =>
          exact (automaticCoordinateRingEvidence?_eq_none_iff molecule spatial input).mp computed
      | some output =>
          exact (automaticCoordinateRingEvidence?_eq_some_iff
            molecule spatial input output).mp computed
  | twist input =>
      simp only [analyzeHybridRequest]
      cases computed : coordinateTwistEvidence? molecule input with
      | none => exact (coordinateTwistEvidence?_eq_none_iff molecule input).mp computed
      | some output =>
          exact (coordinateTwistEvidence?_eq_some_iff molecule input output).mp computed
  | inOut input =>
      simp only [analyzeHybridRequest]
      cases computed : coordinateInOutEvidence? premises molecule input with
      | none =>
          exact (coordinateInOutEvidence?_eq_none_iff premises molecule input).mp computed
      | some output =>
          exact (coordinateInOutEvidence?_eq_some_iff
            premises molecule input output).mp computed
  | carbohydrate unit =>
      simp only [analyzeHybridRequest]
      cases computed : automaticCarbohydrateFiveRingTwistEvidence?
          carbohydrateAuthority molecule spatial unit with
      | none =>
          exact (automaticCarbohydrateFiveRingTwistEvidence?_eq_none_iff
            carbohydrateAuthority molecule spatial unit).mp computed
      | some output =>
          exact (automaticCarbohydrateFiveRingTwistEvidence?_eq_some_iff
            carbohydrateAuthority molecule spatial unit output).mp computed

/-! ## Exact finite request surface -/

noncomputable def hybridMolecularRequests {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (plan : MolecularCompleteInOutLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    List (HybridMolecularRequest State) :=
  (selectedAutomaticCoordinateRingInputs (hybridRingAuthority external) molecule).toList.map
      HybridMolecularRequest.ring ++
    (scheduledMolecularTwistInputsFromLedgers plan).map HybridMolecularRequest.twist ++
    (scheduledMolecularCompleteInOutInputs molecule
      plan.atomSpatialStates plan.lonePairStates).map HybridMolecularRequest.inOut ++
    (scheduledCarbohydrateFiveRingUnits carbohydrateAuthority molecule).toList.map
      HybridMolecularRequest.carbohydrate

theorem hybridMolecularRequests_ring_mem_iff
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (plan : MolecularCompleteInOutLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (input : AutomaticCoordinateRingInput) :
    (.ring input : HybridMolecularRequest State) ∈
        hybridMolecularRequests molecule plan external carbohydrateAuthority ↔
      (hybridRingAuthority external).Applies molecule input := by
  classical
  simp [hybridMolecularRequests, mem_selectedAutomaticCoordinateRingInputs_iff]

theorem hybridMolecularRequests_twist_mem_iff
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (plan : MolecularCompleteInOutLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (input : CoordinateTwistInput State) :
    (.twist input : HybridMolecularRequest State) ∈
        hybridMolecularRequests molecule plan external carbohydrateAuthority ↔
      input ∈ scheduledMolecularTwistInputsFromLedgers plan := by
  classical
  simp [hybridMolecularRequests]

theorem hybridMolecularRequests_inOut_mem_iff
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (plan : MolecularCompleteInOutLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (input : CoordinateInOutInput ThetaFramework) :
    (.inOut input : HybridMolecularRequest State) ∈
        hybridMolecularRequests molecule plan external carbohydrateAuthority ↔
      input ∈ scheduledMolecularCompleteInOutInputs molecule
        plan.atomSpatialStates plan.lonePairStates := by
  classical
  simp [hybridMolecularRequests]

theorem hybridMolecularRequests_carbohydrate_mem_iff
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (plan : MolecularCompleteInOutLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (unit : P94ConformationUnit) :
    (.carbohydrate unit : HybridMolecularRequest State) ∈
        hybridMolecularRequests molecule plan external carbohydrateAuthority ↔
      carbohydrateAuthority.Applies molecule unit := by
  classical
  simp [hybridMolecularRequests, mem_scheduledCarbohydrateFiveRingUnits_iff]

/-! ## Total typed outcome transaction -/

noncomputable def hybridMolecularOutcomes {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    List (HybridMolecularOutcome State) :=
  (hybridMolecularRequests certified.result.parsed plan external carbohydrateAuthority).map
    (analyzeHybridRequest premises certified.result.parsed plan.spatial carbohydrateAuthority)

theorem hybridMolecularOutcomes_map_request
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    (hybridMolecularOutcomes premises certified plan external carbohydrateAuthority).map
        HybridMolecularOutcome.request =
      hybridMolecularRequests certified.result.parsed plan external carbohydrateAuthority := by
  simp [hybridMolecularOutcomes, Function.comp_def,
    analyzeHybridRequest_outcome_request premises certified.result.parsed plan.spatial
      carbohydrateAuthority]

theorem hybridMolecularOutcomes_all_correct
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    ∀ outcome ∈ hybridMolecularOutcomes premises certified plan external carbohydrateAuthority,
      outcome.Correct premises certified.result.parsed plan.spatial carbohydrateAuthority := by
  intro outcome present
  rcases List.mem_map.mp present with ⟨request, _requestPresent, rfl⟩
  exact analyzeHybridRequest_correct premises certified.result.parsed plan.spatial
    carbohydrateAuthority request

theorem hybridMolecularOutcomes_length_eq_requests_length
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCompleteInOutLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    (hybridMolecularOutcomes premises certified plan external carbohydrateAuthority).length =
      (hybridMolecularRequests certified.result.parsed plan external
        carbohydrateAuthority).length := by
  simp [hybridMolecularOutcomes]

end BlueBookP94.P94MolecularHybridOutcomeLedger
end TetraStereo.OneCenter
