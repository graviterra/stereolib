import TetraStereo.OneCenter.P94MolecularRingCycleScheduler
import TetraStereo.OneCenter.P94CoordinateTwistInOutPerception
import Mathlib.Data.List.Dedup

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP94.P94MolecularAggregator

open CoordinateRing
open CoordinateTwistInOut
open P94MolecularRingCycleScheduler

/-!
# Whole-molecule aggregation for represented P-94 coordinate evidence

This module gives the represented coordinate P-94 families one molecule-level transaction.  Ring
requests are generated exhaustively from the molecule's chordless induced cycles.  Twist and
in-out requests remain explicit because coordinates alone do not determine direct formally-single-
bond rotation steps, complete bicyclic-framework membership, bridge sufficiency, cage interiors,
or lone-pair inventories.

Every request receives exactly one typed accepted/refused outcome.  Accepted family assignments
are combined and deduplicated by `(unit, descriptor)`, with membership and multiplicity stated
against a separate disjunction of the three family judgments.  Thus aggregation cannot create a
descriptor, lose a supported descriptor, or multiply the same public assignment merely because
several witnesses support it.
-/

/-- Molecule-level evidence supplied in addition to the automatically scheduled ring carriers. -/
structure MolecularEvidencePlan (State Framework : Type*) where
  spatial : SpatialConfiguration
  twistInputs : List (CoordinateTwistInput State)
  inOutInputs : List (CoordinateInOutInput Framework)

/-- One request in the represented molecule-level P-94 coordinate transaction. -/
inductive MolecularRequest (State Framework : Type*) where
  | ring (input : AutomaticCoordinateRingInput)
  | twist (input : CoordinateTwistInput State)
  | inOut (input : CoordinateInOutInput Framework)

/-- Every request is retained in its outcome, including refused requests. -/
inductive MolecularOutcome (State Framework : Type*) where
  | ringAccepted (input : AutomaticCoordinateRingInput) (output : CoordinateRingEvidence)
  | twistAccepted (input : CoordinateTwistInput State) (output : CoordinateTwistEvidence State)
  | inOutAccepted (input : CoordinateInOutInput Framework)
      (output : CoordinateInOutEvidence Framework)
  | refused (request : MolecularRequest State Framework)

def MolecularOutcome.request {State Framework : Type*} :
    MolecularOutcome State Framework → MolecularRequest State Framework
  | .ringAccepted input _ => .ring input
  | .twistAccepted input _ => .twist input
  | .inOutAccepted input _ => .inOut input
  | .refused request => request

/-- Independent meaning of each typed transaction outcome.  Refusal means absence of any family
judgment, not failure of a heuristic or exhaustion of implementation fuel. -/
def MolecularOutcome.Correct {State Framework : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises Framework) (molecule : RawMolecule)
    (spatial : SpatialConfiguration) : MolecularOutcome State Framework → Prop
  | .ringAccepted input output =>
      AutomaticCoordinateRingEvidenceJudgment molecule spatial input output
  | .twistAccepted input output => CoordinateTwistEvidenceJudgment molecule input output
  | .inOutAccepted input output =>
      CoordinateInOutEvidenceJudgment premises molecule input output
  | .refused (.ring input) => ¬AutomaticCoordinateRingWitness molecule spatial input
  | .refused (.twist input) => ¬∃ output, CoordinateTwistEvidenceJudgment molecule input output
  | .refused (.inOut input) =>
      ¬∃ output, CoordinateInOutEvidenceJudgment premises molecule input output

/-- Total reference transaction for one request. -/
noncomputable def analyzeRequest {State Framework : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises Framework) (molecule : RawMolecule)
    (spatial : SpatialConfiguration) :
    MolecularRequest State Framework → MolecularOutcome State Framework
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

theorem analyzeRequest_outcome_request {State Framework : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises Framework) (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (request : MolecularRequest State Framework) :
    (analyzeRequest premises molecule spatial request).request = request := by
  cases request <;> simp only [analyzeRequest] <;> split <;> rfl

theorem analyzeRequest_correct {State Framework : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises Framework) (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (request : MolecularRequest State Framework) :
    (analyzeRequest premises molecule spatial request).Correct premises molecule spatial := by
  cases request with
  | ring input =>
      simp only [analyzeRequest]
      cases computed : automaticCoordinateRingEvidence? molecule spatial input with
      | none =>
          exact (automaticCoordinateRingEvidence?_eq_none_iff molecule spatial input).mp computed
      | some output =>
          exact (automaticCoordinateRingEvidence?_eq_some_iff
            molecule spatial input output).mp computed
  | twist input =>
      simp only [analyzeRequest]
      cases computed : coordinateTwistEvidence? molecule input with
      | none => exact (coordinateTwistEvidence?_eq_none_iff molecule input).mp computed
      | some output =>
          exact (coordinateTwistEvidence?_eq_some_iff molecule input output).mp computed
  | inOut input =>
      simp only [analyzeRequest]
      cases computed : coordinateInOutEvidence? premises molecule input with
      | none =>
          exact (coordinateInOutEvidence?_eq_none_iff premises molecule input).mp computed
      | some output =>
          exact (coordinateInOutEvidence?_eq_some_iff
            premises molecule input output).mp computed

/-- Exhaustive request ledger: automatic ring requests first, followed by the explicitly supplied
twist and in-out requests without reordering. -/
noncomputable def molecularRequests {State Framework : Type*}
    (molecule : RawMolecule) (plan : MolecularEvidencePlan State Framework) :
    List (MolecularRequest State Framework) :=
  (scheduledAutomaticCoordinateRingInputs molecule).toList.map MolecularRequest.ring ++
    plan.twistInputs.map MolecularRequest.twist ++
    plan.inOutInputs.map MolecularRequest.inOut

noncomputable def molecularOutcomes {State Framework : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises Framework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularEvidencePlan State Framework) : List (MolecularOutcome State Framework) :=
  (molecularRequests certified.result.parsed plan).map
    (analyzeRequest premises certified.result.parsed plan.spatial)

/-- The transaction neither drops nor invents request occurrences. -/
theorem molecularOutcomes_map_request {State Framework : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises Framework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularEvidencePlan State Framework) :
    (molecularOutcomes premises certified plan).map MolecularOutcome.request =
      molecularRequests certified.result.parsed plan := by
  simp [molecularOutcomes, Function.comp_def,
    analyzeRequest_outcome_request premises certified.result.parsed plan.spatial]

/-- Every accepted or refused ledger entry has its exact independent meaning. -/
theorem molecularOutcomes_all_correct {State Framework : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises Framework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularEvidencePlan State Framework) :
    ∀ outcome ∈ molecularOutcomes premises certified plan,
      outcome.Correct premises certified.result.parsed plan.spatial := by
  intro outcome present
  rcases List.mem_map.mp present with ⟨request, _, rfl⟩
  exact analyzeRequest_correct premises certified.result.parsed plan.spatial request


def IndependentMolecularAssignment {State Framework : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises Framework) (molecule : RawMolecule)
    (plan : MolecularEvidencePlan State Framework)
    (assignment : P94ConformationAssignment) : Prop :=
  ((∃ input ∈ scheduledAutomaticCoordinateRingInputs molecule,
        ∃ output,
          AutomaticCoordinateRingEvidenceJudgment molecule plan.spatial input output ∧
            IndependentP94ConformationAssignment molecule [output] assignment) ∨
      ∃ input ∈ plan.twistInputs,
        ∃ output,
          CoordinateTwistEvidenceJudgment molecule input output ∧
            IndependentP94ConformationAssignment molecule [output] assignment) ∨
    ∃ input ∈ plan.inOutInputs,
      ∃ output,
        CoordinateInOutEvidenceJudgment premises molecule input output ∧
          IndependentP94ConformationAssignment molecule [output] assignment

/-- The public molecule report combines all accepted family assignments and removes only repeated
copies of the same `(unit, descriptor)` pair. -/
noncomputable def molecularAssignments {State Framework : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises Framework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularEvidencePlan State Framework) : List P94ConformationAssignment :=
  (((scheduledAutomaticCoordinateRingInputs certified.result.parsed).toList.flatMap
      (automaticCoordinateRingAssignments certified plan.spatial)) ++
    (plan.twistInputs.flatMap (coordinateTwistAssignments certified)) ++
    (plan.inOutInputs.flatMap (coordinateInOutAssignments certified premises))).dedup

theorem molecularAssignments_mem_iff_independent {State Framework : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises Framework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularEvidencePlan State Framework)
    (assignment : P94ConformationAssignment) :
    assignment ∈ molecularAssignments premises certified plan ↔
      IndependentMolecularAssignment premises certified.result.parsed plan assignment := by
  classical
  simp only [molecularAssignments, List.mem_dedup, List.mem_append, List.mem_flatMap,
    Finset.mem_toList]
  simp_rw [automaticCoordinateRingAssignments_mem_iff certified plan.spatial]
  simp_rw [coordinateTwistAssignments_mem_iff certified]
  simp_rw [coordinateInOutAssignments_mem_iff certified premises]
  rfl

theorem molecularAssignments_nodup {State Framework : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises Framework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularEvidencePlan State Framework) :
    (molecularAssignments premises certified plan).Nodup := by
  classical
  exact List.nodup_dedup _

theorem molecularAssignment_count_eq_one_iff {State Framework : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises Framework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularEvidencePlan State Framework)
    (assignment : P94ConformationAssignment) :
    List.count assignment (molecularAssignments premises certified plan) = 1 ↔
      IndependentMolecularAssignment premises certified.result.parsed plan assignment := by
  rw [← molecularAssignments_mem_iff_independent]
  constructor
  · intro countOne
    by_contra absent
    have countZero : List.count assignment (molecularAssignments premises certified plan) = 0 :=
      List.count_eq_zero_of_not_mem absent
    omega
  · exact List.count_eq_one_of_mem (molecularAssignments_nodup premises certified plan)

theorem molecularAssignment_count_eq_zero_iff {State Framework : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises Framework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularEvidencePlan State Framework)
    (assignment : P94ConformationAssignment) :
    List.count assignment (molecularAssignments premises certified plan) = 0 ↔
      ¬IndependentMolecularAssignment premises certified.result.parsed plan assignment := by
  rw [List.count_eq_zero, molecularAssignments_mem_iff_independent]

end BlueBookP94.P94MolecularAggregator
end TetraStereo.OneCenter
