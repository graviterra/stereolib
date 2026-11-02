import TetraStereo.OneCenter.P94MolecularDirectRotationEvidence
import TetraStereo.OneCenter.P94MolecularHybridOutcomeLedger

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP94.P94MolecularAuditedHybridTransaction

open CoordinateTwistInOut
open P94MolecularRequestScheduler
open P94MolecularCompleteInOutRequestScheduler
open P94CarbohydrateFiveRingTwist
open P94MolecularHybridRingSelection
open P94MolecularHybridOutcomeLedger
open P94MolecularDirectRotationEvidence

/-!
# Final hybrid P-94 transaction over audited direct-rotation ledgers

The final hybrid report previously inherited the generic twist-ledger relation.  This module
replaces that last integration seam with `MolecularDirectRotationLedger`: every generated twist
input receives only the molecule-bound, named-single-bond relation proved by the direct-rotation
module.  Ring, in/out, and carbohydrate scheduling are unchanged.

The adapter reuses the established final assignment and typed-outcome theorems.  A separate
provenance theorem shows that every twist request in the final transaction recovers one source
audited ledger and all of its molecular single-bond soundness facts.
-/

structure MolecularAuditedHybridLedgerPlan (State : Type*) where
  spatial : SpatialConfiguration
  twistLedgers : List (MolecularDirectRotationLedger State)
  atomSpatialStates : List SpatialConfiguration
  lonePairStates : List P94MolecularLonePairInOutObservationScheduler.LonePairGeometryState

def MolecularAuditedHybridLedgerPlan.toCompleteInOutLedgerPlan
    {State : Type*} [DecidableEq State]
    (plan : MolecularAuditedHybridLedgerPlan State) (molecule : RawMolecule) :
    MolecularCompleteInOutLedgerPlan State :=
  { spatial := plan.spatial
    twistLedgers := plan.twistLedgers.map (auditedCoordinateTwistLedger molecule)
    atomSpatialStates := plan.atomSpatialStates
    lonePairStates := plan.lonePairStates }

noncomputable def scheduledAuditedMolecularTwistInputs
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (plan : MolecularAuditedHybridLedgerPlan State) :
    List (CoordinateTwistInput State) :=
  plan.twistLedgers.flatMap fun ledger =>
    scheduledCoordinateTwistInputs (auditedCoordinateTwistLedger molecule ledger)

theorem scheduledMolecularTwistInputsFromAuditedPlan_eq
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (plan : MolecularAuditedHybridLedgerPlan State) :
    P94MolecularAuthoritativeRingSelection.scheduledMolecularTwistInputsFromLedgers
        (plan.toCompleteInOutLedgerPlan molecule) =
      scheduledAuditedMolecularTwistInputs molecule plan := by
  change (plan.twistLedgers.map (auditedCoordinateTwistLedger molecule)).flatMap
      scheduledCoordinateTwistInputs =
    plan.twistLedgers.flatMap fun ledger =>
      scheduledCoordinateTwistInputs (auditedCoordinateTwistLedger molecule ledger)
  induction plan.twistLedgers with
  | nil => rfl
  | cons ledger rest inductionHypothesis =>
      simp only [List.map_cons, List.flatMap_cons, inductionHypothesis]

theorem mem_scheduledAuditedMolecularTwistInputs_iff
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (plan : MolecularAuditedHybridLedgerPlan State)
    (input : CoordinateTwistInput State) :
    input ∈ scheduledAuditedMolecularTwistInputs molecule plan ↔
      ∃ ledger ∈ plan.twistLedgers,
        input ∈ scheduledCoordinateTwistInputs
          (auditedCoordinateTwistLedger molecule ledger) := by
  simp [scheduledAuditedMolecularTwistInputs]

/-! ## Exact final request and outcome surfaces -/

noncomputable def auditedHybridMolecularRequests
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (plan : MolecularAuditedHybridLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    List (HybridMolecularRequest State) :=
  hybridMolecularRequests molecule (plan.toCompleteInOutLedgerPlan molecule)
    external carbohydrateAuthority

theorem auditedHybridMolecularRequests_twist_mem_iff
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (plan : MolecularAuditedHybridLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (input : CoordinateTwistInput State) :
    (.twist input : HybridMolecularRequest State) ∈
        auditedHybridMolecularRequests molecule plan external carbohydrateAuthority ↔
      ∃ ledger ∈ plan.twistLedgers,
        input ∈ scheduledCoordinateTwistInputs
          (auditedCoordinateTwistLedger molecule ledger) := by
  rw [auditedHybridMolecularRequests,
    hybridMolecularRequests_twist_mem_iff,
    scheduledMolecularTwistInputsFromAuditedPlan_eq,
    mem_scheduledAuditedMolecularTwistInputs_iff]

theorem auditedHybridMolecularRequest_twist_rotation_sound
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (plan : MolecularAuditedHybridLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (input : CoordinateTwistInput State)
    (requestPresent : (.twist input : HybridMolecularRequest State) ∈
      auditedHybridMolecularRequests molecule plan external carbohydrateAuthority)
    (first second : State)
    (rotation : input.independentSingleBondRotation first second) :
    ∃ ledger ∈ plan.twistLedgers,
      MolecularSingleBondRotationSound molecule ledger first second := by
  rcases (auditedHybridMolecularRequests_twist_mem_iff molecule plan external
    carbohydrateAuthority input).mp requestPresent with
    ⟨ledger, ledgerPresent, inputPresent⟩
  exact ⟨ledger, ledgerPresent,
    scheduledAuditedCoordinateTwistInput_rotation_sound molecule ledger input
      inputPresent first second rotation⟩

noncomputable def auditedHybridMolecularOutcomes
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularAuditedHybridLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    List (HybridMolecularOutcome State) :=
  hybridMolecularOutcomes premises certified
    (plan.toCompleteInOutLedgerPlan certified.result.parsed)
    external carbohydrateAuthority

theorem auditedHybridMolecularOutcomes_map_request
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularAuditedHybridLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    (auditedHybridMolecularOutcomes premises certified plan external
      carbohydrateAuthority).map HybridMolecularOutcome.request =
      auditedHybridMolecularRequests certified.result.parsed plan external
        carbohydrateAuthority :=
  hybridMolecularOutcomes_map_request premises certified
    (plan.toCompleteInOutLedgerPlan certified.result.parsed)
    external carbohydrateAuthority

theorem auditedHybridMolecularOutcomes_all_correct
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularAuditedHybridLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    ∀ outcome ∈ auditedHybridMolecularOutcomes premises certified plan external
        carbohydrateAuthority,
      outcome.Correct premises certified.result.parsed plan.spatial
        carbohydrateAuthority :=
  hybridMolecularOutcomes_all_correct premises certified
    (plan.toCompleteInOutLedgerPlan certified.result.parsed)
    external carbohydrateAuthority

theorem auditedHybridMolecularOutcomes_length_eq_requests_length
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularAuditedHybridLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    (auditedHybridMolecularOutcomes premises certified plan external
        carbohydrateAuthority).length =
      (auditedHybridMolecularRequests certified.result.parsed plan external
        carbohydrateAuthority).length :=
  hybridMolecularOutcomes_length_eq_requests_length premises certified
    (plan.toCompleteInOutLedgerPlan certified.result.parsed)
    external carbohydrateAuthority

/-! ## Exact final public assignment report -/

abbrev IndependentAuditedMolecularAssignmentWithHybridRings
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (molecule : RawMolecule) (plan : MolecularAuditedHybridLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment) : Prop :=
  IndependentMolecularAssignmentWithHybridRings premises molecule
    (plan.toCompleteInOutLedgerPlan molecule) external carbohydrateAuthority assignment

noncomputable def auditedMolecularAssignmentsWithHybridRings
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularAuditedHybridLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    List P94ConformationAssignment :=
  molecularAssignmentsWithHybridRings premises certified
    (plan.toCompleteInOutLedgerPlan certified.result.parsed)
    external carbohydrateAuthority

theorem auditedMolecularAssignmentsWithHybridRings_mem_iff_independent
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularAuditedHybridLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment) :
    assignment ∈ auditedMolecularAssignmentsWithHybridRings premises certified plan
        external carbohydrateAuthority ↔
      IndependentAuditedMolecularAssignmentWithHybridRings premises
        certified.result.parsed plan external carbohydrateAuthority assignment :=
  molecularAssignmentsWithHybridRings_mem_iff_independent premises certified
    (plan.toCompleteInOutLedgerPlan certified.result.parsed)
    external carbohydrateAuthority assignment

theorem auditedMolecularAssignmentsWithHybridRings_nodup
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularAuditedHybridLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    (auditedMolecularAssignmentsWithHybridRings premises certified plan
      external carbohydrateAuthority).Nodup :=
  molecularAssignmentsWithHybridRings_nodup premises certified
    (plan.toCompleteInOutLedgerPlan certified.result.parsed)
    external carbohydrateAuthority

theorem auditedMolecularAssignmentWithHybridRings_count_eq_one_iff
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularAuditedHybridLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment) :
    List.count assignment (auditedMolecularAssignmentsWithHybridRings premises certified plan
        external carbohydrateAuthority) = 1 ↔
      IndependentAuditedMolecularAssignmentWithHybridRings premises
        certified.result.parsed plan external carbohydrateAuthority assignment :=
  molecularAssignmentWithHybridRings_count_eq_one_iff premises certified
    (plan.toCompleteInOutLedgerPlan certified.result.parsed)
    external carbohydrateAuthority assignment

theorem auditedMolecularAssignmentWithHybridRings_count_eq_zero_iff
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularAuditedHybridLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment) :
    List.count assignment (auditedMolecularAssignmentsWithHybridRings premises certified plan
        external carbohydrateAuthority) = 0 ↔
      ¬IndependentAuditedMolecularAssignmentWithHybridRings premises
        certified.result.parsed plan external carbohydrateAuthority assignment :=
  molecularAssignmentWithHybridRings_count_eq_zero_iff premises certified
    (plan.toCompleteInOutLedgerPlan certified.result.parsed)
    external carbohydrateAuthority assignment

end BlueBookP94.P94MolecularAuditedHybridTransaction
end TetraStereo.OneCenter
