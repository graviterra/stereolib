import TetraStereo.OneCenter.P94MolecularCoordinateFrameRotationTransaction

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP94.P94MolecularCoordinateFrameCompleteTransaction

open CoordinateTwistInOut
open P94CarbohydrateFiveRingTwist
open P94MolecularHybridRingSelection
open P94MolecularHybridOutcomeLedger
open P94MolecularAuditedHybridTransaction
open P94MolecularCoordinateFrameLedger
open P94MolecularCoordinateFrameRotationTransaction
















structure CoordinateFrameCompleteTransaction where
  assignments : List P94ConformationAssignment
  descriptorOutcomes : List (HybridMolecularOutcome Nat)
  rotationOutcomes : List CoordinateFrameRotationOutcome

noncomputable def coordinateFrameCompleteTransaction
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    CoordinateFrameCompleteTransaction :=
  { assignments := auditedMolecularAssignmentsWithHybridRings premises certified
      plan.toAuditedHybridLedgerPlan external carbohydrateAuthority
    descriptorOutcomes := auditedHybridMolecularOutcomes premises certified
      plan.toAuditedHybridLedgerPlan external carbohydrateAuthority
    rotationOutcomes := coordinateFrameRotationOutcomes certified.result.parsed plan }

theorem coordinateFrameCompleteTransaction_assignments
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    (coordinateFrameCompleteTransaction premises certified plan external
      carbohydrateAuthority).assignments =
      auditedMolecularAssignmentsWithHybridRings premises certified
        plan.toAuditedHybridLedgerPlan external carbohydrateAuthority :=
  rfl

theorem coordinateFrameCompleteTransaction_descriptorOutcomes
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    (coordinateFrameCompleteTransaction premises certified plan external
      carbohydrateAuthority).descriptorOutcomes =
      auditedHybridMolecularOutcomes premises certified plan.toAuditedHybridLedgerPlan external
        carbohydrateAuthority :=
  rfl

theorem coordinateFrameCompleteTransaction_rotationOutcomes
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    (coordinateFrameCompleteTransaction premises certified plan external
      carbohydrateAuthority).rotationOutcomes =
      coordinateFrameRotationOutcomes certified.result.parsed plan :=
  rfl

abbrev IndependentCoordinateFrameAssignment
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (molecule : RawMolecule) (plan : MolecularCoordinateFrameHybridPlan)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment) : Prop :=
  IndependentAuditedMolecularAssignmentWithHybridRings premises molecule
    plan.toAuditedHybridLedgerPlan external carbohydrateAuthority assignment

theorem coordinateFrameCompleteTransaction_assignments_mem_iff_independent
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment) :
    assignment ∈ (coordinateFrameCompleteTransaction premises certified plan external
        carbohydrateAuthority).assignments ↔
      IndependentCoordinateFrameAssignment premises certified.result.parsed plan external
        carbohydrateAuthority assignment :=
  auditedMolecularAssignmentsWithHybridRings_mem_iff_independent premises certified
    plan.toAuditedHybridLedgerPlan external carbohydrateAuthority assignment

theorem coordinateFrameCompleteTransaction_assignments_nodup
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    (coordinateFrameCompleteTransaction premises certified plan external
      carbohydrateAuthority).assignments.Nodup :=
  auditedMolecularAssignmentsWithHybridRings_nodup premises certified
    plan.toAuditedHybridLedgerPlan external carbohydrateAuthority

theorem coordinateFrameCompleteTransaction_assignment_count_eq_one_iff
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment) :
    List.count assignment (coordinateFrameCompleteTransaction premises certified plan external
        carbohydrateAuthority).assignments = 1 ↔
      IndependentCoordinateFrameAssignment premises certified.result.parsed plan external
        carbohydrateAuthority assignment :=
  auditedMolecularAssignmentWithHybridRings_count_eq_one_iff premises certified
    plan.toAuditedHybridLedgerPlan external carbohydrateAuthority assignment

theorem coordinateFrameCompleteTransaction_assignment_count_eq_zero_iff
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (assignment : P94ConformationAssignment) :
    List.count assignment (coordinateFrameCompleteTransaction premises certified plan external
        carbohydrateAuthority).assignments = 0 ↔
      ¬IndependentCoordinateFrameAssignment premises certified.result.parsed plan external
        carbohydrateAuthority assignment :=
  auditedMolecularAssignmentWithHybridRings_count_eq_zero_iff premises certified
    plan.toAuditedHybridLedgerPlan external carbohydrateAuthority assignment

theorem coordinateFrameCompleteTransaction_descriptorOutcomes_map_request
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    (coordinateFrameCompleteTransaction premises certified plan external
        carbohydrateAuthority).descriptorOutcomes.map HybridMolecularOutcome.request =
      auditedHybridMolecularRequests certified.result.parsed plan.toAuditedHybridLedgerPlan
        external carbohydrateAuthority :=
  auditedHybridMolecularOutcomes_map_request premises certified
    plan.toAuditedHybridLedgerPlan external carbohydrateAuthority

theorem coordinateFrameCompleteTransaction_descriptorOutcomes_length
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    (coordinateFrameCompleteTransaction premises certified plan external
        carbohydrateAuthority).descriptorOutcomes.length =
      (auditedHybridMolecularRequests certified.result.parsed plan.toAuditedHybridLedgerPlan
        external carbohydrateAuthority).length :=
  auditedHybridMolecularOutcomes_length_eq_requests_length premises certified
    plan.toAuditedHybridLedgerPlan external carbohydrateAuthority

theorem coordinateFrameCompleteTransaction_descriptorOutcomes_all_correct
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    ∀ outcome ∈ (coordinateFrameCompleteTransaction premises certified plan external
        carbohydrateAuthority).descriptorOutcomes,
      outcome.Correct premises certified.result.parsed plan.spatial carbohydrateAuthority :=
  auditedHybridMolecularOutcomes_all_correct premises certified plan.toAuditedHybridLedgerPlan
    external carbohydrateAuthority

theorem coordinateFrameCompleteTransaction_rotationOutcomes_map_request
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    (coordinateFrameCompleteTransaction premises certified plan external
        carbohydrateAuthority).rotationOutcomes.map CoordinateFrameRotationOutcome.request =
      coordinateFrameRotationRequests plan :=
  coordinateFrameRotationOutcomes_map_request certified.result.parsed plan

theorem coordinateFrameCompleteTransaction_rotationOutcomes_length
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    (coordinateFrameCompleteTransaction premises certified plan external
        carbohydrateAuthority).rotationOutcomes.length =
      (coordinateFrameRotationRequests plan).length :=
  coordinateFrameRotationOutcomes_length certified.result.parsed plan

theorem coordinateFrameCompleteTransaction_rotationOutcomes_all_correct
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority) :
    ∀ outcome ∈ (coordinateFrameCompleteTransaction premises certified plan external
        carbohydrateAuthority).rotationOutcomes,
      outcome.Correct certified.result.parsed :=
  coordinateFrameRotationOutcomes_all_correct certified.result.parsed plan

def TransactionAcceptedMolecularDirectRotation
    (transaction : CoordinateFrameCompleteTransaction)
    (ledger : MolecularCoordinateFrameLedger) (first second : Nat) : Prop :=
  ∃ assertion,
    (.accepted ⟨ledger, assertion⟩ : CoordinateFrameRotationOutcome) ∈
        transaction.rotationOutcomes ∧
      assertion.first = first ∧ assertion.second = second

theorem transactionAcceptedMolecularDirectRotation_iff
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (ledger : MolecularCoordinateFrameLedger) (first second : Nat) :
    TransactionAcceptedMolecularDirectRotation
        (coordinateFrameCompleteTransaction premises certified plan external
          carbohydrateAuthority) ledger first second ↔
      PlanAcceptedMolecularDirectRotation certified.result.parsed plan ledger first second :=
  Iff.rfl

theorem coordinateFrameCompleteTransaction_twistAccepted_paths_audited
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (input : CoordinateTwistInput Nat) (output : CoordinateTwistEvidence Nat)
    (outcomePresent : (.twistAccepted input output : HybridMolecularOutcome Nat) ∈
      (coordinateFrameCompleteTransaction premises certified plan external
        carbohydrateAuthority).descriptorOutcomes) :
    ∃ ledger ∈ plan.twistLedgers,
      DirectedRotationPath
          (TransactionAcceptedMolecularDirectRotation
            (coordinateFrameCompleteTransaction premises certified plan external
              carbohydrateAuthority) ledger)
          input.firstLeg ∧
        DirectedRotationPath
          (TransactionAcceptedMolecularDirectRotation
            (coordinateFrameCompleteTransaction premises certified plan external
              carbohydrateAuthority) ledger)
          input.secondLeg := by
  exact coordinateFrameHybridTwistAccepted_paths_plan_audited premises certified plan external
    carbohydrateAuthority input output outcomePresent

end BlueBookP94.P94MolecularCoordinateFrameCompleteTransaction
end TetraStereo.OneCenter
