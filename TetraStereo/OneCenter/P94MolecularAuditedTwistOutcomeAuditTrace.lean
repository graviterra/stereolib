import TetraStereo.OneCenter.P94MolecularDirectRotationAuditLedger
import TetraStereo.OneCenter.P94MolecularAuditedTwistOutcomeSoundness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP94.P94MolecularAuditedTwistOutcomeAuditTrace

open CoordinateTwistInOut
open P94MolecularRequestScheduler
open P94CarbohydrateFiveRingTwist
open P94MolecularHybridRingSelection
open P94MolecularHybridOutcomeLedger
open P94MolecularDirectRotationEvidence
open P94MolecularDirectRotationAuditLedger
open P94MolecularAuditedHybridTransaction










def AcceptedMolecularDirectRotation {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State)
    (first second : State) : Prop :=
  ∃ assertion,
    (.accepted assertion : MolecularDirectRotationOutcome State) ∈
        molecularDirectRotationOutcomes molecule ledger ∧
      assertion.first = first ∧ assertion.second = second

theorem acceptedMolecularDirectRotation_iff
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State)
    (first second : State) :
    AcceptedMolecularDirectRotation molecule ledger first second ↔
      RotationAboutMolecularSingleBond molecule ledger first second :=
  (rotationAboutMolecularSingleBond_iff_accepted_outcome
    molecule ledger first second).symm

theorem scheduledAuditedCoordinateTwistInput_rotation_accepted
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State)
    (input : CoordinateTwistInput State)
    (inputPresent : input ∈ scheduledCoordinateTwistInputs
      (auditedCoordinateTwistLedger molecule ledger))
    (first second : State)
    (rotation : input.independentSingleBondRotation first second) :
    AcceptedMolecularDirectRotation molecule ledger first second := by
  rcases (mem_scheduledCoordinateTwistInputs_iff
    (auditedCoordinateTwistLedger molecule ledger) input).mp inputPresent with
    ⟨candidate, _candidatePresent, inputEq⟩
  subst input
  change RotationAboutMolecularSingleBond molecule ledger first second at rotation
  exact (acceptedMolecularDirectRotation_iff molecule ledger first second).2 rotation

theorem scheduledAuditedCoordinateTwistInput_boundedDirectRotationStep_audited
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State)
    (input : CoordinateTwistInput State)
    (inputPresent : input ∈ scheduledCoordinateTwistInputs
      (auditedCoordinateTwistLedger molecule ledger))
    (first second : State)
    (step : DirectRotationStep input.BoundedSingleBondRotation first second) :
    DirectRotationStep (AcceptedMolecularDirectRotation molecule ledger) first second := by
  rcases step with forward | reverse
  · exact Or.inl (scheduledAuditedCoordinateTwistInput_rotation_accepted
      molecule ledger input inputPresent first second forward.2.2)
  · exact Or.inr (scheduledAuditedCoordinateTwistInput_rotation_accepted
      molecule ledger input inputPresent second first reverse.2.2)

theorem scheduledAuditedCoordinateTwistInput_directedRotationPath_audited
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State)
    (input : CoordinateTwistInput State)
    (inputPresent : input ∈ scheduledCoordinateTwistInputs
      (auditedCoordinateTwistLedger molecule ledger))
    {states : List State}
    (path : DirectedRotationPath input.BoundedSingleBondRotation states) :
    DirectedRotationPath (AcceptedMolecularDirectRotation molecule ledger) states := by
  induction path with
  | singleton state => exact .singleton state
  | @cons first second rest direct tail inductionHypothesis =>
      exact .cons
        (scheduledAuditedCoordinateTwistInput_boundedDirectRotationStep_audited
          molecule ledger input inputPresent first second direct)
        inductionHypothesis

theorem auditedHybridTwistAccepted_paths_audited
    {State : Type*} [DecidableEq State]
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularAuditedHybridLedgerPlan State)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (input : CoordinateTwistInput State) (output : CoordinateTwistEvidence State)
    (outcomePresent : (.twistAccepted input output : HybridMolecularOutcome State) ∈
      auditedHybridMolecularOutcomes premises certified plan external
        carbohydrateAuthority) :
    ∃ ledger ∈ plan.twistLedgers,
      DirectedRotationPath
          (AcceptedMolecularDirectRotation certified.result.parsed ledger)
          input.firstLeg ∧
        DirectedRotationPath
          (AcceptedMolecularDirectRotation certified.result.parsed ledger)
          input.secondLeg := by
  have correct := auditedHybridMolecularOutcomes_all_correct premises certified plan external
    carbohydrateAuthority (.twistAccepted input output) outcomePresent
  change CoordinateTwistEvidenceJudgment certified.result.parsed input output at correct
  rcases correct with ⟨_kind, _unitValid, _statesNodup, _bounded, explicit, _outputEq⟩
  rcases explicit with
    ⟨_firstBoat, _secondBoat, _stateDistinct, _spatialDistinct,
      _firstBoatJudged, _secondBoatJudged, _candidateNotBoat, _candidateNotChair,
      _firstHead, _firstLast, _secondHead, _secondLast,
      firstPath, secondPath, _combinedNodup⟩
  have requestPresent : (.twist input : HybridMolecularRequest State) ∈
      auditedHybridMolecularRequests certified.result.parsed plan external
        carbohydrateAuthority := by
    rw [← auditedHybridMolecularOutcomes_map_request premises certified plan external
      carbohydrateAuthority]
    exact List.mem_map.mpr
      ⟨.twistAccepted input output, outcomePresent, rfl⟩
  rcases (auditedHybridMolecularRequests_twist_mem_iff certified.result.parsed plan external
    carbohydrateAuthority input).mp requestPresent with
    ⟨ledger, ledgerPresent, inputPresent⟩
  exact ⟨ledger, ledgerPresent,
    scheduledAuditedCoordinateTwistInput_directedRotationPath_audited
      certified.result.parsed ledger input inputPresent firstPath,
    scheduledAuditedCoordinateTwistInput_directedRotationPath_audited
      certified.result.parsed ledger input inputPresent secondPath⟩

end BlueBookP94.P94MolecularAuditedTwistOutcomeAuditTrace
end TetraStereo.OneCenter
