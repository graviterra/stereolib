import TetraStereo.OneCenter.P94MolecularAuditedHybridTransaction

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP94.P94MolecularAuditedTwistOutcomeSoundness

open CoordinateTwistInOut
open P94MolecularRequestScheduler
open P94CarbohydrateFiveRingTwist
open P94MolecularHybridRingSelection
open P94MolecularHybridOutcomeLedger
open P94MolecularDirectRotationEvidence
open P94MolecularAuditedHybridTransaction

/-!
# Molecular single-bond soundness of accepted audited twist paths

The audited final transaction proves that every twist request originates in one molecule-bound
direct-rotation ledger.  This module transports that fact through the independent ordered path
object stored by an accepted twist judgment.  Every adjacent edge of both boat-to-candidate legs
therefore carries `MolecularSingleBondRotationSound`, rather than only the older abstract bounded
state relation.
-/

private theorem molecularSingleBondRotationSound_reverse
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State)
    (first second : State)
    (sound : MolecularSingleBondRotationSound molecule ledger second first) :
    MolecularSingleBondRotationSound molecule ledger first second := by
  rcases sound with
    ⟨bond, bondPresent, saturated, namedEdge, kind, unitValid,
      secondPresent, firstPresent, stateDistinct, spatialDistinct,
      secondComplete, firstComplete⟩
  exact ⟨bond, bondPresent, saturated, namedEdge, kind, unitValid,
    firstPresent, secondPresent, stateDistinct.symm, spatialDistinct.symm,
    firstComplete, secondComplete⟩

theorem scheduledAuditedCoordinateTwistInput_boundedDirectRotationStep_sound
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State)
    (input : CoordinateTwistInput State)
    (inputPresent : input ∈ scheduledCoordinateTwistInputs
      (auditedCoordinateTwistLedger molecule ledger))
    (first second : State)
    (step : DirectRotationStep input.BoundedSingleBondRotation first second) :
    MolecularSingleBondRotationSound molecule ledger first second := by
  rcases step with forward | reverse
  · exact scheduledAuditedCoordinateTwistInput_rotation_sound molecule ledger input
      inputPresent first second forward.2.2
  · exact molecularSingleBondRotationSound_reverse molecule ledger first second
      (scheduledAuditedCoordinateTwistInput_rotation_sound molecule ledger input
        inputPresent second first reverse.2.2)

theorem scheduledAuditedCoordinateTwistInput_directedRotationPath_sound
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State)
    (input : CoordinateTwistInput State)
    (inputPresent : input ∈ scheduledCoordinateTwistInputs
      (auditedCoordinateTwistLedger molecule ledger))
    {states : List State}
    (path : DirectedRotationPath input.BoundedSingleBondRotation states) :
    DirectedRotationPath (MolecularSingleBondRotationSound molecule ledger) states := by
  induction path with
  | singleton state => exact .singleton state
  | @cons first second rest direct tail inductionHypothesis =>
      exact .cons
        (Or.inl (scheduledAuditedCoordinateTwistInput_boundedDirectRotationStep_sound
          molecule ledger input inputPresent first second direct))
        inductionHypothesis

theorem auditedHybridTwistAccepted_paths_sound
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
          (MolecularSingleBondRotationSound certified.result.parsed ledger)
          input.firstLeg ∧
        DirectedRotationPath
          (MolecularSingleBondRotationSound certified.result.parsed ledger)
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
    scheduledAuditedCoordinateTwistInput_directedRotationPath_sound
      certified.result.parsed ledger input inputPresent firstPath,
    scheduledAuditedCoordinateTwistInput_directedRotationPath_sound
      certified.result.parsed ledger input inputPresent secondPath⟩

end BlueBookP94.P94MolecularAuditedTwistOutcomeSoundness
end TetraStereo.OneCenter
