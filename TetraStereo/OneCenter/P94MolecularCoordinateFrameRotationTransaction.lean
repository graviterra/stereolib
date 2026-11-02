import TetraStereo.OneCenter.P94MolecularCoordinateFrameLedger

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP94.P94MolecularCoordinateFrameRotationTransaction

open CoordinateTwistInOut
open P94CarbohydrateFiveRingTwist
open P94MolecularHybridRingSelection
open P94MolecularHybridOutcomeLedger
open P94MolecularDirectRotationEvidence
open P94MolecularDirectRotationAuditLedger
open P94MolecularAuditedHybridTransaction
open P94MolecularAuditedTwistOutcomeAuditTrace
open P94MolecularCoordinateFrameLedger















structure CoordinateFrameRotationRequest where
  ledger : MolecularCoordinateFrameLedger
  assertion : MolecularDirectRotationAssertion Nat

inductive CoordinateFrameRotationOutcome where
  | accepted (request : CoordinateFrameRotationRequest)
  | refused (request : CoordinateFrameRotationRequest)

def CoordinateFrameRotationOutcome.request :
    CoordinateFrameRotationOutcome → CoordinateFrameRotationRequest
  | .accepted request => request
  | .refused request => request

def CoordinateFrameRotationOutcome.Correct (molecule : RawMolecule) :
    CoordinateFrameRotationOutcome → Prop
  | .accepted request =>
      request.assertion.ValidFor molecule request.ledger.toDirectRotationLedger
  | .refused request =>
      ¬request.assertion.ValidFor molecule request.ledger.toDirectRotationLedger

noncomputable def analyzeCoordinateFrameRotationRequest
    (molecule : RawMolecule) (request : CoordinateFrameRotationRequest) :
    CoordinateFrameRotationOutcome := by
  classical
  exact if request.assertion.ValidFor molecule request.ledger.toDirectRotationLedger then
      .accepted request
    else
      .refused request

theorem analyzeCoordinateFrameRotationRequest_request
    (molecule : RawMolecule) (request : CoordinateFrameRotationRequest) :
    (analyzeCoordinateFrameRotationRequest molecule request).request = request := by
  classical
  unfold analyzeCoordinateFrameRotationRequest
  split <;> rfl

theorem analyzeCoordinateFrameRotationRequest_correct
    (molecule : RawMolecule) (request : CoordinateFrameRotationRequest) :
    (analyzeCoordinateFrameRotationRequest molecule request).Correct molecule := by
  classical
  unfold analyzeCoordinateFrameRotationRequest
  split <;> simp_all [CoordinateFrameRotationOutcome.Correct]

def coordinateFrameRotationRequests (plan : MolecularCoordinateFrameHybridPlan) :
    List CoordinateFrameRotationRequest :=
  plan.twistLedgers.flatMap fun ledger =>
    ledger.assertions.map fun assertion => ⟨ledger, assertion⟩

theorem coordinateFrameRotationRequests_mem_iff
    (plan : MolecularCoordinateFrameHybridPlan)
    (request : CoordinateFrameRotationRequest) :
    request ∈ coordinateFrameRotationRequests plan ↔
      request.ledger ∈ plan.twistLedgers ∧
        request.assertion ∈ request.ledger.assertions := by
  cases request with
  | mk ledger assertion =>
      simp [coordinateFrameRotationRequests]

noncomputable def coordinateFrameRotationOutcomes
    (molecule : RawMolecule) (plan : MolecularCoordinateFrameHybridPlan) :
    List CoordinateFrameRotationOutcome :=
  (coordinateFrameRotationRequests plan).map
    (analyzeCoordinateFrameRotationRequest molecule)

theorem coordinateFrameRotationOutcomes_map_request
    (molecule : RawMolecule) (plan : MolecularCoordinateFrameHybridPlan) :
    (coordinateFrameRotationOutcomes molecule plan).map
        CoordinateFrameRotationOutcome.request = coordinateFrameRotationRequests plan := by
  classical
  simp [coordinateFrameRotationOutcomes, Function.comp_def,
    analyzeCoordinateFrameRotationRequest_request molecule]

theorem coordinateFrameRotationOutcomes_length
    (molecule : RawMolecule) (plan : MolecularCoordinateFrameHybridPlan) :
    (coordinateFrameRotationOutcomes molecule plan).length =
      (coordinateFrameRotationRequests plan).length := by
  simp [coordinateFrameRotationOutcomes]

theorem coordinateFrameRotationOutcomes_all_correct
    (molecule : RawMolecule) (plan : MolecularCoordinateFrameHybridPlan) :
    ∀ outcome ∈ coordinateFrameRotationOutcomes molecule plan,
      outcome.Correct molecule := by
  intro outcome present
  rcases List.mem_map.mp present with ⟨request, _requestPresent, rfl⟩
  exact analyzeCoordinateFrameRotationRequest_correct molecule request

theorem coordinateFrameRotationAccepted_mem_iff
    (molecule : RawMolecule) (plan : MolecularCoordinateFrameHybridPlan)
    (request : CoordinateFrameRotationRequest) :
    (.accepted request : CoordinateFrameRotationOutcome) ∈
        coordinateFrameRotationOutcomes molecule plan ↔
      request ∈ coordinateFrameRotationRequests plan ∧
        request.assertion.ValidFor molecule request.ledger.toDirectRotationLedger := by
  classical
  constructor
  · intro accepted
    rcases List.mem_map.mp accepted with ⟨candidate, candidatePresent, outcomeEq⟩
    by_cases valid : candidate.assertion.ValidFor molecule
        candidate.ledger.toDirectRotationLedger
    · have candidateEq : candidate = request := by
        simpa [analyzeCoordinateFrameRotationRequest, valid] using outcomeEq
      subst candidate
      exact ⟨candidatePresent, valid⟩
    · simp [analyzeCoordinateFrameRotationRequest, valid] at outcomeEq
  · rintro ⟨requestPresent, valid⟩
    exact List.mem_map.mpr
      ⟨request, requestPresent, by
        simp [analyzeCoordinateFrameRotationRequest, valid]⟩

theorem coordinateFrameRotationRefused_mem_iff
    (molecule : RawMolecule) (plan : MolecularCoordinateFrameHybridPlan)
    (request : CoordinateFrameRotationRequest) :
    (.refused request : CoordinateFrameRotationOutcome) ∈
        coordinateFrameRotationOutcomes molecule plan ↔
      request ∈ coordinateFrameRotationRequests plan ∧
        ¬request.assertion.ValidFor molecule request.ledger.toDirectRotationLedger := by
  classical
  constructor
  · intro refused
    rcases List.mem_map.mp refused with ⟨candidate, candidatePresent, outcomeEq⟩
    by_cases valid : candidate.assertion.ValidFor molecule
        candidate.ledger.toDirectRotationLedger
    · simp [analyzeCoordinateFrameRotationRequest, valid] at outcomeEq
    · have candidateEq : candidate = request := by
        simpa [analyzeCoordinateFrameRotationRequest, valid] using outcomeEq
      subst candidate
      exact ⟨candidatePresent, valid⟩
  · rintro ⟨requestPresent, invalid⟩
    exact List.mem_map.mpr
      ⟨request, requestPresent, by
        simp [analyzeCoordinateFrameRotationRequest, invalid]⟩

def PlanAcceptedMolecularDirectRotation
    (molecule : RawMolecule) (plan : MolecularCoordinateFrameHybridPlan)
    (ledger : MolecularCoordinateFrameLedger) (first second : Nat) : Prop :=
  ∃ assertion,
    (.accepted ⟨ledger, assertion⟩ : CoordinateFrameRotationOutcome) ∈
        coordinateFrameRotationOutcomes molecule plan ∧
      assertion.first = first ∧ assertion.second = second

theorem planAcceptedMolecularDirectRotation_iff
    (molecule : RawMolecule) (plan : MolecularCoordinateFrameHybridPlan)
    (ledger : MolecularCoordinateFrameLedger) (first second : Nat) :
    PlanAcceptedMolecularDirectRotation molecule plan ledger first second ↔
      ledger ∈ plan.twistLedgers ∧
        AcceptedMolecularDirectRotation molecule ledger.toDirectRotationLedger first second := by
  constructor
  · rintro ⟨assertion, accepted, firstEq, secondEq⟩
    rcases (coordinateFrameRotationAccepted_mem_iff molecule plan
      ⟨ledger, assertion⟩).mp accepted with ⟨requestPresent, valid⟩
    rcases (coordinateFrameRotationRequests_mem_iff plan
      ⟨ledger, assertion⟩).mp requestPresent with ⟨ledgerPresent, assertionPresent⟩
    exact ⟨ledgerPresent, assertion,
      (molecularDirectRotationAccepted_mem_iff molecule
        ledger.toDirectRotationLedger assertion).2 ⟨assertionPresent, valid⟩,
      firstEq, secondEq⟩
  · rintro ⟨ledgerPresent, assertion, accepted, firstEq, secondEq⟩
    rcases (molecularDirectRotationAccepted_mem_iff molecule
      ledger.toDirectRotationLedger assertion).mp accepted with
      ⟨assertionPresent, valid⟩
    have requestPresent : (⟨ledger, assertion⟩ : CoordinateFrameRotationRequest) ∈
        coordinateFrameRotationRequests plan :=
      (coordinateFrameRotationRequests_mem_iff plan ⟨ledger, assertion⟩).2
        ⟨ledgerPresent, assertionPresent⟩
    exact ⟨assertion,
      (coordinateFrameRotationAccepted_mem_iff molecule plan
        ⟨ledger, assertion⟩).2 ⟨requestPresent, valid⟩,
      firstEq, secondEq⟩

private theorem directedRotationPath_plan_audited
    (molecule : RawMolecule) (plan : MolecularCoordinateFrameHybridPlan)
    (ledger : MolecularCoordinateFrameLedger) (ledgerPresent : ledger ∈ plan.twistLedgers)
    {states : List Nat}
    (path : DirectedRotationPath
      (AcceptedMolecularDirectRotation molecule ledger.toDirectRotationLedger) states) :
    DirectedRotationPath
      (PlanAcceptedMolecularDirectRotation molecule plan ledger) states := by
  induction path with
  | singleton state => exact .singleton state
  | @cons first second rest direct tail inductionHypothesis =>
      rcases direct with forward | reverse
      · exact .cons
          (Or.inl ((planAcceptedMolecularDirectRotation_iff
            molecule plan ledger first second).2 ⟨ledgerPresent, forward⟩))
          inductionHypothesis
      · exact .cons
          (Or.inr ((planAcceptedMolecularDirectRotation_iff
            molecule plan ledger second first).2 ⟨ledgerPresent, reverse⟩))
          inductionHypothesis

theorem coordinateFrameHybridTwistAccepted_paths_plan_audited
    (premises : IndependentInOutPremises
      P94MolecularBicyclicFramework.ThetaFramework)
    (certified : CertifiedChemistryNormalizationResult)
    (plan : MolecularCoordinateFrameHybridPlan)
    (external : IndependentAmbiguousP94RingSelectionAuthority)
    (carbohydrateAuthority : IndependentCarbohydrateFiveRingAuthority)
    (input : CoordinateTwistInput Nat) (output : CoordinateTwistEvidence Nat)
    (outcomePresent : (.twistAccepted input output : HybridMolecularOutcome Nat) ∈
      auditedHybridMolecularOutcomes premises certified plan.toAuditedHybridLedgerPlan external
        carbohydrateAuthority) :
    ∃ ledger ∈ plan.twistLedgers,
      DirectedRotationPath
          (PlanAcceptedMolecularDirectRotation certified.result.parsed plan ledger)
          input.firstLeg ∧
        DirectedRotationPath
          (PlanAcceptedMolecularDirectRotation certified.result.parsed plan ledger)
          input.secondLeg := by
  rcases coordinateFrameHybridTwistAccepted_paths_audited premises certified plan external
      carbohydrateAuthority input output outcomePresent with
    ⟨ledger, ledgerPresent, firstPath, secondPath⟩
  exact ⟨ledger, ledgerPresent,
    directedRotationPath_plan_audited certified.result.parsed plan ledger ledgerPresent firstPath,
    directedRotationPath_plan_audited certified.result.parsed plan ledger ledgerPresent secondPath⟩

end BlueBookP94.P94MolecularCoordinateFrameRotationTransaction
end TetraStereo.OneCenter
