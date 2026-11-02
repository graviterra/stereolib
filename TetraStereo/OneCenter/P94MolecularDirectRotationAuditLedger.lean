import TetraStereo.OneCenter.P94MolecularDirectRotationEvidence

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP94.P94MolecularDirectRotationAuditLedger

open P94MolecularDirectRotationEvidence














inductive MolecularDirectRotationOutcome (State : Type*) where
  | accepted (assertion : MolecularDirectRotationAssertion State)
  | refused (assertion : MolecularDirectRotationAssertion State)
  deriving DecidableEq

def MolecularDirectRotationOutcome.request {State : Type*} :
    MolecularDirectRotationOutcome State → MolecularDirectRotationAssertion State
  | .accepted assertion => assertion
  | .refused assertion => assertion

def MolecularDirectRotationOutcome.Correct {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State) :
    MolecularDirectRotationOutcome State → Prop
  | .accepted assertion => assertion.ValidFor molecule ledger
  | .refused assertion => ¬assertion.ValidFor molecule ledger

noncomputable def auditMolecularDirectRotationAssertion
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State)
    (assertion : MolecularDirectRotationAssertion State) :
    MolecularDirectRotationOutcome State := by
  classical
  exact if assertion.ValidFor molecule ledger then
      .accepted assertion
    else
      .refused assertion

theorem auditMolecularDirectRotationAssertion_request
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State)
    (assertion : MolecularDirectRotationAssertion State) :
    (auditMolecularDirectRotationAssertion molecule ledger assertion).request = assertion := by
  classical
  unfold auditMolecularDirectRotationAssertion
  split <;> rfl

theorem auditMolecularDirectRotationAssertion_correct
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State)
    (assertion : MolecularDirectRotationAssertion State) :
    (auditMolecularDirectRotationAssertion molecule ledger assertion).Correct molecule ledger := by
  classical
  unfold auditMolecularDirectRotationAssertion
  split <;> simp_all [MolecularDirectRotationOutcome.Correct]

noncomputable def molecularDirectRotationOutcomes
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State) :
    List (MolecularDirectRotationOutcome State) :=
  ledger.assertions.map (auditMolecularDirectRotationAssertion molecule ledger)

theorem molecularDirectRotationOutcomes_map_request
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State) :
    (molecularDirectRotationOutcomes molecule ledger).map
        MolecularDirectRotationOutcome.request = ledger.assertions := by
  classical
  simp [molecularDirectRotationOutcomes, Function.comp_def,
    auditMolecularDirectRotationAssertion_request molecule ledger]

theorem molecularDirectRotationOutcomes_length
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State) :
    (molecularDirectRotationOutcomes molecule ledger).length = ledger.assertions.length := by
  simp [molecularDirectRotationOutcomes]

theorem molecularDirectRotationOutcomes_all_correct
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State) :
    ∀ outcome ∈ molecularDirectRotationOutcomes molecule ledger,
      outcome.Correct molecule ledger := by
  intro outcome present
  rcases List.mem_map.mp present with ⟨assertion, _assertionPresent, rfl⟩
  exact auditMolecularDirectRotationAssertion_correct molecule ledger assertion

theorem molecularDirectRotationAccepted_mem_iff
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State)
    (assertion : MolecularDirectRotationAssertion State) :
    (.accepted assertion : MolecularDirectRotationOutcome State) ∈
        molecularDirectRotationOutcomes molecule ledger ↔
      assertion ∈ ledger.assertions ∧ assertion.ValidFor molecule ledger := by
  classical
  constructor
  · intro accepted
    rcases List.mem_map.mp accepted with ⟨candidate, candidatePresent, outcomeEq⟩
    by_cases valid : candidate.ValidFor molecule ledger
    · have candidateEq : candidate = assertion := by
        simpa [auditMolecularDirectRotationAssertion, valid] using outcomeEq
      subst candidate
      exact ⟨candidatePresent, valid⟩
    · simp [auditMolecularDirectRotationAssertion, valid] at outcomeEq
  · rintro ⟨assertionPresent, valid⟩
    exact List.mem_map.mpr
      ⟨assertion, assertionPresent, by
        simp [auditMolecularDirectRotationAssertion, valid]⟩

theorem molecularDirectRotationRefused_mem_iff
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State)
    (assertion : MolecularDirectRotationAssertion State) :
    (.refused assertion : MolecularDirectRotationOutcome State) ∈
        molecularDirectRotationOutcomes molecule ledger ↔
      assertion ∈ ledger.assertions ∧ ¬assertion.ValidFor molecule ledger := by
  classical
  constructor
  · intro refused
    rcases List.mem_map.mp refused with ⟨candidate, candidatePresent, outcomeEq⟩
    by_cases valid : candidate.ValidFor molecule ledger
    · simp [auditMolecularDirectRotationAssertion, valid] at outcomeEq
    · have candidateEq : candidate = assertion := by
        simpa [auditMolecularDirectRotationAssertion, valid] using outcomeEq
      subst candidate
      exact ⟨candidatePresent, valid⟩
  · rintro ⟨assertionPresent, invalid⟩
    exact List.mem_map.mpr
      ⟨assertion, assertionPresent, by
        simp [auditMolecularDirectRotationAssertion, invalid]⟩

theorem rotationAboutMolecularSingleBond_iff_accepted_outcome
    {State : Type*} [DecidableEq State]
    (molecule : RawMolecule) (ledger : MolecularDirectRotationLedger State)
    (first second : State) :
    RotationAboutMolecularSingleBond molecule ledger first second ↔
      ∃ assertion,
        (.accepted assertion : MolecularDirectRotationOutcome State) ∈
            molecularDirectRotationOutcomes molecule ledger ∧
          assertion.first = first ∧ assertion.second = second := by
  constructor
  · rintro ⟨assertion, assertionPresent, firstEq, secondEq, valid⟩
    exact ⟨assertion,
      (molecularDirectRotationAccepted_mem_iff molecule ledger assertion).2
        ⟨assertionPresent, valid⟩,
      firstEq, secondEq⟩
  · rintro ⟨assertion, accepted, firstEq, secondEq⟩
    rcases (molecularDirectRotationAccepted_mem_iff molecule ledger assertion).1 accepted with
      ⟨assertionPresent, valid⟩
    exact ⟨assertion, assertionPresent, firstEq, secondEq, valid⟩

end BlueBookP94.P94MolecularDirectRotationAuditLedger
end TetraStereo.OneCenter
