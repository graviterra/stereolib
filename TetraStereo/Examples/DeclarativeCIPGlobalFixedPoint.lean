import TetraStereo.Examples.VS298OccurrenceEvaluatorCertificate
import TetraStereo.OneCenter.DeclarativeCIPOccurrenceRules456

set_option autoImplicit false

namespace TetraStereo.Examples.VS298

open OneCenter
open OneCenter.DeclarativeCIP
open OneCenter.DeclarativeCIP.ProductionOccurrenceRules456

/-!
# VS298 root-relative occurrence regression

The same physical stereocenter (atom 6) occurs twice under final center 1 with distinct incoming
frames.  Exhaustive production discovery retains them as distinct values of the actual
root-relative occurrence carrier, and the actual production occurrence evaluator assigns
opposite auxiliary senses (`R` and `S`).

The bounded production computations are split into small ordinary-kernel certificate modules.
No native evaluation tactic is used.
-/

/-- Reify each independently verified production fact at its exact exhaustive occurrence. -/
noncomputable def leftOccurrenceLabel : Label discovery :=
  labelOfOrdinaryFact discovery leftProductionOccurrence leftExpectedFact fuel state (by
    rw [leftProductionSourceExact]
    exact leftOccurrenceFact)

noncomputable def rightOccurrenceLabel : Label discovery :=
  labelOfOrdinaryFact discovery rightProductionOccurrence rightExpectedFact fuel state (by
    rw [rightProductionSourceExact]
    exact rightOccurrenceFact)

/-- A typed occurrence-state witness containing precisely the two verified auxiliary results.
This is deliberately called an evidence state, not a `CIPModel`: the production computations
below certify these two coordinates, while a global model claim additionally requires the full
declarative derivation equations at every discovered occurrence. -/
noncomputable def occurrenceEvidenceState : State discovery := fun occurrence =>
  if occurrence = leftProductionOccurrence then some leftOccurrenceLabel
  else if occurrence = rightProductionOccurrence then some rightOccurrenceLabel
  else none

@[simp] theorem occurrenceEvidenceState_left :
    occurrenceEvidenceState leftProductionOccurrence = some leftOccurrenceLabel := by
  simp [occurrenceEvidenceState]

@[simp] theorem occurrenceEvidenceState_right :
    occurrenceEvidenceState rightProductionOccurrence = some rightOccurrenceLabel := by
  have rightNeLeft : rightProductionOccurrence ≠ leftProductionOccurrence :=
    Ne.symm productionOccurrencesNe
  simp [occurrenceEvidenceState, rightNeLeft]

/-- The old production evaluator equations and the new occurrence-indexed coordinates refer to
the very same facts; this is the honest one-way evidence bridge used by the regression. -/
theorem verifiedProductionFacts_reifiedAtOccurrences :
    leftProductionOccurrence.sourceNode? = some leftSource ∧
      rightProductionOccurrence.sourceNode? = some rightSource ∧
      occurrenceFact? molecule fuel state leftSource = some leftOccurrenceLabel.fact ∧
      occurrenceFact? molecule fuel state rightSource = some rightOccurrenceLabel.fact ∧
      occurrenceEvidenceState leftProductionOccurrence = some leftOccurrenceLabel ∧
      occurrenceEvidenceState rightProductionOccurrence = some rightOccurrenceLabel := by
  exact ⟨leftProductionSourceExact, rightProductionSourceExact,
    by simpa [leftOccurrenceLabel] using leftOccurrenceFact,
    by simpa [rightOccurrenceLabel] using rightOccurrenceFact,
    occurrenceEvidenceState_left, occurrenceEvidenceState_right⟩

/-- Occurrence-level projection of the two verified label coordinates.  These are auxiliary
occurrences, so this theorem intentionally does not call them final-descriptor projections. -/
theorem occurrenceEvidenceDescriptorProjections :
    ((occurrenceEvidenceState leftProductionOccurrence).map
        (occurrenceSystem discovery fuel).descriptorOf,
      (occurrenceEvidenceState rightProductionOccurrence).map
        (occurrenceSystem discovery fuel).descriptorOf) =
        (some Descriptor.R, some Descriptor.S) := by
  simp [occurrenceSystem, leftOccurrenceLabel, rightOccurrenceLabel, labelOfOrdinaryFact,
    leftExpectedFact, rightExpectedFact, descriptorOfFact]

/-- One physical atom has two distinct exhaustive occurrence identities and verified opposite
production senses.  The evaluator equations are included in the statement, rather than merely
imported next to a theorem about literal expected-data fields. -/
theorem samePhysicalAtom_oppositeOccurrenceSenses :
    leftSource.atom = rightSource.atom ∧
      leftProductionOccurrence ≠ rightProductionOccurrence ∧
      occurrenceFact? molecule fuel state leftSource = some leftExpectedFact ∧
      occurrenceFact? molecule fuel state rightSource = some rightExpectedFact ∧
      leftExpectedFact.descriptor = .R ∧
      rightExpectedFact.descriptor = .S :=
  ⟨sameAtom, productionOccurrencesNe, leftOccurrenceFact, rightOccurrenceFact, rfl, rfl⟩

end TetraStereo.Examples.VS298
