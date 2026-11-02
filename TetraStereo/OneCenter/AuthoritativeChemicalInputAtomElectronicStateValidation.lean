import TetraStereo.OneCenter.AuthoritativeChemicalInputAtomElectronicStateEvidence

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInputWithAtomElectronicStates

/-!
# Exact validation of finite atom electronic-state annotations

`AuthoritativeChemicalInputWithAtomElectronicStates` is an untrusted finite data object: its atom
indices and inventory counts carry no proofs.  This module gives that object a single exact
certification boundary.  Acceptance means structural source validity, unique atom keys, canonical
reuse of each record in every retained directed endpoint context, and coverage of every retained
endpoint.  Rejection is classified by the corresponding four positive failure families.
-/

/-- Complete proposition checked before an untrusted finite atom-state input may drive analysis. -/
def CertificationReady
    (input : AuthoritativeChemicalInputWithAtomElectronicStates) : Prop :=
  input.StructurallyWellFormed ∧ input.CoversCanonicalIndividualDoubleBondEndpoints

/-- Exhaustive positive classification of certification failure. -/
def CertificationRefusal
    (input : AuthoritativeChemicalInputWithAtomElectronicStates) : Prop :=
  ¬ input.source.StructurallyWellFormed ∨
    ¬ (input.atomElectronicStates.map
      AuthoritativeChemicalInput.AromaticCanonicalAtomElectronicStateRecord.key).Nodup ∨
    (∃ record ∈ input.atomElectronicStates,
      ∃ partner,
        input.source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint
            record.atom partner ∧
          ¬ input.source.CanonicalAromaticCanonicalRule3EndpointElectronicInventory
            record.atom partner record.inventory) ∨
    (∃ endpoint partner,
      input.source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint endpoint partner ∧
        input.inventoryAt? endpoint = none)

/-- Readiness is decidable by finite reflection. -/
noncomputable def certificationReady?
    (input : AuthoritativeChemicalInputWithAtomElectronicStates) : Bool := by
  classical
  exact decide input.CertificationReady

@[simp] theorem certificationReady?_eq_true_iff
    (input : AuthoritativeChemicalInputWithAtomElectronicStates) :
    input.certificationReady? = true ↔ input.CertificationReady := by
  classical
  simp [certificationReady?]

/-- Failure of the complete certification proposition has exactly one of the explicit structural,
duplicate-key, inconsistent-record, or uncovered-endpoint witnesses. -/
theorem not_certificationReady_iff_refusal
    (input : AuthoritativeChemicalInputWithAtomElectronicStates) :
    ¬ input.CertificationReady ↔ input.CertificationRefusal := by
  classical
  unfold CertificationReady CertificationRefusal StructurallyWellFormed
    AuthoritativeChemicalInput.AromaticCanonicalAtomElectronicStateRecordsWellFormed
    CoversCanonicalIndividualDoubleBondEndpoints
  constructor
  · intro notReady
    by_cases sourceWellFormed : input.source.StructurallyWellFormed
    · by_cases uniqueKeys :
        (input.atomElectronicStates.map
          AuthoritativeChemicalInput.AromaticCanonicalAtomElectronicStateRecord.key).Nodup
      · by_cases recordsCanonical :
          ∀ record, record ∈ input.atomElectronicStates →
            ∀ partner,
              input.source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint
                  record.atom partner →
                input.source.CanonicalAromaticCanonicalRule3EndpointElectronicInventory
                  record.atom partner record.inventory
        · right
          right
          right
          have notCovered :
              ¬ ∀ endpoint partner,
                input.source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint
                    endpoint partner →
                  ∃ inventory, input.inventoryAt? endpoint = some inventory := by
            intro covered
            exact notReady ⟨⟨sourceWellFormed, uniqueKeys, recordsCanonical⟩, covered⟩
          push_neg at notCovered
          obtain ⟨endpoint, partner, directed, absent⟩ := notCovered
          refine ⟨endpoint, partner, directed, ?_⟩
          cases observed : input.inventoryAt? endpoint with
          | none => rfl
          | some inventory => exact False.elim (absent inventory observed)
        · right
          right
          left
          push_neg at recordsCanonical
          obtain ⟨record, present, partner, directed, notCanonical⟩ := recordsCanonical
          exact ⟨record, present, partner, directed, notCanonical⟩
      · right
        left
        exact uniqueKeys
    · left
      exact sourceWellFormed
  · rintro (sourceInvalid | duplicateKeys | inconsistent | uncovered)
    · rintro ⟨⟨sourceWellFormed, _recordsWellFormed⟩, _covered⟩
      exact sourceInvalid sourceWellFormed
    · rintro ⟨⟨_sourceWellFormed, uniqueKeys, _recordsCanonical⟩, _covered⟩
      exact duplicateKeys uniqueKeys
    · obtain ⟨record, present, partner, directed, notCanonical⟩ := inconsistent
      rintro ⟨⟨_sourceWellFormed, _uniqueKeys, recordsCanonical⟩, _covered⟩
      exact notCanonical (recordsCanonical record present partner directed)
    · obtain ⟨endpoint, partner, directed, absent⟩ := uncovered
      rintro ⟨_wellFormed, covered⟩
      obtain ⟨inventory, found⟩ := covered endpoint partner directed
      rw [absent] at found
      contradiction

@[simp] theorem certificationReady?_eq_false_iff_refusal
    (input : AuthoritativeChemicalInputWithAtomElectronicStates) :
    input.certificationReady? = false ↔ input.CertificationRefusal := by
  classical
  rw [Bool.eq_false_iff]
  simpa using input.not_certificationReady_iff_refusal

/-- Turn a successful validation proof into the proof-carrying input consumed by the analyzer. -/
def certifiedOf
    (input : AuthoritativeChemicalInputWithAtomElectronicStates)
    (ready : input.CertificationReady) :
    CertifiedAuthoritativeChemicalInputWithAtomElectronicStates where
  input := input
  structurallyWellFormed := ready.1
  coversCanonicalIndividualDoubleBondEndpoints := ready.2

/-- Exact certifier for untrusted finite atom electronic-state annotations. -/
noncomputable def certify?
    (input : AuthoritativeChemicalInputWithAtomElectronicStates) :
    Option CertifiedAuthoritativeChemicalInputWithAtomElectronicStates := by
  classical
  exact if ready : input.CertificationReady then
    some (input.certifiedOf ready)
  else
    none

@[simp] theorem certify?_isSome_iff_ready
    (input : AuthoritativeChemicalInputWithAtomElectronicStates) :
    input.certify?.isSome ↔ input.CertificationReady := by
  classical
  simp [certify?]

@[simp] theorem certify?_eq_none_iff_refusal
    (input : AuthoritativeChemicalInputWithAtomElectronicStates) :
    input.certify? = none ↔ input.CertificationRefusal := by
  classical
  rw [← input.not_certificationReady_iff_refusal]
  simp [certify?]

theorem certify?_eq_some_of_ready
    (input : AuthoritativeChemicalInputWithAtomElectronicStates)
    (ready : input.CertificationReady) :
    input.certify? = some (input.certifiedOf ready) := by
  classical
  simp [certify?, ready]

/-- Validate and, only on success, run the complete inventory-aware ordinary-double-bond
analyzer. -/
noncomputable def analyzeOrdinaryDoubleBonds?
    (input : AuthoritativeChemicalInputWithAtomElectronicStates)
    (carrierFuel : Nat)
    (viewAt : (atom : input.source.AromaticCanonicalAtom) →
      input.source.AromaticCanonicalDependencyView
        (input.source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    Option (List input.source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) := by
  classical
  exact if ready : input.CertificationReady then
    some ((input.certifiedOf ready).analyzeOrdinaryDoubleBonds carrierFuel viewAt)
  else
    none

@[simp] theorem analyzeOrdinaryDoubleBonds?_eq_none_iff_refusal
    (input : AuthoritativeChemicalInputWithAtomElectronicStates)
    (carrierFuel : Nat)
    (viewAt : (atom : input.source.AromaticCanonicalAtom) →
      input.source.AromaticCanonicalDependencyView
        (input.source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    input.analyzeOrdinaryDoubleBonds? carrierFuel viewAt = none ↔
      input.CertificationRefusal := by
  classical
  rw [← input.not_certificationReady_iff_refusal]
  simp [analyzeOrdinaryDoubleBonds?]

/-- On successful validation the public optional entry point returns exactly the already-certified
complete family analyzer. -/
theorem analyzeOrdinaryDoubleBonds?_eq_some_of_ready
    (input : AuthoritativeChemicalInputWithAtomElectronicStates)
    (ready : input.CertificationReady)
    (carrierFuel : Nat)
    (viewAt : (atom : input.source.AromaticCanonicalAtom) →
      input.source.AromaticCanonicalDependencyView
        (input.source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    input.analyzeOrdinaryDoubleBonds? carrierFuel viewAt =
      some ((input.certifiedOf ready).analyzeOrdinaryDoubleBonds carrierFuel viewAt) := by
  classical
  simp [analyzeOrdinaryDoubleBonds?, ready]

/-- After successful finite validation, membership is exactly the independent inventory-aware
canonical spatial judgment. -/
theorem mem_validatedAnalyzeOrdinaryDoubleBonds_iff_canonical
    (input : AuthoritativeChemicalInputWithAtomElectronicStates)
    (ready : input.CertificationReady)
    (carrierFuel : Nat)
    (viewAt : (atom : input.source.AromaticCanonicalAtom) →
      input.source.AromaticCanonicalDependencyView
        (input.source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (assignment :
      input.source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    assignment ∈ (input.certifiedOf ready).analyzeOrdinaryDoubleBonds carrierFuel viewAt ↔
      ∃ bond,
        input.source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalSpatialJudgment
          carrierFuel (input.certifiedOf ready).inventorySource bond
            (viewAt bond.left) (viewAt bond.right) assignment := by
  exact (input.certifiedOf ready).mem_analyzeOrdinaryDoubleBonds_iff_canonical
    carrierFuel viewAt assignment

/-- Successful validation transports the exhaustive unique-emission or explicit chemical-refusal
classification to every retained individual ordinary double bond. -/
theorem every_validatedIndividualDoubleBond_exact_success_or_refusal
    (input : AuthoritativeChemicalInputWithAtomElectronicStates)
    (ready : input.CertificationReady)
    (carrierFuel : Nat)
    (viewAt : (atom : input.source.AromaticCanonicalAtom) →
      input.source.AromaticCanonicalDependencyView
        (input.source.aromaticCanonicalRootOccurrence carrierFuel atom)) :
    ∀ bond ∈ input.source.aromaticCanonicalIndividualDoubleBondCarriers,
      (input.source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalReadiness
          carrierFuel (input.certifiedOf ready).inventorySource bond
            (viewAt bond.left) (viewAt bond.right) ∧
        ∃! assignment,
          assignment ∈ (input.certifiedOf ready).analyzeOrdinaryDoubleBonds
            carrierFuel viewAt ∧ assignment.bond = bond) ∨
      (input.source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalRefusal
          carrierFuel (input.certifiedOf ready).inventorySource bond
            (viewAt bond.left) (viewAt bond.right) ∧
        input.source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithElectronicInventory?
          carrierFuel (input.certifiedOf ready).inventorySource bond
            (viewAt bond.left) (viewAt bond.right) = none) := by
  exact (input.certifiedOf ready).every_individualDoubleBond_exact_success_or_refusal
    carrierFuel viewAt

/-- Every successfully returned analysis list is duplicate-free. -/
theorem analyzeOrdinaryDoubleBonds?_some_nodup
    (input : AuthoritativeChemicalInputWithAtomElectronicStates)
    (carrierFuel : Nat)
    (viewAt : (atom : input.source.AromaticCanonicalAtom) →
      input.source.AromaticCanonicalDependencyView
        (input.source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (assignments :
      List input.source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment)
    (computed : input.analyzeOrdinaryDoubleBonds? carrierFuel viewAt = some assignments) :
    assignments.Nodup := by
  classical
  unfold analyzeOrdinaryDoubleBonds? at computed
  split at computed
  next ready =>
    simp only [Option.some.injEq] at computed
    subst assignments
    exact (input.certifiedOf ready).analyzeOrdinaryDoubleBonds_nodup carrierFuel viewAt
  next notReady => contradiction

end AuthoritativeChemicalInputWithAtomElectronicStates
end TetraStereo.OneCenter
