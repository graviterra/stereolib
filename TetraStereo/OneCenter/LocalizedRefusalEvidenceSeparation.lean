import TetraStereo.OneCenter.Rule4bOccurrenceClassification
import TetraStereo.OneCenter.LocalizedUniversalDescriptorEvaluation
import TetraStereo.OneCenter.LocalizedUniversalReferencePipeline
import TetraStereo.OneCenter.LocalizedUniversalSemanticClosure

set_option autoImplicit false

/-!
# Localized refusal-evidence separation

The localized universal refusal theorem
(`universalDescriptor?_eq_none_iff_forall_not_declarativeUniversalDescriptor_of_derived`,
`LocalizedUniversalSemanticClosure`) says that the universal evaluator returns `none` exactly when
no declarative universal descriptor is derivable at the current dependency view.  That theorem is
operational: it deliberately does not distinguish

* a missing geometry / dependency / auxiliary-state fact, from
* a structurally non-bearing occurrence (a phantom or duplicate node), from
* a completed priority comparison that is genuinely tied, from
* an undifferentiated operational refusal (a deeper dependency or stage failed).

All four are `none` and therefore all four look the same at the descriptor API.  Treating the
first, third and fourth as chemical nonchirality would hide unknowns; treating them as `known
nonchiral` would convert missing evidence into a negative chemical verdict.  This module introduces
one shared, explicit evidence-status refinement and proves that the refinement is exactly what the
actual executables report.

## The shared refinement

`LocalizedEvidenceStatus Descriptor` has six constructors:

* `positive d` / `pseudoasymmetric d` -- actual recorded auxiliary evidence.  At the occurrence
  layer these are reached only from the uppercase and lowercase selector verdicts respectively
  (proved below).  At the universal layer `positive d` means only that a descriptor `d` was
  produced; `d : LocalizedAuxiliaryLabel` may itself be either uppercase (`chiral`) or lowercase
  (`pseudoasymmetric`), and this generic status does not classify the label's case;
* `structuralNonbearing` -- the independent structural route, proved from non-real provenance;
* `unavailableEvidence` -- a required geometry, dependency or auxiliary-state fact is absent;
* `completedPriorityTie` -- every dependency of the legacy occurrence evaluator completed and the
  ranking contains an adjacent `Ordering.eq` (this one cause *is* witnessed precisely);
* `operationalRefusal` -- some deeper stage refused; this constructor deliberately does **not**
  claim a specific cause (an incomplete ranking dependency, a missing downstream dependency, a
  preparation or assembly failure, etc. are all collapsed here).

`toClassification` and `descriptorOption` are the projections to the selection slot and to the
descriptor API.  There is deliberately no generic status-to-`OccurrenceChiralityClass` map: the
uppercase reading of `positive` is only valid for the occurrence-layer status, where it is proved
from the selector classifier, and is not asserted for universal labels.

## Occurrence layer

`occurrenceEvidenceStatus` refines `occurrenceSelectorChiralityClass` (the actual selector-facing
auxiliary-state observer) with `occurrenceLegacyStatus` (the actual legacy compiler observer).  We
prove the projection to the selector classification, the exact characterisations of the positive,
structural, tie and operational-refusal cases, and that missing geometry never becomes
`knownNonchiral`.

## Universal layer

`universalEvidenceStatus` is defined by the same case analysis as the actual executable
`universalDescriptorOutcome`: centre refusal, base refusal, Rule-3 preparation refusal, descriptor
assembly refusal and success.  We prove `descriptorOption (universalEvidenceStatus ...) =
universalDescriptor? ...`, connect positive statuses to declarative derivations and refusal
statuses to the unconditional no-derivation theorem, and show that a structurally non-bearing
occurrence is a proved alternative to unavailable evidence, not the same status.

## Pipeline projection

For `LocalizedUniversalReference.Input`, reading the status at the reference state's own dependency
view projects to `referenceState` itself (`referenceEvidenceStatus_descriptorOption`, through the
reference equation `referenceState_eq_universalDescriptor_referenceView`).  A refusal status there
is converted into the unconditional declarative non-derivation statement of
`LocalizedUniversalSemanticClosure`.

## Scope

Everything is relative to the existing localized formal input domain and its actual executables.
No chemical applicability claim is made.  `structuralNonbearing` means non-real canonical
provenance (a phantom or duplicate node), not a claim that a physical atom is achiral.
-/

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput

namespace LocalizedRefusalEvidence

/-! ## 1. The shared evidence-status refinement -/

/-- Explicit evidence status shared by the occurrence compiler layer and the universal descriptor
pipeline.  The refusal constructors are deliberately distinct: absence, structural non-bearing, a
witnessed completed tie and an undifferentiated operational refusal are different observations and
must not collapse into one another. -/
inductive LocalizedEvidenceStatus (Descriptor : Type) where
  /-- Actual recorded auxiliary evidence / a successful descriptor.  Its case is a property of the
  payload: at the occurrence layer this constructor is proved to come only from an uppercase
  selector verdict; at the universal layer the payload may be either an uppercase or a lowercase
  `LocalizedAuxiliaryLabel`. -/
  | positive (descriptor : Descriptor)
  /-- Actual lowercase (pseudoasymmetric) occurrence evidence. -/
  | pseudoasymmetric (descriptor : Descriptor)
  /-- Proved structural non-bearing: the occurrence node has non-real provenance. -/
  | structuralNonbearing
  /-- A required geometry, dependency or auxiliary-state fact is unavailable. -/
  | unavailableEvidence
  /-- Every legacy-evaluator dependency completed and the ranking contains a tie.  This cause is
  witnessed by `occurrenceLegacyRankingTie? = some true`. -/
  | completedPriorityTie
  /-- Some deeper stage refused.  No specific cause is claimed: this constructor covers missing
  downstream dependencies, incomplete ranking prerequisites, preparation/assembly failures and
  any other refusal not witnessed as `unavailableEvidence` or `completedPriorityTie`. -/
  | operationalRefusal
  deriving DecidableEq, Repr

namespace LocalizedEvidenceStatus

variable {Descriptor : Type}

/-- The `Option (Option Descriptor)` slot projection.  At the occurrence layer this is the
Rule-4b selection slot: `some (some d)` is an uppercase reading only because the occurrence-layer
`.positive d` is proved to come from the uppercase selector verdict.  At the universal layer
`.positive d` is a produced descriptor of arbitrary label case, so this projection is *not* an
uppercase classification there. -/
def toClassification : LocalizedEvidenceStatus Descriptor → Option (Option Descriptor)
  | positive descriptor => some (some descriptor)
  | pseudoasymmetric _ => some none
  | structuralNonbearing => some none
  | unavailableEvidence => none
  | completedPriorityTie => none
  | operationalRefusal => none

/-- The descriptor projection.  Only the two positive-evidence constructors carry a label. -/
def descriptorOption : LocalizedEvidenceStatus Descriptor → Option Descriptor
  | positive descriptor => some descriptor
  | pseudoasymmetric descriptor => some descriptor
  | structuralNonbearing => none
  | unavailableEvidence => none
  | completedPriorityTie => none
  | operationalRefusal => none

@[simp] theorem toClassification_positive (descriptor : Descriptor) :
    toClassification (positive descriptor) = some (some descriptor) := rfl

@[simp] theorem toClassification_pseudoasymmetric (descriptor : Descriptor) :
    toClassification (pseudoasymmetric descriptor) = some none := rfl

@[simp] theorem toClassification_structuralNonbearing :
    toClassification (structuralNonbearing : LocalizedEvidenceStatus Descriptor) = some none := rfl

@[simp] theorem toClassification_unavailableEvidence :
    toClassification (unavailableEvidence : LocalizedEvidenceStatus Descriptor) = none := rfl

@[simp] theorem toClassification_completedPriorityTie :
    toClassification (completedPriorityTie : LocalizedEvidenceStatus Descriptor) = none := rfl

@[simp] theorem toClassification_operationalRefusal :
    toClassification (operationalRefusal : LocalizedEvidenceStatus Descriptor) = none := rfl

@[simp] theorem descriptorOption_positive (descriptor : Descriptor) :
    descriptorOption (positive descriptor) = some descriptor := rfl

@[simp] theorem descriptorOption_pseudoasymmetric (descriptor : Descriptor) :
    descriptorOption (pseudoasymmetric descriptor) = some descriptor := rfl

@[simp] theorem descriptorOption_structuralNonbearing :
    descriptorOption (structuralNonbearing : LocalizedEvidenceStatus Descriptor) = none := rfl

@[simp] theorem descriptorOption_unavailableEvidence :
    descriptorOption (unavailableEvidence : LocalizedEvidenceStatus Descriptor) = none := rfl

@[simp] theorem descriptorOption_completedPriorityTie :
    descriptorOption (completedPriorityTie : LocalizedEvidenceStatus Descriptor) = none := rfl

@[simp] theorem descriptorOption_operationalRefusal :
    descriptorOption (operationalRefusal : LocalizedEvidenceStatus Descriptor) = none := rfl

/-- A descriptor refusal is exactly one of the three operational refusal constructors (the
structural route is deliberately not a descriptor refusal status: it is a separate proved
alternative). -/
theorem toClassification_eq_none_iff (status : LocalizedEvidenceStatus Descriptor) :
    toClassification status = none ↔
      status = unavailableEvidence ∨ status = completedPriorityTie ∨
        status = operationalRefusal := by
  cases status <;> simp [toClassification]

/-- A value in the `some none` slot is either actual lowercase evidence or the structural route. -/
theorem toClassification_eq_some_none_iff (status : LocalizedEvidenceStatus Descriptor) :
    toClassification status = some none ↔
      (∃ descriptor, status = pseudoasymmetric descriptor) ∨
        status = structuralNonbearing := by
  cases status <;> simp [toClassification]

/-- A descriptor slot is occupied exactly by positive or pseudoasymmetric evidence. -/
theorem toClassification_eq_some_some_iff (status : LocalizedEvidenceStatus Descriptor)
    (descriptor : Descriptor) :
    toClassification status = some (some descriptor) ↔ status = positive descriptor := by
  cases status <;> simp [toClassification]

/-- The descriptor projection is empty exactly for the structural route and the three operational
refusal statuses. -/
theorem descriptorOption_eq_none_iff (status : LocalizedEvidenceStatus Descriptor) :
    descriptorOption status = none ↔
      status = structuralNonbearing ∨ status = unavailableEvidence ∨
        status = completedPriorityTie ∨ status = operationalRefusal := by
  cases status <;> simp [descriptorOption]

/-- A descriptor is carried exactly by positive or pseudoasymmetric evidence. -/
theorem descriptorOption_eq_some_iff (status : LocalizedEvidenceStatus Descriptor)
    (descriptor : Descriptor) :
    descriptorOption status = some descriptor ↔
      status = positive descriptor ∨ status = pseudoasymmetric descriptor := by
  cases status <;> simp [descriptorOption]

/-- Any of the three operational refusal statuses projects to no descriptor. -/
theorem descriptorOption_eq_none_of_refusal (status : LocalizedEvidenceStatus Descriptor)
    (h : status = unavailableEvidence ∨ status = completedPriorityTie ∨
      status = operationalRefusal) :
    descriptorOption status = none := by
  rcases h with h | h | h <;> rw [h] <;> rfl

/-- The structural route is not an operational refusal: the two are distinct constructors, so a
missing geometry can never be silently relabelled as structural non-bearing. -/
theorem structuralNonbearing_ne_unavailableEvidence :
    (structuralNonbearing : LocalizedEvidenceStatus Descriptor) ≠ .unavailableEvidence := by
  intro h
  cases h

/-- A completed tie is not an undifferentiated operational refusal: the tie constructor carries a
witnessed completed comparison, whereas the refusal constructor carries no cause claim. -/
theorem completedPriorityTie_ne_operationalRefusal :
    (completedPriorityTie : LocalizedEvidenceStatus Descriptor) ≠ .operationalRefusal := by
  intro h
  cases h

end LocalizedEvidenceStatus

open LocalizedEvidenceStatus

/-! ## 2. The occurrence-layer observer

The selector-facing classifier `occurrenceSelectorChiralityClass` is the honest auxiliary-state
observer.  When it refuses a real-atom occurrence, the legacy compiler status
`occurrenceLegacyStatus` tells us why: a completed ranking tie, a missing structural prerequisite,
or a deeper operational refusal whose specific cause is not claimed here.  The shared status
records exactly that distinction. -/

/-- Shared evidence status of one occurrence, derived from the actual selector observer and the
actual legacy compiler observer. -/
def occurrenceEvidenceStatus (mol : RawMolecule) (fuel : ℕ)
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor) :
    LocalizedEvidenceStatus RS :=
  match occurrenceSelectorChiralityClass state cursor with
  | .uppercaseChiral descriptor => .positive descriptor
  | .pseudoasymmetric descriptor => .pseudoasymmetric descriptor
  | .knownNonchiral => .structuralNonbearing
  | .unavailable =>
      match occurrenceLegacyStatus mol fuel state cursor.node with
      | .fact _ => .unavailableEvidence
      | .completedRankingTie => .completedPriorityTie
      | .refused =>
          if occurrenceTetrahedralCandidate? mol cursor.node = none ∨
              occurrenceLigandFrame? mol cursor.node = none then
            .unavailableEvidence
          else
            .operationalRefusal

/-- The selector-facing `Option (Option)` classification is the projection of the selector class.
This definitional bridge is what lets the shared status project without unfolding the evidence
resolver. -/
theorem occurrenceSelectorChiralityClassification?_eq_toOptionOption
    (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor) :
    occurrenceSelectorChiralityClassification? state cursor =
      OccurrenceChiralityClass.toOptionOption
        (occurrenceSelectorChiralityClass state cursor) := rfl

/-- **Projection to the selector classification.**  The shared refinement changes no selector
verdict: positive evidence is `some (some d)`, lowercase or structural evidence is `some none`, and
every refusal cause is `none`. -/
theorem toClassification_occurrenceEvidenceStatus
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor) :
    (occurrenceEvidenceStatus mol fuel state cursor).toClassification =
      occurrenceSelectorChiralityClassification? state cursor := by
  unfold occurrenceEvidenceStatus
  rw [occurrenceSelectorChiralityClassification?_eq_toOptionOption state cursor]
  cases hClass : occurrenceSelectorChiralityClass state cursor with
  | uppercaseChiral descriptor => rfl
  | pseudoasymmetric descriptor => rfl
  | knownNonchiral => rfl
  | unavailable =>
      cases hStatus : occurrenceLegacyStatus mol fuel state cursor.node with
      | fact fact => rfl
      | completedRankingTie => rfl
      | refused =>
          by_cases hGeometry : occurrenceTetrahedralCandidate? mol cursor.node = none ∨
              occurrenceLigandFrame? mol cursor.node = none
          · simp [hGeometry]
          · simp [hGeometry]

/-- **Positive evidence is actual selector evidence.**  The positive constructor is reachable only
from an `uppercaseChiral` selector verdict, which in turn requires an actual uppercase auxiliary
fact at a real-atom occurrence. -/
theorem occurrenceEvidenceStatus_eq_positive_iff
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor) (descriptor : RS) :
    occurrenceEvidenceStatus mol fuel state cursor = .positive descriptor ↔
      occurrenceSelectorChiralityClass state cursor = .uppercaseChiral descriptor := by
  unfold occurrenceEvidenceStatus
  cases hClass : occurrenceSelectorChiralityClass state cursor with
  | uppercaseChiral found => simp
  | pseudoasymmetric found => simp
  | knownNonchiral => simp
  | unavailable =>
      cases hStatus : occurrenceLegacyStatus mol fuel state cursor.node with
      | fact fact => simp
      | completedRankingTie => simp
      | refused =>
          by_cases hGeometry : occurrenceTetrahedralCandidate? mol cursor.node = none ∨
              occurrenceLigandFrame? mol cursor.node = none
          · simp [hGeometry]
          · simp [hGeometry]

/-- **A positive shared status carries actual state evidence.** -/
theorem occurrenceEvidenceStatus_positive_source
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor) (descriptor : RS)
    (h : occurrenceEvidenceStatus mol fuel state cursor = .positive descriptor) :
    cursor.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom ∧
      ∃ fact, state.factAt? cursor.node = some fact ∧
        fact.uppercase = true ∧ fact.descriptor = descriptor :=
  (occurrenceSelectorChiralityClass_eq_uppercaseChiral_iff state cursor descriptor).mp
    ((occurrenceEvidenceStatus_eq_positive_iff mol fuel state cursor descriptor).mp h)

/-- Lowercase evidence is actual selector evidence too. -/
theorem occurrenceEvidenceStatus_eq_pseudoasymmetric_iff
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor) (descriptor : RS) :
    occurrenceEvidenceStatus mol fuel state cursor = .pseudoasymmetric descriptor ↔
      occurrenceSelectorChiralityClass state cursor = .pseudoasymmetric descriptor := by
  unfold occurrenceEvidenceStatus
  cases hClass : occurrenceSelectorChiralityClass state cursor with
  | uppercaseChiral found => simp
  | pseudoasymmetric found => simp
  | knownNonchiral => simp
  | unavailable =>
      cases hStatus : occurrenceLegacyStatus mol fuel state cursor.node with
      | fact fact => simp
      | completedRankingTie => simp
      | refused =>
          by_cases hGeometry : occurrenceTetrahedralCandidate? mol cursor.node = none ∨
              occurrenceLigandFrame? mol cursor.node = none
          · simp [hGeometry]
          · simp [hGeometry]

/-- **Structural non-bearing is exactly non-real provenance.**  It is the independent structural
route, and no absence of evidence can reach it. -/
theorem occurrenceEvidenceStatus_eq_structuralNonbearing_iff
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor) :
    occurrenceEvidenceStatus mol fuel state cursor = .structuralNonbearing ↔
      cursor.node.provenance ≠ RawMolecule.CanonicalNodeProvenance.realAtom := by
  unfold occurrenceEvidenceStatus
  cases hClass : occurrenceSelectorChiralityClass state cursor with
  | uppercaseChiral descriptor =>
      have hProvenance :=
        ((occurrenceSelectorChiralityClass_eq_uppercaseChiral_iff
          state cursor descriptor).mp hClass).1
      simp [hProvenance]
  | pseudoasymmetric descriptor =>
      have hProvenance :=
        ((occurrenceSelectorChiralityClass_eq_pseudoasymmetric_iff
          state cursor descriptor).mp hClass).1
      simp [hProvenance]
  | knownNonchiral =>
      have hNonReal :=
        (occurrenceSelectorChiralityClass_eq_knownNonchiral_iff state cursor).mp hClass
      simp [hNonReal]
  | unavailable =>
      have hProvenance :=
        ((occurrenceSelectorChiralityClass_eq_unavailable_iff state cursor).mp hClass).1
      cases hStatus : occurrenceLegacyStatus mol fuel state cursor.node with
      | fact fact => simp [hProvenance]
      | completedRankingTie => simp [hProvenance]
      | refused =>
          by_cases hGeometry : occurrenceTetrahedralCandidate? mol cursor.node = none ∨
              occurrenceLigandFrame? mol cursor.node = none
          · simp [hGeometry, hProvenance]
          · simp [hGeometry, hProvenance]

/-- Structural non-bearing is a proved alternative, reachable from the actual structural route. -/
theorem occurrenceEvidenceStatus_eq_structuralNonbearing_of_nonReal
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor)
    (hNonReal : cursor.node.provenance ≠
      RawMolecule.CanonicalNodeProvenance.realAtom) :
    occurrenceEvidenceStatus mol fuel state cursor = .structuralNonbearing :=
  (occurrenceEvidenceStatus_eq_structuralNonbearing_iff mol fuel state cursor).mpr hNonReal

/-- **A genuinely completed tie is exactly a legacy completed-ranking-tie status at a selector
refusal.**  This is the derived tie/refusal distinction, not an assumed outcome. -/
theorem occurrenceEvidenceStatus_eq_completedPriorityTie_iff
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor) :
    occurrenceEvidenceStatus mol fuel state cursor = .completedPriorityTie ↔
      occurrenceSelectorChiralityClass state cursor = .unavailable ∧
        occurrenceLegacyStatus mol fuel state cursor.node = .completedRankingTie := by
  unfold occurrenceEvidenceStatus
  cases hClass : occurrenceSelectorChiralityClass state cursor with
  | uppercaseChiral descriptor => simp
  | pseudoasymmetric descriptor => simp
  | knownNonchiral => simp
  | unavailable =>
      cases hStatus : occurrenceLegacyStatus mol fuel state cursor.node with
      | fact fact => simp
      | completedRankingTie => simp
      | refused =>
          by_cases hGeometry : occurrenceTetrahedralCandidate? mol cursor.node = none ∨
              occurrenceLigandFrame? mol cursor.node = none
          · simp [hGeometry]
          · simp [hGeometry]

/-- A completed tie is certified by the actual ranking-tie detector, and the legacy evaluator
refused exactly because of it. -/
theorem occurrenceEvidenceStatus_completedPriorityTie_certificate
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor)
    (h : occurrenceEvidenceStatus mol fuel state cursor = .completedPriorityTie) :
    legacyOccurrenceFact? mol fuel state cursor.node = none ∧
      occurrenceLegacyRankingTie? mol fuel state cursor.node = some true := by
  have hStatus :=
    ((occurrenceEvidenceStatus_eq_completedPriorityTie_iff mol fuel state cursor).mp h).2
  exact (occurrenceLegacyStatus_eq_completedRankingTie_iff
    mol fuel state cursor.node).mp hStatus

/-- **An operational refusal is exactly a legacy refusal with the basic atom/tetrahedral and
four-ligand prerequisites present.**  This is as far as the observed data supports the claim: the
legacy status is `refused`, which may mean either a missing deeper ranking dependency or a
completed ranking, and no cause beyond the two basic prerequisites is asserted.  The tie status is
separated from this by construction: a tie requires `occurrenceLegacyStatus = completedRankingTie`
while this status requires `refused`. -/
theorem occurrenceEvidenceStatus_eq_operationalRefusal_iff
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor) :
    occurrenceEvidenceStatus mol fuel state cursor = .operationalRefusal ↔
      occurrenceSelectorChiralityClass state cursor = .unavailable ∧
        occurrenceLegacyStatus mol fuel state cursor.node = .refused ∧
          occurrenceTetrahedralCandidate? mol cursor.node ≠ none ∧
            occurrenceLigandFrame? mol cursor.node ≠ none := by
  unfold occurrenceEvidenceStatus
  cases hClass : occurrenceSelectorChiralityClass state cursor with
  | uppercaseChiral descriptor => simp
  | pseudoasymmetric descriptor => simp
  | knownNonchiral => simp
  | unavailable =>
      cases hStatus : occurrenceLegacyStatus mol fuel state cursor.node with
      | fact fact => simp
      | completedRankingTie => simp
      | refused =>
          by_cases hCandidate : occurrenceTetrahedralCandidate? mol cursor.node = none
          · simp [hCandidate]
          · by_cases hFrame : occurrenceLigandFrame? mol cursor.node = none
            · simp [hCandidate, hFrame]
            · simp [hCandidate, hFrame]

/-- A tie and an undifferentiated operational refusal can never be the same observation: the
legacy observer cannot be both `completedRankingTie` and `refused`. -/
theorem occurrenceEvidenceStatus_completedPriorityTie_ne_operationalRefusal
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor)
    (hTie : occurrenceEvidenceStatus mol fuel state cursor = .completedPriorityTie) :
    occurrenceEvidenceStatus mol fuel state cursor ≠ .operationalRefusal := by
  intro hRefusal
  have hTieStatus :=
    (occurrenceEvidenceStatus_eq_completedPriorityTie_iff mol fuel state cursor).mp hTie
  have hRefusalStatus :=
    (occurrenceEvidenceStatus_eq_operationalRefusal_iff mol fuel state cursor).mp hRefusal
  rw [hTieStatus.2] at hRefusalStatus
  cases hRefusalStatus.2.1

/-- A refusal status is always a selector refusal; it never fabricates a selector verdict. -/
theorem occurrenceEvidenceStatus_eq_unavailableEvidence_selector_unavailable
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor)
    (h : occurrenceEvidenceStatus mol fuel state cursor = .unavailableEvidence) :
    occurrenceSelectorChiralityClass state cursor = .unavailable := by
  unfold occurrenceEvidenceStatus at h
  cases hClass : occurrenceSelectorChiralityClass state cursor with
  | uppercaseChiral descriptor => simp [hClass] at h
  | pseudoasymmetric descriptor => simp [hClass] at h
  | knownNonchiral => simp [hClass] at h
  | unavailable => rfl

/-- An unavailable-evidence status is produced when the selector refuses and the legacy compiler
recorded some fact: the missing dependency is the auxiliary-state fact itself. -/
theorem occurrenceEvidenceStatus_eq_unavailableEvidence_of_selector_unavailable_of_legacy_fact
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor)
    (hClass : occurrenceSelectorChiralityClass state cursor = .unavailable)
    (hFact : ∃ fact, occurrenceLegacyStatus mol fuel state cursor.node = .fact fact) :
    occurrenceEvidenceStatus mol fuel state cursor = .unavailableEvidence := by
  rcases hFact with ⟨fact, hFact⟩
  unfold occurrenceEvidenceStatus
  simp [hClass, hFact]

/-- An unavailable-evidence status is produced when the selector refuses, the legacy compiler
refused, and the atom/tetrahedral prerequisite is absent. -/
theorem occurrenceEvidenceStatus_eq_unavailableEvidence_of_selector_unavailable_of_refused_of_candidate_none
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor)
    (hClass : occurrenceSelectorChiralityClass state cursor = .unavailable)
    (hRefused : occurrenceLegacyStatus mol fuel state cursor.node = .refused)
    (hNone : occurrenceTetrahedralCandidate? mol cursor.node = none) :
    occurrenceEvidenceStatus mol fuel state cursor = .unavailableEvidence := by
  unfold occurrenceEvidenceStatus
  simp [hClass, hRefused, hNone]

/-- An unavailable-evidence status is produced when the selector refuses, the legacy compiler
refused, and the four-ligand frame is absent. -/
theorem occurrenceEvidenceStatus_eq_unavailableEvidence_of_selector_unavailable_of_refused_of_frame_none
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor)
    (hClass : occurrenceSelectorChiralityClass state cursor = .unavailable)
    (hRefused : occurrenceLegacyStatus mol fuel state cursor.node = .refused)
    (hNone : occurrenceLigandFrame? mol cursor.node = none) :
    occurrenceEvidenceStatus mol fuel state cursor = .unavailableEvidence := by
  unfold occurrenceEvidenceStatus
  simp [hClass, hRefused, hNone]

/-- An operational refusal is produced exactly when the selector refuses, the legacy compiler
refuses, and both basic structural prerequisites are present.  No deeper cause is claimed. -/
theorem occurrenceEvidenceStatus_eq_operationalRefusal_of_selector_unavailable_of_refused_of_geometry
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor)
    (hClass : occurrenceSelectorChiralityClass state cursor = .unavailable)
    (hRefused : occurrenceLegacyStatus mol fuel state cursor.node = .refused)
    (hCandidate : occurrenceTetrahedralCandidate? mol cursor.node ≠ none)
    (hFrame : occurrenceLigandFrame? mol cursor.node ≠ none) :
    occurrenceEvidenceStatus mol fuel state cursor = .operationalRefusal :=
  (occurrenceEvidenceStatus_eq_operationalRefusal_iff mol fuel state cursor).mpr
    ⟨hClass, hRefused, hCandidate, hFrame⟩

/-- A completed tie is produced exactly when the selector refuses and the legacy compiler records
a completed ranking tie. -/
theorem occurrenceEvidenceStatus_eq_completedPriorityTie_of_selector_unavailable_of_legacy_tie
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor)
    (hClass : occurrenceSelectorChiralityClass state cursor = .unavailable)
    (hTie : occurrenceLegacyStatus mol fuel state cursor.node = .completedRankingTie) :
    occurrenceEvidenceStatus mol fuel state cursor = .completedPriorityTie :=
  (occurrenceEvidenceStatus_eq_completedPriorityTie_iff mol fuel state cursor).mpr
    ⟨hClass, hTie⟩

/-- **Missing evidence is never a nonchirality verdict.**  An unavailable-evidence status projects
to `none`, not to `some none`; the selector can never read it as `knownNonchiral`. -/
theorem occurrenceEvidenceStatus_unavailableEvidence_toClassification
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor)
    (h : occurrenceEvidenceStatus mol fuel state cursor = .unavailableEvidence) :
    (occurrenceEvidenceStatus mol fuel state cursor).toClassification = none := by
  rw [toClassification_occurrenceEvidenceStatus]
  have hClass :=
    occurrenceEvidenceStatus_eq_unavailableEvidence_selector_unavailable
      mol fuel state cursor h
  exact (occurrenceSelectorChiralityClassification?_eq_none_iff state cursor).mpr
    ((occurrenceSelectorChiralityClass_eq_unavailable_iff state cursor).mp hClass)

/-- **Structural non-bearing is a definite alternative.**  It projects to `some none`, the existing
definite nonchiral slot, and is not converted into an operational refusal. -/
theorem occurrenceEvidenceStatus_structuralNonbearing_toClassification
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor)
    (h : occurrenceEvidenceStatus mol fuel state cursor = .structuralNonbearing) :
    (occurrenceEvidenceStatus mol fuel state cursor).toClassification = some none := by
  rw [toClassification_occurrenceEvidenceStatus]
  have hNonReal :=
    (occurrenceEvidenceStatus_eq_structuralNonbearing_iff mol fuel state cursor).mp h
  exact (occurrenceSelectorChiralityClassification?_eq_some_none_iff state cursor).mpr
    (Or.inl hNonReal)

/-! ## 3. Sufficient structural inputs: the status partition is complete

The legacy occurrence evaluator computes
`atom`, `parity`, `frame`, `sort`, `positions`, `comparison`, then applies the strictness gate.
If all six dependencies are available and the completed ranking has no adjacent tie, the
evaluator is productive.  This is derived here from the actual do-block; it is not assumed.  It
implies that, under those sufficient inputs, the occurrence status can be neither a completed tie
nor an operational refusal. -/

/-- **Productivity of the legacy evaluator under sufficient structural inputs.**  If the atom,
tetrahedral parity, ligand frame, ranking, position lookup and adjacent-comparison traversal all
succeed and no adjacent ordering is `eq`, then `legacyOccurrenceFact?` returns a fact. -/
theorem legacyOccurrenceFact?_exists_of_sufficient_inputs
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor)
    (spec : AtomSpec) (parity : TetrahedralInputParity)
    (roots : List CanonicalRerootCursor)
    (sorted : List CanonicalRerootCursor × ℕ)
    (compared : List (OccurrenceComparedPair mol state fuel)) (positions : List ℕ)
    (hAtom : mol.atomAt? cursor.node.atom = some spec)
    (hParity : spec.tetrahedral? = some parity)
    (hFrame : occurrenceLigandFrame? mol cursor.node = some roots)
    (hSorted : sortOccurrencesTracked? mol state fuel roots = some sorted)
    (hCompared : compareOccurrenceAdjacentPairs? mol state fuel sorted.1 = some compared)
    (hPositions : sorted.1.mapM (fun inner =>
      ((mol.ligandsWithLonePair cursor.node.atom).zipIdx.find?
        fun entry => entry.1 == inner.node.atom).map Prod.snd) = some positions)
    (hNoTie : (compared.map (fun comparison => comparison.decision)).all
      (fun decision => decision.ordering != Ordering.eq) = true) :
    ∃ fact, legacyOccurrenceFact? mol fuel state cursor.node = some fact := by
  -- Choose the exact fact that the do-block constructs on the success branch.  This mirrors the
  -- kernel-green production direction of `LegacyOrdinaryFactClauses.production_eq`.
  refine ⟨{ key := canonicalOccurrenceKey cursor.node
            atom := cursor.node.atom
            descriptor := RawMolecule.descriptorOfParity parity
              (RawMolecule.permutationIsEven positions)
            uppercase :=
              ((compared.map (fun comparison => comparison.decision)).filter
                (fun decision => decision.pseudo)).length % 2 == 0
            priorityPositions := positions }, ?_⟩
  -- With all six dependencies present, the only remaining side condition of the actual do-block
  -- is its strictness gate, which `simp` reflects into the universal form of `List.all`.
  simp [legacyOccurrenceFact?, hAtom, hParity, hFrame, hSorted, hPositions, hCompared]
  intro comparison member
  have decisionMember : comparison.decision ∈
      compared.map (fun entry => entry.decision) :=
    List.mem_map.mpr ⟨comparison, member, rfl⟩
  simpa using (List.all_eq_true.mp hNoTie) comparison.decision decisionMember

/-- **The tie/refusal split is complete under sufficient structural inputs and no tie.**  The
completed-tie and operational-refusal statuses are both impossible: the compiler is productive, so
the legacy observer is `.fact`, hence neither the witnessed tie branch nor the refusal branch is
observed.  This does not claim that a completed no-tie ranking is the *only* possible cause of a
refusal in the absence of these hypotheses; it derives non-refusal from the sufficient inputs. -/
theorem occurrenceEvidenceStatus_no_tie_no_operationalRefusal_of_sufficient_inputs
    (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (cursor : CanonicalRerootCursor)
    (spec : AtomSpec) (parity : TetrahedralInputParity)
    (roots : List CanonicalRerootCursor)
    (sorted : List CanonicalRerootCursor × ℕ)
    (compared : List (OccurrenceComparedPair mol state fuel)) (positions : List ℕ)
    (hAtom : mol.atomAt? cursor.node.atom = some spec)
    (hParity : spec.tetrahedral? = some parity)
    (hFrame : occurrenceLigandFrame? mol cursor.node = some roots)
    (hSorted : sortOccurrencesTracked? mol state fuel roots = some sorted)
    (hCompared : compareOccurrenceAdjacentPairs? mol state fuel sorted.1 = some compared)
    (hPositions : sorted.1.mapM (fun inner =>
      ((mol.ligandsWithLonePair cursor.node.atom).zipIdx.find?
        fun entry => entry.1 == inner.node.atom).map Prod.snd) = some positions)
    (hNoTie : (compared.map (fun comparison => comparison.decision)).all
      (fun decision => decision.ordering != Ordering.eq) = true) :
    occurrenceEvidenceStatus mol fuel state cursor ≠ .completedPriorityTie ∧
      occurrenceEvidenceStatus mol fuel state cursor ≠ .operationalRefusal := by
  rcases legacyOccurrenceFact?_exists_of_sufficient_inputs mol fuel state cursor
    spec parity roots sorted compared positions hAtom hParity hFrame hSorted hCompared
    hPositions hNoTie with ⟨fact, hFact⟩
  have hStatusFact :
      occurrenceLegacyStatus mol fuel state cursor.node = .fact fact :=
    (occurrenceLegacyStatus_eq_fact_iff mol fuel state cursor.node fact).mpr hFact
  unfold occurrenceEvidenceStatus
  cases hClass : occurrenceSelectorChiralityClass state cursor with
  | uppercaseChiral descriptor => simp
  | pseudoasymmetric descriptor => simp
  | knownNonchiral => simp
  | unavailable => simp [hStatusFact]

/-! ## 4. The universal-layer observer

`universalEvidenceStatus` follows the executable `universalDescriptorOutcome` branch for branch.
A missing centre is split by provenance: real provenance is unavailable evidence, non-real
provenance is the proved structural route.  A missing four-ligand base is unavailable geometry.  A
Rule-3 preparation refusal or a descriptor-assembly refusal is an undifferentiated operational
refusal: the executable does not expose which downstream dependency, cycle/planarity check or
assembly stage failed, so the status does not claim one.  Success is recorded evidence carrying the
actual label.  The completed-tie constructor is not observable at this layer. -/

/-- Shared evidence status of the universal descriptor pipeline. -/
def universalEvidenceStatus (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    LocalizedEvidenceStatus LocalizedAuxiliaryLabel :=
  match input.localizedOccurrenceDescriptorCenter? target with
  | none =>
      if target.1.node.provenance = OfficialCIPNodeProvenance.realAtom then
        .unavailableEvidence
      else
        .structuralNonbearing
  | some center =>
      match input.localizedNoDoubleFourLigandFrameExec? target with
      | none => .unavailableEvidence
      | some base =>
          match (input.prepareUniversalRule3EvaluationOutcome
              base.cursors target view).2 with
          | none => .operationalRefusal
          | some frame =>
              match input.descriptorFromFrame? target view center base (some frame) with
              | none => .operationalRefusal
              | some descriptor => .positive descriptor

/-- **Projection to the executable universal descriptor.**  The shared refinement returns a
descriptor exactly when `universalDescriptor?` does, and returns the same descriptor. -/
theorem descriptorOption_universalEvidenceStatus
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    (universalEvidenceStatus input target view).descriptorOption =
      input.universalDescriptor? target view := by
  unfold universalEvidenceStatus universalDescriptor?
  cases hCenter : input.localizedOccurrenceDescriptorCenter? target with
  | none =>
      by_cases hReal : target.1.node.provenance =
          OfficialCIPNodeProvenance.realAtom
      · simp [universalDescriptorOutcome, hCenter, hReal]
      · simp [universalDescriptorOutcome, hCenter, hReal]
  | some center =>
      cases hBase : input.localizedNoDoubleFourLigandFrameExec? target with
      | none => simp [universalDescriptorOutcome, hCenter, hBase]
      | some base =>
          rw [universalDescriptorOutcome_eq_prepared input target view center base
            hCenter hBase]
          cases hFrame : (input.prepareUniversalRule3EvaluationOutcome
              base.cursors target view).2 with
          | none => simp [hFrame, descriptorFromFrame?]
          | some frame =>
              cases hDescriptor : input.descriptorFromFrame? target view center base
                  (some frame) with
              | none => simp [hFrame, hDescriptor]
              | some descriptor => simp [hFrame, hDescriptor]

/-- **Structural non-bearing at the universal layer is exactly non-real provenance with no
descriptor centre.**  A present real centre never yields this status. -/
theorem universalEvidenceStatus_eq_structuralNonbearing_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    universalEvidenceStatus input target view = .structuralNonbearing ↔
      input.localizedOccurrenceDescriptorCenter? target = none ∧
        target.1.node.provenance ≠ OfficialCIPNodeProvenance.realAtom := by
  unfold universalEvidenceStatus
  cases hCenter : input.localizedOccurrenceDescriptorCenter? target with
  | none =>
      by_cases hReal : target.1.node.provenance =
          OfficialCIPNodeProvenance.realAtom
      · simp [hReal]
      · simp [hReal]
  | some center =>
      cases hBase : input.localizedNoDoubleFourLigandFrameExec? target with
      | none => simp
      | some base =>
          cases hFrame : (input.prepareUniversalRule3EvaluationOutcome
              base.cursors target view).2 with
          | none => simp [hFrame]
          | some frame =>
              cases hDescriptor : input.descriptorFromFrame? target view center base
                  (some frame) with
              | none => simp [hFrame, hDescriptor]
              | some descriptor => simp [hFrame, hDescriptor]

/-- A missing descriptor centre at real provenance is unavailable geometry, not structural
non-bearing. -/
theorem universalEvidenceStatus_eq_unavailableEvidence_of_center_none_of_real
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (hCenter : input.localizedOccurrenceDescriptorCenter? target = none)
    (hReal : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    universalEvidenceStatus input target view = .unavailableEvidence := by
  unfold universalEvidenceStatus
  simp [hCenter, hReal]

/-- A missing four-ligand base is unavailable geometry. -/
theorem universalEvidenceStatus_eq_unavailableEvidence_of_base_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (center : input.TetrahedralCenter)
    (hCenter : input.localizedOccurrenceDescriptorCenter? target = some center)
    (hBase : input.localizedNoDoubleFourLigandFrameExec? target = none) :
    universalEvidenceStatus input target view = .unavailableEvidence := by
  unfold universalEvidenceStatus
  simp [hCenter, hBase]

/-- A failed universal Rule-3 preparation is an operational refusal, not structural non-bearing.
The specific downstream cause of the preparation failure is deliberately not classified. -/
theorem universalEvidenceStatus_eq_operationalRefusal_of_prepare_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (center : input.TetrahedralCenter)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (hCenter : input.localizedOccurrenceDescriptorCenter? target = some center)
    (hBase : input.localizedNoDoubleFourLigandFrameExec? target = some base)
    (hFrame : (input.prepareUniversalRule3EvaluationOutcome
      base.cursors target view).2 = none) :
    universalEvidenceStatus input target view = .operationalRefusal := by
  unfold universalEvidenceStatus
  simp [hCenter, hBase, hFrame]

/-- A failed descriptor assembly from a present Rule-3 frame is an operational refusal.  The
specific missing dependency, cycle, tie or planarity cause is deliberately not classified. -/
theorem universalEvidenceStatus_eq_operationalRefusal_of_descriptor_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (center : input.TetrahedralCenter)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (hCenter : input.localizedOccurrenceDescriptorCenter? target = some center)
    (hBase : input.localizedNoDoubleFourLigandFrameExec? target = some base)
    (hFrame : (input.prepareUniversalRule3EvaluationOutcome
      base.cursors target view).2 = some frame)
    (hDescriptor : input.descriptorFromFrame? target view center base (some frame) = none) :
    universalEvidenceStatus input target view = .operationalRefusal := by
  unfold universalEvidenceStatus
  simp [hCenter, hBase, hFrame, hDescriptor]

/-- Successful universal descriptor assembly is recorded positive evidence carrying the actual
label.  The generic status does not classify the label's case: the label may be an uppercase
`chiral` descriptor or a lowercase `pseudoasymmetric` descriptor. -/
theorem universalEvidenceStatus_eq_positive_of_descriptor_some
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (center : input.TetrahedralCenter)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (descriptor : LocalizedAuxiliaryLabel)
    (hCenter : input.localizedOccurrenceDescriptorCenter? target = some center)
    (hBase : input.localizedNoDoubleFourLigandFrameExec? target = some base)
    (hFrame : (input.prepareUniversalRule3EvaluationOutcome
      base.cursors target view).2 = some frame)
    (hDescriptor : input.descriptorFromFrame? target view center base (some frame) =
      some descriptor) :
    universalEvidenceStatus input target view = .positive descriptor := by
  unfold universalEvidenceStatus
  simp [hCenter, hBase, hFrame, hDescriptor]

/-- The completed-tie constructor is not observable at the universal layer: that layer reports a
frame or a refusal, never the legacy ranking-tie diagnostic. -/
theorem universalEvidenceStatus_ne_completedPriorityTie
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    universalEvidenceStatus input target view ≠ .completedPriorityTie := by
  unfold universalEvidenceStatus
  cases hCenter : input.localizedOccurrenceDescriptorCenter? target with
  | none =>
      by_cases hReal : target.1.node.provenance =
          OfficialCIPNodeProvenance.realAtom
      · simp [hReal]
      · simp [hReal]
  | some center =>
      cases hBase : input.localizedNoDoubleFourLigandFrameExec? target with
      | none => simp
      | some base =>
          cases hFrame : (input.prepareUniversalRule3EvaluationOutcome
              base.cursors target view).2 with
          | none => simp [hFrame]
          | some frame =>
              cases hDescriptor : input.descriptorFromFrame? target view center base
                  (some frame) with
              | none => simp [hFrame, hDescriptor]
              | some descriptor => simp [hFrame, hDescriptor]

/-- The universal status does not use the occurrence-layer `.pseudoasymmetric` constructor.  This
is a syntactic fact about the observer, not a claim that the produced label is never lowercase: a
lowercase `LocalizedAuxiliaryLabel.pseudoasymmetric` label is returned as `.positive` by
`universalEvidenceStatus`, and its case must be read from the label payload. -/
theorem universalEvidenceStatus_ne_pseudoasymmetric
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel) :
    universalEvidenceStatus input target view ≠ .pseudoasymmetric descriptor := by
  unfold universalEvidenceStatus
  cases hCenter : input.localizedOccurrenceDescriptorCenter? target with
  | none =>
      by_cases hReal : target.1.node.provenance =
          OfficialCIPNodeProvenance.realAtom
      · simp [hReal]
      · simp [hReal]
  | some center =>
      cases hBase : input.localizedNoDoubleFourLigandFrameExec? target with
      | none => simp
      | some base =>
          cases hFrame : (input.prepareUniversalRule3EvaluationOutcome
              base.cursors target view).2 with
          | none => simp [hFrame]
          | some frame =>
              cases hDescriptor : input.descriptorFromFrame? target view center base
                  (some frame) with
              | none => simp [hFrame, hDescriptor]
              | some found => simp [hFrame, hDescriptor]

/-! ## 5. Universal semantic separation

A positive universal status carries an actual declarative universal descriptor at some Rule-3
budget.  Every refusal status carries the unconditional negative statement: no budget and no label
satisfy the declarative universal descriptor.  The structural route is included among the refusal
statuses, so it is a proved alternative to missing evidence, not a chemical negative verdict. -/

/-- **Positive universal evidence is declarative derivability.** -/
theorem universalEvidenceStatus_positive_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel)
    (h : universalEvidenceStatus input target view = .positive descriptor) :
    ∃ evaluationBudget : Nat,
      input.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
        evaluationBudget descriptor := by
  have hDescriptor : input.universalDescriptor? target view = some descriptor := by
    rw [← descriptorOption_universalEvidenceStatus input target view]
    simp [h]
  exact (input.universalDescriptor?_eq_some_iff_exists_declarativeUniversalDescriptor_of_derived
    target view descriptor).mp hDescriptor

/-- **Every refusal status is a declarative non-derivation.**  Missing geometry, proved structural
non-bearing and an undifferentiated operational refusal all refuse the declarative universal
descriptor; the distinction between them is retained in the status, not erased.  This is
operational non-derivability, not a chemical achirality verdict. -/
theorem universalEvidenceStatus_refusal_no_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (h : universalEvidenceStatus input target view = .unavailableEvidence ∨
      universalEvidenceStatus input target view = .structuralNonbearing ∨
        universalEvidenceStatus input target view = .operationalRefusal) :
    ∀ (evaluationBudget : Nat) (descriptor : LocalizedAuxiliaryLabel),
      ¬ input.DeclarativeLocalizedOccurrenceUniversalDescriptor target view
        evaluationBudget descriptor := by
  have hNone : input.universalDescriptor? target view = none := by
    rw [← descriptorOption_universalEvidenceStatus input target view]
    rcases h with h | h | h <;> simp [h]
  exact (input.universalDescriptor?_eq_none_iff_forall_not_declarativeUniversalDescriptor_of_derived
    target view).mp hNone

/-! ## 6. Projection into the universal reference pipeline

For a `LocalizedUniversalReference.Input`, reading the shared status at the reference state's own
dependency view projects exactly to `referenceState`.  This is the pipeline connection: the status
is not an abstract annotation layered on top of the theorem, it is a decomposition of the same
executable call that defines the reference state. -/

/-- The runtime pipeline input. -/
abbrev PipelineInput := LocalizedUniversalReference.Input

/-- A carrier occurrence of the runtime pipeline. -/
abbrev PipelineOccurrence (input : PipelineInput) :=
  LocalizedUniversalReference.Occurrence input

/-- The dependency view of the reference state at a target. -/
abbrev referenceView (input : PipelineInput) (target : PipelineOccurrence input) :
    input.certified.LocalizedDependencyView target :=
  input.certified.localizedDependencyView
    (LocalizedUniversalReference.referenceState input) target

/-- The shared evidence status read at the reference state's own view. -/
def referenceEvidenceStatus (input : PipelineInput) (target : PipelineOccurrence input) :
    LocalizedEvidenceStatus LocalizedAuxiliaryLabel :=
  universalEvidenceStatus input.certified target (referenceView input target)

/-- The reference equation, written as `universalDescriptor?` at the reference view. -/
theorem referenceState_eq_universalDescriptor_referenceView
    (input : PipelineInput) (target : PipelineOccurrence input) :
    LocalizedUniversalReference.referenceState input target =
      input.certified.universalDescriptor? target (referenceView input target) := by
  have h := LocalizedUniversalReference.reference_equation input target
  rw [LocalizedUniversalReference.evaluator_eq_universalDescriptor_apply input
    (LocalizedUniversalReference.carrierFuel input) target
    (input.certified.localizedDependencyView
      (LocalizedUniversalReference.referenceState input) target)] at h
  exact h.symm

/-- **Pipeline projection.**  The descriptor slot of the reference-view evidence status is exactly
the generated reference state. -/
theorem referenceEvidenceStatus_descriptorOption
    (input : PipelineInput) (target : PipelineOccurrence input) :
    (referenceEvidenceStatus input target).descriptorOption =
      LocalizedUniversalReference.referenceState input target := by
  unfold referenceEvidenceStatus
  rw [descriptorOption_universalEvidenceStatus]
  exact (referenceState_eq_universalDescriptor_referenceView input target).symm

/-- A refusal status at the reference view forces the reference state to refuse. -/
theorem referenceState_eq_none_of_referenceEvidenceStatus_refusal
    (input : PipelineInput) (target : PipelineOccurrence input)
    (h : referenceEvidenceStatus input target = .unavailableEvidence ∨
      referenceEvidenceStatus input target = .structuralNonbearing ∨
        referenceEvidenceStatus input target = .operationalRefusal) :
    LocalizedUniversalReference.referenceState input target = none := by
  rw [← referenceEvidenceStatus_descriptorOption input target]
  rcases h with h | h | h <;> simp [h]

/-- **The pipeline conversion theorem.**  A reference-view refusal status yields both the
operational `referenceState = none` and the unconditional declarative non-derivation statement of
`LocalizedUniversalSemanticClosure`.  The status distinguishes the cause; the declarative relation
remains exactly the one already proved. -/
theorem referenceState_refusal_declarative_of_referenceEvidenceStatus
    (input : PipelineInput) (target : PipelineOccurrence input)
    (h : referenceEvidenceStatus input target = .unavailableEvidence ∨
      referenceEvidenceStatus input target = .structuralNonbearing ∨
        referenceEvidenceStatus input target = .operationalRefusal) :
    LocalizedUniversalReference.referenceState input target = none ∧
      ∀ (evaluationBudget : Nat) (descriptor : LocalizedAuxiliaryLabel),
        ¬ input.certified.DeclarativeLocalizedOccurrenceUniversalDescriptor target
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input) target)
          evaluationBudget descriptor := by
  have hNone := referenceState_eq_none_of_referenceEvidenceStatus_refusal input target h
  exact ⟨hNone,
    (LocalizedUniversalReference.referenceState_eq_none_iff_forall_not_declarativeUniversalDescriptor_unconditional
      input target).mp hNone⟩

/-- The structural alternative is visible at the pipeline layer: it is exactly a descriptor-centre
refusal at non-real provenance. -/
theorem referenceEvidenceStatus_eq_structuralNonbearing_iff
    (input : PipelineInput) (target : PipelineOccurrence input) :
    referenceEvidenceStatus input target = .structuralNonbearing ↔
      input.certified.localizedOccurrenceDescriptorCenter? target = none ∧
        target.1.node.provenance ≠ OfficialCIPNodeProvenance.realAtom := by
  unfold referenceEvidenceStatus
  exact universalEvidenceStatus_eq_structuralNonbearing_iff input.certified target
    (referenceView input target)

/-- Missing geometry at a real occurrence remains unavailable evidence at the pipeline layer. -/
theorem referenceEvidenceStatus_eq_unavailableEvidence_of_center_none_of_real
    (input : PipelineInput) (target : PipelineOccurrence input)
    (hCenter : input.certified.localizedOccurrenceDescriptorCenter? target = none)
    (hReal : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    referenceEvidenceStatus input target = .unavailableEvidence := by
  unfold referenceEvidenceStatus
  exact universalEvidenceStatus_eq_unavailableEvidence_of_center_none_of_real
    input.certified target (referenceView input target) hCenter hReal

end LocalizedRefusalEvidence

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedRefusalEvidence.toClassification_occurrenceEvidenceStatus
assert_kernel_only TetraStereo.OneCenter.LocalizedRefusalEvidence.occurrenceEvidenceStatus_eq_structuralNonbearing_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedRefusalEvidence.occurrenceEvidenceStatus_eq_completedPriorityTie_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedRefusalEvidence.occurrenceEvidenceStatus_eq_operationalRefusal_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedRefusalEvidence.occurrenceEvidenceStatus_completedPriorityTie_ne_operationalRefusal
assert_kernel_only TetraStereo.OneCenter.LocalizedRefusalEvidence.legacyOccurrenceFact?_exists_of_sufficient_inputs
assert_kernel_only TetraStereo.OneCenter.LocalizedRefusalEvidence.occurrenceEvidenceStatus_no_tie_no_operationalRefusal_of_sufficient_inputs
assert_kernel_only TetraStereo.OneCenter.LocalizedRefusalEvidence.descriptorOption_universalEvidenceStatus
assert_kernel_only TetraStereo.OneCenter.LocalizedRefusalEvidence.universalEvidenceStatus_eq_structuralNonbearing_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedRefusalEvidence.universalEvidenceStatus_refusal_no_declarative
assert_kernel_only TetraStereo.OneCenter.LocalizedRefusalEvidence.referenceEvidenceStatus_descriptorOption
assert_kernel_only TetraStereo.OneCenter.LocalizedRefusalEvidence.referenceState_refusal_declarative_of_referenceEvidenceStatus
