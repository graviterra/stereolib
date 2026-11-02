import TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
import TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserCausalModel

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge

/-!
Canonical optional outcomes and finite causal scheduling for the constitution-bound parser channel.
The actual channel uses conversion-pinned RawAnnotationAgreement and WrittenNeighborExact, allowing
independent drawing records without requiring whole-diagram equality. Its canonical execution
relation retains independent constitution-parser evidence, including actual raw parity, matched
absolute source annotation, returned-root alignment, keys and safe tracked order. Exactness is
about that canonical relation, not a converse from the weaker independent descriptor meaning.

The model constructs its own scheduled state. Full-agreement execution equivalence and the genuine
closed CFClBrI R witness are proved without caller labels, callback identities or success inputs.
No claim of a non-full-diagram closed assigned witness is made here. Noncomputable Lean scheduling
is not a runnable extracted interpreter. The priority backend remains the existing Rules-3--5
backend, including its spatial unit queries; the separate planar frame is not yet integrated.
Mixed-channel conflict checking, directional interpretation, source-wide admission and production
export remain TECHNICAL_PROOF_REQUIRED. Annotation conventions remain HUMAN_REVIEW_REQUIRED and
source adoption remains EXTERNAL_EVIDENCE_REQUIRED. Existing guards and production readers remain
unchanged.
-/

variable (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
  (agreement : RawAnnotationAgreement molecule source) (writtenExact : molecule.WrittenNeighborExact)

def CanonicalConstitutionParserRichDescriptor {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (descriptor : AromaticCanonicalAuxiliaryLabel) : Prop :=
  ∃ evidence,
    constitutionParserRichPriorityEvidence? molecule source agreement writtenExact
      target view ruleFuel = some evidence ∧
    ConstitutionParserRichPriorityEvidenceMeaning molecule source agreement writtenExact
      target view ruleFuel evidence ∧
    descriptor = classifyTetrahedralRSPseudo evidence.raw evidence.tracked.pseudoComparisons

theorem canonical_constitution_parser_rich_descriptor_sound {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (descriptor : AromaticCanonicalAuxiliaryLabel)
    (canonical : CanonicalConstitutionParserRichDescriptor molecule source agreement writtenExact
      target view ruleFuel descriptor) :
    ConstitutionParserRichDescriptorMeaning molecule source agreement writtenExact
      target view ruleFuel descriptor := by
  obtain ⟨evidence, _, meaning, classified⟩ := canonical
  exact ⟨evidence, meaning, classified⟩

theorem constitutionParserRichDescriptor?_eq_some_iff_canonical {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (descriptor : AromaticCanonicalAuxiliaryLabel) :
    constitutionParserRichDescriptor? molecule source agreement writtenExact target view ruleFuel =
      some descriptor ↔
    CanonicalConstitutionParserRichDescriptor molecule source agreement writtenExact
      target view ruleFuel descriptor := by
  constructor
  · intro computed
    unfold constitutionParserRichDescriptor? at computed
    cases evidenceComputed : constitutionParserRichPriorityEvidence? molecule source agreement
        writtenExact target view ruleFuel with
    | none => simp [evidenceComputed] at computed
    | some evidence =>
        simp [evidenceComputed] at computed
        subst descriptor
        exact ⟨evidence, evidenceComputed,
          constitutionParserRichPriorityEvidence?_sound molecule source agreement writtenExact
            target view ruleFuel evidence evidenceComputed, rfl⟩
  · rintro ⟨evidence, computed, _, rfl⟩
    simp [constitutionParserRichDescriptor?, computed]

theorem constitutionParserRichDescriptor?_eq_none_iff_no_canonical {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    constitutionParserRichDescriptor? molecule source agreement writtenExact target view ruleFuel = none ↔
      ¬∃ descriptor, CanonicalConstitutionParserRichDescriptor molecule source agreement writtenExact
        target view ruleFuel descriptor := by
  constructor
  · intro absent ⟨descriptor, canonical⟩
    have computed := (constitutionParserRichDescriptor?_eq_some_iff_canonical
      molecule source agreement writtenExact target view ruleFuel descriptor).mpr canonical
    rw [absent] at computed
    contradiction
  · intro absent
    cases computed : constitutionParserRichDescriptor? molecule source agreement writtenExact
        target view ruleFuel with
    | none => rfl
    | some descriptor =>
        exact False.elim (absent ⟨descriptor,
          (constitutionParserRichDescriptor?_eq_some_iff_canonical molecule source agreement
            writtenExact target view ruleFuel descriptor).mp computed⟩)

def ConstitutionParserRichOutcome {carrierFuel : Nat} (ruleFuel : Nat)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (outcome : Option AromaticCanonicalAuxiliaryLabel) : Prop :=
  match outcome with
  | none => ¬∃ descriptor, CanonicalConstitutionParserRichDescriptor molecule source agreement
      writtenExact target (source.aromaticCanonicalDependencyView state target) ruleFuel descriptor
  | some descriptor => CanonicalConstitutionParserRichDescriptor molecule source agreement
      writtenExact target (source.aromaticCanonicalDependencyView state target) ruleFuel descriptor

theorem constitutionParserRichOutcome_iff {carrierFuel : Nat} (ruleFuel : Nat)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (outcome : Option AromaticCanonicalAuxiliaryLabel) :
    ConstitutionParserRichOutcome molecule source agreement writtenExact ruleFuel state target outcome ↔
      constitutionParserRichDescriptor? molecule source agreement writtenExact target
        (source.aromaticCanonicalDependencyView state target) ruleFuel = outcome := by
  cases outcome with
  | none => exact (constitutionParserRichDescriptor?_eq_none_iff_no_canonical
      molecule source agreement writtenExact target _ ruleFuel).symm
  | some descriptor => exact (constitutionParserRichDescriptor?_eq_some_iff_canonical
      molecule source agreement writtenExact target _ ruleFuel descriptor).symm

noncomputable def constitutionParserRichAuxiliarySemantics (carrierFuel ruleFuel : Nat) :
    source.AromaticCanonicalRuleSemantics carrierFuel where
  DeclarativeDerivation := ConstitutionParserRichOutcome molecule source agreement writtenExact ruleFuel
  executableRule := fun target view =>
    constitutionParserRichDescriptor? molecule source agreement writtenExact target view ruleFuel
  derivation_executable_iff := constitutionParserRichOutcome_iff molecule source agreement
    writtenExact ruleFuel

theorem existsUnique_constitutionParserRichCIPModel (carrierFuel ruleFuel : Nat) :
    ∃! state, (source.aromaticCanonicalOccurrenceSystem
      (constitutionParserRichAuxiliarySemantics molecule source agreement writtenExact
        carrierFuel ruleFuel)).CIPModel state :=
  source.existsUnique_aromaticCanonicalCIPModel
    (constitutionParserRichAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)

noncomputable def constitutionParserRichScheduledState (carrierFuel ruleFuel : Nat) :
    source.AromaticCanonicalAuxiliaryState carrierFuel :=
  DeclarativeCIP.OccurrenceScheduler.decode
    (source.aromaticCanonicalOccurrenceSystem
      (constitutionParserRichAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel))
    (@source.AromaticCanonicalDepthDependency carrierFuel)
    (DeclarativeCIP.OccurrenceScheduler.closure
      (source.aromaticCanonicalOccurrenceSystem
        (constitutionParserRichAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel))
      (@source.AromaticCanonicalDepthDependency carrierFuel))

theorem constitutionParserRichScheduledState_cipModel (carrierFuel ruleFuel : Nat) :
    (source.aromaticCanonicalOccurrenceSystem
      (constitutionParserRichAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)).CIPModel
      (constitutionParserRichScheduledState molecule source agreement writtenExact carrierFuel ruleFuel) :=
  source.aromaticCanonicalSchedulerClosure_cipModel
    (constitutionParserRichAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)

theorem constitutionParserRichModel_evaluates {carrierFuel ruleFuel : Nat}
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (constitutionParserRichAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)).CIPModel state)
    (target : source.AromaticCanonicalOccurrence carrierFuel) :
    constitutionParserRichDescriptor? molecule source agreement writtenExact target
      (source.aromaticCanonicalDependencyView state target) ruleFuel = state target := by
  have fixed := (source.aromaticCanonicalOccurrenceSystem
    (constitutionParserRichAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)).cipModel_iff_executableStateStep_fixed
    (source.aromaticCanonicalDerivationStepCorrespondence
      (constitutionParserRichAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)) state |>.mp model
  exact congrFun fixed target

theorem constitutionParserRichModel_output_sound {carrierFuel ruleFuel : Nat}
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (constitutionParserRichAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)).CIPModel state)
    (target : source.AromaticCanonicalOccurrence carrierFuel) (descriptor : AromaticCanonicalAuxiliaryLabel)
    (assigned : state target = some descriptor) :
    ConstitutionParserRichDescriptorMeaning molecule source agreement writtenExact target
      (source.aromaticCanonicalDependencyView state target) ruleFuel descriptor :=
  constitutionParserRichDescriptor?_sound molecule source agreement writtenExact target _ ruleFuel descriptor
    ((constitutionParserRichModel_evaluates molecule source agreement writtenExact state model target).trans assigned)

theorem constitutionParserRichModel_unique (carrierFuel ruleFuel : Nat)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (constitutionParserRichAuxiliarySemantics molecule source agreement writtenExact
        carrierFuel ruleFuel)).CIPModel state) :
    state = constitutionParserRichScheduledState molecule source agreement writtenExact
      carrierFuel ruleFuel := by
  obtain ⟨canonical, _canonicalModel, unique⟩ :=
    existsUnique_constitutionParserRichCIPModel molecule source agreement writtenExact
      carrierFuel ruleFuel
  exact (unique state model).trans
    (unique _ (constitutionParserRichScheduledState_cipModel molecule source agreement writtenExact
      carrierFuel ruleFuel)).symm

/-- Full agreement execution has exactly the same actual evidence, by conversion-index identity.
No equality of old spatial judgments or assumed comparator callbacks is used. -/
theorem constitutionParserRichPriorityEvidence?_eq_full {carrierFuel : Nat}
    (full : molecule.AuthoritativeStructureAgreement source)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    constitutionParserRichPriorityEvidence? molecule source agreement writtenExact
        target view ruleFuel =
      occurrenceParserRichPriorityEvidence? molecule source full writtenExact
        target view ruleFuel := by
  rfl

theorem constitutionParserRichDescriptor?_eq_full {carrierFuel : Nat}
    (full : molecule.AuthoritativeStructureAgreement source)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    constitutionParserRichDescriptor? molecule source agreement writtenExact
        target view ruleFuel =
      occurrenceParserRichDescriptor? molecule source full writtenExact target view ruleFuel := by
  unfold constitutionParserRichDescriptor? occurrenceParserRichDescriptor?
  rw [constitutionParserRichPriorityEvidence?_eq_full molecule source agreement writtenExact
    full target view ruleFuel]

namespace ClosedConstitutionParserModel

open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment.ClosedParserWitness
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserWitness
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge.ConstitutionClosedWitness

noncomputable def parserSemantics : parserSource.AromaticCanonicalRuleSemantics 0 :=
  constitutionParserRichAuxiliarySemantics annotatedRawCF parserSource
    parserSource_annotationAgreement parserSource_writtenExact 0 2

noncomputable def parserScheduledState : parserSource.AromaticCanonicalAuxiliaryState 0 :=
  constitutionParserRichScheduledState annotatedRawCF parserSource
    parserSource_annotationAgreement parserSource_writtenExact 0 2

theorem parserScheduledState_cipModel :
    (parserSource.aromaticCanonicalOccurrenceSystem parserSemantics).CIPModel parserScheduledState :=
  constitutionParserRichScheduledState_cipModel annotatedRawCF parserSource
    parserSource_annotationAgreement parserSource_writtenExact 0 2

/-- The actual constitution channel emits R for every view at the actual closed target. -/
theorem parser_actual_constitution_descriptor_R
    (view : parserSource.AromaticCanonicalDependencyView parserTarget) :
    constitutionParserRichDescriptor? annotatedRawCF parserSource parserSource_annotationAgreement
      parserSource_writtenExact parserTarget view 2 = some (.chiral RS.R) := by
  rw [constitutionParserRichDescriptor?_eq_full annotatedRawCF parserSource
    parserSource_annotationAgreement parserSource_writtenExact parserSource_agreement
    parserTarget view 2]
  exact parser_actual_rich_descriptor_R view

/-- The actual internally constructed constitution parser state has R, from the inhabited safe-sort
witness and its own model equation. No old model state or label is supplied to the new evaluator. -/
theorem parser_scheduled_R : parserScheduledState parserTarget = some (.chiral RS.R) := by
  rw [← constitutionParserRichModel_evaluates annotatedRawCF parserSource
    parserSource_annotationAgreement parserSource_writtenExact parserScheduledState
    parserScheduledState_cipModel parserTarget]
  exact parser_actual_constitution_descriptor_R _

theorem parser_scheduled_R_meaning :
    ConstitutionParserRichDescriptorMeaning annotatedRawCF parserSource
      parserSource_annotationAgreement parserSource_writtenExact parserTarget
      (parserSource.aromaticCanonicalDependencyView parserScheduledState parserTarget) 2
      (.chiral RS.R) :=
  constitutionParserRichModel_output_sound annotatedRawCF parserSource
    parserSource_annotationAgreement parserSource_writtenExact parserScheduledState
    parserScheduledState_cipModel parserTarget (.chiral RS.R) parser_scheduled_R

end ClosedConstitutionParserModel
end TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel
