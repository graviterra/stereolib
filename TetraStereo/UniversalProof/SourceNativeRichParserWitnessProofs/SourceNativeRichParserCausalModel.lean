import TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserWitness

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserCausalModel

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence

/-!
Exact optional outcomes and causal scheduling for the rich original-occurrence parser channel.
The canonical relation pins actual compiled evidence and also retains its independent sound
meaning. Exactness concerns this canonical execution relation, not a converse of the weaker
independent derivation. The source's finite depth dependency orders genuine parser evaluations;
no auxiliary state or assigned label is supplied to the concrete CFClBrI witness. This leaves
the conservative raw guard unchanged. Mixed-input admission, broader interpreter coverage and
scientific source approval remain separate; the priority backend retains its Rule-3 spatial
unit queries. Parser parity and tracked pseudo history determine this channel's emitted label.
-/

variable (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
  (agreement : molecule.AuthoritativeStructureAgreement source) (writtenExact : molecule.WrittenNeighborExact)

def CanonicalOccurrenceParserRichDescriptor {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (descriptor : AromaticCanonicalAuxiliaryLabel) : Prop :=
  ∃ evidence,
    occurrenceParserRichPriorityEvidence? molecule source agreement writtenExact
      target view ruleFuel = some evidence ∧
    OccurrenceParserRichPriorityEvidenceMeaning molecule source agreement writtenExact
      target view ruleFuel evidence ∧
    descriptor = classifyTetrahedralRSPseudo evidence.raw evidence.tracked.pseudoComparisons

theorem canonical_parser_rich_descriptor_sound {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (descriptor : AromaticCanonicalAuxiliaryLabel)
    (canonical : CanonicalOccurrenceParserRichDescriptor molecule source agreement writtenExact
      target view ruleFuel descriptor) :
    OccurrenceParserRichDescriptorMeaning molecule source agreement writtenExact
      target view ruleFuel descriptor := by
  obtain ⟨evidence, _, meaning, classified⟩ := canonical
  exact ⟨evidence, meaning, classified⟩

theorem occurrenceParserRichDescriptor?_eq_some_iff_canonical {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (descriptor : AromaticCanonicalAuxiliaryLabel) :
    occurrenceParserRichDescriptor? molecule source agreement writtenExact target view ruleFuel =
      some descriptor ↔
    CanonicalOccurrenceParserRichDescriptor molecule source agreement writtenExact
      target view ruleFuel descriptor := by
  constructor
  · intro computed
    unfold occurrenceParserRichDescriptor? at computed
    cases evidenceComputed : occurrenceParserRichPriorityEvidence? molecule source agreement
        writtenExact target view ruleFuel with
    | none => simp [evidenceComputed] at computed
    | some evidence =>
        simp [evidenceComputed] at computed
        subst descriptor
        exact ⟨evidence, evidenceComputed,
          occurrenceParserRichPriorityEvidence?_sound molecule source agreement writtenExact
            target view ruleFuel evidence evidenceComputed, rfl⟩
  · rintro ⟨evidence, computed, _, rfl⟩
    simp [occurrenceParserRichDescriptor?, computed]

theorem occurrenceParserRichDescriptor?_eq_none_iff_no_canonical {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    occurrenceParserRichDescriptor? molecule source agreement writtenExact target view ruleFuel = none ↔
      ¬∃ descriptor, CanonicalOccurrenceParserRichDescriptor molecule source agreement writtenExact
        target view ruleFuel descriptor := by
  constructor
  · intro absent ⟨descriptor, canonical⟩
    have computed := (occurrenceParserRichDescriptor?_eq_some_iff_canonical
      molecule source agreement writtenExact target view ruleFuel descriptor).mpr canonical
    rw [absent] at computed
    contradiction
  · intro absent
    cases computed : occurrenceParserRichDescriptor? molecule source agreement writtenExact
        target view ruleFuel with
    | none => rfl
    | some descriptor =>
        exact False.elim (absent ⟨descriptor,
          (occurrenceParserRichDescriptor?_eq_some_iff_canonical molecule source agreement
            writtenExact target view ruleFuel descriptor).mp computed⟩)

def OccurrenceParserRichOutcome {carrierFuel : Nat} (ruleFuel : Nat)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (outcome : Option AromaticCanonicalAuxiliaryLabel) : Prop :=
  match outcome with
  | none => ¬∃ descriptor, CanonicalOccurrenceParserRichDescriptor molecule source agreement
      writtenExact target (source.aromaticCanonicalDependencyView state target) ruleFuel descriptor
  | some descriptor => CanonicalOccurrenceParserRichDescriptor molecule source agreement
      writtenExact target (source.aromaticCanonicalDependencyView state target) ruleFuel descriptor

theorem occurrenceParserRichOutcome_iff {carrierFuel : Nat} (ruleFuel : Nat)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (outcome : Option AromaticCanonicalAuxiliaryLabel) :
    OccurrenceParserRichOutcome molecule source agreement writtenExact ruleFuel state target outcome ↔
      occurrenceParserRichDescriptor? molecule source agreement writtenExact target
        (source.aromaticCanonicalDependencyView state target) ruleFuel = outcome := by
  cases outcome with
  | none => exact (occurrenceParserRichDescriptor?_eq_none_iff_no_canonical
      molecule source agreement writtenExact target _ ruleFuel).symm
  | some descriptor => exact (occurrenceParserRichDescriptor?_eq_some_iff_canonical
      molecule source agreement writtenExact target _ ruleFuel descriptor).symm

noncomputable def occurrenceParserRichAuxiliarySemantics (carrierFuel ruleFuel : Nat) :
    source.AromaticCanonicalRuleSemantics carrierFuel where
  DeclarativeDerivation := OccurrenceParserRichOutcome molecule source agreement writtenExact ruleFuel
  executableRule := fun target view =>
    occurrenceParserRichDescriptor? molecule source agreement writtenExact target view ruleFuel
  derivation_executable_iff := occurrenceParserRichOutcome_iff molecule source agreement
    writtenExact ruleFuel

theorem existsUnique_occurrenceParserRichCIPModel (carrierFuel ruleFuel : Nat) :
    ∃! state, (source.aromaticCanonicalOccurrenceSystem
      (occurrenceParserRichAuxiliarySemantics molecule source agreement writtenExact
        carrierFuel ruleFuel)).CIPModel state :=
  source.existsUnique_aromaticCanonicalCIPModel
    (occurrenceParserRichAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)

noncomputable def occurrenceParserRichScheduledState (carrierFuel ruleFuel : Nat) :
    source.AromaticCanonicalAuxiliaryState carrierFuel :=
  DeclarativeCIP.OccurrenceScheduler.decode
    (source.aromaticCanonicalOccurrenceSystem
      (occurrenceParserRichAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel))
    (@source.AromaticCanonicalDepthDependency carrierFuel)
    (DeclarativeCIP.OccurrenceScheduler.closure
      (source.aromaticCanonicalOccurrenceSystem
        (occurrenceParserRichAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel))
      (@source.AromaticCanonicalDepthDependency carrierFuel))

theorem occurrenceParserRichScheduledState_cipModel (carrierFuel ruleFuel : Nat) :
    (source.aromaticCanonicalOccurrenceSystem
      (occurrenceParserRichAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)).CIPModel
      (occurrenceParserRichScheduledState molecule source agreement writtenExact carrierFuel ruleFuel) :=
  source.aromaticCanonicalSchedulerClosure_cipModel
    (occurrenceParserRichAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)

theorem occurrenceParserRichModel_evaluates {carrierFuel ruleFuel : Nat}
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (occurrenceParserRichAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)).CIPModel state)
    (target : source.AromaticCanonicalOccurrence carrierFuel) :
    occurrenceParserRichDescriptor? molecule source agreement writtenExact target
      (source.aromaticCanonicalDependencyView state target) ruleFuel = state target := by
  have fixed := (source.aromaticCanonicalOccurrenceSystem
    (occurrenceParserRichAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)).cipModel_iff_executableStateStep_fixed
    (source.aromaticCanonicalDerivationStepCorrespondence
      (occurrenceParserRichAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)) state |>.mp model
  exact congrFun fixed target

theorem occurrenceParserRichModel_output_sound {carrierFuel ruleFuel : Nat}
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (occurrenceParserRichAuxiliarySemantics molecule source agreement writtenExact carrierFuel ruleFuel)).CIPModel state)
    (target : source.AromaticCanonicalOccurrence carrierFuel) (descriptor : AromaticCanonicalAuxiliaryLabel)
    (assigned : state target = some descriptor) :
    OccurrenceParserRichDescriptorMeaning molecule source agreement writtenExact target
      (source.aromaticCanonicalDependencyView state target) ruleFuel descriptor :=
  occurrenceParserRichDescriptor?_sound molecule source agreement writtenExact target _ ruleFuel descriptor
    ((occurrenceParserRichModel_evaluates molecule source agreement writtenExact state model target).trans assigned)

namespace ClosedParserModel
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment.ClosedParserWitness
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserWitness

noncomputable def parserScheduledState : parserSource.AromaticCanonicalAuxiliaryState 0 :=
  occurrenceParserRichScheduledState annotatedRawCF parserSource parserSource_agreement parserSource_writtenExact 0 2
noncomputable def parserSemantics : parserSource.AromaticCanonicalRuleSemantics 0 :=
  occurrenceParserRichAuxiliarySemantics annotatedRawCF parserSource parserSource_agreement parserSource_writtenExact 0 2
theorem parserScheduledState_cipModel :
    (parserSource.aromaticCanonicalOccurrenceSystem parserSemantics).CIPModel parserScheduledState :=
  occurrenceParserRichScheduledState_cipModel annotatedRawCF parserSource parserSource_agreement parserSource_writtenExact 0 2

theorem parser_every_model_R (state : parserSource.AromaticCanonicalAuxiliaryState 0)
    (model : (parserSource.aromaticCanonicalOccurrenceSystem parserSemantics).CIPModel state) :
    state parserTarget = some (.chiral RS.R) := by
  rw [← occurrenceParserRichModel_evaluates annotatedRawCF parserSource parserSource_agreement
    parserSource_writtenExact state model parserTarget]
  exact parser_actual_rich_descriptor_R _
theorem parser_scheduled_R : parserScheduledState parserTarget = some (.chiral RS.R) :=
  parser_every_model_R parserScheduledState parserScheduledState_cipModel
theorem parser_scheduled_R_meaning :
    OccurrenceParserRichDescriptorMeaning annotatedRawCF parserSource parserSource_agreement parserSource_writtenExact
      parserTarget (parserSource.aromaticCanonicalDependencyView parserScheduledState parserTarget) 2 (.chiral RS.R) :=
  occurrenceParserRichModel_output_sound annotatedRawCF parserSource parserSource_agreement parserSource_writtenExact
    parserScheduledState parserScheduledState_cipModel parserTarget (.chiral RS.R) parser_scheduled_R

end ClosedParserModel
end TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserCausalModel
