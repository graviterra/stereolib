import TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel
import TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
import TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
import TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserWitness

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace TetraStereo.UniversalProof.SourceNativeConstitutionParserAnnotationAuditProofs.SourceNativeConstitutionParserAnnotationAudit

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge.ConstitutionClosedWitness
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserWitness
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment.ClosedParserWitness














































/-! ## 1. Every real raw record, at every real index -/

/-- Exact coverage of the actual raw atom annotations: membership is an in-range index whose actual
normalized specification carries exactly that parity.  No index is skipped and no out-of-range or
unrepresented record is silently dropped. -/
theorem mem_rawAtomAnnotations_iff (molecule : RawMolecule) (annotation : RawAtomAnnotation) :
    annotation ∈ rawAtomAnnotations molecule ↔
      annotation.index < molecule.atomCount ∧
        ∃ spec, molecule.atomAt? annotation.index = some spec ∧
          spec.tetrahedral? = some annotation.parity := by
  unfold rawAtomAnnotations
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨index, indexMem, mapped⟩
    rw [List.mem_range] at indexMem
    cases observed : molecule.atomAt? index with
    | none => simp [observed] at mapped
    | some spec =>
        cases parityObserved : spec.tetrahedral? with
        | none => simp [observed, parityObserved] at mapped
        | some parity =>
            have same : ({ index := index, parity := parity } : RawAtomAnnotation) = annotation := by
              simpa [observed, parityObserved] using mapped
            subst annotation
            exact ⟨indexMem, spec, observed, parityObserved⟩
  · rintro ⟨indexLt, spec, specEq, parityEq⟩
    cases annotation with
    | mk annotationIndex annotationParity =>
      refine ⟨annotationIndex, List.mem_range.mpr indexLt, ?_⟩
      simp [specEq, parityEq]

/-- Exact coverage of the actual raw directional bond records, including `down` (`false`). -/
theorem mem_rawBondDirections_iff (molecule : RawMolecule) (raw : RawBondDirection) :
    raw ∈ rawBondDirections molecule ↔
      raw.bond ∈ molecule.bonds ∧ raw.bond.kind.directional? = some raw.direction := by
  unfold rawBondDirections
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨bond, present, mapped⟩
    cases observed : bond.kind.directional? with
    | none => simp [observed] at mapped
    | some direction =>
        have same : ({ bond := bond, direction := direction } : RawBondDirection) = raw := by
          simpa [observed] using mapped
        subst raw
        exact ⟨present, observed⟩
  · rintro ⟨present, directionEq⟩
    cases raw with
    | mk bond direction =>
      refine ⟨bond, present, ?_⟩
      simp [directionEq]

/-- The checked semantic conversion pins the source atom index identity: the semantic atom at a
candidate's conversion-only raw index is exactly the checked conversion of the raw record at that
same index.  No diagram equality is used. -/
theorem sourceCandidate_index_identity (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    listGet? source.molecule.atoms
        (parserIndexViaConversion molecule source agreement.1 center).val =
      (molecule.atomAt?
        (parserIndexViaConversion molecule source agreement.1 center).val).bind
        AtomSpec.toSemanticAtom? :=
  RawAnnotationAgreement.semanticAtom_index_identity molecule source agreement _

/-! ## 2. Independent successful interpretation meaning -/

/-- The actual source candidates whose conversion-pinned raw index equals one actual raw index. -/
noncomputable def matchingSourceCandidates (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (annotation : RawAtomAnnotation) : List source.AromaticCanonicalTetrahedralCenter :=
  source.aromaticCanonicalTetrahedralCenters.filter fun candidate =>
    (parserIndexViaConversion molecule source agreement.1 candidate).val == annotation.index

/-- Source-bound meaning of one genuinely interpreted raw atom parity.  It retains the actual raw
parity (the actual normalized record at the candidate's real index), the actual source candidate
with its exact conversion-pinned raw/source index identity, the descriptor read from the
**internally scheduled constitution model** at the candidate's actual final occurrence, and the
complete constitution rich descriptor meaning.  It is not a definition of `isSome` and mentions no
expected label and no caller semantics. -/
def RawAtomAnnotationInterpretation (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) (carrierFuel ruleFuel : Nat)
    (annotation : RawAtomAnnotation) : Prop :=
  ∃ candidate : source.AromaticCanonicalTetrahedralCenter,
    (parserIndexViaConversion molecule source agreement.1 candidate).val = annotation.index ∧
      (∃ spec, molecule.atomAt?
          (parserIndexViaConversion molecule source agreement.1 candidate).val = some spec ∧
        spec.tetrahedral? = some annotation.parity) ∧
        ∃ descriptor : AromaticCanonicalAuxiliaryLabel,
          constitutionParserRichScheduledState molecule source agreement writtenExact carrierFuel
              ruleFuel (source.aromaticCanonicalFinalOccurrence carrierFuel candidate) =
            some descriptor ∧
            ConstitutionParserRichDescriptorMeaning molecule source agreement writtenExact
              (source.aromaticCanonicalFinalOccurrence carrierFuel candidate)
              (source.aromaticCanonicalDependencyView
                (constitutionParserRichScheduledState molecule source agreement writtenExact
                  carrierFuel ruleFuel)
                (source.aromaticCanonicalFinalOccurrence carrierFuel candidate))
              ruleFuel descriptor

/-- Formal scheduled presence test for the source-bound interpretation meaning.  This noncomputable
definition reads the internally constructed constitution causal state; independent assigned
evidence follows from its proved model law.  Runnable extraction is a separate obligation. -/
noncomputable def parserAuditInterpreted? (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) (carrierFuel ruleFuel : Nat)
    (annotation : RawAtomAnnotation) : Bool :=
  (matchingSourceCandidates molecule source agreement annotation).any fun candidate =>
    (match molecule.atomAt?
        (parserIndexViaConversion molecule source agreement.1 candidate).val with
     | some spec => decide (spec.tetrahedral? = some annotation.parity)
     | none => false) &&
      (constitutionParserRichScheduledState molecule source agreement writtenExact carrierFuel
        ruleFuel
        (source.aromaticCanonicalFinalOccurrence carrierFuel candidate)).isSome

theorem matchingSourceCandidates_eq_nil_iff (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (annotation : RawAtomAnnotation) :
    matchingSourceCandidates molecule source agreement annotation = [] ↔
      ∀ candidate : source.AromaticCanonicalTetrahedralCenter,
        (parserIndexViaConversion molecule source agreement.1 candidate).val ≠
          annotation.index := by
  constructor
  · intro empty candidate indexEq
    have member : candidate ∈ matchingSourceCandidates molecule source agreement annotation := by
      unfold matchingSourceCandidates
      rw [List.mem_filter]
      exact ⟨(mem_aromaticCanonicalTetrahedralCenters_iff source candidate).mpr candidate.2,
        beq_iff_eq.mpr indexEq⟩
    rw [empty] at member
    exact List.not_mem_nil member
  · intro noCandidate
    cases observed : matchingSourceCandidates molecule source agreement annotation with
    | nil => rfl
    | cons head tail =>
        have member : head ∈ matchingSourceCandidates molecule source agreement annotation := by
          simp [observed]
        unfold matchingSourceCandidates at member
        rw [List.mem_filter] at member
        exact absurd (beq_iff_eq.mp member.2) (noCandidate head)

theorem not_interpreted_of_no_matching_candidate (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) (carrierFuel ruleFuel : Nat)
    (annotation : RawAtomAnnotation)
    (noCandidate : ∀ candidate : source.AromaticCanonicalTetrahedralCenter,
      (parserIndexViaConversion molecule source agreement.1 candidate).val ≠
        annotation.index) :
    ¬ RawAtomAnnotationInterpretation molecule source agreement writtenExact carrierFuel ruleFuel
      annotation := by
  rintro ⟨candidate, indexEq, _⟩
  exact noCandidate candidate indexEq

/-- The formal presence test is exactly the source-bound interpretation relation: presence of a
scheduled constitution descriptor yields independent rich evidence through the proved scheduled
constitution CIP model. -/
theorem parserAuditInterpreted?_eq_true_iff (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) (carrierFuel ruleFuel : Nat)
    (annotation : RawAtomAnnotation) :
    parserAuditInterpreted? molecule source agreement writtenExact carrierFuel ruleFuel annotation =
        true ↔
      RawAtomAnnotationInterpretation molecule source agreement writtenExact carrierFuel ruleFuel
        annotation := by
  unfold parserAuditInterpreted? RawAtomAnnotationInterpretation
  rw [List.any_eq_true]
  constructor
  · rintro ⟨candidate, member, matched⟩
    unfold matchingSourceCandidates at member
    rw [List.mem_filter] at member
    have indexEq :
        (parserIndexViaConversion molecule source agreement.1 candidate).val =
          annotation.index :=
      beq_iff_eq.mp member.2
    obtain ⟨specMatched, stateIsSome⟩ := Bool.and_eq_true_iff.mp matched
    refine ⟨candidate, indexEq, ?_, ?_⟩
    · cases observed : molecule.atomAt?
          (parserIndexViaConversion molecule source agreement.1 candidate).val with
      | none => simp [observed] at specMatched
      | some spec =>
          have parityEq : spec.tetrahedral? = some annotation.parity :=
            of_decide_eq_true (by simpa only [observed] using specMatched)
          exact ⟨spec, rfl, parityEq⟩
    · obtain ⟨descriptor, stateEq⟩ := Option.isSome_iff_exists.mp stateIsSome
      exact ⟨descriptor, stateEq,
        constitutionParserRichModel_output_sound molecule source agreement writtenExact
          (constitutionParserRichScheduledState molecule source agreement writtenExact carrierFuel
            ruleFuel)
          (constitutionParserRichScheduledState_cipModel molecule source agreement writtenExact
            carrierFuel ruleFuel)
          (source.aromaticCanonicalFinalOccurrence carrierFuel candidate) descriptor stateEq⟩
  · rintro ⟨candidate, indexEq, specData, descriptor, stateEq, _meaning⟩
    refine ⟨candidate, ?_, ?_⟩
    · unfold matchingSourceCandidates
      rw [List.mem_filter]
      exact ⟨(mem_aromaticCanonicalTetrahedralCenters_iff source candidate).mpr candidate.2,
        beq_iff_eq.mpr indexEq⟩
    · obtain ⟨spec, specEq, parityEq⟩ := specData
      simp [specEq, parityEq, stateEq]






inductive ParserAnnotationAuditIssue where
  | absentSourceCandidate (annotation : RawAtomAnnotation)
  | absentRichDescriptor (annotation : RawAtomAnnotation)
  | unsupportedRawBondDirection (raw : RawBondDirection)
  deriving DecidableEq

noncomputable def parserAuditIssue? (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) (carrierFuel ruleFuel : Nat)
    (annotation : RawAtomAnnotation) : Option ParserAnnotationAuditIssue :=
  if matchingSourceCandidates molecule source agreement annotation = [] then
    some (.absentSourceCandidate annotation)
  else if
    parserAuditInterpreted? molecule source agreement writtenExact carrierFuel ruleFuel annotation =
      true
  then none
  else some (.absentRichDescriptor annotation)

theorem parserAuditIssue?_eq_none_iff (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) (carrierFuel ruleFuel : Nat)
    (annotation : RawAtomAnnotation) :
    parserAuditIssue? molecule source agreement writtenExact carrierFuel ruleFuel annotation = none ↔
      RawAtomAnnotationInterpretation molecule source agreement writtenExact carrierFuel ruleFuel
        annotation := by
  unfold parserAuditIssue?
  by_cases empty : matchingSourceCandidates molecule source agreement annotation = []
  · rw [if_pos empty]
    exact ⟨fun h => absurd h (by simp), fun interpreted =>
      absurd interpreted (not_interpreted_of_no_matching_candidate molecule source agreement
        writtenExact carrierFuel ruleFuel annotation
        ((matchingSourceCandidates_eq_nil_iff molecule source agreement annotation).mp empty))⟩
  · rw [if_neg empty]
    by_cases supported : parserAuditInterpreted? molecule source agreement writtenExact carrierFuel
        ruleFuel annotation = true
    · rw [if_pos supported]
      exact ⟨fun _ => (parserAuditInterpreted?_eq_true_iff molecule source agreement writtenExact
          carrierFuel ruleFuel annotation).mp supported, fun _ => rfl⟩
    · rw [if_neg supported]
      exact ⟨fun h => absurd h (by simp), fun interpreted =>
        absurd ((parserAuditInterpreted?_eq_true_iff molecule source agreement writtenExact
          carrierFuel ruleFuel annotation).mpr interpreted) supported⟩

noncomputable def rawAtomAuditIssues (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) (carrierFuel ruleFuel : Nat) :
    List ParserAnnotationAuditIssue :=
  (rawAtomAnnotations molecule).filterMap
    (parserAuditIssue? molecule source agreement writtenExact carrierFuel ruleFuel)

def rawBondAuditIssues (molecule : RawMolecule) : List ParserAnnotationAuditIssue :=
  (rawBondDirections molecule).map fun raw =>
    ParserAnnotationAuditIssue.unsupportedRawBondDirection raw

theorem rawAtomAuditIssues_eq_nil_iff (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) (carrierFuel ruleFuel : Nat) :
    rawAtomAuditIssues molecule source agreement writtenExact carrierFuel ruleFuel = [] ↔
      ∀ annotation, annotation ∈ rawAtomAnnotations molecule →
        RawAtomAnnotationInterpretation molecule source agreement writtenExact carrierFuel ruleFuel
          annotation := by
  unfold rawAtomAuditIssues
  rw [List.filterMap_eq_nil_iff]
  constructor
  · intro empty annotation present
    exact (parserAuditIssue?_eq_none_iff molecule source agreement writtenExact carrierFuel ruleFuel
      annotation).mp (empty annotation present)
  · intro interpreted annotation present
    exact (parserAuditIssue?_eq_none_iff molecule source agreement writtenExact carrierFuel ruleFuel
      annotation).mpr (interpreted annotation present)

theorem rawBondAuditIssues_eq_nil_iff (molecule : RawMolecule) :
    rawBondAuditIssues molecule = [] ↔ rawBondDirections molecule = [] := by
  simp [rawBondAuditIssues]

/-- Every actual raw directional bond, `false` included, is an unconditional typed issue. -/
theorem rawBondDirection_flagged (molecule : RawMolecule) (raw : RawBondDirection)
    (present : raw ∈ rawBondDirections molecule) :
    ParserAnnotationAuditIssue.unsupportedRawBondDirection raw ∈ rawBondAuditIssues molecule := by
  unfold rawBondAuditIssues
  exact List.mem_map.mpr ⟨raw, present, rfl⟩


noncomputable def parserAnnotationAudit (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) (carrierFuel ruleFuel : Nat) :
    List ParserAnnotationAuditIssue :=
  rawAtomAuditIssues molecule source agreement writtenExact carrierFuel ruleFuel ++
    rawBondAuditIssues molecule




theorem parserAnnotationAudit_eq_nil_iff (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) (carrierFuel ruleFuel : Nat) :
    parserAnnotationAudit molecule source agreement writtenExact carrierFuel ruleFuel = [] ↔
      (∀ annotation, annotation ∈ rawAtomAnnotations molecule →
        RawAtomAnnotationInterpretation molecule source agreement writtenExact carrierFuel ruleFuel
          annotation) ∧
        rawBondDirections molecule = [] := by
  unfold parserAnnotationAudit
  rw [List.append_eq_nil_iff]
  constructor
  · rintro ⟨atomNil, bondNil⟩
    exact ⟨(rawAtomAuditIssues_eq_nil_iff molecule source agreement writtenExact carrierFuel
        ruleFuel).mp atomNil, (rawBondAuditIssues_eq_nil_iff molecule).mp bondNil⟩
  · rintro ⟨interpreted, bondNil⟩
    exact ⟨(rawAtomAuditIssues_eq_nil_iff molecule source agreement writtenExact carrierFuel
        ruleFuel).mpr interpreted, (rawBondAuditIssues_eq_nil_iff molecule).mpr bondNil⟩

/-- Every accepted annotated event has actual checked constitution rich meaning. -/
theorem accepted_raw_parity_has_rich_meaning (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) (carrierFuel ruleFuel : Nat)
    (accepted : parserAnnotationAudit molecule source agreement writtenExact carrierFuel ruleFuel
      = [])
    (annotation : RawAtomAnnotation) (present : annotation ∈ rawAtomAnnotations molecule) :
    ∃ candidate descriptor,
      (parserIndexViaConversion molecule source agreement.1 candidate).val = annotation.index ∧
        constitutionParserRichScheduledState molecule source agreement writtenExact carrierFuel
            ruleFuel (source.aromaticCanonicalFinalOccurrence carrierFuel candidate) =
          some descriptor ∧
          ConstitutionParserRichDescriptorMeaning molecule source agreement writtenExact
            (source.aromaticCanonicalFinalOccurrence carrierFuel candidate)
            (source.aromaticCanonicalDependencyView
              (constitutionParserRichScheduledState molecule source agreement writtenExact
                carrierFuel ruleFuel)
              (source.aromaticCanonicalFinalOccurrence carrierFuel candidate))
            ruleFuel descriptor := by
  obtain ⟨candidate, indexEq, _spec, descriptor, stateEq, meaning⟩ :=
    ((parserAnnotationAudit_eq_nil_iff molecule source agreement writtenExact carrierFuel
      ruleFuel).mp accepted).1 annotation present
  exact ⟨candidate, descriptor, indexEq, stateEq, meaning⟩



noncomputable def parserAnnotationAccepted (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) (carrierFuel ruleFuel : Nat) : Bool :=
  decide (parserAnnotationAudit molecule source agreement writtenExact carrierFuel ruleFuel = [])

theorem parserAnnotationAccepted_eq_true_iff (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact) (carrierFuel ruleFuel : Nat) :
    parserAnnotationAccepted molecule source agreement writtenExact carrierFuel ruleFuel = true ↔
      (∀ annotation, annotation ∈ rawAtomAnnotations molecule →
        RawAtomAnnotationInterpretation molecule source agreement writtenExact carrierFuel ruleFuel
          annotation) ∧
        rawBondDirections molecule = [] := by
  unfold parserAnnotationAccepted
  rw [decide_eq_true_eq]
  exact parserAnnotationAudit_eq_nil_iff molecule source agreement writtenExact carrierFuel ruleFuel

/-! ## 4. Closed actual CFClBrI constitution witness at carrier `0` / rule `2` -/

theorem annotated_rawAtomAnnotations :
    rawAtomAnnotations annotatedRawCF =
      [{ index := 0, parity := TetrahedralInputParity.clockwise }] := by
  decide +kernel

theorem closed_parserScheduledState_eq :
    constitutionParserRichScheduledState annotatedRawCF parserSource
        parserSource_annotationAgreement parserSource_writtenExact 0 2 =
      ClosedConstitutionParserModel.parserScheduledState := rfl

theorem closed_parserTarget_eq :
    parserSource.aromaticCanonicalFinalOccurrence 0 parserCenter = parserTarget := rfl

/-- The actual scheduled constitution parser model assigns `R` at the actual final occurrence. -/
theorem closed_scheduled_state_R :
    constitutionParserRichScheduledState annotatedRawCF parserSource parserSource_annotationAgreement
        parserSource_writtenExact 0 2
        (parserSource.aromaticCanonicalFinalOccurrence 0 parserCenter) = some (.chiral RS.R) := by
  rw [closed_parserScheduledState_eq, closed_parserTarget_eq]
  exact ClosedConstitutionParserModel.parser_scheduled_R

/-- The actual scheduled `R` carries its complete checked constitution rich meaning. -/
theorem closed_scheduled_R_meaning :
    ConstitutionParserRichDescriptorMeaning annotatedRawCF parserSource
      parserSource_annotationAgreement parserSource_writtenExact
      (parserSource.aromaticCanonicalFinalOccurrence 0 parserCenter)
      (parserSource.aromaticCanonicalDependencyView
        (constitutionParserRichScheduledState annotatedRawCF parserSource
          parserSource_annotationAgreement parserSource_writtenExact 0 2)
        (parserSource.aromaticCanonicalFinalOccurrence 0 parserCenter))
      2 (.chiral RS.R) := by
  rw [closed_parserScheduledState_eq, closed_parserTarget_eq]
  exact ClosedConstitutionParserModel.parser_scheduled_R_meaning

/-- The actual carbon `@@` raw parity is genuinely interpreted at carrier `0` / rule `2`. -/
theorem closed_raw_parity_interpreted :
    RawAtomAnnotationInterpretation annotatedRawCF parserSource parserSource_annotationAgreement
      parserSource_writtenExact 0 2
      { index := 0, parity := TetrahedralInputParity.clockwise } := by
  refine ⟨parserCenter,
    ConstitutionClosedWitness.parserSource_index_identity, ?_, .chiral RS.R,
    closed_scheduled_state_R, closed_scheduled_R_meaning⟩
  exact ⟨_,
    SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence.ClosedParserWitness.parserSource_atom,
    SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence.ClosedParserWitness.parserSource_spec_parity⟩


theorem closed_audit_nil :
    parserAnnotationAudit annotatedRawCF parserSource parserSource_annotationAgreement
        parserSource_writtenExact 0 2 = [] := by
  rw [parserAnnotationAudit_eq_nil_iff]
  refine ⟨?_, ?_⟩
  · intro annotation present
    rw [annotated_rawAtomAnnotations, List.mem_singleton] at present
    rw [present]
    exact closed_raw_parity_interpreted
  · decide +kernel



theorem closed_parserAnnotationAccepted_true :
    parserAnnotationAccepted annotatedRawCF parserSource parserSource_annotationAgreement
      parserSource_writtenExact 0 2 = true :=
  (parserAnnotationAccepted_eq_true_iff annotatedRawCF parserSource parserSource_annotationAgreement
    parserSource_writtenExact 0 2).mpr
    ((parserAnnotationAudit_eq_nil_iff annotatedRawCF parserSource parserSource_annotationAgreement
      parserSource_writtenExact 0 2).mp closed_audit_nil)

/-! ## 5. Negatives: an unsupported direction and a remote parity -/

/-- The carbon annotation with its first ligand bond carrying a `down` (`\`, `false`) marker. -/
def directionalRawCF : RawMolecule :=
  { annotatedRawCF with
    bonds := [⟨0, 1, .down⟩, ⟨0, 2, .single⟩, ⟨0, 3, .single⟩, ⟨0, 4, .single⟩] }

theorem directionalRawCF_toSemanticMolecule :
    directionalRawCF.toSemanticMolecule? = some SingleWedgeSourceRegression.molecule := by
  decide +kernel

theorem directionalRawCF_writtenExact : directionalRawCF.WrittenNeighborExact :=
  (directionalRawCF.writtenNeighborExact?_eq_true_iff).mp (by decide +kernel)

def directionalSource : AuthoritativeChemicalInput :=
  { molecule := SingleWedgeSourceRegression.molecule
    diagram? := some directionalRawCF.toDiagramConfiguration }

/-- The directional raw molecule still satisfies the weaker conversion-pinned record agreement:
the `down` record matches the materialized `directionalDown` diagram bond exactly. -/
theorem directionalSource_annotationAgreement :
    RawAnnotationAgreement directionalRawCF directionalSource :=
  ⟨directionalRawCF_toSemanticMolecule,
    (rawAnnotationAgreementIssues_eq_nil_iff directionalRawCF directionalSource).mp
      (by decide +kernel)⟩

theorem directional_rawRecord_present :
    ({ bond := ⟨0, 1, .down⟩, direction := false } : RawBondDirection) ∈
      rawBondDirections directionalRawCF :=
  (mem_rawBondDirections_iff directionalRawCF
    { bond := ⟨0, 1, .down⟩, direction := false }).mpr ⟨by decide +kernel, rfl⟩

/-- The actual `down` record is refused even though the record agreement holds: directional
interpretation is absent, so no directional record is ever interpreted. -/
theorem directional_audit_rejects :
    parserAnnotationAudit directionalRawCF directionalSource directionalSource_annotationAgreement
        directionalRawCF_writtenExact 0 2 ≠ [] := by
  intro empty
  have member :=
    rawBondDirection_flagged directionalRawCF { bond := ⟨0, 1, .down⟩, direction := false }
      directional_rawRecord_present
  have present : ParserAnnotationAuditIssue.unsupportedRawBondDirection
      { bond := ⟨0, 1, .down⟩, direction := false } ∈
      parserAnnotationAudit directionalRawCF directionalSource directionalSource_annotationAgreement
        directionalRawCF_writtenExact 0 2 := by
    unfold parserAnnotationAudit
    exact List.mem_append.mpr (Or.inr member)
  rw [empty] at present
  exact List.not_mem_nil present

/-- The same constitution with the remote fluorine index `1` carrying a raw `@@` (`clockwise`)
parity, in addition to the carbon. -/
def remoteParityRawCF : RawMolecule :=
  { annotatedRawCF with
    atoms :=
      [{ AtomSpec.aliphatic .C with tetrahedral? := some .clockwise },
        { AtomSpec.aliphatic .F with tetrahedral? := some .clockwise },
        AtomSpec.aliphatic .Cl, AtomSpec.aliphatic .Br, AtomSpec.aliphatic .I] }

theorem remoteParityRawCF_toSemanticMolecule :
    remoteParityRawCF.toSemanticMolecule? = some SingleWedgeSourceRegression.molecule := by
  decide +kernel

theorem remoteParityRawCF_writtenExact : remoteParityRawCF.WrittenNeighborExact :=
  (remoteParityRawCF.writtenNeighborExact?_eq_true_iff).mp (by decide +kernel)

def remoteSource : AuthoritativeChemicalInput :=
  { molecule := SingleWedgeSourceRegression.molecule
    diagram? := some remoteParityRawCF.toDiagramConfiguration }

/-- The remote-parity raw molecule also satisfies the weaker conversion-pinned record agreement:
both raw parities are matched by their materialized absolute atom configurations. -/
theorem remoteSource_annotationAgreement :
    RawAnnotationAgreement remoteParityRawCF remoteSource :=
  ⟨remoteParityRawCF_toSemanticMolecule,
    (rawAnnotationAgreementIssues_eq_nil_iff remoteParityRawCF remoteSource).mp
      (by decide +kernel)⟩

/-- The fluorine atom at source index `1` is an element outside the connectivity-only tetrahedral
domain, so no source candidate can carry that raw index. -/
abbrev remoteSource_one : remoteSource.AromaticCanonicalAtom := ⟨1, by decide⟩

theorem remoteSource_one_not_eligible :
    ¬ remoteSource.ConnectivityOnlyTetrahedralCenterAtom remoteSource_one := by
  unfold remoteSource_one ConnectivityOnlyTetrahedralCenterAtom
    ConnectivityOnlyTetrahedralPeriodicElement
  decide +kernel

theorem remoteSource_not_eligible_of_val_eq_one (center : remoteSource.AromaticCanonicalAtom)
    (valEq : center.val = 1) : ¬ remoteSource.ConnectivityOnlyTetrahedralCenterAtom center := by
  have same : center = remoteSource_one := Fin.ext valEq
  rw [same]
  exact remoteSource_one_not_eligible

theorem remoteParity_no_matching_candidate
    (candidate : remoteSource.AromaticCanonicalTetrahedralCenter)
    (indexEq : (parserIndexViaConversion remoteParityRawCF remoteSource
      remoteSource_annotationAgreement.1 candidate).val = 1) : False := by
  have valEq : candidate.1.val = 1 := indexEq
  have eligible : remoteSource.ConnectivityOnlyTetrahedralCenterAtom candidate.1 :=
    ((remoteSource.mem_aromaticCanonicalTetrahedralCenterSet_iff candidate.1).mp candidate.2).1
  exact remoteSource_not_eligible_of_val_eq_one candidate.1 valEq eligible

theorem remoteParity_candidates_empty :
    matchingSourceCandidates remoteParityRawCF remoteSource remoteSource_annotationAgreement
        { index := 1, parity := TetrahedralInputParity.clockwise } = [] :=
  (matchingSourceCandidates_eq_nil_iff remoteParityRawCF remoteSource remoteSource_annotationAgreement
    _).mpr fun candidate indexEq => remoteParity_no_matching_candidate candidate indexEq

theorem remoteParity_rawRecord_present :
    ({ index := 1, parity := TetrahedralInputParity.clockwise } : RawAtomAnnotation) ∈
      rawAtomAnnotations remoteParityRawCF := by
  decide +kernel

/-- The fluorine raw parity at an element-ineligible index is refused as a typed issue even though
the record agreement holds. -/
theorem remoteParity_audit_rejects :
    parserAnnotationAudit remoteParityRawCF remoteSource remoteSource_annotationAgreement
        remoteParityRawCF_writtenExact 0 2 ≠ [] := by
  intro empty
  have present : ParserAnnotationAuditIssue.absentSourceCandidate
      { index := 1, parity := TetrahedralInputParity.clockwise } ∈
      parserAnnotationAudit remoteParityRawCF remoteSource remoteSource_annotationAgreement
        remoteParityRawCF_writtenExact 0 2 := by
    unfold parserAnnotationAudit
    refine List.mem_append.mpr (Or.inl ?_)
    unfold rawAtomAuditIssues
    rw [List.mem_filterMap]
    exact ⟨{ index := 1, parity := TetrahedralInputParity.clockwise }, remoteParity_rawRecord_present,
      by simp [parserAuditIssue?, remoteParity_candidates_empty]⟩
  rw [empty] at present
  exact List.not_mem_nil present

end TetraStereo.UniversalProof.SourceNativeConstitutionParserAnnotationAuditProofs.SourceNativeConstitutionParserAnnotationAudit
