import TetraStereo.UniversalProof.SourceNativePlanarParserCausalModelProofs.SourceNativePlanarParserCausalModel
import TetraStereo.OneCenter.CIPAuthoritativeStereoAssignmentConformance
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace TetraStereo.UniversalProof.SourceNativeExecutableParserRefinementProofs.SourceNativeExecutableParserRefinement

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
























/-! ## 1. Four distinct written indices -/

/-- Four distinct written indices at the recovered center. The compatibility name does not imply
distinct atomic numbers or priorities; those are proved separately for the closed witnesses. -/
def AtomicWrittenLigands (raw : RawMolecule) (index : Fin raw.atomCount) : Prop :=
  (rawWrittenLigandFrame raw index).length = 4 ∧ (rawWrittenLigandFrame raw index).Nodup

/-- The anticlockwise written-frame descriptor is the `RS.swap` of the clockwise one at the same
actual written slots and actual priority order.  This is the written-parity mirror used by the
closed anticlockwise witness. -/
theorem writtenFramePriorityDescriptor_anticlockwise_eq_swap
    (slots : List Nat) (order : List (Fin 4)) :
    writtenFramePriorityDescriptor TetrahedralInputParity.anticlockwise slots order =
      RS.swap (writtenFramePriorityDescriptor TetrahedralInputParity.clockwise slots order) := by
  unfold writtenFramePriorityDescriptor RawMolecule.descriptorOfParity
  cases RawMolecule.permutationIsEven (order.map fun position => slots.getD position.val 0) <;> rfl

/-- The actual parser evidence's own raw descriptor is its written-frame descriptor at its actual
returned priority order.  Derived from the soundness meaning, never assumed. -/
theorem constitutionParserRichPriorityEvidence_raw_self
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source) (writtenExact : molecule.WrittenNeighborExact)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (evidence : ParserRichPriorityEvidence source carrierFuel)
    (computed : constitutionParserRichPriorityEvidence? molecule source agreement writtenExact
      target view ruleFuel = some evidence) :
    evidence.raw = writtenFramePriorityDescriptor evidence.writtenParity evidence.slots
      evidence.tracked.highestFirst := by
  obtain ⟨_writtenExact, center, roots, spec, writtenParity, configuration, slotPerm,
    _h1, _h2, _h3, h4, _h5, _h6, _h7, _h8, _h9, _h10, _h11, _h12, _h13, _h14, _h15, h16⟩ :=
    constitutionParserRichPriorityEvidence?_sound molecule source agreement writtenExact
      target view ruleFuel evidence computed
  rw [h4]
  exact h16

/-- The actual authoritative occurrence-fact descriptor is `descriptorOfParity` at the fact's own
actual priority positions.  Derived from the primitive-stage certificate, never assumed. -/
theorem AuthoritativeTetrahedralOccurrenceFactJudgment.descriptor_eq_descriptorOfParity
    (mol : RawMolecule) (fuel center : Nat) (fact : RawDescriptorFact)
    (judgment : AuthoritativeTetrahedralOccurrenceFactJudgment mol fuel center fact) :
    ∃ parity positions,
      fact.descriptor = RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven positions) ∧
        fact.priorityPositions = positions := by
  unfold AuthoritativeTetrahedralOccurrenceFactJudgment at judgment
  obtain ⟨aux, occurrenceFact, auxEq, clauses, factEq⟩ := judgment
  unfold AuthoritativeOrdinaryFactClauses at clauses
  obtain ⟨certificate⟩ := clauses
  cases certificate with
  | legacy unavailable certificate =>
      exact ⟨certificate.parity, certificate.positions,
        by simp only [factEq, certificate.fact_eq],
        by simp only [factEq, certificate.fact_eq]⟩
  | framed certificate =>
      exact ⟨certificate.parity, certificate.positions,
        by simp only [factEq, certificate.fact_eq],
        by simp only [factEq, certificate.fact_eq]⟩

/-! ## 2. The four-distinct-written-index no-ordinary-double-bond input class -/






structure AtomicSeparatedNoDoubleRequest where
  raw : RawMolecule
  certified : CertifiedChemistryNormalizationResult
  /-- normalization provenance: the certificate's result is the actual normalizer's result -/
  normalizationEq : certified.result = normalizeRawMolecule raw
  /-- the actual normalized parsed record is the unchanged literal raw input -/
  parsedEq : certified.result.parsed = raw
  source : AuthoritativeChemicalInput
  agreement : RawAnnotationAgreement raw source
  writtenExact : raw.WrittenNeighborExact
  noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond
  carrierFuel : Nat
  ruleFuel : Nat
  center : source.AromaticCanonicalTetrahedralCenter
  /-- four distinct indices in the recovered center's written environment -/
  atomicLigands : AtomicWrittenLigands raw
    (parserIndexViaConversion raw source agreement.1 center)

namespace AtomicSeparatedNoDoubleRequest

variable (request : AtomicSeparatedNoDoubleRequest)

/-- The real raw atom index returned for the recovered center by the conversion-only parser index. -/
def centerIndex : Nat :=
  (parserIndexViaConversion request.raw request.source request.agreement.1 request.center).val

/-- The recovered center index is an actual raw atom index. -/
theorem centerIndex_lt : request.centerIndex < request.raw.atomCount :=
  (parserIndexViaConversion request.raw request.source request.agreement.1 request.center).isLt

/-- The real raw atom index is exactly the actual source center's numerical value. -/
theorem centerIndex_eq_source : request.centerIndex = request.center.val.val :=
  parserIndexViaConversion_val request.raw request.source request.agreement.1 request.center

/-- The four-distinct-index property holds at the recovered real index. -/
theorem atomicLigands_at_index :
    (rawWrittenLigandFrame request.raw
        (parserIndexViaConversion request.raw request.source request.agreement.1
          request.center)).length = 4 ∧
      (rawWrittenLigandFrame request.raw
        (parserIndexViaConversion request.raw request.source request.agreement.1
          request.center)).Nodup :=
  request.atomicLigands




theorem planar_eq_constitution {carrierFuel : Nat}
    (target : request.source.AromaticCanonicalOccurrence carrierFuel)
    (view : request.source.AromaticCanonicalDependencyView target) :
    TetraStereo.UniversalProof.SourceNativePlanarParserOccurrenceProofs.SourceNativePlanarParserOccurrence.planarConstitutionParserRichDescriptor?
        request.raw request.source request.agreement request.writtenExact target view request.ruleFuel =
      constitutionParserRichDescriptor? request.raw request.source request.agreement
        request.writtenExact target view request.ruleFuel :=
  TetraStereo.UniversalProof.SourceNativePlanarParserCausalModelProofs.SourceNativePlanarParserCausalModel.planarConstitutionParserRichDescriptor?_eq_constitution_of_noDouble
    request.raw request.source request.agreement request.writtenExact request.noDouble
    target view request.ruleFuel

end AtomicSeparatedNoDoubleRequest

/-! ## 3. Conditional fact/evidence label agreement -/

/-- Conditional two-input label algebra, forward direction. From the authoritative occurrence-fact
judgment on `mol` and the parser priority evidence on `molecule` at the actual
target, under the explicit written-parity binding and the priority-permutation parity alignment
(the comparator/cursor alignment), and requiring the actual classification to be chiral, the
executable authoritative outcome is exactly the chiral label whose `RS` value is the parser's actual
raw written-frame descriptor.

The written-parity and priority-permutation bindings are explicit assumptions. There is no
same-request binding between `mol` and `molecule`, and this algebraic lemma supplies no
arbitrary-input executable refinement. The closed same-request equivalences below do not use it. -/
theorem executableAuthoritativeOutcome_refines_parserChiral
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact)
    (mol : RawMolecule) (fuel centerIndex : Nat) (fact : RawDescriptorFact)
    (_judgment : AuthoritativeTetrahedralOccurrenceFactJudgment mol fuel centerIndex fact)
    (uppercase : fact.uppercase = true)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (evidence : ParserRichPriorityEvidence source carrierFuel)
    (evidenceComputed : constitutionParserRichPriorityEvidence? molecule source agreement writtenExact
      target view ruleFuel = some evidence)
    (parity : TetrahedralInputParity) (positions : List Nat)
    (descriptorForm : fact.descriptor = RawMolecule.descriptorOfParity parity
      (RawMolecule.permutationIsEven positions))
    (_priorityPositions : fact.priorityPositions = positions)
    (writtenParityEq : evidence.writtenParity = parity)
    (orderParityEq : RawMolecule.permutationIsEven positions =
      RawMolecule.permutationIsEven
        (evidence.tracked.highestFirst.map fun position => evidence.slots.getD position.val 0))
    (pseudoNotOne : evidence.tracked.pseudoComparisons ≠ 1) :
    authoritativeOccurrenceOutcome fact = StereoOutcome.tetrahedral evidence.raw ∧
      classifyTetrahedralRSPseudo evidence.raw evidence.tracked.pseudoComparisons =
        .chiral evidence.raw := by
  have rawSelf := constitutionParserRichPriorityEvidence_raw_self molecule source agreement
    writtenExact target view ruleFuel evidence evidenceComputed
  have rawForm : evidence.raw = RawMolecule.descriptorOfParity parity
      (RawMolecule.permutationIsEven positions) := by
    rw [rawSelf, writtenParityEq]
    unfold writtenFramePriorityDescriptor
    rw [orderParityEq]
  have descriptorEq : fact.descriptor = evidence.raw := by
    rw [descriptorForm, rawForm]
  constructor
  · unfold authoritativeOccurrenceOutcome
    rw [uppercase]
    simp [descriptorEq]
  · unfold classifyTetrahedralRSPseudo
    rw [if_neg pseudoNotOne]

/-- The same conditional two-input label agreement in both directions for one chiral label: under the alignment and chirality
hypotheses the executable authoritative outcome carries `d` exactly when the parser classifies its
actual raw written-frame descriptor as the chiral `d`. -/
theorem executableAuthoritativeChiral_iff_parserChiral
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact)
    (mol : RawMolecule) (fuel centerIndex : Nat) (fact : RawDescriptorFact)
    (judgment : AuthoritativeTetrahedralOccurrenceFactJudgment mol fuel centerIndex fact)
    (uppercase : fact.uppercase = true)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (evidence : ParserRichPriorityEvidence source carrierFuel)
    (evidenceComputed : constitutionParserRichPriorityEvidence? molecule source agreement writtenExact
      target view ruleFuel = some evidence)
    (parity : TetrahedralInputParity) (positions : List Nat)
    (descriptorForm : fact.descriptor = RawMolecule.descriptorOfParity parity
      (RawMolecule.permutationIsEven positions))
    (priorityPositions : fact.priorityPositions = positions)
    (writtenParityEq : evidence.writtenParity = parity)
    (orderParityEq : RawMolecule.permutationIsEven positions =
      RawMolecule.permutationIsEven
        (evidence.tracked.highestFirst.map fun position => evidence.slots.getD position.val 0))
    (pseudoNotOne : evidence.tracked.pseudoComparisons ≠ 1) (d : RS) :
    authoritativeOccurrenceOutcome fact = StereoOutcome.tetrahedral d ↔
      classifyTetrahedralRSPseudo evidence.raw evidence.tracked.pseudoComparisons = .chiral d := by
  have h := executableAuthoritativeOutcome_refines_parserChiral molecule source agreement writtenExact
    mol fuel centerIndex fact judgment uppercase target view ruleFuel evidence evidenceComputed
    parity positions descriptorForm priorityPositions writtenParityEq orderParityEq pseudoNotOne
  constructor
  · intro outcomeEq
    rw [h.2]
    have same : d = evidence.raw := by
      rw [h.1] at outcomeEq
      exact (StereoOutcome.tetrahedral.inj outcomeEq).symm
    rw [same]
  · intro classEq
    rw [h.1]
    have same : d = evidence.raw := by
      rw [h.2] at classEq
      exact (LocalizedTetrahedralRSPseudoDescriptor.chiral.inj classEq).symm
    rw [same]

/-! ## 4. Assignment-level refinement at the public output boundary -/

/-- Every authoritative occurrence assignment emitted by the executable override carries the
recovered real atom index and the authoritative occurrence-fact outcome; combining with section 3
gives the parser-descriptor refinement at the actual `StereoAssignment` surface.  The assignment
equality and the fact judgment are exposed as explicit premises, so no existential is projected. -/
theorem authoritativeAssignment_refines_parserChiral
    (result : ChemistryNormalizationResult) (centerIndex : Nat)
    (assignment : StereoAssignment) (fact : RawDescriptorFact)
    (assignmentEq : assignment =
      { unit := StereoUnit.tetrahedral centerIndex
        outcome := authoritativeOccurrenceOutcome fact })
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement molecule source)
    (writtenExact : molecule.WrittenNeighborExact)
    (judgment : AuthoritativeTetrahedralOccurrenceFactJudgment
      result.parsed.withExplicitHydrogens (analysisFuel result.parsed.withExplicitHydrogens)
      centerIndex fact)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (evidence : ParserRichPriorityEvidence source carrierFuel)
    (evidenceComputed : constitutionParserRichPriorityEvidence? molecule source agreement writtenExact
      target view ruleFuel = some evidence)
    (uppercase : fact.uppercase = true)
    (parity : TetrahedralInputParity) (positions : List Nat)
    (descriptorForm : fact.descriptor =
      RawMolecule.descriptorOfParity parity (RawMolecule.permutationIsEven positions))
    (priorityPositions : fact.priorityPositions = positions)
    (writtenParityEq : evidence.writtenParity = parity)
    (orderParityEq : RawMolecule.permutationIsEven positions =
      RawMolecule.permutationIsEven
        (evidence.tracked.highestFirst.map fun position => evidence.slots.getD position.val 0))
    (pseudoNotOne : evidence.tracked.pseudoComparisons ≠ 1) :
    assignment.unit = StereoUnit.tetrahedral centerIndex ∧
      assignment.outcome = StereoOutcome.tetrahedral evidence.raw ∧
      classifyTetrahedralRSPseudo evidence.raw evidence.tracked.pseudoComparisons =
        .chiral evidence.raw := by
  have h := executableAuthoritativeOutcome_refines_parserChiral molecule source agreement writtenExact
    result.parsed.withExplicitHydrogens (analysisFuel result.parsed.withExplicitHydrogens) centerIndex
    fact judgment uppercase target view ruleFuel evidence evidenceComputed parity positions
    descriptorForm priorityPositions writtenParityEq orderParityEq pseudoNotOne
  refine ⟨?_, ?_, h.2⟩
  · rw [assignmentEq]
  · rw [assignmentEq]
    exact h.1

/-! ## 5. Closed actual CFClBrI witnesses, both written parities -/

namespace ClosedExecutableBridge

open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment.ClosedParserWitness
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence.ClosedParserWitness
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge.ConstitutionClosedWitness

/-- The actual certified normalized clockwise CFClBrI input of the committed counterexample. -/
abbrev certifiedClockwise : CertifiedChemistryNormalizationResult :=
  TetraStereo.UniversalProof.SourceNativeRawAnnotationGuardProofs.SourceNativeRawAnnotationGuard.ClosedRawCounterexample.annotatedCertifiedCF

/-- The literal CFClBrI constitution with the carbon's written parity reversed to `@`. -/
def anticlockwiseRaw : RawMolecule where
  atoms := [{ AtomSpec.aliphatic .C with tetrahedral? := some TetrahedralInputParity.anticlockwise },
    AtomSpec.aliphatic .F, AtomSpec.aliphatic .Cl, AtomSpec.aliphatic .Br, AtomSpec.aliphatic .I]
  bonds := [⟨0, 1, .single⟩, ⟨0, 2, .single⟩, ⟨0, 3, .single⟩, ⟨0, 4, .single⟩]

theorem anticlockwiseRaw_toSemanticMolecule :
    anticlockwiseRaw.toSemanticMolecule? = some parserSource.molecule := by
  decide +kernel

/-- The same source molecule with the literal anticlockwise raw annotation materialized. -/
def anticlockwiseSource : AuthoritativeChemicalInput :=
  { parserSource with diagram? := some anticlockwiseRaw.toDiagramConfiguration }

theorem anticlockwiseSource_audit :
    rawAnnotationAgreementIssues anticlockwiseRaw anticlockwiseSource = [] := by
  decide +kernel

theorem anticlockwiseSource_annotationAgreement :
    RawAnnotationAgreement anticlockwiseRaw anticlockwiseSource :=
  ⟨anticlockwiseRaw_toSemanticMolecule,
    (rawAnnotationAgreementIssues_eq_nil_iff anticlockwiseRaw anticlockwiseSource).mp
      anticlockwiseSource_audit⟩

theorem anticlockwiseRaw_writtenExact : anticlockwiseRaw.WrittenNeighborExact :=
  (anticlockwiseRaw.writtenNeighborExact?_eq_true_iff).mp (by decide +kernel)

theorem anticlockwiseSource_no_ordinary_double_bond :
    anticlockwiseSource.NoAromaticCanonicalOrdinaryDoubleBond := by
  intro left right ordinary
  have different : anticlockwiseSource.molecule.aromaticCanonicalBondOrder left.val right.val ≠ 2 := by
    fin_cases left <;> fin_cases right <;> decide +kernel
  exact different ordinary.2

theorem anticlockwiseRaw_atom :
    anticlockwiseRaw.atomAt? 0 =
      some { AtomSpec.aliphatic .C with tetrahedral? := some TetrahedralInputParity.anticlockwise } :=
  rfl

/-- The actual raw written frame of the recovered clockwise center is the literal written order. -/
theorem clockwise_index_identity :
    (parserIndexViaConversion annotatedRawCF parserSource parserSource_annotationAgreement.1
      parserCenter).val = 0 := rfl

theorem clockwise_raw_frame :
    rawWrittenLigandFrame annotatedRawCF
      (parserIndexViaConversion annotatedRawCF parserSource parserSource_annotationAgreement.1
        parserCenter) = [1, 2, 3, 4] := by
  unfold rawWrittenLigandFrame
  rw [clockwise_index_identity]
  exact parserSource_written_endpoints

theorem clockwise_atomicLigands : AtomicWrittenLigands annotatedRawCF
    (parserIndexViaConversion annotatedRawCF parserSource parserSource_annotationAgreement.1
      parserCenter) := by
  constructor <;> rw [clockwise_raw_frame] <;> decide

/-- The four-distinct-written-index no-double request at the actual clockwise CFClBrI input. -/
noncomputable def clockwiseRequest : AtomicSeparatedNoDoubleRequest where
  raw := annotatedRawCF
  certified := certifiedClockwise
  normalizationEq := rfl
  parsedEq := rfl
  source := parserSource
  agreement := parserSource_annotationAgreement
  writtenExact := parserSource_writtenExact
  noDouble := parserSource_no_ordinary_double_bond
  carrierFuel := 0
  ruleFuel := 2
  center := parserCenter
  atomicLigands := clockwise_atomicLigands

/-- The actual executable authority-facing output for the clockwise CFClBrI input, evaluated. -/
theorem clockwise_executable_output :
    analyzeCertifiedNormalized certifiedClockwise =
      [{ unit := StereoUnit.tetrahedral 0, outcome := StereoOutcome.tetrahedral RS.R }] := by
  decide +kernel

/-- The actual constitution parser channel emits the matching chiral `R` at the actual target. -/
theorem clockwise_parser_R
    (view : parserSource.AromaticCanonicalDependencyView
      TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserWitness.parserTarget) :
    constitutionParserRichDescriptor? annotatedRawCF parserSource parserSource_annotationAgreement
      parserSource_writtenExact
      TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserWitness.parserTarget view 2 =
      some (.chiral RS.R) :=
  ClosedConstitutionParserModel.parser_actual_constitution_descriptor_R view


theorem clockwise_planar_R
    (view : parserSource.AromaticCanonicalDependencyView
      TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserWitness.parserTarget) :
    TetraStereo.UniversalProof.SourceNativePlanarParserOccurrenceProofs.SourceNativePlanarParserOccurrence.planarConstitutionParserRichDescriptor?
        annotatedRawCF parserSource parserSource_annotationAgreement parserSource_writtenExact
        TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserWitness.parserTarget view 2 =
      some (.chiral RS.R) :=
  TetraStereo.UniversalProof.SourceNativePlanarParserCausalModelProofs.SourceNativePlanarParserCausalModel.ClosedPlanarParserModel.parser_actual_planar_descriptor_R
    view

/-- The actual planar `R` carries the complete independent NEW planar meaning. -/
theorem clockwise_planar_R_meaning :
    TetraStereo.UniversalProof.SourceNativePlanarParserOccurrenceProofs.SourceNativePlanarParserOccurrence.PlanarConstitutionParserRichDescriptorMeaning
      annotatedRawCF parserSource parserSource_annotationAgreement parserSource_writtenExact
      TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserWitness.parserTarget
      (parserSource.aromaticCanonicalDependencyView
        TetraStereo.UniversalProof.SourceNativePlanarParserCausalModelProofs.SourceNativePlanarParserCausalModel.ClosedPlanarParserModel.parserScheduledState
        TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserWitness.parserTarget)
      2 (.chiral RS.R) :=
  TetraStereo.UniversalProof.SourceNativePlanarParserCausalModelProofs.SourceNativePlanarParserCausalModel.ClosedPlanarParserModel.parser_scheduled_R_meaning

theorem clockwise_member (d : RS) :
    ({ unit := StereoUnit.tetrahedral 0, outcome := StereoOutcome.tetrahedral d } :
        StereoAssignment) ∈ analyzeCertifiedNormalized certifiedClockwise ↔ d = RS.R := by
  rw [clockwise_executable_output]
  cases d <;> decide +kernel

/-! ### Anticlockwise source: own center, roots, frame and priorities -/

noncomputable def antiCenter : anticlockwiseSource.AromaticCanonicalTetrahedralCenter :=
  parserCenter

noncomputable def antiTarget : anticlockwiseSource.AromaticCanonicalOccurrence 0 :=
  anticlockwiseSource.aromaticCanonicalFinalOccurrence 0 antiCenter

noncomputable def antiRoots : List (anticlockwiseSource.AromaticCanonicalRerootCursor 0) :=
  finalOccurrenceRoots anticlockwiseSource 0 antiCenter

theorem antiRoots_length : antiRoots.length = 4 := by rfl

noncomputable def antiFrame : anticlockwiseSource.AromaticCanonicalOccurrenceFourLigandFrame 0 :=
  { roots := antiRoots, rootsLength := antiRoots_length }

theorem antiTarget_roots_returned :
    anticlockwiseSource.aromaticCanonicalOccurrenceLigandFrame? antiTarget = some antiFrame.roots :=
  finalOccurrenceRoots_are_returned anticlockwiseSource 0 antiCenter

theorem anti_index_identity :
    (parserIndexViaConversion anticlockwiseRaw anticlockwiseSource
      anticlockwiseSource_annotationAgreement.1 antiCenter).val = 0 := rfl

theorem anticlockwiseRaw_written_endpoints :
    anticlockwiseRaw.writtenNeighbors 0 = [1, 2, 3, 4] := by
  decide +kernel

theorem anti_raw_frame :
    rawWrittenLigandFrame anticlockwiseRaw
      (parserIndexViaConversion anticlockwiseRaw anticlockwiseSource
        anticlockwiseSource_annotationAgreement.1 antiCenter) = [1, 2, 3, 4] := by
  unfold rawWrittenLigandFrame
  rw [anti_index_identity]
  exact anticlockwiseRaw_written_endpoints

theorem anti_root_ids :
    occurrenceRootIDs anticlockwiseSource antiRoots = [some 1, some 2, some 3, some 4] := by rfl

theorem anti_slot_alignment :
    findSlotAlignment?
      (rawWrittenLigandFrame anticlockwiseRaw
        (parserIndexViaConversion anticlockwiseRaw anticlockwiseSource
          anticlockwiseSource_annotationAgreement.1 antiCenter))
      (occurrenceRootIDs anticlockwiseSource antiRoots) = some [0, 1, 2, 3] := by
  rw [anti_raw_frame, anti_root_ids]
  decide +kernel

theorem antiRoots_real : OccurrenceRootsReal anticlockwiseSource antiFrame := by
  intro slot
  fin_cases slot <;> exact ⟨_, rfl, rfl⟩

def antiAtomicPriorityValue : Fin 4 → Nat
  | ⟨0, _⟩ => 9
  | ⟨1, _⟩ => 17
  | ⟨2, _⟩ => 35
  | ⟨3, _⟩ => 53

theorem anti_actual_atomic_priority (slot : Fin 4) :
    occurrenceAtomicPriority anticlockwiseSource antiFrame slot = antiAtomicPriorityValue slot := by
  fin_cases slot <;> rfl

theorem anti_actual_atomic_priority_injective :
    Function.Injective (occurrenceAtomicPriority anticlockwiseSource antiFrame) := by
  have injective : Function.Injective antiAtomicPriorityValue := by decide +kernel
  intro left right equal
  apply injective
  simpa only [anti_actual_atomic_priority] using equal

theorem anti_actual_priority_order_unique (order : List (Fin 4))
    (perm : order.Perm (List.finRange 4))
    (descending : order.Pairwise (fun left right =>
      occurrenceAtomicPriority anticlockwiseSource antiFrame right <
        occurrenceAtomicPriority anticlockwiseSource antiFrame left)) :
    order = [3, 2, 1, 0] := by
  have reversedPerm : ([3, 2, 1, 0] : List (Fin 4)).Perm (List.finRange 4) := by decide +kernel
  have reversedDescending : ([3, 2, 1, 0] : List (Fin 4)).Pairwise (fun left right =>
      occurrenceAtomicPriority anticlockwiseSource antiFrame right <
        occurrenceAtomicPriority anticlockwiseSource antiFrame left) := by
    simp only [anti_actual_atomic_priority]
    decide +kernel
  exact (perm.trans reversedPerm.symm).eq_of_pairwise
    (fun _ _ _ _ higher reverse => False.elim (Nat.lt_asymm higher reverse))
    descending reversedDescending

/-- The actual constitution parser channel emits the matching chiral `S` at the actual anticlockwise
target for every dependency view, from the actual production key/sort, strict priority uniqueness
and the actual reversed written parity. -/
theorem anti_parser_S
    (view : anticlockwiseSource.AromaticCanonicalDependencyView antiTarget) :
    constitutionParserRichDescriptor? anticlockwiseRaw anticlockwiseSource
      anticlockwiseSource_annotationAgreement anticlockwiseRaw_writtenExact antiTarget view 2 =
      some (.chiral RS.S) := by
  obtain ⟨keys, tracked, keysComputed, trackedComputed, perm, descending, zero⟩ :=
    exists_occurrence_production_keys_and_safe_order anticlockwiseSource antiTarget view antiFrame
      antiTarget_roots_returned antiRoots_real anti_actual_atomic_priority_injective
      anticlockwiseSource_no_ordinary_double_bond
  have keysComputed2 : anticlockwiseSource.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      antiTarget view 2 antiRoots = some keys := keysComputed
  have orderEq := anti_actual_priority_order_unique tracked.highestFirst perm descending
  have writtenOrder : tracked.highestFirst.map
      (fun position => ([0, 1, 2, 3] : List Nat).getD position.val 0) = [3, 2, 1, 0] := by
    rw [orderEq]
    rfl
  have rawEq : writtenFramePriorityDescriptor TetrahedralInputParity.anticlockwise [0, 1, 2, 3]
      tracked.highestFirst = RS.S := by
    rw [writtenFramePriorityDescriptor_anticlockwise_eq_swap,
      writtenFramePriorityDescriptor_clockwise_reverse [0, 1, 2, 3] tracked.highestFirst
        writtenOrder]
    rfl
  have recovered : anticlockwiseSource.aromaticCanonicalOccurrenceTetrahedralCenter? antiTarget =
      some antiCenter := occurrenceTetrahedralCenter?_final anticlockwiseSource 0 antiCenter
  have evidenceComputed : constitutionParserRichPriorityEvidence? anticlockwiseRaw
      anticlockwiseSource anticlockwiseSource_annotationAgreement anticlockwiseRaw_writtenExact
      antiTarget view 2 =
      some
        ({ slots := [0, 1, 2, 3]
           keys := keys
           tracked := tracked
           writtenParity := .anticlockwise
           raw := RS.S } : ParserRichPriorityEvidence anticlockwiseSource 0) := by
    simp [constitutionParserRichPriorityEvidence?, recovered, anti_index_identity,
      anticlockwiseRaw_atom, antiTarget_roots_returned, antiFrame, anti_slot_alignment,
      keysComputed2, trackedComputed, rawEq]
  simp [constitutionParserRichDescriptor?, evidenceComputed, zero, classifyTetrahedralRSPseudo_zero]

/-- The actual anticlockwise constitution `S` carries the complete independent rich meaning. -/
theorem anti_parser_S_meaning
    (view : anticlockwiseSource.AromaticCanonicalDependencyView antiTarget) :
    ConstitutionParserRichDescriptorMeaning anticlockwiseRaw anticlockwiseSource
      anticlockwiseSource_annotationAgreement anticlockwiseRaw_writtenExact antiTarget view 2
      (.chiral RS.S) :=
  constitutionParserRichDescriptor?_sound anticlockwiseRaw anticlockwiseSource
    anticlockwiseSource_annotationAgreement anticlockwiseRaw_writtenExact antiTarget view 2
    (.chiral RS.S) (anti_parser_S view)

/-- The actual normalized anticlockwise CFClBrI certified input. -/
def antiNormalized : ChemistryNormalizationResult := normalizeRawMolecule anticlockwiseRaw

def antiCertified : CertifiedChemistryNormalizationResult where
  result := antiNormalized
  admissible := (antiNormalized.parsed.admissible?_eq_true_iff).mp (by decide +kernel)
  writtenNeighborExact :=
    (antiNormalized.parsed.writtenNeighborExact?_eq_true_iff).mp (by decide +kernel)
  valenceOK := (antiNormalized.parsed.valenceOK?_eq_true_iff).mp (by decide +kernel)
  rule2MassesKnown := (antiNormalized.parsed.rule2MassesKnown?_eq_true_iff).mp (by decide +kernel)

/-- The actual executable authority-facing output for the anticlockwise CFClBrI input, evaluated. -/
theorem anti_executable_output :
    analyzeCertifiedNormalized antiCertified =
      [{ unit := StereoUnit.tetrahedral 0, outcome := StereoOutcome.tetrahedral RS.S }] := by
  decide +kernel

theorem anti_member (d : RS) :
    ({ unit := StereoUnit.tetrahedral 0, outcome := StereoOutcome.tetrahedral d } :
        StereoAssignment) ∈ analyzeCertifiedNormalized antiCertified ↔ d = RS.S := by
  rw [anti_executable_output]
  cases d <;> decide +kernel

/-- The four-distinct-written-index no-double request at the actual anticlockwise CFClBrI input. -/
noncomputable def antiRequest : AtomicSeparatedNoDoubleRequest where
  raw := anticlockwiseRaw
  certified := antiCertified
  normalizationEq := rfl
  parsedEq := rfl
  source := anticlockwiseSource
  agreement := anticlockwiseSource_annotationAgreement
  writtenExact := anticlockwiseRaw_writtenExact
  noDouble := anticlockwiseSource_no_ordinary_double_bond
  carrierFuel := 0
  ruleFuel := 2
  center := antiCenter
  atomicLigands := by
    constructor <;> rw [anti_raw_frame] <;> decide

/-- Direct closed same-request equivalence; no generic priority-parity binding is assumed. -/
theorem clockwise_runtime_iff_parser
    (view : parserSource.AromaticCanonicalDependencyView
      TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserWitness.parserTarget) (d : RS) :
    ({ unit := StereoUnit.tetrahedral 0, outcome := StereoOutcome.tetrahedral d } :
        StereoAssignment) ∈ analyzeCertifiedNormalized certifiedClockwise ↔
      constitutionParserRichDescriptor? annotatedRawCF parserSource parserSource_annotationAgreement
        parserSource_writtenExact
        TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserWitness.parserTarget view 2 =
          some (.chiral d) := by
  rw [clockwise_member, clockwise_parser_R view]
  simp [eq_comm]

/-- Direct closed anticlockwise equivalence at its own source and arbitrary restricted view. -/
theorem anti_runtime_iff_parser
    (view : anticlockwiseSource.AromaticCanonicalDependencyView antiTarget) (d : RS) :
    ({ unit := StereoUnit.tetrahedral 0, outcome := StereoOutcome.tetrahedral d } :
        StereoAssignment) ∈ analyzeCertifiedNormalized antiCertified ↔
      constitutionParserRichDescriptor? anticlockwiseRaw anticlockwiseSource
        anticlockwiseSource_annotationAgreement anticlockwiseRaw_writtenExact antiTarget view 2 =
          some (.chiral d) := by
  rw [anti_member, anti_parser_S view]
  simp [eq_comm]

/-! ## Actual nonidentity written-order witness -/

open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserWitness

/-- Same clockwise raw annotation and constitution, but an actual nontrivial written order. -/
def permutedRaw : RawMolecule :=
  { annotatedRawCF with neighborOrder := [[2, 1, 3, 4], [0], [0], [0], [0]] }

def permutedNormalized : ChemistryNormalizationResult := normalizeRawMolecule permutedRaw

def permutedCertified : CertifiedChemistryNormalizationResult where
  result := permutedNormalized
  admissible := (permutedNormalized.parsed.admissible?_eq_true_iff).mp (by decide +kernel)
  writtenNeighborExact :=
    (permutedNormalized.parsed.writtenNeighborExact?_eq_true_iff).mp (by decide +kernel)
  valenceOK := (permutedNormalized.parsed.valenceOK?_eq_true_iff).mp (by decide +kernel)
  rule2MassesKnown := (permutedNormalized.parsed.rule2MassesKnown?_eq_true_iff).mp (by decide +kernel)


theorem permuted_binding :
    permutedCertified.result = normalizeRawMolecule permutedRaw ∧
      permutedCertified.result.parsed = permutedRaw ∧
      permutedRaw.toSemanticMolecule? = some parserSource.molecule ∧
      rawAnnotationAgreementIssues permutedRaw parserSource = [] := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> decide +kernel

theorem permuted_agreement : RawAnnotationAgreement permutedRaw parserSource :=
  ⟨permuted_binding.2.2.1,
    (rawAnnotationAgreementIssues_eq_nil_iff permutedRaw parserSource).mp permuted_binding.2.2.2⟩

theorem permuted_written_exact : permutedRaw.WrittenNeighborExact :=
  (permutedRaw.writtenNeighborExact?_eq_true_iff).mp (by decide +kernel)

theorem permuted_index :
    (parserIndexViaConversion permutedRaw parserSource permuted_agreement.1 parserCenter).val = 0 := rfl

theorem permuted_raw_frame : rawWrittenLigandFrame permutedRaw
    (parserIndexViaConversion permutedRaw parserSource permuted_agreement.1 parserCenter) =
      [2, 1, 3, 4] := by
  unfold rawWrittenLigandFrame
  rw [permuted_index]
  decide +kernel

/-- The actual matcher returns nonidentity slots, not merely reversed priority. -/
theorem permuted_slot_alignment : findSlotAlignment?
    (rawWrittenLigandFrame permutedRaw
      (parserIndexViaConversion permutedRaw parserSource permuted_agreement.1 parserCenter))
    (occurrenceRootIDs parserSource parserRoots) = some [1, 0, 2, 3] := by
  rw [permuted_raw_frame, parser_actual_root_ids]
  decide +kernel

/-- The same source's actual production keys and safe order determine the new raw written descriptor. -/
theorem permuted_parser_S (view : parserSource.AromaticCanonicalDependencyView parserTarget) :
    constitutionParserRichDescriptor? permutedRaw parserSource permuted_agreement
      permuted_written_exact parserTarget view 2 = some (.chiral RS.S) := by
  obtain ⟨keys, tracked, keysComputed, trackedComputed, perm, descending, zero⟩ :=
    exists_occurrence_production_keys_and_safe_order parserSource parserTarget view parserFrame
      parser_actual_returned_frame parser_actual_roots_real parser_actual_atomic_priority_injective
      parserSource_no_ordinary_double_bond
  have keysComputed2 : parserSource.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      parserTarget view 2 parserRoots = some keys := keysComputed
  have orderEq := parser_actual_priority_order_unique tracked.highestFirst perm descending
  have rawEq : writtenFramePriorityDescriptor TetrahedralInputParity.clockwise [1, 0, 2, 3]
      tracked.highestFirst = RS.S := by
    rw [orderEq]
    decide +kernel
  have recovered : parserSource.aromaticCanonicalOccurrenceTetrahedralCenter? parserTarget =
      some parserCenter := occurrenceTetrahedralCenter?_final parserSource 0 parserCenter
  have atom : permutedRaw.atomAt? 0 = some { AtomSpec.aliphatic .C with
      tetrahedral? := some TetrahedralInputParity.clockwise } := rfl
  have evidenceComputed : constitutionParserRichPriorityEvidence? permutedRaw parserSource
      permuted_agreement permuted_written_exact parserTarget view 2 = some
        ({ slots := [1, 0, 2, 3], keys := keys, tracked := tracked,
           writtenParity := .clockwise, raw := RS.S } : ParserRichPriorityEvidence parserSource 0) := by
    simp [constitutionParserRichPriorityEvidence?, recovered, permuted_index, atom,
      parser_actual_returned_frame, parserFrame, permuted_slot_alignment,
      keysComputed2, trackedComputed, rawEq]
  simp [constitutionParserRichDescriptor?, evidenceComputed, zero, classifyTetrahedralRSPseudo_zero]

theorem permuted_parser_S_meaning (view : parserSource.AromaticCanonicalDependencyView parserTarget) :
    ConstitutionParserRichDescriptorMeaning permutedRaw parserSource permuted_agreement
      permuted_written_exact parserTarget view 2 (.chiral RS.S) :=
  constitutionParserRichDescriptor?_sound permutedRaw parserSource permuted_agreement
    permuted_written_exact parserTarget view 2 (.chiral RS.S) (permuted_parser_S view)

/-- Actual executable output, evaluated independently of the source-native priority proof. -/
theorem permuted_executable_output : analyzeCertifiedNormalized permutedCertified =
    [{ unit := StereoUnit.tetrahedral 0, outcome := StereoOutcome.tetrahedral RS.S }] := by
  decide +kernel

theorem permuted_planar_S (view : parserSource.AromaticCanonicalDependencyView parserTarget) :
    TetraStereo.UniversalProof.SourceNativePlanarParserOccurrenceProofs.SourceNativePlanarParserOccurrence.planarConstitutionParserRichDescriptor?
      permutedRaw parserSource permuted_agreement permuted_written_exact parserTarget view 2 =
        some (.chiral RS.S) := by
  rw [TetraStereo.UniversalProof.SourceNativePlanarParserCausalModelProofs.SourceNativePlanarParserCausalModel.planarConstitutionParserRichDescriptor?_eq_constitution_of_noDouble
    permutedRaw parserSource permuted_agreement permuted_written_exact
    parserSource_no_ordinary_double_bond parserTarget view 2]
  exact permuted_parser_S view

theorem permuted_planar_S_meaning (view : parserSource.AromaticCanonicalDependencyView parserTarget) :
    TetraStereo.UniversalProof.SourceNativePlanarParserOccurrenceProofs.SourceNativePlanarParserOccurrence.PlanarConstitutionParserRichDescriptorMeaning
      permutedRaw parserSource permuted_agreement permuted_written_exact parserTarget view 2
        (.chiral RS.S) :=
  TetraStereo.UniversalProof.SourceNativePlanarParserOccurrenceProofs.SourceNativePlanarParserOccurrence.planarConstitutionParserRichDescriptor?_sound
    permutedRaw parserSource permuted_agreement permuted_written_exact parserTarget view 2
      (.chiral RS.S) (permuted_planar_S view)

/-- Closed same-request equivalence and independent meaning for the genuinely permuted input. -/
theorem permuted_runtime_iff_parser_meaning
    (view : parserSource.AromaticCanonicalDependencyView parserTarget) (d : RS) :
    (({ unit := StereoUnit.tetrahedral 0, outcome := StereoOutcome.tetrahedral d } :
        StereoAssignment) ∈ analyzeCertifiedNormalized permutedCertified ↔
      constitutionParserRichDescriptor? permutedRaw parserSource permuted_agreement
        permuted_written_exact parserTarget view 2 = some (.chiral d)) ∧
      ConstitutionParserRichDescriptorMeaning permutedRaw parserSource permuted_agreement
        permuted_written_exact parserTarget view 2 (.chiral RS.S) ∧
      TetraStereo.UniversalProof.SourceNativePlanarParserOccurrenceProofs.SourceNativePlanarParserOccurrence.PlanarConstitutionParserRichDescriptorMeaning
        permutedRaw parserSource permuted_agreement permuted_written_exact parserTarget view 2
          (.chiral RS.S) := by
  refine ⟨?_, permuted_parser_S_meaning view, permuted_planar_S_meaning view⟩
  rw [permuted_executable_output, permuted_parser_S view]
  simp [eq_comm]

end ClosedExecutableBridge

end TetraStereo.UniversalProof.SourceNativeExecutableParserRefinementProofs.SourceNativeExecutableParserRefinement
