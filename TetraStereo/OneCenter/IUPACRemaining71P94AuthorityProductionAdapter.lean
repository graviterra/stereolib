import TetraStereo.OneCenter.IUPACRemaining71P94ReviewedSemantics
import TetraStereo.OneCenter.IUPACRemaining71AuthorityDataReviewedSemantics
import TetraStereo.OneCenter.IUPACPrimitive35Interpreter

set_option autoImplicit false

/-!
# Production adapter for remaining P-94 and authority-data rows

The twelve P-94 rows run the complete `analyzeP94Conformation` compiler directly on the exact
reviewed raw molecule.  The three authority rows query the frozen periodic-number,
CIAAW-2021 standard-weight, and AME-2020 isotope-mass tables directly.  Reviewed `Judges` is never
used as production.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

/-! ## Fixed P-94 production -/

/-- Exact totality still required to run the executable P-94 compiler on every independently
valid reviewed observation. This proposition is fixed to `normalizeRawMoleculeCertified?`; it is
not a caller-selected production relation. The parsed-equality clause rules out silently changing
the reviewed molecule during unspecified-bond normalization. -/
def P94RemainingFixedNormalizationTotality (policy : P94AuthorityPolicy) : Prop :=
  ∀ (source : AuthoritativeChemicalInput) (observation : P94AuthorityObservation policy),
    observation.ValidFor policy source →
      ∃ certified : CertifiedChemistryNormalizationResult,
        normalizeRawMoleculeCertified? observation.molecule = some certified ∧
          certified.result.parsed = observation.molecule

def p94RemainingProductionAssignment
    {policy : P94AuthorityPolicy} (observation : P94AuthorityObservation policy) :
    P94ConformationAssignment :=
  { unit := observation.evidence.unit
    descriptor := observation.claim.descriptor }

/-- Concrete P-94 production relation.  All descriptor support comes from membership in the
complete report computed on the exact reviewed molecule; source provenance and row routing remain
independent guards. -/
def P94RemainingProductionJudged
    (policy : P94AuthorityPolicy)
    (provision : IUPACNormativeProvision)
    (source : AuthoritativeChemicalInput)
    (observation : P94AuthorityObservation policy) : Prop :=
  observation.molecule.AuthoritativeStructureAgreement source ∧
    policy.EvidenceObserved source observation.molecule observation.evidence ∧
    observation.claim.MatchesEvidence observation.evidence ∧
    P94InOutCertificateMatches policy source observation.molecule
      observation.evidence observation.inOutCertificate? ∧
    observation.claim.provision = provision ∧
    p94RemainingProductionAssignment observation ∈
      observation.molecule.analyzeP94Conformation [observation.evidence]

theorem p94RemainingProductionJudged_iff_validForProvision
    {policy : P94AuthorityPolicy}
    (provision : IUPACNormativeProvision)
    (source : AuthoritativeChemicalInput)
    (observation : P94AuthorityObservation policy) :
    P94RemainingProductionJudged policy provision source observation ↔
      observation.ValidForProvision policy provision source := by
  constructor
  · rintro ⟨structureAgreement, observed, claimMatches, inOut, provisionExact, emitted⟩
    have independent :=
      (RawMolecule.mem_analyzeP94Conformation_iff_independent observation.molecule
        [observation.evidence]
        (p94RemainingProductionAssignment observation)).mp emitted
    rcases independent with
      ⟨record, recordPresent, unitExact, unitValid, rolesValid, supports⟩
    have recordExact : record = observation.evidence := by
      simpa using recordPresent
    subst record
    refine ⟨⟨structureAgreement, observed, ?_, ?_, claimMatches, ?_, inOut⟩, provisionExact⟩
    · simpa [p94RemainingProductionAssignment] using unitValid
    · simpa [p94RemainingProductionAssignment] using rolesValid
    · simpa [p94RemainingProductionAssignment] using supports
  · rintro ⟨valid, provisionExact⟩
    rcases valid with ⟨structureAgreement, observed, unitValid, rolesValid,
      claimMatches, supports, inOut⟩
    refine ⟨structureAgreement, observed, claimMatches, inOut, provisionExact, ?_⟩
    apply (RawMolecule.mem_analyzeP94Conformation_iff_independent observation.molecule
      [observation.evidence]
      (p94RemainingProductionAssignment observation)).mpr
    refine ⟨observation.evidence, by simp, rfl, ?_, ?_, ?_⟩
    · simpa [p94RemainingProductionAssignment] using unitValid
    · simpa [p94RemainingProductionAssignment] using rolesValid
    · exact supports

def Remaining71P94AuthorityRow.ProductionJudges
    (policy : P94AuthorityPolicy)
    (row : Remaining71P94AuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policy).Observation) : Prop :=
  P94RemainingProductionJudged policy row.provision source observation

theorem Remaining71P94AuthorityRow.production_eq_reference
    {policy : P94AuthorityPolicy}
    (row : Remaining71P94AuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policy).Observation) :
    row.ProductionJudges policy source observation ↔
      (row.reference policy).Judges source observation :=
  p94RemainingProductionJudged_iff_validForProvision row.provision source observation

theorem Remaining71P94AuthorityRow.reference_applicable_of_judged
    {policy : P94AuthorityPolicy}
    (row : Remaining71P94AuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policy).Observation)
    (judged : (row.reference policy).Judges source observation) :
    (row.reference policy).Applicable source :=
  ⟨observation, judged⟩

/-! ## Frozen authority-data production -/

def PeriodicAtomicNumberProductionJudged
    (observation : PeriodicAtomicNumberAuthorityObservation) : Prop :=
  observation.atomicNumber ∈ CIPRule2MassData.currentAtomicNumbers

def StandardAtomicWeightProductionJudged
    (observation : StandardAtomicWeightAuthorityObservation) : Prop :=
  CIAAWStandardAtomicWeights2021.entry? observation.atomicNumber = some observation.entry

def IsotopeAtomicMassProductionJudged
    (observation : IsotopeAtomicMassAuthorityObservation) : Prop :=
  (observation.atomicNumber, observation.massNumber) ∈
      CIPRule2MassData.supportedNuclides ∧
    CIPRule2MassData.isotopeAtomicMassPico?
      observation.atomicNumber observation.massNumber = some observation.massPico

def Remaining71AuthorityDataRow.ProductionJudges :
    (row : Remaining71AuthorityDataRow) → row.reference.Observation → Prop
  | .periodicAtomicNumbers => PeriodicAtomicNumberProductionJudged
  | .standardAtomicWeights => StandardAtomicWeightProductionJudged
  | .isotopeAtomicMasses => IsotopeAtomicMassProductionJudged

theorem Remaining71AuthorityDataRow.production_eq_reference
    (row : Remaining71AuthorityDataRow)
    (source : AuthoritativeChemicalInput)
    (observation : row.reference.Observation) :
    row.ProductionJudges observation ↔ row.reference.Judges source observation := by
  cases row <;> rfl

theorem periodicAtomicNumbersProduction_nonempty :
    ∃ observation : PeriodicAtomicNumberAuthorityObservation,
      PeriodicAtomicNumberProductionJudged observation := by
  exact ⟨⟨1⟩, by simp [PeriodicAtomicNumberProductionJudged,
    CIPRule2MassData.currentAtomicNumbers]⟩

theorem standardAtomicWeightsProduction_nonempty :
    ∃ observation : StandardAtomicWeightAuthorityObservation,
      StandardAtomicWeightProductionJudged observation := by
  exact ⟨⟨1, .interval 1007840000000 1008110000000⟩, rfl⟩

theorem isotopeAtomicMassesProduction_nonempty :
    ∃ observation : IsotopeAtomicMassAuthorityObservation,
      IsotopeAtomicMassProductionJudged observation := by
  let hydrogen1 : IsotopeAtomicMassAuthorityObservation :=
    ⟨1, 1, 1007825031898⟩
  refine ⟨hydrogen1, ?_⟩
  constructor
  · apply List.mem_flatMap.mpr
    refine ⟨1, ?_, ?_⟩
    · simp [CIPRule2MassData.currentAtomicNumbers]
    · exact List.mem_map.mpr
        ⟨(1, 1007825031898), by
          simp [CIPRule2MassData.Generated.isotopeMassesPico], rfl⟩
  · rfl

theorem Remaining71AuthorityDataRow.reference_applicable
    (row : Remaining71AuthorityDataRow) (source : AuthoritativeChemicalInput) :
    row.reference.Applicable source := by
  cases row with
  | periodicAtomicNumbers => exact periodicAtomicNumbersProduction_nonempty
  | standardAtomicWeights => exact standardAtomicWeightsProduction_nonempty
  | isotopeAtomicMasses => exact isotopeAtomicMassesProduction_nonempty

/-! ## Combined fifteen-row interpreter -/

def p94AuthorityProductionScope : List IUPACNormativeProvision :=
  p94ReviewedSemanticsSlice ++ authorityDataReviewedSemanticsSlice

theorem remaining71P94CorpusReference_eq_of_member
    {policy : P94AuthorityPolicy} {corpus : FrozenProvisionCorpus}
    (faithful : ProvisionBatchReferenceFaithful
      (remaining71P94ReviewedSemantics policy).reviewed corpus)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p94ReviewedSemanticsSlice) :
    corpus.reference provision =
      (remaining71P94AuthorityRowOf provision member).reference policy := by
  have exactRow := faithful.exact (by simpa using member)
  simpa [remaining71P94ReviewedSemantics, Remaining71P94AuthorityRow.semantics] using
    exactRow.2.2

theorem remaining71AuthorityDataCorpusReference_eq_of_member
    {corpus : FrozenProvisionCorpus}
    (faithful : ProvisionBatchReferenceFaithful
      remaining71AuthorityDataReviewedSemantics.reviewed corpus)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ authorityDataReviewedSemanticsSlice) :
    corpus.reference provision =
      (remaining71AuthorityDataRowOf provision member).reference := by
  have exactRow := faithful.exact (by simpa using member)
  simpa [remaining71AuthorityDataReviewedSemantics,
    Remaining71AuthorityDataRow.semantics] using exactRow.2.2

noncomputable def p94AuthorityProductionInterpreter
    {policy : P94AuthorityPolicy} {corpus : FrozenProvisionCorpus}
    (p94Faithful : ProvisionBatchReferenceFaithful
      (remaining71P94ReviewedSemantics policy).reviewed corpus)
    (authorityFaithful : ProvisionBatchReferenceFaithful
      remaining71AuthorityDataReviewedSemantics.reviewed corpus) :
    ProvisionInterpreter corpus where
  Produces := fun provision source observation =>
    if member : provision ∈ p94ReviewedSemanticsSlice then
      let row := remaining71P94AuthorityRowOf provision member
      let referenceEq := remaining71P94CorpusReference_eq_of_member
        p94Faithful provision member
      row.ProductionJudges policy source
        (cast (congrArg ProvisionReference.Observation referenceEq) observation)
    else if member : provision ∈ authorityDataReviewedSemanticsSlice then
      let row := remaining71AuthorityDataRowOf provision member
      let referenceEq := remaining71AuthorityDataCorpusReference_eq_of_member
        authorityFaithful provision member
      row.ProductionJudges
        (cast (congrArg ProvisionReference.Observation referenceEq) observation)
    else False

@[simp] theorem p94AuthorityProductionInterpreter_p94_exact
    {policy : P94AuthorityPolicy} {corpus : FrozenProvisionCorpus}
    (p94Faithful : ProvisionBatchReferenceFaithful
      (remaining71P94ReviewedSemantics policy).reviewed corpus)
    (authorityFaithful : ProvisionBatchReferenceFaithful
      remaining71AuthorityDataReviewedSemantics.reviewed corpus)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p94ReviewedSemanticsSlice)
    (source : AuthoritativeChemicalInput)
    (observation : (corpus.reference provision).Observation) :
    (p94AuthorityProductionInterpreter p94Faithful authorityFaithful).Produces
        provision source observation ↔
      (remaining71P94AuthorityRowOf provision member).ProductionJudges policy source
        (cast (congrArg ProvisionReference.Observation
          (remaining71P94CorpusReference_eq_of_member p94Faithful provision member))
            observation) := by
  simp only [p94AuthorityProductionInterpreter, dif_pos member]

@[simp] theorem p94AuthorityProductionInterpreter_authority_exact
    {policy : P94AuthorityPolicy} {corpus : FrozenProvisionCorpus}
    (p94Faithful : ProvisionBatchReferenceFaithful
      (remaining71P94ReviewedSemantics policy).reviewed corpus)
    (authorityFaithful : ProvisionBatchReferenceFaithful
      remaining71AuthorityDataReviewedSemantics.reviewed corpus)
    (provision : IUPACNormativeProvision)
    (p94Absent : provision ∉ p94ReviewedSemanticsSlice)
    (member : provision ∈ authorityDataReviewedSemanticsSlice)
    (source : AuthoritativeChemicalInput)
    (observation : (corpus.reference provision).Observation) :
    (p94AuthorityProductionInterpreter p94Faithful authorityFaithful).Produces
        provision source observation ↔
      (remaining71AuthorityDataRowOf provision member).ProductionJudges
        (cast (congrArg ProvisionReference.Observation
          (remaining71AuthorityDataCorpusReference_eq_of_member
            authorityFaithful provision member)) observation) := by
  simp only [p94AuthorityProductionInterpreter, dif_neg p94Absent, dif_pos member]

theorem p94AuthorityProductionInterpreter_p94_provisionCorrect
    {policy : P94AuthorityPolicy} {corpus : FrozenProvisionCorpus}
    (p94Faithful : ProvisionBatchReferenceFaithful
      (remaining71P94ReviewedSemantics policy).reviewed corpus)
    (authorityFaithful : ProvisionBatchReferenceFaithful
      remaining71AuthorityDataReviewedSemantics.reviewed corpus)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p94ReviewedSemanticsSlice) :
    ProvisionCorrect corpus
      (p94AuthorityProductionInterpreter p94Faithful authorityFaithful) provision := by
  intro source _admitted observation
  let row := remaining71P94AuthorityRowOf provision member
  let referenceEq := remaining71P94CorpusReference_eq_of_member
    p94Faithful provision member
  let rowObservation : (row.reference policy).Observation :=
    cast (congrArg ProvisionReference.Observation referenceEq) observation
  have judgment := row.production_eq_reference source rowObservation
  have applicableTransport := ProvisionReference.applicable_congr referenceEq source
  have judgmentTransport := ProvisionReference.judges_cast_congr referenceEq source observation
  rw [p94AuthorityProductionInterpreter_p94_exact
    p94Faithful authorityFaithful provision member source observation]
  change row.ProductionJudges policy source rowObservation ↔
    (corpus.reference provision).Applicable source ∧
      (corpus.reference provision).Judges source observation
  constructor
  · intro produced
    have judged := judgment.mp produced
    exact ⟨applicableTransport.mpr
      (row.reference_applicable_of_judged source rowObservation judged),
        judgmentTransport.mpr judged⟩
  · rintro ⟨_applicable, judged⟩
    exact judgment.mpr (judgmentTransport.mp judged)

theorem p94AuthorityProductionInterpreter_authority_provisionCorrect
    {policy : P94AuthorityPolicy} {corpus : FrozenProvisionCorpus}
    (p94Faithful : ProvisionBatchReferenceFaithful
      (remaining71P94ReviewedSemantics policy).reviewed corpus)
    (authorityFaithful : ProvisionBatchReferenceFaithful
      remaining71AuthorityDataReviewedSemantics.reviewed corpus)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ authorityDataReviewedSemanticsSlice)
    (p94Absent : provision ∉ p94ReviewedSemanticsSlice) :
    ProvisionCorrect corpus
      (p94AuthorityProductionInterpreter p94Faithful authorityFaithful) provision := by
  intro source _admitted observation
  let row := remaining71AuthorityDataRowOf provision member
  let referenceEq := remaining71AuthorityDataCorpusReference_eq_of_member
    authorityFaithful provision member
  let rowObservation : row.reference.Observation :=
    cast (congrArg ProvisionReference.Observation referenceEq) observation
  have judgment := row.production_eq_reference source rowObservation
  have applicable := row.reference_applicable source
  have applicableTransport := ProvisionReference.applicable_congr referenceEq source
  have judgmentTransport := ProvisionReference.judges_cast_congr referenceEq source observation
  rw [p94AuthorityProductionInterpreter_authority_exact
    p94Faithful authorityFaithful provision p94Absent member source observation]
  change row.ProductionJudges rowObservation ↔
    (corpus.reference provision).Applicable source ∧
      (corpus.reference provision).Judges source observation
  constructor
  · intro produced
    exact ⟨applicableTransport.mpr applicable,
      judgmentTransport.mpr (judgment.mp produced)⟩
  · rintro ⟨_applicable, judged⟩
    exact judgment.mpr (judgmentTransport.mp judged)

/-- One dependent theorem covers the exact 15-row union. The authority branch is unconditional;
the P-94 branch consumes only the fixed normalization realization obligation above. -/
theorem p94AuthorityProductionInterpreter_provisionCorrect
    {policy : P94AuthorityPolicy} {corpus : FrozenProvisionCorpus}
    (p94Faithful : ProvisionBatchReferenceFaithful
      (remaining71P94ReviewedSemantics policy).reviewed corpus)
    (authorityFaithful : ProvisionBatchReferenceFaithful
      remaining71AuthorityDataReviewedSemantics.reviewed corpus)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p94AuthorityProductionScope) :
    ProvisionCorrect corpus
      (p94AuthorityProductionInterpreter p94Faithful authorityFaithful) provision := by
  rcases (List.mem_append.mp member) with p94Member | authorityMember
  · exact p94AuthorityProductionInterpreter_p94_provisionCorrect
      p94Faithful authorityFaithful provision p94Member
  · have p94Absent : provision ∉ p94ReviewedSemanticsSlice := by
      intro overlap
      have p94Descriptor : provision ∈ p94SemanticsSlice := by simpa using overlap
      have authorityDescriptor : provision ∈ descriptorAssignmentAuthorityDataProvisions := by
        simpa using authorityMember
      have p94AuthorityDisjoint :
          List.Disjoint p94SemanticsSlice descriptorAssignmentAuthorityDataProvisions := by
        have p94AvoidsAuthority :
            p94SemanticsSlice.Forall
              (fun row => row ∉ descriptorAssignmentAuthorityDataProvisions) := by
          decide
        rw [List.disjoint_left]
        intro row p94Member authorityMember
        exact (List.forall_iff_forall_mem.mp p94AvoidsAuthority row p94Member)
          authorityMember
      exact (List.disjoint_left.mp p94AuthorityDisjoint)
        p94Descriptor authorityDescriptor
    exact p94AuthorityProductionInterpreter_authority_provisionCorrect
      p94Faithful authorityFaithful provision authorityMember p94Absent

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p94RemainingProductionJudged_iff_validForProvision
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71AuthorityDataRow.production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p94AuthorityProductionInterpreter_authority_provisionCorrect
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p94AuthorityProductionInterpreter_provisionCorrect
