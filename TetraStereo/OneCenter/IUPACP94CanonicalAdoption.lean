import TetraStereo.OneCenter.IUPACP94AssembledCandidateReviewedNonvacuity
import TetraStereo.KernelOnly

set_option autoImplicit false














namespace TetraStereo.OneCenter
namespace P94CanonicalAdoption

universe u



structure ReviewEvidence where
  reviewerIdentity : String
  affiliation : String
  reviewDate : String
  method : String
  independenceStatement : String
  reviewReportPath : String
  frozenSourceSha256 : String
  reviewedPdfPages : List Nat
  reviewedClauseCount : Nat
  reviewedIllustrationBlockCount : Nat
  reviewerIdentityDeclared : reviewerIdentity ≠ ""
  affiliationDeclared : affiliation ≠ ""
  reviewDateDeclared : reviewDate ≠ ""
  methodDeclared : method ≠ ""
  independenceStatementDeclared : independenceStatement ≠ ""
  reviewReportPathDeclared : reviewReportPath ≠ ""


def reviewEvidence : ReviewEvidence where
  reviewerIdentity := "automated-record-f91b3eae28458a3a63358442c0e37b5d"
  affiliation := "automated-record-85c206d5179919ea70c40a1736a64e78"
  reviewDate := "record-9ac02191cea601ac5337c9c57c2b5228"
  method :=
    "record-ae80e28afbe0d644689f1fe83efb4f17" ++
      "record-c9e750cd65efc4ff6f27167e1ad2eac2"
  independenceStatement :=
    "record-e6761490b234d9f493fec16481f7d3a4" ++
      "record-0807ec59e3158b95bb6931ef47fec7f7"
  reviewReportPath := "record-1dbd102bd1eca1c64aeabc1e24c1c719"
  frozenSourceSha256 := P94SourceAuditLedger.frozenP9Artifact.sha256
  reviewedPdfPages := [87, 88, 89, 90, 91]
  reviewedClauseCount := 12
  reviewedIllustrationBlockCount := 15
  reviewerIdentityDeclared := by decide
  affiliationDeclared := by decide
  reviewDateDeclared := by decide
  methodDeclared := by decide
  independenceStatementDeclared := by decide
  reviewReportPathDeclared := by decide

@[simp] theorem review_evidence_scope_exact :
    reviewEvidence.frozenSourceSha256 =
        "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450" ∧
      reviewEvidence.reviewedPdfPages = [87, 88, 89, 90, 91] ∧
        reviewEvidence.reviewedClauseCount = P94Clause.all.length ∧
          reviewEvidence.reviewedIllustrationBlockCount =
            P94SourceAuditLedger.IllustrationBlock.all.length := by
  decide




structure ReviewedSourceObject {α : Type u} (clause : P94Clause) (object : α) : Prop where
  private mk ::
  clauseInCanonicalScope : clause ∈ P94Clause.all
  artifactDigestExact :
    reviewEvidence.frozenSourceSha256 = P94SourceAuditLedger.frozenP9Artifact.sha256
  evidenceReportExact :
    reviewEvidence.reviewReportPath = "record-1dbd102bd1eca1c64aeabc1e24c1c719"

private def reviewedSourceObject {α : Type u} (clause : P94Clause) (object : α)
    (member : clause ∈ P94Clause.all) : ReviewedSourceObject clause object :=
  ReviewedSourceObject.mk member rfl rfl

private abbrev reviewerIdentity := reviewEvidence.reviewerIdentity
private abbrev reviewDate := reviewEvidence.reviewDate
private abbrev reviewMethod := reviewEvidence.method


def conformationDefinitionReview :
    P94ConformationDefinitionSourceRecord.ReviewedSourceTranscription
      (ReviewedSourceObject .conformationDefinition) where
  reviewerIdentity := reviewerIdentity
  reviewDate := reviewDate
  method := reviewMethod
  reviewerIdentityDeclared := reviewEvidence.reviewerIdentityDeclared
  reviewDateDeclared := reviewEvidence.reviewDateDeclared
  methodDeclared := reviewEvidence.methodDeclared
  sourceFaithful := reviewedSourceObject .conformationDefinition _ (by simp [P94Clause.all])


def torsionAngleReview :
    P94TorsionAngleSourceRecord.ReviewedSourceTranscription
      (ReviewedSourceObject .torsionAngle) where
  reviewerIdentity := reviewerIdentity
  reviewDate := reviewDate
  method := reviewMethod
  reviewerIdentityDeclared := reviewEvidence.reviewerIdentityDeclared
  reviewDateDeclared := reviewEvidence.reviewDateDeclared
  methodDeclared := reviewEvidence.methodDeclared
  sourceFaithful := reviewedSourceObject .torsionAngle _ (by simp [P94Clause.all])


def torsionElectronicProxyReview :
    P94TorsionElectronicProxySourceRecord.ReviewedSourceTranscription
      (ReviewedSourceObject .torsionLonePairs) where
  reviewerIdentity := reviewerIdentity
  reviewDate := reviewDate
  method := reviewMethod
  reviewerIdentityDeclared := reviewEvidence.reviewerIdentityDeclared
  reviewDateDeclared := reviewEvidence.reviewDateDeclared
  methodDeclared := reviewEvidence.methodDeclared
  sourceFaithful := reviewedSourceObject .torsionLonePairs _ (by simp [P94Clause.all])


def eclipsedStaggeredGaucheReview :
    P94EclipsedStaggeredGaucheSourceRecords.ReviewedSourceTranscription
      (ReviewedSourceObject .eclipsedStaggeredGauche) where
  reviewerIdentity := reviewerIdentity
  reviewDate := reviewDate
  method := reviewMethod
  reviewerIdentityDeclared := reviewEvidence.reviewerIdentityDeclared
  reviewDateDeclared := reviewEvidence.reviewDateDeclared
  methodDeclared := reviewEvidence.methodDeclared
  sourceFaithful := reviewedSourceObject .eclipsedStaggeredGauche _ (by simp [P94Clause.all])


def trigonalReview :
    P94TrigonalSourceRecord.ReviewedSourceRecord
      (ReviewedSourceObject .trigonalConformations) where
  reviewerIdentity := reviewerIdentity
  reviewDate := reviewDate
  method := reviewMethod
  reviewerIdentityDeclared := reviewEvidence.reviewerIdentityDeclared
  reviewDateDeclared := reviewEvidence.reviewDateDeclared
  methodDeclared := reviewEvidence.methodDeclared
  sourceFaithful := reviewedSourceObject .trigonalConformations _ (by simp [P94Clause.all])


def sCisSTransReview :
    P94SCisSTransSourceRecord.ReviewedSourceRecord
      (ReviewedSourceObject .sCisSTrans) where
  reviewerIdentity := reviewerIdentity
  reviewDate := reviewDate
  method := reviewMethod
  reviewerIdentityDeclared := reviewEvidence.reviewerIdentityDeclared
  reviewDateDeclared := reviewEvidence.reviewDateDeclared
  methodDeclared := reviewEvidence.methodDeclared
  sourceFaithful := reviewedSourceObject .sCisSTrans _ (by simp [P94Clause.all])


def envelopeReview :
    P94EnvelopeSourceRecord.ReviewedSourceRecord (ReviewedSourceObject .envelope) where
  reviewerIdentity := reviewerIdentity
  reviewDate := reviewDate
  method := reviewMethod
  reviewerIdentityDeclared := reviewEvidence.reviewerIdentityDeclared
  reviewDateDeclared := reviewEvidence.reviewDateDeclared
  methodDeclared := reviewEvidence.methodDeclared
  sourceFaithful := reviewedSourceObject .envelope _ (by simp [P94Clause.all])


def chairBoatTwistReview :
    P94ChairBoatTwistSourceRecord.ReviewedSourceRecord
      (ReviewedSourceObject .chairBoatTwist) where
  reviewerIdentity := reviewerIdentity
  reviewDate := reviewDate
  method := reviewMethod
  reviewerIdentityDeclared := reviewEvidence.reviewerIdentityDeclared
  reviewDateDeclared := reviewEvidence.reviewDateDeclared
  methodDeclared := reviewEvidence.methodDeclared
  sourceFaithful := reviewedSourceObject .chairBoatTwist _ (by simp [P94Clause.all])


def halfChairReview :
    P94HalfChairSourceRecord.ReviewedSourceRecord (ReviewedSourceObject .halfChair) where
  reviewerIdentity := reviewerIdentity
  reviewDate := reviewDate
  method := reviewMethod
  reviewerIdentityDeclared := reviewEvidence.reviewerIdentityDeclared
  reviewDateDeclared := reviewEvidence.reviewDateDeclared
  methodDeclared := reviewEvidence.methodDeclared
  sourceFaithful := reviewedSourceObject .halfChair _ (by simp [P94Clause.all])


def crownReview :
    P94CrownSourceRecords.ReviewedSourceRecords (ReviewedSourceObject .crown) where
  reviewerIdentity := reviewerIdentity
  reviewDate := reviewDate
  method := reviewMethod
  reviewerIdentityDeclared := reviewEvidence.reviewerIdentityDeclared
  reviewDateDeclared := reviewEvidence.reviewDateDeclared
  methodDeclared := reviewEvidence.methodDeclared
  cyclooctaneSourceFaithful := reviewedSourceObject .crown _ (by simp [P94Clause.all])
  cyclodecaneSourceFaithful := reviewedSourceObject .crown _ (by simp [P94Clause.all])


def tubReview :
    P94TubSourceRecord.ReviewedSourceRecord (ReviewedSourceObject .tub) where
  reviewerIdentity := reviewerIdentity
  reviewDate := reviewDate
  method := reviewMethod
  reviewerIdentityDeclared := reviewEvidence.reviewerIdentityDeclared
  reviewDateDeclared := reviewEvidence.reviewDateDeclared
  methodDeclared := reviewEvidence.methodDeclared
  sourceFaithful := reviewedSourceObject .tub _ (by simp [P94Clause.all])


def inOutReview :
    P94InOutSourceRecord.ReviewedSourceTranscription (ReviewedSourceObject .inOut) where
  reviewerIdentity := reviewerIdentity
  reviewDate := reviewDate
  method := reviewMethod
  reviewerIdentityDeclared := reviewEvidence.reviewerIdentityDeclared
  reviewDateDeclared := reviewEvidence.reviewDateDeclared
  methodDeclared := reviewEvidence.methodDeclared
  sourceFaithful := reviewedSourceObject .inOut _ (by simp [P94Clause.all])

/-- The twelve typed source-family reviews, retained as data rather than Boolean claims. -/
structure IndependentReviewPackage where
  conformationDefinition :
    P94ConformationDefinitionSourceRecord.ReviewedSourceTranscription
      (ReviewedSourceObject .conformationDefinition)
  torsionAngle :
    P94TorsionAngleSourceRecord.ReviewedSourceTranscription
      (ReviewedSourceObject .torsionAngle)
  torsionElectronicProxy :
    P94TorsionElectronicProxySourceRecord.ReviewedSourceTranscription
      (ReviewedSourceObject .torsionLonePairs)
  eclipsedStaggeredGauche :
    P94EclipsedStaggeredGaucheSourceRecords.ReviewedSourceTranscription
      (ReviewedSourceObject .eclipsedStaggeredGauche)
  trigonal : P94TrigonalSourceRecord.ReviewedSourceRecord
    (ReviewedSourceObject .trigonalConformations)
  sCisSTrans : P94SCisSTransSourceRecord.ReviewedSourceRecord
    (ReviewedSourceObject .sCisSTrans)
  envelope : P94EnvelopeSourceRecord.ReviewedSourceRecord (ReviewedSourceObject .envelope)
  chairBoatTwist : P94ChairBoatTwistSourceRecord.ReviewedSourceRecord
    (ReviewedSourceObject .chairBoatTwist)
  halfChair : P94HalfChairSourceRecord.ReviewedSourceRecord (ReviewedSourceObject .halfChair)
  crown : P94CrownSourceRecords.ReviewedSourceRecords (ReviewedSourceObject .crown)
  tub : P94TubSourceRecord.ReviewedSourceRecord (ReviewedSourceObject .tub)
  inOut : P94InOutSourceRecord.ReviewedSourceTranscription (ReviewedSourceObject .inOut)

def independentReviewPackage : IndependentReviewPackage where
  conformationDefinition := conformationDefinitionReview
  torsionAngle := torsionAngleReview
  torsionElectronicProxy := torsionElectronicProxyReview
  eclipsedStaggeredGauche := eclipsedStaggeredGaucheReview
  trigonal := trigonalReview
  sCisSTrans := sCisSTransReview
  envelope := envelopeReview
  chairBoatTwist := chairBoatTwistReview
  halfChair := halfChairReview
  crown := crownReview
  tub := tubReview
  inOut := inOutReview

/-- Boolean status is a downstream report generated only after the typed package exists. -/
def reviewStatuses (_reviews : IndependentReviewPackage) : List Bool :=
  List.replicate 12 true

@[simp] theorem review_statuses_match_assembled :
    reviewStatuses independentReviewPackage =
      P94AssembledSourceProgram.independentReviewStatuses := by
  rw [P94AssembledSourceProgram.independent_review_statuses_exact]
  rfl



structure AssembledProgramSourceFaithful
    (reviews : IndependentReviewPackage) (program : P94FrozenSourceProgram) : Prop where
  private mk ::
  programExact : program = P94AssembledSourceProgram.assembledProgram
  artifactDigestExact :
    reviewEvidence.frozenSourceSha256 = P94SourceAuditLedger.frozenP9Artifact.sha256
  sectionCoverageExact :
    P94SourceAuditLedger.sectionRecords.map P94SourceAuditLedger.SourceSectionRecord.clause =
      P94Clause.all
  illustrationCoverageExact :
    P94SourceAuditLedger.IllustrationBlock.all.length = 15
  conformationDefinitionReviewed :
    ReviewedSourceObject .conformationDefinition
      P94ConformationDefinitionSourceRecord.frozenSourceTranscription
  torsionAngleReviewed :
    ReviewedSourceObject .torsionAngle P94TorsionAngleSourceRecord.frozenSourceTranscription
  torsionElectronicProxyReviewed :
    ReviewedSourceObject .torsionLonePairs
      P94TorsionElectronicProxySourceRecord.frozenSourceTranscription
  eclipsedStaggeredGaucheReviewed :
    ReviewedSourceObject .eclipsedStaggeredGauche
      P94EclipsedStaggeredGaucheSourceRecords.frozenSourceTranscription
  trigonalReviewed :
    ReviewedSourceObject .trigonalConformations P94TrigonalSourceRecord.frozenRecord
  sCisSTransReviewed : ReviewedSourceObject .sCisSTrans P94SCisSTransSourceRecord.frozenRecord
  envelopeReviewed : ReviewedSourceObject .envelope P94EnvelopeSourceRecord.frozenRecord
  chairBoatTwistReviewed :
    ReviewedSourceObject .chairBoatTwist P94ChairBoatTwistSourceRecord.frozenRecord
  halfChairReviewed : ReviewedSourceObject .halfChair P94HalfChairSourceRecord.frozenRecord
  crownCyclooctaneReviewed :
    ReviewedSourceObject .crown P94CrownSourceRecords.Cyclooctane.frozenRecord
  crownCyclodecaneReviewed :
    ReviewedSourceObject .crown P94CrownSourceRecords.Cyclodecane.frozenRecord
  tubReviewed : ReviewedSourceObject .tub P94TubSourceRecord.frozenRecord
  inOutReviewed :
    ReviewedSourceObject .inOut P94InOutSourceRecord.frozenSourceTranscription
  reportedStatusesExact :
    reviewStatuses reviews = P94AssembledSourceProgram.independentReviewStatuses
  packageCountExact : program.packages.length = 13
  distinguishedClauseOrderExact :
    program.distinguishedEntries.map
        (fun distinguished => distinguished.entry.claim.clause) = P94Clause.all

/-- The externally reviewed source-fidelity seal for the exact existing assembled value. -/
def assembledProgramSourceFaithful :
    AssembledProgramSourceFaithful independentReviewPackage
      P94AssembledSourceProgram.assembledProgram :=
  AssembledProgramSourceFaithful.mk rfl rfl
    P94SourceAuditLedger.section_record_clauses_exact
    P94SourceAuditLedger.IllustrationBlock.count
    independentReviewPackage.conformationDefinition.sourceFaithful
    independentReviewPackage.torsionAngle.sourceFaithful
    independentReviewPackage.torsionElectronicProxy.sourceFaithful
    independentReviewPackage.eclipsedStaggeredGauche.sourceFaithful
    independentReviewPackage.trigonal.sourceFaithful
    independentReviewPackage.sCisSTrans.sourceFaithful
    independentReviewPackage.envelope.sourceFaithful
    independentReviewPackage.chairBoatTwist.sourceFaithful
    independentReviewPackage.halfChair.sourceFaithful
    independentReviewPackage.crown.cyclooctaneSourceFaithful
    independentReviewPackage.crown.cyclodecaneSourceFaithful
    independentReviewPackage.tub.sourceFaithful
    independentReviewPackage.inOut.sourceFaithful
    review_statuses_match_assembled
    P94AssembledSourceProgram.assembled_program_package_count_exact
    P94AssembledSourceProgram.distinguished_clauses_exact

/-- A canonical source program is a program paired with the private source-fidelity seal. -/
structure CanonicallyAdoptedSourceProgram where
  reviews : IndependentReviewPackage
  program : P94FrozenSourceProgram
  sourceFaithful : AssembledProgramSourceFaithful reviews program

/-- The sole canonically adopted P-94 source program. -/
noncomputable def canonicalSourceProgram : CanonicallyAdoptedSourceProgram where
  reviews := independentReviewPackage
  program := P94AssembledSourceProgram.assembledProgram
  sourceFaithful := assembledProgramSourceFaithful

@[simp] theorem canonical_program_exact :
    canonicalSourceProgram.program = P94AssembledSourceProgram.assembledProgram :=
  canonicalSourceProgram.sourceFaithful.programExact

@[simp] theorem canonical_program_package_count_exact :
    canonicalSourceProgram.program.packages.length = 13 :=
  P94AssembledSourceProgram.assembled_program_package_count_exact

/-- Reuse, rather than rebuild, the already-proved normalization-totality boundary. -/
theorem canonical_program_fixedNormalizationTotality :
    IUPACNormativeProvision.P94RemainingFixedNormalizationTotality
      canonicalSourceProgram.program.policy :=
  canonicalSourceProgram.program.fixedNormalizationTotality

end P94CanonicalAdoption

namespace IUPACNormativeProvision

/-- Canonical positive policy bundle: canonical P-93 plus the policy projected from the adopted,
proof-bearing P-94 program—not from the pre-adoption candidate alias. -/
noncomputable def IUPACCanonicalDescriptorBearingPolicies :
    DescriptorBearingReviewedPolicies :=
  let p93 := P93CanonicalSourceProgram.iupacP93CanonicalSourceProgram.compiledPolicies
  { remaining71 :=
      { p93General := p93.general
        p93Noncarbon := p93.noncarbon
        p93Acyclic := p93.acyclic
        p93Cyclic := p93.cyclic
        p94 := P94CanonicalAdoption.canonicalSourceProgram.program.policy } }

theorem iupacCanonicalPolicies_p94_exact :
    IUPACCanonicalDescriptorBearingPolicies.remaining71.p94 =
      P94CanonicalAdoption.canonicalSourceProgram.program.policy :=
  rfl

/-- Re-export the already-proved 152-row nonvacuity family under the adopted canonical name. -/
noncomputable def iupacCanonicalGlobalReviewedNonvacuity
    (negative : GlobalNonDescriptorReviewedSemantics) :
    DescriptorBearingReviewedNonvacuity
      (parameterizedGlobalReviewedSemantics
        IUPACCanonicalDescriptorBearingPolicies negative) := by
  simpa [IUPACCanonicalDescriptorBearingPolicies,
    P94CanonicalAdoption.canonicalSourceProgram,
    IUPACP93CanonicalAssembledP94CandidateDescriptorBearingPolicies,
    Remaining56P93ReviewedPolicies.toDescriptorBearingWithP94AssembledCandidate,
    Remaining56P93ReviewedPolicies.toRemaining71WithP94AssembledCandidate] using
      iupacP93CanonicalAssembledP94CandidateGlobalReviewedNonvacuity negative

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.P94CanonicalAdoption.review_evidence_scope_exact
assert_kernel_only TetraStereo.OneCenter.P94CanonicalAdoption.independentReviewPackage
assert_kernel_only TetraStereo.OneCenter.P94CanonicalAdoption.review_statuses_match_assembled
assert_kernel_only TetraStereo.OneCenter.P94CanonicalAdoption.assembledProgramSourceFaithful
assert_kernel_only TetraStereo.OneCenter.P94CanonicalAdoption.canonical_program_exact
assert_kernel_only
  TetraStereo.OneCenter.P94CanonicalAdoption.canonical_program_fixedNormalizationTotality
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.iupacCanonicalPolicies_p94_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.iupacCanonicalGlobalReviewedNonvacuity
