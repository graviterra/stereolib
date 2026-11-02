import TetraStereo.OneCenter.Glycolipid1997TechnicalAuditReadiness
import TetraStereo.OneCenter.AuthoritativeChemicalInput
import TetraStereo.OneCenter.IUPACNormativeFigureReviewConvergence
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192













namespace TetraStereo.OneCenter
namespace Glycolipid1997
namespace IndependentFigureReviewContract

open IUPACNormativeFigureReviewConvergence

inductive SourceImageArtifact where
  | gl3Bond
  | gl41A
  | gl41B
  | gl42
  | gl432
  | gl535
  | gl61A
  | gl61B
  | gl65A
  | gl65B
  | alter
  | arrowB
  | arrowR
  deriving DecidableEq, Repr

namespace SourceImageArtifact

def all : List SourceImageArtifact :=
  [ .gl3Bond, .gl41A, .gl41B, .gl42, .gl432, .gl535, .gl61A, .gl61B, .gl65A,
    .gl65B, .alter, .arrowB, .arrowR ]

@[simp] theorem mem_all (artifact : SourceImageArtifact) : artifact ∈ all := by
  cases artifact <;> simp [all]

theorem all_nodup : all.Nodup := by decide

def relativePath : SourceImageArtifact → String
  | .gl3Bond => "iupac.qmul.ac.uk/misc/miscgif/GL3BND.GIF"
  | .gl41A => "iupac.qmul.ac.uk/misc/miscgif/GL41A.GIF"
  | .gl41B => "iupac.qmul.ac.uk/misc/miscgif/GL41B.GIF"
  | .gl42 => "iupac.qmul.ac.uk/misc/miscgif/GL42.GIF"
  | .gl432 => "iupac.qmul.ac.uk/misc/miscgif/GL432.GIF"
  | .gl535 => "iupac.qmul.ac.uk/misc/miscgif/GL535.GIF"
  | .gl61A => "iupac.qmul.ac.uk/misc/miscgif/GL61A.GIF"
  | .gl61B => "iupac.qmul.ac.uk/misc/miscgif/GL61B.GIF"
  | .gl65A => "iupac.qmul.ac.uk/misc/miscgif/GL65A.GIF"
  | .gl65B => "iupac.qmul.ac.uk/misc/miscgif/GL65B.GIF"
  | .alter => "iupac.qmul.ac.uk/greek/ALTER.GIF"
  | .arrowB => "iupac.qmul.ac.uk/greek/ARROWB.GIF"
  | .arrowR => "iupac.qmul.ac.uk/greek/ARROWR.GIF"

def isChemicalFigure : SourceImageArtifact → Bool
  | .alter | .arrowB | .arrowR => false
  | _ => true

def isChemicalNotation : SourceImageArtifact → Bool
  | .gl3Bond => true
  | _ => false

end SourceImageArtifact

def sourceImageArtifacts : List SourceImageArtifact := SourceImageArtifact.all

def chemicalFigureTargets : List SourceImageArtifact :=
  sourceImageArtifacts.filter SourceImageArtifact.isChemicalFigure

def chemicalNotationArtifacts : List SourceImageArtifact :=
  sourceImageArtifacts.filter SourceImageArtifact.isChemicalNotation

def nonchemicalArtifacts : List SourceImageArtifact :=
  sourceImageArtifacts.filter fun artifact => !artifact.isChemicalFigure

@[simp] theorem source_image_count_exact : sourceImageArtifacts.length = 13 := by decide
@[simp] theorem chemical_figure_target_count_exact : chemicalFigureTargets.length = 10 := by decide
@[simp] theorem chemical_notation_artifacts_exact :
    chemicalNotationArtifacts = [.gl3Bond] := by decide
@[simp] theorem nonchemical_artifact_count_exact : nonchemicalArtifacts.length = 3 := by decide
theorem source_image_artifacts_nodup : sourceImageArtifacts.Nodup := SourceImageArtifact.all_nodup

structure CertifiedMoleculeFamily where
  Parameter : Type
  parameterNonempty : Nonempty Parameter
  instantiate : Parameter → CertifiedAuthoritativeChemicalInput

inductive ChemicalFigureDenotation : Type 1 where
  | concrete (input : CertifiedAuthoritativeChemicalInput)
  | moleculeFamily (family : CertifiedMoleculeFamily)

structure ChemicalNotationContextEvidence where
  embeddingRelation : String
  literalPrefix : String
  frozenHtmlPath : String
  frozenHtmlSha256 : String
  openBondOrder : Nat
  openEndpointCount : Nat
  openBondOrientations : List String

def gl3BondContextEvidence : ChemicalNotationContextEvidence where
  embeddingRelation := "immediately_after_literal"
  literalPrefix := "O=P"
  frozenHtmlPath :=
    "record-ac80ee881499435cfddd99135a59d596" ++
      "record-847e14b2b183d4493d1004ed04524099"
  frozenHtmlSha256 := "bd1a1225e35882012bf03438bd432a003ce5d48410a3e96102805646b32a41cc"
  openBondOrder := 1
  openEndpointCount := 2
  openBondOrientations := ["upper-right", "lower-right"]

inductive FigureDenotation : SourceImageArtifact → Type 1 where
  | chemical {artifact : SourceImageArtifact}
      (chemicalTarget : artifact.isChemicalFigure = true)
      (notNotation : artifact.isChemicalNotation = false)
      (denotation : ChemicalFigureDenotation) : FigureDenotation artifact
  | chemicalNotationGlyph {artifact : SourceImageArtifact}
      (notationTarget : artifact.isChemicalNotation = true)
      (contextEvidence : ChemicalNotationContextEvidence)
      (contextExact : contextEvidence = gl3BondContextEvidence) : FigureDenotation artifact
  | nonchemicalGlyph {artifact : SourceImageArtifact}
      (nonchemicalTarget : artifact.isChemicalFigure = false) : FigureDenotation artifact

structure FigureTranscription : Type 1 where
  artifact : SourceImageArtifact
  denotation : FigureDenotation artifact

def coveredArtifacts (transcriptions : List FigureTranscription) : List SourceImageArtifact :=
  transcriptions.map FigureTranscription.artifact

def ExactFigureCoverage (transcriptions : List FigureTranscription) : Prop :=
  (coveredArtifacts transcriptions).Perm sourceImageArtifacts

structure ReviewedFigureTranscription
    (SourceFaithful : FigureTranscription → Prop) : Type 1 where
  transcription : FigureTranscription
  reviewer : String
  reviewDate : String
  method : String
  sourceFaithful : SourceFaithful transcription

def reviewedTranscriptions
    {SourceFaithful : FigureTranscription → Prop}
    (reviews : List (ReviewedFigureTranscription SourceFaithful)) : List FigureTranscription :=
  reviews.map ReviewedFigureTranscription.transcription

def CompleteReviewedCoverage
    {SourceFaithful : FigureTranscription → Prop}
    (reviews : List (ReviewedFigureTranscription SourceFaithful)) : Prop :=
  ExactFigureCoverage (reviewedTranscriptions reviews)

def currentReviewedTranscriptions : List (ReviewedFigureTranscription fun _ => False) := []

@[simp] theorem current_reviewed_coverage_is_incomplete :
    ¬CompleteReviewedCoverage currentReviewedTranscriptions := by
  intro complete
  have impossible : 0 = 13 := by
    calc
      0 = (coveredArtifacts (reviewedTranscriptions currentReviewedTranscriptions)).length := rfl
      _ = sourceImageArtifacts.length := complete.length_eq
      _ = 13 := source_image_count_exact
  exact Nat.noConfusion impossible

def sourceBundleSha256 : String :=
  (P10DelegatedAuthorityCorpus.snapshot .glycolipid1997).bundleSha256

def ReviewMetadataMatches
    (reviewer : DeclaredIndependentReviewer)
    {SourceFaithful : FigureTranscription → Prop}
    (review : ReviewedFigureTranscription SourceFaithful) : Prop :=
  review.reviewer = reviewer.identity ∧ review.reviewDate = reviewer.reviewDate ∧
    review.method = reviewer.method

structure IndependentReviewPackage
    (SourceFaithful : FigureTranscription → Prop)
    (ArtifactContinuityReviewed : Prop) : Type 1 where
  reviewer : DeclaredIndependentReviewer
  technicalDossier : TechnicalAuditReadiness.MachinePreparedForIndependentReview
  reviews : List (ReviewedFigureTranscription SourceFaithful)
  completeReviewedCoverage : CompleteReviewedCoverage reviews
  reviewMetadataExact : reviews.Forall (ReviewMetadataMatches reviewer)
  artifactContinuityReviewed : ArtifactContinuityReviewed

namespace IndependentReviewPackage

variable {SourceFaithful : FigureTranscription → Prop}
variable {ArtifactContinuityReviewed : Prop}

@[simp] theorem review_count_exact
    (package : IndependentReviewPackage SourceFaithful ArtifactContinuityReviewed) :
    package.reviews.length = 13 := by
  calc
    package.reviews.length = (reviewedTranscriptions package.reviews).length := by
      simp [reviewedTranscriptions]
    _ = (coveredArtifacts (reviewedTranscriptions package.reviews)).length := by
      simp [coveredArtifacts]
    _ = sourceImageArtifacts.length := package.completeReviewedCoverage.length_eq
    _ = 13 := source_image_count_exact

theorem every_review_metadata_exact
    (package : IndependentReviewPackage SourceFaithful ArtifactContinuityReviewed)
    (review : ReviewedFigureTranscription SourceFaithful) (member : review ∈ package.reviews) :
    review.reviewer = package.reviewer.identity ∧
      review.reviewDate = package.reviewer.reviewDate ∧ review.method = package.reviewer.method :=
  (List.forall_iff_forall_mem.mp package.reviewMetadataExact) review member

end IndependentReviewPackage

@[simp] theorem source_bundle_digest_matches_manifest :
    sourceBundleSha256 =
      (IUPACNormativeSource.sha256? .glycolipidRecommendations1997).getD "" := rfl

def GlycolipidFigureReviewAdopted
    (SourceFaithful : FigureTranscription → Prop)
    (ArtifactContinuityReviewed : Prop) (source : IUPACNormativeSource) : Prop :=
  source = .glycolipidRecommendations1997 ∧
    Nonempty (IndependentReviewPackage SourceFaithful ArtifactContinuityReviewed)

theorem glycolipid_figure_review_adopted_of_package
    {SourceFaithful : FigureTranscription → Prop}
    {ArtifactContinuityReviewed : Prop}
    (package : IndependentReviewPackage SourceFaithful ArtifactContinuityReviewed) :
    GlycolipidFigureReviewAdopted SourceFaithful ArtifactContinuityReviewed
      .glycolipidRecommendations1997 :=
  ⟨rfl, ⟨package⟩⟩

def glycolipidSourceFigureReviewSeal
    {SourceFaithful : FigureTranscription → Prop}
    {ArtifactContinuityReviewed : Prop}
    (package : IndependentReviewPackage SourceFaithful ArtifactContinuityReviewed) :
    SourceFigureReviewSeal
      (GlycolipidFigureReviewAdopted SourceFaithful ArtifactContinuityReviewed)
      .glycolipidRecommendations1997 where
  reviewer := package.reviewer
  frozenSourceSha256 := sourceBundleSha256
  frozenSourceSha256Exact := source_bundle_digest_matches_manifest
  reviewedTargetCount := 13
  reviewedTargetCountExact := by decide
  reviewComplete := glycolipid_figure_review_adopted_of_package package

@[simp] theorem glycolipid_seal_target_count_exact
    {SourceFaithful : FigureTranscription → Prop}
    {ArtifactContinuityReviewed : Prop}
    (package : IndependentReviewPackage SourceFaithful ArtifactContinuityReviewed) :
    (glycolipidSourceFigureReviewSeal package).reviewedTargetCount = 13 := rfl

def candidateProvisionAuditChecklist
    {SourceFaithful : FigureTranscription → Prop}
    {ArtifactContinuityReviewed : Prop}
    (_package : IndependentReviewPackage SourceFaithful ArtifactContinuityReviewed) :
    IUPACNormativeSource.ProvisionAuditChecklist :=
  (IUPACNormativeSource.currentProvisionAuditChecklist
    .glycolipidRecommendations1997).withFigureReview

@[simp] theorem candidate_checklist_complete
    {SourceFaithful : FigureTranscription → Prop}
    {ArtifactContinuityReviewed : Prop}
    (package : IndependentReviewPackage SourceFaithful ArtifactContinuityReviewed) :
    (candidateProvisionAuditChecklist package).Complete := by
  exact complete_after_confirming_sole_figure_requirement
    (IUPACNormativeSource.currentProvisionAuditChecklist .glycolipidRecommendations1997)
    TechnicalAuditReadiness.current_open_glycolipid_review_requirements_exact

end IndependentFigureReviewContract
end Glycolipid1997
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Glycolipid1997.IndependentFigureReviewContract.source_image_count_exact
assert_kernel_only TetraStereo.OneCenter.Glycolipid1997.IndependentFigureReviewContract.chemical_figure_target_count_exact
assert_kernel_only TetraStereo.OneCenter.Glycolipid1997.IndependentFigureReviewContract.nonchemical_artifact_count_exact
assert_kernel_only TetraStereo.OneCenter.Glycolipid1997.IndependentFigureReviewContract.source_image_artifacts_nodup
assert_kernel_only TetraStereo.OneCenter.Glycolipid1997.IndependentFigureReviewContract.current_reviewed_coverage_is_incomplete
assert_kernel_only TetraStereo.OneCenter.Glycolipid1997.IndependentFigureReviewContract.IndependentReviewPackage.review_count_exact
assert_kernel_only TetraStereo.OneCenter.Glycolipid1997.IndependentFigureReviewContract.IndependentReviewPackage.every_review_metadata_exact
assert_kernel_only TetraStereo.OneCenter.Glycolipid1997.IndependentFigureReviewContract.source_bundle_digest_matches_manifest
assert_kernel_only TetraStereo.OneCenter.Glycolipid1997.IndependentFigureReviewContract.glycolipid_figure_review_adopted_of_package
assert_kernel_only TetraStereo.OneCenter.Glycolipid1997.IndependentFigureReviewContract.glycolipid_seal_target_count_exact
assert_kernel_only TetraStereo.OneCenter.Glycolipid1997.IndependentFigureReviewContract.candidate_checklist_complete
