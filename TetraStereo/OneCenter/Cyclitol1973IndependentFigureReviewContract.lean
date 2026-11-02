import TetraStereo.OneCenter.Cyclitol1973TechnicalAuditReadiness
import TetraStereo.OneCenter.AuthoritativeChemicalInput
import TetraStereo.OneCenter.IUPACNormativeFigureReviewConvergence
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192










namespace TetraStereo.OneCenter
namespace Cyclitol1973
namespace IndependentFigureReviewContract

open IUPACNormativeFigureReviewConvergence

structure CertifiedMoleculeFamily where
  Parameter : Type
  parameterNonempty : Nonempty Parameter
  instantiate : Parameter → CertifiedAuthoritativeChemicalInput

inductive FigureDenotation : Type 1 where
  | concrete (input : CertifiedAuthoritativeChemicalInput)
  | moleculeFamily (family : CertifiedMoleculeFamily)

structure FigureTranscription : Type 1 where
  artifact : SourceImageArtifact
  molecularTarget : artifact.isMolecularGraph = true
  normative1973Target : artifact.belongsTo1973Recommendation = true
  denotation : FigureDenotation

def figureTargets : List SourceImageArtifact :=
  SourceImageArtifact.all.filter fun artifact =>
    artifact.isMolecularGraph && artifact.belongsTo1973Recommendation

@[simp] theorem figure_target_count_exact : figureTargets.length = 42 := by decide
theorem figure_targets_nodup : figureTargets.Nodup := SourceImageArtifact.all_nodup.filter _

def coveredArtifacts (transcriptions : List FigureTranscription) : List SourceImageArtifact :=
  transcriptions.map FigureTranscription.artifact

def ExactFigureCoverage (transcriptions : List FigureTranscription) : Prop :=
  (coveredArtifacts transcriptions).Perm figureTargets

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
  have impossible : 0 = 42 := by
    calc
      0 = (coveredArtifacts (reviewedTranscriptions currentReviewedTranscriptions)).length := rfl
      _ = figureTargets.length := complete.length_eq
      _ = 42 := figure_target_count_exact
  exact Nat.noConfusion impossible

def sourceBundleSha256 : String :=
  (P10DelegatedAuthorityCorpus.snapshot .cyclitol1973).bundleSha256

def ReviewMetadataMatches
    (reviewer : DeclaredIndependentReviewer)
    {SourceFaithful : FigureTranscription → Prop}
    (review : ReviewedFigureTranscription SourceFaithful) : Prop :=
  review.reviewer = reviewer.identity ∧ review.reviewDate = reviewer.reviewDate ∧
    review.method = reviewer.method

structure IndependentReviewPackage
    (SourceFaithful : FigureTranscription → Prop) : Type 1 where
  reviewer : DeclaredIndependentReviewer
  technicalDossier : TechnicalAuditReadiness.MachinePreparedForIndependentReview
  reviews : List (ReviewedFigureTranscription SourceFaithful)
  completeReviewedCoverage : CompleteReviewedCoverage reviews
  reviewMetadataExact : reviews.Forall (ReviewMetadataMatches reviewer)

namespace IndependentReviewPackage

variable {SourceFaithful : FigureTranscription → Prop}

@[simp] theorem review_count_exact (package : IndependentReviewPackage SourceFaithful) :
    package.reviews.length = 42 := by
  calc
    package.reviews.length = (reviewedTranscriptions package.reviews).length := by
      simp [reviewedTranscriptions]
    _ = (coveredArtifacts (reviewedTranscriptions package.reviews)).length := by
      simp [coveredArtifacts]
    _ = figureTargets.length := package.completeReviewedCoverage.length_eq
    _ = 42 := figure_target_count_exact

theorem every_review_metadata_exact
    (package : IndependentReviewPackage SourceFaithful)
    (review : ReviewedFigureTranscription SourceFaithful) (member : review ∈ package.reviews) :
    review.reviewer = package.reviewer.identity ∧
      review.reviewDate = package.reviewer.reviewDate ∧ review.method = package.reviewer.method :=
  (List.forall_iff_forall_mem.mp package.reviewMetadataExact) review member

end IndependentReviewPackage

@[simp] theorem source_bundle_digest_matches_manifest :
    sourceBundleSha256 =
      (IUPACNormativeSource.sha256? .cyclitolRecommendations1973).getD "" := rfl

def CyclitolFigureReviewAdopted
    (SourceFaithful : FigureTranscription → Prop) (source : IUPACNormativeSource) : Prop :=
  source = .cyclitolRecommendations1973 ∧ Nonempty (IndependentReviewPackage SourceFaithful)

theorem cyclitol_figure_review_adopted_of_package
    {SourceFaithful : FigureTranscription → Prop}
    (package : IndependentReviewPackage SourceFaithful) :
    CyclitolFigureReviewAdopted SourceFaithful .cyclitolRecommendations1973 :=
  ⟨rfl, ⟨package⟩⟩

def cyclitolSourceFigureReviewSeal
    {SourceFaithful : FigureTranscription → Prop}
    (package : IndependentReviewPackage SourceFaithful) :
    SourceFigureReviewSeal (CyclitolFigureReviewAdopted SourceFaithful)
      .cyclitolRecommendations1973 where
  reviewer := package.reviewer
  frozenSourceSha256 := sourceBundleSha256
  frozenSourceSha256Exact := source_bundle_digest_matches_manifest
  reviewedTargetCount := 42
  reviewedTargetCountExact := by decide
  reviewComplete := cyclitol_figure_review_adopted_of_package package

@[simp] theorem cyclitol_seal_target_count_exact
    {SourceFaithful : FigureTranscription → Prop}
    (package : IndependentReviewPackage SourceFaithful) :
    (cyclitolSourceFigureReviewSeal package).reviewedTargetCount = 42 := rfl

def candidateProvisionAuditChecklist
    {SourceFaithful : FigureTranscription → Prop}
    (_package : IndependentReviewPackage SourceFaithful) :
    IUPACNormativeSource.ProvisionAuditChecklist :=
  (IUPACNormativeSource.currentProvisionAuditChecklist
    .cyclitolRecommendations1973).withFigureReview

@[simp] theorem candidate_checklist_complete
    {SourceFaithful : FigureTranscription → Prop}
    (package : IndependentReviewPackage SourceFaithful) :
    (candidateProvisionAuditChecklist package).Complete := by
  exact complete_after_confirming_sole_figure_requirement
    (IUPACNormativeSource.currentProvisionAuditChecklist .cyclitolRecommendations1973)
    TechnicalAuditReadiness.current_open_cyclitol_review_requirements_exact

end IndependentFigureReviewContract
end Cyclitol1973
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Cyclitol1973.IndependentFigureReviewContract.figure_target_count_exact
assert_kernel_only TetraStereo.OneCenter.Cyclitol1973.IndependentFigureReviewContract.figure_targets_nodup
assert_kernel_only TetraStereo.OneCenter.Cyclitol1973.IndependentFigureReviewContract.current_reviewed_coverage_is_incomplete
assert_kernel_only TetraStereo.OneCenter.Cyclitol1973.IndependentFigureReviewContract.IndependentReviewPackage.review_count_exact
assert_kernel_only TetraStereo.OneCenter.Cyclitol1973.IndependentFigureReviewContract.IndependentReviewPackage.every_review_metadata_exact
assert_kernel_only TetraStereo.OneCenter.Cyclitol1973.IndependentFigureReviewContract.source_bundle_digest_matches_manifest
assert_kernel_only TetraStereo.OneCenter.Cyclitol1973.IndependentFigureReviewContract.cyclitol_figure_review_adopted_of_package
assert_kernel_only TetraStereo.OneCenter.Cyclitol1973.IndependentFigureReviewContract.cyclitol_seal_target_count_exact
assert_kernel_only TetraStereo.OneCenter.Cyclitol1973.IndependentFigureReviewContract.candidate_checklist_complete
