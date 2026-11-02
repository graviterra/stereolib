import TetraStereo.OneCenter.Carbohydrate1996TechnicalAuditReadiness
import TetraStereo.OneCenter.IUPACNormativeFigureReviewConvergence
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192












namespace TetraStereo.OneCenter
namespace Carbohydrate1996
namespace IndependentFigureReviewContract

open Carbohydrate1996ImageTranscription
open IUPACNormativeFigureReviewConvergence

def sourceBundleSha256 : String :=
  (P10DelegatedAuthorityCorpus.snapshot .carbohydrate1996).bundleSha256

def ReviewMetadataMatches
    (reviewer : DeclaredIndependentReviewer)
    {SourceFaithful : AtomLevelImageTranscription → Prop}
    (review : ReviewedImageTranscription SourceFaithful) : Prop :=
  review.reviewer = reviewer.identity ∧
    review.reviewDate = reviewer.reviewDate ∧
      review.method = reviewer.method

structure IndependentReviewPackage
    (SourceFaithful : AtomLevelImageTranscription → Prop) where
  reviewer : DeclaredIndependentReviewer
  technicalDossier : TechnicalAuditReadiness.TechnicalEvidence
  technicalDossierExact : technicalDossier = TechnicalAuditReadiness.currentTechnicalEvidence
  reviews : List (ReviewedImageTranscription SourceFaithful)
  completeReviewedCoverage : CompleteReviewedCoverage reviews
  reviewMetadataExact : reviews.Forall (ReviewMetadataMatches reviewer)

namespace IndependentReviewPackage

variable {SourceFaithful : AtomLevelImageTranscription → Prop}

@[simp] theorem review_count_exact
    (package : IndependentReviewPackage SourceFaithful) :
    package.reviews.length = 425 := by
  calc
    package.reviews.length = (reviewedTranscriptions package.reviews).length := by
      simp [reviewedTranscriptions]
    _ = 425 := complete_reviewed_catalog_has_425_transcriptions package.reviews
      package.completeReviewedCoverage

theorem every_review_metadata_exact
    (package : IndependentReviewPackage SourceFaithful)
    (review : ReviewedImageTranscription SourceFaithful)
    (member : review ∈ package.reviews) :
    review.reviewer = package.reviewer.identity ∧
      review.reviewDate = package.reviewer.reviewDate ∧
        review.method = package.reviewer.method :=
  (List.forall_iff_forall_mem.mp package.reviewMetadataExact) review member

end IndependentReviewPackage

@[simp] theorem source_bundle_digest_matches_manifest :
    sourceBundleSha256 =
      (IUPACNormativeSource.sha256? .carbohydrateRecommendations1996).getD "" :=
  rfl

def CarbohydrateFigureReviewAdopted
    (SourceFaithful : AtomLevelImageTranscription → Prop)
    (source : IUPACNormativeSource) : Prop :=
  source = .carbohydrateRecommendations1996 ∧
    Nonempty (IndependentReviewPackage SourceFaithful)

theorem carbohydrate_figure_review_adopted_of_package
    {SourceFaithful : AtomLevelImageTranscription → Prop}
    (package : IndependentReviewPackage SourceFaithful) :
    CarbohydrateFigureReviewAdopted SourceFaithful .carbohydrateRecommendations1996 :=
  ⟨rfl, ⟨package⟩⟩

def carbohydrateSourceFigureReviewSeal
    {SourceFaithful : AtomLevelImageTranscription → Prop}
    (package : IndependentReviewPackage SourceFaithful) :
    SourceFigureReviewSeal (CarbohydrateFigureReviewAdopted SourceFaithful)
      .carbohydrateRecommendations1996 where
  reviewer := package.reviewer
  frozenSourceSha256 := sourceBundleSha256
  frozenSourceSha256Exact := source_bundle_digest_matches_manifest
  reviewedTargetCount := 425
  reviewedTargetCountExact := by decide
  reviewComplete := carbohydrate_figure_review_adopted_of_package package

@[simp] theorem carbohydrate_seal_target_count_exact
    {SourceFaithful : AtomLevelImageTranscription → Prop}
    (package : IndependentReviewPackage SourceFaithful) :
    (carbohydrateSourceFigureReviewSeal package).reviewedTargetCount = 425 :=
  rfl

@[simp] theorem carbohydrate_seal_frozen_digest_exact
    {SourceFaithful : AtomLevelImageTranscription → Prop}
    (package : IndependentReviewPackage SourceFaithful) :
    (carbohydrateSourceFigureReviewSeal package).frozenSourceSha256 = sourceBundleSha256 :=
  rfl

def candidateProvisionAuditChecklist
    {SourceFaithful : AtomLevelImageTranscription → Prop}
    (_package : IndependentReviewPackage SourceFaithful) :
    IUPACNormativeSource.ProvisionAuditChecklist :=
  (IUPACNormativeSource.currentProvisionAuditChecklist
    .carbohydrateRecommendations1996).withFigureReview

@[simp] theorem candidate_checklist_complete
    {SourceFaithful : AtomLevelImageTranscription → Prop}
    (package : IndependentReviewPackage SourceFaithful) :
    (candidateProvisionAuditChecklist package).Complete := by
  exact complete_after_confirming_sole_figure_requirement
    (IUPACNormativeSource.currentProvisionAuditChecklist .carbohydrateRecommendations1996)
    TechnicalAuditReadiness.current_open_carbohydrate_review_requirements_exact

end IndependentFigureReviewContract
end Carbohydrate1996
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996.IndependentFigureReviewContract.IndependentReviewPackage.review_count_exact
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996.IndependentFigureReviewContract.IndependentReviewPackage.every_review_metadata_exact
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996.IndependentFigureReviewContract.source_bundle_digest_matches_manifest
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996.IndependentFigureReviewContract.carbohydrate_figure_review_adopted_of_package
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996.IndependentFigureReviewContract.carbohydrate_seal_target_count_exact
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996.IndependentFigureReviewContract.carbohydrate_seal_frozen_digest_exact
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996.IndependentFigureReviewContract.candidate_checklist_complete
