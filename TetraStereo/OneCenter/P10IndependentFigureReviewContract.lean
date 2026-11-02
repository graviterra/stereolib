import TetraStereo.OneCenter.P10TechnicalAuditReadiness
import TetraStereo.OneCenter.IUPACNormativeFigureReviewConvergence
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192












namespace TetraStereo.OneCenter
namespace P10IndependentFigureReviewContract

open IUPACNormativeFigureReviewConvergence
open P10FigureTranscription

def ReviewMetadataMatches
    (reviewer : DeclaredIndependentReviewer)
    {SourceFaithful : AtomLevelFigureTranscription → Prop}
    (review : ReviewedFigureTranscription SourceFaithful) : Prop :=
  review.reviewer = reviewer.identity ∧
    review.reviewDate = reviewer.reviewDate ∧
      review.method = reviewer.method

/-! One proof-relevant package for the largest normative figure cluster. Exact target coverage is
permutation equality with the duplicate-free 473-item canonical queue. -/
structure IndependentReviewPackage
    (SourceFaithful : AtomLevelFigureTranscription → Prop) where
  reviewer : DeclaredIndependentReviewer
  technicalDossier : P10TechnicalAuditReadiness.MachinePreparedForIndependentReview
  reviews : List (ReviewedFigureTranscription SourceFaithful)
  completeReviewedCoverage : CompleteReviewedCoverage reviews
  reviewMetadataExact : reviews.Forall (ReviewMetadataMatches reviewer)

namespace IndependentReviewPackage

variable {SourceFaithful : AtomLevelFigureTranscription → Prop}

@[simp] theorem review_count_exact
    (package : IndependentReviewPackage SourceFaithful) :
    package.reviews.length = 473 := by
  calc
    package.reviews.length = (reviewedTranscriptions package.reviews).length := by
      simp [reviewedTranscriptions]
    _ = 473 := complete_reviewed_catalog_has_473_transcriptions package.reviews
      package.completeReviewedCoverage

theorem every_review_metadata_exact
    (package : IndependentReviewPackage SourceFaithful)
    (review : ReviewedFigureTranscription SourceFaithful)
    (member : review ∈ package.reviews) :
    review.reviewer = package.reviewer.identity ∧
      review.reviewDate = package.reviewer.reviewDate ∧
        review.method = package.reviewer.method :=
  (List.forall_iff_forall_mem.mp package.reviewMetadataExact) review member

end IndependentReviewPackage

@[simp] theorem source_artifact_digest_matches_manifest :
    sourceArtifactSha256 =
      (IUPACNormativeSource.sha256? .blueBook2013P10).getD "" :=
  rfl

def P10FigureReviewAdopted
    (SourceFaithful : AtomLevelFigureTranscription → Prop)
    (source : IUPACNormativeSource) : Prop :=
  source = .blueBook2013P10 ∧ Nonempty (IndependentReviewPackage SourceFaithful)

theorem p10_figure_review_adopted_of_package
    {SourceFaithful : AtomLevelFigureTranscription → Prop}
    (package : IndependentReviewPackage SourceFaithful) :
    P10FigureReviewAdopted SourceFaithful .blueBook2013P10 :=
  ⟨rfl, ⟨package⟩⟩

def p10SourceFigureReviewSeal
    {SourceFaithful : AtomLevelFigureTranscription → Prop}
    (package : IndependentReviewPackage SourceFaithful) :
    SourceFigureReviewSeal (P10FigureReviewAdopted SourceFaithful) .blueBook2013P10 where
  reviewer := package.reviewer
  frozenSourceSha256 := sourceArtifactSha256
  frozenSourceSha256Exact := source_artifact_digest_matches_manifest
  reviewedTargetCount := 473
  reviewedTargetCountExact := by decide
  reviewComplete := p10_figure_review_adopted_of_package package

@[simp] theorem p10_seal_target_count_exact
    {SourceFaithful : AtomLevelFigureTranscription → Prop}
    (package : IndependentReviewPackage SourceFaithful) :
    (p10SourceFigureReviewSeal package).reviewedTargetCount = 473 :=
  rfl

@[simp] theorem p10_seal_frozen_digest_exact
    {SourceFaithful : AtomLevelFigureTranscription → Prop}
    (package : IndependentReviewPackage SourceFaithful) :
    (p10SourceFigureReviewSeal package).frozenSourceSha256 = sourceArtifactSha256 :=
  rfl

def candidateProvisionAuditChecklist
    {SourceFaithful : AtomLevelFigureTranscription → Prop}
    (_package : IndependentReviewPackage SourceFaithful) :
    IUPACNormativeSource.ProvisionAuditChecklist :=
  (IUPACNormativeSource.currentProvisionAuditChecklist .blueBook2013P10).withFigureReview

@[simp] theorem candidate_checklist_complete
    {SourceFaithful : AtomLevelFigureTranscription → Prop}
    (package : IndependentReviewPackage SourceFaithful) :
    (candidateProvisionAuditChecklist package).Complete := by
  exact complete_after_confirming_sole_figure_requirement
    (IUPACNormativeSource.currentProvisionAuditChecklist .blueBook2013P10)
    P10TechnicalAuditReadiness.current_open_p10_review_requirements_exact

end P10IndependentFigureReviewContract
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P10IndependentFigureReviewContract.IndependentReviewPackage.review_count_exact
assert_kernel_only
  TetraStereo.OneCenter.P10IndependentFigureReviewContract.IndependentReviewPackage.every_review_metadata_exact
assert_kernel_only
  TetraStereo.OneCenter.P10IndependentFigureReviewContract.source_artifact_digest_matches_manifest
assert_kernel_only
  TetraStereo.OneCenter.P10IndependentFigureReviewContract.p10_figure_review_adopted_of_package
assert_kernel_only
  TetraStereo.OneCenter.P10IndependentFigureReviewContract.p10_seal_target_count_exact
assert_kernel_only
  TetraStereo.OneCenter.P10IndependentFigureReviewContract.p10_seal_frozen_digest_exact
assert_kernel_only
  TetraStereo.OneCenter.P10IndependentFigureReviewContract.candidate_checklist_complete
