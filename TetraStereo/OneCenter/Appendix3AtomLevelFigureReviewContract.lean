import TetraStereo.OneCenter.Appendix3TechnicalAuditReadiness
import TetraStereo.OneCenter.AuthoritativeChemicalInput
import TetraStereo.OneCenter.IUPACNormativeFigureReviewConvergence
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192














namespace TetraStereo.OneCenter
namespace Appendix3
namespace AtomLevelFigureReviewContract

open BlueBookAppendix3Audit
open IUPACNormativeFigureReviewConvergence

/-! One atom-level transcription for a directly drawn or source-rule-composed Appendix row. -/
structure AtomLevelStructureTranscription where
  provision : Provision
  provisionCanonical : provision ∈ Provision.all
  molecularGraphs : List CertifiedAuthoritativeChemicalInput
  molecularGraphsNonempty : molecularGraphs ≠ []

def coveredProvisions (transcriptions : List AtomLevelStructureTranscription) : List Provision :=
  transcriptions.map AtomLevelStructureTranscription.provision

def ExactProvisionCoverage (transcriptions : List AtomLevelStructureTranscription) : Prop :=
  (coveredProvisions transcriptions).Perm Provision.all

structure ReviewedStructureTranscription
    (SourceFaithful : AtomLevelStructureTranscription → Prop) where
  transcription : AtomLevelStructureTranscription
  reviewer : String
  reviewDate : String
  method : String
  sourceFaithful : SourceFaithful transcription

def reviewedTranscriptions
    {SourceFaithful : AtomLevelStructureTranscription → Prop}
    (reviews : List (ReviewedStructureTranscription SourceFaithful)) :
    List AtomLevelStructureTranscription :=
  reviews.map ReviewedStructureTranscription.transcription

def CompleteReviewedCoverage
    {SourceFaithful : AtomLevelStructureTranscription → Prop}
    (reviews : List (ReviewedStructureTranscription SourceFaithful)) : Prop :=
  ExactProvisionCoverage (reviewedTranscriptions reviews)

def currentReviewedTranscriptions :
    List (ReviewedStructureTranscription fun _ => False) := []

@[simp] theorem current_reviewed_coverage_is_incomplete :
    ¬CompleteReviewedCoverage currentReviewedTranscriptions := by
  intro complete
  have impossible : 0 = 171 := by
    calc
      0 = (coveredProvisions
          (reviewedTranscriptions currentReviewedTranscriptions)).length := by
            rfl
      _ = Provision.all.length := complete.length_eq
      _ = 171 := Provision.all_length
  exact Nat.noConfusion impossible

def ReviewMetadataMatches
    (reviewer : DeclaredIndependentReviewer)
    {SourceFaithful : AtomLevelStructureTranscription → Prop}
    (review : ReviewedStructureTranscription SourceFaithful) : Prop :=
  review.reviewer = reviewer.identity ∧
    review.reviewDate = reviewer.reviewDate ∧
      review.method = reviewer.method

/-! `ArtifactContinuityReviewed` is deliberately external. The reviewed mirror digest is known to
differ from the historical frozen digest, so continuity cannot be manufactured by equality. -/
structure IndependentReviewPackage
    (SourceFaithful : AtomLevelStructureTranscription → Prop)
    (ArtifactContinuityReviewed : Prop) where
  reviewer : DeclaredIndependentReviewer
  technicalDossier : TechnicalAuditReadiness.TechnicalEvidence
  technicalDossierExact : technicalDossier = TechnicalAuditReadiness.currentTechnicalEvidence
  reviews : List (ReviewedStructureTranscription SourceFaithful)
  completeReviewedCoverage : CompleteReviewedCoverage reviews
  reviewMetadataExact : reviews.Forall (ReviewMetadataMatches reviewer)
  artifactContinuityReviewed : ArtifactContinuityReviewed

namespace IndependentReviewPackage

variable {SourceFaithful : AtomLevelStructureTranscription → Prop}
variable {ArtifactContinuityReviewed : Prop}

@[simp] theorem review_count_exact
    (package : IndependentReviewPackage SourceFaithful ArtifactContinuityReviewed) :
    package.reviews.length = 171 := by
  calc
    package.reviews.length = (reviewedTranscriptions package.reviews).length := by
      simp [reviewedTranscriptions]
    _ = (coveredProvisions (reviewedTranscriptions package.reviews)).length := by
      simp [coveredProvisions]
    _ = Provision.all.length := package.completeReviewedCoverage.length_eq
    _ = 171 := Provision.all_length

theorem every_review_has_nonempty_graphs
    (package : IndependentReviewPackage SourceFaithful ArtifactContinuityReviewed)
    (review : ReviewedStructureTranscription SourceFaithful)
    (_member : review ∈ package.reviews) :
    review.transcription.molecularGraphs ≠ [] :=
  review.transcription.molecularGraphsNonempty

theorem every_review_metadata_exact
    (package : IndependentReviewPackage SourceFaithful ArtifactContinuityReviewed)
    (review : ReviewedStructureTranscription SourceFaithful)
    (member : review ∈ package.reviews) :
    review.reviewer = package.reviewer.identity ∧
      review.reviewDate = package.reviewer.reviewDate ∧
        review.method = package.reviewer.method :=
  (List.forall_iff_forall_mem.mp package.reviewMetadataExact) review member

end IndependentReviewPackage

@[simp] theorem frozen_source_digest_matches_manifest :
    IUPACNormativeProvision.GlobalNonDescriptorAppendix3SourceMeanings.frozenSourceSha256 =
      (IUPACNormativeSource.sha256? .blueBook2013Appendix3).getD "" :=
  rfl

def Appendix3FigureReviewAdopted
    (SourceFaithful : AtomLevelStructureTranscription → Prop)
    (ArtifactContinuityReviewed : Prop)
    (source : IUPACNormativeSource) : Prop :=
  source = .blueBook2013Appendix3 ∧
    Nonempty (IndependentReviewPackage SourceFaithful ArtifactContinuityReviewed)

theorem appendix3_figure_review_adopted_of_package
    {SourceFaithful : AtomLevelStructureTranscription → Prop}
    {ArtifactContinuityReviewed : Prop}
    (package : IndependentReviewPackage SourceFaithful ArtifactContinuityReviewed) :
    Appendix3FigureReviewAdopted SourceFaithful ArtifactContinuityReviewed
      .blueBook2013Appendix3 :=
  ⟨rfl, ⟨package⟩⟩

def appendix3SourceFigureReviewSeal
    {SourceFaithful : AtomLevelStructureTranscription → Prop}
    {ArtifactContinuityReviewed : Prop}
    (package : IndependentReviewPackage SourceFaithful ArtifactContinuityReviewed) :
    SourceFigureReviewSeal
      (Appendix3FigureReviewAdopted SourceFaithful ArtifactContinuityReviewed)
      .blueBook2013Appendix3 where
  reviewer := package.reviewer
  frozenSourceSha256 :=
    IUPACNormativeProvision.GlobalNonDescriptorAppendix3SourceMeanings.frozenSourceSha256
  frozenSourceSha256Exact := frozen_source_digest_matches_manifest
  reviewedTargetCount := 171
  reviewedTargetCountExact := by decide
  reviewComplete := appendix3_figure_review_adopted_of_package package

@[simp] theorem appendix3_seal_target_count_exact
    {SourceFaithful : AtomLevelStructureTranscription → Prop}
    {ArtifactContinuityReviewed : Prop}
    (package : IndependentReviewPackage SourceFaithful ArtifactContinuityReviewed) :
    (appendix3SourceFigureReviewSeal package).reviewedTargetCount = 171 :=
  rfl

@[simp] theorem appendix3_seal_frozen_digest_exact
    {SourceFaithful : AtomLevelStructureTranscription → Prop}
    {ArtifactContinuityReviewed : Prop}
    (package : IndependentReviewPackage SourceFaithful ArtifactContinuityReviewed) :
    (appendix3SourceFigureReviewSeal package).frozenSourceSha256 =
      IUPACNormativeProvision.GlobalNonDescriptorAppendix3SourceMeanings.frozenSourceSha256 :=
  rfl

def candidateProvisionAuditChecklist
    {SourceFaithful : AtomLevelStructureTranscription → Prop}
    {ArtifactContinuityReviewed : Prop}
    (_package : IndependentReviewPackage SourceFaithful ArtifactContinuityReviewed) :
    IUPACNormativeSource.ProvisionAuditChecklist :=
  (IUPACNormativeSource.currentProvisionAuditChecklist .blueBook2013Appendix3).withFigureReview

@[simp] theorem candidate_checklist_complete
    {SourceFaithful : AtomLevelStructureTranscription → Prop}
    {ArtifactContinuityReviewed : Prop}
    (package : IndependentReviewPackage SourceFaithful ArtifactContinuityReviewed) :
    (candidateProvisionAuditChecklist package).Complete := by
  exact complete_after_confirming_sole_figure_requirement
    (IUPACNormativeSource.currentProvisionAuditChecklist .blueBook2013Appendix3)
    TechnicalAuditReadiness.current_open_appendix3_review_requirements_exact

end AtomLevelFigureReviewContract
end Appendix3
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Appendix3.AtomLevelFigureReviewContract.current_reviewed_coverage_is_incomplete
assert_kernel_only
  TetraStereo.OneCenter.Appendix3.AtomLevelFigureReviewContract.IndependentReviewPackage.review_count_exact
assert_kernel_only
  TetraStereo.OneCenter.Appendix3.AtomLevelFigureReviewContract.IndependentReviewPackage.every_review_has_nonempty_graphs
assert_kernel_only
  TetraStereo.OneCenter.Appendix3.AtomLevelFigureReviewContract.IndependentReviewPackage.every_review_metadata_exact
assert_kernel_only
  TetraStereo.OneCenter.Appendix3.AtomLevelFigureReviewContract.frozen_source_digest_matches_manifest
assert_kernel_only
  TetraStereo.OneCenter.Appendix3.AtomLevelFigureReviewContract.appendix3_figure_review_adopted_of_package
assert_kernel_only
  TetraStereo.OneCenter.Appendix3.AtomLevelFigureReviewContract.appendix3_seal_target_count_exact
assert_kernel_only
  TetraStereo.OneCenter.Appendix3.AtomLevelFigureReviewContract.appendix3_seal_frozen_digest_exact
assert_kernel_only
  TetraStereo.OneCenter.Appendix3.AtomLevelFigureReviewContract.candidate_checklist_complete
