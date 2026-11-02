import TetraStereo.OneCenter.IUPACNormativeFigureReviewFrontier
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter















namespace IUPACNormativeSource.ProvisionAuditChecklist


def withFigureReview (checklist : ProvisionAuditChecklist) : ProvisionAuditChecklist where
  provisionEnumerationConfirmed := checklist.provisionEnumerationConfirmed
  proseTableCoverageConfirmed := checklist.proseTableCoverageConfirmed
  figureGraphTranscriptionsReviewed := true
  delegatedAuthorityClosureConfirmed := checklist.delegatedAuthorityClosureConfirmed

end IUPACNormativeSource.ProvisionAuditChecklist

namespace IUPACNormativeFigureReviewConvergence

open IUPACNormativeSource
open IUPACNormativeFigureReviewFrontier

/-- If the figure requirement is the sole open item, confirming it completes the checklist. -/
theorem complete_after_confirming_sole_figure_requirement
    (checklist : ProvisionAuditChecklist)
    (onlyFigure : checklist.openRequirements = [.figureGraphTranscriptionsReviewed]) :
    checklist.withFigureReview.Complete := by
  rcases checklist with ⟨enumeration, prose, figures, delegated⟩
  cases enumeration <;> cases prose <;> cases figures <;> cases delegated <;>
    simp [ProvisionAuditChecklist.openRequirements,
      ProvisionAuditChecklist.requirementConfirmed?,
      ProvisionAuditRequirement.all,
      ProvisionAuditChecklist.withFigureReview,
      ProvisionAuditChecklist.Complete] at onlyFigure ⊢


structure DeclaredIndependentReviewer where
  identity : String
  affiliation : String
  reviewDate : String
  method : String
  independenceStatement : String
  identityDeclared : identity ≠ ""
  affiliationDeclared : affiliation ≠ ""
  reviewDateDeclared : reviewDate ≠ ""
  methodDeclared : method ≠ ""
  independenceStatementDeclared : independenceStatement ≠ ""

/-- One source-family seal. `FigureReviewComplete` is deliberately external: Lean checks that its
proof covers the exact source family, but does not infer fidelity from a digest or target count. -/
structure SourceFigureReviewSeal
    (FigureReviewComplete : IUPACNormativeSource → Prop)
    (source : IUPACNormativeSource) where
  reviewer : DeclaredIndependentReviewer
  frozenSourceSha256 : String
  frozenSourceSha256Exact : frozenSourceSha256 = (sha256? source).getD ""
  reviewedTargetCount : Nat
  reviewedTargetCountExact : reviewedTargetCount = figureReviewTargetCount source
  reviewComplete : FigureReviewComplete source

/-- Exact dependent coverage: a source-family seal is required for every member of the manifest's
ten-source frontier.  No constructor field accepts a seal for an unrelated source. -/
structure FrontierFigureReviewPackage
    (FigureReviewComplete : IUPACNormativeSource → Prop) where
  «seal» : (source : IUPACNormativeSource) → source ∈ frontierSources →
    SourceFigureReviewSeal FigureReviewComplete source

theorem frontier_seal_target_count_exact
    {FigureReviewComplete : IUPACNormativeSource → Prop}
    (package : FrontierFigureReviewPackage FigureReviewComplete)
    (source : IUPACNormativeSource) (member : source ∈ frontierSources) :
    (package.seal source member).reviewedTargetCount = figureReviewTargetCount source :=
  (package.seal source member).reviewedTargetCountExact



def checklistAfterFigureReviews
    {FigureReviewComplete : IUPACNormativeSource → Prop}
    (_package : FrontierFigureReviewPackage FigureReviewComplete)
    (source : IUPACNormativeSource) : ProvisionAuditChecklist :=
  if source ∈ frontierSources then
    (currentProvisionAuditChecklist source).withFigureReview
  else
    currentProvisionAuditChecklist source

theorem every_source_complete_after_frontier_figure_reviews
    {FigureReviewComplete : IUPACNormativeSource → Prop}
    (package : FrontierFigureReviewPackage FigureReviewComplete)
    (source : IUPACNormativeSource) :
    (checklistAfterFigureReviews package source).Complete := by
  by_cases member : source ∈ frontierSources
  · simp only [checklistAfterFigureReviews, if_pos member]
    exact complete_after_confirming_sole_figure_requirement
      (currentProvisionAuditChecklist source)
      (every_frontier_source_has_only_figure_review_open source member)
  · simp only [checklistAfterFigureReviews, if_neg member]
    have currentComplete : ProvisionAuditComplete source := by
      by_contra incomplete
      have sourceMember :=
        (mem_currentIncompleteProvisionAuditSources_iff source).2 incomplete
      exact member (by simpa [frontierSources] using sourceMember)
    exact currentComplete

theorem every_source_has_no_open_requirements_after_frontier_figure_reviews
    {FigureReviewComplete : IUPACNormativeSource → Prop}
    (package : FrontierFigureReviewPackage FigureReviewComplete)
    (source : IUPACNormativeSource) :
    (checklistAfterFigureReviews package source).openRequirements = [] :=
  (ProvisionAuditChecklist.complete_iff_no_open_requirements
    (checklistAfterFigureReviews package source)).mp
      (every_source_complete_after_frontier_figure_reviews package source)


def currentFigureReviewComplete (_source : IUPACNormativeSource) : Prop := False

theorem current_frontier_review_package_uninhabited :
    ¬Nonempty (FrontierFigureReviewPackage currentFigureReviewComplete) := by
  rintro ⟨package⟩
  have p10Member : IUPACNormativeSource.blueBook2013P10 ∈ frontierSources := by
    decide
  exact (package.seal .blueBook2013P10 p10Member).reviewComplete

end IUPACNormativeFigureReviewConvergence
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeFigureReviewConvergence.complete_after_confirming_sole_figure_requirement
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeFigureReviewConvergence.frontier_seal_target_count_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeFigureReviewConvergence.every_source_complete_after_frontier_figure_reviews
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeFigureReviewConvergence.every_source_has_no_open_requirements_after_frontier_figure_reviews
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeFigureReviewConvergence.current_frontier_review_package_uninhabited
