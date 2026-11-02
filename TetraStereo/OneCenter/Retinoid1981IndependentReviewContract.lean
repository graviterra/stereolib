import TetraStereo.OneCenter.Retinoid1981TechnicalAuditReadiness
import TetraStereo.KernelOnly

set_option autoImplicit false

















namespace TetraStereo.OneCenter
namespace Retinoid1981
namespace IndependentReviewContract



structure IndependentHumanReviewer where
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

structure ClauseReview
    (ClauseSourceFaithful : SourceAudit.Ledger.NormativeClause → Prop) where
  clause : SourceAudit.Ledger.NormativeClause
  sourceFaithful : ClauseSourceFaithful clause

structure TableRowReview
    (TableRowSourceFaithful : SourceAudit.Ledger.StereoparentSubstituentRow → Prop) where
  row : SourceAudit.Ledger.StereoparentSubstituentRow
  sourceFaithful : TableRowSourceFaithful row



structure FigureGraphReview
    (FigureGraphSourceFaithful :
      FigureGraphTranscription.FrozenImageData →
        FigureGraphTranscription.FigureGraphFamilyEntry → Prop) where
  figure : FigureGraphTranscription.FrozenImageData
  family : FigureGraphTranscription.FigureGraphFamilyEntry
  artifactExact : family.artifact = figure.artifact
  sourceFaithful : FigureGraphSourceFaithful figure family



structure IndependentReviewPackage
    (ClauseSourceFaithful : SourceAudit.Ledger.NormativeClause → Prop)
    (TableRowSourceFaithful : SourceAudit.Ledger.StereoparentSubstituentRow → Prop)
    (FigureGraphSourceFaithful :
      FigureGraphTranscription.FrozenImageData →
        FigureGraphTranscription.FigureGraphFamilyEntry → Prop) where
  reviewer : IndependentHumanReviewer
  technicalDossier : TechnicalAuditReadiness.MachinePreparedForIndependentReview
  provisionEnumerationReview : List SourceAudit.Ledger.NormativeClause → Prop
  proseTableCoverageReview :
    List SourceAudit.Ledger.NormativeClause →
      List SourceAudit.Ledger.StereoparentSubstituentRow → Prop
  figureGraphCoverageReview :
    List FigureGraphTranscription.FrozenImageData →
      List FigureGraphTranscription.FigureGraphFamilyEntry → Prop
  clauseReviews : List (ClauseReview ClauseSourceFaithful)
  tableRowReviews : List (TableRowReview TableRowSourceFaithful)
  figureReviews : List (FigureGraphReview FigureGraphSourceFaithful)
  clauseReviewsExact : clauseReviews.map ClauseReview.clause =
    SourceAudit.Ledger.NormativeClause.all
  tableRowReviewsExact : tableRowReviews.map TableRowReview.row =
    SourceAudit.Ledger.stereoparentSubstituentRows
  figureImageReviewsExact : figureReviews.map FigureGraphReview.figure =
    FigureGraphTranscription.frozenImageData
  figureGraphFamilyReviewsExact : figureReviews.map FigureGraphReview.family =
    FigureGraphTranscription.figureGraphFamilies
  provisionEnumerationConfirmed :
    provisionEnumerationReview SourceAudit.Ledger.NormativeClause.all
  proseTableCoverageConfirmed :
    proseTableCoverageReview SourceAudit.Ledger.NormativeClause.all
      SourceAudit.Ledger.stereoparentSubstituentRows
  figureGraphTranscriptionsReviewed :
    figureGraphCoverageReview FigureGraphTranscription.frozenImageData
      FigureGraphTranscription.figureGraphFamilies

namespace IndependentReviewPackage

variable
  {ClauseSourceFaithful : SourceAudit.Ledger.NormativeClause → Prop}
  {TableRowSourceFaithful : SourceAudit.Ledger.StereoparentSubstituentRow → Prop}
  {FigureGraphSourceFaithful :
    FigureGraphTranscription.FrozenImageData →
      FigureGraphTranscription.FigureGraphFamilyEntry → Prop}

theorem clause_reviews_exact
    (package : IndependentReviewPackage ClauseSourceFaithful
      TableRowSourceFaithful FigureGraphSourceFaithful) :
    package.clauseReviews.map ClauseReview.clause =
      SourceAudit.Ledger.NormativeClause.all :=
  package.clauseReviewsExact

theorem table_row_reviews_exact
    (package : IndependentReviewPackage ClauseSourceFaithful
      TableRowSourceFaithful FigureGraphSourceFaithful) :
    package.tableRowReviews.map TableRowReview.row =
      SourceAudit.Ledger.stereoparentSubstituentRows :=
  package.tableRowReviewsExact

theorem figure_image_reviews_exact
    (package : IndependentReviewPackage ClauseSourceFaithful
      TableRowSourceFaithful FigureGraphSourceFaithful) :
    package.figureReviews.map FigureGraphReview.figure =
      FigureGraphTranscription.frozenImageData :=
  package.figureImageReviewsExact

theorem figure_graph_family_reviews_exact
    (package : IndependentReviewPackage ClauseSourceFaithful
      TableRowSourceFaithful FigureGraphSourceFaithful) :
    package.figureReviews.map FigureGraphReview.family =
      FigureGraphTranscription.figureGraphFamilies :=
  package.figureGraphFamilyReviewsExact

@[simp] theorem reviewed_graph_count_exact
    (package : IndependentReviewPackage ClauseSourceFaithful
      TableRowSourceFaithful FigureGraphSourceFaithful) :
    (package.figureReviews.flatMap fun review => review.family.graphs).length = 16 := by
  calc
    (package.figureReviews.flatMap fun review => review.family.graphs).length =
        ((package.figureReviews.map FigureGraphReview.family).flatMap
          FigureGraphTranscription.FigureGraphFamilyEntry.graphs).length := by
            simp [Function.comp_def]
    _ = (FigureGraphTranscription.figureGraphFamilies.flatMap
          FigureGraphTranscription.FigureGraphFamilyEntry.graphs).length := by
            rw [package.figureGraphFamilyReviewsExact]
    _ = 16 := FigureGraphTranscription.transcribedGraph_count

theorem every_figure_review_artifact_exact
    (package : IndependentReviewPackage ClauseSourceFaithful
      TableRowSourceFaithful FigureGraphSourceFaithful)
    (review : FigureGraphReview FigureGraphSourceFaithful)
    (_member : review ∈ package.figureReviews) :
    review.family.artifact = review.figure.artifact :=
  review.artifactExact

@[simp] theorem review_counts_exact
    (package : IndependentReviewPackage ClauseSourceFaithful
      TableRowSourceFaithful FigureGraphSourceFaithful) :
    package.clauseReviews.length = 62 ∧
      package.tableRowReviews.length = 10 ∧
        package.figureReviews.length = 14 := by
  constructor
  · simpa using congrArg List.length package.clauseReviewsExact
  constructor
  · simpa using congrArg List.length package.tableRowReviewsExact
  · simpa using congrArg List.length package.figureImageReviewsExact



def candidateProvisionAuditChecklist
    (_package : IndependentReviewPackage ClauseSourceFaithful
      TableRowSourceFaithful FigureGraphSourceFaithful) :
    IUPACNormativeSource.ProvisionAuditChecklist :=
  IUPACNormativeSource.ProvisionAuditChecklist.allConfirmed

@[simp] theorem candidate_checklist_complete
    (package : IndependentReviewPackage ClauseSourceFaithful
      TableRowSourceFaithful FigureGraphSourceFaithful) :
    package.candidateProvisionAuditChecklist.Complete := by
  simp [candidateProvisionAuditChecklist,
    IUPACNormativeSource.ProvisionAuditChecklist.Complete,
    IUPACNormativeSource.ProvisionAuditChecklist.allConfirmed]

@[simp] theorem candidate_checklist_has_no_open_requirements
    (package : IndependentReviewPackage ClauseSourceFaithful
      TableRowSourceFaithful FigureGraphSourceFaithful) :
    package.candidateProvisionAuditChecklist.openRequirements = [] :=
  (IUPACNormativeSource.ProvisionAuditChecklist.complete_iff_no_open_requirements
    package.candidateProvisionAuditChecklist).mp package.candidate_checklist_complete

end IndependentReviewPackage

/-- Repository issuance state. This remains false until an actual external package has been
reviewed and deliberately adopted; it is not inferred from machine readiness. -/
def currentIndependentReviewPackageIssued : Bool := false

@[simp] theorem current_independent_review_package_not_issued :
    currentIndependentReviewPackageIssued = false := by
  rfl

theorem current_manifest_retinoid_audit_not_promoted :
    ¬IUPACNormativeSource.ProvisionAuditComplete .retinoidRecommendations1981 :=
  TechnicalAuditReadiness.current_retinoid_audit_remains_incomplete

end IndependentReviewContract
end Retinoid1981
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.IndependentReviewContract.IndependentReviewPackage.clause_reviews_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.IndependentReviewContract.IndependentReviewPackage.table_row_reviews_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.IndependentReviewContract.IndependentReviewPackage.figure_image_reviews_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.IndependentReviewContract.IndependentReviewPackage.figure_graph_family_reviews_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.IndependentReviewContract.IndependentReviewPackage.reviewed_graph_count_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.IndependentReviewContract.IndependentReviewPackage.every_figure_review_artifact_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.IndependentReviewContract.IndependentReviewPackage.review_counts_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.IndependentReviewContract.IndependentReviewPackage.candidate_checklist_complete
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.IndependentReviewContract.IndependentReviewPackage.candidate_checklist_has_no_open_requirements
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.IndependentReviewContract.current_independent_review_package_not_issued
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.IndependentReviewContract.current_manifest_retinoid_audit_not_promoted
