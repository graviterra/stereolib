import TetraStereo.OneCenter.Retinoid1981IndependentReviewContract
import TetraStereo.OneCenter.IUPACNormativeFigureReviewConvergence
import TetraStereo.KernelOnly

set_option autoImplicit false












namespace TetraStereo.OneCenter
namespace Retinoid1981
namespace NormativeFigureReviewSeal

open IndependentReviewContract
open IUPACNormativeFigureReviewConvergence

variable
  {ClauseSourceFaithful : SourceAudit.Ledger.NormativeClause → Prop}
  {TableRowSourceFaithful : SourceAudit.Ledger.StereoparentSubstituentRow → Prop}
  {FigureGraphSourceFaithful :
    FigureGraphTranscription.FrozenImageData →
      FigureGraphTranscription.FigureGraphFamilyEntry → Prop}

def declaredIndependentReviewerOf
    (reviewer : IndependentHumanReviewer) : DeclaredIndependentReviewer where
  identity := reviewer.identity
  affiliation := reviewer.affiliation
  reviewDate := reviewer.reviewDate
  method := reviewer.method
  independenceStatement := reviewer.independenceStatement
  identityDeclared := reviewer.identityDeclared
  affiliationDeclared := reviewer.affiliationDeclared
  reviewDateDeclared := reviewer.reviewDateDeclared
  methodDeclared := reviewer.methodDeclared
  independenceStatementDeclared := reviewer.independenceStatementDeclared

/-! Adoption is source-indexed: the Retinoid package cannot serve as evidence for any other
normative source. -/
def RetinoidFigureReviewAdopted
    (ClauseSourceFaithful : SourceAudit.Ledger.NormativeClause → Prop)
    (TableRowSourceFaithful : SourceAudit.Ledger.StereoparentSubstituentRow → Prop)
    (FigureGraphSourceFaithful :
      FigureGraphTranscription.FrozenImageData →
        FigureGraphTranscription.FigureGraphFamilyEntry → Prop)
    (source : IUPACNormativeSource) : Prop :=
  source = .retinoidRecommendations1981 ∧
    Nonempty (IndependentReviewPackage ClauseSourceFaithful
      TableRowSourceFaithful FigureGraphSourceFaithful)

theorem retinoid_figure_review_adopted_of_package
    (package : IndependentReviewPackage ClauseSourceFaithful
      TableRowSourceFaithful FigureGraphSourceFaithful) :
    RetinoidFigureReviewAdopted ClauseSourceFaithful TableRowSourceFaithful
      FigureGraphSourceFaithful .retinoidRecommendations1981 :=
  ⟨rfl, ⟨package⟩⟩

/-! A genuine source-specific package supplies the complete global Retinoid seal. The digest and
target count are computed from the manifest/frontier definitions, not accepted from the caller. -/
def retinoidSourceFigureReviewSeal
    (package : IndependentReviewPackage ClauseSourceFaithful
      TableRowSourceFaithful FigureGraphSourceFaithful) :
    SourceFigureReviewSeal
      (RetinoidFigureReviewAdopted ClauseSourceFaithful TableRowSourceFaithful
        FigureGraphSourceFaithful)
      .retinoidRecommendations1981 where
  reviewer := declaredIndependentReviewerOf package.reviewer
  frozenSourceSha256 :=
    (IUPACNormativeSource.sha256? .retinoidRecommendations1981).getD ""
  frozenSourceSha256Exact := rfl
  reviewedTargetCount := 14
  reviewedTargetCountExact := by decide
  reviewComplete := retinoid_figure_review_adopted_of_package package

@[simp] theorem retinoid_seal_reviewer_identity_exact
    (package : IndependentReviewPackage ClauseSourceFaithful
      TableRowSourceFaithful FigureGraphSourceFaithful) :
    (retinoidSourceFigureReviewSeal package).reviewer.identity = package.reviewer.identity :=
  rfl

@[simp] theorem retinoid_seal_target_count_exact
    (package : IndependentReviewPackage ClauseSourceFaithful
      TableRowSourceFaithful FigureGraphSourceFaithful) :
    (retinoidSourceFigureReviewSeal package).reviewedTargetCount = 14 :=
  rfl

@[simp] theorem retinoid_seal_frozen_digest_exact
    (package : IndependentReviewPackage ClauseSourceFaithful
      TableRowSourceFaithful FigureGraphSourceFaithful) :
    (retinoidSourceFigureReviewSeal package).frozenSourceSha256 =
      (IUPACNormativeSource.sha256? .retinoidRecommendations1981).getD "" :=
  rfl

end NormativeFigureReviewSeal
end Retinoid1981
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.NormativeFigureReviewSeal.retinoid_figure_review_adopted_of_package
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.NormativeFigureReviewSeal.retinoid_seal_reviewer_identity_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.NormativeFigureReviewSeal.retinoid_seal_target_count_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.NormativeFigureReviewSeal.retinoid_seal_frozen_digest_exact
