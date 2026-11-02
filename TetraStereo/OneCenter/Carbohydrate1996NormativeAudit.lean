import TetraStereo.OneCenter.CarbohydrateFoundationStereochemistrySemantics
import TetraStereo.OneCenter.CarbohydrateScopeParentChoiceSemantics
import TetraStereo.OneCenter.CarbohydrateAppendixErrataGlossarySemantics
import TetraStereo.OneCenter.CarbohydrateImageArtifactAudit
import TetraStereo.OneCenter.P10DelegatedAuthorityCorpus
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192













namespace TetraStereo.OneCenter
namespace Carbohydrate1996SourceReview

/-- Disjoint typed union of every prose/table obligation in the frozen 1996 web edition. -/
inductive TextualProvision where
  | scopeParent (provision : Carbohydrate1996ScopeParent.Provision)
  | foundation (provision : Carbohydrate1996Foundation.Provision)
  | namedParent (provision : Carbohydrate1996NamedParents.Provision)
  | derivative (provision : Carbohydrate1996Derivatives.Provision)
  | unsaturatedBranched (provision : Carbohydrate1996UnsaturatedBranched.Provision)
  | alditolAcid (provision : Carbohydrate1996AlditolsAcids.Provision)
  | heteroSubstitutionAnhydride
      (provision : Carbohydrate1996HeteroSubstitutionAnhydride.Provision)
  | acetal (provision : Carbohydrate1996Acetals.Provision)
  | residueIon (provision : Carbohydrate1996ResiduesIons.Provision)
  | glycosideRing (provision : Carbohydrate1996GlycosidesRings.Provision)
  | oligosaccharidePolysaccharide
      (provision : Carbohydrate1996OligosaccharidesPolysaccharides.Provision)
  | appendixErrataGlossary
      (provision : Carbohydrate1996AppendixErrataGlossary.Provision)
  deriving DecidableEq, Repr

namespace TextualProvision

def all : List TextualProvision :=
  Carbohydrate1996ScopeParent.Provision.all.map .scopeParent ++
    Carbohydrate1996Foundation.Provision.all.map .foundation ++
    Carbohydrate1996NamedParents.Provision.all.map .namedParent ++
    Carbohydrate1996Derivatives.Provision.all.map .derivative ++
    Carbohydrate1996UnsaturatedBranched.Provision.all.map .unsaturatedBranched ++
    Carbohydrate1996AlditolsAcids.Provision.all.map .alditolAcid ++
    Carbohydrate1996HeteroSubstitutionAnhydride.Provision.all.map
      .heteroSubstitutionAnhydride ++
    Carbohydrate1996Acetals.Provision.all.map .acetal ++
    Carbohydrate1996ResiduesIons.Provision.all.map .residueIon ++
    Carbohydrate1996GlycosidesRings.Provision.all.map .glycosideRing ++
    Carbohydrate1996OligosaccharidesPolysaccharides.Provision.all.map
      .oligosaccharidePolysaccharide ++
    Carbohydrate1996AppendixErrataGlossary.Provision.all.map .appendixErrataGlossary

@[simp] theorem all_length : all.length = 1274 := by
  simp [all]

end TextualProvision

/-- Exact 43-page HTML inventory reviewed from the byte-frozen recursive snapshot. -/
def reviewedHtmlArtifacts : List String :=
  [ "2carb/index.html"
  , "2carb/cont.html"
  , "2carb/00n01.html"
  , "2carb/02.html"
  , "2carb/03n04.html"
  , "2carb/05.html"
  , "2carb/06n07.html"
  , "2carb/08n09.html"
  , "2carb/10.html"
  , "2carb/11n12.html"
  , "2carb/13.html"
  , "2carb/14n15.html"
  , "2carb/16.html"
  , "2carb/17.html"
  , "2carb/18.html"
  , "2carb/19.html"
  , "2carb/20.html"
  , "2carb/21.html"
  , "2carb/22.html"
  , "2carb/23.html"
  , "2carb/24.html"
  , "2carb/25n26.html"
  , "2carb/27n28.html"
  , "2carb/29n30.html"
  , "2carb/31.html"
  , "2carb/32.html"
  , "2carb/33.html"
  , "2carb/34.html"
  , "2carb/35.html"
  , "2carb/36.html"
  , "2carb/37.html"
  , "2carb/38.html"
  , "2carb/39.html"
  , "2carb/ref.html"
  , "2carb/app.html"
  , "2carb/glo.html"
  , "2carb/errat.html"
  , "2carb/er054.html"
  , "2carb/er222.html"
  , "2carb/er234.html"
  , "2carb/er243.html"
  , "2carb/er336.html"
  , "2carb/er372.html"
  ]

@[simp] theorem reviewed_html_artifact_count : reviewedHtmlArtifacts.length = 43 := by
  decide

theorem reviewed_html_artifacts_nodup : reviewedHtmlArtifacts.Nodup := by
  decide

/-- Screenshot-capture anomalies that received an additional frozen-HTML/DOM text check. -/
def rawHtmlDomCrossChecks : List String :=
  [ "2carb/er222.html", "2carb/er243.html", "2carb/er372.html" ]

@[simp] theorem raw_html_dom_cross_check_count : rawHtmlDomCrossChecks.length = 3 := by
  decide

def currentSourceReviewProvisionEnumerationConfirmed : Bool := true
def currentSourceReviewProseTableCoverageConfirmed : Bool := true
def currentSourceReviewFigureGraphTranscriptionsReviewed : Bool := false

structure SourceReviewEvidence where
  sourceRootUrl : String
  sourceBundleSha256 : String
  reviewedArtifacts : Nat
  reviewedHtmlArtifacts : List String
  reviewedTextualProvisions : List TextualProvision
  imageArtifactCount : Nat
  chemicalImageCount : Nat
  nonchemicalGlyphCount : Nat
  atomLevelGraphTranscriptionCount : Nat
  rawHtmlDomCrossChecks : List String
  sourceRootUrlExact :
    sourceRootUrl = (P10DelegatedAuthorityCorpus.snapshot .carbohydrate1996).rootUrl
  sourceBundleSha256Exact :
    sourceBundleSha256 = (P10DelegatedAuthorityCorpus.snapshot .carbohydrate1996).bundleSha256
  reviewedArtifactCountExact :
    reviewedArtifacts = (P10DelegatedAuthorityCorpus.snapshot .carbohydrate1996).artifactCount
  reviewedHtmlArtifactsExact :
    reviewedHtmlArtifacts = Carbohydrate1996SourceReview.reviewedHtmlArtifacts
  reviewedTextualProvisionsExact : reviewedTextualProvisions = TextualProvision.all
  imageArtifactCountExact : imageArtifactCount = Carbohydrate1996ImageAudit.ImageArtifact.all.length
  chemicalImageCountExact : chemicalImageCount = 425
  nonchemicalGlyphCountExact : nonchemicalGlyphCount = 5
  atomLevelGraphTranscriptionCountExact : atomLevelGraphTranscriptionCount = 0
  rawHtmlDomCrossChecksExact :
    rawHtmlDomCrossChecks = Carbohydrate1996SourceReview.rawHtmlDomCrossChecks
  provisionEnumerationConfirmed : Bool
  proseTableCoverageConfirmed : Bool
  figureGraphTranscriptionsReviewed : Bool
  provisionEnumerationConfirmedExact :
    provisionEnumerationConfirmed = currentSourceReviewProvisionEnumerationConfirmed
  proseTableCoverageConfirmedExact :
    proseTableCoverageConfirmed = currentSourceReviewProseTableCoverageConfirmed
  figureGraphTranscriptionsReviewedExact :
    figureGraphTranscriptionsReviewed = currentSourceReviewFigureGraphTranscriptionsReviewed

def currentSourceReview : SourceReviewEvidence where
  sourceRootUrl := "https://iupac.qmul.ac.uk/2carb/"
  sourceBundleSha256 :=
    "f310af9535a0acf1f03997596188e9031ae2bda6a3366b51b535f387edc33413"
  reviewedArtifacts := 473
  reviewedHtmlArtifacts := reviewedHtmlArtifacts
  reviewedTextualProvisions := TextualProvision.all
  imageArtifactCount := 430
  chemicalImageCount := 425
  nonchemicalGlyphCount := 5
  atomLevelGraphTranscriptionCount := 0
  rawHtmlDomCrossChecks := rawHtmlDomCrossChecks
  sourceRootUrlExact := by rfl
  sourceBundleSha256Exact := by rfl
  reviewedArtifactCountExact := by rfl
  reviewedHtmlArtifactsExact := by rfl
  reviewedTextualProvisionsExact := by rfl
  imageArtifactCountExact := by simp
  chemicalImageCountExact := by rfl
  nonchemicalGlyphCountExact := by rfl
  atomLevelGraphTranscriptionCountExact := by rfl
  rawHtmlDomCrossChecksExact := by rfl
  provisionEnumerationConfirmed := currentSourceReviewProvisionEnumerationConfirmed
  proseTableCoverageConfirmed := currentSourceReviewProseTableCoverageConfirmed
  figureGraphTranscriptionsReviewed := currentSourceReviewFigureGraphTranscriptionsReviewed
  provisionEnumerationConfirmedExact := by rfl
  proseTableCoverageConfirmedExact := by rfl
  figureGraphTranscriptionsReviewedExact := by rfl

@[simp] theorem current_source_review_counts_exact :
    currentSourceReview.reviewedHtmlArtifacts.length = 43 ∧
      currentSourceReview.reviewedTextualProvisions.length = 1274 ∧
        currentSourceReview.reviewedArtifacts = 473 ∧
          currentSourceReview.sourceBundleSha256 =
            "f310af9535a0acf1f03997596188e9031ae2bda6a3366b51b535f387edc33413" := by
  simp [currentSourceReview]

@[simp] theorem current_source_review_gate_state_exact :
    currentSourceReview.provisionEnumerationConfirmed = true ∧
      currentSourceReview.proseTableCoverageConfirmed = true ∧
        currentSourceReview.figureGraphTranscriptionsReviewed = false := by
  decide

end Carbohydrate1996SourceReview
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996SourceReview.TextualProvision.all_length
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996SourceReview.reviewed_html_artifact_count
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996SourceReview.reviewed_html_artifacts_nodup
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996SourceReview.currentSourceReview
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996SourceReview.current_source_review_counts_exact
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996SourceReview.current_source_review_gate_state_exact
