import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateFinalImageSourceMeanings
import TetraStereo.OneCenter.CarbohydrateImageTranscriptionContract
import TetraStereo.OneCenter.IUPACNormativeManifest
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192















namespace TetraStereo.OneCenter
namespace Carbohydrate1996
namespace TechnicalAuditReadiness

open IUPACNormativeProvision

def textualTableProvisions : List IUPACNormativeProvision :=
  carbohydrate1996SemanticsSlice

def imageArtifacts : List Carbohydrate1996ImageAudit.ImageArtifact :=
  Carbohydrate1996ImageAudit.ImageArtifact.all

def imageArtifactProvisions : List IUPACNormativeProvision :=
  carbohydrate1996ImageArtifactSourceSlice

def sourceProvisions : List IUPACNormativeProvision :=
  IUPACNormativeProvision.sourceProvisions .carbohydrateRecommendations1996

@[simp] theorem textual_table_provision_count :
    textualTableProvisions.length = 1274 := by
  simp [textualTableProvisions, carbohydrate1996SemanticsSlice]

@[simp] theorem image_artifact_count : imageArtifacts.length = 430 := by
  simp [imageArtifacts]

@[simp] theorem source_provision_count : sourceProvisions.length = 1704 := by
  simp [sourceProvisions]

@[simp] theorem source_partition_exact :
    textualTableProvisions ++ imageArtifactProvisions = sourceProvisions := by
  simp [textualTableProvisions, imageArtifactProvisions, sourceProvisions]

def chemicalImageArtifacts : List Carbohydrate1996ImageAudit.ImageArtifact :=
  imageArtifacts.filter fun artifact => artifact.data.kind.requiresMolecularGraph

def nonchemicalGlyphArtifacts : List Carbohydrate1996ImageAudit.ImageArtifact :=
  imageArtifacts.filter fun artifact => !artifact.data.kind.requiresMolecularGraph

@[simp] theorem image_kind_partition_counts :
    chemicalImageArtifacts.length = 425 ∧
      nonchemicalGlyphArtifacts.length = 5 := by
  simp [chemicalImageArtifacts, nonchemicalGlyphArtifacts, imageArtifacts]

/-! ## Graph-level versus atom-level completion -/

def graphLevelRemainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings.remainingImageRows

@[simp] theorem graph_level_remaining_images_exact :
    graphLevelRemainingImageRows = [] := by
  apply List.eq_nil_of_length_eq_zero
  simp [graphLevelRemainingImageRows]

def currentAtomLevelTranscriptions :
    List Carbohydrate1996ImageTranscription.AtomLevelImageTranscription :=
  Carbohydrate1996ImageTranscription.currentAtomLevelTranscriptions

@[simp] theorem current_atom_level_transcription_count :
    currentAtomLevelTranscriptions.length = 0 := by
  rfl

theorem current_atom_level_coverage_incomplete :
    ¬Carbohydrate1996ImageTranscription.ExactArtifactCoverage
      currentAtomLevelTranscriptions := by
  simpa [currentAtomLevelTranscriptions] using
    Carbohydrate1996ImageTranscription.current_atom_level_image_coverage_is_incomplete

/-! ## One proof-carrying machine dossier -/

structure TechnicalEvidence where
  sourceProvisionCount : Nat
  textualTableProvisionCount : Nat
  imageArtifactCount : Nat
  chemicalImageCount : Nat
  nonchemicalGlyphCount : Nat
  graphLevelRemainingImageCount : Nat
  atomLevelTranscriptionCount : Nat
  sourceProvisionCountExact : sourceProvisionCount = sourceProvisions.length
  textualTableProvisionCountExact : textualTableProvisionCount = textualTableProvisions.length
  imageArtifactCountExact : imageArtifactCount = imageArtifacts.length
  chemicalImageCountExact : chemicalImageCount = chemicalImageArtifacts.length
  nonchemicalGlyphCountExact : nonchemicalGlyphCount = nonchemicalGlyphArtifacts.length
  graphLevelRemainingImageCountExact :
    graphLevelRemainingImageCount = graphLevelRemainingImageRows.length
  atomLevelTranscriptionCountExact :
    atomLevelTranscriptionCount = currentAtomLevelTranscriptions.length
  sourcePartitionExact : textualTableProvisions ++ imageArtifactProvisions = sourceProvisions
  graphLevelImagesExhausted : graphLevelRemainingImageRows = []
  atomLevelCoverageIncomplete :
    ¬Carbohydrate1996ImageTranscription.ExactArtifactCoverage
      currentAtomLevelTranscriptions

def currentTechnicalEvidence : TechnicalEvidence where
  sourceProvisionCount := 1704
  textualTableProvisionCount := 1274
  imageArtifactCount := 430
  chemicalImageCount := 425
  nonchemicalGlyphCount := 5
  graphLevelRemainingImageCount := 0
  atomLevelTranscriptionCount := 0
  sourceProvisionCountExact := by simp
  textualTableProvisionCountExact := by simp
  imageArtifactCountExact := by simp
  chemicalImageCountExact := by simp
  nonchemicalGlyphCountExact := by simp
  graphLevelRemainingImageCountExact := by simp
  atomLevelTranscriptionCountExact := by simp
  sourcePartitionExact := source_partition_exact
  graphLevelImagesExhausted := graph_level_remaining_images_exact
  atomLevelCoverageIncomplete := current_atom_level_coverage_incomplete

@[simp] theorem current_technical_evidence_counts_exact :
    currentTechnicalEvidence.sourceProvisionCount = 1704 ∧
      currentTechnicalEvidence.textualTableProvisionCount = 1274 ∧
        currentTechnicalEvidence.imageArtifactCount = 430 ∧
          currentTechnicalEvidence.chemicalImageCount = 425 ∧
            currentTechnicalEvidence.nonchemicalGlyphCount = 5 ∧
              currentTechnicalEvidence.graphLevelRemainingImageCount = 0 ∧
                currentTechnicalEvidence.atomLevelTranscriptionCount = 0 := by
  decide



def currentOpenCarbohydrateReviewRequirements :
    List IUPACNormativeSource.ProvisionAuditRequirement :=
  IUPACNormativeSource.currentOpenProvisionAuditRequirements
    .carbohydrateRecommendations1996

@[simp] theorem current_open_carbohydrate_review_requirements_exact :
    currentOpenCarbohydrateReviewRequirements =
      [ .figureGraphTranscriptionsReviewed ] := by
  decide

@[simp] theorem current_enumeration_confirmed :
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .carbohydrateRecommendations1996).provisionEnumerationConfirmed = true := by
  rfl

@[simp] theorem current_prose_table_coverage_confirmed :
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .carbohydrateRecommendations1996).proseTableCoverageConfirmed = true := by
  rfl

/-- Repository issuance state.  Graph-level materialization cannot flip this flag. -/
def currentIndependentReviewPackageIssued : Bool := false

@[simp] theorem current_independent_review_package_not_issued :
    currentIndependentReviewPackageIssued = false := by
  rfl

theorem current_carbohydrate_audit_remains_incomplete :
    ¬IUPACNormativeSource.ProvisionAuditComplete
      .carbohydrateRecommendations1996 := by
  simp [IUPACNormativeSource.ProvisionAuditComplete,
    IUPACNormativeSource.currentProvisionAuditChecklist,
    IUPACNormativeSource.ProvisionAuditChecklist.Complete,
    Carbohydrate1996SourceReview.currentSourceReviewProvisionEnumerationConfirmed,
    Carbohydrate1996SourceReview.currentSourceReviewProseTableCoverageConfirmed,
    Carbohydrate1996SourceReview.currentSourceReviewFigureGraphTranscriptionsReviewed]

end TechnicalAuditReadiness
end Carbohydrate1996
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996.TechnicalAuditReadiness.source_partition_exact
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996.TechnicalAuditReadiness.graph_level_remaining_images_exact
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996.TechnicalAuditReadiness.current_atom_level_coverage_incomplete
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996.TechnicalAuditReadiness.currentTechnicalEvidence
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996.TechnicalAuditReadiness.current_open_carbohydrate_review_requirements_exact
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996.TechnicalAuditReadiness.current_prose_table_coverage_confirmed
assert_kernel_only
  TetraStereo.OneCenter.Carbohydrate1996.TechnicalAuditReadiness.current_carbohydrate_audit_remains_incomplete
