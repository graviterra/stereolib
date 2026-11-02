import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateFinalImageArtifactSlice
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateFinalImageMeaningData
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateFinalImageReview
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192

/-!
# Complete remaining carbohydrate image source meanings

The final 41 numbered molecular figures and five nonchemical glyphs matched the frozen SHA-256
catalog. Every raster was inspected at original resolution against 2-Carb-36--39 and every HTML
context that references a terminal glyph. Molecular meanings bind the existing printed-source
rows to explicit graph summaries; glyphs receive notation roles instead of molecular graphs.

The exact overlay frontier advances from 92/1,991/217 to 92/2,037/171. Consequently, all 424
formerly missing carbohydrate image provisions now have source meanings, and the only remaining
missing non-descriptor provisions are the 171 Appendix-3 structures.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings

open GlobalNonDescriptorSourceMeaningConstructor

def priorRemainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings.remainingImageRows

def rows : List Carbohydrate1996ImageAudit.Provision := priorRemainingImageRows.take 46

def molecularArtifacts : List Carbohydrate1996ImageAudit.ImageArtifact :=
  GlobalNonDescriptorCarbohydrateFinalImageArtifactSlice.molecularArtifacts

def glyphArtifacts : List Carbohydrate1996ImageAudit.ImageArtifact :=
  GlobalNonDescriptorCarbohydrateFinalImageArtifactSlice.glyphArtifacts

def artifacts : List Carbohydrate1996ImageAudit.ImageArtifact := molecularArtifacts ++ glyphArtifacts

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem row_count : rows.length = 46 := by
  simp [rows, priorRemainingImageRows]

@[simp] theorem molecular_artifact_count : molecularArtifacts.length = 41 := by
  simp [molecularArtifacts]

@[simp] theorem glyph_artifact_count : glyphArtifacts.length = 5 := by
  simp [glyphArtifacts]

@[simp] theorem artifact_count : artifacts.length = 46 := by
  simp [artifacts]

@[simp] theorem provision_count : provisions.length = 46 := by
  simp [provisions]

@[simp] theorem molecular_source_pages_exact :
    molecularArtifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 8 ["36.html"] ++ List.replicate 16 ["37.html"] ++
        List.replicate 5 ["38.html"] ++ List.replicate 12 ["39.html"] := by
  exact GlobalNonDescriptorCarbohydrateFinalImageArtifactSlice.molecular_source_pages_exact

@[simp] theorem glyph_source_pages_exact :
    glyphArtifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      [ ["00n01.html", "03n04.html", "05.html", "06n07.html", "11n12.html", "16.html",
          "17.html", "18.html", "22.html", "23.html", "24.html", "31.html", "33.html",
          "37.html", "app.html", "index.html", "ref.html"]
      , ["36.html", "37.html"]
      , ["06n07.html", "36.html", "37.html", "39.html", "er372.html", "errat.html"]
      , ["errat.html"]
      , ["06n07.html"] ] := by
  exact GlobalNonDescriptorCarbohydrateFinalImageArtifactSlice.glyph_source_pages_exact

def sourceMeaningPairs : List (Carbohydrate1996ImageAudit.ImageArtifact × FinalImageMeaning) :=
  List.zip artifacts finalImageMeanings

def allArtifactsHaveSourceMeaning : Bool :=
  decide (sourceMeaningPairs.length = artifacts.length)

@[simp] theorem all_artifacts_have_source_meaning : allArtifactsHaveSourceMeaning = true := by
  simp [allArtifactsHaveSourceMeaning, sourceMeaningPairs]

def visionReviewedMeanings : List VisionReviewedFinalImageMeaning :=
  sourceMeaningPairs.map visionReviewedFinalImageMeaningOfPair

@[simp] theorem vision_reviewed_count : visionReviewedMeanings.length = 46 := by
  simp [visionReviewedMeanings, sourceMeaningPairs]

@[simp] theorem vision_reviewed_complete :
    visionReviewedMeanings.all VisionReviewedFinalImageMeaning.complete = true := by
  exact vision_reviewed_final_pairs_complete sourceMeaningPairs

def reviewedPairs : List (Carbohydrate1996ImageAudit.Provision × FinalImageMeaning) :=
  List.zip rows finalImageMeanings

def pairedProvisions : List IUPACNormativeProvision :=
  reviewedPairs.map fun pair =>
    IUPACNormativeProvision.carbohydrate1996ImageArtifact pair.1

private theorem reviewed_pairs_map_fst : reviewedPairs.map Prod.fst = rows := by
  rw [reviewedPairs, List.map_fst_zip]
  simp

theorem paired_provisions_eq_provisions : pairedProvisions = provisions := by
  calc
    pairedProvisions = (reviewedPairs.map Prod.fst).map
        IUPACNormativeProvision.carbohydrate1996ImageArtifact := by rfl
    _ = rows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact := by
      rw [reviewed_pairs_map_fst]
    _ = provisions := by rfl

def reviewedPairMeaning
    (pair : Carbohydrate1996ImageAudit.Provision × FinalImageMeaning) :
    VisionReviewedFinalImageMeaning :=
  match pair.1 with
  | .imageArtifact artifact => visionReviewedFinalImageMeaningOfPair (artifact, pair.2)

def pairedGraphLevelBatch : GlobalNonDescriptorSourceMeaningBatch pairedProvisions :=
  GlobalNonDescriptorIndexedSourceData.totalMeaningBatch reviewedPairs
    (fun pair => IUPACNormativeProvision.carbohydrate1996ImageArtifact pair.1)
    reviewedPairMeaning (by intro _pair; rfl)

def visionReviewedGraphLevelBatch : GlobalNonDescriptorSourceMeaningBatch provisions := by
  rw [← paired_provisions_eq_provisions]
  exact pairedGraphLevelBatch

@[simp] theorem vision_reviewed_entry_count :
    visionReviewedGraphLevelBatch.entries.length = 46 := by
  rw [visionReviewedGraphLevelBatch.entries_length, provision_count]

/-! ## Exact advance from the prior 92/1,991/217 overlay -/

def remainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  priorRemainingImageRows.drop 46

@[simp] theorem remaining_image_count : remainingImageRows.length = 0 := by
  simp [remainingImageRows, priorRemainingImageRows]

theorem rows_append_remaining_eq_prior :
    rows ++ remainingImageRows = priorRemainingImageRows := by
  exact List.take_append_drop 46 priorRemainingImageRows

def advancedMaterializedProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings.advancedMaterializedProvisions ++
    provisions

def advancedMaterializedBatch :
    GlobalNonDescriptorSourceMeaningBatch advancedMaterializedProvisions :=
  GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings.advancedMaterializedBatch.append
    visionReviewedGraphLevelBatch

@[simp] theorem advanced_materialized_count : advancedMaterializedProvisions.length = 2037 := by
  simp [advancedMaterializedProvisions]

def advancedMissingProvisions : List IUPACNormativeProvision :=
  sourceProvisions .blueBook2013Appendix3 ++
    remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem advanced_missing_count : advancedMissingProvisions.length = 171 := by
  simp [advancedMissingProvisions]

set_option maxRecDepth 8192 in
theorem selected_then_advanced_missing_perm_prior_missing :
    (provisions ++ advancedMissingProvisions).Perm
      GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings.advancedMissingProvisions := by
  have imageEquality := congrArg
    (List.map IUPACNormativeProvision.carbohydrate1996ImageArtifact)
    rows_append_remaining_eq_prior
  let remainingProvisions :=
    remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact
  have swapPrefix :
      (provisions ++ sourceProvisions .blueBook2013Appendix3).Perm
        (sourceProvisions .blueBook2013Appendix3 ++ provisions) :=
    List.perm_append_comm
  have reordered :
      (provisions ++ advancedMissingProvisions).Perm
        (sourceProvisions .blueBook2013Appendix3 ++
          (provisions ++ remainingProvisions)) := by
    change (provisions ++
        (sourceProvisions .blueBook2013Appendix3 ++ remainingProvisions)).Perm
      (sourceProvisions .blueBook2013Appendix3 ++
        (provisions ++ remainingProvisions))
    simpa only [List.append_assoc] using swapPrefix.append_right remainingProvisions
  have selectedThenRemaining :
      provisions ++ remainingProvisions =
        priorRemainingImageRows.map
          IUPACNormativeProvision.carbohydrate1996ImageArtifact := by
    simpa [provisions, remainingProvisions, List.map_append] using imageEquality
  calc
    (provisions ++ advancedMissingProvisions).Perm _ := reordered
    _ = sourceProvisions .blueBook2013Appendix3 ++
        priorRemainingImageRows.map
          IUPACNormativeProvision.carbohydrate1996ImageArtifact := by
      rw [selectedThenRemaining]
    _ = GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings.advancedMissingProvisions := by
      rfl

theorem mem_prior_missing_iff_selected_or_advanced_missing
    (provision : IUPACNormativeProvision) :
    provision ∈
        GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings.advancedMissingProvisions ↔
      provision ∈ provisions ∨ provision ∈ advancedMissingProvisions := by
  simpa only [List.mem_append] using
    (selected_then_advanced_missing_perm_prior_missing.mem_iff).symm

private theorem selected_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ provisions) :
    provision ∈
      GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_left _ member)

private theorem advanced_missing_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ advancedMissingProvisions) :
    provision ∈
      GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_right _ member)

private theorem selected_append_advanced_missing_nodup :
    (provisions ++ advancedMissingProvisions).Nodup :=
  GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings.advanced_missing_nodup.perm
    selected_then_advanced_missing_perm_prior_missing.symm

theorem provisions_nodup : provisions.Nodup :=
  List.Nodup.of_append_left selected_append_advanced_missing_nodup

theorem advanced_missing_nodup : advancedMissingProvisions.Nodup :=
  List.Nodup.of_append_right selected_append_advanced_missing_nodup

private theorem selected_disjoint_advanced_missing :
    provisions.Disjoint advancedMissingProvisions :=
  List.disjoint_of_nodup_append selected_append_advanced_missing_nodup

private theorem prior_materialized_disjoint_selected :
    GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings.advancedMaterializedProvisions.Disjoint
      provisions := by
  rw [List.disjoint_left]
  intro provision materialized selected
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings.advanced_materialized_disjoint_missing)
      materialized (selected_subset_prior_missing selected)

theorem advanced_materialized_nodup : advancedMaterializedProvisions.Nodup := by
  exact
    GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings.advanced_materialized_nodup.append
      provisions_nodup prior_materialized_disjoint_selected

theorem advanced_materialized_disjoint_missing :
    advancedMaterializedProvisions.Disjoint advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision advanced missing
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings.advanced_materialized_disjoint_missing)
        priorMaterialized (advanced_missing_subset_prior_missing missing)
  · exact (List.disjoint_left.mp selected_disjoint_advanced_missing) selected missing

theorem reviewed_disjoint_advanced_materialized :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMaterializedProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed advanced
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings.reviewed_disjoint_advanced_materialized)
        reviewed priorMaterialized
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings.reviewed_disjoint_advanced_missing)
        reviewed (selected_subset_prior_missing selected)

theorem reviewed_disjoint_advanced_missing :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed missing
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings.reviewed_disjoint_advanced_missing)
      reviewed (advanced_missing_subset_prior_missing missing)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem mem_reviewed_or_advanced_materialized_or_missing_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions ∨
      provision ∈ advancedMaterializedProvisions ∨
        provision ∈ advancedMissingProvisions ↔
      provision ∈ globalNonDescriptorProvisions := by
  rw [← GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff]
  rw [mem_prior_missing_iff_selected_or_advanced_missing]
  simp only [advancedMaterializedProvisions, List.mem_append]
  tauto

theorem advanced_live_frontier_counts :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.length = 92 ∧
      advancedMaterializedProvisions.length = 2037 ∧
        advancedMissingProvisions.length = 171 ∧
          92 + 2037 + 171 = 2300 := by
  exact ⟨GlobalNonDescriptorSourceMeaningProgress.reviewed_count,
    advanced_materialized_count, advanced_missing_count, by omega⟩

end GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings.molecular_source_pages_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings.molecular_image_meanings_well_formed
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings.visionReviewedGraphLevelBatch
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings.selected_then_advanced_missing_perm_prior_missing
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff
