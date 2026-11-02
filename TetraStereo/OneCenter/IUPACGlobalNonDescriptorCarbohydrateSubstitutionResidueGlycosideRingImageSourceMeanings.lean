import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateAlditolAcidImageSourceMeanings
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateLateImageArtifactSlice
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateLateImageReview
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateSubstitutionAcetalImageMeaningData
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateResidueIonImageMeaningData
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateGlycosideRingImageMeaningData
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192














namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings

open GlobalNonDescriptorSourceMeaningConstructor
open CarbohydrateLateImageMeaningData

def priorRemainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  GlobalNonDescriptorCarbohydrateAlditolAcidImageSourceMeanings.remainingImageRows

def rows : List Carbohydrate1996ImageAudit.Provision := priorRemainingImageRows.take 150

def artifactOf : Carbohydrate1996ImageAudit.Provision →
    Carbohydrate1996ImageAudit.ImageArtifact
  | .imageArtifact artifact => artifact

def artifacts : List Carbohydrate1996ImageAudit.ImageArtifact :=
  GlobalNonDescriptorCarbohydrateLateImageArtifactSlice.artifacts

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem row_count : rows.length = 150 := by simp [rows, priorRemainingImageRows]
@[simp] theorem artifact_count : artifacts.length = 150 := by simp [artifacts]
@[simp] theorem provision_count : provisions.length = 150 := by simp [provisions]

@[simp] theorem source_pages_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 19 ["24.html"] ++ List.replicate 16 ["25n26.html"] ++
        List.replicate 10 ["27n28.html"] ++ List.replicate 11 ["29n30.html"] ++
          List.replicate 20 ["31.html"] ++ List.replicate 16 ["32.html"] ++
            List.replicate 34 ["33.html"] ++ List.replicate 9 ["34.html"] ++
              List.replicate 15 ["35.html"] := by
  exact GlobalNonDescriptorCarbohydrateLateImageArtifactSlice.source_pages_exact

def allImageMeanings : List ImageMeaning :=
  substitutionAnhydrideImageMeanings ++ acetalImageMeanings ++
    residueIonImageMeanings ++ glycosideRingImageMeanings

@[simp] theorem all_image_meaning_count : allImageMeanings.length = 150 := by
  simp [allImageMeanings]

@[simp] theorem all_image_meanings_well_formed :
    allImageMeanings.all ImageMeaning.wellFormed = true := by
  simp only [allImageMeanings, List.all_append]
  rw [substitution_anhydride_meanings_well_formed, acetal_meanings_well_formed,
    residue_ion_meanings_well_formed, glycoside_ring_meanings_well_formed]
  decide

def sourceMeaningPairs : List (Carbohydrate1996ImageAudit.ImageArtifact × ImageMeaning) :=
  List.zip artifacts allImageMeanings

def allArtifactsHaveSourceMeaning : Bool :=
  decide (sourceMeaningPairs.length = artifacts.length)

@[simp] theorem all_artifacts_have_source_meaning : allArtifactsHaveSourceMeaning = true := by
  simp [allArtifactsHaveSourceMeaning, sourceMeaningPairs]

def visionReviewedMeanings : List VisionReviewedImageMeaning :=
  sourceMeaningPairs.map visionReviewedImageMeaningOfPair

@[simp] theorem vision_reviewed_count : visionReviewedMeanings.length = 150 := by
  simp [visionReviewedMeanings, sourceMeaningPairs]

@[simp] theorem vision_reviewed_complete :
    visionReviewedMeanings.all VisionReviewedImageMeaning.complete = true := by
  exact vision_reviewed_pairs_complete sourceMeaningPairs

def reviewedPairs : List (Carbohydrate1996ImageAudit.Provision × ImageMeaning) :=
  List.zip rows allImageMeanings

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
    (pair : Carbohydrate1996ImageAudit.Provision × ImageMeaning) :
    VisionReviewedImageMeaning :=
  match pair.1 with
  | .imageArtifact artifact => visionReviewedImageMeaningOfPair (artifact, pair.2)

def pairedGraphLevelBatch : GlobalNonDescriptorSourceMeaningBatch pairedProvisions :=
  GlobalNonDescriptorIndexedSourceData.totalMeaningBatch reviewedPairs
    (fun pair => IUPACNormativeProvision.carbohydrate1996ImageArtifact pair.1)
    reviewedPairMeaning (by intro _pair; rfl)

def visionReviewedGraphLevelBatch : GlobalNonDescriptorSourceMeaningBatch provisions := by
  rw [← paired_provisions_eq_provisions]
  exact pairedGraphLevelBatch

@[simp] theorem vision_reviewed_entry_count :
    visionReviewedGraphLevelBatch.entries.length = 150 := by
  rw [visionReviewedGraphLevelBatch.entries_length, provision_count]

/-! ## Exact advance from the prior 1,841/367 overlay -/

def remainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  priorRemainingImageRows.drop 150

@[simp] theorem remaining_image_count : remainingImageRows.length = 46 := by
  simp [remainingImageRows, priorRemainingImageRows]

theorem rows_append_remaining_eq_prior :
    rows ++ remainingImageRows = priorRemainingImageRows := by
  exact List.take_append_drop 150 priorRemainingImageRows

def advancedMaterializedProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorCarbohydrateAlditolAcidImageSourceMeanings.advancedMaterializedProvisions ++
    provisions

def advancedMaterializedBatch :
    GlobalNonDescriptorSourceMeaningBatch advancedMaterializedProvisions :=
  GlobalNonDescriptorCarbohydrateAlditolAcidImageSourceMeanings.advancedMaterializedBatch.append
    visionReviewedGraphLevelBatch

@[simp] theorem advanced_materialized_count : advancedMaterializedProvisions.length = 1991 := by
  simp [advancedMaterializedProvisions]

def advancedMissingProvisions : List IUPACNormativeProvision :=
  sourceProvisions .blueBook2013Appendix3 ++
    remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem advanced_missing_count : advancedMissingProvisions.length = 217 := by
  simp [advancedMissingProvisions]

set_option maxRecDepth 8192 in
theorem selected_then_advanced_missing_perm_prior_missing :
    (provisions ++ advancedMissingProvisions).Perm
      GlobalNonDescriptorCarbohydrateAlditolAcidImageSourceMeanings.advancedMissingProvisions := by
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
    _ = GlobalNonDescriptorCarbohydrateAlditolAcidImageSourceMeanings.advancedMissingProvisions := by
      rfl

theorem mem_prior_missing_iff_selected_or_advanced_missing
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorCarbohydrateAlditolAcidImageSourceMeanings.advancedMissingProvisions ↔
      provision ∈ provisions ∨ provision ∈ advancedMissingProvisions := by
  simpa only [List.mem_append] using
    (selected_then_advanced_missing_perm_prior_missing.mem_iff).symm

private theorem selected_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ provisions) :
    provision ∈ GlobalNonDescriptorCarbohydrateAlditolAcidImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_left _ member)

private theorem advanced_missing_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ advancedMissingProvisions) :
    provision ∈ GlobalNonDescriptorCarbohydrateAlditolAcidImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_right _ member)

private theorem selected_append_advanced_missing_nodup :
    (provisions ++ advancedMissingProvisions).Nodup :=
  GlobalNonDescriptorCarbohydrateAlditolAcidImageSourceMeanings.advanced_missing_nodup.perm
    selected_then_advanced_missing_perm_prior_missing.symm

theorem provisions_nodup : provisions.Nodup :=
  List.Nodup.of_append_left selected_append_advanced_missing_nodup

theorem advanced_missing_nodup : advancedMissingProvisions.Nodup :=
  List.Nodup.of_append_right selected_append_advanced_missing_nodup

private theorem selected_disjoint_advanced_missing :
    provisions.Disjoint advancedMissingProvisions :=
  List.disjoint_of_nodup_append selected_append_advanced_missing_nodup

private theorem prior_materialized_disjoint_selected :
    GlobalNonDescriptorCarbohydrateAlditolAcidImageSourceMeanings.advancedMaterializedProvisions.Disjoint
      provisions := by
  rw [List.disjoint_left]
  intro provision materialized selected
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateAlditolAcidImageSourceMeanings.advanced_materialized_disjoint_missing)
      materialized (selected_subset_prior_missing selected)

theorem advanced_materialized_nodup : advancedMaterializedProvisions.Nodup := by
  exact GlobalNonDescriptorCarbohydrateAlditolAcidImageSourceMeanings.advanced_materialized_nodup.append
    provisions_nodup prior_materialized_disjoint_selected

theorem advanced_materialized_disjoint_missing :
    advancedMaterializedProvisions.Disjoint advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision advanced missing
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateAlditolAcidImageSourceMeanings.advanced_materialized_disjoint_missing)
        priorMaterialized (advanced_missing_subset_prior_missing missing)
  · exact (List.disjoint_left.mp selected_disjoint_advanced_missing) selected missing

theorem reviewed_disjoint_advanced_materialized :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMaterializedProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed advanced
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateAlditolAcidImageSourceMeanings.reviewed_disjoint_advanced_materialized)
        reviewed priorMaterialized
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateAlditolAcidImageSourceMeanings.reviewed_disjoint_advanced_missing)
        reviewed (selected_subset_prior_missing selected)

theorem reviewed_disjoint_advanced_missing :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed missing
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateAlditolAcidImageSourceMeanings.reviewed_disjoint_advanced_missing)
      reviewed (advanced_missing_subset_prior_missing missing)

set_option maxRecDepth 8192 in
theorem mem_reviewed_or_advanced_materialized_or_missing_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions ∨
      provision ∈ advancedMaterializedProvisions ∨
        provision ∈ advancedMissingProvisions ↔
      provision ∈ globalNonDescriptorProvisions := by
  rw [← GlobalNonDescriptorCarbohydrateAlditolAcidImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff]
  rw [mem_prior_missing_iff_selected_or_advanced_missing]
  simp only [advancedMaterializedProvisions, List.mem_append]
  tauto

theorem advanced_live_frontier_counts :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.length = 92 ∧
      advancedMaterializedProvisions.length = 1991 ∧
        advancedMissingProvisions.length = 217 ∧
          92 + 1991 + 217 = 2300 := by
  exact ⟨GlobalNonDescriptorSourceMeaningProgress.reviewed_count,
    advanced_materialized_count, advanced_missing_count, by omega⟩

end GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings.source_pages_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings.all_image_meanings_well_formed
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings.visionReviewedGraphLevelBatch
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings.selected_then_advanced_missing_perm_prior_missing
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateSubstitutionResidueGlycosideRingImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff
