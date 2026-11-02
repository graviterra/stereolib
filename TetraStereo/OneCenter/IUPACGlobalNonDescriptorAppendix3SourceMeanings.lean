import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateFinalImageSourceMeanings
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceDataCore
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorAppendix3Review
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192










namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorAppendix3SourceMeanings

open BlueBookAppendix3Audit

def provisions : List IUPACNormativeProvision :=
  sourceProvisions .blueBook2013Appendix3

@[simp] theorem provision_count : provisions.length = 171 := by
  simp [provisions]

def visionReviewedGraphLevelBatch :
    GlobalNonDescriptorSourceMeaningBatch provisions := by
  simpa [provisions, sourceProvisions] using
    GlobalNonDescriptorIndexedSourceData.totalMeaningBatch Provision.all
      IUPACNormativeProvision.appendix3 reviewEntry (by intro _row; rfl)

@[simp] theorem batch_entry_count :
    visionReviewedGraphLevelBatch.entries.length = 171 := by
  rw [visionReviewedGraphLevelBatch.entries_length, provision_count]

private theorem prior_missing_eq_provisions :
    GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings.advancedMissingProvisions =
      provisions := by
  have noImages :
      GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings.remainingImageRows = [] :=
    List.eq_nil_of_length_eq_zero
      GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings.remaining_image_count
  simp [GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings.advancedMissingProvisions,
    noImages, provisions]

def advancedMaterializedProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings.advancedMaterializedProvisions ++
    provisions

def advancedMaterializedBatch :
    GlobalNonDescriptorSourceMeaningBatch advancedMaterializedProvisions :=
  GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings.advancedMaterializedBatch.append
    visionReviewedGraphLevelBatch

def advancedMissingProvisions : List IUPACNormativeProvision := []

@[simp] theorem advanced_materialized_count : advancedMaterializedProvisions.length = 2208 := by
  simp [advancedMaterializedProvisions]

@[simp] theorem advanced_missing_exact : advancedMissingProvisions = [] := rfl

@[simp] theorem advanced_missing_count : advancedMissingProvisions.length = 0 := rfl

theorem provisions_nodup : provisions.Nodup := by
  exact BlueBookAppendix3Audit.Provision.all_nodup.map
    (by intro left right equal; cases equal; rfl)

private theorem prior_materialized_disjoint_provisions :
    GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings.advancedMaterializedProvisions.Disjoint
      provisions := by
  rw [← prior_missing_eq_provisions]
  exact
    GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings.advanced_materialized_disjoint_missing

theorem advanced_materialized_nodup : advancedMaterializedProvisions.Nodup := by
  exact
    GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings.advanced_materialized_nodup.append
      provisions_nodup prior_materialized_disjoint_provisions

theorem advanced_materialized_disjoint_missing :
    advancedMaterializedProvisions.Disjoint advancedMissingProvisions := by
  simp [advancedMissingProvisions]

set_option maxHeartbeats 1000000 in
theorem mem_reviewed_or_advanced_materialized_or_missing_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions ∨
      provision ∈ advancedMaterializedProvisions ∨
        provision ∈ advancedMissingProvisions ↔
      provision ∈ globalNonDescriptorProvisions := by
  rw [←
    GlobalNonDescriptorCarbohydrateFinalImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff]
  rw [prior_missing_eq_provisions]
  simp only [advancedMaterializedProvisions, advancedMissingProvisions, List.mem_append,
    List.not_mem_nil, or_false]

theorem advanced_live_frontier_counts :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.length = 92 ∧
      advancedMaterializedProvisions.length = 2208 ∧
        advancedMissingProvisions.length = 0 ∧
          92 + 2208 + 0 = 2300 := by
  exact ⟨GlobalNonDescriptorSourceMeaningProgress.reviewed_count,
    advanced_materialized_count, advanced_missing_count, by omega⟩

end GlobalNonDescriptorAppendix3SourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorAppendix3SourceMeanings.meanings_rows_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorAppendix3SourceMeanings.origin_counts_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorAppendix3SourceMeanings.review_complete
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorAppendix3SourceMeanings.visionReviewedGraphLevelBatch
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorAppendix3SourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff
