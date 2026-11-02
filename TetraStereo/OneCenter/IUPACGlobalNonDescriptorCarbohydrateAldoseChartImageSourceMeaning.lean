import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings
import TetraStereo.KernelOnly

set_option autoImplicit false
















namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateAldoseChartImageSourceMeaning

open GlobalNonDescriptorSourceMeaningConstructor

def priorRemainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  GlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings.remainingImageRows

def rows : List Carbohydrate1996ImageAudit.Provision := priorRemainingImageRows.take 1

def artifactOf : Carbohydrate1996ImageAudit.Provision →
    Carbohydrate1996ImageAudit.ImageArtifact
  | .imageArtifact artifact => artifact

def artifacts : List Carbohydrate1996ImageAudit.ImageArtifact := rows.map artifactOf

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem row_count : rows.length = 1 := by
  simp [rows, priorRemainingImageRows]

@[simp] theorem artifact_count : artifacts.length = 1 := by simp [artifacts]
@[simp] theorem provision_count : provisions.length = 1 := by simp [provisions]

set_option maxRecDepth 4096 in
@[simp] theorem frozen_artifact_data_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.data =
      [ ⟨"2carb/2C0gif/022.GIF",
          "3dd6271bc78867a0fb6ef3f5514bcfd140ab52190503a6e024ded804afd3646c",
          .numberedOrChartStructure⟩ ] := by
  decide

set_option maxRecDepth 4096 in
@[simp] theorem source_pages_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages = [["02.html"]] := by
  decide

set_option maxRecDepth 4096 in
private theorem rows_nodup : rows.Nodup := by
  decide

theorem provisions_nodup : provisions.Nodup := by
  exact rows_nodup.map (by intro left right equal; cases equal; rfl)

structure AldoseChartEntry where
  trivialName : String
  configurationalPrefix : String
  recommendedAbbreviation? : Option String
  carbonCount : Nat
  hydroxylSides : List Carbohydrate1996ImageAudit.FischerHorizontalSide
  deriving DecidableEq, Repr

def AldoseChartEntry.wellFormed (entry : AldoseChartEntry) : Bool :=
  decide (3 ≤ entry.carbonCount) &&
    entry.hydroxylSides.length = entry.carbonCount - 2 &&
      !entry.trivialName.isEmpty && !entry.configurationalPrefix.isEmpty

def chartEntries : List AldoseChartEntry :=
  [ ⟨"D-glyceraldehyde", "D-glycero", none, 3, [.right]⟩
  , ⟨"D-erythrose", "D-erythro", none, 4, [.right, .right]⟩
  , ⟨"D-threose", "D-threo", none, 4, [.left, .right]⟩
  , ⟨"D-ribose", "D-ribo", some "D-Rib", 5, [.right, .right, .right]⟩
  , ⟨"D-arabinose", "D-arabino", some "D-Ara", 5, [.left, .right, .right]⟩
  , ⟨"D-xylose", "D-xylo", some "D-Xyl", 5, [.right, .left, .right]⟩
  , ⟨"D-lyxose", "D-lyxo", some "D-Lyx", 5, [.left, .left, .right]⟩
  , ⟨"D-allose", "D-allo", some "D-All", 6, [.right, .right, .right, .right]⟩
  , ⟨"D-altrose", "D-altro", some "D-Alt", 6, [.left, .right, .right, .right]⟩
  , ⟨"D-glucose", "D-gluco", some "D-Glc", 6, [.right, .left, .right, .right]⟩
  , ⟨"D-mannose", "D-manno", some "D-Man", 6, [.left, .left, .right, .right]⟩
  , ⟨"D-gulose", "D-gulo", some "D-Gul", 6, [.right, .right, .left, .right]⟩
  , ⟨"D-idose", "D-ido", some "D-Ido", 6, [.left, .right, .left, .right]⟩
  , ⟨"D-galactose", "D-galacto", some "D-Gal", 6, [.right, .left, .left, .right]⟩
  , ⟨"D-talose", "D-talo", some "D-Tal", 6, [.left, .left, .left, .right]⟩ ]

@[simp] theorem chart_entry_count : chartEntries.length = 15 := rfl

@[simp] theorem chart_entries_exact : chartEntries =
    [ ⟨"D-glyceraldehyde", "D-glycero", none, 3, [.right]⟩
    , ⟨"D-erythrose", "D-erythro", none, 4, [.right, .right]⟩
    , ⟨"D-threose", "D-threo", none, 4, [.left, .right]⟩
    , ⟨"D-ribose", "D-ribo", some "D-Rib", 5, [.right, .right, .right]⟩
    , ⟨"D-arabinose", "D-arabino", some "D-Ara", 5, [.left, .right, .right]⟩
    , ⟨"D-xylose", "D-xylo", some "D-Xyl", 5, [.right, .left, .right]⟩
    , ⟨"D-lyxose", "D-lyxo", some "D-Lyx", 5, [.left, .left, .right]⟩
    , ⟨"D-allose", "D-allo", some "D-All", 6, [.right, .right, .right, .right]⟩
    , ⟨"D-altrose", "D-altro", some "D-Alt", 6, [.left, .right, .right, .right]⟩
    , ⟨"D-glucose", "D-gluco", some "D-Glc", 6, [.right, .left, .right, .right]⟩
    , ⟨"D-mannose", "D-manno", some "D-Man", 6, [.left, .left, .right, .right]⟩
    , ⟨"D-gulose", "D-gulo", some "D-Gul", 6, [.right, .right, .left, .right]⟩
    , ⟨"D-idose", "D-ido", some "D-Ido", 6, [.left, .right, .left, .right]⟩
    , ⟨"D-galactose", "D-galacto", some "D-Gal", 6, [.right, .left, .left, .right]⟩
    , ⟨"D-talose", "D-talo", some "D-Tal", 6, [.left, .left, .left, .right]⟩ ] := rfl

def chart_entries_well_formed : Bool := chartEntries.all AldoseChartEntry.wellFormed

structure AldoseChartMeaning where
  entries : List AldoseChartEntry
  onlyDFormsShown : Bool
  lFormsAreMirrorImages : Bool
  acyclicAldehydicForms : Bool
  boldChainsCorrespondToPrefixes : Bool
  deriving DecidableEq, Repr

def chartMeaning : AldoseChartMeaning where
  entries := chartEntries
  onlyDFormsShown := true
  lFormsAreMirrorImages := true
  acyclicAldehydicForms := true
  boldChainsCorrespondToPrefixes := true

structure VisionReviewedChartMeaning where
  artifactData : Carbohydrate1996ImageAudit.ImageArtifactData
  sourcePages : List String
  meaning : AldoseChartMeaning
  reviewerKind : String
  reviewMethod : String
  reviewLimitations : String
  deriving DecidableEq, Repr

def visionReviewedChartMeaning
    (row : Carbohydrate1996ImageAudit.Provision) : VisionReviewedChartMeaning :=
  match row with
  | .imageArtifact artifact =>
      { artifactData := artifact.data
        sourcePages := artifact.sourcePages
        meaning := chartMeaning
        reviewerKind := "visionAutomated"
        reviewMethod := "record-39c6eb30b46527e0c96d55159468322e"
        reviewLimitations := "automated-record-dea0f86743dc0740de4fb10ba17511a4" }

def visionReviewedGraphLevelBatch :
    GlobalNonDescriptorSourceMeaningBatch provisions := by
  simpa [provisions] using
    GlobalNonDescriptorIndexedSourceData.totalMeaningBatch rows
      IUPACNormativeProvision.carbohydrate1996ImageArtifact
      visionReviewedChartMeaning (by intro _row; rfl)

@[simp] theorem vision_reviewed_entry_count :
    visionReviewedGraphLevelBatch.entries.length = 1 := by
  rw [visionReviewedGraphLevelBatch.entries_length, provision_count]

/-! ## Exact advance from the prior 1,618/590 overlay -/

def remainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  priorRemainingImageRows.drop 1

@[simp] theorem remaining_image_count : remainingImageRows.length = 418 := by
  simp [remainingImageRows, priorRemainingImageRows]

theorem rows_append_remaining_eq_prior :
    rows ++ remainingImageRows = priorRemainingImageRows := by
  exact List.take_append_drop 1 priorRemainingImageRows

def advancedMaterializedProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings.advancedMaterializedProvisions ++
    provisions

def advancedMaterializedBatch :
    GlobalNonDescriptorSourceMeaningBatch advancedMaterializedProvisions :=
  GlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings.advancedMaterializedBatch.append
    visionReviewedGraphLevelBatch

@[simp] theorem advanced_materialized_count : advancedMaterializedProvisions.length = 1619 := by
  simp [advancedMaterializedProvisions]

def advancedMissingProvisions : List IUPACNormativeProvision :=
  sourceProvisions .blueBook2013Appendix3 ++
    remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem advanced_missing_count : advancedMissingProvisions.length = 589 := by
  simp [advancedMissingProvisions]

set_option maxRecDepth 8192 in
theorem selected_then_advanced_missing_perm_prior_missing :
    (provisions ++ advancedMissingProvisions).Perm
      GlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings.advancedMissingProvisions := by
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
    _ = GlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings.advancedMissingProvisions := by
      rfl

theorem mem_prior_missing_iff_selected_or_advanced_missing
    (provision : IUPACNormativeProvision) :
    provision ∈
        GlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings.advancedMissingProvisions ↔
      provision ∈ provisions ∨ provision ∈ advancedMissingProvisions := by
  simpa only [List.mem_append] using
    (selected_then_advanced_missing_perm_prior_missing.mem_iff).symm

private theorem selected_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ provisions) :
    provision ∈
      GlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_left _ member)

private theorem advanced_missing_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ advancedMissingProvisions) :
    provision ∈
      GlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_right _ member)

private theorem selected_append_advanced_missing_nodup :
    (provisions ++ advancedMissingProvisions).Nodup :=
  GlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings.advanced_missing_nodup.perm
    selected_then_advanced_missing_perm_prior_missing.symm

theorem advanced_missing_nodup : advancedMissingProvisions.Nodup :=
  List.Nodup.of_append_right selected_append_advanced_missing_nodup

private theorem selected_disjoint_advanced_missing :
    provisions.Disjoint advancedMissingProvisions :=
  List.disjoint_of_nodup_append selected_append_advanced_missing_nodup

private theorem prior_materialized_disjoint_selected :
    GlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings.advancedMaterializedProvisions.Disjoint
      provisions := by
  rw [List.disjoint_left]
  intro provision materialized selected
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings.advanced_materialized_disjoint_missing)
      materialized (selected_subset_prior_missing selected)

theorem advanced_materialized_nodup : advancedMaterializedProvisions.Nodup := by
  exact GlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings.advanced_materialized_nodup.append
    provisions_nodup prior_materialized_disjoint_selected

theorem advanced_materialized_disjoint_missing :
    advancedMaterializedProvisions.Disjoint advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision advanced missing
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings.advanced_materialized_disjoint_missing)
        priorMaterialized (advanced_missing_subset_prior_missing missing)
  · exact (List.disjoint_left.mp selected_disjoint_advanced_missing) selected missing

theorem reviewed_disjoint_advanced_materialized :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMaterializedProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed advanced
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings.reviewed_disjoint_advanced_materialized)
        reviewed priorMaterialized
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings.reviewed_disjoint_advanced_missing)
        reviewed (selected_subset_prior_missing selected)

theorem reviewed_disjoint_advanced_missing :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed missing
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings.reviewed_disjoint_advanced_missing)
      reviewed (advanced_missing_subset_prior_missing missing)

set_option maxRecDepth 8192 in
theorem mem_reviewed_or_advanced_materialized_or_missing_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions ∨
      provision ∈ advancedMaterializedProvisions ∨
        provision ∈ advancedMissingProvisions ↔
      provision ∈ globalNonDescriptorProvisions := by
  rw [← GlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff]
  rw [mem_prior_missing_iff_selected_or_advanced_missing]
  simp only [advancedMaterializedProvisions, List.mem_append]
  tauto

theorem advanced_live_frontier_counts :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.length = 92 ∧
      advancedMaterializedProvisions.length = 1619 ∧
        advancedMissingProvisions.length = 589 ∧
          92 + 1619 + 589 = 2300 := by
  exact ⟨GlobalNonDescriptorSourceMeaningProgress.reviewed_count,
    advanced_materialized_count, advanced_missing_count, by omega⟩

end GlobalNonDescriptorCarbohydrateAldoseChartImageSourceMeaning
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAldoseChartImageSourceMeaning.frozen_artifact_data_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAldoseChartImageSourceMeaning.chart_entries_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAldoseChartImageSourceMeaning.visionReviewedGraphLevelBatch
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAldoseChartImageSourceMeaning.selected_then_advanced_missing_perm_prior_missing
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAldoseChartImageSourceMeaning.mem_reviewed_or_advanced_materialized_or_missing_iff
