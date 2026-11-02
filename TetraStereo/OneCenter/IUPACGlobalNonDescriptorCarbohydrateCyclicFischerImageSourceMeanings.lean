import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings
import TetraStereo.KernelOnly

set_option autoImplicit false













namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateCyclicFischerImageSourceMeanings

open GlobalNonDescriptorSourceMeaningConstructor

def priorRemainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.remainingImageRows

def rows : List Carbohydrate1996ImageAudit.Provision := priorRemainingImageRows.take 5

def artifactOf : Carbohydrate1996ImageAudit.Provision →
    Carbohydrate1996ImageAudit.ImageArtifact
  | .imageArtifact artifact => artifact

def artifacts : List Carbohydrate1996ImageAudit.ImageArtifact := rows.map artifactOf

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem row_count : rows.length = 5 := by
  simp [rows, priorRemainingImageRows]

@[simp] theorem artifact_count : artifacts.length = 5 := by simp [artifacts]
@[simp] theorem provision_count : provisions.length = 5 := by simp [provisions]

set_option maxRecDepth 4096 in
@[simp] theorem frozen_artifact_data_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.data =
      [ ⟨"2carb/2C0gif/052A.GIF", "9130729e4cefe8e7d22e468b15a5a519be84b190bbfc3acdbdfdafe5de5e7c57", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/052B.GIF", "0659fd0e8c28857960ed626d497d6f1fbfd1f185727130984e4eae64a047ba5e", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/052C.GIF", "593bd0246ebc4434a20932722892b71e66ed06d53e246941960bdc5b96584ff3", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/052D.GIF", "1816ab30e171e5385775cb018e1c0a8cabe5d2cb0b96ab95a60c62828843c0a9", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/052E.GIF", "89f0e8c65c8100c10ad4f9dd595e27a99e1d18df1a57ae9a48a6dd4054073e8d", .numberedOrChartStructure⟩ ] := by
  decide

set_option maxRecDepth 4096 in
@[simp] theorem source_pages_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 5 ["05.html"] := by
  decide

set_option maxRecDepth 4096 in
private theorem rows_nodup : rows.Nodup := by
  decide

theorem provisions_nodup : provisions.Nodup := by
  exact rows_nodup.map (by intro left right equal; cases equal; rfl)

inductive RingClass where
  | oxirose | oxetose | furanose | pyranose | septanose
  deriving DecidableEq, Repr

def RingClass.memberCount : RingClass → Nat
  | .oxirose => 3
  | .oxetose => 4
  | .furanose => 5
  | .pyranose => 6
  | .septanose => 7

structure CyclicFischerMeaning where
  publishedName : String
  ringClass : RingClass
  ringSize : Nat
  anomericCarbonLocant : Nat
  ringOxygenSourceLocant : Nat
  anomericHydroxylSide : Carbohydrate1996ImageAudit.FischerHorizontalSide
  parentHydroxylSides : List (Nat × Carbohydrate1996ImageAudit.FischerHorizontalSide)
  deriving DecidableEq, Repr

def dGlucoseHydroxylSides :
    List (Nat × Carbohydrate1996ImageAudit.FischerHorizontalSide) :=
  [(2, .right), (3, .left), (4, .right), (5, .right)]

def ringMeanings : List CyclicFischerMeaning :=
  [ ⟨"alpha-D-glucooxirose", .oxirose, 3, 1, 2, .right, dGlucoseHydroxylSides⟩
  , ⟨"alpha-D-glucooxetose", .oxetose, 4, 1, 3, .right, dGlucoseHydroxylSides⟩
  , ⟨"alpha-D-glucofuranose", .furanose, 5, 1, 4, .right, dGlucoseHydroxylSides⟩
  , ⟨"alpha-D-glucopyranose", .pyranose, 6, 1, 5, .right, dGlucoseHydroxylSides⟩
  , ⟨"alpha-D-glucoseptanose", .septanose, 7, 1, 6, .right, dGlucoseHydroxylSides⟩ ]

@[simp] theorem ring_meanings_exact : ringMeanings =
    [ ⟨"alpha-D-glucooxirose", .oxirose, 3, 1, 2, .right,
        [(2, .right), (3, .left), (4, .right), (5, .right)]⟩
    , ⟨"alpha-D-glucooxetose", .oxetose, 4, 1, 3, .right,
        [(2, .right), (3, .left), (4, .right), (5, .right)]⟩
    , ⟨"alpha-D-glucofuranose", .furanose, 5, 1, 4, .right,
        [(2, .right), (3, .left), (4, .right), (5, .right)]⟩
    , ⟨"alpha-D-glucopyranose", .pyranose, 6, 1, 5, .right,
        [(2, .right), (3, .left), (4, .right), (5, .right)]⟩
    , ⟨"alpha-D-glucoseptanose", .septanose, 7, 1, 6, .right,
        [(2, .right), (3, .left), (4, .right), (5, .right)]⟩ ] := rfl

def CyclicFischerMeaning.wellFormed (meaning : CyclicFischerMeaning) : Bool :=
  meaning.ringClass.memberCount = meaning.ringSize &&
    meaning.anomericCarbonLocant = 1 &&
      meaning.ringSize = meaning.ringOxygenSourceLocant + 1 &&
        1 < meaning.ringOxygenSourceLocant && meaning.ringOxygenSourceLocant ≤ 6 &&
          meaning.anomericHydroxylSide = .right &&
            meaning.parentHydroxylSides = dGlucoseHydroxylSides &&
              !meaning.publishedName.isEmpty

structure CyclicFischerRule where
  longBondConnectsRingOxygenToAnomericCarbon : Bool
  carbonylLocantCitedFirst : Bool
  hydroxyLocantCitedSecond : Bool
  deriving DecidableEq, Repr

def cyclicFischerRule : CyclicFischerRule where
  longBondConnectsRingOxygenToAnomericCarbon := true
  carbonylLocantCitedFirst := true
  hydroxyLocantCitedSecond := true

def sourceMeaning? : String → Option CyclicFischerMeaning
  | "2carb/2C0gif/052A.GIF" => ringMeanings[0]?
  | "2carb/2C0gif/052B.GIF" => ringMeanings[1]?
  | "2carb/2C0gif/052C.GIF" => ringMeanings[2]?
  | "2carb/2C0gif/052D.GIF" => ringMeanings[3]?
  | "2carb/2C0gif/052E.GIF" => ringMeanings[4]?
  | _ => none

def all_ring_meanings_well_formed : Bool :=
  artifacts.all fun artifact =>
    match sourceMeaning? artifact.data.relativePath with
    | some meaning => meaning.wellFormed
    | none => false

structure VisionReviewedImageMeaning where
  artifactData : Carbohydrate1996ImageAudit.ImageArtifactData
  sourcePages : List String
  sourceMeaning : Option CyclicFischerMeaning
  rule : CyclicFischerRule
  reviewerKind : String
  reviewMethod : String
  reviewLimitations : String
  deriving DecidableEq, Repr

def visionReviewedImageMeaning
    (row : Carbohydrate1996ImageAudit.Provision) : VisionReviewedImageMeaning :=
  match row with
  | .imageArtifact artifact =>
      { artifactData := artifact.data
        sourcePages := artifact.sourcePages
        sourceMeaning := sourceMeaning? artifact.data.relativePath
        rule := cyclicFischerRule
        reviewerKind := "visionAutomated"
        reviewMethod := "record-1b7e5add3283e6b5f54eaa2fa5deba2f"
        reviewLimitations := "automated-record-dea0f86743dc0740de4fb10ba17511a4" }

def visionReviewedGraphLevelBatch :
    GlobalNonDescriptorSourceMeaningBatch provisions := by
  simpa [provisions] using
    GlobalNonDescriptorIndexedSourceData.totalMeaningBatch rows
      IUPACNormativeProvision.carbohydrate1996ImageArtifact
      visionReviewedImageMeaning (by intro _row; rfl)

@[simp] theorem vision_reviewed_entry_count :
    visionReviewedGraphLevelBatch.entries.length = 5 := by
  rw [visionReviewedGraphLevelBatch.entries_length, provision_count]

/-! ## Exact advance from the prior 1,631/577 overlay -/

def remainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  priorRemainingImageRows.drop 5

@[simp] theorem remaining_image_count : remainingImageRows.length = 401 := by
  simp [remainingImageRows, priorRemainingImageRows]

theorem rows_append_remaining_eq_prior :
    rows ++ remainingImageRows = priorRemainingImageRows := by
  exact List.take_append_drop 5 priorRemainingImageRows

def advancedMaterializedProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.advancedMaterializedProvisions ++
    provisions

def advancedMaterializedBatch :
    GlobalNonDescriptorSourceMeaningBatch advancedMaterializedProvisions :=
  GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.advancedMaterializedBatch.append
    visionReviewedGraphLevelBatch

@[simp] theorem advanced_materialized_count : advancedMaterializedProvisions.length = 1636 := by
  simp [advancedMaterializedProvisions]

def advancedMissingProvisions : List IUPACNormativeProvision :=
  sourceProvisions .blueBook2013Appendix3 ++
    remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem advanced_missing_count : advancedMissingProvisions.length = 572 := by
  simp [advancedMissingProvisions]

set_option maxRecDepth 8192 in
theorem selected_then_advanced_missing_perm_prior_missing :
    (provisions ++ advancedMissingProvisions).Perm
      GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.advancedMissingProvisions := by
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
    _ = GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.advancedMissingProvisions := by
      rfl

theorem mem_prior_missing_iff_selected_or_advanced_missing
    (provision : IUPACNormativeProvision) :
    provision ∈
        GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.advancedMissingProvisions ↔
      provision ∈ provisions ∨ provision ∈ advancedMissingProvisions := by
  simpa only [List.mem_append] using
    (selected_then_advanced_missing_perm_prior_missing.mem_iff).symm

private theorem selected_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ provisions) :
    provision ∈
      GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_left _ member)

private theorem advanced_missing_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ advancedMissingProvisions) :
    provision ∈
      GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_right _ member)

private theorem selected_append_advanced_missing_nodup :
    (provisions ++ advancedMissingProvisions).Nodup :=
  GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.advanced_missing_nodup.perm
    selected_then_advanced_missing_perm_prior_missing.symm

theorem advanced_missing_nodup : advancedMissingProvisions.Nodup :=
  List.Nodup.of_append_right selected_append_advanced_missing_nodup

private theorem selected_disjoint_advanced_missing :
    provisions.Disjoint advancedMissingProvisions :=
  List.disjoint_of_nodup_append selected_append_advanced_missing_nodup

private theorem prior_materialized_disjoint_selected :
    GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.advancedMaterializedProvisions.Disjoint
      provisions := by
  rw [List.disjoint_left]
  intro provision materialized selected
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.advanced_materialized_disjoint_missing)
      materialized (selected_subset_prior_missing selected)

theorem advanced_materialized_nodup : advancedMaterializedProvisions.Nodup := by
  exact GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.advanced_materialized_nodup.append
    provisions_nodup prior_materialized_disjoint_selected

theorem advanced_materialized_disjoint_missing :
    advancedMaterializedProvisions.Disjoint advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision advanced missing
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.advanced_materialized_disjoint_missing)
        priorMaterialized (advanced_missing_subset_prior_missing missing)
  · exact (List.disjoint_left.mp selected_disjoint_advanced_missing) selected missing

theorem reviewed_disjoint_advanced_materialized :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMaterializedProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed advanced
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.reviewed_disjoint_advanced_materialized)
        reviewed priorMaterialized
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.reviewed_disjoint_advanced_missing)
        reviewed (selected_subset_prior_missing selected)

theorem reviewed_disjoint_advanced_missing :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed missing
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.reviewed_disjoint_advanced_missing)
      reviewed (advanced_missing_subset_prior_missing missing)

set_option maxRecDepth 8192 in
theorem mem_reviewed_or_advanced_materialized_or_missing_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions ∨
      provision ∈ advancedMaterializedProvisions ∨
        provision ∈ advancedMissingProvisions ↔
      provision ∈ globalNonDescriptorProvisions := by
  rw [← GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff]
  rw [mem_prior_missing_iff_selected_or_advanced_missing]
  simp only [advancedMaterializedProvisions, List.mem_append]
  tauto

theorem advanced_live_frontier_counts :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.length = 92 ∧
      advancedMaterializedProvisions.length = 1636 ∧
        advancedMissingProvisions.length = 572 ∧
          92 + 1636 + 572 = 2300 := by
  exact ⟨GlobalNonDescriptorSourceMeaningProgress.reviewed_count,
    advanced_materialized_count, advanced_missing_count, by omega⟩

end GlobalNonDescriptorCarbohydrateCyclicFischerImageSourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateCyclicFischerImageSourceMeanings.frozen_artifact_data_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateCyclicFischerImageSourceMeanings.ring_meanings_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateCyclicFischerImageSourceMeanings.visionReviewedGraphLevelBatch
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateCyclicFischerImageSourceMeanings.selected_then_advanced_missing_perm_prior_missing
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateCyclicFischerImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff
