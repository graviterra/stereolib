import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateFischerConventionImageSourceMeanings
import TetraStereo.KernelOnly

set_option autoImplicit false














namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings

open GlobalNonDescriptorSourceMeaningConstructor

def priorRemainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  GlobalNonDescriptorCarbohydrateFischerConventionImageSourceMeanings.remainingImageRows

def rows : List Carbohydrate1996ImageAudit.Provision := priorRemainingImageRows.take 10

def artifactOf : Carbohydrate1996ImageAudit.Provision →
    Carbohydrate1996ImageAudit.ImageArtifact
  | .imageArtifact artifact => artifact

def artifacts : List Carbohydrate1996ImageAudit.ImageArtifact := rows.map artifactOf

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem row_count : rows.length = 10 := by
  simp [rows, priorRemainingImageRows]

@[simp] theorem artifact_count : artifacts.length = 10 := by simp [artifacts]
@[simp] theorem provision_count : provisions.length = 10 := by simp [provisions]

set_option maxRecDepth 4096 in
@[simp] theorem frozen_artifact_data_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.data =
      [ ⟨"2carb/2C0gif/041A.GIF", "0b7d23ec4b023bc59b17c8df254b22467b3f48d87522b4e995ceb90d2de880b0", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/041B.GIF", "2fd58da40e729e5aa18c3d62e237573c0b6c343d7a12c09a8850f2e3b57f729a", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/042A.GIF", "6a4b91690b40521dc8d33bc0d2be45f63c05a62a47de7d640a35c82be9fd25bc", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/042B.GIF", "fcb1ed7600a9d40744f1718b5bd2af2d19db8efd922afb28fb83723686e8a7b4", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/042C.GIF", "36cb6b6bc76c2ca772755b132c08d4a249f00899d94743557b709abf9d3e89e6", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/042D.GIF", "9186bd2fa5d74d836155fef8b4d1792de1854712fba6265d6ffe36c441061443", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/042E.GIF", "26b3fc274810528b93d41e0cec9fa82f63c5c8575a7703e2670763ac88f114c8", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/042F.GIF", "3934f78c6f3a86cac18db1bcc2c806d9fa0d08b5bd083c414ff46eb482e0330e", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/042G.GIF", "3682f2251bfbe7c3f5475d14a8ddee7cc26d94e5154797796432e719cce0fb63", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/042H.GIF", "e3c17f69ab161127c284b445851084c8b926a4e30af2de37befa214860de9f8a", .numberedOrChartStructure⟩ ] := by
  decide

set_option maxRecDepth 4096 in
@[simp] theorem source_pages_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 10 ["03n04.html"] := by
  decide

set_option maxRecDepth 4096 in
private theorem rows_nodup : rows.Nodup := by
  decide

theorem provisions_nodup : provisions.Nodup := by
  exact rows_nodup.map (by intro left right equal; cases equal; rfl)

inductive ConfigurationalSeries where
  | D | L
  deriving DecidableEq, Repr

inductive ExampleRole where
  | absoluteGlyceraldehydeReference
  | configurationalAtomExample
  deriving DecidableEq, Repr

structure ConfigurationalExampleMeaning where
  publishedName : String
  role : ExampleRole
  series : ConfigurationalSeries
  carbonCount : Nat
  carbonylLocant : Nat
  hydroxylSides : List (Nat × Carbohydrate1996ImageAudit.FischerHorizontalSide)
  configurationalAtomLocant : Nat
  deriving DecidableEq, Repr

def exampleMeanings : List ConfigurationalExampleMeaning :=
  [ ⟨"D-glyceraldehyde", .absoluteGlyceraldehydeReference, .D, 3, 1,
      [(2, .right)], 2⟩
  , ⟨"L-glyceraldehyde", .absoluteGlyceraldehydeReference, .L, 3, 1,
      [(2, .left)], 2⟩
  , ⟨"D-glucose", .configurationalAtomExample, .D, 6, 1,
      [(2, .right), (3, .left), (4, .right), (5, .right)], 5⟩
  , ⟨"D-xylose", .configurationalAtomExample, .D, 5, 1,
      [(2, .right), (3, .left), (4, .right)], 4⟩
  , ⟨"D-arabino-hex-2-ulose (D-fructose)", .configurationalAtomExample, .D, 6, 2,
      [(3, .left), (4, .right), (5, .right)], 5⟩
  , ⟨"D-glycero-L-gulo-heptose", .configurationalAtomExample, .D, 7, 1,
      [(2, .left), (3, .right), (4, .right), (5, .left), (6, .right)], 6⟩
  , ⟨"L-glucose", .configurationalAtomExample, .L, 6, 1,
      [(2, .left), (3, .right), (4, .left), (5, .left)], 5⟩
  , ⟨"L-arabinose", .configurationalAtomExample, .L, 5, 1,
      [(2, .right), (3, .left), (4, .left)], 4⟩
  , ⟨"L-xylo-hex-2-ulose (L-sorbose)", .configurationalAtomExample, .L, 6, 2,
      [(3, .right), (4, .left), (5, .left)], 5⟩
  , ⟨"L-glycero-D-manno-heptose", .configurationalAtomExample, .L, 7, 1,
      [(2, .right), (3, .left), (4, .left), (5, .right), (6, .left)], 6⟩ ]

@[simp] theorem example_meanings_exact : exampleMeanings =
    [ ⟨"D-glyceraldehyde", .absoluteGlyceraldehydeReference, .D, 3, 1,
        [(2, .right)], 2⟩
    , ⟨"L-glyceraldehyde", .absoluteGlyceraldehydeReference, .L, 3, 1,
        [(2, .left)], 2⟩
    , ⟨"D-glucose", .configurationalAtomExample, .D, 6, 1,
        [(2, .right), (3, .left), (4, .right), (5, .right)], 5⟩
    , ⟨"D-xylose", .configurationalAtomExample, .D, 5, 1,
        [(2, .right), (3, .left), (4, .right)], 4⟩
    , ⟨"D-arabino-hex-2-ulose (D-fructose)", .configurationalAtomExample, .D, 6, 2,
        [(3, .left), (4, .right), (5, .right)], 5⟩
    , ⟨"D-glycero-L-gulo-heptose", .configurationalAtomExample, .D, 7, 1,
        [(2, .left), (3, .right), (4, .right), (5, .left), (6, .right)], 6⟩
    , ⟨"L-glucose", .configurationalAtomExample, .L, 6, 1,
        [(2, .left), (3, .right), (4, .left), (5, .left)], 5⟩
    , ⟨"L-arabinose", .configurationalAtomExample, .L, 5, 1,
        [(2, .right), (3, .left), (4, .left)], 4⟩
    , ⟨"L-xylo-hex-2-ulose (L-sorbose)", .configurationalAtomExample, .L, 6, 2,
        [(3, .right), (4, .left), (5, .left)], 5⟩
    , ⟨"L-glycero-D-manno-heptose", .configurationalAtomExample, .L, 7, 1,
        [(2, .right), (3, .left), (4, .left), (5, .right), (6, .left)], 6⟩ ] := rfl

def ConfigurationalExampleMeaning.wellFormedAndSeriesConsistent
    (meaning : ConfigurationalExampleMeaning) : Bool :=
  decide (3 ≤ meaning.carbonCount) &&
    0 < meaning.carbonylLocant && meaning.carbonylLocant < meaning.carbonCount &&
      !meaning.hydroxylSides.isEmpty &&
        decide (meaning.hydroxylSides.map Prod.fst).Nodup &&
          meaning.hydroxylSides.all (fun center =>
            meaning.carbonylLocant < center.1 && center.1 < meaning.carbonCount) &&
            meaning.hydroxylSides.getLast?.map Prod.fst = some meaning.configurationalAtomLocant &&
              (match meaning.hydroxylSides.getLast?.map Prod.snd, meaning.series with
              | some .right, .D => true
              | some .left, .L => true
              | _, _ => false) &&
                !meaning.publishedName.isEmpty

structure ConfigurationalSeriesRule where
  assignmentUsesHighestNumberedChiralCenter : Bool
  rightHydroxylMeansD : Bool
  leftHydroxylMeansL : Bool
  glyceraldehydeProjectionsAreAbsoluteConfigurations : Bool
  deriving DecidableEq, Repr

def seriesRule : ConfigurationalSeriesRule where
  assignmentUsesHighestNumberedChiralCenter := true
  rightHydroxylMeansD := true
  leftHydroxylMeansL := true
  glyceraldehydeProjectionsAreAbsoluteConfigurations := true

def sourceMeaning? : String → Option ConfigurationalExampleMeaning
  | "2carb/2C0gif/041A.GIF" => exampleMeanings[0]?
  | "2carb/2C0gif/041B.GIF" => exampleMeanings[1]?
  | "2carb/2C0gif/042A.GIF" => exampleMeanings[2]?
  | "2carb/2C0gif/042B.GIF" => exampleMeanings[3]?
  | "2carb/2C0gif/042C.GIF" => exampleMeanings[4]?
  | "2carb/2C0gif/042D.GIF" => exampleMeanings[5]?
  | "2carb/2C0gif/042E.GIF" => exampleMeanings[6]?
  | "2carb/2C0gif/042F.GIF" => exampleMeanings[7]?
  | "2carb/2C0gif/042G.GIF" => exampleMeanings[8]?
  | "2carb/2C0gif/042H.GIF" => exampleMeanings[9]?
  | _ => none

def all_examples_well_formed_and_series_consistent : Bool :=
  artifacts.all fun artifact =>
    match sourceMeaning? artifact.data.relativePath with
    | some meaning => meaning.wellFormedAndSeriesConsistent
    | none => false

structure VisionReviewedImageMeaning where
  artifactData : Carbohydrate1996ImageAudit.ImageArtifactData
  sourcePages : List String
  sourceMeaning : Option ConfigurationalExampleMeaning
  rule : ConfigurationalSeriesRule
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
        rule := seriesRule
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
    visionReviewedGraphLevelBatch.entries.length = 10 := by
  rw [visionReviewedGraphLevelBatch.entries_length, provision_count]

/-! ## Exact advance from the prior 1,621/587 overlay -/

def remainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  priorRemainingImageRows.drop 10

@[simp] theorem remaining_image_count : remainingImageRows.length = 406 := by
  simp [remainingImageRows, priorRemainingImageRows]

theorem rows_append_remaining_eq_prior :
    rows ++ remainingImageRows = priorRemainingImageRows := by
  exact List.take_append_drop 10 priorRemainingImageRows

def advancedMaterializedProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorCarbohydrateFischerConventionImageSourceMeanings.advancedMaterializedProvisions ++
    provisions

def advancedMaterializedBatch :
    GlobalNonDescriptorSourceMeaningBatch advancedMaterializedProvisions :=
  GlobalNonDescriptorCarbohydrateFischerConventionImageSourceMeanings.advancedMaterializedBatch.append
    visionReviewedGraphLevelBatch

@[simp] theorem advanced_materialized_count : advancedMaterializedProvisions.length = 1631 := by
  simp [advancedMaterializedProvisions]

def advancedMissingProvisions : List IUPACNormativeProvision :=
  sourceProvisions .blueBook2013Appendix3 ++
    remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem advanced_missing_count : advancedMissingProvisions.length = 577 := by
  simp [advancedMissingProvisions]

set_option maxRecDepth 8192 in
theorem selected_then_advanced_missing_perm_prior_missing :
    (provisions ++ advancedMissingProvisions).Perm
      GlobalNonDescriptorCarbohydrateFischerConventionImageSourceMeanings.advancedMissingProvisions := by
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
    _ = GlobalNonDescriptorCarbohydrateFischerConventionImageSourceMeanings.advancedMissingProvisions := by
      rfl

theorem mem_prior_missing_iff_selected_or_advanced_missing
    (provision : IUPACNormativeProvision) :
    provision ∈
        GlobalNonDescriptorCarbohydrateFischerConventionImageSourceMeanings.advancedMissingProvisions ↔
      provision ∈ provisions ∨ provision ∈ advancedMissingProvisions := by
  simpa only [List.mem_append] using
    (selected_then_advanced_missing_perm_prior_missing.mem_iff).symm

private theorem selected_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ provisions) :
    provision ∈
      GlobalNonDescriptorCarbohydrateFischerConventionImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_left _ member)

private theorem advanced_missing_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ advancedMissingProvisions) :
    provision ∈
      GlobalNonDescriptorCarbohydrateFischerConventionImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_right _ member)

private theorem selected_append_advanced_missing_nodup :
    (provisions ++ advancedMissingProvisions).Nodup :=
  GlobalNonDescriptorCarbohydrateFischerConventionImageSourceMeanings.advanced_missing_nodup.perm
    selected_then_advanced_missing_perm_prior_missing.symm

theorem advanced_missing_nodup : advancedMissingProvisions.Nodup :=
  List.Nodup.of_append_right selected_append_advanced_missing_nodup

private theorem selected_disjoint_advanced_missing :
    provisions.Disjoint advancedMissingProvisions :=
  List.disjoint_of_nodup_append selected_append_advanced_missing_nodup

private theorem prior_materialized_disjoint_selected :
    GlobalNonDescriptorCarbohydrateFischerConventionImageSourceMeanings.advancedMaterializedProvisions.Disjoint
      provisions := by
  rw [List.disjoint_left]
  intro provision materialized selected
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateFischerConventionImageSourceMeanings.advanced_materialized_disjoint_missing)
      materialized (selected_subset_prior_missing selected)

theorem advanced_materialized_nodup : advancedMaterializedProvisions.Nodup := by
  exact GlobalNonDescriptorCarbohydrateFischerConventionImageSourceMeanings.advanced_materialized_nodup.append
    provisions_nodup prior_materialized_disjoint_selected

theorem advanced_materialized_disjoint_missing :
    advancedMaterializedProvisions.Disjoint advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision advanced missing
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateFischerConventionImageSourceMeanings.advanced_materialized_disjoint_missing)
        priorMaterialized (advanced_missing_subset_prior_missing missing)
  · exact (List.disjoint_left.mp selected_disjoint_advanced_missing) selected missing

theorem reviewed_disjoint_advanced_materialized :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMaterializedProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed advanced
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateFischerConventionImageSourceMeanings.reviewed_disjoint_advanced_materialized)
        reviewed priorMaterialized
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateFischerConventionImageSourceMeanings.reviewed_disjoint_advanced_missing)
        reviewed (selected_subset_prior_missing selected)

theorem reviewed_disjoint_advanced_missing :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed missing
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateFischerConventionImageSourceMeanings.reviewed_disjoint_advanced_missing)
      reviewed (advanced_missing_subset_prior_missing missing)

set_option maxRecDepth 8192 in
theorem mem_reviewed_or_advanced_materialized_or_missing_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions ∨
      provision ∈ advancedMaterializedProvisions ∨
        provision ∈ advancedMissingProvisions ↔
      provision ∈ globalNonDescriptorProvisions := by
  rw [← GlobalNonDescriptorCarbohydrateFischerConventionImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff]
  rw [mem_prior_missing_iff_selected_or_advanced_missing]
  simp only [advancedMaterializedProvisions, List.mem_append]
  tauto

theorem advanced_live_frontier_counts :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.length = 92 ∧
      advancedMaterializedProvisions.length = 1631 ∧
        advancedMissingProvisions.length = 577 ∧
          92 + 1631 + 577 = 2300 := by
  exact ⟨GlobalNonDescriptorSourceMeaningProgress.reviewed_count,
    advanced_materialized_count, advanced_missing_count, by omega⟩

end GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.frozen_artifact_data_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.example_meanings_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.visionReviewedGraphLevelBatch
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.selected_then_advanced_missing_perm_prior_missing
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff
