import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateAldoseChartImageSourceMeaning
import TetraStereo.KernelOnly

set_option autoImplicit false















namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateFischerConventionImageSourceMeanings

open GlobalNonDescriptorSourceMeaningConstructor

def priorRemainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  GlobalNonDescriptorCarbohydrateAldoseChartImageSourceMeaning.remainingImageRows

def rows : List Carbohydrate1996ImageAudit.Provision := priorRemainingImageRows.take 2

def artifactOf : Carbohydrate1996ImageAudit.Provision →
    Carbohydrate1996ImageAudit.ImageArtifact
  | .imageArtifact artifact => artifact

def artifacts : List Carbohydrate1996ImageAudit.ImageArtifact := rows.map artifactOf

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem row_count : rows.length = 2 := by
  simp [rows, priorRemainingImageRows]

@[simp] theorem artifact_count : artifacts.length = 2 := by simp [artifacts]
@[simp] theorem provision_count : provisions.length = 2 := by simp [provisions]

set_option maxRecDepth 4096 in
@[simp] theorem frozen_artifact_data_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.data =
      [ ⟨"2carb/2C0gif/03A.GIF",
          "80db065f1ddd965fdd2b7e626ae51745c780bfe642b94b62ea3d5b2febaf7ab7",
          .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/03B.GIF",
          "6bfa579c22b63ab086c5fd5012590c4f845dae233fc422150170c00741fcd185",
          .numberedOrChartStructure⟩ ] := by
  decide

set_option maxRecDepth 4096 in
@[simp] theorem source_pages_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      [["03n04.html"], ["03n04.html"]] := by
  decide

set_option maxRecDepth 4096 in
private theorem rows_nodup : rows.Nodup := by
  decide

theorem provisions_nodup : provisions.Nodup := by
  exact rows_nodup.map (by intro left right equal; cases equal; rfl)

inductive FischerVariantLabel where
  | a | b | c | d | e | f | g
  deriving DecidableEq, Repr

/-- The common molecular graph and projection semantics shared by raster variants `(a)`--`(g)`.
The record deliberately does not infer conformation from the projection. -/
structure FischerCenterConventionMeaning where
  variantLabels : List FischerVariantLabel
  generallyUsedVariant : FischerVariantLabel
  exampleMolecule : String
  exampleCenterLocant : Nat
  upperCarbonLocant : Nat
  lowerCarbonLocant : Nat
  hydrogenSide : Carbohydrate1996ImageAudit.FischerHorizontalSide
  hydroxylSide : Carbohydrate1996ImageAudit.FischerHorizontalSide
  verticalCarbonChain : Bool
  lowestNumberedCarbonAtTop : Bool
  verticalNeighborsProjectBelowPlane : Bool
  horizontalGroupsProjectAbovePlane : Bool
  intendedAsConformation : Bool
  deriving DecidableEq, Repr

def centerConventionMeaning : FischerCenterConventionMeaning where
  variantLabels := [.a, .b, .c, .d, .e, .f, .g]
  generallyUsedVariant := .e
  exampleMolecule := "D-glucose"
  exampleCenterLocant := 2
  upperCarbonLocant := 1
  lowerCarbonLocant := 3
  hydrogenSide := .left
  hydroxylSide := .right
  verticalCarbonChain := true
  lowestNumberedCarbonAtTop := true
  verticalNeighborsProjectBelowPlane := true
  horizontalGroupsProjectAbovePlane := true
  intendedAsConformation := false

def FischerCenterConventionMeaning.wellFormed
    (meaning : FischerCenterConventionMeaning) : Bool :=
  meaning.variantLabels.length = 7 &&
    decide meaning.variantLabels.Nodup &&
      decide (meaning.generallyUsedVariant ∈ meaning.variantLabels) &&
        meaning.upperCarbonLocant < meaning.exampleCenterLocant &&
          meaning.exampleCenterLocant < meaning.lowerCarbonLocant &&
            meaning.hydrogenSide != meaning.hydroxylSide &&
              meaning.verticalCarbonChain && meaning.lowestNumberedCarbonAtTop &&
                meaning.verticalNeighborsProjectBelowPlane &&
                  meaning.horizontalGroupsProjectAbovePlane &&
                    !meaning.intendedAsConformation

structure NumberedDGlucoseMeaning where
  numberedLocants : List Nat
  carbonCount : Nat
  aldehydeLocant : Nat
  hydroxymethylLocant : Nat
  hydroxylSides : List (Nat × Carbohydrate1996ImageAudit.FischerHorizontalSide)
  acyclicForm : Bool
  intendedAsConformation : Bool
  deriving DecidableEq, Repr

def numberedDGlucoseMeaning : NumberedDGlucoseMeaning where
  numberedLocants := [1, 2, 3, 4, 5, 6]
  carbonCount := 6
  aldehydeLocant := 1
  hydroxymethylLocant := 6
  hydroxylSides := [(2, .right), (3, .left), (4, .right), (5, .right)]
  acyclicForm := true
  intendedAsConformation := false

def NumberedDGlucoseMeaning.wellFormed (meaning : NumberedDGlucoseMeaning) : Bool :=
  meaning.numberedLocants = List.range' 1 meaning.carbonCount &&
    meaning.aldehydeLocant = 1 &&
      meaning.hydroxymethylLocant = meaning.carbonCount &&
        meaning.hydroxylSides.length = meaning.carbonCount - 2 &&
          decide (meaning.hydroxylSides.map Prod.fst).Nodup &&
            meaning.hydroxylSides.all (fun center =>
              1 < center.1 && center.1 < meaning.carbonCount) &&
              meaning.acyclicForm && !meaning.intendedAsConformation

inductive ImageSourceMeaning where
  | centerConvention (meaning : FischerCenterConventionMeaning)
  | numberedDGlucose (meaning : NumberedDGlucoseMeaning)
  deriving DecidableEq, Repr

def sourceMeaning? : String → Option ImageSourceMeaning
  | "2carb/2C0gif/03A.GIF" => some (.centerConvention centerConventionMeaning)
  | "2carb/2C0gif/03B.GIF" => some (.numberedDGlucose numberedDGlucoseMeaning)
  | _ => none

def ImageSourceMeaning.wellFormed : ImageSourceMeaning → Bool
  | .centerConvention meaning => meaning.wellFormed
  | .numberedDGlucose meaning => meaning.wellFormed

def source_meanings_present_and_well_formed : Bool :=
  artifacts.all fun artifact =>
    match sourceMeaning? artifact.data.relativePath with
    | some meaning => meaning.wellFormed
    | none => false

structure VisionReviewedImageMeaning where
  artifactData : Carbohydrate1996ImageAudit.ImageArtifactData
  sourcePages : List String
  sourceMeaning : Option ImageSourceMeaning
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
    visionReviewedGraphLevelBatch.entries.length = 2 := by
  rw [visionReviewedGraphLevelBatch.entries_length, provision_count]

/-! ## Exact advance from the prior 1,619/589 overlay -/

def remainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  priorRemainingImageRows.drop 2

@[simp] theorem remaining_image_count : remainingImageRows.length = 416 := by
  simp [remainingImageRows, priorRemainingImageRows]

theorem rows_append_remaining_eq_prior :
    rows ++ remainingImageRows = priorRemainingImageRows := by
  exact List.take_append_drop 2 priorRemainingImageRows

def advancedMaterializedProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorCarbohydrateAldoseChartImageSourceMeaning.advancedMaterializedProvisions ++
    provisions

def advancedMaterializedBatch :
    GlobalNonDescriptorSourceMeaningBatch advancedMaterializedProvisions :=
  GlobalNonDescriptorCarbohydrateAldoseChartImageSourceMeaning.advancedMaterializedBatch.append
    visionReviewedGraphLevelBatch

@[simp] theorem advanced_materialized_count : advancedMaterializedProvisions.length = 1621 := by
  simp [advancedMaterializedProvisions]

def advancedMissingProvisions : List IUPACNormativeProvision :=
  sourceProvisions .blueBook2013Appendix3 ++
    remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem advanced_missing_count : advancedMissingProvisions.length = 587 := by
  simp [advancedMissingProvisions]

set_option maxRecDepth 8192 in
theorem selected_then_advanced_missing_perm_prior_missing :
    (provisions ++ advancedMissingProvisions).Perm
      GlobalNonDescriptorCarbohydrateAldoseChartImageSourceMeaning.advancedMissingProvisions := by
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
    _ = GlobalNonDescriptorCarbohydrateAldoseChartImageSourceMeaning.advancedMissingProvisions := by
      rfl

theorem mem_prior_missing_iff_selected_or_advanced_missing
    (provision : IUPACNormativeProvision) :
    provision ∈
        GlobalNonDescriptorCarbohydrateAldoseChartImageSourceMeaning.advancedMissingProvisions ↔
      provision ∈ provisions ∨ provision ∈ advancedMissingProvisions := by
  simpa only [List.mem_append] using
    (selected_then_advanced_missing_perm_prior_missing.mem_iff).symm

private theorem selected_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ provisions) :
    provision ∈
      GlobalNonDescriptorCarbohydrateAldoseChartImageSourceMeaning.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_left _ member)

private theorem advanced_missing_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ advancedMissingProvisions) :
    provision ∈
      GlobalNonDescriptorCarbohydrateAldoseChartImageSourceMeaning.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_right _ member)

private theorem selected_append_advanced_missing_nodup :
    (provisions ++ advancedMissingProvisions).Nodup :=
  GlobalNonDescriptorCarbohydrateAldoseChartImageSourceMeaning.advanced_missing_nodup.perm
    selected_then_advanced_missing_perm_prior_missing.symm

theorem advanced_missing_nodup : advancedMissingProvisions.Nodup :=
  List.Nodup.of_append_right selected_append_advanced_missing_nodup

private theorem selected_disjoint_advanced_missing :
    provisions.Disjoint advancedMissingProvisions :=
  List.disjoint_of_nodup_append selected_append_advanced_missing_nodup

private theorem prior_materialized_disjoint_selected :
    GlobalNonDescriptorCarbohydrateAldoseChartImageSourceMeaning.advancedMaterializedProvisions.Disjoint
      provisions := by
  rw [List.disjoint_left]
  intro provision materialized selected
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateAldoseChartImageSourceMeaning.advanced_materialized_disjoint_missing)
      materialized (selected_subset_prior_missing selected)

theorem advanced_materialized_nodup : advancedMaterializedProvisions.Nodup := by
  exact GlobalNonDescriptorCarbohydrateAldoseChartImageSourceMeaning.advanced_materialized_nodup.append
    provisions_nodup prior_materialized_disjoint_selected

theorem advanced_materialized_disjoint_missing :
    advancedMaterializedProvisions.Disjoint advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision advanced missing
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateAldoseChartImageSourceMeaning.advanced_materialized_disjoint_missing)
        priorMaterialized (advanced_missing_subset_prior_missing missing)
  · exact (List.disjoint_left.mp selected_disjoint_advanced_missing) selected missing

theorem reviewed_disjoint_advanced_materialized :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMaterializedProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed advanced
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateAldoseChartImageSourceMeaning.reviewed_disjoint_advanced_materialized)
        reviewed priorMaterialized
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateAldoseChartImageSourceMeaning.reviewed_disjoint_advanced_missing)
        reviewed (selected_subset_prior_missing selected)

theorem reviewed_disjoint_advanced_missing :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed missing
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateAldoseChartImageSourceMeaning.reviewed_disjoint_advanced_missing)
      reviewed (advanced_missing_subset_prior_missing missing)

set_option maxRecDepth 8192 in
theorem mem_reviewed_or_advanced_materialized_or_missing_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions ∨
      provision ∈ advancedMaterializedProvisions ∨
        provision ∈ advancedMissingProvisions ↔
      provision ∈ globalNonDescriptorProvisions := by
  rw [← GlobalNonDescriptorCarbohydrateAldoseChartImageSourceMeaning.mem_reviewed_or_advanced_materialized_or_missing_iff]
  rw [mem_prior_missing_iff_selected_or_advanced_missing]
  simp only [advancedMaterializedProvisions, List.mem_append]
  tauto

theorem advanced_live_frontier_counts :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.length = 92 ∧
      advancedMaterializedProvisions.length = 1621 ∧
        advancedMissingProvisions.length = 587 ∧
          92 + 1621 + 587 = 2300 := by
  exact ⟨GlobalNonDescriptorSourceMeaningProgress.reviewed_count,
    advanced_materialized_count, advanced_missing_count, by omega⟩

end GlobalNonDescriptorCarbohydrateFischerConventionImageSourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateFischerConventionImageSourceMeanings.frozen_artifact_data_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateFischerConventionImageSourceMeanings.source_pages_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateFischerConventionImageSourceMeanings.visionReviewedGraphLevelBatch
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateFischerConventionImageSourceMeanings.selected_then_advanced_missing_perm_prior_missing
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateFischerConventionImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff
