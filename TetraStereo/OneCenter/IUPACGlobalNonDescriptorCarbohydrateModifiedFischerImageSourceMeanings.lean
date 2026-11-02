import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateCyclicFischerImageSourceMeanings
import TetraStereo.KernelOnly

set_option autoImplicit false















namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateModifiedFischerImageSourceMeanings

open GlobalNonDescriptorSourceMeaningConstructor

def priorRemainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  GlobalNonDescriptorCarbohydrateCyclicFischerImageSourceMeanings.remainingImageRows

def rows : List Carbohydrate1996ImageAudit.Provision := priorRemainingImageRows.take 4

def artifactOf : Carbohydrate1996ImageAudit.Provision →
    Carbohydrate1996ImageAudit.ImageArtifact
  | .imageArtifact artifact => artifact

def artifacts : List Carbohydrate1996ImageAudit.ImageArtifact := rows.map artifactOf

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem row_count : rows.length = 4 := by
  simp [rows, priorRemainingImageRows]

@[simp] theorem artifact_count : artifacts.length = 4 := by simp [artifacts]
@[simp] theorem provision_count : provisions.length = 4 := by simp [provisions]

set_option maxRecDepth 4096 in
@[simp] theorem frozen_artifact_data_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.data =
      [ ⟨"2carb/2C0gif/053A.GIF", "b8d94e9f38d67e6de25c1bd4feb8f439ec27e787adaf3966023df800b46700ea", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/053B.GIF", "2ac38874c54038147679007956c05599de546953c17db1f4f68e9a94c557ab20", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/053C.GIF", "087a4870435e6eb1e5e2c1eee5aecae8fce2c53ed50c7eb5bd9085390fe28ed2", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/053D.GIF", "568e6fb753afdc10e9dff20ca5c66eae01826a016bfe4309a0ed7493e6d78343", .numberedOrChartStructure⟩ ] := by
  decide

set_option maxRecDepth 4096 in
@[simp] theorem source_pages_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 4 ["05.html"] := by
  decide

set_option maxRecDepth 4096 in
private theorem rows_nodup : rows.Nodup := by
  decide

theorem provisions_nodup : provisions.Nodup := by
  exact rows_nodup.map (by intro left right equal; cases equal; rfl)

inductive Anomer where
  | alpha | beta
  deriving DecidableEq, Repr

inductive CarbonylKind where
  | aldose | ketose
  deriving DecidableEq, Repr

inductive StericRelation where
  | transHydroxymethylToAnomericHydroxyl
  | cisMethylToAnomericHydroxyl
  | notHighlighted
  deriving DecidableEq, Repr

structure ModifiedFischerMeaning where
  publishedName : String
  anomer : Anomer
  series : GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.ConfigurationalSeries
  carbonylKind : CarbonylKind
  anomericCarbonLocant : Nat
  ringOxygenSourceLocant : Nat
  ringSize : Nat
  rotatedCarbonLocant : Nat
  rotationBondPartnerLocant : Nat
  oAcetylLocants : List Nat
  hydroxymethylCarbonLocants : List Nat
  methylSubstituentAt? : Option Nat
  stericRelation : StericRelation
  ringAtomsVertical : Bool
  longBondBehindPlane : Bool
  deriving DecidableEq, Repr

def meanings : List ModifiedFischerMeaning :=
  [ { publishedName := "alpha-D-glucopyranose"
      anomer := .alpha
      series := .D
      carbonylKind := .aldose
      anomericCarbonLocant := 1
      ringOxygenSourceLocant := 5
      ringSize := 6
      rotatedCarbonLocant := 5
      rotationBondPartnerLocant := 4
      oAcetylLocants := []
      hydroxymethylCarbonLocants := [6]
      methylSubstituentAt? := none
      stericRelation := .transHydroxymethylToAnomericHydroxyl
      ringAtomsVertical := true
      longBondBehindPlane := true }
  , { publishedName := "2,3,5,6-tetra-O-acetyl-alpha-D-galactofuranose"
      anomer := .alpha
      series := .D
      carbonylKind := .aldose
      anomericCarbonLocant := 1
      ringOxygenSourceLocant := 4
      ringSize := 5
      rotatedCarbonLocant := 4
      rotationBondPartnerLocant := 3
      oAcetylLocants := [2, 3, 5, 6]
      hydroxymethylCarbonLocants := [6]
      methylSubstituentAt? := none
      stericRelation := .notHighlighted
      ringAtomsVertical := true
      longBondBehindPlane := true }
  , { publishedName := "beta-L-fucopyranose"
      anomer := .beta
      series := .L
      carbonylKind := .aldose
      anomericCarbonLocant := 1
      ringOxygenSourceLocant := 5
      ringSize := 6
      rotatedCarbonLocant := 5
      rotationBondPartnerLocant := 4
      oAcetylLocants := []
      hydroxymethylCarbonLocants := []
      methylSubstituentAt? := some 5
      stericRelation := .cisMethylToAnomericHydroxyl
      ringAtomsVertical := true
      longBondBehindPlane := true }
  , { publishedName := "beta-D-fructofuranose"
      anomer := .beta
      series := .D
      carbonylKind := .ketose
      anomericCarbonLocant := 2
      ringOxygenSourceLocant := 5
      ringSize := 5
      rotatedCarbonLocant := 2
      rotationBondPartnerLocant := 3
      oAcetylLocants := []
      hydroxymethylCarbonLocants := [1, 6]
      methylSubstituentAt? := none
      stericRelation := .notHighlighted
      ringAtomsVertical := true
      longBondBehindPlane := true } ]

@[simp] theorem meanings_exact : meanings =
    [ { publishedName := "alpha-D-glucopyranose"
        anomer := .alpha
        series := .D
        carbonylKind := .aldose
        anomericCarbonLocant := 1
        ringOxygenSourceLocant := 5
        ringSize := 6
        rotatedCarbonLocant := 5
        rotationBondPartnerLocant := 4
        oAcetylLocants := []
        hydroxymethylCarbonLocants := [6]
        methylSubstituentAt? := none
        stericRelation := .transHydroxymethylToAnomericHydroxyl
        ringAtomsVertical := true
        longBondBehindPlane := true }
    , { publishedName := "2,3,5,6-tetra-O-acetyl-alpha-D-galactofuranose"
        anomer := .alpha
        series := .D
        carbonylKind := .aldose
        anomericCarbonLocant := 1
        ringOxygenSourceLocant := 4
        ringSize := 5
        rotatedCarbonLocant := 4
        rotationBondPartnerLocant := 3
        oAcetylLocants := [2, 3, 5, 6]
        hydroxymethylCarbonLocants := [6]
        methylSubstituentAt? := none
        stericRelation := .notHighlighted
        ringAtomsVertical := true
        longBondBehindPlane := true }
    , { publishedName := "beta-L-fucopyranose"
        anomer := .beta
        series := .L
        carbonylKind := .aldose
        anomericCarbonLocant := 1
        ringOxygenSourceLocant := 5
        ringSize := 6
        rotatedCarbonLocant := 5
        rotationBondPartnerLocant := 4
        oAcetylLocants := []
        hydroxymethylCarbonLocants := []
        methylSubstituentAt? := some 5
        stericRelation := .cisMethylToAnomericHydroxyl
        ringAtomsVertical := true
        longBondBehindPlane := true }
    , { publishedName := "beta-D-fructofuranose"
        anomer := .beta
        series := .D
        carbonylKind := .ketose
        anomericCarbonLocant := 2
        ringOxygenSourceLocant := 5
        ringSize := 5
        rotatedCarbonLocant := 2
        rotationBondPartnerLocant := 3
        oAcetylLocants := []
        hydroxymethylCarbonLocants := [1, 6]
        methylSubstituentAt? := none
        stericRelation := .notHighlighted
        ringAtomsVertical := true
        longBondBehindPlane := true } ] := rfl

def ModifiedFischerMeaning.wellFormed (meaning : ModifiedFischerMeaning) : Bool :=
  meaning.ringSize = meaning.ringOxygenSourceLocant - meaning.anomericCarbonLocant + 2 &&
    meaning.anomericCarbonLocant < meaning.ringOxygenSourceLocant &&
      (match meaning.carbonylKind with
       | .aldose =>
           meaning.rotatedCarbonLocant = meaning.ringOxygenSourceLocant &&
             meaning.rotationBondPartnerLocant + 1 = meaning.rotatedCarbonLocant
       | .ketose =>
           meaning.rotatedCarbonLocant = 2 && meaning.rotationBondPartnerLocant = 3) &&
        meaning.oAcetylLocants.Nodup && meaning.hydroxymethylCarbonLocants.Nodup &&
          meaning.oAcetylLocants.all (fun locant => 1 ≤ locant && locant ≤ 6) &&
            meaning.hydroxymethylCarbonLocants.all (fun locant => 1 ≤ locant && locant ≤ 6) &&
              meaning.ringAtomsVertical && meaning.longBondBehindPlane &&
                !meaning.publishedName.isEmpty

structure ModifiedFischerRule where
  rotateRingOxygenCarbonAboutPrecedingBondForAldoses : Bool
  ketosesMayRequireDifferentRotation : Bool
  fructofuranoseRotatesC2AboutC3 : Bool
  bridgeImaginedBehindPaper : Bool
  deriving DecidableEq, Repr

def modifiedFischerRule : ModifiedFischerRule where
  rotateRingOxygenCarbonAboutPrecedingBondForAldoses := true
  ketosesMayRequireDifferentRotation := true
  fructofuranoseRotatesC2AboutC3 := true
  bridgeImaginedBehindPaper := true

def sourceMeaning? : String → Option ModifiedFischerMeaning
  | "2carb/2C0gif/053A.GIF" => meanings[0]?
  | "2carb/2C0gif/053B.GIF" => meanings[1]?
  | "2carb/2C0gif/053C.GIF" => meanings[2]?
  | "2carb/2C0gif/053D.GIF" => meanings[3]?
  | _ => none

def all_meanings_well_formed : Bool :=
  artifacts.all fun artifact =>
    match sourceMeaning? artifact.data.relativePath with
    | some meaning => meaning.wellFormed
    | none => false

structure VisionReviewedImageMeaning where
  artifactData : Carbohydrate1996ImageAudit.ImageArtifactData
  sourcePages : List String
  sourceMeaning : Option ModifiedFischerMeaning
  rule : ModifiedFischerRule
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
        rule := modifiedFischerRule
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
    visionReviewedGraphLevelBatch.entries.length = 4 := by
  rw [visionReviewedGraphLevelBatch.entries_length, provision_count]

/-! ## Exact advance from the prior 1,636/572 overlay -/

def remainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  priorRemainingImageRows.drop 4

@[simp] theorem remaining_image_count : remainingImageRows.length = 397 := by
  simp [remainingImageRows, priorRemainingImageRows]

theorem rows_append_remaining_eq_prior :
    rows ++ remainingImageRows = priorRemainingImageRows := by
  exact List.take_append_drop 4 priorRemainingImageRows

def advancedMaterializedProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorCarbohydrateCyclicFischerImageSourceMeanings.advancedMaterializedProvisions ++
    provisions

def advancedMaterializedBatch :
    GlobalNonDescriptorSourceMeaningBatch advancedMaterializedProvisions :=
  GlobalNonDescriptorCarbohydrateCyclicFischerImageSourceMeanings.advancedMaterializedBatch.append
    visionReviewedGraphLevelBatch

@[simp] theorem advanced_materialized_count : advancedMaterializedProvisions.length = 1640 := by
  simp [advancedMaterializedProvisions]

def advancedMissingProvisions : List IUPACNormativeProvision :=
  sourceProvisions .blueBook2013Appendix3 ++
    remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem advanced_missing_count : advancedMissingProvisions.length = 568 := by
  simp [advancedMissingProvisions]

set_option maxRecDepth 8192 in
theorem selected_then_advanced_missing_perm_prior_missing :
    (provisions ++ advancedMissingProvisions).Perm
      GlobalNonDescriptorCarbohydrateCyclicFischerImageSourceMeanings.advancedMissingProvisions := by
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
    _ = GlobalNonDescriptorCarbohydrateCyclicFischerImageSourceMeanings.advancedMissingProvisions := by
      rfl

theorem mem_prior_missing_iff_selected_or_advanced_missing
    (provision : IUPACNormativeProvision) :
    provision ∈
        GlobalNonDescriptorCarbohydrateCyclicFischerImageSourceMeanings.advancedMissingProvisions ↔
      provision ∈ provisions ∨ provision ∈ advancedMissingProvisions := by
  simpa only [List.mem_append] using
    (selected_then_advanced_missing_perm_prior_missing.mem_iff).symm

private theorem selected_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ provisions) :
    provision ∈
      GlobalNonDescriptorCarbohydrateCyclicFischerImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_left _ member)

private theorem advanced_missing_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ advancedMissingProvisions) :
    provision ∈
      GlobalNonDescriptorCarbohydrateCyclicFischerImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_right _ member)

private theorem selected_append_advanced_missing_nodup :
    (provisions ++ advancedMissingProvisions).Nodup :=
  GlobalNonDescriptorCarbohydrateCyclicFischerImageSourceMeanings.advanced_missing_nodup.perm
    selected_then_advanced_missing_perm_prior_missing.symm

theorem advanced_missing_nodup : advancedMissingProvisions.Nodup :=
  List.Nodup.of_append_right selected_append_advanced_missing_nodup

private theorem selected_disjoint_advanced_missing :
    provisions.Disjoint advancedMissingProvisions :=
  List.disjoint_of_nodup_append selected_append_advanced_missing_nodup

private theorem prior_materialized_disjoint_selected :
    GlobalNonDescriptorCarbohydrateCyclicFischerImageSourceMeanings.advancedMaterializedProvisions.Disjoint
      provisions := by
  rw [List.disjoint_left]
  intro provision materialized selected
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateCyclicFischerImageSourceMeanings.advanced_materialized_disjoint_missing)
      materialized (selected_subset_prior_missing selected)

theorem advanced_materialized_nodup : advancedMaterializedProvisions.Nodup := by
  exact GlobalNonDescriptorCarbohydrateCyclicFischerImageSourceMeanings.advanced_materialized_nodup.append
    provisions_nodup prior_materialized_disjoint_selected

theorem advanced_materialized_disjoint_missing :
    advancedMaterializedProvisions.Disjoint advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision advanced missing
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateCyclicFischerImageSourceMeanings.advanced_materialized_disjoint_missing)
        priorMaterialized (advanced_missing_subset_prior_missing missing)
  · exact (List.disjoint_left.mp selected_disjoint_advanced_missing) selected missing

theorem reviewed_disjoint_advanced_materialized :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMaterializedProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed advanced
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateCyclicFischerImageSourceMeanings.reviewed_disjoint_advanced_materialized)
        reviewed priorMaterialized
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateCyclicFischerImageSourceMeanings.reviewed_disjoint_advanced_missing)
        reviewed (selected_subset_prior_missing selected)

theorem reviewed_disjoint_advanced_missing :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed missing
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateCyclicFischerImageSourceMeanings.reviewed_disjoint_advanced_missing)
      reviewed (advanced_missing_subset_prior_missing missing)

set_option maxRecDepth 8192 in
theorem mem_reviewed_or_advanced_materialized_or_missing_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions ∨
      provision ∈ advancedMaterializedProvisions ∨
        provision ∈ advancedMissingProvisions ↔
      provision ∈ globalNonDescriptorProvisions := by
  rw [← GlobalNonDescriptorCarbohydrateCyclicFischerImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff]
  rw [mem_prior_missing_iff_selected_or_advanced_missing]
  simp only [advancedMaterializedProvisions, List.mem_append]
  tauto

theorem advanced_live_frontier_counts :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.length = 92 ∧
      advancedMaterializedProvisions.length = 1640 ∧
        advancedMissingProvisions.length = 568 ∧
          92 + 1640 + 568 = 2300 := by
  exact ⟨GlobalNonDescriptorSourceMeaningProgress.reviewed_count,
    advanced_materialized_count, advanced_missing_count, by omega⟩

end GlobalNonDescriptorCarbohydrateModifiedFischerImageSourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateModifiedFischerImageSourceMeanings.frozen_artifact_data_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateModifiedFischerImageSourceMeanings.meanings_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateModifiedFischerImageSourceMeanings.visionReviewedGraphLevelBatch
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateModifiedFischerImageSourceMeanings.selected_then_advanced_missing_perm_prior_missing
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateModifiedFischerImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff
