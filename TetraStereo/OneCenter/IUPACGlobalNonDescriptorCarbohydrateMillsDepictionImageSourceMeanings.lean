import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateUnconventionalHaworthChartImageSourceMeaning
import TetraStereo.KernelOnly

set_option autoImplicit false















namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateMillsDepictionImageSourceMeanings

open GlobalNonDescriptorSourceMeaningConstructor

def priorRemainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  GlobalNonDescriptorCarbohydrateUnconventionalHaworthChartImageSourceMeaning.remainingImageRows

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
      [ ⟨"2carb/2C0gif/056A.GIF", "f5240c5455288259c0147f2dba129f730acf9b008f1cfd1716ebe508a04f61d7", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/056B.GIF", "df658691918db37d465b0ce6eef09ddb47364c312b7851c523599c1ec1963d22", .numberedOrChartStructure⟩ ] := by
  decide

set_option maxRecDepth 4096 in
@[simp] theorem source_pages_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 2 ["05.html"] := by
  decide

set_option maxRecDepth 4096 in
private theorem rows_nodup : rows.Nodup := by
  decide

theorem provisions_nodup : provisions.Nodup := by
  exact rows_nodup.map (by intro left right equal; cases equal; rfl)

inductive BridgeKind where
  | isopropylidene | lactone
  deriving DecidableEq, Repr

structure Bridge where
  kind : BridgeKind
  firstLocant : Nat
  secondLocant : Nat
  deriving DecidableEq, Repr

structure MillsMeaning where
  publishedName : String
  series : GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.ConfigurationalSeries
  parentFischerHydroxylSides :
    List (Nat × Carbohydrate1996ImageAudit.FischerHorizontalSide)
  anomer : Option GlobalNonDescriptorCarbohydrateHaworthImageSourceMeanings.Anomer
  hemiacetalRingClosure? : Option (Nat × Nat)
  bridges : List Bridge
  millsAboveLocants : List Nat
  millsBelowLocants : List Nat
  deriving DecidableEq, Repr

def meanings : List MillsMeaning :=
  [ { publishedName := "1,2:3,4-di-O-isopropylidene-alpha-D-galactopyranose"
      series := .D
      parentFischerHydroxylSides :=
        [(2, .right), (3, .left), (4, .left), (5, .right)]
      anomer := some .alpha
      hemiacetalRingClosure? := some (1, 5)
      bridges := [⟨.isopropylidene, 1, 2⟩, ⟨.isopropylidene, 3, 4⟩]
      millsAboveLocants := [3, 4]
      millsBelowLocants := [1, 2] }
  , { publishedName := "D-glucaro-1,4:6,3-dilactone"
      series := .D
      parentFischerHydroxylSides :=
        [(2, .right), (3, .left), (4, .right), (5, .right)]
      anomer := none
      hemiacetalRingClosure? := none
      bridges := [⟨.lactone, 1, 4⟩, ⟨.lactone, 6, 3⟩]
      millsAboveLocants := []
      millsBelowLocants := [] } ]

@[simp] theorem meanings_exact : meanings =
    [ { publishedName := "1,2:3,4-di-O-isopropylidene-alpha-D-galactopyranose"
        series := .D
        parentFischerHydroxylSides :=
          [(2, .right), (3, .left), (4, .left), (5, .right)]
        anomer := some .alpha
        hemiacetalRingClosure? := some (1, 5)
        bridges := [⟨.isopropylidene, 1, 2⟩, ⟨.isopropylidene, 3, 4⟩]
        millsAboveLocants := [3, 4]
        millsBelowLocants := [1, 2] }
    , { publishedName := "D-glucaro-1,4:6,3-dilactone"
        series := .D
        parentFischerHydroxylSides :=
          [(2, .right), (3, .left), (4, .right), (5, .right)]
        anomer := none
        hemiacetalRingClosure? := none
        bridges := [⟨.lactone, 1, 4⟩, ⟨.lactone, 6, 3⟩]
        millsAboveLocants := []
        millsBelowLocants := [] } ] := rfl

def Bridge.wellFormed (bridge : Bridge) : Bool :=
  1 ≤ bridge.firstLocant && bridge.firstLocant ≤ 6 &&
    1 ≤ bridge.secondLocant && bridge.secondLocant ≤ 6 &&
      bridge.firstLocant ≠ bridge.secondLocant

def MillsMeaning.wellFormed (meaning : MillsMeaning) : Bool :=
  meaning.parentFischerHydroxylSides.length = 4 &&
    (meaning.parentFischerHydroxylSides.map Prod.fst).Nodup &&
      meaning.bridges.length = 2 && meaning.bridges.Nodup &&
        meaning.bridges.all Bridge.wellFormed &&
          meaning.millsAboveLocants.Nodup && meaning.millsBelowLocants.Nodup &&
            meaning.millsAboveLocants.all (fun locant => 1 ≤ locant && locant ≤ 6) &&
              meaning.millsBelowLocants.all (fun locant => 1 ≤ locant && locant ≤ 6) &&
                meaning.millsAboveLocants.all
                    (fun locant => !meaning.millsBelowLocants.contains locant) &&
                  !meaning.publishedName.isEmpty

structure MillsRule where
  mainHemiacetalRingInPaperPlane : Bool
  dashedBondsMeanBelowPlane : Bool
  thickenedBondsMeanAbovePlane : Bool
  additionalRingsMotivateDepiction : Bool
  deriving DecidableEq, Repr

def millsRule : MillsRule where
  mainHemiacetalRingInPaperPlane := true
  dashedBondsMeanBelowPlane := true
  thickenedBondsMeanAbovePlane := true
  additionalRingsMotivateDepiction := true

def sourceMeaning? : String → Option MillsMeaning
  | "2carb/2C0gif/056A.GIF" => meanings[0]?
  | "2carb/2C0gif/056B.GIF" => meanings[1]?
  | _ => none

def all_meanings_well_formed : Bool :=
  artifacts.all fun artifact =>
    match sourceMeaning? artifact.data.relativePath with
    | some meaning => meaning.wellFormed
    | none => false

structure VisionReviewedImageMeaning where
  artifactData : Carbohydrate1996ImageAudit.ImageArtifactData
  sourcePages : List String
  sourceMeaning : Option MillsMeaning
  rule : MillsRule
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
        rule := millsRule
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

/-! ## Exact advance from the prior 1,650/558 overlay -/

def remainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  priorRemainingImageRows.drop 2

@[simp] theorem remaining_image_count : remainingImageRows.length = 385 := by
  simp [remainingImageRows, priorRemainingImageRows]

theorem rows_append_remaining_eq_prior :
    rows ++ remainingImageRows = priorRemainingImageRows := by
  exact List.take_append_drop 2 priorRemainingImageRows

def advancedMaterializedProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorCarbohydrateUnconventionalHaworthChartImageSourceMeaning.advancedMaterializedProvisions ++
    provisions

def advancedMaterializedBatch :
    GlobalNonDescriptorSourceMeaningBatch advancedMaterializedProvisions :=
  GlobalNonDescriptorCarbohydrateUnconventionalHaworthChartImageSourceMeaning.advancedMaterializedBatch.append
    visionReviewedGraphLevelBatch

@[simp] theorem advanced_materialized_count : advancedMaterializedProvisions.length = 1652 := by
  simp [advancedMaterializedProvisions]

def advancedMissingProvisions : List IUPACNormativeProvision :=
  sourceProvisions .blueBook2013Appendix3 ++
    remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem advanced_missing_count : advancedMissingProvisions.length = 556 := by
  simp [advancedMissingProvisions]

set_option maxRecDepth 8192 in
theorem selected_then_advanced_missing_perm_prior_missing :
    (provisions ++ advancedMissingProvisions).Perm
      GlobalNonDescriptorCarbohydrateUnconventionalHaworthChartImageSourceMeaning.advancedMissingProvisions := by
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
    _ = GlobalNonDescriptorCarbohydrateUnconventionalHaworthChartImageSourceMeaning.advancedMissingProvisions := by
      rfl

theorem mem_prior_missing_iff_selected_or_advanced_missing
    (provision : IUPACNormativeProvision) :
    provision ∈
        GlobalNonDescriptorCarbohydrateUnconventionalHaworthChartImageSourceMeaning.advancedMissingProvisions ↔
      provision ∈ provisions ∨ provision ∈ advancedMissingProvisions := by
  simpa only [List.mem_append] using
    (selected_then_advanced_missing_perm_prior_missing.mem_iff).symm

private theorem selected_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ provisions) :
    provision ∈
      GlobalNonDescriptorCarbohydrateUnconventionalHaworthChartImageSourceMeaning.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_left _ member)

private theorem advanced_missing_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ advancedMissingProvisions) :
    provision ∈
      GlobalNonDescriptorCarbohydrateUnconventionalHaworthChartImageSourceMeaning.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_right _ member)

private theorem selected_append_advanced_missing_nodup :
    (provisions ++ advancedMissingProvisions).Nodup :=
  GlobalNonDescriptorCarbohydrateUnconventionalHaworthChartImageSourceMeaning.advanced_missing_nodup.perm
    selected_then_advanced_missing_perm_prior_missing.symm

theorem advanced_missing_nodup : advancedMissingProvisions.Nodup :=
  List.Nodup.of_append_right selected_append_advanced_missing_nodup

private theorem selected_disjoint_advanced_missing :
    provisions.Disjoint advancedMissingProvisions :=
  List.disjoint_of_nodup_append selected_append_advanced_missing_nodup

private theorem prior_materialized_disjoint_selected :
    GlobalNonDescriptorCarbohydrateUnconventionalHaworthChartImageSourceMeaning.advancedMaterializedProvisions.Disjoint
      provisions := by
  rw [List.disjoint_left]
  intro provision materialized selected
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateUnconventionalHaworthChartImageSourceMeaning.advanced_materialized_disjoint_missing)
      materialized (selected_subset_prior_missing selected)

theorem advanced_materialized_nodup : advancedMaterializedProvisions.Nodup := by
  exact GlobalNonDescriptorCarbohydrateUnconventionalHaworthChartImageSourceMeaning.advanced_materialized_nodup.append
    provisions_nodup prior_materialized_disjoint_selected

theorem advanced_materialized_disjoint_missing :
    advancedMaterializedProvisions.Disjoint advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision advanced missing
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateUnconventionalHaworthChartImageSourceMeaning.advanced_materialized_disjoint_missing)
        priorMaterialized (advanced_missing_subset_prior_missing missing)
  · exact (List.disjoint_left.mp selected_disjoint_advanced_missing) selected missing

theorem reviewed_disjoint_advanced_materialized :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMaterializedProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed advanced
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateUnconventionalHaworthChartImageSourceMeaning.reviewed_disjoint_advanced_materialized)
        reviewed priorMaterialized
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateUnconventionalHaworthChartImageSourceMeaning.reviewed_disjoint_advanced_missing)
        reviewed (selected_subset_prior_missing selected)

theorem reviewed_disjoint_advanced_missing :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed missing
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateUnconventionalHaworthChartImageSourceMeaning.reviewed_disjoint_advanced_missing)
      reviewed (advanced_missing_subset_prior_missing missing)

set_option maxRecDepth 8192 in
theorem mem_reviewed_or_advanced_materialized_or_missing_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions ∨
      provision ∈ advancedMaterializedProvisions ∨
        provision ∈ advancedMissingProvisions ↔
      provision ∈ globalNonDescriptorProvisions := by
  rw [← GlobalNonDescriptorCarbohydrateUnconventionalHaworthChartImageSourceMeaning.mem_reviewed_or_advanced_materialized_or_missing_iff]
  rw [mem_prior_missing_iff_selected_or_advanced_missing]
  simp only [advancedMaterializedProvisions, List.mem_append]
  tauto

theorem advanced_live_frontier_counts :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.length = 92 ∧
      advancedMaterializedProvisions.length = 1652 ∧
        advancedMissingProvisions.length = 556 ∧
          92 + 1652 + 556 = 2300 := by
  exact ⟨GlobalNonDescriptorSourceMeaningProgress.reviewed_count,
    advanced_materialized_count, advanced_missing_count, by omega⟩

end GlobalNonDescriptorCarbohydrateMillsDepictionImageSourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateMillsDepictionImageSourceMeanings.frozen_artifact_data_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateMillsDepictionImageSourceMeanings.meanings_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateMillsDepictionImageSourceMeanings.visionReviewedGraphLevelBatch
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateMillsDepictionImageSourceMeanings.selected_then_advanced_missing_perm_prior_missing
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateMillsDepictionImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff
