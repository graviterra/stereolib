import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateMillsDepictionImageSourceMeanings
import TetraStereo.KernelOnly

set_option autoImplicit false















namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateConformationImageSourceMeanings

open GlobalNonDescriptorSourceMeaningConstructor
open GlobalNonDescriptorCarbohydrateHaworthImageSourceMeanings

def priorRemainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  GlobalNonDescriptorCarbohydrateMillsDepictionImageSourceMeanings.remainingImageRows

def rows : List Carbohydrate1996ImageAudit.Provision := priorRemainingImageRows.take 3

def artifactOf : Carbohydrate1996ImageAudit.Provision →
    Carbohydrate1996ImageAudit.ImageArtifact
  | .imageArtifact artifact => artifact

def artifacts : List Carbohydrate1996ImageAudit.ImageArtifact := rows.map artifactOf

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem row_count : rows.length = 3 := by
  simp [rows, priorRemainingImageRows]

@[simp] theorem artifact_count : artifacts.length = 3 := by simp [artifacts]
@[simp] theorem provision_count : provisions.length = 3 := by simp [provisions]

set_option maxRecDepth 4096 in
@[simp] theorem frozen_artifact_data_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.data =
      [ ⟨"2carb/2C0gif/057.GIF", "a22339527f4bce2a0a6438e0b013da4b85363808c7cf081e8ebece60453cc523", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/058A.GIF", "babce91edaf1164912ce6fe87e30477f84d3e013d757f440cf4c37020706ea6e", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/058B.GIF", "6cad5323b75f2f151713709819dad389daa8c0771ab3fad0372b586a288d7386", .numberedOrChartStructure⟩ ] := by
  decide

set_option maxRecDepth 4096 in
@[simp] theorem source_pages_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 3 ["05.html"] := by
  decide

set_option maxRecDepth 4096 in
private theorem rows_nodup : rows.Nodup := by
  decide

theorem provisions_nodup : provisions.Nodup := by
  exact rows_nodup.map (by intro left right equal; cases equal; rfl)

inductive CyclicRendering where
  | ringHydrogensIncluded | ringHydrogensOmitted
  deriving DecidableEq, Repr

structure CyclicConformationMeaning where
  publishedName : String
  printedConformerSymbol? : Option String
  canonicalRingSubstituents : List RingSubstituent
  renderings : List CyclicRendering
  deriving DecidableEq, Repr

def cyclicMeaning : CyclicConformationMeaning where
  publishedName := "beta-D-glucopyranose in a chair conformation"
  printedConformerSymbol? := none
  canonicalRingSubstituents :=
    [ ⟨1, .hydroxyl, .above⟩, ⟨2, .hydroxyl, .below⟩, ⟨3, .hydroxyl, .above⟩
    , ⟨4, .hydroxyl, .below⟩, ⟨5, .hydroxymethyl 6, .above⟩ ]
  renderings := [.ringHydrogensIncluded, .ringHydrogensOmitted]

structure AcyclicConformationMeaning where
  publishedName : String
  parentFischerHydroxylSides :
    List (Nat × Carbohydrate1996ImageAudit.FischerHorizontalSide)
  hydroxylLocantsAbovePlane : List Nat
  hydrogenLocantsBelowPlane : List Nat
  backboneDrawnAsPlanarZigzag : Bool
  deriving DecidableEq, Repr

def acyclicMeanings : List AcyclicConformationMeaning :=
  [ { publishedName := "D-arabinitol"
      parentFischerHydroxylSides := [(2, .left), (3, .right), (4, .right)]
      hydroxylLocantsAbovePlane := [2, 3, 4]
      hydrogenLocantsBelowPlane := [2, 3, 4]
      backboneDrawnAsPlanarZigzag := true }
  , { publishedName := "xylitol"
      parentFischerHydroxylSides := [(2, .right), (3, .left), (4, .right)]
      hydroxylLocantsAbovePlane := [2, 3, 4]
      hydrogenLocantsBelowPlane := [2, 3, 4]
      backboneDrawnAsPlanarZigzag := true } ]

@[simp] theorem acyclic_meanings_exact : acyclicMeanings =
    [ { publishedName := "D-arabinitol"
        parentFischerHydroxylSides := [(2, .left), (3, .right), (4, .right)]
        hydroxylLocantsAbovePlane := [2, 3, 4]
        hydrogenLocantsBelowPlane := [2, 3, 4]
        backboneDrawnAsPlanarZigzag := true }
    , { publishedName := "xylitol"
        parentFischerHydroxylSides := [(2, .right), (3, .left), (4, .right)]
        hydroxylLocantsAbovePlane := [2, 3, 4]
        hydrogenLocantsBelowPlane := [2, 3, 4]
        backboneDrawnAsPlanarZigzag := true } ] := rfl

def CyclicConformationMeaning.wellFormed (meaning : CyclicConformationMeaning) : Bool :=
  meaning.canonicalRingSubstituents.Nodup && meaning.renderings.Nodup &&
    meaning.renderings.length = 2 && !meaning.publishedName.isEmpty

def AcyclicConformationMeaning.wellFormed (meaning : AcyclicConformationMeaning) : Bool :=
  meaning.parentFischerHydroxylSides.length = 3 &&
    (meaning.parentFischerHydroxylSides.map Prod.fst).Nodup &&
      meaning.hydroxylLocantsAbovePlane = [2, 3, 4] &&
        meaning.hydrogenLocantsBelowPlane = [2, 3, 4] &&
          meaning.backboneDrawnAsPlanarZigzag && !meaning.publishedName.isEmpty

structure ConformationRule where
  haworthRepresentationImpliesPlanarRing : Bool
  actualMonosaccharideRingsNonplanar : Bool
  hydrogenInclusionMayMakeStereochemicalPoint : Bool
  acyclicSelectedAtomsPlacedInPaperPlane : Bool
  solidBondsMeanAbovePlane : Bool
  dashedBondsMeanBelowPlane : Bool
  favoredAcyclicConformerNeedNotHaveAllCarbonsCoplanar : Bool
  deriving DecidableEq, Repr

def conformationRule : ConformationRule where
  haworthRepresentationImpliesPlanarRing := true
  actualMonosaccharideRingsNonplanar := true
  hydrogenInclusionMayMakeStereochemicalPoint := true
  acyclicSelectedAtomsPlacedInPaperPlane := true
  solidBondsMeanAbovePlane := true
  dashedBondsMeanBelowPlane := true
  favoredAcyclicConformerNeedNotHaveAllCarbonsCoplanar := true

inductive SourceMeaning where
  | cyclic (meaning : CyclicConformationMeaning)
  | acyclic (meaning : AcyclicConformationMeaning)
  deriving DecidableEq, Repr

def sourceMeaning? : String → Option SourceMeaning
  | "2carb/2C0gif/057.GIF" => some (.cyclic cyclicMeaning)
  | "2carb/2C0gif/058A.GIF" => acyclicMeanings[0]?.map SourceMeaning.acyclic
  | "2carb/2C0gif/058B.GIF" => acyclicMeanings[1]?.map SourceMeaning.acyclic
  | _ => none

def SourceMeaning.wellFormed : SourceMeaning → Bool
  | .cyclic meaning => meaning.wellFormed
  | .acyclic meaning => meaning.wellFormed

def all_meanings_well_formed : Bool :=
  artifacts.all fun artifact =>
    match sourceMeaning? artifact.data.relativePath with
    | some meaning => meaning.wellFormed
    | none => false

structure VisionReviewedImageMeaning where
  artifactData : Carbohydrate1996ImageAudit.ImageArtifactData
  sourcePages : List String
  sourceMeaning : Option SourceMeaning
  rule : ConformationRule
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
        rule := conformationRule
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
    visionReviewedGraphLevelBatch.entries.length = 3 := by
  rw [visionReviewedGraphLevelBatch.entries_length, provision_count]

/-! ## Exact advance from the prior 1,652/556 overlay -/

def remainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  priorRemainingImageRows.drop 3

@[simp] theorem remaining_image_count : remainingImageRows.length = 382 := by
  simp [remainingImageRows, priorRemainingImageRows]

theorem rows_append_remaining_eq_prior :
    rows ++ remainingImageRows = priorRemainingImageRows := by
  exact List.take_append_drop 3 priorRemainingImageRows

def advancedMaterializedProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorCarbohydrateMillsDepictionImageSourceMeanings.advancedMaterializedProvisions ++
    provisions

def advancedMaterializedBatch :
    GlobalNonDescriptorSourceMeaningBatch advancedMaterializedProvisions :=
  GlobalNonDescriptorCarbohydrateMillsDepictionImageSourceMeanings.advancedMaterializedBatch.append
    visionReviewedGraphLevelBatch

@[simp] theorem advanced_materialized_count : advancedMaterializedProvisions.length = 1655 := by
  simp [advancedMaterializedProvisions]

def advancedMissingProvisions : List IUPACNormativeProvision :=
  sourceProvisions .blueBook2013Appendix3 ++
    remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem advanced_missing_count : advancedMissingProvisions.length = 553 := by
  simp [advancedMissingProvisions]

set_option maxRecDepth 8192 in
theorem selected_then_advanced_missing_perm_prior_missing :
    (provisions ++ advancedMissingProvisions).Perm
      GlobalNonDescriptorCarbohydrateMillsDepictionImageSourceMeanings.advancedMissingProvisions := by
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
    _ = GlobalNonDescriptorCarbohydrateMillsDepictionImageSourceMeanings.advancedMissingProvisions := by
      rfl

theorem mem_prior_missing_iff_selected_or_advanced_missing
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorCarbohydrateMillsDepictionImageSourceMeanings.advancedMissingProvisions ↔
      provision ∈ provisions ∨ provision ∈ advancedMissingProvisions := by
  simpa only [List.mem_append] using
    (selected_then_advanced_missing_perm_prior_missing.mem_iff).symm

private theorem selected_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ provisions) :
    provision ∈ GlobalNonDescriptorCarbohydrateMillsDepictionImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_left _ member)

private theorem advanced_missing_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ advancedMissingProvisions) :
    provision ∈ GlobalNonDescriptorCarbohydrateMillsDepictionImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_right _ member)

private theorem selected_append_advanced_missing_nodup :
    (provisions ++ advancedMissingProvisions).Nodup :=
  GlobalNonDescriptorCarbohydrateMillsDepictionImageSourceMeanings.advanced_missing_nodup.perm
    selected_then_advanced_missing_perm_prior_missing.symm

theorem advanced_missing_nodup : advancedMissingProvisions.Nodup :=
  List.Nodup.of_append_right selected_append_advanced_missing_nodup

private theorem selected_disjoint_advanced_missing :
    provisions.Disjoint advancedMissingProvisions :=
  List.disjoint_of_nodup_append selected_append_advanced_missing_nodup

private theorem prior_materialized_disjoint_selected :
    GlobalNonDescriptorCarbohydrateMillsDepictionImageSourceMeanings.advancedMaterializedProvisions.Disjoint
      provisions := by
  rw [List.disjoint_left]
  intro provision materialized selected
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateMillsDepictionImageSourceMeanings.advanced_materialized_disjoint_missing)
      materialized (selected_subset_prior_missing selected)

theorem advanced_materialized_nodup : advancedMaterializedProvisions.Nodup := by
  exact GlobalNonDescriptorCarbohydrateMillsDepictionImageSourceMeanings.advanced_materialized_nodup.append
    provisions_nodup prior_materialized_disjoint_selected

theorem advanced_materialized_disjoint_missing :
    advancedMaterializedProvisions.Disjoint advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision advanced missing
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateMillsDepictionImageSourceMeanings.advanced_materialized_disjoint_missing)
        priorMaterialized (advanced_missing_subset_prior_missing missing)
  · exact (List.disjoint_left.mp selected_disjoint_advanced_missing) selected missing

theorem reviewed_disjoint_advanced_materialized :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMaterializedProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed advanced
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateMillsDepictionImageSourceMeanings.reviewed_disjoint_advanced_materialized)
        reviewed priorMaterialized
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateMillsDepictionImageSourceMeanings.reviewed_disjoint_advanced_missing)
        reviewed (selected_subset_prior_missing selected)

theorem reviewed_disjoint_advanced_missing :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed missing
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateMillsDepictionImageSourceMeanings.reviewed_disjoint_advanced_missing)
      reviewed (advanced_missing_subset_prior_missing missing)

set_option maxRecDepth 8192 in
theorem mem_reviewed_or_advanced_materialized_or_missing_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions ∨
      provision ∈ advancedMaterializedProvisions ∨
        provision ∈ advancedMissingProvisions ↔
      provision ∈ globalNonDescriptorProvisions := by
  rw [← GlobalNonDescriptorCarbohydrateMillsDepictionImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff]
  rw [mem_prior_missing_iff_selected_or_advanced_missing]
  simp only [advancedMaterializedProvisions, List.mem_append]
  tauto

theorem advanced_live_frontier_counts :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.length = 92 ∧
      advancedMaterializedProvisions.length = 1655 ∧
        advancedMissingProvisions.length = 553 ∧
          92 + 1655 + 553 = 2300 := by
  exact ⟨GlobalNonDescriptorSourceMeaningProgress.reviewed_count,
    advanced_materialized_count, advanced_missing_count, by omega⟩

end GlobalNonDescriptorCarbohydrateConformationImageSourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateConformationImageSourceMeanings.frozen_artifact_data_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateConformationImageSourceMeanings.acyclic_meanings_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateConformationImageSourceMeanings.visionReviewedGraphLevelBatch
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateConformationImageSourceMeanings.selected_then_advanced_missing_perm_prior_missing
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateConformationImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff
