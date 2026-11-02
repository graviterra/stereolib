import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings
import TetraStereo.KernelOnly

set_option autoImplicit false














namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateAnomerMixtureImageSourceMeanings

open GlobalNonDescriptorSourceMeaningConstructor
open GlobalNonDescriptorCarbohydrateHaworthImageSourceMeanings

def priorRemainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  GlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings.remainingImageRows

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
      [ ⟨"2carb/2C0gif/063A.GIF", "f907f3dc060456bb63b0c3eff8c30063f26ddee147ac2e3957a97b6b786e0ea6", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/063B.GIF", "0e6b9d79b5bde08b6d3d881f7dc570a53d6bb1493f8035d1d55a6982d11bdd44", .numberedOrChartStructure⟩ ] := by
  decide

set_option maxRecDepth 4096 in
@[simp] theorem source_pages_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 2 ["06n07.html"] := by
  decide

set_option maxRecDepth 4096 in
private theorem rows_nodup : rows.Nodup := by
  decide

theorem provisions_nodup : provisions.Nodup := by
  exact rows_nodup.map (by intro left right equal; cases equal; rfl)

inductive AnomericLigand where
  | hydrogen | hydroxyl | hydroxymethyl (carbonLocant : Nat)
  deriving DecidableEq, Repr

inductive MixtureRenderingKind where
  | ligandsSeparatedFromAlphaAndBetaBonds
  | wavyAnomericBond
  deriving DecidableEq, Repr

structure MixtureRendering where
  panelLabel : String
  kind : MixtureRenderingKind
  deriving DecidableEq, Repr

structure AnomerMixtureMeaning where
  publishedName : String
  anomersPresent : List GlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings.Anomer
  anomericCarbonLocant : Nat
  ringOxygenSourceLocant : Nat
  ringSize : Nat
  anomericLigands : List AnomericLigand
  fixedRingSubstituents : List RingSubstituent
  renderings : List MixtureRendering
  deriving DecidableEq, Repr

def meanings : List AnomerMixtureMeaning :=
  [ { publishedName := "alpha,beta-D-glucopyranose"
      anomersPresent := [.alpha, .beta]
      anomericCarbonLocant := 1, ringOxygenSourceLocant := 5, ringSize := 6
      anomericLigands := [.hydrogen, .hydroxyl]
      fixedRingSubstituents :=
        [ ⟨2, .hydroxyl, .below⟩, ⟨3, .hydroxyl, .above⟩
        , ⟨4, .hydroxyl, .below⟩, ⟨5, .hydroxymethyl 6, .above⟩ ]
      renderings :=
        [⟨"a", .ligandsSeparatedFromAlphaAndBetaBonds⟩, ⟨"b", .wavyAnomericBond⟩] }
  , { publishedName := "alpha,beta-D-fructofuranose 6-phosphate"
      anomersPresent := [.alpha, .beta]
      anomericCarbonLocant := 2, ringOxygenSourceLocant := 5, ringSize := 5
      anomericLigands := [.hydroxymethyl 1, .hydroxyl]
      fixedRingSubstituents :=
        [ ⟨3, .hydroxyl, .above⟩, ⟨4, .hydroxyl, .below⟩
        , ⟨5, .phosphorylatedHydroxymethyl 6, .above⟩ ]
      renderings :=
        [⟨"c", .ligandsSeparatedFromAlphaAndBetaBonds⟩, ⟨"d", .wavyAnomericBond⟩] } ]

@[simp] theorem meanings_exact : meanings =
    [ { publishedName := "alpha,beta-D-glucopyranose"
        anomersPresent := [.alpha, .beta]
        anomericCarbonLocant := 1, ringOxygenSourceLocant := 5, ringSize := 6
        anomericLigands := [.hydrogen, .hydroxyl]
        fixedRingSubstituents :=
          [ ⟨2, .hydroxyl, .below⟩, ⟨3, .hydroxyl, .above⟩
          , ⟨4, .hydroxyl, .below⟩, ⟨5, .hydroxymethyl 6, .above⟩ ]
        renderings :=
          [⟨"a", .ligandsSeparatedFromAlphaAndBetaBonds⟩, ⟨"b", .wavyAnomericBond⟩] }
    , { publishedName := "alpha,beta-D-fructofuranose 6-phosphate"
        anomersPresent := [.alpha, .beta]
        anomericCarbonLocant := 2, ringOxygenSourceLocant := 5, ringSize := 5
        anomericLigands := [.hydroxymethyl 1, .hydroxyl]
        fixedRingSubstituents :=
          [ ⟨3, .hydroxyl, .above⟩, ⟨4, .hydroxyl, .below⟩
          , ⟨5, .phosphorylatedHydroxymethyl 6, .above⟩ ]
        renderings :=
          [⟨"c", .ligandsSeparatedFromAlphaAndBetaBonds⟩, ⟨"d", .wavyAnomericBond⟩] } ] := rfl

def AnomerMixtureMeaning.wellFormed (meaning : AnomerMixtureMeaning) : Bool :=
  meaning.anomersPresent = [.alpha, .beta] &&
    meaning.ringSize = meaning.ringOxygenSourceLocant - meaning.anomericCarbonLocant + 2 &&
      meaning.anomericCarbonLocant < meaning.ringOxygenSourceLocant &&
        meaning.anomericLigands.length = 2 && meaning.anomericLigands.Nodup &&
          meaning.fixedRingSubstituents.Nodup &&
            (meaning.renderings.map MixtureRendering.kind) =
              [.ligandsSeparatedFromAlphaAndBetaBonds, .wavyAnomericBond] &&
              meaning.renderings.all (fun rendering => !rendering.panelLabel.isEmpty) &&
                !meaning.publishedName.isEmpty

structure MixtureRule where
  sameRingSizeRequired : Bool
  nameUsesAlphaCommaBetaPrefix : Bool
  formulaMaySeparateLigandsFromBothAnomericBonds : Bool
  formulaMayUseWavyAnomericBond : Bool
  wavyBondEspeciallyUsefulWhenHydrogensOmitted : Bool
  solutionMixturesAreEquilibratingTautomers : Bool
  deriving DecidableEq, Repr

def mixtureRule : MixtureRule where
  sameRingSizeRequired := true
  nameUsesAlphaCommaBetaPrefix := true
  formulaMaySeparateLigandsFromBothAnomericBonds := true
  formulaMayUseWavyAnomericBond := true
  wavyBondEspeciallyUsefulWhenHydrogensOmitted := true
  solutionMixturesAreEquilibratingTautomers := true

def sourceMeaning? : String → Option AnomerMixtureMeaning
  | "2carb/2C0gif/063A.GIF" => meanings[0]?
  | "2carb/2C0gif/063B.GIF" => meanings[1]?
  | _ => none

def all_meanings_well_formed : Bool :=
  artifacts.all fun artifact =>
    match sourceMeaning? artifact.data.relativePath with
    | some meaning => meaning.wellFormed
    | none => false

structure VisionReviewedImageMeaning where
  artifactData : Carbohydrate1996ImageAudit.ImageArtifactData
  sourcePages : List String
  sourceMeaning : Option AnomerMixtureMeaning
  rule : MixtureRule
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
        rule := mixtureRule
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

/-! ## Exact advance from the prior 1,663/545 overlay -/

def remainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  priorRemainingImageRows.drop 2

@[simp] theorem remaining_image_count : remainingImageRows.length = 372 := by
  simp [remainingImageRows, priorRemainingImageRows]

theorem rows_append_remaining_eq_prior :
    rows ++ remainingImageRows = priorRemainingImageRows := by
  exact List.take_append_drop 2 priorRemainingImageRows

def advancedMaterializedProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings.advancedMaterializedProvisions ++
    provisions

def advancedMaterializedBatch :
    GlobalNonDescriptorSourceMeaningBatch advancedMaterializedProvisions :=
  GlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings.advancedMaterializedBatch.append
    visionReviewedGraphLevelBatch

@[simp] theorem advanced_materialized_count : advancedMaterializedProvisions.length = 1665 := by
  simp [advancedMaterializedProvisions]

def advancedMissingProvisions : List IUPACNormativeProvision :=
  sourceProvisions .blueBook2013Appendix3 ++
    remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem advanced_missing_count : advancedMissingProvisions.length = 543 := by
  simp [advancedMissingProvisions]

set_option maxRecDepth 8192 in
theorem selected_then_advanced_missing_perm_prior_missing :
    (provisions ++ advancedMissingProvisions).Perm
      GlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings.advancedMissingProvisions := by
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
    _ = GlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings.advancedMissingProvisions := by
      rfl

theorem mem_prior_missing_iff_selected_or_advanced_missing
    (provision : IUPACNormativeProvision) :
    provision ∈
        GlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings.advancedMissingProvisions ↔
      provision ∈ provisions ∨ provision ∈ advancedMissingProvisions := by
  simpa only [List.mem_append] using
    (selected_then_advanced_missing_perm_prior_missing.mem_iff).symm

private theorem selected_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ provisions) :
    provision ∈
      GlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_left _ member)

private theorem advanced_missing_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ advancedMissingProvisions) :
    provision ∈
      GlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_right _ member)

private theorem selected_append_advanced_missing_nodup :
    (provisions ++ advancedMissingProvisions).Nodup :=
  GlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings.advanced_missing_nodup.perm
    selected_then_advanced_missing_perm_prior_missing.symm

theorem advanced_missing_nodup : advancedMissingProvisions.Nodup :=
  List.Nodup.of_append_right selected_append_advanced_missing_nodup

private theorem selected_disjoint_advanced_missing :
    provisions.Disjoint advancedMissingProvisions :=
  List.disjoint_of_nodup_append selected_append_advanced_missing_nodup

private theorem prior_materialized_disjoint_selected :
    GlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings.advancedMaterializedProvisions.Disjoint
      provisions := by
  rw [List.disjoint_left]
  intro provision materialized selected
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings.advanced_materialized_disjoint_missing)
      materialized (selected_subset_prior_missing selected)

theorem advanced_materialized_nodup : advancedMaterializedProvisions.Nodup := by
  exact GlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings.advanced_materialized_nodup.append
    provisions_nodup prior_materialized_disjoint_selected

theorem advanced_materialized_disjoint_missing :
    advancedMaterializedProvisions.Disjoint advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision advanced missing
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings.advanced_materialized_disjoint_missing)
        priorMaterialized (advanced_missing_subset_prior_missing missing)
  · exact (List.disjoint_left.mp selected_disjoint_advanced_missing) selected missing

theorem reviewed_disjoint_advanced_materialized :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMaterializedProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed advanced
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings.reviewed_disjoint_advanced_materialized)
        reviewed priorMaterialized
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings.reviewed_disjoint_advanced_missing)
        reviewed (selected_subset_prior_missing selected)

theorem reviewed_disjoint_advanced_missing :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed missing
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings.reviewed_disjoint_advanced_missing)
      reviewed (advanced_missing_subset_prior_missing missing)

set_option maxRecDepth 8192 in
theorem mem_reviewed_or_advanced_materialized_or_missing_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions ∨
      provision ∈ advancedMaterializedProvisions ∨
        provision ∈ advancedMissingProvisions ↔
      provision ∈ globalNonDescriptorProvisions := by
  rw [← GlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff]
  rw [mem_prior_missing_iff_selected_or_advanced_missing]
  simp only [advancedMaterializedProvisions, List.mem_append]
  tauto

theorem advanced_live_frontier_counts :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.length = 92 ∧
      advancedMaterializedProvisions.length = 1665 ∧
        advancedMissingProvisions.length = 543 ∧
          92 + 1665 + 543 = 2300 := by
  exact ⟨GlobalNonDescriptorSourceMeaningProgress.reviewed_count,
    advanced_materialized_count, advanced_missing_count, by omega⟩

end GlobalNonDescriptorCarbohydrateAnomerMixtureImageSourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAnomerMixtureImageSourceMeanings.frozen_artifact_data_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAnomerMixtureImageSourceMeanings.meanings_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAnomerMixtureImageSourceMeanings.visionReviewedGraphLevelBatch
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAnomerMixtureImageSourceMeanings.selected_then_advanced_missing_perm_prior_missing
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAnomerMixtureImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff
