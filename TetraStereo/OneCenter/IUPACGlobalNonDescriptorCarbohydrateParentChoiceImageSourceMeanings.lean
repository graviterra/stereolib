import TetraStereo.OneCenter.IUPACGlobalNonDescriptorMaterializedSourceMeaningProgress
import TetraStereo.KernelOnly

set_option autoImplicit false















namespace TetraStereo.OneCenter

namespace Carbohydrate1996ImageAudit

inductive FischerHorizontalSide where
  | left | right
  deriving DecidableEq, Repr

inductive FischerOxygenSubstituent where
  | hydroxy | methoxy | acetoxy
  deriving DecidableEq, Repr

structure FischerSubstituent where
  locant : Nat
  oxygenGroup : FischerOxygenSubstituent
  horizontalSide : FischerHorizontalSide
  deriving DecidableEq, Repr

/-- Hydrogens opposite the listed horizontal oxygen groups are implicit. -/
structure FischerProjection where
  carbonCount : Nat
  carbonylLocant? : Option Nat := none
  substituents : List FischerSubstituent
  hydroxymethylTermini : Bool := true
  deriving DecidableEq, Repr

def FischerSubstituent.wellFormedFor
    (substituent : FischerSubstituent) (carbonCount : Nat) : Bool :=
  1 < substituent.locant && substituent.locant < carbonCount

def FischerProjection.wellFormed (projection : FischerProjection) : Bool :=
  decide (2 ≤ projection.carbonCount) &&
    projection.substituents.all (FischerSubstituent.wellFormedFor · projection.carbonCount) &&
    decide (projection.substituents.map FischerSubstituent.locant).Nodup &&
    match projection.carbonylLocant? with
    | none => true
    | some locant =>
        0 < locant && locant ≤ projection.carbonCount &&
          decide (locant ∉ projection.substituents.map FischerSubstituent.locant)

def lGlucitolFischerProjection : FischerProjection :=
  { carbonCount := 6
    substituents :=
      [ ⟨2, .hydroxy, .left⟩, ⟨3, .hydroxy, .right⟩
      , ⟨4, .hydroxy, .left⟩, ⟨5, .hydroxy, .left⟩ ] }

def lErythroLGlucNon5UloseFischerProjection : FischerProjection :=
  { carbonCount := 9
    carbonylLocant? := some 5
    substituents :=
      [ ⟨2, .hydroxy, .left⟩, ⟨3, .hydroxy, .right⟩, ⟨4, .hydroxy, .right⟩
      , ⟨6, .hydroxy, .left⟩, ⟨7, .hydroxy, .right⟩, ⟨8, .hydroxy, .right⟩ ] }

def fourOMethylDXylitolFischerProjection : FischerProjection :=
  { carbonCount := 5
    substituents :=
      [ ⟨2, .hydroxy, .right⟩, ⟨3, .hydroxy, .left⟩, ⟨4, .methoxy, .right⟩ ] }

def twoThreeFiveTriOMethylDMannitolFischerProjection : FischerProjection :=
  { carbonCount := 6
    substituents :=
      [ ⟨2, .methoxy, .left⟩, ⟨3, .methoxy, .left⟩
      , ⟨4, .hydroxy, .right⟩, ⟨5, .methoxy, .right⟩ ] }

def twoOAcetylFiveOMethylDMannitolFischerProjection : FischerProjection :=
  { carbonCount := 6
    substituents :=
      [ ⟨2, .acetoxy, .left⟩, ⟨3, .hydroxy, .left⟩
      , ⟨4, .hydroxy, .right⟩, ⟨5, .methoxy, .right⟩ ] }

end Carbohydrate1996ImageAudit

namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings

open GlobalNonDescriptorSourceMeaningConstructor

def oldPendingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  Carbohydrate1996ImageAudit.Provision.notTranscribed



def rows : List Carbohydrate1996ImageAudit.Provision :=
  (oldPendingImageRows.take 6).drop 1

def artifactOf : Carbohydrate1996ImageAudit.Provision →
    Carbohydrate1996ImageAudit.ImageArtifact
  | .imageArtifact artifact => artifact

def artifacts : List Carbohydrate1996ImageAudit.ImageArtifact := rows.map artifactOf

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem row_count : rows.length = 5 := by
  simp [rows, oldPendingImageRows]

@[simp] theorem artifact_count : artifacts.length = 5 := by simp [artifacts]
@[simp] theorem provision_count : provisions.length = 5 := by simp [provisions]

set_option maxRecDepth 4096 in
@[simp] theorem frozen_artifact_data_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.data =
      [ ⟨"2carb/2C0gif/0222A.GIF",
          "134681f30231cee586666780e670aeb0aa595999e0a99a6d9efc425d06edee6e",
          .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/0222B.GIF",
          "a74a4a686a3805f9f00bb4020cf870d305809a59373a42570eee2ac4a4c17502",
          .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/02231.GIF",
          "e23160d9131287fb5dd55b1559e307517dc05bb7b35103c4ddff4a55e36feec2",
          .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/02232.GIF",
          "a5840dbbc65bee1c705a7d48fe86882e74bfdc0d2848ca189980dc72aa3228e5",
          .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/02233.GIF",
          "412479b33f6e353556f4858f4672ce61cbd9ded4f98e6f97e980ea2689a491c9",
          .numberedOrChartStructure⟩ ] := by
  decide

set_option maxRecDepth 4096 in
@[simp] theorem source_pages_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      [["02.html"], ["02.html"], ["02.html"], ["02.html"], ["02.html"]] := by
  decide

set_option maxRecDepth 8192 in
private theorem rows_nodup : rows.Nodup := by
  have pendingNodup : oldPendingImageRows.Nodup := by
    change (Carbohydrate1996ImageAudit.Provision.all.filter fun provision =>
      !Carbohydrate1996ImageAudit.Provision.symbolicTemplateTranscribed provision).Nodup
    exact Carbohydrate1996ImageAudit.Provision.all_nodup.filter _
  have firstSixNodup : (oldPendingImageRows.take 6).Nodup := pendingNodup.take
  exact firstSixNodup.drop

theorem provisions_nodup : provisions.Nodup := by
  exact rows_nodup.map (by intro left right equal; cases equal; rfl)

inductive ParentChoiceRule where
  | alphabeticallyFirstParentName
  | preferDOverL
  | lowestSetOfSubstituentLocants
  | lowestLocantForFirstAlphabeticalSubstituent
  deriving DecidableEq, Repr

structure SourceExampleMeaning where
  preferredName : String
  rejectedName : String
  choiceRule : ParentChoiceRule
  fischerProjection : Carbohydrate1996ImageAudit.FischerProjection
  deriving DecidableEq, Repr

def expectedSourceMeanings : List SourceExampleMeaning :=
  [ { preferredName := "L-glucitol"
      rejectedName := "D-gulitol"
      choiceRule := .alphabeticallyFirstParentName
      fischerProjection := Carbohydrate1996ImageAudit.lGlucitolFischerProjection }
  , { preferredName := "L-erythro-L-gluco-non-5-ulose"
      rejectedName := "D-threo-D-allo-non-5-ulose"
      choiceRule := .alphabeticallyFirstParentName
      fischerProjection := Carbohydrate1996ImageAudit.lErythroLGlucNon5UloseFischerProjection }
  , { preferredName := "4-O-methyl-D-xylitol"
      rejectedName := "2-O-methyl-L-xylitol"
      choiceRule := .preferDOverL
      fischerProjection := Carbohydrate1996ImageAudit.fourOMethylDXylitolFischerProjection }
  , { preferredName := "2,3,5-tri-O-methyl-D-mannitol"
      rejectedName := "2,4,5-tri-O-methyl-D-mannitol"
      choiceRule := .lowestSetOfSubstituentLocants
      fischerProjection := Carbohydrate1996ImageAudit.twoThreeFiveTriOMethylDMannitolFischerProjection }
  , { preferredName := "2-O-acetyl-5-O-methyl-D-mannitol"
      rejectedName := "5-O-acetyl-2-O-methyl-D-mannitol"
      choiceRule := .lowestLocantForFirstAlphabeticalSubstituent
      fischerProjection := Carbohydrate1996ImageAudit.twoOAcetylFiveOMethylDMannitolFischerProjection } ]

@[simp] theorem expected_source_meanings_exact : expectedSourceMeanings =
    [ { preferredName := "L-glucitol"
        rejectedName := "D-gulitol"
        choiceRule := .alphabeticallyFirstParentName
        fischerProjection := Carbohydrate1996ImageAudit.lGlucitolFischerProjection }
    , { preferredName := "L-erythro-L-gluco-non-5-ulose"
        rejectedName := "D-threo-D-allo-non-5-ulose"
        choiceRule := .alphabeticallyFirstParentName
        fischerProjection := Carbohydrate1996ImageAudit.lErythroLGlucNon5UloseFischerProjection }
    , { preferredName := "4-O-methyl-D-xylitol"
        rejectedName := "2-O-methyl-L-xylitol"
        choiceRule := .preferDOverL
        fischerProjection := Carbohydrate1996ImageAudit.fourOMethylDXylitolFischerProjection }
    , { preferredName := "2,3,5-tri-O-methyl-D-mannitol"
        rejectedName := "2,4,5-tri-O-methyl-D-mannitol"
        choiceRule := .lowestSetOfSubstituentLocants
        fischerProjection := Carbohydrate1996ImageAudit.twoThreeFiveTriOMethylDMannitolFischerProjection }
    , { preferredName := "2-O-acetyl-5-O-methyl-D-mannitol"
        rejectedName := "5-O-acetyl-2-O-methyl-D-mannitol"
        choiceRule := .lowestLocantForFirstAlphabeticalSubstituent
        fischerProjection := Carbohydrate1996ImageAudit.twoOAcetylFiveOMethylDMannitolFischerProjection } ] := rfl

def sourceMeaning? : String → Option SourceExampleMeaning
  | "2carb/2C0gif/0222A.GIF" => expectedSourceMeanings[0]?
  | "2carb/2C0gif/0222B.GIF" => expectedSourceMeanings[1]?
  | "2carb/2C0gif/02231.GIF" => expectedSourceMeanings[2]?
  | "2carb/2C0gif/02232.GIF" => expectedSourceMeanings[3]?
  | "2carb/2C0gif/02233.GIF" => expectedSourceMeanings[4]?
  | _ => none

def every_graph_is_well_formed_and_source_meaning_present : Bool :=
  artifacts.all fun artifact =>
    match sourceMeaning? artifact.data.relativePath with
    | some meaning => meaning.fischerProjection.wellFormed
    | none => false

structure AutomatedVisualReviewData where
  relativePath : String
  sha256 : String
  sourceMeaning : SourceExampleMeaning
  deriving DecidableEq, Repr

def agentVisualReviews : List AutomatedVisualReviewData :=
  List.zipWith (fun artifact meaning =>
    ⟨artifact.data.relativePath, artifact.data.sha256, meaning⟩)
    artifacts expectedSourceMeanings

def automated_visual_review_paths_and_digests_exact : Bool :=
  decide (agentVisualReviews.map (fun review => (review.relativePath, review.sha256)) =
    artifacts.map (fun artifact => (artifact.data.relativePath, artifact.data.sha256)))

structure VisionReviewedFischerMeaning where
  artifactData : Carbohydrate1996ImageAudit.ImageArtifactData
  sourcePages : List String
  sourceMeaning : Option SourceExampleMeaning
  reviewerKind : String
  reviewMethod : String
  reviewLimitations : String
  deriving DecidableEq, Repr

def visionReviewedFischerMeaning
    (row : Carbohydrate1996ImageAudit.Provision) : VisionReviewedFischerMeaning :=
  match row with
  | .imageArtifact artifact =>
      { artifactData := artifact.data
        sourcePages := artifact.sourcePages
        sourceMeaning := sourceMeaning? artifact.data.relativePath
        reviewerKind := "visionAutomated"
        reviewMethod := "record-824ebd8a0c17aacf0b0f018c167d02e2"
        reviewLimitations := "automated-record-dea0f86743dc0740de4fb10ba17511a4" }

def visionReviewedGraphLevelBatch :
    GlobalNonDescriptorSourceMeaningBatch provisions := by
  simpa [provisions] using
    GlobalNonDescriptorIndexedSourceData.totalMeaningBatch rows
      IUPACNormativeProvision.carbohydrate1996ImageArtifact
      visionReviewedFischerMeaning (by intro _row; rfl)

@[simp] theorem vision_reviewed_entry_count :
    visionReviewedGraphLevelBatch.entries.length = 5 := by
  rw [visionReviewedGraphLevelBatch.entries_length, provision_count]

/-! ## Exact resource-safe overlay on the historical materialized frontier -/

def remainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  oldPendingImageRows.take 1 ++ oldPendingImageRows.drop 6

@[simp] theorem remaining_image_count : remainingImageRows.length = 419 := by
  simp [remainingImageRows, oldPendingImageRows]

set_option maxRecDepth 8192 in
theorem rows_append_remaining_perm_old_pending :
    (rows ++ remainingImageRows).Perm oldPendingImageRows := by
  let firstSix := oldPendingImageRows.take 6
  have splitFirstSix : oldPendingImageRows.take 1 ++ rows = firstSix := by
    have prefixEq : oldPendingImageRows.take 1 = firstSix.take 1 := by
      rw [show firstSix.take 1 = oldPendingImageRows.take (min 1 6) by
        exact List.take_take]
      rfl
    rw [prefixEq]
    exact List.take_append_drop 1 firstSix
  have swapPrefix :
      (rows ++ oldPendingImageRows.take 1).Perm
        (oldPendingImageRows.take 1 ++ rows) :=
    List.perm_append_comm
  calc
    (rows ++ remainingImageRows).Perm
        ((oldPendingImageRows.take 1 ++ rows) ++ oldPendingImageRows.drop 6) := by
          simp only [remainingImageRows, List.append_assoc]
          simpa only [List.append_assoc] using
            swapPrefix.append_right (oldPendingImageRows.drop 6)
    _ = firstSix ++ oldPendingImageRows.drop 6 := by rw [splitFirstSix]
    _ = oldPendingImageRows := by
      change oldPendingImageRows.take 6 ++ oldPendingImageRows.drop 6 = oldPendingImageRows
      exact List.take_append_drop 6 oldPendingImageRows

def effectiveTranscribedImageProvisions : List IUPACNormativeProvision :=
  carbohydrate1996TranscribedImageSemanticsSlice ++ provisions

@[simp] theorem effective_transcribed_image_count :
    effectiveTranscribedImageProvisions.length = 11 := by
  simp [effectiveTranscribedImageProvisions]

def advancedMaterializedProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorMaterializedSourceMeaningProgress.materializedProvisions ++ provisions

def advancedMaterializedBatch :
    GlobalNonDescriptorSourceMeaningBatch advancedMaterializedProvisions :=
  GlobalNonDescriptorMaterializedSourceMeaning.batch.append visionReviewedGraphLevelBatch

@[simp] theorem advanced_materialized_count : advancedMaterializedProvisions.length = 1618 := by
  simp [advancedMaterializedProvisions]

def advancedMissingProvisions : List IUPACNormativeProvision :=
  sourceProvisions .blueBook2013Appendix3 ++
    remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem advanced_missing_count : advancedMissingProvisions.length = 590 := by
  simp [advancedMissingProvisions]

set_option maxRecDepth 8192 in
theorem selected_then_advanced_missing_perm_old_missing :
    (provisions ++ advancedMissingProvisions).Perm
      globalNonDescriptorMissingSourceMeaningProvisions := by
  have imagePermutation := rows_append_remaining_perm_old_pending.map
    IUPACNormativeProvision.carbohydrate1996ImageArtifact
  let remainingProvisions :=
    remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact
  have swapPrefix :
      (provisions ++ sourceProvisions .blueBook2013Appendix3).Perm
        (sourceProvisions .blueBook2013Appendix3 ++ provisions) :=
    List.perm_append_comm
  have reordered :
      (provisions ++ advancedMissingProvisions).Perm
        (sourceProvisions .blueBook2013Appendix3 ++
          (provisions ++
            remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact)) := by
    change (provisions ++
        (sourceProvisions .blueBook2013Appendix3 ++ remainingProvisions)).Perm
      (sourceProvisions .blueBook2013Appendix3 ++
        (provisions ++ remainingProvisions))
    simpa only [List.append_assoc] using swapPrefix.append_right remainingProvisions
  have appendedImagePermutation :
      (sourceProvisions .blueBook2013Appendix3 ++
          (provisions ++
            remainingProvisions)).Perm
        (sourceProvisions .blueBook2013Appendix3 ++
          carbohydrate1996UntranscribedImageSourceSlice) := by
    apply List.Perm.append_left
    simpa [provisions, remainingProvisions, carbohydrate1996UntranscribedImageSourceSlice,
      oldPendingImageRows, List.map_append] using imagePermutation
  simpa [globalNonDescriptorMissingSourceMeaningProvisions] using
    reordered.trans appendedImagePermutation

theorem mem_old_missing_iff_selected_or_advanced_missing
    (provision : IUPACNormativeProvision) :
    provision ∈ globalNonDescriptorMissingSourceMeaningProvisions ↔
      provision ∈ provisions ∨ provision ∈ advancedMissingProvisions := by
  simpa only [List.mem_append] using
    (selected_then_advanced_missing_perm_old_missing.mem_iff).symm

private theorem selected_subset_old_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ provisions) :
    provision ∈ globalNonDescriptorMissingSourceMeaningProvisions :=
  selected_then_advanced_missing_perm_old_missing.mem_iff.mp
    (List.mem_append_left _ member)

private theorem advanced_missing_subset_old_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ advancedMissingProvisions) :
    provision ∈ globalNonDescriptorMissingSourceMeaningProvisions :=
  selected_then_advanced_missing_perm_old_missing.mem_iff.mp
    (List.mem_append_right _ member)

private theorem selected_append_advanced_missing_nodup :
    (provisions ++ advancedMissingProvisions).Nodup :=
  globalNonDescriptorMissingSourceMeaningProvisions_nodup.perm
    selected_then_advanced_missing_perm_old_missing.symm

theorem advanced_missing_nodup : advancedMissingProvisions.Nodup :=
  List.Nodup.of_append_right selected_append_advanced_missing_nodup

private theorem selected_disjoint_advanced_missing :
    provisions.Disjoint advancedMissingProvisions :=
  List.disjoint_of_nodup_append selected_append_advanced_missing_nodup

private theorem old_materialized_disjoint_old_missing :
    GlobalNonDescriptorMaterializedSourceMeaningProgress.materializedProvisions.Disjoint
      globalNonDescriptorMissingSourceMeaningProvisions := by
  rw [List.disjoint_left]
  intro provision materialized missing
  have residual :=
    GlobalNonDescriptorMaterializedSourceMeaningProgress.materialized_subset_residual materialized
  exact (List.disjoint_left.mp
    GlobalNonDescriptorSourceMeaningProgress.residual_disjoint_missing) residual missing

private theorem old_materialized_disjoint_selected :
    GlobalNonDescriptorMaterializedSourceMeaningProgress.materializedProvisions.Disjoint
      provisions := by
  rw [List.disjoint_left]
  intro provision materialized selected
  exact (List.disjoint_left.mp old_materialized_disjoint_old_missing)
    materialized (selected_subset_old_missing selected)

theorem advanced_materialized_nodup : advancedMaterializedProvisions.Nodup := by
  exact GlobalNonDescriptorMaterializedSourceMeaningProgress.materialized_nodup.append
    provisions_nodup old_materialized_disjoint_selected

theorem advanced_materialized_disjoint_missing :
    advancedMaterializedProvisions.Disjoint advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision advanced missing
  rcases List.mem_append.mp advanced with oldMaterialized | selected
  · exact (List.disjoint_left.mp old_materialized_disjoint_old_missing)
      oldMaterialized (advanced_missing_subset_old_missing missing)
  · exact (List.disjoint_left.mp selected_disjoint_advanced_missing) selected missing

theorem reviewed_disjoint_advanced_materialized :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMaterializedProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed advanced
  rcases List.mem_append.mp advanced with oldMaterialized | selected
  · have residual :=
      GlobalNonDescriptorMaterializedSourceMeaningProgress.materialized_subset_residual
        oldMaterialized
    exact (List.disjoint_left.mp
      GlobalNonDescriptorSourceMeaningProgress.reviewed_disjoint_residual) reviewed residual
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorSourceMeaningProgress.reviewed_disjoint_missing)
        reviewed (selected_subset_old_missing selected)

theorem reviewed_disjoint_advanced_missing :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed missing
  exact (List.disjoint_left.mp
    GlobalNonDescriptorSourceMeaningProgress.reviewed_disjoint_missing)
      reviewed (advanced_missing_subset_old_missing missing)

set_option maxRecDepth 8192 in
theorem mem_reviewed_or_advanced_materialized_or_missing_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions ∨
      provision ∈ advancedMaterializedProvisions ∨
        provision ∈ advancedMissingProvisions ↔
      provision ∈ globalNonDescriptorProvisions := by
  have oldFrontier :=
    TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaningProgress.mem_reviewed_or_materialized_or_remaining_or_missing_iff
      provision
  simp only [TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorMaterializedSourceMeaningProgress.remainingPartiallyFormalizedProvisions,
    List.not_mem_nil] at oldFrontier
  rw [← oldFrontier, mem_old_missing_iff_selected_or_advanced_missing]
  simp only [advancedMaterializedProvisions, List.mem_append]
  tauto

theorem advanced_live_frontier_counts :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.length = 92 ∧
      advancedMaterializedProvisions.length = 1618 ∧
        advancedMissingProvisions.length = 590 ∧
          92 + 1618 + 590 = 2300 := by
  exact ⟨GlobalNonDescriptorSourceMeaningProgress.reviewed_count,
    advanced_materialized_count, advanced_missing_count, by omega⟩

end GlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings.frozen_artifact_data_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings.source_pages_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings.visionReviewedGraphLevelBatch
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings.selected_then_advanced_missing_perm_old_missing
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateParentChoiceImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff
