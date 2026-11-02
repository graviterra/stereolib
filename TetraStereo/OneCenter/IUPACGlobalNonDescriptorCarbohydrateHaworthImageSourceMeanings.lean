import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateModifiedFischerImageSourceMeanings
import TetraStereo.KernelOnly

set_option autoImplicit false














namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateHaworthImageSourceMeanings

open GlobalNonDescriptorSourceMeaningConstructor

def priorRemainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  GlobalNonDescriptorCarbohydrateModifiedFischerImageSourceMeanings.remainingImageRows

def rows : List Carbohydrate1996ImageAudit.Provision := priorRemainingImageRows.take 9

def artifactOf : Carbohydrate1996ImageAudit.Provision →
    Carbohydrate1996ImageAudit.ImageArtifact
  | .imageArtifact artifact => artifact

def artifacts : List Carbohydrate1996ImageAudit.ImageArtifact := rows.map artifactOf

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem row_count : rows.length = 9 := by
  simp [rows, priorRemainingImageRows]

@[simp] theorem artifact_count : artifacts.length = 9 := by simp [artifacts]
@[simp] theorem provision_count : provisions.length = 9 := by simp [provisions]

set_option maxRecDepth 4096 in
@[simp] theorem frozen_artifact_data_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.data =
      [ ⟨"2carb/2C0gif/054A.GIF", "dadb8127444a18df1bab69142d2793390853fa178088753ad628cf13b058c4a3", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/054B.GIF", "c0d11aca33301fa3cc0ddf4df8b2e120be6ca531ccb699afd94cc148792c85b9", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/054C.GIF", "22aeca3e142f2f26c5303d9662b7291434273595ddab8cc52e3daa5b0c8d2de8", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/054D.GIF", "d075cf8fa3657a65a5e1cb3fa9fb38e6f06846a08cd30fb209dd155a85bced58", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/054E.GIF", "161f55046fe8a2abcc506236df9311fbf68a57e9dd3a0320f723bfa24f33fad7", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/054F.GIF", "cd7e14c320748dc182ad5990dbccf1f2a00af5ce71c475f05fc27be6f817d2e2", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/054G.GIF", "7ecee305bfee4810c6f7c2d09578ca72e3230b1c82402547cf1925d4c6d7eb67", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/054H.GIF", "57d0b124dc0c81270d5e749f5122731454c7849f29fdcc2f837151e61c39bd19", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/054I.GIF", "7b2a89d0f0fa2798040155f845667af073f2a8ff38e0c416e97c216fc961b88c", .numberedOrChartStructure⟩ ] := by
  decide

set_option maxRecDepth 4096 in
@[simp] theorem source_pages_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 9 ["05.html"] := by
  decide

def officialErrataPages : List String := ["er054.html"]

set_option maxRecDepth 4096 in
private theorem rows_nodup : rows.Nodup := by
  decide

theorem provisions_nodup : provisions.Nodup := by
  exact rows_nodup.map (by intro left right equal; cases equal; rfl)

inductive Anomer where
  | alpha | beta
  deriving DecidableEq, Repr

inductive RingFace where
  | above | below
  deriving DecidableEq, Repr

inductive HaworthGroup where
  | hydroxyl
  | methoxy
  | hydroxymethyl (carbonLocant : Nat)
  | phosphorylatedHydroxymethyl (carbonLocant : Nat)
  | remainingCarbonChain (firstLocant terminalLocant : Nat)
  deriving DecidableEq, Repr

structure RingSubstituent where
  attachedAtLocant : Nat
  group : HaworthGroup
  face : RingFace
  deriving DecidableEq, Repr

structure HaworthMeaning where
  publishedName : String
  anomer : Option Anomer
  series : GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.ConfigurationalSeries
  anomericCarbonLocant : Nat
  ringOxygenSourceLocant : Nat
  ringSize : Nat
  ringSubstituents : List RingSubstituent
  showsFischerToHaworthDerivation : Bool
  explicitRingHydrogensIncluded : Bool
  erratum? : Option String
  deriving DecidableEq, Repr

def meanings : List HaworthMeaning :=
  [ { publishedName := "Haworth representation of D-glucopyranose"
      anomer := none, series := .D, anomericCarbonLocant := 1
      ringOxygenSourceLocant := 5, ringSize := 6
      ringSubstituents :=
        [ ⟨2, .hydroxyl, .below⟩, ⟨3, .hydroxyl, .above⟩, ⟨4, .hydroxyl, .below⟩
        , ⟨5, .hydroxymethyl 6, .above⟩ ]
      showsFischerToHaworthDerivation := true
      explicitRingHydrogensIncluded := true, erratum? := none }
  , { publishedName := "beta-L-arabinofuranose"
      anomer := some .beta, series := .L, anomericCarbonLocant := 1
      ringOxygenSourceLocant := 4, ringSize := 5
      ringSubstituents :=
        [ ⟨1, .hydroxyl, .below⟩, ⟨2, .hydroxyl, .below⟩, ⟨3, .hydroxyl, .above⟩
        , ⟨4, .hydroxymethyl 5, .below⟩ ]
      showsFischerToHaworthDerivation := true
      explicitRingHydrogensIncluded := true, erratum? := none }
  , { publishedName := "beta-D-ribopyranose"
      anomer := some .beta, series := .D, anomericCarbonLocant := 1
      ringOxygenSourceLocant := 5, ringSize := 6
      ringSubstituents :=
        [ ⟨1, .hydroxyl, .above⟩, ⟨2, .hydroxyl, .below⟩
        , ⟨3, .hydroxyl, .below⟩, ⟨4, .hydroxyl, .below⟩ ]
      showsFischerToHaworthDerivation := false
      explicitRingHydrogensIncluded := true, erratum? := none }
  , { publishedName := "beta-D-ribofuranose 5-phosphate"
      anomer := some .beta, series := .D, anomericCarbonLocant := 1
      ringOxygenSourceLocant := 4, ringSize := 5
      ringSubstituents :=
        [ ⟨1, .hydroxyl, .above⟩, ⟨2, .hydroxyl, .below⟩
        , ⟨3, .hydroxyl, .below⟩, ⟨4, .phosphorylatedHydroxymethyl 5, .above⟩ ]
      showsFischerToHaworthDerivation := false
      explicitRingHydrogensIncluded := true, erratum? := none }
  , { publishedName := "alpha-D-fructopyranose"
      anomer := some .alpha, series := .D, anomericCarbonLocant := 2
      ringOxygenSourceLocant := 6, ringSize := 6
      ringSubstituents :=
        [ ⟨2, .hydroxymethyl 1, .above⟩, ⟨2, .hydroxyl, .below⟩
        , ⟨3, .hydroxyl, .above⟩, ⟨4, .hydroxyl, .below⟩
        , ⟨5, .hydroxyl, .below⟩ ]
      showsFischerToHaworthDerivation := true
      explicitRingHydrogensIncluded := true, erratum? := none }
  , { publishedName := "alpha-D-fructofuranose 1,6-bisphosphate"
      anomer := some .alpha, series := .D, anomericCarbonLocant := 2
      ringOxygenSourceLocant := 5, ringSize := 5
      ringSubstituents :=
        [ ⟨2, .phosphorylatedHydroxymethyl 1, .above⟩, ⟨2, .hydroxyl, .below⟩
        , ⟨3, .hydroxyl, .above⟩, ⟨4, .hydroxyl, .below⟩
        , ⟨5, .phosphorylatedHydroxymethyl 6, .above⟩ ]
      showsFischerToHaworthDerivation := false
      explicitRingHydrogensIncluded := true, erratum? := none }
  , { publishedName := "methyl alpha-D-glucoseptanoside"
      anomer := some .alpha, series := .D, anomericCarbonLocant := 1
      ringOxygenSourceLocant := 6, ringSize := 7
      ringSubstituents :=
        [ ⟨1, .methoxy, .below⟩, ⟨2, .hydroxyl, .below⟩
        , ⟨3, .hydroxyl, .above⟩, ⟨4, .hydroxyl, .below⟩
        , ⟨5, .hydroxyl, .below⟩ ]
      showsFischerToHaworthDerivation := true
      explicitRingHydrogensIncluded := true
      erratum? := some "right-hand structure omits the H from the OH at C3" }
  , { publishedName := "methyl alpha-L-altrooxetoside"
      anomer := some .alpha, series := .L, anomericCarbonLocant := 1
      ringOxygenSourceLocant := 3, ringSize := 4
      ringSubstituents :=
        [ ⟨1, .methoxy, .above⟩, ⟨2, .hydroxyl, .below⟩
        , ⟨3, .remainingCarbonChain 4 6, .below⟩ ]
      showsFischerToHaworthDerivation := false
      explicitRingHydrogensIncluded := true, erratum? := none }
  , { publishedName := "methyl beta-D-allooxiroside"
      anomer := some .beta, series := .D, anomericCarbonLocant := 1
      ringOxygenSourceLocant := 2, ringSize := 3
      ringSubstituents :=
        [ ⟨1, .methoxy, .above⟩, ⟨2, .remainingCarbonChain 3 6, .above⟩ ]
      showsFischerToHaworthDerivation := false
      explicitRingHydrogensIncluded := true, erratum? := none } ]

@[simp] theorem meanings_exact : meanings =
    [ { publishedName := "Haworth representation of D-glucopyranose"
        anomer := none, series := .D, anomericCarbonLocant := 1
        ringOxygenSourceLocant := 5, ringSize := 6
        ringSubstituents :=
          [ ⟨2, .hydroxyl, .below⟩, ⟨3, .hydroxyl, .above⟩, ⟨4, .hydroxyl, .below⟩
          , ⟨5, .hydroxymethyl 6, .above⟩ ]
        showsFischerToHaworthDerivation := true
        explicitRingHydrogensIncluded := true, erratum? := none }
    , { publishedName := "beta-L-arabinofuranose"
        anomer := some .beta, series := .L, anomericCarbonLocant := 1
        ringOxygenSourceLocant := 4, ringSize := 5
        ringSubstituents :=
          [ ⟨1, .hydroxyl, .below⟩, ⟨2, .hydroxyl, .below⟩, ⟨3, .hydroxyl, .above⟩
          , ⟨4, .hydroxymethyl 5, .below⟩ ]
        showsFischerToHaworthDerivation := true
        explicitRingHydrogensIncluded := true, erratum? := none }
    , { publishedName := "beta-D-ribopyranose"
        anomer := some .beta, series := .D, anomericCarbonLocant := 1
        ringOxygenSourceLocant := 5, ringSize := 6
        ringSubstituents :=
          [ ⟨1, .hydroxyl, .above⟩, ⟨2, .hydroxyl, .below⟩
          , ⟨3, .hydroxyl, .below⟩, ⟨4, .hydroxyl, .below⟩ ]
        showsFischerToHaworthDerivation := false
        explicitRingHydrogensIncluded := true, erratum? := none }
    , { publishedName := "beta-D-ribofuranose 5-phosphate"
        anomer := some .beta, series := .D, anomericCarbonLocant := 1
        ringOxygenSourceLocant := 4, ringSize := 5
        ringSubstituents :=
          [ ⟨1, .hydroxyl, .above⟩, ⟨2, .hydroxyl, .below⟩
          , ⟨3, .hydroxyl, .below⟩, ⟨4, .phosphorylatedHydroxymethyl 5, .above⟩ ]
        showsFischerToHaworthDerivation := false
        explicitRingHydrogensIncluded := true, erratum? := none }
    , { publishedName := "alpha-D-fructopyranose"
        anomer := some .alpha, series := .D, anomericCarbonLocant := 2
        ringOxygenSourceLocant := 6, ringSize := 6
        ringSubstituents :=
          [ ⟨2, .hydroxymethyl 1, .above⟩, ⟨2, .hydroxyl, .below⟩
          , ⟨3, .hydroxyl, .above⟩, ⟨4, .hydroxyl, .below⟩
          , ⟨5, .hydroxyl, .below⟩ ]
        showsFischerToHaworthDerivation := true
        explicitRingHydrogensIncluded := true, erratum? := none }
    , { publishedName := "alpha-D-fructofuranose 1,6-bisphosphate"
        anomer := some .alpha, series := .D, anomericCarbonLocant := 2
        ringOxygenSourceLocant := 5, ringSize := 5
        ringSubstituents :=
          [ ⟨2, .phosphorylatedHydroxymethyl 1, .above⟩, ⟨2, .hydroxyl, .below⟩
          , ⟨3, .hydroxyl, .above⟩, ⟨4, .hydroxyl, .below⟩
          , ⟨5, .phosphorylatedHydroxymethyl 6, .above⟩ ]
        showsFischerToHaworthDerivation := false
        explicitRingHydrogensIncluded := true, erratum? := none }
    , { publishedName := "methyl alpha-D-glucoseptanoside"
        anomer := some .alpha, series := .D, anomericCarbonLocant := 1
        ringOxygenSourceLocant := 6, ringSize := 7
        ringSubstituents :=
          [ ⟨1, .methoxy, .below⟩, ⟨2, .hydroxyl, .below⟩
          , ⟨3, .hydroxyl, .above⟩, ⟨4, .hydroxyl, .below⟩
          , ⟨5, .hydroxyl, .below⟩ ]
        showsFischerToHaworthDerivation := true
        explicitRingHydrogensIncluded := true
        erratum? := some "right-hand structure omits the H from the OH at C3" }
    , { publishedName := "methyl alpha-L-altrooxetoside"
        anomer := some .alpha, series := .L, anomericCarbonLocant := 1
        ringOxygenSourceLocant := 3, ringSize := 4
        ringSubstituents :=
          [ ⟨1, .methoxy, .above⟩, ⟨2, .hydroxyl, .below⟩
          , ⟨3, .remainingCarbonChain 4 6, .below⟩ ]
        showsFischerToHaworthDerivation := false
        explicitRingHydrogensIncluded := true, erratum? := none }
    , { publishedName := "methyl beta-D-allooxiroside"
        anomer := some .beta, series := .D, anomericCarbonLocant := 1
        ringOxygenSourceLocant := 2, ringSize := 3
        ringSubstituents :=
          [ ⟨1, .methoxy, .above⟩, ⟨2, .remainingCarbonChain 3 6, .above⟩ ]
        showsFischerToHaworthDerivation := false
        explicitRingHydrogensIncluded := true, erratum? := none } ] := rfl

def RingSubstituent.wellFormedFor (meaning : HaworthMeaning)
    (substituent : RingSubstituent) : Bool :=
  meaning.anomericCarbonLocant ≤ substituent.attachedAtLocant &&
    substituent.attachedAtLocant ≤ meaning.ringOxygenSourceLocant &&
      match substituent.group with
      | .hydroxyl | .methoxy => true
      | .hydroxymethyl carbonLocant | .phosphorylatedHydroxymethyl carbonLocant =>
          1 ≤ carbonLocant && carbonLocant ≤ 6
      | .remainingCarbonChain firstLocant terminalLocant =>
          1 ≤ firstLocant && firstLocant ≤ terminalLocant && terminalLocant ≤ 6

def HaworthMeaning.wellFormed (meaning : HaworthMeaning) : Bool :=
  meaning.ringSize = meaning.ringOxygenSourceLocant - meaning.anomericCarbonLocant + 2 &&
    meaning.anomericCarbonLocant < meaning.ringOxygenSourceLocant &&
      3 ≤ meaning.ringSize && meaning.ringSize ≤ 7 &&
        meaning.ringSubstituents.Nodup &&
          meaning.ringSubstituents.all (RingSubstituent.wellFormedFor meaning) &&
            meaning.explicitRingHydrogensIncluded && !meaning.publishedName.isEmpty

structure HaworthRule where
  ringAlmostPerpendicularToPaper : Bool
  oxygenBehindAndC1AtRight : Bool
  standardNumberingClockwise : Bool
  modifiedFischerRightMapsBelow : Bool
  modifiedFischerLeftMapsAbove : Bool
  commonDAldohexoseC6Above : Bool
  explicitRingHydrogensPreferred : Bool
  deriving DecidableEq, Repr

def haworthRule : HaworthRule where
  ringAlmostPerpendicularToPaper := true
  oxygenBehindAndC1AtRight := true
  standardNumberingClockwise := true
  modifiedFischerRightMapsBelow := true
  modifiedFischerLeftMapsAbove := true
  commonDAldohexoseC6Above := true
  explicitRingHydrogensPreferred := true

def sourceMeaning? : String → Option HaworthMeaning
  | "2carb/2C0gif/054A.GIF" => meanings[0]?
  | "2carb/2C0gif/054B.GIF" => meanings[1]?
  | "2carb/2C0gif/054C.GIF" => meanings[2]?
  | "2carb/2C0gif/054D.GIF" => meanings[3]?
  | "2carb/2C0gif/054E.GIF" => meanings[4]?
  | "2carb/2C0gif/054F.GIF" => meanings[5]?
  | "2carb/2C0gif/054G.GIF" => meanings[6]?
  | "2carb/2C0gif/054H.GIF" => meanings[7]?
  | "2carb/2C0gif/054I.GIF" => meanings[8]?
  | _ => none

def all_meanings_well_formed : Bool :=
  artifacts.all fun artifact =>
    match sourceMeaning? artifact.data.relativePath with
    | some meaning => meaning.wellFormed
    | none => false

structure VisionReviewedImageMeaning where
  artifactData : Carbohydrate1996ImageAudit.ImageArtifactData
  sourcePages : List String
  sourceMeaning : Option HaworthMeaning
  rule : HaworthRule
  officialErrataPages : List String
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
        rule := haworthRule
        officialErrataPages := officialErrataPages
        reviewerKind := "visionAutomated"
        reviewMethod := "record-5a9ae93f4573fd6a6e00f93dce28f32c"
        reviewLimitations := "automated-record-dea0f86743dc0740de4fb10ba17511a4" }

def visionReviewedGraphLevelBatch :
    GlobalNonDescriptorSourceMeaningBatch provisions := by
  simpa [provisions] using
    GlobalNonDescriptorIndexedSourceData.totalMeaningBatch rows
      IUPACNormativeProvision.carbohydrate1996ImageArtifact
      visionReviewedImageMeaning (by intro _row; rfl)

@[simp] theorem vision_reviewed_entry_count :
    visionReviewedGraphLevelBatch.entries.length = 9 := by
  rw [visionReviewedGraphLevelBatch.entries_length, provision_count]

/-! ## Exact advance from the prior 1,640/568 overlay -/

def remainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  priorRemainingImageRows.drop 9

@[simp] theorem remaining_image_count : remainingImageRows.length = 388 := by
  simp [remainingImageRows, priorRemainingImageRows]

theorem rows_append_remaining_eq_prior :
    rows ++ remainingImageRows = priorRemainingImageRows := by
  exact List.take_append_drop 9 priorRemainingImageRows

def advancedMaterializedProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorCarbohydrateModifiedFischerImageSourceMeanings.advancedMaterializedProvisions ++
    provisions

def advancedMaterializedBatch :
    GlobalNonDescriptorSourceMeaningBatch advancedMaterializedProvisions :=
  GlobalNonDescriptorCarbohydrateModifiedFischerImageSourceMeanings.advancedMaterializedBatch.append
    visionReviewedGraphLevelBatch

@[simp] theorem advanced_materialized_count : advancedMaterializedProvisions.length = 1649 := by
  simp [advancedMaterializedProvisions]

def advancedMissingProvisions : List IUPACNormativeProvision :=
  sourceProvisions .blueBook2013Appendix3 ++
    remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem advanced_missing_count : advancedMissingProvisions.length = 559 := by
  simp [advancedMissingProvisions]

set_option maxRecDepth 8192 in
theorem selected_then_advanced_missing_perm_prior_missing :
    (provisions ++ advancedMissingProvisions).Perm
      GlobalNonDescriptorCarbohydrateModifiedFischerImageSourceMeanings.advancedMissingProvisions := by
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
    _ = GlobalNonDescriptorCarbohydrateModifiedFischerImageSourceMeanings.advancedMissingProvisions := by
      rfl

theorem mem_prior_missing_iff_selected_or_advanced_missing
    (provision : IUPACNormativeProvision) :
    provision ∈
        GlobalNonDescriptorCarbohydrateModifiedFischerImageSourceMeanings.advancedMissingProvisions ↔
      provision ∈ provisions ∨ provision ∈ advancedMissingProvisions := by
  simpa only [List.mem_append] using
    (selected_then_advanced_missing_perm_prior_missing.mem_iff).symm

private theorem selected_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ provisions) :
    provision ∈
      GlobalNonDescriptorCarbohydrateModifiedFischerImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_left _ member)

private theorem advanced_missing_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ advancedMissingProvisions) :
    provision ∈
      GlobalNonDescriptorCarbohydrateModifiedFischerImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_right _ member)

private theorem selected_append_advanced_missing_nodup :
    (provisions ++ advancedMissingProvisions).Nodup :=
  GlobalNonDescriptorCarbohydrateModifiedFischerImageSourceMeanings.advanced_missing_nodup.perm
    selected_then_advanced_missing_perm_prior_missing.symm

theorem advanced_missing_nodup : advancedMissingProvisions.Nodup :=
  List.Nodup.of_append_right selected_append_advanced_missing_nodup

private theorem selected_disjoint_advanced_missing :
    provisions.Disjoint advancedMissingProvisions :=
  List.disjoint_of_nodup_append selected_append_advanced_missing_nodup

private theorem prior_materialized_disjoint_selected :
    GlobalNonDescriptorCarbohydrateModifiedFischerImageSourceMeanings.advancedMaterializedProvisions.Disjoint
      provisions := by
  rw [List.disjoint_left]
  intro provision materialized selected
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateModifiedFischerImageSourceMeanings.advanced_materialized_disjoint_missing)
      materialized (selected_subset_prior_missing selected)

theorem advanced_materialized_nodup : advancedMaterializedProvisions.Nodup := by
  exact GlobalNonDescriptorCarbohydrateModifiedFischerImageSourceMeanings.advanced_materialized_nodup.append
    provisions_nodup prior_materialized_disjoint_selected

theorem advanced_materialized_disjoint_missing :
    advancedMaterializedProvisions.Disjoint advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision advanced missing
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateModifiedFischerImageSourceMeanings.advanced_materialized_disjoint_missing)
        priorMaterialized (advanced_missing_subset_prior_missing missing)
  · exact (List.disjoint_left.mp selected_disjoint_advanced_missing) selected missing

theorem reviewed_disjoint_advanced_materialized :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMaterializedProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed advanced
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateModifiedFischerImageSourceMeanings.reviewed_disjoint_advanced_materialized)
        reviewed priorMaterialized
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateModifiedFischerImageSourceMeanings.reviewed_disjoint_advanced_missing)
        reviewed (selected_subset_prior_missing selected)

theorem reviewed_disjoint_advanced_missing :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed missing
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateModifiedFischerImageSourceMeanings.reviewed_disjoint_advanced_missing)
      reviewed (advanced_missing_subset_prior_missing missing)

set_option maxRecDepth 8192 in
theorem mem_reviewed_or_advanced_materialized_or_missing_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions ∨
      provision ∈ advancedMaterializedProvisions ∨
        provision ∈ advancedMissingProvisions ↔
      provision ∈ globalNonDescriptorProvisions := by
  rw [← GlobalNonDescriptorCarbohydrateModifiedFischerImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff]
  rw [mem_prior_missing_iff_selected_or_advanced_missing]
  simp only [advancedMaterializedProvisions, List.mem_append]
  tauto

theorem advanced_live_frontier_counts :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.length = 92 ∧
      advancedMaterializedProvisions.length = 1649 ∧
        advancedMissingProvisions.length = 559 ∧
          92 + 1649 + 559 = 2300 := by
  exact ⟨GlobalNonDescriptorSourceMeaningProgress.reviewed_count,
    advanced_materialized_count, advanced_missing_count, by omega⟩

end GlobalNonDescriptorCarbohydrateHaworthImageSourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateHaworthImageSourceMeanings.frozen_artifact_data_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateHaworthImageSourceMeanings.meanings_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateHaworthImageSourceMeanings.visionReviewedGraphLevelBatch
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateHaworthImageSourceMeanings.selected_then_advanced_missing_perm_prior_missing
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateHaworthImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff
