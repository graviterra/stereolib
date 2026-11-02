import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateConformationImageSourceMeanings
import TetraStereo.KernelOnly

set_option autoImplicit false















namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings

open GlobalNonDescriptorSourceMeaningConstructor

def priorRemainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  GlobalNonDescriptorCarbohydrateConformationImageSourceMeanings.remainingImageRows

def rows : List Carbohydrate1996ImageAudit.Provision := priorRemainingImageRows.take 8

def artifactOf : Carbohydrate1996ImageAudit.Provision →
    Carbohydrate1996ImageAudit.ImageArtifact
  | .imageArtifact artifact => artifact

def artifacts : List Carbohydrate1996ImageAudit.ImageArtifact := rows.map artifactOf

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem row_count : rows.length = 8 := by
  simp [rows, priorRemainingImageRows]

@[simp] theorem artifact_count : artifacts.length = 8 := by simp [artifacts]
@[simp] theorem provision_count : provisions.length = 8 := by simp [provisions]

set_option maxRecDepth 4096 in
@[simp] theorem frozen_artifact_data_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.data =
      [ ⟨"2carb/2C0gif/062A.GIF", "649a579a468dac845482bed7ea9b02f800af4aeac3c042a467a5ce4140de4290", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/062B.GIF", "a008d314c9f1d769bbc4742caaddff79aba372e4daf06b40e32023c53829efc5", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/062C.GIF", "cb928122d7a29bfbccba2782ddb67fe1bafb1835e734bb9e6d7be5790df738af", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/062D.GIF", "87925a4b5378371e04b5b80a9e226324625333c86f281e5765bb11e7ac07fc85", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/062E.GIF", "eb8833fc951c1ff3676d2682026946005ef032bfdf442520111fece23ec8d767", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/062F.GIF", "f254ebafd086579bac79563a685c7d0157eb96497b320cf5cc5d0eff591f8960", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/062G.GIF", "36a103f7599f1c5a6121303ba96dd0234bc299c2a5b19e627301024cc58455f0", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/062H.GIF", "92179b41e7f8cf33a1db701608cc943f52421e0cf7586caeddbadae74d36cb8b", .numberedOrChartStructure⟩ ] := by
  decide

set_option maxRecDepth 4096 in
@[simp] theorem source_pages_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 8 ["06n07.html"] := by
  decide

set_option maxRecDepth 4096 in
private theorem rows_nodup : rows.Nodup := by
  decide

theorem provisions_nodup : provisions.Nodup := by
  exact rows_nodup.map (by intro left right equal; cases equal; rfl)

inductive Anomer where
  | alpha | beta
  deriving DecidableEq, Repr

inductive FormalOxygenRelation where
  | cis | trans
  deriving DecidableEq, Repr

inductive AnomericSubstituent where
  | hydroxyl | methoxy
  deriving DecidableEq, Repr

inductive ConfigurationGroup where
  | hydroxy | acetamido
  deriving DecidableEq, Repr

structure ConfigurationalPrefix where
  stem : String
  series : GlobalNonDescriptorCarbohydrateConfigurationalSeriesImageSourceMeanings.ConfigurationalSeries
  deriving DecidableEq, Repr

structure ConfigurationEntry where
  locant : Nat
  group : ConfigurationGroup
  side : Carbohydrate1996ImageAudit.FischerHorizontalSide
  deriving DecidableEq, Repr

structure AnomericReferenceMeaning where
  publishedName : String
  anomer : Anomer
  formalOxygenRelation : FormalOxygenRelation
  configurationalPrefixes : List ConfigurationalPrefix
  anomericPrefixIndex : Nat
  anomericCarbonLocant : Nat
  anomericSubstituent : AnomericSubstituent
  ringOxygenSourceLocant : Nat
  ringSize : Nat
  anomericReferenceAtomLocant : Nat
  configurationalAtomLocant : Nat
  parentConfiguration : List ConfigurationEntry
  deriving DecidableEq, Repr

def meanings : List AnomericReferenceMeaning :=
  [ { publishedName := "alpha-D-glucopyranose"
      anomer := .alpha, formalOxygenRelation := .cis
      configurationalPrefixes := [⟨"gluco", .D⟩], anomericPrefixIndex := 0
      anomericCarbonLocant := 1, anomericSubstituent := .hydroxyl
      ringOxygenSourceLocant := 5, ringSize := 6
      anomericReferenceAtomLocant := 5, configurationalAtomLocant := 5
      parentConfiguration :=
        [⟨2, .hydroxy, .right⟩, ⟨3, .hydroxy, .left⟩,
         ⟨4, .hydroxy, .right⟩, ⟨5, .hydroxy, .right⟩] }
  , { publishedName := "beta-D-glucopyranose"
      anomer := .beta, formalOxygenRelation := .trans
      configurationalPrefixes := [⟨"gluco", .D⟩], anomericPrefixIndex := 0
      anomericCarbonLocant := 1, anomericSubstituent := .hydroxyl
      ringOxygenSourceLocant := 5, ringSize := 6
      anomericReferenceAtomLocant := 5, configurationalAtomLocant := 5
      parentConfiguration :=
        [⟨2, .hydroxy, .right⟩, ⟨3, .hydroxy, .left⟩,
         ⟨4, .hydroxy, .right⟩, ⟨5, .hydroxy, .right⟩] }
  , { publishedName := "methyl alpha-L-arabinopyranoside"
      anomer := .alpha, formalOxygenRelation := .cis
      configurationalPrefixes := [⟨"arabino", .L⟩], anomericPrefixIndex := 0
      anomericCarbonLocant := 1, anomericSubstituent := .methoxy
      ringOxygenSourceLocant := 5, ringSize := 6
      anomericReferenceAtomLocant := 4, configurationalAtomLocant := 4
      parentConfiguration :=
        [⟨2, .hydroxy, .right⟩, ⟨3, .hydroxy, .left⟩,
         ⟨4, .hydroxy, .left⟩] }
  , { publishedName := "methyl beta-L-threofuranoside"
      anomer := .beta, formalOxygenRelation := .trans
      configurationalPrefixes := [⟨"threo", .L⟩], anomericPrefixIndex := 0
      anomericCarbonLocant := 1, anomericSubstituent := .methoxy
      ringOxygenSourceLocant := 4, ringSize := 5
      anomericReferenceAtomLocant := 3, configurationalAtomLocant := 3
      parentConfiguration := [⟨2, .hydroxy, .right⟩, ⟨3, .hydroxy, .left⟩] }
  , { publishedName := "methyl beta-D-galactofuranoside"
      anomer := .beta, formalOxygenRelation := .trans
      configurationalPrefixes := [⟨"galacto", .D⟩], anomericPrefixIndex := 0
      anomericCarbonLocant := 1, anomericSubstituent := .methoxy
      ringOxygenSourceLocant := 4, ringSize := 5
      anomericReferenceAtomLocant := 5, configurationalAtomLocant := 5
      parentConfiguration :=
        [⟨2, .hydroxy, .right⟩, ⟨3, .hydroxy, .left⟩,
         ⟨4, .hydroxy, .left⟩, ⟨5, .hydroxy, .right⟩] }
  , { publishedName := "methyl L-glycero-alpha-D-manno-heptopyranoside"
      anomer := .alpha, formalOxygenRelation := .cis
      configurationalPrefixes := [⟨"glycero", .L⟩, ⟨"manno", .D⟩]
      anomericPrefixIndex := 1
      anomericCarbonLocant := 1, anomericSubstituent := .methoxy
      ringOxygenSourceLocant := 5, ringSize := 6
      anomericReferenceAtomLocant := 5, configurationalAtomLocant := 6
      parentConfiguration :=
        [⟨2, .hydroxy, .left⟩, ⟨3, .hydroxy, .left⟩,
         ⟨4, .hydroxy, .right⟩, ⟨5, .hydroxy, .right⟩,
         ⟨6, .hydroxy, .left⟩] }
  , { publishedName := "methyl beta-D-fructofuranoside"
      anomer := .beta, formalOxygenRelation := .trans
      configurationalPrefixes := [⟨"arabino", .D⟩], anomericPrefixIndex := 0
      anomericCarbonLocant := 2, anomericSubstituent := .methoxy
      ringOxygenSourceLocant := 5, ringSize := 5
      anomericReferenceAtomLocant := 5, configurationalAtomLocant := 5
      parentConfiguration :=
        [⟨3, .hydroxy, .left⟩, ⟨4, .hydroxy, .right⟩,
         ⟨5, .hydroxy, .right⟩] }
  , { publishedName :=
        "methyl 5-acetamido-3,5-dideoxy-D-glycero-beta-D-galacto-non-2-ulopyranosonate"
      anomer := .beta, formalOxygenRelation := .trans
      configurationalPrefixes := [⟨"glycero", .D⟩, ⟨"galacto", .D⟩]
      anomericPrefixIndex := 1
      anomericCarbonLocant := 2, anomericSubstituent := .hydroxyl
      ringOxygenSourceLocant := 6, ringSize := 6
      anomericReferenceAtomLocant := 6, configurationalAtomLocant := 8
      parentConfiguration :=
        [⟨4, .hydroxy, .right⟩, ⟨5, .acetamido, .left⟩,
         ⟨6, .hydroxy, .left⟩, ⟨7, .hydroxy, .left⟩,
         ⟨8, .hydroxy, .right⟩] } ]

@[simp] theorem meanings_exact : meanings =
    [ { publishedName := "alpha-D-glucopyranose"
        anomer := .alpha, formalOxygenRelation := .cis
        configurationalPrefixes := [⟨"gluco", .D⟩], anomericPrefixIndex := 0
        anomericCarbonLocant := 1, anomericSubstituent := .hydroxyl
        ringOxygenSourceLocant := 5, ringSize := 6
        anomericReferenceAtomLocant := 5, configurationalAtomLocant := 5
        parentConfiguration :=
          [⟨2, .hydroxy, .right⟩, ⟨3, .hydroxy, .left⟩,
           ⟨4, .hydroxy, .right⟩, ⟨5, .hydroxy, .right⟩] }
    , { publishedName := "beta-D-glucopyranose"
        anomer := .beta, formalOxygenRelation := .trans
        configurationalPrefixes := [⟨"gluco", .D⟩], anomericPrefixIndex := 0
        anomericCarbonLocant := 1, anomericSubstituent := .hydroxyl
        ringOxygenSourceLocant := 5, ringSize := 6
        anomericReferenceAtomLocant := 5, configurationalAtomLocant := 5
        parentConfiguration :=
          [⟨2, .hydroxy, .right⟩, ⟨3, .hydroxy, .left⟩,
           ⟨4, .hydroxy, .right⟩, ⟨5, .hydroxy, .right⟩] }
    , { publishedName := "methyl alpha-L-arabinopyranoside"
        anomer := .alpha, formalOxygenRelation := .cis
        configurationalPrefixes := [⟨"arabino", .L⟩], anomericPrefixIndex := 0
        anomericCarbonLocant := 1, anomericSubstituent := .methoxy
        ringOxygenSourceLocant := 5, ringSize := 6
        anomericReferenceAtomLocant := 4, configurationalAtomLocant := 4
        parentConfiguration :=
          [⟨2, .hydroxy, .right⟩, ⟨3, .hydroxy, .left⟩,
           ⟨4, .hydroxy, .left⟩] }
    , { publishedName := "methyl beta-L-threofuranoside"
        anomer := .beta, formalOxygenRelation := .trans
        configurationalPrefixes := [⟨"threo", .L⟩], anomericPrefixIndex := 0
        anomericCarbonLocant := 1, anomericSubstituent := .methoxy
        ringOxygenSourceLocant := 4, ringSize := 5
        anomericReferenceAtomLocant := 3, configurationalAtomLocant := 3
        parentConfiguration := [⟨2, .hydroxy, .right⟩, ⟨3, .hydroxy, .left⟩] }
    , { publishedName := "methyl beta-D-galactofuranoside"
        anomer := .beta, formalOxygenRelation := .trans
        configurationalPrefixes := [⟨"galacto", .D⟩], anomericPrefixIndex := 0
        anomericCarbonLocant := 1, anomericSubstituent := .methoxy
        ringOxygenSourceLocant := 4, ringSize := 5
        anomericReferenceAtomLocant := 5, configurationalAtomLocant := 5
        parentConfiguration :=
          [⟨2, .hydroxy, .right⟩, ⟨3, .hydroxy, .left⟩,
           ⟨4, .hydroxy, .left⟩, ⟨5, .hydroxy, .right⟩] }
    , { publishedName := "methyl L-glycero-alpha-D-manno-heptopyranoside"
        anomer := .alpha, formalOxygenRelation := .cis
        configurationalPrefixes := [⟨"glycero", .L⟩, ⟨"manno", .D⟩]
        anomericPrefixIndex := 1
        anomericCarbonLocant := 1, anomericSubstituent := .methoxy
        ringOxygenSourceLocant := 5, ringSize := 6
        anomericReferenceAtomLocant := 5, configurationalAtomLocant := 6
        parentConfiguration :=
          [⟨2, .hydroxy, .left⟩, ⟨3, .hydroxy, .left⟩,
           ⟨4, .hydroxy, .right⟩, ⟨5, .hydroxy, .right⟩,
           ⟨6, .hydroxy, .left⟩] }
    , { publishedName := "methyl beta-D-fructofuranoside"
        anomer := .beta, formalOxygenRelation := .trans
        configurationalPrefixes := [⟨"arabino", .D⟩], anomericPrefixIndex := 0
        anomericCarbonLocant := 2, anomericSubstituent := .methoxy
        ringOxygenSourceLocant := 5, ringSize := 5
        anomericReferenceAtomLocant := 5, configurationalAtomLocant := 5
        parentConfiguration :=
          [⟨3, .hydroxy, .left⟩, ⟨4, .hydroxy, .right⟩,
           ⟨5, .hydroxy, .right⟩] }
    , { publishedName :=
          "methyl 5-acetamido-3,5-dideoxy-D-glycero-beta-D-galacto-non-2-ulopyranosonate"
        anomer := .beta, formalOxygenRelation := .trans
        configurationalPrefixes := [⟨"glycero", .D⟩, ⟨"galacto", .D⟩]
        anomericPrefixIndex := 1
        anomericCarbonLocant := 2, anomericSubstituent := .hydroxyl
        ringOxygenSourceLocant := 6, ringSize := 6
        anomericReferenceAtomLocant := 6, configurationalAtomLocant := 8
        parentConfiguration :=
          [⟨4, .hydroxy, .right⟩, ⟨5, .acetamido, .left⟩,
           ⟨6, .hydroxy, .left⟩, ⟨7, .hydroxy, .left⟩,
           ⟨8, .hydroxy, .right⟩] } ] := rfl

def AnomericReferenceMeaning.wellFormed (meaning : AnomericReferenceMeaning) : Bool :=
  meaning.anomericPrefixIndex < meaning.configurationalPrefixes.length &&
    meaning.configurationalPrefixes.all
        (fun configurationalPrefix => !configurationalPrefix.stem.isEmpty) &&
      meaning.ringSize = meaning.ringOxygenSourceLocant - meaning.anomericCarbonLocant + 2 &&
        meaning.anomericCarbonLocant < meaning.ringOxygenSourceLocant &&
          5 ≤ meaning.ringSize && meaning.ringSize ≤ 6 &&
            1 ≤ meaning.anomericReferenceAtomLocant &&
              meaning.anomericReferenceAtomLocant ≤ 8 &&
                1 ≤ meaning.configurationalAtomLocant &&
                  meaning.configurationalAtomLocant ≤ 8 &&
                    (meaning.parentConfiguration.map ConfigurationEntry.locant).Nodup &&
                      (match meaning.anomer with
                       | .alpha => meaning.formalOxygenRelation = .cis
                       | .beta => meaning.formalOxygenRelation = .trans) &&
                        (if meaning.configurationalPrefixes.length = 1 then
                           meaning.anomericReferenceAtomLocant = meaning.configurationalAtomLocant
                         else true) &&
                          !meaning.publishedName.isEmpty

structure AnomericReferenceRule where
  hemiacetalClosureCreatesAnomericCenter : Bool
  alphaMeansFormalCisOxygens : Bool
  betaMeansFormalTransOxygens : Bool
  symbolPrecedesRelevantConfigurationalPrefix : Bool
  multiPrefixUsesHighestRingAtomInAdjacentPrefixGroup : Bool
  simpleCasesReferenceEqualsConfigurationalAtom : Bool
  deriving DecidableEq, Repr

def anomericReferenceRule : AnomericReferenceRule where
  hemiacetalClosureCreatesAnomericCenter := true
  alphaMeansFormalCisOxygens := true
  betaMeansFormalTransOxygens := true
  symbolPrecedesRelevantConfigurationalPrefix := true
  multiPrefixUsesHighestRingAtomInAdjacentPrefixGroup := true
  simpleCasesReferenceEqualsConfigurationalAtom := true

def sourceMeaning? : String → Option AnomericReferenceMeaning
  | "2carb/2C0gif/062A.GIF" => meanings[0]?
  | "2carb/2C0gif/062B.GIF" => meanings[1]?
  | "2carb/2C0gif/062C.GIF" => meanings[2]?
  | "2carb/2C0gif/062D.GIF" => meanings[3]?
  | "2carb/2C0gif/062E.GIF" => meanings[4]?
  | "2carb/2C0gif/062F.GIF" => meanings[5]?
  | "2carb/2C0gif/062G.GIF" => meanings[6]?
  | "2carb/2C0gif/062H.GIF" => meanings[7]?
  | _ => none

def all_meanings_well_formed : Bool :=
  artifacts.all fun artifact =>
    match sourceMeaning? artifact.data.relativePath with
    | some meaning => meaning.wellFormed
    | none => false

structure VisionReviewedImageMeaning where
  artifactData : Carbohydrate1996ImageAudit.ImageArtifactData
  sourcePages : List String
  sourceMeaning : Option AnomericReferenceMeaning
  rule : AnomericReferenceRule
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
        rule := anomericReferenceRule
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
    visionReviewedGraphLevelBatch.entries.length = 8 := by
  rw [visionReviewedGraphLevelBatch.entries_length, provision_count]

/-! ## Exact advance from the prior 1,655/553 overlay -/

def remainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  priorRemainingImageRows.drop 8

@[simp] theorem remaining_image_count : remainingImageRows.length = 374 := by
  simp [remainingImageRows, priorRemainingImageRows]

theorem rows_append_remaining_eq_prior :
    rows ++ remainingImageRows = priorRemainingImageRows := by
  exact List.take_append_drop 8 priorRemainingImageRows

def advancedMaterializedProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorCarbohydrateConformationImageSourceMeanings.advancedMaterializedProvisions ++
    provisions

def advancedMaterializedBatch :
    GlobalNonDescriptorSourceMeaningBatch advancedMaterializedProvisions :=
  GlobalNonDescriptorCarbohydrateConformationImageSourceMeanings.advancedMaterializedBatch.append
    visionReviewedGraphLevelBatch

@[simp] theorem advanced_materialized_count : advancedMaterializedProvisions.length = 1663 := by
  simp [advancedMaterializedProvisions]

def advancedMissingProvisions : List IUPACNormativeProvision :=
  sourceProvisions .blueBook2013Appendix3 ++
    remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem advanced_missing_count : advancedMissingProvisions.length = 545 := by
  simp [advancedMissingProvisions]

set_option maxRecDepth 8192 in
theorem selected_then_advanced_missing_perm_prior_missing :
    (provisions ++ advancedMissingProvisions).Perm
      GlobalNonDescriptorCarbohydrateConformationImageSourceMeanings.advancedMissingProvisions := by
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
    _ = GlobalNonDescriptorCarbohydrateConformationImageSourceMeanings.advancedMissingProvisions := by
      rfl

theorem mem_prior_missing_iff_selected_or_advanced_missing
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorCarbohydrateConformationImageSourceMeanings.advancedMissingProvisions ↔
      provision ∈ provisions ∨ provision ∈ advancedMissingProvisions := by
  simpa only [List.mem_append] using
    (selected_then_advanced_missing_perm_prior_missing.mem_iff).symm

private theorem selected_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ provisions) :
    provision ∈ GlobalNonDescriptorCarbohydrateConformationImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_left _ member)

private theorem advanced_missing_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ advancedMissingProvisions) :
    provision ∈ GlobalNonDescriptorCarbohydrateConformationImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_right _ member)

private theorem selected_append_advanced_missing_nodup :
    (provisions ++ advancedMissingProvisions).Nodup :=
  GlobalNonDescriptorCarbohydrateConformationImageSourceMeanings.advanced_missing_nodup.perm
    selected_then_advanced_missing_perm_prior_missing.symm

theorem advanced_missing_nodup : advancedMissingProvisions.Nodup :=
  List.Nodup.of_append_right selected_append_advanced_missing_nodup

private theorem selected_disjoint_advanced_missing :
    provisions.Disjoint advancedMissingProvisions :=
  List.disjoint_of_nodup_append selected_append_advanced_missing_nodup

private theorem prior_materialized_disjoint_selected :
    GlobalNonDescriptorCarbohydrateConformationImageSourceMeanings.advancedMaterializedProvisions.Disjoint
      provisions := by
  rw [List.disjoint_left]
  intro provision materialized selected
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateConformationImageSourceMeanings.advanced_materialized_disjoint_missing)
      materialized (selected_subset_prior_missing selected)

theorem advanced_materialized_nodup : advancedMaterializedProvisions.Nodup := by
  exact GlobalNonDescriptorCarbohydrateConformationImageSourceMeanings.advanced_materialized_nodup.append
    provisions_nodup prior_materialized_disjoint_selected

theorem advanced_materialized_disjoint_missing :
    advancedMaterializedProvisions.Disjoint advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision advanced missing
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateConformationImageSourceMeanings.advanced_materialized_disjoint_missing)
        priorMaterialized (advanced_missing_subset_prior_missing missing)
  · exact (List.disjoint_left.mp selected_disjoint_advanced_missing) selected missing

theorem reviewed_disjoint_advanced_materialized :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMaterializedProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed advanced
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateConformationImageSourceMeanings.reviewed_disjoint_advanced_materialized)
        reviewed priorMaterialized
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateConformationImageSourceMeanings.reviewed_disjoint_advanced_missing)
        reviewed (selected_subset_prior_missing selected)

theorem reviewed_disjoint_advanced_missing :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed missing
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateConformationImageSourceMeanings.reviewed_disjoint_advanced_missing)
      reviewed (advanced_missing_subset_prior_missing missing)

set_option maxRecDepth 8192 in
theorem mem_reviewed_or_advanced_materialized_or_missing_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions ∨
      provision ∈ advancedMaterializedProvisions ∨
        provision ∈ advancedMissingProvisions ↔
      provision ∈ globalNonDescriptorProvisions := by
  rw [← GlobalNonDescriptorCarbohydrateConformationImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff]
  rw [mem_prior_missing_iff_selected_or_advanced_missing]
  simp only [advancedMaterializedProvisions, List.mem_append]
  tauto

theorem advanced_live_frontier_counts :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.length = 92 ∧
      advancedMaterializedProvisions.length = 1663 ∧
        advancedMissingProvisions.length = 545 ∧
          92 + 1663 + 545 = 2300 := by
  exact ⟨GlobalNonDescriptorSourceMeaningProgress.reviewed_count,
    advanced_materialized_count, advanced_missing_count, by omega⟩

end GlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings.frozen_artifact_data_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings.meanings_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings.visionReviewedGraphLevelBatch
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings.selected_then_advanced_missing_perm_prior_missing
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAnomericReferenceImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff
