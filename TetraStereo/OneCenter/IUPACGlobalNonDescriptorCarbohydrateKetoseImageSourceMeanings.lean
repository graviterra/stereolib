import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateConformationAldoseDialdoseImageSourceMeanings
import TetraStereo.KernelOnly

set_option autoImplicit false














namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings

open GlobalNonDescriptorSourceMeaningConstructor

def priorRemainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  GlobalNonDescriptorCarbohydrateConformationAldoseDialdoseImageSourceMeanings.remainingImageRows

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
      [ ⟨"2carb/2C1gif/102.GIF", "255a314933b6ae1420f53d0edd145b5e89a0891ceeb68b044c826f84464a2f65", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/104A.GIF", "86b34ee4ce3e2e5e3ffab5870cdba0b0debc34196f759c787fdf249307c1ac19", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/104B.GIF", "c127f9c84f3ad4f83b048f483cefb4dd65a5390bc35051436dc438b1d455bf85", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/104C.GIF", "fbae33ac8562568421c5ddb63c54ccc7e25ff8956390b14ebe88f89754f2d6c0", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/104D.GIF", "0d4d5a0279759fda1c6c0d19975bd392cf7dafb40e70d62708a1a217e0ff5ad0", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/104E.GIF", "bb8c1d14cfb73be1f42179abbb7590606df083eba218162c23b087388e735866", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/104F.GIF", "40fb0c77aa39c73ca5a30f7b9ddf209dab4b36a17993806e788c2087cfbac6bb", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/104G.GIF", "be2ebf6be8cd41f76dba461a43044db289ee8f6923084792dbc30e8113da84ae", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/104H.GIF", "b7ea704f06726d8df4e9d877cc42367280221ee88fd892fd6ec252d010168824", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/104I.GIF", "d1b4a9013227d49cad9fbd9658ec983573f99b7f29d5ccfbe2ece2e02600794c", .numberedOrChartStructure⟩ ] := by
  decide

set_option maxRecDepth 4096 in
@[simp] theorem source_pages_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 10 ["10.html"] := by
  decide

set_option maxRecDepth 4096 in
private theorem rows_nodup : rows.Nodup := by
  decide

theorem provisions_nodup : provisions.Nodup := by
  exact rows_nodup.map (by intro left right equal; cases equal; rfl)

/-! ## Typed ketose structures and naming rules -/

inductive HydroxylSide where
  | left
  | right
  deriving DecidableEq, Repr, Inhabited

structure ConfigurationalGroup where
  prefixText : String
  locants : List Nat
  hydroxylSides : List HydroxylSide
  deriving DecidableEq, Repr, Inhabited

def ConfigurationalGroup.wellFormed (group : ConfigurationalGroup) : Bool :=
  !group.prefixText.isEmpty && !group.locants.isEmpty && group.locants.Nodup &&
    group.locants.length == group.hydroxylSides.length

structure TrivialName where
  name : String
  abbreviation : Option String := none
  deriving DecidableEq, Repr, Inhabited

inductive RingSize where
  | pyranose
  deriving DecidableEq, Repr, Inhabited

structure RingClosure where
  potentialCarbonylLocant : Nat
  oxygenBearingCarbonLocant : Nat
  ringSize : RingSize
  deriving DecidableEq, Repr, Inhabited

inductive RejectedAlternativeReason where
  | higherCarbonylLocant
  | carbohydrateParentChoiceTieBreak
  deriving DecidableEq, Repr, Inhabited

structure RejectedAlternative where
  name : String
  reason : RejectedAlternativeReason
  deriving DecidableEq, Repr, Inhabited

structure KetoseEntry where
  publishedName : String
  carbonCount : Nat
  carbonylLocant : Nat
  configurationGroups : List ConfigurationalGroup := []
  trivialName : Option TrivialName := none
  ringClosure : Option RingClosure := none
  rejectedAlternative : Option RejectedAlternative := none
  deriving DecidableEq, Repr, Inhabited

def KetoseEntry.configurationLocants (entry : KetoseEntry) : List Nat :=
  entry.configurationGroups.flatMap ConfigurationalGroup.locants

def KetoseEntry.ringClosureWellFormed (entry : KetoseEntry) : Bool :=
  match entry.ringClosure with
  | none => true
  | some closure =>
      decide (closure.potentialCarbonylLocant = entry.carbonylLocant ∧
        0 < closure.oxygenBearingCarbonLocant ∧
        closure.oxygenBearingCarbonLocant < entry.carbonCount ∧
        closure.oxygenBearingCarbonLocant = closure.potentialCarbonylLocant + 4)

def KetoseEntry.wellFormed (entry : KetoseEntry) : Bool :=
  !entry.publishedName.isEmpty &&
    decide (3 ≤ entry.carbonCount ∧ 0 < entry.carbonylLocant ∧
      entry.carbonylLocant < entry.carbonCount) &&
    entry.configurationGroups.all ConfigurationalGroup.wellFormed &&
    entry.configurationLocants.Nodup &&
    (entry.configurationLocants.all fun locant =>
      decide (0 < locant ∧ locant < entry.carbonCount ∧ locant ≠ entry.carbonylLocant)) &&
    entry.ringClosureWellFormed

private def group (prefixText : String) (locants : List Nat)
    (hydroxylSides : List HydroxylSide) : ConfigurationalGroup :=
  { prefixText, locants, hydroxylSides }

private def trivial (name : String) (abbreviation : Option String := none) : TrivialName :=
  { name, abbreviation }

def chartEntries : List KetoseEntry :=
  [ { publishedName := "1,3-Dihydroxyacetone", carbonCount := 3, carbonylLocant := 2 }
  , { publishedName := "D-glycero-Tetrulose", carbonCount := 4, carbonylLocant := 2
      configurationGroups := [group "D-glycero" [3] [.right]]
      trivialName := some (trivial "D-Erythrulose") }
  , { publishedName := "D-erythro-Pent-2-ulose", carbonCount := 5, carbonylLocant := 2
      configurationGroups := [group "D-erythro" [3, 4] [.right, .right]]
      trivialName := some (trivial "D-Ribulose" (some "D-Rul")) }
  , { publishedName := "D-threo-Pent-2-ulose", carbonCount := 5, carbonylLocant := 2
      configurationGroups := [group "D-threo" [3, 4] [.left, .right]]
      trivialName := some (trivial "D-Xylulose" (some "D-Xul")) }
  , { publishedName := "D-ribo-Hex-2-ulose", carbonCount := 6, carbonylLocant := 2
      configurationGroups := [group "D-ribo" [3, 4, 5] [.right, .right, .right]]
      trivialName := some (trivial "D-Psicose" (some "D-Psi")) }
  , { publishedName := "D-arabino-Hex-2-ulose", carbonCount := 6, carbonylLocant := 2
      configurationGroups := [group "D-arabino" [3, 4, 5] [.left, .right, .right]]
      trivialName := some (trivial "D-Fructose" (some "D-Fru")) }
  , { publishedName := "D-xylo-Hex-2-ulose", carbonCount := 6, carbonylLocant := 2
      configurationGroups := [group "D-xylo" [3, 4, 5] [.right, .left, .right]]
      trivialName := some (trivial "D-Sorbose" (some "D-Sor")) }
  , { publishedName := "D-lyxo-Hex-2-ulose", carbonCount := 6, carbonylLocant := 2
      configurationGroups := [group "D-lyxo" [3, 4, 5] [.left, .left, .right]]
      trivialName := some (trivial "D-Tagatose" (some "D-Tag")) } ]

@[simp] theorem chart_entry_count : chartEntries.length = 8 := rfl

@[simp] theorem chart_published_names_exact :
    chartEntries.map KetoseEntry.publishedName =
      [ "1,3-Dihydroxyacetone"
      , "D-glycero-Tetrulose"
      , "D-erythro-Pent-2-ulose"
      , "D-threo-Pent-2-ulose"
      , "D-ribo-Hex-2-ulose"
      , "D-arabino-Hex-2-ulose"
      , "D-xylo-Hex-2-ulose"
      , "D-lyxo-Hex-2-ulose" ] := rfl

def ketoseExamples : List KetoseEntry :=
  [ { publishedName := "L-xylo-Hex-2-ulose", carbonCount := 6, carbonylLocant := 2
      configurationGroups := [group "L-xylo" [3, 4, 5] [.left, .right, .left]]
      trivialName := some (trivial "L-Sorbose") }
  , { publishedName := "D-altro-Hept-2-ulose", carbonCount := 7, carbonylLocant := 2
      configurationGroups := [group "D-altro" [3, 4, 5, 6] [.left, .right, .right, .right]]
      trivialName := some (trivial "D-Sedoheptulose") }
  , { publishedName := "D-altro-Hept-2-ulopyranose", carbonCount := 7, carbonylLocant := 2
      configurationGroups := [group "D-altro" [3, 4, 5, 6] [.left, .right, .right, .right]]
      ringClosure := some ⟨2, 6, .pyranose⟩ }
  , { publishedName := "L-glycero-D-manno-Oct-2-ulose", carbonCount := 8, carbonylLocant := 2
      configurationGroups :=
        [ group "L-glycero" [7] [.left]
        , group "D-manno" [3, 4, 5, 6] [.left, .left, .right, .right] ] }
  , { publishedName := "D-arabino-Hex-3-ulose", carbonCount := 6, carbonylLocant := 3
      configurationGroups := [group "D-arabino" [2, 4, 5] [.left, .right, .right]] }
  , { publishedName := "D-xylo-Hex-3-ulose", carbonCount := 6, carbonylLocant := 3
      configurationGroups := [group "D-xylo" [2, 4, 5] [.right, .left, .right]]
      rejectedAlternative := some ⟨"L-xylo-hex-4-ulose", .higherCarbonylLocant⟩ }
  , { publishedName := "L-gluco-Hept-4-ulose", carbonCount := 7, carbonylLocant := 4
      configurationGroups := [group "L-gluco" [2, 3, 5, 6] [.left, .right, .left, .left]]
      rejectedAlternative :=
        some ⟨"D-gulo-hept-4-ulose", .carbohydrateParentChoiceTieBreak⟩ }
  , { publishedName := "L-threo-D-allo-Non-3-ulose", carbonCount := 9, carbonylLocant := 3
      configurationGroups :=
        [ group "L-threo" [7, 8] [.right, .left]
        , group "D-allo" [2, 4, 5, 6] [.right, .right, .right, .right] ] }
  , { publishedName := "L-erythro-L-gluco-Non-5-ulose", carbonCount := 9, carbonylLocant := 5
      configurationGroups :=
        [ group "L-erythro" [7, 8] [.left, .left]
        , group "L-gluco" [2, 3, 4, 6] [.left, .right, .left, .left] ]
      rejectedAlternative :=
        some ⟨"D-threo-L-allo-non-5-ulose", .carbohydrateParentChoiceTieBreak⟩ } ]

@[simp] theorem example_published_names_exact :
    ketoseExamples.map KetoseEntry.publishedName =
      [ "L-xylo-Hex-2-ulose"
      , "D-altro-Hept-2-ulose"
      , "D-altro-Hept-2-ulopyranose"
      , "L-glycero-D-manno-Oct-2-ulose"
      , "D-arabino-Hex-3-ulose"
      , "D-xylo-Hex-3-ulose"
      , "L-gluco-Hept-4-ulose"
      , "L-threo-D-allo-Non-3-ulose"
      , "L-erythro-L-gluco-Non-5-ulose" ] := rfl

structure ClassificationRule where
  classifiedByPotentialCarbonylLocant : Bool
  locantTwoMayBeOmittedOnlyWhenUnambiguous : Bool
  deriving DecidableEq, Repr

def classificationRule : ClassificationRule where
  classifiedByPotentialCarbonylLocant := true
  locantTwoMayBeOmittedOnlyWhenUnambiguous := true

structure SystematicNameRule where
  aldoseOseEndingReplacedByUlose : Bool
  carbonylReceivesLowestPossibleLocant : Bool
  middleOddChainTieUsesCarbohydrateParentChoice : Bool
  deriving DecidableEq, Repr

def systematicNameRule : SystematicNameRule where
  aldoseOseEndingReplacedByUlose := true
  carbonylReceivesLowestPossibleLocant := true
  middleOddChainTieUsesCarbohydrateParentChoice := true

structure ConfigurationalPrefixRule where
  twoKetosesFollowAldosePrefixRules : Bool
  higherCarbonylIsIgnoredForPrefixSequence : Bool
  multipleGroupsCitedFarthestFirst : Bool
  deriving DecidableEq, Repr

def configurationalPrefixRule : ConfigurationalPrefixRule where
  twoKetosesFollowAldosePrefixRules := true
  higherCarbonylIsIgnoredForPrefixSequence := true
  multipleGroupsCitedFarthestFirst := true

def discouragedDerivativeTrivialNames : List String :=
  ["L-Erythrulose", "L-Ribulose", "L-Xylulose"]

/-! ## Total typed lookup and reviewed batch -/

inductive ImageSourceMeaning where
  | ketoseChart (entries : List KetoseEntry)
  | ketoseExample (entry : KetoseEntry)
  deriving DecidableEq, Repr

def sourceMeaning? : String → Option ImageSourceMeaning
  | "2carb/2C1gif/102.GIF" => some (.ketoseChart chartEntries)
  | "2carb/2C1gif/104A.GIF" => ketoseExamples[0]?.map ImageSourceMeaning.ketoseExample
  | "2carb/2C1gif/104B.GIF" => ketoseExamples[1]?.map ImageSourceMeaning.ketoseExample
  | "2carb/2C1gif/104C.GIF" => ketoseExamples[2]?.map ImageSourceMeaning.ketoseExample
  | "2carb/2C1gif/104D.GIF" => ketoseExamples[3]?.map ImageSourceMeaning.ketoseExample
  | "2carb/2C1gif/104E.GIF" => ketoseExamples[4]?.map ImageSourceMeaning.ketoseExample
  | "2carb/2C1gif/104F.GIF" => ketoseExamples[5]?.map ImageSourceMeaning.ketoseExample
  | "2carb/2C1gif/104G.GIF" => ketoseExamples[6]?.map ImageSourceMeaning.ketoseExample
  | "2carb/2C1gif/104H.GIF" => ketoseExamples[7]?.map ImageSourceMeaning.ketoseExample
  | "2carb/2C1gif/104I.GIF" => ketoseExamples[8]?.map ImageSourceMeaning.ketoseExample
  | _ => none

def all_image_meanings_present : Bool :=
  artifacts.all fun artifact => (sourceMeaning? artifact.data.relativePath).isSome

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
    visionReviewedGraphLevelBatch.entries.length = 10 := by
  rw [visionReviewedGraphLevelBatch.entries_length, provision_count]

/-! ## Exact advance from the prior 1,678/530 overlay -/

def remainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  priorRemainingImageRows.drop 10

@[simp] theorem remaining_image_count : remainingImageRows.length = 349 := by
  simp [remainingImageRows, priorRemainingImageRows]

theorem rows_append_remaining_eq_prior :
    rows ++ remainingImageRows = priorRemainingImageRows := by
  exact List.take_append_drop 10 priorRemainingImageRows

def advancedMaterializedProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorCarbohydrateConformationAldoseDialdoseImageSourceMeanings.advancedMaterializedProvisions ++
    provisions

def advancedMaterializedBatch :
    GlobalNonDescriptorSourceMeaningBatch advancedMaterializedProvisions :=
  GlobalNonDescriptorCarbohydrateConformationAldoseDialdoseImageSourceMeanings.advancedMaterializedBatch.append
    visionReviewedGraphLevelBatch

@[simp] theorem advanced_materialized_count : advancedMaterializedProvisions.length = 1688 := by
  simp [advancedMaterializedProvisions]

def advancedMissingProvisions : List IUPACNormativeProvision :=
  sourceProvisions .blueBook2013Appendix3 ++
    remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem advanced_missing_count : advancedMissingProvisions.length = 520 := by
  simp [advancedMissingProvisions]

set_option maxRecDepth 8192 in
theorem selected_then_advanced_missing_perm_prior_missing :
    (provisions ++ advancedMissingProvisions).Perm
      GlobalNonDescriptorCarbohydrateConformationAldoseDialdoseImageSourceMeanings.advancedMissingProvisions := by
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
    _ = GlobalNonDescriptorCarbohydrateConformationAldoseDialdoseImageSourceMeanings.advancedMissingProvisions := by
      rfl

theorem mem_prior_missing_iff_selected_or_advanced_missing
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorCarbohydrateConformationAldoseDialdoseImageSourceMeanings.advancedMissingProvisions ↔
      provision ∈ provisions ∨ provision ∈ advancedMissingProvisions := by
  simpa only [List.mem_append] using
    (selected_then_advanced_missing_perm_prior_missing.mem_iff).symm

private theorem selected_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ provisions) :
    provision ∈ GlobalNonDescriptorCarbohydrateConformationAldoseDialdoseImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_left _ member)

private theorem advanced_missing_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ advancedMissingProvisions) :
    provision ∈ GlobalNonDescriptorCarbohydrateConformationAldoseDialdoseImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_right _ member)

private theorem selected_append_advanced_missing_nodup :
    (provisions ++ advancedMissingProvisions).Nodup :=
  GlobalNonDescriptorCarbohydrateConformationAldoseDialdoseImageSourceMeanings.advanced_missing_nodup.perm
    selected_then_advanced_missing_perm_prior_missing.symm

theorem advanced_missing_nodup : advancedMissingProvisions.Nodup :=
  List.Nodup.of_append_right selected_append_advanced_missing_nodup

private theorem selected_disjoint_advanced_missing :
    provisions.Disjoint advancedMissingProvisions :=
  List.disjoint_of_nodup_append selected_append_advanced_missing_nodup

private theorem prior_materialized_disjoint_selected :
    GlobalNonDescriptorCarbohydrateConformationAldoseDialdoseImageSourceMeanings.advancedMaterializedProvisions.Disjoint
      provisions := by
  rw [List.disjoint_left]
  intro provision materialized selected
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateConformationAldoseDialdoseImageSourceMeanings.advanced_materialized_disjoint_missing)
      materialized (selected_subset_prior_missing selected)

theorem advanced_materialized_nodup : advancedMaterializedProvisions.Nodup := by
  exact GlobalNonDescriptorCarbohydrateConformationAldoseDialdoseImageSourceMeanings.advanced_materialized_nodup.append
    provisions_nodup prior_materialized_disjoint_selected

theorem advanced_materialized_disjoint_missing :
    advancedMaterializedProvisions.Disjoint advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision advanced missing
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateConformationAldoseDialdoseImageSourceMeanings.advanced_materialized_disjoint_missing)
        priorMaterialized (advanced_missing_subset_prior_missing missing)
  · exact (List.disjoint_left.mp selected_disjoint_advanced_missing) selected missing

theorem reviewed_disjoint_advanced_materialized :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMaterializedProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed advanced
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateConformationAldoseDialdoseImageSourceMeanings.reviewed_disjoint_advanced_materialized)
        reviewed priorMaterialized
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateConformationAldoseDialdoseImageSourceMeanings.reviewed_disjoint_advanced_missing)
        reviewed (selected_subset_prior_missing selected)

theorem reviewed_disjoint_advanced_missing :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed missing
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateConformationAldoseDialdoseImageSourceMeanings.reviewed_disjoint_advanced_missing)
      reviewed (advanced_missing_subset_prior_missing missing)

set_option maxRecDepth 8192 in
theorem mem_reviewed_or_advanced_materialized_or_missing_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions ∨
      provision ∈ advancedMaterializedProvisions ∨
        provision ∈ advancedMissingProvisions ↔
      provision ∈ globalNonDescriptorProvisions := by
  rw [← GlobalNonDescriptorCarbohydrateConformationAldoseDialdoseImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff]
  rw [mem_prior_missing_iff_selected_or_advanced_missing]
  simp only [advancedMaterializedProvisions, List.mem_append]
  tauto

theorem advanced_live_frontier_counts :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.length = 92 ∧
      advancedMaterializedProvisions.length = 1688 ∧
        advancedMissingProvisions.length = 520 ∧
          92 + 1688 + 520 = 2300 := by
  exact ⟨GlobalNonDescriptorSourceMeaningProgress.reviewed_count,
    advanced_materialized_count, advanced_missing_count, by omega⟩

end GlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings.frozen_artifact_data_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings.chart_published_names_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings.example_published_names_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings.visionReviewedGraphLevelBatch
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings.selected_then_advanced_missing_perm_prior_missing
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff
