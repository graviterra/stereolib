import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings
import TetraStereo.KernelOnly

set_option autoImplicit false















namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings

open GlobalNonDescriptorSourceMeaningConstructor

def priorRemainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  GlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings.remainingImageRows

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
      [ ⟨"2carb/2C1gif/111A.GIF", "c63289dde8cc11c6954e532995be572e6fbca5a28551c6c2e1dc67af47bdeb54", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/111B.GIF", "13e0e4e607715aedb7ad6753cfeb5c37e0db20e239bec8157627f5cd8c3f5928", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/112A.GIF", "068f6db3aa8fc32d42f22d6d23b196c97bfab79ef0e0cf23e64355ab3bdb7866", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/112B.GIF", "8b74059b63e38f61522a89580ecdbb357eb63489ac4eeb437bd5660f03644726", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/112C.GIF", "338457bf4044ba30608c6aacfe9f8c89ff90f60b5d82432f8f9a64ba4f346e56", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/112D.GIF", "5477ed3e8e87e2ff205dbe613f130e9f1a38945b5643313927314c9f57b9acb4", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/112E.GIF", "50956103bcca409c05d0963a2f213c95faa4c1dfe6bacbd90348c1271fb0caf7", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/121A.GIF", "71f7d1b5b97a5af67fbf820facce63c8821f0d58a7ac6dfea3afcde1b75c4ac6", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/121B.GIF", "51ec442e8ddbc68bcc12216803c8411e5d83fe0ab8c8615c75a6df2d791e51ac", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/121C.GIF", "0a8d1235ce1f799b284073b15b4a8625ff18d227adc88ff99b25b4150b8b6eb7", .numberedOrChartStructure⟩ ] := by
  decide

set_option maxRecDepth 4096 in
@[simp] theorem source_pages_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 10 ["11n12.html"] := by
  decide

set_option maxRecDepth 4096 in
private theorem rows_nodup : rows.Nodup := by
  decide

theorem provisions_nodup : provisions.Nodup := by
  exact rows_nodup.map (by intro left right equal; cases equal; rfl)

/-! ## Typed dicarbonyl structures -/

inductive HydroxylSide where
  | left | right
  deriving DecidableEq, Repr, Inhabited

structure ConfigurationalGroup where
  prefixText : String
  locants : List Nat
  hydroxylSides : List HydroxylSide
  deriving DecidableEq, Repr, Inhabited

def ConfigurationalGroup.wellFormed (group : ConfigurationalGroup) : Bool :=
  !group.prefixText.isEmpty && !group.locants.isEmpty && group.locants.Nodup &&
    group.locants.length == group.hydroxylSides.length

inductive DicarbonylFamily where
  | diketose | ketoaldose
  deriving DecidableEq, Repr, Inhabited

inductive CarbonylKind where
  | aldehyde | ketone
  deriving DecidableEq, Repr, Inhabited

structure Carbonyl where
  locant : Nat
  kind : CarbonylKind
  deriving DecidableEq, Repr, Inhabited

structure RingClosure where
  potentialCarbonylLocant : Nat
  oxygenBearingCarbonLocant : Nat
  ringSize : Nat
  deriving DecidableEq, Repr, Inhabited

inductive AnomericDescriptor where
  | alpha | beta
  deriving DecidableEq, Repr, Inhabited

structure CyclicForm where
  closure : RingClosure
  descriptor? : Option AnomericDescriptor
  methylGlycoside : Bool
  deriving DecidableEq, Repr, Inhabited

structure DicarbonylMeaning where
  publishedName : String
  family : DicarbonylFamily
  chainLength : Nat
  carbonyls : List Carbonyl
  configurationGroups : List ConfigurationalGroup
  cyclicForm? : Option CyclicForm := none
  rejectedName? : Option String := none
  isMeso : Bool := false
  erratum? : Option String := none
  deriving DecidableEq, Repr, Inhabited

def DicarbonylMeaning.configurationLocants (meaning : DicarbonylMeaning) : List Nat :=
  meaning.configurationGroups.flatMap ConfigurationalGroup.locants

def DicarbonylMeaning.familyWellFormed (meaning : DicarbonylMeaning) : Bool :=
  match meaning.family with
  | .diketose => meaning.carbonyls.all fun carbonyl => carbonyl.kind == .ketone
  | .ketoaldose =>
      meaning.carbonyls[0]? == some ⟨1, .aldehyde⟩ &&
        (meaning.carbonyls.drop 1).all fun carbonyl => carbonyl.kind == .ketone

def DicarbonylMeaning.cyclicFormWellFormed (meaning : DicarbonylMeaning) : Bool :=
  match meaning.cyclicForm? with
  | none => true
  | some cyclic =>
      (meaning.carbonyls.any fun carbonyl =>
        carbonyl.locant == cyclic.closure.potentialCarbonylLocant) &&
      decide (0 < cyclic.closure.oxygenBearingCarbonLocant ∧
        cyclic.closure.oxygenBearingCarbonLocant < meaning.chainLength ∧
        cyclic.closure.potentialCarbonylLocant ≠ cyclic.closure.oxygenBearingCarbonLocant) &&
      cyclic.closure.ringSize ==
        Nat.max cyclic.closure.potentialCarbonylLocant cyclic.closure.oxygenBearingCarbonLocant -
          Nat.min cyclic.closure.potentialCarbonylLocant cyclic.closure.oxygenBearingCarbonLocant + 2 &&
      (!cyclic.methylGlycoside || cyclic.descriptor?.isSome)

def DicarbonylMeaning.wellFormed (meaning : DicarbonylMeaning) : Bool :=
  !meaning.publishedName.isEmpty && decide (1 < meaning.chainLength) &&
    meaning.carbonyls.length == 2 && meaning.carbonyls.Nodup &&
      (meaning.carbonyls.all fun carbonyl =>
        decide (0 < carbonyl.locant ∧ carbonyl.locant ≤ meaning.chainLength)) &&
      meaning.familyWellFormed &&
      meaning.configurationGroups.all ConfigurationalGroup.wellFormed &&
      meaning.configurationLocants.Nodup &&
      (meaning.configurationLocants.all fun locant =>
        decide (0 < locant ∧ locant < meaning.chainLength) &&
          !(meaning.carbonyls.any fun carbonyl => carbonyl.locant == locant)) &&
      meaning.cyclicFormWellFormed

private def group (prefixText : String) (locants : List Nat)
    (hydroxylSides : List HydroxylSide) : ConfigurationalGroup :=
  { prefixText, locants, hydroxylSides }

private def ketone (locant : Nat) : Carbonyl := ⟨locant, .ketone⟩
private def aldehyde (locant : Nat) : Carbonyl := ⟨locant, .aldehyde⟩

def diketoseMeanings : List DicarbonylMeaning :=
  [ { publishedName := "L-threo-Hexo-2,5-diulose", family := .diketose, chainLength := 6
      carbonyls := [ketone 2, ketone 5]
      configurationGroups := [group "L-threo" [3, 4] [.right, .left]] }
  , { publishedName := "meso-xylo-Hepto-2,6-diulose", family := .diketose
      chainLength := 7, carbonyls := [ketone 2, ketone 6]
      configurationGroups := [group "xylo" [3, 4, 5] [.right, .left, .right]]
      isMeso := true }
  , { publishedName := "D-threo-Hexo-2,4-diulose", family := .diketose, chainLength := 6
      carbonyls := [ketone 2, ketone 4]
      configurationGroups := [group "D-threo" [3, 5] [.left, .right]] }
  , { publishedName := "alpha-D-threo-Hexo-2,4-diulo-2,5-furanose"
      family := .diketose, chainLength := 6, carbonyls := [ketone 2, ketone 4]
      configurationGroups := [group "D-threo" [3, 5] [.left, .right]]
      cyclicForm? := some
        { closure := ⟨2, 5, 5⟩, descriptor? := some .alpha, methylGlycoside := false } }
  , { publishedName := "L-altro-Octo-4,5-diulose", family := .diketose, chainLength := 8
      carbonyls := [ketone 4, ketone 5]
      configurationGroups := [group "L-altro" [2, 3, 6, 7] [.right, .left, .left, .left]]
      rejectedName? := some "L-talo-octo-4,5-diulose" }
  , { publishedName := "L-glycero-D-manno-Nono-2,7-diulose"
      family := .diketose, chainLength := 9, carbonyls := [ketone 2, ketone 7]
      configurationGroups :=
        [ group "L-glycero" [8] [.left]
        , group "D-manno" [3, 4, 5, 6] [.left, .left, .right, .right] ] }
  , { publishedName := "D-glycero-D-ido-Nono-3,6-diulose"
      family := .diketose, chainLength := 9, carbonyls := [ketone 3, ketone 6]
      configurationGroups :=
        [ group "D-glycero" [8] [.right]
        , group "D-ido" [2, 4, 5, 7] [.left, .right, .left, .right] ] } ]

@[simp] theorem diketose_meaning_count : diketoseMeanings.length = 7 := rfl

@[simp] theorem diketose_published_names_exact :
    diketoseMeanings.map DicarbonylMeaning.publishedName =
      [ "L-threo-Hexo-2,5-diulose"
      , "meso-xylo-Hepto-2,6-diulose"
      , "D-threo-Hexo-2,4-diulose"
      , "alpha-D-threo-Hexo-2,4-diulo-2,5-furanose"
      , "L-altro-Octo-4,5-diulose"
      , "L-glycero-D-manno-Nono-2,7-diulose"
      , "D-glycero-D-ido-Nono-3,6-diulose" ] := rfl

def ketoaldoseMeanings : List DicarbonylMeaning :=
  [ { publishedName := "D-arabino-Hexos-3-ulose", family := .ketoaldose, chainLength := 6
      carbonyls := [aldehyde 1, ketone 3]
      configurationGroups := [group "D-arabino" [2, 4, 5] [.left, .right, .right]] }
  , { publishedName := "Methyl beta-D-xylo-hexopyranosid-4-ulose"
      family := .ketoaldose, chainLength := 6, carbonyls := [aldehyde 1, ketone 4]
      configurationGroups := [group "D-xylo" [2, 3, 5] [.right, .left, .right]]
      cyclicForm? := some
        { closure := ⟨1, 5, 6⟩, descriptor? := some .beta, methylGlycoside := true } }
  , { publishedName := "Methyl alpha-L-xylo-hexos-2-ulo-2,5-furanoside"
      family := .ketoaldose, chainLength := 6, carbonyls := [aldehyde 1, ketone 2]
      configurationGroups := [group "L-xylo" [3, 4, 5] [.left, .right, .left]]
      cyclicForm? := some
        { closure := ⟨2, 5, 5⟩, descriptor? := some .alpha, methylGlycoside := true }
      erratum? := some "The H at C5 was omitted from the left-hand version" } ]

@[simp] theorem ketoaldose_meaning_count : ketoaldoseMeanings.length = 3 := rfl

@[simp] theorem ketoaldose_published_names_exact :
    ketoaldoseMeanings.map DicarbonylMeaning.publishedName =
      [ "D-arabino-Hexos-3-ulose"
      , "Methyl beta-D-xylo-hexopyranosid-4-ulose"
      , "Methyl alpha-L-xylo-hexos-2-ulo-2,5-furanoside" ] := rfl

structure DiketoseRule where
  terminalSeReplacedByDiulose : Bool
  carbonylLocantsLowestPossible : Bool
  carbonylLocantsBeforeEnding : Bool
  carbohydrateParentChoiceBreaksTies : Bool
  nonchiralCentersIgnoredForPrefixes : Bool
  closureCitesCarbonylFirst : Bool
  deriving DecidableEq, Repr

def diketoseRule : DiketoseRule where
  terminalSeReplacedByDiulose := true
  carbonylLocantsLowestPossible := true
  carbonylLocantsBeforeEnding := true
  carbohydrateParentChoiceBreaksTies := true
  nonchiralCentersIgnoredForPrefixes := true
  closureCitesCarbonylFirst := true

structure KetoaldoseRule where
  terminalEReplacedByUlose : Bool
  aldehydeCarbonIsOne : Bool
  aldehydeLocantOmitted : Bool
  ketoneLocantIsInfix : Bool
  ketoneLocantTwoMayBeOmitted : Bool
  locantTwoRetainedForClarity : Bool
  closureCitesCarbonylFirst : Bool
  ringDesignatorPositionDependsOnClosingCarbonyl : Bool
  deriving DecidableEq, Repr

def ketoaldoseRule : KetoaldoseRule where
  terminalEReplacedByUlose := true
  aldehydeCarbonIsOne := true
  aldehydeLocantOmitted := true
  ketoneLocantIsInfix := true
  ketoneLocantTwoMayBeOmitted := true
  locantTwoRetainedForClarity := true
  closureCitesCarbonylFirst := true
  ringDesignatorPositionDependsOnClosingCarbonyl := true

/-! ## Total typed lookup and reviewed batch -/

inductive ImageSourceMeaning where
  | diketose (meaning : DicarbonylMeaning)
  | ketoaldose (meaning : DicarbonylMeaning)
  deriving DecidableEq, Repr

def sourceMeaning? : String → Option ImageSourceMeaning
  | "2carb/2C1gif/111A.GIF" => diketoseMeanings[0]?.map ImageSourceMeaning.diketose
  | "2carb/2C1gif/111B.GIF" => diketoseMeanings[1]?.map ImageSourceMeaning.diketose
  | "2carb/2C1gif/112A.GIF" => diketoseMeanings[2]?.map ImageSourceMeaning.diketose
  | "2carb/2C1gif/112B.GIF" => diketoseMeanings[3]?.map ImageSourceMeaning.diketose
  | "2carb/2C1gif/112C.GIF" => diketoseMeanings[4]?.map ImageSourceMeaning.diketose
  | "2carb/2C1gif/112D.GIF" => diketoseMeanings[5]?.map ImageSourceMeaning.diketose
  | "2carb/2C1gif/112E.GIF" => diketoseMeanings[6]?.map ImageSourceMeaning.diketose
  | "2carb/2C1gif/121A.GIF" => ketoaldoseMeanings[0]?.map ImageSourceMeaning.ketoaldose
  | "2carb/2C1gif/121B.GIF" => ketoaldoseMeanings[1]?.map ImageSourceMeaning.ketoaldose
  | "2carb/2C1gif/121C.GIF" => ketoaldoseMeanings[2]?.map ImageSourceMeaning.ketoaldose
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

/-! ## Exact advance from the prior 1,688/520 overlay -/

def remainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  priorRemainingImageRows.drop 10

@[simp] theorem remaining_image_count : remainingImageRows.length = 339 := by
  simp [remainingImageRows, priorRemainingImageRows]

theorem rows_append_remaining_eq_prior :
    rows ++ remainingImageRows = priorRemainingImageRows := by
  exact List.take_append_drop 10 priorRemainingImageRows

def advancedMaterializedProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings.advancedMaterializedProvisions ++
    provisions

def advancedMaterializedBatch :
    GlobalNonDescriptorSourceMeaningBatch advancedMaterializedProvisions :=
  GlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings.advancedMaterializedBatch.append
    visionReviewedGraphLevelBatch

@[simp] theorem advanced_materialized_count : advancedMaterializedProvisions.length = 1698 := by
  simp [advancedMaterializedProvisions]

def advancedMissingProvisions : List IUPACNormativeProvision :=
  sourceProvisions .blueBook2013Appendix3 ++
    remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem advanced_missing_count : advancedMissingProvisions.length = 510 := by
  simp [advancedMissingProvisions]

set_option maxRecDepth 8192 in
theorem selected_then_advanced_missing_perm_prior_missing :
    (provisions ++ advancedMissingProvisions).Perm
      GlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings.advancedMissingProvisions := by
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
    _ = GlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings.advancedMissingProvisions := by
      rfl

theorem mem_prior_missing_iff_selected_or_advanced_missing
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings.advancedMissingProvisions ↔
      provision ∈ provisions ∨ provision ∈ advancedMissingProvisions := by
  simpa only [List.mem_append] using
    (selected_then_advanced_missing_perm_prior_missing.mem_iff).symm

private theorem selected_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ provisions) :
    provision ∈ GlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_left _ member)

private theorem advanced_missing_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ advancedMissingProvisions) :
    provision ∈ GlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_right _ member)

private theorem selected_append_advanced_missing_nodup :
    (provisions ++ advancedMissingProvisions).Nodup :=
  GlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings.advanced_missing_nodup.perm
    selected_then_advanced_missing_perm_prior_missing.symm

theorem advanced_missing_nodup : advancedMissingProvisions.Nodup :=
  List.Nodup.of_append_right selected_append_advanced_missing_nodup

private theorem selected_disjoint_advanced_missing :
    provisions.Disjoint advancedMissingProvisions :=
  List.disjoint_of_nodup_append selected_append_advanced_missing_nodup

private theorem prior_materialized_disjoint_selected :
    GlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings.advancedMaterializedProvisions.Disjoint
      provisions := by
  rw [List.disjoint_left]
  intro provision materialized selected
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings.advanced_materialized_disjoint_missing)
      materialized (selected_subset_prior_missing selected)

theorem advanced_materialized_nodup : advancedMaterializedProvisions.Nodup := by
  exact GlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings.advanced_materialized_nodup.append
    provisions_nodup prior_materialized_disjoint_selected

theorem advanced_materialized_disjoint_missing :
    advancedMaterializedProvisions.Disjoint advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision advanced missing
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings.advanced_materialized_disjoint_missing)
        priorMaterialized (advanced_missing_subset_prior_missing missing)
  · exact (List.disjoint_left.mp selected_disjoint_advanced_missing) selected missing

theorem reviewed_disjoint_advanced_materialized :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMaterializedProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed advanced
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings.reviewed_disjoint_advanced_materialized)
        reviewed priorMaterialized
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings.reviewed_disjoint_advanced_missing)
        reviewed (selected_subset_prior_missing selected)

theorem reviewed_disjoint_advanced_missing :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed missing
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings.reviewed_disjoint_advanced_missing)
      reviewed (advanced_missing_subset_prior_missing missing)

set_option maxRecDepth 8192 in
theorem mem_reviewed_or_advanced_materialized_or_missing_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions ∨
      provision ∈ advancedMaterializedProvisions ∨
        provision ∈ advancedMissingProvisions ↔
      provision ∈ globalNonDescriptorProvisions := by
  rw [← GlobalNonDescriptorCarbohydrateKetoseImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff]
  rw [mem_prior_missing_iff_selected_or_advanced_missing]
  simp only [advancedMaterializedProvisions, List.mem_append]
  tauto

theorem advanced_live_frontier_counts :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.length = 92 ∧
      advancedMaterializedProvisions.length = 1698 ∧
        advancedMissingProvisions.length = 510 ∧
          92 + 1698 + 510 = 2300 := by
  exact ⟨GlobalNonDescriptorSourceMeaningProgress.reviewed_count,
    advanced_materialized_count, advanced_missing_count, by omega⟩

end GlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings.frozen_artifact_data_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings.diketose_published_names_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings.ketoaldose_published_names_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings.visionReviewedGraphLevelBatch
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings.selected_then_advanced_missing_perm_prior_missing
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff
