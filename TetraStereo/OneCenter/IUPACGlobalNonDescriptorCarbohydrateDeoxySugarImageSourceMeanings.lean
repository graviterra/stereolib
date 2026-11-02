import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings
import TetraStereo.KernelOnly

set_option autoImplicit false















namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings

open GlobalNonDescriptorSourceMeaningConstructor

def priorRemainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  GlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings.remainingImageRows

def rows : List Carbohydrate1996ImageAudit.Provision := priorRemainingImageRows.take 17

def artifactOf : Carbohydrate1996ImageAudit.Provision →
    Carbohydrate1996ImageAudit.ImageArtifact
  | .imageArtifact artifact => artifact

def artifacts : List Carbohydrate1996ImageAudit.ImageArtifact := rows.map artifactOf

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem row_count : rows.length = 17 := by
  simp [rows, priorRemainingImageRows]

@[simp] theorem artifact_count : artifacts.length = 17 := by simp [artifacts]
@[simp] theorem provision_count : provisions.length = 17 := by simp [provisions]

set_option maxRecDepth 4096 in
@[simp] theorem frozen_artifact_data_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.data =
      [ ⟨"2carb/2C1gif/131A.GIF", "f3bc07fb8171c1d5a84ea9f05dd5b065d0227afc5c1bad9dbd0f54552e9ebfc1", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/131B.GIF", "782a6dc5f42261b93b803fc461287f583362b6d51153e353caad19d23b3edfd3", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/131C.GIF", "a2236a932ba76a30f04a3ffbd0001115d375851632a6bdeeb85f210677336dee", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/131D.GIF", "ec2806719f645e9ac95f05890d2ef80a5c7dfd71b6d2e259e7cf27b9a7dc199c", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/131E.GIF", "2d28e221645cb3beb2135a9e262d39fe22eb4f987197977ddddd0e58cc25ca4d", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/131F.GIF", "281a6129820b48d1733b50070bba67863dd746144eff0167350dc7127648f46b", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/132.GIF", "6da9b3b162a47a3e80ef6a613182e39d606b72f80095be0f19f30a938bee827a", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/133A.GIF", "0df5777613fc16b964112df6f62b48b9fe3d19b2409aa7d3178c4fe99219b6db", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/133B.GIF", "20a9caf9b94bc1bad084ca81da9dcef1b693b5a3e90eec0a006f7b6be9b85325", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/133C.GIF", "ceec4b002fa4698025c7b43fc28d5539d7ccc44bf035cf50486d7d797568f91b", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/133D.GIF", "fd26a0173683b9cad1fde62264d4daa547622fa100b8c053ee4af73b12b4d37b", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/133E.GIF", "62d574c3ebff04ae8ff4567b252dfae540bd481573aa3112e3688174c10f06a4", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/133F.GIF", "4630d5826b4fa8dc27e8bdf8b6845a074bdcccc7b403c7facfbe6782dff7bdbd", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/133G.GIF", "4850b72ff05873a02c107a8ec7688d351cad7b1aa690da55748b346a70b6ad52", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/133H.GIF", "3a05a87ad01dc77ea3f4ef59019a14ee351e83d36bd7fd7cc59dac9cde861e3a", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/134A.GIF", "6bd50c9d2fc35627ef4d7c4f5638663730c77b016628ebf031cf4b1a30bcee09", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/134B.GIF", "999b0fcb1a6ca881fc27edde85cb3572ca273373d49800739d2cb584f27fe6d4", .numberedOrChartStructure⟩ ] := by
  decide

set_option maxRecDepth 4096 in
@[simp] theorem source_pages_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 17 ["13.html"] := by
  decide

set_option maxRecDepth 4096 in
private theorem rows_nodup : rows.Nodup := by
  decide

theorem provisions_nodup : provisions.Nodup := by
  exact rows_nodup.map (by intro left right equal; cases equal; rfl)

/-! ## Typed deoxy-sugar structures -/

inductive HydroxylSide where
  | left | right
  deriving DecidableEq, Repr, Inhabited

structure ConfigurationalGroup where
  prefixText : String
  locants : List Nat
  deriving DecidableEq, Repr, Inhabited

def ConfigurationalGroup.wellFormed (group : ConfigurationalGroup) : Bool :=
  !group.prefixText.isEmpty && !group.locants.isEmpty && group.locants.Nodup

inductive AnomericDescriptor where
  | alpha | beta
  deriving DecidableEq, Repr, Inhabited

structure CyclicForm where
  potentialCarbonylLocant : Nat
  oxygenBearingCarbonLocant : Nat
  ringSize : Nat
  descriptor? : Option AnomericDescriptor
  deriving DecidableEq, Repr, Inhabited

structure Substituent where
  locant : Nat
  name : String
  deriving DecidableEq, Repr, Inhabited

inductive DeoxyMeaningKind where
  | retainedName | derivedTrivial | systematic | alditol
  deriving DecidableEq, Repr, Inhabited

structure DeoxyMeaning where
  primaryName : String
  equivalentName? : Option String := none
  rejectedNames : List String := []
  kind : DeoxyMeaningKind
  chainLength : Nat
  deoxyLocants : List Nat
  configurationGroups : List ConfigurationalGroup
  fischerHydroxylSides : List (Nat × HydroxylSide) := []
  cyclicForm? : Option CyclicForm := none
  carbonylLocants : List Nat := []
  substituents : List Substituent := []
  phosphateLocant? : Option Nat := none
  methylGlycoside : Bool := false
  terminalMethylLocants : List Nat := []
  deriving DecidableEq, Repr, Inhabited

def locantInChain (chainLength locant : Nat) : Bool :=
  decide (0 < locant ∧ locant ≤ chainLength)

def DeoxyMeaning.cyclicFormWellFormed (meaning : DeoxyMeaning) : Bool :=
  match meaning.cyclicForm? with
  | none => !meaning.methylGlycoside
  | some cyclic =>
      meaning.carbonylLocants.contains cyclic.potentialCarbonylLocant &&
        locantInChain meaning.chainLength cyclic.oxygenBearingCarbonLocant &&
        decide (cyclic.potentialCarbonylLocant ≠ cyclic.oxygenBearingCarbonLocant) &&
        cyclic.ringSize ==
          Nat.max cyclic.potentialCarbonylLocant cyclic.oxygenBearingCarbonLocant -
            Nat.min cyclic.potentialCarbonylLocant cyclic.oxygenBearingCarbonLocant + 2 &&
        (!meaning.methylGlycoside || cyclic.descriptor?.isSome)

def DeoxyMeaning.wellFormed (meaning : DeoxyMeaning) : Bool :=
  !meaning.primaryName.isEmpty && decide (1 < meaning.chainLength) &&
    meaning.deoxyLocants.Nodup &&
      meaning.deoxyLocants.all (locantInChain meaning.chainLength) &&
    meaning.configurationGroups.all ConfigurationalGroup.wellFormed &&
      (meaning.configurationGroups.flatMap ConfigurationalGroup.locants).Nodup &&
      (meaning.configurationGroups.flatMap ConfigurationalGroup.locants).all
        (locantInChain meaning.chainLength) &&
    (meaning.fischerHydroxylSides.map Prod.fst).Nodup &&
      (meaning.fischerHydroxylSides.map Prod.fst).all (locantInChain meaning.chainLength) &&
    meaning.carbonylLocants.Nodup &&
      meaning.carbonylLocants.all (locantInChain meaning.chainLength) &&
    (meaning.substituents.map Substituent.locant).Nodup &&
      meaning.substituents.all fun substituent =>
        locantInChain meaning.chainLength substituent.locant && !substituent.name.isEmpty &&
    (match meaning.phosphateLocant? with
      | none => true
      | some locant => locantInChain meaning.chainLength locant) &&
    meaning.terminalMethylLocants.Nodup &&
      meaning.terminalMethylLocants.all fun locant =>
        locantInChain meaning.chainLength locant && meaning.deoxyLocants.contains locant &&
    meaning.cyclicFormWellFormed

private def group (prefixText : String) (locants : List Nat) : ConfigurationalGroup :=
  { prefixText, locants }

private def pyranose (descriptor? : Option AnomericDescriptor) : CyclicForm :=
  ⟨1, 5, 6, descriptor?⟩

def retainedNameMeanings : List DeoxyMeaning :=
  [ { primaryName := "alpha-L-Fucopyranose"
      equivalentName? := some "6-Deoxy-alpha-L-galactopyranose"
      kind := .retainedName, chainLength := 6, deoxyLocants := [6]
      configurationGroups := [group "L-galacto" [2, 3, 4, 5]]
      cyclicForm? := some (pyranose (some .alpha)), carbonylLocants := [1]
      terminalMethylLocants := [6] }
  , { primaryName := "beta-D-Quinovopyranose"
      equivalentName? := some "6-Deoxy-beta-D-glucopyranose"
      kind := .retainedName, chainLength := 6, deoxyLocants := [6]
      configurationGroups := [group "D-gluco" [2, 3, 4, 5]]
      cyclicForm? := some (pyranose (some .beta)), carbonylLocants := [1]
      terminalMethylLocants := [6] }
  , { primaryName := "L-Rhamnopyranose"
      equivalentName? := some "6-Deoxy-L-mannopyranose"
      kind := .retainedName, chainLength := 6, deoxyLocants := [6]
      configurationGroups := [group "L-manno" [2, 3, 4, 5]]
      cyclicForm? := some (pyranose none), carbonylLocants := [1]
      terminalMethylLocants := [6] }
  , { primaryName := "2,6-Dideoxy-beta-D-ribo-hexopyranose"
      equivalentName? := some "beta-Digitoxopyranose"
      kind := .retainedName, chainLength := 6, deoxyLocants := [2, 6]
      configurationGroups := [group "D-ribo" [3, 4, 5]]
      cyclicForm? := some (pyranose (some .beta)), carbonylLocants := [1]
      terminalMethylLocants := [6] }
  , { primaryName := "3,6-Dideoxy-beta-D-xylo-hexopyranose"
      equivalentName? := some "beta-Abequopyranose"
      kind := .retainedName, chainLength := 6, deoxyLocants := [3, 6]
      configurationGroups := [group "D-xylo" [2, 4, 5]]
      cyclicForm? := some (pyranose (some .beta)), carbonylLocants := [1]
      terminalMethylLocants := [6] }
  , { primaryName := "3,6-Dideoxy-beta-D-arabino-hexopyranose"
      equivalentName? := some "beta-Tyvelopyranose"
      kind := .retainedName, chainLength := 6, deoxyLocants := [3, 6]
      configurationGroups := [group "D-arabino" [2, 4, 5]]
      cyclicForm? := some (pyranose (some .beta)), carbonylLocants := [1]
      terminalMethylLocants := [6] } ]

@[simp] theorem retained_name_count : retainedNameMeanings.length = 6 := rfl

@[simp] theorem retained_primary_names_exact :
    retainedNameMeanings.map DeoxyMeaning.primaryName =
      [ "alpha-L-Fucopyranose"
      , "beta-D-Quinovopyranose"
      , "L-Rhamnopyranose"
      , "2,6-Dideoxy-beta-D-ribo-hexopyranose"
      , "3,6-Dideoxy-beta-D-xylo-hexopyranose"
      , "3,6-Dideoxy-beta-D-arabino-hexopyranose" ] := rfl

def deoxyribosePhosphate : DeoxyMeaning :=
  { primaryName := "2-Deoxy-D-erythro-pentofuranose 5-phosphate"
    kind := .derivedTrivial, chainLength := 5, deoxyLocants := [2]
    configurationGroups := [group "D-erythro" [3, 4]]
    cyclicForm? := some ⟨1, 4, 5, none⟩, carbonylLocants := [1]
    phosphateLocant? := some 5 }

def systematicMeanings : List DeoxyMeaning :=
  [ { primaryName := "4-Deoxy-beta-D-xylo-hexopyranose"
      rejectedNames := ["4-deoxy-beta-D-galactopyranose"]
      kind := .systematic, chainLength := 6, deoxyLocants := [4]
      configurationGroups := [group "D-xylo" [2, 3, 5]]
      cyclicForm? := some (pyranose (some .beta)), carbonylLocants := [1] }
  , { primaryName := "2-Deoxy-D-ribo-hexose"
      rejectedNames := ["2-deoxy-D-allose"]
      kind := .systematic, chainLength := 6, deoxyLocants := [2]
      configurationGroups := [group "D-ribo" [3, 4, 5]]
      fischerHydroxylSides := [(3, .right), (4, .right), (5, .right)]
      carbonylLocants := [1] }
  , { primaryName := "2-Deoxy-alpha-D-allo-heptopyranose"
      kind := .systematic, chainLength := 7, deoxyLocants := [2]
      configurationGroups := [group "D-allo" [3, 4, 5, 6]]
      cyclicForm? := some (pyranose (some .alpha)), carbonylLocants := [1] }
  , { primaryName := "1-Deoxy-L-glycero-D-altro-oct-2-ulose"
      kind := .systematic, chainLength := 8, deoxyLocants := [1]
      configurationGroups := [group "L-glycero" [7], group "D-altro" [3, 4, 5, 6]]
      fischerHydroxylSides :=
        [(3, .left), (4, .right), (5, .right), (6, .right), (7, .left)]
      carbonylLocants := [2], terminalMethylLocants := [1] }
  , { primaryName :=
        "Methyl 3-azido-4-O-benzoyl-6-bromo-2,3,6-trideoxy-2-fluoro-alpha-D-allopyranoside"
      kind := .systematic, chainLength := 6, deoxyLocants := [2, 3, 6]
      configurationGroups := [group "D-allo" [2, 3, 4, 5]]
      cyclicForm? := some (pyranose (some .alpha)), carbonylLocants := [1]
      substituents := [⟨3, "azido"⟩, ⟨4, "O-benzoyl"⟩, ⟨6, "bromo"⟩, ⟨2, "fluoro"⟩]
      methylGlycoside := true }
  , { primaryName := "3-Deoxy-D-ribo-hexose"
      rejectedNames := ["3-deoxy-D-erythro-D-glycero-hexose"]
      kind := .systematic, chainLength := 6, deoxyLocants := [3]
      configurationGroups := [group "D-ribo" [2, 4, 5]]
      fischerHydroxylSides := [(2, .right), (4, .right), (5, .right)]
      carbonylLocants := [1] }
  , { primaryName := "5-Deoxy-D-arabino-hept-3-ulose"
      rejectedNames := ["5-deoxy-D-glycero-D-glycero-L-glycero-hept-3-ulose"]
      kind := .systematic, chainLength := 7, deoxyLocants := [5]
      configurationGroups := [group "D-arabino" [2, 4, 6]]
      fischerHydroxylSides := [(2, .left), (4, .right), (6, .right)]
      carbonylLocants := [3] }
  , { primaryName := "6-Deoxy-L-gluco-oct-2-ulose"
      rejectedNames := ["6-deoxy-L-glycero-L-xylo-oct-2-ulose"]
      kind := .systematic, chainLength := 8, deoxyLocants := [6]
      configurationGroups := [group "L-gluco" [3, 4, 5, 7]]
      fischerHydroxylSides := [(3, .left), (4, .right), (5, .left), (7, .left)]
      carbonylLocants := [2] } ]

@[simp] theorem systematic_meaning_count : systematicMeanings.length = 8 := rfl

@[simp] theorem systematic_primary_names_exact :
    systematicMeanings.map DeoxyMeaning.primaryName =
      [ "4-Deoxy-beta-D-xylo-hexopyranose"
      , "2-Deoxy-D-ribo-hexose"
      , "2-Deoxy-alpha-D-allo-heptopyranose"
      , "1-Deoxy-L-glycero-D-altro-oct-2-ulose"
      , "Methyl 3-azido-4-O-benzoyl-6-bromo-2,3,6-trideoxy-2-fluoro-alpha-D-allopyranoside"
      , "3-Deoxy-D-ribo-hexose"
      , "5-Deoxy-D-arabino-hept-3-ulose"
      , "6-Deoxy-L-gluco-oct-2-ulose" ] := rfl

def alditolMeanings : List DeoxyMeaning :=
  [ { primaryName := "1-Deoxy-D-arabinitol"
      rejectedNames := ["5-deoxy-D-lyxitol"]
      kind := .alditol, chainLength := 5, deoxyLocants := [1]
      configurationGroups := [group "D-arabinitol" [2, 3, 4]]
      fischerHydroxylSides := [(2, .left), (3, .right), (4, .right)]
      terminalMethylLocants := [1] }
  , { primaryName := "5-Deoxy-D-arabinitol"
      rejectedNames := ["1-deoxy-D-lyxitol"]
      kind := .alditol, chainLength := 5, deoxyLocants := [5]
      configurationGroups := [group "D-arabinitol" [2, 3, 4]]
      fischerHydroxylSides := [(2, .left), (3, .right), (4, .left)]
      terminalMethylLocants := [5] } ]

@[simp] theorem alditol_meaning_count : alditolMeanings.length = 2 := rfl

@[simp] theorem alditol_primary_names_exact :
    alditolMeanings.map DeoxyMeaning.primaryName =
      ["1-Deoxy-D-arabinitol", "5-Deoxy-D-arabinitol"] := rfl

def allMeanings : List DeoxyMeaning :=
  retainedNameMeanings ++ [deoxyribosePhosphate] ++ systematicMeanings ++ alditolMeanings

@[simp] theorem all_meaning_count : allMeanings.length = 17 := by
  simp [allMeanings]

structure DeoxyRule where
  retainedNamesPreferredOnlyForUnmodifiedSugars : Bool
  systematicNamesPreferredForDerivatives : Bool
  terminalMethylNamedOmegaDeoxyNotCMethyl : Bool
  deoxyWithTrivialNameAllowedWhenNoChiralCenterRemoved : Bool
  deoxyRemovalOfChiralCenterCreatesRedundancy : Bool
  configurationalPrefixesDescribePresentCenters : Bool
  configurationalGroupsCitedFarthestFirst : Bool
  methyleneInterruptionsIgnored : Bool
  deoxyIsDetachableAlphabetizedPrefix : Bool
  anomericHydroxyToHydrogenRoutesToAnhydroAlditol : Bool
  aldehydeToTerminalMethylUsesDeoxyAlditol : Bool
  deriving DecidableEq, Repr

def deoxyRule : DeoxyRule where
  retainedNamesPreferredOnlyForUnmodifiedSugars := true
  systematicNamesPreferredForDerivatives := true
  terminalMethylNamedOmegaDeoxyNotCMethyl := true
  deoxyWithTrivialNameAllowedWhenNoChiralCenterRemoved := true
  deoxyRemovalOfChiralCenterCreatesRedundancy := true
  configurationalPrefixesDescribePresentCenters := true
  configurationalGroupsCitedFarthestFirst := true
  methyleneInterruptionsIgnored := true
  deoxyIsDetachableAlphabetizedPrefix := true
  anomericHydroxyToHydrogenRoutesToAnhydroAlditol := true
  aldehydeToTerminalMethylUsesDeoxyAlditol := true

/-! ## Total typed lookup and reviewed batch -/

def sourceMeaning? : String → Option DeoxyMeaning
  | "2carb/2C1gif/131A.GIF" => retainedNameMeanings[0]?
  | "2carb/2C1gif/131B.GIF" => retainedNameMeanings[1]?
  | "2carb/2C1gif/131C.GIF" => retainedNameMeanings[2]?
  | "2carb/2C1gif/131D.GIF" => retainedNameMeanings[3]?
  | "2carb/2C1gif/131E.GIF" => retainedNameMeanings[4]?
  | "2carb/2C1gif/131F.GIF" => retainedNameMeanings[5]?
  | "2carb/2C1gif/132.GIF" => some deoxyribosePhosphate
  | "2carb/2C1gif/133A.GIF" => systematicMeanings[0]?
  | "2carb/2C1gif/133B.GIF" => systematicMeanings[1]?
  | "2carb/2C1gif/133C.GIF" => systematicMeanings[2]?
  | "2carb/2C1gif/133D.GIF" => systematicMeanings[3]?
  | "2carb/2C1gif/133E.GIF" => systematicMeanings[4]?
  | "2carb/2C1gif/133F.GIF" => systematicMeanings[5]?
  | "2carb/2C1gif/133G.GIF" => systematicMeanings[6]?
  | "2carb/2C1gif/133H.GIF" => systematicMeanings[7]?
  | "2carb/2C1gif/134A.GIF" => alditolMeanings[0]?
  | "2carb/2C1gif/134B.GIF" => alditolMeanings[1]?
  | _ => none

def all_image_meanings_present : Bool :=
  artifacts.all fun artifact => (sourceMeaning? artifact.data.relativePath).isSome

structure VisionReviewedImageMeaning where
  artifactData : Carbohydrate1996ImageAudit.ImageArtifactData
  sourcePages : List String
  sourceMeaning : Option DeoxyMeaning
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
    visionReviewedGraphLevelBatch.entries.length = 17 := by
  rw [visionReviewedGraphLevelBatch.entries_length, provision_count]

/-! ## Exact advance from the prior 1,698/510 overlay -/

def remainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  priorRemainingImageRows.drop 17

@[simp] theorem remaining_image_count : remainingImageRows.length = 322 := by
  simp [remainingImageRows, priorRemainingImageRows]

theorem rows_append_remaining_eq_prior :
    rows ++ remainingImageRows = priorRemainingImageRows := by
  exact List.take_append_drop 17 priorRemainingImageRows

def advancedMaterializedProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings.advancedMaterializedProvisions ++
    provisions

def advancedMaterializedBatch :
    GlobalNonDescriptorSourceMeaningBatch advancedMaterializedProvisions :=
  GlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings.advancedMaterializedBatch.append
    visionReviewedGraphLevelBatch

@[simp] theorem advanced_materialized_count : advancedMaterializedProvisions.length = 1715 := by
  simp [advancedMaterializedProvisions]

def advancedMissingProvisions : List IUPACNormativeProvision :=
  sourceProvisions .blueBook2013Appendix3 ++
    remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem advanced_missing_count : advancedMissingProvisions.length = 493 := by
  simp [advancedMissingProvisions]

set_option maxRecDepth 8192 in
theorem selected_then_advanced_missing_perm_prior_missing :
    (provisions ++ advancedMissingProvisions).Perm
      GlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings.advancedMissingProvisions := by
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
    _ = GlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings.advancedMissingProvisions := by
      rfl

theorem mem_prior_missing_iff_selected_or_advanced_missing
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings.advancedMissingProvisions ↔
      provision ∈ provisions ∨ provision ∈ advancedMissingProvisions := by
  simpa only [List.mem_append] using
    (selected_then_advanced_missing_perm_prior_missing.mem_iff).symm

private theorem selected_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ provisions) :
    provision ∈ GlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_left _ member)

private theorem advanced_missing_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ advancedMissingProvisions) :
    provision ∈ GlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_right _ member)

private theorem selected_append_advanced_missing_nodup :
    (provisions ++ advancedMissingProvisions).Nodup :=
  GlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings.advanced_missing_nodup.perm
    selected_then_advanced_missing_perm_prior_missing.symm

theorem advanced_missing_nodup : advancedMissingProvisions.Nodup :=
  List.Nodup.of_append_right selected_append_advanced_missing_nodup

private theorem selected_disjoint_advanced_missing :
    provisions.Disjoint advancedMissingProvisions :=
  List.disjoint_of_nodup_append selected_append_advanced_missing_nodup

private theorem prior_materialized_disjoint_selected :
    GlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings.advancedMaterializedProvisions.Disjoint
      provisions := by
  rw [List.disjoint_left]
  intro provision materialized selected
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings.advanced_materialized_disjoint_missing)
      materialized (selected_subset_prior_missing selected)

theorem advanced_materialized_nodup : advancedMaterializedProvisions.Nodup := by
  exact GlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings.advanced_materialized_nodup.append
    provisions_nodup prior_materialized_disjoint_selected

theorem advanced_materialized_disjoint_missing :
    advancedMaterializedProvisions.Disjoint advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision advanced missing
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings.advanced_materialized_disjoint_missing)
        priorMaterialized (advanced_missing_subset_prior_missing missing)
  · exact (List.disjoint_left.mp selected_disjoint_advanced_missing) selected missing

theorem reviewed_disjoint_advanced_materialized :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMaterializedProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed advanced
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings.reviewed_disjoint_advanced_materialized)
        reviewed priorMaterialized
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings.reviewed_disjoint_advanced_missing)
        reviewed (selected_subset_prior_missing selected)

theorem reviewed_disjoint_advanced_missing :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed missing
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings.reviewed_disjoint_advanced_missing)
      reviewed (advanced_missing_subset_prior_missing missing)

set_option maxRecDepth 8192 in
theorem mem_reviewed_or_advanced_materialized_or_missing_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions ∨
      provision ∈ advancedMaterializedProvisions ∨
        provision ∈ advancedMissingProvisions ↔
      provision ∈ globalNonDescriptorProvisions := by
  rw [← GlobalNonDescriptorCarbohydrateDiketoseKetoaldoseImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff]
  rw [mem_prior_missing_iff_selected_or_advanced_missing]
  simp only [advancedMaterializedProvisions, List.mem_append]
  tauto

theorem advanced_live_frontier_counts :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.length = 92 ∧
      advancedMaterializedProvisions.length = 1715 ∧
        advancedMissingProvisions.length = 493 ∧
          92 + 1715 + 493 = 2300 := by
  exact ⟨GlobalNonDescriptorSourceMeaningProgress.reviewed_count,
    advanced_materialized_count, advanced_missing_count, by omega⟩

end GlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings.frozen_artifact_data_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings.retained_primary_names_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings.systematic_primary_names_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings.visionReviewedGraphLevelBatch
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings.selected_then_advanced_missing_perm_prior_missing
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff
