import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateReverseRingClosureImageSourceMeanings
import TetraStereo.KernelOnly

set_option autoImplicit false















namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateConformationAldoseDialdoseImageSourceMeanings

open GlobalNonDescriptorSourceMeaningConstructor

def priorRemainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  GlobalNonDescriptorCarbohydrateReverseRingClosureImageSourceMeanings.remainingImageRows

def rows : List Carbohydrate1996ImageAudit.Provision := priorRemainingImageRows.take 11

def artifactOf : Carbohydrate1996ImageAudit.Provision →
    Carbohydrate1996ImageAudit.ImageArtifact
  | .imageArtifact artifact => artifact

def artifacts : List Carbohydrate1996ImageAudit.ImageArtifact := rows.map artifactOf

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem row_count : rows.length = 11 := by
  simp [rows, priorRemainingImageRows]

@[simp] theorem artifact_count : artifacts.length = 11 := by simp [artifacts]
@[simp] theorem provision_count : provisions.length = 11 := by simp [provisions]

set_option maxRecDepth 4096 in
@[simp] theorem frozen_artifact_data_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.data =
      [ ⟨"2carb/2C0gif/071A.GIF", "b20f1f7db94ff30fbf4a6bf56f76fe6155b9edcc34f3091894a417512bd76f56", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/071B.GIF", "1852667e592cf33f5b50638f4e99904a40dfa90f1dc89d0ec38ff2146f5dd2a0", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/074.GIF", "172e3a532a00429e7117a8aebc76a84a38923924be82a50f31e5111e39424f80", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/083A.GIF", "1ec6ed022df72d729a850f8c39f7da2f1185668f8a8b191e91dc66e77f4294d3", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/083B.GIF", "789ea60583862e29f9bd90ba36715ea102ca38762a5f9c2f707d35e58f4e0963", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/084.GIF", "65922a2e056cf988da549c8d9d4886425e3176b17b0b0a35af616c8e03c067cb", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/09A.GIF", "1e1d6b93f4f246469d4b0dcf1e8d2a6cd5e5e34c88ddc856ba649d2b5c3f58b4", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/09B.GIF", "eb9137c1eb1cf74a2343466c69ac8fb0aa0cfbf7d3386eec058b3eacf438662a", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/09C.GIF", "5eb1d472dccfbbaa1721437c5d994934692085695c157f44f8f3af259c3d20ec", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/09D.GIF", "d84177731ea1dc73f5e9a67a4bf7ccd681c58d3ba56dd978b5bd58882cb31629", .numberedOrChartStructure⟩
      , ⟨"2carb/2C0gif/09E.GIF", "365aef3b430f3626a9ec4a46c3947369769da294f1d63b799d786de375abbe8e", .numberedOrChartStructure⟩ ] := by
  decide

set_option maxRecDepth 4096 in
@[simp] theorem source_pages_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 3 ["06n07.html"] ++ List.replicate 8 ["08n09.html"] := by
  decide

set_option maxRecDepth 4096 in
private theorem rows_nodup : rows.Nodup := by
  decide

theorem provisions_nodup : provisions.Nodup := by
  exact rows_nodup.map (by intro left right equal; cases equal; rfl)

/-! ## 2-Carb-7 conformation semantics -/

inductive RingAtom where
  | carbon (locant : Nat)
  | oxygen (locant : Nat)
  | sulfur (locant : Nat)
  deriving DecidableEq, Repr, Inhabited

inductive SugarKind where
  | aldofuranose | aldopyranose | pyranoidLactone
  deriving DecidableEq, Repr, Inhabited

inductive RingShape where
  | envelope | twist | chair | boat | skew | halfChair
  deriving DecidableEq, Repr, Inhabited

structure ConformationEntry where
  publishedName : String
  sugarKind : SugarKind
  shape : RingShape
  ringAtoms : List RingAtom
  referencePlane : List RingAtom
  abovePlane : List RingAtom
  belowPlane : List RingAtom
  notationText : String
  erratum : Option String := none
  deriving DecidableEq, Repr, Inhabited

def ConformationEntry.wellFormed (entry : ConformationEntry) : Bool :=
  !entry.publishedName.isEmpty && !entry.notationText.isEmpty && entry.ringAtoms.Nodup &&
    !entry.referencePlane.isEmpty && entry.referencePlane.Nodup && entry.abovePlane.Nodup &&
      entry.belowPlane.Nodup && entry.referencePlane.all (entry.ringAtoms.contains ·) &&
        entry.abovePlane.all (entry.ringAtoms.contains ·) &&
          entry.belowPlane.all (entry.ringAtoms.contains ·) &&
            (entry.referencePlane.all fun atom => !entry.abovePlane.contains atom) &&
              (entry.referencePlane.all fun atom => !entry.belowPlane.contains atom) &&
                (entry.abovePlane.all fun atom => !entry.belowPlane.contains atom)

private def furanoseAtoms : List RingAtom :=
  [.carbon 1, .carbon 2, .carbon 3, .carbon 4, .oxygen 4]

private def pyranoseAtoms : List RingAtom :=
  [.carbon 1, .carbon 2, .carbon 3, .carbon 4, .carbon 5, .oxygen 5]

def glucopyranoseChair : ConformationEntry :=
  { publishedName := "alpha-D-glucopyranose-4C1"
    sugarKind := .aldopyranose
    shape := .chair
    ringAtoms := pyranoseAtoms
    referencePlane := [.carbon 2, .carbon 3, .carbon 5, .oxygen 5]
    abovePlane := [.carbon 4]
    belowPlane := [.carbon 1]
    notationText := "^4C_1" }

def chartEntries : List ConformationEntry :=
  [ { publishedName := "Methyl beta-D-arabinofuranoside-E2"
      sugarKind := .aldofuranose, shape := .envelope, ringAtoms := furanoseAtoms
      referencePlane := [.oxygen 4, .carbon 1, .carbon 3, .carbon 4]
      abovePlane := [], belowPlane := [.carbon 2], notationText := "E_2" }
  , { publishedName := "alpha-D-arabinofuranose-3E"
      sugarKind := .aldofuranose, shape := .envelope, ringAtoms := furanoseAtoms
      referencePlane := [.carbon 1, .carbon 2, .carbon 4, .oxygen 4]
      abovePlane := [.carbon 3], belowPlane := [], notationText := "^3E" }
  , { publishedName := "1,2-O-isopropylidene-beta-L-idofuranose-3T2"
      sugarKind := .aldofuranose, shape := .twist, ringAtoms := furanoseAtoms
      referencePlane := [.carbon 1, .oxygen 4, .carbon 4]
      abovePlane := [.carbon 3], belowPlane := [.carbon 2], notationText := "^3T_2" }
  , { publishedName := "2,3-O-isopropylidene-alpha-D-lyxofuranose-2T1"
      sugarKind := .aldofuranose, shape := .twist, ringAtoms := furanoseAtoms
      referencePlane := [.carbon 3, .carbon 4, .oxygen 4]
      abovePlane := [.carbon 2], belowPlane := [.carbon 1], notationText := "^2T_1" }
  , { publishedName := "alpha-L-arabinopyranose-4C1"
      sugarKind := .aldopyranose, shape := .chair, ringAtoms := pyranoseAtoms
      referencePlane := [.carbon 2, .carbon 3, .carbon 5, .oxygen 5]
      abovePlane := [.carbon 4], belowPlane := [.carbon 1], notationText := "^4C_1" }
  , { publishedName := "L-glucono-1,5-lactone-1C4"
      sugarKind := .pyranoidLactone, shape := .chair, ringAtoms := pyranoseAtoms
      referencePlane := [.carbon 2, .carbon 3, .carbon 5, .oxygen 5]
      abovePlane := [.carbon 1], belowPlane := [.carbon 4], notationText := "^1C_4" }
  , { publishedName := "Methyl 2,6-anhydro-alpha-D-altropyranoside-2,5B"
      sugarKind := .aldopyranose, shape := .boat, ringAtoms := pyranoseAtoms
      referencePlane := [.oxygen 5, .carbon 1, .carbon 3, .carbon 4]
      abovePlane := [.carbon 2, .carbon 5], belowPlane := [], notationText := "^2,5B" }
  , { publishedName := "1,4-anhydro-alpha-D-allopyranose-B1,4"
      sugarKind := .aldopyranose, shape := .boat, ringAtoms := pyranoseAtoms
      referencePlane := [.carbon 2, .carbon 3, .carbon 5, .oxygen 5]
      abovePlane := [], belowPlane := [.carbon 1, .carbon 4], notationText := "B_1,4" }
  , { publishedName := "1,2-O-ethylidene-alpha-D-glucopyranose-1S3"
      sugarKind := .aldopyranose, shape := .skew, ringAtoms := pyranoseAtoms
      referencePlane := [.carbon 2, .carbon 4, .carbon 5, .oxygen 5]
      abovePlane := [.carbon 1], belowPlane := [.carbon 3], notationText := "^1S_3" }
  , { publishedName := "beta-L-altropyranose-2SO"
      sugarKind := .aldopyranose, shape := .skew, ringAtoms := pyranoseAtoms
      referencePlane := [.carbon 1, .carbon 3, .carbon 4, .carbon 5]
      abovePlane := [.carbon 2], belowPlane := [.oxygen 5], notationText := "^2S_O" }
  , { publishedName := "Methyl 2,3-anhydro-5-thio-beta-L-lyxopyranoside-5HS"
      sugarKind := .aldopyranose, shape := .halfChair
      ringAtoms := [.carbon 1, .carbon 2, .carbon 3, .carbon 4, .carbon 5, .sulfur 5]
      referencePlane := [.carbon 1, .carbon 2, .carbon 3, .carbon 4]
      abovePlane := [.carbon 5], belowPlane := [.sulfur 5], notationText := "^5H_S"
      erratum := some "The S linking C5 to C1 was omitted from Chart III structure 11" }
  , { publishedName := "2,3-dideoxy-D-erythro-hex-2-enono-1,5-lactone-5E"
      sugarKind := .pyranoidLactone, shape := .envelope, ringAtoms := pyranoseAtoms
      referencePlane := [.carbon 1, .carbon 2, .carbon 3, .carbon 4, .oxygen 5]
      abovePlane := [.carbon 5], belowPlane := [], notationText := "^5E" } ]

@[simp] theorem chart_entry_count : chartEntries.length = 12 := by rfl

@[simp] theorem chart_published_names_exact :
    chartEntries.map ConformationEntry.publishedName =
      [ "Methyl beta-D-arabinofuranoside-E2"
      , "alpha-D-arabinofuranose-3E"
      , "1,2-O-isopropylidene-beta-L-idofuranose-3T2"
      , "2,3-O-isopropylidene-alpha-D-lyxofuranose-2T1"
      , "alpha-L-arabinopyranose-4C1"
      , "L-glucono-1,5-lactone-1C4"
      , "Methyl 2,6-anhydro-alpha-D-altropyranoside-2,5B"
      , "1,4-anhydro-alpha-D-allopyranose-B1,4"
      , "1,2-O-ethylidene-alpha-D-glucopyranose-1S3"
      , "beta-L-altropyranose-2SO"
      , "Methyl 2,3-anhydro-5-thio-beta-L-lyxopyranoside-5HS"
      , "2,3-dideoxy-D-erythro-hex-2-enono-1,5-lactone-5E" ] := by
  rfl

@[simp] theorem chart_notations_exact :
    chartEntries.map ConformationEntry.notationText =
      [ "E_2", "^3E", "^3T_2", "^2T_1", "^4C_1", "^1C_4"
      , "^2,5B", "B_1,4", "^1S_3", "^2S_O", "^5H_S", "^5E" ] := by
  rfl

structure EnantiomerMirrorPair where
  dFormName : String
  dFormNotation : String
  lFormName : String
  lFormNotation : String
  sameReferencePlane : List RingAtom
  deriving DecidableEq, Repr

def mirrorPair : EnantiomerMirrorPair where
  dFormName := "alpha-D-glucopyranose"
  dFormNotation := "^4C_1"
  lFormName := "alpha-L-glucopyranose"
  lFormNotation := "^1C_4"
  sameReferencePlane := [.carbon 2, .carbon 3, .carbon 5, .oxygen 5]

structure ConformationRule where
  descriptorAppendedToName : Bool
  superscriptIsClockwiseSide : Bool
  subscriptIsOppositeSide : Bool
  heteroatomsUseAtomicSymbols : Bool
  enantiomersUseDifferentDescriptors : Bool
  deriving DecidableEq, Repr

def conformationRule : ConformationRule where
  descriptorAppendedToName := true
  superscriptIsClockwiseSide := true
  subscriptIsOppositeSide := true
  heteroatomsUseAtomicSymbols := true
  enantiomersUseDifferentDescriptors := true

/-! ## 2-Carb-8 higher-aldose semantics -/

structure ConfigurationalGroup where
  prefixText : String
  locants : List Nat
  deriving DecidableEq, Repr

structure HigherAldoseMeaning where
  publishedName : String
  rejectedName? : Option String
  chainLength : Nat
  configurationalGroups : List ConfigurationalGroup
  ignoredAchiralLocants : List Nat
  deriving DecidableEq, Repr, Inhabited

def HigherAldoseMeaning.wellFormed (meaning : HigherAldoseMeaning) : Bool :=
  !meaning.publishedName.isEmpty && meaning.chainLength > 0 &&
    !meaning.configurationalGroups.isEmpty &&
      (meaning.configurationalGroups.all fun group =>
        !group.prefixText.isEmpty && !group.locants.isEmpty && group.locants.Nodup &&
          (group.locants.all fun locant => locant > 1 && locant < meaning.chainLength)) &&
      (meaning.configurationalGroups.flatMap ConfigurationalGroup.locants).Nodup &&
        meaning.ignoredAchiralLocants.Nodup &&
          ((meaning.configurationalGroups.flatMap ConfigurationalGroup.locants).all fun locant =>
            !meaning.ignoredAchiralLocants.contains locant)

def higherAldoseMeanings : List HigherAldoseMeaning :=
  [ { publishedName := "D-glycero-D-gluco-heptose"
      rejectedName? := some "D-gluco-D-glycero-heptose"
      chainLength := 7
      configurationalGroups := [⟨"D-glycero", [6]⟩, ⟨"D-gluco", [2, 3, 4, 5]⟩]
      ignoredAchiralLocants := [] }
  , { publishedName := "L-ribo-D-manno-nonose"
      rejectedName? := some "D-manno-L-ribo-nonose"
      chainLength := 9
      configurationalGroups := [⟨"L-ribo", [6, 7, 8]⟩, ⟨"D-manno", [2, 3, 4, 5]⟩]
      ignoredAchiralLocants := [] }
  , { publishedName := "3,6-dideoxy-L-threo-L-talo-decose"
      rejectedName? := none
      chainLength := 10
      configurationalGroups := [⟨"L-threo", [8, 9]⟩, ⟨"L-talo", [2, 4, 5, 7]⟩]
      ignoredAchiralLocants := [3, 6] } ]

@[simp] theorem higher_aldose_names_exact :
    higherAldoseMeanings.map HigherAldoseMeaning.publishedName =
      [ "D-glycero-D-gluco-heptose"
      , "L-ribo-D-manno-nonose"
      , "3,6-dideoxy-L-threo-L-talo-decose" ] := by
  rfl

structure HigherAldoseRule where
  groupsAssignedFromCarbonOneOutward : Bool
  proximalGroupsContainAtMostFourChiralCenters : Bool
  groupsCitedFarthestFirst : Bool
  achiralCentersIgnored : Bool
  deriving DecidableEq, Repr

def higherAldoseRule : HigherAldoseRule where
  groupsAssignedFromCarbonOneOutward := true
  proximalGroupsContainAtMostFourChiralCenters := true
  groupsCitedFarthestFirst := true
  achiralCentersIgnored := true

/-! ## 2-Carb-9 dialdose semantics -/

inductive RingSize where
  | furanose | pyranose
  deriving DecidableEq, Repr

def RingSize.atomCount : RingSize → Nat
  | .furanose => 5
  | .pyranose => 6

structure RingClosure where
  potentialCarbonylLocant : Nat
  hydroxylLocant : Nat
  ringSize : RingSize
  deriving DecidableEq, Repr

def RingClosure.wellFormed (closure : RingClosure) : Bool :=
  closure.potentialCarbonylLocant ≠ closure.hydroxylLocant &&
    closure.ringSize.atomCount =
      Nat.max closure.potentialCarbonylLocant closure.hydroxylLocant -
        Nat.min closure.potentialCarbonylLocant closure.hydroxylLocant + 2

inductive AnomericDescriptor where
  | alpha | absoluteR
  deriving DecidableEq, Repr

structure DialdoseMeaning where
  publishedName : String
  chainLength : Nat
  configurationalPrefix : String
  aldehydeLocants : List Nat
  ringClosures : List RingClosure
  assignments : List (Nat × AnomericDescriptor)
  optionalMesoPrefix : Bool
  methylGlycoside : Bool
  deriving DecidableEq, Repr, Inhabited

def DialdoseMeaning.wellFormed (meaning : DialdoseMeaning) : Bool :=
  !meaning.publishedName.isEmpty && meaning.chainLength > 1 &&
    meaning.aldehydeLocants = [1, meaning.chainLength] && meaning.ringClosures.Nodup &&
      meaning.ringClosures.all RingClosure.wellFormed && meaning.assignments.Nodup &&
        meaning.assignments.all fun assignment =>
          meaning.ringClosures.any fun closure =>
            closure.potentialCarbonylLocant = assignment.1

def dialdoseMeanings : List DialdoseMeaning :=
  [ { publishedName := "L-threo-tetrodialdose", chainLength := 4
      configurationalPrefix := "L-threo", aldehydeLocants := [1, 4]
      ringClosures := [], assignments := [], optionalMesoPrefix := false
      methylGlycoside := false }
  , { publishedName := "galacto-hexodialdose", chainLength := 6
      configurationalPrefix := "galacto", aldehydeLocants := [1, 6]
      ringClosures := [], assignments := [], optionalMesoPrefix := true
      methylGlycoside := false }
  , { publishedName := "alpha-D-gluco-hexodialdo-1,5-pyranose", chainLength := 6
      configurationalPrefix := "D-gluco", aldehydeLocants := [1, 6]
      ringClosures := [⟨1, 5, .pyranose⟩], assignments := [(1, .alpha)]
      optionalMesoPrefix := false, methylGlycoside := false }
  , { publishedName := "(6R)-D-gluco-hexodialdo-6,2-pyranose", chainLength := 6
      configurationalPrefix := "D-gluco", aldehydeLocants := [1, 6]
      ringClosures := [⟨6, 2, .pyranose⟩], assignments := [(6, .absoluteR)]
      optionalMesoPrefix := false, methylGlycoside := false }
  , { publishedName :=
        "Methyl alpha-D-gluco-hexodialdo-6,3-furanose-1,5-pyranoside"
      chainLength := 6, configurationalPrefix := "D-gluco", aldehydeLocants := [1, 6]
      ringClosures := [⟨6, 3, .furanose⟩, ⟨1, 5, .pyranose⟩]
      assignments := [(1, .alpha)], optionalMesoPrefix := false, methylGlycoside := true } ]

@[simp] theorem dialdose_names_exact :
    dialdoseMeanings.map DialdoseMeaning.publishedName =
      [ "L-threo-tetrodialdose"
      , "galacto-hexodialdose"
      , "alpha-D-gluco-hexodialdo-1,5-pyranose"
      , "(6R)-D-gluco-hexodialdo-6,2-pyranose"
      , "Methyl alpha-D-gluco-hexodialdo-6,3-furanose-1,5-pyranoside" ] := by
  rfl

structure DialdoseRule where
  parentEndingIsOdialdose : Bool
  parentChoiceUsesCarbohydrateRuleTwoTwoTwo : Bool
  ringLocantsPotentialCarbonylFirst : Bool
  ringLocantsOxygenBearingCarbonSecond : Bool
  multipleRingSizesAlphabetical : Bool
  deriving DecidableEq, Repr

def dialdoseRule : DialdoseRule where
  parentEndingIsOdialdose := true
  parentChoiceUsesCarbohydrateRuleTwoTwoTwo := true
  ringLocantsPotentialCarbonylFirst := true
  ringLocantsOxygenBearingCarbonSecond := true
  multipleRingSizesAlphabetical := true

/-! ## Total typed lookup and reviewed batch -/

inductive ImageSourceMeaning where
  | conformationExample (entry : ConformationEntry)
  | conformationChart (entries : List ConformationEntry)
  | enantiomerMirror (pair : EnantiomerMirrorPair)
  | higherAldose (meaning : HigherAldoseMeaning)
  | dialdose (meaning : DialdoseMeaning)
  deriving DecidableEq, Repr

def sourceMeaning? : String → Option ImageSourceMeaning
  | "2carb/2C0gif/071A.GIF" => some (.conformationExample glucopyranoseChair)
  | "2carb/2C0gif/071B.GIF" => some (.conformationChart chartEntries)
  | "2carb/2C0gif/074.GIF" => some (.enantiomerMirror mirrorPair)
  | "2carb/2C0gif/083A.GIF" => higherAldoseMeanings[0]?.map ImageSourceMeaning.higherAldose
  | "2carb/2C0gif/083B.GIF" => higherAldoseMeanings[1]?.map ImageSourceMeaning.higherAldose
  | "2carb/2C0gif/084.GIF" => higherAldoseMeanings[2]?.map ImageSourceMeaning.higherAldose
  | "2carb/2C0gif/09A.GIF" => dialdoseMeanings[0]?.map ImageSourceMeaning.dialdose
  | "2carb/2C0gif/09B.GIF" => dialdoseMeanings[1]?.map ImageSourceMeaning.dialdose
  | "2carb/2C0gif/09C.GIF" => dialdoseMeanings[2]?.map ImageSourceMeaning.dialdose
  | "2carb/2C0gif/09D.GIF" => dialdoseMeanings[3]?.map ImageSourceMeaning.dialdose
  | "2carb/2C0gif/09E.GIF" => dialdoseMeanings[4]?.map ImageSourceMeaning.dialdose
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
    visionReviewedGraphLevelBatch.entries.length = 11 := by
  rw [visionReviewedGraphLevelBatch.entries_length, provision_count]

/-! ## Exact advance from the prior 1,667/541 overlay -/

def remainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  priorRemainingImageRows.drop 11

@[simp] theorem remaining_image_count : remainingImageRows.length = 359 := by
  simp [remainingImageRows, priorRemainingImageRows]

theorem rows_append_remaining_eq_prior :
    rows ++ remainingImageRows = priorRemainingImageRows := by
  exact List.take_append_drop 11 priorRemainingImageRows

def advancedMaterializedProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorCarbohydrateReverseRingClosureImageSourceMeanings.advancedMaterializedProvisions ++
    provisions

def advancedMaterializedBatch :
    GlobalNonDescriptorSourceMeaningBatch advancedMaterializedProvisions :=
  GlobalNonDescriptorCarbohydrateReverseRingClosureImageSourceMeanings.advancedMaterializedBatch.append
    visionReviewedGraphLevelBatch

@[simp] theorem advanced_materialized_count : advancedMaterializedProvisions.length = 1678 := by
  simp [advancedMaterializedProvisions]

def advancedMissingProvisions : List IUPACNormativeProvision :=
  sourceProvisions .blueBook2013Appendix3 ++
    remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem advanced_missing_count : advancedMissingProvisions.length = 530 := by
  simp [advancedMissingProvisions]

set_option maxRecDepth 8192 in
theorem selected_then_advanced_missing_perm_prior_missing :
    (provisions ++ advancedMissingProvisions).Perm
      GlobalNonDescriptorCarbohydrateReverseRingClosureImageSourceMeanings.advancedMissingProvisions := by
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
    _ = GlobalNonDescriptorCarbohydrateReverseRingClosureImageSourceMeanings.advancedMissingProvisions := by
      rfl

theorem mem_prior_missing_iff_selected_or_advanced_missing
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorCarbohydrateReverseRingClosureImageSourceMeanings.advancedMissingProvisions ↔
      provision ∈ provisions ∨ provision ∈ advancedMissingProvisions := by
  simpa only [List.mem_append] using
    (selected_then_advanced_missing_perm_prior_missing.mem_iff).symm

private theorem selected_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ provisions) :
    provision ∈ GlobalNonDescriptorCarbohydrateReverseRingClosureImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_left _ member)

private theorem advanced_missing_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ advancedMissingProvisions) :
    provision ∈ GlobalNonDescriptorCarbohydrateReverseRingClosureImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_right _ member)

private theorem selected_append_advanced_missing_nodup :
    (provisions ++ advancedMissingProvisions).Nodup :=
  GlobalNonDescriptorCarbohydrateReverseRingClosureImageSourceMeanings.advanced_missing_nodup.perm
    selected_then_advanced_missing_perm_prior_missing.symm

theorem advanced_missing_nodup : advancedMissingProvisions.Nodup :=
  List.Nodup.of_append_right selected_append_advanced_missing_nodup

private theorem selected_disjoint_advanced_missing :
    provisions.Disjoint advancedMissingProvisions :=
  List.disjoint_of_nodup_append selected_append_advanced_missing_nodup

private theorem prior_materialized_disjoint_selected :
    GlobalNonDescriptorCarbohydrateReverseRingClosureImageSourceMeanings.advancedMaterializedProvisions.Disjoint
      provisions := by
  rw [List.disjoint_left]
  intro provision materialized selected
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateReverseRingClosureImageSourceMeanings.advanced_materialized_disjoint_missing)
      materialized (selected_subset_prior_missing selected)

theorem advanced_materialized_nodup : advancedMaterializedProvisions.Nodup := by
  exact GlobalNonDescriptorCarbohydrateReverseRingClosureImageSourceMeanings.advanced_materialized_nodup.append
    provisions_nodup prior_materialized_disjoint_selected

theorem advanced_materialized_disjoint_missing :
    advancedMaterializedProvisions.Disjoint advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision advanced missing
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateReverseRingClosureImageSourceMeanings.advanced_materialized_disjoint_missing)
        priorMaterialized (advanced_missing_subset_prior_missing missing)
  · exact (List.disjoint_left.mp selected_disjoint_advanced_missing) selected missing

theorem reviewed_disjoint_advanced_materialized :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMaterializedProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed advanced
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateReverseRingClosureImageSourceMeanings.reviewed_disjoint_advanced_materialized)
        reviewed priorMaterialized
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateReverseRingClosureImageSourceMeanings.reviewed_disjoint_advanced_missing)
        reviewed (selected_subset_prior_missing selected)

theorem reviewed_disjoint_advanced_missing :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed missing
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateReverseRingClosureImageSourceMeanings.reviewed_disjoint_advanced_missing)
      reviewed (advanced_missing_subset_prior_missing missing)

set_option maxRecDepth 8192 in
theorem mem_reviewed_or_advanced_materialized_or_missing_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions ∨
      provision ∈ advancedMaterializedProvisions ∨
        provision ∈ advancedMissingProvisions ↔
      provision ∈ globalNonDescriptorProvisions := by
  rw [← GlobalNonDescriptorCarbohydrateReverseRingClosureImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff]
  rw [mem_prior_missing_iff_selected_or_advanced_missing]
  simp only [advancedMaterializedProvisions, List.mem_append]
  tauto

theorem advanced_live_frontier_counts :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.length = 92 ∧
      advancedMaterializedProvisions.length = 1678 ∧
        advancedMissingProvisions.length = 530 ∧
          92 + 1678 + 530 = 2300 := by
  exact ⟨GlobalNonDescriptorSourceMeaningProgress.reviewed_count,
    advanced_materialized_count, advanced_missing_count, by omega⟩

end GlobalNonDescriptorCarbohydrateConformationAldoseDialdoseImageSourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateConformationAldoseDialdoseImageSourceMeanings.frozen_artifact_data_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateConformationAldoseDialdoseImageSourceMeanings.chart_published_names_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateConformationAldoseDialdoseImageSourceMeanings.visionReviewedGraphLevelBatch
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateConformationAldoseDialdoseImageSourceMeanings.selected_then_advanced_missing_perm_prior_missing
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateConformationAldoseDialdoseImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff
