import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings
import TetraStereo.KernelOnly

set_option autoImplicit false














namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings

open GlobalNonDescriptorSourceMeaningConstructor

def priorRemainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  GlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings.remainingImageRows

def rows : List Carbohydrate1996ImageAudit.Provision := priorRemainingImageRows.take 38

def artifactOf : Carbohydrate1996ImageAudit.Provision →
    Carbohydrate1996ImageAudit.ImageArtifact
  | .imageArtifact artifact => artifact

def artifacts : List Carbohydrate1996ImageAudit.ImageArtifact := rows.map artifactOf

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem row_count : rows.length = 38 := by
  simp [rows, priorRemainingImageRows]

@[simp] theorem artifact_count : artifacts.length = 38 := by simp [artifacts]
@[simp] theorem provision_count : provisions.length = 38 := by simp [provisions]

set_option maxRecDepth 4096 in
@[simp] theorem frozen_artifact_data_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.data =
      [ ⟨"2carb/2C1gif/172A.GIF", "2cfd0231599620d50b627a49420f910fe464d03335f9f1c873067ccef7a1df17", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/172B.GIF", "a8d60c4df903f1b0e63a2ea7a486ecf95a9e65229c1ad8022b79d2eb42548525", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/172C.GIF", "adea1333e5e8de8b1dcf2514dabc8fccbb54345e5b81b6c5d73dbdb22f4a5235", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/172D.GIF", "39b5e435bcb65881653906160abe39ef47c07df17fa689900339109b8f83e138", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/172E.GIF", "d57a8fc19398ffc06d743f8e99cce967936b801d494215ea3d0cb6afc6876e34", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/172F.GIF", "24d9ca519cda64b8bb4a361383aedeb8949ff58eaaf9b90465c96e673bd18122", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/172G.GIF", "ef0058aab3519115252c92dab5d1d1586608b60d222339cc085ed430304712ed", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/172H.GIF", "90e1dfd8b192783fcbf57c1fed44437fc3107c2ab8b953db4124f7d7175e4f9d", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/172I.GIF", "ac75662f6a5c594f623662314dcfddbd07101bc9a5424d653ce78e81e703c3a2", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/172J.GIF", "4ca1f98b781a44cea65e56d607a8a0a37eb422364a85dd0df60438e81ae37274", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/172K.GIF", "2b2cbfa22c7fbd1a3c8cc18c140722982a21f3a6c4df73a01c2af9be9a4469cc", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/172L.GIF", "b377c71112beac9c6b05568e43c4d8bfc37c30cab1216699583b53b922ca58f3", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/172M.GIF", "8ca1e7e3741839644be5d9ca2e3aa2f2a5c1b3d22eaa0d6671c1ea70b903ebc9", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/172N.GIF", "541bb7e34c42f9f2dad325c0a5e2478502d0396508253ed683337e9b2477ca94", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/172O.GIF", "538d9771f190536438b411b119313150eff0d42333c8085afc2ce69c2cc64702", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/172P.GIF", "02b97c3d48c757f98a4d74f983bec7b82a48021641594e50633198bbcf07827a", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/172Q.GIF", "33dd2c4ef4fe5e1f6531193bec75262efd83b602394000db6915a04c68be7946", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/173A.GIF", "de734c99ffb3fb3f6e376d878f6f4ad33df1833a5ee3c2bb92bce8fa1a78ede2", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/173B.GIF", "7835ce4946e79042c1648d66b7169e0b4890a58c2f83fb8bea2c64774af57b79", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/173C.GIF", "53e84be165120b82858f8c795d81e73057b39df4ccea7f94d6c3efe8a071e2b9", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/173D.GIF", "463a011bbf6726b29412f301a790bb70d8ff3a09df284bbc2a595e5030194186", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/173E.GIF", "e4c64b695d8c32260d8bb267cd521e669b0dc784c2a2850eefb044f5ba2e0299", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/181A.GIF", "659e8744015c3682b184fa2e6e6adb962d0997d9690ff691ea65ff0ce6b2ded1", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/181B.GIF", "0a000a635c7f2165284020f997503f3d336643fe79904599948e446e8708ff35", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/181C.GIF", "bf02dc83c12445c39b53ce8acf6a063c4153f7adc2f6a6997907d3b288029361", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/181D.GIF", "c8e65afb62fc3bad6428dd6c38e11e5a50f39044eadc798c4dd6139d799ab543", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/181E.GIF", "5095cd43d0421cce0ecf983712962c7e4d77364bdd6649fa68b1d59b8d595eff", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/181F.GIF", "a93687a365080c7d594974cdeec4ba8ff77ed79ab534263071d1037cc2a525a0", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/181G.GIF", "1e0a4bb3c5bef6e0d0a70e2d1719277cc4812d2843308cdf2188f2a1dd04dc20", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/181H.GIF", "ba1ad6af84dc1d0cba46431e2c74c48ec93efb90e09ea4c333955adc83750902", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/183A.GIF", "daeec3b2f406de7ee170a1f0f933fbf7ecd3996596eb31becde705f1da5d454b", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/183B.GIF", "78cf81bc2bea2f6924417e04debc960e402073804f967de398693cbf10dfe043", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/183C.GIF", "e234e5f1e4347bba4664e7b40fe2c3573ee6644e157c80e2d774a65ad715a115", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/183D.GIF", "efd44f096d7686a6e95a5470470cb4f9ce2917dc13ab6b23bdf339dec6c23f15", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/183E.GIF", "3d9e1aa9926d0f604acb02f82a8e9eaca404c2307594bd6f7a4f1b318c520485", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/183F.GIF", "7fb3a8b1637da9b25d5cd23e93bdae0bab707254c70f42328d4fe46f12f3bc3a", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/183G.GIF", "8fefe57d418212224017140b723dd2e279fb07d267cca21cbb518731f67b2a56", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/184.GIF", "8e1f76218aaf8509a512703e1c0f17167eaae45ee4433b8c5dc2188d9797f317", .numberedOrChartStructure⟩ ] := by
  decide

set_option maxRecDepth 4096 in
@[simp] theorem source_pages_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 22 ["17.html"] ++ List.replicate 16 ["18.html"] := by
  decide

set_option maxRecDepth 4096 in
private theorem rows_nodup : rows.Nodup := by
  decide

theorem provisions_nodup : provisions.Nodup := by
  exact rows_nodup.map (by intro left right equal; cases equal; rfl)

/-! ## Typed unsaturated structures -/

inductive AnomericDescriptor where
  | alpha | beta
  deriving DecidableEq, Repr, Inhabited

structure RingForm where
  anomericCarbonLocant : Nat
  closureCarbonLocant : Nat
  ringSize : Nat
  descriptor? : Option AnomericDescriptor
  deriving DecidableEq, Repr, Inhabited

structure ConfigurationalGroup where
  prefixText : String
  locants : List Nat
  deriving DecidableEq, Repr, Inhabited

inductive AttachmentSite where
  | carbon | oxygen | nitrogen
  deriving DecidableEq, Repr, Inhabited

structure Modification where
  locant : Nat
  name : String
  attachment : AttachmentSite
  deriving DecidableEq, Repr, Inhabited

inductive BondKind where
  | doubleBond | tripleBond
  deriving DecidableEq, Repr, Inhabited

inductive Geometry where
  | E | Z
  deriving DecidableEq, Repr, Inhabited

structure BackboneUnsaturation where
  lowerLocant : Nat
  upperLocant : Nat
  kind : BondKind
  geometry? : Option Geometry
  deriving DecidableEq, Repr, Inhabited

structure AnhydroBridge where
  firstLocant : Nat
  secondLocant : Nat
  deriving DecidableEq, Repr, Inhabited

structure UnsaturatedMeaning where
  primaryName : String
  alternativeNames : List String := []
  rejectedNames : List String := []
  chainLength : Nat
  carbonylLocants : List Nat := []
  deoxyLocants : List Nat := []
  configurationGroups : List ConfigurationalGroup := []
  ringForm? : Option RingForm := none
  unsaturations : List BackboneUnsaturation
  anhydroBridges : List AnhydroBridge := []
  modifications : List Modification := []
  deriving DecidableEq, Repr, Inhabited

def locantInChain (chainLength locant : Nat) : Bool :=
  decide (0 < locant ∧ locant ≤ chainLength)

def ConfigurationalGroup.wellFormed (group : ConfigurationalGroup) : Bool :=
  !group.prefixText.isEmpty && !group.locants.isEmpty && group.locants.Nodup

def ringFormWellFormed (chainLength : Nat) (ring : RingForm) : Bool :=
  locantInChain chainLength ring.anomericCarbonLocant &&
    locantInChain chainLength ring.closureCarbonLocant &&
    decide (ring.anomericCarbonLocant ≠ ring.closureCarbonLocant) &&
    ring.ringSize ==
      Nat.max ring.anomericCarbonLocant ring.closureCarbonLocant -
        Nat.min ring.anomericCarbonLocant ring.closureCarbonLocant + 2

def UnsaturatedMeaning.wellFormed (meaning : UnsaturatedMeaning) : Bool :=
  !meaning.primaryName.isEmpty && decide (1 < meaning.chainLength) &&
    !meaning.unsaturations.isEmpty &&
    meaning.carbonylLocants.Nodup &&
      meaning.carbonylLocants.all (locantInChain meaning.chainLength) &&
    meaning.deoxyLocants.Nodup &&
      meaning.deoxyLocants.all (locantInChain meaning.chainLength) &&
    meaning.configurationGroups.all ConfigurationalGroup.wellFormed &&
      (meaning.configurationGroups.flatMap ConfigurationalGroup.locants).Nodup &&
      (meaning.configurationGroups.flatMap ConfigurationalGroup.locants).all
        (locantInChain meaning.chainLength) &&
    meaning.unsaturations.all fun bond =>
      locantInChain meaning.chainLength bond.lowerLocant &&
        locantInChain meaning.chainLength bond.upperLocant &&
        decide (bond.lowerLocant + 1 = bond.upperLocant) &&
    meaning.anhydroBridges.all fun bridge =>
      locantInChain meaning.chainLength bridge.firstLocant &&
        locantInChain meaning.chainLength bridge.secondLocant &&
        decide (bridge.firstLocant ≠ bridge.secondLocant) &&
    meaning.modifications.all fun modification =>
      locantInChain meaning.chainLength modification.locant && !modification.name.isEmpty &&
    (match meaning.ringForm? with
      | none => true
      | some ring => ringFormWellFormed meaning.chainLength ring)

private def group (prefixText : String) (locants : List Nat) : ConfigurationalGroup :=
  ⟨prefixText, locants⟩

private def doubleBond (lowerLocant : Nat) (geometry? : Option Geometry := none) :
    BackboneUnsaturation :=
  ⟨lowerLocant, lowerLocant + 1, .doubleBond, geometry?⟩

private def tripleBond (lowerLocant : Nat) : BackboneUnsaturation :=
  ⟨lowerLocant, lowerLocant + 1, .tripleBond, none⟩

private def pyranose (anomericCarbonLocant : Nat)
    (descriptor? : Option AnomericDescriptor) : RingForm :=
  ⟨anomericCarbonLocant, anomericCarbonLocant + 4, 6, descriptor?⟩

private def furanose (anomericCarbonLocant : Nat)
    (descriptor? : Option AnomericDescriptor) : RingForm :=
  ⟨anomericCarbonLocant, anomericCarbonLocant + 3, 5, descriptor?⟩

def unsaturatedMeanings : List UnsaturatedMeaning :=
  [ { primaryName := "1,5-Anhydro-2-deoxy-D-arabino-hex-1-enitol"
      rejectedNames := ["D-Glucal"], chainLength := 6, deoxyLocants := [2]
      configurationGroups := [group "D-arabino" [3, 4, 5]]
      unsaturations := [doubleBond 1], anhydroBridges := [⟨1, 5⟩] }
  , { primaryName := "Methyl 2-deoxy-D-threo-pent-1-enofuranoside"
      chainLength := 5, deoxyLocants := [2], configurationGroups := [group "D-threo" [3, 4]]
      ringForm? := some (furanose 1 none), unsaturations := [doubleBond 1]
      modifications := [⟨1, "methyl", .oxygen⟩] }
  , { primaryName := "1-(2-Deoxy-D-threo-pent-1-enofuranosyl)uracil"
      chainLength := 5, deoxyLocants := [2], configurationGroups := [group "D-threo" [3, 4]]
      ringForm? := some (furanose 1 none), unsaturations := [doubleBond 1]
      modifications := [⟨1, "uracil", .nitrogen⟩] }
  , { primaryName := "3,4-Di-O-acetyl-2-deoxy-D-erythro-pent-1-enopyranosyl chloride"
      chainLength := 5, deoxyLocants := [2], configurationGroups := [group "D-erythro" [3, 4]]
      ringForm? := some (pyranose 1 none), unsaturations := [doubleBond 1]
      modifications := [⟨3, "acetyl", .oxygen⟩, ⟨4, "acetyl", .oxygen⟩,
        ⟨1, "chloride", .carbon⟩] }
  , { primaryName := "2,6-Anhydro-1-deoxy-D-altro-hept-1-enitol"
      rejectedNames := ["2,6-Anhydro-7-deoxy-D-talo-hept-6-enitol"]
      chainLength := 7, deoxyLocants := [1], configurationGroups := [group "D-altro" [3, 4, 5, 6]]
      unsaturations := [doubleBond 1], anhydroBridges := [⟨2, 6⟩] }
  , { primaryName := "1,2-Dideoxy-D-arabino-hex-1-enitol"
      chainLength := 6, deoxyLocants := [1, 2], configurationGroups := [group "D-arabino" [3, 4, 5]]
      unsaturations := [doubleBond 1] }
  , { primaryName := "(Z)-1,2,3,4,5-Penta-O-acetyl-D-erythro-pent-1-enitol"
      chainLength := 5, configurationGroups := [group "D-erythro" [3, 4]]
      unsaturations := [doubleBond 1 (some .Z)]
      modifications := [⟨1, "acetyl", .oxygen⟩, ⟨2, "acetyl", .oxygen⟩,
        ⟨3, "acetyl", .oxygen⟩, ⟨4, "acetyl", .oxygen⟩, ⟨5, "acetyl", .oxygen⟩] }
  , { primaryName := "(E)-1,2,3,4,5-Penta-O-acetyl-D-erythro-pent-1-enitol"
      chainLength := 5, configurationGroups := [group "D-erythro" [3, 4]]
      unsaturations := [doubleBond 1 (some .E)]
      modifications := [⟨1, "acetyl", .oxygen⟩, ⟨2, "acetyl", .oxygen⟩,
        ⟨3, "acetyl", .oxygen⟩, ⟨4, "acetyl", .oxygen⟩, ⟨5, "acetyl", .oxygen⟩] }
  , { primaryName := "2-Deoxy-D-threo-pent-1-enose dimethyl acetal"
      chainLength := 5, carbonylLocants := [1], deoxyLocants := [2]
      configurationGroups := [group "D-threo" [3, 4]], unsaturations := [doubleBond 1]
      modifications := [⟨1, "dimethyl acetal", .oxygen⟩] }
  , { primaryName := "2,3-Dideoxy-alpha-D-erythro-hex-2-enopyranose"
      chainLength := 6, carbonylLocants := [1], deoxyLocants := [2, 3]
      configurationGroups := [group "D-erythro" [4, 5]]
      ringForm? := some (pyranose 1 (some .alpha)), unsaturations := [doubleBond 2] }
  , { primaryName := "1,2,4,5-Tetradeoxy-D-arabino-octa-1,4-dienitol"
      chainLength := 8, deoxyLocants := [1, 2, 4, 5]
      configurationGroups := [group "D-arabino" [3, 6, 7]]
      unsaturations := [doubleBond 1, doubleBond 4] }
  , { primaryName := "1,5-Anhydro-4-deoxy-D-erythro-hex-4-enitol"
      rejectedNames := ["2,6-Anhydro-3-deoxy-L-erythro-hex-2-enitol"]
      chainLength := 6, deoxyLocants := [4], configurationGroups := [group "D-erythro" [2, 3]]
      unsaturations := [doubleBond 4], anhydroBridges := [⟨1, 5⟩] }
  , { primaryName := "Methyl 3,4-dideoxy-beta-D-glycero-hex-3-en-2-ulopyranoside"
      chainLength := 6, carbonylLocants := [2], deoxyLocants := [3, 4]
      configurationGroups := [group "D-glycero" [5]]
      ringForm? := some (pyranose 2 (some .beta)), unsaturations := [doubleBond 3]
      modifications := [⟨2, "methyl", .oxygen⟩] }
  , { primaryName := "2,3-Dideoxy-alpha-D-glycero-hex-2-enopyranos-4-ulose"
      chainLength := 6, carbonylLocants := [1, 4], deoxyLocants := [2, 3]
      configurationGroups := [group "D-glycero" [5]]
      ringForm? := some (pyranose 1 (some .alpha)), unsaturations := [doubleBond 2] }
  , { primaryName := "Methyl 3,4-dideoxy-beta-D-glycero-hept-3-en-2-ulopyranosid-5-ulose"
      chainLength := 7, carbonylLocants := [2, 5], deoxyLocants := [3, 4]
      configurationGroups := [group "D-glycero" [6]]
      ringForm? := some (pyranose 2 (some .beta)), unsaturations := [doubleBond 3]
      modifications := [⟨2, "methyl", .oxygen⟩] }
  , { primaryName := "5-Deoxy-1,2-O-isopropylidene-beta-L-threo-pent-4-enofuranose"
      chainLength := 5, carbonylLocants := [1], deoxyLocants := [5]
      configurationGroups := [group "L-threo" [2, 3, 4]]
      ringForm? := some (furanose 1 (some .beta)), unsaturations := [doubleBond 4]
      modifications := [⟨1, "isopropylidene", .oxygen⟩, ⟨2, "isopropylidene", .oxygen⟩] }
  , { primaryName := "5,6-Dideoxy-1,2-O-isopropylidene-alpha-D-xylo-hex-5-enfuranose"
      chainLength := 6, carbonylLocants := [1], deoxyLocants := [5, 6]
      configurationGroups := [group "D-xylo" [2, 3, 4]]
      ringForm? := some (furanose 1 (some .alpha)), unsaturations := [doubleBond 5]
      modifications := [⟨1, "isopropylidene", .oxygen⟩, ⟨2, "isopropylidene", .oxygen⟩] }
  , { primaryName := "(Z)-1,7-Anhydro-2,5,6-trideoxy-D-xylo-oct-5-en-1-ynitol"
      alternativeNames := ["(Z)-1,7-Anhydro-1,1,2,2-tetradehydro-2,5,6-trideoxy-D-xylo-oct-5-enitol"]
      chainLength := 8, deoxyLocants := [2, 5, 6], configurationGroups := [group "D-xylo" [3, 4, 7]]
      unsaturations := [doubleBond 5 (some .Z), tripleBond 1], anhydroBridges := [⟨1, 7⟩] }
  , { primaryName := "2-Deoxy-1-O-methyl-D-threo-pent-1-ynitol"
      alternativeNames := ["1,1,2,2-Tetradehydro-2-deoxy-1-O-methyl-D-threo-pentitol"]
      chainLength := 5, deoxyLocants := [2], configurationGroups := [group "D-threo" [3, 4]]
      unsaturations := [tripleBond 1], modifications := [⟨1, "methyl", .oxygen⟩] }
  , { primaryName :=
        "6,7,8-Trideoxy-1,2:3,4-di-O-isopropylidene-alpha-D-galacto-octa-6,7-dienopyranose"
      alternativeNames := ["6,7,7,8-Tetradehydro-6,7,8-trideoxy-1,2:3,4-di-O-isopropylidene-alpha-D-galacto-octopyranose"]
      chainLength := 8, carbonylLocants := [1], deoxyLocants := [6, 7, 8]
      configurationGroups := [group "D-galacto" [2, 3, 4, 5]]
      ringForm? := some (pyranose 1 (some .alpha))
      unsaturations := [doubleBond 6, doubleBond 7]
      modifications := [⟨1, "isopropylidene", .oxygen⟩, ⟨2, "isopropylidene", .oxygen⟩,
        ⟨3, "isopropylidene", .oxygen⟩, ⟨4, "isopropylidene", .oxygen⟩] }
  , { primaryName := "6-O-Acetyl-5-deoxy-alpha-D-xylo-hex-5-ynofuranose"
      alternativeNames := ["6-O-Acetyl-5,5,6,6-tetradehydro-5-deoxy-alpha-D-xylo-hexofuranose"]
      chainLength := 6, carbonylLocants := [1], deoxyLocants := [5]
      configurationGroups := [group "D-xylo" [2, 3, 4]]
      ringForm? := some (furanose 1 (some .alpha)), unsaturations := [tripleBond 5]
      modifications := [⟨6, "acetyl", .oxygen⟩] }
  , { primaryName :=
        "5,6,8-Trideoxy-1,2-O-isopropylidene-alpha-D-xylo-oct-5-ynofuranos-7-ulose"
      alternativeNames := ["5,5,6,6-Tetradehydro-5,6,8-trideoxy-1,2-O-isopropylidene-alpha-D-xylo-octofuranos-7-ulose"]
      chainLength := 8, carbonylLocants := [1, 7], deoxyLocants := [5, 6, 8]
      configurationGroups := [group "D-xylo" [2, 3, 4]]
      ringForm? := some (furanose 1 (some .alpha)), unsaturations := [tripleBond 5]
      modifications := [⟨1, "isopropylidene", .oxygen⟩, ⟨2, "isopropylidene", .oxygen⟩] } ]

@[simp] theorem unsaturated_meaning_count : unsaturatedMeanings.length = 22 := rfl

@[simp] theorem unsaturated_primary_names_exact :
    unsaturatedMeanings.map UnsaturatedMeaning.primaryName =
      [ "1,5-Anhydro-2-deoxy-D-arabino-hex-1-enitol"
      , "Methyl 2-deoxy-D-threo-pent-1-enofuranoside"
      , "1-(2-Deoxy-D-threo-pent-1-enofuranosyl)uracil"
      , "3,4-Di-O-acetyl-2-deoxy-D-erythro-pent-1-enopyranosyl chloride"
      , "2,6-Anhydro-1-deoxy-D-altro-hept-1-enitol"
      , "1,2-Dideoxy-D-arabino-hex-1-enitol"
      , "(Z)-1,2,3,4,5-Penta-O-acetyl-D-erythro-pent-1-enitol"
      , "(E)-1,2,3,4,5-Penta-O-acetyl-D-erythro-pent-1-enitol"
      , "2-Deoxy-D-threo-pent-1-enose dimethyl acetal"
      , "2,3-Dideoxy-alpha-D-erythro-hex-2-enopyranose"
      , "1,2,4,5-Tetradeoxy-D-arabino-octa-1,4-dienitol"
      , "1,5-Anhydro-4-deoxy-D-erythro-hex-4-enitol"
      , "Methyl 3,4-dideoxy-beta-D-glycero-hex-3-en-2-ulopyranoside"
      , "2,3-Dideoxy-alpha-D-glycero-hex-2-enopyranos-4-ulose"
      , "Methyl 3,4-dideoxy-beta-D-glycero-hept-3-en-2-ulopyranosid-5-ulose"
      , "5-Deoxy-1,2-O-isopropylidene-beta-L-threo-pent-4-enofuranose"
      , "5,6-Dideoxy-1,2-O-isopropylidene-alpha-D-xylo-hex-5-enfuranose"
      , "(Z)-1,7-Anhydro-2,5,6-trideoxy-D-xylo-oct-5-en-1-ynitol"
      , "2-Deoxy-1-O-methyl-D-threo-pent-1-ynitol"
      , "6,7,8-Trideoxy-1,2:3,4-di-O-isopropylidene-alpha-D-galacto-octa-6,7-dienopyranose"
      , "6-O-Acetyl-5-deoxy-alpha-D-xylo-hex-5-ynofuranose"
      , "5,6,8-Trideoxy-1,2-O-isopropylidene-alpha-D-xylo-oct-5-ynofuranos-7-ulose" ] := by
  rfl

@[simp] theorem unsaturated_meanings_well_formed :
    unsaturatedMeanings.all UnsaturatedMeaning.wellFormed = true := by
  decide

/-! ## Typed branched structures, including all six Chart V entries -/

structure Branch where
  parentLocant : Nat
  name : String
  attachment : AttachmentSite
  deriving DecidableEq, Repr, Inhabited

inductive AbsoluteDescriptor where
  | R | S
  deriving DecidableEq, Repr, Inhabited

structure AbsoluteCenter where
  site : String
  descriptor : AbsoluteDescriptor
  deriving DecidableEq, Repr, Inhabited

inductive ParentChoice where
  | cyclicRingChain | acyclicTwoCarbTwo | branchSubstituent
  deriving DecidableEq, Repr, Inhabited

structure BranchedMeaning where
  primaryName : String
  trivialName? : Option String := none
  alternativeNames : List String := []
  rejectedNames : List String := []
  parentChoice : ParentChoice
  chainLength : Nat
  carbonylLocants : List Nat := []
  deoxyLocants : List Nat := []
  configurationGroups : List ConfigurationalGroup := []
  ringForm? : Option RingForm := none
  branches : List Branch
  configurationDeterminedBy? : Option String := none
  absoluteCenters : List AbsoluteCenter := []
  branchPointAchiral : Bool := false
  deriving DecidableEq, Repr, Inhabited

def BranchedMeaning.wellFormed (meaning : BranchedMeaning) : Bool :=
  !meaning.primaryName.isEmpty && decide (1 < meaning.chainLength) &&
    meaning.carbonylLocants.Nodup &&
      meaning.carbonylLocants.all (locantInChain meaning.chainLength) &&
    meaning.deoxyLocants.Nodup &&
      meaning.deoxyLocants.all (locantInChain meaning.chainLength) &&
    meaning.configurationGroups.all ConfigurationalGroup.wellFormed &&
      (meaning.configurationGroups.flatMap ConfigurationalGroup.locants).Nodup &&
      (meaning.configurationGroups.flatMap ConfigurationalGroup.locants).all
        (locantInChain meaning.chainLength) &&
    !meaning.branches.isEmpty &&
    meaning.branches.all fun branch =>
      locantInChain meaning.chainLength branch.parentLocant && !branch.name.isEmpty &&
    meaning.absoluteCenters.all fun center => !center.site.isEmpty &&
    (match meaning.configurationDeterminedBy? with
      | none => true
      | some text => !text.isEmpty) &&
    (match meaning.ringForm? with
      | none => true
      | some ring => ringFormWellFormed meaning.chainLength ring)

private def singletonBranch
    (primaryName : String) (parentChoice : ParentChoice) (chainLength : Nat)
    (branches : List Branch) : BranchedMeaning :=
  { primaryName, parentChoice, chainLength, branches }

def branchedImageMeanings : List (List BranchedMeaning) :=
  [ [ { primaryName := "2-C-(Hydroxymethyl)-D-ribopyranose", trivialName? := some "Hamamelose"
        parentChoice := .cyclicRingChain, chainLength := 5, carbonylLocants := [1]
        configurationGroups := [group "D-ribo" [2, 3, 4]]
        ringForm? := some (pyranose 1 none), branches := [⟨2, "hydroxymethyl", .carbon⟩] } ]
  , [ { primaryName := "2,6-Dideoxy-3-C-methyl-3-O-methyl-L-ribo-hexopyranose"
        trivialName? := some "Cladinose", parentChoice := .cyclicRingChain, chainLength := 6
        carbonylLocants := [1], deoxyLocants := [2, 6]
        configurationGroups := [group "L-ribo" [3, 4, 5]]
        ringForm? := some (pyranose 1 none)
        branches := [⟨3, "methyl", .carbon⟩, ⟨3, "methyl", .oxygen⟩] } ]
  , [ { primaryName := "5-Deoxy-3-C-formyl-L-lyxofuranose", trivialName? := some "Streptose"
        parentChoice := .cyclicRingChain, chainLength := 5, carbonylLocants := [1]
        deoxyLocants := [5], configurationGroups := [group "L-lyxo" [2, 3, 4]]
        ringForm? := some (furanose 1 none), branches := [⟨3, "formyl", .carbon⟩] } ]
  , [ { primaryName := "6-Deoxy-3-C-methyl-D-mannopyranose", trivialName? := some "Evalose"
        parentChoice := .cyclicRingChain, chainLength := 6, carbonylLocants := [1]
        deoxyLocants := [6], configurationGroups := [group "D-manno" [2, 3, 4, 5]]
        ringForm? := some (pyranose 1 none), branches := [⟨3, "methyl", .carbon⟩] } ]
  , [ { primaryName :=
          "2,3,6-Trideoxy-3-C-methyl-4-O-methyl-3-nitro-L-arabino-hexopyranose"
        trivialName? := some "Evernitrose", parentChoice := .cyclicRingChain, chainLength := 6
        carbonylLocants := [1], deoxyLocants := [2, 3, 6]
        configurationGroups := [group "L-arabino" [3, 4, 5]]
        ringForm? := some (pyranose 1 none)
        branches := [⟨3, "methyl", .carbon⟩, ⟨4, "methyl", .oxygen⟩,
          ⟨3, "nitro", .carbon⟩] } ]
  , [ { primaryName := "3-Deoxy-4-C-methyl-3-methylamino-L-arabinopyranose"
        trivialName? := some "Garosamine", parentChoice := .cyclicRingChain, chainLength := 6
        carbonylLocants := [1], deoxyLocants := [3]
        configurationGroups := [group "L-arabino" [2, 3, 4, 5]]
        ringForm? := some (pyranose 1 none)
        branches := [⟨4, "methyl", .carbon⟩, ⟨3, "methylamino", .carbon⟩] } ]
  , [ { primaryName := "3-C-(Hydroxymethyl)-D-glycero-tetrose", trivialName? := some "D-Apiose (Api)"
        parentChoice := .acyclicTwoCarbTwo, chainLength := 4, carbonylLocants := [1]
        configurationGroups := [group "D-glycero" [2]]
        branches := [⟨3, "hydroxymethyl", .carbon⟩] } ]
  , [ { primaryName := "3-C-(Hydroxymethyl)-alpha-D-erythrofuranose"
        alternativeNames := ["D-Apio-alpha-D-furanose", "(3R)-alpha-D-apiofuranose"]
        rejectedNames := ["alpha-D-erythro-apiofuranose"]
        parentChoice := .cyclicRingChain, chainLength := 4, carbonylLocants := [1]
        configurationGroups := [group "D-erythro" [2, 3]]
        ringForm? := some (furanose 1 (some .alpha))
        branches := [⟨3, "hydroxymethyl", .carbon⟩] } ]
  , [ { primaryName := "3-C-Methyl-D-glucose", parentChoice := .acyclicTwoCarbTwo
        chainLength := 6, carbonylLocants := [1]
        configurationGroups := [group "D-gluco" [2, 3, 4, 5]]
        branches := [⟨3, "methyl", .carbon⟩], configurationDeterminedBy? := some "OH" } ]
  , [ { primaryName := "3-Deoxy-3-methyl-D-glucose", parentChoice := .acyclicTwoCarbTwo
        chainLength := 6, carbonylLocants := [1], deoxyLocants := [3]
        configurationGroups := [group "D-gluco" [2, 3, 4, 5]]
        branches := [⟨3, "methyl", .carbon⟩], configurationDeterminedBy? := some "CH3" } ]
  , [ { primaryName :=
          "2,3,6-Trideoxy-3-C-methyl-4-O-methyl-3-nitro-D-lyxo-hexopyranose"
        parentChoice := .cyclicRingChain, chainLength := 6, carbonylLocants := [1]
        deoxyLocants := [2, 3, 6], configurationGroups := [group "D-lyxo" [3, 4, 5]]
        ringForm? := some (pyranose 1 none)
        branches := [⟨3, "methyl", .carbon⟩, ⟨4, "methyl", .oxygen⟩,
          ⟨3, "nitro", .carbon⟩]
        configurationDeterminedBy? := some "nitrogen over carbon" } ]
  , [ { primaryName := "4-Cyclohexyl-4-deoxy-4-(hydroxymethyl)-D-allose"
        alternativeNames := ["(4R)-4-Cyclohexyl-4-deoxy-4-(hydroxymethyl)-D-ribo-hexose"]
        parentChoice := .acyclicTwoCarbTwo, chainLength := 6, carbonylLocants := [1]
        deoxyLocants := [4], configurationGroups := [group "D-allo" [2, 3, 4, 5]]
        branches := [⟨4, "cyclohexyl", .carbon⟩, ⟨4, "hydroxymethyl", .carbon⟩]
        configurationDeterminedBy? := some "oxygen over carbon"
        absoluteCenters := [⟨"C4", .R⟩] } ]
  , [ { primaryName := "3-Deoxy-3,3-dimethyl-D-ribo-hexose"
        parentChoice := .acyclicTwoCarbTwo, chainLength := 6, carbonylLocants := [1]
        deoxyLocants := [3], configurationGroups := [group "D-ribo" [2, 4, 5]]
        branches := [⟨3, "methyl", .carbon⟩, ⟨3, "methyl", .carbon⟩]
        branchPointAchiral := true } ]
  , [ { primaryName := "4-C-(Hydroxymethyl)-D-erythro-pentose"
        parentChoice := .acyclicTwoCarbTwo, chainLength := 5, carbonylLocants := [1]
        configurationGroups := [group "D-erythro" [2, 3]]
        branches := [⟨4, "hydroxymethyl", .carbon⟩] } ]
  , [ { primaryName :=
          "3-Deoxy-3-[(1R,2S)-1,2-dihydroxy-3-oxopropyl]-D-glycero-D-altro-heptopyranose"
        alternativeNames := ["3-Deoxy-3-(L-threo-1,2-dihydroxy-3-oxopropyl)-D-glycero-D-altro-heptopyranose"]
        rejectedNames := ["alternative open-chain six-carbon dialdose or eight-carbon aldose"]
        parentChoice := .cyclicRingChain, chainLength := 7, carbonylLocants := [1]
        deoxyLocants := [3], configurationGroups := [group "D-glycero" [6], group "D-altro" [2, 4, 5]]
        ringForm? := some (pyranose 1 none)
        branches := [⟨3, "(1R,2S)-1,2-dihydroxy-3-oxopropyl", .carbon⟩]
        absoluteCenters := [⟨"branch-C1", .R⟩, ⟨"branch-C2", .S⟩] }
      , { primaryName := "4-Deoxy-4-(L-ribo-1,2,3,4-tetrahydroxybutyl)-D-altro-hexodialdose"
          parentChoice := .acyclicTwoCarbTwo, chainLength := 6, carbonylLocants := [1, 6]
          deoxyLocants := [4], configurationGroups := [group "D-altro" [2, 3, 5]]
          branches := [⟨4, "L-ribo-1,2,3,4-tetrahydroxybutyl", .carbon⟩] }
      , { primaryName :=
            "4-Deoxy-4-[(1R,2R)-1,2-dihydroxy-3-oxopropyl]-D-allo-heptulo-2,5-furanose"
          alternativeNames := ["4-Deoxy-4-(L-erythro-1,2-dihydroxy-3-oxopropyl)-D-allo-heptulo-2,5-furanose"]
          rejectedNames := ["alternative ketoaldose"]
          parentChoice := .cyclicRingChain, chainLength := 7, carbonylLocants := [2]
          deoxyLocants := [4], configurationGroups := [group "D-allo" [3, 4, 5, 6]]
          ringForm? := some (furanose 2 none)
          branches := [⟨4, "(1R,2R)-1,2-dihydroxy-3-oxopropyl", .carbon⟩]
          absoluteCenters := [⟨"branch-C1", .R⟩, ⟨"branch-C2", .R⟩] }
      , { primaryName := "4-Deoxy-4-[(1R,2S)-1,2,3-trihydroxypropyl]-L-talo-heptos-6-ulose"
          alternativeNames := ["4-Deoxy-4-(L-erythro-1,2,3-trihydroxypropyl)-L-talo-heptos-6-ulose"]
          parentChoice := .acyclicTwoCarbTwo, chainLength := 7, carbonylLocants := [1, 6]
          deoxyLocants := [4], configurationGroups := [group "L-talo" [2, 3, 5, 6]]
          branches := [⟨4, "(1R,2S)-1,2,3-trihydroxypropyl", .carbon⟩]
          absoluteCenters := [⟨"branch-C1", .R⟩, ⟨"branch-C2", .S⟩] }
      , { primaryName := "4,6-Dideoxy-3-C-(L-glycero-1-hydroxyethyl)-D-ribo-hexose"
          rejectedNames := ["alternative pentose"]
          parentChoice := .acyclicTwoCarbTwo, chainLength := 6, carbonylLocants := [1]
          deoxyLocants := [4, 6], configurationGroups := [group "D-ribo" [2, 3, 5]]
          branches := [⟨3, "L-glycero-1-hydroxyethyl", .carbon⟩] }
      , { primaryName :=
            "3,4-Dideoxy-3-[3-hydroxy-2-(hydroxymethyl)propyl]-4-C-methyl-L-mannose"
          rejectedNames := ["alternative threo-hexose"]
          parentChoice := .acyclicTwoCarbTwo, chainLength := 6, carbonylLocants := [1]
          deoxyLocants := [3, 4], configurationGroups := [group "L-manno" [2, 3, 4, 5]]
          branches := [⟨3, "3-hydroxy-2-(hydroxymethyl)propyl", .carbon⟩,
            ⟨4, "methyl", .carbon⟩] } ]
  , [ { primaryName := "L-gluco-1,2,3,4,5-Pentahydroxypentyl"
        parentChoice := .branchSubstituent, chainLength := 5
        configurationGroups := [group "L-gluco" [1, 2, 3, 4, 5]]
        branches := [⟨1, "parent-chain attachment treated as aldehyde", .carbon⟩] } ] ]

@[simp] theorem branched_image_meaning_count : branchedImageMeanings.length = 16 := rfl

@[simp] theorem branched_structure_count :
    (branchedImageMeanings.flatMap id).length = 21 := by
  decide

@[simp] theorem chart_V_primary_names_exact :
    branchedImageMeanings[14]!.map BranchedMeaning.primaryName =
      [ "3-Deoxy-3-[(1R,2S)-1,2-dihydroxy-3-oxopropyl]-D-glycero-D-altro-heptopyranose"
      , "4-Deoxy-4-(L-ribo-1,2,3,4-tetrahydroxybutyl)-D-altro-hexodialdose"
      , "4-Deoxy-4-[(1R,2R)-1,2-dihydroxy-3-oxopropyl]-D-allo-heptulo-2,5-furanose"
      , "4-Deoxy-4-[(1R,2S)-1,2,3-trihydroxypropyl]-L-talo-heptos-6-ulose"
      , "4,6-Dideoxy-3-C-(L-glycero-1-hydroxyethyl)-D-ribo-hexose"
      , "3,4-Dideoxy-3-[3-hydroxy-2-(hydroxymethyl)propyl]-4-C-methyl-L-mannose" ] := by
  rfl

@[simp] theorem branched_meanings_well_formed :
    (branchedImageMeanings.flatMap id).all BranchedMeaning.wellFormed = true := by
  decide

inductive ImageSourceMeaning where
  | unsaturated (meaning : UnsaturatedMeaning)
  | branched (meanings : List BranchedMeaning)
  deriving DecidableEq, Repr, Inhabited

def allImageMeanings : List ImageSourceMeaning :=
  unsaturatedMeanings.map ImageSourceMeaning.unsaturated ++
    branchedImageMeanings.map ImageSourceMeaning.branched

@[simp] theorem all_image_meaning_count : allImageMeanings.length = 38 := by
  simp [allImageMeanings]

structure SourceRule where
  unsaturationMustJoinContiguousBackboneCarbons : Bool
  exocyclicUnsaturationUsesGeneralOrganicRules : Bool
  doubleBondLocantIsLowerCarbon : Bool
  geometryPrecedesWholeNameWhenNeeded : Bool
  ringAtMostSixMayOmitGeometry : Bool
  glycalNonpreferredAndRestrictedToOneTwoRingDoubleBond : Bool
  deoxyFormallyPrecedesDehydro : Bool
  dehydroAndDeoxyAlphabetized : Bool
  cyclicParentChainMustIncludeRingAtoms : Bool
  cLocantRequiredForAmbiguityButMayEmphasize : Bool
  branchPointUsesElementPriority : Bool
  identicalBranchesMakeCenterAchiral : Bool
  branchRSGenerallyPreferred : Bool
  branchNumberingSchemeForbiddenInNames : Bool
  deriving DecidableEq, Repr

def sourceRule : SourceRule where
  unsaturationMustJoinContiguousBackboneCarbons := true
  exocyclicUnsaturationUsesGeneralOrganicRules := true
  doubleBondLocantIsLowerCarbon := true
  geometryPrecedesWholeNameWhenNeeded := true
  ringAtMostSixMayOmitGeometry := true
  glycalNonpreferredAndRestrictedToOneTwoRingDoubleBond := true
  deoxyFormallyPrecedesDehydro := true
  dehydroAndDeoxyAlphabetized := true
  cyclicParentChainMustIncludeRingAtoms := true
  cLocantRequiredForAmbiguityButMayEmphasize := true
  branchPointUsesElementPriority := true
  identicalBranchesMakeCenterAchiral := true
  branchRSGenerallyPreferred := true
  branchNumberingSchemeForbiddenInNames := true

/-! ## Total typed lookup and reviewed batch -/

def sourceMeaning? : String → Option ImageSourceMeaning
  | "2carb/2C1gif/172A.GIF" => unsaturatedMeanings[0]?.map ImageSourceMeaning.unsaturated
  | "2carb/2C1gif/172B.GIF" => unsaturatedMeanings[1]?.map ImageSourceMeaning.unsaturated
  | "2carb/2C1gif/172C.GIF" => unsaturatedMeanings[2]?.map ImageSourceMeaning.unsaturated
  | "2carb/2C1gif/172D.GIF" => unsaturatedMeanings[3]?.map ImageSourceMeaning.unsaturated
  | "2carb/2C1gif/172E.GIF" => unsaturatedMeanings[4]?.map ImageSourceMeaning.unsaturated
  | "2carb/2C1gif/172F.GIF" => unsaturatedMeanings[5]?.map ImageSourceMeaning.unsaturated
  | "2carb/2C1gif/172G.GIF" => unsaturatedMeanings[6]?.map ImageSourceMeaning.unsaturated
  | "2carb/2C1gif/172H.GIF" => unsaturatedMeanings[7]?.map ImageSourceMeaning.unsaturated
  | "2carb/2C1gif/172I.GIF" => unsaturatedMeanings[8]?.map ImageSourceMeaning.unsaturated
  | "2carb/2C1gif/172J.GIF" => unsaturatedMeanings[9]?.map ImageSourceMeaning.unsaturated
  | "2carb/2C1gif/172K.GIF" => unsaturatedMeanings[10]?.map ImageSourceMeaning.unsaturated
  | "2carb/2C1gif/172L.GIF" => unsaturatedMeanings[11]?.map ImageSourceMeaning.unsaturated
  | "2carb/2C1gif/172M.GIF" => unsaturatedMeanings[12]?.map ImageSourceMeaning.unsaturated
  | "2carb/2C1gif/172N.GIF" => unsaturatedMeanings[13]?.map ImageSourceMeaning.unsaturated
  | "2carb/2C1gif/172O.GIF" => unsaturatedMeanings[14]?.map ImageSourceMeaning.unsaturated
  | "2carb/2C1gif/172P.GIF" => unsaturatedMeanings[15]?.map ImageSourceMeaning.unsaturated
  | "2carb/2C1gif/172Q.GIF" => unsaturatedMeanings[16]?.map ImageSourceMeaning.unsaturated
  | "2carb/2C1gif/173A.GIF" => unsaturatedMeanings[17]?.map ImageSourceMeaning.unsaturated
  | "2carb/2C1gif/173B.GIF" => unsaturatedMeanings[18]?.map ImageSourceMeaning.unsaturated
  | "2carb/2C1gif/173C.GIF" => unsaturatedMeanings[19]?.map ImageSourceMeaning.unsaturated
  | "2carb/2C1gif/173D.GIF" => unsaturatedMeanings[20]?.map ImageSourceMeaning.unsaturated
  | "2carb/2C1gif/173E.GIF" => unsaturatedMeanings[21]?.map ImageSourceMeaning.unsaturated
  | "2carb/2C1gif/181A.GIF" => branchedImageMeanings[0]?.map ImageSourceMeaning.branched
  | "2carb/2C1gif/181B.GIF" => branchedImageMeanings[1]?.map ImageSourceMeaning.branched
  | "2carb/2C1gif/181C.GIF" => branchedImageMeanings[2]?.map ImageSourceMeaning.branched
  | "2carb/2C1gif/181D.GIF" => branchedImageMeanings[3]?.map ImageSourceMeaning.branched
  | "2carb/2C1gif/181E.GIF" => branchedImageMeanings[4]?.map ImageSourceMeaning.branched
  | "2carb/2C1gif/181F.GIF" => branchedImageMeanings[5]?.map ImageSourceMeaning.branched
  | "2carb/2C1gif/181G.GIF" => branchedImageMeanings[6]?.map ImageSourceMeaning.branched
  | "2carb/2C1gif/181H.GIF" => branchedImageMeanings[7]?.map ImageSourceMeaning.branched
  | "2carb/2C1gif/183A.GIF" => branchedImageMeanings[8]?.map ImageSourceMeaning.branched
  | "2carb/2C1gif/183B.GIF" => branchedImageMeanings[9]?.map ImageSourceMeaning.branched
  | "2carb/2C1gif/183C.GIF" => branchedImageMeanings[10]?.map ImageSourceMeaning.branched
  | "2carb/2C1gif/183D.GIF" => branchedImageMeanings[11]?.map ImageSourceMeaning.branched
  | "2carb/2C1gif/183E.GIF" => branchedImageMeanings[12]?.map ImageSourceMeaning.branched
  | "2carb/2C1gif/183F.GIF" => branchedImageMeanings[13]?.map ImageSourceMeaning.branched
  | "2carb/2C1gif/183G.GIF" => branchedImageMeanings[14]?.map ImageSourceMeaning.branched
  | "2carb/2C1gif/184.GIF" => branchedImageMeanings[15]?.map ImageSourceMeaning.branched
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
    visionReviewedGraphLevelBatch.entries.length = 38 := by
  rw [visionReviewedGraphLevelBatch.entries_length, provision_count]

/-! ## Exact advance from the prior 1,744/464 overlay -/

def remainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  priorRemainingImageRows.drop 38

@[simp] theorem remaining_image_count : remainingImageRows.length = 255 := by
  simp [remainingImageRows, priorRemainingImageRows]

theorem rows_append_remaining_eq_prior :
    rows ++ remainingImageRows = priorRemainingImageRows := by
  exact List.take_append_drop 38 priorRemainingImageRows

def advancedMaterializedProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings.advancedMaterializedProvisions ++
    provisions

def advancedMaterializedBatch :
    GlobalNonDescriptorSourceMeaningBatch advancedMaterializedProvisions :=
  GlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings.advancedMaterializedBatch.append
    visionReviewedGraphLevelBatch

@[simp] theorem advanced_materialized_count : advancedMaterializedProvisions.length = 1782 := by
  simp [advancedMaterializedProvisions]

def advancedMissingProvisions : List IUPACNormativeProvision :=
  sourceProvisions .blueBook2013Appendix3 ++
    remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem advanced_missing_count : advancedMissingProvisions.length = 426 := by
  simp [advancedMissingProvisions]

set_option maxRecDepth 8192 in
theorem selected_then_advanced_missing_perm_prior_missing :
    (provisions ++ advancedMissingProvisions).Perm
      GlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings.advancedMissingProvisions := by
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
    _ = GlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings.advancedMissingProvisions := by
      rfl

theorem mem_prior_missing_iff_selected_or_advanced_missing
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings.advancedMissingProvisions ↔
      provision ∈ provisions ∨ provision ∈ advancedMissingProvisions := by
  simpa only [List.mem_append] using
    (selected_then_advanced_missing_perm_prior_missing.mem_iff).symm

private theorem selected_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ provisions) :
    provision ∈ GlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_left _ member)

private theorem advanced_missing_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ advancedMissingProvisions) :
    provision ∈ GlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_right _ member)

private theorem selected_append_advanced_missing_nodup :
    (provisions ++ advancedMissingProvisions).Nodup :=
  GlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings.advanced_missing_nodup.perm
    selected_then_advanced_missing_perm_prior_missing.symm

theorem advanced_missing_nodup : advancedMissingProvisions.Nodup :=
  List.Nodup.of_append_right selected_append_advanced_missing_nodup

private theorem selected_disjoint_advanced_missing :
    provisions.Disjoint advancedMissingProvisions :=
  List.disjoint_of_nodup_append selected_append_advanced_missing_nodup

private theorem prior_materialized_disjoint_selected :
    GlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings.advancedMaterializedProvisions.Disjoint
      provisions := by
  rw [List.disjoint_left]
  intro provision materialized selected
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings.advanced_materialized_disjoint_missing)
      materialized (selected_subset_prior_missing selected)

theorem advanced_materialized_nodup : advancedMaterializedProvisions.Nodup := by
  exact GlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings.advanced_materialized_nodup.append
    provisions_nodup prior_materialized_disjoint_selected

theorem advanced_materialized_disjoint_missing :
    advancedMaterializedProvisions.Disjoint advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision advanced missing
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings.advanced_materialized_disjoint_missing)
        priorMaterialized (advanced_missing_subset_prior_missing missing)
  · exact (List.disjoint_left.mp selected_disjoint_advanced_missing) selected missing

theorem reviewed_disjoint_advanced_materialized :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMaterializedProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed advanced
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings.reviewed_disjoint_advanced_materialized)
        reviewed priorMaterialized
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings.reviewed_disjoint_advanced_missing)
        reviewed (selected_subset_prior_missing selected)

theorem reviewed_disjoint_advanced_missing :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed missing
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings.reviewed_disjoint_advanced_missing)
      reviewed (advanced_missing_subset_prior_missing missing)

set_option maxRecDepth 8192 in
theorem mem_reviewed_or_advanced_materialized_or_missing_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions ∨
      provision ∈ advancedMaterializedProvisions ∨
        provision ∈ advancedMissingProvisions ↔
      provision ∈ globalNonDescriptorProvisions := by
  rw [← GlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff]
  rw [mem_prior_missing_iff_selected_or_advanced_missing]
  simp only [advancedMaterializedProvisions, List.mem_append]
  tauto

theorem advanced_live_frontier_counts :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.length = 92 ∧
      advancedMaterializedProvisions.length = 1782 ∧
        advancedMissingProvisions.length = 426 ∧
          92 + 1782 + 426 = 2300 := by
  exact ⟨GlobalNonDescriptorSourceMeaningProgress.reviewed_count,
    advanced_materialized_count, advanced_missing_count, by omega⟩

end GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings.frozen_artifact_data_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings.unsaturated_primary_names_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings.chart_V_primary_names_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings.unsaturated_meanings_well_formed
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings.branched_meanings_well_formed
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings.visionReviewedGraphLevelBatch
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings.selected_then_advanced_missing_perm_prior_missing
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateUnsaturatedBranchedImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff
