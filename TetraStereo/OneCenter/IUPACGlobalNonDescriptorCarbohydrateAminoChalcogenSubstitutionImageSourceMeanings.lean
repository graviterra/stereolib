import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings
import TetraStereo.KernelOnly

set_option autoImplicit false














namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings

open GlobalNonDescriptorSourceMeaningConstructor

def priorRemainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  GlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings.remainingImageRows

def rows : List Carbohydrate1996ImageAudit.Provision := priorRemainingImageRows.take 29

def artifactOf : Carbohydrate1996ImageAudit.Provision →
    Carbohydrate1996ImageAudit.ImageArtifact
  | .imageArtifact artifact => artifact

def artifacts : List Carbohydrate1996ImageAudit.ImageArtifact := rows.map artifactOf

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem row_count : rows.length = 29 := by
  simp [rows, priorRemainingImageRows]

@[simp] theorem artifact_count : artifacts.length = 29 := by simp [artifacts]
@[simp] theorem provision_count : provisions.length = 29 := by simp [provisions]

set_option maxRecDepth 4096 in
@[simp] theorem frozen_artifact_data_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.data =
      [ ⟨"2carb/2C1gif/142A.GIF", "836e696168cb2d3c82423eb31c5db15fbd29b0f249f07781620efebea255b065", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/142B.GIF", "08f7a93506e22353312c9eb0479ab09188a89c51ba08d77c75e3c51ae937654b", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/142C.GIF", "39488a90a2e1d953ede2166c176fc670a21975434c1ba3c6ff87e5e9e2e9e640", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/143A.GIF", "bf34c00e9b8ee6759a2d5a96fc4a999cbcdeaa5ec4ccbd7bae88023115b8f474", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/143B.GIF", "af14226293b0531a87ac1b9a6eb6d17293f5a6af200a7709dd1a60b4597b685d", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/143C.GIF", "1acd7b21e64fd24b49cbab3ffefacf0a0491e7452928d07868f43603de06f632", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/15A.GIF", "c4bd4cbb072992405c118abf609207071babf0aa45a3cf9116c8946b7f45cbcc", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/15B.GIF", "d44044f5d1d7a56e3590a9657c3597e311ff06816c8e9cedfaf655d66e9969ef", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/15C.GIF", "5c4c354e7cad1aa0139c3da4fe4e6a20a6860313324f735f60c76f93dd738889", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/15D.GIF", "c4f7c06832469ff8fc07bdf9cb31caf1388f1e7eb1baef4a7077423f3c76e79a", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/15E.GIF", "cea793eb2de8b2a3487fc6d8e758b5ca53ad2f6f334f91b29f52d3f4b81fbd67", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/15F.GIF", "5b48eeec0b9d9dbff5df93c82bb96aa27b5fc25013dc3ce72b3e2c08dea4989e", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/15G.GIF", "1fc0bbe5beaeb5971f06a9f37506551a663fc9990cdc11b886ce8e1fe2bfdc06", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/15H.GIF", "74aa5b1046c2d4bd018f9d750bb728573a99d8bcf8213e1ccfe020adcd41f8d3", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/161A.GIF", "126ace0188618f63669693014b98959cc2220be27767df42aef7fe04a00e362d", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/161B.GIF", "9f3d118909ee9d6aac0b17ca0b3e0261925bd213a3eed499c4fffd63df2f7887", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/161C.GIF", "ee9fad753dd2ce387846de4e5a84b1c2967ecea97aa42eb32d3374571782e380", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/162A.GIF", "42393160244146c6baf88a37a7438b3a48fb635176092b1c4d6be3346af8f2db", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/162B.GIF", "e381eebd31bb196d62063c10184e3b62e2b4a34fa3b096e739ce68bd52ab15ce", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/163.GIF", "178ca29d369a0f03af94582091ef6494a6f0c6823a4c732ac0078e833ce2ac85", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/164A.GIF", "72c8f8a3fd3ebc045accb944c42f634a5b3764d4ee7a5dfee9db557357bfd17b", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/164B.GIF", "98bc8ddf15af3670ea881b7d642540656b952f16d9a62b829f64038cb3c00aa7", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/164C.GIF", "3fb119e44df92977f1630f9c220f3c5725a78beb6eec3f6d68eb7bf7cc346fc5", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/165A.GIF", "cfa22253775d79c2c164d83b860dead75bc727f654369ce9f9ee69cbe4192ae7", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/165B.GIF", "8343c818a7d1e9693abe64fd5b86a74a2638e9b8acb16871ea372445b76f90a1", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/165C.GIF", "0e00308e3d1de96f9e61c3a1640509b83d8a68c63ef84e0655935b104f64cfb5", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/165D.GIF", "48715e4e75b84a75af3a750e305e04992628f1f80e0dcc7e7abcc3352540fda9", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/166A.GIF", "84136d7415ceb3ea02169f8b7a7ba32b7c5eddcd3c83097d0ed481c1525de73f", .numberedOrChartStructure⟩
      , ⟨"2carb/2C1gif/166B.GIF", "fbebd205625f36d0d45e37dcabbbb43d628f507155c4a661a45e8d436cb868e9", .numberedOrChartStructure⟩ ] := by
  decide

set_option maxRecDepth 4096 in
@[simp] theorem source_pages_exact :
    artifacts.map Carbohydrate1996ImageAudit.ImageArtifact.sourcePages =
      List.replicate 14 ["14n15.html"] ++ List.replicate 15 ["16.html"] := by
  decide

set_option maxRecDepth 4096 in
private theorem rows_nodup : rows.Nodup := by
  decide

theorem provisions_nodup : provisions.Nodup := by
  exact rows_nodup.map (by intro left right equal; cases equal; rfl)

/-! ## Typed derivative structures -/

inductive DerivativeMeaningKind where
  | aminoSugar | chalcogenAnalogue | carbonSubstitution | deoxySubstitution
  | terminalSubstitution | carbonylNitrogen | isotope
  deriving DecidableEq, Repr, Inhabited

inductive AnomericDescriptor where
  | alpha | beta
  deriving DecidableEq, Repr, Inhabited

inductive RingAtom where
  | oxygen | sulfur | selenium
  deriving DecidableEq, Repr, Inhabited

structure RingForm where
  anomericCarbonLocant : Nat
  closureCarbonLocant : Nat
  ringSize : Nat
  descriptor? : Option AnomericDescriptor
  ringAtom : RingAtom
  deriving DecidableEq, Repr, Inhabited

structure ConfigurationalGroup where
  prefixText : String
  locants : List Nat
  deriving DecidableEq, Repr, Inhabited

inductive AttachmentSite where
  | carbon | oxygen | nitrogen | chalcogen
  deriving DecidableEq, Repr, Inhabited

structure Modification where
  locant : Nat
  name : String
  attachment : AttachmentSite
  deriving DecidableEq, Repr, Inhabited

inductive ChalcogenElement where
  | sulfur | selenium | tellurium
  deriving DecidableEq, Repr, Inhabited

inductive ChalcogenTarget where
  | hydroxyO | carbonylO | ringO
  deriving DecidableEq, Repr, Inhabited

inductive ChalcogenOxidation where
  | none | oxide | dioxide
  deriving DecidableEq, Repr, Inhabited

structure ChalcogenSite where
  locant : Nat
  element : ChalcogenElement
  target : ChalcogenTarget
  oxidation : ChalcogenOxidation
  deriving DecidableEq, Repr, Inhabited

inductive AbsoluteDescriptor where
  | R | S
  deriving DecidableEq, Repr, Inhabited

structure AbsoluteCenter where
  site : String
  descriptor : AbsoluteDescriptor
  deriving DecidableEq, Repr, Inhabited

structure CarbonylNitrogenReplacement where
  locant : Nat
  name : String
  deriving DecidableEq, Repr, Inhabited

inductive IsotopeMode where
  | substitution | labelling
  deriving DecidableEq, Repr, Inhabited

structure IsotopeMark where
  locant : Nat
  massNumber : Nat
  element : String
  mode : IsotopeMode
  deriving DecidableEq, Repr, Inhabited

structure DerivativeMeaning where
  primaryName : String
  alternativeNames : List String := []
  rejectedNames : List String := []
  kind : DerivativeMeaningKind
  chainLength : Nat
  carbonylLocants : List Nat := []
  deoxyLocants : List Nat := []
  configurationGroups : List ConfigurationalGroup := []
  ringForm? : Option RingForm := none
  anomericReferenceLocant? : Option Nat := none
  modifications : List Modification := []
  chalcogenSites : List ChalcogenSite := []
  absoluteCenters : List AbsoluteCenter := []
  carbonylNitrogenReplacements : List CarbonylNitrogenReplacement := []
  isotopes : List IsotopeMark := []
  deriving DecidableEq, Repr, Inhabited

def locantInChain (chainLength locant : Nat) : Bool :=
  decide (0 < locant ∧ locant ≤ chainLength)

def ConfigurationalGroup.wellFormed (group : ConfigurationalGroup) : Bool :=
  !group.prefixText.isEmpty && !group.locants.isEmpty && group.locants.Nodup

def DerivativeMeaning.wellFormed (meaning : DerivativeMeaning) : Bool :=
  !meaning.primaryName.isEmpty && decide (1 < meaning.chainLength) &&
    meaning.carbonylLocants.Nodup &&
      meaning.carbonylLocants.all (locantInChain meaning.chainLength) &&
    meaning.deoxyLocants.Nodup &&
      meaning.deoxyLocants.all (locantInChain meaning.chainLength) &&
    meaning.configurationGroups.all ConfigurationalGroup.wellFormed &&
      (meaning.configurationGroups.flatMap ConfigurationalGroup.locants).Nodup &&
      (meaning.configurationGroups.flatMap ConfigurationalGroup.locants).all
        (locantInChain meaning.chainLength) &&
    meaning.modifications.all fun modification =>
      locantInChain meaning.chainLength modification.locant && !modification.name.isEmpty &&
    meaning.chalcogenSites.all fun site => locantInChain meaning.chainLength site.locant &&
    meaning.absoluteCenters.all fun center => !center.site.isEmpty &&
    meaning.carbonylNitrogenReplacements.all fun replacement =>
      locantInChain meaning.chainLength replacement.locant && !replacement.name.isEmpty &&
    meaning.isotopes.all fun isotope =>
      locantInChain meaning.chainLength isotope.locant && decide (0 < isotope.massNumber) &&
        !isotope.element.isEmpty &&
    (match meaning.anomericReferenceLocant? with
      | none => true
      | some locant => locantInChain meaning.chainLength locant) &&
    (match meaning.ringForm? with
      | none => true
      | some ring =>
          locantInChain meaning.chainLength ring.anomericCarbonLocant &&
            locantInChain meaning.chainLength ring.closureCarbonLocant &&
            decide (ring.anomericCarbonLocant ≠ ring.closureCarbonLocant) &&
            ring.ringSize ==
              Nat.max ring.anomericCarbonLocant ring.closureCarbonLocant -
                Nat.min ring.anomericCarbonLocant ring.closureCarbonLocant + 2)

private def group (prefixText : String) (locants : List Nat) : ConfigurationalGroup :=
  ⟨prefixText, locants⟩

private def pyranose (descriptor? : Option AnomericDescriptor)
    (ringAtom : RingAtom := .oxygen) : RingForm :=
  ⟨1, 5, 6, descriptor?, ringAtom⟩

private def furanose (descriptor? : Option AnomericDescriptor)
    (ringAtom : RingAtom := .oxygen) : RingForm :=
  ⟨1, 4, 5, descriptor?, ringAtom⟩

def aminoMeanings : List DerivativeMeaning :=
  [ { primaryName := "2-Amino-2-deoxy-D-glucopyranose (D-glucosamine)"
      kind := .aminoSugar, chainLength := 6, carbonylLocants := [1], deoxyLocants := [2]
      configurationGroups := [group "D-gluco" [2, 3, 4, 5]]
      ringForm? := some (pyranose none), modifications := [⟨2, "amino", .carbon⟩] }
  , { primaryName :=
        "5-Acetamido-3,5-dideoxy-D-glycero-alpha-D-galacto-non-2-ulopyranosonic acid (alpha-Neu5Ac)"
      alternativeNames := ["N-Acetyl-alpha-neuraminic acid", "alpha-Neu5Ac"]
      kind := .aminoSugar, chainLength := 9, carbonylLocants := [2], deoxyLocants := [3, 5]
      configurationGroups := [group "D-glycero" [8], group "D-galacto" [4, 5, 6, 7]]
      ringForm? := some ⟨2, 6, 6, some .alpha, .oxygen⟩, anomericReferenceLocant? := some 7
      modifications := [⟨5, "acetamido", .carbon⟩] }
  , { primaryName := "2-Amino-3-O-[(R)-1-carboxyethyl]-2-deoxy-beta-D-glucopyranose"
      alternativeNames := ["beta-Muramic acid"]
      kind := .aminoSugar, chainLength := 6, carbonylLocants := [1], deoxyLocants := [2]
      configurationGroups := [group "D-gluco" [2, 3, 4, 5]]
      ringForm? := some (pyranose (some .beta))
      modifications := [⟨2, "amino", .carbon⟩, ⟨3, "(R)-1-carboxyethyl", .oxygen⟩]
      absoluteCenters := [⟨"carboxyethyl-C1", .R⟩] }
  , { primaryName := "2-Deoxy-2-methylamino-L-glucopyranose"
      kind := .aminoSugar, chainLength := 6, carbonylLocants := [1], deoxyLocants := [2]
      configurationGroups := [group "L-gluco" [2, 3, 4, 5]]
      ringForm? := some (pyranose none), modifications := [⟨2, "methylamino", .carbon⟩] }
  , { primaryName := "4,6-Dideoxy-4-formamido-2,3-di-O-methyl-D-mannopyranose"
      kind := .aminoSugar, chainLength := 6, carbonylLocants := [1], deoxyLocants := [4, 6]
      configurationGroups := [group "D-manno" [2, 3, 4, 5]]
      ringForm? := some (pyranose none)
      modifications := [⟨4, "formamido", .carbon⟩, ⟨2, "methyl", .oxygen⟩, ⟨3, "methyl", .oxygen⟩] }
  , { primaryName := "2-Acetamido-1,3,4-tri-O-acetyl-2,6-dideoxy-alpha-L-galactopyranose"
      kind := .aminoSugar, chainLength := 6, carbonylLocants := [1], deoxyLocants := [2, 6]
      configurationGroups := [group "L-galacto" [2, 3, 4, 5]]
      ringForm? := some (pyranose (some .alpha))
      modifications := [⟨2, "acetamido", .carbon⟩, ⟨1, "acetyl", .oxygen⟩,
        ⟨3, "acetyl", .oxygen⟩, ⟨4, "acetyl", .oxygen⟩] } ]

@[simp] theorem amino_meaning_count : aminoMeanings.length = 6 := rfl

def chalcogenMeanings : List DerivativeMeaning :=
  [ { primaryName := "2,3,4,6-Tetra-O-acetyl-1-thio-beta-D-glucopyranose"
      kind := .chalcogenAnalogue, chainLength := 6, carbonylLocants := [1]
      configurationGroups := [group "D-gluco" [2, 3, 4, 5]]
      ringForm? := some (pyranose (some .beta))
      modifications := [⟨2, "acetyl", .oxygen⟩, ⟨3, "acetyl", .oxygen⟩,
        ⟨4, "acetyl", .oxygen⟩, ⟨6, "acetyl", .oxygen⟩]
      chalcogenSites := [⟨1, .sulfur, .hydroxyO, .none⟩] }
  , { primaryName := "5-Thio-beta-D-glucopyranose"
      kind := .chalcogenAnalogue, chainLength := 6, carbonylLocants := [1]
      configurationGroups := [group "D-gluco" [2, 3, 4, 5]]
      ringForm? := some (pyranose (some .beta) .sulfur)
      chalcogenSites := [⟨5, .sulfur, .ringO, .none⟩] }
  , { primaryName := "Methyl 2,3,4-tri-O-acetyl-1-thio-6-O-trityl-alpha-D-glucopyranoside"
      kind := .chalcogenAnalogue, chainLength := 6, carbonylLocants := [1]
      configurationGroups := [group "D-gluco" [2, 3, 4, 5]]
      ringForm? := some (pyranose (some .alpha))
      modifications := [⟨1, "methyl", .chalcogen⟩, ⟨2, "acetyl", .oxygen⟩,
        ⟨3, "acetyl", .oxygen⟩, ⟨4, "acetyl", .oxygen⟩, ⟨6, "trityl", .oxygen⟩]
      chalcogenSites := [⟨1, .sulfur, .hydroxyO, .none⟩] }
  , { primaryName := "Methyl 4-seleno-alpha-D-xylofuranoside"
      kind := .chalcogenAnalogue, chainLength := 5, carbonylLocants := [1]
      configurationGroups := [group "D-xylo" [2, 3, 4]]
      ringForm? := some (furanose (some .alpha) .selenium)
      modifications := [⟨1, "methyl", .oxygen⟩]
      chalcogenSites := [⟨4, .selenium, .ringO, .none⟩] }
  , { primaryName := "4-Thio-beta-D-galactopyranose"
      kind := .chalcogenAnalogue, chainLength := 6, carbonylLocants := [1]
      configurationGroups := [group "D-galacto" [2, 3, 4, 5]]
      ringForm? := some (pyranose (some .beta))
      chalcogenSites := [⟨4, .sulfur, .hydroxyO, .none⟩] }
  , { primaryName := "alpha-D-Glucopyranosyl phenyl (R)-selenoxide"
      kind := .chalcogenAnalogue, chainLength := 6, carbonylLocants := [1]
      configurationGroups := [group "D-gluco" [2, 3, 4, 5]]
      ringForm? := some (pyranose (some .alpha))
      modifications := [⟨1, "phenyl", .chalcogen⟩]
      chalcogenSites := [⟨1, .selenium, .hydroxyO, .oxide⟩]
      absoluteCenters := [⟨"Se", .R⟩] }
  , { primaryName := "Methyl 5-seleno-alpha-D-fructofuranoside"
      kind := .chalcogenAnalogue, chainLength := 6, carbonylLocants := [2]
      configurationGroups := [group "D-fructo" [3, 4, 5]]
      ringForm? := some ⟨2, 5, 5, some .alpha, .selenium⟩
      modifications := [⟨2, "methyl", .oxygen⟩]
      chalcogenSites := [⟨5, .selenium, .ringO, .none⟩] }
  , { primaryName :=
        "Ethyl 3,4,6,7-tetra-O-acetyl-2-deoxy-1,5-dithio-alpha-D-gluco-heptopyranoside"
      kind := .chalcogenAnalogue, chainLength := 7, carbonylLocants := [1], deoxyLocants := [2]
      configurationGroups := [group "D-gluco" [3, 4, 5, 6]]
      ringForm? := some ⟨1, 5, 6, some .alpha, .sulfur⟩
      modifications := [⟨1, "ethyl", .chalcogen⟩, ⟨3, "acetyl", .oxygen⟩,
        ⟨4, "acetyl", .oxygen⟩, ⟨6, "acetyl", .oxygen⟩, ⟨7, "acetyl", .oxygen⟩]
      chalcogenSites := [⟨1, .sulfur, .hydroxyO, .none⟩, ⟨5, .sulfur, .ringO, .none⟩] } ]

@[simp] theorem chalcogen_meaning_count : chalcogenMeanings.length = 8 := rfl

def substitutedMeanings : List DerivativeMeaning :=
  [ { primaryName := "2-C-Phenyl-alpha-D-glucopyranose"
      kind := .carbonSubstitution, chainLength := 6, carbonylLocants := [1]
      configurationGroups := [group "D-gluco" [2, 3, 4, 5]]
      ringForm? := some (pyranose (some .alpha)), modifications := [⟨2, "phenyl", .carbon⟩] }
  , { primaryName := "2-C-Acetamido-2,3,4,6-tetra-O-acetyl-alpha-D-mannopyranosyl fluoride"
      kind := .carbonSubstitution, chainLength := 6, carbonylLocants := [1]
      configurationGroups := [group "D-manno" [2, 3, 4, 5]]
      ringForm? := some (pyranose (some .alpha))
      modifications := [⟨2, "acetamido", .carbon⟩, ⟨2, "acetyl", .oxygen⟩,
        ⟨3, "acetyl", .oxygen⟩, ⟨4, "acetyl", .oxygen⟩, ⟨6, "acetyl", .oxygen⟩,
        ⟨1, "fluoride", .carbon⟩] }
  , { primaryName := "(5R)-1,2,3,4-Tetra-O-acetyl-5-bromo-alpha-D-xylo-hexopyranuronic acid"
      alternativeNames := ["1,2,3,4-Tetra-O-acetyl-5-bromo-beta-L-idopyranuronic acid"]
      kind := .carbonSubstitution, chainLength := 6, carbonylLocants := [1, 6]
      configurationGroups := [group "D-xylo" [2, 3, 4, 5]]
      ringForm? := some (pyranose (some .alpha))
      modifications := [⟨1, "acetyl", .oxygen⟩, ⟨2, "acetyl", .oxygen⟩,
        ⟨3, "acetyl", .oxygen⟩, ⟨4, "acetyl", .oxygen⟩, ⟨5, "bromo", .carbon⟩]
      absoluteCenters := [⟨"C5", .R⟩] }
  , { primaryName := "2-Deoxy-2-phenyl-alpha-D-glucopyranose"
      alternativeNames := ["2-Deoxy-2-C-phenyl-alpha-D-glucopyranose",
        "(2R)-2-Deoxy-2-phenyl-alpha-D-arabino-hexopyranose"]
      kind := .deoxySubstitution, chainLength := 6, carbonylLocants := [1], deoxyLocants := [2]
      configurationGroups := [group "D-gluco" [2, 3, 4, 5]]
      ringForm? := some (pyranose (some .alpha)), modifications := [⟨2, "phenyl", .carbon⟩] }
  , { primaryName :=
        "2,3-Diazido-4-O-benzoyl-6-bromo-2,3,6-trideoxy-alpha-D-mannopyranosyl nitrate"
      kind := .deoxySubstitution, chainLength := 6, carbonylLocants := [1]
      deoxyLocants := [2, 3, 6], configurationGroups := [group "D-manno" [2, 3, 4, 5]]
      ringForm? := some (pyranose (some .alpha))
      modifications := [⟨2, "azido", .carbon⟩, ⟨3, "azido", .carbon⟩,
        ⟨4, "benzoyl", .oxygen⟩, ⟨6, "bromo", .carbon⟩, ⟨1, "nitrate", .oxygen⟩] }
  , { primaryName := "(2R)-2-Bromo-2-chloro-2-deoxy-alpha-D-arabino-hexopyranose"
      alternativeNames := ["2-Bromo-2-chloro-2-deoxy-alpha-D-glucopyranose"]
      kind := .deoxySubstitution, chainLength := 6, carbonylLocants := [1], deoxyLocants := [2]
      configurationGroups := [group "D-arabino" [2, 3, 4, 5]]
      ringForm? := some (pyranose (some .alpha))
      modifications := [⟨2, "bromo", .carbon⟩, ⟨2, "chloro", .carbon⟩]
      absoluteCenters := [⟨"C2", .R⟩] }
  , { primaryName := "(5R)-5-C-Cyclohexyl-5-C-phenyl-D-xylose"
      kind := .terminalSubstitution, chainLength := 5, carbonylLocants := [1]
      configurationGroups := [group "D-xylo" [2, 3, 4]]
      modifications := [⟨5, "cyclohexyl", .carbon⟩, ⟨5, "phenyl", .carbon⟩]
      absoluteCenters := [⟨"C5", .R⟩] }
  , { primaryName := "1-C-Phenyl-D-glucose"
      rejectedNames := ["1-C-Phenyl-D-gluco-hex-1-ulose"]
      kind := .terminalSubstitution, chainLength := 6, carbonylLocants := [1]
      configurationGroups := [group "D-gluco" [2, 3, 4, 5]]
      modifications := [⟨1, "phenyl", .carbon⟩] }
  , { primaryName := "1-C-Phenyl-beta-D-glucopyranose"
      kind := .terminalSubstitution, chainLength := 6, carbonylLocants := [1]
      configurationGroups := [group "D-gluco" [2, 3, 4, 5]]
      ringForm? := some (pyranose (some .beta)), modifications := [⟨1, "phenyl", .carbon⟩] }
  , { primaryName := "1-Deoxy-1-(methylimino)-D-xylitol"
      kind := .carbonylNitrogen, chainLength := 5, carbonylLocants := [1], deoxyLocants := [1]
      configurationGroups := [group "D-xylitol" [2, 3, 4]]
      carbonylNitrogenReplacements := [⟨1, "methylimino"⟩] }
  , { primaryName := "D-Glucose phenylhydrazone"
      kind := .carbonylNitrogen, chainLength := 6, carbonylLocants := [1]
      configurationGroups := [group "D-gluco" [2, 3, 4, 5]]
      carbonylNitrogenReplacements := [⟨1, "phenylhydrazone"⟩] }
  , { primaryName := "D-arabino-Hexos-2-ulose bis(phenylhydrazone)"
      alternativeNames := ["D-arabino-Hex-2-ulose phenylosazone"]
      kind := .carbonylNitrogen, chainLength := 6, carbonylLocants := [1, 2]
      configurationGroups := [group "D-arabino" [3, 4, 5]]
      carbonylNitrogenReplacements := [⟨1, "phenylhydrazone"⟩, ⟨2, "phenylhydrazone"⟩] }
  , { primaryName := "D-arabino-Hexos-2-ulose phenylosotriazole"
      alternativeNames := ["(1R)-1-(2-Phenyl-2H-1,2,3-triazol-4-yl)-D-erythritol",
        "2-Phenyl-4-(L-arabino-1,2,3,4-tetrahydroxybutyl)-2H-1,2,3-triazole"]
      kind := .carbonylNitrogen, chainLength := 6, carbonylLocants := [1, 2]
      configurationGroups := [group "D-arabino" [3, 4, 5]]
      modifications := [⟨1, "phenylosotriazole", .carbon⟩] }
  , { primaryName := "2-Deoxy-D-(2-2H)lyxose"
      alternativeNames := ["(2S)-2-Deoxy-D-threo-(2-2H)pentose"]
      kind := .isotope, chainLength := 5, carbonylLocants := [1], deoxyLocants := [2]
      configurationGroups := [group "D-lyxo" [2, 3, 4]]
      absoluteCenters := [⟨"C2", .S⟩], isotopes := [⟨2, 2, "H", .substitution⟩] }
  , { primaryName := "2-Deoxy-2-[18F]fluoro-D-glucopyranose"
      alternativeNames := ["(2R)-2-Deoxy-2-[18F]fluoro-D-arabino-hexopyranose"]
      kind := .isotope, chainLength := 6, carbonylLocants := [1], deoxyLocants := [2]
      configurationGroups := [group "D-gluco" [2, 3, 4, 5]]
      ringForm? := some (pyranose none), modifications := [⟨2, "fluoro", .carbon⟩]
      absoluteCenters := [⟨"C2", .R⟩], isotopes := [⟨2, 18, "F", .labelling⟩] } ]

@[simp] theorem substituted_meaning_count : substitutedMeanings.length = 15 := rfl

def allMeanings : List DerivativeMeaning :=
  aminoMeanings ++ chalcogenMeanings ++ substitutedMeanings

@[simp] theorem all_meaning_count : allMeanings.length = 29 := by
  simp [allMeanings]

@[simp] theorem primary_names_exact :
    allMeanings.map DerivativeMeaning.primaryName =
      [ "2-Amino-2-deoxy-D-glucopyranose (D-glucosamine)"
      , "5-Acetamido-3,5-dideoxy-D-glycero-alpha-D-galacto-non-2-ulopyranosonic acid (alpha-Neu5Ac)"
      , "2-Amino-3-O-[(R)-1-carboxyethyl]-2-deoxy-beta-D-glucopyranose"
      , "2-Deoxy-2-methylamino-L-glucopyranose"
      , "4,6-Dideoxy-4-formamido-2,3-di-O-methyl-D-mannopyranose"
      , "2-Acetamido-1,3,4-tri-O-acetyl-2,6-dideoxy-alpha-L-galactopyranose"
      , "2,3,4,6-Tetra-O-acetyl-1-thio-beta-D-glucopyranose"
      , "5-Thio-beta-D-glucopyranose"
      , "Methyl 2,3,4-tri-O-acetyl-1-thio-6-O-trityl-alpha-D-glucopyranoside"
      , "Methyl 4-seleno-alpha-D-xylofuranoside"
      , "4-Thio-beta-D-galactopyranose"
      , "alpha-D-Glucopyranosyl phenyl (R)-selenoxide"
      , "Methyl 5-seleno-alpha-D-fructofuranoside"
      , "Ethyl 3,4,6,7-tetra-O-acetyl-2-deoxy-1,5-dithio-alpha-D-gluco-heptopyranoside"
      , "2-C-Phenyl-alpha-D-glucopyranose"
      , "2-C-Acetamido-2,3,4,6-tetra-O-acetyl-alpha-D-mannopyranosyl fluoride"
      , "(5R)-1,2,3,4-Tetra-O-acetyl-5-bromo-alpha-D-xylo-hexopyranuronic acid"
      , "2-Deoxy-2-phenyl-alpha-D-glucopyranose"
      , "2,3-Diazido-4-O-benzoyl-6-bromo-2,3,6-trideoxy-alpha-D-mannopyranosyl nitrate"
      , "(2R)-2-Bromo-2-chloro-2-deoxy-alpha-D-arabino-hexopyranose"
      , "(5R)-5-C-Cyclohexyl-5-C-phenyl-D-xylose"
      , "1-C-Phenyl-D-glucose"
      , "1-C-Phenyl-beta-D-glucopyranose"
      , "1-Deoxy-1-(methylimino)-D-xylitol"
      , "D-Glucose phenylhydrazone"
      , "D-arabino-Hexos-2-ulose bis(phenylhydrazone)"
      , "D-arabino-Hexos-2-ulose phenylosotriazole"
      , "2-Deoxy-D-(2-2H)lyxose"
      , "2-Deoxy-2-[18F]fluoro-D-glucopyranose" ] := by
  rfl

@[simp] theorem all_meanings_well_formed :
    allMeanings.all DerivativeMeaning.wellFormed = true := by
  decide

structure DerivativeRule where
  aminoEquivalentToHydroxyForConfiguration : Bool
  deoxyAlphabetizedAmongDetachablePrefixes : Bool
  anomericAminoNormallyRoutesToGlycosylamine : Bool
  ringChalcogenLocantUsesNonAnomericAdjacentCarbon : Bool
  seleniumAndTelluriumNamedAnalogously : Bool
  thioNotThia : Bool
  thioCommonlyTreatedAsDetachable : Bool
  modifiedCenterAmbiguityUsesAbsoluteDescriptor : Bool
  cLocantRequiredForAmbiguityButMayEmphasize : Bool
  highestPriorityGroupEquivalentToHydroxy : Bool
  terminalMethylRoutesToDeoxySugar : Bool
  aldehydicHydrogenRingReplacementUsesCPrefix : Bool
  carbonylNitrogenRoutesToIminoHydrazoneOrOsazone : Bool
  parenthesesMeanIsotopicSubstitution : Bool
  bracketsMeanIsotopicLabelling : Bool
  uniformLabellingUsesU : Bool
  deriving DecidableEq, Repr

def derivativeRule : DerivativeRule where
  aminoEquivalentToHydroxyForConfiguration := true
  deoxyAlphabetizedAmongDetachablePrefixes := true
  anomericAminoNormallyRoutesToGlycosylamine := true
  ringChalcogenLocantUsesNonAnomericAdjacentCarbon := true
  seleniumAndTelluriumNamedAnalogously := true
  thioNotThia := true
  thioCommonlyTreatedAsDetachable := true
  modifiedCenterAmbiguityUsesAbsoluteDescriptor := true
  cLocantRequiredForAmbiguityButMayEmphasize := true
  highestPriorityGroupEquivalentToHydroxy := true
  terminalMethylRoutesToDeoxySugar := true
  aldehydicHydrogenRingReplacementUsesCPrefix := true
  carbonylNitrogenRoutesToIminoHydrazoneOrOsazone := true
  parenthesesMeanIsotopicSubstitution := true
  bracketsMeanIsotopicLabelling := true
  uniformLabellingUsesU := true

/-! ## Total typed lookup and reviewed batch -/

def sourceMeaning? : String → Option DerivativeMeaning
  | "2carb/2C1gif/142A.GIF" => aminoMeanings[0]?
  | "2carb/2C1gif/142B.GIF" => aminoMeanings[1]?
  | "2carb/2C1gif/142C.GIF" => aminoMeanings[2]?
  | "2carb/2C1gif/143A.GIF" => aminoMeanings[3]?
  | "2carb/2C1gif/143B.GIF" => aminoMeanings[4]?
  | "2carb/2C1gif/143C.GIF" => aminoMeanings[5]?
  | "2carb/2C1gif/15A.GIF" => chalcogenMeanings[0]?
  | "2carb/2C1gif/15B.GIF" => chalcogenMeanings[1]?
  | "2carb/2C1gif/15C.GIF" => chalcogenMeanings[2]?
  | "2carb/2C1gif/15D.GIF" => chalcogenMeanings[3]?
  | "2carb/2C1gif/15E.GIF" => chalcogenMeanings[4]?
  | "2carb/2C1gif/15F.GIF" => chalcogenMeanings[5]?
  | "2carb/2C1gif/15G.GIF" => chalcogenMeanings[6]?
  | "2carb/2C1gif/15H.GIF" => chalcogenMeanings[7]?
  | "2carb/2C1gif/161A.GIF" => substitutedMeanings[0]?
  | "2carb/2C1gif/161B.GIF" => substitutedMeanings[1]?
  | "2carb/2C1gif/161C.GIF" => substitutedMeanings[2]?
  | "2carb/2C1gif/162A.GIF" => substitutedMeanings[3]?
  | "2carb/2C1gif/162B.GIF" => substitutedMeanings[4]?
  | "2carb/2C1gif/163.GIF" => substitutedMeanings[5]?
  | "2carb/2C1gif/164A.GIF" => substitutedMeanings[6]?
  | "2carb/2C1gif/164B.GIF" => substitutedMeanings[7]?
  | "2carb/2C1gif/164C.GIF" => substitutedMeanings[8]?
  | "2carb/2C1gif/165A.GIF" => substitutedMeanings[9]?
  | "2carb/2C1gif/165B.GIF" => substitutedMeanings[10]?
  | "2carb/2C1gif/165C.GIF" => substitutedMeanings[11]?
  | "2carb/2C1gif/165D.GIF" => substitutedMeanings[12]?
  | "2carb/2C1gif/166A.GIF" => substitutedMeanings[13]?
  | "2carb/2C1gif/166B.GIF" => substitutedMeanings[14]?
  | _ => none

def all_image_meanings_present : Bool :=
  artifacts.all fun artifact => (sourceMeaning? artifact.data.relativePath).isSome

structure VisionReviewedImageMeaning where
  artifactData : Carbohydrate1996ImageAudit.ImageArtifactData
  sourcePages : List String
  sourceMeaning : Option DerivativeMeaning
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
    visionReviewedGraphLevelBatch.entries.length = 29 := by
  rw [visionReviewedGraphLevelBatch.entries_length, provision_count]

/-! ## Exact advance from the prior 1,715/493 overlay -/

def remainingImageRows : List Carbohydrate1996ImageAudit.Provision :=
  priorRemainingImageRows.drop 29

@[simp] theorem remaining_image_count : remainingImageRows.length = 293 := by
  simp [remainingImageRows, priorRemainingImageRows]

theorem rows_append_remaining_eq_prior :
    rows ++ remainingImageRows = priorRemainingImageRows := by
  exact List.take_append_drop 29 priorRemainingImageRows

def advancedMaterializedProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings.advancedMaterializedProvisions ++
    provisions

def advancedMaterializedBatch :
    GlobalNonDescriptorSourceMeaningBatch advancedMaterializedProvisions :=
  GlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings.advancedMaterializedBatch.append
    visionReviewedGraphLevelBatch

@[simp] theorem advanced_materialized_count : advancedMaterializedProvisions.length = 1744 := by
  simp [advancedMaterializedProvisions]

def advancedMissingProvisions : List IUPACNormativeProvision :=
  sourceProvisions .blueBook2013Appendix3 ++
    remainingImageRows.map IUPACNormativeProvision.carbohydrate1996ImageArtifact

@[simp] theorem advanced_missing_count : advancedMissingProvisions.length = 464 := by
  simp [advancedMissingProvisions]

set_option maxRecDepth 8192 in
theorem selected_then_advanced_missing_perm_prior_missing :
    (provisions ++ advancedMissingProvisions).Perm
      GlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings.advancedMissingProvisions := by
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
    _ = GlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings.advancedMissingProvisions := by
      rfl

theorem mem_prior_missing_iff_selected_or_advanced_missing
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings.advancedMissingProvisions ↔
      provision ∈ provisions ∨ provision ∈ advancedMissingProvisions := by
  simpa only [List.mem_append] using
    (selected_then_advanced_missing_perm_prior_missing.mem_iff).symm

private theorem selected_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ provisions) :
    provision ∈ GlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_left _ member)

private theorem advanced_missing_subset_prior_missing
    {provision : IUPACNormativeProvision} (member : provision ∈ advancedMissingProvisions) :
    provision ∈ GlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings.advancedMissingProvisions :=
  selected_then_advanced_missing_perm_prior_missing.mem_iff.mp
    (List.mem_append_right _ member)

private theorem selected_append_advanced_missing_nodup :
    (provisions ++ advancedMissingProvisions).Nodup :=
  GlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings.advanced_missing_nodup.perm
    selected_then_advanced_missing_perm_prior_missing.symm

theorem advanced_missing_nodup : advancedMissingProvisions.Nodup :=
  List.Nodup.of_append_right selected_append_advanced_missing_nodup

private theorem selected_disjoint_advanced_missing :
    provisions.Disjoint advancedMissingProvisions :=
  List.disjoint_of_nodup_append selected_append_advanced_missing_nodup

private theorem prior_materialized_disjoint_selected :
    GlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings.advancedMaterializedProvisions.Disjoint
      provisions := by
  rw [List.disjoint_left]
  intro provision materialized selected
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings.advanced_materialized_disjoint_missing)
      materialized (selected_subset_prior_missing selected)

theorem advanced_materialized_nodup : advancedMaterializedProvisions.Nodup := by
  exact GlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings.advanced_materialized_nodup.append
    provisions_nodup prior_materialized_disjoint_selected

theorem advanced_materialized_disjoint_missing :
    advancedMaterializedProvisions.Disjoint advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision advanced missing
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings.advanced_materialized_disjoint_missing)
        priorMaterialized (advanced_missing_subset_prior_missing missing)
  · exact (List.disjoint_left.mp selected_disjoint_advanced_missing) selected missing

theorem reviewed_disjoint_advanced_materialized :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMaterializedProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed advanced
  rcases List.mem_append.mp advanced with priorMaterialized | selected
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings.reviewed_disjoint_advanced_materialized)
        reviewed priorMaterialized
  · exact (List.disjoint_left.mp
      GlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings.reviewed_disjoint_advanced_missing)
        reviewed (selected_subset_prior_missing selected)

theorem reviewed_disjoint_advanced_missing :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.Disjoint
      advancedMissingProvisions := by
  rw [List.disjoint_left]
  intro provision reviewed missing
  exact (List.disjoint_left.mp
    GlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings.reviewed_disjoint_advanced_missing)
      reviewed (advanced_missing_subset_prior_missing missing)

set_option maxRecDepth 8192 in
theorem mem_reviewed_or_advanced_materialized_or_missing_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions ∨
      provision ∈ advancedMaterializedProvisions ∨
        provision ∈ advancedMissingProvisions ↔
      provision ∈ globalNonDescriptorProvisions := by
  rw [← GlobalNonDescriptorCarbohydrateDeoxySugarImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff]
  rw [mem_prior_missing_iff_selected_or_advanced_missing]
  simp only [advancedMaterializedProvisions, List.mem_append]
  tauto

theorem advanced_live_frontier_counts :
    GlobalNonDescriptorSourceMeaningProgress.reviewedProvisions.length = 92 ∧
      advancedMaterializedProvisions.length = 1744 ∧
        advancedMissingProvisions.length = 464 ∧
          92 + 1744 + 464 = 2300 := by
  exact ⟨GlobalNonDescriptorSourceMeaningProgress.reviewed_count,
    advanced_materialized_count, advanced_missing_count, by omega⟩

end GlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings.frozen_artifact_data_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings.primary_names_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings.all_meanings_well_formed
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings.visionReviewedGraphLevelBatch
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings.selected_then_advanced_missing_perm_prior_missing
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAminoChalcogenSubstitutionImageSourceMeanings.mem_reviewed_or_advanced_materialized_or_missing_iff
