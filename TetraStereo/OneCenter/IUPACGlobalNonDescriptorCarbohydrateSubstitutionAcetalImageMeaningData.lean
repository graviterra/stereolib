import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateLateImageMeaningTypes

set_option autoImplicit false

/-! Typed image meanings for all fifty-six figures in 2-Carb-24 through 2-Carb-30. -/

namespace TetraStereo.OneCenter
namespace CarbohydrateLateImageMeaningData

open Carbohydrate1996HeteroSubstitutionAnhydride
open Carbohydrate1996Acetals

private def substitutionFamily :
    Carbohydrate1996HeteroSubstitutionAnhydride.PrintedExample → ImageFamily
  | .pentaAcetylGlucose | .acetylTritylGlucose | .methanesulfonylGalactose
  | .benzoylGlucosylBromide | .methylGalactopyranose | .glucoseDihydrogenPhosphate
  | .glucosylPhosphate | .glucoseSixPhosphate | .fructoseBisphosphate
  | .glyceroylBisphosphate | .glucuronatePhosphate | .adenosineDiphosphate
  | .udpGlucose | .cmpNeu5Ac | .ribofuranosidePhosphonate
  | .azidoThymidinePhosphonate | .glucopyranosylPhosphonate
  | .galactopyranoseSulfate | .paps => .oSubstitution
  | .methylacetamidoGlucitol | .acetylGalactosamine | .sulfoGlucosamine
  | .glycoloylNeuraminic | .acetylatedNeuraminic => .nSubstitution
  | .anhydroMethylGlucose | .anhydroAllononitrile | .anhydroGalactitol
  | .anhydroGlucofuranoside | .anhydroNeuEnonicAcid | .anhydroGlucopyranose
  | .anhydroHeptulopyranose | .anhydroAcetylGlucose | .dianhydroTalopyranose
  | .anhydroGalactopyranose | .levoglucosenone => .intramolecularAnhydride

private def substitutionFeatures :
    Carbohydrate1996HeteroSubstitutionAnhydride.PrintedExample → List StructuralFeature
  | .pentaAcetylGlucose => [.heteroSubstitution .O [2, 3, 4, 5, 6] "acetyl"]
  | .acetylTritylGlucose =>
      [.heteroSubstitution .O [2, 4] "acetyl", .heteroSubstitution .O [6] "trityl"]
  | .methanesulfonylGalactose => [.heteroSubstitution .O [6] "methanesulfonyl"]
  | .benzoylGlucosylBromide =>
      [.heteroSubstitution .O [2, 3, 4, 6] "benzoyl",
        .heteroSubstitution .halogen [1] "bromide"]
  | .methylGalactopyranose => [.heteroSubstitution .O [4, 6] "methyl"]
  | .glucoseDihydrogenPhosphate => [.phosphorusOrSulfurEster .P [6] "dihydrogen phosphate"]
  | .glucosylPhosphate => [.phosphorusOrSulfurEster .P [1] "glycosyl phosphate"]
  | .glucoseSixPhosphate => [.phosphorusOrSulfurEster .P [6] "phosphate/phosphonato"]
  | .fructoseBisphosphate => [.phosphorusOrSulfurEster .P [1, 6] "bisphosphate"]
  | .glyceroylBisphosphate => [.phosphorusOrSulfurEster .P [1, 3] "bisphosphate"]
  | .glucuronatePhosphate => [.phosphorusOrSulfurEster .P [1] "dihydrogen phosphate"]
  | .adenosineDiphosphate =>
      [.phosphorusOrSulfurEster .P [5] "diphosphate", .carbohydrateResidueCount 1]
  | .udpGlucose =>
      [.phosphorusOrSulfurEster .P [1, 5] "diphosphate bridge", .carbohydrateResidueCount 2]
  | .cmpNeu5Ac =>
      [.phosphorusOrSulfurEster .P [2, 5] "monophosphate bridge", .carbohydrateResidueCount 2]
  | .ribofuranosidePhosphonate => [.phosphorusOrSulfurEster .P [5] "hydrogen phosphonate"]
  | .azidoThymidinePhosphonate =>
      [.phosphorusOrSulfurEster .P [5] "phosphonate bridge", .carbohydrateResidueCount 2]
  | .glucopyranosylPhosphonate => [.heteroSubstitution .P [2] "dimethoxyphosphoryl P-C bond"]
  | .galactopyranoseSulfate => [.phosphorusOrSulfurEster .S [2] "sulfate/sulfonato"]
  | .paps =>
      [.phosphorusOrSulfurEster .P [3, 5] "phosphate",
        .phosphorusOrSulfurEster .S [5] "adenylyl sulfate"]
  | .methylacetamidoGlucitol =>
      [.heteroSubstitution .N [2] "methylacetamido",
        .heteroSubstitution .O [1, 3, 4, 5, 6] "acetyl"]
  | .acetylGalactosamine => [.heteroSubstitution .N [2] "acetyl"]
  | .sulfoGlucosamine => [.heteroSubstitution .N [2] "sulfo"]
  | .glycoloylNeuraminic => [.heteroSubstitution .N [5] "glycoloyl"]
  | .acetylatedNeuraminic =>
      [.heteroSubstitution .N [5] "acetyl", .heteroSubstitution .O [4, 8, 9] "acetyl"]
  | .anhydroMethylGlucose =>
      [.anhydroBridge 3 6, .heteroSubstitution .O [2, 4, 5] "methyl"]
  | .anhydroAllononitrile => [.anhydroBridge 2 5, .modification [1] "nitrile"]
  | .anhydroGalactitol => [.anhydroBridge 1 5]
  | .anhydroGlucofuranoside =>
      [.anhydroBridge 3 6, .heteroSubstitution .O [1, 2, 5] "methyl"]
  | .anhydroNeuEnonicAcid =>
      [.anhydroBridge 2 6, .heteroSubstitution .N [5] "acetyl", .modification [2, 3] "enonic/deoxy"]
  | .anhydroGlucopyranose => [.anhydroBridge 1 6]
  | .anhydroHeptulopyranose => [.anhydroBridge 2 7]
  | .anhydroAcetylGlucose =>
      [.anhydroBridge 1 2, .heteroSubstitution .O [3, 4, 6] "acetyl"]
  | .dianhydroTalopyranose => [.anhydroBridge 1 6, .anhydroBridge 3 4]
  | .anhydroGalactopyranose => [.anhydroBridge 1 4]
  | .levoglucosenone =>
      [.anhydroBridge 1 6, .modification [2] "ketone", .modification [3, 4] "double bond/deoxy"]

def substitutionAnhydrideMeaning
    (row : Carbohydrate1996HeteroSubstitutionAnhydride.PrintedExample) : ImageMeaning :=
  let data := row.data
  textMeaning (substitutionFamily row) data.sourceKey data.printedName (substitutionFeatures row)

def substitutionAnhydrideImageMeanings : List ImageMeaning :=
  Carbohydrate1996HeteroSubstitutionAnhydride.PrintedExample.all.map
    substitutionAnhydrideMeaning

@[simp] theorem substitution_anhydride_meaning_count :
    substitutionAnhydrideImageMeanings.length = 35 := by simp [substitutionAnhydrideImageMeanings]

@[simp] theorem substitution_anhydride_meanings_well_formed :
    substitutionAnhydrideImageMeanings.all ImageMeaning.wellFormed = true := by decide

private def acetalFamily : Carbohydrate1996Acetals.PrintedItem → ImageFamily
  | .fructoseDianhydride | .fructoseSorboseDianhydride
  | .galacturonicRhamnoseDianhydride => .intermolecularAnhydride
  | .methyleneXylitol | .isopropylideneGlucofuranose | .diisopropylideneMannitol
  | .rBenzylideneGlucoside | .srDibenzylideneAlloside
  | .sChloroMethoxyMethyleneMannose | .rMethylOrthoacetate => .cyclicAcetal
  | .hemiacetalTemplate | .ethylHemiacetal | .ethylDithiohemiacetal
  | .oEthylMonothiohemiacetal | .sEthylMonothiohemiacetal | .acetalTemplate
  | .glucoseDiethylAcetal | .fructoseDiethylKetal | .propaneDiylDithioacetal
  | .ethylMethylMonothioacetal | .dimethylMonothioacetal => .carbonylDerivative

private def acetalFeatures : Carbohydrate1996Acetals.PrintedItem → List StructuralFeature
  | .fructoseDianhydride | .fructoseSorboseDianhydride
  | .galacturonicRhamnoseDianhydride =>
      [.intermolecularBridge 1 1 2 2, .intermolecularBridge 2 1 1 2,
        .carbohydrateResidueCount 2]
  | .methyleneXylitol => [.acetalBridge [2, 4] [.O, .O] none]
  | .isopropylideneGlucofuranose => [.acetalBridge [1, 2] [.O, .O] none]
  | .diisopropylideneMannitol =>
      [.acetalBridge [1, 2] [.O, .O] none, .acetalBridge [5, 6] [.O, .O] none]
  | .rBenzylideneGlucoside => [.acetalBridge [4, 6] [.O, .O] (some .R)]
  | .srDibenzylideneAlloside =>
      [.acetalBridge [2, 3] [.O, .O] (some .S), .acetalBridge [4, 6] [.O, .O] (some .R)]
  | .sChloroMethoxyMethyleneMannose => [.acetalBridge [1, 2] [.O, .O] (some .S)]
  | .rMethylOrthoacetate => [.acetalBridge [1, 2] [.O, .O] (some .R)]
  | .hemiacetalTemplate =>
      [.carbonylDerivative 1 [.O, .S] none,
        .depictionMeaning "hemiacetal, dithiohemiacetal, and two monothiohemiacetal connectivities"]
  | .ethylHemiacetal => [.carbonylDerivative 1 [.O, .O] (some .S)]
  | .ethylDithiohemiacetal => [.carbonylDerivative 1 [.S, .S] (some .S)]
  | .oEthylMonothiohemiacetal => [.carbonylDerivative 1 [.O, .S] (some .R)]
  | .sEthylMonothiohemiacetal => [.carbonylDerivative 1 [.O, .S] (some .S)]
  | .acetalTemplate =>
      [.carbonylDerivative 1 [.O, .S] none,
        .depictionMeaning "acetal, dithioacetal, and monothioacetal connectivities"]
  | .glucoseDiethylAcetal => [.carbonylDerivative 1 [.O, .O] none]
  | .fructoseDiethylKetal => [.carbonylDerivative 2 [.O, .O] none]
  | .propaneDiylDithioacetal => [.carbonylDerivative 1 [.S, .S] none]
  | .ethylMethylMonothioacetal => [.carbonylDerivative 1 [.O, .S] (some .S)]
  | .dimethylMonothioacetal =>
      [.carbonylDerivative 1 [.O, .S] (some .R), .heteroSubstitution .O [2, 3, 4, 5, 6] "acetyl"]

private def acetalVariantCount : Carbohydrate1996Acetals.PrintedItem → Nat
  | .hemiacetalTemplate => 4
  | .acetalTemplate => 3
  | _ => 1

private def acetalDepictionCount : Carbohydrate1996Acetals.PrintedItem → Nat
  | .methyleneXylitol => 2
  | _ => 1

def acetalMeaning (row : Carbohydrate1996Acetals.PrintedItem) : ImageMeaning :=
  let data := row.data
  textMeaning (acetalFamily row) data.sourceKey data.printedText (acetalFeatures row)
    (acetalVariantCount row) (acetalDepictionCount row)

def acetalImageMeanings : List ImageMeaning :=
  Carbohydrate1996Acetals.PrintedItem.all.map acetalMeaning

@[simp] theorem acetal_meaning_count : acetalImageMeanings.length = 21 := by
  simp [acetalImageMeanings]

@[simp] theorem acetal_meanings_well_formed :
    acetalImageMeanings.all ImageMeaning.wellFormed = true := by decide

@[simp] theorem hemiacetal_template_variant_count :
    (acetalImageMeanings[10]?.map ImageMeaning.structuralVariantCount) = some 4 := by decide

@[simp] theorem acetal_template_variant_count :
    (acetalImageMeanings[15]?.map ImageMeaning.structuralVariantCount) = some 3 := by decide

end CarbohydrateLateImageMeaningData
end TetraStereo.OneCenter
