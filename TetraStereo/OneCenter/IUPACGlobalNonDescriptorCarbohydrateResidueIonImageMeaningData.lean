import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateLateImageMeaningTypes

set_option autoImplicit false

/-! Typed image meanings for all thirty-six figures in 2-Carb-31 and 2-Carb-32. -/

namespace TetraStereo.OneCenter
namespace CarbohydrateLateImageMeaningData

open Carbohydrate1996ResiduesIons

private def residueIonFamily : Carbohydrate1996ResiduesIons.PrintedExample → ImageFamily
  | .fructosOneYl | .aminoGlucosTwoYl | .ribopyranosidTwoOYl | .glucosTwoCYl
  | .deoxyGlucosTwoYl | .mannitolThreeYl | .arabinitolOneCYl | .hydroxyAllopyranosyl
  | .allopyranosylBenzoyl | .fructopyranosylAlanine | .bisFructopyranosylToluidine
  | .adenosylMethionine | .ribofuranosylDisulfide | .glucopyranosylAceticAcid
  | .glucopyranosidylPyruvicAcid | .glucopyranosyloxyIndole
  | .bisDeoxyGlucosidylEtherAmine | .talopyranoseDiylPhosphinite
  | .glucosideDiylPhosphinite | .glucosidYlidenePhosphane => .residue
  | .fructosOYlRadical | .glucopyranosylRadical | .methoxyGlucopyranosylRadical
  | .pentopyranosidYlidene => .radical
  | .hexosCYlium | .deoxyHexosYlium | .glucopyranosylium | .ethyliumDiylAllopyranose
  | .ribopyranosidTwoOium | .ribopyranosidFiveOium => .cation
  | .ribopyranosidTwoOate | .hexosCIde | .deoxyHexosIde | .glucitolOneIde => .anion
  | .glucopyranosiumyl | .deoxyHexosIdYl => .radicalIon

private def residueIonFeatures :
    Carbohydrate1996ResiduesIons.PrintedExample → List StructuralFeature
  | .fructosOneYl => [.freeValence 1 .C 1, .modification [1] "deoxy"]
  | .aminoGlucosTwoYl =>
      [.freeValence 2 .C 1, .heteroSubstitution .N [2] "amino", .modification [2] "deoxy"]
  | .ribopyranosidTwoOYl => [.freeValence 2 .O 1, .heteroSubstitution .O [1] "methyl"]
  | .glucosTwoCYl => [.freeValence 2 .C 1]
  | .deoxyGlucosTwoYl => [.freeValence 2 .C 1, .modification [2] "deoxy"]
  | .mannitolThreeYl => [.freeValence 3 .C 1, .modification [3] "deoxy"]
  | .arabinitolOneCYl =>
      [.freeValence 1 .C 1, .depictionMeaning "new C-1 configuration requires R/S"]
  | .hydroxyAllopyranosyl =>
      [.freeValence 1 .C 1,
        .depictionMeaning "alpha descriptor applies to free valence, not retained hydroxy"]
  | .allopyranosylBenzoyl =>
      [.freeValence 1 .C 1, .heteroSubstitution .O [1, 2, 3, 4, 6] "acetyl"]
  | .fructopyranosylAlanine =>
      [.freeValence 1 .C 1, .glycosidicLink 1 .N "L-alanine nitrogen"]
  | .bisFructopyranosylToluidine =>
      [.freeValence 1 .C 1, .glycosidicLink 1 .N "p-toluidine nitrogen",
        .carbohydrateResidueCount 2]
  | .adenosylMethionine =>
      [.freeValence 5 .C 1, .glycosidicLink 5 .S "L-methionine sulfonium sulfur"]
  | .ribofuranosylDisulfide =>
      [.freeValence 5 .C 1, .glycosidicLink 5 .S "disulfide partner",
        .carbohydrateResidueCount 2]
  | .glucopyranosylAceticAcid => [.freeValence 2 .O 1, .glycosidicLink 2 .O "acetic acid"]
  | .glucopyranosidylPyruvicAcid => [.freeValence 4 .O 1, .glycosidicLink 4 .O "pyruvic acid"]
  | .glucopyranosyloxyIndole => [.freeValence 1 .O 1, .glycosidicLink 1 .O "indole C-3"]
  | .bisDeoxyGlucosidylEtherAmine =>
      [.freeValence 2 .C 1, .carbohydrateResidueCount 2,
        .depictionMeaning "X is independently O or NH"]
  | .talopyranoseDiylPhosphinite =>
      [.freeValence 2 .C 1, .freeValence 4 .C 1,
        .heteroSubstitution .P [2, 4] "methoxyphosphanediyl bridge"]
  | .glucosideDiylPhosphinite =>
      [.freeValence 2 .C 1, .freeValence 4 .C 1,
        .heteroSubstitution .P [2, 4] "methoxyphosphanediyl bridge"]
  | .glucosidYlidenePhosphane =>
      [.freeValence 6 .C 2, .heteroSubstitution .P [6] "triphenyl-phosphanylidene"]
  | .fructosOYlRadical => [.electronicCenter 4 .O .radical]
  | .glucopyranosylRadical => [.electronicCenter 1 .C .radical]
  | .methoxyGlucopyranosylRadical =>
      [.electronicCenter 1 .C .radical, .heteroSubstitution .O [1] "methoxy"]
  | .pentopyranosidYlidene =>
      [.freeValence 2 .C 2, .depictionMeaning "carbene named by ylidene suffix"]
  | .hexosCYlium => [.electronicCenter 2 .C .cation]
  | .deoxyHexosYlium => [.electronicCenter 2 .C .cation, .modification [2] "deoxy"]
  | .glucopyranosylium =>
      [.electronicCenter 1 .C .cation, .depictionMeaning "two resonance contributors"]
  | .ethyliumDiylAllopyranose =>
      [.electronicCenter 1 .C .cation, .addedRing .bridge [1, 2] [.O, .C]]
  | .ribopyranosidTwoOium => [.electronicCenter 2 .O .cation]
  | .ribopyranosidFiveOium => [.electronicCenter 5 .O .cation]
  | .ribopyranosidTwoOate => [.electronicCenter 2 .O .anion]
  | .hexosCIde => [.electronicCenter 2 .C .anion]
  | .deoxyHexosIde => [.electronicCenter 2 .C .anion, .modification [2] "deoxy"]
  | .glucitolOneIde => [.electronicCenter 1 .C .anion, .anhydroBridge 1 5]
  | .glucopyranosiumyl => [.electronicCenter 1 .C .radicalCation]
  | .deoxyHexosIdYl =>
      [.electronicCenter 2 .C .radicalAnion, .modification [2] "deoxy"]

private def residueIonVariantCount : Carbohydrate1996ResiduesIons.PrintedExample → Nat
  | .bisDeoxyGlucosidylEtherAmine => 2
  | _ => 1

private def residueIonDepictionCount : Carbohydrate1996ResiduesIons.PrintedExample → Nat
  | .glucopyranosylium => 2
  | _ => 1

def residueIonMeaning (row : Carbohydrate1996ResiduesIons.PrintedExample) : ImageMeaning :=
  let data := row.data
  textMeaning (residueIonFamily row) data.sourceKey data.printedText (residueIonFeatures row)
    (residueIonVariantCount row) (residueIonDepictionCount row)

def residueIonImageMeanings : List ImageMeaning :=
  Carbohydrate1996ResiduesIons.PrintedExample.all.map residueIonMeaning

@[simp] theorem residue_ion_meaning_count : residueIonImageMeanings.length = 36 := by
  simp [residueIonImageMeanings]

@[simp] theorem residue_ion_meanings_well_formed :
    residueIonImageMeanings.all ImageMeaning.wellFormed = true := by decide

@[simp] theorem ether_amine_variant_count :
    (residueIonImageMeanings[16]?.map ImageMeaning.structuralVariantCount) = some 2 := by decide

@[simp] theorem glucopyranosylium_depiction_count :
    (residueIonImageMeanings[26]?.map ImageMeaning.depictionCount) = some 2 := by decide

end CarbohydrateLateImageMeaningData
end TetraStereo.OneCenter
