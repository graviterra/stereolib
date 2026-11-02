import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarbohydrateLateImageMeaningTypes

set_option autoImplicit false

/-! Typed image meanings for all fifty-eight figures in 2-Carb-33 through 2-Carb-35. -/

namespace TetraStereo.OneCenter
namespace CarbohydrateLateImageMeaningData

open Carbohydrate1996GlycosidesRings

private def glycosideRingFamily : Carbohydrate1996GlycosidesRings.PrintedExample → ImageFamily
  | .e331 | .e332A | .e332B | .e332C | .e332D | .e332E | .e332F | .e332G
  | .e332H | .e332I => .glycoside
  | .e333A | .e333B | .e333C | .e333D => .thioglycoside
  | .e334A | .e334B => .selenoglycoside
  | .e335A | .e335B | .e335C | .e335D | .e335E => .glycosylHalide
  | .e336A | .e336B | .e336C | .e336D | .e336E | .e336F => .glycosylamine
  | .e337A | .e337B | .e337C | .e337D | .e337E | .e337F | .e337G => .carbonGlycosyl
  | .e341A | .e341B | .e341C | .e341D | .e341E => .ringHeteroReplacement
  | .e342A | .e342B | .e342C | .e342D => .ringCarbonReplacement
  | .e351A | .e351B | .e351C | .e351D | .e351E | .e351F | .e351G | .e351H => .bridgedRing
  | .e352A | .e352B | .e352C | .e352D => .fusedRing
  | .e353A | .e353B | .e353C => .spiro

private def glycosideRingFeatures :
    Carbohydrate1996GlycosidesRings.PrintedExample → List StructuralFeature
  | .e331 => [.glycosidicLink 1 .O "methyl"]
  | .e332A => [.glycosidicLink 1 .O "methyl"]
  | .e332B => [.glycosidicLink 2 .O "ethyl"]
  | .e332C => [.glycosidicLink 6 .O "methyl"]
  | .e332D => [.glycosidicLink 1 .O "pregnanediol C-3 oxygen"]
  | .e332E => [.glycosidicLink 1 .O "4-acetylphenyl oxygen"]
  | .e332F => [.glycosidicLink 1 .O "mandelonitrile oxygen"]
  | .e332G => [.glycosidicLink 1 .O "coumarin C-7 oxygen"]
  | .e332H => [.glycosidicLink 1 .O "L-serine O-3"]
  | .e332I =>
      [.freeValence 5 .C 1, .freeValence 5 .O 1, .carbohydrateResidueCount 2,
        .depictionMeaning "two methyl beta-D-xylofuranoside residues"]
  | .e333A => [.glycosidicLink 1 .S "ethyl"]
  | .e333B => [.glycosidicLink 1 .S "4-carboxyphenyl"]
  | .e333C => [.glycosidicLink 1 .S "hydroximothioate sulfur"]
  | .e333D =>
      [.glycosidicLink 1 .S "phenyl sulfoxide", .heteroSubstitution .O [2, 3, 4, 6] "acetyl"]
  | .e334A => [.glycosidicLink 1 .Se "2-carboxyethyl"]
  | .e334B => [.glycosidicLink 1 .Se "D-selenocysteine selenium"]
  | .e335A =>
      [.glycosidicLink 1 .halogen "bromide", .heteroSubstitution .O [2, 3, 4, 6] "acetyl"]
  | .e335B =>
      [.glycosidicLink 1 .halogen "bromide", .heteroSubstitution .O [2, 3, 4] "acetyl"]
  | .e335C =>
      [.glycosidicLink 1 .halogen "bromide", .heteroSubstitution .O [3, 4, 6] "benzyl",
        .modification [2] "ketone"]
  | .e335D =>
      [.glycosidicLink 2 .halogen "bromide", .heteroSubstitution .O [3, 4, 5] "benzyl",
        .modification [1, 2] "aldehyde and ketone"]
  | .e335E =>
      [.glycosidicLink 2 .halogen "chloride", .heteroSubstitution .N [5] "acetyl",
        .heteroSubstitution .O [4, 7, 8, 9] "acetyl"]
  | .e336A => [.glycosidicLink 2 .N "phenylamine nitrogen"]
  | .e336B => [.glycosidicLink 1 .N "uracil N-1"]
  | .e336C =>
      [.glycosidicLink 1 .N "L-lysinamide N-1", .heteroSubstitution .N [2] "acetyl"]
  | .e336D => [.glycosidicLink 1 .N "adenine N-9", .heteroSubstitution .S [5] "methyl"]
  | .e336E =>
      [.glycosidicLink 1 .N "L-asparagine N-4", .heteroSubstitution .N [2] "acetyl"]
  | .e336F => [.glycosidicLink 1 .N "central amine", .carbohydrateResidueCount 2]
  | .e337A => [.glycosidicLink 1 .C "benzoic acid C-4"]
  | .e337B => [.glycosidicLink 1 .C "adenine C-8", .modification [2] "deoxy"]
  | .e337C => [.glycosidicLink 1 .C "uracil C-5"]
  | .e337D =>
      [.glycosidicLink 1 .C "acetonitrile carbon", .anhydroBridge 3 7,
        .modification [2] "deoxy"]
  | .e337E => [.glycosidicLink 1 .C "xanthenone C-2"]
  | .e337F => [.glycosidicLink 1 .C "anthracenone C-10"]
  | .e337G =>
      [.glycosidicLink 1 .C "flavone C-6", .glycosidicLink 1 .C "flavone C-8",
        .carbohydrateResidueCount 2]
  | .e341A => [.ringReplacement 5 .N, .heteroSubstitution .N [5] "amino"]
  | .e341B => [.ringReplacement 5 .N, .anhydroBridge 1 5]
  | .e341C => [.ringReplacement 5 .N, .heteroSubstitution .N [5] "ethyl"]
  | .e341D => [.ringReplacement 5 .P, .heteroSubstitution .P [5] "phosphanyl"]
  | .e341E => [.ringReplacement 3 .N, .modification [3] "aza/deoxy"]
  | .e342A =>
      [.ringReplacement 5 .C, .depictionMeaning "new ring carbon carries carbohydrate locant 5a"]
  | .e342B =>
      [.ringReplacement 4 .C, .glycosidicLink 1 .N "thymine N-1",
        .depictionMeaning "new ring carbon carries locant 4a"]
  | .e342C =>
      [.ringReplacement 5 .C, .glycosidicLink 2 .O "carba-glucopyranoside",
        .carbohydrateResidueCount 2]
  | .e342D =>
      [.ringReplacement 4 .C, .glycosidicLink 1 .N "thymine N-1",
        .heteroSubstitution .halogen [4] "fluoro", .depictionMeaning "4aS ring carbon"]
  | .e351A =>
      [.acetalBridge [2, 3] [.O, .O] none, .acetalBridge [4, 5] [.O, .O] none,
        .addedRing .bridge [2, 3, 4, 5] [.O, .O]]
  | .e351B =>
      [.acetalBridge [4, 6] [.O, .O] (some .S), .addedRing .bridge [4, 6] [.O, .O]]
  | .e351C => [.addedRing .bridge [2, 3] [.C, .C], .modification [2, 3] "dideoxy"]
  | .e351D =>
      [.addedRing .bridge [2, 3] [.C, .C], .modification [2, 3] "dideoxy/double bond"]
  | .e351E =>
      [.anhydroBridge 1 6, .addedRing .bridge [2, 3] [.C, .C], .modification [4] "ketone"]
  | .e351F =>
      [.anhydroBridge 1 5, .addedRing .bridge [1, 2] [.C, .O],
        .heteroSubstitution .O [3, 4, 6] "benzyl"]
  | .e351G =>
      [.addedRing .bridge [4, 6] [.N, .N], .heteroSubstitution .N [4] "acetyl",
        .heteroSubstitution .O [2, 3] "acetyl"]
  | .e351H =>
      [.addedRing .bridge [4, 6] [.C, .C], .heteroSubstitution .O [2, 3] "acetyl"]
  | .e352A => [.addedRing .fusion [1, 2] [.O, .N], .modification [2] "phenyl oxazole"]
  | .e352B =>
      [.addedRing .fusion [1, 2] [.O, .N], .heteroSubstitution .O [3, 4, 6] "acetyl"]
  | .e352C => [.addedRing .fusion [1, 2] [.N, .N], .modification [2, 3] "carbonyl/phenyl"]
  | .e352D =>
      [.addedRing .fusion [1, 2, 3] [.O, .N], .heteroSubstitution .O [4] "acetyl"]
  | .e353A =>
      [.addedRing .spiro [1] [.O, .S, .N], .anhydroBridge 1 5,
        .heteroSubstitution .O [2, 3, 4, 6] "acetyl"]
  | .e353B =>
      [.addedRing .spiro [3] [.O, .N], .acetalBridge [1, 2] [.O, .O] none,
        .heteroSubstitution .O [5] "benzoyl"]
  | .e353C =>
      [.addedRing .spiro [1, 2, 3] [.O, .O], .carbohydrateResidueCount 2,
        .glycosidicLink 1 .O "methyl"]

def glycosideRingMeaning
    (row : Carbohydrate1996GlycosidesRings.PrintedExample) : ImageMeaning :=
  let data := row.data
  { family := glycosideRingFamily row
    sourceKey := data.sourceKey
    acceptedNames := data.acceptedNames
    discouragedNames := data.discouragedNames
    trivialNames := data.trivialNames
    features := glycosideRingFeatures row }

def glycosideRingImageMeanings : List ImageMeaning :=
  Carbohydrate1996GlycosidesRings.PrintedExample.all.map glycosideRingMeaning

@[simp] theorem glycoside_ring_meaning_count : glycosideRingImageMeanings.length = 58 := by
  simp [glycosideRingImageMeanings]

set_option maxRecDepth 8192 in
@[simp] theorem glycoside_ring_meanings_well_formed :
    glycosideRingImageMeanings.all ImageMeaning.wellFormed = true := by decide

end CarbohydrateLateImageMeaningData
end TetraStereo.OneCenter
