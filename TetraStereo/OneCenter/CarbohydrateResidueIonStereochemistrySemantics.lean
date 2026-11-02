import TetraStereo.OneCenter.CarbohydrateAcetalStereochemistrySemantics

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent carbohydrate residue, radical, and ion semantics

This module audits 2-Carb-31 and 2-Carb-32.  Its central stereochemical rule is that a secondary
free valence is treated as equivalent to hydroxy for configurational-prefix assignment, while the
alpha/beta symbol of a `1-hydroxy-...yl` residue describes the free valence rather than the retained
anomeric hydroxy group.
-/

namespace Carbohydrate1996ResiduesIons

inductive PrintedExample where
  | fructosOneYl | aminoGlucosTwoYl | ribopyranosidTwoOYl | glucosTwoCYl
  | deoxyGlucosTwoYl | mannitolThreeYl | arabinitolOneCYl | hydroxyAllopyranosyl
  | allopyranosylBenzoyl | fructopyranosylAlanine | bisFructopyranosylToluidine
  | adenosylMethionine | ribofuranosylDisulfide | glucopyranosylAceticAcid
  | glucopyranosidylPyruvicAcid | glucopyranosyloxyIndole | bisDeoxyGlucosidylEtherAmine
  | talopyranoseDiylPhosphinite | glucosideDiylPhosphinite | glucosidYlidenePhosphane
  | fructosOYlRadical | glucopyranosylRadical | methoxyGlucopyranosylRadical
  | pentopyranosidYlidene | hexosCYlium | deoxyHexosYlium | glucopyranosylium
  | ethyliumDiylAllopyranose | ribopyranosidTwoOium | ribopyranosidFiveOium
  | ribopyranosidTwoOate | hexosCIde | deoxyHexosIde | glucitolOneIde
  | glucopyranosiumyl | deoxyHexosIdYl
  deriving DecidableEq, Repr

namespace PrintedExample

def all : List PrintedExample :=
  [ .fructosOneYl, .aminoGlucosTwoYl, .ribopyranosidTwoOYl, .glucosTwoCYl
  , .deoxyGlucosTwoYl, .mannitolThreeYl, .arabinitolOneCYl, .hydroxyAllopyranosyl
  , .allopyranosylBenzoyl, .fructopyranosylAlanine, .bisFructopyranosylToluidine
  , .adenosylMethionine, .ribofuranosylDisulfide, .glucopyranosylAceticAcid
  , .glucopyranosidylPyruvicAcid, .glucopyranosyloxyIndole
  , .bisDeoxyGlucosidylEtherAmine, .talopyranoseDiylPhosphinite
  , .glucosideDiylPhosphinite, .glucosidYlidenePhosphane, .fructosOYlRadical
  , .glucopyranosylRadical, .methoxyGlucopyranosylRadical, .pentopyranosidYlidene
  , .hexosCYlium, .deoxyHexosYlium, .glucopyranosylium, .ethyliumDiylAllopyranose
  , .ribopyranosidTwoOium, .ribopyranosidFiveOium, .ribopyranosidTwoOate
  , .hexosCIde, .deoxyHexosIde, .glucitolOneIde, .glucopyranosiumyl
  , .deoxyHexosIdYl
  ]

@[simp] theorem mem_all (exampleRow : PrintedExample) : exampleRow ∈ all := by
  cases exampleRow <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 36 := by decide

end PrintedExample

structure PrintedExampleData where
  sourceKey : String
  printedText : String
  deriving DecidableEq, Repr

def PrintedExample.data : PrintedExample → PrintedExampleData
  | .fructosOneYl => ⟨"2-Carb-31.2/312A", "1-Deoxy-D-fructos-1-yl"⟩
  | .aminoGlucosTwoYl => ⟨"2-Carb-31.2/312B", "2-Amino-2-deoxy-D-glucos-2-yl"⟩
  | .ribopyranosidTwoOYl => ⟨"2-Carb-31.2/312C", "(Methyl beta-D-ribopyranosid-2-O-yl)"⟩
  | .glucosTwoCYl => ⟨"2-Carb-31.2/312D", "D-Glucos-2-C-yl"⟩
  | .deoxyGlucosTwoYl => ⟨"2-Carb-31.2/312E", "2-Deoxy-D-glucos-2-yl"⟩
  | .mannitolThreeYl => ⟨"2-Carb-31.2/312F", "3-Deoxy-D-mannitol-3-yl"⟩
  | .arabinitolOneCYl => ⟨"2-Carb-31.2/312G", "L-Arabinitol-1-C-yl; R/S to be specified"⟩
  | .hydroxyAllopyranosyl => ⟨"2-Carb-31.2/312H", "1-Hydroxy-alpha-D-allopyranosyl"⟩
  | .allopyranosylBenzoyl => ⟨"2-Carb-31.2/312I", "4-(1-Acetoxy-2,3,4,6-tetra-O-acetyl-alpha-D-allopyranosyl)benzoyl chloride"⟩
  | .fructopyranosylAlanine => ⟨"2-Carb-31.2/312J", "N-(1-Deoxy-D-fructopyranos-1-yl)-L-alanine"⟩
  | .bisFructopyranosylToluidine => ⟨"2-Carb-31.2/312K", "N,N-Bis-(1-deoxy-D-fructopyranos-1-yl)-p-toluidine"⟩
  | .adenosylMethionine => ⟨"2-Carb-31.2/312L", "S-(5'-Deoxyadenosin-5'-yl)-L-methionine (AdoMet/SAM); systematic alternative"⟩
  | .ribofuranosylDisulfide => ⟨"2-Carb-31.2/312M", "Bis(5-deoxy-beta-D-ribofuranos-5-yl) disulfide/disulfane"⟩
  | .glucopyranosylAceticAcid => ⟨"2-Carb-31.2/312N", "(beta-D-Glucopyranos-2-O-yl)acetic acid; carboxymethyl alternative"⟩
  | .glucopyranosidylPyruvicAcid => ⟨"2-Carb-31.2/312O", "(Methyl alpha-D-glucopyranosid-4-O-yl)pyruvic acid; oxalomethyl alternative"⟩
  | .glucopyranosyloxyIndole => ⟨"2-Carb-31.2/312P", "3-(beta-D-Glucopyranosyloxy)indole; glucopyranoside; indican"⟩
  | .bisDeoxyGlucosidylEtherAmine => ⟨"2-Carb-31.2/312Q", "X=O ether and X=NH amine alternatives for methyl deoxy glucosidyl groups"⟩
  | .talopyranoseDiylPhosphinite => ⟨"2-Carb-31.3/313A", "Methyl beta-D-talopyranose-2-C,4-C-diylphosphinite; two alternatives including (2R,4S)"⟩
  | .glucosideDiylPhosphinite => ⟨"2-Carb-31.3/313B", "Methyl (ethyl 2,4-dideoxy-beta-D-glucopyranoside-2,4-diyl)phosphinite"⟩
  | .glucosidYlidenePhosphane => ⟨"2-Carb-31.3/313C", "(Methyl 6-deoxy-beta-D-glucopyranosid-6-ylidene)triphenyl-lambda5-phosphane"⟩
  | .fructosOYlRadical => ⟨"2-Carb-32.1/321A", "1,3,5,6-Tetra-O-methyl-D-fructos-4-O-yl"⟩
  | .glucopyranosylRadical => ⟨"2-Carb-32.1/321B", "Tetra-O-benzyl-D-glucopyranosyl"⟩
  | .methoxyGlucopyranosylRadical => ⟨"2-Carb-32.1/321C", "2,3,4,6-Tetra-O-benzyl-1-methoxy-D-glucopyranosyl"⟩
  | .pentopyranosidYlidene => ⟨"2-Carb-32.1/321D", "Methyl 2-deoxy-beta-D-erythro-pentopyranosid-2-ylidene"⟩
  | .hexosCYlium => ⟨"2-Carb-32.2/322A", "D-arabino-Hexos-2-C-ylium"⟩
  | .deoxyHexosYlium => ⟨"2-Carb-32.2/322B", "2-Deoxy-D-arabino-hexos-2-ylium"⟩
  | .glucopyranosylium => ⟨"2-Carb-32.2/322C", "D-Glucopyranosylium"⟩
  | .ethyliumDiylAllopyranose => ⟨"2-Carb-32.2/322D", "3,4,6-Tri-O-acetyl-1,2-O-ethyliumdiyl-alpha-D-allopyranose"⟩
  | .ribopyranosidTwoOium => ⟨"2-Carb-32.2/322E", "Methyl 3,4-di-O-methyl-beta-D-ribopyranosid-2-O-ium"⟩
  | .ribopyranosidFiveOium => ⟨"2-Carb-32.2/322F", "Methyl 2,3,4-tri-O-methyl-beta-D-ribopyranosid-5-O-ium"⟩
  | .ribopyranosidTwoOate => ⟨"2-Carb-32.3/323A", "Methyl 3,4-di-O-methyl-beta-D-ribopyranosid-2-O-ate"⟩
  | .hexosCIde => ⟨"2-Carb-32.3/323B", "D-arabino-Hexos-2-C-ide"⟩
  | .deoxyHexosIde => ⟨"2-Carb-32.3/323C", "2-Deoxy-D-arabino-hexos-2-ide"⟩
  | .glucitolOneIde => ⟨"2-Carb-32.3/323D", "1,5-Anhydro-2,3,4,6-tetra-O-methyl-D-glucitol-1-ide"⟩
  | .glucopyranosiumyl => ⟨"2-Carb-32.4/324A", "D-Glucopyranosiumyl; or D-glucopyranose radical cation"⟩
  | .deoxyHexosIdYl => ⟨"2-Carb-32.4/324B", "2-Deoxy-D-arabino-hexos-2-id-2-yl; radical-anion alternative"⟩

theorem printed_example_keys_are_pairwise_distinct :
    (PrintedExample.all.map fun exampleRow => exampleRow.data.sourceKey).Nodup := by decide

inductive Provision where
  | glycosylResidueDropsAnomericHydroxyAndEToYl
  | glycosylResiduesUsedForGlycosidesAndOligosaccharides
  | glycosylAlsoUsedRadicofunctionally
  | carbohydrateSubstituentPrefixesAllowNoncarbohydrateParent
  | residueEndingsNCylNOylOrNyl
  | residueYlMeansLossOfHydrogenAtN
  | secondaryFreeValenceEquivalentToHydroxy
  | alditolResiduesUseSameEndings
  | unlocantedYlMeansLossOfAnomericHydroxy
  | unlocantedYloxyMeansLossOfAnomericHydroxyHydrogen
  | retainedAnomericHydroxyCarbonLossUsesOneHydroxyYl
  | retainedAnomericHydroxyAlphaBetaRefersToFreeValence
  | differentCarbonHydrogenLossUsesDiylTriyl
  | sameCarbonMultipleHydrogenLossUsesYlidene
  | phosphaneTerminologyPreferred
  | radicalNamesFollowSubstituentNames
  | carbeneUsesYlidene
  | carbonHydrideLossCationUsesYlium
  | oxygenHydronationUsesLocantedOium
  | oxygenProtonLossAnionUsesLocantedOate
  | carbonProtonLossAnionUsesIde
  | radicalIonMayAddYlToIonName
  | unspecifiedRadicalIonMayUsePostposedClass
  | revisedRadicalIonAuthorityDelegated
  | printedExample (exampleRow : PrintedExample)
  deriving DecidableEq, Repr

namespace Provision
def base : List Provision :=
  [ .glycosylResidueDropsAnomericHydroxyAndEToYl
  , .glycosylResiduesUsedForGlycosidesAndOligosaccharides
  , .glycosylAlsoUsedRadicofunctionally
  , .carbohydrateSubstituentPrefixesAllowNoncarbohydrateParent
  , .residueEndingsNCylNOylOrNyl, .residueYlMeansLossOfHydrogenAtN
  , .secondaryFreeValenceEquivalentToHydroxy, .alditolResiduesUseSameEndings
  , .unlocantedYlMeansLossOfAnomericHydroxy
  , .unlocantedYloxyMeansLossOfAnomericHydroxyHydrogen
  , .retainedAnomericHydroxyCarbonLossUsesOneHydroxyYl
  , .retainedAnomericHydroxyAlphaBetaRefersToFreeValence
  , .differentCarbonHydrogenLossUsesDiylTriyl, .sameCarbonMultipleHydrogenLossUsesYlidene
  , .phosphaneTerminologyPreferred, .radicalNamesFollowSubstituentNames
  , .carbeneUsesYlidene, .carbonHydrideLossCationUsesYlium
  , .oxygenHydronationUsesLocantedOium, .oxygenProtonLossAnionUsesLocantedOate
  , .carbonProtonLossAnionUsesIde, .radicalIonMayAddYlToIonName
  , .unspecifiedRadicalIonMayUsePostposedClass, .revisedRadicalIonAuthorityDelegated
  ]

def all : List Provision := base ++ PrintedExample.all.map Provision.printedExample

@[simp] theorem mem_all (provision : Provision) : provision ∈ all := by
  cases provision with
  | printedExample exampleRow =>
      apply List.mem_append_right
      exact List.mem_map_of_mem (f := Provision.printedExample) exampleRow.mem_all
  | _ => simp [all, base]

theorem all_nodup : all.Nodup := by decide
@[simp] theorem length_all : all.length = 60 := by decide
end Provision

def Provision.sourceKey : Provision → String
  | .glycosylResidueDropsAnomericHydroxyAndEToYl
  | .glycosylResiduesUsedForGlycosidesAndOligosaccharides
  | .glycosylAlsoUsedRadicofunctionally => "2-Carb-31.1"
  | .carbohydrateSubstituentPrefixesAllowNoncarbohydrateParent
  | .residueEndingsNCylNOylOrNyl | .residueYlMeansLossOfHydrogenAtN
  | .secondaryFreeValenceEquivalentToHydroxy | .alditolResiduesUseSameEndings
  | .unlocantedYlMeansLossOfAnomericHydroxy
  | .unlocantedYloxyMeansLossOfAnomericHydroxyHydrogen
  | .retainedAnomericHydroxyCarbonLossUsesOneHydroxyYl
  | .retainedAnomericHydroxyAlphaBetaRefersToFreeValence => "2-Carb-31.2"
  | .differentCarbonHydrogenLossUsesDiylTriyl | .sameCarbonMultipleHydrogenLossUsesYlidene
  | .phosphaneTerminologyPreferred => "2-Carb-31.3"
  | .radicalNamesFollowSubstituentNames | .carbeneUsesYlidene => "2-Carb-32.1"
  | .carbonHydrideLossCationUsesYlium | .oxygenHydronationUsesLocantedOium => "2-Carb-32.2"
  | .oxygenProtonLossAnionUsesLocantedOate | .carbonProtonLossAnionUsesIde => "2-Carb-32.3"
  | .radicalIonMayAddYlToIonName | .unspecifiedRadicalIonMayUsePostposedClass
  | .revisedRadicalIonAuthorityDelegated => "2-Carb-32.4"
  | .printedExample exampleRow => exampleRow.data.sourceKey

inductive ResidueEvent where
  | secondaryCarbonHydrogenLoss
  | anomericHydroxyLoss
  | anomericHydroxyHydrogenLoss
  | anomericCarbonHydrogenLossHydroxyRetained
  deriving DecidableEq, Repr

inductive AnomericSymbolReferent where | absent | hydroxyGroup | freeValence
  deriving DecidableEq, Repr

def anomericSymbolReferent : ResidueEvent → AnomericSymbolReferent
  | .secondaryCarbonHydrogenLoss => .absent
  | .anomericHydroxyLoss => .freeValence
  | .anomericHydroxyHydrogenLoss => .hydroxyGroup
  | .anomericCarbonHydrogenLossHydroxyRetained => .freeValence

@[simp] theorem one_hydroxy_anomeric_residue_symbol_describes_free_valence :
    anomericSymbolReferent .anomericCarbonHydrogenLossHydroxyRetained = .freeValence := by rfl

inductive ChargeCenter where | carbon | oxygen
  deriving DecidableEq, Repr
inductive ChargeChange where | hydrideLoss | protonLoss | hydronation
  deriving DecidableEq, Repr

def ionSuffix : ChargeCenter → ChargeChange → Option String
  | .carbon, .hydrideLoss => some "ylium"
  | .oxygen, .hydronation => some "O-ium"
  | .oxygen, .protonLoss => some "O-ate"
  | .carbon, .protonLoss => some "ide"
  | _, _ => none

@[simp] theorem ion_suffix_routes_are_exact :
    ionSuffix .carbon .hydrideLoss = some "ylium" ∧
      ionSuffix .oxygen .hydronation = some "O-ium" ∧
      ionSuffix .oxygen .protonLoss = some "O-ate" ∧
      ionSuffix .carbon .protonLoss = some "ide" := by decide

end Carbohydrate1996ResiduesIons
end TetraStereo.OneCenter
