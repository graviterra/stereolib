import TetraStereo.OneCenter.CarbohydrateAlditolAcidStereochemistrySemantics

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent carbohydrate O/N-substitution and anhydride semantics

This module audits 2-Carb-24 through 2-Carb-26 of *Nomenclature of Carbohydrates
(Recommendations 1996)*.  It explicitly preserves configuration through substituted amino groups,
distinguishes bisphosphate from diphosphate, and encodes the anomeric-anhydride ring-size order.
-/

namespace Carbohydrate1996HeteroSubstitutionAnhydride

inductive PrintedExample where
  | pentaAcetylGlucose
  | acetylTritylGlucose
  | methanesulfonylGalactose
  | benzoylGlucosylBromide
  | methylGalactopyranose
  | glucoseDihydrogenPhosphate
  | glucosylPhosphate
  | glucoseSixPhosphate
  | fructoseBisphosphate
  | glyceroylBisphosphate
  | glucuronatePhosphate
  | adenosineDiphosphate
  | udpGlucose
  | cmpNeu5Ac
  | ribofuranosidePhosphonate
  | azidoThymidinePhosphonate
  | glucopyranosylPhosphonate
  | galactopyranoseSulfate
  | paps
  | methylacetamidoGlucitol
  | acetylGalactosamine
  | sulfoGlucosamine
  | glycoloylNeuraminic
  | acetylatedNeuraminic
  | anhydroMethylGlucose
  | anhydroAllononitrile
  | anhydroGalactitol
  | anhydroGlucofuranoside
  | anhydroNeuEnonicAcid
  | anhydroGlucopyranose
  | anhydroHeptulopyranose
  | anhydroAcetylGlucose
  | dianhydroTalopyranose
  | anhydroGalactopyranose
  | levoglucosenone
  deriving DecidableEq, Repr

namespace PrintedExample

def all : List PrintedExample :=
  [ .pentaAcetylGlucose, .acetylTritylGlucose, .methanesulfonylGalactose
  , .benzoylGlucosylBromide, .methylGalactopyranose, .glucoseDihydrogenPhosphate
  , .glucosylPhosphate, .glucoseSixPhosphate, .fructoseBisphosphate
  , .glyceroylBisphosphate, .glucuronatePhosphate, .adenosineDiphosphate
  , .udpGlucose, .cmpNeu5Ac, .ribofuranosidePhosphonate
  , .azidoThymidinePhosphonate, .glucopyranosylPhosphonate, .galactopyranoseSulfate
  , .paps, .methylacetamidoGlucitol, .acetylGalactosamine, .sulfoGlucosamine
  , .glycoloylNeuraminic, .acetylatedNeuraminic, .anhydroMethylGlucose
  , .anhydroAllononitrile, .anhydroGalactitol, .anhydroGlucofuranoside
  , .anhydroNeuEnonicAcid, .anhydroGlucopyranose, .anhydroHeptulopyranose
  , .anhydroAcetylGlucose, .dianhydroTalopyranose, .anhydroGalactopyranose
  , .levoglucosenone
  ]

@[simp] theorem mem_all (exampleRow : PrintedExample) : exampleRow ∈ all := by
  cases exampleRow <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 35 := by decide

end PrintedExample

structure PrintedExampleData where
  sourceKey : String
  printedName : String
  deriving DecidableEq, Repr

def PrintedExample.data : PrintedExample → PrintedExampleData
  | .pentaAcetylGlucose => ⟨"2-Carb-24.1/241A", "Penta-O-acetyl-aldehydo-D-glucose; pentaacetate alternative"⟩
  | .acetylTritylGlucose => ⟨"2-Carb-24.1/241B", "2,4-Di-O-acetyl-6-O-trityl-D-glucopyranose"⟩
  | .methanesulfonylGalactose => ⟨"2-Carb-24.1/241C", "6-O-Methanesulfonyl-D-galactopyranose; methanesulfonate alternative"⟩
  | .benzoylGlucosylBromide => ⟨"2-Carb-24.1/241D", "Tetra-O-benzoyl-alpha-D-glucopyranosyl bromide"⟩
  | .methylGalactopyranose => ⟨"2-Carb-24.1/241E", "4,6-Di-O-methyl-alpha-D-galactopyranose"⟩
  | .glucoseDihydrogenPhosphate => ⟨"2-Carb-24.2.1/2421A", "D-Glucopyranose 6-(dihydrogen phosphate); O-phosphono alternative"⟩
  | .glucosylPhosphate => ⟨"2-Carb-24.2.1/2421B", "alpha-D-Glucopyranosyl phosphate (glucose 1-phosphate; Glc1P)"⟩
  | .glucoseSixPhosphate => ⟨"2-Carb-24.2.1/2421C", "D-Glucopyranose 6-phosphate; phosphonato/phospho alternatives; Glc6P"⟩
  | .fructoseBisphosphate => ⟨"2-Carb-24.2.1/2421D", "D-Fructofuranose 1,6-bisphosphate; two alternatives"⟩
  | .glyceroylBisphosphate => ⟨"2-Carb-24.2.1/2421E", "3-O-Phosphonato-D-glyceroyl phosphate; 1,3-bisphospho-D-glycerate"⟩
  | .glucuronatePhosphate => ⟨"2-Carb-24.2.1/2421F", "alpha-D-Glucopyranuronic acid 1-(dihydrogen phosphate); GlcA1P"⟩
  | .adenosineDiphosphate => ⟨"2-Carb-24.2.1/2421G", "Adenosine 5'-diphosphate (ADP); 5'-diphosphoadenosine"⟩
  | .udpGlucose => ⟨"2-Carb-24.2.1/2421H", "Uridine 5'-(alpha-D-glucopyranosyl diphosphate) (UDP-Glc)"⟩
  | .cmpNeu5Ac => ⟨"2-Carb-24.2.1/2421I", "Cytidine 5'-(beta-D-Neu5Ac monophosphate) (CMP-beta-Neu5Ac)"⟩
  | .ribofuranosidePhosphonate => ⟨"2-Carb-24.2.2/2422A", "Methyl beta-D-ribofuranoside 5-(hydrogen phosphonate); deoxy-yl alternative"⟩
  | .azidoThymidinePhosphonate => ⟨"2-Carb-24.2.2/2422B", "3'-Azido-3'-deoxythymidine 5'-[(sugar onate) phosphonate]"⟩
  | .glucopyranosylPhosphonate => ⟨"2-Carb-24.2.2/2422C", "2-Deoxy-2-dimethoxyphosphoryl-D-glucopyranose; phosphonate alternative"⟩
  | .galactopyranoseSulfate => ⟨"2-Carb-24.3/243A", "alpha-D-Galactopyranose 2-sulfate; O-sulfonato alternative"⟩
  | .paps => ⟨"2-Carb-24.3/243B", "3'-Phospho-5'-adenylyl sulfate (PAPS)"⟩
  | .methylacetamidoGlucitol => ⟨"2-Carb-25/25A", "1,3,4,5,6-Penta-O-acetyl-2-deoxy-2-(N-methylacetamido)-D-glucitol"⟩
  | .acetylGalactosamine => ⟨"2-Carb-25/25B", "2-Acetamido-2-deoxy-D-galactopyranose; N-acetyl-D-galactosamine"⟩
  | .sulfoGlucosamine => ⟨"2-Carb-25/25C", "2-Deoxy-2-sulfoamino-D-glucopyranose; N-sulfo-D-glucosamine"⟩
  | .glycoloylNeuraminic => ⟨"2-Carb-25/25D", "N-Glycoloyl-alpha-neuraminic acid (alpha-Neu5Gc); D implied"⟩
  | .acetylatedNeuraminic => ⟨"2-Carb-25/25E", "5-N-Acetyl-4,8,9-tri-O-acetyl-alpha-neuraminic acid"⟩
  | .anhydroMethylGlucose => ⟨"2-Carb-26/26A", "3,6-Anhydro-2,4,5-tri-O-methyl-D-glucose"⟩
  | .anhydroAllononitrile => ⟨"2-Carb-26/26B", "2,5-Anhydro-D-allononitrile"⟩
  | .anhydroGalactitol => ⟨"2-Carb-26/26C", "1,5-Anhydro-D-galactitol"⟩
  | .anhydroGlucofuranoside => ⟨"2-Carb-26/26D", "Methyl 3,6-anhydro-2,5-di-O-methyl-beta-D-glucofuranoside"⟩
  | .anhydroNeuEnonicAcid => ⟨"2-Carb-26/26E", "5-Acetamido-2,6-anhydro-3,5-dideoxy-D-glycero-D-galacto-non-2-enonic acid"⟩
  | .anhydroGlucopyranose => ⟨"2-Carb-26/26F", "1,6-Anhydro-beta-D-glucopyranose; septanose alternative and levoglucosan rejected"⟩
  | .anhydroHeptulopyranose => ⟨"2-Carb-26/26G", "2,7-Anhydro-beta-D-altro-hept-2-ulopyranose (older sedoheptulosan)"⟩
  | .anhydroAcetylGlucose => ⟨"2-Carb-26/26H", "3,4,6-Tri-O-acetyl-1,2-anhydro-alpha-D-glucopyranose; oxirose alternative rejected"⟩
  | .dianhydroTalopyranose => ⟨"2-Carb-26/26I", "1,6:3,4-Dianhydro-beta-D-talopyranose"⟩
  | .anhydroGalactopyranose => ⟨"2-Carb-26/26J", "1,4-Anhydro-beta-D-galactopyranose"⟩
  | .levoglucosenone => ⟨"2-Carb-26/26K", "1,6-Anhydro-3,4-dideoxy-beta-D-glycero-hex-3-enopyranos-2-ulose (levoglucosenone)"⟩

theorem printed_example_keys_are_pairwise_distinct :
    (PrintedExample.all.map fun exampleRow => exampleRow.data.sourceKey).Nodup := by
  decide

inductive Provision where
  | alcoholicHydroxyHydrogenReplacementIsOSubstitution
  | oLocantNotRepeatedForSameMultipleReplacement
  | numberLocantsSpecifyPositions
  | identicalFullSubstitutionNeedsNoNumberLocants
  | esterEtherPeriphrasesMayIndex
  | anomericOAcylUsesOAcylButOAlkylIsGlycoside
  | biochemicalPhosphateIgnoresIonizationAndCounterion
  | phosphonoAndPhosphonatoPrefixes
  | biochemicalPhosphoPrefix
  | multipleIndependentPhosphatesUseBisTris
  | diphosphateMeansDiphosphoricAcidEster
  | capitalPAbbreviationConvention
  | phosphonateExamplesDefineTerminology
  | phosphorusSubstitutionUsesStandardRules
  | pcLinkedGroupTwoNamingRoutes
  | phosphinateUsesPhosphonateMethods
  | twoPCBondExamplesRouteToThirtyOne
  | sulfoAndSulfonatoPrefixes
  | sulfateMayBePostposedWithLocant
  | papsNamedAsAcylSulfate
  | substitutedAminoGroupHasTwoNamingMethods
  | completeSubstitutedAminoPrefixRetainsHydroxyConfigurationRole
  | trivialAminoSugarUsesItalicNPrefix
  | heteroatomSubstitutionUsesCarbonLocantThenElement
  | sameHeteroatomSubstituentsGrouped
  | heteroatomKindsAlphabetized
  | superscriptHeteroatomLocantsUnusualInCarbohydrates
  | intramolecularEtherIsFormalWaterLoss
  | anhydroPrefixUsesTwoHydroxyLocants
  | anhydroIsDetachableAlphabetizedPrefix
  | anomericHydroxyAnhydridesUseSameProcedure
  | anomericAnhydrideRingPreference
  | threeAndFourMemberedRingsPreferAnhydro
  | anhydroTrivialNamesNotRecommended
  | printedExample (exampleRow : PrintedExample)
  deriving DecidableEq, Repr

namespace Provision

def base : List Provision :=
  [ .alcoholicHydroxyHydrogenReplacementIsOSubstitution
  , .oLocantNotRepeatedForSameMultipleReplacement, .numberLocantsSpecifyPositions
  , .identicalFullSubstitutionNeedsNoNumberLocants, .esterEtherPeriphrasesMayIndex
  , .anomericOAcylUsesOAcylButOAlkylIsGlycoside
  , .biochemicalPhosphateIgnoresIonizationAndCounterion, .phosphonoAndPhosphonatoPrefixes
  , .biochemicalPhosphoPrefix, .multipleIndependentPhosphatesUseBisTris
  , .diphosphateMeansDiphosphoricAcidEster, .capitalPAbbreviationConvention
  , .phosphonateExamplesDefineTerminology, .phosphorusSubstitutionUsesStandardRules
  , .pcLinkedGroupTwoNamingRoutes, .phosphinateUsesPhosphonateMethods
  , .twoPCBondExamplesRouteToThirtyOne, .sulfoAndSulfonatoPrefixes
  , .sulfateMayBePostposedWithLocant, .papsNamedAsAcylSulfate
  , .substitutedAminoGroupHasTwoNamingMethods
  , .completeSubstitutedAminoPrefixRetainsHydroxyConfigurationRole
  , .trivialAminoSugarUsesItalicNPrefix, .heteroatomSubstitutionUsesCarbonLocantThenElement
  , .sameHeteroatomSubstituentsGrouped, .heteroatomKindsAlphabetized
  , .superscriptHeteroatomLocantsUnusualInCarbohydrates
  , .intramolecularEtherIsFormalWaterLoss, .anhydroPrefixUsesTwoHydroxyLocants
  , .anhydroIsDetachableAlphabetizedPrefix, .anomericHydroxyAnhydridesUseSameProcedure
  , .anomericAnhydrideRingPreference, .threeAndFourMemberedRingsPreferAnhydro
  , .anhydroTrivialNamesNotRecommended
  ]

def all : List Provision := base ++ PrintedExample.all.map Provision.printedExample

@[simp] theorem mem_all (provision : Provision) : provision ∈ all := by
  cases provision with
  | printedExample exampleRow =>
      apply List.mem_append_right
      exact List.mem_map_of_mem (f := Provision.printedExample) exampleRow.mem_all
  | _ => simp [all, base]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 69 := by decide

end Provision

def Provision.sourceKey : Provision → String
  | .alcoholicHydroxyHydrogenReplacementIsOSubstitution
  | .oLocantNotRepeatedForSameMultipleReplacement | .numberLocantsSpecifyPositions
  | .identicalFullSubstitutionNeedsNoNumberLocants | .esterEtherPeriphrasesMayIndex
  | .anomericOAcylUsesOAcylButOAlkylIsGlycoside => "2-Carb-24.1"
  | .biochemicalPhosphateIgnoresIonizationAndCounterion | .phosphonoAndPhosphonatoPrefixes
  | .biochemicalPhosphoPrefix | .multipleIndependentPhosphatesUseBisTris
  | .diphosphateMeansDiphosphoricAcidEster | .capitalPAbbreviationConvention => "2-Carb-24.2.1"
  | .phosphonateExamplesDefineTerminology | .phosphorusSubstitutionUsesStandardRules
  | .pcLinkedGroupTwoNamingRoutes => "2-Carb-24.2.2"
  | .phosphinateUsesPhosphonateMethods | .twoPCBondExamplesRouteToThirtyOne => "2-Carb-24.2.3"
  | .sulfoAndSulfonatoPrefixes | .sulfateMayBePostposedWithLocant
  | .papsNamedAsAcylSulfate => "2-Carb-24.3"
  | .substitutedAminoGroupHasTwoNamingMethods
  | .completeSubstitutedAminoPrefixRetainsHydroxyConfigurationRole
  | .trivialAminoSugarUsesItalicNPrefix | .heteroatomSubstitutionUsesCarbonLocantThenElement
  | .sameHeteroatomSubstituentsGrouped | .heteroatomKindsAlphabetized
  | .superscriptHeteroatomLocantsUnusualInCarbohydrates => "2-Carb-25"
  | .intramolecularEtherIsFormalWaterLoss | .anhydroPrefixUsesTwoHydroxyLocants
  | .anhydroIsDetachableAlphabetizedPrefix | .anomericHydroxyAnhydridesUseSameProcedure
  | .anomericAnhydrideRingPreference | .threeAndFourMemberedRingsPreferAnhydro
  | .anhydroTrivialNamesNotRecommended => "2-Carb-26"
  | .printedExample exampleRow => exampleRow.data.sourceKey

/-! ## Executable stereochemical boundaries -/

inductive AminoNamingMethod where
  | completeSubstitutedAminoPrefix
  | trivialNameWithNPrefix
  deriving DecidableEq, Repr

inductive ConfigurationalRole where
  | formerHydroxyPosition
  deriving DecidableEq, Repr

def substitutedAminoConfigurationalRole : AminoNamingMethod → ConfigurationalRole
  | .completeSubstitutedAminoPrefix | .trivialNameWithNPrefix => .formerHydroxyPosition

@[simp] theorem both_amino_naming_methods_preserve_the_former_hydroxy_role :
    substitutedAminoConfigurationalRole .completeSubstitutedAminoPrefix = .formerHydroxyPosition ∧
      substitutedAminoConfigurationalRole .trivialNameWithNPrefix = .formerHydroxyPosition := by
  decide

inductive PhosphateMultiplicity where
  | bisphosphate
  | diphosphate
  deriving DecidableEq, Repr

def PhosphateMultiplicity.meaning : PhosphateMultiplicity → String
  | .bisphosphate => "two independent phosphate groups"
  | .diphosphate => "one diphosphoric-acid ester"

theorem bisphosphate_and_diphosphate_are_not_synonyms :
    PhosphateMultiplicity.bisphosphate.meaning ≠ PhosphateMultiplicity.diphosphate.meaning := by
  decide

inductive HeteroatomKind where
  | nitrogen
  | oxygen
  deriving DecidableEq, Repr

def heteroatomAlphabeticalRank : HeteroatomKind → Nat
  | .nitrogen => 0
  | .oxygen => 1

@[simp] theorem nitrogen_substitution_precedes_oxygen_substitution :
    heteroatomAlphabeticalRank .nitrogen < heteroatomAlphabeticalRank .oxygen := by
  decide

inductive AnhydrideRingDesignator where
  | septanose
  | furanose
  | pyranose
  deriving DecidableEq, Repr

def anomericAnhydridePreference : AnhydrideRingDesignator → Nat
  | .septanose => 0
  | .furanose => 1
  | .pyranose => 2

@[simp] theorem anomeric_anhydride_ring_preference_is_exact :
    anomericAnhydridePreference .pyranose > anomericAnhydridePreference .furanose ∧
      anomericAnhydridePreference .furanose > anomericAnhydridePreference .septanose := by
  decide

def tinyRingUsesAnhydro (ringAtomCount : Nat) : Bool := ringAtomCount = 3 || ringAtomCount = 4

@[simp] theorem three_and_four_membered_rings_use_anhydro :
    tinyRingUsesAnhydro 3 = true ∧ tinyRingUsesAnhydro 4 = true ∧
      tinyRingUsesAnhydro 5 = false := by
  decide

end Carbohydrate1996HeteroSubstitutionAnhydride

end TetraStereo.OneCenter
