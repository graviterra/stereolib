import TetraStereo.OneCenter.CarbohydrateUnsaturatedBranchedStereochemistrySemantics

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent alditol and carbohydrate-acid stereochemistry semantics

This module audits 2-Carb-19 through 2-Carb-23 of *Nomenclature of Carbohydrates
(Recommendations 1996)*.  These sections are stereochemically significant because symmetry can
remove D/L from an alditol or aldaric-acid parent, substitution can require it again, and tartaric
acid is explicitly routed to CIP R/S because historical D/L usage is unreliable.
-/

namespace Carbohydrate1996AlditolsAcids

inductive MesoAldaricName where
  | erythraric
  | ribaric
  | xylaric
  | allaric
  | galactaric
  deriving DecidableEq, Repr

namespace MesoAldaricName

def all : List MesoAldaricName :=
  [ .erythraric, .ribaric, .xylaric, .allaric, .galactaric ]

@[simp] theorem mem_all (name : MesoAldaricName) : name ∈ all := by
  cases name <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 5 := by decide

end MesoAldaricName

def MesoAldaricName.text : MesoAldaricName → String
  | .erythraric => "meso-erythraric acid"
  | .ribaric => "meso-ribaric acid"
  | .xylaric => "meso-xylaric acid"
  | .allaric => "meso-allaric acid"
  | .galactaric => "meso-galactaric acid"

theorem meso_aldaric_inventory_is_pairwise_distinct :
    (MesoAldaricName.all.map MesoAldaricName.text).Nodup := by
  decide

inductive PrintedExample where
  | heptitol
  | octitol
  | arabinitol
  | glucitol
  | fucitol
  | rhamnitol
  | mesoErythritol
  | mesoRibitol
  | mesoGalactitol
  | mesoHeptitol
  | methylGalactitol
  | gluconicAcid
  | gluconate
  | aminoGluconicAcid
  | sodiumGluconate
  | methylGluconate
  | isopropylMannonate
  | dimethylXylonamide
  | deoxyPentonate
  | acetylArabinonate
  | gluconoOneFourLactone
  | gluconoOneFiveLactone
  | deoxyRiboLactone
  | aminoMannonoLactam
  | gluconoylChloride
  | erythroPentUlosonic
  | arabinoHexFiveUlosonic
  | arabinoHexUlopyranosonic
  | kdoForm
  | ethylGlycosiduronate
  | arabinoUlosonoLactone
  | isatanB
  | ascorbicEquilibrium
  | glucuronicAcid
  | mannopyranuronicAcid
  | phenylGlucopyranosiduronic
  | methylIdopyranosiduronic
  | glucopyranosyluronateBromide
  | glucofuranosidurononitrile
  | sodiumGlucofuranosiduronate
  | ethylMannofuranuronate
  | glucuronoLactone
  | glucofuranuronoLactone
  | methylGlucofuranosiduronoLactone
  | deoxyEnopyranuronicAcid
  | methylDeoxyEnopyranuronate
  | methylDeoxyEnopyranosiduronic
  | methylPhenylEnopyranosiduronate
  | galactopyranosiduronamide
  | altraricAcid
  | glucaricAcid
  | heptaricAcid
  | mesoXylaricAcid
  | mesoGalactaricAcid
  | methylDGalactaricAcid
  | positiveTartaricAcid
  | negativeTartaricAcid
  | mesoTartaricAcid
  | oneMethylHydrogenGalactarate
  | sixMethylHydrogenGalactarate
  | glucarOneAmicAcid
  | methylGlucarSixAmate
  | mannaroDilactone
  deriving DecidableEq, Repr

namespace PrintedExample

def all : List PrintedExample :=
  [ .heptitol, .octitol, .arabinitol, .glucitol, .fucitol, .rhamnitol
  , .mesoErythritol, .mesoRibitol, .mesoGalactitol, .mesoHeptitol
  , .methylGalactitol, .gluconicAcid, .gluconate, .aminoGluconicAcid
  , .sodiumGluconate, .methylGluconate, .isopropylMannonate
  , .dimethylXylonamide, .deoxyPentonate, .acetylArabinonate
  , .gluconoOneFourLactone, .gluconoOneFiveLactone, .deoxyRiboLactone
  , .aminoMannonoLactam, .gluconoylChloride, .erythroPentUlosonic
  , .arabinoHexFiveUlosonic, .arabinoHexUlopyranosonic, .kdoForm
  , .ethylGlycosiduronate, .arabinoUlosonoLactone, .isatanB
  , .ascorbicEquilibrium, .glucuronicAcid, .mannopyranuronicAcid
  , .phenylGlucopyranosiduronic, .methylIdopyranosiduronic
  , .glucopyranosyluronateBromide, .glucofuranosidurononitrile
  , .sodiumGlucofuranosiduronate, .ethylMannofuranuronate, .glucuronoLactone
  , .glucofuranuronoLactone, .methylGlucofuranosiduronoLactone
  , .deoxyEnopyranuronicAcid, .methylDeoxyEnopyranuronate
  , .methylDeoxyEnopyranosiduronic, .methylPhenylEnopyranosiduronate
  , .galactopyranosiduronamide, .altraricAcid, .glucaricAcid, .heptaricAcid
  , .mesoXylaricAcid, .mesoGalactaricAcid, .methylDGalactaricAcid
  , .positiveTartaricAcid, .negativeTartaricAcid, .mesoTartaricAcid
  , .oneMethylHydrogenGalactarate, .sixMethylHydrogenGalactarate
  , .glucarOneAmicAcid, .methylGlucarSixAmate, .mannaroDilactone
  ]

@[simp] theorem mem_all (exampleRow : PrintedExample) : exampleRow ∈ all := by
  cases exampleRow <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 63 := by decide

end PrintedExample

structure PrintedExampleData where
  sourceKey : String
  printedName : String
  deriving DecidableEq, Repr

def PrintedExample.data : PrintedExample → PrintedExampleData
  | .heptitol => ⟨"2-Carb-19.1/191A", "D-glycero-L-galacto-Heptitol; not L-glycero-D-manno"⟩
  | .octitol => ⟨"2-Carb-19.1/191B", "D-erythro-L-galacto-Octitol; not D-threo-L-gulo"⟩
  | .arabinitol => ⟨"2-Carb-19.1/191C", "D-Arabinitol (Ara-ol); not D-lyxitol"⟩
  | .glucitol => ⟨"2-Carb-19.1/191D", "D-Glucitol (Glc-ol); not L-gulitol; sorbitol not recommended"⟩
  | .fucitol => ⟨"2-Carb-19.1/191E", "L-Fucitol (L-Fuc-ol) or 1-deoxy-D-galactitol; not 6-deoxy-L-galactitol"⟩
  | .rhamnitol => ⟨"2-Carb-19.1/191F", "L-Rhamnitol (L-Rha-ol) or 1-deoxy-L-mannitol"⟩
  | .mesoErythritol => ⟨"2-Carb-19.2/unnumbered-1", "meso-Erythritol"⟩
  | .mesoRibitol => ⟨"2-Carb-19.2/unnumbered-2", "meso-Ribitol"⟩
  | .mesoGalactitol => ⟨"2-Carb-19.2/unnumbered-3", "meso-Galactitol"⟩
  | .mesoHeptitol => ⟨"2-Carb-19.2/192A", "meso-D-glycero-L-ido-Heptitol; alternative rejected"⟩
  | .methylGalactitol => ⟨"2-Carb-19.2/192B", "5-O-Methyl-D-galactitol; not 2-O-methyl-L-galactitol"⟩
  | .gluconicAcid => ⟨"2-Carb-20.1/201A", "D-Gluconic acid"⟩
  | .gluconate => ⟨"2-Carb-20.1/201B", "D-Gluconate"⟩
  | .aminoGluconicAcid => ⟨"2-Carb-20.1/201C", "2-Amino-2-deoxy-D-gluconic acid"⟩
  | .sodiumGluconate => ⟨"2-Carb-20.2/unnumbered", "Sodium D-gluconate"⟩
  | .methylGluconate => ⟨"2-Carb-20.2/202A", "Methyl D-gluconate"⟩
  | .isopropylMannonate => ⟨"2-Carb-20.2/202B", "Isopropyl 3,4-di-O-methyl-L-mannonate"⟩
  | .dimethylXylonamide => ⟨"2-Carb-20.2/202C", "N,N-Dimethyl-L-xylonamide"⟩
  | .deoxyPentonate => ⟨"2-Carb-20.2/202D", "Methyl 3-deoxy-D-threo-pentonate"⟩
  | .acetylArabinonate => ⟨"2-Carb-20.2/202E", "Methyl tetra-O-acetyl-L-arabinonate"⟩
  | .gluconoOneFourLactone => ⟨"2-Carb-20.2/202F", "D-Glucono-1,4-lactone; gamma periphrase not recommended"⟩
  | .gluconoOneFiveLactone => ⟨"2-Carb-20.2/202G", "D-Glucono-1,5-lactone; delta periphrase not recommended"⟩
  | .deoxyRiboLactone => ⟨"2-Carb-20.2/202H", "3-Deoxy-D-ribo-hexono-1,5-lactone"⟩
  | .aminoMannonoLactam => ⟨"2-Carb-20.2/202I", "5-Amino-5-deoxy-D-mannono-1,5-lactam"⟩
  | .gluconoylChloride => ⟨"2-Carb-20.2/202J", "Penta-O-acetyl-D-gluconoyl chloride"⟩
  | .erythroPentUlosonic => ⟨"2-Carb-21.1/211A", "D-erythro-Pent-2-ulosonic acid"⟩
  | .arabinoHexFiveUlosonic => ⟨"2-Carb-21.1/211B", "D-arabino-Hex-5-ulosonic acid"⟩
  | .arabinoHexUlopyranosonic => ⟨"2-Carb-21.1/211C", "alpha-D-arabino-Hex-2-ulopyranosonic acid"⟩
  | .kdoForm => ⟨"2-Carb-21.1/211D", "3-Deoxy-alpha-D-manno-oct-2-ulopyranosonic acid (a Kdo form)"⟩
  | .ethylGlycosiduronate => ⟨"2-Carb-21.2/212A", "Ethyl (methyl alpha-D-arabino-hex-2-ulopyranosid)onate"⟩
  | .arabinoUlosonoLactone => ⟨"2-Carb-21.2/212B", "beta-D-arabino-Hex-2-ulopyranosono-1,5-lactone"⟩
  | .isatanB => ⟨"2-Carb-21.2/212C", "Indol-3-yl D-xylo-hex-5-ulofuranosonate (isatan B)"⟩
  | .ascorbicEquilibrium => ⟨"2-Carb-21.2/212D", "L-ascorbic acid equilibrium mixture: xylo-ulosono, threo-enono, lyxo-ulosono lactones"⟩
  | .glucuronicAcid => ⟨"2-Carb-22.2/222A", "D-Glucuronic acid"⟩
  | .mannopyranuronicAcid => ⟨"2-Carb-22.2/222B", "alpha-D-Mannopyranuronic acid"⟩
  | .phenylGlucopyranosiduronic => ⟨"2-Carb-22.2/222C", "Phenyl beta-D-glucopyranosiduronic acid; glucuronoside/glucuronide rejected"⟩
  | .methylIdopyranosiduronic => ⟨"2-Carb-22.2/222D", "Methyl alpha-L-idopyranosiduronic acid"⟩
  | .glucopyranosyluronateBromide => ⟨"2-Carb-22.2/222E", "Methyl 2,3,4-tri-O-acetyl-alpha-D-glucopyranosyluronate bromide"⟩
  | .glucofuranosidurononitrile => ⟨"2-Carb-22.2/222F", "Methyl alpha-L-glucofuranosidurononitrile"⟩
  | .sodiumGlucofuranosiduronate => ⟨"2-Carb-22.2/222G", "Sodium (methyl alpha-L-glucofuranosid)uronate"⟩
  | .ethylMannofuranuronate => ⟨"2-Carb-22.2/222H", "Ethyl 2,3,5-tri-O-benzoyl-alpha-D-mannofuranuronate"⟩
  | .glucuronoLactone => ⟨"2-Carb-22.2/222I", "D-Glucurono-6,3-lactone"⟩
  | .glucofuranuronoLactone => ⟨"2-Carb-22.2/222J", "D-Glucofuranurono-6,3-lactone"⟩
  | .methylGlucofuranosiduronoLactone => ⟨"2-Carb-22.2/222K", "Methyl alpha-D-glucofuranosidurono-6,3-lactone"⟩
  | .deoxyEnopyranuronicAcid => ⟨"2-Carb-22.2/222L", "4-Deoxy-L-threo-hex-4-enopyranuronic acid"⟩
  | .methylDeoxyEnopyranuronate => ⟨"2-Carb-22.2/222M", "Methyl 4-deoxy-L-threo-hex-4-enopyranuronate"⟩
  | .methylDeoxyEnopyranosiduronic => ⟨"2-Carb-22.2/222N", "Methyl 4-deoxy-alpha-L-threo-hex-4-enopyranosiduronic acid"⟩
  | .methylPhenylEnopyranosiduronate => ⟨"2-Carb-22.2/222O", "Methyl (phenyl 4-deoxy-beta-L-threo-hex-4-enopyranosid)uronate"⟩
  | .galactopyranosiduronamide => ⟨"2-Carb-22.2/222P", "Methyl beta-D-galactopyranosiduronamide"⟩
  | .altraricAcid => ⟨"2-Carb-23.1/231A", "L-Altraric acid; not L-talaric acid"⟩
  | .glucaricAcid => ⟨"2-Carb-23.1/231B", "D-Glucaric acid; not L-gularic acid"⟩
  | .heptaricAcid => ⟨"2-Carb-23.1/231C", "L-glycero-D-galacto-Heptaric acid; alternative rejected"⟩
  | .mesoXylaricAcid => ⟨"2-Carb-23.2/232A", "meso-Xylaric acid"⟩
  | .mesoGalactaricAcid => ⟨"2-Carb-23.2/232B", "meso-Galactaric acid"⟩
  | .methylDGalactaricAcid => ⟨"2-Carb-23.2/232C", "4-O-Methyl-D-galactaric acid; L alternative rejected"⟩
  | .positiveTartaricAcid => ⟨"2-Carb-23.3/233A", "(2R,3R)- or (+)-Tartaric acid; or L-threaric acid"⟩
  | .negativeTartaricAcid => ⟨"2-Carb-23.3/233B", "(2S,3S)- or (-)-Tartaric acid; or D-threaric acid"⟩
  | .mesoTartaricAcid => ⟨"2-Carb-23.3/233C", "(2R,3S)- or meso-Tartaric acid; or erythraric acid"⟩
  | .oneMethylHydrogenGalactarate => ⟨"2-Carb-23.4/234A", "1-Methyl hydrogen D-galactarate"⟩
  | .sixMethylHydrogenGalactarate => ⟨"2-Carb-23.4/234B", "6-Methyl hydrogen D-galactarate"⟩
  | .glucarOneAmicAcid => ⟨"2-Carb-23.4/234C", "D-Glucar-1-amic acid"⟩
  | .methylGlucarSixAmate => ⟨"2-Carb-23.4/234D", "Methyl D-glucar-6-amate"⟩
  | .mannaroDilactone => ⟨"2-Carb-23.4/234E", "D-Mannaro-1,4:6,3-dilactone"⟩

theorem printed_example_keys_are_pairwise_distinct :
    (PrintedExample.all.map fun exampleRow => exampleRow.data.sourceKey).Nodup := by
  decide

inductive Provision where
  | alditolOseToItol
  | alditolParentChoiceUsesTwoCarbTwo
  | fucitolAndRhamnitolAllowed
  | symmetricAlditolIsOpticallyInactiveMeso
  | mesoPrefixOptionalForSymmetricAlditol
  | substitutedMesoAlditolRequiresDL
  | longMesoAlditolPrefixesRequireDL
  | aldonicClassByCarbonCount
  | aldonicOseToOnicAcid
  | aldonicSaltUsesOnate
  | knownCounterionPrecedesAldonate
  | aldonicEsterUsesOnateAndGroupPrefix
  | aldonicPeriphraseMayIndex
  | aldonicAmideAndNitrileEndings
  | aldonicLactoneUsesOnolactone
  | lactoneLocantsCarbonylThenOxygen
  | lactonePeriphrasesNotRecommended
  | lactamNamedAnalogously
  | aldonicAcylHalideUsesOnoyl
  | complicatedAcidDerivativesUseGeneralRules
  | ketoaldonicUloseToUlosonicWithLocant
  | ketoaldonicAnionUsesUlosonate
  | ketoaldonicNumberingStartsAtCarboxy
  | ketoaldonicGlycosideUsesUlosidonicRingInfix
  | kdoSymbolAndDeprecatedExpansion
  | kdnSymbolUsage
  | ketoaldonicDerivativesFollowAldonicRules
  | esterVsGlycosidicAlkylParentheses
  | ascorbicAcidIsThreeIsomerEquilibrium
  | uronicThreeStemTransformations
  | uronicAldehydicCarbonNumberedOne
  | uronicDerivativesFollowAldonicRules
  | uronicAnionUsesUronate
  | uronicEsterUsesUronate
  | aldaricOseToAricAcid
  | aldaricParentChoiceUsesTwoCarbTwo
  | symmetricAldaricHasNoDL
  | symmetricAldaricMayUseMeso
  | substitutedMesoAldaricRequiresDL
  | tartaricTrivialNameRetained
  | tartaricStereochemistryUsesRS
  | tartaricEstersAreTartrates
  | historicalTartaricDLConfusionRequiresRS
  | aldaricDerivativesFollowAldonicRules
  | complexAldaricDerivativesUseGeneralRules
  | ambiguousAldaricDerivativeRequiresLocants
  | mesoAldaricName (name : MesoAldaricName)
  | printedExample (exampleRow : PrintedExample)
  deriving DecidableEq, Repr

namespace Provision

def base : List Provision :=
  [ .alditolOseToItol, .alditolParentChoiceUsesTwoCarbTwo, .fucitolAndRhamnitolAllowed
  , .symmetricAlditolIsOpticallyInactiveMeso, .mesoPrefixOptionalForSymmetricAlditol
  , .substitutedMesoAlditolRequiresDL, .longMesoAlditolPrefixesRequireDL
  , .aldonicClassByCarbonCount, .aldonicOseToOnicAcid, .aldonicSaltUsesOnate
  , .knownCounterionPrecedesAldonate, .aldonicEsterUsesOnateAndGroupPrefix
  , .aldonicPeriphraseMayIndex, .aldonicAmideAndNitrileEndings
  , .aldonicLactoneUsesOnolactone, .lactoneLocantsCarbonylThenOxygen
  , .lactonePeriphrasesNotRecommended, .lactamNamedAnalogously
  , .aldonicAcylHalideUsesOnoyl, .complicatedAcidDerivativesUseGeneralRules
  , .ketoaldonicUloseToUlosonicWithLocant, .ketoaldonicAnionUsesUlosonate
  , .ketoaldonicNumberingStartsAtCarboxy, .ketoaldonicGlycosideUsesUlosidonicRingInfix
  , .kdoSymbolAndDeprecatedExpansion, .kdnSymbolUsage
  , .ketoaldonicDerivativesFollowAldonicRules, .esterVsGlycosidicAlkylParentheses
  , .ascorbicAcidIsThreeIsomerEquilibrium, .uronicThreeStemTransformations
  , .uronicAldehydicCarbonNumberedOne, .uronicDerivativesFollowAldonicRules
  , .uronicAnionUsesUronate, .uronicEsterUsesUronate, .aldaricOseToAricAcid
  , .aldaricParentChoiceUsesTwoCarbTwo, .symmetricAldaricHasNoDL
  , .symmetricAldaricMayUseMeso, .substitutedMesoAldaricRequiresDL
  , .tartaricTrivialNameRetained, .tartaricStereochemistryUsesRS
  , .tartaricEstersAreTartrates, .historicalTartaricDLConfusionRequiresRS
  , .aldaricDerivativesFollowAldonicRules, .complexAldaricDerivativesUseGeneralRules
  , .ambiguousAldaricDerivativeRequiresLocants
  ]

def all : List Provision :=
  (base ++ MesoAldaricName.all.map Provision.mesoAldaricName) ++
    PrintedExample.all.map Provision.printedExample

@[simp] theorem mem_all (provision : Provision) : provision ∈ all := by
  cases provision with
  | mesoAldaricName name =>
      simp only [all, List.mem_append]
      exact Or.inl (Or.inr (List.mem_map_of_mem (f := Provision.mesoAldaricName) name.mem_all))
  | printedExample exampleRow =>
      simp only [all, List.mem_append]
      exact Or.inr (List.mem_map_of_mem (f := Provision.printedExample) exampleRow.mem_all)
  | _ => simp [all, base]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 114 := by decide

end Provision

def Provision.sourceKey : Provision → String
  | .alditolOseToItol | .alditolParentChoiceUsesTwoCarbTwo
  | .fucitolAndRhamnitolAllowed => "2-Carb-19.1"
  | .symmetricAlditolIsOpticallyInactiveMeso | .mesoPrefixOptionalForSymmetricAlditol
  | .substitutedMesoAlditolRequiresDL | .longMesoAlditolPrefixesRequireDL => "2-Carb-19.2"
  | .aldonicClassByCarbonCount | .aldonicOseToOnicAcid => "2-Carb-20.1"
  | .aldonicSaltUsesOnate | .knownCounterionPrecedesAldonate
  | .aldonicEsterUsesOnateAndGroupPrefix | .aldonicPeriphraseMayIndex
  | .aldonicAmideAndNitrileEndings | .aldonicLactoneUsesOnolactone
  | .lactoneLocantsCarbonylThenOxygen | .lactonePeriphrasesNotRecommended
  | .lactamNamedAnalogously | .aldonicAcylHalideUsesOnoyl
  | .complicatedAcidDerivativesUseGeneralRules => "2-Carb-20.2"
  | .ketoaldonicUloseToUlosonicWithLocant | .ketoaldonicAnionUsesUlosonate
  | .ketoaldonicNumberingStartsAtCarboxy | .ketoaldonicGlycosideUsesUlosidonicRingInfix
  | .kdoSymbolAndDeprecatedExpansion | .kdnSymbolUsage => "2-Carb-21.1"
  | .ketoaldonicDerivativesFollowAldonicRules | .esterVsGlycosidicAlkylParentheses
  | .ascorbicAcidIsThreeIsomerEquilibrium => "2-Carb-21.2"
  | .uronicThreeStemTransformations | .uronicAldehydicCarbonNumberedOne => "2-Carb-22.1"
  | .uronicDerivativesFollowAldonicRules | .uronicAnionUsesUronate
  | .uronicEsterUsesUronate => "2-Carb-22.2"
  | .aldaricOseToAricAcid | .aldaricParentChoiceUsesTwoCarbTwo => "2-Carb-23.1"
  | .symmetricAldaricHasNoDL | .symmetricAldaricMayUseMeso
  | .substitutedMesoAldaricRequiresDL | .mesoAldaricName _ => "2-Carb-23.2"
  | .tartaricTrivialNameRetained | .tartaricStereochemistryUsesRS
  | .tartaricEstersAreTartrates | .historicalTartaricDLConfusionRequiresRS => "2-Carb-23.3"
  | .aldaricDerivativesFollowAldonicRules | .complexAldaricDerivativesUseGeneralRules
  | .ambiguousAldaricDerivativeRequiresLocants => "2-Carb-23.4"
  | .printedExample exampleRow => exampleRow.data.sourceKey

/-! ## Executable symmetry and configuration semantics -/

inductive SymmetryState where
  | asymmetric
  | symmetricUnsubstituted
  | symmetricParentMadeAsymmetric
  deriving DecidableEq, Repr

inductive SeriesRequirement where
  | prohibited
  | optional
  | required
  deriving DecidableEq, Repr

def alditolSeriesRequirement : SymmetryState → SeriesRequirement
  | .asymmetric => .required
  | .symmetricUnsubstituted => .optional
  | .symmetricParentMadeAsymmetric => .required

@[simp] theorem substitution_restores_series_requirement_to_meso_parent :
    alditolSeriesRequirement .symmetricUnsubstituted = .optional ∧
      alditolSeriesRequirement .symmetricParentMadeAsymmetric = .required := by
  decide

def lactoneLocants (carbonyl oxygen : Nat) : List Nat := [carbonyl, oxygen]

@[simp] theorem lactone_locants_are_functional_not_numerically_sorted :
    lactoneLocants 6 3 = [6, 3] := by rfl

inductive UronicNumberingOrigin where
  | potentialAldehyde
  | carboxy
  deriving DecidableEq, Repr

def authoritativeUronicNumberingOrigin : UronicNumberingOrigin := .potentialAldehyde

@[simp] theorem uronic_numbering_is_the_carbohydrate_exception :
    authoritativeUronicNumberingOrigin = .potentialAldehyde ∧
      authoritativeUronicNumberingOrigin ≠ .carboxy := by
  decide

inductive AbsoluteCenterDescriptor where
  | R
  | S
  deriving DecidableEq, Repr

inductive TartaricClass where
  | positive
  | negative
  | meso
  deriving DecidableEq, Repr

def tartaricClass : AbsoluteCenterDescriptor × AbsoluteCenterDescriptor → TartaricClass
  | (.R, .R) => .positive
  | (.S, .S) => .negative
  | _ => .meso

@[simp] theorem tartaric_RS_mapping_is_exact :
    tartaricClass (.R, .R) = .positive ∧ tartaricClass (.S, .S) = .negative ∧
      tartaricClass (.R, .S) = .meso ∧ tartaricClass (.S, .R) = .meso := by
  decide

def ascorbicEquilibriumNames : List String :=
  [ "L-xylo-Hex-2-ulosono-1,4-lactone"
  , "L-threo-Hex-2-enono-1,4-lactone"
  , "L-lyxo-Hex-2-ulosono-1,4-lactone"
  ]

@[simp] theorem ascorbic_equilibrium_has_exactly_three_distinct_isomers :
    ascorbicEquilibriumNames.length = 3 ∧ ascorbicEquilibriumNames.Nodup := by
  decide

end Carbohydrate1996AlditolsAcids

end TetraStereo.OneCenter
