import TetraStereo.OneCenter.CarbohydrateNamedParentStereochemistrySemantics

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent carbohydrate derivative stereochemistry semantics

This module audits 2-Carb-13 through 2-Carb-16 of *Nomenclature of Carbohydrates
(Recommendations 1996)*: deoxy sugars, amino sugars, chalcogen analogues, other substitution,
and isotopic substitution/labelling.  Retained-name inventories and every printed example are
enumerated independently of the production parser.  Structure drawings still require a separate
reviewed graph transcription before these provisions can be promoted beyond partial semantics.
-/

namespace Carbohydrate1996Derivatives

inductive DeoxyTrivialNameRow where
  | fucose
  | quinovose
  | rhamnose
  | digitoxose
  | abequose
  | tyvelose
  | ascarylose
  | colitose
  | paratose
  deriving DecidableEq, Repr

namespace DeoxyTrivialNameRow

def all : List DeoxyTrivialNameRow :=
  [ .fucose, .quinovose, .rhamnose, .digitoxose, .abequose
  , .tyvelose, .ascarylose, .colitose, .paratose
  ]

@[simp] theorem mem_all (row : DeoxyTrivialNameRow) : row ∈ all := by
  cases row <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 9 := by decide

end DeoxyTrivialNameRow

structure DeoxyTrivialNameData where
  trivialName : String
  abbreviation : Option String
  systematicParent : String
  deriving DecidableEq, Repr

def DeoxyTrivialNameRow.data : DeoxyTrivialNameRow → DeoxyTrivialNameData
  | .fucose => ⟨"fucose", some "Fuc", "6-deoxy-L-galactose"⟩
  | .quinovose => ⟨"quinovose", some "Qui", "6-deoxy-D-glucose"⟩
  | .rhamnose => ⟨"rhamnose", some "Rha", "6-deoxy-L-mannose"⟩
  | .digitoxose => ⟨"digitoxose", none, "2,6-dideoxy-D-ribo-hexose"⟩
  | .abequose => ⟨"abequose", none, "3,6-dideoxy-D-xylo-hexose"⟩
  | .tyvelose => ⟨"tyvelose", none, "3,6-dideoxy-D-arabino-hexose"⟩
  | .ascarylose => ⟨"ascarylose", none, "3,6-dideoxy-L-arabino-hexose"⟩
  | .colitose => ⟨"colitose", none, "3,6-dideoxy-L-xylo-hexose"⟩
  | .paratose => ⟨"paratose", none, "3,6-dideoxy-D-ribo-hexose"⟩

theorem deoxy_trivial_names_are_pairwise_distinct :
    (DeoxyTrivialNameRow.all.map fun row => row.data.trivialName).Nodup := by
  decide

inductive AminoTrivialNameRow where
  | galactosamine
  | glucosamine
  | mannosamine
  | fucosamine
  | quinovosamine
  | neuraminicAcid
  | muramicAcid
  deriving DecidableEq, Repr

namespace AminoTrivialNameRow

def all : List AminoTrivialNameRow :=
  [ .galactosamine, .glucosamine, .mannosamine, .fucosamine
  , .quinovosamine, .neuraminicAcid, .muramicAcid
  ]

@[simp] theorem mem_all (row : AminoTrivialNameRow) : row ∈ all := by
  cases row <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 7 := by decide

end AminoTrivialNameRow

structure AminoTrivialNameData where
  trivialName : String
  systematicName : String
  specificallyD : Bool
  deriving DecidableEq, Repr

def AminoTrivialNameRow.data : AminoTrivialNameRow → AminoTrivialNameData
  | .galactosamine => ⟨"D-Galactosamine", "2-amino-2-deoxy-D-galactose", false⟩
  | .glucosamine => ⟨"D-Glucosamine", "2-amino-2-deoxy-D-glucose", false⟩
  | .mannosamine => ⟨"D-Mannosamine", "2-amino-2-deoxy-D-mannose", false⟩
  | .fucosamine => ⟨"D-Fucosamine", "2-amino-2,6-dideoxy-D-galactose", false⟩
  | .quinovosamine => ⟨"D-Quinovosamine", "2-amino-2,6-dideoxy-D-glucose", false⟩
  | .neuraminicAcid =>
      ⟨"Neuraminic acid", "5-amino-3,5-dideoxy-D-glycero-D-galacto-non-2-ulosonic acid", true⟩
  | .muramicAcid =>
      ⟨"Muramic acid", "2-amino-3-O-[(R)-1-carboxyethyl]-2-deoxy-D-glucose", true⟩

@[simp] theorem exactly_neuraminic_and_muramic_names_are_intrinsically_D
    (row : AminoTrivialNameRow) :
    row.data.specificallyD = true ↔ row = .neuraminicAcid ∨ row = .muramicAcid := by
  cases row <;> decide

inductive PrintedExample where
  | fucopyranose
  | quinovopyranose
  | rhamnopyranose
  | digitoxopyranose
  | abequopyranose
  | tyvelopyranose
  | deoxyribosePhosphate
  | deoxyXylo
  | deoxyRibo
  | deoxyAlloHepto
  | deoxyAltroOctulose
  | multiplySubstitutedDeoxy
  | dividedCentersRibo
  | dividedCentersArabino
  | dividedCentersGluco
  | oneDeoxyArabinitol
  | fiveDeoxyArabinitol
  | glucosamine
  | neuraminicAcid
  | muramicAcid
  | methylaminoGlucose
  | formamidoMannose
  | acetamidoGalactose
  | thioGlucoseOne
  | thioGlucoseRing
  | thioGlucoside
  | selenoXylofuranoside
  | thioGalactose
  | phenylSelenoxide
  | selenoFructofuranoside
  | dithioHeptopyranoside
  | cPhenylGlucose
  | cAcetamidoMannosylFluoride
  | bromoXyloUronicAcid
  | deoxyPhenylGlucose
  | diazidoMannosylNitrate
  | bromoChloroDeoxy
  | terminalCyclohexylPhenyl
  | aldehydicPhenylGlucose
  | aldehydicPhenylGlucopyranose
  | methyliminoXylitol
  | glucosePhenylhydrazone
  | ketoaldoseBisPhenylhydrazone
  | phenylOsotriazole
  | carbon13Glucose
  | deuteriumMannose
  | uniformCarbon14Arabinose
  | tritiumGalactose
  | deuteriumCreatesCenter
  | fluorine18CreatesCenter
  deriving DecidableEq, Repr

namespace PrintedExample

def all : List PrintedExample :=
  [ .fucopyranose, .quinovopyranose, .rhamnopyranose, .digitoxopyranose
  , .abequopyranose, .tyvelopyranose, .deoxyribosePhosphate, .deoxyXylo
  , .deoxyRibo, .deoxyAlloHepto, .deoxyAltroOctulose, .multiplySubstitutedDeoxy
  , .dividedCentersRibo, .dividedCentersArabino, .dividedCentersGluco
  , .oneDeoxyArabinitol, .fiveDeoxyArabinitol, .glucosamine, .neuraminicAcid
  , .muramicAcid, .methylaminoGlucose, .formamidoMannose, .acetamidoGalactose
  , .thioGlucoseOne, .thioGlucoseRing, .thioGlucoside, .selenoXylofuranoside
  , .thioGalactose, .phenylSelenoxide, .selenoFructofuranoside
  , .dithioHeptopyranoside, .cPhenylGlucose, .cAcetamidoMannosylFluoride
  , .bromoXyloUronicAcid, .deoxyPhenylGlucose, .diazidoMannosylNitrate
  , .bromoChloroDeoxy, .terminalCyclohexylPhenyl, .aldehydicPhenylGlucose
  , .aldehydicPhenylGlucopyranose, .methyliminoXylitol, .glucosePhenylhydrazone
  , .ketoaldoseBisPhenylhydrazone, .phenylOsotriazole, .carbon13Glucose
  , .deuteriumMannose, .uniformCarbon14Arabinose, .tritiumGalactose
  , .deuteriumCreatesCenter, .fluorine18CreatesCenter
  ]

@[simp] theorem mem_all (exampleRow : PrintedExample) : exampleRow ∈ all := by
  cases exampleRow <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 50 := by decide

end PrintedExample

structure PrintedExampleData where
  sourceKey : String
  printedName : String
  deriving DecidableEq, Repr

def PrintedExample.data : PrintedExample → PrintedExampleData
  | .fucopyranose => ⟨"2-Carb-13.1/131A", "alpha-L-Fucopyranose; 6-deoxy-alpha-L-galactopyranose"⟩
  | .quinovopyranose => ⟨"2-Carb-13.1/131B", "beta-D-Quinovopyranose; 6-deoxy-beta-D-glucopyranose"⟩
  | .rhamnopyranose => ⟨"2-Carb-13.1/131C", "L-Rhamnopyranose; 6-deoxy-L-mannopyranose"⟩
  | .digitoxopyranose => ⟨"2-Carb-13.1/131D", "2,6-Dideoxy-beta-D-ribo-hexopyranose (beta-Digitoxopyranose)"⟩
  | .abequopyranose => ⟨"2-Carb-13.1/131E", "3,6-Dideoxy-beta-D-xylo-hexopyranose (beta-Abequopyranose)"⟩
  | .tyvelopyranose => ⟨"2-Carb-13.1/131F", "3,6-Dideoxy-beta-D-arabino-hexopyranose (beta-Tyvelopyranose)"⟩
  | .deoxyribosePhosphate => ⟨"2-Carb-13.2/132", "2-Deoxy-D-erythro-pentofuranose 5-phosphate"⟩
  | .deoxyXylo => ⟨"2-Carb-13.3/133A", "4-Deoxy-beta-D-xylo-hexopyranose; not 4-deoxy-beta-D-galactopyranose"⟩
  | .deoxyRibo => ⟨"2-Carb-13.3/133B", "2-Deoxy-D-ribo-hexose; not 2-deoxy-D-allose"⟩
  | .deoxyAlloHepto => ⟨"2-Carb-13.3/133C", "2-Deoxy-alpha-D-allo-heptopyranose"⟩
  | .deoxyAltroOctulose => ⟨"2-Carb-13.3/133D", "1-Deoxy-L-glycero-D-altro-oct-2-ulose"⟩
  | .multiplySubstitutedDeoxy =>
      ⟨"2-Carb-13.3/133E", "Methyl 3-azido-4-O-benzoyl-6-bromo-2,3,6-trideoxy-2-fluoro-alpha-D-allopyranoside"⟩
  | .dividedCentersRibo => ⟨"2-Carb-13.3/133F", "3-Deoxy-D-ribo-hexose; not split-prefix name"⟩
  | .dividedCentersArabino => ⟨"2-Carb-13.3/133G", "5-Deoxy-D-arabino-hept-3-ulose; not split-prefix name"⟩
  | .dividedCentersGluco => ⟨"2-Carb-13.3/133H", "6-Deoxy-L-gluco-oct-2-ulose; not split-prefix name"⟩
  | .oneDeoxyArabinitol => ⟨"2-Carb-13.4/134A", "1-Deoxy-D-arabinitol; not 5-deoxy-D-lyxitol"⟩
  | .fiveDeoxyArabinitol => ⟨"2-Carb-13.4/134B", "5-Deoxy-D-arabinitol; not 1-deoxy-D-lyxitol"⟩
  | .glucosamine => ⟨"2-Carb-14.2/142A", "2-Amino-2-deoxy-D-glucopyranose (D-glucosamine)"⟩
  | .neuraminicAcid =>
      ⟨"2-Carb-14.2/142B", "5-Acetamido-3,5-dideoxy-D-glycero-alpha-D-galacto-non-2-ulopyranosonic acid (alpha-Neu5Ac)"⟩
  | .muramicAcid => ⟨"2-Carb-14.2/142C", "2-Amino-3-O-[(R)-1-carboxyethyl]-2-deoxy-beta-D-glucopyranose"⟩
  | .methylaminoGlucose => ⟨"2-Carb-14.3/143A", "2-Deoxy-2-methylamino-L-glucopyranose"⟩
  | .formamidoMannose => ⟨"2-Carb-14.3/143B", "4,6-Dideoxy-4-formamido-2,3-di-O-methyl-D-mannopyranose"⟩
  | .acetamidoGalactose => ⟨"2-Carb-14.3/143C", "2-Acetamido-1,3,4-tri-O-acetyl-2,6-dideoxy-alpha-L-galactopyranose"⟩
  | .thioGlucoseOne => ⟨"2-Carb-15/15A", "2,3,4,6-Tetra-O-acetyl-1-thio-beta-D-glucopyranose"⟩
  | .thioGlucoseRing => ⟨"2-Carb-15/15B", "5-Thio-beta-D-glucopyranose"⟩
  | .thioGlucoside => ⟨"2-Carb-15/15C", "Methyl 2,3,4-tri-O-acetyl-1-thio-6-O-trityl-alpha-D-glucopyranoside"⟩
  | .selenoXylofuranoside => ⟨"2-Carb-15/15D", "Methyl 4-seleno-alpha-D-xylofuranoside"⟩
  | .thioGalactose => ⟨"2-Carb-15/15E", "4-Thio-beta-D-galactopyranose"⟩
  | .phenylSelenoxide => ⟨"2-Carb-15/15F", "alpha-D-Glucopyranosyl phenyl (R)-selenoxide"⟩
  | .selenoFructofuranoside => ⟨"2-Carb-15/15G", "Methyl 5-seleno-alpha-D-fructofuranoside"⟩
  | .dithioHeptopyranoside => ⟨"2-Carb-15/15H", "Ethyl 3,4,6,7-tetra-O-acetyl-2-deoxy-1,5-dithio-alpha-D-gluco-heptopyranoside"⟩
  | .cPhenylGlucose => ⟨"2-Carb-16.1/161A", "2-C-Phenyl-alpha-D-glucopyranose"⟩
  | .cAcetamidoMannosylFluoride => ⟨"2-Carb-16.1/161B", "2-C-Acetamido-2,3,4,6-tetra-O-acetyl-alpha-D-mannopyranosyl fluoride"⟩
  | .bromoXyloUronicAcid => ⟨"2-Carb-16.1/161C", "(5R)-5-bromo-alpha-D-xylo-hexopyranuronic acid; or beta-L-ido name"⟩
  | .deoxyPhenylGlucose => ⟨"2-Carb-16.2/162A", "2-Deoxy-2-phenyl-alpha-D-glucopyranose; C- and (2R)-alternatives"⟩
  | .diazidoMannosylNitrate => ⟨"2-Carb-16.2/162B", "2,3-Diazido-4-O-benzoyl-6-bromo-2,3,6-trideoxy-alpha-D-mannopyranosyl nitrate"⟩
  | .bromoChloroDeoxy => ⟨"2-Carb-16.3/163", "(2R)-2-Bromo-2-chloro-2-deoxy-alpha-D-arabino-hexopyranose; Br over Cl"⟩
  | .terminalCyclohexylPhenyl => ⟨"2-Carb-16.4/164A", "(5R)-5-C-Cyclohexyl-5-C-phenyl-D-xylose"⟩
  | .aldehydicPhenylGlucose => ⟨"2-Carb-16.4/164B", "1-C-Phenyl-D-glucose; not hex-1-ulose"⟩
  | .aldehydicPhenylGlucopyranose => ⟨"2-Carb-16.4/164C", "1-C-Phenyl-beta-D-glucopyranose"⟩
  | .methyliminoXylitol => ⟨"2-Carb-16.5/165A", "1-Deoxy-1-(methylimino)-D-xylitol"⟩
  | .glucosePhenylhydrazone => ⟨"2-Carb-16.5/165B", "D-Glucose phenylhydrazone"⟩
  | .ketoaldoseBisPhenylhydrazone => ⟨"2-Carb-16.5/165C", "D-arabino-Hexos-2-ulose bis(phenylhydrazone); phenylosazone alternative"⟩
  | .phenylOsotriazole => ⟨"2-Carb-16.5/165D", "D-arabino-Hexos-2-ulose phenylosotriazole; two systematic alternatives"⟩
  | .carbon13Glucose => ⟨"2-Carb-16.6/unnumbered-1", "D-(1-13C)Glucose (substitution)"⟩
  | .deuteriumMannose => ⟨"2-Carb-16.6/unnumbered-2", "D-(2-2H)Mannose (substitution)"⟩
  | .uniformCarbon14Arabinose => ⟨"2-Carb-16.6/unnumbered-3", "L-[U-14C]Arabinose (labelling)"⟩
  | .tritiumGalactose => ⟨"2-Carb-16.6/unnumbered-4", "D-[1-3H]Galactose (labelling)"⟩
  | .deuteriumCreatesCenter => ⟨"2-Carb-16.6/166A", "2-Deoxy-D-(2-2H)lyxose; or (2S)-D-threo name"⟩
  | .fluorine18CreatesCenter => ⟨"2-Carb-16.6/166B", "2-Deoxy-2-[18F]fluoro-D-glucopyranose; or (2R)-D-arabino name"⟩

theorem printed_example_keys_are_pairwise_distinct :
    (PrintedExample.all.map fun exampleRow => exampleRow.data.sourceKey).Nodup := by
  decide

inductive Provision where
  | establishedDeoxyTrivialNames
  | deoxyTrivialNamesRetainedForUnmodifiedSugars
  | systematicDeoxyNamesPreferredForDerivatives
  | otherUsedDeoxyTrivialNames
  | terminalMethylIsOmegaDeoxyNotCMethyl
  | deoxyWithTrivialNameWhenNoCenterRemoved
  | deoxyRemovalOfCenterCreatesRedundancy
  | systematicPreferredWhenCenterRemoved
  | commonTwoDeoxyNames
  | systematicDeoxyLocantPrefixStem
  | deoxyPrefixesDescribePresentCenters
  | configurationalPrefixesCitedFarthestFromC1
  | deoxyIsDetachableAlphabetizedPrefix
  | detachablePracticeConflictsGeneralGuide
  | methyleneInterruptionIgnored
  | prefixCoversEntireRemainingCenterSequence
  | anomericHydroxyToHydrogenRoutesToAnhydroAlditol
  | terminalAldehydeToMethylUsesDeoxyAlditol
  | fucitolAndRhamnitolFrequent
  | aminoReplacementIsSubstitutionOnDeoxySugar
  | aminoEquivalentToHydroxyForConfiguration
  | nSubstitutedTreatmentRoutesToTwoCarbTwentyFive
  | acceptedAminoTrivialNames
  | neuraminicAndMuramicNamesSpecificallyD
  | nonexistentParentAminoNamesNotRecommended
  | ringNitrogenRoutesToTwoCarbThirtyFour
  | systematicAminoUsesDeoxyAndAminoPrefixes
  | aminoDeoxyAlphabetization
  | anomericAminoNormallyGlycosylamine
  | hydroxyOrCarbonylOxygenToSulfurUsesThio
  | ringOxygenToSulfurUsesAdjacentNonanomericLocant
  | seleniumAndTelluriumUseSelenoTelluro
  | chalcogenOxidesMayUseFunctionalClassNames
  | thioNotThia
  | thioCommonlyTreatedAsDetachable
  | nonterminalHydrogenReplacementIsCSubstitution
  | highestCIPPriorityGroupEquivalentToHydroxy
  | ambiguousModifiedCenterUsesRS
  | nonanomericHydroxyReplacementUsesDeoxyParent
  | replacingGroupDeterminesConfiguration
  | hydroxyReplacementAmbiguityUsesRS
  | cLocantRequiredOnlyForAmbiguityButMayEmphasize
  | unequalSubstitutionUsesDisubstitutedDeoxyParent
  | unequalHigherCIPGroupEquivalentToHydroxy
  | unequalSubstitutionAmbiguityUsesRS
  | terminalCreatedCenterUsesRS
  | terminalMethylStillDeoxyNotCMethyl
  | aldehydicHydrogenRingReplacementUsesCPrefix
  | iminoAnalogueMayUseIminoDeoxyAlditol
  | oximesAndHydrazonesNamedDirectly
  | arylosazonePrefersKetoaldoseBisHydrazone
  | oxidizedArylosazoneMayUseTriazolylAlditol
  | isotopeRulesDelegatedToSectionH
  | isotopeParenthesesVsLabellingBrackets
  | uniformLabellingUsesU
  | isotopeCreatedCenterFollowsSubstitutionRules
  | deoxyTrivialName (row : DeoxyTrivialNameRow)
  | aminoTrivialName (row : AminoTrivialNameRow)
  | printedExample (exampleRow : PrintedExample)
  deriving DecidableEq, Repr

namespace Provision

def base : List Provision :=
  [ .establishedDeoxyTrivialNames, .deoxyTrivialNamesRetainedForUnmodifiedSugars
  , .systematicDeoxyNamesPreferredForDerivatives, .otherUsedDeoxyTrivialNames
  , .terminalMethylIsOmegaDeoxyNotCMethyl, .deoxyWithTrivialNameWhenNoCenterRemoved
  , .deoxyRemovalOfCenterCreatesRedundancy, .systematicPreferredWhenCenterRemoved
  , .commonTwoDeoxyNames, .systematicDeoxyLocantPrefixStem
  , .deoxyPrefixesDescribePresentCenters, .configurationalPrefixesCitedFarthestFromC1
  , .deoxyIsDetachableAlphabetizedPrefix, .detachablePracticeConflictsGeneralGuide
  , .methyleneInterruptionIgnored, .prefixCoversEntireRemainingCenterSequence
  , .anomericHydroxyToHydrogenRoutesToAnhydroAlditol
  , .terminalAldehydeToMethylUsesDeoxyAlditol, .fucitolAndRhamnitolFrequent
  , .aminoReplacementIsSubstitutionOnDeoxySugar, .aminoEquivalentToHydroxyForConfiguration
  , .nSubstitutedTreatmentRoutesToTwoCarbTwentyFive, .acceptedAminoTrivialNames
  , .neuraminicAndMuramicNamesSpecificallyD, .nonexistentParentAminoNamesNotRecommended
  , .ringNitrogenRoutesToTwoCarbThirtyFour, .systematicAminoUsesDeoxyAndAminoPrefixes
  , .aminoDeoxyAlphabetization, .anomericAminoNormallyGlycosylamine
  , .hydroxyOrCarbonylOxygenToSulfurUsesThio
  , .ringOxygenToSulfurUsesAdjacentNonanomericLocant
  , .seleniumAndTelluriumUseSelenoTelluro, .chalcogenOxidesMayUseFunctionalClassNames
  , .thioNotThia, .thioCommonlyTreatedAsDetachable
  , .nonterminalHydrogenReplacementIsCSubstitution
  , .highestCIPPriorityGroupEquivalentToHydroxy, .ambiguousModifiedCenterUsesRS
  , .nonanomericHydroxyReplacementUsesDeoxyParent, .replacingGroupDeterminesConfiguration
  , .hydroxyReplacementAmbiguityUsesRS, .cLocantRequiredOnlyForAmbiguityButMayEmphasize
  , .unequalSubstitutionUsesDisubstitutedDeoxyParent
  , .unequalHigherCIPGroupEquivalentToHydroxy, .unequalSubstitutionAmbiguityUsesRS
  , .terminalCreatedCenterUsesRS, .terminalMethylStillDeoxyNotCMethyl
  , .aldehydicHydrogenRingReplacementUsesCPrefix, .iminoAnalogueMayUseIminoDeoxyAlditol
  , .oximesAndHydrazonesNamedDirectly, .arylosazonePrefersKetoaldoseBisHydrazone
  , .oxidizedArylosazoneMayUseTriazolylAlditol, .isotopeRulesDelegatedToSectionH
  , .isotopeParenthesesVsLabellingBrackets, .uniformLabellingUsesU
  , .isotopeCreatedCenterFollowsSubstitutionRules
  ]

def all : List Provision :=
  (((base ++ DeoxyTrivialNameRow.all.map Provision.deoxyTrivialName) ++
      AminoTrivialNameRow.all.map Provision.aminoTrivialName) ++
    PrintedExample.all.map Provision.printedExample)

@[simp] theorem mem_all (provision : Provision) : provision ∈ all := by
  cases provision with
  | deoxyTrivialName row =>
      simp only [all, List.mem_append]
      exact Or.inl (Or.inl (Or.inr
        (List.mem_map_of_mem (f := Provision.deoxyTrivialName) row.mem_all)))
  | aminoTrivialName row =>
      simp only [all, List.mem_append]
      exact Or.inl (Or.inr
        (List.mem_map_of_mem (f := Provision.aminoTrivialName) row.mem_all))
  | printedExample exampleRow =>
      simp only [all, List.mem_append]
      exact Or.inr (List.mem_map_of_mem (f := Provision.printedExample) exampleRow.mem_all)
  | _ => simp [all, base]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 122 := by decide

end Provision

def Provision.sourceKey : Provision → String
  | .establishedDeoxyTrivialNames | .deoxyTrivialNamesRetainedForUnmodifiedSugars
  | .systematicDeoxyNamesPreferredForDerivatives | .otherUsedDeoxyTrivialNames
  | .terminalMethylIsOmegaDeoxyNotCMethyl | .deoxyTrivialName _ => "2-Carb-13.1"
  | .deoxyWithTrivialNameWhenNoCenterRemoved | .deoxyRemovalOfCenterCreatesRedundancy
  | .systematicPreferredWhenCenterRemoved | .commonTwoDeoxyNames => "2-Carb-13.2"
  | .systematicDeoxyLocantPrefixStem | .deoxyPrefixesDescribePresentCenters
  | .configurationalPrefixesCitedFarthestFromC1 | .deoxyIsDetachableAlphabetizedPrefix
  | .detachablePracticeConflictsGeneralGuide | .methyleneInterruptionIgnored
  | .prefixCoversEntireRemainingCenterSequence
  | .anomericHydroxyToHydrogenRoutesToAnhydroAlditol => "2-Carb-13.3"
  | .terminalAldehydeToMethylUsesDeoxyAlditol | .fucitolAndRhamnitolFrequent => "2-Carb-13.4"
  | .aminoReplacementIsSubstitutionOnDeoxySugar
  | .aminoEquivalentToHydroxyForConfiguration
  | .nSubstitutedTreatmentRoutesToTwoCarbTwentyFive => "2-Carb-14.1"
  | .acceptedAminoTrivialNames | .neuraminicAndMuramicNamesSpecificallyD
  | .nonexistentParentAminoNamesNotRecommended | .ringNitrogenRoutesToTwoCarbThirtyFour
  | .aminoTrivialName _ => "2-Carb-14.2"
  | .systematicAminoUsesDeoxyAndAminoPrefixes | .aminoDeoxyAlphabetization
  | .anomericAminoNormallyGlycosylamine => "2-Carb-14.3"
  | .hydroxyOrCarbonylOxygenToSulfurUsesThio
  | .ringOxygenToSulfurUsesAdjacentNonanomericLocant
  | .seleniumAndTelluriumUseSelenoTelluro | .chalcogenOxidesMayUseFunctionalClassNames
  | .thioNotThia | .thioCommonlyTreatedAsDetachable => "2-Carb-15"
  | .nonterminalHydrogenReplacementIsCSubstitution
  | .highestCIPPriorityGroupEquivalentToHydroxy | .ambiguousModifiedCenterUsesRS => "2-Carb-16.1"
  | .nonanomericHydroxyReplacementUsesDeoxyParent | .replacingGroupDeterminesConfiguration
  | .hydroxyReplacementAmbiguityUsesRS
  | .cLocantRequiredOnlyForAmbiguityButMayEmphasize => "2-Carb-16.2"
  | .unequalSubstitutionUsesDisubstitutedDeoxyParent
  | .unequalHigherCIPGroupEquivalentToHydroxy
  | .unequalSubstitutionAmbiguityUsesRS => "2-Carb-16.3"
  | .terminalCreatedCenterUsesRS | .terminalMethylStillDeoxyNotCMethyl
  | .aldehydicHydrogenRingReplacementUsesCPrefix => "2-Carb-16.4"
  | .iminoAnalogueMayUseIminoDeoxyAlditol | .oximesAndHydrazonesNamedDirectly
  | .arylosazonePrefersKetoaldoseBisHydrazone
  | .oxidizedArylosazoneMayUseTriazolylAlditol => "2-Carb-16.5"
  | .isotopeRulesDelegatedToSectionH | .isotopeParenthesesVsLabellingBrackets
  | .uniformLabellingUsesU | .isotopeCreatedCenterFollowsSubstitutionRules => "2-Carb-16.6"
  | .printedExample exampleRow => exampleRow.data.sourceKey

/-! ## Executable configuration-routing semantics -/

inductive ConfigurationSurrogate where
  | hydroxy
  | amino
  | replacingGroup
  | highestCIPPrioritySubstituent
  deriving DecidableEq, Repr

inductive ModificationKind where
  | aminoForHydroxy
  | replaceHydroxy
  | addSubstituentToCarbon
  | unequalDoubleSubstitution
  deriving DecidableEq, Repr

def configurationSurrogate : ModificationKind → ConfigurationSurrogate
  | .aminoForHydroxy => .amino
  | .replaceHydroxy => .replacingGroup
  | .addSubstituentToCarbon | .unequalDoubleSubstitution => .highestCIPPrioritySubstituent

@[simp] theorem amino_is_treated_as_hydroxy_position_for_configuration :
    configurationSurrogate .aminoForHydroxy = .amino := by rfl

@[simp] theorem carbon_substitution_routes_through_CIP_priority :
    configurationSurrogate .addSubstituentToCarbon = .highestCIPPrioritySubstituent ∧
      configurationSurrogate .unequalDoubleSubstitution = .highestCIPPrioritySubstituent := by
  decide

/-- A lost chiral center is absent rather than beginning a new configurational-prefix group. -/
def remainingConfigurationSides
    (positions : List (Option Carbohydrate1996NamedParents.FischerSide)) :
    List Carbohydrate1996NamedParents.FischerSide :=
  positions.filterMap id

@[simp] theorem deoxy_methylene_does_not_split_the_configuration_sequence :
    remainingConfigurationSides
      [some .left, some .right, none, some .right, some .left] =
      [.left, .right, .right, .left] := by
  rfl

inductive Chalcogen where
  | sulfur
  | selenium
  | tellurium
  deriving DecidableEq, Repr

def Chalcogen.replacementPrefix : Chalcogen → String
  | .sulfur => "thio"
  | .selenium => "seleno"
  | .tellurium => "telluro"

@[simp] theorem sulfur_prefix_is_thio_not_thia :
    Chalcogen.sulfur.replacementPrefix = "thio" ∧
      Chalcogen.sulfur.replacementPrefix ≠ "thia" := by
  decide

def atomicNumber : String → Option Nat
  | "Cl" => some 17
  | "Br" => some 35
  | _ => none

@[simp] theorem bromine_has_CIP_atomic_number_priority_over_chlorine :
    atomicNumber "Br" = some 35 ∧ atomicNumber "Cl" = some 17 ∧ 35 > 17 := by
  decide

inductive IsotopeNotation where
  | substitution
  | labelling
  deriving DecidableEq, Repr

def IsotopeNotation.delimiters : IsotopeNotation → String × String
  | .substitution => ("(", ")")
  | .labelling => ("[", "]")

@[simp] theorem isotope_substitution_and_labelling_have_distinct_delimiters :
    IsotopeNotation.substitution.delimiters = ("(", ")") ∧
      IsotopeNotation.labelling.delimiters = ("[", "]") ∧
      IsotopeNotation.substitution.delimiters ≠ IsotopeNotation.labelling.delimiters := by
  decide

def requiresExplicitRS (createsCenter ambiguous : Bool) : Bool :=
  createsCenter || ambiguous

@[simp] theorem newly_created_terminal_or_isotopic_center_requires_RS :
    requiresExplicitRS true false = true := by decide

end Carbohydrate1996Derivatives

end TetraStereo.OneCenter
