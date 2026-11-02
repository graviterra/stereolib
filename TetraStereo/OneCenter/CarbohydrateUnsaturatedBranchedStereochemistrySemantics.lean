import TetraStereo.OneCenter.CarbohydrateDerivativeStereochemistrySemantics

set_option autoImplicit false

namespace TetraStereo.OneCenter










namespace Carbohydrate1996UnsaturatedBranched

inductive ChartVRow where
  | cyclicHeptopyranose
  | acyclicHexodialdose
  | cyclicHeptulofuranose
  | acyclicHeptosulose
  | alternativePentoseRejected
  | alternativeThreoHexoseRejected
  deriving DecidableEq, Repr

namespace ChartVRow

def all : List ChartVRow :=
  [ .cyclicHeptopyranose, .acyclicHexodialdose, .cyclicHeptulofuranose
  , .acyclicHeptosulose, .alternativePentoseRejected, .alternativeThreoHexoseRejected
  ]

@[simp] theorem mem_all (row : ChartVRow) : row ∈ all := by
  cases row <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 6 := by decide

end ChartVRow

structure ChartVData where
  printedIndex : Nat
  preferredName : String
  rejectedParent : Option String
  cyclic : Bool
  deriving DecidableEq, Repr

def ChartVRow.data : ChartVRow → ChartVData
  | .cyclicHeptopyranose =>
      ⟨1, "3-Deoxy-3-[(1R,2S)-1,2-dihydroxy-3-oxopropyl]-D-glycero-D-altro-heptopyranose",
        some "alternative open-chain six-carbon dialdose or eight-carbon aldose", true⟩
  | .acyclicHexodialdose =>
      ⟨2, "4-Deoxy-4-(L-ribo-1,2,3,4-tetrahydroxybutyl)-D-altro-hexodialdose", none, false⟩
  | .cyclicHeptulofuranose =>
      ⟨3, "4-Deoxy-4-[(1R,2R)-1,2-dihydroxy-3-oxopropyl]-D-allo-heptulo-2,5-furanose",
        some "alternative ketoaldose", true⟩
  | .acyclicHeptosulose =>
      ⟨4, "4-Deoxy-4-[(1R,2S)-1,2,3-trihydroxypropyl]-L-talo-heptos-6-ulose", none, false⟩
  | .alternativePentoseRejected =>
      ⟨5, "4,6-Dideoxy-3-C-(L-glycero-1-hydroxyethyl)-D-ribo-hexose",
        some "alternative pentose", false⟩
  | .alternativeThreoHexoseRejected =>
      ⟨6, "3,4-Dideoxy-3-[3-hydroxy-2-(hydroxymethyl)propyl]-4-C-methyl-L-mannose",
        some "alternative threo-hexose", false⟩

theorem chart_V_indices_are_exact :
    ChartVRow.all.map (fun row => row.data.printedIndex) = [1, 2, 3, 4, 5, 6] := by
  decide

inductive PrintedExample where
  | glucal
  | methylPentEnofuranoside
  | uracilEnofuranosyl
  | enopyranosylChloride
  | anhydroAltroEnitol
  | dideoxyArabinoEnitol
  | zPentaacetylEnitol
  | ePentaacetylEnitol
  | enoseDimethylAcetal
  | erythroEnopyranose
  | dienitol
  | enantiomericPrecedenceEnitol
  | glyceroEnUlopyranoside
  | glyceroEnopyranosulose
  | glyceroHeptEnDiulose
  | terminalPentEnofuranose
  | terminalHexEnfuranose
  | enYnOctitol
  | pentYnitol
  | cumulativeDienopyranose
  | hexYnofuranose
  | octYnofuranosulose
  | hamamelose
  | cladinose
  | streptose
  | evalose
  | evernitrose
  | garosamine
  | apiose
  | apiofuranose
  | cMethylGlucose
  | deoxyMethylGlucose
  | nitroLyxoHexopyranose
  | cyclohexylHydroxymethylAllose
  | dimethylRiboHexose
  | hydroxymethylErythroPentose
  | pentahydroxypentyl
  deriving DecidableEq, Repr

namespace PrintedExample

def all : List PrintedExample :=
  [ .glucal, .methylPentEnofuranoside, .uracilEnofuranosyl, .enopyranosylChloride
  , .anhydroAltroEnitol, .dideoxyArabinoEnitol, .zPentaacetylEnitol
  , .ePentaacetylEnitol, .enoseDimethylAcetal, .erythroEnopyranose, .dienitol
  , .enantiomericPrecedenceEnitol, .glyceroEnUlopyranoside, .glyceroEnopyranosulose
  , .glyceroHeptEnDiulose, .terminalPentEnofuranose, .terminalHexEnfuranose
  , .enYnOctitol, .pentYnitol, .cumulativeDienopyranose, .hexYnofuranose
  , .octYnofuranosulose, .hamamelose, .cladinose, .streptose, .evalose
  , .evernitrose, .garosamine, .apiose, .apiofuranose, .cMethylGlucose
  , .deoxyMethylGlucose, .nitroLyxoHexopyranose, .cyclohexylHydroxymethylAllose
  , .dimethylRiboHexose, .hydroxymethylErythroPentose, .pentahydroxypentyl
  ]

@[simp] theorem mem_all (exampleRow : PrintedExample) : exampleRow ∈ all := by
  cases exampleRow <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 37 := by decide

end PrintedExample

structure PrintedExampleData where
  sourceKey : String
  printedName : String
  deriving DecidableEq, Repr

def PrintedExample.data : PrintedExample → PrintedExampleData
  | .glucal => ⟨"2-Carb-17.2/172A", "1,5-Anhydro-2-deoxy-D-arabino-hex-1-enitol (non-preferred D-glucal)"⟩
  | .methylPentEnofuranoside => ⟨"2-Carb-17.2/172B", "Methyl 2-deoxy-D-threo-pent-1-enofuranoside"⟩
  | .uracilEnofuranosyl => ⟨"2-Carb-17.2/172C", "1-(2-Deoxy-D-threo-pent-1-enofuranosyl)uracil"⟩
  | .enopyranosylChloride => ⟨"2-Carb-17.2/172D", "3,4-Di-O-acetyl-2-deoxy-D-erythro-pent-1-enopyranosyl chloride"⟩
  | .anhydroAltroEnitol => ⟨"2-Carb-17.2/172E", "2,6-Anhydro-1-deoxy-D-altro-hept-1-enitol; alphabetic-preference alternative rejected"⟩
  | .dideoxyArabinoEnitol => ⟨"2-Carb-17.2/172F", "1,2-Dideoxy-D-arabino-hex-1-enitol"⟩
  | .zPentaacetylEnitol => ⟨"2-Carb-17.2/172G", "(Z)-1,2,3,4,5-Penta-O-acetyl-D-erythro-pent-1-enitol"⟩
  | .ePentaacetylEnitol => ⟨"2-Carb-17.2/172H", "(E)-1,2,3,4,5-Penta-O-acetyl-D-erythro-pent-1-enitol"⟩
  | .enoseDimethylAcetal => ⟨"2-Carb-17.2/172I", "2-Deoxy-D-threo-pent-1-enose dimethyl acetal"⟩
  | .erythroEnopyranose => ⟨"2-Carb-17.2/172J", "2,3-Dideoxy-alpha-D-erythro-hex-2-enopyranose"⟩
  | .dienitol => ⟨"2-Carb-17.2/172K", "1,2,4,5-Tetradeoxy-D-arabino-octa-1,4-dienitol"⟩
  | .enantiomericPrecedenceEnitol => ⟨"2-Carb-17.2/172L", "1,5-Anhydro-4-deoxy-D-erythro-hex-4-enitol; L alternative rejected"⟩
  | .glyceroEnUlopyranoside => ⟨"2-Carb-17.2/172M", "Methyl 3,4-dideoxy-beta-D-glycero-hex-3-en-2-ulopyranoside"⟩
  | .glyceroEnopyranosulose => ⟨"2-Carb-17.2/172N", "2,3-Dideoxy-alpha-D-glycero-hex-2-enopyranos-4-ulose"⟩
  | .glyceroHeptEnDiulose => ⟨"2-Carb-17.2/172O", "Methyl 3,4-dideoxy-beta-D-glycero-hept-3-en-2-ulopyranosid-5-ulose"⟩
  | .terminalPentEnofuranose => ⟨"2-Carb-17.2/172P", "5-Deoxy-1,2-O-isopropylidene-beta-L-threo-pent-4-enofuranose"⟩
  | .terminalHexEnfuranose => ⟨"2-Carb-17.2/172Q", "5,6-Dideoxy-1,2-O-isopropylidene-alpha-D-xylo-hex-5-enfuranose"⟩
  | .enYnOctitol => ⟨"2-Carb-17.3/173A", "(Z)-1,7-Anhydro-2,5,6-trideoxy-D-xylo-oct-5-en-1-ynitol; dehydro alternative"⟩
  | .pentYnitol => ⟨"2-Carb-17.3/173B", "2-Deoxy-1-O-methyl-D-threo-pent-1-ynitol; tetradehydro alternative"⟩
  | .cumulativeDienopyranose => ⟨"2-Carb-17.3/173C", "6,7,8-Trideoxy-alpha-D-galacto-octa-6,7-dienopyranose; dehydro alternative"⟩
  | .hexYnofuranose => ⟨"2-Carb-17.3/173D", "6-O-Acetyl-5-deoxy-alpha-D-xylo-hex-5-ynofuranose; dehydro alternative"⟩
  | .octYnofuranosulose => ⟨"2-Carb-17.3/173E", "5,6,8-Trideoxy-alpha-D-xylo-oct-5-ynofuranos-7-ulose; dehydro alternative"⟩
  | .hamamelose => ⟨"2-Carb-18.1/181A", "Hamamelose; 2-C-(Hydroxymethyl)-D-ribopyranose"⟩
  | .cladinose => ⟨"2-Carb-18.1/181B", "Cladinose; 2,6-dideoxy-3-C-methyl-3-O-methyl-L-ribo-hexopyranose"⟩
  | .streptose => ⟨"2-Carb-18.1/181C", "Streptose; 5-deoxy-3-C-formyl-L-lyxofuranose"⟩
  | .evalose => ⟨"2-Carb-18.1/181D", "6-Deoxy-3-C-methyl-D-mannopyranose (Evalose)"⟩
  | .evernitrose => ⟨"2-Carb-18.1/181E", "2,3,6-Trideoxy-3-C-methyl-4-O-methyl-3-nitro-L-arabino-hexopyranose (Evernitrose)"⟩
  | .garosamine => ⟨"2-Carb-18.1/181F", "3-Deoxy-4-C-methyl-3-methylamino-L-arabinopyranose (Garosamine)"⟩
  | .apiose => ⟨"2-Carb-18.1/181G", "D-Apiose (Api); 3-C-(Hydroxymethyl)-D-glycero-tetrose"⟩
  | .apiofuranose => ⟨"2-Carb-18.1/181H", "3-C-(Hydroxymethyl)-alpha-D-erythrofuranose; apiofuranose alternatives ambiguous or nonpreferred"⟩
  | .cMethylGlucose => ⟨"2-Carb-18.3/183A", "3-C-Methyl-D-glucose (configuration determined by OH)"⟩
  | .deoxyMethylGlucose => ⟨"2-Carb-18.3/183B", "3-Deoxy-3-methyl-D-glucose (configuration determined by CH3)"⟩
  | .nitroLyxoHexopyranose => ⟨"2-Carb-18.3/183C", "2,3,6-Trideoxy-3-C-methyl-4-O-methyl-3-nitro-D-lyxo-hexopyranose (N over C)"⟩
  | .cyclohexylHydroxymethylAllose => ⟨"2-Carb-18.3/183D", "4-Cyclohexyl-4-deoxy-4-(hydroxymethyl)-D-allose (O over C); (4R) alternative"⟩
  | .dimethylRiboHexose => ⟨"2-Carb-18.3/183E", "3-Deoxy-3,3-dimethyl-D-ribo-hexose"⟩
  | .hydroxymethylErythroPentose => ⟨"2-Carb-18.3/183F", "4-C-(Hydroxymethyl)-D-erythro-pentose"⟩
  | .pentahydroxypentyl => ⟨"2-Carb-18.4/184", "L-gluco-1,2,3,4,5-Pentahydroxypentyl"⟩

theorem printed_example_keys_are_pairwise_distinct :
    (PrintedExample.all.map fun exampleRow => exampleRow.data.sourceKey).Nodup := by
  decide

inductive Provision where
  | unsaturationScopeContiguousBackboneCarbons
  | exocyclicUnsaturationUsesGeneralOrganicRules
  | doubleBondUsesXEnInfixAndEuphonicO
  | unsaturationInfixAfterChainStem
  | doubleBondLocantIsLowerCarbon
  | ezPrecedesWholeNameWhenNecessary
  | multipleDoubleBondsUseDienAndEuphonicA
  | glycalNonpreferredOnlyForRingOneTwoDoubleBond
  | glycalNotGeneralClassName
  | ringCCROClassificationDependsOnR
  | ringAtMostSixMayOmitEZ
  | tripleBondUsesNYn
  | cumulativeDoubleBondsUseDien
  | alternativeDehydroDeoxyMethod
  | deoxyOperationFormallyPrecedesDehydro
  | dehydroAndDeoxyPrefixesAlphabetized
  | branchedRulesModify1980WithCyclicPriority
  | branchedTrivialNamesExist
  | listedBranchedEnantiomersNamedSystematically
  | cyclicApioseSystematicNamePreferred
  | alphaDErythroApiofuranoseIsAmbiguous
  | branchedNamedAsSubstitutedUnbranchedParent
  | cLocantsOnlyRequiredForAmbiguityButMayEmphasize
  | cyclicParentChainMustIncludeRingAtoms
  | acyclicBranchedParentUsesTwoCarbTwo
  | hydroxyCanDetermineBranchPointConfiguration
  | deoxyBranchPointUsesRemainingSubstituent
  | branchPointUsesCIPElementPriority
  | identicalBranchSubstituentsMakeCenterAchiral
  | achiralBranchPointUsesWholeSequencePrefix
  | cyclizationCanChangePrefixCenterCount
  | cyclicAndAcyclicFormsCanHaveDifferentNames
  | branchesNamedAsSubstitutedAlkylGroups
  | branchCentersUseRSOrStraightforwardCarbohydratePrefix
  | attachmentActsAsAldehydeAbsentBranchCarbonyl
  | branchCarbonylOrTerminalAcidDefinesPrefix
  | branchRSGenerallyPreferred
  | alternativeResidueSubstituentRoute
  | parentChainNumberingUsesTwoCarbTwo
  | optionalUniqueBranchNumberingScheme
  | branchNumberingSchemeForbiddenInNames
  | terminalSubstitutionRoutesToTwoCarbSixteen
  | chartV (row : ChartVRow)
  | printedExample (exampleRow : PrintedExample)
  deriving DecidableEq, Repr

namespace Provision

def base : List Provision :=
  [ .unsaturationScopeContiguousBackboneCarbons, .exocyclicUnsaturationUsesGeneralOrganicRules
  , .doubleBondUsesXEnInfixAndEuphonicO, .unsaturationInfixAfterChainStem
  , .doubleBondLocantIsLowerCarbon, .ezPrecedesWholeNameWhenNecessary
  , .multipleDoubleBondsUseDienAndEuphonicA, .glycalNonpreferredOnlyForRingOneTwoDoubleBond
  , .glycalNotGeneralClassName, .ringCCROClassificationDependsOnR
  , .ringAtMostSixMayOmitEZ, .tripleBondUsesNYn, .cumulativeDoubleBondsUseDien
  , .alternativeDehydroDeoxyMethod, .deoxyOperationFormallyPrecedesDehydro
  , .dehydroAndDeoxyPrefixesAlphabetized, .branchedRulesModify1980WithCyclicPriority
  , .branchedTrivialNamesExist, .listedBranchedEnantiomersNamedSystematically
  , .cyclicApioseSystematicNamePreferred, .alphaDErythroApiofuranoseIsAmbiguous
  , .branchedNamedAsSubstitutedUnbranchedParent
  , .cLocantsOnlyRequiredForAmbiguityButMayEmphasize, .cyclicParentChainMustIncludeRingAtoms
  , .acyclicBranchedParentUsesTwoCarbTwo, .hydroxyCanDetermineBranchPointConfiguration
  , .deoxyBranchPointUsesRemainingSubstituent, .branchPointUsesCIPElementPriority
  , .identicalBranchSubstituentsMakeCenterAchiral, .achiralBranchPointUsesWholeSequencePrefix
  , .cyclizationCanChangePrefixCenterCount, .cyclicAndAcyclicFormsCanHaveDifferentNames
  , .branchesNamedAsSubstitutedAlkylGroups
  , .branchCentersUseRSOrStraightforwardCarbohydratePrefix
  , .attachmentActsAsAldehydeAbsentBranchCarbonyl
  , .branchCarbonylOrTerminalAcidDefinesPrefix, .branchRSGenerallyPreferred
  , .alternativeResidueSubstituentRoute, .parentChainNumberingUsesTwoCarbTwo
  , .optionalUniqueBranchNumberingScheme, .branchNumberingSchemeForbiddenInNames
  , .terminalSubstitutionRoutesToTwoCarbSixteen
  ]

def all : List Provision :=
  (base ++ ChartVRow.all.map Provision.chartV) ++
    PrintedExample.all.map Provision.printedExample

@[simp] theorem mem_all (provision : Provision) : provision ∈ all := by
  cases provision with
  | chartV row =>
      simp only [all, List.mem_append]
      exact Or.inl (Or.inr (List.mem_map_of_mem (f := Provision.chartV) row.mem_all))
  | printedExample exampleRow =>
      simp only [all, List.mem_append]
      exact Or.inr (List.mem_map_of_mem (f := Provision.printedExample) exampleRow.mem_all)
  | _ => simp [all, base]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 85 := by decide

end Provision

def Provision.sourceKey : Provision → String
  | .unsaturationScopeContiguousBackboneCarbons
  | .exocyclicUnsaturationUsesGeneralOrganicRules => "2-Carb-17.1"
  | .doubleBondUsesXEnInfixAndEuphonicO | .unsaturationInfixAfterChainStem
  | .doubleBondLocantIsLowerCarbon | .ezPrecedesWholeNameWhenNecessary
  | .multipleDoubleBondsUseDienAndEuphonicA | .glycalNonpreferredOnlyForRingOneTwoDoubleBond
  | .glycalNotGeneralClassName | .ringCCROClassificationDependsOnR
  | .ringAtMostSixMayOmitEZ => "2-Carb-17.2"
  | .tripleBondUsesNYn | .cumulativeDoubleBondsUseDien | .alternativeDehydroDeoxyMethod
  | .deoxyOperationFormallyPrecedesDehydro
  | .dehydroAndDeoxyPrefixesAlphabetized => "2-Carb-17.3"
  | .branchedRulesModify1980WithCyclicPriority | .branchedTrivialNamesExist
  | .listedBranchedEnantiomersNamedSystematically | .cyclicApioseSystematicNamePreferred
  | .alphaDErythroApiofuranoseIsAmbiguous => "2-Carb-18.1"
  | .branchedNamedAsSubstitutedUnbranchedParent
  | .cLocantsOnlyRequiredForAmbiguityButMayEmphasize => "2-Carb-18.2"
  | .cyclicParentChainMustIncludeRingAtoms | .acyclicBranchedParentUsesTwoCarbTwo
  | .hydroxyCanDetermineBranchPointConfiguration | .deoxyBranchPointUsesRemainingSubstituent
  | .branchPointUsesCIPElementPriority | .identicalBranchSubstituentsMakeCenterAchiral
  | .achiralBranchPointUsesWholeSequencePrefix | .cyclizationCanChangePrefixCenterCount
  | .cyclicAndAcyclicFormsCanHaveDifferentNames | .chartV _ => "2-Carb-18.3/Chart V"
  | .branchesNamedAsSubstitutedAlkylGroups
  | .branchCentersUseRSOrStraightforwardCarbohydratePrefix
  | .attachmentActsAsAldehydeAbsentBranchCarbonyl
  | .branchCarbonylOrTerminalAcidDefinesPrefix | .branchRSGenerallyPreferred
  | .alternativeResidueSubstituentRoute => "2-Carb-18.4"
  | .parentChainNumberingUsesTwoCarbTwo | .optionalUniqueBranchNumberingScheme
  | .branchNumberingSchemeForbiddenInNames => "2-Carb-18.5"
  | .terminalSubstitutionRoutesToTwoCarbSixteen => "2-Carb-18.6"
  | .printedExample exampleRow => exampleRow.data.sourceKey

/-! ## Executable applicability and configuration semantics -/

inductive BackboneUnsaturation where
  | doubleBond
  | tripleBond
  | cumulativeDoubleBonds
  deriving DecidableEq, Repr

def BackboneUnsaturation.infix (lowerLocant : Nat) : BackboneUnsaturation → String
  | .doubleBond => toString lowerLocant ++ "-en"
  | .tripleBond => toString lowerLocant ++ "-yn"
  | .cumulativeDoubleBonds => toString lowerLocant ++ "," ++ toString (lowerLocant + 1) ++ "-dien"

@[simp] theorem unsaturation_infices_distinguish_double_triple_and_cumulative :
    BackboneUnsaturation.doubleBond.infix 5 = "5-en" ∧
      BackboneUnsaturation.tripleBond.infix 5 = "5-yn" ∧
      BackboneUnsaturation.cumulativeDoubleBonds.infix 6 = "6,7-dien" := by
  decide

def ezMayBeOmitted (insideRing : Bool) (ringAtomCount : Nat) : Bool :=
  insideRing && ringAtomCount ≤ 6

@[simp] theorem six_membered_ring_may_omit_but_seven_membered_may_not :
    ezMayBeOmitted true 6 = true ∧ ezMayBeOmitted true 7 = false ∧
      ezMayBeOmitted false 5 = false := by
  decide

inductive RingEnolSubstituentKind where
  | hydrogenOrCarbon
  | halogenChalcogenOrNitrogenFamily
  deriving DecidableEq, Repr

inductive RingEnolParentClass where
  | unsaturatedAnhydroAlditol
  | glycenoseOrGlycenosyl
  deriving DecidableEq, Repr

def ringEnolParentClass : RingEnolSubstituentKind → RingEnolParentClass
  | .hydrogenOrCarbon => .unsaturatedAnhydroAlditol
  | .halogenChalcogenOrNitrogenFamily => .glycenoseOrGlycenosyl

@[simp] theorem ring_enol_parent_class_boundary_is_exact :
    ringEnolParentClass .hydrogenOrCarbon = .unsaturatedAnhydroAlditol ∧
      ringEnolParentClass .halogenChalcogenOrNitrogenFamily = .glycenoseOrGlycenosyl := by
  decide

inductive BranchParentEvidence where
  | cyclicRingChain
  | acyclicTwoCarbTwoChoice
  deriving DecidableEq, Repr

def chooseBranchParentEvidence (formsCyclicHemiacetalOrHemiketal : Bool) : BranchParentEvidence :=
  if formsCyclicHemiacetalOrHemiketal then .cyclicRingChain else .acyclicTwoCarbTwoChoice

@[simp] theorem cyclic_branch_parent_must_use_ring_chain :
    chooseBranchParentEvidence true = .cyclicRingChain := by rfl

inductive BranchConfigurationMethod where
  | CIPRS
  | carbohydratePrefix
  deriving DecidableEq, Repr

def preferredBranchConfigurationMethod : BranchConfigurationMethod := .CIPRS

@[simp] theorem branch_RS_is_the_general_preference :
    preferredBranchConfigurationMethod = .CIPRS := by rfl

def elementRank : String → Option Nat
  | "C" => some 6
  | "N" => some 7
  | "O" => some 8
  | _ => none

@[simp] theorem chart_V_priority_examples_follow_atomic_number :
    elementRank "N" = some 7 ∧ elementRank "O" = some 8 ∧ elementRank "C" = some 6 ∧
      7 > 6 ∧ 8 > 6 := by
  decide

def branchPointIsChiral {α : Type} [DecidableEq α] (first second : α) : Bool :=
  first != second

@[simp] theorem identical_branch_substituents_destroy_branch_point_chirality
    {α : Type} [DecidableEq α] (substituent : α) :
    branchPointIsChiral substituent substituent = false := by
  simp [branchPointIsChiral]

end Carbohydrate1996UnsaturatedBranched

end TetraStereo.OneCenter
