import TetraStereo.OneCenter.Basic
import TetraStereo.OneCenter.P10DelegatedAuthorityCorpus

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent carbohydrate scope, definitions, and parent-choice semantics

This module audits the normative preamble, 2-Carb-1, and 2-Carb-2 of *Nomenclature of
Carbohydrates (Recommendations 1996)*.  Historical section 2-Carb-0 is recorded as historical
material rather than silently promoted into rules.  Parent selection is important to
stereochemistry: the ordered criteria select which D/L and alpha/beta-bearing parent name is the
authoritative name when several carbohydrate substructures are present.
-/

namespace Carbohydrate1996ScopeParent

inductive HistoricalTopic where
  | earlyApproaches
  | emilFischer
  | cyclicForms
  | nomenclatureCommissions
  deriving DecidableEq, Repr

def HistoricalTopic.all : List HistoricalTopic :=
  [ .earlyApproaches, .emilFischer, .cyclicForms, .nomenclatureCommissions ]

@[simp] theorem HistoricalTopic.mem_all (topic : HistoricalTopic) : topic ∈ HistoricalTopic.all := by
  cases topic <;> simp [HistoricalTopic.all]

inductive AbbreviationGroup where
  | acetyl
  | benzyl
  | benzoyl
  | ethyl
  | methyl
  | trimethylsilyl
  | tertButyldimethylsilyl
  | phenyl
  | triflyl
  | tosyl
  | trityl
  deriving DecidableEq, Repr

namespace AbbreviationGroup

def all : List AbbreviationGroup :=
  [ .acetyl, .benzyl, .benzoyl, .ethyl, .methyl, .trimethylsilyl
  , .tertButyldimethylsilyl, .phenyl, .triflyl, .tosyl, .trityl
  ]

@[simp] theorem mem_all (group : AbbreviationGroup) : group ∈ all := by
  cases group <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 11 := by decide

end AbbreviationGroup

structure AbbreviationData where
  meaning : String
  accepted : List String
  rejected : List String := []
  deriving DecidableEq, Repr

def AbbreviationGroup.data : AbbreviationGroup → AbbreviationData
  | .acetyl => ⟨"acetyl", ["Ac"], []⟩
  | .benzyl => ⟨"benzyl", ["Bn", "PhCH2"], []⟩
  | .benzoyl => ⟨"benzoyl", ["Bz", "PhCO"], []⟩
  | .ethyl => ⟨"ethyl", ["Et"], []⟩
  | .methyl => ⟨"methyl", ["Me"], []⟩
  | .trimethylsilyl => ⟨"trimethylsilyl", ["Me3Si"], ["TMS"]⟩
  | .tertButyldimethylsilyl => ⟨"tert-butyldimethylsilyl", ["ButMe2Si"], ["TBDMS"]⟩
  | .phenyl => ⟨"phenyl", ["Ph"], []⟩
  | .triflyl => ⟨"triflyl = trifluoromethanesulfonyl", ["Tf"], []⟩
  | .tosyl => ⟨"tosyl = toluene-p-sulfonyl", ["Ts"], []⟩
  | .trityl => ⟨"trityl", ["Tr"], []⟩

theorem abbreviation_meanings_are_pairwise_distinct :
    (AbbreviationGroup.all.map fun group => group.data.meaning).Nodup := by
  decide

inductive ParentChoiceExample where
  | glucitolOverGulitol
  | erythroGlucoOverThreoAllo
  | methylDXylitol
  | trimethylDMannitol
  | acetylBeforeMethyl
  deriving DecidableEq, Repr

namespace ParentChoiceExample

def all : List ParentChoiceExample :=
  [ .glucitolOverGulitol, .erythroGlucoOverThreoAllo, .methylDXylitol
  , .trimethylDMannitol, .acetylBeforeMethyl
  ]

@[simp] theorem mem_all (exampleRow : ParentChoiceExample) : exampleRow ∈ all := by
  cases exampleRow <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 5 := by decide

end ParentChoiceExample

structure ParentChoiceExampleData where
  sourceKey : String
  preferredName : String
  rejectedName : String
  deriving DecidableEq, Repr

def ParentChoiceExample.data : ParentChoiceExample → ParentChoiceExampleData
  | .glucitolOverGulitol =>
      ⟨"2-Carb-2.2.2/example 0222A", "L-Glucitol", "D-gulitol"⟩
  | .erythroGlucoOverThreoAllo =>
      ⟨"2-Carb-2.2.2/example 0222B", "L-erythro-L-gluco-Non-5-ulose",
        "D-threo-D-allo-non-5-ulose"⟩
  | .methylDXylitol =>
      ⟨"2-Carb-2.2.3.1/example 02231", "4-O-Methyl-D-xylitol", "2-O-methyl-L-xylitol"⟩
  | .trimethylDMannitol =>
      ⟨"2-Carb-2.2.3.2/example 02232", "2,3,5-Tri-O-methyl-D-mannitol",
        "2,4,5-tri-O-methyl-D-mannitol"⟩
  | .acetylBeforeMethyl =>
      ⟨"2-Carb-2.2.3.3/example 02233", "2-O-Acetyl-5-O-methyl-D-mannitol",
        "5-O-acetyl-2-O-methyl-D-mannitol"⟩

theorem parent_choice_example_keys_are_pairwise_distinct :
    (ParentChoiceExample.all.map fun exampleRow => exampleRow.data.sourceKey).Nodup := by
  decide

inductive Provision where
  | replaces1969TentativeRules
  | replacesEarlierSpecialistDocuments
  | relatedRecommendationsNotIncorporated
  | scopeMonosaccharidesDerivativesOligoPoly
  | additionalToGeneralOrganicRules
  | carbohydrateGenericClassInventory
  | carbohydrateDerivativeOperations
  | sugarTermUsage
  | cyclitolsGenerallyExcluded
  | parentMonosaccharideMinimumAndFunctions
  | monosaccharideIsSingleUnglycosylatedUnit
  | monosaccharideClassInventory
  | monosaccharideRequiresPotentialCarbonyl
  | aldoseDefinition
  | ketoseDefinition
  | potentialCarbonylDefinitions
  | furanoseFiveMembered
  | pyranoseSixMembered
  | otherRingSizesRouteToTwoCarbFive
  | dialdoseDefinition
  | diketoseDefinition
  | ketoaldoseDefinition
  | ketoaldoseTermPreferred
  | deoxySugarDefinition
  | aminoSugarDefinition
  | glycosylamineDefinition
  | alditolDefinition
  | aldonicAcidDefinition
  | ketoaldonicAcidDefinition
  | uronicAcidDefinition
  | aldaricAcidDefinition
  | glycosideDefinition
  | glycosidicBondDefinition
  | glycosideExtendedDefinitionRoute
  | oligosaccharideDefinition
  | oligosaccharideUnitCountNames
  | oligoPolyBoundaryNotStrict
  | oligoUsuallyDefinedStructure
  | nonglycosidicOligoAnalogues
  | polysaccharideDefinition
  | polyGlycoseNotFullSynonym
  | aminoSugarPolymerTerminology
  | homoAndHeteropolysaccharideClasses
  | glycanCanMeanGlycoproteinSaccharide
  | mixedGlycosidicPhosphateUsage
  | exampleInitialCapitalConvention
  | structuralFormulaAbbreviationInventory
  | parentCriteriaAppliedUntilDecision
  | preferredFunctionalGroupFirst
  | greatestPreferredFunctionOccurrenceCount
  | exactFunctionalClassPrecedence
  | greatestCarbonChainLength
  | alphabeticalNameCriterion
  | trivialOrConfigurationalPrefixAlphabetization
  | dBeforeL
  | alphaBeforeBeta
  | greatestPrefixSubstituentCount
  | bridgingSubstitutionCountsMultiple
  | lowestSubstituentLocantSet
  | lowestFirstCitedSubstituentLocant
  | branchedStructuresRouteToTwoCarbEighteen
  | uronicPotentialAldehydeRemainsPrincipal
  | carbohydrateIntegrityCanOverrideGeneralPreference
  | acyclicParentStructureGroundsName
  | chartsProvideTrivialNamesThroughSixCarbons
  | systematicProceduresDelegatedToEightAndTen
  | chartIShowsOnlyDAndLIsMirror
  | boldChartChainDefinesConfigurationalPrefix
  | parentCarbonsNumberedConsecutively
  | potentialAldehydeReceivesLocantOne
  | aldehydeLocantOneEvenWithSeniorFunction
  | nextSeniorSuffixFunctionLowestLocant
  | carboxylicAcidPrecedesKetonicCarbonyl
  | parentNameAlphabeticalIncludingConfigPrefix
  | trivialNamePreferenceBoundary
  | symmetricDerivativeCriteriaOrdered
  | symmetricDerivativeDBeforeL
  | symmetricDerivativeLowestLocantSet
  | symmetricDerivativeLowestFirstAlphabeticLocant
  | abbreviation (group : AbbreviationGroup)
  | parentChoiceExample (exampleRow : ParentChoiceExample)
  deriving DecidableEq, Repr

namespace Provision

def base : List Provision :=
  [ .replaces1969TentativeRules
  , .replacesEarlierSpecialistDocuments
  , .relatedRecommendationsNotIncorporated
  , .scopeMonosaccharidesDerivativesOligoPoly
  , .additionalToGeneralOrganicRules
  , .carbohydrateGenericClassInventory
  , .carbohydrateDerivativeOperations
  , .sugarTermUsage
  , .cyclitolsGenerallyExcluded
  , .parentMonosaccharideMinimumAndFunctions
  , .monosaccharideIsSingleUnglycosylatedUnit
  , .monosaccharideClassInventory
  , .monosaccharideRequiresPotentialCarbonyl
  , .aldoseDefinition
  , .ketoseDefinition
  , .potentialCarbonylDefinitions
  , .furanoseFiveMembered
  , .pyranoseSixMembered
  , .otherRingSizesRouteToTwoCarbFive
  , .dialdoseDefinition
  , .diketoseDefinition
  , .ketoaldoseDefinition
  , .ketoaldoseTermPreferred
  , .deoxySugarDefinition
  , .aminoSugarDefinition
  , .glycosylamineDefinition
  , .alditolDefinition
  , .aldonicAcidDefinition
  , .ketoaldonicAcidDefinition
  , .uronicAcidDefinition
  , .aldaricAcidDefinition
  , .glycosideDefinition
  , .glycosidicBondDefinition
  , .glycosideExtendedDefinitionRoute
  , .oligosaccharideDefinition
  , .oligosaccharideUnitCountNames
  , .oligoPolyBoundaryNotStrict
  , .oligoUsuallyDefinedStructure
  , .nonglycosidicOligoAnalogues
  , .polysaccharideDefinition
  , .polyGlycoseNotFullSynonym
  , .aminoSugarPolymerTerminology
  , .homoAndHeteropolysaccharideClasses
  , .glycanCanMeanGlycoproteinSaccharide
  , .mixedGlycosidicPhosphateUsage
  , .exampleInitialCapitalConvention
  , .structuralFormulaAbbreviationInventory
  , .parentCriteriaAppliedUntilDecision
  , .preferredFunctionalGroupFirst
  , .greatestPreferredFunctionOccurrenceCount
  , .exactFunctionalClassPrecedence
  , .greatestCarbonChainLength
  , .alphabeticalNameCriterion
  , .trivialOrConfigurationalPrefixAlphabetization
  , .dBeforeL
  , .alphaBeforeBeta
  , .greatestPrefixSubstituentCount
  , .bridgingSubstitutionCountsMultiple
  , .lowestSubstituentLocantSet
  , .lowestFirstCitedSubstituentLocant
  , .branchedStructuresRouteToTwoCarbEighteen
  , .uronicPotentialAldehydeRemainsPrincipal
  , .carbohydrateIntegrityCanOverrideGeneralPreference
  , .acyclicParentStructureGroundsName
  , .chartsProvideTrivialNamesThroughSixCarbons
  , .systematicProceduresDelegatedToEightAndTen
  , .chartIShowsOnlyDAndLIsMirror
  , .boldChartChainDefinesConfigurationalPrefix
  , .parentCarbonsNumberedConsecutively
  , .potentialAldehydeReceivesLocantOne
  , .aldehydeLocantOneEvenWithSeniorFunction
  , .nextSeniorSuffixFunctionLowestLocant
  , .carboxylicAcidPrecedesKetonicCarbonyl
  , .parentNameAlphabeticalIncludingConfigPrefix
  , .trivialNamePreferenceBoundary
  , .symmetricDerivativeCriteriaOrdered
  , .symmetricDerivativeDBeforeL
  , .symmetricDerivativeLowestLocantSet
  , .symmetricDerivativeLowestFirstAlphabeticLocant
  ]

def all : List Provision :=
  (base ++ AbbreviationGroup.all.map Provision.abbreviation) ++
    ParentChoiceExample.all.map Provision.parentChoiceExample

@[simp] theorem mem_all (provision : Provision) : provision ∈ all := by
  cases provision with
  | abbreviation group =>
      simp only [all, List.mem_append]
      exact Or.inl (Or.inr (List.mem_map_of_mem (f := Provision.abbreviation) group.mem_all))
  | parentChoiceExample exampleRow =>
      simp only [all, List.mem_append]
      exact Or.inr
        (List.mem_map_of_mem (f := Provision.parentChoiceExample) exampleRow.mem_all)
  | _ => simp [all, base]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 95 := by decide

end Provision

def Provision.sourceKey : Provision → String
  | .replaces1969TentativeRules | .replacesEarlierSpecialistDocuments
  | .relatedRecommendationsNotIncorporated | .scopeMonosaccharidesDerivativesOligoPoly
  | .additionalToGeneralOrganicRules => "Preamble"
  | .carbohydrateGenericClassInventory | .carbohydrateDerivativeOperations
  | .sugarTermUsage | .cyclitolsGenerallyExcluded => "2-Carb-1.1"
  | .parentMonosaccharideMinimumAndFunctions | .monosaccharideIsSingleUnglycosylatedUnit
  | .monosaccharideClassInventory | .monosaccharideRequiresPotentialCarbonyl => "2-Carb-1.2"
  | .aldoseDefinition | .ketoseDefinition | .potentialCarbonylDefinitions => "2-Carb-1.2.1"
  | .furanoseFiveMembered | .pyranoseSixMembered
  | .otherRingSizesRouteToTwoCarbFive => "2-Carb-1.2.2"
  | .dialdoseDefinition => "2-Carb-1.3"
  | .diketoseDefinition => "2-Carb-1.4"
  | .ketoaldoseDefinition | .ketoaldoseTermPreferred => "2-Carb-1.5"
  | .deoxySugarDefinition => "2-Carb-1.6"
  | .aminoSugarDefinition | .glycosylamineDefinition => "2-Carb-1.7"
  | .alditolDefinition => "2-Carb-1.8"
  | .aldonicAcidDefinition => "2-Carb-1.9"
  | .ketoaldonicAcidDefinition => "2-Carb-1.10"
  | .uronicAcidDefinition => "2-Carb-1.11"
  | .aldaricAcidDefinition => "2-Carb-1.12"
  | .glycosideDefinition | .glycosidicBondDefinition
  | .glycosideExtendedDefinitionRoute => "2-Carb-1.13"
  | .oligosaccharideDefinition | .oligosaccharideUnitCountNames
  | .oligoPolyBoundaryNotStrict | .oligoUsuallyDefinedStructure
  | .nonglycosidicOligoAnalogues => "2-Carb-1.14"
  | .polysaccharideDefinition | .polyGlycoseNotFullSynonym
  | .aminoSugarPolymerTerminology | .homoAndHeteropolysaccharideClasses
  | .glycanCanMeanGlycoproteinSaccharide | .mixedGlycosidicPhosphateUsage => "2-Carb-1.15"
  | .exampleInitialCapitalConvention => "2-Carb-1.16.1"
  | .structuralFormulaAbbreviationInventory | .abbreviation _ => "2-Carb-1.16.2"
  | .parentCriteriaAppliedUntilDecision | .preferredFunctionalGroupFirst
  | .greatestPreferredFunctionOccurrenceCount | .exactFunctionalClassPrecedence => "2-Carb-2.1.1"
  | .greatestCarbonChainLength => "2-Carb-2.1.2"
  | .alphabeticalNameCriterion | .trivialOrConfigurationalPrefixAlphabetization
  | .dBeforeL | .alphaBeforeBeta => "2-Carb-2.1.3"
  | .greatestPrefixSubstituentCount | .bridgingSubstitutionCountsMultiple => "2-Carb-2.1.4"
  | .lowestSubstituentLocantSet => "2-Carb-2.1.5"
  | .lowestFirstCitedSubstituentLocant => "2-Carb-2.1.6"
  | .branchedStructuresRouteToTwoCarbEighteen | .uronicPotentialAldehydeRemainsPrincipal
  | .carbohydrateIntegrityCanOverrideGeneralPreference => "2-Carb-2.1/notes"
  | .acyclicParentStructureGroundsName | .chartsProvideTrivialNamesThroughSixCarbons
  | .systematicProceduresDelegatedToEightAndTen | .chartIShowsOnlyDAndLIsMirror
  | .boldChartChainDefinesConfigurationalPrefix => "2-Carb-2.2"
  | .parentCarbonsNumberedConsecutively | .potentialAldehydeReceivesLocantOne
  | .aldehydeLocantOneEvenWithSeniorFunction | .nextSeniorSuffixFunctionLowestLocant
  | .carboxylicAcidPrecedesKetonicCarbonyl => "2-Carb-2.2.1"
  | .parentNameAlphabeticalIncludingConfigPrefix | .trivialNamePreferenceBoundary => "2-Carb-2.2.2"
  | .symmetricDerivativeCriteriaOrdered | .symmetricDerivativeDBeforeL
  | .symmetricDerivativeLowestLocantSet
  | .symmetricDerivativeLowestFirstAlphabeticLocant => "2-Carb-2.2.3"
  | .parentChoiceExample exampleRow => exampleRow.data.sourceKey

/-! ## Exact parent-choice hierarchy -/

inductive ParentFunctionalClass where
  | ketose
  | diketose
  | aldose
  | ketoaldose
  | dialdose
  | aldonicAcid
  | ketoaldonicAcid
  | uronicAcid
  | aldaricAcid
  deriving DecidableEq, Repr

/-- Equal ranks are the source's slash-separated ties. -/
def ParentFunctionalClass.rank : ParentFunctionalClass → Nat
  | .ketose => 0
  | .diketose => 1
  | .aldose | .ketoaldose => 2
  | .dialdose => 3
  | .aldonicAcid | .ketoaldonicAcid | .uronicAcid => 4
  | .aldaricAcid => 5

@[simp] theorem functional_class_precedence_is_exact :
    ParentFunctionalClass.aldaricAcid.rank > ParentFunctionalClass.uronicAcid.rank ∧
    ParentFunctionalClass.uronicAcid.rank = ParentFunctionalClass.ketoaldonicAcid.rank ∧
    ParentFunctionalClass.ketoaldonicAcid.rank = ParentFunctionalClass.aldonicAcid.rank ∧
    ParentFunctionalClass.aldonicAcid.rank > ParentFunctionalClass.dialdose.rank ∧
    ParentFunctionalClass.dialdose.rank > ParentFunctionalClass.ketoaldose.rank ∧
    ParentFunctionalClass.ketoaldose.rank = ParentFunctionalClass.aldose.rank ∧
    ParentFunctionalClass.aldose.rank > ParentFunctionalClass.diketose.rank ∧
    ParentFunctionalClass.diketose.rank > ParentFunctionalClass.ketose.rank := by
  decide

inductive ParentCriterion where
  | functionalClass
  | preferredFunctionOccurrenceCount
  | carbonChainLength
  | alphabeticalTrivialOrPrefixName
  | dBeforeL
  | alphaBeforeBeta
  | prefixSubstituentCount
  | lowestSubstituentLocantSet
  | lowestFirstCitedSubstituentLocant
  deriving DecidableEq, Repr

def ParentCriterion.inOrder : List ParentCriterion :=
  [ .functionalClass, .preferredFunctionOccurrenceCount, .carbonChainLength
  , .alphabeticalTrivialOrPrefixName, .dBeforeL, .alphaBeforeBeta
  , .prefixSubstituentCount, .lowestSubstituentLocantSet
  , .lowestFirstCitedSubstituentLocant
  ]

@[simp] theorem parent_criterion_count : ParentCriterion.inOrder.length = 9 := by decide

/-- `gt` means the left candidate is preferred at this criterion. -/
def firstDecisive : List Ordering → Ordering
  | [] => .eq
  | .eq :: remaining => firstDecisive remaining
  | result :: _ => result

theorem first_decisive_criterion_controls
    (equalPrefix remaining : List Ordering) (result : Ordering) (h : result ≠ .eq)
    (heq : ∀ item ∈ equalPrefix, item = .eq) :
    firstDecisive (equalPrefix ++ result :: remaining) = result := by
  induction equalPrefix with
  | nil => simp [firstDecisive]
  | cons item rest ih =>
      have hitem : item = .eq := heq item (by simp)
      subst item
      simp only [List.cons_append, firstDecisive]
      apply ih
      intro candidate hc
      exact heq candidate (by simp [hc])

theorem later_criteria_cannot_override_first_success
    (laterA laterB : List Ordering) (result : Ordering) (h : result ≠ .eq) :
    firstDecisive (result :: laterA) = firstDecisive (result :: laterB) := by
  simp [firstDecisive]

inductive CarbohydrateSeries where
  | D
  | L
  deriving DecidableEq, Repr

def seriesPreference : CarbohydrateSeries → Nat
  | .D => 1
  | .L => 0

@[simp] theorem D_is_preferred_to_L_at_the_series_tiebreaker :
    seriesPreference .D > seriesPreference .L := by decide

inductive CarbohydrateAnomer where
  | alpha
  | beta
  deriving DecidableEq, Repr

def anomerPreference : CarbohydrateAnomer → Nat
  | .alpha => 1
  | .beta => 0

@[simp] theorem alpha_is_preferred_to_beta_at_the_anomer_tiebreaker :
    anomerPreference .alpha > anomerPreference .beta := by decide

/-- Bridging substitutions are already expanded to their number of substituted positions. -/
def prefixSubstitutionCount (ordinaryPositions bridgingPositions : List Nat) : Nat :=
  ordinaryPositions.length + bridgingPositions.length

@[simp] theorem methylene_bridge_counts_as_two_substitutions :
    prefixSubstitutionCount [] [2, 3] = 2 := by decide

end Carbohydrate1996ScopeParent

end TetraStereo.OneCenter
