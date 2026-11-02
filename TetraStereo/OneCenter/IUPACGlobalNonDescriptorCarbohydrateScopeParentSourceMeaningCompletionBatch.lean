import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceDataBatch
import TetraStereo.KernelOnly

set_option autoImplicit false











namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning

open GlobalNonDescriptorIndexedSourceData

inductive SemanticDomain where
  | editionAndScope
  | carbohydrateDefinition
  | parentSelection
  | parentNaming
  deriving DecidableEq, Repr

def semanticDomain (row : Carbohydrate1996ScopeParent.Provision) : SemanticDomain :=
  match row.sourceKey with
  | "Preamble" => .editionAndScope
  | "2-Carb-1.1" | "2-Carb-1.2" | "2-Carb-1.2.1" | "2-Carb-1.2.2"
  | "2-Carb-1.3" | "2-Carb-1.4" | "2-Carb-1.5" | "2-Carb-1.6"
  | "2-Carb-1.7" | "2-Carb-1.8" | "2-Carb-1.9" | "2-Carb-1.10"
  | "2-Carb-1.11" | "2-Carb-1.12" | "2-Carb-1.13" | "2-Carb-1.14"
  | "2-Carb-1.15" | "2-Carb-1.16.1" | "2-Carb-1.16.2" => .carbohydrateDefinition
  | "2-Carb-2.1.1" | "2-Carb-2.1.2" | "2-Carb-2.1.3" | "2-Carb-2.1.4"
  | "2-Carb-2.1.5" | "2-Carb-2.1.6" | "2-Carb-2.1/notes" => .parentSelection
  | _ => .parentNaming

inductive CarbohydrateClass where
  | monosaccharide
  | carbohydrateDerivative
  | oligosaccharide
  | polysaccharide
  deriving DecidableEq, Repr

inductive RingClass where
  | furanose
  | pyranose
  deriving DecidableEq, Repr

def carbohydrateClassInventory : List CarbohydrateClass :=
  [.monosaccharide, .carbohydrateDerivative, .oligosaccharide, .polysaccharide]

def potentialCarbonylInventory : List Carbohydrate1996ScopeParent.ParentFunctionalClass :=
  [.aldose, .ketose, .dialdose, .diketose, .ketoaldose, .aldonicAcid,
    .ketoaldonicAcid, .uronicAcid, .aldaricAcid]

def oligosaccharideUnitCountInventory : List (Nat × String) :=
  [ (2, "disaccharide"), (3, "trisaccharide"), (4, "tetrasaccharide")
  , (5, "pentasaccharide"), (6, "hexasaccharide"), (7, "heptasaccharide")
  , (8, "octasaccharide"), (9, "nonasaccharide"), (10, "decasaccharide") ]

def parentCriterionInventory : List Carbohydrate1996ScopeParent.ParentCriterion :=
  Carbohydrate1996ScopeParent.ParentCriterion.inOrder

def parentFunctionalClassInventory :
    List (Carbohydrate1996ScopeParent.ParentFunctionalClass × Nat) :=
  potentialCarbonylInventory.map fun functionalClass => (functionalClass, functionalClass.rank)

def symmetricDerivativeCriterionInventory :
    List Carbohydrate1996ScopeParent.ParentCriterion :=
  [.dBeforeL, .lowestSubstituentLocantSet, .lowestFirstCitedSubstituentLocant]

/- Typed assertion constructors independently name every source clause; modeled tables and
selection functions retain their concrete values. -/
inductive SourceAssertion where
  | replaces1969TentativeRules
  | replacesEarlierSpecialistDocuments
  | relatedRecommendationsNotIncorporated
  | scopeMonosaccharidesDerivativesOligoPoly
      (inventory : List CarbohydrateClass)
  | additionalToGeneralOrganicRules
  | carbohydrateGenericClassInventory (inventory : List CarbohydrateClass)
  | carbohydrateDerivativeOperations
  | sugarTermUsage
  | cyclitolsGenerallyExcluded
  | parentMonosaccharideMinimumAndFunctions
  | monosaccharideIsSingleUnglycosylatedUnit
  | monosaccharideClassInventory (inventory : List CarbohydrateClass)
  | monosaccharideRequiresPotentialCarbonyl
  | aldoseDefinition (functionalClass : Carbohydrate1996ScopeParent.ParentFunctionalClass)
  | ketoseDefinition (functionalClass : Carbohydrate1996ScopeParent.ParentFunctionalClass)
  | potentialCarbonylDefinitions
      (inventory : List Carbohydrate1996ScopeParent.ParentFunctionalClass)
  | furanoseFiveMembered (ring : RingClass) (memberCount : Nat)
  | pyranoseSixMembered (ring : RingClass) (memberCount : Nat)
  | otherRingSizesRouteToTwoCarbFive (route : String)
  | dialdoseDefinition (functionalClass : Carbohydrate1996ScopeParent.ParentFunctionalClass)
  | diketoseDefinition (functionalClass : Carbohydrate1996ScopeParent.ParentFunctionalClass)
  | ketoaldoseDefinition (functionalClass : Carbohydrate1996ScopeParent.ParentFunctionalClass)
  | ketoaldoseTermPreferred
  | deoxySugarDefinition
  | aminoSugarDefinition
  | glycosylamineDefinition
  | alditolDefinition
  | aldonicAcidDefinition (functionalClass : Carbohydrate1996ScopeParent.ParentFunctionalClass)
  | ketoaldonicAcidDefinition
      (functionalClass : Carbohydrate1996ScopeParent.ParentFunctionalClass)
  | uronicAcidDefinition (functionalClass : Carbohydrate1996ScopeParent.ParentFunctionalClass)
  | aldaricAcidDefinition (functionalClass : Carbohydrate1996ScopeParent.ParentFunctionalClass)
  | glycosideDefinition
  | glycosidicBondDefinition
  | glycosideExtendedDefinitionRoute (route : String)
  | oligosaccharideDefinition
  | oligosaccharideUnitCountNames (inventory : List (Nat × String))
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
      (inventory : List (Carbohydrate1996ScopeParent.AbbreviationGroup ×
        Carbohydrate1996ScopeParent.AbbreviationData))
  | parentCriteriaAppliedUntilDecision
      (inventory : List Carbohydrate1996ScopeParent.ParentCriterion)
  | preferredFunctionalGroupFirst
  | greatestPreferredFunctionOccurrenceCount
  | exactFunctionalClassPrecedence
      (inventory : List (Carbohydrate1996ScopeParent.ParentFunctionalClass × Nat))
  | greatestCarbonChainLength
  | alphabeticalNameCriterion
  | trivialOrConfigurationalPrefixAlphabetization
  | dBeforeL
      (preferred : Carbohydrate1996ScopeParent.CarbohydrateSeries) (preferredRank : Nat)
      (other : Carbohydrate1996ScopeParent.CarbohydrateSeries) (otherRank : Nat)
  | alphaBeforeBeta
      (preferred : Carbohydrate1996ScopeParent.CarbohydrateAnomer) (preferredRank : Nat)
      (other : Carbohydrate1996ScopeParent.CarbohydrateAnomer) (otherRank : Nat)
  | greatestPrefixSubstituentCount
  | bridgingSubstitutionCountsMultiple
      (ordinaryPositions bridgingPositions : List Nat) (count : Nat)
  | lowestSubstituentLocantSet
  | lowestFirstCitedSubstituentLocant
  | branchedStructuresRouteToTwoCarbEighteen (route : String)
  | uronicPotentialAldehydeRemainsPrincipal
  | carbohydrateIntegrityCanOverrideGeneralPreference
  | acyclicParentStructureGroundsName
  | chartsProvideTrivialNamesThroughSixCarbons (maximumCarbonCount : Nat)
  | systematicProceduresDelegatedToEightAndTen (routes : List String)
  | chartIShowsOnlyDAndLIsMirror
      (shown mirror : Carbohydrate1996ScopeParent.CarbohydrateSeries)
  | boldChartChainDefinesConfigurationalPrefix
  | parentCarbonsNumberedConsecutively
  | potentialAldehydeReceivesLocantOne (locant : Nat)
  | aldehydeLocantOneEvenWithSeniorFunction (locant : Nat)
  | nextSeniorSuffixFunctionLowestLocant
  | carboxylicAcidPrecedesKetonicCarbonyl
      (acidRank carbonylRank : Nat)
  | parentNameAlphabeticalIncludingConfigPrefix
  | trivialNamePreferenceBoundary
  | symmetricDerivativeCriteriaOrdered
      (inventory : List Carbohydrate1996ScopeParent.ParentCriterion)
  | symmetricDerivativeDBeforeL
      (preferred : Carbohydrate1996ScopeParent.CarbohydrateSeries)
  | symmetricDerivativeLowestLocantSet
  | symmetricDerivativeLowestFirstAlphabeticLocant
  | abbreviation
      (group : Carbohydrate1996ScopeParent.AbbreviationGroup)
      (data : Carbohydrate1996ScopeParent.AbbreviationData)
  | parentChoiceExample
      (exampleRow : Carbohydrate1996ScopeParent.ParentChoiceExample)
      (data : Carbohydrate1996ScopeParent.ParentChoiceExampleData)
  deriving Repr

def abbreviationInventory :
    List (Carbohydrate1996ScopeParent.AbbreviationGroup ×
      Carbohydrate1996ScopeParent.AbbreviationData) :=
  Carbohydrate1996ScopeParent.AbbreviationGroup.all.map fun group => (group, group.data)

def sourceAssertion : Carbohydrate1996ScopeParent.Provision → SourceAssertion
  | .replaces1969TentativeRules => .replaces1969TentativeRules
  | .replacesEarlierSpecialistDocuments => .replacesEarlierSpecialistDocuments
  | .relatedRecommendationsNotIncorporated => .relatedRecommendationsNotIncorporated
  | .scopeMonosaccharidesDerivativesOligoPoly =>
      .scopeMonosaccharidesDerivativesOligoPoly carbohydrateClassInventory
  | .additionalToGeneralOrganicRules => .additionalToGeneralOrganicRules
  | .carbohydrateGenericClassInventory =>
      .carbohydrateGenericClassInventory carbohydrateClassInventory
  | .carbohydrateDerivativeOperations => .carbohydrateDerivativeOperations
  | .sugarTermUsage => .sugarTermUsage
  | .cyclitolsGenerallyExcluded => .cyclitolsGenerallyExcluded
  | .parentMonosaccharideMinimumAndFunctions => .parentMonosaccharideMinimumAndFunctions
  | .monosaccharideIsSingleUnglycosylatedUnit => .monosaccharideIsSingleUnglycosylatedUnit
  | .monosaccharideClassInventory => .monosaccharideClassInventory [.monosaccharide]
  | .monosaccharideRequiresPotentialCarbonyl => .monosaccharideRequiresPotentialCarbonyl
  | .aldoseDefinition => .aldoseDefinition .aldose
  | .ketoseDefinition => .ketoseDefinition .ketose
  | .potentialCarbonylDefinitions => .potentialCarbonylDefinitions potentialCarbonylInventory
  | .furanoseFiveMembered => .furanoseFiveMembered .furanose 5
  | .pyranoseSixMembered => .pyranoseSixMembered .pyranose 6
  | .otherRingSizesRouteToTwoCarbFive => .otherRingSizesRouteToTwoCarbFive "2-Carb-5"
  | .dialdoseDefinition => .dialdoseDefinition .dialdose
  | .diketoseDefinition => .diketoseDefinition .diketose
  | .ketoaldoseDefinition => .ketoaldoseDefinition .ketoaldose
  | .ketoaldoseTermPreferred => .ketoaldoseTermPreferred
  | .deoxySugarDefinition => .deoxySugarDefinition
  | .aminoSugarDefinition => .aminoSugarDefinition
  | .glycosylamineDefinition => .glycosylamineDefinition
  | .alditolDefinition => .alditolDefinition
  | .aldonicAcidDefinition => .aldonicAcidDefinition .aldonicAcid
  | .ketoaldonicAcidDefinition => .ketoaldonicAcidDefinition .ketoaldonicAcid
  | .uronicAcidDefinition => .uronicAcidDefinition .uronicAcid
  | .aldaricAcidDefinition => .aldaricAcidDefinition .aldaricAcid
  | .glycosideDefinition => .glycosideDefinition
  | .glycosidicBondDefinition => .glycosidicBondDefinition
  | .glycosideExtendedDefinitionRoute => .glycosideExtendedDefinitionRoute "2-Carb-33"
  | .oligosaccharideDefinition => .oligosaccharideDefinition
  | .oligosaccharideUnitCountNames =>
      .oligosaccharideUnitCountNames oligosaccharideUnitCountInventory
  | .oligoPolyBoundaryNotStrict => .oligoPolyBoundaryNotStrict
  | .oligoUsuallyDefinedStructure => .oligoUsuallyDefinedStructure
  | .nonglycosidicOligoAnalogues => .nonglycosidicOligoAnalogues
  | .polysaccharideDefinition => .polysaccharideDefinition
  | .polyGlycoseNotFullSynonym => .polyGlycoseNotFullSynonym
  | .aminoSugarPolymerTerminology => .aminoSugarPolymerTerminology
  | .homoAndHeteropolysaccharideClasses => .homoAndHeteropolysaccharideClasses
  | .glycanCanMeanGlycoproteinSaccharide => .glycanCanMeanGlycoproteinSaccharide
  | .mixedGlycosidicPhosphateUsage => .mixedGlycosidicPhosphateUsage
  | .exampleInitialCapitalConvention => .exampleInitialCapitalConvention
  | .structuralFormulaAbbreviationInventory =>
      .structuralFormulaAbbreviationInventory abbreviationInventory
  | .parentCriteriaAppliedUntilDecision =>
      .parentCriteriaAppliedUntilDecision parentCriterionInventory
  | .preferredFunctionalGroupFirst => .preferredFunctionalGroupFirst
  | .greatestPreferredFunctionOccurrenceCount => .greatestPreferredFunctionOccurrenceCount
  | .exactFunctionalClassPrecedence =>
      .exactFunctionalClassPrecedence parentFunctionalClassInventory
  | .greatestCarbonChainLength => .greatestCarbonChainLength
  | .alphabeticalNameCriterion => .alphabeticalNameCriterion
  | .trivialOrConfigurationalPrefixAlphabetization =>
      .trivialOrConfigurationalPrefixAlphabetization
  | .dBeforeL =>
      .dBeforeL .D (Carbohydrate1996ScopeParent.seriesPreference .D)
        .L (Carbohydrate1996ScopeParent.seriesPreference .L)
  | .alphaBeforeBeta =>
      .alphaBeforeBeta .alpha (Carbohydrate1996ScopeParent.anomerPreference .alpha)
        .beta (Carbohydrate1996ScopeParent.anomerPreference .beta)
  | .greatestPrefixSubstituentCount => .greatestPrefixSubstituentCount
  | .bridgingSubstitutionCountsMultiple =>
      .bridgingSubstitutionCountsMultiple [] [2, 3]
        (Carbohydrate1996ScopeParent.prefixSubstitutionCount [] [2, 3])
  | .lowestSubstituentLocantSet => .lowestSubstituentLocantSet
  | .lowestFirstCitedSubstituentLocant => .lowestFirstCitedSubstituentLocant
  | .branchedStructuresRouteToTwoCarbEighteen =>
      .branchedStructuresRouteToTwoCarbEighteen "2-Carb-18"
  | .uronicPotentialAldehydeRemainsPrincipal => .uronicPotentialAldehydeRemainsPrincipal
  | .carbohydrateIntegrityCanOverrideGeneralPreference =>
      .carbohydrateIntegrityCanOverrideGeneralPreference
  | .acyclicParentStructureGroundsName => .acyclicParentStructureGroundsName
  | .chartsProvideTrivialNamesThroughSixCarbons =>
      .chartsProvideTrivialNamesThroughSixCarbons 6
  | .systematicProceduresDelegatedToEightAndTen =>
      .systematicProceduresDelegatedToEightAndTen ["2-Carb-8", "2-Carb-10"]
  | .chartIShowsOnlyDAndLIsMirror => .chartIShowsOnlyDAndLIsMirror .D .L
  | .boldChartChainDefinesConfigurationalPrefix => .boldChartChainDefinesConfigurationalPrefix
  | .parentCarbonsNumberedConsecutively => .parentCarbonsNumberedConsecutively
  | .potentialAldehydeReceivesLocantOne => .potentialAldehydeReceivesLocantOne 1
  | .aldehydeLocantOneEvenWithSeniorFunction => .aldehydeLocantOneEvenWithSeniorFunction 1
  | .nextSeniorSuffixFunctionLowestLocant => .nextSeniorSuffixFunctionLowestLocant
  | .carboxylicAcidPrecedesKetonicCarbonyl =>
      .carboxylicAcidPrecedesKetonicCarbonyl
        (Carbohydrate1996ScopeParent.ParentFunctionalClass.aldonicAcid.rank)
        (Carbohydrate1996ScopeParent.ParentFunctionalClass.ketose.rank)
  | .parentNameAlphabeticalIncludingConfigPrefix => .parentNameAlphabeticalIncludingConfigPrefix
  | .trivialNamePreferenceBoundary => .trivialNamePreferenceBoundary
  | .symmetricDerivativeCriteriaOrdered =>
      .symmetricDerivativeCriteriaOrdered symmetricDerivativeCriterionInventory
  | .symmetricDerivativeDBeforeL => .symmetricDerivativeDBeforeL .D
  | .symmetricDerivativeLowestLocantSet => .symmetricDerivativeLowestLocantSet
  | .symmetricDerivativeLowestFirstAlphabeticLocant =>
      .symmetricDerivativeLowestFirstAlphabeticLocant
  | .abbreviation group => .abbreviation group group.data
  | .parentChoiceExample exampleRow => .parentChoiceExample exampleRow exampleRow.data

def SourceAssertion.provision : SourceAssertion → Carbohydrate1996ScopeParent.Provision
  | .replaces1969TentativeRules => .replaces1969TentativeRules
  | .replacesEarlierSpecialistDocuments => .replacesEarlierSpecialistDocuments
  | .relatedRecommendationsNotIncorporated => .relatedRecommendationsNotIncorporated
  | .scopeMonosaccharidesDerivativesOligoPoly _ => .scopeMonosaccharidesDerivativesOligoPoly
  | .additionalToGeneralOrganicRules => .additionalToGeneralOrganicRules
  | .carbohydrateGenericClassInventory _ => .carbohydrateGenericClassInventory
  | .carbohydrateDerivativeOperations => .carbohydrateDerivativeOperations
  | .sugarTermUsage => .sugarTermUsage
  | .cyclitolsGenerallyExcluded => .cyclitolsGenerallyExcluded
  | .parentMonosaccharideMinimumAndFunctions => .parentMonosaccharideMinimumAndFunctions
  | .monosaccharideIsSingleUnglycosylatedUnit => .monosaccharideIsSingleUnglycosylatedUnit
  | .monosaccharideClassInventory _ => .monosaccharideClassInventory
  | .monosaccharideRequiresPotentialCarbonyl => .monosaccharideRequiresPotentialCarbonyl
  | .aldoseDefinition _ => .aldoseDefinition
  | .ketoseDefinition _ => .ketoseDefinition
  | .potentialCarbonylDefinitions _ => .potentialCarbonylDefinitions
  | .furanoseFiveMembered _ _ => .furanoseFiveMembered
  | .pyranoseSixMembered _ _ => .pyranoseSixMembered
  | .otherRingSizesRouteToTwoCarbFive _ => .otherRingSizesRouteToTwoCarbFive
  | .dialdoseDefinition _ => .dialdoseDefinition
  | .diketoseDefinition _ => .diketoseDefinition
  | .ketoaldoseDefinition _ => .ketoaldoseDefinition
  | .ketoaldoseTermPreferred => .ketoaldoseTermPreferred
  | .deoxySugarDefinition => .deoxySugarDefinition
  | .aminoSugarDefinition => .aminoSugarDefinition
  | .glycosylamineDefinition => .glycosylamineDefinition
  | .alditolDefinition => .alditolDefinition
  | .aldonicAcidDefinition _ => .aldonicAcidDefinition
  | .ketoaldonicAcidDefinition _ => .ketoaldonicAcidDefinition
  | .uronicAcidDefinition _ => .uronicAcidDefinition
  | .aldaricAcidDefinition _ => .aldaricAcidDefinition
  | .glycosideDefinition => .glycosideDefinition
  | .glycosidicBondDefinition => .glycosidicBondDefinition
  | .glycosideExtendedDefinitionRoute _ => .glycosideExtendedDefinitionRoute
  | .oligosaccharideDefinition => .oligosaccharideDefinition
  | .oligosaccharideUnitCountNames _ => .oligosaccharideUnitCountNames
  | .oligoPolyBoundaryNotStrict => .oligoPolyBoundaryNotStrict
  | .oligoUsuallyDefinedStructure => .oligoUsuallyDefinedStructure
  | .nonglycosidicOligoAnalogues => .nonglycosidicOligoAnalogues
  | .polysaccharideDefinition => .polysaccharideDefinition
  | .polyGlycoseNotFullSynonym => .polyGlycoseNotFullSynonym
  | .aminoSugarPolymerTerminology => .aminoSugarPolymerTerminology
  | .homoAndHeteropolysaccharideClasses => .homoAndHeteropolysaccharideClasses
  | .glycanCanMeanGlycoproteinSaccharide => .glycanCanMeanGlycoproteinSaccharide
  | .mixedGlycosidicPhosphateUsage => .mixedGlycosidicPhosphateUsage
  | .exampleInitialCapitalConvention => .exampleInitialCapitalConvention
  | .structuralFormulaAbbreviationInventory _ => .structuralFormulaAbbreviationInventory
  | .parentCriteriaAppliedUntilDecision _ => .parentCriteriaAppliedUntilDecision
  | .preferredFunctionalGroupFirst => .preferredFunctionalGroupFirst
  | .greatestPreferredFunctionOccurrenceCount => .greatestPreferredFunctionOccurrenceCount
  | .exactFunctionalClassPrecedence _ => .exactFunctionalClassPrecedence
  | .greatestCarbonChainLength => .greatestCarbonChainLength
  | .alphabeticalNameCriterion => .alphabeticalNameCriterion
  | .trivialOrConfigurationalPrefixAlphabetization => .trivialOrConfigurationalPrefixAlphabetization
  | .dBeforeL _ _ _ _ => .dBeforeL
  | .alphaBeforeBeta _ _ _ _ => .alphaBeforeBeta
  | .greatestPrefixSubstituentCount => .greatestPrefixSubstituentCount
  | .bridgingSubstitutionCountsMultiple _ _ _ => .bridgingSubstitutionCountsMultiple
  | .lowestSubstituentLocantSet => .lowestSubstituentLocantSet
  | .lowestFirstCitedSubstituentLocant => .lowestFirstCitedSubstituentLocant
  | .branchedStructuresRouteToTwoCarbEighteen _ => .branchedStructuresRouteToTwoCarbEighteen
  | .uronicPotentialAldehydeRemainsPrincipal => .uronicPotentialAldehydeRemainsPrincipal
  | .carbohydrateIntegrityCanOverrideGeneralPreference =>
      .carbohydrateIntegrityCanOverrideGeneralPreference
  | .acyclicParentStructureGroundsName => .acyclicParentStructureGroundsName
  | .chartsProvideTrivialNamesThroughSixCarbons _ => .chartsProvideTrivialNamesThroughSixCarbons
  | .systematicProceduresDelegatedToEightAndTen _ => .systematicProceduresDelegatedToEightAndTen
  | .chartIShowsOnlyDAndLIsMirror _ _ => .chartIShowsOnlyDAndLIsMirror
  | .boldChartChainDefinesConfigurationalPrefix => .boldChartChainDefinesConfigurationalPrefix
  | .parentCarbonsNumberedConsecutively => .parentCarbonsNumberedConsecutively
  | .potentialAldehydeReceivesLocantOne _ => .potentialAldehydeReceivesLocantOne
  | .aldehydeLocantOneEvenWithSeniorFunction _ => .aldehydeLocantOneEvenWithSeniorFunction
  | .nextSeniorSuffixFunctionLowestLocant => .nextSeniorSuffixFunctionLowestLocant
  | .carboxylicAcidPrecedesKetonicCarbonyl _ _ => .carboxylicAcidPrecedesKetonicCarbonyl
  | .parentNameAlphabeticalIncludingConfigPrefix => .parentNameAlphabeticalIncludingConfigPrefix
  | .trivialNamePreferenceBoundary => .trivialNamePreferenceBoundary
  | .symmetricDerivativeCriteriaOrdered _ => .symmetricDerivativeCriteriaOrdered
  | .symmetricDerivativeDBeforeL _ => .symmetricDerivativeDBeforeL
  | .symmetricDerivativeLowestLocantSet => .symmetricDerivativeLowestLocantSet
  | .symmetricDerivativeLowestFirstAlphabeticLocant =>
      .symmetricDerivativeLowestFirstAlphabeticLocant
  | .abbreviation group _ => .abbreviation group
  | .parentChoiceExample exampleRow _ => .parentChoiceExample exampleRow

@[simp] theorem sourceAssertion_provision_exact (row : Carbohydrate1996ScopeParent.Provision) :
    (sourceAssertion row).provision = row := by
  cases row <;> rfl

structure SourceMeaning where
  sourceKey : String
  semanticDomain : SemanticDomain
  assertion : SourceAssertion
  deriving Repr

def sourceMeaning (row : Carbohydrate1996ScopeParent.Provision) : SourceMeaning :=
  ⟨row.sourceKey, semanticDomain row, sourceAssertion row⟩

@[simp] theorem sourceMeaning_key_exact (row : Carbohydrate1996ScopeParent.Provision) :
    (sourceMeaning row).sourceKey = row.sourceKey := by
  rfl

@[simp] theorem sourceMeaning_domain_exact (row : Carbohydrate1996ScopeParent.Provision) :
    (sourceMeaning row).semanticDomain = semanticDomain row := by
  rfl

theorem sourceMeaning_injective : Function.Injective sourceMeaning := by
  intro left right equal
  have assertionEqual : (sourceMeaning left).assertion = (sourceMeaning right).assertion :=
    congrArg SourceMeaning.assertion equal
  have provisionEqual := congrArg SourceAssertion.provision assertionEqual
  simpa [sourceMeaning] using provisionEqual

def fullFamilyRows : List Carbohydrate1996ScopeParent.Provision :=
  Carbohydrate1996ScopeParent.Provision.all

def fullFamilyProvisions : List IUPACNormativeProvision :=
  fullFamilyRows.map IUPACNormativeProvision.carbohydrate1996ScopeParent

def completionRows : List Carbohydrate1996ScopeParent.Provision :=
  Carbohydrate1996ScopeParent.Provision.base

def completionProvisions : List IUPACNormativeProvision :=
  completionRows.map IUPACNormativeProvision.carbohydrate1996ScopeParent

def completionBatch : GlobalNonDescriptorSourceMeaningBatch completionProvisions :=
  totalMeaningBatch completionRows IUPACNormativeProvision.carbohydrate1996ScopeParent sourceMeaning
    (by intro _row; rfl)

@[simp] theorem full_family_provisions_exact :
    fullFamilyProvisions = carbohydrate1996ScopeParentSemanticsSlice := by
  rfl

@[simp] theorem full_family_provision_count : fullFamilyProvisions.length = 95 := by
  simp [fullFamilyProvisions, fullFamilyRows]

@[simp] theorem completion_provision_count : completionProvisions.length = 79 := by
  simp [completionProvisions, completionRows, Carbohydrate1996ScopeParent.Provision.base]

@[simp] theorem completion_entry_count : completionBatch.entries.length = 79 := by
  rw [completionBatch.entries_length, completion_provision_count]

private theorem completion_rows_then_indexed_exact :
    completionRows ++ GlobalNonDescriptorIndexedSourceData.carbohydrateScopeParentRows =
      fullFamilyRows := by
  simp [completionRows, fullFamilyRows,
    GlobalNonDescriptorIndexedSourceData.carbohydrateScopeParentRows,
    Carbohydrate1996ScopeParent.Provision.all, List.append_assoc]

theorem completion_then_indexed_exact_source_order :
    completionProvisions ++
      GlobalNonDescriptorIndexedSourceData.carbohydrateScopeParentProvisions =
        carbohydrate1996ScopeParentSemanticsSlice := by
  rw [← full_family_provisions_exact]
  simp only [completionProvisions,
    GlobalNonDescriptorIndexedSourceData.carbohydrateScopeParentProvisions,
    fullFamilyProvisions, ← List.map_append]
  rw [completion_rows_then_indexed_exact]

theorem materialized_order_perm_source :
    (GlobalNonDescriptorIndexedSourceData.carbohydrateScopeParentProvisions ++
      completionProvisions).Perm carbohydrate1996ScopeParentSemanticsSlice := by
  calc
    (GlobalNonDescriptorIndexedSourceData.carbohydrateScopeParentProvisions ++
      completionProvisions).Perm
        (completionProvisions ++
          GlobalNonDescriptorIndexedSourceData.carbohydrateScopeParentProvisions) :=
      List.perm_append_comm
    _ = carbohydrate1996ScopeParentSemanticsSlice :=
      completion_then_indexed_exact_source_order

theorem completion_disjoint_indexed :
    completionProvisions.Disjoint
      GlobalNonDescriptorIndexedSourceData.carbohydrateScopeParentProvisions := by
  apply List.disjoint_of_nodup_append
  rw [completion_then_indexed_exact_source_order]
  exact Carbohydrate1996ScopeParent.Provision.all_nodup.map
    (by intro left right equal; cases equal; rfl)

theorem completion_provisions_nodup : completionProvisions.Nodup := by
  exact Carbohydrate1996ScopeParent.Provision.all_nodup.of_append_left.of_append_left.map
    (by intro left right equal; cases equal; rfl)

@[simp] theorem completion_entry_provisions_exact :
    completionBatch.entries.map GlobalNonDescriptorSourceMeaningEntry.provision =
      completionProvisions :=
  completionBatch.provisions_exact

theorem every_completion_entry_nonvacuous
    (entry : GlobalNonDescriptorSourceMeaningEntry) (_member : entry ∈ completionBatch.entries) :
    ∃ input, ∃ observation : entry.reference.toReference.Observation,
      input.StructurallyWellFormed ∧
        entry.reference.toReference.Applicable input ∧
          entry.reference.toReference.Judges input observation :=
  entry.admittedJudgment

theorem source_audit_still_open :
    ¬IUPACNormativeSource.ProvisionAuditComplete .carbohydrateRecommendations1996 := by
  exact IUPACNormativeSource.provisionAuditIncomplete_of_figure_review_open _ rfl

end GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.full_family_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completion_then_indexed_exact_source_order
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.materialized_order_perm_source
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.sourceMeaning_injective
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.completion_entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.every_completion_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateScopeParentSourceMeaning.source_audit_still_open
