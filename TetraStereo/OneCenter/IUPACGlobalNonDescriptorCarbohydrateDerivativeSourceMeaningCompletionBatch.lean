import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceDataBatch
import TetraStereo.KernelOnly

set_option autoImplicit false











namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning

open GlobalNonDescriptorIndexedSourceData

inductive SemanticDomain where
  | deoxySugar
  | aminoSugar
  | chalcogenAnalogue
  | carbonSubstitution
  | isotopeNotation
  | printedExample
  deriving DecidableEq, Repr

def semanticDomain : Carbohydrate1996Derivatives.Provision → SemanticDomain
  | .establishedDeoxyTrivialNames | .deoxyTrivialNamesRetainedForUnmodifiedSugars
  | .systematicDeoxyNamesPreferredForDerivatives | .otherUsedDeoxyTrivialNames
  | .terminalMethylIsOmegaDeoxyNotCMethyl | .deoxyWithTrivialNameWhenNoCenterRemoved
  | .deoxyRemovalOfCenterCreatesRedundancy | .systematicPreferredWhenCenterRemoved
  | .commonTwoDeoxyNames | .systematicDeoxyLocantPrefixStem
  | .deoxyPrefixesDescribePresentCenters | .configurationalPrefixesCitedFarthestFromC1
  | .deoxyIsDetachableAlphabetizedPrefix | .detachablePracticeConflictsGeneralGuide
  | .methyleneInterruptionIgnored | .prefixCoversEntireRemainingCenterSequence
  | .anomericHydroxyToHydrogenRoutesToAnhydroAlditol
  | .terminalAldehydeToMethylUsesDeoxyAlditol | .fucitolAndRhamnitolFrequent
  | .deoxyTrivialName _ => .deoxySugar
  | .aminoReplacementIsSubstitutionOnDeoxySugar | .aminoEquivalentToHydroxyForConfiguration
  | .nSubstitutedTreatmentRoutesToTwoCarbTwentyFive | .acceptedAminoTrivialNames
  | .neuraminicAndMuramicNamesSpecificallyD | .nonexistentParentAminoNamesNotRecommended
  | .ringNitrogenRoutesToTwoCarbThirtyFour | .systematicAminoUsesDeoxyAndAminoPrefixes
  | .aminoDeoxyAlphabetization | .anomericAminoNormallyGlycosylamine
  | .aminoTrivialName _ => .aminoSugar
  | .hydroxyOrCarbonylOxygenToSulfurUsesThio
  | .ringOxygenToSulfurUsesAdjacentNonanomericLocant
  | .seleniumAndTelluriumUseSelenoTelluro | .chalcogenOxidesMayUseFunctionalClassNames
  | .thioNotThia | .thioCommonlyTreatedAsDetachable => .chalcogenAnalogue
  | .nonterminalHydrogenReplacementIsCSubstitution
  | .highestCIPPriorityGroupEquivalentToHydroxy | .ambiguousModifiedCenterUsesRS
  | .nonanomericHydroxyReplacementUsesDeoxyParent | .replacingGroupDeterminesConfiguration
  | .hydroxyReplacementAmbiguityUsesRS | .cLocantRequiredOnlyForAmbiguityButMayEmphasize
  | .unequalSubstitutionUsesDisubstitutedDeoxyParent
  | .unequalHigherCIPGroupEquivalentToHydroxy | .unequalSubstitutionAmbiguityUsesRS
  | .terminalCreatedCenterUsesRS | .terminalMethylStillDeoxyNotCMethyl
  | .aldehydicHydrogenRingReplacementUsesCPrefix | .iminoAnalogueMayUseIminoDeoxyAlditol
  | .oximesAndHydrazonesNamedDirectly | .arylosazonePrefersKetoaldoseBisHydrazone
  | .oxidizedArylosazoneMayUseTriazolylAlditol => .carbonSubstitution
  | .isotopeRulesDelegatedToSectionH | .isotopeParenthesesVsLabellingBrackets
  | .uniformLabellingUsesU | .isotopeCreatedCenterFollowsSubstitutionRules => .isotopeNotation
  | .printedExample _ => .printedExample

def deoxyTrivialNameInventory :
    List (Carbohydrate1996Derivatives.DeoxyTrivialNameRow ×
      Carbohydrate1996Derivatives.DeoxyTrivialNameData) :=
  Carbohydrate1996Derivatives.DeoxyTrivialNameRow.all.map fun row => (row, row.data)

def aminoTrivialNameInventory :
    List (Carbohydrate1996Derivatives.AminoTrivialNameRow ×
      Carbohydrate1996Derivatives.AminoTrivialNameData) :=
  Carbohydrate1996Derivatives.AminoTrivialNameRow.all.map fun row => (row, row.data)

def printedExampleInventory :
    List (Carbohydrate1996Derivatives.PrintedExample ×
      Carbohydrate1996Derivatives.PrintedExampleData) :=
  Carbohydrate1996Derivatives.PrintedExample.all.map fun row => (row, row.data)

def substitutionSurrogateInventory :
    List (Carbohydrate1996Derivatives.ModificationKind ×
      Carbohydrate1996Derivatives.ConfigurationSurrogate) :=
  [ (.aminoForHydroxy, Carbohydrate1996Derivatives.configurationSurrogate .aminoForHydroxy)
  , (.replaceHydroxy, Carbohydrate1996Derivatives.configurationSurrogate .replaceHydroxy)
  , (.addSubstituentToCarbon,
      Carbohydrate1996Derivatives.configurationSurrogate .addSubstituentToCarbon)
  , (.unequalDoubleSubstitution,
      Carbohydrate1996Derivatives.configurationSurrogate .unequalDoubleSubstitution) ]

def remainingConfigurationExample :
    List (Option Carbohydrate1996NamedParents.FischerSide) :=
  [some .left, some .right, none, some .right, some .left]

def chalcogenPrefixInventory :
    List (Carbohydrate1996Derivatives.Chalcogen × String) :=
  [ (.sulfur, Carbohydrate1996Derivatives.Chalcogen.sulfur.replacementPrefix)
  , (.selenium, Carbohydrate1996Derivatives.Chalcogen.selenium.replacementPrefix)
  , (.tellurium, Carbohydrate1996Derivatives.Chalcogen.tellurium.replacementPrefix) ]

def halogenAtomicNumberInventory : List (String × Option Nat) :=
  [ ("Cl", Carbohydrate1996Derivatives.atomicNumber "Cl")
  , ("Br", Carbohydrate1996Derivatives.atomicNumber "Br") ]

def isotopeDelimiterInventory :
    List (Carbohydrate1996Derivatives.IsotopeNotation × (String × String)) :=
  [ (.substitution, Carbohydrate1996Derivatives.IsotopeNotation.substitution.delimiters)
  , (.labelling, Carbohydrate1996Derivatives.IsotopeNotation.labelling.delimiters) ]

inductive SourceAssertion where
  | establishedDeoxyTrivialNames
      (inventory : List (Carbohydrate1996Derivatives.DeoxyTrivialNameRow ×
        Carbohydrate1996Derivatives.DeoxyTrivialNameData))
  | deoxyTrivialNamesRetainedForUnmodifiedSugars
      (inventory : List (Carbohydrate1996Derivatives.DeoxyTrivialNameRow ×
        Carbohydrate1996Derivatives.DeoxyTrivialNameData))
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
      (positions : List (Option Carbohydrate1996NamedParents.FischerSide))
      (sides : List Carbohydrate1996NamedParents.FischerSide)
  | prefixCoversEntireRemainingCenterSequence
      (positions : List (Option Carbohydrate1996NamedParents.FischerSide))
      (sides : List Carbohydrate1996NamedParents.FischerSide)
  | anomericHydroxyToHydrogenRoutesToAnhydroAlditol (route : String)
  | terminalAldehydeToMethylUsesDeoxyAlditol
  | fucitolAndRhamnitolFrequent
  | aminoReplacementIsSubstitutionOnDeoxySugar
  | aminoEquivalentToHydroxyForConfiguration
      (kind : Carbohydrate1996Derivatives.ModificationKind)
      (surrogate : Carbohydrate1996Derivatives.ConfigurationSurrogate)
  | nSubstitutedTreatmentRoutesToTwoCarbTwentyFive (route : String)
  | acceptedAminoTrivialNames
      (inventory : List (Carbohydrate1996Derivatives.AminoTrivialNameRow ×
        Carbohydrate1996Derivatives.AminoTrivialNameData))
  | neuraminicAndMuramicNamesSpecificallyD
      (rows : List Carbohydrate1996Derivatives.AminoTrivialNameRow)
  | nonexistentParentAminoNamesNotRecommended
  | ringNitrogenRoutesToTwoCarbThirtyFour (route : String)
  | systematicAminoUsesDeoxyAndAminoPrefixes
  | aminoDeoxyAlphabetization
  | anomericAminoNormallyGlycosylamine
  | hydroxyOrCarbonylOxygenToSulfurUsesThio
      (prefixName : String)
  | ringOxygenToSulfurUsesAdjacentNonanomericLocant
  | seleniumAndTelluriumUseSelenoTelluro
      (inventory : List (Carbohydrate1996Derivatives.Chalcogen × String))
  | chalcogenOxidesMayUseFunctionalClassNames
  | thioNotThia (prefixName : String)
  | thioCommonlyTreatedAsDetachable
  | nonterminalHydrogenReplacementIsCSubstitution
  | highestCIPPriorityGroupEquivalentToHydroxy
      (inventory : List (Carbohydrate1996Derivatives.ModificationKind ×
        Carbohydrate1996Derivatives.ConfigurationSurrogate))
  | ambiguousModifiedCenterUsesRS (createsCenter ambiguous result : Bool)
  | nonanomericHydroxyReplacementUsesDeoxyParent
  | replacingGroupDeterminesConfiguration
      (kind : Carbohydrate1996Derivatives.ModificationKind)
      (surrogate : Carbohydrate1996Derivatives.ConfigurationSurrogate)
  | hydroxyReplacementAmbiguityUsesRS (createsCenter ambiguous result : Bool)
  | cLocantRequiredOnlyForAmbiguityButMayEmphasize
  | unequalSubstitutionUsesDisubstitutedDeoxyParent
  | unequalHigherCIPGroupEquivalentToHydroxy
      (kind : Carbohydrate1996Derivatives.ModificationKind)
      (surrogate : Carbohydrate1996Derivatives.ConfigurationSurrogate)
  | unequalSubstitutionAmbiguityUsesRS (createsCenter ambiguous result : Bool)
  | terminalCreatedCenterUsesRS (createsCenter ambiguous result : Bool)
  | terminalMethylStillDeoxyNotCMethyl
  | aldehydicHydrogenRingReplacementUsesCPrefix
  | iminoAnalogueMayUseIminoDeoxyAlditol
  | oximesAndHydrazonesNamedDirectly
  | arylosazonePrefersKetoaldoseBisHydrazone
  | oxidizedArylosazoneMayUseTriazolylAlditol
  | isotopeRulesDelegatedToSectionH (route : String)
  | isotopeParenthesesVsLabellingBrackets
      (inventory : List (Carbohydrate1996Derivatives.IsotopeNotation × (String × String)))
  | uniformLabellingUsesU (symbol : String)
  | isotopeCreatedCenterFollowsSubstitutionRules (createsCenter ambiguous result : Bool)
  | deoxyTrivialName (row : Carbohydrate1996Derivatives.DeoxyTrivialNameRow)
      (data : Carbohydrate1996Derivatives.DeoxyTrivialNameData)
  | aminoTrivialName (row : Carbohydrate1996Derivatives.AminoTrivialNameRow)
      (data : Carbohydrate1996Derivatives.AminoTrivialNameData)
  | printedExample (row : Carbohydrate1996Derivatives.PrintedExample)
      (data : Carbohydrate1996Derivatives.PrintedExampleData)
  deriving Repr

def sourceAssertion : Carbohydrate1996Derivatives.Provision → SourceAssertion
  | .establishedDeoxyTrivialNames => .establishedDeoxyTrivialNames deoxyTrivialNameInventory
  | .deoxyTrivialNamesRetainedForUnmodifiedSugars =>
      .deoxyTrivialNamesRetainedForUnmodifiedSugars deoxyTrivialNameInventory
  | .systematicDeoxyNamesPreferredForDerivatives => .systematicDeoxyNamesPreferredForDerivatives
  | .otherUsedDeoxyTrivialNames => .otherUsedDeoxyTrivialNames
  | .terminalMethylIsOmegaDeoxyNotCMethyl => .terminalMethylIsOmegaDeoxyNotCMethyl
  | .deoxyWithTrivialNameWhenNoCenterRemoved => .deoxyWithTrivialNameWhenNoCenterRemoved
  | .deoxyRemovalOfCenterCreatesRedundancy => .deoxyRemovalOfCenterCreatesRedundancy
  | .systematicPreferredWhenCenterRemoved => .systematicPreferredWhenCenterRemoved
  | .commonTwoDeoxyNames => .commonTwoDeoxyNames
  | .systematicDeoxyLocantPrefixStem => .systematicDeoxyLocantPrefixStem
  | .deoxyPrefixesDescribePresentCenters => .deoxyPrefixesDescribePresentCenters
  | .configurationalPrefixesCitedFarthestFromC1 =>
      .configurationalPrefixesCitedFarthestFromC1
  | .deoxyIsDetachableAlphabetizedPrefix => .deoxyIsDetachableAlphabetizedPrefix
  | .detachablePracticeConflictsGeneralGuide => .detachablePracticeConflictsGeneralGuide
  | .methyleneInterruptionIgnored =>
      .methyleneInterruptionIgnored remainingConfigurationExample
        (Carbohydrate1996Derivatives.remainingConfigurationSides remainingConfigurationExample)
  | .prefixCoversEntireRemainingCenterSequence =>
      .prefixCoversEntireRemainingCenterSequence remainingConfigurationExample
        (Carbohydrate1996Derivatives.remainingConfigurationSides remainingConfigurationExample)
  | .anomericHydroxyToHydrogenRoutesToAnhydroAlditol =>
      .anomericHydroxyToHydrogenRoutesToAnhydroAlditol "2-Carb-26"
  | .terminalAldehydeToMethylUsesDeoxyAlditol => .terminalAldehydeToMethylUsesDeoxyAlditol
  | .fucitolAndRhamnitolFrequent => .fucitolAndRhamnitolFrequent
  | .aminoReplacementIsSubstitutionOnDeoxySugar => .aminoReplacementIsSubstitutionOnDeoxySugar
  | .aminoEquivalentToHydroxyForConfiguration =>
      .aminoEquivalentToHydroxyForConfiguration .aminoForHydroxy
        (Carbohydrate1996Derivatives.configurationSurrogate .aminoForHydroxy)
  | .nSubstitutedTreatmentRoutesToTwoCarbTwentyFive =>
      .nSubstitutedTreatmentRoutesToTwoCarbTwentyFive "2-Carb-25"
  | .acceptedAminoTrivialNames => .acceptedAminoTrivialNames aminoTrivialNameInventory
  | .neuraminicAndMuramicNamesSpecificallyD =>
      .neuraminicAndMuramicNamesSpecificallyD [.neuraminicAcid, .muramicAcid]
  | .nonexistentParentAminoNamesNotRecommended => .nonexistentParentAminoNamesNotRecommended
  | .ringNitrogenRoutesToTwoCarbThirtyFour => .ringNitrogenRoutesToTwoCarbThirtyFour "2-Carb-34"
  | .systematicAminoUsesDeoxyAndAminoPrefixes => .systematicAminoUsesDeoxyAndAminoPrefixes
  | .aminoDeoxyAlphabetization => .aminoDeoxyAlphabetization
  | .anomericAminoNormallyGlycosylamine => .anomericAminoNormallyGlycosylamine
  | .hydroxyOrCarbonylOxygenToSulfurUsesThio =>
      .hydroxyOrCarbonylOxygenToSulfurUsesThio
        Carbohydrate1996Derivatives.Chalcogen.sulfur.replacementPrefix
  | .ringOxygenToSulfurUsesAdjacentNonanomericLocant =>
      .ringOxygenToSulfurUsesAdjacentNonanomericLocant
  | .seleniumAndTelluriumUseSelenoTelluro =>
      .seleniumAndTelluriumUseSelenoTelluro chalcogenPrefixInventory
  | .chalcogenOxidesMayUseFunctionalClassNames => .chalcogenOxidesMayUseFunctionalClassNames
  | .thioNotThia => .thioNotThia Carbohydrate1996Derivatives.Chalcogen.sulfur.replacementPrefix
  | .thioCommonlyTreatedAsDetachable => .thioCommonlyTreatedAsDetachable
  | .nonterminalHydrogenReplacementIsCSubstitution =>
      .nonterminalHydrogenReplacementIsCSubstitution
  | .highestCIPPriorityGroupEquivalentToHydroxy =>
      .highestCIPPriorityGroupEquivalentToHydroxy substitutionSurrogateInventory
  | .ambiguousModifiedCenterUsesRS =>
      .ambiguousModifiedCenterUsesRS false true
        (Carbohydrate1996Derivatives.requiresExplicitRS false true)
  | .nonanomericHydroxyReplacementUsesDeoxyParent =>
      .nonanomericHydroxyReplacementUsesDeoxyParent
  | .replacingGroupDeterminesConfiguration =>
      .replacingGroupDeterminesConfiguration .replaceHydroxy
        (Carbohydrate1996Derivatives.configurationSurrogate .replaceHydroxy)
  | .hydroxyReplacementAmbiguityUsesRS =>
      .hydroxyReplacementAmbiguityUsesRS false true
        (Carbohydrate1996Derivatives.requiresExplicitRS false true)
  | .cLocantRequiredOnlyForAmbiguityButMayEmphasize =>
      .cLocantRequiredOnlyForAmbiguityButMayEmphasize
  | .unequalSubstitutionUsesDisubstitutedDeoxyParent =>
      .unequalSubstitutionUsesDisubstitutedDeoxyParent
  | .unequalHigherCIPGroupEquivalentToHydroxy =>
      .unequalHigherCIPGroupEquivalentToHydroxy .unequalDoubleSubstitution
        (Carbohydrate1996Derivatives.configurationSurrogate .unequalDoubleSubstitution)
  | .unequalSubstitutionAmbiguityUsesRS =>
      .unequalSubstitutionAmbiguityUsesRS false true
        (Carbohydrate1996Derivatives.requiresExplicitRS false true)
  | .terminalCreatedCenterUsesRS =>
      .terminalCreatedCenterUsesRS true false
        (Carbohydrate1996Derivatives.requiresExplicitRS true false)
  | .terminalMethylStillDeoxyNotCMethyl => .terminalMethylStillDeoxyNotCMethyl
  | .aldehydicHydrogenRingReplacementUsesCPrefix => .aldehydicHydrogenRingReplacementUsesCPrefix
  | .iminoAnalogueMayUseIminoDeoxyAlditol => .iminoAnalogueMayUseIminoDeoxyAlditol
  | .oximesAndHydrazonesNamedDirectly => .oximesAndHydrazonesNamedDirectly
  | .arylosazonePrefersKetoaldoseBisHydrazone => .arylosazonePrefersKetoaldoseBisHydrazone
  | .oxidizedArylosazoneMayUseTriazolylAlditol => .oxidizedArylosazoneMayUseTriazolylAlditol
  | .isotopeRulesDelegatedToSectionH => .isotopeRulesDelegatedToSectionH "Section H"
  | .isotopeParenthesesVsLabellingBrackets =>
      .isotopeParenthesesVsLabellingBrackets isotopeDelimiterInventory
  | .uniformLabellingUsesU => .uniformLabellingUsesU "U"
  | .isotopeCreatedCenterFollowsSubstitutionRules =>
      .isotopeCreatedCenterFollowsSubstitutionRules true false
        (Carbohydrate1996Derivatives.requiresExplicitRS true false)
  | .deoxyTrivialName row => .deoxyTrivialName row row.data
  | .aminoTrivialName row => .aminoTrivialName row row.data
  | .printedExample row => .printedExample row row.data

def SourceAssertion.provision : SourceAssertion → Carbohydrate1996Derivatives.Provision
  | .establishedDeoxyTrivialNames _ => .establishedDeoxyTrivialNames
  | .deoxyTrivialNamesRetainedForUnmodifiedSugars _ =>
      .deoxyTrivialNamesRetainedForUnmodifiedSugars
  | .systematicDeoxyNamesPreferredForDerivatives => .systematicDeoxyNamesPreferredForDerivatives
  | .otherUsedDeoxyTrivialNames => .otherUsedDeoxyTrivialNames
  | .terminalMethylIsOmegaDeoxyNotCMethyl => .terminalMethylIsOmegaDeoxyNotCMethyl
  | .deoxyWithTrivialNameWhenNoCenterRemoved => .deoxyWithTrivialNameWhenNoCenterRemoved
  | .deoxyRemovalOfCenterCreatesRedundancy => .deoxyRemovalOfCenterCreatesRedundancy
  | .systematicPreferredWhenCenterRemoved => .systematicPreferredWhenCenterRemoved
  | .commonTwoDeoxyNames => .commonTwoDeoxyNames
  | .systematicDeoxyLocantPrefixStem => .systematicDeoxyLocantPrefixStem
  | .deoxyPrefixesDescribePresentCenters => .deoxyPrefixesDescribePresentCenters
  | .configurationalPrefixesCitedFarthestFromC1 =>
      .configurationalPrefixesCitedFarthestFromC1
  | .deoxyIsDetachableAlphabetizedPrefix => .deoxyIsDetachableAlphabetizedPrefix
  | .detachablePracticeConflictsGeneralGuide => .detachablePracticeConflictsGeneralGuide
  | .methyleneInterruptionIgnored _ _ => .methyleneInterruptionIgnored
  | .prefixCoversEntireRemainingCenterSequence _ _ => .prefixCoversEntireRemainingCenterSequence
  | .anomericHydroxyToHydrogenRoutesToAnhydroAlditol _ =>
      .anomericHydroxyToHydrogenRoutesToAnhydroAlditol
  | .terminalAldehydeToMethylUsesDeoxyAlditol => .terminalAldehydeToMethylUsesDeoxyAlditol
  | .fucitolAndRhamnitolFrequent => .fucitolAndRhamnitolFrequent
  | .aminoReplacementIsSubstitutionOnDeoxySugar => .aminoReplacementIsSubstitutionOnDeoxySugar
  | .aminoEquivalentToHydroxyForConfiguration _ _ => .aminoEquivalentToHydroxyForConfiguration
  | .nSubstitutedTreatmentRoutesToTwoCarbTwentyFive _ =>
      .nSubstitutedTreatmentRoutesToTwoCarbTwentyFive
  | .acceptedAminoTrivialNames _ => .acceptedAminoTrivialNames
  | .neuraminicAndMuramicNamesSpecificallyD _ => .neuraminicAndMuramicNamesSpecificallyD
  | .nonexistentParentAminoNamesNotRecommended => .nonexistentParentAminoNamesNotRecommended
  | .ringNitrogenRoutesToTwoCarbThirtyFour _ => .ringNitrogenRoutesToTwoCarbThirtyFour
  | .systematicAminoUsesDeoxyAndAminoPrefixes => .systematicAminoUsesDeoxyAndAminoPrefixes
  | .aminoDeoxyAlphabetization => .aminoDeoxyAlphabetization
  | .anomericAminoNormallyGlycosylamine => .anomericAminoNormallyGlycosylamine
  | .hydroxyOrCarbonylOxygenToSulfurUsesThio _ => .hydroxyOrCarbonylOxygenToSulfurUsesThio
  | .ringOxygenToSulfurUsesAdjacentNonanomericLocant =>
      .ringOxygenToSulfurUsesAdjacentNonanomericLocant
  | .seleniumAndTelluriumUseSelenoTelluro _ => .seleniumAndTelluriumUseSelenoTelluro
  | .chalcogenOxidesMayUseFunctionalClassNames => .chalcogenOxidesMayUseFunctionalClassNames
  | .thioNotThia _ => .thioNotThia
  | .thioCommonlyTreatedAsDetachable => .thioCommonlyTreatedAsDetachable
  | .nonterminalHydrogenReplacementIsCSubstitution =>
      .nonterminalHydrogenReplacementIsCSubstitution
  | .highestCIPPriorityGroupEquivalentToHydroxy _ => .highestCIPPriorityGroupEquivalentToHydroxy
  | .ambiguousModifiedCenterUsesRS _ _ _ => .ambiguousModifiedCenterUsesRS
  | .nonanomericHydroxyReplacementUsesDeoxyParent =>
      .nonanomericHydroxyReplacementUsesDeoxyParent
  | .replacingGroupDeterminesConfiguration _ _ => .replacingGroupDeterminesConfiguration
  | .hydroxyReplacementAmbiguityUsesRS _ _ _ => .hydroxyReplacementAmbiguityUsesRS
  | .cLocantRequiredOnlyForAmbiguityButMayEmphasize =>
      .cLocantRequiredOnlyForAmbiguityButMayEmphasize
  | .unequalSubstitutionUsesDisubstitutedDeoxyParent =>
      .unequalSubstitutionUsesDisubstitutedDeoxyParent
  | .unequalHigherCIPGroupEquivalentToHydroxy _ _ => .unequalHigherCIPGroupEquivalentToHydroxy
  | .unequalSubstitutionAmbiguityUsesRS _ _ _ => .unequalSubstitutionAmbiguityUsesRS
  | .terminalCreatedCenterUsesRS _ _ _ => .terminalCreatedCenterUsesRS
  | .terminalMethylStillDeoxyNotCMethyl => .terminalMethylStillDeoxyNotCMethyl
  | .aldehydicHydrogenRingReplacementUsesCPrefix => .aldehydicHydrogenRingReplacementUsesCPrefix
  | .iminoAnalogueMayUseIminoDeoxyAlditol => .iminoAnalogueMayUseIminoDeoxyAlditol
  | .oximesAndHydrazonesNamedDirectly => .oximesAndHydrazonesNamedDirectly
  | .arylosazonePrefersKetoaldoseBisHydrazone => .arylosazonePrefersKetoaldoseBisHydrazone
  | .oxidizedArylosazoneMayUseTriazolylAlditol => .oxidizedArylosazoneMayUseTriazolylAlditol
  | .isotopeRulesDelegatedToSectionH _ => .isotopeRulesDelegatedToSectionH
  | .isotopeParenthesesVsLabellingBrackets _ => .isotopeParenthesesVsLabellingBrackets
  | .uniformLabellingUsesU _ => .uniformLabellingUsesU
  | .isotopeCreatedCenterFollowsSubstitutionRules _ _ _ =>
      .isotopeCreatedCenterFollowsSubstitutionRules
  | .deoxyTrivialName row _ => .deoxyTrivialName row
  | .aminoTrivialName row _ => .aminoTrivialName row
  | .printedExample row _ => .printedExample row

@[simp] theorem sourceAssertion_provision_exact (row : Carbohydrate1996Derivatives.Provision) :
    (sourceAssertion row).provision = row := by
  cases row <;> rfl

structure SourceMeaning where
  sourceKey : String
  semanticDomain : SemanticDomain
  assertion : SourceAssertion
  deriving Repr

def sourceMeaning (row : Carbohydrate1996Derivatives.Provision) : SourceMeaning :=
  ⟨row.sourceKey, semanticDomain row, sourceAssertion row⟩

@[simp] theorem sourceMeaning_key_exact (row : Carbohydrate1996Derivatives.Provision) :
    (sourceMeaning row).sourceKey = row.sourceKey := by rfl

@[simp] theorem sourceMeaning_domain_exact (row : Carbohydrate1996Derivatives.Provision) :
    (sourceMeaning row).semanticDomain = semanticDomain row := by rfl

theorem sourceMeaning_injective : Function.Injective sourceMeaning := by
  intro left right equal
  have assertionEqual : (sourceMeaning left).assertion = (sourceMeaning right).assertion :=
    congrArg SourceMeaning.assertion equal
  have provisionEqual := congrArg SourceAssertion.provision assertionEqual
  simpa [sourceMeaning] using provisionEqual

def fullFamilyRows : List Carbohydrate1996Derivatives.Provision :=
  Carbohydrate1996Derivatives.Provision.all

def fullFamilyProvisions : List IUPACNormativeProvision :=
  fullFamilyRows.map IUPACNormativeProvision.carbohydrate1996Derivatives

def completionRows : List Carbohydrate1996Derivatives.Provision :=
  Carbohydrate1996Derivatives.Provision.base

def completionProvisions : List IUPACNormativeProvision :=
  completionRows.map IUPACNormativeProvision.carbohydrate1996Derivatives

def completionBatch : GlobalNonDescriptorSourceMeaningBatch completionProvisions :=
  totalMeaningBatch completionRows IUPACNormativeProvision.carbohydrate1996Derivatives
    sourceMeaning (by intro _row; rfl)

@[simp] theorem full_family_provisions_exact :
    fullFamilyProvisions = carbohydrate1996DerivativesSemanticsSlice := by rfl

@[simp] theorem full_family_provision_count : fullFamilyProvisions.length = 122 := by
  simp [fullFamilyProvisions, fullFamilyRows]

@[simp] theorem completion_provision_count : completionProvisions.length = 56 := by
  simp [completionProvisions, completionRows, Carbohydrate1996Derivatives.Provision.base]

@[simp] theorem completion_entry_count : completionBatch.entries.length = 56 := by
  rw [completionBatch.entries_length, completion_provision_count]

private theorem completion_rows_then_indexed_exact :
    completionRows ++ GlobalNonDescriptorIndexedSourceData.carbohydrateDerivativeRows =
      fullFamilyRows := by
  simp [completionRows, fullFamilyRows,
    GlobalNonDescriptorIndexedSourceData.carbohydrateDerivativeRows,
    Carbohydrate1996Derivatives.Provision.all, List.append_assoc]

theorem completion_then_indexed_exact_source_order :
    completionProvisions ++ GlobalNonDescriptorIndexedSourceData.carbohydrateDerivativeProvisions =
      carbohydrate1996DerivativesSemanticsSlice := by
  rw [← full_family_provisions_exact]
  simp only [completionProvisions,
    GlobalNonDescriptorIndexedSourceData.carbohydrateDerivativeProvisions,
    fullFamilyProvisions, ← List.map_append]
  rw [completion_rows_then_indexed_exact]

theorem materialized_order_perm_source :
    (GlobalNonDescriptorIndexedSourceData.carbohydrateDerivativeProvisions ++
      completionProvisions).Perm carbohydrate1996DerivativesSemanticsSlice := by
  calc
    (GlobalNonDescriptorIndexedSourceData.carbohydrateDerivativeProvisions ++
      completionProvisions).Perm
        (completionProvisions ++
          GlobalNonDescriptorIndexedSourceData.carbohydrateDerivativeProvisions) :=
      List.perm_append_comm
    _ = carbohydrate1996DerivativesSemanticsSlice := completion_then_indexed_exact_source_order

theorem completion_disjoint_indexed :
    completionProvisions.Disjoint
      GlobalNonDescriptorIndexedSourceData.carbohydrateDerivativeProvisions := by
  apply List.disjoint_of_nodup_append
  rw [completion_then_indexed_exact_source_order]
  exact Carbohydrate1996Derivatives.Provision.all_nodup.map
    (by intro left right equal; cases equal; rfl)

theorem completion_provisions_nodup : completionProvisions.Nodup := by
  exact Carbohydrate1996Derivatives.Provision.all_nodup.of_append_left.of_append_left.of_append_left.map
    (by intro left right equal; cases equal; rfl)

@[simp] theorem completion_entry_provisions_exact :
    completionBatch.entries.map GlobalNonDescriptorSourceMeaningEntry.provision =
      completionProvisions := completionBatch.provisions_exact

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

end GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.full_family_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completion_then_indexed_exact_source_order
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.materialized_order_perm_source
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.sourceMeaning_injective
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.completion_entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.every_completion_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateDerivativeSourceMeaning.source_audit_still_open
