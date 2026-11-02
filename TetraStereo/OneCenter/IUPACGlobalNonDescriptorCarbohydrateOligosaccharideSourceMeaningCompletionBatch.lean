import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceDataBatch
import TetraStereo.KernelOnly

set_option autoImplicit false










namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning

open GlobalNonDescriptorIndexedSourceData

inductive SemanticDomain where
  | disaccharide
  | higherOligosaccharide
  | branch
  | cyclic
  | linkageAnalogue
  | symbolNotation
  | extendedNotation
  | condensedNotation
  | shortNotation
  | homoglycan
  | heteroglycan
  | carbohydrateConjugate
  | indexedDisaccharide
  | indexedSymbol
  | untranscribedPrintedExample
  deriving DecidableEq, Repr

def semanticDomain :
    Carbohydrate1996OligosaccharidesPolysaccharides.Provision → SemanticDomain
  | .disaccharideTwoMonosaccharidesJoinedByGlycosidicLinkage
  | .nonreducingTwoAnomericHydroxylReaction
  | .nonreducingNameGlycosylGlycoside
  | .nonreducingParentByCarb21
  | .nonreducingBothAnomericDescriptorsRequired
  | .nonreducingTerm
  | .nonreducingTrivialDerivativeFirstSystematicComponentPrimed
  | .reducingOneGlycosylReplacesAlcoholicHydroxylHydrogen
  | .reducingNameGlycosylglycose
  | .reducingLinkageLocantsRequired
  | .reducingAnomericDescriptorsRequired
  | .reducingTwoEstablishedLocantMethods
  | .reducingParentheticalLocantsPreferred
  | .reducingPrefixLocantsCAS
  | .previousOLocantsOmitted
  | .reducingTerm
  | .establishedDisaccharideTrivialNames
  | .earlierTrehaloseSucroseMaltoseLactoseSystematicNames
  | .reducingTrivialDerivativeFirstSystematicComponentPrimed
  | .uronicEsterGlycosideEsterAlkylAtBeginning
  | .uronicEsterGlycosideAglyconicAlkylWithResidue => .disaccharide
  | .nonfreeHigherOligosaccharideNameForms
  | .nonfreeGlycosidePortionChoiceByCarb21
  | .nonfreeSequentialMethodRegardlessOfCarb21
  | .nonfreePreferredDisaccharideLocantMethod
  | .interResidueSyntaxAnomericLocantArrowOxygenLocant
  | .trivialDerivativeLastComponentUnprimedThenReversePrimes
  | .higherDerivativeSystematicNamingPreferred
  | .freeOligosaccharideGlycosylNGlycose
  | .reducingSugarIsParent
  | .freeOligosaccharideDescriptorsAndLocants
  | .conventionalReducingResidueRight
  | .conventionalNonreducingResidueLeft
  | .internalUnitsAreGlycosylResidues
  | .anhydrosugarUnitTermDiscouraged
  | .downstreamEndGeneralTerm
  | .higherOligosaccharidesSameSystematicMethod
  | .higherOligosaccharideSymbolsOftenPreferable
  | .maltoSeriesTrivialNames
  | .otherHomoOligosaccharideNamesSparing
  | .residueRomanNumeralsAscendingFromReducingEnd
  | .residueArabicNumeralsCanConflict
  | .residueRomanNumeralsFollowGlycolipidUsage => .higherOligosaccharide
  | .branchTermsInSquareBrackets
  | .branchedLongestChainIsParent
  | .equalLengthLowerBranchLocantPreferred
  | .traditionalBranchDepictionMayDiffer => .branch
  | .cyclicSemisystematicCycloLinkageCountOse
  | .cyclodextrinTrivialNamesEstablished
  | .nonOneFourCyclicLinkagesSystematic
  | .schardingerAndCyclohexaamyloseNamesNotRecommended
  | .cdAbbreviationTolerated
  | .uniformCyclicSubstitutionSingleMultiplicativePrefix
  | .varyingCyclicSubstitutionUsesRomanResidueLocants
  | .cyclicSystematicCycloMultiplicativeLinkageResidue
  | .oneSixCyclicNameNotCycloisomaltohexaose => .cyclic
  | .methyleneLinkReplacementUsesCarba
  | .methyleneReplacementLocantFromLowerRomanResidue
  | .methyleneReplacementLocantHasSuperscriptRomanAndA
  | .oxyaminoLinkReplacementUsesAminoSugarNomenclature => .linkageAnalogue
  | .symbolsRecommendedForLongCarbohydrateSequences
  | .symbolsWithLocantsAndAnomersAdequatelyDescribeSequences
  | .commonResidueSymbolsListedInTableTwo
  | .symbolsGenerallyDerivedFromTrivialNames
  | .substituentAbbreviationsFollowResidueSymbolDirectly
  | .substituentAbbreviationsPrecededByLocants
  | .reducingOrModifiedReducingResidueAtRight
  | .noncarbohydrateLinkedGlycosylResidueAtRight
  | .residueNumberingRightToLeft => .symbolNotation
  | .extendedFormCarbBankAndPreferred
  | .extendedSymbolPrecededByAnomericDescriptor
  | .extendedSymbolPrecededByConfiguration
  | .extendedRingSizeExplicit
  | .extendedLinkLocantsParenthesized
  | .extendedDoubleArrowForTwoAnomericPositions
  | .extendedOmittedAnomerMeansUnknown
  | .extendedOmittedConfigurationMeansUnknown
  | .extendedOmittedRingSizeMeansUnknown
  | .extendedBranchesSecondLineOrBrackets
  | .extendedHyphensOptionalExceptConfigurationSeparation => .extendedNotation
  | .condensedConfigurationAndRingOmitted
  | .condensedDefaultConfigurationD
  | .condensedFucoseAndIduronicUsuallyL
  | .condensedDefaultRingPyranose
  | .condensedAnomerInsideLinkageParentheses
  | .abbreviatedExtendedUsuallyPreferShortForm => .condensedNotation
  | .shortOmitAnomericCarbonLocants
  | .shortOmitLinkageParentheses
  | .shortHyphensOptional
  | .shortBranchesUseEnclosingMarks
  | .shortMayRestoreConfigurationAndRingDetail
  | .shortExplicitBranchingVersionRecommended
  | .symbolicMainChainMayDeviateFromCarb373
  | .symbolicDeviationSupportsHomomorphicRelationships => .shortNotation
  | .homoglycanSingleResidueType
  | .homoglycanOseEndingBecomesAn
  | .establishedXylanMannanGalactanUsage
  | .celluloseAndStarchAreGlucans
  | .knownResidueSeriesMayPrefixGlycanName
  | .majorHomoglycanLinkageMayBeNamed
  | .linkageDesignationNamesBondedCarbons
  | .linkagePrecedesConfigurationSymbols
  | .nonglycosidicPolymerGlycanTerminologyInappropriate
  | .nonglycosidicPolymerUsesPolymerNomenclature
  | .broadCurrentPracticeMayStillClassifyAsPolysaccharide
  | .newPolysaccharideNamesEndAn
  | .anNameMeansUnsubstitutedPolysaccharide
  | .establishedPolysaccharideNamesRetained
  | .carrageenanAndLaminaranCurrentUsage
  | .glycuronicAcidIcAcidEndingBecomesAn
  | .glycuronanGenericName
  | .polyuronideTermIncorrect
  | .aminoPolysaccharideModifiesSystematicAminoSugarName => .homoglycan
  | .heteroglycanHasAtLeastTwoResidueKinds
  | .singleTypeBackboneCitedLastAsGlycan
  | .nonbackboneResiduesAlphabeticalGlycoPrefixes
  | .noPrincipalChainAllResiduesAlphabeticalGlycoPrefixes
  | .noPrincipalChainNameEndsGlycan
  | .substitutedGlycanCitesEverySubstituentType
  | .substitutedGlycanSubstituentsAlphabetical => .heteroglycan
  | .carbohydrateAminoAcidPolymersUseThreeBroadTerms
  | .broadConjugateTermsHaveNoPreciseBoundary
  | .glycoproteinHasLowMassCarbohydrateGroups
  | .proteoglycanHasHighMassPolysaccharide
  | .peptidoglycanHasPolysaccharideAndPeptideChains
  | .conjugateNomenclatureDelegated
  | .neoglycoproteinForSyntheticOrModifiedConjugate
  | .conjugateCarbohydrateSubstituentUsesSequentialOligosaccharideNaming =>
      .carbohydrateConjugate
  | .disaccharideTrivialRow _ => .indexedDisaccharide
  | .symbolRow _ => .indexedSymbol
  | .printedExample _ => .untranscribedPrintedExample

def disaccharideFormInventory :
    List (Carbohydrate1996OligosaccharidesPolysaccharides.HemiacetalStatus ×
      Carbohydrate1996OligosaccharidesPolysaccharides.DisaccharideNameForm × Nat) :=
  [ (.free,
      Carbohydrate1996OligosaccharidesPolysaccharides.disaccharideNameForm .free,
      Carbohydrate1996OligosaccharidesPolysaccharides.requiredAnomericDescriptorCount .free)
  , (.unavailable,
      Carbohydrate1996OligosaccharidesPolysaccharides.disaccharideNameForm .unavailable,
      Carbohydrate1996OligosaccharidesPolysaccharides.requiredAnomericDescriptorCount .unavailable) ]

def cyclicNameStyleInventory :
    List (Nat × Carbohydrate1996OligosaccharidesPolysaccharides.CyclicNameStyle) :=
  [ (4, Carbohydrate1996OligosaccharidesPolysaccharides.cyclicNameStyle 4)
  , (6, Carbohydrate1996OligosaccharidesPolysaccharides.cyclicNameStyle 6) ]

def analogueNamingRouteInventory :
    List (Carbohydrate1996OligosaccharidesPolysaccharides.LinkReplacement ×
      Carbohydrate1996OligosaccharidesPolysaccharides.AnalogueNamingRoute) :=
  [ (.methylene,
      Carbohydrate1996OligosaccharidesPolysaccharides.analogueNamingRoute .methylene)
  , (.oxyamino,
      Carbohydrate1996OligosaccharidesPolysaccharides.analogueNamingRoute .oxyamino) ]

def condensedDefaultInventory :
    List (Carbohydrate1996OligosaccharidesPolysaccharides.SymbolRow ×
      Carbohydrate1996OligosaccharidesPolysaccharides.CondensedDefaults) :=
  [ (.fucose, Carbohydrate1996OligosaccharidesPolysaccharides.condensedDefaults .fucose)
  , (.iduronicAcid,
      Carbohydrate1996OligosaccharidesPolysaccharides.condensedDefaults .iduronicAcid)
  , (.glucose, Carbohydrate1996OligosaccharidesPolysaccharides.condensedDefaults .glucose) ]

def heteroglycanRouteInventory :
    List (Bool × Carbohydrate1996OligosaccharidesPolysaccharides.HeteroglycanNameRoute) :=
  [ (true, Carbohydrate1996OligosaccharidesPolysaccharides.heteroglycanNameRoute true)
  , (false, Carbohydrate1996OligosaccharidesPolysaccharides.heteroglycanNameRoute false) ]

def conjugateClassInventory :
    List ((Carbohydrate1996OligosaccharidesPolysaccharides.CarbohydrateComponent × Bool) ×
      Carbohydrate1996OligosaccharidesPolysaccharides.ConjugateClass) :=
  [ ((.oligosaccharide, false),
      Carbohydrate1996OligosaccharidesPolysaccharides.conjugateClass .oligosaccharide false)
  , ((.highMassPolysaccharide, false),
      Carbohydrate1996OligosaccharidesPolysaccharides.conjugateClass
        .highMassPolysaccharide false)
  , ((.lowMassPolysaccharide, true),
      Carbohydrate1996OligosaccharidesPolysaccharides.conjugateClass
        .lowMassPolysaccharide true) ]

abbrev OligosaccharideProvision :=
  Carbohydrate1996OligosaccharidesPolysaccharides.Provision

inductive SourceAssertion where
  | semanticClause (row : OligosaccharideProvision)
  | disaccharideNameForm (row : OligosaccharideProvision)
      (status : Carbohydrate1996OligosaccharidesPolysaccharides.HemiacetalStatus)
      (form : Carbohydrate1996OligosaccharidesPolysaccharides.DisaccharideNameForm)
  | requiredAnomericDescriptorCount (row : OligosaccharideProvision)
      (status : Carbohydrate1996OligosaccharidesPolysaccharides.HemiacetalStatus) (count : Nat)
  | chainEnd (row : OligosaccharideProvision)
      (end_ : Carbohydrate1996OligosaccharidesPolysaccharides.ChainEnd)
  | cyclicNameStyle (row : OligosaccharideProvision) (acceptorLocant : Nat)
      (style : Carbohydrate1996OligosaccharidesPolysaccharides.CyclicNameStyle)
  | analogueNamingRoute (row : OligosaccharideProvision)
      (replacement : Carbohydrate1996OligosaccharidesPolysaccharides.LinkReplacement)
      (route : Carbohydrate1996OligosaccharidesPolysaccharides.AnalogueNamingRoute)
  | condensedDefaults (row : OligosaccharideProvision)
      (symbol : Carbohydrate1996OligosaccharidesPolysaccharides.SymbolRow)
      (defaults : Carbohydrate1996OligosaccharidesPolysaccharides.CondensedDefaults)
  | heteroglycanNameRoute (row : OligosaccharideProvision) (hasSingleTypeBackbone : Bool)
      (route : Carbohydrate1996OligosaccharidesPolysaccharides.HeteroglycanNameRoute)
  | conjugateClass (row : OligosaccharideProvision)
      (component : Carbohydrate1996OligosaccharidesPolysaccharides.CarbohydrateComponent)
      (hasPeptideChains : Bool)
      (classification : Carbohydrate1996OligosaccharidesPolysaccharides.ConjugateClass)
  | indexedDisaccharide
      (row : Carbohydrate1996OligosaccharidesPolysaccharides.DisaccharideTrivialRow)
      (data : Carbohydrate1996OligosaccharidesPolysaccharides.DisaccharideTrivialData)
  | indexedSymbol (row : Carbohydrate1996OligosaccharidesPolysaccharides.SymbolRow)
      (data : Carbohydrate1996OligosaccharidesPolysaccharides.SymbolData)
  | untranscribedPrintedExample
      (row : Carbohydrate1996OligosaccharidesPolysaccharides.PrintedExample) (sourceKey : String)
  deriving Repr

def sourceAssertion : OligosaccharideProvision → SourceAssertion
  | .nonreducingNameGlycosylGlycoside =>
      .disaccharideNameForm .nonreducingNameGlycosylGlycoside .unavailable
        (Carbohydrate1996OligosaccharidesPolysaccharides.disaccharideNameForm .unavailable)
  | .reducingNameGlycosylglycose =>
      .disaccharideNameForm .reducingNameGlycosylglycose .free
        (Carbohydrate1996OligosaccharidesPolysaccharides.disaccharideNameForm .free)
  | .nonreducingBothAnomericDescriptorsRequired =>
      .requiredAnomericDescriptorCount .nonreducingBothAnomericDescriptorsRequired .unavailable
        (Carbohydrate1996OligosaccharidesPolysaccharides.requiredAnomericDescriptorCount
          .unavailable)
  | .reducingAnomericDescriptorsRequired =>
      .requiredAnomericDescriptorCount .reducingAnomericDescriptorsRequired .free
        (Carbohydrate1996OligosaccharidesPolysaccharides.requiredAnomericDescriptorCount .free)
  | .conventionalReducingResidueRight =>
      .chainEnd .conventionalReducingResidueRight
        Carbohydrate1996OligosaccharidesPolysaccharides.conventionalReducingEnd
  | .conventionalNonreducingResidueLeft =>
      .chainEnd .conventionalNonreducingResidueLeft
        Carbohydrate1996OligosaccharidesPolysaccharides.conventionalNonreducingEnd
  | .cyclicSemisystematicCycloLinkageCountOse =>
      .cyclicNameStyle .cyclicSemisystematicCycloLinkageCountOse 4
        (Carbohydrate1996OligosaccharidesPolysaccharides.cyclicNameStyle 4)
  | .oneSixCyclicNameNotCycloisomaltohexaose =>
      .cyclicNameStyle .oneSixCyclicNameNotCycloisomaltohexaose 6
        (Carbohydrate1996OligosaccharidesPolysaccharides.cyclicNameStyle 6)
  | .methyleneLinkReplacementUsesCarba =>
      .analogueNamingRoute .methyleneLinkReplacementUsesCarba .methylene
        (Carbohydrate1996OligosaccharidesPolysaccharides.analogueNamingRoute .methylene)
  | .oxyaminoLinkReplacementUsesAminoSugarNomenclature =>
      .analogueNamingRoute .oxyaminoLinkReplacementUsesAminoSugarNomenclature .oxyamino
        (Carbohydrate1996OligosaccharidesPolysaccharides.analogueNamingRoute .oxyamino)
  | .condensedFucoseAndIduronicUsuallyL =>
      .condensedDefaults .condensedFucoseAndIduronicUsuallyL .fucose
        (Carbohydrate1996OligosaccharidesPolysaccharides.condensedDefaults .fucose)
  | .condensedDefaultConfigurationD =>
      .condensedDefaults .condensedDefaultConfigurationD .glucose
        (Carbohydrate1996OligosaccharidesPolysaccharides.condensedDefaults .glucose)
  | .singleTypeBackboneCitedLastAsGlycan =>
      .heteroglycanNameRoute .singleTypeBackboneCitedLastAsGlycan true
        (Carbohydrate1996OligosaccharidesPolysaccharides.heteroglycanNameRoute true)
  | .noPrincipalChainAllResiduesAlphabeticalGlycoPrefixes =>
      .heteroglycanNameRoute .noPrincipalChainAllResiduesAlphabeticalGlycoPrefixes false
        (Carbohydrate1996OligosaccharidesPolysaccharides.heteroglycanNameRoute false)
  | .glycoproteinHasLowMassCarbohydrateGroups =>
      .conjugateClass .glycoproteinHasLowMassCarbohydrateGroups .oligosaccharide false
        (Carbohydrate1996OligosaccharidesPolysaccharides.conjugateClass .oligosaccharide false)
  | .proteoglycanHasHighMassPolysaccharide =>
      .conjugateClass .proteoglycanHasHighMassPolysaccharide .highMassPolysaccharide false
        (Carbohydrate1996OligosaccharidesPolysaccharides.conjugateClass
          .highMassPolysaccharide false)
  | .peptidoglycanHasPolysaccharideAndPeptideChains =>
      .conjugateClass .peptidoglycanHasPolysaccharideAndPeptideChains
        .lowMassPolysaccharide true
        (Carbohydrate1996OligosaccharidesPolysaccharides.conjugateClass
          .lowMassPolysaccharide true)
  | .disaccharideTrivialRow row => .indexedDisaccharide row row.data
  | .symbolRow row => .indexedSymbol row row.data
  | .printedExample row => .untranscribedPrintedExample row row.sourceKey
  | row => .semanticClause row

def SourceAssertion.provision : SourceAssertion → OligosaccharideProvision
  | .semanticClause row => row
  | .disaccharideNameForm row _ _ => row
  | .requiredAnomericDescriptorCount row _ _ => row
  | .chainEnd row _ => row
  | .cyclicNameStyle row _ _ => row
  | .analogueNamingRoute row _ _ => row
  | .condensedDefaults row _ _ => row
  | .heteroglycanNameRoute row _ _ => row
  | .conjugateClass row _ _ _ => row
  | .indexedDisaccharide row _ => .disaccharideTrivialRow row
  | .indexedSymbol row _ => .symbolRow row
  | .untranscribedPrintedExample row _ => .printedExample row

@[simp] theorem sourceAssertion_provision_exact (row : OligosaccharideProvision) :
    (sourceAssertion row).provision = row := by
  cases row <;> rfl

structure SourceMeaning where
  sourceKey : String
  semanticDomain : SemanticDomain
  assertion : SourceAssertion
  deriving Repr

def sourceMeaning (row : OligosaccharideProvision) : SourceMeaning :=
  ⟨row.sourceKey, semanticDomain row, sourceAssertion row⟩

@[simp] theorem sourceMeaning_key_exact (row : OligosaccharideProvision) :
    (sourceMeaning row).sourceKey = row.sourceKey := by rfl

@[simp] theorem sourceMeaning_domain_exact (row : OligosaccharideProvision) :
    (sourceMeaning row).semanticDomain = semanticDomain row := by rfl

theorem sourceMeaning_injective : Function.Injective sourceMeaning := by
  intro left right equal
  have assertionEqual : (sourceMeaning left).assertion = (sourceMeaning right).assertion :=
    congrArg SourceMeaning.assertion equal
  have provisionEqual := congrArg SourceAssertion.provision assertionEqual
  simpa [sourceMeaning] using provisionEqual

def fullFamilyRows : List OligosaccharideProvision :=
  Carbohydrate1996OligosaccharidesPolysaccharides.Provision.all

def fullFamilyProvisions : List IUPACNormativeProvision :=
  fullFamilyRows.map IUPACNormativeProvision.carbohydrate1996OligosaccharidesPolysaccharides

def completionRows : List OligosaccharideProvision :=
  Carbohydrate1996OligosaccharidesPolysaccharides.Provision.base

def completionProvisions : List IUPACNormativeProvision :=
  completionRows.map IUPACNormativeProvision.carbohydrate1996OligosaccharidesPolysaccharides

def untranscribedPrintedRows : List OligosaccharideProvision :=
  Carbohydrate1996OligosaccharidesPolysaccharides.PrintedExample.all.map
    Carbohydrate1996OligosaccharidesPolysaccharides.Provision.printedExample

def untranscribedPrintedProvisions : List IUPACNormativeProvision :=
  untranscribedPrintedRows.map
    IUPACNormativeProvision.carbohydrate1996OligosaccharidesPolysaccharides

/-- The exact printed-example source rows, now carrying their official associated text. -/
def printedRows : List Carbohydrate1996OligosaccharidesPolysaccharides.PrintedExample :=
  Carbohydrate1996OligosaccharidesPolysaccharides.PrintedExample.all

def printedProvisions : List IUPACNormativeProvision :=
  printedRows.map fun row =>
    IUPACNormativeProvision.carbohydrate1996OligosaccharidesPolysaccharides (.printedExample row)

def completionBatch : GlobalNonDescriptorSourceMeaningBatch completionProvisions :=
  totalMeaningBatch completionRows
    IUPACNormativeProvision.carbohydrate1996OligosaccharidesPolysaccharides sourceMeaning
      (by intro _row; rfl)

def printedBatch : GlobalNonDescriptorSourceMeaningBatch printedProvisions :=
  totalMeaningBatch printedRows
    (fun row =>
      IUPACNormativeProvision.carbohydrate1996OligosaccharidesPolysaccharides
        (.printedExample row))
    Carbohydrate1996OligosaccharidesPolysaccharides.PrintedExample.data (by intro _row; rfl)

def materializedProvisions : List IUPACNormativeProvision :=
  (completionProvisions ++ carbohydrateOligosaccharideProvisions) ++ printedProvisions

def materializedBatch : GlobalNonDescriptorSourceMeaningBatch materializedProvisions :=
  (completionBatch.append carbohydrateOligosaccharideBatch).append printedBatch

@[simp] theorem full_family_provisions_exact :
    fullFamilyProvisions = carbohydrate1996OligosaccharidesPolysaccharidesSemanticsSlice := by rfl

@[simp] theorem full_family_provision_count : fullFamilyProvisions.length = 220 := by
  simp [fullFamilyProvisions, fullFamilyRows]

@[simp] theorem completion_provision_count : completionProvisions.length = 128 := by
  simp [completionProvisions, completionRows,
    Carbohydrate1996OligosaccharidesPolysaccharides.Provision.base]

@[simp] theorem indexed_provision_count : carbohydrateOligosaccharideProvisions.length = 51 :=
  carbohydrateOligosaccharideProvisionCount

@[simp] theorem untranscribed_printed_provision_count :
    untranscribedPrintedProvisions.length = 41 := by
  simp [untranscribedPrintedProvisions, untranscribedPrintedRows]

@[simp] theorem printed_provisions_eq_prior_untranscribed :
    printedProvisions = untranscribedPrintedProvisions := by
  simp [printedProvisions, printedRows, untranscribedPrintedProvisions,
    untranscribedPrintedRows, List.map_map]

@[simp] theorem printed_provision_count : printedProvisions.length = 41 := by
  simp [printedProvisions, printedRows]

@[simp] theorem printed_entry_count : printedBatch.entries.length = 41 := by
  rw [printedBatch.entries_length, printed_provision_count]

@[simp] theorem completion_entry_count : completionBatch.entries.length = 128 := by
  rw [completionBatch.entries_length, completion_provision_count]

private theorem partition_rows_exact_source_order :
    (completionRows ++ carbohydrateOligosaccharideRows) ++ untranscribedPrintedRows =
      fullFamilyRows := by
  simp [completionRows, carbohydrateOligosaccharideRows, untranscribedPrintedRows,
    fullFamilyRows, Carbohydrate1996OligosaccharidesPolysaccharides.Provision.all,
    List.append_assoc]

theorem completion_then_indexed_then_untranscribed_exact_source_order :
    (completionProvisions ++ carbohydrateOligosaccharideProvisions) ++
      untranscribedPrintedProvisions =
        carbohydrate1996OligosaccharidesPolysaccharidesSemanticsSlice := by
  rw [← full_family_provisions_exact]
  simp only [completionProvisions, carbohydrateOligosaccharideProvisions,
    untranscribedPrintedProvisions, fullFamilyProvisions, ← List.map_append]
  rw [partition_rows_exact_source_order]

theorem materialized_then_untranscribed_order_perm_source :
    ((carbohydrateOligosaccharideProvisions ++ completionProvisions) ++
      untranscribedPrintedProvisions).Perm
        carbohydrate1996OligosaccharidesPolysaccharidesSemanticsSlice := by
  calc
    ((carbohydrateOligosaccharideProvisions ++ completionProvisions) ++
      untranscribedPrintedProvisions).Perm
        ((completionProvisions ++ carbohydrateOligosaccharideProvisions) ++
          untranscribedPrintedProvisions) := List.perm_append_comm.append_right _
    _ = carbohydrate1996OligosaccharidesPolysaccharidesSemanticsSlice :=
      completion_then_indexed_then_untranscribed_exact_source_order

private theorem partition_provisions_nodup :
    ((completionProvisions ++ carbohydrateOligosaccharideProvisions) ++
      untranscribedPrintedProvisions).Nodup := by
  rw [completion_then_indexed_then_untranscribed_exact_source_order]
  exact Carbohydrate1996OligosaccharidesPolysaccharides.Provision.all_nodup.map
    (by intro left right equal; cases equal; rfl)

theorem completion_provisions_nodup : completionProvisions.Nodup :=
  partition_provisions_nodup.of_append_left.of_append_left

theorem indexed_provisions_nodup : carbohydrateOligosaccharideProvisions.Nodup :=
  partition_provisions_nodup.of_append_left.of_append_right

theorem untranscribed_printed_provisions_nodup : untranscribedPrintedProvisions.Nodup :=
  partition_provisions_nodup.of_append_right

theorem printed_provisions_nodup : printedProvisions.Nodup := by
  rw [printed_provisions_eq_prior_untranscribed]
  exact untranscribed_printed_provisions_nodup

theorem materialized_provisions_exact : materializedProvisions = fullFamilyProvisions := by
  rw [materializedProvisions, printed_provisions_eq_prior_untranscribed,
    completion_then_indexed_then_untranscribed_exact_source_order,
    full_family_provisions_exact]

@[simp] theorem materialized_provision_count : materializedProvisions.length = 220 := by
  rw [materialized_provisions_exact, full_family_provision_count]

theorem materialized_provisions_nodup : materializedProvisions.Nodup := by
  rw [materialized_provisions_exact, fullFamilyProvisions, fullFamilyRows]
  exact Carbohydrate1996OligosaccharidesPolysaccharides.Provision.all_nodup.map
    (by intro left right equal; cases equal; rfl)

theorem completion_disjoint_indexed :
    completionProvisions.Disjoint carbohydrateOligosaccharideProvisions :=
  List.disjoint_of_nodup_append partition_provisions_nodup.of_append_left

private theorem materialized_disjoint_untranscribed :
    (completionProvisions ++ carbohydrateOligosaccharideProvisions).Disjoint
      untranscribedPrintedProvisions :=
  List.disjoint_of_nodup_append partition_provisions_nodup

theorem completion_disjoint_untranscribed_printed :
    completionProvisions.Disjoint untranscribedPrintedProvisions := by
  rw [List.disjoint_left]
  intro provision completionMember untranscribedMember
  exact (List.disjoint_left.mp materialized_disjoint_untranscribed)
    (List.mem_append_left _ completionMember) untranscribedMember

theorem indexed_disjoint_untranscribed_printed :
    carbohydrateOligosaccharideProvisions.Disjoint untranscribedPrintedProvisions := by
  rw [List.disjoint_left]
  intro provision indexedMember untranscribedMember
  exact (List.disjoint_left.mp materialized_disjoint_untranscribed)
    (List.mem_append_right _ indexedMember) untranscribedMember

theorem every_untranscribed_provision_is_printed_example
    (provision : IUPACNormativeProvision) (member : provision ∈ untranscribedPrintedProvisions) :
    ∃ row : Carbohydrate1996OligosaccharidesPolysaccharides.PrintedExample,
      provision = .carbohydrate1996OligosaccharidesPolysaccharides (.printedExample row) := by
  rw [untranscribedPrintedProvisions, untranscribedPrintedRows, List.map_map] at member
  obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp member
  exact ⟨row, rfl⟩

@[simp] theorem completion_entry_provisions_exact :
    completionBatch.entries.map GlobalNonDescriptorSourceMeaningEntry.provision =
      completionProvisions := completionBatch.provisions_exact

@[simp] theorem printed_entry_provisions_exact :
    printedBatch.entries.map GlobalNonDescriptorSourceMeaningEntry.provision = printedProvisions :=
  printedBatch.provisions_exact

@[simp] theorem materialized_entry_provisions_exact :
    materializedBatch.entries.map GlobalNonDescriptorSourceMeaningEntry.provision =
      materializedProvisions :=
  materializedBatch.provisions_exact

theorem every_completion_entry_nonvacuous
    (entry : GlobalNonDescriptorSourceMeaningEntry) (_member : entry ∈ completionBatch.entries) :
    ∃ input, ∃ observation : entry.reference.toReference.Observation,
      input.StructurallyWellFormed ∧ entry.reference.toReference.Applicable input ∧
        entry.reference.toReference.Judges input observation :=
  entry.admittedJudgment

theorem every_printed_entry_nonvacuous
    (entry : GlobalNonDescriptorSourceMeaningEntry) (_member : entry ∈ printedBatch.entries) :
    ∃ input, ∃ observation : entry.reference.toReference.Observation,
      input.StructurallyWellFormed ∧ entry.reference.toReference.Applicable input ∧
        entry.reference.toReference.Judges input observation :=
  entry.admittedJudgment

theorem source_audit_still_open :
    ¬IUPACNormativeSource.ProvisionAuditComplete .carbohydrateRecommendations1996 := by
  exact IUPACNormativeSource.provisionAuditIncomplete_of_figure_review_open _ rfl

end GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.full_family_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completion_then_indexed_then_untranscribed_exact_source_order
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.materialized_then_untranscribed_order_perm_source
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.sourceMeaning_injective
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.completion_entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.every_untranscribed_provision_is_printed_example
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.every_completion_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateOligosaccharideSourceMeaning.source_audit_still_open
