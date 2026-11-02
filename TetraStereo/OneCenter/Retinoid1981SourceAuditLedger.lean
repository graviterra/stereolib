import TetraStereo.OneCenter.Retinoid1981FigureGraphTranscription
import TetraStereo.KernelOnly

set_option autoImplicit false













namespace TetraStereo.OneCenter
namespace Retinoid1981
namespace SourceAudit
namespace Ledger

/-! ## Exhaustive normative-clause inventory -/

/-- One semantic obligation or source-data assertion in the nineteen substantive recommendation
sections. Constructor names are normalized paraphrases rather than copied source prose. -/
inductive NormativeClause where
  | classFourHeadToTailIsoprenoidUnits
  | monocyclicFiveDoubleBondTerminalFunctionDerivation
  | parentHydrocarbonUnnamed
  | vitaminAGenericActivityDescriptor
  | vitaminADerivedTerms
  | stereoparentNameImpliesStereochemistry
  | skeletalFormulaOmitsCarbonHydrogen
  | tenTerminalGroupStructures
  | compoundOneRetinolDesignation
  | retinolSynonymsRecorded
  | compoundTwoRetinalDesignation
  | retinaldehydeAmbiguityAlternative
  | retinalSynonymsRecorded
  | compoundThreeRetinoicAcidDesignation
  | retinoicAcidSynonymsRecorded
  | numberingStructuresOneToTen
  | numberingCarotenoidDelegation
  | compoundFourDeoxyretinolDesignation
  | deoxyretinolNotStereoparent
  | deoxyPrefixNondetachable
  | deoxyAdjacentStemAvoidsLocant
  | c15CH2UsesRetinyl
  | c15CHUsesRetinylidene
  | c15DerivativesRetainNumbering
  | retinylExamplesFiveSix
  | retinalAldehydeDerivativeRoute
  | retinalRetinylideneRoute
  | retinalExamplesSevenEight
  | retinoicAcidDerivativeRules
  | retinoicAcidExamplesNineTen
  | hydrogenationUsesHydroDehydro
  | hydrogenationLocantsSpecifyAtoms
  | hydrogenationPrefixesNondetachable
  | dehydroPrecedesHydro
  | substitutionUsesGeneralPrefixes
  | substitutionSuffixesUnavailable
  | substitutedRetinoidExamples
  | ringFissionUsesSeco
  | secoRetainsNumbering
  | secoRetinoidExample
  | eliminatedGroupUsesNor
  | norCarriesRemovedAtomLocant
  | norChoosesHighestLocant
  | norRetainsNumbering
  | norPrefixNondetachable
  | norDiffersFromCarotenoidLowestLocant
  | retroShiftsConjugatedSystem
  | retroUsesLocantPair
  | retroFirstLocantLosesProton
  | retroSecondLocantGainsProton
  | retroPrefixNondetachable
  | retroPreferredLowerLocantName
  | otherModificationsUseAppropriatePrefixes
  | chiralCentresUseRS
  | rsSymbolsAndLocantsPrecedeName
  | polyeneDefaultsToAllTrans
  | cisCitationsFollowAbsoluteConfiguration
  | ezMayBeUsed
  | ezRequiredWhenAmbiguous
  | substitutionMayRelabelEZWithoutGeometryChange
  | allDoubleBondsCitedWithEZ
  | retroSixSevenStatedWhenNeeded
  deriving DecidableEq, Repr

namespace NormativeClause

def all : List NormativeClause :=
  [ .classFourHeadToTailIsoprenoidUnits
  , .monocyclicFiveDoubleBondTerminalFunctionDerivation
  , .parentHydrocarbonUnnamed
  , .vitaminAGenericActivityDescriptor
  , .vitaminADerivedTerms
  , .stereoparentNameImpliesStereochemistry
  , .skeletalFormulaOmitsCarbonHydrogen
  , .tenTerminalGroupStructures
  , .compoundOneRetinolDesignation
  , .retinolSynonymsRecorded
  , .compoundTwoRetinalDesignation
  , .retinaldehydeAmbiguityAlternative
  , .retinalSynonymsRecorded
  , .compoundThreeRetinoicAcidDesignation
  , .retinoicAcidSynonymsRecorded
  , .numberingStructuresOneToTen
  , .numberingCarotenoidDelegation
  , .compoundFourDeoxyretinolDesignation
  , .deoxyretinolNotStereoparent
  , .deoxyPrefixNondetachable
  , .deoxyAdjacentStemAvoidsLocant
  , .c15CH2UsesRetinyl
  , .c15CHUsesRetinylidene
  , .c15DerivativesRetainNumbering
  , .retinylExamplesFiveSix
  , .retinalAldehydeDerivativeRoute
  , .retinalRetinylideneRoute
  , .retinalExamplesSevenEight
  , .retinoicAcidDerivativeRules
  , .retinoicAcidExamplesNineTen
  , .hydrogenationUsesHydroDehydro
  , .hydrogenationLocantsSpecifyAtoms
  , .hydrogenationPrefixesNondetachable
  , .dehydroPrecedesHydro
  , .substitutionUsesGeneralPrefixes
  , .substitutionSuffixesUnavailable
  , .substitutedRetinoidExamples
  , .ringFissionUsesSeco
  , .secoRetainsNumbering
  , .secoRetinoidExample
  , .eliminatedGroupUsesNor
  , .norCarriesRemovedAtomLocant
  , .norChoosesHighestLocant
  , .norRetainsNumbering
  , .norPrefixNondetachable
  , .norDiffersFromCarotenoidLowestLocant
  , .retroShiftsConjugatedSystem
  , .retroUsesLocantPair
  , .retroFirstLocantLosesProton
  , .retroSecondLocantGainsProton
  , .retroPrefixNondetachable
  , .retroPreferredLowerLocantName
  , .otherModificationsUseAppropriatePrefixes
  , .chiralCentresUseRS
  , .rsSymbolsAndLocantsPrecedeName
  , .polyeneDefaultsToAllTrans
  , .cisCitationsFollowAbsoluteConfiguration
  , .ezMayBeUsed
  , .ezRequiredWhenAmbiguous
  , .substitutionMayRelabelEZWithoutGeometryChange
  , .allDoubleBondsCitedWithEZ
  , .retroSixSevenStatedWhenNeeded ]

def normativeSection : NormativeClause → NormativeSection
  | .classFourHeadToTailIsoprenoidUnits
  | .monocyclicFiveDoubleBondTerminalFunctionDerivation
  | .parentHydrocarbonUnnamed => .ret1
  | .vitaminAGenericActivityDescriptor
  | .vitaminADerivedTerms => .ret1_1
  | .stereoparentNameImpliesStereochemistry
  | .skeletalFormulaOmitsCarbonHydrogen
  | .tenTerminalGroupStructures => .ret2
  | .compoundOneRetinolDesignation
  | .retinolSynonymsRecorded => .ret2_1
  | .compoundTwoRetinalDesignation
  | .retinaldehydeAmbiguityAlternative
  | .retinalSynonymsRecorded => .ret2_2
  | .compoundThreeRetinoicAcidDesignation
  | .retinoicAcidSynonymsRecorded => .ret2_3
  | .numberingStructuresOneToTen
  | .numberingCarotenoidDelegation => .ret3
  | .compoundFourDeoxyretinolDesignation
  | .deoxyretinolNotStereoparent
  | .deoxyPrefixNondetachable
  | .deoxyAdjacentStemAvoidsLocant => .ret4_1
  | .c15CH2UsesRetinyl
  | .c15CHUsesRetinylidene
  | .c15DerivativesRetainNumbering
  | .retinylExamplesFiveSix => .ret4_2_1
  | .retinalAldehydeDerivativeRoute
  | .retinalRetinylideneRoute
  | .retinalExamplesSevenEight => .ret4_2_2
  | .retinoicAcidDerivativeRules
  | .retinoicAcidExamplesNineTen => .ret4_2_3
  | .hydrogenationUsesHydroDehydro
  | .hydrogenationLocantsSpecifyAtoms
  | .hydrogenationPrefixesNondetachable
  | .dehydroPrecedesHydro => .ret4_3
  | .substitutionUsesGeneralPrefixes
  | .substitutionSuffixesUnavailable
  | .substitutedRetinoidExamples => .ret4_4
  | .ringFissionUsesSeco
  | .secoRetainsNumbering
  | .secoRetinoidExample => .ret4_5
  | .eliminatedGroupUsesNor
  | .norCarriesRemovedAtomLocant
  | .norChoosesHighestLocant
  | .norRetainsNumbering
  | .norPrefixNondetachable
  | .norDiffersFromCarotenoidLowestLocant => .ret4_6
  | .retroShiftsConjugatedSystem
  | .retroUsesLocantPair
  | .retroFirstLocantLosesProton
  | .retroSecondLocantGainsProton
  | .retroPrefixNondetachable
  | .retroPreferredLowerLocantName => .ret4_7
  | .otherModificationsUseAppropriatePrefixes => .ret4_8
  | .chiralCentresUseRS
  | .rsSymbolsAndLocantsPrecedeName => .ret5_1
  | .polyeneDefaultsToAllTrans
  | .cisCitationsFollowAbsoluteConfiguration
  | .ezMayBeUsed
  | .ezRequiredWhenAmbiguous
  | .substitutionMayRelabelEZWithoutGeometryChange
  | .allDoubleBondsCitedWithEZ
  | .retroSixSevenStatedWhenNeeded => .ret5_2

@[simp] theorem length_all : all.length = 62 := by
  decide

theorem all_nodup : all.Nodup := by
  decide

@[simp] theorem section_coverage_exact :
    (all.map normativeSection).eraseDups = NormativeSection.all := by
  decide

theorem every_section_covered (sourceSection : NormativeSection) :
    ∃ clause ∈ all, clause.normativeSection = sourceSection := by
  cases sourceSection with
  | ret1 => exact ⟨.classFourHeadToTailIsoprenoidUnits, by simp [all], rfl⟩
  | ret1_1 => exact ⟨.vitaminAGenericActivityDescriptor, by simp [all], rfl⟩
  | ret2 => exact ⟨.stereoparentNameImpliesStereochemistry, by simp [all], rfl⟩
  | ret2_1 => exact ⟨.compoundOneRetinolDesignation, by simp [all], rfl⟩
  | ret2_2 => exact ⟨.compoundTwoRetinalDesignation, by simp [all], rfl⟩
  | ret2_3 => exact ⟨.compoundThreeRetinoicAcidDesignation, by simp [all], rfl⟩
  | ret3 => exact ⟨.numberingStructuresOneToTen, by simp [all], rfl⟩
  | ret4_1 => exact ⟨.compoundFourDeoxyretinolDesignation, by simp [all], rfl⟩
  | ret4_2_1 => exact ⟨.c15CH2UsesRetinyl, by simp [all], rfl⟩
  | ret4_2_2 => exact ⟨.retinalAldehydeDerivativeRoute, by simp [all], rfl⟩
  | ret4_2_3 => exact ⟨.retinoicAcidDerivativeRules, by simp [all], rfl⟩
  | ret4_3 => exact ⟨.hydrogenationUsesHydroDehydro, by simp [all], rfl⟩
  | ret4_4 => exact ⟨.substitutionUsesGeneralPrefixes, by simp [all], rfl⟩
  | ret4_5 => exact ⟨.ringFissionUsesSeco, by simp [all], rfl⟩
  | ret4_6 => exact ⟨.eliminatedGroupUsesNor, by simp [all], rfl⟩
  | ret4_7 => exact ⟨.retroShiftsConjugatedSystem, by simp [all], rfl⟩
  | ret4_8 => exact ⟨.otherModificationsUseAppropriatePrefixes, by simp [all], rfl⟩
  | ret5_1 => exact ⟨.chiralCentresUseRS, by simp [all], rfl⟩
  | ret5_2 => exact ⟨.polyeneDefaultsToAllTrans, by simp [all], rfl⟩

/-! ### Bridge to the thirteen global retinoid provisions -/

/-- Exact normalized clause or clauses that support one modeled stereochemical provision.
`ezAllowedAndRequiredWhenAmbiguous` intentionally cites two independently enumerated clauses. -/
def forProvision : Provision → List NormativeClause
  | .stereoparentNameImpliesConfiguration => [.stereoparentNameImpliesStereochemistry]
  | .retinolStereoparent => [.compoundOneRetinolDesignation]
  | .retinalStereoparent => [.compoundTwoRetinalDesignation]
  | .retinoicAcidStereoparent => [.compoundThreeRetinoicAcidDesignation]
  | .stereochemicalLocantsUseRetinoidNumbering => [.numberingStructuresOneToTen]
  | .chiralCentersUseRS => [.chiralCentresUseRS]
  | .rsLocantsPrecedeRetinoidName => [.rsSymbolsAndLocantsPrecedeName]
  | .polyeneDefaultsToAllTrans => [.polyeneDefaultsToAllTrans]
  | .cisCitationsFollowAbsoluteConfiguration => [.cisCitationsFollowAbsoluteConfiguration]
  | .ezAllowedAndRequiredWhenAmbiguous => [.ezMayBeUsed, .ezRequiredWhenAmbiguous]
  | .substitutionMayChangeEZWithoutGeometryChange =>
      [.substitutionMayRelabelEZWithoutGeometryChange]
  | .ezNotationCitesEveryDoubleBond => [.allDoubleBondsCitedWithEZ]
  | .retroSixSevenConfigurationExplicitWhenNeeded => [.retroSixSevenStatedWhenNeeded]

@[simp] theorem forProvision_nonempty (row : Provision) :
    forProvision row ≠ [] := by
  cases row <;> simp [forProvision]

theorem forProvision_mem_all (row : Provision) :
    (forProvision row).Forall fun clause => clause ∈ all := by
  cases row <;> simp [forProvision, all]

theorem forProvision_sections_exact (row : Provision) :
    (forProvision row).Forall fun clause =>
      clause.normativeSection = row.normativeSection := by
  cases row <;> simp [forProvision, normativeSection, Provision.normativeSection]

theorem forProvision_injective : Function.Injective forProvision := by
  intro left right equal
  cases left <;> cases right <;> simp [forProvision] at equal ⊢

def provisionClauseOccurrences : List NormativeClause :=
  Provision.all.flatMap forProvision

@[simp] theorem provision_clause_occurrence_count :
    provisionClauseOccurrences.length = 14 := by
  decide

theorem provisionClauseOccurrences_nodup : provisionClauseOccurrences.Nodup := by
  decide

end NormativeClause

/-! ## Ret-2 ten-row stereoparent substituent table -/

inductive TerminalGroup where
  | hydroxymethyl
  | formyl
  | carboxyl
  | methyl
  | acetoxymethyl
  | aminomethyl
  | hydroxyiminomethyl
  | lysylIminomethyl
  | ethoxycarbonyl
  | betaDGlucopyranuronateEster
  deriving DecidableEq, Repr

namespace TerminalGroup

def all : List TerminalGroup :=
  [ .hydroxymethyl, .formyl, .carboxyl, .methyl, .acetoxymethyl
  , .aminomethyl, .hydroxyiminomethyl, .lysylIminomethyl
  , .ethoxycarbonyl, .betaDGlucopyranuronateEster ]

def sourceNotation : TerminalGroup → String
  | .hydroxymethyl => "CH2OH"
  | .formyl => "CHO"
  | .carboxyl => "CO2H"
  | .methyl => "CH3"
  | .acetoxymethyl => "CH2OCOCH3"
  | .aminomethyl => "CH2NH2"
  | .hydroxyiminomethyl => "CH=NOH"
  | .lysylIminomethyl => "CH=N[CH2]4CHNH2CO2H"
  | .ethoxycarbonyl => "CO2C2H5"
  | .betaDGlucopyranuronateEster =>
      "image A2b: 1-O-retinoyl-beta-D-glucopyranuronic acid substituent"

theorem sourceNotations_nodup : (all.map sourceNotation).Nodup := by
  decide

end TerminalGroup

structure StereoparentSubstituentRow where
  structureNumber : Nat
  terminalGroup : TerminalGroup
  embeddedFigure : Option ImageArtifact
  deriving DecidableEq, Repr

def stereoparentSubstituentRows : List StereoparentSubstituentRow :=
  [ ⟨1, .hydroxymethyl, none⟩
  , ⟨2, .formyl, none⟩
  , ⟨3, .carboxyl, none⟩
  , ⟨4, .methyl, none⟩
  , ⟨5, .acetoxymethyl, none⟩
  , ⟨6, .aminomethyl, none⟩
  , ⟨7, .hydroxyiminomethyl, none⟩
  , ⟨8, .lysylIminomethyl, none⟩
  , ⟨9, .ethoxycarbonyl, none⟩
  , ⟨10, .betaDGlucopyranuronateEster, some .glucuronideSubstituent⟩ ]

@[simp] theorem stereoparentSubstituentRow_count :
    stereoparentSubstituentRows.length = 10 := by
  decide

@[simp] theorem stereoparentSubstituent_structure_numbers_exact :
    stereoparentSubstituentRows.map StereoparentSubstituentRow.structureNumber =
      [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by
  decide

theorem stereoparentSubstituent_structure_numbers_nodup :
    (stereoparentSubstituentRows.map
      StereoparentSubstituentRow.structureNumber).Nodup := by
  rw [stereoparentSubstituent_structure_numbers_exact]
  decide

@[simp] theorem stereoparentSubstituent_terminal_groups_exact :
    stereoparentSubstituentRows.map StereoparentSubstituentRow.terminalGroup =
      TerminalGroup.all := by
  rfl

@[simp] theorem stereoparentSubstituent_embedded_figure_exact :
    stereoparentSubstituentRows.filterMap
      StereoparentSubstituentRow.embeddedFigure = [.glucuronideSubstituent] := by
  decide

/-! ## Source-section figure occurrences -/

structure SectionFigureOccurrence where
  sourceSection : NormativeSection
  artifacts : List ImageArtifact
  deriving DecidableEq, Repr

/-- Figure occurrence order is the literal order in the corrected `ret.html` recommendation. -/
def figureOccurrences : List SectionFigureOccurrence :=
  [ ⟨.ret2, [.stereoparentSkeleton, .glucuronideSubstituent]⟩
  , ⟨.ret4_3, [.didehydroretinol, .alphaVitaminA]⟩
  , ⟨.ret4_4, [.epoxyDihydroretinol, .fluororetinoate]⟩
  , ⟨.ret4_5, [.secoRetinol]⟩
  , ⟨.ret4_6, [.motretinideEtretinate, .acetylDinorRetinoicAcid]⟩
  , ⟨.ret4_7, [.anhydroVitaminA, .retroRetinylAcetate]⟩
  , ⟨.ret5_1, [.hydroxyAcetoxyRetinol]⟩
  , ⟨.ret5_2, [.cisRetinoidExamples, .retroRetinalOxime]⟩ ]

@[simp] theorem figureOccurrenceSection_count : figureOccurrences.length = 8 := by
  decide

theorem figureOccurrenceSections_nodup :
    (figureOccurrences.map SectionFigureOccurrence.sourceSection).Nodup := by
  decide

@[simp] theorem figureOccurrenceArtifacts_exact :
    figureOccurrences.flatMap SectionFigureOccurrence.artifacts =
      ImageArtifact.chemicalFigures := by
  decide

@[simp] theorem figureOccurrenceArtifact_count :
    (figureOccurrences.flatMap SectionFigureOccurrence.artifacts).length = 14 := by
  rw [figureOccurrenceArtifacts_exact]
  exact ImageArtifact.chemicalFigure_count

theorem figure_occurrences_match_graph_catalog :
    figureOccurrences.flatMap SectionFigureOccurrence.artifacts =
      FigureGraphTranscription.figureGraphFamilies.map
        FigureGraphTranscription.FigureGraphFamilyEntry.artifact := by
  rw [figureOccurrenceArtifacts_exact,
    FigureGraphTranscription.figureGraphFamilies_artifacts_exact]



structure AutomatedProseTableInspection where
  reviewerIdentity : String
  reviewDate : String
  sourceBundleSha256 : String
  sourceHtmlSha256 : String
  errataHtmlSha256 : String
  bundleDigestMatched : Bool
  normativeSectionCount : Nat
  normativeClauseCount : Nat
  stereoparentTableRowCount : Nat
  figureOccurrenceCount : Nat
  provisionEnumerationConfirmed : Bool
  proseTableCoverageConfirmed : Bool
  figureGraphTranscriptionsReviewed : Bool
  humanSignoffObtained : Bool
  limitations : String
  deriving DecidableEq, Repr

def currentAutomatedProseTableInspection : AutomatedProseTableInspection where
  reviewerIdentity := "automated-record-383f307281f3e8334bf1a04ad8470f83"
  reviewDate := "record-9ac02191cea601ac5337c9c57c2b5228"
  sourceBundleSha256 :=
    "e7fdceac5572f5610d011019d44363b4c1f61a0cfd696ad4255ae0bd836d0f01"
  sourceHtmlSha256 :=
    "e15b0826a2ca2fca480925b0a306f607703358f67e0a758c0d28ca88efc72d5a"
  errataHtmlSha256 :=
    "f17c2ca0543c91353bc8c4a22701b16470ca891fa5e0f0120659f1502a44ece7"
  bundleDigestMatched := true
  normativeSectionCount := 19
  normativeClauseCount := 62
  stereoparentTableRowCount := 10
  figureOccurrenceCount := 14
  provisionEnumerationConfirmed := true
  proseTableCoverageConfirmed := true
  figureGraphTranscriptionsReviewed := false
  humanSignoffObtained := false
  limitations :=
    "automated-record-07150d11977bbb2ba8d3aa089abe2877" ++
    "record-b043c4b89618309bf0407b09b9dc92aa" ++
    "record-861f5cf94abc2149a3cb08a49d92cf98" ++
    "record-b0ea0cc37c3f59996161a99505b45ff2"

@[simp] theorem inspected_bundle_matches_frozen_snapshot :
    currentAutomatedProseTableInspection.sourceBundleSha256 =
      (P10DelegatedAuthorityCorpus.snapshot .retinoid1981).bundleSha256 := by
  rfl

@[simp] theorem current_automated_prose_table_inspection_boundary_exact :
    currentAutomatedProseTableInspection.humanSignoffObtained = false ∧
      currentAutomatedProseTableInspection.provisionEnumerationConfirmed = true ∧
        currentAutomatedProseTableInspection.proseTableCoverageConfirmed = true ∧
          currentAutomatedProseTableInspection.figureGraphTranscriptionsReviewed = false ∧
      currentAutomatedProseTableInspection.normativeClauseCount = 62 ∧
        currentAutomatedProseTableInspection.stereoparentTableRowCount = 10 ∧
          currentAutomatedProseTableInspection.figureOccurrenceCount = 14 := by
  decide

theorem current_automated_counts_come_from_exact_ledgers :
    currentAutomatedProseTableInspection.normativeSectionCount = NormativeSection.all.length ∧
      currentAutomatedProseTableInspection.normativeClauseCount = NormativeClause.all.length ∧
        currentAutomatedProseTableInspection.stereoparentTableRowCount =
          stereoparentSubstituentRows.length ∧
          currentAutomatedProseTableInspection.figureOccurrenceCount =
            (figureOccurrences.flatMap SectionFigureOccurrence.artifacts).length := by
  decide

end Ledger
end SourceAudit
end Retinoid1981
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.SourceAudit.Ledger.NormativeClause.section_coverage_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.SourceAudit.Ledger.NormativeClause.every_section_covered
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.SourceAudit.Ledger.NormativeClause.forProvision_injective
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.SourceAudit.Ledger.NormativeClause.forProvision_sections_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.SourceAudit.Ledger.NormativeClause.provisionClauseOccurrences_nodup
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.SourceAudit.Ledger.stereoparentSubstituent_structure_numbers_nodup
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.SourceAudit.Ledger.figureOccurrenceArtifacts_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.SourceAudit.Ledger.figure_occurrences_match_graph_catalog
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.SourceAudit.Ledger.current_automated_prose_table_inspection_boundary_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.SourceAudit.Ledger.current_automated_counts_come_from_exact_ledgers
