import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceDataBatch
import TetraStereo.KernelOnly

set_option autoImplicit false










namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning

open GlobalNonDescriptorIndexedSourceData

inductive SemanticDomain where
  | glycosideDefinition
  | oxygenGlycoside
  | chalcogenGlycoside
  | glycosylHalide
  | nitrogenLinked
  | carbonLinked
  | heteroRing
  | carbaRing
  | bridge
  | fusion
  | spiro
  | untranscribedPrintedExample
  deriving DecidableEq, Repr

def semanticDomain : Carbohydrate1996GlycosidesRings.Provision → SemanticDomain
  | .originalGlycosideDefinitionMixedCyclicAcetal
  | .extendedGlycosidicReplacementAtoms
  | .thioAndSelenoglycosideGenericTermsLegitimate
  | .nGlycosideImproperPreferGlycosylamine
  | .cGlycosideTerminologyLessAcceptable
  | .aglyconeAndGlyconeTerms => .glycosideDefinition
  | .glycosideThreeNamingMethods
  | .classicalGlycosideEToIdeAndSeparateRWord
  | .classicalMethodForSimpleR
  | .glycosyloxyPrefixIncludesOxygen
  | .oGlycosylPrefixExcludesOxygen
  | .glycuronosylPracticeUnsatisfactory
  | .glycosyloxyuronicTwoWordPrefixTradeoff
  | .glycosideSubstituentsUseResidueMethods => .oxygenGlycoside
  | .thioglycosideThreeNamingMethods
  | .glycosylthioIncludesSulfur
  | .sGlycosylExcludesSulfur
  | .thioglycosideOxidesUseFunctionalClass
  | .selenoglycosidesAnalogousToThioglycosides => .chalcogenGlycoside
  | .glycosylHalideDefinition
  | .glycosylPseudohalidesAnalogous => .glycosylHalide
  | .nGlycosylDerivativesPreferGlycosylamine
  | .complexHeterocyclicAminesUseSameMethod => .nitrogenLinked
  | .cLinkedFormalWaterEliminationUsesGlycosylPrefix
  | .cLinkedNamesAvoidCGlycoside
  | .cGlycosideMisnomerStronglyDiscouraged => .carbonLinked
  | .ringNitrogenPhosphorusUsesAminoPhosphanylSugarParent
  | .heteroRingSizeDesignatorsMatchOxygenAnalogues
  | .anhydroExtendedToAminoHydroxyWaterLoss
  | .azaPhosphaReservedForCarbonReplacement
  | .iminoSugarClassNameAllowed => .heteroRing
  | .carbaIsNondetachableRingOxygenReplacement
  | .carbaLocantUsesNonanomericAdjacentAtomPlusA
  | .carbaLocantDiffersFromDraftNaturalProductRule
  | .newCarbaCarbonAdditionalStereochemistryUsesRS
  | .carbaStructuresMayAlsoUseCyclitolNames => .carbaRing
  | .bridgeNamingHasPrefixAndFusionApproaches
  | .bridgeRecommendationsProvisional
  | .heteroatomBridgePrefixMeansTwoHeteroSubstitutions
  | .externalBridgeHeteroatomsBelongToBridge
  | .carbonBridgeMeansDoubleCSubstitution
  | .ylideneBridgePrefixTraditionalButGenerallyDeprecated
  | .cycloPrefixMayNameSingleBondBridge => .bridge
  | .fusionCarbohydrateFirstParenthesizedAndEToO
  | .newFusionRingBondsEquivalentToHydroxy
  | .carbohydrateSubstituentsInsideFusionParentheses
  | .newRingSubstituentsPrecedeCarbohydrateTerm
  | .newRingNumberingFollowsFusionLocants
  | .carbohydrateFirstOverridesGeneralFusionOrdering
  | .pyranosoRecommendedOverPyrano => .fusion
  | .spiroUsesGeneralProcedures
  | .spiroJunctionPrefixesAdjacentToCarbohydrateStem
  | .spiroCarbohydrateComponentCitedFirst
  | .spiroJunctionConfigurationUsesRS
  | .spiroDisaccharidePrefersGemBivalentPrefix => .spiro
  | .printedExample _ => .untranscribedPrintedExample

def linkTermInventory :
    List (Carbohydrate1996GlycosidesRings.GlycosidicLinkAtom ×
      Carbohydrate1996GlycosidesRings.RecommendedTerm) :=
  [ (.oxygen, Carbohydrate1996GlycosidesRings.recommendedTerm .oxygen)
  , (.sulfur, Carbohydrate1996GlycosidesRings.recommendedTerm .sulfur)
  , (.selenium, Carbohydrate1996GlycosidesRings.recommendedTerm .selenium)
  , (.nitrogen, Carbohydrate1996GlycosidesRings.recommendedTerm .nitrogen)
  , (.carbon, Carbohydrate1996GlycosidesRings.recommendedTerm .carbon) ]

def newRingCenterInventory :
    List (Carbohydrate1996GlycosidesRings.NewRingCenter ×
      Carbohydrate1996GlycosidesRings.DescriptorFamily) :=
  [ (.carbaCarbon,
      Carbohydrate1996GlycosidesRings.descriptorForNewRingCenter .carbaCarbon)
  , (.spiroJunction,
      Carbohydrate1996GlycosidesRings.descriptorForNewRingCenter .spiroJunction) ]

def fusionJunctionInventory :
    List (Bool × Carbohydrate1996GlycosidesRings.FusionJunctionSurrogate) :=
  [ (false, Carbohydrate1996GlycosidesRings.fusionJunctionSurrogate false)
  , (true, Carbohydrate1996GlycosidesRings.fusionJunctionSurrogate true) ]

inductive SourceAssertion where
  | semanticClause (row : Carbohydrate1996GlycosidesRings.Provision)
  | nGlycosideImproperPreferGlycosylamine
      (atom : Carbohydrate1996GlycosidesRings.GlycosidicLinkAtom)
      (term : Carbohydrate1996GlycosidesRings.RecommendedTerm)
  | cGlycosideTerminologyLessAcceptable
      (atom : Carbohydrate1996GlycosidesRings.GlycosidicLinkAtom)
      (term : Carbohydrate1996GlycosidesRings.RecommendedTerm)
  | newCarbaCarbonAdditionalStereochemistryUsesRS
      (center : Carbohydrate1996GlycosidesRings.NewRingCenter)
      (descriptor : Carbohydrate1996GlycosidesRings.DescriptorFamily)
  | newFusionRingBondsEquivalentToHydroxy
      (hydroxyStillPresent : Bool)
      (surrogate : Carbohydrate1996GlycosidesRings.FusionJunctionSurrogate)
  | spiroJunctionConfigurationUsesRS
      (center : Carbohydrate1996GlycosidesRings.NewRingCenter)
      (descriptor : Carbohydrate1996GlycosidesRings.DescriptorFamily)
  | untranscribedPrintedExample
      (row : Carbohydrate1996GlycosidesRings.PrintedExample) (sourceKey : String)
  deriving Repr

def sourceAssertion : Carbohydrate1996GlycosidesRings.Provision → SourceAssertion
  | .nGlycosideImproperPreferGlycosylamine =>
      .nGlycosideImproperPreferGlycosylamine .nitrogen
        (Carbohydrate1996GlycosidesRings.recommendedTerm .nitrogen)
  | .cGlycosideTerminologyLessAcceptable =>
      .cGlycosideTerminologyLessAcceptable .carbon
        (Carbohydrate1996GlycosidesRings.recommendedTerm .carbon)
  | .newCarbaCarbonAdditionalStereochemistryUsesRS =>
      .newCarbaCarbonAdditionalStereochemistryUsesRS .carbaCarbon
        (Carbohydrate1996GlycosidesRings.descriptorForNewRingCenter .carbaCarbon)
  | .newFusionRingBondsEquivalentToHydroxy =>
      .newFusionRingBondsEquivalentToHydroxy false
        (Carbohydrate1996GlycosidesRings.fusionJunctionSurrogate false)
  | .spiroJunctionConfigurationUsesRS =>
      .spiroJunctionConfigurationUsesRS .spiroJunction
        (Carbohydrate1996GlycosidesRings.descriptorForNewRingCenter .spiroJunction)
  | .printedExample row => .untranscribedPrintedExample row row.sourceKey
  | row => .semanticClause row

def SourceAssertion.provision : SourceAssertion → Carbohydrate1996GlycosidesRings.Provision
  | .semanticClause row => row
  | .nGlycosideImproperPreferGlycosylamine _ _ => .nGlycosideImproperPreferGlycosylamine
  | .cGlycosideTerminologyLessAcceptable _ _ => .cGlycosideTerminologyLessAcceptable
  | .newCarbaCarbonAdditionalStereochemistryUsesRS _ _ =>
      .newCarbaCarbonAdditionalStereochemistryUsesRS
  | .newFusionRingBondsEquivalentToHydroxy _ _ => .newFusionRingBondsEquivalentToHydroxy
  | .spiroJunctionConfigurationUsesRS _ _ => .spiroJunctionConfigurationUsesRS
  | .untranscribedPrintedExample row _ => .printedExample row

@[simp] theorem sourceAssertion_provision_exact
    (row : Carbohydrate1996GlycosidesRings.Provision) :
    (sourceAssertion row).provision = row := by
  cases row <;> rfl

structure SourceMeaning where
  sourceKey : String
  semanticDomain : SemanticDomain
  assertion : SourceAssertion
  deriving Repr

def sourceMeaning (row : Carbohydrate1996GlycosidesRings.Provision) : SourceMeaning :=
  ⟨row.sourceKey, semanticDomain row, sourceAssertion row⟩

@[simp] theorem sourceMeaning_key_exact (row : Carbohydrate1996GlycosidesRings.Provision) :
    (sourceMeaning row).sourceKey = row.sourceKey := by rfl

@[simp] theorem sourceMeaning_domain_exact (row : Carbohydrate1996GlycosidesRings.Provision) :
    (sourceMeaning row).semanticDomain = semanticDomain row := by rfl

theorem sourceMeaning_injective : Function.Injective sourceMeaning := by
  intro left right equal
  have assertionEqual : (sourceMeaning left).assertion = (sourceMeaning right).assertion :=
    congrArg SourceMeaning.assertion equal
  have provisionEqual := congrArg SourceAssertion.provision assertionEqual
  simpa [sourceMeaning] using provisionEqual

def fullFamilyRows : List Carbohydrate1996GlycosidesRings.Provision :=
  Carbohydrate1996GlycosidesRings.Provision.all

def fullFamilyProvisions : List IUPACNormativeProvision :=
  fullFamilyRows.map IUPACNormativeProvision.carbohydrate1996GlycosidesRings

def completionRows : List Carbohydrate1996GlycosidesRings.Provision :=
  Carbohydrate1996GlycosidesRings.Provision.base

def completionProvisions : List IUPACNormativeProvision :=
  completionRows.map IUPACNormativeProvision.carbohydrate1996GlycosidesRings

def untranscribedPrintedRows : List Carbohydrate1996GlycosidesRings.Provision :=
  Carbohydrate1996GlycosidesRings.PrintedExample.all.map
    Carbohydrate1996GlycosidesRings.Provision.printedExample

def untranscribedPrintedProvisions : List IUPACNormativeProvision :=
  untranscribedPrintedRows.map IUPACNormativeProvision.carbohydrate1996GlycosidesRings

/-- The exact printed-example source rows, now carrying their official textual name ledger. -/
def printedRows : List Carbohydrate1996GlycosidesRings.PrintedExample :=
  Carbohydrate1996GlycosidesRings.PrintedExample.all

def printedProvisions : List IUPACNormativeProvision :=
  printedRows.map fun row =>
    IUPACNormativeProvision.carbohydrate1996GlycosidesRings (.printedExample row)

def completionBatch : GlobalNonDescriptorSourceMeaningBatch completionProvisions :=
  totalMeaningBatch completionRows IUPACNormativeProvision.carbohydrate1996GlycosidesRings
    sourceMeaning (by intro _row; rfl)

def printedBatch : GlobalNonDescriptorSourceMeaningBatch printedProvisions :=
  totalMeaningBatch printedRows
    (fun row => IUPACNormativeProvision.carbohydrate1996GlycosidesRings (.printedExample row))
    Carbohydrate1996GlycosidesRings.PrintedExample.data (by intro _row; rfl)

def materializedProvisions : List IUPACNormativeProvision :=
  completionProvisions ++ printedProvisions

def materializedBatch : GlobalNonDescriptorSourceMeaningBatch materializedProvisions :=
  completionBatch.append printedBatch

@[simp] theorem full_family_provisions_exact :
    fullFamilyProvisions = carbohydrate1996GlycosidesRingsSemanticsSlice := by rfl

@[simp] theorem full_family_provision_count : fullFamilyProvisions.length = 113 := by
  simp [fullFamilyProvisions, fullFamilyRows]

@[simp] theorem completion_provision_count : completionProvisions.length = 55 := by
  simp [completionProvisions, completionRows, Carbohydrate1996GlycosidesRings.Provision.base]

@[simp] theorem completion_entry_count : completionBatch.entries.length = 55 := by
  rw [completionBatch.entries_length, completion_provision_count]

@[simp] theorem untranscribed_printed_provision_count :
    untranscribedPrintedProvisions.length = 58 := by
  simp [untranscribedPrintedProvisions, untranscribedPrintedRows]

@[simp] theorem printed_provisions_eq_prior_untranscribed :
    printedProvisions = untranscribedPrintedProvisions := by
  simp [printedProvisions, printedRows, untranscribedPrintedProvisions,
    untranscribedPrintedRows, List.map_map]

@[simp] theorem printed_provision_count : printedProvisions.length = 58 := by
  simp [printedProvisions, printedRows]

@[simp] theorem printed_entry_count : printedBatch.entries.length = 58 := by
  rw [printedBatch.entries_length, printed_provision_count]

theorem semantic_then_untranscribed_exact_source_order :
    completionProvisions ++ untranscribedPrintedProvisions =
      carbohydrate1996GlycosidesRingsSemanticsSlice := by
  rw [← full_family_provisions_exact]
  simp only [completionProvisions, untranscribedPrintedProvisions,
    fullFamilyProvisions, ← List.map_append]
  rfl

theorem completion_disjoint_untranscribed_printed :
    completionProvisions.Disjoint untranscribedPrintedProvisions := by
  apply List.disjoint_of_nodup_append
  rw [semantic_then_untranscribed_exact_source_order]
  exact Carbohydrate1996GlycosidesRings.Provision.all_nodup.map
    (by intro left right equal; cases equal; rfl)

theorem completion_provisions_nodup : completionProvisions.Nodup := by
  exact Carbohydrate1996GlycosidesRings.Provision.all_nodup.of_append_left.map
    (by intro left right equal; cases equal; rfl)

theorem untranscribed_printed_provisions_nodup : untranscribedPrintedProvisions.Nodup := by
  exact Carbohydrate1996GlycosidesRings.Provision.all_nodup.of_append_right.map
    (by intro left right equal; cases equal; rfl)

theorem printed_provisions_nodup : printedProvisions.Nodup := by
  rw [printed_provisions_eq_prior_untranscribed]
  exact untranscribed_printed_provisions_nodup

theorem materialized_provisions_exact : materializedProvisions = fullFamilyProvisions := by
  rw [materializedProvisions, printed_provisions_eq_prior_untranscribed,
    semantic_then_untranscribed_exact_source_order, full_family_provisions_exact]

@[simp] theorem materialized_provision_count : materializedProvisions.length = 113 := by
  rw [materialized_provisions_exact, full_family_provision_count]

theorem materialized_provisions_nodup : materializedProvisions.Nodup := by
  rw [materialized_provisions_exact, fullFamilyProvisions, fullFamilyRows]
  exact Carbohydrate1996GlycosidesRings.Provision.all_nodup.map
    (by intro left right equal; cases equal; rfl)

theorem every_untranscribed_provision_is_printed_example
    (provision : IUPACNormativeProvision) (member : provision ∈ untranscribedPrintedProvisions) :
    ∃ row : Carbohydrate1996GlycosidesRings.PrintedExample,
      provision = .carbohydrate1996GlycosidesRings (.printedExample row) := by
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
      input.StructurallyWellFormed ∧
        entry.reference.toReference.Applicable input ∧
          entry.reference.toReference.Judges input observation :=
  entry.admittedJudgment

theorem every_printed_entry_nonvacuous
    (entry : GlobalNonDescriptorSourceMeaningEntry) (_member : entry ∈ printedBatch.entries) :
    ∃ input, ∃ observation : entry.reference.toReference.Observation,
      input.StructurallyWellFormed ∧
        entry.reference.toReference.Applicable input ∧
          entry.reference.toReference.Judges input observation :=
  entry.admittedJudgment

theorem source_audit_still_open :
    ¬IUPACNormativeSource.ProvisionAuditComplete .carbohydrateRecommendations1996 := by
  exact IUPACNormativeSource.provisionAuditIncomplete_of_figure_review_open _ rfl

end GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.full_family_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.semantic_then_untranscribed_exact_source_order
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.sourceMeaning_injective
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.completion_entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.every_untranscribed_provision_is_printed_example
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printed_provisions_eq_prior_untranscribed
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.materialized_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.printed_entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.materialized_entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.every_completion_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.every_printed_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateGlycosideRingSourceMeaning.source_audit_still_open
