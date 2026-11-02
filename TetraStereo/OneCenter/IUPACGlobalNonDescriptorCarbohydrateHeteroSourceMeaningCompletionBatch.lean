import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceDataBatch
import TetraStereo.KernelOnly

set_option autoImplicit false











namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateHeteroSourceMeaning

open GlobalNonDescriptorIndexedSourceData

inductive SemanticDomain where
  | oSubstitution
  | phosphorusSubstitution
  | sulfurSubstitution
  | aminoSubstitution
  | anhydride
  | printedExample
  deriving DecidableEq, Repr

def semanticDomain : Carbohydrate1996HeteroSubstitutionAnhydride.Provision → SemanticDomain
  | .alcoholicHydroxyHydrogenReplacementIsOSubstitution
  | .oLocantNotRepeatedForSameMultipleReplacement | .numberLocantsSpecifyPositions
  | .identicalFullSubstitutionNeedsNoNumberLocants | .esterEtherPeriphrasesMayIndex
  | .anomericOAcylUsesOAcylButOAlkylIsGlycoside => .oSubstitution
  | .biochemicalPhosphateIgnoresIonizationAndCounterion | .phosphonoAndPhosphonatoPrefixes
  | .biochemicalPhosphoPrefix | .multipleIndependentPhosphatesUseBisTris
  | .diphosphateMeansDiphosphoricAcidEster | .capitalPAbbreviationConvention
  | .phosphonateExamplesDefineTerminology | .phosphorusSubstitutionUsesStandardRules
  | .pcLinkedGroupTwoNamingRoutes | .phosphinateUsesPhosphonateMethods
  | .twoPCBondExamplesRouteToThirtyOne => .phosphorusSubstitution
  | .sulfoAndSulfonatoPrefixes | .sulfateMayBePostposedWithLocant
  | .papsNamedAsAcylSulfate => .sulfurSubstitution
  | .substitutedAminoGroupHasTwoNamingMethods
  | .completeSubstitutedAminoPrefixRetainsHydroxyConfigurationRole
  | .trivialAminoSugarUsesItalicNPrefix | .heteroatomSubstitutionUsesCarbonLocantThenElement
  | .sameHeteroatomSubstituentsGrouped | .heteroatomKindsAlphabetized
  | .superscriptHeteroatomLocantsUnusualInCarbohydrates => .aminoSubstitution
  | .intramolecularEtherIsFormalWaterLoss | .anhydroPrefixUsesTwoHydroxyLocants
  | .anhydroIsDetachableAlphabetizedPrefix | .anomericHydroxyAnhydridesUseSameProcedure
  | .anomericAnhydrideRingPreference | .threeAndFourMemberedRingsPreferAnhydro
  | .anhydroTrivialNamesNotRecommended => .anhydride
  | .printedExample _ => .printedExample

def phosphateMultiplicityInventory :
    List (Carbohydrate1996HeteroSubstitutionAnhydride.PhosphateMultiplicity × String) :=
  [ (.bisphosphate,
      Carbohydrate1996HeteroSubstitutionAnhydride.PhosphateMultiplicity.bisphosphate.meaning)
  , (.diphosphate,
      Carbohydrate1996HeteroSubstitutionAnhydride.PhosphateMultiplicity.diphosphate.meaning) ]

def aminoRoleInventory :
    List (Carbohydrate1996HeteroSubstitutionAnhydride.AminoNamingMethod ×
      Carbohydrate1996HeteroSubstitutionAnhydride.ConfigurationalRole) :=
  [ (.completeSubstitutedAminoPrefix,
      Carbohydrate1996HeteroSubstitutionAnhydride.substitutedAminoConfigurationalRole
        .completeSubstitutedAminoPrefix)
  , (.trivialNameWithNPrefix,
      Carbohydrate1996HeteroSubstitutionAnhydride.substitutedAminoConfigurationalRole
        .trivialNameWithNPrefix) ]

def heteroatomRankInventory :
    List (Carbohydrate1996HeteroSubstitutionAnhydride.HeteroatomKind × Nat) :=
  [ (.nitrogen,
      Carbohydrate1996HeteroSubstitutionAnhydride.heteroatomAlphabeticalRank .nitrogen)
  , (.oxygen,
      Carbohydrate1996HeteroSubstitutionAnhydride.heteroatomAlphabeticalRank .oxygen) ]

def anhydridePreferenceInventory :
    List (Carbohydrate1996HeteroSubstitutionAnhydride.AnhydrideRingDesignator × Nat) :=
  [ (.septanose,
      Carbohydrate1996HeteroSubstitutionAnhydride.anomericAnhydridePreference .septanose)
  , (.furanose,
      Carbohydrate1996HeteroSubstitutionAnhydride.anomericAnhydridePreference .furanose)
  , (.pyranose,
      Carbohydrate1996HeteroSubstitutionAnhydride.anomericAnhydridePreference .pyranose) ]

def tinyRingInventory : List (Nat × Bool) :=
  [ (3, Carbohydrate1996HeteroSubstitutionAnhydride.tinyRingUsesAnhydro 3)
  , (4, Carbohydrate1996HeteroSubstitutionAnhydride.tinyRingUsesAnhydro 4)
  , (5, Carbohydrate1996HeteroSubstitutionAnhydride.tinyRingUsesAnhydro 5) ]

inductive SourceAssertion where
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
      (inventory : List (Carbohydrate1996HeteroSubstitutionAnhydride.PhosphateMultiplicity × String))
  | diphosphateMeansDiphosphoricAcidEster
      (multiplicity : Carbohydrate1996HeteroSubstitutionAnhydride.PhosphateMultiplicity)
      (meaning : String)
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
      (inventory : List (Carbohydrate1996HeteroSubstitutionAnhydride.AminoNamingMethod ×
        Carbohydrate1996HeteroSubstitutionAnhydride.ConfigurationalRole))
  | completeSubstitutedAminoPrefixRetainsHydroxyConfigurationRole
      (inventory : List (Carbohydrate1996HeteroSubstitutionAnhydride.AminoNamingMethod ×
        Carbohydrate1996HeteroSubstitutionAnhydride.ConfigurationalRole))
  | trivialAminoSugarUsesItalicNPrefix
      (method : Carbohydrate1996HeteroSubstitutionAnhydride.AminoNamingMethod)
      (role : Carbohydrate1996HeteroSubstitutionAnhydride.ConfigurationalRole)
  | heteroatomSubstitutionUsesCarbonLocantThenElement
  | sameHeteroatomSubstituentsGrouped
  | heteroatomKindsAlphabetized
      (inventory : List (Carbohydrate1996HeteroSubstitutionAnhydride.HeteroatomKind × Nat))
  | superscriptHeteroatomLocantsUnusualInCarbohydrates
  | intramolecularEtherIsFormalWaterLoss
  | anhydroPrefixUsesTwoHydroxyLocants
  | anhydroIsDetachableAlphabetizedPrefix
  | anomericHydroxyAnhydridesUseSameProcedure
  | anomericAnhydrideRingPreference
      (inventory : List (Carbohydrate1996HeteroSubstitutionAnhydride.AnhydrideRingDesignator × Nat))
  | threeAndFourMemberedRingsPreferAnhydro (inventory : List (Nat × Bool))
  | anhydroTrivialNamesNotRecommended
  | printedExample (row : Carbohydrate1996HeteroSubstitutionAnhydride.PrintedExample)
      (data : Carbohydrate1996HeteroSubstitutionAnhydride.PrintedExampleData)
  deriving Repr

def sourceAssertion : Carbohydrate1996HeteroSubstitutionAnhydride.Provision → SourceAssertion
  | .alcoholicHydroxyHydrogenReplacementIsOSubstitution =>
      .alcoholicHydroxyHydrogenReplacementIsOSubstitution
  | .oLocantNotRepeatedForSameMultipleReplacement => .oLocantNotRepeatedForSameMultipleReplacement
  | .numberLocantsSpecifyPositions => .numberLocantsSpecifyPositions
  | .identicalFullSubstitutionNeedsNoNumberLocants => .identicalFullSubstitutionNeedsNoNumberLocants
  | .esterEtherPeriphrasesMayIndex => .esterEtherPeriphrasesMayIndex
  | .anomericOAcylUsesOAcylButOAlkylIsGlycoside => .anomericOAcylUsesOAcylButOAlkylIsGlycoside
  | .biochemicalPhosphateIgnoresIonizationAndCounterion =>
      .biochemicalPhosphateIgnoresIonizationAndCounterion
  | .phosphonoAndPhosphonatoPrefixes => .phosphonoAndPhosphonatoPrefixes
  | .biochemicalPhosphoPrefix => .biochemicalPhosphoPrefix
  | .multipleIndependentPhosphatesUseBisTris =>
      .multipleIndependentPhosphatesUseBisTris phosphateMultiplicityInventory
  | .diphosphateMeansDiphosphoricAcidEster =>
      .diphosphateMeansDiphosphoricAcidEster .diphosphate
        Carbohydrate1996HeteroSubstitutionAnhydride.PhosphateMultiplicity.diphosphate.meaning
  | .capitalPAbbreviationConvention => .capitalPAbbreviationConvention
  | .phosphonateExamplesDefineTerminology => .phosphonateExamplesDefineTerminology
  | .phosphorusSubstitutionUsesStandardRules => .phosphorusSubstitutionUsesStandardRules
  | .pcLinkedGroupTwoNamingRoutes => .pcLinkedGroupTwoNamingRoutes
  | .phosphinateUsesPhosphonateMethods => .phosphinateUsesPhosphonateMethods
  | .twoPCBondExamplesRouteToThirtyOne => .twoPCBondExamplesRouteToThirtyOne
  | .sulfoAndSulfonatoPrefixes => .sulfoAndSulfonatoPrefixes
  | .sulfateMayBePostposedWithLocant => .sulfateMayBePostposedWithLocant
  | .papsNamedAsAcylSulfate => .papsNamedAsAcylSulfate
  | .substitutedAminoGroupHasTwoNamingMethods =>
      .substitutedAminoGroupHasTwoNamingMethods aminoRoleInventory
  | .completeSubstitutedAminoPrefixRetainsHydroxyConfigurationRole =>
      .completeSubstitutedAminoPrefixRetainsHydroxyConfigurationRole aminoRoleInventory
  | .trivialAminoSugarUsesItalicNPrefix =>
      .trivialAminoSugarUsesItalicNPrefix .trivialNameWithNPrefix
        (Carbohydrate1996HeteroSubstitutionAnhydride.substitutedAminoConfigurationalRole
          .trivialNameWithNPrefix)
  | .heteroatomSubstitutionUsesCarbonLocantThenElement =>
      .heteroatomSubstitutionUsesCarbonLocantThenElement
  | .sameHeteroatomSubstituentsGrouped => .sameHeteroatomSubstituentsGrouped
  | .heteroatomKindsAlphabetized => .heteroatomKindsAlphabetized heteroatomRankInventory
  | .superscriptHeteroatomLocantsUnusualInCarbohydrates =>
      .superscriptHeteroatomLocantsUnusualInCarbohydrates
  | .intramolecularEtherIsFormalWaterLoss => .intramolecularEtherIsFormalWaterLoss
  | .anhydroPrefixUsesTwoHydroxyLocants => .anhydroPrefixUsesTwoHydroxyLocants
  | .anhydroIsDetachableAlphabetizedPrefix => .anhydroIsDetachableAlphabetizedPrefix
  | .anomericHydroxyAnhydridesUseSameProcedure => .anomericHydroxyAnhydridesUseSameProcedure
  | .anomericAnhydrideRingPreference =>
      .anomericAnhydrideRingPreference anhydridePreferenceInventory
  | .threeAndFourMemberedRingsPreferAnhydro =>
      .threeAndFourMemberedRingsPreferAnhydro tinyRingInventory
  | .anhydroTrivialNamesNotRecommended => .anhydroTrivialNamesNotRecommended
  | .printedExample row => .printedExample row row.data

def SourceAssertion.provision :
    SourceAssertion → Carbohydrate1996HeteroSubstitutionAnhydride.Provision
  | .alcoholicHydroxyHydrogenReplacementIsOSubstitution =>
      .alcoholicHydroxyHydrogenReplacementIsOSubstitution
  | .oLocantNotRepeatedForSameMultipleReplacement => .oLocantNotRepeatedForSameMultipleReplacement
  | .numberLocantsSpecifyPositions => .numberLocantsSpecifyPositions
  | .identicalFullSubstitutionNeedsNoNumberLocants => .identicalFullSubstitutionNeedsNoNumberLocants
  | .esterEtherPeriphrasesMayIndex => .esterEtherPeriphrasesMayIndex
  | .anomericOAcylUsesOAcylButOAlkylIsGlycoside => .anomericOAcylUsesOAcylButOAlkylIsGlycoside
  | .biochemicalPhosphateIgnoresIonizationAndCounterion =>
      .biochemicalPhosphateIgnoresIonizationAndCounterion
  | .phosphonoAndPhosphonatoPrefixes => .phosphonoAndPhosphonatoPrefixes
  | .biochemicalPhosphoPrefix => .biochemicalPhosphoPrefix
  | .multipleIndependentPhosphatesUseBisTris _ => .multipleIndependentPhosphatesUseBisTris
  | .diphosphateMeansDiphosphoricAcidEster _ _ => .diphosphateMeansDiphosphoricAcidEster
  | .capitalPAbbreviationConvention => .capitalPAbbreviationConvention
  | .phosphonateExamplesDefineTerminology => .phosphonateExamplesDefineTerminology
  | .phosphorusSubstitutionUsesStandardRules => .phosphorusSubstitutionUsesStandardRules
  | .pcLinkedGroupTwoNamingRoutes => .pcLinkedGroupTwoNamingRoutes
  | .phosphinateUsesPhosphonateMethods => .phosphinateUsesPhosphonateMethods
  | .twoPCBondExamplesRouteToThirtyOne => .twoPCBondExamplesRouteToThirtyOne
  | .sulfoAndSulfonatoPrefixes => .sulfoAndSulfonatoPrefixes
  | .sulfateMayBePostposedWithLocant => .sulfateMayBePostposedWithLocant
  | .papsNamedAsAcylSulfate => .papsNamedAsAcylSulfate
  | .substitutedAminoGroupHasTwoNamingMethods _ => .substitutedAminoGroupHasTwoNamingMethods
  | .completeSubstitutedAminoPrefixRetainsHydroxyConfigurationRole _ =>
      .completeSubstitutedAminoPrefixRetainsHydroxyConfigurationRole
  | .trivialAminoSugarUsesItalicNPrefix _ _ => .trivialAminoSugarUsesItalicNPrefix
  | .heteroatomSubstitutionUsesCarbonLocantThenElement =>
      .heteroatomSubstitutionUsesCarbonLocantThenElement
  | .sameHeteroatomSubstituentsGrouped => .sameHeteroatomSubstituentsGrouped
  | .heteroatomKindsAlphabetized _ => .heteroatomKindsAlphabetized
  | .superscriptHeteroatomLocantsUnusualInCarbohydrates =>
      .superscriptHeteroatomLocantsUnusualInCarbohydrates
  | .intramolecularEtherIsFormalWaterLoss => .intramolecularEtherIsFormalWaterLoss
  | .anhydroPrefixUsesTwoHydroxyLocants => .anhydroPrefixUsesTwoHydroxyLocants
  | .anhydroIsDetachableAlphabetizedPrefix => .anhydroIsDetachableAlphabetizedPrefix
  | .anomericHydroxyAnhydridesUseSameProcedure => .anomericHydroxyAnhydridesUseSameProcedure
  | .anomericAnhydrideRingPreference _ => .anomericAnhydrideRingPreference
  | .threeAndFourMemberedRingsPreferAnhydro _ => .threeAndFourMemberedRingsPreferAnhydro
  | .anhydroTrivialNamesNotRecommended => .anhydroTrivialNamesNotRecommended
  | .printedExample row _ => .printedExample row

@[simp] theorem sourceAssertion_provision_exact
    (row : Carbohydrate1996HeteroSubstitutionAnhydride.Provision) :
    (sourceAssertion row).provision = row := by
  cases row <;> rfl

structure SourceMeaning where
  sourceKey : String
  semanticDomain : SemanticDomain
  assertion : SourceAssertion
  deriving Repr

def sourceMeaning (row : Carbohydrate1996HeteroSubstitutionAnhydride.Provision) : SourceMeaning :=
  ⟨row.sourceKey, semanticDomain row, sourceAssertion row⟩

@[simp] theorem sourceMeaning_key_exact
    (row : Carbohydrate1996HeteroSubstitutionAnhydride.Provision) :
    (sourceMeaning row).sourceKey = row.sourceKey := by rfl

@[simp] theorem sourceMeaning_domain_exact
    (row : Carbohydrate1996HeteroSubstitutionAnhydride.Provision) :
    (sourceMeaning row).semanticDomain = semanticDomain row := by rfl

theorem sourceMeaning_injective : Function.Injective sourceMeaning := by
  intro left right equal
  have assertionEqual : (sourceMeaning left).assertion = (sourceMeaning right).assertion :=
    congrArg SourceMeaning.assertion equal
  have provisionEqual := congrArg SourceAssertion.provision assertionEqual
  simpa [sourceMeaning] using provisionEqual

def fullFamilyRows : List Carbohydrate1996HeteroSubstitutionAnhydride.Provision :=
  Carbohydrate1996HeteroSubstitutionAnhydride.Provision.all

def fullFamilyProvisions : List IUPACNormativeProvision :=
  fullFamilyRows.map IUPACNormativeProvision.carbohydrate1996HeteroSubstitutionAnhydride

def completionRows : List Carbohydrate1996HeteroSubstitutionAnhydride.Provision :=
  Carbohydrate1996HeteroSubstitutionAnhydride.Provision.base

def completionProvisions : List IUPACNormativeProvision :=
  completionRows.map IUPACNormativeProvision.carbohydrate1996HeteroSubstitutionAnhydride

def completionBatch : GlobalNonDescriptorSourceMeaningBatch completionProvisions :=
  totalMeaningBatch completionRows
    IUPACNormativeProvision.carbohydrate1996HeteroSubstitutionAnhydride
    sourceMeaning (by intro _row; rfl)

@[simp] theorem full_family_provisions_exact :
    fullFamilyProvisions = carbohydrate1996HeteroSubstitutionAnhydrideSemanticsSlice := by rfl

@[simp] theorem full_family_provision_count : fullFamilyProvisions.length = 69 := by
  simp [fullFamilyProvisions, fullFamilyRows]

@[simp] theorem completion_provision_count : completionProvisions.length = 34 := by
  simp [completionProvisions, completionRows,
    Carbohydrate1996HeteroSubstitutionAnhydride.Provision.base]

@[simp] theorem completion_entry_count : completionBatch.entries.length = 34 := by
  rw [completionBatch.entries_length, completion_provision_count]

private theorem completion_rows_then_indexed_exact :
    completionRows ++ GlobalNonDescriptorIndexedSourceData.carbohydrateHeteroRows =
      fullFamilyRows := by
  simp [completionRows, fullFamilyRows,
    GlobalNonDescriptorIndexedSourceData.carbohydrateHeteroRows,
    Carbohydrate1996HeteroSubstitutionAnhydride.Provision.all]

theorem completion_then_indexed_exact_source_order :
    completionProvisions ++ GlobalNonDescriptorIndexedSourceData.carbohydrateHeteroProvisions =
      carbohydrate1996HeteroSubstitutionAnhydrideSemanticsSlice := by
  rw [← full_family_provisions_exact]
  simp only [completionProvisions,
    GlobalNonDescriptorIndexedSourceData.carbohydrateHeteroProvisions,
    fullFamilyProvisions, ← List.map_append]
  rw [completion_rows_then_indexed_exact]

theorem materialized_order_perm_source :
    (GlobalNonDescriptorIndexedSourceData.carbohydrateHeteroProvisions ++
      completionProvisions).Perm
        carbohydrate1996HeteroSubstitutionAnhydrideSemanticsSlice := by
  calc
    (GlobalNonDescriptorIndexedSourceData.carbohydrateHeteroProvisions ++
      completionProvisions).Perm
        (completionProvisions ++
          GlobalNonDescriptorIndexedSourceData.carbohydrateHeteroProvisions) :=
      List.perm_append_comm
    _ = carbohydrate1996HeteroSubstitutionAnhydrideSemanticsSlice :=
      completion_then_indexed_exact_source_order

theorem completion_disjoint_indexed :
    completionProvisions.Disjoint
      GlobalNonDescriptorIndexedSourceData.carbohydrateHeteroProvisions := by
  apply List.disjoint_of_nodup_append
  rw [completion_then_indexed_exact_source_order]
  exact Carbohydrate1996HeteroSubstitutionAnhydride.Provision.all_nodup.map
    (by intro left right equal; cases equal; rfl)

theorem completion_provisions_nodup : completionProvisions.Nodup := by
  exact Carbohydrate1996HeteroSubstitutionAnhydride.Provision.all_nodup.of_append_left.map
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

end GlobalNonDescriptorCarbohydrateHeteroSourceMeaning
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.full_family_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completion_then_indexed_exact_source_order
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.materialized_order_perm_source
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.sourceMeaning_injective
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.completion_entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.every_completion_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateHeteroSourceMeaning.source_audit_still_open
