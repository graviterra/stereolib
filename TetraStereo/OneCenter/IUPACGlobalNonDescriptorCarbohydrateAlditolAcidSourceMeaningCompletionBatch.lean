import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceDataBatch
import TetraStereo.KernelOnly

set_option autoImplicit false











namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning

open GlobalNonDescriptorIndexedSourceData

inductive SemanticDomain where
  | alditol
  | aldonicAcid
  | ketoaldonicAcid
  | uronicAcid
  | aldaricAcid
  | printedExample
  deriving DecidableEq, Repr

def semanticDomain : Carbohydrate1996AlditolsAcids.Provision → SemanticDomain
  | .alditolOseToItol | .alditolParentChoiceUsesTwoCarbTwo | .fucitolAndRhamnitolAllowed
  | .symmetricAlditolIsOpticallyInactiveMeso | .mesoPrefixOptionalForSymmetricAlditol
  | .substitutedMesoAlditolRequiresDL | .longMesoAlditolPrefixesRequireDL => .alditol
  | .aldonicClassByCarbonCount | .aldonicOseToOnicAcid | .aldonicSaltUsesOnate
  | .knownCounterionPrecedesAldonate | .aldonicEsterUsesOnateAndGroupPrefix
  | .aldonicPeriphraseMayIndex | .aldonicAmideAndNitrileEndings
  | .aldonicLactoneUsesOnolactone | .lactoneLocantsCarbonylThenOxygen
  | .lactonePeriphrasesNotRecommended | .lactamNamedAnalogously
  | .aldonicAcylHalideUsesOnoyl | .complicatedAcidDerivativesUseGeneralRules => .aldonicAcid
  | .ketoaldonicUloseToUlosonicWithLocant | .ketoaldonicAnionUsesUlosonate
  | .ketoaldonicNumberingStartsAtCarboxy | .ketoaldonicGlycosideUsesUlosidonicRingInfix
  | .kdoSymbolAndDeprecatedExpansion | .kdnSymbolUsage
  | .ketoaldonicDerivativesFollowAldonicRules | .esterVsGlycosidicAlkylParentheses
  | .ascorbicAcidIsThreeIsomerEquilibrium => .ketoaldonicAcid
  | .uronicThreeStemTransformations | .uronicAldehydicCarbonNumberedOne
  | .uronicDerivativesFollowAldonicRules | .uronicAnionUsesUronate
  | .uronicEsterUsesUronate => .uronicAcid
  | .aldaricOseToAricAcid | .aldaricParentChoiceUsesTwoCarbTwo
  | .symmetricAldaricHasNoDL | .symmetricAldaricMayUseMeso
  | .substitutedMesoAldaricRequiresDL | .tartaricTrivialNameRetained
  | .tartaricStereochemistryUsesRS | .tartaricEstersAreTartrates
  | .historicalTartaricDLConfusionRequiresRS | .aldaricDerivativesFollowAldonicRules
  | .complexAldaricDerivativesUseGeneralRules | .ambiguousAldaricDerivativeRequiresLocants
  | .mesoAldaricName _ => .aldaricAcid
  | .printedExample _ => .printedExample

def alditolSeriesRequirementInventory :
    List (Carbohydrate1996AlditolsAcids.SymmetryState ×
      Carbohydrate1996AlditolsAcids.SeriesRequirement) :=
  [ (.asymmetric,
      Carbohydrate1996AlditolsAcids.alditolSeriesRequirement .asymmetric)
  , (.symmetricUnsubstituted,
      Carbohydrate1996AlditolsAcids.alditolSeriesRequirement .symmetricUnsubstituted)
  , (.symmetricParentMadeAsymmetric,
      Carbohydrate1996AlditolsAcids.alditolSeriesRequirement .symmetricParentMadeAsymmetric) ]

def tartaricClassInventory :
    List ((Carbohydrate1996AlditolsAcids.AbsoluteCenterDescriptor ×
      Carbohydrate1996AlditolsAcids.AbsoluteCenterDescriptor) ×
        Carbohydrate1996AlditolsAcids.TartaricClass) :=
  [ ((.R, .R), Carbohydrate1996AlditolsAcids.tartaricClass (.R, .R))
  , ((.S, .S), Carbohydrate1996AlditolsAcids.tartaricClass (.S, .S))
  , ((.R, .S), Carbohydrate1996AlditolsAcids.tartaricClass (.R, .S))
  , ((.S, .R), Carbohydrate1996AlditolsAcids.tartaricClass (.S, .R)) ]

inductive SourceAssertion where
  | alditolOseToItol
  | alditolParentChoiceUsesTwoCarbTwo
  | fucitolAndRhamnitolAllowed
  | symmetricAlditolIsOpticallyInactiveMeso
      (inventory : List (Carbohydrate1996AlditolsAcids.SymmetryState ×
        Carbohydrate1996AlditolsAcids.SeriesRequirement))
  | mesoPrefixOptionalForSymmetricAlditol
      (state : Carbohydrate1996AlditolsAcids.SymmetryState)
      (requirement : Carbohydrate1996AlditolsAcids.SeriesRequirement)
  | substitutedMesoAlditolRequiresDL
      (state : Carbohydrate1996AlditolsAcids.SymmetryState)
      (requirement : Carbohydrate1996AlditolsAcids.SeriesRequirement)
  | longMesoAlditolPrefixesRequireDL
      (state : Carbohydrate1996AlditolsAcids.SymmetryState)
      (requirement : Carbohydrate1996AlditolsAcids.SeriesRequirement)
  | aldonicClassByCarbonCount
  | aldonicOseToOnicAcid
  | aldonicSaltUsesOnate
  | knownCounterionPrecedesAldonate
  | aldonicEsterUsesOnateAndGroupPrefix
  | aldonicPeriphraseMayIndex
  | aldonicAmideAndNitrileEndings
  | aldonicLactoneUsesOnolactone
  | lactoneLocantsCarbonylThenOxygen (carbonyl oxygen : Nat) (locants : List Nat)
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
  | ascorbicAcidIsThreeIsomerEquilibrium (names : List String)
  | uronicThreeStemTransformations
  | uronicAldehydicCarbonNumberedOne
      (origin : Carbohydrate1996AlditolsAcids.UronicNumberingOrigin)
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
      (inventory : List ((Carbohydrate1996AlditolsAcids.AbsoluteCenterDescriptor ×
        Carbohydrate1996AlditolsAcids.AbsoluteCenterDescriptor) ×
          Carbohydrate1996AlditolsAcids.TartaricClass))
  | tartaricEstersAreTartrates
  | historicalTartaricDLConfusionRequiresRS
      (inventory : List ((Carbohydrate1996AlditolsAcids.AbsoluteCenterDescriptor ×
        Carbohydrate1996AlditolsAcids.AbsoluteCenterDescriptor) ×
          Carbohydrate1996AlditolsAcids.TartaricClass))
  | aldaricDerivativesFollowAldonicRules
  | complexAldaricDerivativesUseGeneralRules
  | ambiguousAldaricDerivativeRequiresLocants
  | mesoAldaricName (name : Carbohydrate1996AlditolsAcids.MesoAldaricName)
      (text : String)
  | printedExample (row : Carbohydrate1996AlditolsAcids.PrintedExample)
      (data : Carbohydrate1996AlditolsAcids.PrintedExampleData)
  deriving Repr

def sourceAssertion : Carbohydrate1996AlditolsAcids.Provision → SourceAssertion
  | .alditolOseToItol => .alditolOseToItol
  | .alditolParentChoiceUsesTwoCarbTwo => .alditolParentChoiceUsesTwoCarbTwo
  | .fucitolAndRhamnitolAllowed => .fucitolAndRhamnitolAllowed
  | .symmetricAlditolIsOpticallyInactiveMeso =>
      .symmetricAlditolIsOpticallyInactiveMeso alditolSeriesRequirementInventory
  | .mesoPrefixOptionalForSymmetricAlditol =>
      .mesoPrefixOptionalForSymmetricAlditol .symmetricUnsubstituted
        (Carbohydrate1996AlditolsAcids.alditolSeriesRequirement .symmetricUnsubstituted)
  | .substitutedMesoAlditolRequiresDL =>
      .substitutedMesoAlditolRequiresDL .symmetricParentMadeAsymmetric
        (Carbohydrate1996AlditolsAcids.alditolSeriesRequirement .symmetricParentMadeAsymmetric)
  | .longMesoAlditolPrefixesRequireDL =>
      .longMesoAlditolPrefixesRequireDL .symmetricParentMadeAsymmetric
        (Carbohydrate1996AlditolsAcids.alditolSeriesRequirement .symmetricParentMadeAsymmetric)
  | .aldonicClassByCarbonCount => .aldonicClassByCarbonCount
  | .aldonicOseToOnicAcid => .aldonicOseToOnicAcid
  | .aldonicSaltUsesOnate => .aldonicSaltUsesOnate
  | .knownCounterionPrecedesAldonate => .knownCounterionPrecedesAldonate
  | .aldonicEsterUsesOnateAndGroupPrefix => .aldonicEsterUsesOnateAndGroupPrefix
  | .aldonicPeriphraseMayIndex => .aldonicPeriphraseMayIndex
  | .aldonicAmideAndNitrileEndings => .aldonicAmideAndNitrileEndings
  | .aldonicLactoneUsesOnolactone => .aldonicLactoneUsesOnolactone
  | .lactoneLocantsCarbonylThenOxygen =>
      .lactoneLocantsCarbonylThenOxygen 6 3 (Carbohydrate1996AlditolsAcids.lactoneLocants 6 3)
  | .lactonePeriphrasesNotRecommended => .lactonePeriphrasesNotRecommended
  | .lactamNamedAnalogously => .lactamNamedAnalogously
  | .aldonicAcylHalideUsesOnoyl => .aldonicAcylHalideUsesOnoyl
  | .complicatedAcidDerivativesUseGeneralRules => .complicatedAcidDerivativesUseGeneralRules
  | .ketoaldonicUloseToUlosonicWithLocant => .ketoaldonicUloseToUlosonicWithLocant
  | .ketoaldonicAnionUsesUlosonate => .ketoaldonicAnionUsesUlosonate
  | .ketoaldonicNumberingStartsAtCarboxy => .ketoaldonicNumberingStartsAtCarboxy
  | .ketoaldonicGlycosideUsesUlosidonicRingInfix => .ketoaldonicGlycosideUsesUlosidonicRingInfix
  | .kdoSymbolAndDeprecatedExpansion => .kdoSymbolAndDeprecatedExpansion
  | .kdnSymbolUsage => .kdnSymbolUsage
  | .ketoaldonicDerivativesFollowAldonicRules => .ketoaldonicDerivativesFollowAldonicRules
  | .esterVsGlycosidicAlkylParentheses => .esterVsGlycosidicAlkylParentheses
  | .ascorbicAcidIsThreeIsomerEquilibrium =>
      .ascorbicAcidIsThreeIsomerEquilibrium Carbohydrate1996AlditolsAcids.ascorbicEquilibriumNames
  | .uronicThreeStemTransformations => .uronicThreeStemTransformations
  | .uronicAldehydicCarbonNumberedOne =>
      .uronicAldehydicCarbonNumberedOne
        Carbohydrate1996AlditolsAcids.authoritativeUronicNumberingOrigin
  | .uronicDerivativesFollowAldonicRules => .uronicDerivativesFollowAldonicRules
  | .uronicAnionUsesUronate => .uronicAnionUsesUronate
  | .uronicEsterUsesUronate => .uronicEsterUsesUronate
  | .aldaricOseToAricAcid => .aldaricOseToAricAcid
  | .aldaricParentChoiceUsesTwoCarbTwo => .aldaricParentChoiceUsesTwoCarbTwo
  | .symmetricAldaricHasNoDL => .symmetricAldaricHasNoDL
  | .symmetricAldaricMayUseMeso => .symmetricAldaricMayUseMeso
  | .substitutedMesoAldaricRequiresDL => .substitutedMesoAldaricRequiresDL
  | .tartaricTrivialNameRetained => .tartaricTrivialNameRetained
  | .tartaricStereochemistryUsesRS => .tartaricStereochemistryUsesRS tartaricClassInventory
  | .tartaricEstersAreTartrates => .tartaricEstersAreTartrates
  | .historicalTartaricDLConfusionRequiresRS =>
      .historicalTartaricDLConfusionRequiresRS tartaricClassInventory
  | .aldaricDerivativesFollowAldonicRules => .aldaricDerivativesFollowAldonicRules
  | .complexAldaricDerivativesUseGeneralRules => .complexAldaricDerivativesUseGeneralRules
  | .ambiguousAldaricDerivativeRequiresLocants => .ambiguousAldaricDerivativeRequiresLocants
  | .mesoAldaricName name => .mesoAldaricName name name.text
  | .printedExample row => .printedExample row row.data

def SourceAssertion.provision : SourceAssertion → Carbohydrate1996AlditolsAcids.Provision
  | .alditolOseToItol => .alditolOseToItol
  | .alditolParentChoiceUsesTwoCarbTwo => .alditolParentChoiceUsesTwoCarbTwo
  | .fucitolAndRhamnitolAllowed => .fucitolAndRhamnitolAllowed
  | .symmetricAlditolIsOpticallyInactiveMeso _ => .symmetricAlditolIsOpticallyInactiveMeso
  | .mesoPrefixOptionalForSymmetricAlditol _ _ => .mesoPrefixOptionalForSymmetricAlditol
  | .substitutedMesoAlditolRequiresDL _ _ => .substitutedMesoAlditolRequiresDL
  | .longMesoAlditolPrefixesRequireDL _ _ => .longMesoAlditolPrefixesRequireDL
  | .aldonicClassByCarbonCount => .aldonicClassByCarbonCount
  | .aldonicOseToOnicAcid => .aldonicOseToOnicAcid
  | .aldonicSaltUsesOnate => .aldonicSaltUsesOnate
  | .knownCounterionPrecedesAldonate => .knownCounterionPrecedesAldonate
  | .aldonicEsterUsesOnateAndGroupPrefix => .aldonicEsterUsesOnateAndGroupPrefix
  | .aldonicPeriphraseMayIndex => .aldonicPeriphraseMayIndex
  | .aldonicAmideAndNitrileEndings => .aldonicAmideAndNitrileEndings
  | .aldonicLactoneUsesOnolactone => .aldonicLactoneUsesOnolactone
  | .lactoneLocantsCarbonylThenOxygen _ _ _ => .lactoneLocantsCarbonylThenOxygen
  | .lactonePeriphrasesNotRecommended => .lactonePeriphrasesNotRecommended
  | .lactamNamedAnalogously => .lactamNamedAnalogously
  | .aldonicAcylHalideUsesOnoyl => .aldonicAcylHalideUsesOnoyl
  | .complicatedAcidDerivativesUseGeneralRules => .complicatedAcidDerivativesUseGeneralRules
  | .ketoaldonicUloseToUlosonicWithLocant => .ketoaldonicUloseToUlosonicWithLocant
  | .ketoaldonicAnionUsesUlosonate => .ketoaldonicAnionUsesUlosonate
  | .ketoaldonicNumberingStartsAtCarboxy => .ketoaldonicNumberingStartsAtCarboxy
  | .ketoaldonicGlycosideUsesUlosidonicRingInfix => .ketoaldonicGlycosideUsesUlosidonicRingInfix
  | .kdoSymbolAndDeprecatedExpansion => .kdoSymbolAndDeprecatedExpansion
  | .kdnSymbolUsage => .kdnSymbolUsage
  | .ketoaldonicDerivativesFollowAldonicRules => .ketoaldonicDerivativesFollowAldonicRules
  | .esterVsGlycosidicAlkylParentheses => .esterVsGlycosidicAlkylParentheses
  | .ascorbicAcidIsThreeIsomerEquilibrium _ => .ascorbicAcidIsThreeIsomerEquilibrium
  | .uronicThreeStemTransformations => .uronicThreeStemTransformations
  | .uronicAldehydicCarbonNumberedOne _ => .uronicAldehydicCarbonNumberedOne
  | .uronicDerivativesFollowAldonicRules => .uronicDerivativesFollowAldonicRules
  | .uronicAnionUsesUronate => .uronicAnionUsesUronate
  | .uronicEsterUsesUronate => .uronicEsterUsesUronate
  | .aldaricOseToAricAcid => .aldaricOseToAricAcid
  | .aldaricParentChoiceUsesTwoCarbTwo => .aldaricParentChoiceUsesTwoCarbTwo
  | .symmetricAldaricHasNoDL => .symmetricAldaricHasNoDL
  | .symmetricAldaricMayUseMeso => .symmetricAldaricMayUseMeso
  | .substitutedMesoAldaricRequiresDL => .substitutedMesoAldaricRequiresDL
  | .tartaricTrivialNameRetained => .tartaricTrivialNameRetained
  | .tartaricStereochemistryUsesRS _ => .tartaricStereochemistryUsesRS
  | .tartaricEstersAreTartrates => .tartaricEstersAreTartrates
  | .historicalTartaricDLConfusionRequiresRS _ => .historicalTartaricDLConfusionRequiresRS
  | .aldaricDerivativesFollowAldonicRules => .aldaricDerivativesFollowAldonicRules
  | .complexAldaricDerivativesUseGeneralRules => .complexAldaricDerivativesUseGeneralRules
  | .ambiguousAldaricDerivativeRequiresLocants => .ambiguousAldaricDerivativeRequiresLocants
  | .mesoAldaricName name _ => .mesoAldaricName name
  | .printedExample row _ => .printedExample row

@[simp] theorem sourceAssertion_provision_exact
    (row : Carbohydrate1996AlditolsAcids.Provision) :
    (sourceAssertion row).provision = row := by
  cases row <;> rfl

structure SourceMeaning where
  sourceKey : String
  semanticDomain : SemanticDomain
  assertion : SourceAssertion
  deriving Repr

def sourceMeaning (row : Carbohydrate1996AlditolsAcids.Provision) : SourceMeaning :=
  ⟨row.sourceKey, semanticDomain row, sourceAssertion row⟩

@[simp] theorem sourceMeaning_key_exact (row : Carbohydrate1996AlditolsAcids.Provision) :
    (sourceMeaning row).sourceKey = row.sourceKey := by rfl

@[simp] theorem sourceMeaning_domain_exact (row : Carbohydrate1996AlditolsAcids.Provision) :
    (sourceMeaning row).semanticDomain = semanticDomain row := by rfl

theorem sourceMeaning_injective : Function.Injective sourceMeaning := by
  intro left right equal
  have assertionEqual : (sourceMeaning left).assertion = (sourceMeaning right).assertion :=
    congrArg SourceMeaning.assertion equal
  have provisionEqual := congrArg SourceAssertion.provision assertionEqual
  simpa [sourceMeaning] using provisionEqual

def fullFamilyRows : List Carbohydrate1996AlditolsAcids.Provision :=
  Carbohydrate1996AlditolsAcids.Provision.all

def fullFamilyProvisions : List IUPACNormativeProvision :=
  fullFamilyRows.map IUPACNormativeProvision.carbohydrate1996AlditolsAcids

def completionRows : List Carbohydrate1996AlditolsAcids.Provision :=
  Carbohydrate1996AlditolsAcids.Provision.base

def completionProvisions : List IUPACNormativeProvision :=
  completionRows.map IUPACNormativeProvision.carbohydrate1996AlditolsAcids

def completionBatch : GlobalNonDescriptorSourceMeaningBatch completionProvisions :=
  totalMeaningBatch completionRows IUPACNormativeProvision.carbohydrate1996AlditolsAcids
    sourceMeaning (by intro _row; rfl)

@[simp] theorem full_family_provisions_exact :
    fullFamilyProvisions = carbohydrate1996AlditolsAcidsSemanticsSlice := by rfl

@[simp] theorem full_family_provision_count : fullFamilyProvisions.length = 114 := by
  simp [fullFamilyProvisions, fullFamilyRows]

@[simp] theorem completion_provision_count : completionProvisions.length = 46 := by
  simp [completionProvisions, completionRows, Carbohydrate1996AlditolsAcids.Provision.base]

@[simp] theorem completion_entry_count : completionBatch.entries.length = 46 := by
  rw [completionBatch.entries_length, completion_provision_count]

private theorem completion_rows_then_indexed_exact :
    completionRows ++ GlobalNonDescriptorIndexedSourceData.carbohydrateAlditolAcidRows =
      fullFamilyRows := by
  simp [completionRows, fullFamilyRows,
    GlobalNonDescriptorIndexedSourceData.carbohydrateAlditolAcidRows,
    Carbohydrate1996AlditolsAcids.Provision.all, List.append_assoc]

theorem completion_then_indexed_exact_source_order :
    completionProvisions ++ GlobalNonDescriptorIndexedSourceData.carbohydrateAlditolAcidProvisions =
      carbohydrate1996AlditolsAcidsSemanticsSlice := by
  rw [← full_family_provisions_exact]
  simp only [completionProvisions,
    GlobalNonDescriptorIndexedSourceData.carbohydrateAlditolAcidProvisions,
    fullFamilyProvisions, ← List.map_append]
  rw [completion_rows_then_indexed_exact]

theorem materialized_order_perm_source :
    (GlobalNonDescriptorIndexedSourceData.carbohydrateAlditolAcidProvisions ++
      completionProvisions).Perm carbohydrate1996AlditolsAcidsSemanticsSlice := by
  calc
    (GlobalNonDescriptorIndexedSourceData.carbohydrateAlditolAcidProvisions ++
      completionProvisions).Perm
        (completionProvisions ++
          GlobalNonDescriptorIndexedSourceData.carbohydrateAlditolAcidProvisions) :=
      List.perm_append_comm
    _ = carbohydrate1996AlditolsAcidsSemanticsSlice :=
      completion_then_indexed_exact_source_order

theorem completion_disjoint_indexed :
    completionProvisions.Disjoint
      GlobalNonDescriptorIndexedSourceData.carbohydrateAlditolAcidProvisions := by
  apply List.disjoint_of_nodup_append
  rw [completion_then_indexed_exact_source_order]
  exact Carbohydrate1996AlditolsAcids.Provision.all_nodup.map
    (by intro left right equal; cases equal; rfl)

theorem completion_provisions_nodup : completionProvisions.Nodup := by
  exact Carbohydrate1996AlditolsAcids.Provision.all_nodup.of_append_left.of_append_left.map
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

end GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.full_family_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completion_then_indexed_exact_source_order
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.materialized_order_perm_source
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.sourceMeaning_injective
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.completion_entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.every_completion_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCarbohydrateAlditolAcidSourceMeaning.source_audit_still_open
