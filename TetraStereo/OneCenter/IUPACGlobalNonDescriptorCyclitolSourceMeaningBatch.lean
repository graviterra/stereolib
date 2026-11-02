import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceDataCore
import TetraStereo.KernelOnly

set_option autoImplicit false














namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorCyclitolSourceMeaning

open GlobalNonDescriptorIndexedSourceData

def cyclitolDomainProfile : Cyclitol1973.RingAlcoholProfile :=
  ⟨true, 3⟩

def generalDomainProfile : Cyclitol1973.RingAlcoholProfile :=
  ⟨true, 2⟩

def inositolPrefixInventory : List (Cyclitol1973.InositolParent × String) :=
  Cyclitol1973.InositolParent.all.map fun parent => (parent, parent.stereoprefix)

def inositolFractionInventory :
    List (Cyclitol1973.InositolParent × Cyclitol1973.RelativeFraction) :=
  Cyclitol1973.InositolParent.all.map fun parent => (parent, parent.relativeFraction)

def chiroDLInventory :
    List (Cyclitol1973.InositolParent × Cyclitol1973.RelativeFraction ×
      Option Cyclitol1973.DLSeries) :=
  [ (.chiroD, Cyclitol1973.InositolParent.chiroD.relativeFraction,
      Cyclitol1973.InositolParent.chiroD.absoluteSeries?)
  , (.chiroL, Cyclitol1973.InositolParent.chiroL.relativeFraction,
      Cyclitol1973.InositolParent.chiroL.absoluteSeries?) ]

def inositolPartitionInventory :
    List (Cyclitol1973.InositolParent × Cyclitol1973.RelativeFraction × Bool) :=
  Cyclitol1973.InositolParent.all.map fun parent =>
    (parent, parent.relativeFraction, parent.relativeFraction.isInositolPartition)

def retainedNumberingWitness : List (Nat × Nat) :=
  Cyclitol1973.inositolLocants.map fun locant => (locant, locant)

def retainedParentRoutes :
    List (Nat × Bool × Bool × Cyclitol1973.InositolDerivativeRoute) :=
  [ (1, true, false, Cyclitol1973.inositolDerivativeRoute 1 true false)
  , (2, true, false, Cyclitol1973.inositolDerivativeRoute 2 true false)
  , (3, true, false, Cyclitol1973.inositolDerivativeRoute 3 true false) ]

def rightCanonicalProjection : Cyclitol1973.FischerTollensProjection :=
  ⟨true, true, .right⟩

def leftCanonicalProjection : Cyclitol1973.FischerTollensProjection :=
  ⟨true, true, .left⟩

def canonicalProjectionReadings :
    List (Cyclitol1973.FischerTollensProjection × Option Cyclitol1973.DLSeries) :=
  [ (rightCanonicalProjection, Cyclitol1973.seriesFromCanonicalFischer rightCanonicalProjection)
  , (leftCanonicalProjection, Cyclitol1973.seriesFromCanonicalFischer leftCanonicalProjection) ]

def derivativeNameOrderWitness : List Cyclitol1973.NameComponent :=
  Cyclitol1973.generalDerivativeNameOrder (some (.D, some 1))
    Cyclitol1973.InositolParent.myo.relativeFraction "cyclitol derivative"

def notationCombinationInventory : List (Bool × Bool × Cyclitol1973.CombinedNotation) :=
  [ (false, false, Cyclitol1973.combineNotations false false)
  , (true, false, Cyclitol1973.combineNotations true false)
  , (false, true, Cyclitol1973.combineNotations false true)
  , (true, true, Cyclitol1973.combineNotations true true) ]

/-- Typed payloads preserve concrete source-model values rather than only the manifest row tag. -/
inductive SourceAssertion where
  | cyclitolDomainAtLeastThreeHydroxyls
      (profile : Cyclitol1973.RingAlcoholProfile) (domain : Cyclitol1973.NomenclatureDomain)
  | fewerHydroxylsUseGeneralNomenclature
      (profile : Cyclitol1973.RingAlcoholProfile) (domain : Cyclitol1973.NomenclatureDomain)
  | classSpecificConfigurationMethod
      (purpose : Cyclitol1973.NotationPurpose) (selected : Cyclitol1973.ConfigurationNotation)
  | generalRSAllowedForRelationsAndChiralSubstituents
      (purposes : List Cyclitol1973.NotationPurpose)
      (selected : List Cyclitol1973.ConfigurationNotation)
  | planarRingFaceConvention (faces : List Cyclitol1973.RingFace)
  | relativeFractionSeparatedFromAbsoluteDL
      (relative : Cyclitol1973.RelativeFraction)
      (dSeries lSeries : Option Cyclitol1973.DLSeries)
  | inositolPrefixInventory (inventory : List (Cyclitol1973.InositolParent × String))
  | inositolFractionInventory
      (inventory : List (Cyclitol1973.InositolParent × Cyclitol1973.RelativeFraction))
  | chiroDLPair
      (inventory : List (Cyclitol1973.InositolParent × Cyclitol1973.RelativeFraction ×
        Option Cyclitol1973.DLSeries))
  | inositolDerivativeNumberingRetained (mapping : List (Nat × Nat))
  | enantiomericPositionsReceiveSameLocants (locants : List Nat)
  | numberingCriteriaAppliedSuccessively (criteria : List Cyclitol1973.NumberingCriterion)
  | numberingLowestNumericalSeries (lower higher : List Nat) (isLower : Bool)
  | numberingMoreNumerousFaceSet (criterion : Cyclitol1973.NumberingCriterion)
  | numberingLowerFaceSet (criterion : Cyclitol1973.NumberingCriterion)
  | numberingNonHydroxyPriority (criterion : Cyclitol1973.NumberingCriterion)
  | numberingAlphabeticalPriority (criterion : Cyclitol1973.NumberingCriterion)
  | numberingMesoLBeforeD (criterion : Cyclitol1973.NumberingCriterion)
  | mesoClockwiseApplication
      (sense : Cyclitol1973.RingNumberingSense) (series : Cyclitol1973.DLSeries)
  | relativeFractionFacePartition
      (inventory : List (Cyclitol1973.InositolParent × Cyclitol1973.RelativeFraction × Bool))
  | relativeFractionLowerSetNumerator
      (firstFace secondFace : List Nat) (canonical : Cyclitol1973.RelativeFraction)
  | hydroxyOnlyFractionServesAsLocants
      (fraction : Cyclitol1973.RelativeFraction) (locants : List Nat)
  | oneToThreeReplacementsRetainParent
      (routes : List (Nat × Bool × Bool × Cyclitol1973.InositolDerivativeRoute))
  | seniorSuffixLeavesInositolRoute
      (replacementCount : Nat) (hasSeniorSuffix : Bool)
      (route : Cyclitol1973.InositolDerivativeRoute)
  | additionalSubstituentPrefixRefersToHydroxyl
      (additionalSubstituent : String) (referent : Cyclitol1973.ConfigurationReferent)
  | generalDerivativeRelativeFraction (fraction : Cyclitol1973.RelativeFraction)
  | generalDerivativeFractionPlacement (components : List Cyclitol1973.NameComponent)
  | disubstitutedFractionRefersToHydroxyl
      (additionalSubstituent : String) (referent : Cyclitol1973.ConfigurationReferent)
  | fischerTollensOrientation
      (readings : List (Cyclitol1973.FischerTollensProjection × Option Cyclitol1973.DLSeries))
  | definingSubstituentRightLeftDL
      (readings : List (Cyclitol1973.HorizontalSide × Cyclitol1973.DLSeries))
  | definingCenterLocantMayPrefixDL
      (prefixes : List (Cyclitol1973.DLSeries × Nat × Cyclitol1973.AbsolutePrefix))
  | racemateUsesDL (state : Cyclitol1973.ChiralityState)
      (absolute : Option Cyclitol1973.AbsolutePrefix)
  | omittedDLPrefixMeansMeso (state : Cyclitol1973.ChiralityState)
      (absolute : Option Cyclitol1973.AbsolutePrefix)
  | definingCenterOneRecommended
      (prefixes : List (Cyclitol1973.DLSeries × Cyclitol1973.AbsolutePrefix))
  | mixedBiochemicalDcLc
      (readings : List (Cyclitol1973.DLSeries × Cyclitol1973.MixedBiochemicalSeries))
  | cyclitolNotationCombinesWithCIPOrSn
      (inventory : List (Bool × Bool × Cyclitol1973.CombinedNotation))
  | manyReplacementsMayUseCIP
      (purpose : Cyclitol1973.NotationPurpose) (selected : Cyclitol1973.ConfigurationNotation)
  deriving DecidableEq, Repr

def sourceAssertion : Cyclitol1973.Provision → SourceAssertion
  | .cyclitolDomainAtLeastThreeHydroxyls =>
      .cyclitolDomainAtLeastThreeHydroxyls cyclitolDomainProfile
        (Cyclitol1973.nomenclatureDomain cyclitolDomainProfile)
  | .fewerHydroxylsUseGeneralNomenclature =>
      .fewerHydroxylsUseGeneralNomenclature generalDomainProfile
        (Cyclitol1973.nomenclatureDomain generalDomainProfile)
  | .classSpecificConfigurationMethod =>
      .classSpecificConfigurationMethod .cyclitolClassConfiguration
        (Cyclitol1973.preferredNotation .cyclitolClassConfiguration)
  | .generalRSAllowedForRelationsAndChiralSubstituents =>
      let purposes : List Cyclitol1973.NotationPurpose :=
        [.relationToGeneralStereochemistry, .chiralSubstituent]
      .generalRSAllowedForRelationsAndChiralSubstituents purposes
        (purposes.map Cyclitol1973.preferredNotation)
  | .planarRingFaceConvention => .planarRingFaceConvention [.above, .below]
  | .relativeFractionSeparatedFromAbsoluteDL =>
      .relativeFractionSeparatedFromAbsoluteDL
        Cyclitol1973.InositolParent.chiroD.relativeFraction
        Cyclitol1973.InositolParent.chiroD.absoluteSeries?
        Cyclitol1973.InositolParent.chiroL.absoluteSeries?
  | .inositolPrefixInventory => .inositolPrefixInventory inositolPrefixInventory
  | .inositolFractionInventory => .inositolFractionInventory inositolFractionInventory
  | .chiroDLPair => .chiroDLPair chiroDLInventory
  | .inositolDerivativeNumberingRetained =>
      .inositolDerivativeNumberingRetained retainedNumberingWitness
  | .enantiomericPositionsReceiveSameLocants =>
      .enantiomericPositionsReceiveSameLocants Cyclitol1973.inositolLocants
  | .numberingCriteriaAppliedSuccessively =>
      .numberingCriteriaAppliedSuccessively Cyclitol1973.NumberingCriterion.all
  | .numberingLowestNumericalSeries =>
      .numberingLowestNumericalSeries [1, 2, 3, 6] [1, 2, 4, 5]
        (Cyclitol1973.locantSeriesLess [1, 2, 3, 6] [1, 2, 4, 5])
  | .numberingMoreNumerousFaceSet =>
      .numberingMoreNumerousFaceSet .moreNumerousFaceSet
  | .numberingLowerFaceSet => .numberingLowerFaceSet .lowerNumberableFaceSet
  | .numberingNonHydroxyPriority => .numberingNonHydroxyPriority .nonHydroxySubstituents
  | .numberingAlphabeticalPriority =>
      .numberingAlphabeticalPriority .alphabeticallyFirstSubstituent
  | .numberingMesoLBeforeD => .numberingMesoLBeforeD .LBeforeDForMeso
  | .mesoClockwiseApplication =>
      .mesoClockwiseApplication .clockwise (Cyclitol1973.mesoSeriesFromUpwardView .clockwise)
  | .relativeFractionFacePartition =>
      .relativeFractionFacePartition inositolPartitionInventory
  | .relativeFractionLowerSetNumerator =>
      .relativeFractionLowerSetNumerator [3, 5, 6] [1, 2, 4]
        (Cyclitol1973.canonicalRelativeFraction [3, 5, 6] [1, 2, 4])
  | .hydroxyOnlyFractionServesAsLocants =>
      .hydroxyOnlyFractionServesAsLocants
        Cyclitol1973.InositolParent.myo.relativeFraction Cyclitol1973.inositolLocants
  | .oneToThreeReplacementsRetainParent =>
      .oneToThreeReplacementsRetainParent retainedParentRoutes
  | .seniorSuffixLeavesInositolRoute =>
      .seniorSuffixLeavesInositolRoute 1 true
        (Cyclitol1973.inositolDerivativeRoute 1 true true)
  | .additionalSubstituentPrefixRefersToHydroxyl =>
      .additionalSubstituentPrefixRefersToHydroxyl "additional substituent"
        (Cyclitol1973.disubstitutedCarbonReferent "additional substituent")
  | .generalDerivativeRelativeFraction =>
      .generalDerivativeRelativeFraction Cyclitol1973.InositolParent.myo.relativeFraction
  | .generalDerivativeFractionPlacement =>
      .generalDerivativeFractionPlacement derivativeNameOrderWitness
  | .disubstitutedFractionRefersToHydroxyl =>
      .disubstitutedFractionRefersToHydroxyl "additional substituent"
        (Cyclitol1973.disubstitutedCarbonReferent "additional substituent")
  | .fischerTollensOrientation => .fischerTollensOrientation canonicalProjectionReadings
  | .definingSubstituentRightLeftDL =>
      .definingSubstituentRightLeftDL [(.right, .D), (.left, .L)]
  | .definingCenterLocantMayPrefixDL =>
      .definingCenterLocantMayPrefixDL
        [(.D, 2, Cyclitol1973.withDefiningCenterLocant .D 2),
          (.L, 3, Cyclitol1973.withDefiningCenterLocant .L 3)]
  | .racemateUsesDL =>
      .racemateUsesDL .racemic (Cyclitol1973.absolutePrefix .racemic)
  | .omittedDLPrefixMeansMeso =>
      .omittedDLPrefixMeansMeso .meso (Cyclitol1973.absolutePrefix .meso)
  | .definingCenterOneRecommended =>
      .definingCenterOneRecommended
        [(.D, Cyclitol1973.withDefiningCenterLocant .D 1),
          (.L, Cyclitol1973.withDefiningCenterLocant .L 1)]
  | .mixedBiochemicalDcLc =>
      .mixedBiochemicalDcLc
        [(.D, Cyclitol1973.cyclitolSubscript .D), (.L, Cyclitol1973.cyclitolSubscript .L)]
  | .cyclitolNotationCombinesWithCIPOrSn =>
      .cyclitolNotationCombinesWithCIPOrSn notationCombinationInventory
  | .manyReplacementsMayUseCIP =>
      .manyReplacementsMayUseCIP .extensivelyReplacedCyclitol
        (Cyclitol1973.preferredNotation .extensivelyReplacedCyclitol)

/-- Recovering the owning row gives an efficient injectivity proof while each assertion retains
its domain-specific semantic payload. -/
def SourceAssertion.provision : SourceAssertion → Cyclitol1973.Provision
  | .cyclitolDomainAtLeastThreeHydroxyls _ _ => .cyclitolDomainAtLeastThreeHydroxyls
  | .fewerHydroxylsUseGeneralNomenclature _ _ => .fewerHydroxylsUseGeneralNomenclature
  | .classSpecificConfigurationMethod _ _ => .classSpecificConfigurationMethod
  | .generalRSAllowedForRelationsAndChiralSubstituents _ _ =>
      .generalRSAllowedForRelationsAndChiralSubstituents
  | .planarRingFaceConvention _ => .planarRingFaceConvention
  | .relativeFractionSeparatedFromAbsoluteDL _ _ _ => .relativeFractionSeparatedFromAbsoluteDL
  | .inositolPrefixInventory _ => .inositolPrefixInventory
  | .inositolFractionInventory _ => .inositolFractionInventory
  | .chiroDLPair _ => .chiroDLPair
  | .inositolDerivativeNumberingRetained _ => .inositolDerivativeNumberingRetained
  | .enantiomericPositionsReceiveSameLocants _ => .enantiomericPositionsReceiveSameLocants
  | .numberingCriteriaAppliedSuccessively _ => .numberingCriteriaAppliedSuccessively
  | .numberingLowestNumericalSeries _ _ _ => .numberingLowestNumericalSeries
  | .numberingMoreNumerousFaceSet _ => .numberingMoreNumerousFaceSet
  | .numberingLowerFaceSet _ => .numberingLowerFaceSet
  | .numberingNonHydroxyPriority _ => .numberingNonHydroxyPriority
  | .numberingAlphabeticalPriority _ => .numberingAlphabeticalPriority
  | .numberingMesoLBeforeD _ => .numberingMesoLBeforeD
  | .mesoClockwiseApplication _ _ => .mesoClockwiseApplication
  | .relativeFractionFacePartition _ => .relativeFractionFacePartition
  | .relativeFractionLowerSetNumerator _ _ _ => .relativeFractionLowerSetNumerator
  | .hydroxyOnlyFractionServesAsLocants _ _ => .hydroxyOnlyFractionServesAsLocants
  | .oneToThreeReplacementsRetainParent _ => .oneToThreeReplacementsRetainParent
  | .seniorSuffixLeavesInositolRoute _ _ _ => .seniorSuffixLeavesInositolRoute
  | .additionalSubstituentPrefixRefersToHydroxyl _ _ =>
      .additionalSubstituentPrefixRefersToHydroxyl
  | .generalDerivativeRelativeFraction _ => .generalDerivativeRelativeFraction
  | .generalDerivativeFractionPlacement _ => .generalDerivativeFractionPlacement
  | .disubstitutedFractionRefersToHydroxyl _ _ => .disubstitutedFractionRefersToHydroxyl
  | .fischerTollensOrientation _ => .fischerTollensOrientation
  | .definingSubstituentRightLeftDL _ => .definingSubstituentRightLeftDL
  | .definingCenterLocantMayPrefixDL _ => .definingCenterLocantMayPrefixDL
  | .racemateUsesDL _ _ => .racemateUsesDL
  | .omittedDLPrefixMeansMeso _ _ => .omittedDLPrefixMeansMeso
  | .definingCenterOneRecommended _ => .definingCenterOneRecommended
  | .mixedBiochemicalDcLc _ => .mixedBiochemicalDcLc
  | .cyclitolNotationCombinesWithCIPOrSn _ => .cyclitolNotationCombinesWithCIPOrSn
  | .manyReplacementsMayUseCIP _ _ => .manyReplacementsMayUseCIP

@[simp] theorem sourceAssertion_provision_exact (row : Cyclitol1973.Provision) :
    (sourceAssertion row).provision = row := by
  cases row <;> rfl

structure SourceMeaning where
  sourceSection : String
  sourceKey : String
  semanticDomain : Cyclitol1973.SemanticDomain
  assertion : SourceAssertion
  deriving DecidableEq, Repr

def sourceMeaning (row : Cyclitol1973.Provision) : SourceMeaning :=
  ⟨row.sourceSection, row.sourceKey, Cyclitol1973.provisionSemanticDomain row,
    sourceAssertion row⟩

@[simp] theorem sourceMeaning_section_exact (row : Cyclitol1973.Provision) :
    (sourceMeaning row).sourceSection = row.sourceSection := by
  rfl

@[simp] theorem sourceMeaning_key_exact (row : Cyclitol1973.Provision) :
    (sourceMeaning row).sourceKey = row.sourceKey := by
  rfl

@[simp] theorem sourceMeaning_domain_exact (row : Cyclitol1973.Provision) :
    (sourceMeaning row).semanticDomain = Cyclitol1973.provisionSemanticDomain row := by
  rfl

theorem sourceMeaning_injective : Function.Injective sourceMeaning := by
  intro left right equal
  have assertionEqual : (sourceMeaning left).assertion = (sourceMeaning right).assertion :=
    congrArg SourceMeaning.assertion equal
  have provisionEqual := congrArg SourceAssertion.provision assertionEqual
  simpa [sourceMeaning] using provisionEqual

def rows : List Cyclitol1973.Provision :=
  Cyclitol1973.Provision.all

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.cyclitol1973

def batch : GlobalNonDescriptorSourceMeaningBatch provisions :=
  totalMeaningBatch rows IUPACNormativeProvision.cyclitol1973 sourceMeaning
    (by intro _row; rfl)

@[simp] theorem provisions_exact :
    provisions = sourceProvisions .cyclitolRecommendations1973 := by
  exact cyclitol1973SemanticsSlice_exact

@[simp] theorem provision_count : provisions.length = 37 := by
  simp [provisions, rows]

@[simp] theorem entry_count : batch.entries.length = 37 := by
  rw [batch.entries_length, provision_count]

theorem provisions_nodup : provisions.Nodup := by
  exact Cyclitol1973.Provision.all_nodup.map
    (by intro left right equal; cases equal; rfl)

@[simp] theorem entry_provisions_exact :
    batch.entries.map GlobalNonDescriptorSourceMeaningEntry.provision = provisions :=
  batch.provisions_exact

theorem every_entry_nonvacuous
    (entry : GlobalNonDescriptorSourceMeaningEntry) (_member : entry ∈ batch.entries) :
    ∃ input, ∃ observation : entry.reference.toReference.Observation,
      input.StructurallyWellFormed ∧
        entry.reference.toReference.Applicable input ∧
          entry.reference.toReference.Judges input observation :=
  entry.admittedJudgment

theorem source_audit_still_open :
    ¬IUPACNormativeSource.ProvisionAuditComplete .cyclitolRecommendations1973 := by
  simp [IUPACNormativeSource.ProvisionAuditComplete,
    IUPACNormativeSource.currentProvisionAuditChecklist,
    IUPACNormativeSource.ProvisionAuditChecklist.Complete,
    Cyclitol1973.currentSourceReviewProvisionEnumerationConfirmed,
    Cyclitol1973.currentSourceReviewProseTableCoverageConfirmed,
    Cyclitol1973.currentSourceReviewFigureGraphTranscriptionsReviewed]

end GlobalNonDescriptorCyclitolSourceMeaning
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCyclitolSourceMeaning.provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCyclitolSourceMeaning.sourceMeaning_injective
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCyclitolSourceMeaning.entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCyclitolSourceMeaning.every_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCyclitolSourceMeaning.source_audit_still_open
