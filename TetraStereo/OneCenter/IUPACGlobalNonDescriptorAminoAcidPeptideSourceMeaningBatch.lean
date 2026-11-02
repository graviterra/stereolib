import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceDataCore
import TetraStereo.KernelOnly

set_option autoImplicit false














namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorAminoAcidPeptideSourceMeaning

open GlobalNonDescriptorIndexedSourceData

inductive PrefixPlacement where
  | immediatelyBeforeParent
  | beforeSubstituentPrefix
  | beforeParentResidue
  deriving DecidableEq, Repr

inductive DelegatedAuthority where
  | carbohydrateRecommendations1996
  | generalStereochemicalNomenclature
  deriving DecidableEq, Repr

inductive MultiCenterPrefixPolicy where
  | discouraged
  deriving DecidableEq, Repr

inductive ProlineGeometryReferent where
  | hydroxylVersusCarboxyl
  deriving DecidableEq, Repr

inductive ResidueScope where
  | local
  deriving DecidableEq, Repr

inductive TemporaryLabelPolicy where
  | allowedPendingResolution
  deriving DecidableEq, Repr

def omissionInventory :
    List (AminoAcidPeptide1983.OmissionContext × AminoAcidPeptide1983.PopulationMeaning) :=
  [ (.proteinSource, AminoAcidPeptide1983.omittedPrefixMeaning .proteinSource)
  , (.unresolvedSynthetic, AminoAcidPeptide1983.omittedPrefixMeaning .unresolvedSynthetic)
  , (.statementIndependentOfEnantiomer,
      AminoAcidPeptide1983.omittedPrefixMeaning .statementIndependentOfEnantiomer) ]

def referenceSubscriptInventory :
    List (AminoAcidPeptide1983.SeriesReferenceSystem × AminoAcidPeptide1983.DLSubscript) :=
  [ (.aminoAcid, AminoAcidPeptide1983.subscriptForReference .aminoAcid)
  , (.carbohydrate, AminoAcidPeptide1983.subscriptForReference .carbohydrate) ]

def lAlphaCIPInventory :
    List (AminoAcidPeptide1983.AminoAcidCIPClass × AminoAcidPeptide1983.RS) :=
  [ (.ordinaryProteinogenic, AminoAcidPeptide1983.cipOfLAlphaCarbon .ordinaryProteinogenic)
  , (.cysteine, AminoAcidPeptide1983.cipOfLAlphaCarbon .cysteine)
  , (.cystine, AminoAcidPeptide1983.cipOfLAlphaCarbon .cystine) ]

def alloInventory : List (String × List AminoAcidPeptide1983.LocatedRS) :=
  [ ("L-threonine", AminoAcidPeptide1983.ThreonineFamily.Lthreonine.configuration)
  , ("L-allothreonine", AminoAcidPeptide1983.ThreonineFamily.Lallothreonine.configuration)
  , ("L-isoleucine", AminoAcidPeptide1983.IsoleucineFamily.Lisoleucine.configuration)
  , ("L-alloisoleucine", AminoAcidPeptide1983.IsoleucineFamily.Lalloisoleucine.configuration) ]

def symbolInventory :
    List (AminoAcidPeptide1983.SymbolConfigurationMark ×
      AminoAcidPeptide1983.ResidueConfiguration) :=
  [ (.omittedMeansL, AminoAcidPeptide1983.symbolMeaning .omittedMeansL)
  , (.D, AminoAcidPeptide1983.symbolMeaning .D)
  , (.DL, AminoAcidPeptide1983.symbolMeaning .DL)
  , (.ambo, AminoAcidPeptide1983.symbolMeaning .ambo)
  , (.xi, AminoAcidPeptide1983.symbolMeaning .xi) ]

def allUnknownExample : AminoAcidPeptide1983.PartiallyKnownConfiguration :=
  ⟨[(2, .xi), (5, .xi)]⟩

/- Typed payloads preserve actual source-model values rather than only the manifest row tag. -/
inductive SourceAssertion where
  | alphaCarbonUsesSerineReferencedDL
      (dPrefix lPrefix : AminoAcidPeptide1983.AlphaPrefix)
  | alphaUnknownUsesXi (prefixValue : AminoAcidPeptide1983.AlphaPrefix)
  | fischerRosanoffProjection
      (projection : AminoAcidPeptide1983.FischerRosanoffProjection)
      (series : Option AminoAcidPeptide1983.DLSeries)
  | dlPrefixImmediatelyPrecedesParent (placement : PrefixPlacement)
  | chiralGlycineDerivativePrefixPrecedesSubstituent (placement : PrefixPlacement)
  | derivativeAndPeptidePrefixPrecedesParentResidue (placement : PrefixPlacement)
  | proteinSourceMayOmitImpliedL
      (inventory : List (AminoAcidPeptide1983.OmissionContext ×
        AminoAcidPeptide1983.PopulationMeaning))
  | unresolvedSyntheticMayOmitImpliedRacemate
      (inventory : List (AminoAcidPeptide1983.OmissionContext ×
        AminoAcidPeptide1983.PopulationMeaning))
  | enantiomerIndependentStatementMayOmitPrefix
      (inventory : List (AminoAcidPeptide1983.OmissionContext ×
        AminoAcidPeptide1983.PopulationMeaning))
  | aminoAcidAndCarbohydrateDLSubscripts
      (inventory : List (AminoAcidPeptide1983.SeriesReferenceSystem ×
        AminoAcidPeptide1983.DLSubscript))
  | dlSubscriptsRequiredWhenAmbiguous
      (inventory : List (AminoAcidPeptide1983.SeriesReferenceSystem ×
        AminoAcidPeptide1983.DLSubscript)) (required : Bool)
  | cipRSGeneralMethod (descriptors : List AminoAcidPeptide1983.RS)
  | proteinogenicLUsuallyS
      (cipClass : AminoAcidPeptide1983.AminoAcidCIPClass)
      (descriptor : AminoAcidPeptide1983.RS)
  | cysteineAndCystineAreRExceptions
      (inventory : List (AminoAcidPeptide1983.AminoAcidCIPClass × AminoAcidPeptide1983.RS))
  | aminoSugarDerivedRouteUsesCarbohydrateRules (authority : DelegatedAuthority)
  | alphaAndHighestSugarCenterSeriesAreIndependent
      (readings : List AminoAcidPeptide1983.AminoSugarSeriesReading)
  | mesoMeansAchiralDespiteChiralGroups
      (hasChiralGroups hasInternalCompensation : Bool)
      (symmetry : AminoAcidPeptide1983.SymmetryClass)
  | dlMeansEquimolarEnantiomers (racemate : AminoAcidPeptide1983.Racemate)
  | racAndPlusMinusAlternatives (rotation : AminoAcidPeptide1983.OpticalRotationSign)
  | nonAlphaCentersPreferRS (descriptors : List AminoAcidPeptide1983.RS)
  | uniformRSMayIncludeAlphaCenter (descriptors : List AminoAcidPeptide1983.RS)
  | carbohydrateMultiCenterPrefixesDiscouraged (policy : MultiCenterPrefixPolicy)
  | prolineCisTransReferent (referent : ProlineGeometryReferent)
  | prolineCisTransMayBeOmittedWhenUnambiguous (mayOmit : Bool)
  | alloRestrictedToIsoleucineAndThreonine (families : List String)
  | alloConfigurationInventory (inventory : List (String × List AminoAcidPeptide1983.LocatedRS))
  | unresolvedIsomersMayUseTemporaryLabels (policy : TemporaryLabelPolicy)
  | knownAndUnknownCentersUseRSAndXi
      (configuration : AminoAcidPeptide1983.PartiallyKnownConfiguration)
  | allUnknownCentersUseXi (configuration : AminoAcidPeptide1983.PartiallyKnownConfiguration)
  | knownRelativeUnknownAbsoluteUsesRStarSStar
      (configuration : AminoAcidPeptide1983.PartiallyKnownConfiguration)
  | otherElementsUseGeneralStereochemicalRules (authority : DelegatedAuthority)
  | opticalRotationSignIsSeparateFromConfiguration
      (first second : AminoAcidPeptide1983.ConfigurationAndRotation)
  | racemateMayUsePlusMinus (rotation : AminoAcidPeptide1983.OpticalRotationSign)
  | peptidePrefixIsResidueLocal (scope : ResidueScope)
  | dlForbiddenAsMultiChiralPeptideDescription
      (products : List (List AminoAcidPeptide1983.DLSeries))
  | amboDescribesAllLocalConfigurations
      (products : List (List AminoAcidPeptide1983.DLSeries))
  | amboMayBeLocalizedToOneResidue
      (products : List (List AminoAcidPeptide1983.DLSeries))
  | aminoAcidSymbolsDefaultToL
      (inventory : List (AminoAcidPeptide1983.SymbolConfigurationMark ×
        AminoAcidPeptide1983.ResidueConfiguration))
  | symbolMayExplicitlyMarkDOrDL
      (inventory : List (AminoAcidPeptide1983.SymbolConfigurationMark ×
        AminoAcidPeptide1983.ResidueConfiguration))
  | peptideSequenceDMarker (meaning : AminoAcidPeptide1983.ResidueConfiguration)
  | peptideSequenceAmboMarker (meaning : AminoAcidPeptide1983.ResidueConfiguration)
  | peptideSequenceXiMarker (meaning : AminoAcidPeptide1983.ResidueConfiguration)
  | namedPeptideEnantiomericReplacementUsesD
      (meaning : AminoAcidPeptide1983.ResidueConfiguration)
  | namedPeptideReplacementMixtureUsesAmbo
      (meaning : AminoAcidPeptide1983.ResidueConfiguration)
  | retroReversesAndEntInvertsWholeNamedPeptide
      (before retroResult entResult : List AminoAcidPeptide1983.DLSeries)
  deriving Repr

def sourceAssertion : AminoAcidPeptide1983.Provision → SourceAssertion
  | .alphaCarbonUsesSerineReferencedDL =>
      .alphaCarbonUsesSerineReferencedDL
        (AminoAcidPeptide1983.alphaPrefix (.known .D))
        (AminoAcidPeptide1983.alphaPrefix (.known .L))
  | .alphaUnknownUsesXi => .alphaUnknownUsesXi (AminoAcidPeptide1983.alphaPrefix .unknown)
  | .fischerRosanoffProjection =>
      let projection : AminoAcidPeptide1983.FischerRosanoffProjection := ⟨true, true, true, .left⟩
      .fischerRosanoffProjection projection
        (AminoAcidPeptide1983.seriesFromCanonicalFischer projection)
  | .dlPrefixImmediatelyPrecedesParent => .dlPrefixImmediatelyPrecedesParent .immediatelyBeforeParent
  | .chiralGlycineDerivativePrefixPrecedesSubstituent =>
      .chiralGlycineDerivativePrefixPrecedesSubstituent .beforeSubstituentPrefix
  | .derivativeAndPeptidePrefixPrecedesParentResidue =>
      .derivativeAndPeptidePrefixPrecedesParentResidue .beforeParentResidue
  | .proteinSourceMayOmitImpliedL => .proteinSourceMayOmitImpliedL omissionInventory
  | .unresolvedSyntheticMayOmitImpliedRacemate =>
      .unresolvedSyntheticMayOmitImpliedRacemate omissionInventory
  | .enantiomerIndependentStatementMayOmitPrefix =>
      .enantiomerIndependentStatementMayOmitPrefix omissionInventory
  | .aminoAcidAndCarbohydrateDLSubscripts =>
      .aminoAcidAndCarbohydrateDLSubscripts referenceSubscriptInventory
  | .dlSubscriptsRequiredWhenAmbiguous =>
      .dlSubscriptsRequiredWhenAmbiguous referenceSubscriptInventory true
  | .cipRSGeneralMethod => .cipRSGeneralMethod [.R, .S]
  | .proteinogenicLUsuallyS =>
      .proteinogenicLUsuallyS .ordinaryProteinogenic
        (AminoAcidPeptide1983.cipOfLAlphaCarbon .ordinaryProteinogenic)
  | .cysteineAndCystineAreRExceptions =>
      .cysteineAndCystineAreRExceptions lAlphaCIPInventory
  | .aminoSugarDerivedRouteUsesCarbohydrateRules =>
      .aminoSugarDerivedRouteUsesCarbohydrateRules .carbohydrateRecommendations1996
  | .alphaAndHighestSugarCenterSeriesAreIndependent =>
      .alphaAndHighestSugarCenterSeriesAreIndependent
        [AminoAcidPeptide1983.glucosaminicReading, AminoAcidPeptide1983.mannosaminicReading]
  | .mesoMeansAchiralDespiteChiralGroups =>
      .mesoMeansAchiralDespiteChiralGroups true true (AminoAcidPeptide1983.mesoMeaning true true)
  | .dlMeansEquimolarEnantiomers =>
      .dlMeansEquimolarEnantiomers AminoAcidPeptide1983.dlRacemate
  | .racAndPlusMinusAlternatives => .racAndPlusMinusAlternatives .plusMinus
  | .nonAlphaCentersPreferRS => .nonAlphaCentersPreferRS [.R, .S]
  | .uniformRSMayIncludeAlphaCenter => .uniformRSMayIncludeAlphaCenter [.R, .S]
  | .carbohydrateMultiCenterPrefixesDiscouraged =>
      .carbohydrateMultiCenterPrefixesDiscouraged .discouraged
  | .prolineCisTransReferent => .prolineCisTransReferent .hydroxylVersusCarboxyl
  | .prolineCisTransMayBeOmittedWhenUnambiguous =>
      .prolineCisTransMayBeOmittedWhenUnambiguous true
  | .alloRestrictedToIsoleucineAndThreonine =>
      .alloRestrictedToIsoleucineAndThreonine ["isoleucine", "threonine"]
  | .alloConfigurationInventory => .alloConfigurationInventory alloInventory
  | .unresolvedIsomersMayUseTemporaryLabels =>
      .unresolvedIsomersMayUseTemporaryLabels .allowedPendingResolution
  | .knownAndUnknownCentersUseRSAndXi =>
      .knownAndUnknownCentersUseRSAndXi AminoAcidPeptide1983.sourcePartiallyKnownExample
  | .allUnknownCentersUseXi => .allUnknownCentersUseXi allUnknownExample
  | .knownRelativeUnknownAbsoluteUsesRStarSStar =>
      .knownRelativeUnknownAbsoluteUsesRStarSStar AminoAcidPeptide1983.sourceRelativeExample
  | .otherElementsUseGeneralStereochemicalRules =>
      .otherElementsUseGeneralStereochemicalRules .generalStereochemicalNomenclature
  | .opticalRotationSignIsSeparateFromConfiguration =>
      .opticalRotationSignIsSeparateFromConfiguration
        AminoAcidPeptide1983.lPlus AminoAcidPeptide1983.lMinus
  | .racemateMayUsePlusMinus => .racemateMayUsePlusMinus .plusMinus
  | .peptidePrefixIsResidueLocal => .peptidePrefixIsResidueLocal .local
  | .dlForbiddenAsMultiChiralPeptideDescription =>
      .dlForbiddenAsMultiChiralPeptideDescription AminoAcidPeptide1983.twoResidueDLProducts
  | .amboDescribesAllLocalConfigurations =>
      .amboDescribesAllLocalConfigurations AminoAcidPeptide1983.twoResidueDLProducts
  | .amboMayBeLocalizedToOneResidue =>
      .amboMayBeLocalizedToOneResidue
        (AminoAcidPeptide1983.residueLocalMixture (.exact .L) .ambo)
  | .aminoAcidSymbolsDefaultToL => .aminoAcidSymbolsDefaultToL symbolInventory
  | .symbolMayExplicitlyMarkDOrDL => .symbolMayExplicitlyMarkDOrDL symbolInventory
  | .peptideSequenceDMarker => .peptideSequenceDMarker (AminoAcidPeptide1983.symbolMeaning .D)
  | .peptideSequenceAmboMarker =>
      .peptideSequenceAmboMarker (AminoAcidPeptide1983.symbolMeaning .ambo)
  | .peptideSequenceXiMarker =>
      .peptideSequenceXiMarker (AminoAcidPeptide1983.symbolMeaning .xi)
  | .namedPeptideEnantiomericReplacementUsesD =>
      .namedPeptideEnantiomericReplacementUsesD (AminoAcidPeptide1983.symbolMeaning .D)
  | .namedPeptideReplacementMixtureUsesAmbo =>
      .namedPeptideReplacementMixtureUsesAmbo (AminoAcidPeptide1983.symbolMeaning .ambo)
  | .retroReversesAndEntInvertsWholeNamedPeptide =>
      .retroReversesAndEntInvertsWholeNamedPeptide
        [.L, .L, .D]
        (AminoAcidPeptide1983.retroPeptide [.L, .L, .D])
        (AminoAcidPeptide1983.entPeptide [.L, .L, .D])

def SourceAssertion.provision : SourceAssertion → AminoAcidPeptide1983.Provision
  | .alphaCarbonUsesSerineReferencedDL _ _ => .alphaCarbonUsesSerineReferencedDL
  | .alphaUnknownUsesXi _ => .alphaUnknownUsesXi
  | .fischerRosanoffProjection _ _ => .fischerRosanoffProjection
  | .dlPrefixImmediatelyPrecedesParent _ => .dlPrefixImmediatelyPrecedesParent
  | .chiralGlycineDerivativePrefixPrecedesSubstituent _ =>
      .chiralGlycineDerivativePrefixPrecedesSubstituent
  | .derivativeAndPeptidePrefixPrecedesParentResidue _ =>
      .derivativeAndPeptidePrefixPrecedesParentResidue
  | .proteinSourceMayOmitImpliedL _ => .proteinSourceMayOmitImpliedL
  | .unresolvedSyntheticMayOmitImpliedRacemate _ => .unresolvedSyntheticMayOmitImpliedRacemate
  | .enantiomerIndependentStatementMayOmitPrefix _ =>
      .enantiomerIndependentStatementMayOmitPrefix
  | .aminoAcidAndCarbohydrateDLSubscripts _ => .aminoAcidAndCarbohydrateDLSubscripts
  | .dlSubscriptsRequiredWhenAmbiguous _ _ => .dlSubscriptsRequiredWhenAmbiguous
  | .cipRSGeneralMethod _ => .cipRSGeneralMethod
  | .proteinogenicLUsuallyS _ _ => .proteinogenicLUsuallyS
  | .cysteineAndCystineAreRExceptions _ => .cysteineAndCystineAreRExceptions
  | .aminoSugarDerivedRouteUsesCarbohydrateRules _ => .aminoSugarDerivedRouteUsesCarbohydrateRules
  | .alphaAndHighestSugarCenterSeriesAreIndependent _ =>
      .alphaAndHighestSugarCenterSeriesAreIndependent
  | .mesoMeansAchiralDespiteChiralGroups _ _ _ => .mesoMeansAchiralDespiteChiralGroups
  | .dlMeansEquimolarEnantiomers _ => .dlMeansEquimolarEnantiomers
  | .racAndPlusMinusAlternatives _ => .racAndPlusMinusAlternatives
  | .nonAlphaCentersPreferRS _ => .nonAlphaCentersPreferRS
  | .uniformRSMayIncludeAlphaCenter _ => .uniformRSMayIncludeAlphaCenter
  | .carbohydrateMultiCenterPrefixesDiscouraged _ => .carbohydrateMultiCenterPrefixesDiscouraged
  | .prolineCisTransReferent _ => .prolineCisTransReferent
  | .prolineCisTransMayBeOmittedWhenUnambiguous _ =>
      .prolineCisTransMayBeOmittedWhenUnambiguous
  | .alloRestrictedToIsoleucineAndThreonine _ => .alloRestrictedToIsoleucineAndThreonine
  | .alloConfigurationInventory _ => .alloConfigurationInventory
  | .unresolvedIsomersMayUseTemporaryLabels _ => .unresolvedIsomersMayUseTemporaryLabels
  | .knownAndUnknownCentersUseRSAndXi _ => .knownAndUnknownCentersUseRSAndXi
  | .allUnknownCentersUseXi _ => .allUnknownCentersUseXi
  | .knownRelativeUnknownAbsoluteUsesRStarSStar _ =>
      .knownRelativeUnknownAbsoluteUsesRStarSStar
  | .otherElementsUseGeneralStereochemicalRules _ => .otherElementsUseGeneralStereochemicalRules
  | .opticalRotationSignIsSeparateFromConfiguration _ _ =>
      .opticalRotationSignIsSeparateFromConfiguration
  | .racemateMayUsePlusMinus _ => .racemateMayUsePlusMinus
  | .peptidePrefixIsResidueLocal _ => .peptidePrefixIsResidueLocal
  | .dlForbiddenAsMultiChiralPeptideDescription _ => .dlForbiddenAsMultiChiralPeptideDescription
  | .amboDescribesAllLocalConfigurations _ => .amboDescribesAllLocalConfigurations
  | .amboMayBeLocalizedToOneResidue _ => .amboMayBeLocalizedToOneResidue
  | .aminoAcidSymbolsDefaultToL _ => .aminoAcidSymbolsDefaultToL
  | .symbolMayExplicitlyMarkDOrDL _ => .symbolMayExplicitlyMarkDOrDL
  | .peptideSequenceDMarker _ => .peptideSequenceDMarker
  | .peptideSequenceAmboMarker _ => .peptideSequenceAmboMarker
  | .peptideSequenceXiMarker _ => .peptideSequenceXiMarker
  | .namedPeptideEnantiomericReplacementUsesD _ => .namedPeptideEnantiomericReplacementUsesD
  | .namedPeptideReplacementMixtureUsesAmbo _ => .namedPeptideReplacementMixtureUsesAmbo
  | .retroReversesAndEntInvertsWholeNamedPeptide _ _ _ =>
      .retroReversesAndEntInvertsWholeNamedPeptide

@[simp] theorem sourceAssertion_provision_exact (row : AminoAcidPeptide1983.Provision) :
    (sourceAssertion row).provision = row := by
  cases row <;> rfl

structure SourceMeaning where
  sourceSection : String
  sourceKey : String
  semanticDomain : AminoAcidPeptide1983.SemanticDomain
  assertion : SourceAssertion
  deriving Repr

def sourceMeaning (row : AminoAcidPeptide1983.Provision) : SourceMeaning :=
  ⟨row.sourceSection, row.sourceKey, AminoAcidPeptide1983.provisionSemanticDomain row,
    sourceAssertion row⟩

@[simp] theorem sourceMeaning_section_exact (row : AminoAcidPeptide1983.Provision) :
    (sourceMeaning row).sourceSection = row.sourceSection := by
  rfl

@[simp] theorem sourceMeaning_key_exact (row : AminoAcidPeptide1983.Provision) :
    (sourceMeaning row).sourceKey = row.sourceKey := by
  rfl

@[simp] theorem sourceMeaning_domain_exact (row : AminoAcidPeptide1983.Provision) :
    (sourceMeaning row).semanticDomain = AminoAcidPeptide1983.provisionSemanticDomain row := by
  rfl

theorem sourceMeaning_injective : Function.Injective sourceMeaning := by
  intro left right equal
  have assertionEqual : (sourceMeaning left).assertion = (sourceMeaning right).assertion :=
    congrArg SourceMeaning.assertion equal
  have provisionEqual := congrArg SourceAssertion.provision assertionEqual
  simpa [sourceMeaning] using provisionEqual

def rows : List AminoAcidPeptide1983.Provision :=
  AminoAcidPeptide1983.Provision.all

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.aminoAcidPeptide1983

def batch : GlobalNonDescriptorSourceMeaningBatch provisions :=
  totalMeaningBatch rows IUPACNormativeProvision.aminoAcidPeptide1983 sourceMeaning
    (by intro _row; rfl)

@[simp] theorem provisions_exact :
    provisions = sourceProvisions .aminoAcidPeptideRecommendations1983 := by
  exact aminoAcidPeptide1983SemanticsSlice_exact

@[simp] theorem provision_count : provisions.length = 45 := by
  simp [provisions, rows]

@[simp] theorem entry_count : batch.entries.length = 45 := by
  rw [batch.entries_length, provision_count]

theorem provisions_nodup : provisions.Nodup := by
  exact AminoAcidPeptide1983.Provision.all_nodup.map
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
    ¬IUPACNormativeSource.ProvisionAuditComplete .aminoAcidPeptideRecommendations1983 := by
  simp [IUPACNormativeSource.ProvisionAuditComplete,
    IUPACNormativeSource.currentProvisionAuditChecklist,
    IUPACNormativeSource.ProvisionAuditChecklist.Complete,
    AminoAcidPeptide1983.currentSourceReviewProvisionEnumerationConfirmed,
    AminoAcidPeptide1983.currentSourceReviewProseTableCoverageConfirmed,
    AminoAcidPeptide1983.currentSourceReviewFigureGraphTranscriptionsReviewed]

end GlobalNonDescriptorAminoAcidPeptideSourceMeaning
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorAminoAcidPeptideSourceMeaning.sourceMeaning_injective
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorAminoAcidPeptideSourceMeaning.entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorAminoAcidPeptideSourceMeaning.every_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorAminoAcidPeptideSourceMeaning.source_audit_still_open
