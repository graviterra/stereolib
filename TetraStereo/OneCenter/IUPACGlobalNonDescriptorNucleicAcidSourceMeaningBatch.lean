import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceDataCore
import TetraStereo.KernelOnly

set_option autoImplicit false














namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorNucleicAcidSourceMeaning

open GlobalNonDescriptorIndexedSourceData

def baseKinds : List NucleicAcid1970.BaseKind :=
  [.pyrimidine, .purine, .pseudouridine, .otherOrUnspecified]

def defaultResolutionInventory :
    List (NucleicAcid1970.BaseKind × NucleicAcid1970.ResolvedNucleosideFacts) :=
  baseKinds.map fun base => (base, NucleicAcid1970.resolveNucleosideFacts base {})

def explicitOverrideFacts : NucleicAcid1970.ExplicitNucleosideFacts :=
  { attachment? := some (.explicitlySpecified "C-5")
    anomer? := some .alpha
    sugarSeries? := some .L
    sugarIdentity? := some .arabinose }

def threeLetterInventory :
    List (NucleicAcid1970.ThreeLetterNucleoside × NucleicAcid1970.BaseKind ×
      NucleicAcid1970.ResolvedNucleosideFacts) :=
  NucleicAcid1970.ThreeLetterNucleoside.all.map fun symbol =>
    (symbol, symbol.baseKind, symbol.impliedFacts)

def sugarPrefixInventory :
    List (NucleicAcid1970.SugarPrefix × NucleicAcid1970.SugarIdentity) :=
  [ (.r, NucleicAcid1970.SugarPrefix.r.meaning)
  , (.d, NucleicAcid1970.SugarPrefix.d.meaning)
  , (.a, NucleicAcid1970.SugarPrefix.a.meaning)
  , (.x, NucleicAcid1970.SugarPrefix.x.meaning)
  , (.l, NucleicAcid1970.SugarPrefix.l.meaning) ]

def scopedModifierInventory : List NucleicAcid1970.ScopedSugarModifier :=
  [ NucleicAcid1970.uniformSeriesModifier .r
  , NucleicAcid1970.uniformSeriesModifier .d
  , ⟨.a, .oneResidue⟩ ]

def markerPlacementInventory : List (Bool × NucleicAcid1970.DeoxyMarkerPlacement) :=
  [ (false, NucleicAcid1970.deoxyMarkerPlacement false)
  , (true, NucleicAcid1970.deoxyMarkerPlacement true) ]

def mixedSeriesWitness : List NucleicAcid1970.SugarIdentity :=
  [.ribose, .twoPrimeDeoxyribose]

def nonstandardLinkage : NucleicAcid1970.DirectedPhosphodiester :=
  ⟨.twoPrime, .fivePrime⟩

/-- Typed payloads preserve actual source-model values rather than only the provision tag. -/
inductive SourceAssertion where
  | defaultsApplyOnlyWithoutExplicitSymbols
      (base : NucleicAcid1970.BaseKind)
      (explicit : NucleicAcid1970.ExplicitNucleosideFacts)
      (resolved : NucleicAcid1970.ResolvedNucleosideFacts)
  | pyrimidineGlycosylAttachmentAtOne
      (base : NucleicAcid1970.BaseKind) (attachment : Option NucleicAcid1970.GlycosylAttachment)
  | purineGlycosylAttachmentAtNine
      (base : NucleicAcid1970.BaseKind) (attachment : Option NucleicAcid1970.GlycosylAttachment)
  | pseudouridineAttachmentException
      (base : NucleicAcid1970.BaseKind) (attachment : Option NucleicAcid1970.GlycosylAttachment)
  | nucleosideLinkageDefaultsBeta
      (inventory : List (NucleicAcid1970.BaseKind × NucleicAcid1970.ResolvedNucleosideFacts))
  | sugarConfigurationDefaultsD
      (inventory : List (NucleicAcid1970.BaseKind × NucleicAcid1970.ResolvedNucleosideFacts))
  | sugarIdentityDefaultsRibosyl
      (inventory : List (NucleicAcid1970.BaseKind × NucleicAcid1970.ResolvedNucleosideFacts))
  | deoxyribosylDefaultsToTwoPrimeDeoxy
      (sugarPrefix : NucleicAcid1970.SugarPrefix) (identity : NucleicAcid1970.SugarIdentity)
  | leftToRightLinkageDefaultsThreePrimeToFivePrime
      (linkage : NucleicAcid1970.DirectedPhosphodiester) (requiresLocants : Bool)
  | threeLetterRibonucleosideInventory
      (inventory : List (NucleicAcid1970.ThreeLetterNucleoside × NucleicAcid1970.BaseKind ×
        NucleicAcid1970.ResolvedNucleosideFacts))
  | riboPrefixMayEmphasizeRibose
      (sugarPrefix : NucleicAcid1970.SugarPrefix) (identity : NucleicAcid1970.SugarIdentity)
  | deoxyPrefixMeansTwoPrimeDeoxyribose
      (sugarPrefix : NucleicAcid1970.SugarPrefix) (identity : NucleicAcid1970.SugarIdentity)
  | sugarPrefixMayScopeConnectedSeries (modifiers : List NucleicAcid1970.ScopedSugarModifier)
  | mixedRiboDeoxySeriesMarksEachResidue
      (sugars : List NucleicAcid1970.SugarIdentity) (needsPerResidueMarkers : Bool)
  | arabinoXyloLyxoPrefixes
      (meanings : List (NucleicAcid1970.SugarPrefix × NucleicAcid1970.SugarIdentity))
  | oneLetterRibonucleosideInventory (inventory : List NucleicAcid1970.OneLetterNucleoside)
  | deoxyUsesPrefixWhenUnambiguous
      (hasConflictingPrefix : Bool) (placement : NucleicAcid1970.DeoxyMarkerPlacement)
  | deoxyUsesSubscriptWhenPrefixesConflict
      (hasConflictingPrefix : Bool) (placement : NucleicAcid1970.DeoxyMarkerPlacement)
  | unusualSugarRequiresDefinedPrefix
      (sugarPrefix : NucleicAcid1970.SugarPrefix) (identity : NucleicAcid1970.SugarIdentity)
  | nonstandardLinkageRequiresLocants
      (linkage : NucleicAcid1970.DirectedPhosphodiester) (requiresLocants : Bool)
  | reverseDirectionRequiresExplicitMarker
      (defaultDirection : Bool) (allowedExplicitMarkers : List NucleicAcid1970.DirectionMarker)
  deriving DecidableEq, Repr

def sourceAssertion : NucleicAcid1970.Provision → SourceAssertion
  | .defaultsApplyOnlyWithoutExplicitSymbols =>
      .defaultsApplyOnlyWithoutExplicitSymbols .purine explicitOverrideFacts
        (NucleicAcid1970.resolveNucleosideFacts .purine explicitOverrideFacts)
  | .pyrimidineGlycosylAttachmentAtOne =>
      .pyrimidineGlycosylAttachmentAtOne .pyrimidine
        (NucleicAcid1970.defaultAttachment .pyrimidine)
  | .purineGlycosylAttachmentAtNine =>
      .purineGlycosylAttachmentAtNine .purine (NucleicAcid1970.defaultAttachment .purine)
  | .pseudouridineAttachmentException =>
      .pseudouridineAttachmentException .pseudouridine
        (NucleicAcid1970.defaultAttachment .pseudouridine)
  | .nucleosideLinkageDefaultsBeta =>
      .nucleosideLinkageDefaultsBeta defaultResolutionInventory
  | .sugarConfigurationDefaultsD =>
      .sugarConfigurationDefaultsD defaultResolutionInventory
  | .sugarIdentityDefaultsRibosyl =>
      .sugarIdentityDefaultsRibosyl defaultResolutionInventory
  | .deoxyribosylDefaultsToTwoPrimeDeoxy =>
      .deoxyribosylDefaultsToTwoPrimeDeoxy .d NucleicAcid1970.SugarPrefix.d.meaning
  | .leftToRightLinkageDefaultsThreePrimeToFivePrime =>
      .leftToRightLinkageDefaultsThreePrimeToFivePrime
        NucleicAcid1970.defaultLeftToRightLinkage
        (NucleicAcid1970.needsExplicitLinkageLocants NucleicAcid1970.defaultLeftToRightLinkage)
  | .threeLetterRibonucleosideInventory =>
      .threeLetterRibonucleosideInventory threeLetterInventory
  | .riboPrefixMayEmphasizeRibose =>
      .riboPrefixMayEmphasizeRibose .r NucleicAcid1970.SugarPrefix.r.meaning
  | .deoxyPrefixMeansTwoPrimeDeoxyribose =>
      .deoxyPrefixMeansTwoPrimeDeoxyribose .d NucleicAcid1970.SugarPrefix.d.meaning
  | .sugarPrefixMayScopeConnectedSeries =>
      .sugarPrefixMayScopeConnectedSeries scopedModifierInventory
  | .mixedRiboDeoxySeriesMarksEachResidue =>
      .mixedRiboDeoxySeriesMarksEachResidue mixedSeriesWitness
        (NucleicAcid1970.mixedRiboDeoxyNeedsPerResidueMarkers mixedSeriesWitness)
  | .arabinoXyloLyxoPrefixes =>
      .arabinoXyloLyxoPrefixes
        [(.a, NucleicAcid1970.SugarPrefix.a.meaning),
          (.x, NucleicAcid1970.SugarPrefix.x.meaning),
          (.l, NucleicAcid1970.SugarPrefix.l.meaning)]
  | .oneLetterRibonucleosideInventory =>
      .oneLetterRibonucleosideInventory NucleicAcid1970.OneLetterNucleoside.all
  | .deoxyUsesPrefixWhenUnambiguous =>
      .deoxyUsesPrefixWhenUnambiguous false (NucleicAcid1970.deoxyMarkerPlacement false)
  | .deoxyUsesSubscriptWhenPrefixesConflict =>
      .deoxyUsesSubscriptWhenPrefixesConflict true (NucleicAcid1970.deoxyMarkerPlacement true)
  | .unusualSugarRequiresDefinedPrefix =>
      let sugarPrefix : NucleicAcid1970.SugarPrefix := .definedAdHoc "q"
      .unusualSugarRequiresDefinedPrefix sugarPrefix sugarPrefix.meaning
  | .nonstandardLinkageRequiresLocants =>
      .nonstandardLinkageRequiresLocants nonstandardLinkage
        (NucleicAcid1970.needsExplicitLinkageLocants nonstandardLinkage)
  | .reverseDirectionRequiresExplicitMarker =>
      .reverseDirectionRequiresExplicitMarker false
        (NucleicAcid1970.allowedDirectionMarkers false)

def SourceAssertion.provision : SourceAssertion → NucleicAcid1970.Provision
  | .defaultsApplyOnlyWithoutExplicitSymbols _ _ _ => .defaultsApplyOnlyWithoutExplicitSymbols
  | .pyrimidineGlycosylAttachmentAtOne _ _ => .pyrimidineGlycosylAttachmentAtOne
  | .purineGlycosylAttachmentAtNine _ _ => .purineGlycosylAttachmentAtNine
  | .pseudouridineAttachmentException _ _ => .pseudouridineAttachmentException
  | .nucleosideLinkageDefaultsBeta _ => .nucleosideLinkageDefaultsBeta
  | .sugarConfigurationDefaultsD _ => .sugarConfigurationDefaultsD
  | .sugarIdentityDefaultsRibosyl _ => .sugarIdentityDefaultsRibosyl
  | .deoxyribosylDefaultsToTwoPrimeDeoxy _ _ => .deoxyribosylDefaultsToTwoPrimeDeoxy
  | .leftToRightLinkageDefaultsThreePrimeToFivePrime _ _ =>
      .leftToRightLinkageDefaultsThreePrimeToFivePrime
  | .threeLetterRibonucleosideInventory _ => .threeLetterRibonucleosideInventory
  | .riboPrefixMayEmphasizeRibose _ _ => .riboPrefixMayEmphasizeRibose
  | .deoxyPrefixMeansTwoPrimeDeoxyribose _ _ => .deoxyPrefixMeansTwoPrimeDeoxyribose
  | .sugarPrefixMayScopeConnectedSeries _ => .sugarPrefixMayScopeConnectedSeries
  | .mixedRiboDeoxySeriesMarksEachResidue _ _ => .mixedRiboDeoxySeriesMarksEachResidue
  | .arabinoXyloLyxoPrefixes _ => .arabinoXyloLyxoPrefixes
  | .oneLetterRibonucleosideInventory _ => .oneLetterRibonucleosideInventory
  | .deoxyUsesPrefixWhenUnambiguous _ _ => .deoxyUsesPrefixWhenUnambiguous
  | .deoxyUsesSubscriptWhenPrefixesConflict _ _ => .deoxyUsesSubscriptWhenPrefixesConflict
  | .unusualSugarRequiresDefinedPrefix _ _ => .unusualSugarRequiresDefinedPrefix
  | .nonstandardLinkageRequiresLocants _ _ => .nonstandardLinkageRequiresLocants
  | .reverseDirectionRequiresExplicitMarker _ _ => .reverseDirectionRequiresExplicitMarker

@[simp] theorem sourceAssertion_provision_exact (row : NucleicAcid1970.Provision) :
    (sourceAssertion row).provision = row := by
  cases row <;> rfl

structure SourceMeaning where
  sourceSection : String
  sourceKey : String
  semanticDomain : NucleicAcid1970.SemanticDomain
  incorporatedErrata : List NucleicAcid1970.IncorporatedErratum
  assertion : SourceAssertion
  deriving DecidableEq, Repr

def sourceMeaning (row : NucleicAcid1970.Provision) : SourceMeaning :=
  ⟨row.sourceSection, row.sourceKey, NucleicAcid1970.provisionSemanticDomain row,
    NucleicAcid1970.IncorporatedErratum.all, sourceAssertion row⟩

@[simp] theorem sourceMeaning_section_exact (row : NucleicAcid1970.Provision) :
    (sourceMeaning row).sourceSection = row.sourceSection := by
  rfl

@[simp] theorem sourceMeaning_key_exact (row : NucleicAcid1970.Provision) :
    (sourceMeaning row).sourceKey = row.sourceKey := by
  rfl

@[simp] theorem sourceMeaning_domain_exact (row : NucleicAcid1970.Provision) :
    (sourceMeaning row).semanticDomain = NucleicAcid1970.provisionSemanticDomain row := by
  rfl

@[simp] theorem sourceMeaning_errata_exact (row : NucleicAcid1970.Provision) :
    (sourceMeaning row).incorporatedErrata = NucleicAcid1970.IncorporatedErratum.all := by
  rfl

theorem sourceMeaning_errata_nonsemantic (row : NucleicAcid1970.Provision) :
    (sourceMeaning row).incorporatedErrata.Forall fun erratum =>
      !erratum.changesConfigurationSemantics := by
  simp [sourceMeaning, NucleicAcid1970.IncorporatedErratum.all,
    NucleicAcid1970.IncorporatedErratum.changesConfigurationSemantics]

theorem sourceMeaning_injective : Function.Injective sourceMeaning := by
  intro left right equal
  have assertionEqual : (sourceMeaning left).assertion = (sourceMeaning right).assertion :=
    congrArg SourceMeaning.assertion equal
  have provisionEqual := congrArg SourceAssertion.provision assertionEqual
  simpa [sourceMeaning] using provisionEqual

def rows : List NucleicAcid1970.Provision :=
  NucleicAcid1970.Provision.all

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.nucleicAcid1970

def batch : GlobalNonDescriptorSourceMeaningBatch provisions :=
  totalMeaningBatch rows IUPACNormativeProvision.nucleicAcid1970 sourceMeaning
    (by intro _row; rfl)

@[simp] theorem provisions_exact :
    provisions = sourceProvisions .nucleicAcidRecommendations1970 := by
  exact nucleicAcid1970SemanticsSlice_exact

@[simp] theorem provision_count : provisions.length = 21 := by
  simp [provisions, rows]

@[simp] theorem entry_count : batch.entries.length = 21 := by
  rw [batch.entries_length, provision_count]

theorem provisions_nodup : provisions.Nodup := by
  exact NucleicAcid1970.Provision.all_nodup.map
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

theorem source_audit_complete :
    IUPACNormativeSource.ProvisionAuditComplete .nucleicAcidRecommendations1970 := by
  simp [IUPACNormativeSource.ProvisionAuditComplete,
    IUPACNormativeSource.currentProvisionAuditChecklist,
    IUPACNormativeSource.ProvisionAuditChecklist.Complete,
    NucleicAcid1970.currentSourceReviewProvisionEnumerationConfirmed,
    NucleicAcid1970.currentSourceReviewProseTableCoverageConfirmed,
    NucleicAcid1970.currentSourceReviewFigureGraphTranscriptionsReviewed]

end GlobalNonDescriptorNucleicAcidSourceMeaning
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorNucleicAcidSourceMeaning.provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorNucleicAcidSourceMeaning.sourceMeaning_injective
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorNucleicAcidSourceMeaning.sourceMeaning_errata_nonsemantic
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorNucleicAcidSourceMeaning.entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorNucleicAcidSourceMeaning.every_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorNucleicAcidSourceMeaning.source_audit_complete
