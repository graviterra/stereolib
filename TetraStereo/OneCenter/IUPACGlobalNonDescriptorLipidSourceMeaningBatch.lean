import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceDataCore
import TetraStereo.KernelOnly

set_option autoImplicit false















namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorLipidSourceMeaning

open GlobalNonDescriptorIndexedSourceData

def sourceStatusInventory : List (String × Lipid1976.SourceStatus) :=
  [ ("Lip-1.10 (current edited text)", Lipid1976.sectionStatus "Lip-1.10 (current edited text)")
  , ("Lip-1.10 archive", Lipid1976.sectionStatus "Lip-1.10 archive")
  , ("Lip-3 superseded part", Lipid1976.sectionStatus "Lip-3 superseded part") ]

def compoundApplicabilityInventory : List (Lipid1976.CompoundFamily × Bool) :=
  [ (.glycerolDerivative, Lipid1976.stereospecificNumberingApplicable .glycerolDerivative)
  , (.sphingoid, Lipid1976.stereospecificNumberingApplicable .sphingoid)
  , (.other, Lipid1976.stereospecificNumberingApplicable .other) ]

def sphingoidParents : List Lipid1976.SphingoidParent :=
  [.sphinganine, .dThreoC2Epimer, .phytosphingosine, .sphingosine, .cisFourSphingenine]

def sphingoidInventory :
    List (Lipid1976.SphingoidParent × List Lipid1976.LocatedRS × List Lipid1976.LocatedEZ ×
      Option (Lipid1976.DLSeries × Lipid1976.ErythroThreo) × Bool) :=
  sphingoidParents.map fun parent =>
    (parent, parent.centerConfiguration, parent.doubleBondConfiguration,
      parent.classConfiguration, Lipid1976.mayUseSphinganineRoot parent)

def glycerolSiteInventory : List (Lipid1976.PhysicalGlycerolSite × Nat) :=
  [ (.topInReferenceFischer, Lipid1976.snLocant .topInReferenceFischer)
  , (.middle, Lipid1976.snLocant .middle)
  , (.bottomInReferenceFischer, Lipid1976.snLocant .bottomInReferenceFischer) ]

def knowledgePrefixInventory :
    List (Lipid1976.KnowledgeState × Lipid1976.ConfigurationPrefix) :=
  [ (.oneEnantiomer, Lipid1976.prefixForKnowledge .oneEnantiomer)
  , (.equalAntipodes, Lipid1976.prefixForKnowledge .equalAntipodes)
  , (.unknownOrUnspecified, Lipid1976.prefixForKnowledge .unknownOrUnspecified) ]

def glycerolPhosphateInventory :
    List (Lipid1976.GlycerolPhosphate × List Lipid1976.ConventionalGlycerolName ×
      Lipid1976.GlycerolPhosphate) :=
  [ (.snGlycerol3Phosphate,
      Lipid1976.conventionalEquivalentNames .snGlycerol3Phosphate,
      Lipid1976.GlycerolPhosphate.enantiomer .snGlycerol3Phosphate)
  , (.snGlycerol1Phosphate,
      Lipid1976.conventionalEquivalentNames .snGlycerol1Phosphate,
      Lipid1976.GlycerolPhosphate.enantiomer .snGlycerol1Phosphate) ]

def glycerophospholipidParentInventory : List Lipid1976.SnGlycerolSubstitution :=
  [ Lipid1976.commonPhosphatidicAcid
  , Lipid1976.plasmenicAcid
  , Lipid1976.lysoplasmenicAcid
  , Lipid1976.plasmanicAcid ]

/-- Typed payloads preserve actual source-model values rather than only the manifest row tag. -/
inductive SourceAssertion where
  | stereospecificNumberingLimitedToGlycerol
      (inventory : List (Lipid1976.CompoundFamily × Bool))
  | laterGlycolipidRulesSupersedeParts (sectionKey : String) (status : Lipid1976.SourceStatus)
  | currentEditedLip110ReplacesArchive (statuses : List (String × Lipid1976.SourceStatus))
  | sphingoidGenericIncludesStereoisomers
      (inventory : List (Lipid1976.SphingoidParent × List Lipid1976.LocatedRS ×
        List Lipid1976.LocatedEZ × Option (Lipid1976.DLSeries × Lipid1976.ErythroThreo) × Bool))
  | sphinganineImpliedConfiguration
      (parent : Lipid1976.SphingoidParent) (centers : List Lipid1976.LocatedRS)
      (classConfiguration : Option (Lipid1976.DLSeries × Lipid1976.ErythroThreo))
  | sphinganineRootImpliesConfiguration (parent : Lipid1976.SphingoidParent) (mayUseRoot : Bool)
  | c2c3StereoisomersUseSystematicNames
      (parent : Lipid1976.SphingoidParent) (mayUseRoot : Bool)
  | substitutedSphingoidsUseRS (descriptors : List Lipid1976.RS)
  | sphingoidRSMayRelabelAfterSubstitution
      (before after : Lipid1976.SphingoidRelabelExample)
  | phytosphingosineConfiguration
      (parent : Lipid1976.SphingoidParent) (centers : List Lipid1976.LocatedRS)
  | sphingosineConfiguration
      (parent : Lipid1976.SphingoidParent) (centers : List Lipid1976.LocatedRS)
      (doubleBonds : List Lipid1976.LocatedEZ)
  | cisFourSphingenineConfiguration
      (parent : Lipid1976.SphingoidParent) (doubleBonds : List Lipid1976.LocatedEZ)
  | knownDoubleBondGeometryUsesEZ (descriptors : List Lipid1976.EZ)
  | glycerolNumberingIsStereospecific
      (kind : Lipid1976.GlycerolNumberingKind) (prefixValue : Option String)
  | glycerolReferenceFischerProjection
      (projection : Lipid1976.ReferenceFischerProjection) (isReference : Bool)
      (sites : List (Lipid1976.PhysicalGlycerolSite × Nat))
  | snPrefixDistinguishesFixedNumbering
      (kind : Lipid1976.GlycerolNumberingKind) (prefixValue : Option String)
  | racPrefixMeansEqualAntipodes
      (knowledge : Lipid1976.KnowledgeState) (prefixValue : Lipid1976.ConfigurationPrefix)
  | xPrefixMeansUnknownOrUnspecified
      (knowledge : Lipid1976.KnowledgeState) (prefixValue : Lipid1976.ConfigurationPrefix)
  | snGlycerolThreePhosphateEquivalences
      (parent : Lipid1976.GlycerolPhosphate) (names : List Lipid1976.ConventionalGlycerolName)
  | snGlycerolOnePhosphateIsEnantiomer
      (parent enantiomer : Lipid1976.GlycerolPhosphate)
  | glycerolRSMayRelabelAfterSubstitution
      (before after : Lipid1976.GlycerolCIPReading)
  | phosphatidicAcidMayUseSnLocants
      (parent : Lipid1976.SnGlycerolSubstitution) (prefixValue : Option String)
  | commonPhosphatidicAcidPositions (parent : Lipid1976.SnGlycerolSubstitution)
  | phosphatidylLocantsPreferred (locants : List Nat)
  | glycerophospholipidStemUsesSnPositions
      (parent : Lipid1976.SnGlycerolSubstitution) (sites : List (Lipid1976.PhysicalGlycerolSite × Nat))
  | phosphatidylinositolContainsThreeSnPhosphatidyl
      (reference : Lipid1976.PhosphatidylinositolReference)
  | plasmenicAcidPositions (parent : Lipid1976.SnGlycerolSubstitution)
  | positionTwoPhosphateNotPlasmenic
      (candidate : Lipid1976.SnGlycerolSubstitution) (isPlasmenic : Bool)
  | lysoplasmenicAcidPositions (parent : Lipid1976.SnGlycerolSubstitution)
  | plasmanicAcidPositions (parent : Lipid1976.SnGlycerolSubstitution)
  | individualGlycerophospholipidUsesSn
      (parents : List Lipid1976.SnGlycerolSubstitution) (prefixValue : Option String)
  deriving Repr

def sourceAssertion : Lipid1976.Provision → SourceAssertion
  | .stereospecificNumberingLimitedToGlycerol =>
      .stereospecificNumberingLimitedToGlycerol compoundApplicabilityInventory
  | .laterGlycolipidRulesSupersedeParts =>
      .laterGlycolipidRulesSupersedeParts "Lip-3 superseded part"
        (Lipid1976.sectionStatus "Lip-3 superseded part")
  | .currentEditedLip110ReplacesArchive =>
      .currentEditedLip110ReplacesArchive
        [("Lip-1.10 (current edited text)", Lipid1976.sectionStatus "Lip-1.10 (current edited text)"),
          ("Lip-1.10 archive", Lipid1976.sectionStatus "Lip-1.10 archive")]
  | .sphingoidGenericIncludesStereoisomers =>
      .sphingoidGenericIncludesStereoisomers sphingoidInventory
  | .sphinganineImpliedConfiguration =>
      .sphinganineImpliedConfiguration .sphinganine
        Lipid1976.SphingoidParent.sphinganine.centerConfiguration
        Lipid1976.SphingoidParent.sphinganine.classConfiguration
  | .sphinganineRootImpliesConfiguration =>
      .sphinganineRootImpliesConfiguration .sphinganine
        (Lipid1976.mayUseSphinganineRoot .sphinganine)
  | .c2c3StereoisomersUseSystematicNames =>
      .c2c3StereoisomersUseSystematicNames .dThreoC2Epimer
        (Lipid1976.mayUseSphinganineRoot .dThreoC2Epimer)
  | .substitutedSphingoidsUseRS => .substitutedSphingoidsUseRS [.R, .S]
  | .sphingoidRSMayRelabelAfterSubstitution =>
      .sphingoidRSMayRelabelAfterSubstitution
        Lipid1976.icosasphinganineReading Lipid1976.fourHydroxysphinganineReading
  | .phytosphingosineConfiguration =>
      .phytosphingosineConfiguration .phytosphingosine
        Lipid1976.SphingoidParent.phytosphingosine.centerConfiguration
  | .sphingosineConfiguration =>
      .sphingosineConfiguration .sphingosine
        Lipid1976.SphingoidParent.sphingosine.centerConfiguration
        Lipid1976.SphingoidParent.sphingosine.doubleBondConfiguration
  | .cisFourSphingenineConfiguration =>
      .cisFourSphingenineConfiguration .cisFourSphingenine
        Lipid1976.SphingoidParent.cisFourSphingenine.doubleBondConfiguration
  | .knownDoubleBondGeometryUsesEZ => .knownDoubleBondGeometryUsesEZ [.E, .Z]
  | .glycerolNumberingIsStereospecific =>
      .glycerolNumberingIsStereospecific .stereospecific
        (Lipid1976.prefixForNumbering .stereospecific)
  | .glycerolReferenceFischerProjection =>
      let projection : Lipid1976.ReferenceFischerProjection := ⟨true, true⟩
      .glycerolReferenceFischerProjection projection
        (Lipid1976.isSnReferenceProjection projection) glycerolSiteInventory
  | .snPrefixDistinguishesFixedNumbering =>
      .snPrefixDistinguishesFixedNumbering .stereospecific
        (Lipid1976.prefixForNumbering .stereospecific)
  | .racPrefixMeansEqualAntipodes =>
      .racPrefixMeansEqualAntipodes .equalAntipodes (Lipid1976.prefixForKnowledge .equalAntipodes)
  | .xPrefixMeansUnknownOrUnspecified =>
      .xPrefixMeansUnknownOrUnspecified .unknownOrUnspecified
        (Lipid1976.prefixForKnowledge .unknownOrUnspecified)
  | .snGlycerolThreePhosphateEquivalences =>
      .snGlycerolThreePhosphateEquivalences .snGlycerol3Phosphate
        (Lipid1976.conventionalEquivalentNames .snGlycerol3Phosphate)
  | .snGlycerolOnePhosphateIsEnantiomer =>
      .snGlycerolOnePhosphateIsEnantiomer .snGlycerol1Phosphate
        (Lipid1976.GlycerolPhosphate.enantiomer .snGlycerol1Phosphate)
  | .glycerolRSMayRelabelAfterSubstitution =>
      .glycerolRSMayRelabelAfterSubstitution Lipid1976.snOneR Lipid1976.snOneS
  | .phosphatidicAcidMayUseSnLocants =>
      .phosphatidicAcidMayUseSnLocants Lipid1976.commonPhosphatidicAcid
        (Lipid1976.prefixForNumbering .stereospecific)
  | .commonPhosphatidicAcidPositions =>
      .commonPhosphatidicAcidPositions Lipid1976.commonPhosphatidicAcid
  | .phosphatidylLocantsPreferred => .phosphatidylLocantsPreferred [1, 2, 3]
  | .glycerophospholipidStemUsesSnPositions =>
      .glycerophospholipidStemUsesSnPositions Lipid1976.commonPhosphatidicAcid
        glycerolSiteInventory
  | .phosphatidylinositolContainsThreeSnPhosphatidyl =>
      .phosphatidylinositolContainsThreeSnPhosphatidyl
        Lipid1976.standardPhosphatidylinositol
  | .plasmenicAcidPositions => .plasmenicAcidPositions Lipid1976.plasmenicAcid
  | .positionTwoPhosphateNotPlasmenic =>
      let candidate : Lipid1976.SnGlycerolSubstitution := ⟨.oneAlkenyl, .phosphate, .acyl⟩
      .positionTwoPhosphateNotPlasmenic candidate
        (Lipid1976.positionTwoPhosphateIsPlasmenic candidate)
  | .lysoplasmenicAcidPositions =>
      .lysoplasmenicAcidPositions Lipid1976.lysoplasmenicAcid
  | .plasmanicAcidPositions => .plasmanicAcidPositions Lipid1976.plasmanicAcid
  | .individualGlycerophospholipidUsesSn =>
      .individualGlycerophospholipidUsesSn glycerophospholipidParentInventory
        (Lipid1976.prefixForNumbering .stereospecific)

def SourceAssertion.provision : SourceAssertion → Lipid1976.Provision
  | .stereospecificNumberingLimitedToGlycerol _ => .stereospecificNumberingLimitedToGlycerol
  | .laterGlycolipidRulesSupersedeParts _ _ => .laterGlycolipidRulesSupersedeParts
  | .currentEditedLip110ReplacesArchive _ => .currentEditedLip110ReplacesArchive
  | .sphingoidGenericIncludesStereoisomers _ => .sphingoidGenericIncludesStereoisomers
  | .sphinganineImpliedConfiguration _ _ _ => .sphinganineImpliedConfiguration
  | .sphinganineRootImpliesConfiguration _ _ => .sphinganineRootImpliesConfiguration
  | .c2c3StereoisomersUseSystematicNames _ _ => .c2c3StereoisomersUseSystematicNames
  | .substitutedSphingoidsUseRS _ => .substitutedSphingoidsUseRS
  | .sphingoidRSMayRelabelAfterSubstitution _ _ => .sphingoidRSMayRelabelAfterSubstitution
  | .phytosphingosineConfiguration _ _ => .phytosphingosineConfiguration
  | .sphingosineConfiguration _ _ _ => .sphingosineConfiguration
  | .cisFourSphingenineConfiguration _ _ => .cisFourSphingenineConfiguration
  | .knownDoubleBondGeometryUsesEZ _ => .knownDoubleBondGeometryUsesEZ
  | .glycerolNumberingIsStereospecific _ _ => .glycerolNumberingIsStereospecific
  | .glycerolReferenceFischerProjection _ _ _ => .glycerolReferenceFischerProjection
  | .snPrefixDistinguishesFixedNumbering _ _ => .snPrefixDistinguishesFixedNumbering
  | .racPrefixMeansEqualAntipodes _ _ => .racPrefixMeansEqualAntipodes
  | .xPrefixMeansUnknownOrUnspecified _ _ => .xPrefixMeansUnknownOrUnspecified
  | .snGlycerolThreePhosphateEquivalences _ _ => .snGlycerolThreePhosphateEquivalences
  | .snGlycerolOnePhosphateIsEnantiomer _ _ => .snGlycerolOnePhosphateIsEnantiomer
  | .glycerolRSMayRelabelAfterSubstitution _ _ => .glycerolRSMayRelabelAfterSubstitution
  | .phosphatidicAcidMayUseSnLocants _ _ => .phosphatidicAcidMayUseSnLocants
  | .commonPhosphatidicAcidPositions _ => .commonPhosphatidicAcidPositions
  | .phosphatidylLocantsPreferred _ => .phosphatidylLocantsPreferred
  | .glycerophospholipidStemUsesSnPositions _ _ => .glycerophospholipidStemUsesSnPositions
  | .phosphatidylinositolContainsThreeSnPhosphatidyl _ =>
      .phosphatidylinositolContainsThreeSnPhosphatidyl
  | .plasmenicAcidPositions _ => .plasmenicAcidPositions
  | .positionTwoPhosphateNotPlasmenic _ _ => .positionTwoPhosphateNotPlasmenic
  | .lysoplasmenicAcidPositions _ => .lysoplasmenicAcidPositions
  | .plasmanicAcidPositions _ => .plasmanicAcidPositions
  | .individualGlycerophospholipidUsesSn _ _ => .individualGlycerophospholipidUsesSn

@[simp] theorem sourceAssertion_provision_exact (row : Lipid1976.Provision) :
    (sourceAssertion row).provision = row := by
  cases row <;> rfl

structure SourceMeaning where
  sourceSection : String
  sourceKey : String
  semanticDomain : Lipid1976.SemanticDomain
  assertion : SourceAssertion
  deriving Repr

def sourceMeaning (row : Lipid1976.Provision) : SourceMeaning :=
  ⟨row.sourceSection, row.sourceKey, Lipid1976.provisionSemanticDomain row, sourceAssertion row⟩

@[simp] theorem sourceMeaning_section_exact (row : Lipid1976.Provision) :
    (sourceMeaning row).sourceSection = row.sourceSection := by
  rfl

@[simp] theorem sourceMeaning_key_exact (row : Lipid1976.Provision) :
    (sourceMeaning row).sourceKey = row.sourceKey := by
  rfl

@[simp] theorem sourceMeaning_domain_exact (row : Lipid1976.Provision) :
    (sourceMeaning row).semanticDomain = Lipid1976.provisionSemanticDomain row := by
  rfl

theorem sourceMeaning_injective : Function.Injective sourceMeaning := by
  intro left right equal
  have assertionEqual : (sourceMeaning left).assertion = (sourceMeaning right).assertion :=
    congrArg SourceMeaning.assertion equal
  have provisionEqual := congrArg SourceAssertion.provision assertionEqual
  simpa [sourceMeaning] using provisionEqual

def rows : List Lipid1976.Provision :=
  Lipid1976.Provision.all

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.lipid1976

def batch : GlobalNonDescriptorSourceMeaningBatch provisions :=
  totalMeaningBatch rows IUPACNormativeProvision.lipid1976 sourceMeaning
    (by intro _row; rfl)

@[simp] theorem provisions_exact :
    provisions = sourceProvisions .lipidRecommendations1976 := by
  exact lipid1976SemanticsSlice_exact

@[simp] theorem provision_count : provisions.length = 31 := by
  simp [provisions, rows]

@[simp] theorem entry_count : batch.entries.length = 31 := by
  rw [batch.entries_length, provision_count]

theorem provisions_nodup : provisions.Nodup := by
  exact Lipid1976.Provision.all_nodup.map
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
    ¬IUPACNormativeSource.ProvisionAuditComplete .lipidRecommendations1976 := by
  simp [IUPACNormativeSource.ProvisionAuditComplete,
    IUPACNormativeSource.currentProvisionAuditChecklist,
    IUPACNormativeSource.ProvisionAuditChecklist.Complete,
    Lipid1976.currentSourceReviewProvisionEnumerationConfirmed,
    Lipid1976.currentSourceReviewProseTableCoverageConfirmed,
    Lipid1976.currentSourceReviewFigureGraphTranscriptionsReviewed]

end GlobalNonDescriptorLipidSourceMeaning
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorLipidSourceMeaning.provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorLipidSourceMeaning.sourceMeaning_injective
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorLipidSourceMeaning.entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorLipidSourceMeaning.every_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorLipidSourceMeaning.source_audit_still_open
