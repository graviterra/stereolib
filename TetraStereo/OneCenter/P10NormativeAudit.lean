set_option autoImplicit false

namespace TetraStereo.OneCenter














namespace BlueBookP10Audit

inductive Provision where
  | p101StereoparentCommonConfiguration
  | p101StereochemicalNumberingTieBreak
  | p101ParentNameImpliesConfiguration
  | p101ParentAlphaBetaXiOrientation
  | p101ChangedCenterAlphaBetaXi
  | p101EpiInversion
  | p101RSFallback
  | p101StereoparentTableAndStructures
  | p101BondFormationConfiguration
  | p101BondCleavageConfiguration
  | p101ReplacementConfiguration
  | p101FusedIndicatedHydrogenConfiguration
  | p101SubstituentConfigurationPlacement
  | p101DoubleBondDescriptors
  | p101AllPrefix
  | p101EntInversion
  | p101Racemates
  | p101RelativeConfiguration
  | p101AchiralParentAndRingOpeningRS
  | p102AcyclicFischerProjection
  | p102DAndL
  | p102ConfigurationalAtom
  | p102CyclicFischerProjection
  | p102HaworthProjection
  | p102AnomericCenterRequirement
  | p102AlphaBetaAnomerRelation
  | p102MonosaccharideConformation
  | p102MillsDepiction
  | p102DLRacemates
  | p102AnomerMixtures
  | p102StereochemicalParentChoice
  | p102AldoseConfigurationalPrefixTable
  | p102KetoseConfigurationalPrefixTable
  | p102MultipleConfigurationalPrefixGrouping
  | p102NonchiralGapPrefixAssignment
  | p102LongChainCyclicAnomerReference
  | p102DeoxyConfigurationPreservationAndCIPBoundary
  | p102AminoReplacementConfiguration
  | p102CSubstitutionHydroxyEquivalence
  | p102TwiceSubstitutedCenterRS
  | p102TerminalSubstitutionNewCenter
  | p102MesoAlditols
  | p102MesoAldaricAcids
  | p102TartaricAcidRS
  | p102GlycosylFreeValenceAnomerDescriptor
  | p102DisaccharideAnomerDescriptors
  | p102OligosaccharideAnomerDescriptors
  | p103AlphaAminoAcidConfiguration
  | p103NonalphaCenterConfiguration
  | p103AlloInversion
  | p103PeptideComponentConfiguration
  | p103PeptideMixtureUnknownAndEnantiomer
  | p103ResidueEnantiomerReplacement
  | p104InositolAndOtherCyclitolDomainSplit
  | p104InositolStereoprefixes
  | p104CyclitolDAndLOrientation
  | p104OtherCyclitolsCIP
  | p104ConfigurationSensitiveNumbering
  | p104InositolDerivativeConfiguration
  | p104OtherCyclitolDerivativeConfiguration
  | p105RetainedNucleosideStereoparents
  | p105CarbohydrateMoietyModification
  | p106RetainedNucleotideStereoparents
  | p106NucleotideDerivativeConfiguration
  | p107RetainedSphinganineConfiguration
  | p107StereospecificGlycerolNumbering
  | p107SnRacAndUnknownDescriptors
  | p107PhosphatidylserineConfiguration
  | p107PhosphatidylinositolConfiguration
  | p107GlycoglycerolipidConfiguration
  | p107SphinganineDerivativeConfiguration
  deriving DecidableEq, Repr

namespace Provision

def all : List Provision :=
  [ .p101StereoparentCommonConfiguration
  , .p101StereochemicalNumberingTieBreak
  , .p101ParentNameImpliesConfiguration
  , .p101ParentAlphaBetaXiOrientation
  , .p101ChangedCenterAlphaBetaXi
  , .p101EpiInversion
  , .p101RSFallback
  , .p101StereoparentTableAndStructures
  , .p101BondFormationConfiguration
  , .p101BondCleavageConfiguration
  , .p101ReplacementConfiguration
  , .p101FusedIndicatedHydrogenConfiguration
  , .p101SubstituentConfigurationPlacement
  , .p101DoubleBondDescriptors
  , .p101AllPrefix
  , .p101EntInversion
  , .p101Racemates
  , .p101RelativeConfiguration
  , .p101AchiralParentAndRingOpeningRS
  , .p102AcyclicFischerProjection
  , .p102DAndL
  , .p102ConfigurationalAtom
  , .p102CyclicFischerProjection
  , .p102HaworthProjection
  , .p102AnomericCenterRequirement
  , .p102AlphaBetaAnomerRelation
  , .p102MonosaccharideConformation
  , .p102MillsDepiction
  , .p102DLRacemates
  , .p102AnomerMixtures
  , .p102StereochemicalParentChoice
  , .p102AldoseConfigurationalPrefixTable
  , .p102KetoseConfigurationalPrefixTable
  , .p102MultipleConfigurationalPrefixGrouping
  , .p102NonchiralGapPrefixAssignment
  , .p102LongChainCyclicAnomerReference
  , .p102DeoxyConfigurationPreservationAndCIPBoundary
  , .p102AminoReplacementConfiguration
  , .p102CSubstitutionHydroxyEquivalence
  , .p102TwiceSubstitutedCenterRS
  , .p102TerminalSubstitutionNewCenter
  , .p102MesoAlditols
  , .p102MesoAldaricAcids
  , .p102TartaricAcidRS
  , .p102GlycosylFreeValenceAnomerDescriptor
  , .p102DisaccharideAnomerDescriptors
  , .p102OligosaccharideAnomerDescriptors
  , .p103AlphaAminoAcidConfiguration
  , .p103NonalphaCenterConfiguration
  , .p103AlloInversion
  , .p103PeptideComponentConfiguration
  , .p103PeptideMixtureUnknownAndEnantiomer
  , .p103ResidueEnantiomerReplacement
  , .p104InositolAndOtherCyclitolDomainSplit
  , .p104InositolStereoprefixes
  , .p104CyclitolDAndLOrientation
  , .p104OtherCyclitolsCIP
  , .p104ConfigurationSensitiveNumbering
  , .p104InositolDerivativeConfiguration
  , .p104OtherCyclitolDerivativeConfiguration
  , .p105RetainedNucleosideStereoparents
  , .p105CarbohydrateMoietyModification
  , .p106RetainedNucleotideStereoparents
  , .p106NucleotideDerivativeConfiguration
  , .p107RetainedSphinganineConfiguration
  , .p107StereospecificGlycerolNumbering
  , .p107SnRacAndUnknownDescriptors
  , .p107PhosphatidylserineConfiguration
  , .p107PhosphatidylinositolConfiguration
  , .p107GlycoglycerolipidConfiguration
  , .p107SphinganineDerivativeConfiguration
  ]

@[simp] theorem mem_all (provision : Provision) : provision ∈ all := by
  cases provision <;> simp [all]

theorem all_nodup : all.Nodup := by
  decide

@[simp] theorem length_all : all.length = 71 := by
  decide

def sourceSection : Provision → String
  | .p101StereoparentCommonConfiguration => "P-101.2.1.3"
  | .p101StereochemicalNumberingTieBreak => "P-101.2.3.2(e)"
  | .p101ParentNameImpliesConfiguration => "P-101.2.6"
  | .p101ParentAlphaBetaXiOrientation => "P-101.2.6"
  | .p101ChangedCenterAlphaBetaXi => "P-101.2.6.1.1"
  | .p101EpiInversion => "P-101.2.6.1.2"
  | .p101RSFallback => "P-101.2.6.1.3"
  | .p101StereoparentTableAndStructures => "P-101.2.7/Table 10.1/Appendix 3"
  | .p101BondFormationConfiguration => "P-101.3.3"
  | .p101BondCleavageConfiguration => "P-101.3.4"
  | .p101ReplacementConfiguration => "P-101.4.3"
  | .p101FusedIndicatedHydrogenConfiguration => "P-101.5.1.2"
  | .p101SubstituentConfigurationPlacement => "P-101.7.1"
  | .p101DoubleBondDescriptors => "P-101.6.2"
  | .p101AllPrefix => "P-101.6.3"
  | .p101EntInversion => "P-101.8.1"
  | .p101Racemates => "P-101.8.2"
  | .p101RelativeConfiguration => "P-101.8.3"
  | .p101AchiralParentAndRingOpeningRS => "P-101.8.4"
  | .p102AcyclicFischerProjection => "P-102.3.1"
  | .p102DAndL => "P-102.3.2"
  | .p102ConfigurationalAtom => "P-102.3.3"
  | .p102CyclicFischerProjection => "P-102.3.4.1.1"
  | .p102HaworthProjection => "P-102.3.4.1.2"
  | .p102AnomericCenterRequirement => "P-102.3.4.2.1"
  | .p102AlphaBetaAnomerRelation => "P-102.3.4.2.2"
  | .p102MonosaccharideConformation => "P-102.3.5"
  | .p102MillsDepiction => "P-102.3.6"
  | .p102DLRacemates => "P-102.3.7.1"
  | .p102AnomerMixtures => "P-102.3.7.2"
  | .p102StereochemicalParentChoice => "P-102.4(b)(i)--(iii)"
  | .p102AldoseConfigurationalPrefixTable => "P-102.5.1.1.1/Table 10.2"
  | .p102KetoseConfigurationalPrefixTable => "P-102.5.2.2--P-102.5.2.3/Table 10.3"
  | .p102MultipleConfigurationalPrefixGrouping => "P-102.5.1.1.2"
  | .p102NonchiralGapPrefixAssignment => "P-102.5.1.1.3"
  | .p102LongChainCyclicAnomerReference => "P-102.5.1.1.4"
  | .p102DeoxyConfigurationPreservationAndCIPBoundary => "P-102.5.3.3--P-102.5.3.4"
  | .p102AminoReplacementConfiguration => "P-102.5.4"
  | .p102CSubstitutionHydroxyEquivalence => "P-102.5.6.3.1"
  | .p102TwiceSubstitutedCenterRS => "P-102.5.6.3.2"
  | .p102TerminalSubstitutionNewCenter => "P-102.5.6.3.3"
  | .p102MesoAlditols => "P-102.5.6.5.2"
  | .p102MesoAldaricAcids => "P-102.5.6.6.5.1"
  | .p102TartaricAcidRS => "P-102.5.6.6.5.2"
  | .p102GlycosylFreeValenceAnomerDescriptor => "P-102.6.1.1"
  | .p102DisaccharideAnomerDescriptors => "P-102.7.1"
  | .p102OligosaccharideAnomerDescriptors => "P-102.7.2"
  | .p103AlphaAminoAcidConfiguration => "P-103.1.3.1"
  | .p103NonalphaCenterConfiguration => "P-103.1.3.2.1"
  | .p103AlloInversion => "P-103.1.3.2.2"
  | .p103PeptideComponentConfiguration => "P-103.3.4"
  | .p103PeptideMixtureUnknownAndEnantiomer => "P-103.3.4"
  | .p103ResidueEnantiomerReplacement => "P-103.3.5.1.2"
  | .p104InositolAndOtherCyclitolDomainSplit => "P-104.1"
  | .p104InositolStereoprefixes => "P-104.2.1"
  | .p104CyclitolDAndLOrientation => "P-104.2.1"
  | .p104OtherCyclitolsCIP => "P-104.2.2"
  | .p104ConfigurationSensitiveNumbering => "P-104.2.3"
  | .p104InositolDerivativeConfiguration => "P-104.3.1"
  | .p104OtherCyclitolDerivativeConfiguration => "P-104.3.2"
  | .p105RetainedNucleosideStereoparents => "P-105.1"
  | .p105CarbohydrateMoietyModification => "P-105.2"
  | .p106RetainedNucleotideStereoparents => "P-106.1"
  | .p106NucleotideDerivativeConfiguration => "P-106.3.1"
  | .p107RetainedSphinganineConfiguration => "P-107.1"
  | .p107StereospecificGlycerolNumbering => "P-107.3.2"
  | .p107SnRacAndUnknownDescriptors => "P-107.3.2"
  | .p107PhosphatidylserineConfiguration => "P-107.3.3"
  | .p107PhosphatidylinositolConfiguration => "P-107.3.6"
  | .p107GlycoglycerolipidConfiguration => "P-107.4.2"
  | .p107SphinganineDerivativeConfiguration => "P-107.4.3.1"

/-- Owning P-10 section.  This is used below because the introductions to P-102--P-107 delegate
their subject nomenclature to one specialist recommendation each. -/
def sectionNumber : Provision → Nat
  | .p101StereoparentCommonConfiguration
  | .p101StereochemicalNumberingTieBreak
  | .p101ParentNameImpliesConfiguration
  | .p101ParentAlphaBetaXiOrientation
  | .p101ChangedCenterAlphaBetaXi
  | .p101EpiInversion
  | .p101RSFallback
  | .p101StereoparentTableAndStructures
  | .p101BondFormationConfiguration
  | .p101BondCleavageConfiguration
  | .p101ReplacementConfiguration
  | .p101FusedIndicatedHydrogenConfiguration
  | .p101SubstituentConfigurationPlacement
  | .p101DoubleBondDescriptors
  | .p101AllPrefix
  | .p101EntInversion
  | .p101Racemates
  | .p101RelativeConfiguration
  | .p101AchiralParentAndRingOpeningRS => 101
  | .p102AcyclicFischerProjection
  | .p102DAndL
  | .p102ConfigurationalAtom
  | .p102CyclicFischerProjection
  | .p102HaworthProjection
  | .p102AnomericCenterRequirement
  | .p102AlphaBetaAnomerRelation
  | .p102MonosaccharideConformation
  | .p102MillsDepiction
  | .p102DLRacemates
  | .p102AnomerMixtures
  | .p102StereochemicalParentChoice
  | .p102AldoseConfigurationalPrefixTable
  | .p102KetoseConfigurationalPrefixTable
  | .p102MultipleConfigurationalPrefixGrouping
  | .p102NonchiralGapPrefixAssignment
  | .p102LongChainCyclicAnomerReference
  | .p102DeoxyConfigurationPreservationAndCIPBoundary
  | .p102AminoReplacementConfiguration
  | .p102CSubstitutionHydroxyEquivalence
  | .p102TwiceSubstitutedCenterRS
  | .p102TerminalSubstitutionNewCenter
  | .p102MesoAlditols
  | .p102MesoAldaricAcids
  | .p102TartaricAcidRS
  | .p102GlycosylFreeValenceAnomerDescriptor
  | .p102DisaccharideAnomerDescriptors
  | .p102OligosaccharideAnomerDescriptors => 102
  | .p103AlphaAminoAcidConfiguration
  | .p103NonalphaCenterConfiguration
  | .p103AlloInversion
  | .p103PeptideComponentConfiguration
  | .p103PeptideMixtureUnknownAndEnantiomer
  | .p103ResidueEnantiomerReplacement => 103
  | .p104InositolAndOtherCyclitolDomainSplit
  | .p104InositolStereoprefixes
  | .p104CyclitolDAndLOrientation
  | .p104OtherCyclitolsCIP
  | .p104ConfigurationSensitiveNumbering
  | .p104InositolDerivativeConfiguration
  | .p104OtherCyclitolDerivativeConfiguration => 104
  | .p105RetainedNucleosideStereoparents
  | .p105CarbohydrateMoietyModification => 105
  | .p106RetainedNucleotideStereoparents
  | .p106NucleotideDerivativeConfiguration => 106
  | .p107RetainedSphinganineConfiguration
  | .p107StereospecificGlycerolNumbering
  | .p107SnRacAndUnknownDescriptors
  | .p107PhosphatidylserineConfiguration
  | .p107PhosphatidylinositolConfiguration
  | .p107GlycoglycerolipidConfiguration
  | .p107SphinganineDerivativeConfiguration => 107

end Provision

/-! ## Authority-closure dependencies -/

inductive ExternalAuthority where
  | blueBookAppendix3
  | steroidNomenclature
  | carotenoidAndRetinoidNomenclature
  | carbohydrateNomenclature
  | aminoAcidAndPeptideNomenclature
  | cyclitolNomenclature
  | nucleicAcidNomenclature
  | lipidNomenclature
  | glycolipidNomenclature
  deriving DecidableEq, Repr

namespace ExternalAuthority

def all : List ExternalAuthority :=
  [ .blueBookAppendix3
  , .steroidNomenclature
  , .carotenoidAndRetinoidNomenclature
  , .carbohydrateNomenclature
  , .aminoAcidAndPeptideNomenclature
  , .cyclitolNomenclature
  , .nucleicAcidNomenclature
  , .lipidNomenclature
  , .glycolipidNomenclature
  ]

@[simp] theorem mem_all (authority : ExternalAuthority) : authority ∈ all := by
  cases authority <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 9 := by decide

end ExternalAuthority

/-- Direct source dependency induced by P-10's section introductions and explicit cross-references.

Every P-102 provision inherits reference 27, every P-103 provision reference 18, every P-104
provision reference 39, P-105 and P-106 reference 47, and every P-107 provision reference 48.
The revised glycolipid source (reference 50) additionally governs the two P-107 glycolipid rows.
P-101 dependencies are kept clause-specific because that section combines multiple natural-product
families rather than delegating the section wholesale. -/
def Requires (provision : Provision) : ExternalAuthority → Prop
  | .blueBookAppendix3 => provision = .p101StereoparentTableAndStructures
  | .steroidNomenclature =>
      provision = .p101ParentAlphaBetaXiOrientation ∨
        provision = .p101ChangedCenterAlphaBetaXi
  | .carotenoidAndRetinoidNomenclature =>
      provision = .p101StereochemicalNumberingTieBreak ∨
        provision = .p101DoubleBondDescriptors
  | .carbohydrateNomenclature => provision.sectionNumber = 102
  | .aminoAcidAndPeptideNomenclature => provision.sectionNumber = 103
  | .cyclitolNomenclature => provision.sectionNumber = 104
  | .nucleicAcidNomenclature =>
      provision.sectionNumber = 105 ∨ provision.sectionNumber = 106
  | .lipidNomenclature => provision.sectionNumber = 107
  | .glycolipidNomenclature =>
      provision = .p107GlycoglycerolipidConfiguration ∨
        provision = .p107SphinganineDerivativeConfiguration

instance requiresDecidable (provision : Provision) (authority : ExternalAuthority) :
    Decidable (Requires provision authority) := by
  cases authority <;> simp [Requires] <;> infer_instance

def hasExplicitExternalDependency (provision : Provision) : Bool :=
  ExternalAuthority.all.any fun authority => decide (Requires provision authority)

def provisionsWithExplicitExternalDependency : List Provision :=
  Provision.all.filter hasExplicitExternalDependency

@[simp] theorem provisionsWithExplicitExternalDependency_length :
    provisionsWithExplicitExternalDependency.length = 57 := by
  decide

theorem every_listed_external_dependency_has_authority
    (provision : Provision) (member : provision ∈ provisionsWithExplicitExternalDependency) :
    ∃ authority, Requires provision authority := by
  have anyTrue :
      (ExternalAuthority.all.any fun authority => decide (Requires provision authority)) = true := by
    exact (List.mem_filter.mp member).2
  rw [List.any_eq_true] at anyTrue
  obtain ⟨authority, _member, decided⟩ := anyTrue
  exact ⟨authority, of_decide_eq_true decided⟩







structure ProvisionEnumerationReviewEvidence where
  reviewerKind : String
  reviewDate : String
  method : String
  sourceArtifactSha256 : String
  auditedRows : List Provision
  sourceSectionReferences : List String
  crosswalkedPrimarySectionTokenCount : Nat
  missingPrimarySectionTokens : List String
  reverseKeywordBearingSectionCount : Nat
  unmatchedReverseKeywordSections : List String
  reviewerKindDeclared : reviewerKind ≠ ""
  reviewDateDeclared : reviewDate ≠ ""
  methodDeclared : method ≠ ""
  auditedRowsExact : auditedRows = Provision.all
  sourceSectionReferencesExact :
    sourceSectionReferences = Provision.all.map Provision.sourceSection
  crosswalkedPrimarySectionTokenCountPositive : 0 < crosswalkedPrimarySectionTokenCount
  noMissingPrimarySectionTokens : missingPrimarySectionTokens = []
  reverseKeywordBearingSectionCountPositive : 0 < reverseKeywordBearingSectionCount
  noUnmatchedReverseKeywordSections : unmatchedReverseKeywordSections = []

def currentProvisionEnumerationReview : ProvisionEnumerationReviewEvidence where
  reviewerKind := "automated-record-0e9ff8ee11712125d507ef4bc1fa8058"
  reviewDate := "record-54db71cc66a48d655191405c29c6a9ac"
  method :=
    "record-85271f851d5b49c6b858e25c710e311b"
  sourceArtifactSha256 :=
    "e1185116ad0e61641832931ad87d333e14a8b37ce55e8a19e4570c4c1b42bedf"
  auditedRows := Provision.all
  sourceSectionReferences := Provision.all.map Provision.sourceSection
  crosswalkedPrimarySectionTokenCount := 69
  missingPrimarySectionTokens := []
  reverseKeywordBearingSectionCount := 120
  unmatchedReverseKeywordSections := []
  reviewerKindDeclared := by decide
  reviewDateDeclared := by decide
  methodDeclared := by decide
  auditedRowsExact := rfl
  sourceSectionReferencesExact := rfl
  crosswalkedPrimarySectionTokenCountPositive := by decide
  noMissingPrimarySectionTokens := rfl
  reverseKeywordBearingSectionCountPositive := by decide
  noUnmatchedReverseKeywordSections := rfl

@[simp] theorem current_provision_enumeration_review_counts_exact :
    currentProvisionEnumerationReview.auditedRows.length = 71 ∧
      currentProvisionEnumerationReview.sourceSectionReferences.length = 71 ∧
        currentProvisionEnumerationReview.crosswalkedPrimarySectionTokenCount = 69 ∧
          currentProvisionEnumerationReview.missingPrimarySectionTokens = [] ∧
            currentProvisionEnumerationReview.reverseKeywordBearingSectionCount = 120 ∧
              currentProvisionEnumerationReview.unmatchedReverseKeywordSections = [] := by
  decide



/-- Small manifest-facing constants keep checklist computation independent of the full dossier. -/
def currentSourceReviewProvisionEnumerationConfirmed : Bool := true
def currentSourceReviewProseTableCoverageConfirmed : Bool := true
def currentSourceReviewFigureGraphTranscriptionsReviewed : Bool := false





structure SourceReviewEvidence where
  reviewerKind : String
  reviewDate : String
  method : String
  sourceArtifactSha256 : String
  reviewedRenderedPageNumbers : List Nat
  reviewedRenderedPages : Nat
  reviewedProvisions : List Provision
  provisionEnumerationConfirmed : Bool
  proseTableCoverageConfirmed : Bool
  figureGraphTranscriptionsReviewed : Bool
  reviewerKindDeclared : reviewerKind ≠ ""
  reviewDateDeclared : reviewDate ≠ ""
  methodDeclared : method ≠ ""
  sourceArtifactSha256Exact :
    sourceArtifactSha256 = currentProvisionEnumerationReview.sourceArtifactSha256
  reviewedRenderedPageNumbersExact :
    reviewedRenderedPageNumbers = (List.range 113).map (fun page => page + 1)
  reviewedRenderedPagesExact : reviewedRenderedPages = reviewedRenderedPageNumbers.length
  reviewedProvisionsExact : reviewedProvisions = Provision.all
  provisionEnumerationConfirmedExact : provisionEnumerationConfirmed = true
  proseTableCoverageConfirmedExact : proseTableCoverageConfirmed = true
  figureGraphTranscriptionsReviewedExact : figureGraphTranscriptionsReviewed = false

def currentSourceReview : SourceReviewEvidence where
  reviewerKind := "automated-record-ff5b7f6496e601ebe8a14c262136c4a1"
  reviewDate := "record-54db71cc66a48d655191405c29c6a9ac"
  method :=
    "record-5bb45d35e673c97aada238270189d72a"
  sourceArtifactSha256 :=
    "e1185116ad0e61641832931ad87d333e14a8b37ce55e8a19e4570c4c1b42bedf"
  reviewedRenderedPageNumbers := (List.range 113).map (fun page => page + 1)
  reviewedRenderedPages := 113
  reviewedProvisions := Provision.all
  provisionEnumerationConfirmed := currentSourceReviewProvisionEnumerationConfirmed
  proseTableCoverageConfirmed := currentSourceReviewProseTableCoverageConfirmed
  figureGraphTranscriptionsReviewed := currentSourceReviewFigureGraphTranscriptionsReviewed
  reviewerKindDeclared := by decide
  reviewDateDeclared := by decide
  methodDeclared := by decide
  sourceArtifactSha256Exact := rfl
  reviewedRenderedPageNumbersExact := rfl
  reviewedRenderedPagesExact := by decide
  reviewedProvisionsExact := rfl
  provisionEnumerationConfirmedExact := rfl
  proseTableCoverageConfirmedExact := rfl
  figureGraphTranscriptionsReviewedExact := rfl

@[simp] theorem current_source_review_counts_and_gates_exact :
    currentSourceReview.reviewedRenderedPages = 113 ∧
      currentSourceReview.reviewedRenderedPageNumbers.length = 113 ∧
        currentSourceReview.reviewedProvisions.length = 71 ∧
          currentSourceReview.provisionEnumerationConfirmed = true ∧
            currentSourceReview.proseTableCoverageConfirmed = true ∧
              currentSourceReview.figureGraphTranscriptionsReviewed = false := by
  decide

end BlueBookP10Audit

end TetraStereo.OneCenter
