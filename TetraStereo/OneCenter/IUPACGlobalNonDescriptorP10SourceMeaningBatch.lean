import TetraStereo.OneCenter.IUPACGlobalNonDescriptorIndexedSourceDataCore
import TetraStereo.KernelOnly

set_option autoImplicit false














namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorP10SourceMeaning

open GlobalNonDescriptorIndexedSourceData

/-- The three independent semantic layers whose disjoint source-order union is P-10. -/
inductive SemanticDomain where
  | p101 (domain : BlueBookP101.SemanticDomain)
  | p102 (domain : BlueBookP102.SemanticDomain)
  | p103to107 (domain : BlueBookP103to107.SemanticDomain)
  deriving DecidableEq, Repr

/-- Total, typed ownership of every audited P-10 row by its independent semantic domain. -/
def semanticDomain : BlueBookP10Audit.Provision → SemanticDomain
  | .p101StereoparentCommonConfiguration
  | .p101ParentNameImpliesConfiguration
  | .p101ParentAlphaBetaXiOrientation
  | .p101StereoparentTableAndStructures => .p101 .retainedParent
  | .p101StereochemicalNumberingTieBreak => .p101 .numbering
  | .p101ChangedCenterAlphaBetaXi
  | .p101EpiInversion
  | .p101RSFallback => .p101 .changedCenter
  | .p101BondFormationConfiguration
  | .p101BondCleavageConfiguration
  | .p101ReplacementConfiguration => .p101 .skeletalModification
  | .p101FusedIndicatedHydrogenConfiguration => .p101 .fusion
  | .p101SubstituentConfigurationPlacement => .p101 .substitution
  | .p101DoubleBondDescriptors
  | .p101AllPrefix => .p101 .doubleBond
  | .p101EntInversion
  | .p101Racemates
  | .p101RelativeConfiguration
  | .p101AchiralParentAndRingOpeningRS => .p101 .wholeMoleculeScope
  | .p102AcyclicFischerProjection
  | .p102DAndL
  | .p102ConfigurationalAtom => .p102 .projectionAndSeries
  | .p102CyclicFischerProjection
  | .p102HaworthProjection
  | .p102AnomericCenterRequirement
  | .p102AlphaBetaAnomerRelation => .p102 .cyclicAndAnomeric
  | .p102MonosaccharideConformation
  | .p102MillsDepiction => .p102 .conformationAndDepiction
  | .p102DLRacemates
  | .p102AnomerMixtures => .p102 .mixtures
  | .p102StereochemicalParentChoice => .p102 .parentChoice
  | .p102AldoseConfigurationalPrefixTable
  | .p102KetoseConfigurationalPrefixTable
  | .p102MultipleConfigurationalPrefixGrouping
  | .p102NonchiralGapPrefixAssignment
  | .p102LongChainCyclicAnomerReference => .p102 .configurationalPrefixes
  | .p102DeoxyConfigurationPreservationAndCIPBoundary
  | .p102AminoReplacementConfiguration
  | .p102CSubstitutionHydroxyEquivalence
  | .p102TwiceSubstitutedCenterRS
  | .p102TerminalSubstitutionNewCenter => .p102 .modifiedSugars
  | .p102MesoAlditols
  | .p102MesoAldaricAcids
  | .p102TartaricAcidRS => .p102 .mesoAndAcids
  | .p102GlycosylFreeValenceAnomerDescriptor
  | .p102DisaccharideAnomerDescriptors
  | .p102OligosaccharideAnomerDescriptors => .p102 .saccharideComponents
  | .p103AlphaAminoAcidConfiguration
  | .p103NonalphaCenterConfiguration
  | .p103AlloInversion => .p103to107 .aminoAcid
  | .p103PeptideComponentConfiguration
  | .p103PeptideMixtureUnknownAndEnantiomer
  | .p103ResidueEnantiomerReplacement => .p103to107 .peptide
  | .p104InositolAndOtherCyclitolDomainSplit
  | .p104InositolStereoprefixes
  | .p104CyclitolDAndLOrientation
  | .p104OtherCyclitolsCIP
  | .p104ConfigurationSensitiveNumbering
  | .p104InositolDerivativeConfiguration
  | .p104OtherCyclitolDerivativeConfiguration => .p103to107 .cyclitol
  | .p105RetainedNucleosideStereoparents
  | .p105CarbohydrateMoietyModification => .p103to107 .nucleoside
  | .p106RetainedNucleotideStereoparents
  | .p106NucleotideDerivativeConfiguration => .p103to107 .nucleotide
  | .p107RetainedSphinganineConfiguration
  | .p107StereospecificGlycerolNumbering
  | .p107SnRacAndUnknownDescriptors
  | .p107PhosphatidylserineConfiguration
  | .p107PhosphatidylinositolConfiguration
  | .p107GlycoglycerolipidConfiguration
  | .p107SphinganineDerivativeConfiguration => .p103to107 .lipid

/-- Every direct P-10 cross-reference, retained as data rather than collapsed to a Boolean. -/
def externalAuthorities (row : BlueBookP10Audit.Provision) :
    List BlueBookP10Audit.ExternalAuthority :=
  BlueBookP10Audit.ExternalAuthority.all.filter fun authority =>
    decide (BlueBookP10Audit.Requires row authority)

/-- Typed partial source meaning compiled from the three independent semantic layers. -/
structure SourceMeaning where
  provision : BlueBookP10Audit.Provision
  sourceSection : String
  semanticDomain : SemanticDomain
  externalAuthorities : List BlueBookP10Audit.ExternalAuthority
  deriving DecidableEq, Repr

def sourceMeaning (row : BlueBookP10Audit.Provision) : SourceMeaning :=
  ⟨row, row.sourceSection, semanticDomain row, externalAuthorities row⟩

@[simp] theorem sourceMeaning_provision_exact (row : BlueBookP10Audit.Provision) :
    (sourceMeaning row).provision = row :=
  rfl

@[simp] theorem sourceMeaning_section_exact (row : BlueBookP10Audit.Provision) :
    (sourceMeaning row).sourceSection = row.sourceSection :=
  rfl

@[simp] theorem sourceMeaning_externalAuthorities_exact (row : BlueBookP10Audit.Provision) :
    (sourceMeaning row).externalAuthorities =
      BlueBookP10Audit.ExternalAuthority.all.filter fun authority =>
        decide (BlueBookP10Audit.Requires row authority) :=
  rfl

/-- The payload preserves the exact existing P-101 domain assignment. -/
theorem sourceMeaning_p101_domain (row : BlueBookP10Audit.Provision)
    (member : row ∈ BlueBookP101.p101Provisions) :
    ∃ domain, (sourceMeaning row).semanticDomain = .p101 domain := by
  cases row <;>
    simp [BlueBookP101.p101Provisions, sourceMeaning, semanticDomain] at member ⊢

/-- The payload preserves the exact existing P-102 domain assignment. -/
theorem sourceMeaning_p102_domain (row : BlueBookP10Audit.Provision)
    (member : row ∈ BlueBookP102.p102Provisions) :
    ∃ domain, (sourceMeaning row).semanticDomain = .p102 domain := by
  cases row <;>
    simp [BlueBookP102.p102Provisions, sourceMeaning, semanticDomain] at member ⊢

/-- The payload preserves the exact existing P-103--P-107 domain assignment. -/
theorem sourceMeaning_p103to107_domain (row : BlueBookP10Audit.Provision)
    (member : row ∈ BlueBookP103to107.p103to107Provisions) :
    ∃ domain, (sourceMeaning row).semanticDomain = .p103to107 domain := by
  cases row <;>
    simp [BlueBookP103to107.p103to107Provisions, sourceMeaning, semanticDomain] at member ⊢

/-- A nonempty dependency payload agrees exactly with the frozen P-10 dependency classifier. -/
theorem sourceMeaning_has_external_authority_iff (row : BlueBookP10Audit.Provision) :
    (sourceMeaning row).externalAuthorities.length > 0 ↔
      row ∈ BlueBookP10Audit.provisionsWithExplicitExternalDependency := by
  cases row <;>
    decide

theorem sourceMeaning_injective : Function.Injective sourceMeaning := by
  intro left right equal
  exact congrArg SourceMeaning.provision equal

def rows : List BlueBookP10Audit.Provision :=
  BlueBookP10Audit.Provision.all

def provisions : List IUPACNormativeProvision :=
  rows.map IUPACNormativeProvision.p10

def batch : GlobalNonDescriptorSourceMeaningBatch provisions :=
  totalMeaningBatch rows IUPACNormativeProvision.p10 sourceMeaning
    (by intro _row; rfl)

@[simp] theorem provisions_exact :
    provisions = sourceProvisions .blueBook2013P10 :=
  rfl

@[simp] theorem provision_count : provisions.length = 71 := by
  simp [provisions, rows]

@[simp] theorem entry_count : batch.entries.length = 71 := by
  rw [batch.entries_length, provision_count]

theorem provisions_nodup : provisions.Nodup := by
  exact BlueBookP10Audit.Provision.all_nodup.map
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
    ¬IUPACNormativeSource.ProvisionAuditComplete .blueBook2013P10 := by
  exact IUPACNormativeSource.provisionAuditIncomplete_of_figure_review_open _ rfl

end GlobalNonDescriptorP10SourceMeaning
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorP10SourceMeaning.provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorP10SourceMeaning.sourceMeaning_p101_domain
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorP10SourceMeaning.sourceMeaning_p102_domain
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorP10SourceMeaning.sourceMeaning_p103to107_domain
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorP10SourceMeaning.sourceMeaning_has_external_authority_iff
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorP10SourceMeaning.sourceMeaning_injective
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorP10SourceMeaning.entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorP10SourceMeaning.every_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorP10SourceMeaning.source_audit_still_open
