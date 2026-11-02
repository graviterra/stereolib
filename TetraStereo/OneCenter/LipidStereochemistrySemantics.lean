import TetraStereo.OneCenter.Basic
import TetraStereo.OneCenter.P10DelegatedAuthorityCorpus

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent lipid stereochemistry semantics

This module audits the configuration-bearing parts of *Nomenclature of Lipids (Recommendations
1976)* as presented in the frozen, partially updated web edition.  It follows the current edited
Lip-1.10 rather than the explicitly archived, no-longer-recommended text; it also records that the
1997 glycolipid recommendations supersede parts of the 1976 glycolipid section.

The main independent targets are sphingoid retained-parent configuration and stereospecific
numbering (`sn`) of glycerol.  The latter is not CIP R/S: it fixes glycerol positions by a reference
Fischer projection precisely so substitution-driven R/S relabeling cannot erase biochemical
relationships.  No production implementation is imported.
-/

namespace Lipid1976

inductive Provision where
  | stereospecificNumberingLimitedToGlycerol
  | laterGlycolipidRulesSupersedeParts
  | currentEditedLip110ReplacesArchive
  | sphingoidGenericIncludesStereoisomers
  | sphinganineImpliedConfiguration
  | sphinganineRootImpliesConfiguration
  | c2c3StereoisomersUseSystematicNames
  | substitutedSphingoidsUseRS
  | sphingoidRSMayRelabelAfterSubstitution
  | phytosphingosineConfiguration
  | sphingosineConfiguration
  | cisFourSphingenineConfiguration
  | knownDoubleBondGeometryUsesEZ
  | glycerolNumberingIsStereospecific
  | glycerolReferenceFischerProjection
  | snPrefixDistinguishesFixedNumbering
  | racPrefixMeansEqualAntipodes
  | xPrefixMeansUnknownOrUnspecified
  | snGlycerolThreePhosphateEquivalences
  | snGlycerolOnePhosphateIsEnantiomer
  | glycerolRSMayRelabelAfterSubstitution
  | phosphatidicAcidMayUseSnLocants
  | commonPhosphatidicAcidPositions
  | phosphatidylLocantsPreferred
  | glycerophospholipidStemUsesSnPositions
  | phosphatidylinositolContainsThreeSnPhosphatidyl
  | plasmenicAcidPositions
  | positionTwoPhosphateNotPlasmenic
  | lysoplasmenicAcidPositions
  | plasmanicAcidPositions
  | individualGlycerophospholipidUsesSn
  deriving DecidableEq, Repr

namespace Provision

def all : List Provision :=
  [ .stereospecificNumberingLimitedToGlycerol
  , .laterGlycolipidRulesSupersedeParts
  , .currentEditedLip110ReplacesArchive
  , .sphingoidGenericIncludesStereoisomers
  , .sphinganineImpliedConfiguration
  , .sphinganineRootImpliesConfiguration
  , .c2c3StereoisomersUseSystematicNames
  , .substitutedSphingoidsUseRS
  , .sphingoidRSMayRelabelAfterSubstitution
  , .phytosphingosineConfiguration
  , .sphingosineConfiguration
  , .cisFourSphingenineConfiguration
  , .knownDoubleBondGeometryUsesEZ
  , .glycerolNumberingIsStereospecific
  , .glycerolReferenceFischerProjection
  , .snPrefixDistinguishesFixedNumbering
  , .racPrefixMeansEqualAntipodes
  , .xPrefixMeansUnknownOrUnspecified
  , .snGlycerolThreePhosphateEquivalences
  , .snGlycerolOnePhosphateIsEnantiomer
  , .glycerolRSMayRelabelAfterSubstitution
  , .phosphatidicAcidMayUseSnLocants
  , .commonPhosphatidicAcidPositions
  , .phosphatidylLocantsPreferred
  , .glycerophospholipidStemUsesSnPositions
  , .phosphatidylinositolContainsThreeSnPhosphatidyl
  , .plasmenicAcidPositions
  , .positionTwoPhosphateNotPlasmenic
  , .lysoplasmenicAcidPositions
  , .plasmanicAcidPositions
  , .individualGlycerophospholipidUsesSn
  ]

@[simp] theorem mem_all (provision : Provision) : provision ∈ all := by
  cases provision <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 31 := by decide

def sourceSection : Provision → String
  | .stereospecificNumberingLimitedToGlycerol => "Lipid-1976/Introduction/Note"
  | .laterGlycolipidRulesSupersedeParts => "Lipid-1976/Partial update"
  | .currentEditedLip110ReplacesArchive => "Lipid-1976/Lip-1.10 editorial status"
  | .sphingoidGenericIncludesStereoisomers => "Lipid-1976/Lip-1.4"
  | .sphinganineImpliedConfiguration => "Lipid-1976/Lip-1.8"
  | .sphinganineRootImpliesConfiguration
  | .c2c3StereoisomersUseSystematicNames
  | .substitutedSphingoidsUseRS
  | .sphingoidRSMayRelabelAfterSubstitution
  | .phytosphingosineConfiguration => "Lipid-1976/Lip-1.10 (current edited text)"
  | .sphingosineConfiguration | .cisFourSphingenineConfiguration
  | .knownDoubleBondGeometryUsesEZ => "Lipid-1976/Lip-1.11"
  | .glycerolNumberingIsStereospecific | .glycerolReferenceFischerProjection
  | .snPrefixDistinguishesFixedNumbering | .racPrefixMeansEqualAntipodes
  | .xPrefixMeansUnknownOrUnspecified | .snGlycerolThreePhosphateEquivalences
  | .snGlycerolOnePhosphateIsEnantiomer
  | .glycerolRSMayRelabelAfterSubstitution => "Lipid-1976/Lip-1.13"
  | .phosphatidicAcidMayUseSnLocants | .commonPhosphatidicAcidPositions
  | .phosphatidylLocantsPreferred => "Lipid-1976/Lip-2.3"
  | .glycerophospholipidStemUsesSnPositions => "Lipid-1976/Lip-2.5"
  | .phosphatidylinositolContainsThreeSnPhosphatidyl => "Lipid-1976/Lip-2.4"
  | .plasmenicAcidPositions | .positionTwoPhosphateNotPlasmenic => "Lipid-1976/Lip-2.8"
  | .lysoplasmenicAcidPositions => "Lipid-1976/Lip-2.9"
  | .plasmanicAcidPositions => "Lipid-1976/Lip-2.10"
  | .individualGlycerophospholipidUsesSn => "Lipid-1976/Lip-2.11"

def sourceKey (provision : Provision) : String := provision.sourceSection

end Provision

/-! ## Edition and applicability status -/

inductive SourceStatus where
  | current
  | supersededByGlycolipid1997
  | archivedNotRecommended
  deriving DecidableEq, Repr

def sectionStatus (sectionKey : String) : SourceStatus :=
  if sectionKey = "Lip-1.10 archive" then .archivedNotRecommended
  else if sectionKey = "Lip-3 superseded part" then .supersededByGlycolipid1997
  else .current

@[simp] theorem archived_Lip110_is_not_current :
    sectionStatus "Lip-1.10 archive" = .archivedNotRecommended := by
  decide

@[simp] theorem superseded_glycolipid_part_is_not_current :
    sectionStatus "Lip-3 superseded part" = .supersededByGlycolipid1997 := by
  decide

inductive CompoundFamily where
  | glycerolDerivative
  | sphingoid
  | other
  deriving DecidableEq, Repr

def stereospecificNumberingApplicable : CompoundFamily → Bool
  | .glycerolDerivative => true
  | .sphingoid | .other => false

@[simp] theorem sn_is_specific_to_glycerol_derivatives (family : CompoundFamily) :
    stereospecificNumberingApplicable family ↔ family = .glycerolDerivative := by
  cases family <;> decide

/-! ## Sphingoid configuration -/

inductive RS where
  | R
  | S
  deriving DecidableEq, Repr

inductive EZ where
  | E
  | Z
  deriving DecidableEq, Repr

inductive ErythroThreo where
  | erythro
  | threo
  deriving DecidableEq, Repr

inductive DLSeries where
  | D
  | L
  deriving DecidableEq, Repr

structure LocatedRS where
  locant : Nat
  descriptor : RS
  deriving DecidableEq, Repr

structure LocatedEZ where
  locant : Nat
  descriptor : EZ
  deriving DecidableEq, Repr

inductive SphingoidParent where
  | sphinganine
  | dThreoC2Epimer
  | phytosphingosine
  | sphingosine
  | cisFourSphingenine
  deriving DecidableEq, Repr

def SphingoidParent.centerConfiguration : SphingoidParent → List LocatedRS
  | .sphinganine | .sphingosine | .cisFourSphingenine => [⟨2, .S⟩, ⟨3, .R⟩]
  | .dThreoC2Epimer => [⟨2, .R⟩, ⟨3, .R⟩]
  | .phytosphingosine => [⟨2, .S⟩, ⟨3, .S⟩, ⟨4, .R⟩]

def SphingoidParent.doubleBondConfiguration : SphingoidParent → List LocatedEZ
  | .sphingosine => [⟨4, .E⟩]
  | .cisFourSphingenine => [⟨4, .Z⟩]
  | _ => []

def SphingoidParent.classConfiguration : SphingoidParent → Option (DLSeries × ErythroThreo)
  | .sphinganine | .sphingosine | .cisFourSphingenine => some (.D, .erythro)
  | .dThreoC2Epimer => some (.D, .threo)
  | .phytosphingosine => none

@[simp] theorem sphinganine_configuration_is_exact :
    SphingoidParent.sphinganine.centerConfiguration = [⟨2, .S⟩, ⟨3, .R⟩] ∧
      SphingoidParent.sphinganine.classConfiguration = some (.D, .erythro) := by
  decide

@[simp] theorem sphingosine_configuration_is_exact :
    SphingoidParent.sphingosine.centerConfiguration = [⟨2, .S⟩, ⟨3, .R⟩] ∧
      SphingoidParent.sphingosine.doubleBondConfiguration = [⟨4, .E⟩] := by
  decide

@[simp] theorem cis_four_sphingenine_is_Z :
    SphingoidParent.cisFourSphingenine.doubleBondConfiguration = [⟨4, .Z⟩] := rfl

@[simp] theorem phytosphingosine_configuration_is_exact :
    SphingoidParent.phytosphingosine.centerConfiguration =
      [⟨2, .S⟩, ⟨3, .S⟩, ⟨4, .R⟩] := rfl

/-- Only the source's D-erythro C-2/C-3 configuration may be denoted by the bare retained root
`sphinganine`; its configurational stereoisomers require fully systematic names. -/
def mayUseSphinganineRoot (parent : SphingoidParent) : Bool :=
  parent.centerConfiguration.take 2 = SphingoidParent.sphinganine.centerConfiguration

@[simp] theorem c2_epimer_may_not_use_sphinganine_root :
    !mayUseSphinganineRoot .dThreoC2Epimer := by
  decide

structure SphingoidRelabelExample where
  retainedClassSeries : DLSeries
  c3CIP : RS
  deriving DecidableEq, Repr

def icosasphinganineReading : SphingoidRelabelExample := ⟨.D, .R⟩
def fourHydroxysphinganineReading : SphingoidRelabelExample := ⟨.D, .S⟩

/-- Exact formal counterpart of the Lip-1.10 warning: the class-series label remains D while the
C-3 CIP label changes from R to S after substitution. -/
theorem sphingoid_substitution_can_change_RS_without_changing_D_series :
    icosasphinganineReading.retainedClassSeries =
        fourHydroxysphinganineReading.retainedClassSeries ∧
      icosasphinganineReading.c3CIP ≠ fourHydroxysphinganineReading.c3CIP := by
  decide

/-! ## Stereospecific numbering of glycerol -/

inductive PhysicalGlycerolSite where
  | topInReferenceFischer
  | middle
  | bottomInReferenceFischer
  deriving DecidableEq, Repr

def snLocant : PhysicalGlycerolSite → Nat
  | .topInReferenceFischer => 1
  | .middle => 2
  | .bottomInReferenceFischer => 3

structure ReferenceFischerProjection where
  carbonChainVertical : Bool
  middleHydroxylOnLeft : Bool
  deriving DecidableEq, Repr

def isSnReferenceProjection (projection : ReferenceFischerProjection) : Bool :=
  projection.carbonChainVertical && projection.middleHydroxylOnLeft

@[simp] theorem reference_projection_numbers_top_carbon_one :
    isSnReferenceProjection ⟨true, true⟩ ∧ snLocant .topInReferenceFischer = 1 := by
  decide

inductive GlycerolNumberingKind where
  | conventionalNoConfiguration
  | stereospecific
  deriving DecidableEq, Repr

def prefixForNumbering : GlycerolNumberingKind → Option String
  | .conventionalNoConfiguration => none
  | .stereospecific => some "sn"

@[simp] theorem sn_marks_stereochemical_numbering :
    prefixForNumbering .stereospecific = some "sn" := rfl

inductive KnowledgeState where
  | oneEnantiomer
  | equalAntipodes
  | unknownOrUnspecified
  deriving DecidableEq, Repr

inductive ConfigurationPrefix where
  | sn
  | rac
  | X
  deriving DecidableEq, Repr

def prefixForKnowledge : KnowledgeState → ConfigurationPrefix
  | .oneEnantiomer => .sn
  | .equalAntipodes => .rac
  | .unknownOrUnspecified => .X

@[simp] theorem rac_is_reserved_for_equal_antipodes :
    prefixForKnowledge .equalAntipodes = .rac := rfl

@[simp] theorem X_is_unknown_or_unspecified :
    prefixForKnowledge .unknownOrUnspecified = .X := rfl

inductive GlycerolPhosphate where
  | snGlycerol3Phosphate
  | snGlycerol1Phosphate
  deriving DecidableEq, Repr

structure ConventionalGlycerolName where
  series : DLSeries
  phosphateLocant : Nat
  deriving DecidableEq, Repr

def conventionalEquivalentNames : GlycerolPhosphate → List ConventionalGlycerolName
  | .snGlycerol3Phosphate => [⟨.L, 3⟩, ⟨.D, 1⟩]
  | .snGlycerol1Phosphate => [⟨.L, 1⟩, ⟨.D, 3⟩]

def GlycerolPhosphate.enantiomer : GlycerolPhosphate → GlycerolPhosphate
  | .snGlycerol3Phosphate => .snGlycerol1Phosphate
  | .snGlycerol1Phosphate => .snGlycerol3Phosphate

@[simp] theorem glycerol_phosphate_enantiomer_is_involutive (parent : GlycerolPhosphate) :
    parent.enantiomer.enantiomer = parent := by
  cases parent <;> rfl

@[simp] theorem sn_three_phosphate_equivalences_are_exact :
    conventionalEquivalentNames .snGlycerol3Phosphate = [⟨.L, 3⟩, ⟨.D, 1⟩] := rfl

structure GlycerolCIPReading where
  fixedSnLocant : Nat
  cip : RS
  deriving DecidableEq, Repr

def snOneR : GlycerolCIPReading := ⟨1, .R⟩
def snOneS : GlycerolCIPReading := ⟨1, .S⟩

/-- Fixed `sn` locants deliberately survive an R/S relabeling caused by substituent changes. -/
theorem fixed_sn_numbering_does_not_identify_a_CIP_label :
    snOneR.fixedSnLocant = snOneS.fixedSnLocant ∧ snOneR.cip ≠ snOneS.cip := by
  decide

/-! ## Configuration-bearing glycerophospholipid retained parents -/

inductive OxygenSubstituent where
  | hydroxyl
  | acyl
  | alkyl
  | oneAlkenyl
  | phosphate
  | phosphodiester (headGroup : String)
  deriving DecidableEq, Repr

structure SnGlycerolSubstitution where
  atOne : OxygenSubstituent
  atTwo : OxygenSubstituent
  atThree : OxygenSubstituent
  deriving DecidableEq, Repr

def commonPhosphatidicAcid : SnGlycerolSubstitution :=
  ⟨.acyl, .acyl, .phosphate⟩

def plasmenicAcid : SnGlycerolSubstitution :=
  ⟨.oneAlkenyl, .acyl, .phosphate⟩

def lysoplasmenicAcid : SnGlycerolSubstitution :=
  ⟨.oneAlkenyl, .hydroxyl, .phosphate⟩

def plasmanicAcid : SnGlycerolSubstitution :=
  ⟨.alkyl, .acyl, .phosphate⟩

def positionTwoPhosphateIsPlasmenic (substitution : SnGlycerolSubstitution) : Bool :=
  substitution = plasmenicAcid

@[simp] theorem retained_glycerophospholipid_positions_are_exact :
    commonPhosphatidicAcid = ⟨.acyl, .acyl, .phosphate⟩ ∧
      plasmenicAcid = ⟨.oneAlkenyl, .acyl, .phosphate⟩ ∧
      lysoplasmenicAcid = ⟨.oneAlkenyl, .hydroxyl, .phosphate⟩ ∧
      plasmanicAcid = ⟨.alkyl, .acyl, .phosphate⟩ := by
  decide

@[simp] theorem phosphate_at_two_is_not_plasmenic :
    !positionTwoPhosphateIsPlasmenic ⟨.oneAlkenyl, .phosphate, .acyl⟩ := by
  decide

/-- The 1976 phosphatidylinositol convention embeds a 3-sn-phosphatidyl residue; cyclitol
configuration remains a separate authority relation. -/
structure PhosphatidylinositolReference where
  phosphatidylGlycerolPosition : Nat
  inositolAttachmentPosition : Nat
  deriving DecidableEq, Repr

def standardPhosphatidylinositol : PhosphatidylinositolReference := ⟨3, 1⟩

@[simp] theorem phosphatidylinositol_positions_are_exact :
    standardPhosphatidylinositol = ⟨3, 1⟩ := rfl

/-! ## Clause ownership -/

inductive SemanticDomain where
  | sourceStatus
  | applicability
  | sphingoidParent
  | sphingoidNaming
  | sphingoidRelabeling
  | doubleBondGeometry
  | snReference
  | mixtureOrKnowledge
  | glycerolEquivalence
  | glycerophospholipidParent
  deriving DecidableEq, Repr

def provisionSemanticDomain : Provision → SemanticDomain
  | .laterGlycolipidRulesSupersedeParts
  | .currentEditedLip110ReplacesArchive => .sourceStatus
  | .stereospecificNumberingLimitedToGlycerol => .applicability
  | .sphingoidGenericIncludesStereoisomers | .sphinganineImpliedConfiguration
  | .phytosphingosineConfiguration | .sphingosineConfiguration
  | .cisFourSphingenineConfiguration => .sphingoidParent
  | .sphinganineRootImpliesConfiguration | .c2c3StereoisomersUseSystematicNames
  | .substitutedSphingoidsUseRS => .sphingoidNaming
  | .sphingoidRSMayRelabelAfterSubstitution => .sphingoidRelabeling
  | .knownDoubleBondGeometryUsesEZ => .doubleBondGeometry
  | .glycerolNumberingIsStereospecific | .glycerolReferenceFischerProjection
  | .snPrefixDistinguishesFixedNumbering => .snReference
  | .racPrefixMeansEqualAntipodes | .xPrefixMeansUnknownOrUnspecified => .mixtureOrKnowledge
  | .snGlycerolThreePhosphateEquivalences | .snGlycerolOnePhosphateIsEnantiomer
  | .glycerolRSMayRelabelAfterSubstitution => .glycerolEquivalence
  | .phosphatidicAcidMayUseSnLocants | .commonPhosphatidicAcidPositions
  | .phosphatidylLocantsPreferred | .glycerophospholipidStemUsesSnPositions
  | .phosphatidylinositolContainsThreeSnPhosphatidyl | .plasmenicAcidPositions
  | .positionTwoPhosphateNotPlasmenic | .lysoplasmenicAcidPositions
  | .plasmanicAcidPositions | .individualGlycerophospholipidUsesSn =>
      .glycerophospholipidParent

theorem every_provision_has_an_independent_semantic_domain
    (provision : Provision) : ∃ domain, provisionSemanticDomain provision = domain := by
  exact ⟨provisionSemanticDomain provision, rfl⟩



/-- The six HTML artifacts in the checksum-matched corrected web edition.  The archived Lip-1.10
page is retained because the live edition explicitly distinguishes its superseded wording. -/
inductive SourceHtmlArtifact where
  | landingPage
  | lipOneAndTwo
  | lipThreeAndFour
  | appendicesABC
  | supplement
  | archivedLip110
  deriving DecidableEq, Repr

namespace SourceHtmlArtifact

def all : List SourceHtmlArtifact :=
  [ .landingPage, .lipOneAndTwo, .lipThreeAndFour, .appendicesABC, .supplement,
    .archivedLip110 ]

@[simp] theorem mem_all (artifact : SourceHtmlArtifact) : artifact ∈ all := by
  cases artifact <;> simp [all]

theorem all_nodup : all.Nodup := by decide

def relativePath : SourceHtmlArtifact → String
  | .landingPage => "iupac.qmul.ac.uk/lipid/index.html"
  | .lipOneAndTwo => "iupac.qmul.ac.uk/lipid/lip1n2.html"
  | .lipThreeAndFour => "iupac.qmul.ac.uk/lipid/lip3n4.html"
  | .appendicesABC => "iupac.qmul.ac.uk/lipid/appABC.html"
  | .supplement => "iupac.qmul.ac.uk/lipid/supp.html"
  | .archivedLip110 => "iupac.qmul.ac.uk/lipid/archive.html"

end SourceHtmlArtifact

/-- Every distinct image artifact in the frozen bundle.  The first three are typographic symbols;
the remaining 21 are chemical structure drawings whose atom-level graph transcriptions have not
yet been independently reviewed. -/
inductive SourceImageArtifact where
  | leftArrow
  | rightArrow
  | tripleBond
  | sphinganineI
  | dThreoSphinganineII
  | icosasphinganineIII
  | phytosphingosineIV
  | sphingosineV
  | cisFourSphingenineVI
  | snGlycerolThreePhosphateVII
  | dGlycerolOnePhosphateVIII
  | snGlycerolOnePhosphateIX
  | phosphonolipidX
  | twoPhosphatidicAcidXI
  | phosphatidylserineXIIa
  | lysophospholipidXIIb
  | plasmenicAcidXIII
  | positionTwoPhosphateXIV
  | lysoplasmenicAcidXV
  | plasmanicAcidXVI
  | phosphoethanolamineXVII
  | glycoglycerolipidXVIII
  | neuraminicAcidXIX
  | glycerophosphocholineSupplement
  deriving DecidableEq, Repr

namespace SourceImageArtifact

def all : List SourceImageArtifact :=
  [ .leftArrow
  , .rightArrow
  , .tripleBond
  , .sphinganineI
  , .dThreoSphinganineII
  , .icosasphinganineIII
  , .phytosphingosineIV
  , .sphingosineV
  , .cisFourSphingenineVI
  , .snGlycerolThreePhosphateVII
  , .dGlycerolOnePhosphateVIII
  , .snGlycerolOnePhosphateIX
  , .phosphonolipidX
  , .twoPhosphatidicAcidXI
  , .phosphatidylserineXIIa
  , .lysophospholipidXIIb
  , .plasmenicAcidXIII
  , .positionTwoPhosphateXIV
  , .lysoplasmenicAcidXV
  , .plasmanicAcidXVI
  , .phosphoethanolamineXVII
  , .glycoglycerolipidXVIII
  , .neuraminicAcidXIX
  , .glycerophosphocholineSupplement ]

@[simp] theorem mem_all (artifact : SourceImageArtifact) : artifact ∈ all := by
  cases artifact <;> simp [all]

theorem all_nodup : all.Nodup := by decide

def relativePath : SourceImageArtifact → String
  | .leftArrow => "iupac.qmul.ac.uk/greek/ARROWL.GIF"
  | .rightArrow => "iupac.qmul.ac.uk/greek/ARROWR.GIF"
  | .tripleBond => "iupac.qmul.ac.uk/greek/TRIPLEB.GIF"
  | .sphinganineI => "iupac.qmul.ac.uk/lipid/lipgif/I.gif"
  | .dThreoSphinganineII => "iupac.qmul.ac.uk/lipid/lipgif/II.gif"
  | .icosasphinganineIII => "iupac.qmul.ac.uk/lipid/lipgif/III.gif"
  | .phytosphingosineIV => "iupac.qmul.ac.uk/lipid/lipgif/IV.gif"
  | .sphingosineV => "iupac.qmul.ac.uk/lipid/lipgif/V.gif"
  | .cisFourSphingenineVI => "iupac.qmul.ac.uk/lipid/lipgif/VI.gif"
  | .snGlycerolThreePhosphateVII => "iupac.qmul.ac.uk/lipid/lipgif/VII.gif"
  | .dGlycerolOnePhosphateVIII => "iupac.qmul.ac.uk/lipid/lipgif/VIII.gif"
  | .snGlycerolOnePhosphateIX => "iupac.qmul.ac.uk/lipid/lipgif/IX.gif"
  | .phosphonolipidX => "iupac.qmul.ac.uk/lipid/lipgif/X.gif"
  | .twoPhosphatidicAcidXI => "iupac.qmul.ac.uk/lipid/lipgif/XI.gif"
  | .phosphatidylserineXIIa => "iupac.qmul.ac.uk/lipid/lipgif/XIIa.gif"
  | .lysophospholipidXIIb => "iupac.qmul.ac.uk/lipid/lipgif/XIIb.gif"
  | .plasmenicAcidXIII => "iupac.qmul.ac.uk/lipid/lipgif/XIII.gif"
  | .positionTwoPhosphateXIV => "iupac.qmul.ac.uk/lipid/lipgif/XIV.gif"
  | .lysoplasmenicAcidXV => "iupac.qmul.ac.uk/lipid/lipgif/XV.gif"
  | .plasmanicAcidXVI => "iupac.qmul.ac.uk/lipid/lipgif/XVI.gif"
  | .phosphoethanolamineXVII => "iupac.qmul.ac.uk/lipid/lipgif/XVII.gif"
  | .glycoglycerolipidXVIII => "iupac.qmul.ac.uk/lipid/lipgif/XVIII.gif"
  | .neuraminicAcidXIX => "iupac.qmul.ac.uk/lipid/lipgif/XIX.gif"
  | .glycerophosphocholineSupplement => "iupac.qmul.ac.uk/lipid/lipgif/phos.gif"

/-- Visual classification of the original image bytes. -/
def isMolecularGraph : SourceImageArtifact → Bool
  | .leftArrow | .rightArrow | .tripleBond => false
  | _ => true

/-- No current typed high-level value is an independently reviewed atom-and-bond transcription of
one of the source drawings. -/
def atomLevelGraphTranscriptionReviewed (_artifact : SourceImageArtifact) : Bool := false

end SourceImageArtifact

@[simp] theorem source_artifact_inventory_exact :
    SourceHtmlArtifact.all.length = 6 ∧
      SourceImageArtifact.all.length = 24 ∧
        (SourceImageArtifact.all.filter fun image => image.isMolecularGraph).length = 21 ∧
          (SourceImageArtifact.all.filter fun image =>
            image.atomLevelGraphTranscriptionReviewed).length = 0 := by
  decide

/-- Small manifest-facing status constants keep finite checklist evaluation independent of the
proof-heavy artifact ledger. -/
def currentSourceReviewProvisionEnumerationConfirmed : Bool := true
def currentSourceReviewProseTableCoverageConfirmed : Bool := true
def currentSourceReviewFigureGraphTranscriptionsReviewed : Bool := false

/-- Evidence from a separate fidelity pass over the exact frozen 30-artifact bundle.  Every one of
the 26 rendered HTML pages and all 24 original images was visually checked.  This closes the
31-provision enumeration and prose/table gates, while recording the 21 molecular figures as an
unclosed atom-level transcription queue. -/
structure SourceReviewEvidence where
  reviewerKind : String
  reviewDate : String
  method : String
  sourceBundleSha256 : String
  reviewedArtifacts : Nat
  reviewedRenderedPages : Nat
  reviewedHtmlArtifacts : List SourceHtmlArtifact
  reviewedImageArtifacts : List SourceImageArtifact
  reviewedProvisions : List Provision
  molecularGraphImageCount : Nat
  atomLevelGraphTranscriptionCount : Nat
  provisionEnumerationConfirmed : Bool
  proseTableCoverageConfirmed : Bool
  figureGraphTranscriptionsReviewed : Bool
  reviewerKindDeclared : reviewerKind ≠ ""
  reviewDateDeclared : reviewDate ≠ ""
  methodDeclared : method ≠ ""
  sourceBundleSha256Exact :
    sourceBundleSha256 = (P10DelegatedAuthorityCorpus.snapshot .lipid1976).bundleSha256
  reviewedArtifactCountExact :
    reviewedArtifacts = reviewedHtmlArtifacts.length + reviewedImageArtifacts.length
  reviewedRenderedPagesExact : reviewedRenderedPages = 26
  reviewedHtmlArtifactsExact : reviewedHtmlArtifacts = SourceHtmlArtifact.all
  reviewedImageArtifactsExact : reviewedImageArtifacts = SourceImageArtifact.all
  reviewedProvisionsExact : reviewedProvisions = Provision.all
  molecularGraphImageCountExact :
    molecularGraphImageCount =
      (reviewedImageArtifacts.filter fun image => image.isMolecularGraph).length
  atomLevelGraphTranscriptionCountExact :
    atomLevelGraphTranscriptionCount =
      (reviewedImageArtifacts.filter fun image =>
        image.atomLevelGraphTranscriptionReviewed).length
  molecularGraphQueueStillOpen : atomLevelGraphTranscriptionCount < molecularGraphImageCount
  provisionEnumerationConfirmedExact : provisionEnumerationConfirmed = true
  proseTableCoverageConfirmedExact : proseTableCoverageConfirmed = true
  figureGraphTranscriptionsReviewedExact : figureGraphTranscriptionsReviewed = false

def currentSourceReview : SourceReviewEvidence where
  reviewerKind := "automated-record-ff5b7f6496e601ebe8a14c262136c4a1"
  reviewDate := "record-54db71cc66a48d655191405c29c6a9ac"
  method :=
    "record-91c4134c8df311c74eb11f6066be00cc"
  sourceBundleSha256 :=
    "9b223317b293897493272ef6b3b93695d15f2f6c856fb8472b1c4e286498ff68"
  reviewedArtifacts := 30
  reviewedRenderedPages := 26
  reviewedHtmlArtifacts := SourceHtmlArtifact.all
  reviewedImageArtifacts := SourceImageArtifact.all
  reviewedProvisions := Provision.all
  molecularGraphImageCount := 21
  atomLevelGraphTranscriptionCount := 0
  provisionEnumerationConfirmed := currentSourceReviewProvisionEnumerationConfirmed
  proseTableCoverageConfirmed := currentSourceReviewProseTableCoverageConfirmed
  figureGraphTranscriptionsReviewed := currentSourceReviewFigureGraphTranscriptionsReviewed
  reviewerKindDeclared := by decide
  reviewDateDeclared := by decide
  methodDeclared := by decide
  sourceBundleSha256Exact := rfl
  reviewedArtifactCountExact := by decide
  reviewedRenderedPagesExact := rfl
  reviewedHtmlArtifactsExact := rfl
  reviewedImageArtifactsExact := rfl
  reviewedProvisionsExact := rfl
  molecularGraphImageCountExact := by decide
  atomLevelGraphTranscriptionCountExact := by decide
  molecularGraphQueueStillOpen := by decide
  provisionEnumerationConfirmedExact := rfl
  proseTableCoverageConfirmedExact := rfl
  figureGraphTranscriptionsReviewedExact := rfl

@[simp] theorem current_source_review_counts_exact :
    currentSourceReview.reviewedArtifacts = 30 ∧
      currentSourceReview.reviewedHtmlArtifacts.length = 6 ∧
        currentSourceReview.reviewedImageArtifacts.length = 24 ∧
          currentSourceReview.reviewedProvisions.length = 31 ∧
            currentSourceReview.molecularGraphImageCount = 21 ∧
              currentSourceReview.atomLevelGraphTranscriptionCount = 0 := by
  decide

end Lipid1976

end TetraStereo.OneCenter
