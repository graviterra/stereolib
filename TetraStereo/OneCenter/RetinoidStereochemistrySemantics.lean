import TetraStereo.OneCenter.Basic
import TetraStereo.OneCenter.P10DelegatedAuthorityCorpus

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent retinoid stereochemistry semantics

This module audits and transcribes the configuration-bearing rules of *Nomenclature of Retinoids
(Recommendations 1981)*.  It is independent of the production descriptor pipeline.  The source is
the corrected IUPAC web edition frozen by `P10DelegatedAuthorityCorpus`.

The document's Appendix is explicitly a convenience list and says that it does not officially
recognize the listed trivial names.  Its corrected Blumenol A entry is recorded below as source
data but is therefore not counted as a normative rule.
-/

namespace Retinoid1981

inductive Provision where
  | stereoparentNameImpliesConfiguration
  | retinolStereoparent
  | retinalStereoparent
  | retinoicAcidStereoparent
  | stereochemicalLocantsUseRetinoidNumbering
  | chiralCentersUseRS
  | rsLocantsPrecedeRetinoidName
  | polyeneDefaultsToAllTrans
  | cisCitationsFollowAbsoluteConfiguration
  | ezAllowedAndRequiredWhenAmbiguous
  | substitutionMayChangeEZWithoutGeometryChange
  | ezNotationCitesEveryDoubleBond
  | retroSixSevenConfigurationExplicitWhenNeeded
  deriving DecidableEq, Repr

namespace Provision

def all : List Provision :=
  [ .stereoparentNameImpliesConfiguration
  , .retinolStereoparent
  , .retinalStereoparent
  , .retinoicAcidStereoparent
  , .stereochemicalLocantsUseRetinoidNumbering
  , .chiralCentersUseRS
  , .rsLocantsPrecedeRetinoidName
  , .polyeneDefaultsToAllTrans
  , .cisCitationsFollowAbsoluteConfiguration
  , .ezAllowedAndRequiredWhenAmbiguous
  , .substitutionMayChangeEZWithoutGeometryChange
  , .ezNotationCitesEveryDoubleBond
  , .retroSixSevenConfigurationExplicitWhenNeeded
  ]

@[simp] theorem mem_all (provision : Provision) : provision ∈ all := by
  cases provision <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 13 := by decide

def sourceSection : Provision → String
  | .stereoparentNameImpliesConfiguration => "Ret-2"
  | .retinolStereoparent => "Ret-2.1/Figure 1"
  | .retinalStereoparent => "Ret-2.2/Figure 2"
  | .retinoicAcidStereoparent => "Ret-2.3/Figure 3"
  | .stereochemicalLocantsUseRetinoidNumbering => "Ret-3"
  | .chiralCentersUseRS => "Ret-5.1"
  | .rsLocantsPrecedeRetinoidName => "Ret-5.1"
  | .polyeneDefaultsToAllTrans => "Ret-5.2"
  | .cisCitationsFollowAbsoluteConfiguration => "Ret-5.2"
  | .ezAllowedAndRequiredWhenAmbiguous => "Ret-5.2"
  | .substitutionMayChangeEZWithoutGeometryChange => "Ret-5.2"
  | .ezNotationCitesEveryDoubleBond => "Ret-5.2"
  | .retroSixSevenConfigurationExplicitWhenNeeded => "Ret-5.2"

def sourceKey (provision : Provision) : String :=
  "RETINOID-1981/" ++ provision.sourceSection

end Provision










namespace SourceAudit

inductive NormativeSection where
  | ret1
  | ret1_1
  | ret2
  | ret2_1
  | ret2_2
  | ret2_3
  | ret3
  | ret4_1
  | ret4_2_1
  | ret4_2_2
  | ret4_2_3
  | ret4_3
  | ret4_4
  | ret4_5
  | ret4_6
  | ret4_7
  | ret4_8
  | ret5_1
  | ret5_2
  deriving DecidableEq, Repr

namespace NormativeSection

def all : List NormativeSection :=
  [ .ret1
  , .ret1_1
  , .ret2
  , .ret2_1
  , .ret2_2
  , .ret2_3
  , .ret3
  , .ret4_1
  , .ret4_2_1
  , .ret4_2_2
  , .ret4_2_3
  , .ret4_3
  , .ret4_4
  , .ret4_5
  , .ret4_6
  , .ret4_7
  , .ret4_8
  , .ret5_1
  , .ret5_2 ]

@[simp] theorem mem_all (sourceSection : NormativeSection) : sourceSection ∈ all := by
  cases sourceSection <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 19 := by decide

/-- Stable HTML anchor in the corrected IUPAC/QMUL web edition. -/
def htmlAnchor : NormativeSection → String
  | .ret1 => "p1"
  | .ret1_1 => "p11"
  | .ret2 => "p2"
  | .ret2_1 => "p21"
  | .ret2_2 => "p22"
  | .ret2_3 => "p23"
  | .ret3 => "p3"
  | .ret4_1 => "p41"
  | .ret4_2_1 => "p421"
  | .ret4_2_2 => "p422"
  | .ret4_2_3 => "p423"
  | .ret4_3 => "p43"
  | .ret4_4 => "p44"
  | .ret4_5 => "p45"
  | .ret4_6 => "p46"
  | .ret4_7 => "p47"
  | .ret4_8 => "p48"
  | .ret5_1 => "p51"
  | .ret5_2 => "p52"

theorem htmlAnchors_nodup : (all.map htmlAnchor).Nodup := by decide

end NormativeSection

end SourceAudit

/-- Clause-level source link for each of the thirteen modeled stereochemical obligations. -/
def Provision.normativeSection : Provision → SourceAudit.NormativeSection
  | .stereoparentNameImpliesConfiguration => .ret2
  | .retinolStereoparent => .ret2_1
  | .retinalStereoparent => .ret2_2
  | .retinoicAcidStereoparent => .ret2_3
  | .stereochemicalLocantsUseRetinoidNumbering => .ret3
  | .chiralCentersUseRS => .ret5_1
  | .rsLocantsPrecedeRetinoidName => .ret5_1
  | .polyeneDefaultsToAllTrans => .ret5_2
  | .cisCitationsFollowAbsoluteConfiguration => .ret5_2
  | .ezAllowedAndRequiredWhenAmbiguous => .ret5_2
  | .substitutionMayChangeEZWithoutGeometryChange => .ret5_2
  | .ezNotationCitesEveryDoubleBond => .ret5_2
  | .retroSixSevenConfigurationExplicitWhenNeeded => .ret5_2

namespace SourceAudit

/-- The exact seven recommendation clauses that own the thirteen modeled stereochemical rows. -/
def stereochemistryBearingSections : List NormativeSection :=
  [ .ret2, .ret2_1, .ret2_2, .ret2_3, .ret3, .ret5_1, .ret5_2 ]

theorem stereochemistryBearingSections_nodup : stereochemistryBearingSections.Nodup := by
  decide

theorem stereochemistryBearingSections_subset_normative
    {sourceSection : NormativeSection}
    (_member : sourceSection ∈ stereochemistryBearingSections) :
    sourceSection ∈ NormativeSection.all :=
  sourceSection.mem_all

/-- Deduplication is intentional: Ret-5.1 and Ret-5.2 each own several distinct obligations. -/
theorem provision_sections_exact :
    (Provision.all.map Provision.normativeSection).eraseDups =
      stereochemistryBearingSections := by
  decide

theorem every_stereochemistry_section_has_provision
    (sourceSection : NormativeSection)
    (member : sourceSection ∈ stereochemistryBearingSections) :
    ∃ provision ∈ Provision.all, provision.normativeSection = sourceSection := by
  cases sourceSection with
  | ret2 =>
      exact ⟨.stereoparentNameImpliesConfiguration, by simp [Provision.all], rfl⟩
  | ret2_1 => exact ⟨.retinolStereoparent, by simp [Provision.all], rfl⟩
  | ret2_2 => exact ⟨.retinalStereoparent, by simp [Provision.all], rfl⟩
  | ret2_3 => exact ⟨.retinoicAcidStereoparent, by simp [Provision.all], rfl⟩
  | ret3 => exact ⟨.stereochemicalLocantsUseRetinoidNumbering, by simp [Provision.all], rfl⟩
  | ret5_1 => exact ⟨.chiralCentersUseRS, by simp [Provision.all], rfl⟩
  | ret5_2 => exact ⟨.polyeneDefaultsToAllTrans, by simp [Provision.all], rfl⟩
  | ret1 | ret1_1 | ret4_1 | ret4_2_1 | ret4_2_2 | ret4_2_3 | ret4_3 | ret4_4
  | ret4_5 | ret4_6 | ret4_7 | ret4_8 =>
      simp [stereochemistryBearingSections] at member





inductive ImageArtifact where
  | correctionMarker
  | stereoparentSkeleton
  | glucuronideSubstituent
  | didehydroretinol
  | alphaVitaminA
  | epoxyDihydroretinol
  | fluororetinoate
  | secoRetinol
  | motretinideEtretinate
  | acetylDinorRetinoicAcid
  | anhydroVitaminA
  | retroRetinylAcetate
  | hydroxyAcetoxyRetinol
  | cisRetinoidExamples
  | retroRetinalOxime
  deriving DecidableEq, Repr

namespace ImageArtifact

def all : List ImageArtifact :=
  [ .correctionMarker
  , .stereoparentSkeleton
  , .glucuronideSubstituent
  , .didehydroretinol
  , .alphaVitaminA
  , .epoxyDihydroretinol
  , .fluororetinoate
  , .secoRetinol
  , .motretinideEtretinate
  , .acetylDinorRetinoicAcid
  , .anhydroVitaminA
  , .retroRetinylAcetate
  , .hydroxyAcetoxyRetinol
  , .cisRetinoidExamples
  , .retroRetinalOxime ]

@[simp] theorem mem_all (artifact : ImageArtifact) : artifact ∈ all := by
  cases artifact <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 15 := by decide

def relativePath : ImageArtifact → String
  | .correctionMarker => "../greek/ALTER.GIF"
  | .stereoparentSkeleton => "miscgif/A2a.gif"
  | .glucuronideSubstituent => "miscgif/A2b.gif"
  | .didehydroretinol => "miscgif/A43a.gif"
  | .alphaVitaminA => "miscgif/A43b.gif"
  | .epoxyDihydroretinol => "miscgif/A44a.gif"
  | .fluororetinoate => "miscgif/A44b.gif"
  | .secoRetinol => "miscgif/A45.gif"
  | .motretinideEtretinate => "miscgif/A46a.gif"
  | .acetylDinorRetinoicAcid => "miscgif/A46b.gif"
  | .anhydroVitaminA => "miscgif/A47a.gif"
  | .retroRetinylAcetate => "miscgif/A47b.gif"
  | .hydroxyAcetoxyRetinol => "miscgif/A51.gif"
  | .cisRetinoidExamples => "miscgif/A52a.gif"
  | .retroRetinalOxime => "miscgif/A52b.gif"

theorem relativePaths_nodup : (all.map relativePath).Nodup := by decide

def isChemical : ImageArtifact → Bool
  | .correctionMarker => false
  | _ => true

def chemicalFigures : List ImageArtifact :=
  all.filter isChemical

def nonchemicalArtifacts : List ImageArtifact :=
  all.filter fun artifact => !artifact.isChemical

@[simp] theorem chemicalFigure_count : chemicalFigures.length = 14 := by decide

@[simp] theorem nonchemicalArtifacts_exact : nonchemicalArtifacts = [.correctionMarker] := by
  decide

/-- No figure is promoted merely from its source path; every chemical drawing remains queued for
reviewed atom/bond graph transcription. -/
def pendingGraphTranscriptions : List ImageArtifact :=
  chemicalFigures

@[simp] theorem pendingGraphTranscription_count : pendingGraphTranscriptions.length = 14 := by
  exact chemicalFigure_count

end ImageArtifact

end SourceAudit

/-! ## Retained stereoparent denotation -/

inductive Parent where
  | retinol
  | retinal
  | retinoicAcid
  deriving DecidableEq, Repr

namespace Parent

def retainedName : Parent → String
  | .retinol => "retinol"
  | .retinal => "retinal"
  | .retinoicAcid => "retinoic acid"

/-- Retinoid locants of the four acyclic polyene-chain double bonds.  The 5(6) bond is in the
ring and is not part of the all-trans polyene-chain assertion in Ret-5.2. -/
def polyeneBondLocants (_parent : Parent) : List Nat := [7, 9, 11, 13]

@[simp] theorem polyeneBondLocants_length (parent : Parent) :
    parent.polyeneBondLocants.length = 4 := by
  cases parent <;> rfl

end Parent

inductive ParentGeometry where
  | cis
  | trans
  deriving DecidableEq, Repr

/-- The denotation supplied by Ret-2 and Ret-5.2 for a retained parent name. -/
def impliedPolyeneGeometry (parent : Parent) (locant : Nat) : Option ParentGeometry :=
  if locant ∈ parent.polyeneBondLocants then some .trans else none

theorem retained_parent_implies_trans_at_every_polyene_bond
    (parent : Parent) (locant : Nat) (member : locant ∈ parent.polyeneBondLocants) :
    impliedPolyeneGeometry parent locant = some .trans := by
  simp [impliedPolyeneGeometry, member]

theorem all_three_retained_parents_have_same_polyene_configuration
    (first second : Parent) (locant : Nat)
    (firstMember : locant ∈ first.polyeneBondLocants)
    (secondMember : locant ∈ second.polyeneBondLocants) :
    impliedPolyeneGeometry first locant = impliedPolyeneGeometry second locant := by
  simp [impliedPolyeneGeometry, firstMember, secondMember]

/-! ## Chiral-centre descriptors and name-component order -/

inductive RS where
  | R
  | S
  deriving DecidableEq, Repr

structure CenterDescriptor where
  locant : Nat
  descriptor : RS
  deriving DecidableEq, Repr

inductive EZ where
  | E
  | Z
  deriving DecidableEq, Repr

inductive DoubleBondDescriptor where
  | cis
  | trans
  | ez (descriptor : EZ)
  deriving DecidableEq, Repr

namespace DoubleBondDescriptor

def isEZ : DoubleBondDescriptor → Bool
  | .ez _ => true
  | .cis | .trans => false

end DoubleBondDescriptor

structure BondCitation where
  locant : Nat
  descriptor : DoubleBondDescriptor
  deriving DecidableEq, Repr

/-- Ret-5.1 and Ret-5.2 impose this component order: absolute centre configuration, then explicit
cis double-bond departures, then the retinoid name. -/
inductive StereochemicalNameComponent where
  | absoluteCenters (descriptors : List CenterDescriptor)
  | cisDoubleBonds (citations : List BondCitation)
  | retinoidParent (parent : Parent)
  deriving DecidableEq, Repr

def componentOrder (centers : List CenterDescriptor) (cisBonds : List BondCitation)
    (parent : Parent) : List StereochemicalNameComponent :=
  [.absoluteCenters centers, .cisDoubleBonds cisBonds, .retinoidParent parent]

@[simp] theorem absolute_configuration_precedes_cis_citations
    (centers : List CenterDescriptor) (cisBonds : List BondCitation) (parent : Parent) :
    (componentOrder centers cisBonds parent).head? = some (.absoluteCenters centers) := by
  rfl

@[simp] theorem cis_citations_precede_parent_name
    (centers : List CenterDescriptor) (cisBonds : List BondCitation) (parent : Parent) :
    (componentOrder centers cisBonds parent).drop 1 =
      [.cisDoubleBonds cisBonds, .retinoidParent parent] := by
  rfl

/-! ## Cis/trans versus E/Z -/

def CitesLocantWithEZ (citations : List BondCitation) (locant : Nat) : Prop :=
  ∃ citation ∈ citations,
    citation.locant = locant ∧ citation.descriptor.isEZ = true

/-- If cis/trans would be ambiguous, the affected bond must be explicitly cited with E/Z. -/
def AmbiguousBondsUseEZ (parent : Parent) (ambiguous : Nat → Bool)
    (citations : List BondCitation) : Prop :=
  ∀ locant ∈ parent.polyeneBondLocants,
    ambiguous locant = true → CitesLocantWithEZ citations locant

def UsesEZ (citations : List BondCitation) : Prop :=
  ∃ citation ∈ citations, citation.descriptor.isEZ = true

def CitesEveryPolyeneBond (parent : Parent) (citations : List BondCitation) : Prop :=
  ∀ locant ∈ parent.polyeneBondLocants,
    ∃ citation ∈ citations, citation.locant = locant

/-- Ret-5.2 recommends a complete double-bond citation whenever E/Z notation is selected. -/
def CompleteEZCitation (parent : Parent) (citations : List BondCitation) : Prop :=
  UsesEZ citations → CitesEveryPolyeneBond parent citations

theorem complete_ez_citation_covers_ambiguous_bond
    (parent : Parent) (citations : List BondCitation)
    (complete : CompleteEZCitation parent citations)
    (uses : UsesEZ citations) (locant : Nat)
    (member : locant ∈ parent.polyeneBondLocants) :
    ∃ citation ∈ citations, citation.locant = locant :=
  complete uses locant member

/-! The chemical configuration of the inherited polyene chain and its CIP E/Z label are distinct
observations.  Substitution can change which groups are selected as high priority without changing
the parent-chain geometry. -/

inductive SideRelation where
  | sameSide
  | oppositeSides
  deriving DecidableEq, Repr

def ezOfHighPriorityRelation : SideRelation → EZ
  | .sameSide => .Z
  | .oppositeSides => .E

structure BondInterpretation where
  parentChainGeometry : ParentGeometry
  highPriorityRelation : SideRelation
  deriving DecidableEq, Repr

def BondInterpretation.ez (interpretation : BondInterpretation) : EZ :=
  ezOfHighPriorityRelation interpretation.highPriorityRelation

def beforeSubstitution : BondInterpretation :=
  { parentChainGeometry := .trans, highPriorityRelation := .oppositeSides }

def afterPriorityChangingSubstitution : BondInterpretation :=
  { parentChainGeometry := .trans, highPriorityRelation := .sameSide }

/-- Formal witness to the warning in Ret-5.2: unchanged parent-chain geometry does not imply an
unchanged E/Z label after substitution changes CIP priority. -/
theorem substitution_can_change_E_to_Z_without_parent_geometry_change :
    beforeSubstitution.parentChainGeometry =
        afterPriorityChangingSubstitution.parentChainGeometry ∧
      beforeSubstitution.ez = .E ∧ afterPriorityChangingSubstitution.ez = .Z := by
  decide

/-! ## Retro-retinoids -/

structure RetroSixSevenEvidence where
  sixSevenConfigurationMustBeIndicated : Bool
  sixSevenConfigurationCited : Bool
  deriving DecidableEq, Repr

def RetroSixSevenEvidence.WellSpecified (evidence : RetroSixSevenEvidence) : Prop :=
  evidence.sixSevenConfigurationMustBeIndicated = true →
    evidence.sixSevenConfigurationCited = true

theorem retro_sixSeven_required_is_cited
    (evidence : RetroSixSevenEvidence) (valid : evidence.WellSpecified)
    (required : evidence.sixSevenConfigurationMustBeIndicated = true) :
    evidence.sixSevenConfigurationCited = true :=
  valid required

/-! ## Corrected non-normative Appendix datum -/

structure LocatedRS where
  locant : Nat
  configuration : RS
  deriving DecidableEq, Repr

def correctedBlumenolAConfigurations : List LocatedRS :=
  [{ locant := 6, configuration := .S }, { locant := 9, configuration := .R }]

/-- The Appendix itself disclaims official recognition of its listed trivial names. -/
def appendixTrivialNamesAreNormativelyRecognized : Bool := false

@[simp] theorem appendix_disclaims_normative_recognition :
    appendixTrivialNamesAreNormativelyRecognized = false := rfl

/-! ## Clause ownership -/

inductive SemanticDomain where
  | retainedStereoparent
  | numbering
  | chiralCenter
  | componentOrder
  | doubleBondDefault
  | doubleBondNotation
  | substitutionRelabeling
  | retroDoubleBond
  deriving DecidableEq, Repr

def provisionSemanticDomain : Provision → SemanticDomain
  | .stereoparentNameImpliesConfiguration
  | .retinolStereoparent
  | .retinalStereoparent
  | .retinoicAcidStereoparent => .retainedStereoparent
  | .stereochemicalLocantsUseRetinoidNumbering => .numbering
  | .chiralCentersUseRS => .chiralCenter
  | .rsLocantsPrecedeRetinoidName
  | .cisCitationsFollowAbsoluteConfiguration => .componentOrder
  | .polyeneDefaultsToAllTrans => .doubleBondDefault
  | .ezAllowedAndRequiredWhenAmbiguous
  | .ezNotationCitesEveryDoubleBond => .doubleBondNotation
  | .substitutionMayChangeEZWithoutGeometryChange => .substitutionRelabeling
  | .retroSixSevenConfigurationExplicitWhenNeeded => .retroDoubleBond

theorem every_provision_has_independent_semantic_domain
    (provision : Provision) : ∃ domain, provisionSemanticDomain provision = domain :=
  ⟨provisionSemanticDomain provision, rfl⟩

end Retinoid1981

end TetraStereo.OneCenter
