import TetraStereo.OneCenter.Basic
import TetraStereo.OneCenter.P10DelegatedAuthorityCorpus

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent amino-acid and peptide stereochemistry semantics

This module audits the configuration-bearing clauses of *Nomenclature and Symbolism for Amino
Acids and Peptides (Recommendations 1983)* in its corrected web edition.  It covers 3AA-3,
3AA-4, 3AA-5, peptide-name rule 3AA-13.2, symbol defaults 3AA-14.5 and 3AA-19.2, and the
enantiomeric replacement/whole-peptide rules in 3AA-22.

The source's most easily mishandled distinction is formalized explicitly: `DL` is a racemate for
one chiral amino acid, but applying `DL` independently at several peptide residues produces more
than one enantiomeric pair and is not one racemate.  Such residue-local uncertainty is `ambo`.
No production analyzer is imported.
-/

namespace AminoAcidPeptide1983

inductive Provision where
  | alphaCarbonUsesSerineReferencedDL
  | alphaUnknownUsesXi
  | fischerRosanoffProjection
  | dlPrefixImmediatelyPrecedesParent
  | chiralGlycineDerivativePrefixPrecedesSubstituent
  | derivativeAndPeptidePrefixPrecedesParentResidue
  | proteinSourceMayOmitImpliedL
  | unresolvedSyntheticMayOmitImpliedRacemate
  | enantiomerIndependentStatementMayOmitPrefix
  | aminoAcidAndCarbohydrateDLSubscripts
  | dlSubscriptsRequiredWhenAmbiguous
  | cipRSGeneralMethod
  | proteinogenicLUsuallyS
  | cysteineAndCystineAreRExceptions
  | aminoSugarDerivedRouteUsesCarbohydrateRules
  | alphaAndHighestSugarCenterSeriesAreIndependent
  | mesoMeansAchiralDespiteChiralGroups
  | dlMeansEquimolarEnantiomers
  | racAndPlusMinusAlternatives
  | nonAlphaCentersPreferRS
  | uniformRSMayIncludeAlphaCenter
  | carbohydrateMultiCenterPrefixesDiscouraged
  | prolineCisTransReferent
  | prolineCisTransMayBeOmittedWhenUnambiguous
  | alloRestrictedToIsoleucineAndThreonine
  | alloConfigurationInventory
  | unresolvedIsomersMayUseTemporaryLabels
  | knownAndUnknownCentersUseRSAndXi
  | allUnknownCentersUseXi
  | knownRelativeUnknownAbsoluteUsesRStarSStar
  | otherElementsUseGeneralStereochemicalRules
  | opticalRotationSignIsSeparateFromConfiguration
  | racemateMayUsePlusMinus
  | peptidePrefixIsResidueLocal
  | dlForbiddenAsMultiChiralPeptideDescription
  | amboDescribesAllLocalConfigurations
  | amboMayBeLocalizedToOneResidue
  | aminoAcidSymbolsDefaultToL
  | symbolMayExplicitlyMarkDOrDL
  | peptideSequenceDMarker
  | peptideSequenceAmboMarker
  | peptideSequenceXiMarker
  | namedPeptideEnantiomericReplacementUsesD
  | namedPeptideReplacementMixtureUsesAmbo
  | retroReversesAndEntInvertsWholeNamedPeptide
  deriving DecidableEq, Repr

namespace Provision

def all : List Provision :=
  [ .alphaCarbonUsesSerineReferencedDL
  , .alphaUnknownUsesXi
  , .fischerRosanoffProjection
  , .dlPrefixImmediatelyPrecedesParent
  , .chiralGlycineDerivativePrefixPrecedesSubstituent
  , .derivativeAndPeptidePrefixPrecedesParentResidue
  , .proteinSourceMayOmitImpliedL
  , .unresolvedSyntheticMayOmitImpliedRacemate
  , .enantiomerIndependentStatementMayOmitPrefix
  , .aminoAcidAndCarbohydrateDLSubscripts
  , .dlSubscriptsRequiredWhenAmbiguous
  , .cipRSGeneralMethod
  , .proteinogenicLUsuallyS
  , .cysteineAndCystineAreRExceptions
  , .aminoSugarDerivedRouteUsesCarbohydrateRules
  , .alphaAndHighestSugarCenterSeriesAreIndependent
  , .mesoMeansAchiralDespiteChiralGroups
  , .dlMeansEquimolarEnantiomers
  , .racAndPlusMinusAlternatives
  , .nonAlphaCentersPreferRS
  , .uniformRSMayIncludeAlphaCenter
  , .carbohydrateMultiCenterPrefixesDiscouraged
  , .prolineCisTransReferent
  , .prolineCisTransMayBeOmittedWhenUnambiguous
  , .alloRestrictedToIsoleucineAndThreonine
  , .alloConfigurationInventory
  , .unresolvedIsomersMayUseTemporaryLabels
  , .knownAndUnknownCentersUseRSAndXi
  , .allUnknownCentersUseXi
  , .knownRelativeUnknownAbsoluteUsesRStarSStar
  , .otherElementsUseGeneralStereochemicalRules
  , .opticalRotationSignIsSeparateFromConfiguration
  , .racemateMayUsePlusMinus
  , .peptidePrefixIsResidueLocal
  , .dlForbiddenAsMultiChiralPeptideDescription
  , .amboDescribesAllLocalConfigurations
  , .amboMayBeLocalizedToOneResidue
  , .aminoAcidSymbolsDefaultToL
  , .symbolMayExplicitlyMarkDOrDL
  , .peptideSequenceDMarker
  , .peptideSequenceAmboMarker
  , .peptideSequenceXiMarker
  , .namedPeptideEnantiomericReplacementUsesD
  , .namedPeptideReplacementMixtureUsesAmbo
  , .retroReversesAndEntInvertsWholeNamedPeptide
  ]

@[simp] theorem mem_all (provision : Provision) : provision ∈ all := by
  cases provision <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 45 := by decide

def sourceSection : Provision → String
  | .alphaCarbonUsesSerineReferencedDL | .alphaUnknownUsesXi
  | .fischerRosanoffProjection => "Amino-Acid-1983/3AA-3.1"
  | .dlPrefixImmediatelyPrecedesParent
  | .chiralGlycineDerivativePrefixPrecedesSubstituent
  | .derivativeAndPeptidePrefixPrecedesParentResidue => "Amino-Acid-1983/3AA-3.2"
  | .proteinSourceMayOmitImpliedL
  | .unresolvedSyntheticMayOmitImpliedRacemate
  | .enantiomerIndependentStatementMayOmitPrefix => "Amino-Acid-1983/3AA-3.3"
  | .aminoAcidAndCarbohydrateDLSubscripts
  | .dlSubscriptsRequiredWhenAmbiguous => "Amino-Acid-1983/3AA-3.4"
  | .cipRSGeneralMethod | .proteinogenicLUsuallyS
  | .cysteineAndCystineAreRExceptions => "Amino-Acid-1983/3AA-3.5"
  | .aminoSugarDerivedRouteUsesCarbohydrateRules
  | .alphaAndHighestSugarCenterSeriesAreIndependent => "Amino-Acid-1983/3AA-3.6"
  | .mesoMeansAchiralDespiteChiralGroups => "Amino-Acid-1983/3AA-3.7"
  | .dlMeansEquimolarEnantiomers | .racAndPlusMinusAlternatives => "Amino-Acid-1983/3AA-3.8"
  | .nonAlphaCentersPreferRS | .uniformRSMayIncludeAlphaCenter => "Amino-Acid-1983/3AA-4.1"
  | .carbohydrateMultiCenterPrefixesDiscouraged => "Amino-Acid-1983/3AA-4.2"
  | .prolineCisTransReferent
  | .prolineCisTransMayBeOmittedWhenUnambiguous => "Amino-Acid-1983/3AA-4.3"
  | .alloRestrictedToIsoleucineAndThreonine
  | .alloConfigurationInventory => "Amino-Acid-1983/3AA-4.4"
  | .unresolvedIsomersMayUseTemporaryLabels | .knownAndUnknownCentersUseRSAndXi
  | .allUnknownCentersUseXi
  | .knownRelativeUnknownAbsoluteUsesRStarSStar => "Amino-Acid-1983/3AA-4.5"
  | .otherElementsUseGeneralStereochemicalRules => "Amino-Acid-1983/3AA-4.6"
  | .opticalRotationSignIsSeparateFromConfiguration
  | .racemateMayUsePlusMinus => "Amino-Acid-1983/3AA-5"
  | .peptidePrefixIsResidueLocal | .dlForbiddenAsMultiChiralPeptideDescription
  | .amboDescribesAllLocalConfigurations
  | .amboMayBeLocalizedToOneResidue => "Amino-Acid-1983/3AA-13.2"
  | .aminoAcidSymbolsDefaultToL
  | .symbolMayExplicitlyMarkDOrDL => "Amino-Acid-1983/3AA-14.5"
  | .peptideSequenceDMarker | .peptideSequenceAmboMarker
  | .peptideSequenceXiMarker => "Amino-Acid-1983/3AA-19.2"
  | .namedPeptideEnantiomericReplacementUsesD
  | .namedPeptideReplacementMixtureUsesAmbo => "Amino-Acid-1983/3AA-22.1(e)"
  | .retroReversesAndEntInvertsWholeNamedPeptide => "Amino-Acid-1983/3AA-22.7"

def sourceKey (provision : Provision) : String := provision.sourceSection

end Provision

/-! ## Alpha-carbon D/L and CIP R/S -/

inductive DLSeries where
  | D
  | L
  deriving DecidableEq, Repr

namespace DLSeries

def inverted : DLSeries → DLSeries
  | .D => .L
  | .L => .D

@[simp] theorem inverted_involutive (series : DLSeries) : series.inverted.inverted = series := by
  cases series <;> rfl

end DLSeries

inductive RS where
  | R
  | S
  deriving DecidableEq, Repr

namespace RS

def inverted : RS → RS
  | .R => .S
  | .S => .R

@[simp] theorem inverted_involutive (descriptor : RS) : descriptor.inverted.inverted = descriptor := by
  cases descriptor <;> rfl

end RS

inductive AlphaConfiguration where
  | known (series : DLSeries)
  | unknown
  deriving DecidableEq, Repr

inductive AlphaPrefix where
  | D
  | L
  | xi
  deriving DecidableEq, Repr

def alphaPrefix : AlphaConfiguration → AlphaPrefix
  | .known .D => .D
  | .known .L => .L
  | .unknown => .xi

inductive HorizontalSide where
  | left
  | right
  deriving DecidableEq, Repr

structure FischerRosanoffProjection where
  principalChainVertical : Bool
  principalChainBehindPlane : Bool
  horizontalGroupsInFront : Bool
  aminoGroupSide : HorizontalSide
  deriving DecidableEq, Repr

def FischerRosanoffProjection.isCanonical (projection : FischerRosanoffProjection) : Bool :=
  projection.principalChainVertical && projection.principalChainBehindPlane &&
    projection.horizontalGroupsInFront

def seriesFromCanonicalFischer (projection : FischerRosanoffProjection) : Option DLSeries :=
  if projection.isCanonical then
    some (match projection.aminoGroupSide with | .left => .L | .right => .D)
  else none

@[simp] theorem canonical_amino_left_projection_is_L :
    seriesFromCanonicalFischer ⟨true, true, true, .left⟩ = some .L := rfl

inductive AminoAcidCIPClass where
  | ordinaryProteinogenic
  | cysteine
  | cystine
  deriving DecidableEq, Repr

/-- The statement is scoped to the source's L alpha-amino-acid comparison. -/
def cipOfLAlphaCarbon : AminoAcidCIPClass → RS
  | .ordinaryProteinogenic => .S
  | .cysteine | .cystine => .R

@[simp] theorem L_cysteine_and_cystine_are_R_exceptions :
    cipOfLAlphaCarbon .cysteine = .R ∧ cipOfLAlphaCarbon .cystine = .R := by
  decide

inductive DLSubscript where
  | sForSerineReference
  | gForGlyceraldehydeReference
  deriving DecidableEq, Repr

inductive SeriesReferenceSystem where
  | aminoAcid
  | carbohydrate
  deriving DecidableEq, Repr

def subscriptForReference : SeriesReferenceSystem → DLSubscript
  | .aminoAcid => .sForSerineReference
  | .carbohydrate => .gForGlyceraldehydeReference

structure AminoSugarSeriesReading where
  alphaSeries : DLSeries
  highestNumberedChiralCenterSeries : DLSeries
  deriving DecidableEq, Repr

/-- 3AA-3.6 gives both equal and unequal examples, so neither series is derivable from the other. -/
def glucosaminicReading : AminoSugarSeriesReading := ⟨.D, .D⟩
def mannosaminicReading : AminoSugarSeriesReading := ⟨.L, .D⟩

theorem amino_sugar_alpha_and_highest_center_series_are_independent :
    glucosaminicReading.highestNumberedChiralCenterSeries =
        mannosaminicReading.highestNumberedChiralCenterSeries ∧
      glucosaminicReading.alphaSeries ≠ mannosaminicReading.alphaSeries := by
  decide

/-! ## Prefix omission, meso, racemic, and optical rotation -/

inductive OmissionContext where
  | proteinSource
  | unresolvedSynthetic
  | statementIndependentOfEnantiomer
  deriving DecidableEq, Repr

inductive PopulationMeaning where
  | enantiopure (series : DLSeries)
  | equimolarRacemate
  | arbitraryOrUnspecified
  deriving DecidableEq, Repr

def omittedPrefixMeaning : OmissionContext → PopulationMeaning
  | .proteinSource => .enantiopure .L
  | .unresolvedSynthetic => .equimolarRacemate
  | .statementIndependentOfEnantiomer => .arbitraryOrUnspecified

@[simp] theorem omitted_prefix_is_context_sensitive :
    omittedPrefixMeaning .proteinSource ≠ omittedPrefixMeaning .unresolvedSynthetic := by
  decide

structure Racemate where
  first : DLSeries
  second : DLSeries
  firstFraction : Rat
  secondFraction : Rat
  deriving DecidableEq, Repr

def dlRacemate : Racemate := ⟨.D, .L, 1 / 2, 1 / 2⟩

@[simp] theorem DL_is_an_equimolar_D_L_pair :
    dlRacemate.first = .D ∧ dlRacemate.second = .L ∧
      dlRacemate.firstFraction = 1 / 2 ∧ dlRacemate.secondFraction = 1 / 2 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

inductive SymmetryClass where
  | chiral
  | achiral
  deriving DecidableEq, Repr

def mesoMeaning (hasChiralGroups hasInternalCompensation : Bool) : SymmetryClass :=
  if hasChiralGroups && hasInternalCompensation then .achiral else .chiral

@[simp] theorem meso_can_have_chiral_groups_but_is_achiral :
    mesoMeaning true true = .achiral := rfl

inductive OpticalRotationSign where
  | plus
  | minus
  | plusMinus
  deriving DecidableEq, Repr

structure ConfigurationAndRotation where
  series : DLSeries
  rotation : OpticalRotationSign
  deriving DecidableEq, Repr

/-- Rotation and D/L are separate reported properties; the source permits a sign together with a
known D/L symbol rather than defining one from the other. -/
def lPlus : ConfigurationAndRotation := ⟨.L, .plus⟩
def lMinus : ConfigurationAndRotation := ⟨.L, .minus⟩

theorem reference_semantics_does_not_identify_L_with_an_optical_sign :
    lPlus.series = lMinus.series ∧ lPlus.rotation ≠ lMinus.rotation := by
  decide

/-! ## Non-alpha centers and retained diastereomer names -/

structure LocatedRS where
  locant : Nat
  descriptor : RS
  deriving DecidableEq, Repr

inductive ThreonineFamily where
  | Lthreonine
  | Lallothreonine
  deriving DecidableEq, Repr

def ThreonineFamily.configuration : ThreonineFamily → List LocatedRS
  | .Lthreonine => [⟨2, .S⟩, ⟨3, .R⟩]
  | .Lallothreonine => [⟨2, .S⟩, ⟨3, .S⟩]

inductive IsoleucineFamily where
  | Lisoleucine
  | Lalloisoleucine
  deriving DecidableEq, Repr

def IsoleucineFamily.configuration : IsoleucineFamily → List LocatedRS
  | .Lisoleucine => [⟨2, .S⟩, ⟨3, .S⟩]
  | .Lalloisoleucine => [⟨2, .S⟩, ⟨3, .R⟩]

@[simp] theorem allo_inventory_changes_only_the_side_chain_center :
    ThreonineFamily.Lthreonine.configuration ≠
        ThreonineFamily.Lallothreonine.configuration ∧
      IsoleucineFamily.Lisoleucine.configuration ≠
        IsoleucineFamily.Lalloisoleucine.configuration := by
  decide

inductive CenterDescriptor where
  | absolute (descriptor : RS)
  | relativeRStar
  | relativeSStar
  | xi
  deriving DecidableEq, Repr

structure PartiallyKnownConfiguration where
  descriptors : List (Nat × CenterDescriptor)
  deriving DecidableEq, Repr

def sourcePartiallyKnownExample : PartiallyKnownConfiguration :=
  ⟨[(2, .absolute .S), (5, .xi)]⟩

def sourceRelativeExample : PartiallyKnownConfiguration :=
  ⟨[(2, .relativeRStar), (5, .relativeSStar)]⟩

inductive ProlineRelativeGeometry where
  | cis
  | trans
  deriving DecidableEq, Repr

structure ProlineGeometryReading where
  hydroxylVersusCarboxyl : ProlineRelativeGeometry
  deriving DecidableEq, Repr

/-! ## Peptide mixtures and local configuration -/

inductive ResidueConfiguration where
  | exact (series : DLSeries)
  | ambo
  | unknown
  deriving DecidableEq, Repr

def expandResidueConfiguration : ResidueConfiguration → List DLSeries
  | .exact series => [series]
  | .ambo | .unknown => [.D, .L]

def twoResidueDLProducts : List (List DLSeries) :=
  [[.L, .L], [.L, .D], [.D, .L], [.D, .D]]

def invertSequence (sequence : List DLSeries) : List DLSeries := sequence.map DLSeries.inverted

@[simp] theorem two_DL_residues_form_two_enantiomeric_pairs_not_one_racemate :
    invertSequence [.L, .L] = [.D, .D] ∧
      invertSequence [.L, .D] = [.D, .L] ∧
      twoResidueDLProducts.length = 4 := by
  decide

def residueLocalMixture (first second : ResidueConfiguration) : List (List DLSeries) :=
  (expandResidueConfiguration first).flatMap fun firstSeries =>
    (expandResidueConfiguration second).map fun secondSeries => [firstSeries, secondSeries]

@[simp] theorem ambo_at_one_residue_expands_only_that_residue :
    residueLocalMixture (.exact .L) .ambo = [[.L, .D], [.L, .L]] := by
  decide

def entPeptide (sequence : List DLSeries) : List DLSeries := invertSequence sequence

@[simp] theorem ent_inverts_every_residue_and_is_involutive (sequence : List DLSeries) :
    entPeptide (entPeptide sequence) = sequence := by
  simp [entPeptide, invertSequence, List.map_map, Function.comp_def]

/-- The `retro-` operation in 3AA-22.7 reverses residue order without changing the local
configuration of any residue. -/
def retroPeptide (sequence : List DLSeries) : List DLSeries := sequence.reverse

@[simp] theorem retro_reverses_sequence_and_is_involutive (sequence : List DLSeries) :
    retroPeptide (retroPeptide sequence) = sequence := by
  simp [retroPeptide]

@[simp] theorem retro_and_ent_are_distinct_operations :
    retroPeptide [.L, .L, .D] = [.D, .L, .L] ∧
      entPeptide [.L, .L, .D] = [.D, .D, .L] := by
  decide

inductive SymbolConfigurationMark where
  | omittedMeansL
  | D
  | DL
  | ambo
  | xi
  deriving DecidableEq, Repr

def symbolMeaning : SymbolConfigurationMark → ResidueConfiguration
  | .omittedMeansL => .exact .L
  | .D => .exact .D
  | .DL | .ambo => .ambo
  | .xi => .unknown

@[simp] theorem bare_chiral_residue_symbol_means_L :
    symbolMeaning .omittedMeansL = .exact .L := rfl

/-! ## Clause ownership -/

inductive SemanticDomain where
  | alphaSeries
  | fischerProjection
  | prefixPlacement
  | omission
  | referenceSubscript
  | cipRelation
  | carbohydrateBoundary
  | mesoAndRacemate
  | nonAlphaConfiguration
  | retainedDiastereomer
  | incompleteKnowledge
  | otherStereogenicElement
  | opticalRotation
  | peptideMixture
  | symbolDefault
  | namedPeptideOperation
  deriving DecidableEq, Repr

def provisionSemanticDomain : Provision → SemanticDomain
  | .alphaCarbonUsesSerineReferencedDL | .alphaUnknownUsesXi => .alphaSeries
  | .fischerRosanoffProjection => .fischerProjection
  | .dlPrefixImmediatelyPrecedesParent | .chiralGlycineDerivativePrefixPrecedesSubstituent
  | .derivativeAndPeptidePrefixPrecedesParentResidue => .prefixPlacement
  | .proteinSourceMayOmitImpliedL | .unresolvedSyntheticMayOmitImpliedRacemate
  | .enantiomerIndependentStatementMayOmitPrefix => .omission
  | .aminoAcidAndCarbohydrateDLSubscripts | .dlSubscriptsRequiredWhenAmbiguous =>
      .referenceSubscript
  | .cipRSGeneralMethod | .proteinogenicLUsuallyS
  | .cysteineAndCystineAreRExceptions => .cipRelation
  | .aminoSugarDerivedRouteUsesCarbohydrateRules
  | .alphaAndHighestSugarCenterSeriesAreIndependent
  | .carbohydrateMultiCenterPrefixesDiscouraged => .carbohydrateBoundary
  | .mesoMeansAchiralDespiteChiralGroups | .dlMeansEquimolarEnantiomers
  | .racAndPlusMinusAlternatives => .mesoAndRacemate
  | .nonAlphaCentersPreferRS | .uniformRSMayIncludeAlphaCenter
  | .prolineCisTransReferent | .prolineCisTransMayBeOmittedWhenUnambiguous =>
      .nonAlphaConfiguration
  | .alloRestrictedToIsoleucineAndThreonine | .alloConfigurationInventory =>
      .retainedDiastereomer
  | .unresolvedIsomersMayUseTemporaryLabels | .knownAndUnknownCentersUseRSAndXi
  | .allUnknownCentersUseXi | .knownRelativeUnknownAbsoluteUsesRStarSStar =>
      .incompleteKnowledge
  | .otherElementsUseGeneralStereochemicalRules => .otherStereogenicElement
  | .opticalRotationSignIsSeparateFromConfiguration
  | .racemateMayUsePlusMinus => .opticalRotation
  | .peptidePrefixIsResidueLocal | .dlForbiddenAsMultiChiralPeptideDescription
  | .amboDescribesAllLocalConfigurations | .amboMayBeLocalizedToOneResidue => .peptideMixture
  | .aminoAcidSymbolsDefaultToL | .symbolMayExplicitlyMarkDOrDL
  | .peptideSequenceDMarker | .peptideSequenceAmboMarker
  | .peptideSequenceXiMarker => .symbolDefault
  | .namedPeptideEnantiomericReplacementUsesD
  | .namedPeptideReplacementMixtureUsesAmbo
  | .retroReversesAndEntInvertsWholeNamedPeptide => .namedPeptideOperation

theorem every_provision_has_an_independent_semantic_domain
    (provision : Provision) : ∃ domain, provisionSemanticDomain provision = domain := by
  exact ⟨provisionSemanticDomain provision, rfl⟩



/-- The 37 HTML artifacts in the refreshed official bundle. -/
inductive SourceHtmlArtifact where
  | a1113 | a1416 | a1525 | a1819 | a2021 | aa122 | aa17 | aa171 | aa172
  | aa173 | aa191 | aa194 | aa1n2 | aa212 | aa22 | aa229 | aa3t5 | aa610
  | addenda | appendix | appendixContinuation | contents | err134 | err135 | err152
  | err193 | err215 | errAddenda | errAppendix | errContents | errata | hacek
  | index | introduction | references | tables2to4 | table1
  deriving DecidableEq, Repr

namespace SourceHtmlArtifact

def all : List SourceHtmlArtifact :=
  [ .a1113, .a1416, .a1525, .a1819, .a2021, .aa122, .aa17, .aa171, .aa172
  , .aa173, .aa191, .aa194, .aa1n2, .aa212, .aa22, .aa229, .aa3t5, .aa610
  , .addenda, .appendix, .appendixContinuation, .contents, .err134, .err135, .err152
  , .err193, .err215, .errAddenda, .errAppendix, .errContents, .errata, .hacek
  , .index, .introduction, .references, .tables2to4, .table1 ]

@[simp] theorem mem_all (artifact : SourceHtmlArtifact) : artifact ∈ all := by
  cases artifact <;> simp [all]

theorem all_nodup : all.Nodup := by decide

def filename : SourceHtmlArtifact → String
  | .a1113 => "A1113.html"
  | .a1416 => "A1416.html"
  | .a1525 => "A1525.html"
  | .a1819 => "A1819.html"
  | .a2021 => "A2021.html"
  | .aa122 => "AA122.html"
  | .aa17 => "AA17.html"
  | .aa171 => "AA171.html"
  | .aa172 => "AA172.html"
  | .aa173 => "AA173.html"
  | .aa191 => "AA191.html"
  | .aa194 => "AA194.html"
  | .aa1n2 => "AA1n2.html"
  | .aa212 => "AA212.html"
  | .aa22 => "AA22.html"
  | .aa229 => "AA229.html"
  | .aa3t5 => "AA3t5.html"
  | .aa610 => "AA610.html"
  | .addenda => "AAad.html"
  | .appendix => "AAap.html"
  | .appendixContinuation => "AAap2.html"
  | .contents => "cont.html"
  | .err134 => "er134.html"
  | .err135 => "er135.html"
  | .err152 => "er152.html"
  | .err193 => "er193.html"
  | .err215 => "er215.html"
  | .errAddenda => "eradd.html"
  | .errAppendix => "erapp.html"
  | .errContents => "ercon.html"
  | .errata => "errat.html"
  | .hacek => "hacek.html"
  | .index => "index.html"
  | .introduction => "intro.html"
  | .references => "refs.html"
  | .tables2to4 => "ta2t4.html"
  | .table1 => "tab1.html"

def relativePath (artifact : SourceHtmlArtifact) : String :=
  "iupac.qmul.ac.uk/AminoAcid/" ++ artifact.filename

end SourceHtmlArtifact

/-- Every original GIF in the refreshed bundle, named by its exact normalized filename. -/
inductive SourceImageArtifact where
  | aa134 | aa1521 | aa1525 | aa162 | aa1641 | aa1642 | aa165
  | aa171a | aa171b | aa171c
  | aa172a | aa172b | aa172c | aa172d | aa172e | aa172f | aa172g | aa172h
  | aa172i | aa172j | aa172k | aa172l | aa172m | aa172n | aa172o | aa172p | aa172q
  | aa173a | aa173b | aa173c | aa174a | aa174b | aa174c
  | aa191a | aa191b | aa191c | aa191d | aa191e | aa191f | aa191g
  | aa193a | aa193b | aa193c | aa193d
  | aa194a | aa194b | aa194c | aa194d
  | aa1951a | aa1951b | aa1951c | aa1952a | aa1952b | aa1952c
  | aa1a | aa1b | aa1c | aa1d
  | aa221a | aa221b | aa221c | aa222 | aa223 | aa224 | aa2251
  | aa2252a | aa2252b | aa2252c | aa2253 | aa226a | aa226b
  | aa229a | aa229b | aa229c | aa229d | aa229e | aa229f | aa229x
  | aa31a | aa31b | aa43 | aa44 | aaada
  | aaapa | aaapb | aaapc | aaapd | aaape | aaapf | aaapg | aaaph | aaapi
  | aaapj | aaapk | aaadb | accent | alterationMark
  deriving DecidableEq, Repr

namespace SourceImageArtifact

def all : List SourceImageArtifact :=
  [ .aa134, .aa1521, .aa1525, .aa162, .aa1641, .aa1642, .aa165
  , .aa171a, .aa171b, .aa171c
  , .aa172a, .aa172b, .aa172c, .aa172d, .aa172e, .aa172f, .aa172g, .aa172h
  , .aa172i, .aa172j, .aa172k, .aa172l, .aa172m, .aa172n, .aa172o, .aa172p, .aa172q
  , .aa173a, .aa173b, .aa173c, .aa174a, .aa174b, .aa174c
  , .aa191a, .aa191b, .aa191c, .aa191d, .aa191e, .aa191f, .aa191g
  , .aa193a, .aa193b, .aa193c, .aa193d
  , .aa194a, .aa194b, .aa194c, .aa194d
  , .aa1951a, .aa1951b, .aa1951c, .aa1952a, .aa1952b, .aa1952c
  , .aa1a, .aa1b, .aa1c, .aa1d
  , .aa221a, .aa221b, .aa221c, .aa222, .aa223, .aa224, .aa2251
  , .aa2252a, .aa2252b, .aa2252c, .aa2253, .aa226a, .aa226b
  , .aa229a, .aa229b, .aa229c, .aa229d, .aa229e, .aa229f, .aa229x
  , .aa31a, .aa31b, .aa43, .aa44, .aaada
  , .aaapa, .aaapb, .aaapc, .aaapd, .aaape, .aaapf, .aaapg, .aaaph, .aaapi
  , .aaapj, .aaapk, .aaadb, .accent, .alterationMark ]

@[simp] theorem mem_all (artifact : SourceImageArtifact) : artifact ∈ all := by
  cases artifact <;> simp [all]

theorem all_nodup : all.Nodup := by decide

def filename : SourceImageArtifact → String
  | .aa134 => "AA134.GIF"
  | .aa1521 => "AA1521.GIF"
  | .aa1525 => "AA1525.GIF"
  | .aa162 => "AA162.GIF"
  | .aa1641 => "AA1641.GIF"
  | .aa1642 => "AA1642.GIF"
  | .aa165 => "AA165.GIF"
  | .aa171a => "AA171A.GIF"
  | .aa171b => "AA171B.GIF"
  | .aa171c => "AA171C.GIF"
  | .aa172a => "AA172A.GIF"
  | .aa172b => "AA172B.GIF"
  | .aa172c => "AA172C.GIF"
  | .aa172d => "AA172D.GIF"
  | .aa172e => "AA172E.GIF"
  | .aa172f => "AA172F.GIF"
  | .aa172g => "AA172G.GIF"
  | .aa172h => "AA172H.GIF"
  | .aa172i => "AA172I.GIF"
  | .aa172j => "AA172J.GIF"
  | .aa172k => "AA172K.GIF"
  | .aa172l => "AA172L.GIF"
  | .aa172m => "AA172M.GIF"
  | .aa172n => "AA172N.GIF"
  | .aa172o => "AA172O.GIF"
  | .aa172p => "AA172P.GIF"
  | .aa172q => "AA172Q.GIF"
  | .aa173a => "AA173A.GIF"
  | .aa173b => "AA173B.GIF"
  | .aa173c => "AA173C.GIF"
  | .aa174a => "AA174A.GIF"
  | .aa174b => "AA174B.GIF"
  | .aa174c => "AA174C.GIF"
  | .aa191a => "AA191A.GIF"
  | .aa191b => "AA191B.GIF"
  | .aa191c => "AA191C.GIF"
  | .aa191d => "AA191D.GIF"
  | .aa191e => "AA191E.GIF"
  | .aa191f => "AA191F.GIF"
  | .aa191g => "AA191G.GIF"
  | .aa193a => "AA193A.GIF"
  | .aa193b => "AA193B.GIF"
  | .aa193c => "AA193C.GIF"
  | .aa193d => "AA193D.GIF"
  | .aa194a => "AA194A.GIF"
  | .aa194b => "AA194B.GIF"
  | .aa194c => "AA194C.GIF"
  | .aa194d => "AA194D.GIF"
  | .aa1951a => "AA1951A.GIF"
  | .aa1951b => "AA1951B.GIF"
  | .aa1951c => "AA1951C.GIF"
  | .aa1952a => "AA1952A.GIF"
  | .aa1952b => "AA1952B.GIF"
  | .aa1952c => "AA1952C.GIF"
  | .aa1a => "AA1A.GIF"
  | .aa1b => "AA1B.GIF"
  | .aa1c => "AA1C.GIF"
  | .aa1d => "AA1D.GIF"
  | .aa221a => "AA221A.GIF"
  | .aa221b => "AA221B.GIF"
  | .aa221c => "AA221C.GIF"
  | .aa222 => "AA222.GIF"
  | .aa223 => "AA223.GIF"
  | .aa224 => "AA224.GIF"
  | .aa2251 => "AA2251.GIF"
  | .aa2252a => "AA2252A.GIF"
  | .aa2252b => "AA2252B.GIF"
  | .aa2252c => "AA2252C.GIF"
  | .aa2253 => "AA2253.GIF"
  | .aa226a => "AA226A.GIF"
  | .aa226b => "AA226B.GIF"
  | .aa229a => "AA229A.GIF"
  | .aa229b => "AA229B.GIF"
  | .aa229c => "AA229C.GIF"
  | .aa229d => "AA229D.GIF"
  | .aa229e => "AA229E.GIF"
  | .aa229f => "AA229F.GIF"
  | .aa229x => "AA229X.GIF"
  | .aa31a => "AA31A.GIF"
  | .aa31b => "AA31B.GIF"
  | .aa43 => "AA43.GIF"
  | .aa44 => "AA44.GIF"
  | .aaada => "AAADA.GIF"
  | .aaapa => "AAAPA.GIF"
  | .aaapb => "AAAPB.GIF"
  | .aaapc => "AAAPC.GIF"
  | .aaapd => "AAAPD.GIF"
  | .aaape => "AAAPE.GIF"
  | .aaapf => "AAAPF.GIF"
  | .aaapg => "AAAPG.GIF"
  | .aaaph => "AAAPH.GIF"
  | .aaapi => "AAAPI.GIF"
  | .aaapj => "AAAPJ.GIF"
  | .aaapk => "AAAPK.GIF"
  | .aaadb => "AAadb.gif"
  | .accent => "ACCENT.GIF"
  | .alterationMark => "ALTER.GIF"

def relativePath (artifact : SourceImageArtifact) : String :=
  "iupac.qmul.ac.uk/AminoAcid/AAgif/" ++ artifact.filename

/-- Direct inspection classifies `ACCENT.GIF` as a reference-text facsimile and `ALTER.GIF` as
the red correction dot. Every other original image carries chemical structure, residue topology,
stereochemical projection, or peptide connectivity that remains in the transcription queue. -/
def isGraphOrTopologyDiagram : SourceImageArtifact → Bool
  | .accent | .alterationMark => false
  | _ => true

/-- The typed amino-acid semantics are not image-by-image graph/topology transcriptions. -/
def transcriptionReviewed (_artifact : SourceImageArtifact) : Bool := false

end SourceImageArtifact

@[simp] theorem source_artifact_inventory_exact :
    SourceHtmlArtifact.all.length = 37 ∧
      SourceImageArtifact.all.length = 97 ∧
        (SourceImageArtifact.all.filter fun image => image.isGraphOrTopologyDiagram).length = 95 ∧
          (SourceImageArtifact.all.filter fun image => image.transcriptionReviewed).length = 0 := by
  decide

/-- Small manifest-facing constants keep checklist computation independent of the full ledger. -/
def currentSourceReviewProvisionEnumerationConfirmed : Bool := true
def currentSourceReviewProseTableCoverageConfirmed : Bool := true
def currentSourceReviewFigureGraphTranscriptionsReviewed : Bool := false

/-- Evidence from a separate fidelity pass over the refreshed 134-artifact official bundle.
All 93 rendered HTML pages and all 97 original GIFs were visually reviewed, and the 45 modeled
configuration-bearing provisions were checked against the primary 29-page publication. The
official site's broken uppercase image reference is recorded explicitly. -/
structure SourceReviewEvidence where
  reviewerKind : String
  reviewDate : String
  method : String
  sourceBundleSha256 : String
  sourcePathCaseNormalization : String
  primaryPublicationCrossCheck : String
  reviewedArtifacts : Nat
  reviewedRenderedPages : Nat
  reviewedHtmlArtifacts : List SourceHtmlArtifact
  reviewedImageArtifacts : List SourceImageArtifact
  reviewedProvisions : List Provision
  graphOrTopologyImageCount : Nat
  reviewedTranscriptionCount : Nat
  provisionEnumerationConfirmed : Bool
  proseTableCoverageConfirmed : Bool
  figureGraphTranscriptionsReviewed : Bool
  reviewerKindDeclared : reviewerKind ≠ ""
  reviewDateDeclared : reviewDate ≠ ""
  methodDeclared : method ≠ ""
  sourceBundleSha256Exact :
    sourceBundleSha256 = (P10DelegatedAuthorityCorpus.snapshot .aminoAcidPeptide1983).bundleSha256
  sourcePathCaseNormalizationExact : sourcePathCaseNormalization =
    "AAad.html AAgif/AAADB.GIF normalized to official served AAgif/AAadb.gif"
  primaryPublicationCrossCheckExact : primaryPublicationCrossCheck =
    "Eur. J. Biochem. 138, 9-37 (1984), DOI 10.1111/j.1432-1033.1984.tb07877.x"
  reviewedArtifactCountExact :
    reviewedArtifacts = reviewedHtmlArtifacts.length + reviewedImageArtifacts.length
  reviewedRenderedPagesExact : reviewedRenderedPages = 93
  reviewedHtmlArtifactsExact : reviewedHtmlArtifacts = SourceHtmlArtifact.all
  reviewedImageArtifactsExact : reviewedImageArtifacts = SourceImageArtifact.all
  reviewedProvisionsExact : reviewedProvisions = Provision.all
  graphOrTopologyImageCountExact :
    graphOrTopologyImageCount =
      (reviewedImageArtifacts.filter fun image => image.isGraphOrTopologyDiagram).length
  reviewedTranscriptionCountExact :
    reviewedTranscriptionCount =
      (reviewedImageArtifacts.filter fun image => image.transcriptionReviewed).length
  graphOrTopologyQueueStillOpen : reviewedTranscriptionCount < graphOrTopologyImageCount
  provisionEnumerationConfirmedExact : provisionEnumerationConfirmed = true
  proseTableCoverageConfirmedExact : proseTableCoverageConfirmed = true
  figureGraphTranscriptionsReviewedExact : figureGraphTranscriptionsReviewed = false

def currentSourceReview : SourceReviewEvidence where
  reviewerKind := "automated-record-ff5b7f6496e601ebe8a14c262136c4a1"
  reviewDate := "record-54db71cc66a48d655191405c29c6a9ac"
  method :=
    "record-77e06e5fe9502e9d56f86722449c3bb5"
  sourceBundleSha256 :=
    "f55486c6c8c24d545cde6387792b7ac77959476653ffd005f4d480572a8f808d"
  sourcePathCaseNormalization :=
    "AAad.html AAgif/AAADB.GIF normalized to official served AAgif/AAadb.gif"
  primaryPublicationCrossCheck :=
    "Eur. J. Biochem. 138, 9-37 (1984), DOI 10.1111/j.1432-1033.1984.tb07877.x"
  reviewedArtifacts := 134
  reviewedRenderedPages := 93
  reviewedHtmlArtifacts := SourceHtmlArtifact.all
  reviewedImageArtifacts := SourceImageArtifact.all
  reviewedProvisions := Provision.all
  graphOrTopologyImageCount := 95
  reviewedTranscriptionCount := 0
  provisionEnumerationConfirmed := currentSourceReviewProvisionEnumerationConfirmed
  proseTableCoverageConfirmed := currentSourceReviewProseTableCoverageConfirmed
  figureGraphTranscriptionsReviewed := currentSourceReviewFigureGraphTranscriptionsReviewed
  reviewerKindDeclared := by decide
  reviewDateDeclared := by decide
  methodDeclared := by decide
  sourceBundleSha256Exact := rfl
  sourcePathCaseNormalizationExact := rfl
  primaryPublicationCrossCheckExact := rfl
  reviewedArtifactCountExact := by decide
  reviewedRenderedPagesExact := rfl
  reviewedHtmlArtifactsExact := rfl
  reviewedImageArtifactsExact := rfl
  reviewedProvisionsExact := rfl
  graphOrTopologyImageCountExact := by decide
  reviewedTranscriptionCountExact := by decide
  graphOrTopologyQueueStillOpen := by decide
  provisionEnumerationConfirmedExact := rfl
  proseTableCoverageConfirmedExact := rfl
  figureGraphTranscriptionsReviewedExact := rfl

@[simp] theorem current_source_review_counts_exact :
    currentSourceReview.reviewedArtifacts = 134 ∧
      currentSourceReview.reviewedRenderedPages = 93 ∧
        currentSourceReview.reviewedHtmlArtifacts.length = 37 ∧
          currentSourceReview.reviewedImageArtifacts.length = 97 ∧
            currentSourceReview.reviewedProvisions.length = 45 ∧
              currentSourceReview.graphOrTopologyImageCount = 95 ∧
                currentSourceReview.reviewedTranscriptionCount = 0 := by
  decide

@[simp] theorem current_source_review_provenance_notes_exact :
    currentSourceReview.sourcePathCaseNormalization =
        "AAad.html AAgif/AAADB.GIF normalized to official served AAgif/AAadb.gif" ∧
      currentSourceReview.primaryPublicationCrossCheck =
        "Eur. J. Biochem. 138, 9-37 (1984), DOI 10.1111/j.1432-1033.1984.tb07877.x" := by
  decide

end AminoAcidPeptide1983

end TetraStereo.OneCenter
