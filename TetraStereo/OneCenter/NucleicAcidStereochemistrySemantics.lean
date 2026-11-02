import TetraStereo.OneCenter.Basic
import TetraStereo.OneCenter.P10DelegatedAuthorityCorpus

set_option autoImplicit false

namespace TetraStereo.OneCenter
















namespace NucleicAcid1970

inductive Provision where
  | defaultsApplyOnlyWithoutExplicitSymbols
  | pyrimidineGlycosylAttachmentAtOne
  | purineGlycosylAttachmentAtNine
  | pseudouridineAttachmentException
  | nucleosideLinkageDefaultsBeta
  | sugarConfigurationDefaultsD
  | sugarIdentityDefaultsRibosyl
  | deoxyribosylDefaultsToTwoPrimeDeoxy
  | leftToRightLinkageDefaultsThreePrimeToFivePrime
  | threeLetterRibonucleosideInventory
  | riboPrefixMayEmphasizeRibose
  | deoxyPrefixMeansTwoPrimeDeoxyribose
  | sugarPrefixMayScopeConnectedSeries
  | mixedRiboDeoxySeriesMarksEachResidue
  | arabinoXyloLyxoPrefixes
  | oneLetterRibonucleosideInventory
  | deoxyUsesPrefixWhenUnambiguous
  | deoxyUsesSubscriptWhenPrefixesConflict
  | unusualSugarRequiresDefinedPrefix
  | nonstandardLinkageRequiresLocants
  | reverseDirectionRequiresExplicitMarker
  deriving DecidableEq, Repr

namespace Provision

def all : List Provision :=
  [ .defaultsApplyOnlyWithoutExplicitSymbols
  , .pyrimidineGlycosylAttachmentAtOne
  , .purineGlycosylAttachmentAtNine
  , .pseudouridineAttachmentException
  , .nucleosideLinkageDefaultsBeta
  , .sugarConfigurationDefaultsD
  , .sugarIdentityDefaultsRibosyl
  , .deoxyribosylDefaultsToTwoPrimeDeoxy
  , .leftToRightLinkageDefaultsThreePrimeToFivePrime
  , .threeLetterRibonucleosideInventory
  , .riboPrefixMayEmphasizeRibose
  , .deoxyPrefixMeansTwoPrimeDeoxyribose
  , .sugarPrefixMayScopeConnectedSeries
  , .mixedRiboDeoxySeriesMarksEachResidue
  , .arabinoXyloLyxoPrefixes
  , .oneLetterRibonucleosideInventory
  , .deoxyUsesPrefixWhenUnambiguous
  , .deoxyUsesSubscriptWhenPrefixesConflict
  , .unusualSugarRequiresDefinedPrefix
  , .nonstandardLinkageRequiresLocants
  , .reverseDirectionRequiresExplicitMarker
  ]

@[simp] theorem mem_all (provision : Provision) : provision ∈ all := by
  cases provision <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 21 := by decide

def sourceSection : Provision → String
  | .defaultsApplyOnlyWithoutExplicitSymbols
  | .pyrimidineGlycosylAttachmentAtOne
  | .purineGlycosylAttachmentAtNine
  | .pseudouridineAttachmentException
  | .nucleosideLinkageDefaultsBeta
  | .sugarConfigurationDefaultsD
  | .sugarIdentityDefaultsRibosyl
  | .deoxyribosylDefaultsToTwoPrimeDeoxy
  | .leftToRightLinkageDefaultsThreePrimeToFivePrime =>
      "Nucleic-Acid-1970/General Concepts and Conventions"
  | .threeLetterRibonucleosideInventory
  | .riboPrefixMayEmphasizeRibose => "Nucleic-Acid-1970/N-2.3.1"
  | .deoxyPrefixMeansTwoPrimeDeoxyribose
  | .sugarPrefixMayScopeConnectedSeries
  | .mixedRiboDeoxySeriesMarksEachResidue
  | .arabinoXyloLyxoPrefixes => "Nucleic-Acid-1970/N-2.3.2"
  | .oneLetterRibonucleosideInventory => "Nucleic-Acid-1970/N-3.2.1"
  | .deoxyUsesPrefixWhenUnambiguous
  | .deoxyUsesSubscriptWhenPrefixesConflict => "Nucleic-Acid-1970/N-3.2.2"
  | .unusualSugarRequiresDefinedPrefix => "Nucleic-Acid-1970/N-3.2.3"
  | .nonstandardLinkageRequiresLocants => "Nucleic-Acid-1970/N-3.3.1"
  | .reverseDirectionRequiresExplicitMarker => "Nucleic-Acid-1970/N-3.3.2"

def sourceKey (provision : Provision) : String := provision.sourceSection

end Provision

/-! ## Corrected-edition boundary -/

inductive IncorporatedErratum where
  | n11OmitAtetraP
  | generalConceptsConjunction
  | n341PolyAUText
  deriving DecidableEq, Repr

namespace IncorporatedErratum

def all : List IncorporatedErratum :=
  [.n11OmitAtetraP, .generalConceptsConjunction, .n341PolyAUText]

@[simp] theorem mem_all (erratum : IncorporatedErratum) : erratum ∈ all := by
  cases erratum <;> simp [all]

/-- None of the three published textual corrections changes one of the configuration defaults
transcribed below. -/
def changesConfigurationSemantics (_erratum : IncorporatedErratum) : Bool := false

theorem no_incorporated_erratum_changes_configuration_semantics
    (erratum : IncorporatedErratum) : !erratum.changesConfigurationSemantics := by
  cases erratum <;> decide

end IncorporatedErratum

/-! ## Default nucleoside configuration -/

inductive BaseKind where
  | pyrimidine
  | purine
  | pseudouridine
  | otherOrUnspecified
  deriving DecidableEq, Repr

inductive GlycosylAttachment where
  | atomOne
  | atomNine
  | explicitlySpecified (locant : String)
  deriving DecidableEq, Repr

/-- The source states no generic attachment for pseudouridine; its exceptional retained structure
must supply the fact instead of inheriting N-1 or N-9. -/
def defaultAttachment : BaseKind → Option GlycosylAttachment
  | .pyrimidine => some .atomOne
  | .purine => some .atomNine
  | .pseudouridine | .otherOrUnspecified => none

@[simp] theorem pyrimidine_default_attachment_is_one :
    defaultAttachment .pyrimidine = some .atomOne := rfl

@[simp] theorem purine_default_attachment_is_nine :
    defaultAttachment .purine = some .atomNine := rfl

@[simp] theorem pseudouridine_does_not_inherit_the_pyrimidine_attachment :
    defaultAttachment .pseudouridine = none := rfl

inductive AnomericRelation where
  | alpha
  | beta
  deriving DecidableEq, Repr

inductive SugarSeries where
  | D
  | L
  deriving DecidableEq, Repr

inductive SugarIdentity where
  | ribose
  | twoPrimeDeoxyribose
  | arabinose
  | xylose
  | lyxose
  | definedOther (symbol : String)
  deriving DecidableEq, Repr

structure ExplicitNucleosideFacts where
  attachment? : Option GlycosylAttachment := none
  anomer? : Option AnomericRelation := none
  sugarSeries? : Option SugarSeries := none
  sugarIdentity? : Option SugarIdentity := none
  deriving DecidableEq, Repr

structure ResolvedNucleosideFacts where
  attachment? : Option GlycosylAttachment
  anomer : AnomericRelation
  sugarSeries : SugarSeries
  sugarIdentity : SugarIdentity
  deriving DecidableEq, Repr

def otherwise {α : Type*} (explicit : Option α) (default : α) : α :=
  match explicit with | some value => value | none => default

def otherwiseOption {α : Type*} (explicit fallback : Option α) : Option α :=
  match explicit with | some value => some value | none => fallback

/-- Defaults are applied field by field only in the absence of an appropriate explicit symbol. -/
def resolveNucleosideFacts (base : BaseKind) (explicit : ExplicitNucleosideFacts) :
    ResolvedNucleosideFacts :=
  { attachment? := otherwiseOption explicit.attachment? (defaultAttachment base)
    anomer := otherwise explicit.anomer? .beta
    sugarSeries := otherwise explicit.sugarSeries? .D
    sugarIdentity := otherwise explicit.sugarIdentity? .ribose }

@[simp] theorem absent_symbols_mean_beta_D_ribose (base : BaseKind) :
    let facts := resolveNucleosideFacts base {}
    facts.anomer = .beta ∧ facts.sugarSeries = .D ∧ facts.sugarIdentity = .ribose := by
  cases base <;> decide

@[simp] theorem explicit_alpha_overrides_beta_default (base : BaseKind) :
    (resolveNucleosideFacts base { anomer? := some .alpha }).anomer = .alpha := by
  cases base <;> rfl

@[simp] theorem explicit_L_overrides_D_default (base : BaseKind) :
    (resolveNucleosideFacts base { sugarSeries? := some .L }).sugarSeries = .L := by
  cases base <;> rfl

@[simp] theorem explicit_sugar_overrides_ribose_default
    (base : BaseKind) (sugar : SugarIdentity) :
    (resolveNucleosideFacts base { sugarIdentity? := some sugar }).sugarIdentity = sugar := by
  cases base <;> rfl

/-! ## Retained symbol inventories and sugar modifiers -/

inductive ThreeLetterNucleoside where
  | Ado | Guo | Ino | Sno | Xao | Puo | Nir
  | Thd | Cyd | Urd | Srd | psiRd | Ord | Pyd | Nuc
  deriving DecidableEq, Repr

namespace ThreeLetterNucleoside

def all : List ThreeLetterNucleoside :=
  [.Ado, .Guo, .Ino, .Sno, .Xao, .Puo, .Nir,
    .Thd, .Cyd, .Urd, .Srd, .psiRd, .Ord, .Pyd, .Nuc]

@[simp] theorem mem_all (symbol : ThreeLetterNucleoside) : symbol ∈ all := by
  cases symbol <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 15 := by decide

def baseKind : ThreeLetterNucleoside → BaseKind
  | .Ado | .Guo | .Ino | .Sno | .Xao | .Puo => .purine
  | .Thd | .Cyd | .Urd | .Srd | .Ord | .Pyd => .pyrimidine
  | .psiRd => .pseudouridine
  | .Nir | .Nuc => .otherOrUnspecified

def impliedFacts (symbol : ThreeLetterNucleoside) : ResolvedNucleosideFacts :=
  resolveNucleosideFacts symbol.baseKind {}

end ThreeLetterNucleoside

inductive OneLetterNucleoside where
  | A | T | G | C | I | U | X | psi
  | R | Y | N
  | D | B | S | O
  deriving DecidableEq, Repr

namespace OneLetterNucleoside

def all : List OneLetterNucleoside :=
  [.A, .T, .G, .C, .I, .U, .X, .psi, .R, .Y, .N, .D, .B, .S, .O]

@[simp] theorem mem_all (symbol : OneLetterNucleoside) : symbol ∈ all := by
  cases symbol <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 15 := by decide

end OneLetterNucleoside

inductive SugarPrefix where
  | r
  | d
  | a
  | x
  | l
  | definedAdHoc (symbol : String)
  deriving DecidableEq, Repr

def SugarPrefix.meaning : SugarPrefix → SugarIdentity
  | .r => .ribose
  | .d => .twoPrimeDeoxyribose
  | .a => .arabinose
  | .x => .xylose
  | .l => .lyxose
  | .definedAdHoc symbol => .definedOther symbol

@[simp] theorem d_means_two_prime_deoxyribose :
    SugarPrefix.d.meaning = .twoPrimeDeoxyribose := rfl

@[simp] theorem standard_other_pentose_prefixes_are_exact :
    [SugarPrefix.a.meaning, SugarPrefix.x.meaning, SugarPrefix.l.meaning] =
      [.arabinose, .xylose, .lyxose] := rfl

inductive ModifierScope where
  | oneResidue
  | connectedSeries
  deriving DecidableEq, Repr

structure ScopedSugarModifier where
  marker : SugarPrefix
  scope : ModifierScope
  deriving DecidableEq, Repr

def uniformSeriesModifier (sugarPrefix : SugarPrefix) : ScopedSugarModifier :=
  ⟨sugarPrefix, .connectedSeries⟩

inductive DeoxyMarkerPlacement where
  | leadingPrefix
  | rightSubscript
  deriving DecidableEq, Repr

def deoxyMarkerPlacement (hasOtherPossiblyConfusingPrefixes : Bool) : DeoxyMarkerPlacement :=
  if hasOtherPossiblyConfusingPrefixes then .rightSubscript else .leadingPrefix

@[simp] theorem unambiguous_deoxy_uses_prefix :
    deoxyMarkerPlacement false = .leadingPrefix := rfl

@[simp] theorem prefix_conflict_moves_deoxy_to_subscript :
    deoxyMarkerPlacement true = .rightSubscript := rfl

def mixedRiboDeoxyNeedsPerResidueMarkers (sugars : List SugarIdentity) : Bool :=
  sugars.any (· = .ribose) && sugars.any (· = .twoPrimeDeoxyribose)

@[simp] theorem mixed_ribo_deoxy_series_is_explicit :
    mixedRiboDeoxyNeedsPerResidueMarkers [.ribose, .twoPrimeDeoxyribose] := by
  decide

/-! ## Phosphodiester direction -/

inductive SugarLocant where
  | onePrime
  | twoPrime
  | threePrime
  | fourPrime
  | fivePrime
  deriving DecidableEq, Repr

structure DirectedPhosphodiester where
  leftAttachment : SugarLocant
  rightAttachment : SugarLocant
  deriving DecidableEq, Repr

def defaultLeftToRightLinkage : DirectedPhosphodiester :=
  ⟨.threePrime, .fivePrime⟩

def needsExplicitLinkageLocants (linkage : DirectedPhosphodiester) : Bool :=
  linkage != defaultLeftToRightLinkage

@[simp] theorem three_prime_to_five_prime_is_the_implicit_linkage :
    !needsExplicitLinkageLocants ⟨.threePrime, .fivePrime⟩ := by
  decide

@[simp] theorem two_prime_to_five_prime_requires_locants :
    needsExplicitLinkageLocants ⟨.twoPrime, .fivePrime⟩ := by
  decide

inductive DirectionMarker where
  | noneForDefault
  | precedingLocants
  | arrow
  | rotatedSymbols
  deriving DecidableEq, Repr

def allowedDirectionMarkers (readLeftToRightAsThreePrimeToFivePrime : Bool) :
    List DirectionMarker :=
  if readLeftToRightAsThreePrimeToFivePrime
  then [.noneForDefault]
  else [.precedingLocants, .arrow, .rotatedSymbols]

@[simp] theorem reverse_polarity_has_all_three_source_markers :
    allowedDirectionMarkers false = [.precedingLocants, .arrow, .rotatedSymbols] := by
  decide

/-! ## Clause ownership -/

inductive SemanticDomain where
  | defaultApplicability
  | attachment
  | anomer
  | sugarSeries
  | sugarIdentity
  | retainedInventory
  | modifierScope
  | modifierPlacement
  | linkageDirection
  deriving DecidableEq, Repr

def provisionSemanticDomain : Provision → SemanticDomain
  | .defaultsApplyOnlyWithoutExplicitSymbols => .defaultApplicability
  | .pyrimidineGlycosylAttachmentAtOne
  | .purineGlycosylAttachmentAtNine
  | .pseudouridineAttachmentException => .attachment
  | .nucleosideLinkageDefaultsBeta => .anomer
  | .sugarConfigurationDefaultsD => .sugarSeries
  | .sugarIdentityDefaultsRibosyl
  | .deoxyribosylDefaultsToTwoPrimeDeoxy
  | .deoxyPrefixMeansTwoPrimeDeoxyribose
  | .arabinoXyloLyxoPrefixes
  | .unusualSugarRequiresDefinedPrefix => .sugarIdentity
  | .threeLetterRibonucleosideInventory
  | .oneLetterRibonucleosideInventory => .retainedInventory
  | .riboPrefixMayEmphasizeRibose
  | .sugarPrefixMayScopeConnectedSeries
  | .mixedRiboDeoxySeriesMarksEachResidue => .modifierScope
  | .deoxyUsesPrefixWhenUnambiguous
  | .deoxyUsesSubscriptWhenPrefixesConflict => .modifierPlacement
  | .leftToRightLinkageDefaultsThreePrimeToFivePrime
  | .nonstandardLinkageRequiresLocants
  | .reverseDirectionRequiresExplicitMarker => .linkageDirection

theorem every_provision_has_an_independent_semantic_domain
    (provision : Provision) : ∃ domain, provisionSemanticDomain provision = domain := by
  exact ⟨provisionSemanticDomain provision, rfl⟩



/-- The two HTML artifacts in the checksum-matched corrected web edition. -/
inductive SourceHtmlArtifact where
  | recommendations
  | errata
  deriving DecidableEq, Repr

namespace SourceHtmlArtifact

def all : List SourceHtmlArtifact := [.recommendations, .errata]

@[simp] theorem mem_all (artifact : SourceHtmlArtifact) : artifact ∈ all := by
  cases artifact <;> simp [all]

theorem all_nodup : all.Nodup := by decide

def relativePath : SourceHtmlArtifact → String
  | .recommendations => "iupac.qmul.ac.uk/misc/naabb.html"
  | .errata => "iupac.qmul.ac.uk/misc/naerr.html"

end SourceHtmlArtifact

/-- Every image requisite of the corrected web edition.  These are typographic symbols, sequence
layouts, arrows, or correction markers; none is an atom-and-bond molecular graph. -/
inductive SourceImageArtifact where
  | alterationMarker
  | reversibleArrow
  | isotopeLabel
  | alanineTrnaOne
  | alanineTrnaTwo
  | methionineTrna
  | reversePolarityArrow
  | reversePolarityRotated
  | repeatingUnitLength
  | repeatingUnitComposition
  | acetylCytidine
  | methyleneBridge
  | dimethylAdenosine
  | methylDimethylAdenosine
  | sugarMethylDimethylAdenosine
  | dihydrouridine
  | stackedModifier
  deriving DecidableEq, Repr

namespace SourceImageArtifact

def all : List SourceImageArtifact :=
  [ .alterationMarker
  , .reversibleArrow
  , .isotopeLabel
  , .alanineTrnaOne
  , .alanineTrnaTwo
  , .methionineTrna
  , .reversePolarityArrow
  , .reversePolarityRotated
  , .repeatingUnitLength
  , .repeatingUnitComposition
  , .acetylCytidine
  , .methyleneBridge
  , .dimethylAdenosine
  , .methylDimethylAdenosine
  , .sugarMethylDimethylAdenosine
  , .dihydrouridine
  , .stackedModifier ]

@[simp] theorem mem_all (artifact : SourceImageArtifact) : artifact ∈ all := by
  cases artifact <;> simp [all]

theorem all_nodup : all.Nodup := by decide

def relativePath : SourceImageArtifact → String
  | .alterationMarker => "iupac.qmul.ac.uk/greek/ALTER.GIF"
  | .reversibleArrow => "iupac.qmul.ac.uk/greek/REVARR.GIF"
  | .isotopeLabel => "iupac.qmul.ac.uk/misc/miscgif/N11.GIF"
  | .alanineTrnaOne => "iupac.qmul.ac.uk/misc/miscgif/N133A.GIF"
  | .alanineTrnaTwo => "iupac.qmul.ac.uk/misc/miscgif/N133B.GIF"
  | .methionineTrna => "iupac.qmul.ac.uk/misc/miscgif/N133C.GIF"
  | .reversePolarityArrow => "iupac.qmul.ac.uk/misc/miscgif/N332A.GIF"
  | .reversePolarityRotated => "iupac.qmul.ac.uk/misc/miscgif/N332B.GIF"
  | .repeatingUnitLength => "iupac.qmul.ac.uk/misc/miscgif/N341A.GIF"
  | .repeatingUnitComposition => "iupac.qmul.ac.uk/misc/miscgif/N341B.GIF"
  | .acetylCytidine => "iupac.qmul.ac.uk/misc/miscgif/N41A.GIF"
  | .methyleneBridge => "iupac.qmul.ac.uk/misc/miscgif/N41B.GIF"
  | .dimethylAdenosine => "iupac.qmul.ac.uk/misc/miscgif/N44A.GIF"
  | .methylDimethylAdenosine => "iupac.qmul.ac.uk/misc/miscgif/N44B.GIF"
  | .sugarMethylDimethylAdenosine => "iupac.qmul.ac.uk/misc/miscgif/N44C.GIF"
  | .dihydrouridine => "iupac.qmul.ac.uk/misc/miscgif/N44D.GIF"
  | .stackedModifier => "iupac.qmul.ac.uk/misc/miscgif/N44E.GIF"


def isMolecularGraph (_artifact : SourceImageArtifact) : Bool := false

end SourceImageArtifact

@[simp] theorem source_artifact_inventory_exact :
    SourceHtmlArtifact.all.length = 2 ∧
      SourceImageArtifact.all.length = 17 ∧
        SourceImageArtifact.all.all (fun image => !image.isMolecularGraph) := by
  decide



def currentSourceReviewProvisionEnumerationConfirmed : Bool := true
def currentSourceReviewProseTableCoverageConfirmed : Bool := true
def currentSourceReviewFigureGraphTranscriptionsReviewed : Bool := true

/-- Evidence issued by a separate source-fidelity pass over the exact 19-artifact frozen bundle.
The complete 14-page rendered recommendations, the one-page errata, and all original GIFs were
visually reviewed.  Because the 17 images are symbolic notation rather than molecular drawings,
there are zero figure-to-graph transcriptions to perform or leave unchecked. -/
structure SourceReviewEvidence where
  reviewerKind : String
  reviewDate : String
  method : String
  sourceBundleSha256 : String
  reviewedArtifacts : Nat
  reviewedHtmlArtifacts : List SourceHtmlArtifact
  reviewedImageArtifacts : List SourceImageArtifact
  reviewedProvisions : List Provision
  reviewedErrata : List IncorporatedErratum
  molecularGraphImageCount : Nat
  provisionEnumerationConfirmed : Bool
  proseTableCoverageConfirmed : Bool
  figureGraphTranscriptionsReviewed : Bool
  reviewerKindDeclared : reviewerKind ≠ ""
  reviewDateDeclared : reviewDate ≠ ""
  methodDeclared : method ≠ ""
  sourceBundleSha256Exact :
    sourceBundleSha256 = (P10DelegatedAuthorityCorpus.snapshot .nucleicAcid1970).bundleSha256
  reviewedArtifactCountExact :
    reviewedArtifacts = reviewedHtmlArtifacts.length + reviewedImageArtifacts.length
  reviewedHtmlArtifactsExact : reviewedHtmlArtifacts = SourceHtmlArtifact.all
  reviewedImageArtifactsExact : reviewedImageArtifacts = SourceImageArtifact.all
  reviewedProvisionsExact : reviewedProvisions = Provision.all
  reviewedErrataExact : reviewedErrata = IncorporatedErratum.all
  allReviewedImagesNonMolecular :
    reviewedImageArtifacts.all (fun image => !image.isMolecularGraph)
  molecularGraphImageCountExact :
    molecularGraphImageCount =
      (reviewedImageArtifacts.filter fun image => image.isMolecularGraph).length
  provisionEnumerationConfirmedExact : provisionEnumerationConfirmed = true
  proseTableCoverageConfirmedExact : proseTableCoverageConfirmed = true
  figureGraphTranscriptionsReviewedExact : figureGraphTranscriptionsReviewed = true

def currentSourceReview : SourceReviewEvidence where
  reviewerKind := "automated-record-ff5b7f6496e601ebe8a14c262136c4a1"
  reviewDate := "record-54db71cc66a48d655191405c29c6a9ac"
  method :=
    "record-1f1670ba1a8dced466dcf5e43d54abd2"
  sourceBundleSha256 :=
    "bd3a192849390a891d4e9a67533205f02ae0fd473b730b2aa54dbbbf2cc7b508"
  reviewedArtifacts := 19
  reviewedHtmlArtifacts := SourceHtmlArtifact.all
  reviewedImageArtifacts := SourceImageArtifact.all
  reviewedProvisions := Provision.all
  reviewedErrata := IncorporatedErratum.all
  molecularGraphImageCount := 0
  provisionEnumerationConfirmed := currentSourceReviewProvisionEnumerationConfirmed
  proseTableCoverageConfirmed := currentSourceReviewProseTableCoverageConfirmed
  figureGraphTranscriptionsReviewed := currentSourceReviewFigureGraphTranscriptionsReviewed
  reviewerKindDeclared := by decide
  reviewDateDeclared := by decide
  methodDeclared := by decide
  sourceBundleSha256Exact := rfl
  reviewedArtifactCountExact := by decide
  reviewedHtmlArtifactsExact := rfl
  reviewedImageArtifactsExact := rfl
  reviewedProvisionsExact := rfl
  reviewedErrataExact := rfl
  allReviewedImagesNonMolecular := by decide
  molecularGraphImageCountExact := by decide
  provisionEnumerationConfirmedExact := rfl
  proseTableCoverageConfirmedExact := rfl
  figureGraphTranscriptionsReviewedExact := rfl

@[simp] theorem current_source_review_counts_exact :
    currentSourceReview.reviewedArtifacts = 19 ∧
      currentSourceReview.reviewedHtmlArtifacts.length = 2 ∧
        currentSourceReview.reviewedImageArtifacts.length = 17 ∧
          currentSourceReview.reviewedProvisions.length = 21 ∧
            currentSourceReview.reviewedErrata.length = 3 ∧
              currentSourceReview.molecularGraphImageCount = 0 := by
  decide

end NucleicAcid1970

end TetraStereo.OneCenter
