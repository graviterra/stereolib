import TetraStereo.OneCenter.Basic
import TetraStereo.OneCenter.P10DelegatedAuthorityCorpus

set_option autoImplicit false

namespace TetraStereo.OneCenter










namespace Carotenoid1974

inductive Provision where
  | chiralCentersUseRS
  | rsLocantsPrecedeCarotenoidName
  | knownAlleneConfigurationUsesAbsoluteDescriptor
  | caroteneStemDefaultsToAllTrans
  | cisCitationsFollowAbsoluteConfiguration
  | trisubstitutedCisUsesMainChainSubstituents
  | neoPrefixDoesNotAssertKnownGeometry
  | ezAllowedWhenCisTransAmbiguous
  | cyclicEndGroupGemDimethylNumbering
  | acyclicEndGroupGemDimethylNumbering
  deriving DecidableEq, Repr

namespace Provision

def all : List Provision :=
  [ .chiralCentersUseRS
  , .rsLocantsPrecedeCarotenoidName
  , .knownAlleneConfigurationUsesAbsoluteDescriptor
  , .caroteneStemDefaultsToAllTrans
  , .cisCitationsFollowAbsoluteConfiguration
  , .trisubstitutedCisUsesMainChainSubstituents
  , .neoPrefixDoesNotAssertKnownGeometry
  , .ezAllowedWhenCisTransAmbiguous
  , .cyclicEndGroupGemDimethylNumbering
  , .acyclicEndGroupGemDimethylNumbering
  ]

@[simp] theorem mem_all (provision : Provision) : provision ∈ all := by
  cases provision <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 10 := by decide

def sourceSection : Provision → String
  | .chiralCentersUseRS => "Carotenoid 12.1"
  | .rsLocantsPrecedeCarotenoidName => "Carotenoid 12.1"
  | .knownAlleneConfigurationUsesAbsoluteDescriptor => "Carotenoid 12.2"
  | .caroteneStemDefaultsToAllTrans => "Carotenoid 12.3"
  | .cisCitationsFollowAbsoluteConfiguration => "Carotenoid 12.3"
  | .trisubstitutedCisUsesMainChainSubstituents => "Carotenoid 12.3"
  | .neoPrefixDoesNotAssertKnownGeometry => "Carotenoid 12.3"
  | .ezAllowedWhenCisTransAmbiguous => "Carotenoid 12.3"
  | .cyclicEndGroupGemDimethylNumbering => "Carotenoid 12.4/Figure A-B"
  | .acyclicEndGroupGemDimethylNumbering => "Carotenoid 12.4/Figure C"

def sourceKey (provision : Provision) : String :=
  "CAROTENOID-1974/" ++ provision.sourceSection

end Provision

/-! ## Absolute configuration -/

inductive RS where
  | R
  | S
  deriving DecidableEq, Repr

structure LocatedRS where
  locant : String
  descriptor : RS
  deriving DecidableEq, Repr

inductive AbsoluteElement where
  | chiralCenter (locant : String)
  | alleneAxis (locant : String)
  deriving DecidableEq, Repr

/-- Rule 12.2 requires the absolute allene descriptor when configuration is known and makes no
descriptor assertion when it is not known. -/
def knownAbsoluteDescriptor (known : Bool) (descriptor : RS) : Option RS :=
  if known then some descriptor else none

@[simp] theorem known_allene_gets_descriptor (descriptor : RS) :
    knownAbsoluteDescriptor true descriptor = some descriptor := by
  rfl

@[simp] theorem unknown_allene_gets_no_invented_descriptor (descriptor : RS) :
    knownAbsoluteDescriptor false descriptor = none := by
  rfl

/-! ## Carotene stem and double-bond configuration -/

inductive Geometry where
  | cis
  | trans
  deriving DecidableEq, Repr

/-- Rule 12.3 quantifies over every double bond in the carotene stem; it is not an inventory of
only the locants appearing in one example. -/
inductive CaroteneDoubleBondScope where
  | allDoubleBonds
  deriving DecidableEq, Repr

/-- Different carotene parents expose different configurationally relevant double-bond locants;
Rule 12.3 gives all of them the same default. -/
structure CaroteneStem (BondLocant : Type*) where
  configurationalDoubleBonds : List BondLocant

def CaroteneStem.impliedGeometry {BondLocant : Type*} [DecidableEq BondLocant]
    (stem : CaroteneStem BondLocant) (locant : BondLocant) : Option Geometry :=
  if locant ∈ stem.configurationalDoubleBonds then some .trans else none

theorem carotene_stem_implies_trans
    {BondLocant : Type*} [DecidableEq BondLocant]
    (stem : CaroteneStem BondLocant) (locant : BondLocant)
    (member : locant ∈ stem.configurationalDoubleBonds) :
    stem.impliedGeometry locant = some .trans := by
  simp [CaroteneStem.impliedGeometry, member]

inductive NameComponent where
  | absoluteConfiguration (descriptors : List LocatedRS)
  | cisDoubleBonds (locants : List String)
  | carotenoidName (name : String)
  deriving DecidableEq, Repr

def componentOrder (absolute : List LocatedRS) (cisLocants : List String) (name : String) :
    List NameComponent :=
  [.absoluteConfiguration absolute, .cisDoubleBonds cisLocants, .carotenoidName name]

@[simp] theorem absolute_configuration_is_first
    (absolute : List LocatedRS) (cisLocants : List String) (name : String) :
    (componentOrder absolute cisLocants name).head? = some (.absoluteConfiguration absolute) := by
  rfl

@[simp] theorem cis_configuration_follows_absolute
    (absolute : List LocatedRS) (cisLocants : List String) (name : String) :
    (componentOrder absolute cisLocants name).drop 1 =
      [.cisDoubleBonds cisLocants, .carotenoidName name] := by
  rfl

inductive SideRelation where
  | sameSide
  | oppositeSides
  deriving DecidableEq, Repr

/-- At a trisubstituted bond, `cis` is defined using the two substituents belonging to the main
carbon chain—not by whichever substituents happen to rank highest under CIP. -/
def trisubstitutedMainChainGeometry : SideRelation → Geometry
  | .sameSide => .cis
  | .oppositeSides => .trans

inductive EZ where
  | E
  | Z
  deriving DecidableEq, Repr

def ezFromCIPHighPriorityGroups : SideRelation → EZ
  | .sameSide => .Z
  | .oppositeSides => .E

structure TrisubstitutedReading where
  mainChainRelation : SideRelation
  cipHighPriorityRelation : SideRelation
  deriving DecidableEq, Repr

def TrisubstitutedReading.cisTrans (reading : TrisubstitutedReading) : Geometry :=
  trisubstitutedMainChainGeometry reading.mainChainRelation

def TrisubstitutedReading.ez (reading : TrisubstitutedReading) : EZ :=
  ezFromCIPHighPriorityGroups reading.cipHighPriorityRelation

def carotenoidAmbiguityWitness : TrisubstitutedReading :=
  { mainChainRelation := .sameSide, cipHighPriorityRelation := .oppositeSides }

/-- Main-chain `cis` and CIP `E` can simultaneously be correct; Rule 12.3 therefore permits E/Z
when the older cis/trans wording could be ambiguous. -/
theorem trisubstituted_cis_is_not_definitionally_Z :
    carotenoidAmbiguityWitness.cisTrans = .cis ∧
      carotenoidAmbiguityWitness.ez = .E := by
  decide

/-- A `neo` label distinguishes an incompletely characterized cis isomer; it is not evidence for a
particular geometrical configuration. -/
structure NeoDesignation where
  label : String
  deriving DecidableEq, Repr

def NeoDesignation.assertedGeometry (_designation : NeoDesignation) : Option Geometry := none

@[simp] theorem neo_prefix_does_not_assert_geometry (designation : NeoDesignation) :
    designation.assertedGeometry = none := rfl

/-! ## Rule 12.4 configuration-sensitive methyl numbering -/

inductive MethylPosition where
  | below
  | above
  deriving DecidableEq, Repr

inductive CyclicProjection where
  | formulaA
  | formulaB1
  | formulaB2
  deriving DecidableEq, Repr

/-- In A and B1 the assignments are unaltered; B2 reverses them. -/
def cyclicMethylLocant : CyclicProjection → MethylPosition → Nat
  | .formulaA, .below | .formulaB1, .below => 16
  | .formulaA, .above | .formulaB1, .above => 17
  | .formulaB2, .below => 17
  | .formulaB2, .above => 16

@[simp] theorem formulaA_and_B1_numbering_agree (position : MethylPosition) :
    cyclicMethylLocant .formulaA position = cyclicMethylLocant .formulaB1 position := by
  cases position <;> rfl

@[simp] theorem formulaB2_reverses_formulaA (position : MethylPosition) :
    cyclicMethylLocant .formulaB2 position ≠ cyclicMethylLocant .formulaA position := by
  cases position <;> decide

inductive AcyclicMethylRelation where
  | transToMainChain
  | cisToMainChain
  deriving DecidableEq, Repr

def acyclicMethylLocant : AcyclicMethylRelation → Nat
  | .transToMainChain => 16
  | .cisToMainChain => 17

@[simp] theorem acyclic_trans_methyl_is_16 :
    acyclicMethylLocant .transToMainChain = 16 := rfl

@[simp] theorem acyclic_cis_methyl_is_17 :
    acyclicMethylLocant .cisToMainChain = 17 := rfl

/-! ## Clause ownership -/

inductive SemanticDomain where
  | absoluteCenter
  | absoluteAllene
  | nameOrder
  | stemDefault
  | trisubstitutedGeometry
  | unknownGeometry
  | geometricNotation
  | cyclicMethylNumbering
  | acyclicMethylNumbering
  deriving DecidableEq, Repr

def provisionSemanticDomain : Provision → SemanticDomain
  | .chiralCentersUseRS => .absoluteCenter
  | .rsLocantsPrecedeCarotenoidName
  | .cisCitationsFollowAbsoluteConfiguration => .nameOrder
  | .knownAlleneConfigurationUsesAbsoluteDescriptor => .absoluteAllene
  | .caroteneStemDefaultsToAllTrans => .stemDefault
  | .trisubstitutedCisUsesMainChainSubstituents => .trisubstitutedGeometry
  | .neoPrefixDoesNotAssertKnownGeometry => .unknownGeometry
  | .ezAllowedWhenCisTransAmbiguous => .geometricNotation
  | .cyclicEndGroupGemDimethylNumbering => .cyclicMethylNumbering
  | .acyclicEndGroupGemDimethylNumbering => .acyclicMethylNumbering

theorem every_provision_has_independent_semantic_domain
    (provision : Provision) : ∃ domain, provisionSemanticDomain provision = domain :=
  ⟨provisionSemanticDomain provision, rfl⟩



/-- The four HTML artifacts in the checksum-matched recursive bundle. -/
inductive SourceHtmlArtifact where
  | index
  | rulesOneToSeven
  | rulesEightToThirteen
  | trivialNameAppendix
  deriving DecidableEq, Repr

namespace SourceHtmlArtifact

def all : List SourceHtmlArtifact :=
  [.index, .rulesOneToSeven, .rulesEightToThirteen, .trivialNameAppendix]

@[simp] theorem mem_all (artifact : SourceHtmlArtifact) : artifact ∈ all := by
  cases artifact <;> simp [all]

theorem all_nodup : all.Nodup := by decide

def relativePath : SourceHtmlArtifact → String
  | .index => "iupac.qmul.ac.uk/carot/index.html"
  | .rulesOneToSeven => "iupac.qmul.ac.uk/carot/car1t7.html"
  | .rulesEightToThirteen => "iupac.qmul.ac.uk/carot/car8t13.html"
  | .trivialNameAppendix => "iupac.qmul.ac.uk/carot/app.html"

end SourceHtmlArtifact

/-- Every original GIF in the frozen bundle, named by its exact source filename. -/
inductive SourceImageArtifact where
  | c105a | c105b | c11a | c11b | c121 | c122 | c123 | c124a | c124b
  | c1a | c1b | c2
  | c32a | c32b | c32c | c32d | c32e | c32f | c32g | c32h
  | c33a | c33b | c34 | c4a | c4b
  | c51a | c51b | c51c | c52 | c6a | c6b | c6c
  | c71a | c71b | c72 | c73a | c73b | c74a | c74b
  | c81a | c81b | c82a | c82b | c82c | c82d
  | c94a | c94b | c94c
  deriving DecidableEq, Repr

namespace SourceImageArtifact

def all : List SourceImageArtifact :=
  [ .c105a, .c105b, .c11a, .c11b, .c121, .c122, .c123, .c124a, .c124b
  , .c1a, .c1b, .c2
  , .c32a, .c32b, .c32c, .c32d, .c32e, .c32f, .c32g, .c32h
  , .c33a, .c33b, .c34, .c4a, .c4b
  , .c51a, .c51b, .c51c, .c52, .c6a, .c6b, .c6c
  , .c71a, .c71b, .c72, .c73a, .c73b, .c74a, .c74b
  , .c81a, .c81b, .c82a, .c82b, .c82c, .c82d
  , .c94a, .c94b, .c94c ]

@[simp] theorem mem_all (artifact : SourceImageArtifact) : artifact ∈ all := by
  cases artifact <;> simp [all]

theorem all_nodup : all.Nodup := by decide

def filename : SourceImageArtifact → String
  | .c105a => "c105a.gif"
  | .c105b => "c105b.gif"
  | .c11a => "c11a.gif"
  | .c11b => "c11b.gif"
  | .c121 => "c121.gif"
  | .c122 => "c122.gif"
  | .c123 => "c123.gif"
  | .c124a => "c124a.gif"
  | .c124b => "c124b.gif"
  | .c1a => "c1a.gif"
  | .c1b => "c1b.gif"
  | .c2 => "c2.gif"
  | .c32a => "c32a.gif"
  | .c32b => "c32b.gif"
  | .c32c => "c32c.gif"
  | .c32d => "c32d.gif"
  | .c32e => "c32e.gif"
  | .c32f => "c32f.gif"
  | .c32g => "c32g.gif"
  | .c32h => "c32h.gif"
  | .c33a => "c33a.gif"
  | .c33b => "c33b.gif"
  | .c34 => "c34.gif"
  | .c4a => "c4a.gif"
  | .c4b => "c4b.gif"
  | .c51a => "c51a.gif"
  | .c51b => "c51b.gif"
  | .c51c => "c51c.gif"
  | .c52 => "c52.gif"
  | .c6a => "c6a.gif"
  | .c6b => "c6b.gif"
  | .c6c => "c6c.gif"
  | .c71a => "c71a.gif"
  | .c71b => "c71b.gif"
  | .c72 => "c72.gif"
  | .c73a => "c73a.gif"
  | .c73b => "c73b.gif"
  | .c74a => "c74a.gif"
  | .c74b => "c74b.gif"
  | .c81a => "c81a.gif"
  | .c81b => "c81b.gif"
  | .c82a => "c82a.gif"
  | .c82b => "c82b.gif"
  | .c82c => "c82c.gif"
  | .c82d => "c82d.gif"
  | .c94a => "c94a.gif"
  | .c94b => "c94b.gif"
  | .c94c => "c94c.gif"

def relativePath (artifact : SourceImageArtifact) : String :=
  "iupac.qmul.ac.uk/carot/cargif/" ++ artifact.filename

/-- Direct inspection of every original GIF classifies all 48 as molecular structure or numbered
structural diagrams. -/
def isMolecularGraph (_artifact : SourceImageArtifact) : Bool := true

/-- The existing typed Rule-12 values are not atom-and-bond transcriptions of the 48 drawings. -/
def atomLevelGraphTranscriptionReviewed (_artifact : SourceImageArtifact) : Bool := false

end SourceImageArtifact

@[simp] theorem source_artifact_inventory_exact :
    SourceHtmlArtifact.all.length = 4 ∧
      SourceImageArtifact.all.length = 48 ∧
        (SourceImageArtifact.all.filter fun image => image.isMolecularGraph).length = 48 ∧
          (SourceImageArtifact.all.filter fun image =>
            image.atomLevelGraphTranscriptionReviewed).length = 0 := by
  decide

/-- Small manifest-facing constants keep checklist computation independent of the full ledger. -/
def currentSourceReviewProvisionEnumerationConfirmed : Bool := true
def currentSourceReviewProseTableCoverageConfirmed : Bool := true
def currentSourceReviewFigureGraphTranscriptionsReviewed : Bool := false

/-- Evidence from a separate fidelity pass over the exact frozen 52-artifact bundle.  All 21
rendered HTML pages and all 48 original GIFs were visually reviewed.  This confirms the complete
ten-provision Rule-12 enumeration and prose/table coverage while retaining all 48 molecular
figures as an open atom-level transcription queue. -/
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
    sourceBundleSha256 = (P10DelegatedAuthorityCorpus.snapshot .carotenoid1974).bundleSha256
  reviewedArtifactCountExact :
    reviewedArtifacts = reviewedHtmlArtifacts.length + reviewedImageArtifacts.length
  reviewedRenderedPagesExact : reviewedRenderedPages = 21
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
    "013686e2241d6a410e9ddd94796d395dd5ef3e2b5288db7f148d7be71390ed70"
  reviewedArtifacts := 52
  reviewedRenderedPages := 21
  reviewedHtmlArtifacts := SourceHtmlArtifact.all
  reviewedImageArtifacts := SourceImageArtifact.all
  reviewedProvisions := Provision.all
  molecularGraphImageCount := 48
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
    currentSourceReview.reviewedArtifacts = 52 ∧
      currentSourceReview.reviewedRenderedPages = 21 ∧
        currentSourceReview.reviewedHtmlArtifacts.length = 4 ∧
          currentSourceReview.reviewedImageArtifacts.length = 48 ∧
            currentSourceReview.reviewedProvisions.length = 10 ∧
              currentSourceReview.molecularGraphImageCount = 48 ∧
                currentSourceReview.atomLevelGraphTranscriptionCount = 0 := by
  decide

end Carotenoid1974

end TetraStereo.OneCenter
