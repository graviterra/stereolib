import TetraStereo.OneCenter.CIPAuthoritativeConformance
import TetraStereo.OneCenter.Appendix3NormativeAudit
import TetraStereo.OneCenter.GraphicalRepresentationST0
import TetraStereo.OneCenter.GraphicalRepresentationST1Tetrahedral
import TetraStereo.OneCenter.GraphicalRepresentationST1Special
import TetraStereo.OneCenter.GraphicalRepresentationST2
import TetraStereo.OneCenter.GraphicalRepresentationST3to6
import TetraStereo.OneCenter.P10NormativeAudit
import TetraStereo.OneCenter.P10DelegatedAuthorityCorpus
import TetraStereo.OneCenter.P101NaturalProductSemantics
import TetraStereo.OneCenter.P102CarbohydrateSemantics
import TetraStereo.OneCenter.P103to107BiochemicalSemantics
import TetraStereo.OneCenter.CarotenoidStereochemistrySemantics
import TetraStereo.OneCenter.CyclitolStereochemistrySemantics
import TetraStereo.OneCenter.NucleicAcidStereochemistrySemantics
import TetraStereo.OneCenter.LipidStereochemistrySemantics
import TetraStereo.OneCenter.GlycolipidStereochemistrySemantics
import TetraStereo.OneCenter.AminoAcidPeptideStereochemistrySemantics
import TetraStereo.OneCenter.CarbohydrateFoundationStereochemistrySemantics
import TetraStereo.OneCenter.CarbohydrateNamedParentStereochemistrySemantics
import TetraStereo.OneCenter.CarbohydrateScopeParentChoiceSemantics
import TetraStereo.OneCenter.CarbohydrateDerivativeStereochemistrySemantics
import TetraStereo.OneCenter.CarbohydrateUnsaturatedBranchedStereochemistrySemantics
import TetraStereo.OneCenter.CarbohydrateAlditolAcidStereochemistrySemantics
import TetraStereo.OneCenter.CarbohydrateHeteroSubstitutionAnhydrideSemantics
import TetraStereo.OneCenter.CarbohydrateAcetalStereochemistrySemantics
import TetraStereo.OneCenter.CarbohydrateResidueIonStereochemistrySemantics
import TetraStereo.OneCenter.CarbohydrateGlycosideRingSystemSemantics
import TetraStereo.OneCenter.CarbohydrateOligosaccharidePolysaccharideSemantics
import TetraStereo.OneCenter.CarbohydrateAppendixErrataGlossarySemantics
import TetraStereo.OneCenter.CarbohydrateImageArtifactAudit
import TetraStereo.OneCenter.CarbohydrateImageTranscriptionContract
import TetraStereo.OneCenter.Carbohydrate1996NormativeAudit
import TetraStereo.OneCenter.RetinoidStereochemistrySemantics
import TetraStereo.OneCenter.Retinoid1981SourceAuditLedger
import TetraStereo.OneCenter.SteroidStereochemistrySemantics
import TetraStereo.OneCenter.P90Scope
import TetraStereo.OneCenter.P91DescriptorSyntax
import TetraStereo.OneCenter.P92StereogenicUnitSemantics
import TetraStereo.OneCenter.P93AcyclicConfiguration
import TetraStereo.OneCenter.P93CyclicConfiguration
import TetraStereo.OneCenter.P93GeneralConfiguration
import TetraStereo.OneCenter.P93NoncarbonTetrahedra
import TetraStereo.OneCenter.P94Conformation
import TetraStereo.OneCenter.PolyhedralConfiguration
import TetraStereo.OneCenter.IR9PolyhedralSemantics
import TetraStereo.OneCenter.GeometryAnnotatedCIPConformance
import TetraStereo.OneCenter.CIPRule2MassData

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Machine-readable IUPAC normative manifest

This module is the coverage spine for the complete-authority theorem.  It intentionally separates
source coverage from implementation coverage: enumerating a provision does not prove that its prose
was transcribed correctly, and a primitive conformance proof does not prove its use at every
molecular occurrence.

The manifest is frozen at the granularity at which an end-to-end proof obligation can fail.  In
particular, hierarchical-digraph construction, stereogenic-unit perception, geometry
interpretation, and final descriptor conversion are not hidden under the eight sequence-rule names.
-/

/-- Versioned normative sources required by complete stereodescriptor assignment. -/
inductive IUPACNormativeSource where
  | blueBook2013P9
  | blueBook2013P10
  | blueBook2013Appendix3
  | graphicalRepresentation2006
  | redBook2005IR9
  | periodicTable2022
  | atomicWeights2021
  | atomicMasses2020
  | steroidRecommendations1989
  | carotenoidRules1974
  | retinoidRecommendations1981
  | carbohydrateRecommendations1996
  | aminoAcidPeptideRecommendations1983
  | cyclitolRecommendations1973
  | nucleicAcidRecommendations1970
  | lipidRecommendations1976
  | glycolipidRecommendations1997
  deriving DecidableEq, Repr

namespace IUPACNormativeSource

def title : IUPACNormativeSource → String
  | .blueBook2013P9 =>
      "Nomenclature of Organic Chemistry, IUPAC Recommendations and Preferred Names 2013, P-9"
  | .blueBook2013P10 =>
      "Nomenclature of Organic Chemistry, IUPAC Recommendations and Preferred Names 2013, P-10"
  | .blueBook2013Appendix3 =>
      "Nomenclature of Organic Chemistry, IUPAC Recommendations and Preferred Names 2013, Appendix 3"
  | .graphicalRepresentation2006 =>
      "Graphical Representation of Stereochemical Configuration, IUPAC Recommendations 2006"
  | .redBook2005IR9 =>
      "Nomenclature of Inorganic Chemistry, IUPAC Recommendations 2005, IR-9"
  | .periodicTable2022 => "IUPAC Periodic Table of the Elements, release 4 May 2022"
  | .atomicWeights2021 => "CIAAW Standard Atomic Weights 2021"
  | .atomicMasses2020 =>
      "CIAAW IUPAC atomic masses, AME records through AME-2020, 17 March 2021"
  | .steroidRecommendations1989 =>
      P10DelegatedAuthorityCorpus.Document.title .steroid1989
  | .carotenoidRules1974 =>
      P10DelegatedAuthorityCorpus.Document.title .carotenoid1974
  | .retinoidRecommendations1981 =>
      P10DelegatedAuthorityCorpus.Document.title .retinoid1981
  | .carbohydrateRecommendations1996 =>
      P10DelegatedAuthorityCorpus.Document.title .carbohydrate1996
  | .aminoAcidPeptideRecommendations1983 =>
      P10DelegatedAuthorityCorpus.Document.title .aminoAcidPeptide1983
  | .cyclitolRecommendations1973 =>
      P10DelegatedAuthorityCorpus.Document.title .cyclitol1973
  | .nucleicAcidRecommendations1970 =>
      P10DelegatedAuthorityCorpus.Document.title .nucleicAcid1970
  | .lipidRecommendations1976 =>
      P10DelegatedAuthorityCorpus.Document.title .lipid1976
  | .glycolipidRecommendations1997 =>
      P10DelegatedAuthorityCorpus.Document.title .glycolipid1997

def url : IUPACNormativeSource → String
  | .blueBook2013P9 => "https://iupac.qmul.ac.uk/BlueBook/PDF/P9.pdf"
  | .blueBook2013P10 => "https://iupac.qmul.ac.uk/BlueBook/PDF/P10.pdf"
  | .blueBook2013Appendix3 => "https://iupac.qmul.ac.uk/BlueBook/PDF/Papp3.pdf"
  | .graphicalRepresentation2006 => "https://iupac.qmul.ac.uk/drawing/stereo.html"
  | .redBook2005IR9 =>
      "https://iupac.org/cms/wp-content/uploads/2016/07/Red_Book_2005.pdf"
  | .periodicTable2022 =>
      "https://iupac.org/wp-content/uploads/2022/07/IUPAC_Periodic_Table-04May22_CRA.pdf"
  | .atomicWeights2021 => "https://doi.org/10.1515/pac-2019-0603"
  | .atomicMasses2020 => "https://ciaaw.org/data/IUPAC-atomic-masses.csv"
  | .steroidRecommendations1989 =>
      (P10DelegatedAuthorityCorpus.snapshot .steroid1989).rootUrl
  | .carotenoidRules1974 =>
      (P10DelegatedAuthorityCorpus.snapshot .carotenoid1974).rootUrl
  | .retinoidRecommendations1981 =>
      (P10DelegatedAuthorityCorpus.snapshot .retinoid1981).rootUrl
  | .carbohydrateRecommendations1996 =>
      (P10DelegatedAuthorityCorpus.snapshot .carbohydrate1996).rootUrl
  | .aminoAcidPeptideRecommendations1983 =>
      (P10DelegatedAuthorityCorpus.snapshot .aminoAcidPeptide1983).rootUrl
  | .cyclitolRecommendations1973 =>
      (P10DelegatedAuthorityCorpus.snapshot .cyclitol1973).rootUrl
  | .nucleicAcidRecommendations1970 =>
      (P10DelegatedAuthorityCorpus.snapshot .nucleicAcid1970).rootUrl
  | .lipidRecommendations1976 =>
      (P10DelegatedAuthorityCorpus.snapshot .lipid1976).rootUrl
  | .glycolipidRecommendations1997 =>
      (P10DelegatedAuthorityCorpus.snapshot .glycolipid1997).rootUrl

/-- Retrieval root used for the digest.  For `responseBytes` sources this is the exact byte stream.
For `pathSha256Bundle` sources it is the root of the compound web snapshot described by
`P10DelegatedAuthorityCorpus.snapshot`.  The atomic-weight report's canonical DOI is retained by
`url`; its publisher-version bytes are mirrored by the National Research Council of Canada, one of
the report authors' institutions. -/
def digestUrl : IUPACNormativeSource → String
  | .atomicWeights2021 =>
      "https://nrc-publications.canada.ca/eng/view/ft/" ++
        "?id=a554b02a-d23d-4247-977b-2af87b2220e1"
  | source => source.url

inductive DigestKind where
  | responseBytes
  | pathSha256Bundle
  deriving DecidableEq, Repr

def digestKind : IUPACNormativeSource → DigestKind
  | .steroidRecommendations1989
  | .carotenoidRules1974
  | .retinoidRecommendations1981
  | .carbohydrateRecommendations1996
  | .aminoAcidPeptideRecommendations1983
  | .cyclitolRecommendations1973
  | .nucleicAcidRecommendations1970
  | .lipidRecommendations1976
  | .glycolipidRecommendations1997 => .pathSha256Bundle
  | _ => .responseBytes

/-- Content digests captured on 2026-08-11, except P-10 which was refreshed from the current
official Version-3 response on 2026-08-29. The digest kind determines whether this is a direct
response hash or the compound path-and-content digest defined in the delegated-corpus module. -/
def sha256? : IUPACNormativeSource → Option String
  | .blueBook2013P9 =>
      some "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  | .blueBook2013P10 =>
      some "e1185116ad0e61641832931ad87d333e14a8b37ce55e8a19e4570c4c1b42bedf"
  | .blueBook2013Appendix3 =>
      some "e7f9d689cb5bd19b3c7f30aab7f0df0a73865b6f11e9427e9580c2654a8d9043"
  | .graphicalRepresentation2006 =>
      some "b702d3493a3a64f4090cf75c697301d56ff3b5ae7861dc97d604286b7cd51cee"
  | .periodicTable2022 =>
      some "ef6ca2f6d46554f96e30ad3a60693d6630fe45ad81ce83cb14e508c6cbb7d3b3"
  | .redBook2005IR9 =>
      some "3595c86a1b288b82be6d74061315592b89fe3eb17ffa80bb3df3e970e622890f"
  | .atomicWeights2021 =>
      some "4aba4ddd55523e64039aee076295fe0f9b1bb16576a0bae6111c43dbd0e97318"
  | .atomicMasses2020 =>
      some "26a7b63e27871ac7752b0244ce00b3981cb5e4bee377569ff4f9bb6dfecea732"
  | .steroidRecommendations1989 =>
      some (P10DelegatedAuthorityCorpus.snapshot .steroid1989).bundleSha256
  | .carotenoidRules1974 =>
      some (P10DelegatedAuthorityCorpus.snapshot .carotenoid1974).bundleSha256
  | .retinoidRecommendations1981 =>
      some (P10DelegatedAuthorityCorpus.snapshot .retinoid1981).bundleSha256
  | .carbohydrateRecommendations1996 =>
      some (P10DelegatedAuthorityCorpus.snapshot .carbohydrate1996).bundleSha256
  | .aminoAcidPeptideRecommendations1983 =>
      some (P10DelegatedAuthorityCorpus.snapshot .aminoAcidPeptide1983).bundleSha256
  | .cyclitolRecommendations1973 =>
      some (P10DelegatedAuthorityCorpus.snapshot .cyclitol1973).bundleSha256
  | .nucleicAcidRecommendations1970 =>
      some (P10DelegatedAuthorityCorpus.snapshot .nucleicAcid1970).bundleSha256
  | .lipidRecommendations1976 =>
      some (P10DelegatedAuthorityCorpus.snapshot .lipid1976).bundleSha256
  | .glycolipidRecommendations1997 =>
      some (P10DelegatedAuthorityCorpus.snapshot .glycolipid1997).bundleSha256

def all : List IUPACNormativeSource :=
  [ .blueBook2013P9
  , .blueBook2013P10
  , .blueBook2013Appendix3
  , .graphicalRepresentation2006
  , .redBook2005IR9
  , .periodicTable2022
  , .atomicWeights2021
  , .atomicMasses2020
  , .steroidRecommendations1989
  , .carotenoidRules1974
  , .retinoidRecommendations1981
  , .carbohydrateRecommendations1996
  , .aminoAcidPeptideRecommendations1983
  , .cyclitolRecommendations1973
  , .nucleicAcidRecommendations1970
  , .lipidRecommendations1976
  , .glycolipidRecommendations1997
  ]

@[simp] theorem mem_all (source : IUPACNormativeSource) : source ∈ all := by
  cases source <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 17 := by decide

/-- Every source edition in the frozen corpus now has reproducible publication bytes. -/
theorem every_source_has_digest (source : IUPACNormativeSource) : source.sha256?.isSome := by
  cases source <;> rfl

/-- The manifest and the generated Rule-2 table name the identical byte-verified periodic-table
artifact, preventing provenance metadata from drifting away from executable data. -/
theorem periodic_table_digest_matches_rule2_mass_data :
    sha256? .periodicTable2022 = some CIPRule2MassData.periodicTable2022.sha256 := by
  decide

/-- The manifest and the generated Rule-2 table name the identical byte-verified AME CSV. -/
theorem isotope_mass_digest_matches_rule2_mass_data :
    sha256? .atomicMasses2020 = some CIPRule2MassData.isotopeMasses2020.sha256 := by
  decide




inductive ProvisionAuditRequirement where
  | provisionEnumerationConfirmed
  | proseTableCoverageConfirmed
  | figureGraphTranscriptionsReviewed
  | delegatedAuthorityClosureConfirmed
  deriving DecidableEq, Repr

namespace ProvisionAuditRequirement

def all : List ProvisionAuditRequirement :=
  [ .provisionEnumerationConfirmed
  , .proseTableCoverageConfirmed
  , .figureGraphTranscriptionsReviewed
  , .delegatedAuthorityClosureConfirmed ]

@[simp] theorem mem_all (requirement : ProvisionAuditRequirement) : requirement ∈ all := by
  cases requirement <;> simp [all]

theorem all_nodup : all.Nodup := by decide

end ProvisionAuditRequirement



structure ProvisionAuditChecklist where
  provisionEnumerationConfirmed : Bool
  proseTableCoverageConfirmed : Bool
  figureGraphTranscriptionsReviewed : Bool
  delegatedAuthorityClosureConfirmed : Bool
  deriving DecidableEq, Repr

namespace ProvisionAuditChecklist

def allConfirmed : ProvisionAuditChecklist where
  provisionEnumerationConfirmed := true
  proseTableCoverageConfirmed := true
  figureGraphTranscriptionsReviewed := true
  delegatedAuthorityClosureConfirmed := true

def requirementConfirmed? (checklist : ProvisionAuditChecklist) :
    ProvisionAuditRequirement → Bool
  | .provisionEnumerationConfirmed => checklist.provisionEnumerationConfirmed
  | .proseTableCoverageConfirmed => checklist.proseTableCoverageConfirmed
  | .figureGraphTranscriptionsReviewed => checklist.figureGraphTranscriptionsReviewed
  | .delegatedAuthorityClosureConfirmed => checklist.delegatedAuthorityClosureConfirmed

/-- Exact flip conditions still open for one source. -/
def openRequirements (checklist : ProvisionAuditChecklist) :
    List ProvisionAuditRequirement :=
  ProvisionAuditRequirement.all.filter fun requirement =>
    !checklist.requirementConfirmed? requirement

def Complete (checklist : ProvisionAuditChecklist) : Prop :=
  checklist.provisionEnumerationConfirmed = true ∧
    checklist.proseTableCoverageConfirmed = true ∧
    checklist.figureGraphTranscriptionsReviewed = true ∧
    checklist.delegatedAuthorityClosureConfirmed = true

theorem complete_iff_no_open_requirements (checklist : ProvisionAuditChecklist) :
    checklist.Complete ↔ checklist.openRequirements = [] := by
  cases checklist with
  | mk enumeration prose figures delegated =>
      cases enumeration <;> cases prose <;> cases figures <;> cases delegated <;>
        simp [Complete, openRequirements, ProvisionAuditRequirement.all,
          requirementConfirmed?]

end ProvisionAuditChecklist





















def currentProvisionAuditChecklist : IUPACNormativeSource → ProvisionAuditChecklist
  | .blueBook2013P10 =>
      ⟨ BlueBookP10Audit.currentSourceReviewProvisionEnumerationConfirmed
      , BlueBookP10Audit.currentSourceReviewProseTableCoverageConfirmed
      , BlueBookP10Audit.currentSourceReviewFigureGraphTranscriptionsReviewed
      , true ⟩
  | .blueBook2013Appendix3 =>
      ⟨ BlueBookAppendix3Audit.currentSourceReviewProvisionEnumerationConfirmed
      , BlueBookAppendix3Audit.currentSourceReviewProseTableCoverageConfirmed
      , BlueBookAppendix3Audit.currentSourceReviewFigureGraphTranscriptionsReviewed
      , true ⟩
  | .carbohydrateRecommendations1996 =>
      ⟨ Carbohydrate1996SourceReview.currentSourceReviewProvisionEnumerationConfirmed
      , Carbohydrate1996SourceReview.currentSourceReviewProseTableCoverageConfirmed
      , Carbohydrate1996SourceReview.currentSourceReviewFigureGraphTranscriptionsReviewed
      , true ⟩
  | .glycolipidRecommendations1997 =>
      ⟨ Glycolipid1997.currentTextualSourceReview.provisionEnumerationConfirmed
      , Glycolipid1997.currentTextualSourceReview.proseTableCoverageConfirmed
      , Glycolipid1997.currentTextualSourceReview.figureGraphReviewIssued
      , true ⟩
  | .nucleicAcidRecommendations1970 =>
      ⟨ NucleicAcid1970.currentSourceReviewProvisionEnumerationConfirmed
      , NucleicAcid1970.currentSourceReviewProseTableCoverageConfirmed
      , NucleicAcid1970.currentSourceReviewFigureGraphTranscriptionsReviewed
      , true ⟩
  | .lipidRecommendations1976 =>
      ⟨ Lipid1976.currentSourceReviewProvisionEnumerationConfirmed
      , Lipid1976.currentSourceReviewProseTableCoverageConfirmed
      , Lipid1976.currentSourceReviewFigureGraphTranscriptionsReviewed
      , true ⟩
  | .cyclitolRecommendations1973 =>
      ⟨ Cyclitol1973.currentSourceReviewProvisionEnumerationConfirmed
      , Cyclitol1973.currentSourceReviewProseTableCoverageConfirmed
      , Cyclitol1973.currentSourceReviewFigureGraphTranscriptionsReviewed
      , true ⟩
  | .carotenoidRules1974 =>
      ⟨ Carotenoid1974.currentSourceReviewProvisionEnumerationConfirmed
      , Carotenoid1974.currentSourceReviewProseTableCoverageConfirmed
      , Carotenoid1974.currentSourceReviewFigureGraphTranscriptionsReviewed
      , true ⟩
  | .steroidRecommendations1989 =>
      ⟨ Steroid1989.currentSourceReviewProvisionEnumerationConfirmed
      , Steroid1989.currentSourceReviewProseTableCoverageConfirmed
      , Steroid1989.currentSourceReviewFigureGraphTranscriptionsReviewed
      , true ⟩
  | .aminoAcidPeptideRecommendations1983 =>
      ⟨ AminoAcidPeptide1983.currentSourceReviewProvisionEnumerationConfirmed
      , AminoAcidPeptide1983.currentSourceReviewProseTableCoverageConfirmed
      , AminoAcidPeptide1983.currentSourceReviewFigureGraphTranscriptionsReviewed
      , true ⟩
  | .retinoidRecommendations1981 =>
      ⟨ Retinoid1981.SourceAudit.Ledger.currentAutomatedProseTableInspection.provisionEnumerationConfirmed
      , Retinoid1981.SourceAudit.Ledger.currentAutomatedProseTableInspection.proseTableCoverageConfirmed
      , Retinoid1981.SourceAudit.Ledger.currentAutomatedProseTableInspection.figureGraphTranscriptionsReviewed
      , true ⟩
  | _ => ProvisionAuditChecklist.allConfirmed

def currentOpenProvisionAuditRequirements (source : IUPACNormativeSource) :
    List ProvisionAuditRequirement :=
  (currentProvisionAuditChecklist source).openRequirements

/-- Source-section auditing is deliberately separate from byte provenance. Unlike the former
literal-false gate, this proposition flips exactly when every named checklist requirement is
confirmed. -/
def ProvisionAuditComplete (source : IUPACNormativeSource) : Prop :=
  (currentProvisionAuditChecklist source).Complete

theorem provisionAuditComplete_iff_no_open_requirements
    (source : IUPACNormativeSource) :
    ProvisionAuditComplete source ↔ currentOpenProvisionAuditRequirements source = [] :=
  ProvisionAuditChecklist.complete_iff_no_open_requirements _




theorem provisionAuditIncomplete_of_figure_review_open
    (source : IUPACNormativeSource)
    (figureReviewOpen :
      (currentProvisionAuditChecklist source).figureGraphTranscriptionsReviewed = false) :
    ¬ProvisionAuditComplete source := by
  intro complete
  have impossible : false = true := figureReviewOpen.symm.trans complete.2.2.1
  exact Bool.noConfusion impossible


def currentIncompleteProvisionAuditSources : List IUPACNormativeSource :=
  all.filter fun source => !(currentOpenProvisionAuditRequirements source).isEmpty

theorem currentIncompleteProvisionAuditSources_exact :
    currentIncompleteProvisionAuditSources =
      [ .blueBook2013P10
      , .blueBook2013Appendix3
      , .steroidRecommendations1989
      , .carotenoidRules1974
      , .retinoidRecommendations1981
      , .carbohydrateRecommendations1996
      , .aminoAcidPeptideRecommendations1983
      , .cyclitolRecommendations1973
      , .lipidRecommendations1976
      , .glycolipidRecommendations1997 ] := by
  decide

@[simp] theorem currentIncompleteProvisionAuditSourceCount :
    currentIncompleteProvisionAuditSources.length = 10 := by
  rw [currentIncompleteProvisionAuditSources_exact]
  decide

theorem mem_currentIncompleteProvisionAuditSources_iff
    (source : IUPACNormativeSource) :
    source ∈ currentIncompleteProvisionAuditSources ↔ ¬ProvisionAuditComplete source := by
  cases source <;>
    simp [currentIncompleteProvisionAuditSources, all,
      currentOpenProvisionAuditRequirements, currentProvisionAuditChecklist,
      ProvisionAuditComplete, ProvisionAuditChecklist.Complete,
      ProvisionAuditChecklist.openRequirements, ProvisionAuditRequirement.all,
      ProvisionAuditChecklist.requirementConfirmed?]

theorem current_source_provision_audit_incomplete :
    ¬(∀ source, IUPACNormativeSource.ProvisionAuditComplete source) := by
  intro complete
  have := complete IUPACNormativeSource.blueBook2013P10
  simp [ProvisionAuditComplete, currentProvisionAuditChecklist,
    ProvisionAuditChecklist.Complete,
    BlueBookP10Audit.currentSourceReviewProvisionEnumerationConfirmed,
    BlueBookP10Audit.currentSourceReviewProseTableCoverageConfirmed,
    BlueBookP10Audit.currentSourceReviewFigureGraphTranscriptionsReviewed] at this

/-- Exact bridge from the nine specialist publications into the global source manifest. -/
def ofDelegatedDocument : P10DelegatedAuthorityCorpus.Document → IUPACNormativeSource
  | .steroid1989 => .steroidRecommendations1989
  | .carotenoid1974 => .carotenoidRules1974
  | .retinoid1981 => .retinoidRecommendations1981
  | .carbohydrate1996 => .carbohydrateRecommendations1996
  | .aminoAcidPeptide1983 => .aminoAcidPeptideRecommendations1983
  | .cyclitol1973 => .cyclitolRecommendations1973
  | .nucleicAcid1970 => .nucleicAcidRecommendations1970
  | .lipid1976 => .lipidRecommendations1976
  | .glycolipid1997 => .glycolipidRecommendations1997

@[simp] theorem delegated_document_source_mem_all
    (document : P10DelegatedAuthorityCorpus.Document) : ofDelegatedDocument document ∈ all := by
  cases document <;> simp [ofDelegatedDocument, all]

@[simp] theorem delegated_document_provision_audit_complete_iff
    (document : P10DelegatedAuthorityCorpus.Document) :
    ProvisionAuditComplete (ofDelegatedDocument document) ↔
      document = .nucleicAcid1970 := by
  cases document <;> simp [ofDelegatedDocument, ProvisionAuditComplete,
    currentProvisionAuditChecklist, ProvisionAuditChecklist.Complete,
    Glycolipid1997.currentTextualSourceReview.provisionEnumerationConfirmedExact,
    Glycolipid1997.currentTextualSourceReview.proseTableCoverageConfirmedExact,
    Glycolipid1997.currentTextualSourceReview.figureGraphReviewNotIssued,
    NucleicAcid1970.currentSourceReviewProvisionEnumerationConfirmed,
    NucleicAcid1970.currentSourceReviewProseTableCoverageConfirmed,
    NucleicAcid1970.currentSourceReviewFigureGraphTranscriptionsReviewed,
    Lipid1976.currentSourceReviewProvisionEnumerationConfirmed,
    Lipid1976.currentSourceReviewProseTableCoverageConfirmed,
    Lipid1976.currentSourceReviewFigureGraphTranscriptionsReviewed,
    Cyclitol1973.currentSourceReviewProvisionEnumerationConfirmed,
    Cyclitol1973.currentSourceReviewProseTableCoverageConfirmed,
    Cyclitol1973.currentSourceReviewFigureGraphTranscriptionsReviewed,
    Carotenoid1974.currentSourceReviewProvisionEnumerationConfirmed,
    Carotenoid1974.currentSourceReviewProseTableCoverageConfirmed,
    Carotenoid1974.currentSourceReviewFigureGraphTranscriptionsReviewed,
    Steroid1989.currentSourceReviewProvisionEnumerationConfirmed,
    Steroid1989.currentSourceReviewProseTableCoverageConfirmed,
    Steroid1989.currentSourceReviewFigureGraphTranscriptionsReviewed,
    AminoAcidPeptide1983.currentSourceReviewProvisionEnumerationConfirmed,
    AminoAcidPeptide1983.currentSourceReviewProseTableCoverageConfirmed,
    AminoAcidPeptide1983.currentSourceReviewFigureGraphTranscriptionsReviewed,
    Carbohydrate1996SourceReview.currentSourceReviewProvisionEnumerationConfirmed,
    Carbohydrate1996SourceReview.currentSourceReviewProseTableCoverageConfirmed,
    Carbohydrate1996SourceReview.currentSourceReviewFigureGraphTranscriptionsReviewed]

/-- Global source-manifest view of a P-10 dependency.  The combined carotenoid/retinoid category
has two sources; every other dependency category has exactly one. -/
def ofP10ExternalAuthority : BlueBookP10Audit.ExternalAuthority → List IUPACNormativeSource
  | .blueBookAppendix3 => [.blueBook2013Appendix3]
  | .steroidNomenclature => [.steroidRecommendations1989]
  | .carotenoidAndRetinoidNomenclature => [.carotenoidRules1974, .retinoidRecommendations1981]
  | .carbohydrateNomenclature => [.carbohydrateRecommendations1996]
  | .aminoAcidAndPeptideNomenclature => [.aminoAcidPeptideRecommendations1983]
  | .cyclitolNomenclature => [.cyclitolRecommendations1973]
  | .nucleicAcidNomenclature => [.nucleicAcidRecommendations1970]
  | .lipidNomenclature => [.lipidRecommendations1976]
  | .glycolipidNomenclature => [.glycolipidRecommendations1997]

@[simp] theorem p10_external_authority_sources_nonempty
    (authority : BlueBookP10Audit.ExternalAuthority) :
    (ofP10ExternalAuthority authority).length > 0 := by
  cases authority <;> decide

theorem p10_external_authority_source_mem_all
    (authority : BlueBookP10Audit.ExternalAuthority)
    (source : IUPACNormativeSource)
    (_member : source ∈ ofP10ExternalAuthority authority) : source ∈ all :=
  mem_all source

end IUPACNormativeSource

private instance : Fintype BlueBookP10Audit.Provision :=
  Fintype.ofList BlueBookP10Audit.Provision.all (by intro provision; simp)

private instance : Fintype BlueBookAppendix3Audit.Provision :=
  Fintype.ofList BlueBookAppendix3Audit.Provision.all (by intro provision; simp)

private instance : Fintype Retinoid1981.Provision :=
  Fintype.ofList Retinoid1981.Provision.all (by intro provision; simp)

private instance : Fintype Carotenoid1974.Provision :=
  Fintype.ofList Carotenoid1974.Provision.all (by intro provision; simp)

private instance : Fintype Steroid1989.Provision :=
  Fintype.ofList Steroid1989.Provision.all (by intro provision; simp)

private instance : Fintype Cyclitol1973.Provision :=
  Fintype.ofList Cyclitol1973.Provision.all (by intro provision; simp)

private instance : Fintype NucleicAcid1970.Provision :=
  Fintype.ofList NucleicAcid1970.Provision.all (by intro provision; simp)

private instance : Fintype Lipid1976.Provision :=
  Fintype.ofList Lipid1976.Provision.all (by intro provision; simp)

private instance : Fintype Glycolipid1997.Provision :=
  Fintype.ofList Glycolipid1997.Provision.all (by intro provision; simp)

private instance : Fintype AminoAcidPeptide1983.Provision :=
  Fintype.ofList AminoAcidPeptide1983.Provision.all (by intro provision; simp)

private instance : Fintype Carbohydrate1996Foundation.Provision :=
  Fintype.ofList Carbohydrate1996Foundation.Provision.all (by intro provision; simp)

private instance : Fintype Carbohydrate1996NamedParents.Provision :=
  Fintype.ofList Carbohydrate1996NamedParents.Provision.all (by intro provision; simp)

private instance : Fintype Carbohydrate1996ScopeParent.Provision :=
  Fintype.ofList Carbohydrate1996ScopeParent.Provision.all (by intro provision; simp)

private instance : Fintype Carbohydrate1996Derivatives.Provision :=
  Fintype.ofList Carbohydrate1996Derivatives.Provision.all (by intro provision; simp)

private instance : Fintype Carbohydrate1996UnsaturatedBranched.Provision :=
  Fintype.ofList Carbohydrate1996UnsaturatedBranched.Provision.all (by intro provision; simp)

private instance : Fintype Carbohydrate1996AlditolsAcids.Provision :=
  Fintype.ofList Carbohydrate1996AlditolsAcids.Provision.all (by intro provision; simp)

private instance : Fintype Carbohydrate1996HeteroSubstitutionAnhydride.Provision :=
  Fintype.ofList Carbohydrate1996HeteroSubstitutionAnhydride.Provision.all
    (by intro provision; simp)

private instance : Fintype Carbohydrate1996Acetals.Provision :=
  Fintype.ofList Carbohydrate1996Acetals.Provision.all (by intro provision; simp)

private instance : Fintype Carbohydrate1996ResiduesIons.Provision :=
  Fintype.ofList Carbohydrate1996ResiduesIons.Provision.all (by intro provision; simp)

private instance : Fintype Carbohydrate1996GlycosidesRings.Provision :=
  Fintype.ofList Carbohydrate1996GlycosidesRings.Provision.all (by intro provision; simp)

private instance : Fintype Carbohydrate1996OligosaccharidesPolysaccharides.Provision :=
  Fintype.ofList Carbohydrate1996OligosaccharidesPolysaccharides.Provision.all
    (by intro provision; simp)

private instance : Fintype Carbohydrate1996AppendixErrataGlossary.Provision :=
  Fintype.ofList Carbohydrate1996AppendixErrataGlossary.Provision.all
    (by intro provision; simp)

private instance : Fintype Carbohydrate1996ImageAudit.Provision :=
  Fintype.ofList Carbohydrate1996ImageAudit.Provision.all (by intro provision; simp)




inductive IUPACNormativeProvision where
  | p10 (provision : BlueBookP10Audit.Provision)
  | appendix3 (provision : BlueBookAppendix3Audit.Provision)
  | retinoid1981 (provision : Retinoid1981.Provision)
  | carotenoid1974 (provision : Carotenoid1974.Provision)
  | steroid1989 (provision : Steroid1989.Provision)
  | cyclitol1973 (provision : Cyclitol1973.Provision)
  | nucleicAcid1970 (provision : NucleicAcid1970.Provision)
  | lipid1976 (provision : Lipid1976.Provision)
  | glycolipid1997 (provision : Glycolipid1997.Provision)
  | aminoAcidPeptide1983 (provision : AminoAcidPeptide1983.Provision)
  | carbohydrate1996Foundation (provision : Carbohydrate1996Foundation.Provision)
  | carbohydrate1996NamedParents (provision : Carbohydrate1996NamedParents.Provision)
  | carbohydrate1996ScopeParent (provision : Carbohydrate1996ScopeParent.Provision)
  | carbohydrate1996Derivatives (provision : Carbohydrate1996Derivatives.Provision)
  | carbohydrate1996UnsaturatedBranched
      (provision : Carbohydrate1996UnsaturatedBranched.Provision)
  | carbohydrate1996AlditolsAcids (provision : Carbohydrate1996AlditolsAcids.Provision)
  | carbohydrate1996HeteroSubstitutionAnhydride
      (provision : Carbohydrate1996HeteroSubstitutionAnhydride.Provision)
  | carbohydrate1996Acetals (provision : Carbohydrate1996Acetals.Provision)
  | carbohydrate1996ResiduesIons (provision : Carbohydrate1996ResiduesIons.Provision)
  | carbohydrate1996GlycosidesRings (provision : Carbohydrate1996GlycosidesRings.Provision)
  | carbohydrate1996OligosaccharidesPolysaccharides
      (provision : Carbohydrate1996OligosaccharidesPolysaccharides.Provision)
  | carbohydrate1996AppendixErrataGlossary
      (provision : Carbohydrate1996AppendixErrataGlossary.Provision)
  | carbohydrate1996ImageArtifact (provision : Carbohydrate1996ImageAudit.Provision)
  | p90ScopeAndTerminology
  | p91ConfigurationDepiction
  | p91DescriptorVocabulary
  | p91OtherAcceptableDescriptors
  | p91SubstitutiveNomenclatureDescriptors
  | p91NaturalProductDescriptors
  | p91DescriptorOmission
  | p91NamingOfStereoisomers
  | p92StereogenicUnits
  | p92ChiralityDefinition
  | p92ChiralityCenterDefinition
  | p92ChiralityAxisDefinition
  | p92ChiralityPlaneDefinition
  | p92PseudoasymmetricUnitDefinition
  | p92CisTransDoubleBondUnitDefinition
  | p92EnantiomorphicDoubleBondUnitDefinition
  | p92BondingNumberScope
  | p92ChiralityRuleGeneral
  | p92CenterChiralityRule
  | p92AxisChiralityRule
  | p92PlaneChiralityRule
  | p92HelicityRule
  | p92HelicityAxis
  | p92HelicityPlane
  | p92RSMPDescriptorCorrespondence
  | p92SequenceRulePropertyClasses
  | p92SequenceRuleReflectionBehavior
  | p92LigandDentateKinds
  | p92SequenceRuleHierarchy
  | p92AcyclicDigraph
  | p92MultipleBondDigraph
  | p92CyclicDigraph
  | p92MancudeDigraph
  | p92SphereExploration
  | p92RuleExhaustivity
  | p92Rule1aAtomicNumber
  | p92Rule1aMultipleBondDuplicates
  | p92Rule1aMancude
  | p92Rule1aSaturatedCompounds
  | p92Rule1aDoubleTripleBonds
  | p92Rule1aSaturatedRings
  | p92Rule1bDuplicateProximity
  | p92Rule2IsotopeMass
  | p92Rule3Geometry
  | p92Rule3SeqCisTrans
  | p92Rule3Priority
  | p92Rule4aUnitKind
  | p92Rule4bLikeUnlike
  | p92Rule4bPairingMethodology
  | p92Rule4cPseudoasymmetry
  | p92Rule5Enantiomorph
  | p93OtherElementTetrahedra
  | p93AbsoluteConfiguration
  | p93RelativeConfiguration
  | p93MixedAbsoluteRelativeConfiguration
  | p93Racemates
  | p93Ambo
  | p93OtherElementGeneralMethodology
  | p93AzaniumPhosphanium
  | p93AminePhosphaneOxides
  | p93PhosphatesPhosphonates
  | p93SulfatesSulfonates
  | p93Group14Noncarbon
  | p93NontetrahedralGeneralMethodology
  | p93PolyhedralSymbols
  | p93PolyhedralGeometryRecognition
  | p93PolyhedralPriorityNumbering
  | p93TrigonalPyramid
  | p93TShape
  | p93SeeSaw
  | p93TrigonalBipyramid
  | p93SquarePyramid
  | p93Octahedron
  | p93PolyhedralChirality
  | p93AcyclicCenters
  | p93SingleAcyclicCenter
  | p93MultipleDescriptorsOneCenter
  | p93PrefixComponentCenters
  | p93OrdinaryDoubleBonds
  | p93DoubleBondEZCisTrans
  | p93MultipleDoubleBonds
  | p93HeteroatomDoubleBonds
  | p93EvenCumulenes
  | p93OddCumulenes
  | p93MultipleAcyclicStereogenicUnits
  | p93CyclicConfigurations
  | p93MonocyclicAbsoluteCenters
  | p93MonocyclicAchiralCenters
  | p93MonocyclicCisTrans
  | p93MonocyclicRCT
  | p93UnsaturatedMonocycles
  | p93CyclicDoubleBonds
  | p93ExocyclicDoubleBondEZ
  | p93ExocyclicDoubleBondOther
  | p93VonBaeyerCIPCenters
  | p93VonBaeyerEndoExoSynAnti
  | p93VonBaeyerCisTrans
  | p93VonBaeyerDoubleBonds
  | p93SpiroXabcd
  | p93SpiroXabab
  | p93SpiroDoubleBonds
  | p93SpiroNontetrahedralCenters
  | p93SpiroAxialChirality
  | p93FusedBridgedCIP
  | p93CisoidTransoid
  | p93CyclophanePlanes
  | p93CyclophaneCenters
  | p93CyclophaneDoubleBonds
  | p93FullereneGeneralMethodology
  | p93FullereneInherentParentChirality
  | p93FullereneInherentSubstitutionChirality
  | p93FullereneNoninherentSubstitutionChirality
  | p93FullereneChiralSubstituents
  | p93FullereneSuperimposedStereogenicElements
  | p93RingAssemblyAxes
  | p93RingAssemblyCenters
  | p93RingAssemblyDoubleBonds
  | p93CoupledRingChainConfigurations
  | p94ConformationDefinition
  | p94TorsionAngle
  | p94TorsionLonePairs
  | p94EclipsedStaggeredGauche
  | p94TrigonalConformations
  | p94SCisSTrans
  | p94Envelope
  | p94ChairBoatTwist
  | p94HalfChair
  | p94Crown
  | p94Tub
  | p94InOut
  | drawingOverview
  | drawingPlainBonds
  | drawingHashesDashesWedges
  | drawingWavyBonds
  | drawingStereobondsBetweenStereocenters
  | drawingAsterisks
  | drawingCIPStereodescriptors
  | drawingDiastereoisomerMixtures
  | drawingTetraFourExplicit01
  | drawingTetraFourExplicit02
  | drawingTetraFourExplicit03
  | drawingTetraFourExplicit04
  | drawingTetraFourExplicit05
  | drawingTetraFourExplicit06
  | drawingTetraFourExplicit07
  | drawingTetraFourExplicit08
  | drawingTetraFourExplicit09
  | drawingTetraFourExplicit10
  | drawingTetraFourExplicit11
  | drawingTetraFourExplicit12
  | drawingTetraFourExplicit13
  | drawingTetraFourExplicit14
  | drawingTetraFourExplicit15
  | drawingTetraFourExplicit16
  | drawingTetraFourExplicit17
  | drawingTetraFourExplicit18
  | drawingTetraFourExplicit19
  | drawingTetraFourExplicit20
  | drawingTetraThreeExplicit01
  | drawingTetraThreeExplicit02
  | drawingTetraThreeExplicit03
  | drawingTetraThreeExplicit04
  | drawingTetraThreeExplicit05
  | drawingTetraThreeExplicit06
  | drawingTetraThreeExplicit07
  | drawingTetraThreeExplicit08
  | drawingTetraThreeExplicit09
  | drawingTetraThreeExplicit10
  | drawingTetraThreeExplicit11
  | drawingTetraThreeExplicit12
  | drawingRingTwoBonds
  | drawingRingFusion
  | drawingBridgehead
  | drawingSpiroFusion
  | drawingReentrantTetrahedralCenters
  | drawingHigherOrderTetrahedralBonds
  | drawingEvenConsecutiveDoubleBonds
  | drawingHinderedBiaryls
  | drawingFischerProjections
  | drawingHaworthProjections
  | drawingMillsDepictions
  | drawingHDotDashCircle
  | drawingLinearGeometry
  | drawingAngularGeometry
  | drawingTShapedGeometry
  | drawingTrigonalPlanarGeometry
  | drawingTrigonalPyramidalGeometry
  | drawingSquarePlanarGeometry
  | drawingSquarePyramidalFourGeometry
  | drawingSeeSawGeometry
  | drawingTrigonalBipyramidalGeometry
  | drawingSquarePyramidalFiveGeometry
  | drawingOctahedralGeometry
  | drawingTrigonalPrismaticGeometry
  | drawingHigherCoordinationGeometry
  | drawingPerspectiveRestrictions
  | drawingPerspectiveInterpretation
  | drawingPerspectiveBoldBonds
  | drawingDoubleBondSubstituentPositioning
  | drawingOddConsecutiveDoubleBonds
  | drawingRingDoubleBonds
  | drawingUnspecifiedDoubleBondConfiguration
  | drawingImplicitDoubleBondSubstituents
  | drawingPlanarChirality
  | drawingHelicenes
  | drawingMobiusBands
  | drawingMolecularPropellers
  | drawingMixtureRepresentationGoals
  | drawingAsDrawnAbsoluteConfiguration
  | drawingMixtureExplanatoryText
  | drawingRacemicAndKnownProportions
  | drawingAvoidRacemateRelativeLabels
  | ir9PolyhedralConfiguration
  | ir9ConfigurationIntroduction
  | ir9PolyhedralSymbols
  | ir9GeometryChoice
  | ir9DiastereoisomerGeneral
  | ir9ConfigurationIndex
  | ir9SquarePlanar
  | ir9Octahedral
  | ir9SquarePyramidal
  | ir9Bipyramidal
  | ir9TShape
  | ir9SeeSaw
  | ir9AbsoluteConfigurationGeneral
  | ir9RSTetrahedral
  | ir9RSTrigonalPyramidal
  | ir9CAPolyhedral
  | ir9CATrigonalBipyramidal
  | ir9CASquarePyramidal
  | ir9CASeeSaw
  | ir9CAOctahedral
  | ir9CATrigonalPrismatic
  | ir9CAOtherBipyramidal
  | ir9SkewLines
  | ir9SkewLinesTrisBidentate
  | ir9SkewLinesBisBidentate
  | ir9SkewLinesChelateConformations
  | ir9LigandPriorityGeneral
  | ir9PriorityNumbers
  | ir9PrimingConvention
  | periodicAtomicNumbers
  | standardAtomicWeights
  | isotopeAtomicMasses
  deriving DecidableEq, Repr

namespace IUPACNormativeProvision

/-- Non-parameterized provisions in source order. -/
def coreProvisions : List IUPACNormativeProvision :=
  [ .p90ScopeAndTerminology
  , .p91ConfigurationDepiction
  , .p91DescriptorVocabulary
  , .p91OtherAcceptableDescriptors
  , .p91SubstitutiveNomenclatureDescriptors
  , .p91NaturalProductDescriptors
  , .p91DescriptorOmission
  , .p91NamingOfStereoisomers
  , .p92StereogenicUnits
  , .p92ChiralityDefinition
  , .p92ChiralityCenterDefinition
  , .p92ChiralityAxisDefinition
  , .p92ChiralityPlaneDefinition
  , .p92PseudoasymmetricUnitDefinition
  , .p92CisTransDoubleBondUnitDefinition
  , .p92EnantiomorphicDoubleBondUnitDefinition
  , .p92BondingNumberScope
  , .p92ChiralityRuleGeneral
  , .p92CenterChiralityRule
  , .p92AxisChiralityRule
  , .p92PlaneChiralityRule
  , .p92HelicityRule
  , .p92HelicityAxis
  , .p92HelicityPlane
  , .p92RSMPDescriptorCorrespondence
  , .p92SequenceRulePropertyClasses
  , .p92SequenceRuleReflectionBehavior
  , .p92LigandDentateKinds
  , .p92SequenceRuleHierarchy
  , .p92AcyclicDigraph
  , .p92MultipleBondDigraph
  , .p92CyclicDigraph
  , .p92MancudeDigraph
  , .p92SphereExploration
  , .p92RuleExhaustivity
  , .p92Rule1aAtomicNumber
  , .p92Rule1aMultipleBondDuplicates
  , .p92Rule1aMancude
  , .p92Rule1aSaturatedCompounds
  , .p92Rule1aDoubleTripleBonds
  , .p92Rule1aSaturatedRings
  , .p92Rule1bDuplicateProximity
  , .p92Rule2IsotopeMass
  , .p92Rule3Geometry
  , .p92Rule3SeqCisTrans
  , .p92Rule3Priority
  , .p92Rule4aUnitKind
  , .p92Rule4bLikeUnlike
  , .p92Rule4bPairingMethodology
  , .p92Rule4cPseudoasymmetry
  , .p92Rule5Enantiomorph
  , .p93OtherElementTetrahedra
  , .p93AbsoluteConfiguration
  , .p93RelativeConfiguration
  , .p93MixedAbsoluteRelativeConfiguration
  , .p93Racemates
  , .p93Ambo
  , .p93OtherElementGeneralMethodology
  , .p93AzaniumPhosphanium
  , .p93AminePhosphaneOxides
  , .p93PhosphatesPhosphonates
  , .p93SulfatesSulfonates
  , .p93Group14Noncarbon
  , .p93NontetrahedralGeneralMethodology
  , .p93PolyhedralSymbols
  , .p93PolyhedralGeometryRecognition
  , .p93PolyhedralPriorityNumbering
  , .p93TrigonalPyramid
  , .p93TShape
  , .p93SeeSaw
  , .p93TrigonalBipyramid
  , .p93SquarePyramid
  , .p93Octahedron
  , .p93PolyhedralChirality
  , .p93AcyclicCenters
  , .p93SingleAcyclicCenter
  , .p93MultipleDescriptorsOneCenter
  , .p93PrefixComponentCenters
  , .p93OrdinaryDoubleBonds
  , .p93DoubleBondEZCisTrans
  , .p93MultipleDoubleBonds
  , .p93HeteroatomDoubleBonds
  , .p93EvenCumulenes
  , .p93OddCumulenes
  , .p93MultipleAcyclicStereogenicUnits
  , .p93CyclicConfigurations
  , .p93MonocyclicAbsoluteCenters
  , .p93MonocyclicAchiralCenters
  , .p93MonocyclicCisTrans
  , .p93MonocyclicRCT
  , .p93UnsaturatedMonocycles
  , .p93CyclicDoubleBonds
  , .p93ExocyclicDoubleBondEZ
  , .p93ExocyclicDoubleBondOther
  , .p93VonBaeyerCIPCenters
  , .p93VonBaeyerEndoExoSynAnti
  , .p93VonBaeyerCisTrans
  , .p93VonBaeyerDoubleBonds
  , .p93SpiroXabcd
  , .p93SpiroXabab
  , .p93SpiroDoubleBonds
  , .p93SpiroNontetrahedralCenters
  , .p93SpiroAxialChirality
  , .p93FusedBridgedCIP
  , .p93CisoidTransoid
  , .p93CyclophanePlanes
  , .p93CyclophaneCenters
  , .p93CyclophaneDoubleBonds
  , .p93FullereneGeneralMethodology
  , .p93FullereneInherentParentChirality
  , .p93FullereneInherentSubstitutionChirality
  , .p93FullereneNoninherentSubstitutionChirality
  , .p93FullereneChiralSubstituents
  , .p93FullereneSuperimposedStereogenicElements
  , .p93RingAssemblyAxes
  , .p93RingAssemblyCenters
  , .p93RingAssemblyDoubleBonds
  , .p93CoupledRingChainConfigurations
  , .p94ConformationDefinition
  , .p94TorsionAngle
  , .p94TorsionLonePairs
  , .p94EclipsedStaggeredGauche
  , .p94TrigonalConformations
  , .p94SCisSTrans
  , .p94Envelope
  , .p94ChairBoatTwist
  , .p94HalfChair
  , .p94Crown
  , .p94Tub
  , .p94InOut
  , .drawingOverview
  , .drawingPlainBonds
  , .drawingHashesDashesWedges
  , .drawingWavyBonds
  , .drawingStereobondsBetweenStereocenters
  , .drawingAsterisks
  , .drawingCIPStereodescriptors
  , .drawingDiastereoisomerMixtures
  , .drawingTetraFourExplicit01
  , .drawingTetraFourExplicit02
  , .drawingTetraFourExplicit03
  , .drawingTetraFourExplicit04
  , .drawingTetraFourExplicit05
  , .drawingTetraFourExplicit06
  , .drawingTetraFourExplicit07
  , .drawingTetraFourExplicit08
  , .drawingTetraFourExplicit09
  , .drawingTetraFourExplicit10
  , .drawingTetraFourExplicit11
  , .drawingTetraFourExplicit12
  , .drawingTetraFourExplicit13
  , .drawingTetraFourExplicit14
  , .drawingTetraFourExplicit15
  , .drawingTetraFourExplicit16
  , .drawingTetraFourExplicit17
  , .drawingTetraFourExplicit18
  , .drawingTetraFourExplicit19
  , .drawingTetraFourExplicit20
  , .drawingTetraThreeExplicit01
  , .drawingTetraThreeExplicit02
  , .drawingTetraThreeExplicit03
  , .drawingTetraThreeExplicit04
  , .drawingTetraThreeExplicit05
  , .drawingTetraThreeExplicit06
  , .drawingTetraThreeExplicit07
  , .drawingTetraThreeExplicit08
  , .drawingTetraThreeExplicit09
  , .drawingTetraThreeExplicit10
  , .drawingTetraThreeExplicit11
  , .drawingTetraThreeExplicit12
  , .drawingRingTwoBonds
  , .drawingRingFusion
  , .drawingBridgehead
  , .drawingSpiroFusion
  , .drawingReentrantTetrahedralCenters
  , .drawingHigherOrderTetrahedralBonds
  , .drawingEvenConsecutiveDoubleBonds
  , .drawingHinderedBiaryls
  , .drawingFischerProjections
  , .drawingHaworthProjections
  , .drawingMillsDepictions
  , .drawingHDotDashCircle
  , .drawingLinearGeometry
  , .drawingAngularGeometry
  , .drawingTShapedGeometry
  , .drawingTrigonalPlanarGeometry
  , .drawingTrigonalPyramidalGeometry
  , .drawingSquarePlanarGeometry
  , .drawingSquarePyramidalFourGeometry
  , .drawingSeeSawGeometry
  , .drawingTrigonalBipyramidalGeometry
  , .drawingSquarePyramidalFiveGeometry
  , .drawingOctahedralGeometry
  , .drawingTrigonalPrismaticGeometry
  , .drawingHigherCoordinationGeometry
  , .drawingPerspectiveRestrictions
  , .drawingPerspectiveInterpretation
  , .drawingPerspectiveBoldBonds
  , .drawingDoubleBondSubstituentPositioning
  , .drawingOddConsecutiveDoubleBonds
  , .drawingRingDoubleBonds
  , .drawingUnspecifiedDoubleBondConfiguration
  , .drawingImplicitDoubleBondSubstituents
  , .drawingPlanarChirality
  , .drawingHelicenes
  , .drawingMobiusBands
  , .drawingMolecularPropellers
  , .drawingMixtureRepresentationGoals
  , .drawingAsDrawnAbsoluteConfiguration
  , .drawingMixtureExplanatoryText
  , .drawingRacemicAndKnownProportions
  , .drawingAvoidRacemateRelativeLabels
  , .ir9PolyhedralConfiguration
  , .ir9ConfigurationIntroduction
  , .ir9PolyhedralSymbols
  , .ir9GeometryChoice
  , .ir9DiastereoisomerGeneral
  , .ir9ConfigurationIndex
  , .ir9SquarePlanar
  , .ir9Octahedral
  , .ir9SquarePyramidal
  , .ir9Bipyramidal
  , .ir9TShape
  , .ir9SeeSaw
  , .ir9AbsoluteConfigurationGeneral
  , .ir9RSTetrahedral
  , .ir9RSTrigonalPyramidal
  , .ir9CAPolyhedral
  , .ir9CATrigonalBipyramidal
  , .ir9CASquarePyramidal
  , .ir9CASeeSaw
  , .ir9CAOctahedral
  , .ir9CATrigonalPrismatic
  , .ir9CAOtherBipyramidal
  , .ir9SkewLines
  , .ir9SkewLinesTrisBidentate
  , .ir9SkewLinesBisBidentate
  , .ir9SkewLinesChelateConformations
  , .ir9LigandPriorityGeneral
  , .ir9PriorityNumbers
  , .ir9PrimingConvention
  , .periodicAtomicNumbers
  , .standardAtomicWeights
  , .isotopeAtomicMasses
  ]

/-- Explicit source ordering of the entire finite corpus. -/
def allSourceOrdered : List IUPACNormativeProvision :=
  (((((((((((((((((((coreProvisions ++ BlueBookP10Audit.Provision.all.map IUPACNormativeProvision.p10) ++
                    BlueBookAppendix3Audit.Provision.all.map IUPACNormativeProvision.appendix3) ++
                  Retinoid1981.Provision.all.map IUPACNormativeProvision.retinoid1981) ++
                Carotenoid1974.Provision.all.map IUPACNormativeProvision.carotenoid1974) ++
              Steroid1989.Provision.all.map IUPACNormativeProvision.steroid1989) ++
            Cyclitol1973.Provision.all.map IUPACNormativeProvision.cyclitol1973) ++
          NucleicAcid1970.Provision.all.map IUPACNormativeProvision.nucleicAcid1970) ++
        Lipid1976.Provision.all.map IUPACNormativeProvision.lipid1976) ++
      Glycolipid1997.Provision.all.map IUPACNormativeProvision.glycolipid1997) ++
    AminoAcidPeptide1983.Provision.all.map IUPACNormativeProvision.aminoAcidPeptide1983) ++
    Carbohydrate1996ScopeParent.Provision.all.map
      IUPACNormativeProvision.carbohydrate1996ScopeParent) ++
    Carbohydrate1996Foundation.Provision.all.map
      IUPACNormativeProvision.carbohydrate1996Foundation) ++
    Carbohydrate1996NamedParents.Provision.all.map
      IUPACNormativeProvision.carbohydrate1996NamedParents) ++
    Carbohydrate1996Derivatives.Provision.all.map
      IUPACNormativeProvision.carbohydrate1996Derivatives) ++
    Carbohydrate1996UnsaturatedBranched.Provision.all.map
      IUPACNormativeProvision.carbohydrate1996UnsaturatedBranched) ++
    Carbohydrate1996AlditolsAcids.Provision.all.map
      IUPACNormativeProvision.carbohydrate1996AlditolsAcids) ++
    Carbohydrate1996HeteroSubstitutionAnhydride.Provision.all.map
      IUPACNormativeProvision.carbohydrate1996HeteroSubstitutionAnhydride) ++
    Carbohydrate1996Acetals.Provision.all.map IUPACNormativeProvision.carbohydrate1996Acetals) ++
    Carbohydrate1996ResiduesIons.Provision.all.map
      IUPACNormativeProvision.carbohydrate1996ResiduesIons) ++
    (((Carbohydrate1996GlycosidesRings.Provision.all.map
            IUPACNormativeProvision.carbohydrate1996GlycosidesRings ++
          Carbohydrate1996OligosaccharidesPolysaccharides.Provision.all.map
            IUPACNormativeProvision.carbohydrate1996OligosaccharidesPolysaccharides) ++
        Carbohydrate1996AppendixErrataGlossary.Provision.all.map
          IUPACNormativeProvision.carbohydrate1996AppendixErrataGlossary) ++
      Carbohydrate1996ImageAudit.Provision.all.map
        IUPACNormativeProvision.carbohydrate1996ImageArtifact)

/-- Parameterized provision families, separated from the direct constructor inventory so
aggregate proofs can compose the corpus structurally rather than reduce all 2452 rows at once. -/
def parameterizedProvisions : List IUPACNormativeProvision :=
  BlueBookP10Audit.Provision.all.map IUPACNormativeProvision.p10 ++
  BlueBookAppendix3Audit.Provision.all.map IUPACNormativeProvision.appendix3 ++
  Retinoid1981.Provision.all.map IUPACNormativeProvision.retinoid1981 ++
  Carotenoid1974.Provision.all.map IUPACNormativeProvision.carotenoid1974 ++
  Steroid1989.Provision.all.map IUPACNormativeProvision.steroid1989 ++
  Cyclitol1973.Provision.all.map IUPACNormativeProvision.cyclitol1973 ++
  NucleicAcid1970.Provision.all.map IUPACNormativeProvision.nucleicAcid1970 ++
  Lipid1976.Provision.all.map IUPACNormativeProvision.lipid1976 ++
  Glycolipid1997.Provision.all.map IUPACNormativeProvision.glycolipid1997 ++
  AminoAcidPeptide1983.Provision.all.map IUPACNormativeProvision.aminoAcidPeptide1983 ++
  Carbohydrate1996ScopeParent.Provision.all.map
    IUPACNormativeProvision.carbohydrate1996ScopeParent ++
  Carbohydrate1996Foundation.Provision.all.map
    IUPACNormativeProvision.carbohydrate1996Foundation ++
  Carbohydrate1996NamedParents.Provision.all.map
    IUPACNormativeProvision.carbohydrate1996NamedParents ++
  Carbohydrate1996Derivatives.Provision.all.map
    IUPACNormativeProvision.carbohydrate1996Derivatives ++
  Carbohydrate1996UnsaturatedBranched.Provision.all.map
    IUPACNormativeProvision.carbohydrate1996UnsaturatedBranched ++
  Carbohydrate1996AlditolsAcids.Provision.all.map
    IUPACNormativeProvision.carbohydrate1996AlditolsAcids ++
  Carbohydrate1996HeteroSubstitutionAnhydride.Provision.all.map
    IUPACNormativeProvision.carbohydrate1996HeteroSubstitutionAnhydride ++
  Carbohydrate1996Acetals.Provision.all.map IUPACNormativeProvision.carbohydrate1996Acetals ++
  Carbohydrate1996ResiduesIons.Provision.all.map
    IUPACNormativeProvision.carbohydrate1996ResiduesIons ++
  Carbohydrate1996GlycosidesRings.Provision.all.map
    IUPACNormativeProvision.carbohydrate1996GlycosidesRings ++
  Carbohydrate1996OligosaccharidesPolysaccharides.Provision.all.map
    IUPACNormativeProvision.carbohydrate1996OligosaccharidesPolysaccharides ++
  Carbohydrate1996AppendixErrataGlossary.Provision.all.map
    IUPACNormativeProvision.carbohydrate1996AppendixErrataGlossary ++
  Carbohydrate1996ImageAudit.Provision.all.map
    IUPACNormativeProvision.carbohydrate1996ImageArtifact

/-- Exhaustive provision enumeration. -/
def all : List IUPACNormativeProvision := allSourceOrdered

theorem all_eq_core_append_parameterized :
    all = coreProvisions ++ parameterizedProvisions := by
  simp [all, allSourceOrdered, parameterizedProvisions, List.append_assoc]

@[simp] theorem mem_all (provision : IUPACNormativeProvision) : provision ∈ all := by
  unfold all allSourceOrdered
  cases provision with
  | p10 provision =>
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem (f := IUPACNormativeProvision.p10) provision.mem_all
  | appendix3 provision =>
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem (f := IUPACNormativeProvision.appendix3) provision.mem_all
  | retinoid1981 provision =>
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem (f := IUPACNormativeProvision.retinoid1981) provision.mem_all
  | carotenoid1974 provision =>
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem (f := IUPACNormativeProvision.carotenoid1974) provision.mem_all
  | steroid1989 provision =>
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem (f := IUPACNormativeProvision.steroid1989) provision.mem_all
  | cyclitol1973 provision =>
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem (f := IUPACNormativeProvision.cyclitol1973) provision.mem_all
  | nucleicAcid1970 provision =>
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem (f := IUPACNormativeProvision.nucleicAcid1970) provision.mem_all
  | lipid1976 provision =>
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem (f := IUPACNormativeProvision.lipid1976) provision.mem_all
  | glycolipid1997 provision =>
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem (f := IUPACNormativeProvision.glycolipid1997) provision.mem_all
  | aminoAcidPeptide1983 provision =>
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem (f := IUPACNormativeProvision.aminoAcidPeptide1983) provision.mem_all
  | carbohydrate1996Foundation provision =>
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem
        (f := IUPACNormativeProvision.carbohydrate1996Foundation) provision.mem_all
  | carbohydrate1996NamedParents provision =>
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem
        (f := IUPACNormativeProvision.carbohydrate1996NamedParents) provision.mem_all
  | carbohydrate1996ScopeParent provision =>
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem
        (f := IUPACNormativeProvision.carbohydrate1996ScopeParent) provision.mem_all
  | carbohydrate1996Derivatives provision =>
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem
        (f := IUPACNormativeProvision.carbohydrate1996Derivatives) provision.mem_all
  | carbohydrate1996UnsaturatedBranched provision =>
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem
        (f := IUPACNormativeProvision.carbohydrate1996UnsaturatedBranched) provision.mem_all
  | carbohydrate1996AlditolsAcids provision =>
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem
        (f := IUPACNormativeProvision.carbohydrate1996AlditolsAcids) provision.mem_all
  | carbohydrate1996HeteroSubstitutionAnhydride provision =>
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem
        (f := IUPACNormativeProvision.carbohydrate1996HeteroSubstitutionAnhydride)
        provision.mem_all
  | carbohydrate1996Acetals provision =>
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem
        (f := IUPACNormativeProvision.carbohydrate1996Acetals) provision.mem_all
  | carbohydrate1996ResiduesIons provision =>
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem
        (f := IUPACNormativeProvision.carbohydrate1996ResiduesIons) provision.mem_all
  | carbohydrate1996GlycosidesRings provision =>
      apply List.mem_append_right
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      exact List.mem_map_of_mem
        (f := IUPACNormativeProvision.carbohydrate1996GlycosidesRings) provision.mem_all
  | carbohydrate1996OligosaccharidesPolysaccharides provision =>
      apply List.mem_append_right
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem
        (f := IUPACNormativeProvision.carbohydrate1996OligosaccharidesPolysaccharides)
        provision.mem_all
  | carbohydrate1996AppendixErrataGlossary provision =>
      apply List.mem_append_right
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem
        (f := IUPACNormativeProvision.carbohydrate1996AppendixErrataGlossary)
        provision.mem_all
  | carbohydrate1996ImageArtifact provision =>
      apply List.mem_append_right
      apply List.mem_append_right
      exact List.mem_map_of_mem
        (f := IUPACNormativeProvision.carbohydrate1996ImageArtifact) provision.mem_all
  | _ =>
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_left
      decide

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
private theorem parameterizedProvisions_nodup : parameterizedProvisions.Nodup := by
  have p10_nodup :
      (BlueBookP10Audit.Provision.all.map IUPACNormativeProvision.p10).Nodup :=
    BlueBookP10Audit.Provision.all_nodup.map
      (by intro left right equal; cases equal; rfl)
  have appendix3_nodup :
      (BlueBookAppendix3Audit.Provision.all.map IUPACNormativeProvision.appendix3).Nodup :=
    BlueBookAppendix3Audit.Provision.all_nodup.map
      (by intro left right equal; cases equal; rfl)
  have retinoid_nodup :
      (Retinoid1981.Provision.all.map IUPACNormativeProvision.retinoid1981).Nodup :=
    Retinoid1981.Provision.all_nodup.map
      (by intro left right equal; cases equal; rfl)
  have carotenoid_nodup :
      (Carotenoid1974.Provision.all.map IUPACNormativeProvision.carotenoid1974).Nodup :=
    Carotenoid1974.Provision.all_nodup.map
      (by intro left right equal; cases equal; rfl)
  have steroid_nodup :
      (Steroid1989.Provision.all.map IUPACNormativeProvision.steroid1989).Nodup :=
    Steroid1989.Provision.all_nodup.map
      (by intro left right equal; cases equal; rfl)
  have cyclitol_nodup :
      (Cyclitol1973.Provision.all.map IUPACNormativeProvision.cyclitol1973).Nodup :=
    Cyclitol1973.Provision.all_nodup.map
      (by intro left right equal; cases equal; rfl)
  have nucleic_nodup :
      (NucleicAcid1970.Provision.all.map IUPACNormativeProvision.nucleicAcid1970).Nodup :=
    NucleicAcid1970.Provision.all_nodup.map
      (by intro left right equal; cases equal; rfl)
  have lipid_nodup :
      (Lipid1976.Provision.all.map IUPACNormativeProvision.lipid1976).Nodup :=
    Lipid1976.Provision.all_nodup.map
      (by intro left right equal; cases equal; rfl)
  have glycolipid_nodup :
      (Glycolipid1997.Provision.all.map IUPACNormativeProvision.glycolipid1997).Nodup :=
    Glycolipid1997.Provision.all_nodup.map
      (by intro left right equal; cases equal; rfl)
  have amino_nodup :
      (AminoAcidPeptide1983.Provision.all.map
        IUPACNormativeProvision.aminoAcidPeptide1983).Nodup :=
    AminoAcidPeptide1983.Provision.all_nodup.map
      (by intro left right equal; cases equal; rfl)
  have scope_nodup :
      (Carbohydrate1996ScopeParent.Provision.all.map
        IUPACNormativeProvision.carbohydrate1996ScopeParent).Nodup :=
    Carbohydrate1996ScopeParent.Provision.all_nodup.map
      (by intro left right equal; cases equal; rfl)
  have foundation_nodup :
      (Carbohydrate1996Foundation.Provision.all.map
        IUPACNormativeProvision.carbohydrate1996Foundation).Nodup :=
    Carbohydrate1996Foundation.Provision.all_nodup.map
      (by intro left right equal; cases equal; rfl)
  have named_nodup :
      (Carbohydrate1996NamedParents.Provision.all.map
        IUPACNormativeProvision.carbohydrate1996NamedParents).Nodup :=
    Carbohydrate1996NamedParents.Provision.all_nodup.map
      (by intro left right equal; cases equal; rfl)
  have derivatives_nodup :
      (Carbohydrate1996Derivatives.Provision.all.map
        IUPACNormativeProvision.carbohydrate1996Derivatives).Nodup :=
    Carbohydrate1996Derivatives.Provision.all_nodup.map
      (by intro left right equal; cases equal; rfl)
  have unsaturated_nodup :
      (Carbohydrate1996UnsaturatedBranched.Provision.all.map
        IUPACNormativeProvision.carbohydrate1996UnsaturatedBranched).Nodup :=
    Carbohydrate1996UnsaturatedBranched.Provision.all_nodup.map
      (by intro left right equal; cases equal; rfl)
  have alditols_nodup :
      (Carbohydrate1996AlditolsAcids.Provision.all.map
        IUPACNormativeProvision.carbohydrate1996AlditolsAcids).Nodup :=
    Carbohydrate1996AlditolsAcids.Provision.all_nodup.map
      (by intro left right equal; cases equal; rfl)
  have hetero_nodup :
      (Carbohydrate1996HeteroSubstitutionAnhydride.Provision.all.map
        IUPACNormativeProvision.carbohydrate1996HeteroSubstitutionAnhydride).Nodup :=
    Carbohydrate1996HeteroSubstitutionAnhydride.Provision.all_nodup.map
      (by intro left right equal; cases equal; rfl)
  have acetals_nodup :
      (Carbohydrate1996Acetals.Provision.all.map
        IUPACNormativeProvision.carbohydrate1996Acetals).Nodup :=
    Carbohydrate1996Acetals.Provision.all_nodup.map
      (by intro left right equal; cases equal; rfl)
  have residues_nodup :
      (Carbohydrate1996ResiduesIons.Provision.all.map
        IUPACNormativeProvision.carbohydrate1996ResiduesIons).Nodup :=
    Carbohydrate1996ResiduesIons.Provision.all_nodup.map
      (by intro left right equal; cases equal; rfl)
  have rings_nodup :
      (Carbohydrate1996GlycosidesRings.Provision.all.map
        IUPACNormativeProvision.carbohydrate1996GlycosidesRings).Nodup :=
    Carbohydrate1996GlycosidesRings.Provision.all_nodup.map
      (by intro left right equal; cases equal; rfl)
  have oligosaccharides_nodup :
      (Carbohydrate1996OligosaccharidesPolysaccharides.Provision.all.map
        IUPACNormativeProvision.carbohydrate1996OligosaccharidesPolysaccharides).Nodup :=
    Carbohydrate1996OligosaccharidesPolysaccharides.Provision.all_nodup.map
      (by intro left right equal; cases equal; rfl)
  have appendix_carbohydrate_nodup :
      (Carbohydrate1996AppendixErrataGlossary.Provision.all.map
        IUPACNormativeProvision.carbohydrate1996AppendixErrataGlossary).Nodup :=
    Carbohydrate1996AppendixErrataGlossary.Provision.all_nodup.map
      (by intro left right equal; cases equal; rfl)
  have image_nodup :
      (Carbohydrate1996ImageAudit.Provision.all.map
        IUPACNormativeProvision.carbohydrate1996ImageArtifact).Nodup :=
    Carbohydrate1996ImageAudit.Provision.all_nodup.map
      (by intro left right equal; cases equal; rfl)
  have parameterized_nodup : parameterizedProvisions.Nodup := by
    simp [parameterizedProvisions, List.nodup_append', List.disjoint_left,
      p10_nodup, appendix3_nodup, retinoid_nodup, carotenoid_nodup, steroid_nodup,
      cyclitol_nodup, nucleic_nodup, lipid_nodup, glycolipid_nodup, amino_nodup,
      scope_nodup, foundation_nodup, named_nodup, derivatives_nodup,
      unsaturated_nodup, alditols_nodup, hetero_nodup, acetals_nodup,
      residues_nodup, rings_nodup, oligosaccharides_nodup,
      appendix_carbohydrate_nodup, image_nodup]
  exact parameterized_nodup

set_option maxRecDepth 8192 in
private theorem coreProvisions_nodup : coreProvisions.Nodup := by decide

/-- Constructor-family discriminator used to prove that direct source rows and delegated rows are
disjoint without comparing every pair of the 2,452 manifest entries. -/
def isParameterizedProvision : IUPACNormativeProvision → Bool
  | .p10 _ | .appendix3 _ | .retinoid1981 _ | .carotenoid1974 _ | .steroid1989 _
  | .cyclitol1973 _ | .nucleicAcid1970 _ | .lipid1976 _ | .glycolipid1997 _
  | .aminoAcidPeptide1983 _ | .carbohydrate1996Foundation _
  | .carbohydrate1996NamedParents _ | .carbohydrate1996ScopeParent _
  | .carbohydrate1996Derivatives _ | .carbohydrate1996UnsaturatedBranched _
  | .carbohydrate1996AlditolsAcids _ | .carbohydrate1996HeteroSubstitutionAnhydride _
  | .carbohydrate1996Acetals _ | .carbohydrate1996ResiduesIons _
  | .carbohydrate1996GlycosidesRings _
  | .carbohydrate1996OligosaccharidesPolysaccharides _
  | .carbohydrate1996AppendixErrataGlossary _ | .carbohydrate1996ImageArtifact _ => true
  | _ => false

private theorem forall_parameterized_map
    {α : Type} (rows : List α) (wrap : α → IUPACNormativeProvision)
    (wrapParameterized : ∀ row, isParameterizedProvision (wrap row) = true) :
    (rows.map wrap).Forall (fun row => isParameterizedProvision row = true) := by
  rw [List.forall_iff_forall_mem]
  intro provision member
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
  exact wrapParameterized row

set_option maxRecDepth 8192 in
private theorem coreProvisions_not_parameterized
    (provision : IUPACNormativeProvision) (member : provision ∈ coreProvisions) :
    isParameterizedProvision provision = false := by
  have everyCoreIsDirect :
      coreProvisions.Forall (fun row => isParameterizedProvision row = false) := by
    decide
  exact (List.forall_iff_forall_mem.mp everyCoreIsDirect) provision member

set_option maxRecDepth 4096 in
theorem parameterizedProvisions_are_parameterized
    (provision : IUPACNormativeProvision) (member : provision ∈ parameterizedProvisions) :
    isParameterizedProvision provision = true := by
  have everyDelegatedIsParameterized :
      parameterizedProvisions.Forall
        (fun row => isParameterizedProvision row = true) := by
    simp only [parameterizedProvisions, List.forall_append]
    repeat' constructor
  exact (List.forall_iff_forall_mem.mp everyDelegatedIsParameterized) provision member

private theorem core_parameterized_disjoint :
    List.Disjoint coreProvisions parameterizedProvisions := by
  rw [List.disjoint_left]
  intro provision coreMember parameterizedMember
  have direct := coreProvisions_not_parameterized provision coreMember
  have delegated := parameterizedProvisions_are_parameterized provision parameterizedMember
  simp_all

theorem all_nodup : all.Nodup := by
  rw [all_eq_core_append_parameterized]
  exact coreProvisions_nodup.append parameterizedProvisions_nodup core_parameterized_disjoint

set_option maxRecDepth 4096 in
@[simp] theorem length_all : all.length = 2452 := by
  rw [all_eq_core_append_parameterized]
  simp [parameterizedProvisions, coreProvisions]

end IUPACNormativeProvision

end TetraStereo.OneCenter
