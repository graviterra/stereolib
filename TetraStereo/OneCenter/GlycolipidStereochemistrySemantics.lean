import TetraStereo.OneCenter.Basic
import TetraStereo.OneCenter.P10DelegatedAuthorityCorpus

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent glycolipid stereochemistry semantics

This module audits the configuration-bearing provisions of *Nomenclature of Glycolipids
(Recommendations 1997)* in its corrected web edition.  The recommendation explicitly supersedes
the glycolipid section of the 1976 lipid rules.  Because the retained root structures and the
Svennerholm table imply complete anomeric linkage patterns, each row is a separate provision and
is represented by an exact source-level structure code.

The structure codes are independently auditable data, not yet parsed molecular graphs.  Their
refinement to the general carbohydrate graph semantics and to production input remains open, so
all rows remain partial.  No production analyzer is imported.
-/

namespace Glycolipid1997

inductive RootGlycan where
  | ganglio
  | lacto
  | neolacto
  | globo
  | isoglobo
  | mollu
  | arthro
  deriving DecidableEq, Repr

namespace RootGlycan

def all : List RootGlycan :=
  [.ganglio, .lacto, .neolacto, .globo, .isoglobo, .mollu, .arthro]

@[simp] theorem mem_all (root : RootGlycan) : root ∈ all := by
  cases root <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 7 := by decide

/-- Exact Table-2 symbolic structures, written from the nonreducing end toward ceramide. -/
def structureCode : RootGlycan → String
  | .ganglio => "Galβ3GalNAcβ4Galβ4Glc-"
  | .lacto => "Galβ3GlcNAcβ3Galβ4Glc-"
  | .neolacto => "Galβ4GlcNAcβ3Galβ4Glc-"
  | .globo => "GalNAcβ3Galα4Galβ4Glc-"
  | .isoglobo => "GalNAcβ3Galα3Galβ4Glc-"
  | .mollu => "GlcNAcβ2Manα3Manβ4Glc-"
  | .arthro => "GalNAcβ4GlcNAcβ3Manβ4Glc-"

def symbol : RootGlycan → String
  | .ganglio => "Gg"
  | .lacto => "Lc"
  | .neolacto => "nLc"
  | .globo => "Gb"
  | .isoglobo => "iGb"
  | .mollu => "Mu"
  | .arthro => "At"

theorem structure_codes_are_pairwise_distinct : (all.map structureCode).Nodup := by
  decide

end RootGlycan

inductive SvennerholmEntry where
  | GM3 | GM2 | GM1a | GM1b
  | GD3 | GD2 | GD1a | GD1b
  | GT1a | GT1b | GT1c | GQ1b
  deriving DecidableEq, Repr

namespace SvennerholmEntry

def all : List SvennerholmEntry :=
  [.GM3, .GM2, .GM1a, .GM1b, .GD3, .GD2, .GD1a, .GD1b,
    .GT1a, .GT1b, .GT1c, .GQ1b]

@[simp] theorem mem_all (entry : SvennerholmEntry) : entry ∈ all := by
  cases entry <;> simp [all]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 12 := by decide

/-- Primary-publication Table-3 structures. Parentheses retain the source's branch topology. -/
def structureCode : SvennerholmEntry → String
  | .GM3 => "Neu5Acα3Galβ4GlcCer"
  | .GM2 => "GalNAcβ4(Neu5Acα3)Galβ4GlcCer"
  | .GM1a => "Galβ3GalNAcβ4(Neu5Acα3)Galβ4GlcCer"
  | .GM1b => "Neu5Acα3Galβ3GalNAcβ4Galβ4GlcCer"
  | .GD3 => "Neu5Acα8Neu5Acα3Galβ4GlcCer"
  | .GD2 => "GalNAcβ4(Neu5Acα8Neu5Acα3)Galβ4GlcCer"
  | .GD1a => "Neu5Acα3Galβ3GalNAcβ4(Neu5Acα3)Galβ4GlcCer"
  | .GD1b => "Galβ3GalNAcβ4(Neu5Acα8Neu5Acα3)Galβ4GlcCer"
  | .GT1a => "Neu5Acα8Neu5Acα3Galβ3GalNAcβ4(Neu5Acα3)Galβ4GlcCer"
  | .GT1b => "Neu5Acα3Galβ3GalNAcβ4(Neu5Acα8Neu5Acα3)Galβ4GlcCer"
  | .GT1c => "Galβ3GalNAcβ4(Neu5Acα8Neu5Acα8Neu5Acα3)Galβ4GlcCer"
  | .GQ1b => "Neu5Acα8Neu5Acα3Galβ3GalNAcβ4(Neu5Acα8Neu5Acα3)Galβ4GlcCer"

/--
Literal Table-3 text from the corrected web edition. Its GQ1b row alone contains the unlisted
`Neu5c` transcription defect; this function records those bytes and is not canonical chemistry.
-/
def webLiteralStructureCode : SvennerholmEntry → String
  | .GM3 => "Neu5Acα3Galβ4GlcCer"
  | .GM2 => "GalNAcβ4(Neu5Acα3)Galβ4GlcCer"
  | .GM1a => "Galβ3GalNAcβ4(Neu5Acα3)Galβ4GlcCer"
  | .GM1b => "Neu5Acα3Galβ3GalNAcβ4Galβ4GlcCer"
  | .GD3 => "Neu5Acα8Neu5Acα3Galβ4GlcCer"
  | .GD2 => "GalNAcβ4(Neu5Acα8Neu5Acα3)Galβ4GlcCer"
  | .GD1a => "Neu5Acα3Galβ3GalNAcβ4(Neu5Acα3)Galβ4GlcCer"
  | .GD1b => "Galβ3GalNAcβ4(Neu5Acα8Neu5Acα3)Galβ4GlcCer"
  | .GT1a => "Neu5Acα8Neu5Acα3Galβ3GalNAcβ4(Neu5Acα3)Galβ4GlcCer"
  | .GT1b => "Neu5Acα3Galβ3GalNAcβ4(Neu5Acα8Neu5Acα3)Galβ4GlcCer"
  | .GT1c => "Galβ3GalNAcβ4(Neu5Acα8Neu5Acα8Neu5Acα3)Galβ4GlcCer"
  | .GQ1b => "Neu5Acα8Neu5Acα3Galβ3GalNAcβ4(Neu5Acα8Neu5cα3)Galβ4GlcCer"

@[simp] theorem web_literal_differs_from_primary_print_exactly_at_GQ1b
    (entry : SvennerholmEntry) :
    webLiteralStructureCode entry ≠ structureCode entry ↔ entry = .GQ1b := by
  cases entry <;> decide

def abbreviation : SvennerholmEntry → String
  | .GM3 => "GM3"
  | .GM2 => "GM2"
  | .GM1a => "GM1a"
  | .GM1b => "GM1b"
  | .GD3 => "GD3"
  | .GD2 => "GD2"
  | .GD1a => "GD1a"
  | .GD1b => "GD1b"
  | .GT1a => "GT1a"
  | .GT1b => "GT1b"
  | .GT1c => "GT1c"
  | .GQ1b => "GQ1b"

theorem structure_codes_are_pairwise_distinct : (all.map structureCode).Nodup := by
  decide

end SvennerholmEntry

inductive Provision where
  | supersedesLipid1976GlycolipidSection
  | monosaccharideSemanticsDelegatedToCarbohydrateRules
  | dlSymbolsGenerallyOmitted
  | defaultDExceptFucoseAndRhamnose
  | inositolSymbolUsesOneDNumbering
  | linkagePositionsAndAnomersRequired
  | shortFormOmitsOnlyInvariantAnomericLocant
  | invariantAnomericLocants
  | ringSizeAndConformationRequireFirmEvidence
  | glycerolAlwaysUsesSn
  | glycoglycerolipidExampleConfiguration
  | gpiCombinesPhospholipidAndGlycanRules
  | gpiCoreConfiguration
  | gpiInositolGenerallyDMyo
  | carbohydrateAttachesToSphingoidO1
  | sphinganineConfiguration
  | unsaturatedSphingoidLocantsAndGeometryRequired
  | sphingFourEnineConfiguration
  | phytosphingosineConfiguration
  | explicitMonoglycosylceramidePreferred
  | lactosylceramideConfiguration
  | rootStructure (root : RootGlycan)
  | additionalResidueAnomerRequired
  | branchOrderHighestAcceptingLocantFirst
  | correctedBranchFigureAlignment
  | svennerholmStructure (entry : SvennerholmEntry)
  deriving DecidableEq, Repr

namespace Provision

def base : List Provision :=
  [ .supersedesLipid1976GlycolipidSection
  , .monosaccharideSemanticsDelegatedToCarbohydrateRules
  , .dlSymbolsGenerallyOmitted
  , .defaultDExceptFucoseAndRhamnose
  , .inositolSymbolUsesOneDNumbering
  , .linkagePositionsAndAnomersRequired
  , .shortFormOmitsOnlyInvariantAnomericLocant
  , .invariantAnomericLocants
  , .ringSizeAndConformationRequireFirmEvidence
  , .glycerolAlwaysUsesSn
  , .glycoglycerolipidExampleConfiguration
  , .gpiCombinesPhospholipidAndGlycanRules
  , .gpiCoreConfiguration
  , .gpiInositolGenerallyDMyo
  , .carbohydrateAttachesToSphingoidO1
  , .sphinganineConfiguration
  , .unsaturatedSphingoidLocantsAndGeometryRequired
  , .sphingFourEnineConfiguration
  , .phytosphingosineConfiguration
  , .explicitMonoglycosylceramidePreferred
  , .lactosylceramideConfiguration
  , .additionalResidueAnomerRequired
  , .branchOrderHighestAcceptingLocantFirst
  , .correctedBranchFigureAlignment
  ]

def all : List Provision :=
  (base ++ RootGlycan.all.map Provision.rootStructure) ++
    SvennerholmEntry.all.map Provision.svennerholmStructure

@[simp] theorem mem_all (provision : Provision) : provision ∈ all := by
  cases provision with
  | rootStructure root =>
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map_of_mem (f := Provision.rootStructure) root.mem_all
  | svennerholmStructure entry =>
      apply List.mem_append_right
      exact List.mem_map_of_mem (f := Provision.svennerholmStructure) entry.mem_all
  | _ => simp [all, base]

theorem all_nodup : all.Nodup := by decide

@[simp] theorem length_all : all.length = 43 := by decide

def sourceSection : Provision → String
  | .supersedesLipid1976GlycolipidSection => "Glycolipid-1997/GL-1"
  | .monosaccharideSemanticsDelegatedToCarbohydrateRules
  | .dlSymbolsGenerallyOmitted
  | .defaultDExceptFucoseAndRhamnose
  | .inositolSymbolUsesOneDNumbering => "Glycolipid-1997/GL-3.2/Table 1"
  | .linkagePositionsAndAnomersRequired
  | .shortFormOmitsOnlyInvariantAnomericLocant
  | .invariantAnomericLocants => "Glycolipid-1997/GL-3.3"
  | .ringSizeAndConformationRequireFirmEvidence => "Glycolipid-1997/GL-3.4"
  | .glycerolAlwaysUsesSn | .glycoglycerolipidExampleConfiguration => "Glycolipid-1997/GL-4.1"
  | .gpiCombinesPhospholipidAndGlycanRules
  | .gpiCoreConfiguration | .gpiInositolGenerallyDMyo => "Glycolipid-1997/GL-4.2"
  | .carbohydrateAttachesToSphingoidO1 | .sphinganineConfiguration
  | .unsaturatedSphingoidLocantsAndGeometryRequired
  | .sphingFourEnineConfiguration | .phytosphingosineConfiguration => "Glycolipid-1997/GL-4.3"
  | .explicitMonoglycosylceramidePreferred => "Glycolipid-1997/GL-5.1"
  | .lactosylceramideConfiguration => "Glycolipid-1997/GL-5.2"
  | .rootStructure _ => "Glycolipid-1997/GL-5.3.1/Table 2"
  | .additionalResidueAnomerRequired => "Glycolipid-1997/GL-5.3.4"
  | .branchOrderHighestAcceptingLocantFirst => "Glycolipid-1997/GL-5.3.5"
  | .correctedBranchFigureAlignment => "Glycolipid-1997/Errata/GL-6.5"
  | .svennerholmStructure _ => "Glycolipid-1997/GL-7.2/Table 3"

def sourceKey (provision : Provision) : String := provision.sourceSection

end Provision

/-! ## Corrected-edition boundary -/

inductive IncorporatedErratum where
  | gangliotriaosylSpelling
  | glycuronoglycosphingolipidSpelling
  | arthrotriaosylSpelling
  | gl65BranchAlignment
  | gl72StrayHyphen
  | gl72RepeatedWord
  | referenceOneCommission
  | referenceFourPublication
  deriving DecidableEq, Repr

namespace IncorporatedErratum

def all : List IncorporatedErratum :=
  [ .gangliotriaosylSpelling
  , .glycuronoglycosphingolipidSpelling
  , .arthrotriaosylSpelling
  , .gl65BranchAlignment
  , .gl72StrayHyphen
  , .gl72RepeatedWord
  , .referenceOneCommission
  , .referenceFourPublication
  ]

@[simp] theorem mem_all (erratum : IncorporatedErratum) : erratum ∈ all := by
  cases erratum <;> simp [all]

def changesStructureReading : IncorporatedErratum → Bool
  | .gl65BranchAlignment => true
  | _ => false

theorem only_GL65_alignment_changes_structure_reading (erratum : IncorporatedErratum) :
    erratum.changesStructureReading ↔ erratum = .gl65BranchAlignment := by
  cases erratum <;> decide

end IncorporatedErratum

/-!
The official errata page lists eight corrected items but omits the corrected web edition's GQ1b
`Neu5c` typo. The printed primary publication has `Neu5Ac`, so this is tracked separately from the
incorporated errata and never replaces the canonical structure code.
-/

inductive UnlistedWebTranscriptionDefect where
  | table3GQ1bNeu5c
  deriving DecidableEq, Repr

namespace UnlistedWebTranscriptionDefect

def all : List UnlistedWebTranscriptionDefect := [.table3GQ1bNeu5c]

def primaryPrintToken : UnlistedWebTranscriptionDefect → String
  | .table3GQ1bNeu5c => "Neu5Ac"

def webLiteralToken : UnlistedWebTranscriptionDefect → String
  | .table3GQ1bNeu5c => "Neu5c"

@[simp] theorem mem_all (defect : UnlistedWebTranscriptionDefect) : defect ∈ all := by
  cases defect
  simp [all]

end UnlistedWebTranscriptionDefect

/-! ## Monosaccharide defaults and glycosidic notation -/

inductive Monosaccharide where
  | glucose | galactose | mannose | xylose
  | glucosamine | galactosamine | neuraminicAcid
  | fucose | rhamnose | myoInositol
  deriving DecidableEq, Repr

inductive DLSeries where
  | D
  | L
  deriving DecidableEq, Repr

def defaultSeries : Monosaccharide → DLSeries
  | .fucose | .rhamnose => .L
  | _ => .D

@[simp] theorem default_series_exceptions_are_exact (sugar : Monosaccharide) :
    defaultSeries sugar = .L ↔ sugar = .fucose ∨ sugar = .rhamnose := by
  cases sugar <;> decide

def printedSeries (explicit : Option DLSeries) : Option DLSeries := explicit

@[simp] theorem omitted_series_uses_semantic_default (sugar : Monosaccharide) :
    let semanticSeries := match printedSeries none with
      | some series => series
      | none => defaultSeries sugar
    semanticSeries = defaultSeries sugar := by
  rfl

inductive Anomer where
  | alpha
  | beta
  deriving DecidableEq, Repr

def invariantAnomericCarbon : Monosaccharide → Nat
  | .neuraminicAcid => 2
  | _ => 1

structure GlycosidicCitation where
  anomer : Anomer
  donorLocant : Nat
  acceptorLocant : Nat
  deriving DecidableEq, Repr

def shortCitation (sugar : Monosaccharide) (anomer : Anomer) (acceptorLocant : Nat) :
    GlycosidicCitation :=
  ⟨anomer, invariantAnomericCarbon sugar, acceptorLocant⟩

@[simp] theorem glucose_short_form_restores_donor_one (anomer : Anomer) (acceptor : Nat) :
    (shortCitation .glucose anomer acceptor).donorLocant = 1 := rfl

@[simp] theorem neuraminic_short_form_restores_donor_two (anomer : Anomer) (acceptor : Nat) :
    (shortCitation .neuraminicAcid anomer acceptor).donorLocant = 2 := rfl

structure RingEvidence where
  sizeFirmlyEstablished : Bool
  conformationFirmlyEstablished : Bool
  deriving DecidableEq, Repr

def mayCiteRingSizeAndConformation (evidence : RingEvidence) : Bool :=
  evidence.sizeFirmlyEstablished && evidence.conformationFirmlyEstablished

@[simp] theorem uncertain_conformation_must_not_be_cited (sizeKnown : Bool) :
    !mayCiteRingSizeAndConformation ⟨sizeKnown, false⟩ := by
  cases sizeKnown <;> decide

/-! ## Glycerol, GPI, and sphingoid configuration -/

structure GlycoglycerolipidReference where
  acylLocants : List Nat
  glycosylLocant : Nat
  glycosylAnomer : Anomer
  glycosylSeries : DLSeries
  usesSn : Bool
  deriving DecidableEq, Repr

def sourceGlycoglycerolipidExample : GlycoglycerolipidReference :=
  ⟨[1, 2], 3, .beta, .D, true⟩

@[simp] theorem GL41_example_is_exact :
    sourceGlycoglycerolipidExample = ⟨[1, 2], 3, .beta, .D, true⟩ := rfl

structure GPICoreStep where
  residue : Monosaccharide
  anomer : Anomer
  acceptorLocant : Nat
  deriving DecidableEq, Repr

/-- Manα2Manα6Manα4GlcNα6-inositol, as printed in GL-4.2.2. -/
def gpiCore : List GPICoreStep :=
  [ ⟨.mannose, .alpha, 2⟩
  , ⟨.mannose, .alpha, 6⟩
  , ⟨.mannose, .alpha, 4⟩
  , ⟨.glucosamine, .alpha, 6⟩
  ]

@[simp] theorem gpi_core_has_four_configured_steps : gpiCore.length = 4 := rfl

structure GPIReference where
  glycerolPhosphateLocant : Nat
  glycerolUsesSn : Bool
  inositolSeries : DLSeries
  inositolIsMyo : Bool
  deriving DecidableEq, Repr

def generalGPIReference : GPIReference := ⟨3, true, .D, true⟩

inductive RS where
  | R
  | S
  deriving DecidableEq, Repr

inductive EZ where
  | E
  | Z
  deriving DecidableEq, Repr

structure SphingoidConfiguration where
  c2 : RS
  c3 : RS
  c4Center? : Option RS
  doubleBonds : List (Nat × EZ)
  deriving DecidableEq, Repr

def sphinganine : SphingoidConfiguration := ⟨.S, .R, none, []⟩
def sphingFourEnine : SphingoidConfiguration := ⟨.S, .R, none, [(4, .E)]⟩
def phytosphingosine : SphingoidConfiguration := ⟨.S, .S, some .R, []⟩

@[simp] theorem three_named_sphingoid_configurations_are_exact :
    sphinganine = ⟨.S, .R, none, []⟩ ∧
      sphingFourEnine = ⟨.S, .R, none, [(4, .E)]⟩ ∧
      phytosphingosine = ⟨.S, .S, some .R, []⟩ := by
  decide

def carbohydrateAttachmentAtomOnSphingoid : Nat := 1

/-! ## Table coverage -/

theorem every_root_table_row_has_a_nonempty_structure_code (root : RootGlycan) :
    root.structureCode ≠ "" := by
  cases root <;> decide

theorem every_svennerholm_row_has_a_nonempty_structure_code (entry : SvennerholmEntry) :
    entry.structureCode ≠ "" := by
  cases entry <;> decide

/-! ## Clause ownership -/

inductive SemanticDomain where
  | supersession
  | carbohydrateDelegation
  | seriesDefault
  | glycosidicCitation
  | conformationEvidence
  | glycerolSn
  | gpi
  | sphingoid
  | monoglycosylCeramide
  | rootInventory
  | branching
  | correctedFigure
  | svennerholmInventory
  deriving DecidableEq, Repr

def provisionSemanticDomain : Provision → SemanticDomain
  | .supersedesLipid1976GlycolipidSection => .supersession
  | .monosaccharideSemanticsDelegatedToCarbohydrateRules => .carbohydrateDelegation
  | .dlSymbolsGenerallyOmitted | .defaultDExceptFucoseAndRhamnose
  | .inositolSymbolUsesOneDNumbering => .seriesDefault
  | .linkagePositionsAndAnomersRequired | .shortFormOmitsOnlyInvariantAnomericLocant
  | .invariantAnomericLocants | .additionalResidueAnomerRequired => .glycosidicCitation
  | .ringSizeAndConformationRequireFirmEvidence => .conformationEvidence
  | .glycerolAlwaysUsesSn | .glycoglycerolipidExampleConfiguration => .glycerolSn
  | .gpiCombinesPhospholipidAndGlycanRules | .gpiCoreConfiguration
  | .gpiInositolGenerallyDMyo => .gpi
  | .carbohydrateAttachesToSphingoidO1 | .sphinganineConfiguration
  | .unsaturatedSphingoidLocantsAndGeometryRequired | .sphingFourEnineConfiguration
  | .phytosphingosineConfiguration => .sphingoid
  | .explicitMonoglycosylceramidePreferred | .lactosylceramideConfiguration =>
      .monoglycosylCeramide
  | .rootStructure _ => .rootInventory
  | .branchOrderHighestAcceptingLocantFirst => .branching
  | .correctedBranchFigureAlignment => .correctedFigure
  | .svennerholmStructure _ => .svennerholmInventory

theorem every_provision_has_an_independent_semantic_domain
    (provision : Provision) : ∃ domain, provisionSemanticDomain provision = domain := by
  exact ⟨provisionSemanticDomain provision, rfl⟩








structure TextualSourceReviewEvidence where
  reviewerKind : String
  reviewDate : String
  method : String
  sourceBundleSha256 : String
  primaryPublicationSha256 : String
  reviewedArtifacts : Nat
  reviewedImages : Nat
  reviewedProvisions : List Provision
  reviewedRootRows : List RootGlycan
  reviewedSvennerholmRows : List SvennerholmEntry
  reviewedErrata : List IncorporatedErratum
  reviewedWebDefects : List UnlistedWebTranscriptionDefect
  provisionEnumerationConfirmed : Bool
  proseTableCoverageConfirmed : Bool
  figureGraphReviewIssued : Bool
  reviewerKindDeclared : reviewerKind ≠ ""
  reviewDateDeclared : reviewDate ≠ ""
  methodDeclared : method ≠ ""
  reviewedProvisionsExact : reviewedProvisions = Provision.all
  reviewedRootRowsExact : reviewedRootRows = RootGlycan.all
  reviewedSvennerholmRowsExact : reviewedSvennerholmRows = SvennerholmEntry.all
  reviewedErrataExact : reviewedErrata = IncorporatedErratum.all
  reviewedWebDefectsExact : reviewedWebDefects = UnlistedWebTranscriptionDefect.all
  provisionEnumerationConfirmedExact : provisionEnumerationConfirmed = true
  proseTableCoverageConfirmedExact : proseTableCoverageConfirmed = true
  figureGraphReviewNotIssued : figureGraphReviewIssued = false

def currentTextualSourceReview : TextualSourceReviewEvidence where
  reviewerKind := "automated-record-0e9ff8ee11712125d507ef4bc1fa8058"
  reviewDate := "record-54db71cc66a48d655191405c29c6a9ac"
  method :=
    "record-667850423a762653a74c1c7fb56e822d"
  sourceBundleSha256 :=
    (P10DelegatedAuthorityCorpus.snapshot .glycolipid1997).bundleSha256
  primaryPublicationSha256 :=
    "87f1874c989845f41241ce1a5739438d26d5a1888dc79c8b31320239eb084dff"
  reviewedArtifacts := 15
  reviewedImages := 13
  reviewedProvisions := Provision.all
  reviewedRootRows := RootGlycan.all
  reviewedSvennerholmRows := SvennerholmEntry.all
  reviewedErrata := IncorporatedErratum.all
  reviewedWebDefects := UnlistedWebTranscriptionDefect.all
  provisionEnumerationConfirmed := true
  proseTableCoverageConfirmed := true
  figureGraphReviewIssued := false
  reviewerKindDeclared := by decide
  reviewDateDeclared := by decide
  methodDeclared := by decide
  reviewedProvisionsExact := rfl
  reviewedRootRowsExact := rfl
  reviewedSvennerholmRowsExact := rfl
  reviewedErrataExact := rfl
  reviewedWebDefectsExact := rfl
  provisionEnumerationConfirmedExact := rfl
  proseTableCoverageConfirmedExact := rfl
  figureGraphReviewNotIssued := rfl

@[simp] theorem current_textual_source_review_counts_exact :
    currentTextualSourceReview.reviewedArtifacts = 15 ∧
      currentTextualSourceReview.reviewedImages = 13 ∧
        currentTextualSourceReview.reviewedProvisions.length = 43 ∧
          currentTextualSourceReview.reviewedRootRows.length = 7 ∧
            currentTextualSourceReview.reviewedSvennerholmRows.length = 12 ∧
              currentTextualSourceReview.reviewedErrata.length = 8 ∧
                currentTextualSourceReview.reviewedWebDefects.length = 1 := by
  decide

end Glycolipid1997

end TetraStereo.OneCenter
