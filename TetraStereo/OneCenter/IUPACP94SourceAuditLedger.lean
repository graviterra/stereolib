import TetraStereo.OneCenter.IUPACP94FrozenSourceProgram
import TetraStereo.KernelOnly

set_option autoImplicit false












namespace TetraStereo.OneCenter
namespace P94SourceAuditLedger

structure FrozenP9Artifact where
  normativeSource : IUPACNormativeSource
  canonicalUrl : String
  sha256 : String
  pdfPageCount : Nat
  p94FirstPdfPage : Nat
  p94LastPdfPage : Nat
  deriving DecidableEq, Repr

def frozenP9Artifact : FrozenP9Artifact where
  normativeSource := .blueBook2013P9
  canonicalUrl := "https://iupac.qmul.ac.uk/BlueBook/PDF/P9.pdf"
  sha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  pdfPageCount := 91
  p94FirstPdfPage := 87
  p94LastPdfPage := 91

@[simp] theorem frozen_p9_artifact_exact :
    frozenP9Artifact.normativeSource = .blueBook2013P9 ∧
      frozenP9Artifact.sha256 =
        "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450" ∧
        frozenP9Artifact.pdfPageCount = 91 ∧
          frozenP9Artifact.p94FirstPdfPage = 87 ∧
            frozenP9Artifact.p94LastPdfPage = 91 := by
  decide

@[simp] theorem frozen_p9_url_matches_manifest :
    frozenP9Artifact.canonicalUrl = IUPACNormativeSource.url .blueBook2013P9 := by
  rfl

@[simp] theorem frozen_p9_digest_matches_manifest :
    some frozenP9Artifact.sha256 = IUPACNormativeSource.sha256? .blueBook2013P9 := by
  rfl

structure SourceSectionRecord where
  clause : P94Clause
  sourceLabel : String
  firstPdfPage : Nat
  lastPdfPage : Nat
  deriving DecidableEq, Repr

/-- Exact heading order and inclusive PDF-page spans in the frozen P-9 artifact. -/
def sectionRecords : List SourceSectionRecord :=
  [ ⟨.conformationDefinition, "P-94.1", 87, 87⟩
  , ⟨.torsionAngle, "P-94.2.1", 87, 88⟩
  , ⟨.torsionLonePairs, "P-94.2.2", 88, 89⟩
  , ⟨.eclipsedStaggeredGauche, "P-94.3.1.1", 89, 89⟩
  , ⟨.trigonalConformations, "P-94.3.1.2", 89, 89⟩
  , ⟨.sCisSTrans, "P-94.3.1.3", 89, 89⟩
  , ⟨.envelope, "P-94.3.2.1", 90, 90⟩
  , ⟨.chairBoatTwist, "P-94.3.2.2", 90, 90⟩
  , ⟨.halfChair, "P-94.3.2.3", 90, 90⟩
  , ⟨.crown, "P-94.3.2.4", 90, 90⟩
  , ⟨.tub, "P-94.3.2.5", 90, 90⟩
  , ⟨.inOut, "P-94.3.2.6", 90, 91⟩ ]

@[simp] theorem section_record_clauses_exact :
    sectionRecords.map SourceSectionRecord.clause = P94Clause.all := by
  rfl

@[simp] theorem section_record_anchors_exact :
    sectionRecords.map SourceSectionRecord.sourceLabel =
      [ "P-94.1", "P-94.2.1", "P-94.2.2", "P-94.3.1.1"
      , "P-94.3.1.2", "P-94.3.1.3", "P-94.3.2.1", "P-94.3.2.2"
      , "P-94.3.2.3", "P-94.3.2.4", "P-94.3.2.5", "P-94.3.2.6" ] := by
  rfl

@[simp] theorem section_record_page_ranges_exact :
    sectionRecords.map (fun record => (record.firstPdfPage, record.lastPdfPage)) =
      [ (87, 87), (87, 88), (88, 89), (89, 89)
      , (89, 89), (89, 89), (90, 90), (90, 90)
      , (90, 90), (90, 90), (90, 90), (90, 91) ] := by
  rfl

@[simp] theorem section_record_count : sectionRecords.length = 12 := by
  decide

theorem section_record_clauses_nodup :
    (sectionRecords.map SourceSectionRecord.clause).Nodup := by
  rw [section_record_clauses_exact]
  exact P94Clause.all_nodup

theorem every_clause_has_exactly_one_section_record (clause : P94Clause) :
    (sectionRecords.filter fun record => record.clause == clause).length = 1 := by
  cases clause <;> decide

/-! ## Displayed source illustrations -/

inductive IllustrationBlock where
  | fig93ConformerRepresentations
  | torsionClassAngleDiagram
  | torsionHalogenExamples
  | torsionSelectionCriteriaExamples
  | lonePairAndDuplicateAtomExamples
  | eclipsedStaggeredGaucheExamples
  | bisectingEclipsingExample
  | sCisSTransExamples
  | envelopeExample
  | chairBoatTwistExamples
  | halfChairExample
  | crownExamples
  | tubExample
  | inOutExampleOne
  | inOutExampleTwo
  deriving DecidableEq, Repr

namespace IllustrationBlock

def all : List IllustrationBlock :=
  [ .fig93ConformerRepresentations
  , .torsionClassAngleDiagram
  , .torsionHalogenExamples
  , .torsionSelectionCriteriaExamples
  , .lonePairAndDuplicateAtomExamples
  , .eclipsedStaggeredGaucheExamples
  , .bisectingEclipsingExample
  , .sCisSTransExamples
  , .envelopeExample
  , .chairBoatTwistExamples
  , .halfChairExample
  , .crownExamples
  , .tubExample
  , .inOutExampleOne
  , .inOutExampleTwo ]

def clause : IllustrationBlock → P94Clause
  | .fig93ConformerRepresentations => .conformationDefinition
  | .torsionClassAngleDiagram
  | .torsionHalogenExamples
  | .torsionSelectionCriteriaExamples => .torsionAngle
  | .lonePairAndDuplicateAtomExamples => .torsionLonePairs
  | .eclipsedStaggeredGaucheExamples => .eclipsedStaggeredGauche
  | .bisectingEclipsingExample => .trigonalConformations
  | .sCisSTransExamples => .sCisSTrans
  | .envelopeExample => .envelope
  | .chairBoatTwistExamples => .chairBoatTwist
  | .halfChairExample => .halfChair
  | .crownExamples => .crown
  | .tubExample => .tub
  | .inOutExampleOne | .inOutExampleTwo => .inOut

def pdfPage : IllustrationBlock → Nat
  | .fig93ConformerRepresentations => 87
  | .torsionClassAngleDiagram
  | .torsionHalogenExamples
  | .torsionSelectionCriteriaExamples => 88
  | .lonePairAndDuplicateAtomExamples
  | .eclipsedStaggeredGaucheExamples
  | .bisectingEclipsingExample
  | .sCisSTransExamples => 89
  | .envelopeExample
  | .chairBoatTwistExamples
  | .halfChairExample
  | .crownExamples
  | .tubExample => 90
  | .inOutExampleOne | .inOutExampleTwo => 91

@[simp] theorem count : all.length = 15 := by
  decide

theorem all_nodup : all.Nodup := by
  decide

@[simp] theorem pages_exact : all.map pdfPage =
    [87, 88, 88, 88, 89, 89, 89, 89, 90, 90, 90, 90, 90, 91, 91] := by
  rfl

end IllustrationBlock

def illustrationCountsByClause : List (P94Clause × Nat) :=
  P94Clause.all.map fun clause =>
    (clause, (IllustrationBlock.all.filter fun block => block.clause == clause).length)

@[simp] theorem illustration_counts_by_clause_exact :
    illustrationCountsByClause =
      [ (.conformationDefinition, 1), (.torsionAngle, 3), (.torsionLonePairs, 1)
      , (.eclipsedStaggeredGauche, 1), (.trigonalConformations, 1), (.sCisSTrans, 1)
      , (.envelope, 1), (.chairBoatTwist, 1), (.halfChair, 1), (.crown, 1)
      , (.tub, 1), (.inOut, 2) ] := by
  decide

theorem every_clause_has_an_illustration (clause : P94Clause) :
    ∃ block ∈ IllustrationBlock.all, block.clause = clause := by
  cases clause <;>
    first
    | exact ⟨.fig93ConformerRepresentations, by simp [IllustrationBlock.all], rfl⟩
    | exact ⟨.torsionClassAngleDiagram, by simp [IllustrationBlock.all], rfl⟩
    | exact ⟨.lonePairAndDuplicateAtomExamples, by simp [IllustrationBlock.all], rfl⟩
    | exact ⟨.eclipsedStaggeredGaucheExamples, by simp [IllustrationBlock.all], rfl⟩
    | exact ⟨.bisectingEclipsingExample, by simp [IllustrationBlock.all], rfl⟩
    | exact ⟨.sCisSTransExamples, by simp [IllustrationBlock.all], rfl⟩
    | exact ⟨.envelopeExample, by simp [IllustrationBlock.all], rfl⟩
    | exact ⟨.chairBoatTwistExamples, by simp [IllustrationBlock.all], rfl⟩
    | exact ⟨.halfChairExample, by simp [IllustrationBlock.all], rfl⟩
    | exact ⟨.crownExamples, by simp [IllustrationBlock.all], rfl⟩
    | exact ⟨.tubExample, by simp [IllustrationBlock.all], rfl⟩
    | exact ⟨.inOutExampleOne, by simp [IllustrationBlock.all], rfl⟩



structure AutomatedInspection where
  reviewerIdentity : String
  reviewDate : String
  artifactSha256 : String
  digestMatched : Bool
  textExtractionReviewed : Bool
  renderedPagesReviewed : Bool
  sectionRecordCount : Nat
  illustrationBlockCount : Nat
  humanSignoffObtained : Bool
  canonicalSourceProgramInstantiated : Bool
  limitations : String
  deriving DecidableEq, Repr

def currentAutomatedInspection : AutomatedInspection where
  reviewerIdentity := "automated-record-383f307281f3e8334bf1a04ad8470f83"
  reviewDate := "record-5fef69c92fe2101683b1f8429852bf13"
  artifactSha256 := frozenP9Artifact.sha256
  digestMatched := true
  textExtractionReviewed := true
  renderedPagesReviewed := true
  sectionRecordCount := 12
  illustrationBlockCount := 15
  humanSignoffObtained := false
  canonicalSourceProgramInstantiated := false
  limitations :=
    "record-e78ae7f339b405a0d80098859d59673e" ++
    "record-7ff2c3539c467bc496d609aab4f286d5" ++
    "record-10967fe1c9410e1f45938c68f5eefc95"

@[simp] theorem current_automated_inspection_boundary_exact :
    currentAutomatedInspection.digestMatched = true ∧
      currentAutomatedInspection.textExtractionReviewed = true ∧
        currentAutomatedInspection.renderedPagesReviewed = true ∧
          currentAutomatedInspection.humanSignoffObtained = false ∧
            currentAutomatedInspection.canonicalSourceProgramInstantiated = false := by
  decide

theorem current_automated_counts_come_from_exact_ledgers :
    currentAutomatedInspection.sectionRecordCount = sectionRecords.length ∧
      currentAutomatedInspection.illustrationBlockCount = IllustrationBlock.all.length := by
  decide

end P94SourceAuditLedger
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.P94SourceAuditLedger.frozen_p9_digest_matches_manifest
assert_kernel_only TetraStereo.OneCenter.P94SourceAuditLedger.section_record_clauses_exact
assert_kernel_only TetraStereo.OneCenter.P94SourceAuditLedger.section_record_page_ranges_exact
assert_kernel_only TetraStereo.OneCenter.P94SourceAuditLedger.section_record_clauses_nodup
assert_kernel_only
  TetraStereo.OneCenter.P94SourceAuditLedger.every_clause_has_exactly_one_section_record
assert_kernel_only TetraStereo.OneCenter.P94SourceAuditLedger.IllustrationBlock.pages_exact
assert_kernel_only TetraStereo.OneCenter.P94SourceAuditLedger.illustration_counts_by_clause_exact
assert_kernel_only TetraStereo.OneCenter.P94SourceAuditLedger.every_clause_has_an_illustration
assert_kernel_only TetraStereo.OneCenter.P94SourceAuditLedger.current_automated_inspection_boundary_exact
assert_kernel_only TetraStereo.OneCenter.P94SourceAuditLedger.current_automated_counts_come_from_exact_ledgers
