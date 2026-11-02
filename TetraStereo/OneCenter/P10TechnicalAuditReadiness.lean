import TetraStereo.OneCenter.IUPACGlobalNonDescriptorP10SourceMeaningBatch
import TetraStereo.KernelOnly
import TetraStereo.OneCenter.P10FigureTranscriptionContract

set_option autoImplicit false



















namespace TetraStereo.OneCenter
namespace P10TechnicalAuditReadiness

open IUPACNormativeProvision
open IUPACNormativeProvision.GlobalNonDescriptorP10SourceMeaning

def sourceUrl : String :=
  IUPACNormativeSource.url .blueBook2013P10

/-- Digest currently frozen in the normative manifest. -/
def expectedFrozenSha256 : String :=
  match IUPACNormativeSource.sha256? .blueBook2013P10 with
  | some digest => digest
  | none => ""

/-- SHA-256 of the response served by the official P-10 URL on 2026-08-29. -/
def liveOfficialSha256 : String :=
  "e1185116ad0e61641832931ad87d333e14a8b37ce55e8a19e4570c4c1b42bedf"

def liveOfficialRetrievalDate : String := "record-54db71cc66a48d655191405c29c6a9ac"

def liveOfficialByteCount : Nat := 3627951

def liveOfficialPageCount : Nat := 113

/-- Capture date for the last known pre-recompression official response. -/
def archivedPreReplacementCaptureDate : String := "2024-08-28"

/-- Response length reported by the archive for that capture; not a claim of local recovery. -/
def archivedPreReplacementByteCount : Nat := 8798833

/-- The final 410,225-byte range is not locally available, so exact digest verification is open. -/
def archivedPreReplacementBytesFullyRecovered : Bool := false

/-- All PDF page numbers visually inspected across P-101 through P-107. -/
def visuallyInspectedPages : List Nat :=
  (List.range liveOfficialPageCount).map (fun page => page + 1)

def rows : List BlueBookP10Audit.Provision :=
  BlueBookP10Audit.Provision.all

def p101Rows : List BlueBookP10Audit.Provision :=
  BlueBookP101.p101Provisions

def p102Rows : List BlueBookP10Audit.Provision :=
  BlueBookP102.p102Provisions

def p103to107Rows : List BlueBookP10Audit.Provision :=
  BlueBookP103to107.p103to107Provisions

def provisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorP10SourceMeaning.provisions

def compiledEntries : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorP10SourceMeaning.batch.entries

def figureImageOccurrences : List P10FigureTranscription.FigureOccurrence :=
  P10FigureTranscription.allImageOccurrences

def literalFigureObjectReuses : List P10FigureTranscription.LiteralObjectReuse :=
  P10FigureTranscription.literalObjectReuses

def figureReviewTargets : List P10FigureTranscription.FigureOccurrence :=
  P10FigureTranscription.canonicalFigureTargets

def currentReviewedFigureTranscriptions :=
  P10FigureTranscription.currentReviewedTranscriptions

@[simp] theorem manifest_frozen_digest_exact :
    expectedFrozenSha256 =
      "e1185116ad0e61641832931ad87d333e14a8b37ce55e8a19e4570c4c1b42bedf" := by
  rfl

@[simp] theorem live_official_artifact_exact :
    liveOfficialSha256 =
        "e1185116ad0e61641832931ad87d333e14a8b37ce55e8a19e4570c4c1b42bedf" ∧
      liveOfficialByteCount = 3627951 ∧
        liveOfficialPageCount = 113 := by
  decide

@[simp] theorem archived_pre_replacement_recovery_boundary_exact :
    archivedPreReplacementByteCount = 8798833 ∧
      archivedPreReplacementCaptureDate = "2024-08-28" ∧
        archivedPreReplacementBytesFullyRecovered = false := by
  decide

theorem live_official_digest_matches_frozen_manifest :
    liveOfficialSha256 = expectedFrozenSha256 := by
  rfl

@[simp] theorem visually_inspected_pages_exact :
    visuallyInspectedPages = (List.range 113).map (fun page => page + 1) ∧
      visuallyInspectedPages.length = 113 := by
  decide

@[simp] theorem section_partition_counts_exact :
    rows.length = 71 ∧
      p101Rows.length = 19 ∧
        p102Rows.length = 28 ∧
          p103to107Rows.length = 24 := by
  decide

theorem rows_partition_exact :
    p101Rows ++ p102Rows ++ p103to107Rows = rows := by
  decide

@[simp] theorem compiled_family_exact :
    compiledEntries.length = 71 ∧
      compiledEntries.map GlobalNonDescriptorSourceMeaningEntry.provision = provisions := by
  exact ⟨GlobalNonDescriptorP10SourceMeaning.entry_count,
    GlobalNonDescriptorP10SourceMeaning.entry_provisions_exact⟩

@[simp] theorem figure_inventory_counts_and_open_review_exact :
    figureImageOccurrences.length = 476 ∧
      literalFigureObjectReuses.length = 3 ∧
        figureReviewTargets.length = 473 ∧
          currentReviewedFigureTranscriptions = [] := by
  exact ⟨P10FigureTranscription.image_occurrence_count_exact,
    P10FigureTranscription.literal_object_reuse_count_exact,
    P10FigureTranscription.canonical_figure_target_count_exact, rfl⟩

@[simp] theorem delegated_dependency_counts_exact :
    BlueBookP10Audit.provisionsWithExplicitExternalDependency.length = 57 ∧
      BlueBookP10Audit.ExternalAuthority.all.length = 9 := by
  decide

@[simp] theorem current_provision_enumeration_review_exact :
    BlueBookP10Audit.currentProvisionEnumerationReview.sourceArtifactSha256 =
        liveOfficialSha256 ∧
      BlueBookP10Audit.currentProvisionEnumerationReview.auditedRows.length = 71 ∧
        BlueBookP10Audit.currentProvisionEnumerationReview.sourceSectionReferences.length = 71 ∧
          BlueBookP10Audit.currentProvisionEnumerationReview.crosswalkedPrimarySectionTokenCount = 69 ∧
            BlueBookP10Audit.currentProvisionEnumerationReview.missingPrimarySectionTokens = [] ∧
              BlueBookP10Audit.currentProvisionEnumerationReview.reverseKeywordBearingSectionCount = 120 ∧
                BlueBookP10Audit.currentProvisionEnumerationReview.unmatchedReverseKeywordSections = [] := by
  decide

theorem every_compiled_entry_nonvacuous
    (entry : GlobalNonDescriptorSourceMeaningEntry) (member : entry ∈ compiledEntries) :
    ∃ input, ∃ observation : entry.reference.toReference.Observation,
      input.StructurallyWellFormed ∧
        entry.reference.toReference.Applicable input ∧
          entry.reference.toReference.Judges input observation :=
  GlobalNonDescriptorP10SourceMeaning.every_entry_nonvacuous entry member

def sourceReviewEvidence : BlueBookP10Audit.SourceReviewEvidence :=
  BlueBookP10Audit.currentSourceReview

@[simp] theorem source_review_counts_and_gates_exact :
    sourceReviewEvidence.reviewedRenderedPages = 113 ∧
      sourceReviewEvidence.reviewedProvisions.length = 71 ∧
        sourceReviewEvidence.provisionEnumerationConfirmed = true ∧
          sourceReviewEvidence.proseTableCoverageConfirmed = true ∧
            sourceReviewEvidence.figureGraphTranscriptionsReviewed = false := by
  decide

/-! ## One proof-carrying machine dossier -/

structure TechnicalEvidence where
  manifestFrozenSha256 : String
  observedLiveSha256 : String
  observedLiveByteCount : Nat
  observedLivePageCount : Nat
  archiveReportedByteCount : Nat
  modeledRowCount : Nat
  compiledEntryCount : Nat
  delegatedRowCount : Nat
  externalAuthorityCount : Nat
  provisionEnumerationReview : BlueBookP10Audit.ProvisionEnumerationReviewEvidence
  sourceReview : BlueBookP10Audit.SourceReviewEvidence
  manifestFrozenSha256Exact : manifestFrozenSha256 = expectedFrozenSha256
  observedLiveSha256Exact : observedLiveSha256 = liveOfficialSha256
  observedLiveByteCountExact : observedLiveByteCount = liveOfficialByteCount
  observedLivePageCountExact : observedLivePageCount = liveOfficialPageCount
  archiveReportedByteCountExact : archiveReportedByteCount = archivedPreReplacementByteCount
  modeledRowCountExact : modeledRowCount = rows.length
  compiledEntryCountExact : compiledEntryCount = compiledEntries.length
  delegatedRowCountExact :
    delegatedRowCount = BlueBookP10Audit.provisionsWithExplicitExternalDependency.length
  externalAuthorityCountExact :
    externalAuthorityCount = BlueBookP10Audit.ExternalAuthority.all.length
  provisionEnumerationReviewExact :
    provisionEnumerationReview = BlueBookP10Audit.currentProvisionEnumerationReview
  sourceReviewExact : sourceReview = sourceReviewEvidence
  liveDigestMatchesManifest : observedLiveSha256 = manifestFrozenSha256
  archivedBytesNotFullyRecovered : archivedPreReplacementBytesFullyRecovered = false
  rowsPartitionExact : p101Rows ++ p102Rows ++ p103to107Rows = rows
  compiledEntryProvisionsExact :
    compiledEntries.map GlobalNonDescriptorSourceMeaningEntry.provision = provisions
  allCompiledEntriesNonvacuous :
    ∀ entry ∈ compiledEntries,
      ∃ input, ∃ observation : entry.reference.toReference.Observation,
        input.StructurallyWellFormed ∧
          entry.reference.toReference.Applicable input ∧
            entry.reference.toReference.Judges input observation

def currentTechnicalEvidence : TechnicalEvidence where
  manifestFrozenSha256 := expectedFrozenSha256
  observedLiveSha256 := liveOfficialSha256
  observedLiveByteCount := liveOfficialByteCount
  observedLivePageCount := liveOfficialPageCount
  archiveReportedByteCount := archivedPreReplacementByteCount
  modeledRowCount := 71
  compiledEntryCount := 71
  delegatedRowCount := 57
  externalAuthorityCount := 9
  provisionEnumerationReview := BlueBookP10Audit.currentProvisionEnumerationReview
  sourceReview := sourceReviewEvidence
  manifestFrozenSha256Exact := rfl
  observedLiveSha256Exact := rfl
  observedLiveByteCountExact := rfl
  observedLivePageCountExact := rfl
  archiveReportedByteCountExact := rfl
  modeledRowCountExact := by simp
  compiledEntryCountExact := by simp
  delegatedRowCountExact := by simp
  externalAuthorityCountExact := by simp
  provisionEnumerationReviewExact := rfl
  sourceReviewExact := rfl
  liveDigestMatchesManifest := live_official_digest_matches_frozen_manifest
  archivedBytesNotFullyRecovered := rfl
  rowsPartitionExact := rows_partition_exact
  compiledEntryProvisionsExact := compiled_family_exact.2
  allCompiledEntriesNonvacuous := every_compiled_entry_nonvacuous



def currentOpenP10ReviewRequirements :
    List IUPACNormativeSource.ProvisionAuditRequirement :=
  IUPACNormativeSource.currentOpenProvisionAuditRequirements .blueBook2013P10

@[simp] theorem current_open_p10_review_requirements_exact :
    currentOpenP10ReviewRequirements =
      [ .figureGraphTranscriptionsReviewed ] := by
  decide

@[simp] theorem current_source_review_manifest_gates_exact :
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .blueBook2013P10).provisionEnumerationConfirmed = true ∧
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .blueBook2013P10).proseTableCoverageConfirmed = true ∧
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .blueBook2013P10).figureGraphTranscriptionsReviewed = false := by
  decide

def currentIndependentReviewPackageIssued : Bool := false

@[simp] theorem current_independent_review_package_not_issued :
    currentIndependentReviewPackageIssued = false := by
  rfl

structure MachinePreparedForIndependentReview where
  evidence : TechnicalEvidence
  evidenceExact : evidence = currentTechnicalEvidence
  openRequirementsExact : currentOpenP10ReviewRequirements =
    [ .figureGraphTranscriptionsReviewed ]

def currentMachinePreparedForIndependentReview :
    MachinePreparedForIndependentReview where
  evidence := currentTechnicalEvidence
  evidenceExact := rfl
  openRequirementsExact := current_open_p10_review_requirements_exact

theorem current_p10_audit_remains_incomplete :
    ¬IUPACNormativeSource.ProvisionAuditComplete .blueBook2013P10 := by
  simp [IUPACNormativeSource.ProvisionAuditComplete,
    IUPACNormativeSource.currentProvisionAuditChecklist,
    IUPACNormativeSource.ProvisionAuditChecklist.Complete,
    BlueBookP10Audit.currentSourceReviewProvisionEnumerationConfirmed,
    BlueBookP10Audit.currentSourceReviewProseTableCoverageConfirmed,
    BlueBookP10Audit.currentSourceReviewFigureGraphTranscriptionsReviewed]

end P10TechnicalAuditReadiness
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P10TechnicalAuditReadiness.live_official_digest_matches_frozen_manifest
assert_kernel_only
  TetraStereo.OneCenter.P10TechnicalAuditReadiness.rows_partition_exact
assert_kernel_only
  TetraStereo.OneCenter.P10TechnicalAuditReadiness.compiled_family_exact
assert_kernel_only
  TetraStereo.OneCenter.P10TechnicalAuditReadiness.current_provision_enumeration_review_exact
assert_kernel_only
  TetraStereo.OneCenter.P10TechnicalAuditReadiness.every_compiled_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.P10TechnicalAuditReadiness.sourceReviewEvidence
assert_kernel_only
  TetraStereo.OneCenter.P10TechnicalAuditReadiness.current_source_review_manifest_gates_exact
