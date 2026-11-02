import TetraStereo.OneCenter.IUPACGlobalNonDescriptorAppendix3SourceMeanings
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192
















namespace TetraStereo.OneCenter
namespace Appendix3
namespace TechnicalAuditReadiness

open IUPACNormativeProvision
open IUPACNormativeProvision.GlobalNonDescriptorAppendix3SourceMeanings

def provisions : List BlueBookAppendix3Audit.Provision :=
  BlueBookAppendix3Audit.Provision.all

def meanings : List Appendix3StructureMeaning :=
  IUPACNormativeProvision.GlobalNonDescriptorAppendix3SourceMeanings.meanings

def reviewEntries : List Appendix3ReviewEntry :=
  IUPACNormativeProvision.GlobalNonDescriptorAppendix3SourceMeanings.reviewEntries

@[simp] theorem provision_count : provisions.length = 171 := by
  simp [provisions]

@[simp] theorem meaning_count : meanings.length = 171 := by
  simp [meanings]

@[simp] theorem review_entry_count : reviewEntries.length = 171 := by
  simp [reviewEntries]

@[simp] theorem meaning_origin_counts :
    (meanings.filter fun meaning => meaning.origin = .directDrawing).length = 147 ∧
      (meanings.filter fun meaning => meaning.origin = .composedCaroteneParent).length = 24 := by
  simp [meanings]

@[simp] theorem all_meanings_graph_level_complete :
    meanings.all Appendix3StructureMeaning.complete = true := by
  simp [meanings]

@[simp] theorem all_review_entries_machine_complete :
    reviewEntries.all Appendix3ReviewEntry.complete = true := by
  simp [reviewEntries]

@[simp] theorem reviewed_mirror_bytes_remain_distinct :
    reviewEntries.all (fun entry => !entry.mirrorDigestMatchesFrozen) = true := by
  simp [reviewEntries]

def sourceReviewEvidence : BlueBookAppendix3Audit.SourceReviewEvidence :=
  BlueBookAppendix3Audit.currentSourceReview

structure TechnicalEvidence where
  provisionCount : Nat
  meaningCount : Nat
  reviewEntryCount : Nat
  directDrawingCount : Nat
  composedCaroteneParentCount : Nat
  sourcePageCount : Nat
  frozenSourceSha256 : String
  reviewedMirrorSha256 : String
  sourceReview : BlueBookAppendix3Audit.SourceReviewEvidence
  provisionCountExact : provisionCount = provisions.length
  meaningCountExact : meaningCount = meanings.length
  reviewEntryCountExact : reviewEntryCount = reviewEntries.length
  originCountsExact :
    (meanings.filter fun meaning => meaning.origin = .directDrawing).length =
        directDrawingCount ∧
      (meanings.filter fun meaning => meaning.origin = .composedCaroteneParent).length =
        composedCaroteneParentCount
  sourcePageCountExact : sourcePageCount =
    IUPACNormativeProvision.GlobalNonDescriptorAppendix3SourceMeanings.sourcePageCount
  frozenSourceSha256Exact : frozenSourceSha256 =
    IUPACNormativeProvision.GlobalNonDescriptorAppendix3SourceMeanings.frozenSourceSha256
  reviewedMirrorSha256Exact : reviewedMirrorSha256 =
    IUPACNormativeProvision.GlobalNonDescriptorAppendix3SourceMeanings.reviewedMirrorSha256
  sourceReviewExact : sourceReview = sourceReviewEvidence
  meaningsComplete : meanings.all Appendix3StructureMeaning.complete = true
  reviewsMachineComplete : reviewEntries.all Appendix3ReviewEntry.complete = true
  mirrorBytesRemainDistinct :
    reviewEntries.all (fun entry => !entry.mirrorDigestMatchesFrozen) = true

def currentTechnicalEvidence : TechnicalEvidence where
  provisionCount := 171
  meaningCount := 171
  reviewEntryCount := 171
  directDrawingCount := 147
  composedCaroteneParentCount := 24
  sourcePageCount := 29
  frozenSourceSha256 :=
    "e7f9d689cb5bd19b3c7f30aab7f0df0a73865b6f11e9427e9580c2654a8d9043"
  reviewedMirrorSha256 :=
    "20c588c9d9bfd78f57d89bd7e0123bb1c9b0354191f80ace1f368e2b8290c962"
  sourceReview := sourceReviewEvidence
  provisionCountExact := by simp
  meaningCountExact := by simp
  reviewEntryCountExact := by simp
  originCountsExact := meaning_origin_counts
  sourcePageCountExact := rfl
  frozenSourceSha256Exact := rfl
  reviewedMirrorSha256Exact := rfl
  sourceReviewExact := rfl
  meaningsComplete := all_meanings_graph_level_complete
  reviewsMachineComplete := all_review_entries_machine_complete
  mirrorBytesRemainDistinct := reviewed_mirror_bytes_remain_distinct

@[simp] theorem current_technical_evidence_counts_exact :
    currentTechnicalEvidence.provisionCount = 171 ∧
      currentTechnicalEvidence.meaningCount = 171 ∧
        currentTechnicalEvidence.reviewEntryCount = 171 ∧
          currentTechnicalEvidence.directDrawingCount = 147 ∧
            currentTechnicalEvidence.composedCaroteneParentCount = 24 ∧
              currentTechnicalEvidence.sourcePageCount = 29 := by
  decide

@[simp] theorem source_review_counts_and_gates_exact :
    sourceReviewEvidence.sourceArtifactSha256 =
        currentTechnicalEvidence.reviewedMirrorSha256 ∧
      sourceReviewEvidence.reviewedRenderedPages = 29 ∧
        sourceReviewEvidence.reviewedRenderedPageNumbers.length = 29 ∧
          sourceReviewEvidence.reviewedProvisions.length = 171 ∧
            sourceReviewEvidence.provisionEnumerationConfirmed = true ∧
              sourceReviewEvidence.proseTableCoverageConfirmed = true ∧
                sourceReviewEvidence.figureGraphTranscriptionsReviewed = false := by
  decide

def currentOpenAppendix3ReviewRequirements :
    List IUPACNormativeSource.ProvisionAuditRequirement :=
  IUPACNormativeSource.currentOpenProvisionAuditRequirements .blueBook2013Appendix3

@[simp] theorem current_open_appendix3_review_requirements_exact :
    currentOpenAppendix3ReviewRequirements =
      [ .figureGraphTranscriptionsReviewed ] := by
  decide

@[simp] theorem current_source_review_manifest_gates_exact :
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .blueBook2013Appendix3).provisionEnumerationConfirmed = true ∧
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .blueBook2013Appendix3).proseTableCoverageConfirmed = true ∧
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .blueBook2013Appendix3).figureGraphTranscriptionsReviewed = false := by
  decide

def currentIndependentReviewPackageIssued : Bool := false

@[simp] theorem current_independent_review_package_not_issued :
    currentIndependentReviewPackageIssued = false := by
  rfl

theorem current_appendix3_audit_remains_incomplete :
    ¬IUPACNormativeSource.ProvisionAuditComplete .blueBook2013Appendix3 := by
  simp [IUPACNormativeSource.ProvisionAuditComplete,
    IUPACNormativeSource.currentProvisionAuditChecklist,
    IUPACNormativeSource.ProvisionAuditChecklist.Complete,
    BlueBookAppendix3Audit.currentSourceReviewProvisionEnumerationConfirmed,
    BlueBookAppendix3Audit.currentSourceReviewProseTableCoverageConfirmed,
    BlueBookAppendix3Audit.currentSourceReviewFigureGraphTranscriptionsReviewed]

end TechnicalAuditReadiness
end Appendix3
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Appendix3.TechnicalAuditReadiness.meaning_origin_counts
assert_kernel_only
  TetraStereo.OneCenter.Appendix3.TechnicalAuditReadiness.all_meanings_graph_level_complete
assert_kernel_only
  TetraStereo.OneCenter.Appendix3.TechnicalAuditReadiness.all_review_entries_machine_complete
assert_kernel_only
  TetraStereo.OneCenter.Appendix3.TechnicalAuditReadiness.reviewed_mirror_bytes_remain_distinct
assert_kernel_only
  TetraStereo.OneCenter.Appendix3.TechnicalAuditReadiness.currentTechnicalEvidence
assert_kernel_only
  TetraStereo.OneCenter.Appendix3.TechnicalAuditReadiness.sourceReviewEvidence
assert_kernel_only
  TetraStereo.OneCenter.Appendix3.TechnicalAuditReadiness.source_review_counts_and_gates_exact
assert_kernel_only
  TetraStereo.OneCenter.Appendix3.TechnicalAuditReadiness.current_open_appendix3_review_requirements_exact
assert_kernel_only
  TetraStereo.OneCenter.Appendix3.TechnicalAuditReadiness.current_appendix3_audit_remains_incomplete
