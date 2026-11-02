import TetraStereo.OneCenter.IUPACGlobalNonDescriptorSteroidSourceMeaningBatch
import TetraStereo.KernelOnly

set_option autoImplicit false
















namespace TetraStereo.OneCenter
namespace Steroid1989
namespace TechnicalAuditReadiness

open IUPACNormativeProvision
open IUPACNormativeProvision.GlobalNonDescriptorSteroidSourceMeaning

def sourceSnapshot : P10DelegatedAuthorityCorpus.Snapshot :=
  P10DelegatedAuthorityCorpus.snapshot .steroid1989

def modeledProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorSteroidSourceMeaning.provisions

def compiledEntries : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorSteroidSourceMeaning.batch.entries

def table1Parents : List Steroid1989.Table1Parent :=
  GlobalNonDescriptorSteroidSourceMeaning.table1Inventory.map Prod.fst

def vitaminDTableRows : List Steroid1989.VitaminDParent :=
  GlobalNonDescriptorSteroidSourceMeaning.vitaminDParents

def sourceReviewEvidence : Steroid1989.SourceReviewEvidence :=
  Steroid1989.currentSourceReview

@[simp] theorem source_snapshot_counts_exact :
    sourceSnapshot.artifactCount = 100 ∧
      sourceSnapshot.htmlCount = 23 ∧
        sourceSnapshot.imageCount = 77 := by
  decide

@[simp] theorem source_snapshot_partition_exact :
    sourceSnapshot.htmlCount + sourceSnapshot.imageCount =
      sourceSnapshot.artifactCount := by
  simp [sourceSnapshot]

@[simp] theorem modeled_provision_count : modeledProvisions.length = 62 := by
  simp [modeledProvisions]

@[simp] theorem compiled_entry_count : compiledEntries.length = 62 := by
  simp [compiledEntries]

@[simp] theorem compiled_entry_provisions_exact :
    compiledEntries.map GlobalNonDescriptorSourceMeaningEntry.provision =
      modeledProvisions := by
  simp [compiledEntries, modeledProvisions]

theorem modeled_provisions_nodup : modeledProvisions.Nodup := by
  unfold modeledProvisions
  exact GlobalNonDescriptorSteroidSourceMeaning.provisions_nodup

@[simp] theorem table1_parent_count : table1Parents.length = 8 := by
  decide

@[simp] theorem vitamin_d_table_row_count : vitaminDTableRows.length = 11 := by
  decide

@[simp] theorem both_tacalciol_rows_retained :
    Steroid1989.VitaminDParent.preTacalciol ∈ vitaminDTableRows ∧
      Steroid1989.VitaminDParent.tacalciol ∈ vitaminDTableRows := by
  decide

theorem every_compiled_entry_nonvacuous
    (entry : GlobalNonDescriptorSourceMeaningEntry)
    (member : entry ∈ compiledEntries) :
    ∃ input, ∃ observation : entry.reference.toReference.Observation,
      input.StructurallyWellFormed ∧
        entry.reference.toReference.Applicable input ∧
          entry.reference.toReference.Judges input observation := by
  exact GlobalNonDescriptorSteroidSourceMeaning.every_entry_nonvacuous entry
    (by simpa [compiledEntries] using member)

/-! ## One proof-carrying machine dossier -/

structure TechnicalEvidence where
  sourceArtifactCount : Nat
  sourceHtmlCount : Nat
  sourceImageCount : Nat
  modeledProvisionCount : Nat
  compiledEntryCount : Nat
  table1ParentCount : Nat
  vitaminDTableRowCount : Nat
  sourceRootUrl : String
  sourceRetrievalDate : String
  sourceBundleSha256 : String
  sourceReview : Steroid1989.SourceReviewEvidence
  sourceArtifactCountExact : sourceArtifactCount = sourceSnapshot.artifactCount
  sourceHtmlCountExact : sourceHtmlCount = sourceSnapshot.htmlCount
  sourceImageCountExact : sourceImageCount = sourceSnapshot.imageCount
  modeledProvisionCountExact : modeledProvisionCount = modeledProvisions.length
  compiledEntryCountExact : compiledEntryCount = compiledEntries.length
  table1ParentCountExact : table1ParentCount = table1Parents.length
  vitaminDTableRowCountExact : vitaminDTableRowCount = vitaminDTableRows.length
  sourceRootUrlExact : sourceRootUrl = sourceSnapshot.rootUrl
  sourceRetrievalDateExact : sourceRetrievalDate = sourceSnapshot.retrievalDate
  sourceBundleSha256Exact : sourceBundleSha256 = sourceSnapshot.bundleSha256
  sourceReviewExact : sourceReview = sourceReviewEvidence
  sourceArtifactPartitionExact :
    sourceSnapshot.htmlCount + sourceSnapshot.imageCount = sourceSnapshot.artifactCount
  modeledProvisionsNodup : modeledProvisions.Nodup
  compiledEntryProvisionsExact :
    compiledEntries.map GlobalNonDescriptorSourceMeaningEntry.provision = modeledProvisions
  bothTacalciolRowsRetained :
    Steroid1989.VitaminDParent.preTacalciol ∈ vitaminDTableRows ∧
      Steroid1989.VitaminDParent.tacalciol ∈ vitaminDTableRows
  allCompiledEntriesNonvacuous :
    ∀ entry ∈ compiledEntries,
      ∃ input, ∃ observation : entry.reference.toReference.Observation,
        input.StructurallyWellFormed ∧
          entry.reference.toReference.Applicable input ∧
            entry.reference.toReference.Judges input observation

def currentTechnicalEvidence : TechnicalEvidence where
  sourceArtifactCount := 100
  sourceHtmlCount := 23
  sourceImageCount := 77
  modeledProvisionCount := 62
  compiledEntryCount := 62
  table1ParentCount := 8
  vitaminDTableRowCount := 11
  sourceRootUrl := "https://iupac.qmul.ac.uk/steroid/"
  sourceRetrievalDate := "2026-08-11"
  sourceBundleSha256 :=
    "83cb309d8a3674ca7b6dfb90a0600a4a442aa17e3f3f2bcc898a705f06241210"
  sourceReview := sourceReviewEvidence
  sourceArtifactCountExact := by simp
  sourceHtmlCountExact := by simp
  sourceImageCountExact := by simp
  modeledProvisionCountExact := by simp
  compiledEntryCountExact := by simp
  table1ParentCountExact := by simp
  vitaminDTableRowCountExact := by simp
  sourceRootUrlExact := rfl
  sourceRetrievalDateExact := rfl
  sourceBundleSha256Exact := rfl
  sourceReviewExact := rfl
  sourceArtifactPartitionExact := source_snapshot_partition_exact
  modeledProvisionsNodup := modeled_provisions_nodup
  compiledEntryProvisionsExact := compiled_entry_provisions_exact
  bothTacalciolRowsRetained := both_tacalciol_rows_retained
  allCompiledEntriesNonvacuous := every_compiled_entry_nonvacuous

@[simp] theorem current_technical_evidence_counts_exact :
    currentTechnicalEvidence.sourceArtifactCount = 100 ∧
      currentTechnicalEvidence.sourceHtmlCount = 23 ∧
        currentTechnicalEvidence.sourceImageCount = 77 ∧
          currentTechnicalEvidence.modeledProvisionCount = 62 ∧
            currentTechnicalEvidence.compiledEntryCount = 62 ∧
              currentTechnicalEvidence.table1ParentCount = 8 ∧
                currentTechnicalEvidence.vitaminDTableRowCount = 11 := by
  decide



def currentOpenSteroidReviewRequirements :
    List IUPACNormativeSource.ProvisionAuditRequirement :=
  IUPACNormativeSource.currentOpenProvisionAuditRequirements
    .steroidRecommendations1989

@[simp] theorem current_open_steroid_review_requirements_exact :
    currentOpenSteroidReviewRequirements =
      [ .figureGraphTranscriptionsReviewed ] := by
  decide

@[simp] theorem current_source_review_manifest_gates_exact :
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .steroidRecommendations1989).provisionEnumerationConfirmed = true ∧
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .steroidRecommendations1989).proseTableCoverageConfirmed = true ∧
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .steroidRecommendations1989).figureGraphTranscriptionsReviewed = false := by
  decide


def currentIndependentReviewPackageIssued : Bool := false

@[simp] theorem current_independent_review_package_not_issued :
    currentIndependentReviewPackageIssued = false := by
  rfl

structure MachinePreparedForIndependentReview where
  evidence : TechnicalEvidence
  evidenceExact : evidence = currentTechnicalEvidence
  openRequirementsExact : currentOpenSteroidReviewRequirements =
    [ .figureGraphTranscriptionsReviewed ]

def currentMachinePreparedForIndependentReview :
    MachinePreparedForIndependentReview where
  evidence := currentTechnicalEvidence
  evidenceExact := rfl
  openRequirementsExact := current_open_steroid_review_requirements_exact

theorem current_steroid_audit_remains_incomplete :
    ¬IUPACNormativeSource.ProvisionAuditComplete .steroidRecommendations1989 := by
  simp [IUPACNormativeSource.ProvisionAuditComplete,
    IUPACNormativeSource.currentProvisionAuditChecklist,
    IUPACNormativeSource.ProvisionAuditChecklist.Complete,
    Steroid1989.currentSourceReviewProvisionEnumerationConfirmed,
    Steroid1989.currentSourceReviewProseTableCoverageConfirmed,
    Steroid1989.currentSourceReviewFigureGraphTranscriptionsReviewed]

end TechnicalAuditReadiness
end Steroid1989
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Steroid1989.TechnicalAuditReadiness.source_snapshot_partition_exact
assert_kernel_only
  TetraStereo.OneCenter.Steroid1989.TechnicalAuditReadiness.compiled_entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.Steroid1989.TechnicalAuditReadiness.both_tacalciol_rows_retained
assert_kernel_only
  TetraStereo.OneCenter.Steroid1989.TechnicalAuditReadiness.every_compiled_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.Steroid1989.TechnicalAuditReadiness.currentTechnicalEvidence
assert_kernel_only
  TetraStereo.OneCenter.Steroid1989.TechnicalAuditReadiness.sourceReviewEvidence
assert_kernel_only
  TetraStereo.OneCenter.Steroid1989.TechnicalAuditReadiness.current_open_steroid_review_requirements_exact
assert_kernel_only
  TetraStereo.OneCenter.Steroid1989.TechnicalAuditReadiness.current_source_review_manifest_gates_exact
assert_kernel_only
  TetraStereo.OneCenter.Steroid1989.TechnicalAuditReadiness.current_steroid_audit_remains_incomplete
