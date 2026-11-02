import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCarotenoidSourceMeaningBatch
import TetraStereo.KernelOnly

set_option autoImplicit false
















namespace TetraStereo.OneCenter
namespace Carotenoid1974
namespace TechnicalAuditReadiness

open IUPACNormativeProvision
open IUPACNormativeProvision.GlobalNonDescriptorCarotenoidSourceMeaning

def sourceSnapshot : P10DelegatedAuthorityCorpus.Snapshot :=
  P10DelegatedAuthorityCorpus.snapshot .carotenoid1974

def modeledProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorCarotenoidSourceMeaning.provisions

def compiledEntries : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorCarotenoidSourceMeaning.batch.entries

def cyclicNumberingCases :=
  GlobalNonDescriptorCarotenoidSourceMeaning.cyclicNumberingAssignments

def acyclicNumberingCases :=
  GlobalNonDescriptorCarotenoidSourceMeaning.acyclicNumberingAssignments

def sourceReviewEvidence : Carotenoid1974.SourceReviewEvidence :=
  Carotenoid1974.currentSourceReview

@[simp] theorem source_snapshot_counts_exact :
    sourceSnapshot.artifactCount = 52 ∧
      sourceSnapshot.htmlCount = 4 ∧
        sourceSnapshot.imageCount = 48 := by
  decide

@[simp] theorem source_snapshot_partition_exact :
    sourceSnapshot.htmlCount + sourceSnapshot.imageCount =
      sourceSnapshot.artifactCount := by
  simp [sourceSnapshot]

@[simp] theorem modeled_provision_count : modeledProvisions.length = 10 := by
  simp [modeledProvisions]

@[simp] theorem compiled_entry_count : compiledEntries.length = 10 := by
  simp [compiledEntries]

@[simp] theorem compiled_entry_provisions_exact :
    compiledEntries.map GlobalNonDescriptorSourceMeaningEntry.provision =
      modeledProvisions := by
  simp [compiledEntries, modeledProvisions]

theorem modeled_provisions_nodup : modeledProvisions.Nodup := by
  unfold modeledProvisions
  exact GlobalNonDescriptorCarotenoidSourceMeaning.provisions_nodup

@[simp] theorem methyl_numbering_case_counts_exact :
    cyclicNumberingCases.length = 6 ∧
      acyclicNumberingCases.length = 2 := by
  decide

@[simp] theorem all_double_bonds_scope_exact :
    (GlobalNonDescriptorCarotenoidSourceMeaning.sourceMeaning
      .caroteneStemDefaultsToAllTrans).assertion =
        .caroteneStemDefaultsToAllTrans
          Carotenoid1974.CaroteneDoubleBondScope.allDoubleBonds .trans := by
  rfl

theorem every_compiled_entry_nonvacuous
    (entry : GlobalNonDescriptorSourceMeaningEntry)
    (member : entry ∈ compiledEntries) :
    ∃ input, ∃ observation : entry.reference.toReference.Observation,
      input.StructurallyWellFormed ∧
        entry.reference.toReference.Applicable input ∧
          entry.reference.toReference.Judges input observation := by
  exact GlobalNonDescriptorCarotenoidSourceMeaning.every_entry_nonvacuous entry
    (by simpa [compiledEntries] using member)

structure TechnicalEvidence where
  sourceArtifactCount : Nat
  sourceHtmlCount : Nat
  sourceImageCount : Nat
  modeledProvisionCount : Nat
  compiledEntryCount : Nat
  cyclicNumberingCaseCount : Nat
  acyclicNumberingCaseCount : Nat
  sourceRootUrl : String
  sourceRetrievalDate : String
  sourceBundleSha256 : String
  sourceReview : Carotenoid1974.SourceReviewEvidence
  sourceArtifactCountExact : sourceArtifactCount = sourceSnapshot.artifactCount
  sourceHtmlCountExact : sourceHtmlCount = sourceSnapshot.htmlCount
  sourceImageCountExact : sourceImageCount = sourceSnapshot.imageCount
  modeledProvisionCountExact : modeledProvisionCount = modeledProvisions.length
  compiledEntryCountExact : compiledEntryCount = compiledEntries.length
  cyclicNumberingCaseCountExact :
    cyclicNumberingCaseCount = cyclicNumberingCases.length
  acyclicNumberingCaseCountExact :
    acyclicNumberingCaseCount = acyclicNumberingCases.length
  sourceRootUrlExact : sourceRootUrl = sourceSnapshot.rootUrl
  sourceRetrievalDateExact : sourceRetrievalDate = sourceSnapshot.retrievalDate
  sourceBundleSha256Exact : sourceBundleSha256 = sourceSnapshot.bundleSha256
  sourceReviewExact : sourceReview = sourceReviewEvidence
  sourceArtifactPartitionExact :
    sourceSnapshot.htmlCount + sourceSnapshot.imageCount = sourceSnapshot.artifactCount
  modeledProvisionsNodup : modeledProvisions.Nodup
  compiledEntryProvisionsExact :
    compiledEntries.map GlobalNonDescriptorSourceMeaningEntry.provision = modeledProvisions
  allDoubleBondsScopeExact :
    (GlobalNonDescriptorCarotenoidSourceMeaning.sourceMeaning
      .caroteneStemDefaultsToAllTrans).assertion =
        .caroteneStemDefaultsToAllTrans
          Carotenoid1974.CaroteneDoubleBondScope.allDoubleBonds .trans
  allCompiledEntriesNonvacuous :
    ∀ entry ∈ compiledEntries,
      ∃ input, ∃ observation : entry.reference.toReference.Observation,
        input.StructurallyWellFormed ∧
          entry.reference.toReference.Applicable input ∧
            entry.reference.toReference.Judges input observation

def currentTechnicalEvidence : TechnicalEvidence where
  sourceArtifactCount := 52
  sourceHtmlCount := 4
  sourceImageCount := 48
  modeledProvisionCount := 10
  compiledEntryCount := 10
  cyclicNumberingCaseCount := 6
  acyclicNumberingCaseCount := 2
  sourceRootUrl := "https://iupac.qmul.ac.uk/carot/"
  sourceRetrievalDate := "2026-08-11"
  sourceBundleSha256 :=
    "013686e2241d6a410e9ddd94796d395dd5ef3e2b5288db7f148d7be71390ed70"
  sourceReview := sourceReviewEvidence
  sourceArtifactCountExact := by simp
  sourceHtmlCountExact := by simp
  sourceImageCountExact := by simp
  modeledProvisionCountExact := by simp
  compiledEntryCountExact := by simp
  cyclicNumberingCaseCountExact := by decide
  acyclicNumberingCaseCountExact := by decide
  sourceRootUrlExact := rfl
  sourceRetrievalDateExact := rfl
  sourceBundleSha256Exact := rfl
  sourceReviewExact := rfl
  sourceArtifactPartitionExact := source_snapshot_partition_exact
  modeledProvisionsNodup := modeled_provisions_nodup
  compiledEntryProvisionsExact := compiled_entry_provisions_exact
  allDoubleBondsScopeExact := all_double_bonds_scope_exact
  allCompiledEntriesNonvacuous := every_compiled_entry_nonvacuous

@[simp] theorem current_technical_evidence_counts_exact :
    currentTechnicalEvidence.sourceArtifactCount = 52 ∧
      currentTechnicalEvidence.sourceHtmlCount = 4 ∧
        currentTechnicalEvidence.sourceImageCount = 48 ∧
          currentTechnicalEvidence.modeledProvisionCount = 10 ∧
            currentTechnicalEvidence.compiledEntryCount = 10 ∧
              currentTechnicalEvidence.cyclicNumberingCaseCount = 6 ∧
                currentTechnicalEvidence.acyclicNumberingCaseCount = 2 := by
  decide

def currentOpenCarotenoidReviewRequirements :
    List IUPACNormativeSource.ProvisionAuditRequirement :=
  IUPACNormativeSource.currentOpenProvisionAuditRequirements .carotenoidRules1974

@[simp] theorem current_open_carotenoid_review_requirements_exact :
    currentOpenCarotenoidReviewRequirements =
      [ .figureGraphTranscriptionsReviewed ] := by
  decide

@[simp] theorem current_source_review_manifest_gates_exact :
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .carotenoidRules1974).provisionEnumerationConfirmed = true ∧
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .carotenoidRules1974).proseTableCoverageConfirmed = true ∧
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .carotenoidRules1974).figureGraphTranscriptionsReviewed = false := by
  decide

def currentIndependentReviewPackageIssued : Bool := false

@[simp] theorem current_independent_review_package_not_issued :
    currentIndependentReviewPackageIssued = false := by
  rfl

structure MachinePreparedForIndependentReview where
  evidence : TechnicalEvidence
  evidenceExact : evidence = currentTechnicalEvidence
  openRequirementsExact : currentOpenCarotenoidReviewRequirements =
    [ .figureGraphTranscriptionsReviewed ]

def currentMachinePreparedForIndependentReview :
    MachinePreparedForIndependentReview where
  evidence := currentTechnicalEvidence
  evidenceExact := rfl
  openRequirementsExact := current_open_carotenoid_review_requirements_exact

theorem current_carotenoid_audit_remains_incomplete :
    ¬IUPACNormativeSource.ProvisionAuditComplete .carotenoidRules1974 := by
  simp [IUPACNormativeSource.ProvisionAuditComplete,
    IUPACNormativeSource.currentProvisionAuditChecklist,
    IUPACNormativeSource.ProvisionAuditChecklist.Complete,
    Carotenoid1974.currentSourceReviewProvisionEnumerationConfirmed,
    Carotenoid1974.currentSourceReviewProseTableCoverageConfirmed,
    Carotenoid1974.currentSourceReviewFigureGraphTranscriptionsReviewed]

end TechnicalAuditReadiness
end Carotenoid1974
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Carotenoid1974.TechnicalAuditReadiness.source_snapshot_partition_exact
assert_kernel_only
  TetraStereo.OneCenter.Carotenoid1974.TechnicalAuditReadiness.compiled_entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.Carotenoid1974.TechnicalAuditReadiness.all_double_bonds_scope_exact
assert_kernel_only
  TetraStereo.OneCenter.Carotenoid1974.TechnicalAuditReadiness.every_compiled_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.Carotenoid1974.TechnicalAuditReadiness.currentTechnicalEvidence
assert_kernel_only
  TetraStereo.OneCenter.Carotenoid1974.TechnicalAuditReadiness.sourceReviewEvidence
assert_kernel_only
  TetraStereo.OneCenter.Carotenoid1974.TechnicalAuditReadiness.current_open_carotenoid_review_requirements_exact
assert_kernel_only
  TetraStereo.OneCenter.Carotenoid1974.TechnicalAuditReadiness.current_source_review_manifest_gates_exact
assert_kernel_only
  TetraStereo.OneCenter.Carotenoid1974.TechnicalAuditReadiness.current_carotenoid_audit_remains_incomplete
