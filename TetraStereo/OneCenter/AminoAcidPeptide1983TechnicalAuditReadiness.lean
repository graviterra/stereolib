import TetraStereo.OneCenter.IUPACGlobalNonDescriptorAminoAcidPeptideSourceMeaningBatch
import TetraStereo.KernelOnly

set_option autoImplicit false




















namespace TetraStereo.OneCenter
namespace AminoAcidPeptide1983
namespace TechnicalAuditReadiness

open IUPACNormativeProvision
open IUPACNormativeProvision.GlobalNonDescriptorAminoAcidPeptideSourceMeaning

def sourceSnapshot : P10DelegatedAuthorityCorpus.Snapshot :=
  P10DelegatedAuthorityCorpus.snapshot .aminoAcidPeptide1983

def modeledProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions

def compiledEntries : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorAminoAcidPeptideSourceMeaning.batch.entries

def omissionCases :=
  GlobalNonDescriptorAminoAcidPeptideSourceMeaning.omissionInventory

def referenceSubscriptCases :=
  GlobalNonDescriptorAminoAcidPeptideSourceMeaning.referenceSubscriptInventory

def lAlphaCIPCases :=
  GlobalNonDescriptorAminoAcidPeptideSourceMeaning.lAlphaCIPInventory

def alloCases :=
  GlobalNonDescriptorAminoAcidPeptideSourceMeaning.alloInventory

def symbolCases :=
  GlobalNonDescriptorAminoAcidPeptideSourceMeaning.symbolInventory

def sourceReviewEvidence : AminoAcidPeptide1983.SourceReviewEvidence :=
  AminoAcidPeptide1983.currentSourceReview

@[simp] theorem source_snapshot_counts_exact :
    sourceSnapshot.artifactCount = 134 ∧
      sourceSnapshot.htmlCount = 37 ∧
        sourceSnapshot.imageCount = 97 := by
  decide

@[simp] theorem source_snapshot_partition_exact :
    sourceSnapshot.htmlCount + sourceSnapshot.imageCount =
      sourceSnapshot.artifactCount := by
  simp [sourceSnapshot]

@[simp] theorem modeled_provision_count : modeledProvisions.length = 45 := by
  simp [modeledProvisions]

@[simp] theorem compiled_entry_count : compiledEntries.length = 45 := by
  simp [compiledEntries]

@[simp] theorem compiled_entry_provisions_exact :
    compiledEntries.map GlobalNonDescriptorSourceMeaningEntry.provision =
      modeledProvisions := by
  simp [compiledEntries, modeledProvisions]

theorem modeled_provisions_nodup : modeledProvisions.Nodup := by
  unfold modeledProvisions
  exact GlobalNonDescriptorAminoAcidPeptideSourceMeaning.provisions_nodup

@[simp] theorem typed_inventory_counts_exact :
    omissionCases.length = 3 ∧
      referenceSubscriptCases.length = 2 ∧
        lAlphaCIPCases.length = 3 ∧
          alloCases.length = 4 ∧
            symbolCases.length = 5 := by
  decide

@[simp] theorem retro_and_ent_operations_exact :
    AminoAcidPeptide1983.retroPeptide [.L, .L, .D] = [.D, .L, .L] ∧
      AminoAcidPeptide1983.entPeptide [.L, .L, .D] = [.D, .D, .L] :=
  AminoAcidPeptide1983.retro_and_ent_are_distinct_operations

theorem every_compiled_entry_nonvacuous
    (entry : GlobalNonDescriptorSourceMeaningEntry)
    (member : entry ∈ compiledEntries) :
    ∃ input, ∃ observation : entry.reference.toReference.Observation,
      input.StructurallyWellFormed ∧
        entry.reference.toReference.Applicable input ∧
          entry.reference.toReference.Judges input observation := by
  exact GlobalNonDescriptorAminoAcidPeptideSourceMeaning.every_entry_nonvacuous entry
    (by simpa [compiledEntries] using member)

/-! ## One proof-carrying machine dossier -/

structure TechnicalEvidence where
  sourceArtifactCount : Nat
  sourceHtmlCount : Nat
  sourceImageCount : Nat
  modeledProvisionCount : Nat
  compiledEntryCount : Nat
  omissionCaseCount : Nat
  referenceSubscriptCaseCount : Nat
  lAlphaCIPCaseCount : Nat
  alloCaseCount : Nat
  symbolCaseCount : Nat
  sourceRootUrl : String
  sourceRetrievalDate : String
  sourceBundleSha256 : String
  sourceReview : AminoAcidPeptide1983.SourceReviewEvidence
  sourceArtifactCountExact : sourceArtifactCount = sourceSnapshot.artifactCount
  sourceHtmlCountExact : sourceHtmlCount = sourceSnapshot.htmlCount
  sourceImageCountExact : sourceImageCount = sourceSnapshot.imageCount
  modeledProvisionCountExact : modeledProvisionCount = modeledProvisions.length
  compiledEntryCountExact : compiledEntryCount = compiledEntries.length
  omissionCaseCountExact : omissionCaseCount = omissionCases.length
  referenceSubscriptCaseCountExact :
    referenceSubscriptCaseCount = referenceSubscriptCases.length
  lAlphaCIPCaseCountExact : lAlphaCIPCaseCount = lAlphaCIPCases.length
  alloCaseCountExact : alloCaseCount = alloCases.length
  symbolCaseCountExact : symbolCaseCount = symbolCases.length
  sourceRootUrlExact : sourceRootUrl = sourceSnapshot.rootUrl
  sourceRetrievalDateExact : sourceRetrievalDate = sourceSnapshot.retrievalDate
  sourceBundleSha256Exact : sourceBundleSha256 = sourceSnapshot.bundleSha256
  sourceReviewExact : sourceReview = sourceReviewEvidence
  sourceArtifactPartitionExact :
    sourceSnapshot.htmlCount + sourceSnapshot.imageCount = sourceSnapshot.artifactCount
  modeledProvisionsNodup : modeledProvisions.Nodup
  compiledEntryProvisionsExact :
    compiledEntries.map GlobalNonDescriptorSourceMeaningEntry.provision = modeledProvisions
  retroAndEntOperationsExact :
    AminoAcidPeptide1983.retroPeptide [.L, .L, .D] = [.D, .L, .L] ∧
      AminoAcidPeptide1983.entPeptide [.L, .L, .D] = [.D, .D, .L]
  allCompiledEntriesNonvacuous :
    ∀ entry ∈ compiledEntries,
      ∃ input, ∃ observation : entry.reference.toReference.Observation,
        input.StructurallyWellFormed ∧
          entry.reference.toReference.Applicable input ∧
            entry.reference.toReference.Judges input observation

def currentTechnicalEvidence : TechnicalEvidence where
  sourceArtifactCount := 134
  sourceHtmlCount := 37
  sourceImageCount := 97
  modeledProvisionCount := 45
  compiledEntryCount := 45
  omissionCaseCount := 3
  referenceSubscriptCaseCount := 2
  lAlphaCIPCaseCount := 3
  alloCaseCount := 4
  symbolCaseCount := 5
  sourceRootUrl := "https://iupac.qmul.ac.uk/AminoAcid/"
  sourceRetrievalDate := "record-54db71cc66a48d655191405c29c6a9ac"
  sourceBundleSha256 :=
    "f55486c6c8c24d545cde6387792b7ac77959476653ffd005f4d480572a8f808d"
  sourceReview := sourceReviewEvidence
  sourceArtifactCountExact := by simp
  sourceHtmlCountExact := by simp
  sourceImageCountExact := by simp
  modeledProvisionCountExact := by simp
  compiledEntryCountExact := by simp
  omissionCaseCountExact := by decide
  referenceSubscriptCaseCountExact := by decide
  lAlphaCIPCaseCountExact := by decide
  alloCaseCountExact := by decide
  symbolCaseCountExact := by decide
  sourceRootUrlExact := rfl
  sourceRetrievalDateExact := rfl
  sourceBundleSha256Exact := rfl
  sourceReviewExact := rfl
  sourceArtifactPartitionExact := source_snapshot_partition_exact
  modeledProvisionsNodup := modeled_provisions_nodup
  compiledEntryProvisionsExact := compiled_entry_provisions_exact
  retroAndEntOperationsExact := retro_and_ent_operations_exact
  allCompiledEntriesNonvacuous := every_compiled_entry_nonvacuous

@[simp] theorem current_technical_evidence_counts_exact :
    currentTechnicalEvidence.sourceArtifactCount = 134 ∧
      currentTechnicalEvidence.sourceHtmlCount = 37 ∧
        currentTechnicalEvidence.sourceImageCount = 97 ∧
          currentTechnicalEvidence.modeledProvisionCount = 45 ∧
            currentTechnicalEvidence.compiledEntryCount = 45 ∧
              currentTechnicalEvidence.omissionCaseCount = 3 ∧
                currentTechnicalEvidence.referenceSubscriptCaseCount = 2 ∧
                  currentTechnicalEvidence.lAlphaCIPCaseCount = 3 ∧
                    currentTechnicalEvidence.alloCaseCount = 4 ∧
                      currentTechnicalEvidence.symbolCaseCount = 5 := by
  decide



def currentOpenAminoAcidPeptideReviewRequirements :
    List IUPACNormativeSource.ProvisionAuditRequirement :=
  IUPACNormativeSource.currentOpenProvisionAuditRequirements
    .aminoAcidPeptideRecommendations1983

@[simp] theorem current_open_amino_acid_peptide_review_requirements_exact :
    currentOpenAminoAcidPeptideReviewRequirements =
      [ .figureGraphTranscriptionsReviewed ] := by
  decide

@[simp] theorem current_source_review_manifest_gates_exact :
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .aminoAcidPeptideRecommendations1983).provisionEnumerationConfirmed = true ∧
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .aminoAcidPeptideRecommendations1983).proseTableCoverageConfirmed = true ∧
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .aminoAcidPeptideRecommendations1983).figureGraphTranscriptionsReviewed = false := by
  decide

def currentIndependentReviewPackageIssued : Bool := false

@[simp] theorem current_independent_review_package_not_issued :
    currentIndependentReviewPackageIssued = false := by
  rfl

structure MachinePreparedForIndependentReview where
  evidence : TechnicalEvidence
  evidenceExact : evidence = currentTechnicalEvidence
  openRequirementsExact : currentOpenAminoAcidPeptideReviewRequirements =
    [ .figureGraphTranscriptionsReviewed ]

def currentMachinePreparedForIndependentReview :
    MachinePreparedForIndependentReview where
  evidence := currentTechnicalEvidence
  evidenceExact := rfl
  openRequirementsExact := current_open_amino_acid_peptide_review_requirements_exact

theorem current_amino_acid_peptide_audit_remains_incomplete :
    ¬IUPACNormativeSource.ProvisionAuditComplete
      .aminoAcidPeptideRecommendations1983 := by
  simp [IUPACNormativeSource.ProvisionAuditComplete,
    IUPACNormativeSource.currentProvisionAuditChecklist,
    IUPACNormativeSource.ProvisionAuditChecklist.Complete,
    AminoAcidPeptide1983.currentSourceReviewProvisionEnumerationConfirmed,
    AminoAcidPeptide1983.currentSourceReviewProseTableCoverageConfirmed,
    AminoAcidPeptide1983.currentSourceReviewFigureGraphTranscriptionsReviewed]

end TechnicalAuditReadiness
end AminoAcidPeptide1983
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.AminoAcidPeptide1983.TechnicalAuditReadiness.source_snapshot_partition_exact
assert_kernel_only
  TetraStereo.OneCenter.AminoAcidPeptide1983.TechnicalAuditReadiness.compiled_entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.AminoAcidPeptide1983.TechnicalAuditReadiness.retro_and_ent_operations_exact
assert_kernel_only
  TetraStereo.OneCenter.AminoAcidPeptide1983.TechnicalAuditReadiness.every_compiled_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.AminoAcidPeptide1983.TechnicalAuditReadiness.currentTechnicalEvidence
assert_kernel_only
  TetraStereo.OneCenter.AminoAcidPeptide1983.TechnicalAuditReadiness.sourceReviewEvidence
assert_kernel_only
  TetraStereo.OneCenter.AminoAcidPeptide1983.TechnicalAuditReadiness.current_open_amino_acid_peptide_review_requirements_exact
assert_kernel_only
  TetraStereo.OneCenter.AminoAcidPeptide1983.TechnicalAuditReadiness.current_source_review_manifest_gates_exact
assert_kernel_only
  TetraStereo.OneCenter.AminoAcidPeptide1983.TechnicalAuditReadiness.current_amino_acid_peptide_audit_remains_incomplete
