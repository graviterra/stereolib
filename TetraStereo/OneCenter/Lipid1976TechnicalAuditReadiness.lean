import TetraStereo.OneCenter.IUPACGlobalNonDescriptorLipidSourceMeaningBatch
import TetraStereo.KernelOnly

set_option autoImplicit false



















namespace TetraStereo.OneCenter
namespace Lipid1976
namespace TechnicalAuditReadiness

open IUPACNormativeProvision
open IUPACNormativeProvision.GlobalNonDescriptorLipidSourceMeaning

def sourceSnapshot : P10DelegatedAuthorityCorpus.Snapshot :=
  P10DelegatedAuthorityCorpus.snapshot .lipid1976

def modeledProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorLipidSourceMeaning.provisions

def compiledEntries : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorLipidSourceMeaning.batch.entries

def sourceStatusCases :=
  GlobalNonDescriptorLipidSourceMeaning.sourceStatusInventory

def compoundApplicabilityCases :=
  GlobalNonDescriptorLipidSourceMeaning.compoundApplicabilityInventory

def sphingoidCases :=
  GlobalNonDescriptorLipidSourceMeaning.sphingoidInventory

def glycerolSiteCases :=
  GlobalNonDescriptorLipidSourceMeaning.glycerolSiteInventory

def knowledgePrefixCases :=
  GlobalNonDescriptorLipidSourceMeaning.knowledgePrefixInventory

def glycerolPhosphateCases :=
  GlobalNonDescriptorLipidSourceMeaning.glycerolPhosphateInventory

def glycerophospholipidParentCases :=
  GlobalNonDescriptorLipidSourceMeaning.glycerophospholipidParentInventory

def sourceReviewEvidence : Lipid1976.SourceReviewEvidence :=
  Lipid1976.currentSourceReview

@[simp] theorem source_snapshot_counts_exact :
    sourceSnapshot.artifactCount = 30 ∧
      sourceSnapshot.htmlCount = 6 ∧
        sourceSnapshot.imageCount = 24 := by
  decide

@[simp] theorem source_snapshot_partition_exact :
    sourceSnapshot.htmlCount + sourceSnapshot.imageCount =
      sourceSnapshot.artifactCount := by
  simp [sourceSnapshot]

@[simp] theorem modeled_provision_count : modeledProvisions.length = 31 := by
  simp [modeledProvisions]

@[simp] theorem compiled_entry_count : compiledEntries.length = 31 := by
  simp [compiledEntries]

@[simp] theorem compiled_entry_provisions_exact :
    compiledEntries.map GlobalNonDescriptorSourceMeaningEntry.provision =
      modeledProvisions := by
  simp [compiledEntries, modeledProvisions]

theorem modeled_provisions_nodup : modeledProvisions.Nodup := by
  unfold modeledProvisions
  exact GlobalNonDescriptorLipidSourceMeaning.provisions_nodup

@[simp] theorem typed_inventory_counts_exact :
    sourceStatusCases.length = 3 ∧
      compoundApplicabilityCases.length = 3 ∧
        sphingoidCases.length = 5 ∧
          glycerolSiteCases.length = 3 ∧
            knowledgePrefixCases.length = 3 ∧
              glycerolPhosphateCases.length = 2 ∧
                glycerophospholipidParentCases.length = 4 := by
  decide

@[simp] theorem source_status_cases_exact :
    sourceStatusCases =
      [ ("Lip-1.10 (current edited text)", .current)
      , ("Lip-1.10 archive", .archivedNotRecommended)
      , ("Lip-3 superseded part", .supersededByGlycolipid1997) ] := by
  decide

@[simp] theorem sphingoid_configuration_cases_exact :
    Lipid1976.SphingoidParent.sphinganine.centerConfiguration =
        [Lipid1976.LocatedRS.mk 2 .S, Lipid1976.LocatedRS.mk 3 .R] ∧
      Lipid1976.SphingoidParent.phytosphingosine.centerConfiguration =
        [Lipid1976.LocatedRS.mk 2 .S, Lipid1976.LocatedRS.mk 3 .S,
          Lipid1976.LocatedRS.mk 4 .R] := by
  decide

@[simp] theorem glycerol_reference_projection_exact :
    Lipid1976.isSnReferenceProjection ⟨true, true⟩ ∧
      Lipid1976.snLocant .topInReferenceFischer = 1 := by
  decide

theorem every_compiled_entry_nonvacuous
    (entry : GlobalNonDescriptorSourceMeaningEntry)
    (member : entry ∈ compiledEntries) :
    ∃ input, ∃ observation : entry.reference.toReference.Observation,
      input.StructurallyWellFormed ∧
        entry.reference.toReference.Applicable input ∧
          entry.reference.toReference.Judges input observation := by
  exact GlobalNonDescriptorLipidSourceMeaning.every_entry_nonvacuous entry
    (by simpa [compiledEntries] using member)

/-! ## One proof-carrying machine dossier -/

structure TechnicalEvidence where
  sourceArtifactCount : Nat
  sourceHtmlCount : Nat
  sourceImageCount : Nat
  modeledProvisionCount : Nat
  compiledEntryCount : Nat
  sourceStatusCaseCount : Nat
  compoundApplicabilityCaseCount : Nat
  sphingoidCaseCount : Nat
  glycerolSiteCaseCount : Nat
  knowledgePrefixCaseCount : Nat
  glycerolPhosphateCaseCount : Nat
  glycerophospholipidParentCaseCount : Nat
  sourceRootUrl : String
  sourceRetrievalDate : String
  sourceBundleSha256 : String
  sourceReview : Lipid1976.SourceReviewEvidence
  sourceArtifactCountExact : sourceArtifactCount = sourceSnapshot.artifactCount
  sourceHtmlCountExact : sourceHtmlCount = sourceSnapshot.htmlCount
  sourceImageCountExact : sourceImageCount = sourceSnapshot.imageCount
  modeledProvisionCountExact : modeledProvisionCount = modeledProvisions.length
  compiledEntryCountExact : compiledEntryCount = compiledEntries.length
  sourceStatusCaseCountExact : sourceStatusCaseCount = sourceStatusCases.length
  compoundApplicabilityCaseCountExact :
    compoundApplicabilityCaseCount = compoundApplicabilityCases.length
  sphingoidCaseCountExact : sphingoidCaseCount = sphingoidCases.length
  glycerolSiteCaseCountExact : glycerolSiteCaseCount = glycerolSiteCases.length
  knowledgePrefixCaseCountExact : knowledgePrefixCaseCount = knowledgePrefixCases.length
  glycerolPhosphateCaseCountExact :
    glycerolPhosphateCaseCount = glycerolPhosphateCases.length
  glycerophospholipidParentCaseCountExact :
    glycerophospholipidParentCaseCount = glycerophospholipidParentCases.length
  sourceRootUrlExact : sourceRootUrl = sourceSnapshot.rootUrl
  sourceRetrievalDateExact : sourceRetrievalDate = sourceSnapshot.retrievalDate
  sourceBundleSha256Exact : sourceBundleSha256 = sourceSnapshot.bundleSha256
  sourceReviewExact : sourceReview = sourceReviewEvidence
  sourceArtifactPartitionExact :
    sourceSnapshot.htmlCount + sourceSnapshot.imageCount = sourceSnapshot.artifactCount
  modeledProvisionsNodup : modeledProvisions.Nodup
  compiledEntryProvisionsExact :
    compiledEntries.map GlobalNonDescriptorSourceMeaningEntry.provision = modeledProvisions
  sourceStatusCasesExact : sourceStatusCases =
    [ ("Lip-1.10 (current edited text)", .current)
    , ("Lip-1.10 archive", .archivedNotRecommended)
    , ("Lip-3 superseded part", .supersededByGlycolipid1997) ]
  sphingoidConfigurationCasesExact :
    Lipid1976.SphingoidParent.sphinganine.centerConfiguration =
        [Lipid1976.LocatedRS.mk 2 .S, Lipid1976.LocatedRS.mk 3 .R] ∧
      Lipid1976.SphingoidParent.phytosphingosine.centerConfiguration =
        [Lipid1976.LocatedRS.mk 2 .S, Lipid1976.LocatedRS.mk 3 .S,
          Lipid1976.LocatedRS.mk 4 .R]
  glycerolReferenceProjectionExact :
    Lipid1976.isSnReferenceProjection ⟨true, true⟩ ∧
      Lipid1976.snLocant .topInReferenceFischer = 1
  allCompiledEntriesNonvacuous :
    ∀ entry ∈ compiledEntries,
      ∃ input, ∃ observation : entry.reference.toReference.Observation,
        input.StructurallyWellFormed ∧
          entry.reference.toReference.Applicable input ∧
            entry.reference.toReference.Judges input observation

def currentTechnicalEvidence : TechnicalEvidence where
  sourceArtifactCount := 30
  sourceHtmlCount := 6
  sourceImageCount := 24
  modeledProvisionCount := 31
  compiledEntryCount := 31
  sourceStatusCaseCount := 3
  compoundApplicabilityCaseCount := 3
  sphingoidCaseCount := 5
  glycerolSiteCaseCount := 3
  knowledgePrefixCaseCount := 3
  glycerolPhosphateCaseCount := 2
  glycerophospholipidParentCaseCount := 4
  sourceRootUrl := "https://iupac.qmul.ac.uk/lipid/"
  sourceRetrievalDate := "2026-08-11"
  sourceBundleSha256 :=
    "9b223317b293897493272ef6b3b93695d15f2f6c856fb8472b1c4e286498ff68"
  sourceReview := sourceReviewEvidence
  sourceArtifactCountExact := by simp
  sourceHtmlCountExact := by simp
  sourceImageCountExact := by simp
  modeledProvisionCountExact := by simp
  compiledEntryCountExact := by simp
  sourceStatusCaseCountExact := by decide
  compoundApplicabilityCaseCountExact := by decide
  sphingoidCaseCountExact := by decide
  glycerolSiteCaseCountExact := by decide
  knowledgePrefixCaseCountExact := by decide
  glycerolPhosphateCaseCountExact := by decide
  glycerophospholipidParentCaseCountExact := by decide
  sourceRootUrlExact := rfl
  sourceRetrievalDateExact := rfl
  sourceBundleSha256Exact := rfl
  sourceReviewExact := rfl
  sourceArtifactPartitionExact := source_snapshot_partition_exact
  modeledProvisionsNodup := modeled_provisions_nodup
  compiledEntryProvisionsExact := compiled_entry_provisions_exact
  sourceStatusCasesExact := source_status_cases_exact
  sphingoidConfigurationCasesExact := sphingoid_configuration_cases_exact
  glycerolReferenceProjectionExact := glycerol_reference_projection_exact
  allCompiledEntriesNonvacuous := every_compiled_entry_nonvacuous

@[simp] theorem current_technical_evidence_counts_exact :
    currentTechnicalEvidence.sourceArtifactCount = 30 ∧
      currentTechnicalEvidence.sourceHtmlCount = 6 ∧
        currentTechnicalEvidence.sourceImageCount = 24 ∧
          currentTechnicalEvidence.modeledProvisionCount = 31 ∧
            currentTechnicalEvidence.compiledEntryCount = 31 ∧
              currentTechnicalEvidence.sourceStatusCaseCount = 3 ∧
                currentTechnicalEvidence.compoundApplicabilityCaseCount = 3 ∧
                  currentTechnicalEvidence.sphingoidCaseCount = 5 ∧
                    currentTechnicalEvidence.glycerolSiteCaseCount = 3 ∧
                      currentTechnicalEvidence.knowledgePrefixCaseCount = 3 ∧
                        currentTechnicalEvidence.glycerolPhosphateCaseCount = 2 ∧
                          currentTechnicalEvidence.glycerophospholipidParentCaseCount = 4 := by
  decide



def currentOpenLipidReviewRequirements :
    List IUPACNormativeSource.ProvisionAuditRequirement :=
  IUPACNormativeSource.currentOpenProvisionAuditRequirements .lipidRecommendations1976

@[simp] theorem current_open_lipid_review_requirements_exact :
    currentOpenLipidReviewRequirements =
      [ .figureGraphTranscriptionsReviewed ] := by
  decide

@[simp] theorem current_lipid_review_gate_values_exact :
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .lipidRecommendations1976).provisionEnumerationConfirmed = true ∧
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .lipidRecommendations1976).proseTableCoverageConfirmed = true ∧
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .lipidRecommendations1976).figureGraphTranscriptionsReviewed = false := by
  decide

def currentIndependentReviewPackageIssued : Bool := false

@[simp] theorem current_independent_review_package_not_issued :
    currentIndependentReviewPackageIssued = false := by
  rfl

structure MachinePreparedForIndependentReview where
  evidence : TechnicalEvidence
  evidenceExact : evidence = currentTechnicalEvidence
  openRequirementsExact : currentOpenLipidReviewRequirements =
    [ .figureGraphTranscriptionsReviewed ]

def currentMachinePreparedForIndependentReview :
    MachinePreparedForIndependentReview where
  evidence := currentTechnicalEvidence
  evidenceExact := rfl
  openRequirementsExact := current_open_lipid_review_requirements_exact

theorem current_lipid_audit_remains_incomplete :
    ¬IUPACNormativeSource.ProvisionAuditComplete .lipidRecommendations1976 := by
  simp [IUPACNormativeSource.ProvisionAuditComplete,
    IUPACNormativeSource.currentProvisionAuditChecklist,
    IUPACNormativeSource.ProvisionAuditChecklist.Complete,
    Lipid1976.currentSourceReviewProvisionEnumerationConfirmed,
    Lipid1976.currentSourceReviewProseTableCoverageConfirmed,
    Lipid1976.currentSourceReviewFigureGraphTranscriptionsReviewed]

end TechnicalAuditReadiness
end Lipid1976
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Lipid1976.TechnicalAuditReadiness.source_snapshot_partition_exact
assert_kernel_only
  TetraStereo.OneCenter.Lipid1976.TechnicalAuditReadiness.compiled_entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.Lipid1976.TechnicalAuditReadiness.source_status_cases_exact
assert_kernel_only
  TetraStereo.OneCenter.Lipid1976.TechnicalAuditReadiness.sphingoid_configuration_cases_exact
assert_kernel_only
  TetraStereo.OneCenter.Lipid1976.TechnicalAuditReadiness.glycerol_reference_projection_exact
assert_kernel_only
  TetraStereo.OneCenter.Lipid1976.TechnicalAuditReadiness.every_compiled_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.Lipid1976.TechnicalAuditReadiness.currentTechnicalEvidence
assert_kernel_only
  TetraStereo.OneCenter.Lipid1976.TechnicalAuditReadiness.sourceReviewEvidence
assert_kernel_only
  TetraStereo.OneCenter.Lipid1976.TechnicalAuditReadiness.current_open_lipid_review_requirements_exact
assert_kernel_only
  TetraStereo.OneCenter.Lipid1976.TechnicalAuditReadiness.current_lipid_review_gate_values_exact
assert_kernel_only
  TetraStereo.OneCenter.Lipid1976.TechnicalAuditReadiness.current_lipid_audit_remains_incomplete
