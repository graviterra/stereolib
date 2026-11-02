import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCyclitolSourceMeaningBatch
import TetraStereo.KernelOnly

set_option autoImplicit false





















namespace TetraStereo.OneCenter
namespace Cyclitol1973
namespace TechnicalAuditReadiness

open IUPACNormativeProvision
open IUPACNormativeProvision.GlobalNonDescriptorCyclitolSourceMeaning

def sourceSnapshot : P10DelegatedAuthorityCorpus.Snapshot :=
  P10DelegatedAuthorityCorpus.snapshot .cyclitol1973

def modeledProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorCyclitolSourceMeaning.provisions

def compiledEntries : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorCyclitolSourceMeaning.batch.entries

def inositolCases :=
  GlobalNonDescriptorCyclitolSourceMeaning.inositolFractionInventory

def numberingCriteria :=
  Cyclitol1973.NumberingCriterion.all

def canonicalProjectionCases :=
  GlobalNonDescriptorCyclitolSourceMeaning.canonicalProjectionReadings

def notationCombinationCases :=
  GlobalNonDescriptorCyclitolSourceMeaning.notationCombinationInventory

def retainedParentRouteCases :=
  GlobalNonDescriptorCyclitolSourceMeaning.retainedParentRoutes

def sourceReviewEvidence : Cyclitol1973.SourceReviewEvidence :=
  Cyclitol1973.currentSourceReview

@[simp] theorem source_snapshot_counts_exact :
    sourceSnapshot.artifactCount = 51 ∧
      sourceSnapshot.htmlCount = 4 ∧
        sourceSnapshot.imageCount = 47 := by
  decide

@[simp] theorem source_snapshot_partition_exact :
    sourceSnapshot.htmlCount + sourceSnapshot.imageCount =
      sourceSnapshot.artifactCount := by
  simp [sourceSnapshot]

@[simp] theorem modeled_provision_count : modeledProvisions.length = 37 := by
  simp [modeledProvisions]

@[simp] theorem compiled_entry_count : compiledEntries.length = 37 := by
  simp [compiledEntries]

@[simp] theorem compiled_entry_provisions_exact :
    compiledEntries.map GlobalNonDescriptorSourceMeaningEntry.provision =
      modeledProvisions := by
  simp [compiledEntries, modeledProvisions]

theorem modeled_provisions_nodup : modeledProvisions.Nodup := by
  unfold modeledProvisions
  exact GlobalNonDescriptorCyclitolSourceMeaning.provisions_nodup

@[simp] theorem typed_inventory_counts_exact :
    inositolCases.length = 9 ∧
      numberingCriteria.length = 6 ∧
        canonicalProjectionCases.length = 2 ∧
          notationCombinationCases.length = 4 ∧
            retainedParentRouteCases.length = 3 := by
  decide

@[simp] theorem configuration_retention_gate_exact :
    Cyclitol1973.inositolDerivativeRoute 1 false false =
        .generalCyclitolNomenclature ∧
      Cyclitol1973.inositolDerivativeRoute 1 true false =
        .retainedParentDeoxyNomenclature := by
  decide

@[simp] theorem source_denominator_rendering_exact :
    Cyclitol1973.InositolParent.cis.relativeFraction.sourcePrintedDenominator = [0] ∧
      Cyclitol1973.InositolParent.myo.relativeFraction.sourcePrintedDenominator = [4, 6] := by
  decide

theorem every_compiled_entry_nonvacuous
    (entry : GlobalNonDescriptorSourceMeaningEntry)
    (member : entry ∈ compiledEntries) :
    ∃ input, ∃ observation : entry.reference.toReference.Observation,
      input.StructurallyWellFormed ∧
        entry.reference.toReference.Applicable input ∧
          entry.reference.toReference.Judges input observation := by
  exact GlobalNonDescriptorCyclitolSourceMeaning.every_entry_nonvacuous entry
    (by simpa [compiledEntries] using member)

/-! ## One proof-carrying machine dossier -/

structure TechnicalEvidence where
  sourceArtifactCount : Nat
  sourceHtmlCount : Nat
  sourceImageCount : Nat
  modeledProvisionCount : Nat
  compiledEntryCount : Nat
  inositolCaseCount : Nat
  numberingCriterionCount : Nat
  canonicalProjectionCaseCount : Nat
  notationCombinationCaseCount : Nat
  retainedParentRouteCaseCount : Nat
  sourceRootUrl : String
  sourceRetrievalDate : String
  sourceBundleSha256 : String
  sourceReview : Cyclitol1973.SourceReviewEvidence
  sourceArtifactCountExact : sourceArtifactCount = sourceSnapshot.artifactCount
  sourceHtmlCountExact : sourceHtmlCount = sourceSnapshot.htmlCount
  sourceImageCountExact : sourceImageCount = sourceSnapshot.imageCount
  modeledProvisionCountExact : modeledProvisionCount = modeledProvisions.length
  compiledEntryCountExact : compiledEntryCount = compiledEntries.length
  inositolCaseCountExact : inositolCaseCount = inositolCases.length
  numberingCriterionCountExact : numberingCriterionCount = numberingCriteria.length
  canonicalProjectionCaseCountExact :
    canonicalProjectionCaseCount = canonicalProjectionCases.length
  notationCombinationCaseCountExact :
    notationCombinationCaseCount = notationCombinationCases.length
  retainedParentRouteCaseCountExact :
    retainedParentRouteCaseCount = retainedParentRouteCases.length
  sourceRootUrlExact : sourceRootUrl = sourceSnapshot.rootUrl
  sourceRetrievalDateExact : sourceRetrievalDate = sourceSnapshot.retrievalDate
  sourceBundleSha256Exact : sourceBundleSha256 = sourceSnapshot.bundleSha256
  sourceReviewExact : sourceReview = sourceReviewEvidence
  sourceArtifactPartitionExact :
    sourceSnapshot.htmlCount + sourceSnapshot.imageCount = sourceSnapshot.artifactCount
  modeledProvisionsNodup : modeledProvisions.Nodup
  compiledEntryProvisionsExact :
    compiledEntries.map GlobalNonDescriptorSourceMeaningEntry.provision = modeledProvisions
  configurationRetentionGateExact :
    Cyclitol1973.inositolDerivativeRoute 1 false false =
        .generalCyclitolNomenclature ∧
      Cyclitol1973.inositolDerivativeRoute 1 true false =
        .retainedParentDeoxyNomenclature
  sourceDenominatorRenderingExact :
    Cyclitol1973.InositolParent.cis.relativeFraction.sourcePrintedDenominator = [0] ∧
      Cyclitol1973.InositolParent.myo.relativeFraction.sourcePrintedDenominator = [4, 6]
  allCompiledEntriesNonvacuous :
    ∀ entry ∈ compiledEntries,
      ∃ input, ∃ observation : entry.reference.toReference.Observation,
        input.StructurallyWellFormed ∧
          entry.reference.toReference.Applicable input ∧
            entry.reference.toReference.Judges input observation

def currentTechnicalEvidence : TechnicalEvidence where
  sourceArtifactCount := 51
  sourceHtmlCount := 4
  sourceImageCount := 47
  modeledProvisionCount := 37
  compiledEntryCount := 37
  inositolCaseCount := 9
  numberingCriterionCount := 6
  canonicalProjectionCaseCount := 2
  notationCombinationCaseCount := 4
  retainedParentRouteCaseCount := 3
  sourceRootUrl := "https://iupac.qmul.ac.uk/cyclitol/"
  sourceRetrievalDate := "2026-08-11"
  sourceBundleSha256 :=
    "f4bcd60c0c370d90b7f907adccdc971df0ab26237e7bd77cd0d04597b2163927"
  sourceReview := sourceReviewEvidence
  sourceArtifactCountExact := by simp
  sourceHtmlCountExact := by simp
  sourceImageCountExact := by simp
  modeledProvisionCountExact := by simp
  compiledEntryCountExact := by simp
  inositolCaseCountExact := by decide
  numberingCriterionCountExact := by decide
  canonicalProjectionCaseCountExact := by decide
  notationCombinationCaseCountExact := by decide
  retainedParentRouteCaseCountExact := by decide
  sourceRootUrlExact := rfl
  sourceRetrievalDateExact := rfl
  sourceBundleSha256Exact := rfl
  sourceReviewExact := rfl
  sourceArtifactPartitionExact := source_snapshot_partition_exact
  modeledProvisionsNodup := modeled_provisions_nodup
  compiledEntryProvisionsExact := compiled_entry_provisions_exact
  configurationRetentionGateExact := configuration_retention_gate_exact
  sourceDenominatorRenderingExact := source_denominator_rendering_exact
  allCompiledEntriesNonvacuous := every_compiled_entry_nonvacuous

@[simp] theorem current_technical_evidence_counts_exact :
    currentTechnicalEvidence.sourceArtifactCount = 51 ∧
      currentTechnicalEvidence.sourceHtmlCount = 4 ∧
        currentTechnicalEvidence.sourceImageCount = 47 ∧
          currentTechnicalEvidence.modeledProvisionCount = 37 ∧
            currentTechnicalEvidence.compiledEntryCount = 37 ∧
              currentTechnicalEvidence.inositolCaseCount = 9 ∧
                currentTechnicalEvidence.numberingCriterionCount = 6 ∧
                  currentTechnicalEvidence.canonicalProjectionCaseCount = 2 ∧
                    currentTechnicalEvidence.notationCombinationCaseCount = 4 ∧
                      currentTechnicalEvidence.retainedParentRouteCaseCount = 3 := by
  decide



def currentOpenCyclitolReviewRequirements :
    List IUPACNormativeSource.ProvisionAuditRequirement :=
  IUPACNormativeSource.currentOpenProvisionAuditRequirements
    .cyclitolRecommendations1973

@[simp] theorem current_open_cyclitol_review_requirements_exact :
    currentOpenCyclitolReviewRequirements =
      [ .figureGraphTranscriptionsReviewed ] := by
  decide

@[simp] theorem current_cyclitol_review_gate_values_exact :
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .cyclitolRecommendations1973).provisionEnumerationConfirmed = true ∧
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .cyclitolRecommendations1973).proseTableCoverageConfirmed = true ∧
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .cyclitolRecommendations1973).figureGraphTranscriptionsReviewed = false := by
  decide

def currentIndependentReviewPackageIssued : Bool := false

@[simp] theorem current_independent_review_package_not_issued :
    currentIndependentReviewPackageIssued = false := by
  rfl

structure MachinePreparedForIndependentReview where
  evidence : TechnicalEvidence
  evidenceExact : evidence = currentTechnicalEvidence
  openRequirementsExact : currentOpenCyclitolReviewRequirements =
    [ .figureGraphTranscriptionsReviewed ]

def currentMachinePreparedForIndependentReview :
    MachinePreparedForIndependentReview where
  evidence := currentTechnicalEvidence
  evidenceExact := rfl
  openRequirementsExact := current_open_cyclitol_review_requirements_exact

theorem current_cyclitol_audit_remains_incomplete :
    ¬IUPACNormativeSource.ProvisionAuditComplete .cyclitolRecommendations1973 := by
  simp [IUPACNormativeSource.ProvisionAuditComplete,
    IUPACNormativeSource.currentProvisionAuditChecklist,
    IUPACNormativeSource.ProvisionAuditChecklist.Complete,
    Cyclitol1973.currentSourceReviewProvisionEnumerationConfirmed,
    Cyclitol1973.currentSourceReviewProseTableCoverageConfirmed,
    Cyclitol1973.currentSourceReviewFigureGraphTranscriptionsReviewed]

end TechnicalAuditReadiness
end Cyclitol1973
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Cyclitol1973.TechnicalAuditReadiness.source_snapshot_partition_exact
assert_kernel_only
  TetraStereo.OneCenter.Cyclitol1973.TechnicalAuditReadiness.compiled_entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.Cyclitol1973.TechnicalAuditReadiness.configuration_retention_gate_exact
assert_kernel_only
  TetraStereo.OneCenter.Cyclitol1973.TechnicalAuditReadiness.source_denominator_rendering_exact
assert_kernel_only
  TetraStereo.OneCenter.Cyclitol1973.TechnicalAuditReadiness.every_compiled_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.Cyclitol1973.TechnicalAuditReadiness.currentTechnicalEvidence
assert_kernel_only
  TetraStereo.OneCenter.Cyclitol1973.TechnicalAuditReadiness.sourceReviewEvidence
assert_kernel_only
  TetraStereo.OneCenter.Cyclitol1973.TechnicalAuditReadiness.current_open_cyclitol_review_requirements_exact
assert_kernel_only
  TetraStereo.OneCenter.Cyclitol1973.TechnicalAuditReadiness.current_cyclitol_review_gate_values_exact
assert_kernel_only
  TetraStereo.OneCenter.Cyclitol1973.TechnicalAuditReadiness.current_cyclitol_audit_remains_incomplete
