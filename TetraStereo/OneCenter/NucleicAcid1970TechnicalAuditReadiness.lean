import TetraStereo.OneCenter.IUPACGlobalNonDescriptorNucleicAcidSourceMeaningBatch
import TetraStereo.KernelOnly

set_option autoImplicit false




















namespace TetraStereo.OneCenter
namespace NucleicAcid1970
namespace TechnicalAuditReadiness

open IUPACNormativeProvision
open IUPACNormativeProvision.GlobalNonDescriptorNucleicAcidSourceMeaning

def sourceSnapshot : P10DelegatedAuthorityCorpus.Snapshot :=
  P10DelegatedAuthorityCorpus.snapshot .nucleicAcid1970

def modeledProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorNucleicAcidSourceMeaning.provisions

def compiledEntries : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorNucleicAcidSourceMeaning.batch.entries

def incorporatedErrata :=
  NucleicAcid1970.IncorporatedErratum.all

def defaultResolutionCases :=
  GlobalNonDescriptorNucleicAcidSourceMeaning.defaultResolutionInventory

def threeLetterCases :=
  GlobalNonDescriptorNucleicAcidSourceMeaning.threeLetterInventory

def oneLetterCases :=
  NucleicAcid1970.OneLetterNucleoside.all

def sugarPrefixCases :=
  GlobalNonDescriptorNucleicAcidSourceMeaning.sugarPrefixInventory

@[simp] theorem source_snapshot_counts_exact :
    sourceSnapshot.artifactCount = 19 ∧
      sourceSnapshot.htmlCount = 2 ∧
        sourceSnapshot.imageCount = 17 := by
  decide

@[simp] theorem source_snapshot_partition_exact :
    sourceSnapshot.htmlCount + sourceSnapshot.imageCount =
      sourceSnapshot.artifactCount := by
  simp [sourceSnapshot]

@[simp] theorem modeled_provision_count : modeledProvisions.length = 21 := by
  simp [modeledProvisions]

@[simp] theorem compiled_entry_count : compiledEntries.length = 21 := by
  simp [compiledEntries]

@[simp] theorem compiled_entry_provisions_exact :
    compiledEntries.map GlobalNonDescriptorSourceMeaningEntry.provision =
      modeledProvisions := by
  simp [compiledEntries, modeledProvisions]

theorem modeled_provisions_nodup : modeledProvisions.Nodup := by
  unfold modeledProvisions
  exact GlobalNonDescriptorNucleicAcidSourceMeaning.provisions_nodup

@[simp] theorem typed_inventory_counts_exact :
    incorporatedErrata.length = 3 ∧
      defaultResolutionCases.length = 4 ∧
        threeLetterCases.length = 15 ∧
          oneLetterCases.length = 15 ∧
            sugarPrefixCases.length = 5 := by
  decide

@[simp] theorem reverse_direction_markers_exact :
    NucleicAcid1970.allowedDirectionMarkers false =
      [.precedingLocants, .arrow, .rotatedSymbols] := by
  decide

theorem every_incorporated_erratum_nonsemantic (row : NucleicAcid1970.Provision) :
    (GlobalNonDescriptorNucleicAcidSourceMeaning.sourceMeaning row).incorporatedErrata.Forall
      fun erratum => !erratum.changesConfigurationSemantics :=
  GlobalNonDescriptorNucleicAcidSourceMeaning.sourceMeaning_errata_nonsemantic row

theorem every_compiled_entry_nonvacuous
    (entry : GlobalNonDescriptorSourceMeaningEntry)
    (member : entry ∈ compiledEntries) :
    ∃ input, ∃ observation : entry.reference.toReference.Observation,
      input.StructurallyWellFormed ∧
        entry.reference.toReference.Applicable input ∧
          entry.reference.toReference.Judges input observation := by
  exact GlobalNonDescriptorNucleicAcidSourceMeaning.every_entry_nonvacuous entry
    (by simpa [compiledEntries] using member)

/-! ## One proof-carrying machine dossier -/

structure TechnicalEvidence where
  sourceArtifactCount : Nat
  sourceHtmlCount : Nat
  sourceImageCount : Nat
  modeledProvisionCount : Nat
  compiledEntryCount : Nat
  incorporatedErratumCount : Nat
  defaultResolutionCaseCount : Nat
  threeLetterCaseCount : Nat
  oneLetterCaseCount : Nat
  sugarPrefixCaseCount : Nat
  sourceReview : NucleicAcid1970.SourceReviewEvidence
  sourceRootUrl : String
  sourceRetrievalDate : String
  sourceBundleSha256 : String
  sourceArtifactCountExact : sourceArtifactCount = sourceSnapshot.artifactCount
  sourceHtmlCountExact : sourceHtmlCount = sourceSnapshot.htmlCount
  sourceImageCountExact : sourceImageCount = sourceSnapshot.imageCount
  modeledProvisionCountExact : modeledProvisionCount = modeledProvisions.length
  compiledEntryCountExact : compiledEntryCount = compiledEntries.length
  incorporatedErratumCountExact : incorporatedErratumCount = incorporatedErrata.length
  defaultResolutionCaseCountExact :
    defaultResolutionCaseCount = defaultResolutionCases.length
  threeLetterCaseCountExact : threeLetterCaseCount = threeLetterCases.length
  oneLetterCaseCountExact : oneLetterCaseCount = oneLetterCases.length
  sugarPrefixCaseCountExact : sugarPrefixCaseCount = sugarPrefixCases.length
  sourceReviewExact : sourceReview = NucleicAcid1970.currentSourceReview
  sourceRootUrlExact : sourceRootUrl = sourceSnapshot.rootUrl
  sourceRetrievalDateExact : sourceRetrievalDate = sourceSnapshot.retrievalDate
  sourceBundleSha256Exact : sourceBundleSha256 = sourceSnapshot.bundleSha256
  sourceArtifactPartitionExact :
    sourceSnapshot.htmlCount + sourceSnapshot.imageCount = sourceSnapshot.artifactCount
  modeledProvisionsNodup : modeledProvisions.Nodup
  compiledEntryProvisionsExact :
    compiledEntries.map GlobalNonDescriptorSourceMeaningEntry.provision = modeledProvisions
  reverseDirectionMarkersExact :
    NucleicAcid1970.allowedDirectionMarkers false =
      [.precedingLocants, .arrow, .rotatedSymbols]
  allErrataNonsemantic :
    ∀ row : NucleicAcid1970.Provision,
      (GlobalNonDescriptorNucleicAcidSourceMeaning.sourceMeaning row).incorporatedErrata.Forall
        fun erratum => !erratum.changesConfigurationSemantics
  allCompiledEntriesNonvacuous :
    ∀ entry ∈ compiledEntries,
      ∃ input, ∃ observation : entry.reference.toReference.Observation,
        input.StructurallyWellFormed ∧
          entry.reference.toReference.Applicable input ∧
            entry.reference.toReference.Judges input observation

def currentTechnicalEvidence : TechnicalEvidence where
  sourceArtifactCount := 19
  sourceHtmlCount := 2
  sourceImageCount := 17
  modeledProvisionCount := 21
  compiledEntryCount := 21
  incorporatedErratumCount := 3
  defaultResolutionCaseCount := 4
  threeLetterCaseCount := 15
  oneLetterCaseCount := 15
  sugarPrefixCaseCount := 5
  sourceReview := NucleicAcid1970.currentSourceReview
  sourceRootUrl := "https://iupac.qmul.ac.uk/misc/naabb.html"
  sourceRetrievalDate := "2026-08-11"
  sourceBundleSha256 :=
    "bd3a192849390a891d4e9a67533205f02ae0fd473b730b2aa54dbbbf2cc7b508"
  sourceArtifactCountExact := by simp
  sourceHtmlCountExact := by simp
  sourceImageCountExact := by simp
  modeledProvisionCountExact := by simp
  compiledEntryCountExact := by simp
  incorporatedErratumCountExact := by decide
  defaultResolutionCaseCountExact := by decide
  threeLetterCaseCountExact := by decide
  oneLetterCaseCountExact := by decide
  sugarPrefixCaseCountExact := by decide
  sourceReviewExact := rfl
  sourceRootUrlExact := rfl
  sourceRetrievalDateExact := rfl
  sourceBundleSha256Exact := rfl
  sourceArtifactPartitionExact := source_snapshot_partition_exact
  modeledProvisionsNodup := modeled_provisions_nodup
  compiledEntryProvisionsExact := compiled_entry_provisions_exact
  reverseDirectionMarkersExact := reverse_direction_markers_exact
  allErrataNonsemantic := every_incorporated_erratum_nonsemantic
  allCompiledEntriesNonvacuous := every_compiled_entry_nonvacuous

@[simp] theorem current_technical_evidence_counts_exact :
    currentTechnicalEvidence.sourceArtifactCount = 19 ∧
      currentTechnicalEvidence.sourceHtmlCount = 2 ∧
        currentTechnicalEvidence.sourceImageCount = 17 ∧
          currentTechnicalEvidence.modeledProvisionCount = 21 ∧
            currentTechnicalEvidence.compiledEntryCount = 21 ∧
              currentTechnicalEvidence.incorporatedErratumCount = 3 ∧
                currentTechnicalEvidence.defaultResolutionCaseCount = 4 ∧
                  currentTechnicalEvidence.threeLetterCaseCount = 15 ∧
                    currentTechnicalEvidence.oneLetterCaseCount = 15 ∧
                      currentTechnicalEvidence.sugarPrefixCaseCount = 5 := by
  decide



def currentOpenNucleicAcidReviewRequirements :
    List IUPACNormativeSource.ProvisionAuditRequirement :=
  IUPACNormativeSource.currentOpenProvisionAuditRequirements
    .nucleicAcidRecommendations1970

@[simp] theorem current_source_review_exact :
    NucleicAcid1970.currentSourceReview.sourceBundleSha256 =
        sourceSnapshot.bundleSha256 ∧
      NucleicAcid1970.currentSourceReview.reviewedArtifacts = 19 ∧
        NucleicAcid1970.currentSourceReview.reviewedHtmlArtifacts.length = 2 ∧
          NucleicAcid1970.currentSourceReview.reviewedImageArtifacts.length = 17 ∧
            NucleicAcid1970.currentSourceReview.reviewedProvisions.length = 21 ∧
              NucleicAcid1970.currentSourceReview.reviewedErrata.length = 3 ∧
                NucleicAcid1970.currentSourceReview.molecularGraphImageCount = 0 := by
  decide

@[simp] theorem current_open_nucleic_acid_review_requirements_exact :
    currentOpenNucleicAcidReviewRequirements = [] := by
  decide

@[simp] theorem current_source_review_gates_complete :
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .nucleicAcidRecommendations1970).Complete := by
  simp [IUPACNormativeSource.currentProvisionAuditChecklist,
    IUPACNormativeSource.ProvisionAuditChecklist.Complete,
    NucleicAcid1970.currentSourceReviewProvisionEnumerationConfirmed,
    NucleicAcid1970.currentSourceReviewProseTableCoverageConfirmed,
    NucleicAcid1970.currentSourceReviewFigureGraphTranscriptionsReviewed]

def currentIndependentReviewPackageIssued : Bool := true

@[simp] theorem current_independent_review_package_issued :
    currentIndependentReviewPackageIssued = true := by
  rfl

structure IndependentReviewPackage where
  evidence : TechnicalEvidence
  evidenceExact : evidence = currentTechnicalEvidence
  openRequirementsExact : currentOpenNucleicAcidReviewRequirements = []
  auditComplete :
    IUPACNormativeSource.ProvisionAuditComplete .nucleicAcidRecommendations1970

def currentIndependentReviewPackage : IndependentReviewPackage where
  evidence := currentTechnicalEvidence
  evidenceExact := rfl
  openRequirementsExact := current_open_nucleic_acid_review_requirements_exact
  auditComplete := by
    exact current_source_review_gates_complete

abbrev MachinePreparedForIndependentReview := IndependentReviewPackage

def currentMachinePreparedForIndependentReview :
    MachinePreparedForIndependentReview :=
  currentIndependentReviewPackage

theorem current_nucleic_acid_audit_complete :
    IUPACNormativeSource.ProvisionAuditComplete .nucleicAcidRecommendations1970 :=
  currentIndependentReviewPackage.auditComplete

end TechnicalAuditReadiness
end NucleicAcid1970
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.NucleicAcid1970.TechnicalAuditReadiness.source_snapshot_partition_exact
assert_kernel_only
  TetraStereo.OneCenter.NucleicAcid1970.TechnicalAuditReadiness.compiled_entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.NucleicAcid1970.TechnicalAuditReadiness.reverse_direction_markers_exact
assert_kernel_only
  TetraStereo.OneCenter.NucleicAcid1970.TechnicalAuditReadiness.every_incorporated_erratum_nonsemantic
assert_kernel_only
  TetraStereo.OneCenter.NucleicAcid1970.TechnicalAuditReadiness.every_compiled_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.NucleicAcid1970.TechnicalAuditReadiness.currentTechnicalEvidence
assert_kernel_only
  TetraStereo.OneCenter.NucleicAcid1970.TechnicalAuditReadiness.current_source_review_exact
assert_kernel_only
  TetraStereo.OneCenter.NucleicAcid1970.TechnicalAuditReadiness.current_open_nucleic_acid_review_requirements_exact
assert_kernel_only
  TetraStereo.OneCenter.NucleicAcid1970.TechnicalAuditReadiness.current_nucleic_acid_audit_complete
