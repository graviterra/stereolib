import TetraStereo.OneCenter.IUPACGlobalNonDescriptorGlycolipidSourceMeaningCompletionBatch
import TetraStereo.KernelOnly

set_option autoImplicit false





















namespace TetraStereo.OneCenter
namespace Glycolipid1997
namespace TechnicalAuditReadiness

open IUPACNormativeProvision
open IUPACNormativeProvision.GlobalNonDescriptorGlycolipidSourceMeaning

def sourceSnapshot : P10DelegatedAuthorityCorpus.Snapshot :=
  P10DelegatedAuthorityCorpus.snapshot .glycolipid1997

/-- SHA-256 of the 13-page primary PDF reached through DOI `10.1351/pac199769122475`. -/
def primaryPublicationSha256 : String :=
  "87f1874c989845f41241ce1a5739438d26d5a1888dc79c8b31320239eb084dff"

def primaryPublicationPageCount : Nat := 13

def modeledProvisions : List IUPACNormativeProvision :=
  GlobalNonDescriptorGlycolipidSourceMeaning.fullFamilyProvisions

def completionEntries : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorGlycolipidSourceMeaning.completionBatch.entries

def indexedEntries : List GlobalNonDescriptorSourceMeaningEntry :=
  GlobalNonDescriptorIndexedSourceData.glycolipidBatch.entries

/-- Source order: the 24 base clauses followed by seven Table-2 and twelve Table-3 rows. -/
def compiledEntries : List GlobalNonDescriptorSourceMeaningEntry :=
  completionEntries ++ indexedEntries

def incorporatedErrata := Glycolipid1997.IncorporatedErratum.all

def unlistedWebTranscriptionDefects :=
  Glycolipid1997.UnlistedWebTranscriptionDefect.all

def monosaccharideCases := GlobalNonDescriptorGlycolipidSourceMeaning.monosaccharides

def invariantAnomericCases :=
  GlobalNonDescriptorGlycolipidSourceMeaning.invariantAnomericInventory

def citationCases := GlobalNonDescriptorGlycolipidSourceMeaning.citationInventory

def rootCases := GlobalNonDescriptorGlycolipidSourceMeaning.rootInventory

def svennerholmCases := GlobalNonDescriptorGlycolipidSourceMeaning.svennerholmInventory

@[simp] theorem source_snapshot_counts_exact :
    sourceSnapshot.artifactCount = 15 ∧
      sourceSnapshot.htmlCount = 2 ∧
        sourceSnapshot.imageCount = 13 := by
  decide

@[simp] theorem source_snapshot_partition_exact :
    sourceSnapshot.htmlCount + sourceSnapshot.imageCount =
      sourceSnapshot.artifactCount := by
  simp [sourceSnapshot]

@[simp] theorem family_partition_counts_exact :
    modeledProvisions.length = 43 ∧
      compiledEntries.length = 43 ∧
        completionEntries.length = 24 ∧
          indexedEntries.length = 19 := by
  simp [modeledProvisions, compiledEntries, completionEntries, indexedEntries]

@[simp] theorem compiled_entry_provisions_exact :
    compiledEntries.map GlobalNonDescriptorSourceMeaningEntry.provision =
      modeledProvisions := by
  rw [compiledEntries, List.map_append]
  change
    completionBatch.entries.map GlobalNonDescriptorSourceMeaningEntry.provision ++
        GlobalNonDescriptorIndexedSourceData.glycolipidBatch.entries.map
          GlobalNonDescriptorSourceMeaningEntry.provision =
      modeledProvisions
  rw [completion_entry_provisions_exact,
    GlobalNonDescriptorIndexedSourceData.glycolipidBatch.provisions_exact]
  exact completion_then_indexed_exact_source_order

theorem modeled_provisions_nodup : modeledProvisions.Nodup := by
  unfold modeledProvisions fullFamilyProvisions fullFamilyRows
  exact Glycolipid1997.Provision.all_nodup.map
    (by intro left right equal; cases equal; rfl)

@[simp] theorem typed_inventory_counts_exact :
    incorporatedErrata.length = 8 ∧
      unlistedWebTranscriptionDefects.length = 1 ∧
        monosaccharideCases.length = 10 ∧
          invariantAnomericCases.length = 10 ∧
            citationCases.length = 2 ∧
              rootCases.length = 7 ∧
                svennerholmCases.length = 12 ∧
                  Glycolipid1997.gpiCore.length = 4 := by
  decide

@[simp] theorem GQ1b_primary_and_web_source_variants_exact :
    Glycolipid1997.SvennerholmEntry.structureCode .GQ1b =
        "Neu5Acα8Neu5Acα3Galβ3GalNAcβ4(Neu5Acα8Neu5Acα3)Galβ4GlcCer" ∧
      Glycolipid1997.SvennerholmEntry.webLiteralStructureCode .GQ1b =
        "Neu5Acα8Neu5Acα3Galβ3GalNAcβ4(Neu5Acα8Neu5cα3)Galβ4GlcCer" := by
  decide

theorem only_GL65_erratum_changes_structure_reading
    (erratum : Glycolipid1997.IncorporatedErratum) :
    erratum.changesStructureReading ↔ erratum = .gl65BranchAlignment :=
  Glycolipid1997.IncorporatedErratum.only_GL65_alignment_changes_structure_reading erratum

@[simp] theorem sphingoid_configuration_cases_exact :
    Glycolipid1997.sphinganine = ⟨.S, .R, none, []⟩ ∧
      Glycolipid1997.sphingFourEnine = ⟨.S, .R, none, [(4, .E)]⟩ ∧
        Glycolipid1997.phytosphingosine = ⟨.S, .S, some .R, []⟩ := by
  decide

theorem every_compiled_entry_nonvacuous
    (entry : GlobalNonDescriptorSourceMeaningEntry) (_member : entry ∈ compiledEntries) :
    ∃ input, ∃ observation : entry.reference.toReference.Observation,
      input.StructurallyWellFormed ∧
        entry.reference.toReference.Applicable input ∧
          entry.reference.toReference.Judges input observation :=
  entry.admittedJudgment

/-! ## One proof-carrying machine dossier -/

structure TechnicalEvidence where
  sourceArtifactCount : Nat
  sourceHtmlCount : Nat
  sourceImageCount : Nat
  primaryPdfPageCount : Nat
  modeledProvisionCount : Nat
  compiledEntryCount : Nat
  completionEntryCount : Nat
  indexedEntryCount : Nat
  incorporatedErratumCount : Nat
  unlistedWebDefectCount : Nat
  textualSourceReview : Glycolipid1997.TextualSourceReviewEvidence
  sourceRootUrl : String
  sourceRetrievalDate : String
  sourceBundleSha256 : String
  primaryPdfSha256 : String
  sourceArtifactCountExact : sourceArtifactCount = sourceSnapshot.artifactCount
  sourceHtmlCountExact : sourceHtmlCount = sourceSnapshot.htmlCount
  sourceImageCountExact : sourceImageCount = sourceSnapshot.imageCount
  primaryPdfPageCountExact : primaryPdfPageCount = primaryPublicationPageCount
  modeledProvisionCountExact : modeledProvisionCount = modeledProvisions.length
  compiledEntryCountExact : compiledEntryCount = compiledEntries.length
  completionEntryCountExact : completionEntryCount = completionEntries.length
  indexedEntryCountExact : indexedEntryCount = indexedEntries.length
  incorporatedErratumCountExact : incorporatedErratumCount = incorporatedErrata.length
  unlistedWebDefectCountExact :
    unlistedWebDefectCount = unlistedWebTranscriptionDefects.length
  textualSourceReviewExact : textualSourceReview = Glycolipid1997.currentTextualSourceReview
  sourceRootUrlExact : sourceRootUrl = sourceSnapshot.rootUrl
  sourceRetrievalDateExact : sourceRetrievalDate = sourceSnapshot.retrievalDate
  sourceBundleSha256Exact : sourceBundleSha256 = sourceSnapshot.bundleSha256
  primaryPdfSha256Exact : primaryPdfSha256 = primaryPublicationSha256
  sourceArtifactPartitionExact :
    sourceSnapshot.htmlCount + sourceSnapshot.imageCount = sourceSnapshot.artifactCount
  modeledProvisionsNodup : modeledProvisions.Nodup
  compiledEntryProvisionsExact :
    compiledEntries.map GlobalNonDescriptorSourceMeaningEntry.provision = modeledProvisions
  GQ1bSourceVariantsExact :
    Glycolipid1997.SvennerholmEntry.structureCode .GQ1b =
        "Neu5Acα8Neu5Acα3Galβ3GalNAcβ4(Neu5Acα8Neu5Acα3)Galβ4GlcCer" ∧
      Glycolipid1997.SvennerholmEntry.webLiteralStructureCode .GQ1b =
        "Neu5Acα8Neu5Acα3Galβ3GalNAcβ4(Neu5Acα8Neu5cα3)Galβ4GlcCer"
  allCompiledEntriesNonvacuous :
    ∀ entry ∈ compiledEntries,
      ∃ input, ∃ observation : entry.reference.toReference.Observation,
        input.StructurallyWellFormed ∧
          entry.reference.toReference.Applicable input ∧
            entry.reference.toReference.Judges input observation

def currentTechnicalEvidence : TechnicalEvidence where
  sourceArtifactCount := 15
  sourceHtmlCount := 2
  sourceImageCount := 13
  primaryPdfPageCount := 13
  modeledProvisionCount := 43
  compiledEntryCount := 43
  completionEntryCount := 24
  indexedEntryCount := 19
  incorporatedErratumCount := 8
  unlistedWebDefectCount := 1
  textualSourceReview := Glycolipid1997.currentTextualSourceReview
  sourceRootUrl := "https://iupac.qmul.ac.uk/misc/glylp.html"
  sourceRetrievalDate := "2026-08-11"
  sourceBundleSha256 :=
    "a269ce3f407ae4226e3919b99a4f04c1f98069a180b952f89b998e8ff8bd2a58"
  primaryPdfSha256 :=
    "87f1874c989845f41241ce1a5739438d26d5a1888dc79c8b31320239eb084dff"
  sourceArtifactCountExact := by simp
  sourceHtmlCountExact := by simp
  sourceImageCountExact := by simp
  primaryPdfPageCountExact := rfl
  modeledProvisionCountExact := by simp
  compiledEntryCountExact := by simp
  completionEntryCountExact := by simp
  indexedEntryCountExact := by simp
  incorporatedErratumCountExact := by decide
  unlistedWebDefectCountExact := by decide
  textualSourceReviewExact := rfl
  sourceRootUrlExact := rfl
  sourceRetrievalDateExact := rfl
  sourceBundleSha256Exact := rfl
  primaryPdfSha256Exact := rfl
  sourceArtifactPartitionExact := source_snapshot_partition_exact
  modeledProvisionsNodup := modeled_provisions_nodup
  compiledEntryProvisionsExact := compiled_entry_provisions_exact
  GQ1bSourceVariantsExact := GQ1b_primary_and_web_source_variants_exact
  allCompiledEntriesNonvacuous := every_compiled_entry_nonvacuous



def currentOpenGlycolipidReviewRequirements :
    List IUPACNormativeSource.ProvisionAuditRequirement :=
  IUPACNormativeSource.currentOpenProvisionAuditRequirements
    .glycolipidRecommendations1997

@[simp] theorem current_textual_source_review_exact :
    Glycolipid1997.currentTextualSourceReview.sourceBundleSha256 =
        sourceSnapshot.bundleSha256 ∧
      Glycolipid1997.currentTextualSourceReview.primaryPublicationSha256 =
          primaryPublicationSha256 ∧
        Glycolipid1997.currentTextualSourceReview.reviewedArtifacts = 15 ∧
          Glycolipid1997.currentTextualSourceReview.reviewedImages = 13 ∧
            Glycolipid1997.currentTextualSourceReview.reviewedProvisions.length = 43 ∧
              Glycolipid1997.currentTextualSourceReview.reviewedRootRows.length = 7 ∧
                Glycolipid1997.currentTextualSourceReview.reviewedSvennerholmRows.length = 12 ∧
                  Glycolipid1997.currentTextualSourceReview.reviewedErrata.length = 8 ∧
                    Glycolipid1997.currentTextualSourceReview.figureGraphReviewIssued = false := by
  decide

@[simp] theorem current_open_glycolipid_review_requirements_exact :
    currentOpenGlycolipidReviewRequirements =
      [ .figureGraphTranscriptionsReviewed ] := by
  decide

@[simp] theorem current_textual_gates_confirmed_and_figure_gate_open :
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .glycolipidRecommendations1997).provisionEnumerationConfirmed = true ∧
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .glycolipidRecommendations1997).proseTableCoverageConfirmed = true ∧
    (IUPACNormativeSource.currentProvisionAuditChecklist
      .glycolipidRecommendations1997).figureGraphTranscriptionsReviewed = false := by
  decide

def currentIndependentReviewPackageIssued : Bool := false

@[simp] theorem current_independent_review_package_not_issued :
    currentIndependentReviewPackageIssued = false := by
  rfl

structure MachinePreparedForIndependentReview where
  evidence : TechnicalEvidence
  evidenceExact : evidence = currentTechnicalEvidence
  openRequirementsExact : currentOpenGlycolipidReviewRequirements =
    [ .figureGraphTranscriptionsReviewed ]

def currentMachinePreparedForIndependentReview :
    MachinePreparedForIndependentReview where
  evidence := currentTechnicalEvidence
  evidenceExact := rfl
  openRequirementsExact := current_open_glycolipid_review_requirements_exact

theorem current_glycolipid_audit_remains_incomplete :
    ¬IUPACNormativeSource.ProvisionAuditComplete .glycolipidRecommendations1997 := by
  simp [IUPACNormativeSource.ProvisionAuditComplete,
    IUPACNormativeSource.currentProvisionAuditChecklist,
    IUPACNormativeSource.ProvisionAuditChecklist.Complete]

end TechnicalAuditReadiness
end Glycolipid1997
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Glycolipid1997.TechnicalAuditReadiness.source_snapshot_partition_exact
assert_kernel_only
  TetraStereo.OneCenter.Glycolipid1997.TechnicalAuditReadiness.compiled_entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.Glycolipid1997.TechnicalAuditReadiness.GQ1b_primary_and_web_source_variants_exact
assert_kernel_only
  TetraStereo.OneCenter.Glycolipid1997.TechnicalAuditReadiness.only_GL65_erratum_changes_structure_reading
assert_kernel_only
  TetraStereo.OneCenter.Glycolipid1997.TechnicalAuditReadiness.sphingoid_configuration_cases_exact
assert_kernel_only
  TetraStereo.OneCenter.Glycolipid1997.TechnicalAuditReadiness.every_compiled_entry_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.Glycolipid1997.TechnicalAuditReadiness.currentTechnicalEvidence
assert_kernel_only
  TetraStereo.OneCenter.Glycolipid1997.TechnicalAuditReadiness.current_textual_source_review_exact
assert_kernel_only
  TetraStereo.OneCenter.Glycolipid1997.TechnicalAuditReadiness.current_open_glycolipid_review_requirements_exact
assert_kernel_only
  TetraStereo.OneCenter.Glycolipid1997.TechnicalAuditReadiness.current_glycolipid_audit_remains_incomplete
