import TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamilyReport
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileOccurrenceFacts
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileScheduledSource
import TetraStereo.UniversalProof.FamilyExportBridge

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileCompilerClosure

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule TetraStereo.Engine
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
open TetraStereo.UniversalProof.NextFrontier.NativeNitrileInitialSeed
open TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamilyReport
open TetraStereo.UniversalProof.NextFrontier.NativeNitrileScheduledSource
open TetraStereo.UniversalProof.RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel

theorem actual_public_row_membership (n : Nat) (parity : TetrahedralInputParity) :
    parityRow parity ∈ analyzeNormalized (nitrileResult n parity) := by
  rw [actual_normalized_whole_report]
  apply List.mem_filterMap.mpr
  refine ⟨0, ?_, ?_⟩
  · rw [raw_atomCount]
    exact List.mem_range.mpr (by omega)
  · simp [fullEntry, FamilyReportBridge.entry]

theorem actual_scheduled_meaning (n : Nat) (parity : TetrahedralInputParity) :
    ConstitutionParserRichDescriptorMeaning (expanded parity n) (nitrileSource parity n)
      (expanded_source_annotation_agreement parity n) (expanded_stereochemical_admissible parity n).2
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n))
      (scheduledView n parity) 4 (.chiral (descriptorOfParity parity false)) :=
  FamilySourceBridge.scheduled_output_sound (expanded parity n) (nitrileSource parity n)
    (expanded_source_annotation_agreement parity n) (expanded_stereochemical_admissible parity n).2 1 4
    ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n))
    (.chiral (descriptorOfParity parity false)) (actual_scheduled_descriptor n parity)


/-- The actual authoritative occurrence API, scheduled own-source label and public row name
the same atom and descriptor. The occurrence and seed evidence sizes remain distinct. -/
def RuntimeSourceAgreement (n : Nat) (parity : TetrahedralInputParity) : Prop :=
  ∃ fact : RawDescriptorFact,
    tetrahedralOccurrenceFactAuthoritative? (expanded parity n) (analysisFuel (expanded parity n)) 0 = some fact ∧
    scheduledState n parity ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n)) =
      some (.chiral fact.descriptor) ∧
    ({ unit := .tetrahedral 0, outcome := rawDescriptorFactOutcome fact } : StereoAssignment) ∈
      analyzeNormalized (nitrileResult n parity)

theorem runtimeSourceAgreement_holds (n : Nat) (parity : TetrahedralInputParity) :
    RuntimeSourceAgreement n parity := by
  refine ⟨recoveredPublicFact 0 [1, 2, 3, 0] (descriptorOfParity parity false),
    actual_public_analysis_fuel parity n, actual_scheduled_descriptor n parity, ?_⟩
  simpa only [recoveredPublicFact, rawDescriptorFactOutcome, ↓reduceIte, parityRow] using
    actual_public_row_membership n parity

/-- The production second-sphere sorter retains the decisive multiple-bond duplicate,
and the actual occurrence dispatcher consequently uses its supported legacy route. -/
def ActualDuplicateDecision (n : Nat) (parity : TetrahedralInputParity) : Prop :=
  ({ source := 2, target := 3, kind := .triple } : RawBond) ∈ (raw parity n).bonds ∧
  FrameRuntime.profile? (expanded parity n) (canonicalCenterRoot 0) = none ∧
  (∀ fuel : Nat, ∀ stage : CanonicalRuleStage,
    (sortCursorsBy? (compareCursorBranchAtAuthoritative? (expanded parity n) (fuel + 1) stage)
      (nitrileCursor.children (expanded parity n))).bind (fun sorted =>
        (sorted[1]?).map (fun cursor => cursor.node.provenance)) =
      some (.multipleBondDuplicate 1)) ∧
  (∀ fuel : Nat, ∀ state : OccurrenceAuxState,
    occurrenceFactAuthoritative? (expanded parity n) fuel state (canonicalCenterRoot 0) =
      legacyOccurrenceFactAuthoritative? (expanded parity n) fuel state (canonicalCenterRoot 0))

theorem actualDuplicateDecision_holds (n : Nat) (parity : TetrahedralInputParity) :
    ActualDuplicateDecision n parity :=
  ⟨raw_triple_present parity n, expanded_profile_none parity n,
    actual_sorted_second_nitrogen_provenance parity n,
    actual_authoritative_dispatch_legacy parity n⟩

/-- A substantive member claim: actual String admission, decisive duplicate provenance,
corrected expanded frame, both runtime routes, full report, actual source conversion,
the own-source scheduled model and the same-fact bridge. -/
def FamilyMemberClaim (n : Nat) (parity : TetrahedralInputParity) : Prop :=
  parseOpenSMILES (smiles parity n) = .ok (raw parity n) ∧
  parseAndNormalizeOpenSMILESCertified (smiles parity n) = .ok (rawCertified parity n) ∧
  (raw parity n).atomCount = n + 7 ∧
  (raw parity n).hydrogenHasPreceding 0 = false ∧
  (expanded parity n).atomCount = 3 * n + 14 ∧
  (expanded parity n).writtenNeighbors 0 = [n + 7, 1, 2, 4] ∧
  (expanded parity n).StereochemicalAdmissible ∧
  ActualDuplicateDecision n parity ∧
  (nitrileInitial n parity).factAt? 0 = some (seedFact parity) ∧
  tetrahedralOccurrenceFactAuthoritative? (expanded parity n) (analysisFuel (expanded parity n)) 0 =
    some (recoveredPublicFact 0 [1, 2, 3, 0] (descriptorOfParity parity false)) ∧
  analyzeSmiles (smiles parity n) = .ok (fullRows n parity) ∧
  (fullRows n parity).filter (fun row => row.outcome.assigned) = [parityRow parity] ∧
  (∀ row ∈ fullRows n parity, row.outcome.assigned = false →
    row.outcome = .refused .notSpecified ∨ row.outcome = .refused .rankingUnresolved) ∧
  (expanded parity n).toAuthoritativeChemicalInput? = some (nitrileSource parity n) ∧
  ((nitrileSource parity n).aromaticCanonicalOccurrenceSystem
    (constitutionParserRichAuxiliarySemantics (expanded parity n) (nitrileSource parity n)
      (expanded_source_annotation_agreement parity n) (expanded_stereochemical_admissible parity n).2 1 4)).CIPModel
        (scheduledState n parity) ∧
  scheduledState n parity ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n)) =
    some (.chiral (descriptorOfParity parity false)) ∧
  ConstitutionParserRichDescriptorMeaning (expanded parity n) (nitrileSource parity n)
    (expanded_source_annotation_agreement parity n) (expanded_stereochemical_admissible parity n).2
    ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n))
    (scheduledView n parity) 4 (.chiral (descriptorOfParity parity false)) ∧
  RuntimeSourceAgreement n parity

theorem familyMemberClaim_holds (n : Nat) (parity : TetrahedralInputParity) :
    FamilyMemberClaim n parity :=
  ⟨actual_parse parity n, actual_certified_parse parity n,
    raw_atomCount parity n, show (raw parity n).hydrogenHasPreceding 0 = false from rfl, expanded_atomCount parity n,
    expanded_center_row parity n, expanded_stereochemical_admissible parity n,
    actualDuplicateDecision_holds n parity,
    actual_initial_seed_lookup n parity, actual_public_analysis_fuel parity n,
    actual_string_full_report n parity, actual_assigned_projection n parity,
    actual_refusal_vocabulary n parity, expanded_source_conversion parity n, actual_scheduled_model n parity,
    actual_scheduled_descriptor n parity, actual_scheduled_meaning n parity,
    runtimeSourceAgreement_holds n parity⟩

/-- Every natural chain length, including n=0, and both input parities. -/
def FamilyClaim : Prop := ∀ n : Nat, ∀ parity : TetrahedralInputParity, FamilyMemberClaim n parity

theorem familyClaim_holds : FamilyClaim := familyMemberClaim_holds

def fixedPlan : PublicClaimTheoremPlan where
  imports := ["TetraStereo.UniversalProof.NextFrontier.NativeNitrileCompilerClosure", "TetraStereo.KernelOnly"]
  namespacePath := ["TetraStereo", "Generated", "NativeNitrileFamilyCompilerExport"]
  theoremName := "nativeNitrileFamilyCorrect"
  statement := "TetraStereo.UniversalProof.NextFrontier.NativeNitrileCompilerClosure.FamilyClaim"
  proofTerm := "  exact TetraStereo.UniversalProof.NextFrontier.NativeNitrileCompilerClosure.compiledArtifact_checked\n\nexample : TetraStereo.UniversalProof.NextFrontier.NativeNitrileCompilerClosure.compiledArtifact.claim :=\n  nativeNitrileFamilyCorrect\n\nassert_kernel_only TetraStereo.Generated.NativeNitrileFamilyCompilerExport.nativeNitrileFamilyCorrect"

def compiledArtifact : LeanCertificateArtifact :=
  compilePublicClaim fixedPlan .multiCenterRelation
    "Unbounded nitrile STRING family: actual duplicate decision, parser, runtime, full report and SAME scheduled source"
    FamilyClaim familyClaim_holds

theorem compiledArtifact_claim : compiledArtifact.claim = FamilyClaim := rfl

theorem compiledArtifact_checked : compiledArtifact.claim := compiledArtifact.checked

def exportMetadata : FamilyExportBridge.Metadata where
  key := "native-nitrile-family-compiler-export"
  description := "Every nitrile chain length and both input parities: actual String/report/runtime, decisive duplicate and SAME scheduled source"
  fileName := "NativeNitrileCompilerExport.lean"

def sourceEntry : CertificateSourceEntry :=
  FamilyExportBridge.sourceEntry exportMetadata compiledArtifact

theorem sourceEntry_actual_compiler_source : sourceEntry.source = compiledArtifact.source := rfl

def writeFamilyExport (outputDirectory : String) : IO System.FilePath :=
  FamilyExportBridge.write sourceEntry outputDirectory

theorem writeFamilyExport_emits_renderer (outputDirectory : String) :
    writeFamilyExport outputDirectory = (do
      IO.FS.createDirAll (System.FilePath.mk outputDirectory)
      let path := sourceEntry.outputPath outputDirectory
      IO.FS.writeFile path sourceEntry.fileSource
      pure path) :=
  FamilyExportBridge.write_emits_renderer sourceEntry outputDirectory

theorem inhabited_compiler_family_claim :
    ∃ artifact : LeanCertificateArtifact, artifact = compiledArtifact ∧
      artifact.claim = FamilyClaim ∧ artifact.claim ∧ artifact.source = sourceEntry.source :=
  FamilyExportBridge.inhabited_artifact exportMetadata compiledArtifact FamilyClaim compiledArtifact_claim

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileCompilerClosure
