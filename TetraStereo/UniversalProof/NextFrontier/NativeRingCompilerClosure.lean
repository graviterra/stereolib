import TetraStereo.UniversalProof.NextFrontier.NativeRingFamilyReport
import TetraStereo.UniversalProof.NextFrontier.NativeRingOccurrenceFacts
import TetraStereo.UniversalProof.NextFrontier.NativeRingScheduledSource
import TetraStereo.UniversalProof.FamilyExportBridge

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingCompilerClosure

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule TetraStereo.Engine
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.NativeRingDomain
open TetraStereo.UniversalProof.GeneralRingPhysicalAdmission
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.NativeRingInitialSeed
open TetraStereo.UniversalProof.NativeRingFamilyReport
open TetraStereo.UniversalProof.NativeRingOccurrenceFacts
open TetraStereo.UniversalProof.NativeRingSourceInput
open TetraStereo.UniversalProof.NativeRingScheduledSource
open TetraStereo.UniversalProof.RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel

theorem actual_public_row_membership (n : Nat) (parity : TetrahedralInputParity) :
    parityRow parity ∈ analyzeNormalized (ringResult n parity) := by
  rw [actual_normalized_whole_report]
  apply List.mem_filterMap.mpr
  refine ⟨0, ?_, ?_⟩
  · rw [atom_count]
    exact List.mem_range.mpr (by omega)
  · simp [fullEntry, FamilyReportBridge.entry]

theorem actual_scheduled_meaning (n : Nat) (parity : TetrahedralInputParity) :
    ConstitutionParserRichDescriptorMeaning (expanded n parity) (ringSource n parity)
      (ring_annotation_agreement n parity) (expanded_stereochemical_admissible n parity).2
      ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity))
      (scheduledView n parity) 4 (.chiral (descriptorOfParity parity false)) :=
  FamilySourceBridge.scheduled_output_sound (expanded n parity) (ringSource n parity)
    (ring_annotation_agreement n parity) (expanded_stereochemical_admissible n parity).2 1 4
    ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity))
    (.chiral (descriptorOfParity parity false)) (actual_scheduled_descriptor n parity)


/-- The actual authoritative occurrence API, scheduled own-source label and public row name
the same atom and descriptor. The occurrence and seed evidence sizes remain distinct. -/
def RuntimeSourceAgreement (n : Nat) (parity : TetrahedralInputParity) : Prop :=
  ∃ fact : RawDescriptorFact,
    tetrahedralOccurrenceFactAuthoritative? (expanded n parity) (analysisFuel (expanded n parity)) 0 = some fact ∧
    scheduledState n parity ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity)) =
      some (.chiral fact.descriptor) ∧
    ({ unit := .tetrahedral 0, outcome := rawDescriptorFactOutcome fact } : StereoAssignment) ∈
      analyzeNormalized (ringResult n parity)

theorem runtimeSourceAgreement_holds (n : Nat) (parity : TetrahedralInputParity) :
    RuntimeSourceAgreement n parity := by
  refine ⟨recoveredPublicFact 0 [1, 2, 3, 0] (descriptorOfParity parity false),
    actual_public_analysis_fuel n parity, actual_scheduled_descriptor n parity, ?_⟩
  simpa only [recoveredPublicFact, rawDescriptorFactOutcome, ↓reduceIte, parityRow] using
    actual_public_row_membership n parity

/-- A substantive member claim: actual String admission, corrected expanded frame, both
runtime routes, full report, own-source scheduled model and the same-fact bridge. -/
def FamilyMemberClaim (n : Nat) (parity : TetrahedralInputParity) : Prop :=
  parseOpenSMILES (ringSyntax n parity) = .ok (ringRaw n parity) ∧
  parseAndNormalizeOpenSMILESCertified (ringSyntax n parity) = .ok (ringRawCertified n parity) ∧
  (ringRaw n parity).atomCount = n + 5 ∧
  (ringRaw n parity).hydrogenHasPreceding 0 = false ∧
  (expanded n parity).atomCount = 3 * n + 9 ∧
  (expanded n parity).writtenNeighbors 0 = [n + 5, 1, 2, n + 4] ∧
  (expanded n parity).StereochemicalAdmissible ∧
  (ringInitial n parity).factAt? 0 = some (seedFact parity) ∧
  tetrahedralOccurrenceFactAuthoritative? (expanded n parity) (analysisFuel (expanded n parity)) 0 =
    some (recoveredPublicFact 0 [1, 2, 3, 0] (descriptorOfParity parity false)) ∧
  analyzeSmiles (ringSyntax n parity) = .ok (fullRows n parity) ∧
  (fullRows n parity).filter (fun row => row.outcome.assigned) = [parityRow parity] ∧
  (∀ row ∈ fullRows n parity, row.outcome.assigned = false →
    row.outcome = .refused .notSpecified ∨ row.outcome = .refused .rankingUnresolved) ∧
  ((ringSource n parity).aromaticCanonicalOccurrenceSystem
    (constitutionParserRichAuxiliarySemantics (expanded n parity) (ringSource n parity)
      (ring_annotation_agreement n parity) (expanded_stereochemical_admissible n parity).2 1 4)).CIPModel
        (scheduledState n parity) ∧
  scheduledState n parity ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity)) =
    some (.chiral (descriptorOfParity parity false)) ∧
  ConstitutionParserRichDescriptorMeaning (expanded n parity) (ringSource n parity)
    (ring_annotation_agreement n parity) (expanded_stereochemical_admissible n parity).2
    ((ringSource n parity).aromaticCanonicalFinalOccurrence 1 (ringCenter n parity))
    (scheduledView n parity) 4 (.chiral (descriptorOfParity parity false)) ∧
  RuntimeSourceAgreement n parity

theorem familyMemberClaim_holds (n : Nat) (parity : TetrahedralInputParity) :
    FamilyMemberClaim n parity :=
  ⟨NativeRingParserPublic.parse_ring n parity, NativeRingParserPublic.certified_ring n parity,
    atom_count n parity, root_has_no_predecessor n parity, expanded_atom_count n parity,
    expanded_root_written_row n parity, expanded_stereochemical_admissible n parity,
    actual_initial_seed_lookup n parity, actual_public_analysis_fuel n parity,
    actual_string_full_report n parity, actual_assigned_projection n parity,
    actual_refusal_vocabulary n parity, actual_scheduled_model n parity,
    actual_scheduled_descriptor n parity, actual_scheduled_meaning n parity,
    runtimeSourceAgreement_holds n parity⟩

/-- Every ring size n+3, including the triangle, and both input parities. -/
def FamilyClaim : Prop := ∀ n : Nat, ∀ parity : TetrahedralInputParity, FamilyMemberClaim n parity

theorem familyClaim_holds : FamilyClaim := familyMemberClaim_holds

def fixedPlan : PublicClaimTheoremPlan where
  imports := ["TetraStereo.UniversalProof.NextFrontier.NativeRingCompilerClosure", "TetraStereo.KernelOnly"]
  namespacePath := ["TetraStereo", "Generated", "NativeRingFamilyCompilerExport"]
  theoremName := "nativeRingFamilyCorrect"
  statement := "TetraStereo.UniversalProof.NativeRingCompilerClosure.FamilyClaim"
  proofTerm := "  exact TetraStereo.UniversalProof.NativeRingCompilerClosure.compiledArtifact_checked\n\nexample : TetraStereo.UniversalProof.NativeRingCompilerClosure.compiledArtifact.claim :=\n  nativeRingFamilyCorrect\n\nassert_kernel_only TetraStereo.Generated.NativeRingFamilyCompilerExport.nativeRingFamilyCorrect"

def compiledArtifact : LeanCertificateArtifact :=
  compilePublicClaim fixedPlan .multiCenterRelation
    "All-size chlorinated ring STRING family: corrected frame, actual runtime, full report and SAME scheduled source"
    FamilyClaim familyClaim_holds

theorem compiledArtifact_claim : compiledArtifact.claim = FamilyClaim := rfl

theorem compiledArtifact_checked : compiledArtifact.claim := compiledArtifact.checked

def exportMetadata : FamilyExportBridge.Metadata where
  key := "native-ring-family-compiler-export"
  description := "Every n+3 ring and both input parities: actual String/report/runtime and SAME scheduled source"
  fileName := "NativeRingCompilerExport.lean"

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

end TetraStereo.UniversalProof.NativeRingCompilerClosure
