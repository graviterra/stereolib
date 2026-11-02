import TetraStereo.UniversalProof.NativeSecondSphereFamilyReport
import TetraStereo.UniversalProof.SecondSphereScheduledSourceView
import TetraStereo.UniversalProof.FramedPrimaryDescriptorAdapterProofs.FramedPrimaryDescriptorAdapter
import TetraStereo.UniversalProof.SecondSphereFamilyValenceInstantiation
import TetraStereo.UniversalProof.SecondSphereNativeBlockParser
import TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering
import TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
import TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
import TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel
import TetraStereo.OneCenter.AuthoritativeChemicalInput
import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.Engine.Claims
import TetraStereo.Engine.CertificateExporter

set_option autoImplicit false










































namespace TetraStereo.UniversalProof.SecondSphereCompilerClosure

open TetraStereo.OneCenter TetraStereo.Engine
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeConstitutionParserCausalModel
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
open TetraStereo.UniversalProof.SecondSphereFamilyValenceInstantiation
open TetraStereo.UniversalProof.SecondSphereNativeBlockParser
open TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering
open TetraStereo.UniversalProof.SecondSphereScheduledSourceView

/-- The public row and actual scheduled source label name the same physical center.
The descriptor is derived from this family's parser parity and proved written priority.
The two successful outputs are conclusions; neither is a caller hypothesis. -/
def SourceAgreement (ps : List TetrahedralInputParity) : Prop :=
  ∀ i : Fin ps.length,
    (familyCenter ps i).1.val = tagIndex i.val ∧
    ({ unit := .tetrahedral (tagIndex i.val),
       outcome := .tetrahedral (descriptorOfParity (ps.get i) false) } : StereoAssignment) ∈
      analyzeNormalized (certifiedFamily ps).result ∧
    familyScheduledState ps
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i)) =
        some (.chiral (descriptorOfParity (ps.get i) false))

theorem sourceAgreement_holds (ps : List TetrahedralInputParity) : SourceAgreement ps := by
  intro i
  refine ⟨?_, SecondSphereFamilyReportBridge.actual_tag_public_membership ps i,
    family_scheduled_descriptor ps i⟩
  have center := family_center_index ps i
  dsimp only [tagIndex]
  omega

/-! ### Repaired-runtime source/report bridge

`RuntimeSourceAgreement` ties the actual repaired occurrence API to the SAME converted source
label and the same public report row. It does not assert whole-`RawDescriptorFact` equality with
the Rule3 seed: the seed route records `evidenceSize = 0` while the repaired fact records
`max 1 state.length`. -/

/-- The actual repaired occurrence wrapper, at each maintained tag index, produces a fact whose
descriptor matches the SAME scheduled source label, and the converted typed outcome is the public
report row at the same physical center. -/
def RuntimeSourceAgreement (ps : List TetrahedralInputParity) : Prop :=
  ∀ i : Fin ps.length, ∃ fact : RawDescriptorFact,
    tetrahedralOccurrenceFactAuthoritative? (familyRaw ps) (analysisFuel (familyRaw ps))
        (tagIndex i.val) = some fact ∧
    familyScheduledState ps
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i)) =
        some (.chiral fact.descriptor) ∧
    ({ unit := .tetrahedral (tagIndex i.val),
       outcome := rawDescriptorFactOutcome fact } : StereoAssignment) ∈
      analyzeNormalized (certifiedFamily ps).result





theorem runtimeSourceAgreement_holds (ps : List TetrahedralInputParity) :
    RuntimeSourceAgreement ps := by
  intro i
  refine ⟨{ atom := tagIndex i.val
            descriptor := descriptorOfParity (ps.get i) false
            uppercase := true
            evidenceSize := max 1 (ps.length - 1)
            decisiveRule? := none
            descriptorDependentPairs := ps.length - 1
            priorityPositions := [2, 0, 3, 1] }, ?_, ?_, ?_⟩
  · exact TetraStereo.UniversalProof.FramedPrimaryDescriptorAdapterProofs.FramedPrimaryDescriptorAdapter.family_repaired_authoritative_raw_fact ps i
  · simpa using family_scheduled_descriptor ps i
  · have hmem := SecondSphereFamilyReportBridge.actual_tag_public_membership ps i
    have outcomeEq : rawDescriptorFactOutcome
        ({ atom := tagIndex i.val
           descriptor := descriptorOfParity (ps.get i) false
           uppercase := true
           evidenceSize := max 1 (ps.length - 1)
           decisiveRule? := none
           descriptorDependentPairs := ps.length - 1
           priorityPositions := [2, 0, 3, 1] } : RawDescriptorFact) =
        .tetrahedral (descriptorOfParity (ps.get i) false) := by
      simp [rawDescriptorFactOutcome]
    rw [outcomeEq]
    exact hmem

def FamilyMemberClaim (ps : List TetrahedralInputParity) : Prop :=
  parseOpenSMILES (nativeFamilyString ps) = .ok (familyRaw ps) ∧
  parseAndNormalizeOpenSMILESCertified (nativeFamilyString ps) = .ok (certifiedFamily ps) ∧
  (certifiedFamily ps).result.parsed = familyRaw ps ∧
  (familyRaw ps).atomCount = 12 * ps.length + 2 ∧
  (familyRaw ps).bonds.length = 12 * ps.length + 1 ∧
  (certifiedFamily ps).result.parsed.ValenceOK ∧
  (certifiedFamily ps).result.parsed.StereochemicalAdmissible ∧
  (certifiedFamily ps).result.parsed.Rule2MassesKnown ∧
  SecondSphereFamilyReportBridge.FamilyReport ps ∧
  SourceAgreement ps ∧
  analyzeSmiles (nativeFamilyString ps) = .ok (analyzeNormalized (certifiedFamily ps).result) ∧
  ((familySource ps).aromaticCanonicalOccurrenceSystem
    (constitutionParserRichAuxiliarySemantics (familyRaw ps) (familySource ps)
      (family_annotation_agreement ps) (familyRaw_writtenNeighborExact ps) 1 4)).CIPModel
        (familyScheduledState ps) ∧
  (∀ i : Fin ps.length,
    familyScheduledState ps
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i)) =
        some (.chiral (descriptorOfParity (ps.get i) false))) ∧
  (∀ i : Fin ps.length,
    ConstitutionParserRichDescriptorMeaning (familyRaw ps) (familySource ps)
      (family_annotation_agreement ps) (familyRaw_writtenNeighborExact ps)
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i))
      (familyScheduledView ps i) 4 (.chiral (descriptorOfParity (ps.get i) false))) ∧
  -- A: actual authoritative auxiliary builder success with exact occurrence count.
  (∀ i : Fin ps.length, ∃ state : OccurrenceAuxState,
    buildOccurrenceAuxStateFullyAuthoritative? (familyRaw ps) (analysisFuel (familyRaw ps))
        (tagIndex i.val) = some state ∧
    state.length = ps.length - 1) ∧
  -- B: actual repaired authoritative raw fact at the same tag index.
  (∀ i : Fin ps.length,
    tetrahedralOccurrenceFactAuthoritative? (familyRaw ps) (analysisFuel (familyRaw ps))
        (tagIndex i.val) =
      some
        { atom := tagIndex i.val
          descriptor := descriptorOfParity (ps.get i) false
          uppercase := true
          evidenceSize := max 1 (ps.length - 1)
          decisiveRule? := none
          descriptorDependentPairs := ps.length - 1
          priorityPositions := [2, 0, 3, 1] }) ∧
  -- C: SAME runtime/source/report bridge.
  RuntimeSourceAgreement ps

theorem familyMemberClaim_holds (ps : List TetrahedralInputParity) : FamilyMemberClaim ps := by
  unfold FamilyMemberClaim
  exact ⟨parse_native_family_string ps,
    SecondSphereFamilyReportBridge.actual_certified_string_intake ps,
    certifiedFamily_parsed ps, familyRaw_atomCount ps, familyRaw_bondCount ps,
    (certifiedFamily ps).valenceOK, (certifiedFamily ps).stereochemicalAdmissible,
    (certifiedFamily ps).rule2MassesKnown,
    SecondSphereFamilyReportBridge.familyReport_holds ps,
    sourceAgreement_holds ps,
    SecondSphereFamilyReportBridge.actual_string_report ps,
    family_scheduled_model ps, family_scheduled_descriptor ps,
    family_scheduled_descriptor_meaning ps,
    (fun i => TetraStereo.UniversalProof.FramedPrimaryDescriptorAdapterProofs.FramedPrimaryDescriptorAdapter.family_auxiliary_build_exact_count ps i),
    (fun i => TetraStereo.UniversalProof.FramedPrimaryDescriptorAdapterProofs.FramedPrimaryDescriptorAdapter.family_repaired_authoritative_raw_fact ps i),
    runtimeSourceAgreement_holds ps⟩

def FamilyClaim : Prop := ∀ ps : List TetrahedralInputParity, FamilyMemberClaim ps

theorem familyClaim_holds : FamilyClaim := familyMemberClaim_holds





def fixedPlan : PublicClaimTheoremPlan where
  imports := ["TetraStereo.UniversalProof.SecondSphereCompilerClosure", "TetraStereo.KernelOnly"]
  namespacePath := ["TetraStereo", "Generated", "SecondSphereRepairedRuntimeFamilyCompilerExport"]
  theoremName := "secondSphereRepairedRuntimeFamilyCorrect"
  statement := "TetraStereo.UniversalProof.SecondSphereCompilerClosure.FamilyClaim"
  proofTerm := "  exact TetraStereo.UniversalProof.SecondSphereCompilerClosure.compiledArtifact_checked\n\nexample : TetraStereo.UniversalProof.SecondSphereCompilerClosure.compiledArtifact.claim :=\n  secondSphereRepairedRuntimeFamilyCorrect\n\nassert_kernel_only TetraStereo.Generated.SecondSphereRepairedRuntimeFamilyCompilerExport.secondSphereRepairedRuntimeFamilyCorrect"

def compiledArtifact : LeanCertificateArtifact :=
  compilePublicClaim fixedPlan .multiCenterRelation
    "Repaired-runtime second-sphere STRING family: full report, SAME scheduled source and actual repaired occurrence"
    FamilyClaim familyClaim_holds

theorem compiledArtifact_claim : compiledArtifact.claim = FamilyClaim := rfl

theorem compiledArtifact_checked : compiledArtifact.claim := compiledArtifact.checked

def sourceEntry : CertificateSourceEntry where
  key := "second-sphere-repaired-runtime-family-compiler-export"
  description := "Twelve-atom blocks: actual STRING intake/report, SAME scheduled source and actual repaired occurrence"
  fileName := "SecondSphereRepairedCompilerExport.lean"
  source := compiledArtifact.source

theorem sourceEntry_actual_compiler_source : sourceEntry.source = compiledArtifact.source := rfl

def writeFamilyExport (outputDirectory : String) : IO System.FilePath :=
  sourceEntry.writeSource outputDirectory

theorem writeFamilyExport_emits_renderer (outputDirectory : String) :
    writeFamilyExport outputDirectory = (do
      IO.FS.createDirAll (System.FilePath.mk outputDirectory)
      let path := sourceEntry.outputPath outputDirectory
      IO.FS.writeFile path sourceEntry.fileSource
      pure path) := rfl

theorem inhabited_compiler_family_claim :
    ∃ artifact : LeanCertificateArtifact, artifact = compiledArtifact ∧
      artifact.claim = FamilyClaim ∧ artifact.claim ∧ artifact.source = sourceEntry.source :=
  ⟨compiledArtifact, rfl, compiledArtifact_claim, compiledArtifact_checked, rfl⟩

end TetraStereo.UniversalProof.SecondSphereCompilerClosure
