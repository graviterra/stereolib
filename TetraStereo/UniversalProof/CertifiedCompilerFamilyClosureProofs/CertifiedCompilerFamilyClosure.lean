import TetraStereo.UniversalProof.CertifiedFamilyValenceRecoveryProofs.CertifiedFamilyValenceRecovery
import TetraStereo.Engine.Claims
import TetraStereo.Engine.CertificateExporter

set_option autoImplicit false

namespace TetraStereo.UniversalProof.CertifiedCompilerFamilyClosureProofs.CertifiedCompilerFamilyClosure

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.Engine
open TetraStereo.UniversalProof.ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity
open TetraStereo.UniversalProof.FirstZSeedDiscoveryRecoveryProofs.FirstZSeedDiscoveryRecovery
open TetraStereo.UniversalProof.ActualFamilyReportBridgeProofs.ActualFamilyReportBridge
open TetraStereo.UniversalProof.NativeFamilyRawSupportProofs.PositiveFamilyGeneratorRecovery
open TetraStereo.UniversalProof.CertifiedFamilyValenceRecoveryProofs.CertifiedFamilyValenceRecovery









/-- The complete actual report and SAME own-source labels on the ACTUAL certified result.
Interleaved computed untagged refusals remain present with their honest refusal reasons. -/
def CertifiedFamilyReport (n : ℕ) (parity : ℕ → TetrahedralInputParity)
    (positive : 1 ≤ n) (carrierFuel : ℕ) : Prop :=
    let certificate := certifiedFamily n parity positive
    let result := certificate.result
    let domain := family_normalized_domain n parity positive
    let input := family_normalized_source_input n parity positive
    let fuel := analysisFuel (materialized result)
    analyzeNormalized result = fullRows result fuel ∧
      ((analyzeNormalized result).filter fun assignment => assignment.outcome.assigned) = tagRows result fuel ∧
      (tagRows result fuel).map StereoAssignment.unit =
        (rawAnnotatedCenters result).map StereoUnit.tetrahedral ∧
      (∀ assignment ∈ analyzeNormalized result, assignment.outcome.assigned = false →
        assignment.outcome = .refused .notSpecified ∨ assignment.outcome = .refused .rankingUnresolved) ∧
      (∀ index spec inputParity (observed : result.parsed.atomAt? index = some spec)
        (tagged : spec.tetrahedral? = some inputParity),
        FirstZSourceDiscoveryAlignmentProofs.FirstZSourceDiscoveryAlignment.ownState result domain (familySource result)
          (familyAgreement result domain input) carrierFuel
          ((familySource result).aromaticCanonicalFinalOccurrence carrierFuel
            (tagCenter result domain input index spec inputParity observed tagged)) =
          some (.chiral (seedDescriptor result fuel index inputParity)))

theorem certifiedFamilyReport_holds (n : ℕ) (parity : ℕ → TetrahedralInputParity)
    (positive : 1 ≤ n) (carrierFuel : ℕ) :
    CertifiedFamilyReport n parity positive carrierFuel := by
  unfold CertifiedFamilyReport
  exact positive_family_actual_report_and_source n parity positive carrierFuel

/-- Actual certification succeeds; the RETURNED certificate has the physical counts, encoded
valence/admission/mass proofs and complete actual five-segment/source report. No caller success,
report, source agreement or completed-request premise is accepted. -/
def CertifiedFamilyMemberClaim (n : ℕ) (parity : ℕ → TetrahedralInputParity)
    (positive : 1 ≤ n) (carrierFuel : ℕ) : Prop :=
    let certificate := certifiedFamily n parity positive
    normalizeRawMoleculeCertified? (family n parity) = some certificate ∧
      certificate.result = normalizeRawMolecule (family n parity) ∧
      certificate.result.parsed = family n parity ∧
      certificate.result.parsed.atomCount = 6 * n + 2 ∧
      certificate.result.parsed.bonds.length = 6 * n + 1 ∧
      certificate.result.parsed.ValenceOK ∧
      certificate.result.parsed.StereochemicalAdmissible ∧
      certificate.result.parsed.Rule2MassesKnown ∧
      ZeroHydrogenDemand (family n parity) ∧
      (let branches := normalizedStereoAnalysisBranches certificate.result;
        branches.ordinaryDoubleBond = [] ∧ branches.coupledDoubleBond = [] ∧
          branches.oddCumuleneDoubleBond = [] ∧ branches.extendedAxial = []) ∧
      CertifiedFamilyReport n parity positive carrierFuel

theorem certifiedFamilyMemberClaim_holds (n : ℕ) (parity : ℕ → TetrahedralInputParity)
    (positive : 1 ≤ n) (carrierFuel : ℕ) :
    CertifiedFamilyMemberClaim n parity positive carrierFuel := by
  have atoms : (certifiedFamily n parity positive).result.parsed.atomCount = 6 * n + 2 := by
    rw [certifiedFamily_parsed, family_atomCount]
  have bonds : (certifiedFamily n parity positive).result.parsed.bonds.length = 6 * n + 1 := by
    rw [certifiedFamily_parsed, family_bonds, familyBonds_length n positive]
  unfold CertifiedFamilyMemberClaim
  refine And.intro (family_actual_certified_normalization n parity positive) ?_
  refine And.intro rfl ?_
  refine And.intro (certifiedFamily_parsed n parity positive) ?_
  refine And.intro atoms ?_
  refine And.intro bonds ?_
  refine And.intro (certifiedFamily n parity positive).valenceOK ?_
  refine And.intro (certifiedFamily n parity positive).stereochemicalAdmissible ?_
  refine And.intro (certifiedFamily n parity positive).rule2MassesKnown ?_
  refine And.intro (family_zeroHydrogenDemand n parity) ?_
  exact And.intro (positive_family_other_four_segments_nil n parity positive)
    (certifiedFamilyReport_holds n parity positive carrierFuel)

/-- Inhabited universal certified-intake-to-report compiler proposition, for EVERY positive size
and arbitrary parity assignment. Its inputs are physical data, never desired pipeline results. -/
def CertifiedFamilyClaim : Prop :=
  ∀ (n : ℕ) (parity : ℕ → TetrahedralInputParity) (positive : 1 ≤ n) (carrierFuel : ℕ),
    CertifiedFamilyMemberClaim n parity positive carrierFuel

theorem certifiedFamilyClaim_holds : CertifiedFamilyClaim :=
  certifiedFamilyMemberClaim_holds

/-- An actual returned certificate witness, with the general complete certified family claim. -/
theorem actual_certified_family_member (n : ℕ) (parity : ℕ → TetrahedralInputParity)
    (positive : 1 ≤ n) (carrierFuel : ℕ) :
    ∃ certificate : CertifiedChemistryNormalizationResult,
      normalizeRawMoleculeCertified? (family n parity) = some certificate ∧
      certificate.result = normalizeRawMolecule (family n parity) ∧
      certificate.result.parsed.ValenceOK ∧
      CertifiedFamilyMemberClaim n parity positive carrierFuel :=
  ⟨certifiedFamily n parity positive, family_actual_certified_normalization n parity positive,
    rfl, (certifiedFamily n parity positive).valenceOK,
    certifiedFamilyMemberClaim_holds n parity positive carrierFuel⟩

/-- Fixed declaration/proof target; caller-chosen strings and desired success claims are absent. -/
def fixedCertifiedFamilyPlan : PublicClaimTheoremPlan where
  imports := ["TetraStereo.UniversalProof.CertifiedCompilerFamilyClosureProofs.CertifiedCompilerFamilyClosure", "TetraStereo.KernelOnly"]
  namespacePath := ["TetraStereo", "Generated", "CertifiedPositivePendantFamilyCompilerExport"]
  theoremName := "certifiedPositiveFamilyCorrect"
  statement := "TetraStereo.UniversalProof.CertifiedCompilerFamilyClosureProofs.CertifiedCompilerFamilyClosure.CertifiedFamilyClaim"
  proofTerm := "  exact TetraStereo.UniversalProof.CertifiedCompilerFamilyClosureProofs.CertifiedCompilerFamilyClosure.compiledCertifiedFamilyArtifact_checked\n\nexample : (TetraStereo.UniversalProof.CertifiedCompilerFamilyClosureProofs.CertifiedCompilerFamilyClosure.compiledCertifiedFamilyArtifact).claim :=\n  certifiedPositiveFamilyCorrect\n\nassert_kernel_only TetraStereo.Generated.CertifiedPositivePendantFamilyCompilerExport.certifiedPositiveFamilyCorrect\nassert_kernel_only TetraStereo.UniversalProof.CertifiedCompilerFamilyClosureProofs.CertifiedCompilerFamilyClosure.certifiedFamilyReport_holds\nassert_kernel_only TetraStereo.UniversalProof.CertifiedCompilerFamilyClosureProofs.CertifiedCompilerFamilyClosure.certifiedFamilyMemberClaim_holds\nassert_kernel_only TetraStereo.UniversalProof.CertifiedCompilerFamilyClosureProofs.CertifiedCompilerFamilyClosure.certifiedFamilyClaim_holds\nassert_kernel_only TetraStereo.UniversalProof.CertifiedCompilerFamilyClosureProofs.CertifiedCompilerFamilyClosure.actual_certified_family_member\nassert_kernel_only TetraStereo.UniversalProof.CertifiedCompilerFamilyClosureProofs.CertifiedCompilerFamilyClosure.compiledCertifiedFamilyArtifact_claim\nassert_kernel_only TetraStereo.UniversalProof.CertifiedCompilerFamilyClosureProofs.CertifiedCompilerFamilyClosure.compiledCertifiedFamilyArtifact_checked\nassert_kernel_only TetraStereo.UniversalProof.CertifiedCompilerFamilyClosureProofs.CertifiedCompilerFamilyClosure.compiledCertifiedFamilyArtifact_identity\nassert_kernel_only TetraStereo.UniversalProof.CertifiedCompilerFamilyClosureProofs.CertifiedCompilerFamilyClosure.compiledCertifiedFamilyArtifact_kind\nassert_kernel_only TetraStereo.UniversalProof.CertifiedCompilerFamilyClosureProofs.CertifiedCompilerFamilyClosure.certifiedFamilySourceEntry_actual_compiler_source\nassert_kernel_only TetraStereo.UniversalProof.CertifiedCompilerFamilyClosureProofs.CertifiedCompilerFamilyClosure.certifiedFamilySourceEntry_file_source_exact\nassert_kernel_only TetraStereo.UniversalProof.CertifiedCompilerFamilyClosureProofs.CertifiedCompilerFamilyClosure.writeCertifiedFamilyExport_uses_actual_emitter\nassert_kernel_only TetraStereo.UniversalProof.CertifiedCompilerFamilyClosureProofs.CertifiedCompilerFamilyClosure.writeCertifiedFamilyExport_emits_renderer\nassert_kernel_only TetraStereo.UniversalProof.CertifiedCompilerFamilyClosureProofs.CertifiedCompilerFamilyClosure.inhabited_certified_compiler_family_claim"

/-- Real production compiler receives the universal proposition and its internally derived proof. -/
def compiledCertifiedFamilyArtifact : LeanCertificateArtifact :=
  compilePublicClaim fixedCertifiedFamilyPlan .multiCenterRelation
    "Certified positive-size ordinary-single pendant family: actual intake, report and own source"
    CertifiedFamilyClaim certifiedFamilyClaim_holds

theorem compiledCertifiedFamilyArtifact_claim :
    compiledCertifiedFamilyArtifact.claim = CertifiedFamilyClaim := rfl

theorem compiledCertifiedFamilyArtifact_checked : compiledCertifiedFamilyArtifact.claim :=
  compiledCertifiedFamilyArtifact.checked

theorem compiledCertifiedFamilyArtifact_identity :
    compiledCertifiedFamilyArtifact = compilePublicClaim fixedCertifiedFamilyPlan .multiCenterRelation
      "Certified positive-size ordinary-single pendant family: actual intake, report and own source"
      CertifiedFamilyClaim certifiedFamilyClaim_holds := rfl

theorem compiledCertifiedFamilyArtifact_kind : compiledCertifiedFamilyArtifact.kind = .stereoClaim := rfl

/-- Actual production renderer; independent rendered bytes are checked externally after real IO. -/
def certifiedFamilySourceEntry : CertificateSourceEntry where
  key := "certified-positive-pendant-family-compiler-export"
  description := "Universal certified-intake actual family report and same-source theorem"
  fileName := "CertifiedCompilerFamilyClosureKernelCertificate.lean"
  source := fixedCertifiedFamilyPlan.toTheoremExport.source

theorem certifiedFamilySourceEntry_actual_compiler_source :
    certifiedFamilySourceEntry.source = compiledCertifiedFamilyArtifact.source := rfl

def expectedCertifiedEmittedModule : String := certifiedFamilySourceEntry.fileSource

/-- Renderer binding, not independent giant-literal byte-equality evidence. -/
theorem certifiedFamilySourceEntry_file_source_exact :
    certifiedFamilySourceEntry.fileSource = expectedCertifiedEmittedModule := rfl

def writeCertifiedFamilyExport (outputDirectory : String) : IO System.FilePath :=
  certifiedFamilySourceEntry.writeSource outputDirectory

theorem writeCertifiedFamilyExport_uses_actual_emitter (outputDirectory : String) :
    writeCertifiedFamilyExport outputDirectory =
      certifiedFamilySourceEntry.writeSource outputDirectory := rfl

/-- The actual existing writer's IO program writes the SAME production compiler renderer. -/
theorem writeCertifiedFamilyExport_emits_renderer (outputDirectory : String) :
    writeCertifiedFamilyExport outputDirectory = (do
      IO.FS.createDirAll (System.FilePath.mk outputDirectory)
      let path := certifiedFamilySourceEntry.outputPath outputDirectory
      IO.FS.writeFile path expectedCertifiedEmittedModule
      pure path) := rfl

/-- Real typed compiled artifact carries the non-vacuous universal certified pipeline proposition. -/
theorem inhabited_certified_compiler_family_claim :
    ∃ artifact : LeanCertificateArtifact, artifact = compiledCertifiedFamilyArtifact ∧
      artifact.claim = CertifiedFamilyClaim ∧ artifact.claim ∧
      artifact.source = certifiedFamilySourceEntry.source :=
  ⟨compiledCertifiedFamilyArtifact, rfl, compiledCertifiedFamilyArtifact_claim,
    compiledCertifiedFamilyArtifact_checked, certifiedFamilySourceEntry_actual_compiler_source.symm⟩

end TetraStereo.UniversalProof.CertifiedCompilerFamilyClosureProofs.CertifiedCompilerFamilyClosure
