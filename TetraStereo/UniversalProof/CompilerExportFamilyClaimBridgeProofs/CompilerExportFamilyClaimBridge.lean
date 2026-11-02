import TetraStereo.UniversalProof.NativeFamilyRawSupportProofs.PositiveFamilyGeneratorRecovery
import TetraStereo.Engine.Claims
import TetraStereo.Engine.CertificateExporter

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge

#eval IO.eprintln "CompilerExportFamilyClaimBridgeProofs phase: entered family claim module"

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.Engine
open TetraStereo.UniversalProof.ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity
open TetraStereo.UniversalProof.FirstZSeedDiscoveryRecoveryProofs.FirstZSeedDiscoveryRecovery
open TetraStereo.UniversalProof.ActualFamilyReportBridgeProofs.ActualFamilyReportBridge
open TetraStereo.UniversalProof.NativeFamilyRawSupportProofs.PositiveFamilyGeneratorRecovery










/-- Exact actual report and SAME own-source labels, including the real untagged refusal residual. -/
def ActualFamilyMemberReportClaim (n : ℕ) (parity : ℕ → TetrahedralInputParity)
    (hn : 1 ≤ n) (carrierFuel : ℕ) : Prop :=
    let result := normalizeRawMolecule (family n parity)
    let domain := family_normalized_domain n parity hn
    let input := family_normalized_source_input n parity hn
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

/-- Meaningful universal software/source family claim. Every independent domain premise is derived
from the constructor; the quantified positive size and arbitrary parity are physical inputs. -/
def PositiveFamilyClaim : Prop :=
  ∀ (n : ℕ) (parity : ℕ → TetrahedralInputParity) (hn : 1 ≤ n) (carrierFuel : ℕ),
    (family n parity).atomCount = 6 * n + 2 ∧
    (family n parity).bonds.length = 6 * n + 1 ∧
    (normalizeRawMolecule (family n parity)).parsed.StereochemicalAdmissible ∧
    (normalizeRawMolecule (family n parity)).parsed.Rule2MassesKnown ∧
    ZeroHydrogenDemand (family n parity) ∧
    (let branches := normalizedStereoAnalysisBranches (normalizeRawMolecule (family n parity));
      branches.ordinaryDoubleBond = [] ∧ branches.coupledDoubleBond = [] ∧
        branches.oddCumuleneDoubleBond = [] ∧ branches.extendedAxial = []) ∧
    ActualFamilyMemberReportClaim n parity hn carrierFuel

#check ActualFamilyMemberReportClaim
#check PositiveFamilyClaim

private theorem actualFamilyMemberReportClaim_holds (n : ℕ)
    (parity : ℕ → TetrahedralInputParity) (positive : 1 ≤ n) (carrierFuel : ℕ) :
    ActualFamilyMemberReportClaim n parity positive carrierFuel := by
  unfold ActualFamilyMemberReportClaim
  exact positive_family_actual_report_and_source n parity positive carrierFuel

#check actualFamilyMemberReportClaim_holds

theorem positiveFamilyClaim_holds : PositiveFamilyClaim := by
  intro n parity positive carrierFuel
  refine And.intro (family_atomCount n parity) ?_
  refine And.intro ?_ ?_
  · change (familyBonds n).length = 6 * n + 1
    exact familyBonds_length n positive
  refine And.intro (family_normalized_admissible n parity positive) ?_
  refine And.intro (family_normalized_masses n parity) ?_
  refine And.intro (family_zeroHydrogenDemand n parity) ?_
  exact And.intro (positive_family_other_four_segments_nil n parity positive)
    (actualFamilyMemberReportClaim_holds n parity positive carrierFuel)

#check positiveFamilyClaim_holds
#eval IO.eprintln "CompilerExportFamilyClaimBridgeProofs phase: meaningful universal family proof elaborated"



def fixedFamilyPlan : PublicClaimTheoremPlan where
  imports := ["TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge", "TetraStereo.KernelOnly"]
  namespacePath := ["TetraStereo", "Generated", "PositivePendantFamilyCompilerExport"]
  theoremName := "positiveFamilyCorrect"
  statement := "TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.PositiveFamilyClaim"
  proofTerm := "  exact TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.compiledFamilyArtifact_checked\n\nexample : (TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.compiledFamilyArtifact).claim :=\n  positiveFamilyCorrect\n\nassert_kernel_only TetraStereo.Generated.PositivePendantFamilyCompilerExport.positiveFamilyCorrect\nassert_kernel_only TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.positiveFamilyClaim_holds\nassert_kernel_only TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.compiledFamilyArtifact_claim\nassert_kernel_only TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.compiledFamilyArtifact_checked\nassert_kernel_only TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.compiledFamilyArtifact_identity\nassert_kernel_only TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.compiledFamilyArtifact_kind\nassert_kernel_only TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.fixedFamilyPlan_statement\nassert_kernel_only TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.fixedFamilyPlan_proof_reference\nassert_kernel_only TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.familySourceEntry_actual_compiler_source\nassert_kernel_only TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.familySourceEntry_file_source_exact\nassert_kernel_only TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.writeFamilyExport_uses_actual_emitter\nassert_kernel_only TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.writeFamilyExport_emits_exact_module\nassert_kernel_only TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.inhabited_compiler_family_claim"

/-- The REAL production compiler, with its proof input derived internally from the physical family. -/
def compiledFamilyArtifact : LeanCertificateArtifact :=
  compilePublicClaim fixedFamilyPlan .multiCenterRelation
    "Positive-size ordinary-single pendant family: actual report and own source"
    PositiveFamilyClaim positiveFamilyClaim_holds

theorem compiledFamilyArtifact_claim : compiledFamilyArtifact.claim = PositiveFamilyClaim := rfl

theorem compiledFamilyArtifact_checked : compiledFamilyArtifact.claim :=
  compiledFamilyArtifact.checked

theorem compiledFamilyArtifact_identity :
    compiledFamilyArtifact = compilePublicClaim fixedFamilyPlan .multiCenterRelation
      "Positive-size ordinary-single pendant family: actual report and own source"
      PositiveFamilyClaim positiveFamilyClaim_holds := rfl

theorem compiledFamilyArtifact_kind : compiledFamilyArtifact.kind = .stereoClaim := rfl

theorem fixedFamilyPlan_statement : fixedFamilyPlan.statement = "TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.PositiveFamilyClaim" := rfl

theorem fixedFamilyPlan_proof_reference : fixedFamilyPlan.proofTerm = "  exact TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.compiledFamilyArtifact_checked\n\nexample : (TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.compiledFamilyArtifact).claim :=\n  positiveFamilyCorrect\n\nassert_kernel_only TetraStereo.Generated.PositivePendantFamilyCompilerExport.positiveFamilyCorrect\nassert_kernel_only TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.positiveFamilyClaim_holds\nassert_kernel_only TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.compiledFamilyArtifact_claim\nassert_kernel_only TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.compiledFamilyArtifact_checked\nassert_kernel_only TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.compiledFamilyArtifact_identity\nassert_kernel_only TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.compiledFamilyArtifact_kind\nassert_kernel_only TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.fixedFamilyPlan_statement\nassert_kernel_only TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.fixedFamilyPlan_proof_reference\nassert_kernel_only TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.familySourceEntry_actual_compiler_source\nassert_kernel_only TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.familySourceEntry_file_source_exact\nassert_kernel_only TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.writeFamilyExport_uses_actual_emitter\nassert_kernel_only TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.writeFamilyExport_emits_exact_module\nassert_kernel_only TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge.inhabited_compiler_family_claim" := rfl


def publicClaimSourceEntry (plan : PublicClaimTheoremPlan)
    (key description fileName : String) : CertificateSourceEntry where
  key := key
  description := description
  fileName := fileName
  source := plan.toTheoremExport.source

/-- General compiler-to-source bridge. The claim and its proof are actual typed compiler inputs;
there is no caller-supplied source equality or expected outcome premise. -/
theorem publicClaimSourceEntry_source_eq_compiled (plan : PublicClaimTheoremPlan)
    (key description fileName : String) (kind : PublicClaimKind) (title : String)
    (claim : Prop) (checked : claim) :
    (publicClaimSourceEntry plan key description fileName).source =
      (compilePublicClaim plan kind title claim checked).source := rfl

/-- General existing IO writer uses the SAME renderer as the actual production compiler.
This is an equality of IO programs; it neither executes IO nor supplies byte-observation evidence. -/
theorem publicClaimSourceEntry_write_uses_renderer (plan : PublicClaimTheoremPlan)
    (key description fileName outputDirectory : String) :
    (publicClaimSourceEntry plan key description fileName).writeSource outputDirectory = (do
      IO.FS.createDirAll (System.FilePath.mk outputDirectory)
      let path := (publicClaimSourceEntry plan key description fileName).outputPath outputDirectory
      IO.FS.writeFile path (plan.toTheoremExport.source ++ "\n")
      pure path) := rfl

#eval IO.eprintln "CompilerExportFamilyClaimBridgeProofs phase: general compiler renderer and IO bridge elaborated"


def familySourceEntry : CertificateSourceEntry :=
  publicClaimSourceEntry fixedFamilyPlan
    "positive-pendant-family-compiler-export"
    "Universal positive-size actual family report and same-source theorem"
    "CompilerExportFamilyClaimBridgeKernelCertificate.lean"

theorem familySourceEntry_actual_compiler_source :
    familySourceEntry.source = compiledFamilyArtifact.source :=
  publicClaimSourceEntry_source_eq_compiled fixedFamilyPlan
    "positive-pendant-family-compiler-export"
    "Universal positive-size actual family report and same-source theorem"
    "CompilerExportFamilyClaimBridgeKernelCertificate.lean" .multiCenterRelation
    "Positive-size ordinary-single pendant family: actual report and own source"
    PositiveFamilyClaim positiveFamilyClaim_holds

/-- The actual renderer's complete file source. This definition deliberately makes no separate
kernel claim about a giant frozen literal. ROOT must compare actual emitted bytes against the
independent preserved 2170-byte/c4724efd certificate, then kernel-check that emitted alias. -/
def expectedEmittedModule : String := familySourceEntry.fileSource

theorem familySourceEntry_file_source_exact : familySourceEntry.fileSource = expectedEmittedModule := rfl

#check familySourceEntry_file_source_exact
#eval IO.eprintln "CompilerExportFamilyClaimBridgeProofs phase: fixed family renderer bindings elaborated"

/-- Actual existing IO emitter; verification is a separate ROOT bounded gate, never auto-launched. -/
def writeFamilyExport (outputDirectory : String) : IO System.FilePath :=
  familySourceEntry.writeSource outputDirectory

theorem writeFamilyExport_uses_actual_emitter (outputDirectory : String) :
    writeFamilyExport outputDirectory = familySourceEntry.writeSource outputDirectory := rfl

theorem writeFamilyExport_emits_exact_module (outputDirectory : String) :
    writeFamilyExport outputDirectory = (do
      IO.FS.createDirAll (System.FilePath.mk outputDirectory)
      let path := familySourceEntry.outputPath outputDirectory
      IO.FS.writeFile path expectedEmittedModule
      pure path) := by
  exact publicClaimSourceEntry_write_uses_renderer fixedFamilyPlan
    "positive-pendant-family-compiler-export"
    "Universal positive-size actual family report and same-source theorem"
    "CompilerExportFamilyClaimBridgeKernelCertificate.lean" outputDirectory

/-- A REAL compiled artifact carrying the already derived meaningful universal family theorem.
No caller success/output/completed-request premise appears in this compiler boundary. -/
theorem inhabited_compiler_family_claim :
    ∃ artifact : LeanCertificateArtifact, artifact = compiledFamilyArtifact ∧
      artifact.claim = PositiveFamilyClaim ∧ artifact.claim ∧ artifact.source = familySourceEntry.source :=
  ⟨compiledFamilyArtifact, rfl, compiledFamilyArtifact_claim, compiledFamilyArtifact_checked,
    familySourceEntry_actual_compiler_source.symm⟩

#eval IO.eprintln "CompilerExportFamilyClaimBridgeProofs phase: complete compiler source and emitter bridge elaborated"

end TetraStereo.UniversalProof.CompilerExportFamilyClaimBridgeProofs.CompilerExportFamilyClaimBridge
