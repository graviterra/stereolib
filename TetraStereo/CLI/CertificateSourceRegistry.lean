/-
  Dependency-pruned executable certificate source registry.

  This is the drop-in replacement for `TetraStereo/CLI/CertificateSourceRegistry.lean`.  The only
  semantic change is the import of the two fixture *definitions* that this module actually uses:

  * before: `import TetraStereo.Examples.HostAnalysisRequestBuilder`
    (which, through `HostAnalysisRequestKernelValidation`, imported the whole
    `HostAnalysisRequestKernel*` witness/collision/global proof family, including
    `HostAnalysisRequestKernelWitness10`);
  * after:  `import TetraStereo.Examples.HostAnalysisRequestBuilderFixtures` (the two data
    definitions moved out unchanged) plus
    `import TetraStereo.Examples.HostAnalysisRequestKernelFixture` (the light broad-surface
    fixture module where `broadSurfaceMoleculeAnalysisRequest` is actually defined).

  Every declaration below is byte-for-byte the original declaration: same name, same type, same
  value, same registry order.  `publicDemoCertificateSources` still has sixteen entries, with the
  checked `auto-bridge-official-stereo-checked` entry at index 14 and the real `CCl4` refusal at
  index 15, so `TetraStereo.Examples.OfficialStereoGeneratedCertificateValidation` keeps every one
  of its `rfl` source equalities and checked-artifact proofs unchanged.

  The `assert_kernel_only` commands at the end are the project-wide kernel-authority guard for
  exported theorems (the original module carried no such guards).
-/

import TetraStereo.Engine.OfficialStereoBuilder
import TetraStereo.Engine.HostAnalysisRequestBuilder
import TetraStereo.Engine.HostAnalysisSuiteCompiler
import TetraStereo.Engine.HostClaimCompiler
import TetraStereo.Examples.HostClaimCompiler
import TetraStereo.Examples.HostAnalysisRequestBuilderFixtures
import TetraStereo.Examples.HostAnalysisRequestKernelFixture
import TetraStereo.Examples.HostAnalysisSuiteCompiler
import TetraStereo.Examples.HostModuleCompiler
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace CLI
namespace CertificateSourceRegistry

open Engine
open OneCenter

/-- Shared namespace for generated public demo certificate files. -/
def generatedNamespace : List String :=
  ["TetraStereo", "Examples", "GeneratedCertificates"]

/-- Render a standalone wrapper theorem for a checked artifact claim. -/
def artifactClaimSource (imports : List String) (theoremName artifactExpr proofExpr : String) :
    String :=
  ({ imports := imports
     namespacePath := generatedNamespace
     theoremName := theoremName
     statement := artifactExpr ++ ".claim"
     proofTerm := "  exact " ++ proofExpr } : LeanTheoremExport).source

/-- Build a source-registry entry for a public demo certificate artifact. -/
def artifactEntry (key description fileName moduleName theoremName artifactExpr proofExpr : String) :
    CertificateSourceEntry where
  key := key
  description := description
  fileName := fileName
  source := artifactClaimSource [moduleName] theoremName artifactExpr proofExpr

/-- Generated source entry for the preserved original `C(F)(O)(N)Cl` example.

The active metadata names the checked prepared transaction, not a refusal.  The rendered source is
the generic checked host-query theorem for the actual `autoBridgeQuery`; it never mentions the
retired refusal claim. -/
def autoBridgeCheckedSourceEntry : CertificateSourceEntry :=
  (({ key := "auto-bridge-official-stereo-checked"
      description := "auto-built official-stereo prepared transaction from checked intake"
      fileName := "AutoBridgeOfficialStereoChecked.lean"
      imports := ["TetraStereo.Examples.OfficialStereoBuilder"]
      namespacePath := generatedNamespace
      theoremName := "auto_bridge_official_stereo_checked"
      requestExpr := "TetraStereo.Examples.OfficialStereoBuilder.autoBridgeRequest"
      proofTerm :=
        "  exact TetraStereo.Examples.OfficialStereoBuilder.autoBridgePrepared_checked" } :
     OfficialStereoExportSpec).hostQuerySourceSpec
    "TetraStereo.Examples.OfficialStereoBuilder.autoBridgeQuery"
    "TetraStereo.Examples.OfficialStereoBuilder.autoBridgeHostQueryBuilds"
    "auto_bridge_official_stereo_query_checked").sourceEntry

/-- Executable source registry for the standalone certificate exporter. -/
def publicDemoCertificateSources : List CertificateSourceEntry :=
  [ artifactEntry
      "import-methane"
      "checked raw methane import-normalization certificate"
      "MethaneImportCertificate.lean"
      "TetraStereo.Examples.CertificateExport"
      "methane_import_artifact_checked"
      "TetraStereo.Examples.CertificateExport.methaneImportArtifact"
      "TetraStereo.Examples.CertificateExport.methaneImportArtifact_checked"
  , artifactEntry
      "trace-1-phenylethanol-phenyl-vs-methyl"
      "checked CIP trace outcome for 1-phenylethanol phenyl vs methyl"
      "OnePhenylethanolPhenylMethylTrace.lean"
      "TetraStereo.Examples.CertificateExport"
      "one_phenylethanol_methyl_phenyl_artifact_checked"
      "TetraStereo.Examples.CertificateExport.onePhenylethanolMethylPhenylArtifact"
      "TetraStereo.Examples.CertificateExport.onePhenylethanolMethylPhenylArtifact_checked"
  , artifactEntry
      "rs-1-phenylethanol-right"
      "checked safe public S assignment for right-handed 1-phenylethanol"
      "OnePhenylethanolRightRS.lean"
      "TetraStereo.Examples.CertificateExport"
      "one_phenylethanol_right_rs_artifact_checked"
      "TetraStereo.Examples.CertificateExport.onePhenylethanolRightRSArtifact"
      "TetraStereo.Examples.CertificateExport.onePhenylethanolRightRSArtifact_checked"
  , artifactEntry
      "engine-1-phenylethanol-right"
      "checked public engine transaction for right-handed 1-phenylethanol"
      "OnePhenylethanolEngineRightRS.lean"
      "TetraStereo.Examples.EngineTransaction"
      "one_phenylethanol_engine_artifact_checked"
      "TetraStereo.Examples.EngineTransaction.onePhenylethanolEngineCertified.artifact"
      "TetraStereo.Examples.EngineTransaction.onePhenylethanolEngineDemo_checked"
  , artifactEntry
      "engine-methane-refusal"
      "checked public engine refusal for methane tied priorities"
      "MethaneEngineRefusal.lean"
      "TetraStereo.Examples.EngineRefusal"
      "methane_engine_refusal_artifact_checked"
      "TetraStereo.Examples.EngineRefusal.methaneEngineCertifiedRefusal.artifact"
      "TetraStereo.Examples.EngineRefusal.methaneEngineRefusal_checked"
  , artifactEntry
      "claim-official-cip"
      "checked broad public official-CIP claim transaction"
      "OfficialCIPClaim.lean"
      "TetraStereo.Examples.EngineClaims"
      "official_cip_claim_artifact_checked"
      "TetraStereo.Examples.EngineClaims.officialCIPClaimCertificate.artifact"
      "TetraStereo.Examples.EngineClaims.officialCIPClaimCertificate_checked"
  , artifactEntry
      "claim-multicenter-relation"
      "checked broad public multi-center relation claim transaction"
      "MultiCenterRelationClaim.lean"
      "TetraStereo.Examples.EngineClaims"
      "multi_center_relation_claim_artifact_checked"
      "TetraStereo.Examples.EngineClaims.multiCenterRelationClaimCertificate.artifact"
      "TetraStereo.Examples.EngineClaims.multiCenterRelationClaimCertificate_checked"
  , artifactEntry
      "claim-ensemble"
      "checked broad public ensemble stereochemistry claim transaction"
      "EnsembleClaim.lean"
      "TetraStereo.Examples.EngineClaims"
      "ensemble_claim_artifact_checked"
      "TetraStereo.Examples.EngineClaims.ensembleClaimCertificate.artifact"
      "TetraStereo.Examples.EngineClaims.ensembleClaimCertificate_checked"
  , artifactEntry
      "official-stereo-helical"
      "checked detector-backed helical M/P official-stereo transaction"
      "OfficialStereoHelical.lean"
      "TetraStereo.Examples.OfficialStereoTransaction"
      "official_stereo_helical_artifact_checked"
      "TetraStereo.Examples.OfficialStereoTransaction.helicalBranchCertificate.artifact"
      "TetraStereo.Examples.OfficialStereoTransaction.helicalBranchCertificate_checked"
  , artifactEntry
      "official-stereo-graph-key"
      "checked detector-free oxygen-before-carbon graph-key transaction"
      "OfficialStereoGraphKey.lean"
      "TetraStereo.Examples.OfficialStereoTransaction"
      "official_stereo_graph_key_artifact_checked"
      "TetraStereo.Examples.OfficialStereoTransaction.graphKeyCertificate.artifact"
      "TetraStereo.Examples.OfficialStereoTransaction.graphKeyCertificate_checked"
  , artifactEntry
      "official-stereo-default-fuel"
      "checked default-fuel official graph-key transaction"
      "OfficialStereoDefaultFuel.lean"
      "TetraStereo.Examples.OfficialStereoTransaction"
      "official_stereo_default_fuel_artifact_checked"
      "TetraStereo.Examples.OfficialStereoTransaction.graphKeyDefaultFuelCertificate.artifact"
      "TetraStereo.Examples.OfficialStereoTransaction.graphKeyDefaultFuelCertificate_checked"
  , artifactEntry
      "official-stereo-multiple-bond"
      "checked multiple-bond duplicate-node official-stereo transaction"
      "OfficialStereoMultipleBond.lean"
      "TetraStereo.Examples.OfficialStereoTransaction"
      "official_stereo_multiple_bond_artifact_checked"
      "TetraStereo.Examples.OfficialStereoTransaction.multipleBondCertificate.artifact"
      "TetraStereo.Examples.OfficialStereoTransaction.multipleBondCertificate_checked"
  , artifactEntry
      "official-stereo-virtual-auxiliary"
      "checked virtual auxiliary-node official-stereo transaction"
      "OfficialStereoVirtualAuxiliary.lean"
      "TetraStereo.Examples.OfficialStereoTransaction"
      "official_stereo_virtual_auxiliary_artifact_checked"
      "TetraStereo.Examples.OfficialStereoTransaction.virtualAuxiliaryCertificate.artifact"
      "TetraStereo.Examples.OfficialStereoTransaction.virtualAuxiliaryCertificate_checked"
  , artifactEntry
      "official-stereo-empty-refusal"
      "checked official-stereo refusal for unresolved detector/graph priorities"
      "OfficialStereoEmptyRefusal.lean"
      "TetraStereo.Examples.OfficialStereoTransaction"
      "official_stereo_empty_refusal_artifact_checked"
      "TetraStereo.Examples.OfficialStereoTransaction.emptyDetectorRefusal.artifact"
      "TetraStereo.Examples.OfficialStereoTransaction.emptyDetectorRefusal_checked"
  , autoBridgeCheckedSourceEntry
  , artifactEntry
      "ccl4-official-stereo-refusal"
      "checked actual CCl4 automatic-builder refusal from checked intake"
      "CCl4OfficialStereoRefusal.lean"
      "TetraStereo.Examples.OfficialStereoBuilder"
      "ccl4_official_stereo_refusal_artifact_checked"
      "TetraStereo.Examples.OfficialStereoBuilder.ccl4Refusal.artifact"
      "TetraStereo.Examples.OfficialStereoBuilder.ccl4Refusal_checked"
  ]

/-- The executable registry mirrors the public demo artifact set. -/
theorem publicDemoCertificateSources_length :
    publicDemoCertificateSources.length = 16 :=
  rfl

/-- The generated entry for the preserved original example uses the checked key. -/
theorem autoBridgeCheckedSourceEntry_key :
    autoBridgeCheckedSourceEntry.key = "auto-bridge-official-stereo-checked" :=
  rfl

/-- The generated entry for the preserved original example uses the checked file name. -/
theorem autoBridgeCheckedSourceEntry_fileName :
    autoBridgeCheckedSourceEntry.fileName = "AutoBridgeOfficialStereoChecked.lean" :=
  rfl

/-- Executable source registry for generated host Lean modules. -/
def publicDemoHostModuleSources : List CertificateSourceEntry :=
  [ TetraStereo.Examples.HostModuleCompiler.compiledAutoBridgeHostModuleEntry
  , TetraStereo.Examples.HostModuleCompiler.compiledHelicalBridgeHostModuleEntry
  ]

/-- The generated-host-module registry currently contains two compiled host-module fixtures. -/
theorem publicDemoHostModuleSources_length :
    publicDemoHostModuleSources.length = 2 :=
  rfl

/-- Structured host requests that can be written as two-stage certificate packages. -/
def publicDemoHostRequests : List HostOfficialStereoRequest :=
  [ TetraStereo.Examples.HostModuleCompiler.compiledAutoBridgeHostRequest
  , TetraStereo.Examples.HostModuleCompiler.compiledHelicalBridgeHostRequest
  ]

/-- Find a structured host request by host-facing certificate key. -/
def findHostRequest? (key : String) : Option HostOfficialStereoRequest :=
  publicDemoHostRequests.find? fun request => request.key == key

/-- The host-request registry currently contains two compiled host-request fixtures. -/
theorem publicDemoHostRequests_length :
    publicDemoHostRequests.length = 2 :=
  rfl

/-- Structured broad host claim requests that can be written as generated theorem packages. -/
def publicDemoHostClaimRequests : List HostStereoClaimRequest :=
  TetraStereo.Examples.HostClaimCompiler.hostStereoClaimRequests

/-- Find a broad host claim request by host-facing key. -/
def findHostClaimRequest? (key : String) : Option HostStereoClaimRequest :=
  publicDemoHostClaimRequests.find? fun request => request.key == key

/-- The broad host-claim registry currently contains seven theorem-family fixtures. -/
theorem publicDemoHostClaimRequests_length :
    publicDemoHostClaimRequests.length = 7 :=
  rfl

/-- Structured host analysis suites that bundle molecule-shaped packages and broad claims. -/
def publicDemoHostAnalysisSuites : List HostAnalysisSuiteRequest :=
  [ TetraStereo.Examples.HostAnalysisSuiteCompiler.helicalBridgeFullSuiteRequest
  , TetraStereo.Examples.HostAnalysisRequestBuilder.helicalBridgeMoleculeAnalysisRequest.suiteRequest
  , TetraStereo.Examples.HostAnalysisRequestBuilder.broadSurfaceMoleculeAnalysisRequest.suiteRequest
  ]

/-- Find a generated host analysis suite by host-facing key. -/
def findHostAnalysisSuite? (key : String) : Option HostAnalysisSuiteRequest :=
  publicDemoHostAnalysisSuites.find? fun request => request.key == key

/-- The host analysis-suite registry currently contains three full bundle fixtures. -/
theorem publicDemoHostAnalysisSuites_length :
    publicDemoHostAnalysisSuites.length = 3 :=
  rfl

/-- Structured molecule-analysis requests that derive generated suites automatically. -/
def publicDemoHostMoleculeAnalysisRequests : List HostMoleculeAnalysisRequest :=
  [ TetraStereo.Examples.HostAnalysisRequestBuilder.helicalBridgeMoleculeAnalysisRequest
  , TetraStereo.Examples.HostAnalysisRequestBuilder.broadSurfaceMoleculeAnalysisRequest
  ]

/-- Find a molecule-analysis request by host-facing key. -/
def findHostMoleculeAnalysisRequest? (key : String) :
    Option HostMoleculeAnalysisRequest :=
  publicDemoHostMoleculeAnalysisRequests.find? fun request => request.key == key

/-- The molecule-analysis registry currently contains two derived-suite fixtures. -/
theorem publicDemoHostMoleculeAnalysisRequests_length :
    publicDemoHostMoleculeAnalysisRequests.length = 2 :=
  rfl

/-! ## Kernel-authority guards

Every exported theorem of this registry is closed by kernel reduction, so each one must pass the
project-wide kernel-only check. -/

assert_kernel_only publicDemoCertificateSources_length
assert_kernel_only autoBridgeCheckedSourceEntry_key
assert_kernel_only autoBridgeCheckedSourceEntry_fileName
assert_kernel_only publicDemoHostModuleSources_length
assert_kernel_only publicDemoHostRequests_length
assert_kernel_only publicDemoHostClaimRequests_length
assert_kernel_only publicDemoHostAnalysisSuites_length
assert_kernel_only publicDemoHostMoleculeAnalysisRequests_length

end CertificateSourceRegistry
end CLI
end TetraStereo
