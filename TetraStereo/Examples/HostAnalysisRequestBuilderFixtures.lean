/-
  Definition-only split of `TetraStereo.Examples.HostAnalysisRequestBuilder`.

  The original module mixes two kinds of content:

  * pure fixture definitions (`host` request data, molecules, annotations), and
  * large executable-validation proofs that import the whole
    `TetraStereo.Examples.HostAnalysisRequestKernel*` family.

  `TetraStereo.CLI.CertificateSourceRegistry` needs only the *definitions*
  `helicalBridgeOfficialStereoTarget` and `helicalBridgeMoleculeAnalysisRequest` to build
  `publicDemoHostAnalysisSuites` and `publicDemoHostMoleculeAnalysisRequests`.  Importing the
  mixed module for two data definitions transitively pulled
  `HostAnalysisRequestKernelValidation -> HostAnalysisRequestKernelWitnesses ->
  HostAnalysisRequestKernelWitness10Final -> HostAnalysisRequestKernelWitness10` (and the other
  fifteen witness finals) into the certificate-source validation build.

  This module carries exactly those two definitions, unchanged in name (namespace
  `TetraStereo.Examples.HostAnalysisRequestBuilder`) and unchanged in value.  It imports only the
  engine request builder and the light example host-module compiler; it does not import any
  `HostAnalysisRequestKernel*` proof module.

  The broad-surface fixture needed by the same registry already lives in the light module
  `TetraStereo.Examples.HostAnalysisRequestKernelFixture`; it is deliberately not duplicated here.
-/

import TetraStereo.Engine.HostAnalysisRequestBuilder
import TetraStereo.Examples.HostModuleCompiler

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo
namespace Examples
namespace HostAnalysisRequestBuilder

open Engine
open OneCenter

noncomputable section

/-- Molecule-derived helical branch comparison requested from a shared host packet. -/
def helicalBridgeOfficialStereoTarget : HostOfficialStereoAnalysisTarget where
  keySuffix := "helical-official-stereo"
  description := "typed helical branch comparison"
  definitionPrefix := "helicalBridgeMoleculeAnalysis"
  centerAtom := 0
  left := 0
  right := 1
  target := HostOfficialStereoCertificateTarget.computedComparison

/-- Full molecule-derived analysis request for the typed helical bridge demo. -/
def helicalBridgeMoleculeAnalysisRequest : HostMoleculeAnalysisRequest where
  key := "host-analysis-helical-plus-broad-claims"
  description := "molecule-derived helical bridge analysis plus broad Stereolib claim bundle"
  packet :=
    rawMoleculePacket
      TetraStereo.Examples.HostModuleCompiler.compiledHelicalBridgeRaw
      ChemistryImportTrust.proofCertifiedAdapter
  annotations :=
    TetraStereo.Examples.HostModuleCompiler.compiledHelicalBridgeAnnotations
  officialStereoTargets := [helicalBridgeOfficialStereoTarget]
  broadClaimPolicy := HostBroadClaimPolicy.all
  moduleNamespaceBase := ["TetraStereoGenerated", "Examples", "HostAnalyses", "Modules"]
  certificateNamespaceBase := ["TetraStereoGenerated", "Examples", "HostAnalyses", "Certificates"]
  claimNamespacePath := ["TetraStereoGenerated", "Examples", "HostAnalyses", "Claims"]
  suiteNamespacePath := ["TetraStereoGenerated", "Examples", "HostAnalyses", "Suites"]
  suiteFileName := "HelicalBridgeMoleculeAnalysisSuite.lean"
  suiteTheoremName := "helical_bridge_molecule_analysis_suite_checked"

end

end HostAnalysisRequestBuilder
end Examples
end TetraStereo
