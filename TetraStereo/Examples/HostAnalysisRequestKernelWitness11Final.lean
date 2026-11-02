import TetraStereo.Examples.HostAnalysisRequestKernelWitness11Metadata

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo
namespace Examples
namespace HostAnalysisRequestKernelProof

open Engine
open OneCenter
open HostAnalysisRequestBuilder

noncomputable section

set_option maxHeartbeats 1000000 in
theorem witness11_identity : witness11.validateIdentityShape = .ok () := by rfl

set_option maxHeartbeats 1000000 in
theorem witness11_readiness : witness11.validateReadinessShape = .ok () := by rfl

theorem witness11_generated : witness11.validateGeneratedShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateGeneratedShape
  simp only [witness11_metadata, witness11_identity, witness11_readiness]
  rfl

set_option maxHeartbeats 1000000 in
theorem witness11_moduleName :
    witness11.moduleName =
      "TetraStereoGenerated.Examples.BroadSurface.Witnesses.HostMoleculeTargetWitness_Reqkhost_x45_analysis_x45_broad_x45_stereochemical_x45_surface_GraphSound_Tgtkgraph_x45_classifier_x45_mirror_x45_meso_x45_same_GraphSoundResult_Mirror_IfMeso_Same" := by
  rfl

set_option maxHeartbeats 1000000 in
theorem witness11_suite_valid :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.validateWitnessRequestShape witness11 = .ok () := by
  unfold HostAnalysisSuiteRequest.validateWitnessRequestShape
  simp only [witness11_generated]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
