import TetraStereo.Examples.HostAnalysisRequestKernelWitness10

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
theorem witness10_identity : witness10.validateIdentityShape = .ok () := by rfl

set_option maxHeartbeats 1000000 in
theorem witness10_readiness : witness10.validateReadinessShape = .ok () := by rfl

theorem witness10_generated : witness10.validateGeneratedShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateGeneratedShape
  simp only [witness10_metadata, witness10_identity, witness10_readiness]
  rfl

set_option maxHeartbeats 1000000 in
theorem witness10_moduleName :
    witness10.moduleName =
      "TetraStereoGenerated.Examples.BroadSurface.Witnesses.HostMoleculeTargetWitness_Reqkhost_x45_analysis_x45_broad_x45_stereochemical_x45_surface_GraphSound_Tgtkgraph_x45_classifier_x45_self_x45_same_GraphSoundResult_Self_Same" := by
  rfl

set_option maxHeartbeats 1000000 in
theorem witness10_suite_valid :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.validateWitnessRequestShape witness10 = .ok () := by
  unfold HostAnalysisSuiteRequest.validateWitnessRequestShape
  simp only [witness10_generated]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
