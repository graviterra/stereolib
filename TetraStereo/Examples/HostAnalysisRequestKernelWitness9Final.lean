import TetraStereo.Examples.HostAnalysisRequestKernelWitness9

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
theorem witness9_identity : witness9.validateIdentityShape = .ok () := by rfl

set_option maxHeartbeats 1000000 in
theorem witness9_readiness : witness9.validateReadinessShape = .ok () := by rfl

theorem witness9_generated : witness9.validateGeneratedShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateGeneratedShape
  simp only [witness9_metadata, witness9_identity, witness9_readiness]
  rfl

set_option maxHeartbeats 1000000 in
theorem witness9_moduleName :
    witness9.moduleName =
      "TetraStereoGenerated.Examples.BroadSurface.Witnesses.HostMoleculeTargetWitness_Reqkhost_x45_analysis_x45_broad_x45_stereochemical_x45_surface_GraphSound_Tgtkgraph_x45_classifier_x45_sound_GraphSoundResult" := by
  rfl

set_option maxHeartbeats 1000000 in
theorem witness9_suite_valid :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.validateWitnessRequestShape witness9 = .ok () := by
  unfold HostAnalysisSuiteRequest.validateWitnessRequestShape
  simp only [witness9_generated]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
