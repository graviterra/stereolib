import TetraStereo.Examples.HostAnalysisRequestKernelWitness13Metadata

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
theorem witness13_identity : witness13.validateIdentityShape = .ok () := by rfl

set_option maxHeartbeats 1000000 in
theorem witness13_readiness : witness13.validateReadinessShape = .ok () := by rfl

theorem witness13_generated : witness13.validateGeneratedShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateGeneratedShape
  simp only [witness13_metadata, witness13_identity, witness13_readiness]
  rfl

set_option maxHeartbeats 1000000 in
theorem witness13_moduleName :
    witness13.moduleName =
      "TetraStereoGenerated.Examples.BroadSurface.Witnesses.HostMoleculeTargetWitness_Reqkhost_x45_analysis_x45_broad_x45_stereochemical_x45_surface_GraphRefuse_Tgtkgraph_x45_classifier_x45_refusal_GraphRefusalResult" := by
  rfl

set_option maxHeartbeats 1000000 in
theorem witness13_suite_valid :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.validateWitnessRequestShape witness13 = .ok () := by
  unfold HostAnalysisSuiteRequest.validateWitnessRequestShape
  simp only [witness13_generated]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
