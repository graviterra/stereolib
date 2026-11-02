import TetraStereo.Examples.HostAnalysisRequestKernelWitness8

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
theorem witness8_identity : witness8.validateIdentityShape = .ok () := by rfl

set_option maxHeartbeats 1000000 in
theorem witness8_readiness : witness8.validateReadinessShape = .ok () := by rfl

theorem witness8_generated : witness8.validateGeneratedShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateGeneratedShape
  simp only [witness8_metadata, witness8_identity, witness8_readiness]
  rfl

set_option maxHeartbeats 1000000 in
theorem witness8_moduleName :
    witness8.moduleName =
      "TetraStereoGenerated.Examples.BroadSurface.Witnesses.HostMoleculeTargetWitness_Reqkhost_x45_analysis_x45_broad_x45_stereochemical_x45_surface_McGraph_Tgtkmulticenter_x45_relation_GraphExact" := by
  rfl

set_option maxHeartbeats 1000000 in
theorem witness8_suite_valid :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.validateWitnessRequestShape witness8 = .ok () := by
  unfold HostAnalysisSuiteRequest.validateWitnessRequestShape
  simp only [witness8_generated]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
