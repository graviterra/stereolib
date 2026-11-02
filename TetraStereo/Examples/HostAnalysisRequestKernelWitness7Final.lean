import TetraStereo.Examples.HostAnalysisRequestKernelWitness7

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
theorem witness7_identity : witness7.validateIdentityShape = .ok () := by rfl

set_option maxHeartbeats 1000000 in
theorem witness7_readiness : witness7.validateReadinessShape = .ok () := by rfl

theorem witness7_generated : witness7.validateGeneratedShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateGeneratedShape
  simp only [witness7_metadata, witness7_identity, witness7_readiness]
  rfl

set_option maxHeartbeats 1000000 in
theorem witness7_moduleName :
    witness7.moduleName =
      "TetraStereoGenerated.Examples.BroadSurface.Witnesses.HostMoleculeTargetWitness_Reqkhost_x45_analysis_x45_broad_x45_stereochemical_x45_surface_Lp_Tgtklone_x45_pair_x45_node" := by
  rfl

set_option maxHeartbeats 1000000 in
theorem witness7_suite_valid :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.validateWitnessRequestShape witness7 = .ok () := by
  unfold HostAnalysisSuiteRequest.validateWitnessRequestShape
  simp only [witness7_generated]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
