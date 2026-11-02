import TetraStereo.Examples.HostAnalysisRequestKernelWitness6

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
theorem witness6_identity : witness6.validateIdentityShape = .ok () := by rfl

set_option maxHeartbeats 1000000 in
theorem witness6_readiness : witness6.validateReadinessShape = .ok () := by rfl

theorem witness6_generated : witness6.validateGeneratedShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateGeneratedShape
  simp only [witness6_metadata, witness6_identity, witness6_readiness]
  rfl

set_option maxHeartbeats 1000000 in
theorem witness6_moduleName :
    witness6.moduleName =
      "TetraStereoGenerated.Examples.BroadSurface.Witnesses.HostMoleculeTargetWitness_Reqkhost_x45_analysis_x45_broad_x45_stereochemical_x45_surface_Ph_Tgtkphantom_x45_node" := by
  rfl

set_option maxHeartbeats 1000000 in
theorem witness6_suite_valid :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.validateWitnessRequestShape witness6 = .ok () := by
  unfold HostAnalysisSuiteRequest.validateWitnessRequestShape
  simp only [witness6_generated]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
