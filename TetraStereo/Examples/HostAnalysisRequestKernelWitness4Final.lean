import TetraStereo.Examples.HostAnalysisRequestKernelWitness4

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
theorem witness4_identity : witness4.validateIdentityShape = .ok () := by rfl

set_option maxHeartbeats 1000000 in
theorem witness4_readiness : witness4.validateReadinessShape = .ok () := by rfl

theorem witness4_generated : witness4.validateGeneratedShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateGeneratedShape
  simp only [witness4_metadata, witness4_identity, witness4_readiness]
  rfl

set_option maxHeartbeats 1000000 in
theorem witness4_moduleName :
    witness4.moduleName =
      "TetraStereoGenerated.Examples.BroadSurface.Witnesses.HostMoleculeTargetWitness_Reqkhost_x45_analysis_x45_broad_x45_stereochemical_x45_surface_Cu_Tgtkcumulene_x45_unit" := by
  rfl

set_option maxHeartbeats 1000000 in
theorem witness4_suite_valid :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.validateWitnessRequestShape witness4 = .ok () := by
  unfold HostAnalysisSuiteRequest.validateWitnessRequestShape
  simp only [witness4_generated]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
