import TetraStereo.Examples.HostAnalysisRequestKernelWitness1

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
theorem witness1_identity : witness1.validateIdentityShape = .ok () := by rfl

set_option maxHeartbeats 1000000 in
theorem witness1_readiness : witness1.validateReadinessShape = .ok () := by rfl

theorem witness1_generated : witness1.validateGeneratedShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateGeneratedShape
  simp only [witness1_metadata, witness1_identity, witness1_readiness]
  rfl

set_option maxHeartbeats 1000000 in
theorem witness1_moduleName :
    witness1.moduleName =
      "TetraStereoGenerated.Examples.BroadSurface.Witnesses.HostMoleculeTargetWitness_Reqkhost_x45_analysis_x45_broad_x45_stereochemical_x45_surface_Pl_Tgtkplanar_x45_unit_ResPlRp_SrcPlLA1NA2NA3NA1NA2NA3" := by
  rfl

set_option maxHeartbeats 1000000 in
theorem witness1_suite_valid :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.validateWitnessRequestShape witness1 = .ok () := by
  unfold HostAnalysisSuiteRequest.validateWitnessRequestShape
  simp only [witness1_generated]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
