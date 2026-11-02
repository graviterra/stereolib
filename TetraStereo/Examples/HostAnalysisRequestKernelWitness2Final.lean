import TetraStereo.Examples.HostAnalysisRequestKernelWitness2

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
theorem witness2_identity : witness2.validateIdentityShape = .ok () := by rfl

set_option maxHeartbeats 1000000 in
theorem witness2_readiness : witness2.validateReadinessShape = .ok () := by rfl

theorem witness2_generated : witness2.validateGeneratedShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateGeneratedShape
  simp only [witness2_metadata, witness2_identity, witness2_readiness]
  rfl

set_option maxHeartbeats 1000000 in
theorem witness2_moduleName :
    witness2.moduleName =
      "TetraStereoGenerated.Examples.BroadSurface.Witnesses.HostMoleculeTargetWitness_Reqkhost_x45_analysis_x45_broad_x45_stereochemical_x45_surface_He_Tgtkhelical_x45_unit_ResHeM_SrcHeLA1NA0NA2NA1NA2" := by
  rfl

set_option maxHeartbeats 1000000 in
theorem witness2_suite_valid :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.validateWitnessRequestShape witness2 = .ok () := by
  unfold HostAnalysisSuiteRequest.validateWitnessRequestShape
  simp only [witness2_generated]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
