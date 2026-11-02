import TetraStereo.Examples.HostAnalysisRequestKernelWitness0

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
theorem witness0_identity : witness0.validateIdentityShape = .ok () := by rfl

set_option maxHeartbeats 1000000 in
theorem witness0_readiness : witness0.validateReadinessShape = .ok () := by rfl

theorem witness0_generated : witness0.validateGeneratedShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateGeneratedShape
  simp only [witness0_metadata, witness0_identity, witness0_readiness]
  rfl

set_option maxHeartbeats 1000000 in
theorem witness0_moduleName :
    witness0.moduleName =
      "TetraStereoGenerated.Examples.BroadSurface.Witnesses.HostMoleculeTargetWitness_Reqkhost_x45_analysis_x45_broad_x45_stereochemical_x45_surface_Ax_Tgtkaxial_x45_unit_ResAxRa_SrcAxLA5NA7NA1NA2NA3NA4" := by
  rfl

set_option maxHeartbeats 1000000 in
theorem witness0_suite_valid :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.validateWitnessRequestShape witness0 = .ok () := by
  unfold HostAnalysisSuiteRequest.validateWitnessRequestShape
  simp only [witness0_generated]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
