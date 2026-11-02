import TetraStereo.Examples.HostAnalysisRequestKernelWitness3

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
theorem witness3_identity : witness3.validateIdentityShape = .ok () := by rfl

set_option maxHeartbeats 1000000 in
theorem witness3_readiness : witness3.validateReadinessShape = .ok () := by rfl

theorem witness3_generated : witness3.validateGeneratedShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateGeneratedShape
  simp only [witness3_metadata, witness3_identity, witness3_readiness]
  rfl

set_option maxHeartbeats 1000000 in
theorem witness3_moduleName :
    witness3.moduleName =
      "TetraStereoGenerated.Examples.BroadSurface.Witnesses.HostMoleculeTargetWitness_Reqkhost_x45_analysis_x45_broad_x45_stereochemical_x45_surface_Db_Tgtkalkene_x45_unit_ResDbZ_SrcDbLA8NA9" := by
  rfl

set_option maxHeartbeats 1000000 in
theorem witness3_suite_valid :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.validateWitnessRequestShape witness3 = .ok () := by
  unfold HostAnalysisSuiteRequest.validateWitnessRequestShape
  simp only [witness3_generated]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
