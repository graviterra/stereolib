import TetraStereo.Examples.HostAnalysisRequestKernelWitness5Metadata

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
theorem witness5_identity : witness5.validateIdentityShape = .ok () := by rfl

set_option maxHeartbeats 1000000 in
theorem witness5_readiness : witness5.validateReadinessShape = .ok () := by rfl

theorem witness5_generated : witness5.validateGeneratedShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateGeneratedShape
  simp only [witness5_metadata, witness5_identity, witness5_readiness]
  rfl

set_option maxHeartbeats 1000000 in
theorem witness5_moduleName :
    witness5.moduleName =
      "TetraStereoGenerated.Examples.BroadSurface.Witnesses.HostMoleculeTargetWitness_Reqkhost_x45_analysis_x45_broad_x45_stereochemical_x45_surface_Aux_Tgtkauxiliary_x45_rule5_x45_node_ResAuxDkauxiliary_x45_tetrahedral_x45_center_x45_senior_SrcAuxLA1NA0R0" := by
  rfl

set_option maxHeartbeats 1000000 in
theorem witness5_suite_valid :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.validateWitnessRequestShape witness5 = .ok () := by
  unfold HostAnalysisSuiteRequest.validateWitnessRequestShape
  simp only [witness5_generated]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
