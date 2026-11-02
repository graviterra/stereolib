import TetraStereo.Examples.HostAnalysisRequestKernelWitness14Metadata

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
theorem witness14_identity : witness14.validateIdentityShape = .ok () := by rfl

set_option maxHeartbeats 1000000 in
theorem witness14_readiness : witness14.validateReadinessShape = .ok () := by rfl

theorem witness14_generated : witness14.validateGeneratedShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateGeneratedShape
  simp only [witness14_metadata, witness14_identity, witness14_readiness]
  rfl

set_option maxHeartbeats 1000000 in
theorem witness14_moduleName :
    witness14.moduleName =
      "TetraStereoGenerated.Examples.BroadSurface.Witnesses.HostMoleculeTargetWitness_Reqkhost_x45_analysis_x45_broad_x45_stereochemical_x45_surface_Conf_Tgtkconformer_x45_profile_x45_chiral_ResConfCh_SrcConfIdkLA0NA1NA2NA3NA4NA5NA6NA7NA8NA9NA10NA11" := by
  rfl

set_option maxHeartbeats 1000000 in
theorem witness14_suite_valid :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.validateWitnessRequestShape witness14 = .ok () := by
  unfold HostAnalysisSuiteRequest.validateWitnessRequestShape
  simp only [witness14_generated]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
