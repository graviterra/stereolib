import TetraStereo.Examples.HostAnalysisRequestKernelWitness15Metadata

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
theorem witness15_identity : witness15.validateIdentityShape = .ok () := by rfl

set_option maxHeartbeats 1000000 in
theorem witness15_readiness : witness15.validateReadinessShape = .ok () := by rfl

theorem witness15_generated : witness15.validateGeneratedShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateGeneratedShape
  simp only [witness15_metadata, witness15_identity, witness15_readiness]
  rfl

set_option maxHeartbeats 1000000 in
theorem witness15_moduleName :
    witness15.moduleName =
      "TetraStereoGenerated.Examples.BroadSurface.Witnesses.HostMoleculeTargetWitness_Reqkhost_x45_analysis_x45_broad_x45_stereochemical_x45_surface_Ens_Tgtkensemble_x45_descriptor_x45_chiral_ResEnsCh_SrcEnsIdkLA0NA1NA2NA3NA4NA5NA6NA7NA8NA9NA10NA11" := by
  rfl

set_option maxHeartbeats 1000000 in
theorem witness15_suite_valid :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.validateWitnessRequestShape witness15 = .ok () := by
  unfold HostAnalysisSuiteRequest.validateWitnessRequestShape
  simp only [witness15_generated]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
