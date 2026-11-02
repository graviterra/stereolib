import TetraStereo.Examples.HostAnalysisRequestKernelWitness12Metadata

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
theorem witness12_identity : witness12.validateIdentityShape = .ok () := by rfl

set_option maxHeartbeats 1000000 in
theorem witness12_readiness : witness12.validateReadinessShape = .ok () := by rfl

theorem witness12_generated : witness12.validateGeneratedShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateGeneratedShape
  simp only [witness12_metadata, witness12_identity, witness12_readiness]
  rfl

set_option maxHeartbeats 1000000 in
theorem witness12_moduleName :
    witness12.moduleName =
      "TetraStereoGenerated.Examples.BroadSurface.Witnesses.HostMoleculeTargetWitness_Reqkhost_x45_analysis_x45_broad_x45_stereochemical_x45_surface_GraphSound_Tgtkgraph_x45_classifier_x45_mirror_x45_chiral_x45_enantiomeric_GraphSoundResult_Mirror_IfChiral_Enantiomeric" := by
  rfl

set_option maxHeartbeats 1000000 in
theorem witness12_suite_valid :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.validateWitnessRequestShape witness12 = .ok () := by
  unfold HostAnalysisSuiteRequest.validateWitnessRequestShape
  simp only [witness12_generated]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
