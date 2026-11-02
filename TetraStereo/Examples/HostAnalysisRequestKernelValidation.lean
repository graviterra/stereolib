import TetraStereo.Examples.HostAnalysisRequestKernelOfficial
import TetraStereo.Examples.HostAnalysisRequestKernelClaims
import TetraStereo.Examples.HostAnalysisRequestKernelWitnesses
import TetraStereo.Examples.HostAnalysisRequestKernelGlobal

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

open TetraStereo.Engine
open TetraStereo.Examples.HostAnalysisRequestBuilder

noncomputable section

theorem suite_validation_decompose (request : HostAnalysisSuiteRequest) :
    request.validateGeneratedShape = (do
      request.validateHeaderShape
      request.validateOfficialRequestShapes
      request.validateClaimRequestShapes
      request.validateWitnessRequestShapes
      request.validateGlobalNameShape) := by
  rfl

theorem broadSurface_suite_valid :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.validateGeneratedShape = .ok () := by
  rw [suite_validation_decompose]
  simp only [show broadSurfaceMoleculeAnalysisRequest.suiteRequest.validateHeaderShape = .ok () by
      rfl,
    broadSurface_validateOfficialRequestShapes, broadSurface_validateClaimRequestShapes,
    broadSurface_witness_shapes, broadSurface_validateGlobalNameShape]
  rfl

set_option maxHeartbeats 1000000 in
theorem broadSurface_request_valid :
    broadSurfaceMoleculeAnalysisRequest.validateGeneratedShape = .ok () := by
  unfold HostMoleculeAnalysisRequest.validateGeneratedShape
  rw [broadSurface_suite_valid]
  rfl

end
end TetraStereo.Examples.HostAnalysisRequestKernelProof
