import TetraStereo.Examples.HostAnalysisRequestKernelFixture

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

open TetraStereo.Engine
open TetraStereo.Examples.HostAnalysisRequestBuilder

noncomputable section

set_option maxHeartbeats 500000 in
theorem broadSurface_validateUniqueOfficialHostModules :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.validateUniqueOfficialHostModules = .ok () := by
  rfl

end
end TetraStereo.Examples.HostAnalysisRequestKernelProof
