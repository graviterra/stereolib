import TetraStereo.Examples.HostAnalysisRequestKernelFixture

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
theorem broadSurface_validateOfficialRequestShapes :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.validateOfficialRequestShapes = .ok () := by
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
