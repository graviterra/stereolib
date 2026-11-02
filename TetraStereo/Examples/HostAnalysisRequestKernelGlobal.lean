import TetraStereo.Examples.HostAnalysisRequestKernelGlobalModules
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarations
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalSeparation

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo
namespace Examples
namespace HostAnalysisRequestKernelProof

open Engine
open OneCenter
open HostAnalysisRequestBuilder

noncomputable section

theorem broadSurface_validateGlobalNameShape :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.validateGlobalNameShape = .ok () := by
  unfold Engine.HostAnalysisSuiteRequest.validateGlobalNameShape
  rw [broadSurface_validateGlobalModuleNameShape]
  rw [broadSurface_validateGlobalDeclarationNameShape]
  exact broadSurface_validateGlobalModuleSeparationShape

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
