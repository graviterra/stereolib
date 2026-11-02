import TetraStereo.Examples.HostAnalysisRequestKernelGlobalOfficialModules
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalImports
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalTheorems

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
theorem broadSurface_validateGlobalModuleNameShape :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.validateGlobalModuleNameShape = .ok () := by
  unfold Engine.HostAnalysisSuiteRequest.validateGlobalModuleNameShape
  rw [broadSurface_validateUniqueOfficialHostModules]
  rw [broadSurface_validateUniqueManifestImportModules]
  exact broadSurface_validateUniqueSuiteTheoremNames

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
