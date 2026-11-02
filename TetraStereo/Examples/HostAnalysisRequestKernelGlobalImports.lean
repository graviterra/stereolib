import TetraStereo.Examples.HostAnalysisRequestKernelGlobalImportsDistinct

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

open TetraStereo.Engine
open TetraStereo.Examples.HostAnalysisRequestBuilder

noncomputable section

theorem broadSurface_validateUniqueManifestImportModules :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.validateUniqueManifestImportModules = .ok () := by
  unfold HostAnalysisSuiteRequest.validateUniqueManifestImportModules
  rw [broadSurface_manifestImportModules_eq]
  rw [broadSurface_manifestImportModules_distinct]
  rfl

end
end TetraStereo.Examples.HostAnalysisRequestKernelProof
