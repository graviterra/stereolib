import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationsDistinct

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

open TetraStereo.Engine
open TetraStereo.Examples.HostAnalysisRequestBuilder

noncomputable section

theorem broadSurface_validateUniqueSuiteDeclarationNames :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.validateUniqueSuiteDeclarationNames = .ok () := by
  unfold HostAnalysisSuiteRequest.validateUniqueSuiteDeclarationNames
  rw [broadSurface_suiteDeclarationNames_eq]
  rw [broadSurface_suiteDeclarationNames_distinct]
  rfl

end
end TetraStereo.Examples.HostAnalysisRequestKernelProof
