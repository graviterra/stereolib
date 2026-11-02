import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationsData

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

open TetraStereo.Engine

set_option maxHeartbeats 1000000 in
theorem broadSurface_declarationChunk3_distinct :
    hasDuplicateStrings broadSurfaceDeclarationChunk3 = false := by
  decide

end TetraStereo.Examples.HostAnalysisRequestKernelProof
