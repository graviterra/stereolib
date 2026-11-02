import TetraStereo.Examples.HostAnalysisRequestKernelGlobalImportsData

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

open TetraStereo.Engine

set_option maxHeartbeats 1000000 in
theorem broadSurface_manifestImportModules_distinct :
    hasDuplicateStrings broadSurfaceManifestImportModules = false := by
  decide

end TetraStereo.Examples.HostAnalysisRequestKernelProof
