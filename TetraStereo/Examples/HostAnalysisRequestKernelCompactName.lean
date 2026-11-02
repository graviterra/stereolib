import TetraStereo.Engine.HostAnalysisRequestBuilder

set_option autoImplicit false

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

open TetraStereo.Engine

theorem compactGeneratedNameSegment_collision_regression :
    compactGeneratedNameSegment "Tgt" "tpNAJeBnD0" ≠
      compactGeneratedNameSegment "Tgt" "MM3V5Gg1s5" := by
  decide

end TetraStereo.Examples.HostAnalysisRequestKernelProof
