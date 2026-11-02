import TetraStereo.Examples.HostAnalysisRequestKernelFixture

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

open TetraStereo.Engine
open TetraStereo.Examples.HostAnalysisRequestBuilder

theorem broadSurfaceMoleculeAnalysisRequest_detector_coverage :
    broadSurfaceMoleculeAnalysisRequest.detectorCoverage =
      { rawDoubleBonds := 3
        assignedDoubleBonds := 1
        cumulenes := 1
        axes := 1
        planes := 1
        helices := 1
        conformations := 1
        ensembles := 1
        auxiliaryRule5Nodes := 1
        phantomNodes := 1
        lonePairNodes := 1
        total := 13 } := by
  rfl

end TetraStereo.Examples.HostAnalysisRequestKernelProof
