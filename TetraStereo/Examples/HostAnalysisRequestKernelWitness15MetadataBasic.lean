import TetraStereo.Examples.HostAnalysisRequestKernelWitness15Names
import TetraStereo.Examples.HostAnalysisRequestKernelWitness12MetadataDecompose

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

open TetraStereo.Engine

noncomputable section

set_option maxHeartbeats 1000000 in
theorem witness15_metadata_basic : witnessMetadataBasic witness15 = .ok () := by
  unfold witnessMetadataBasic
  simp only [witness15_imports]
  rfl

end
end TetraStereo.Examples.HostAnalysisRequestKernelProof
