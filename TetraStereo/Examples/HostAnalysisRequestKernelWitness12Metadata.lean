import TetraStereo.Examples.HostAnalysisRequestKernelWitness12MetadataDecompose

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
theorem witness12_metadata : witness12.validateMetadataShape = .ok () := by
  rw [witness_metadata_decompose witness12]
  simp only [witness12_metadata_basic, witness12_names, witness12_metadata_coverage]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
