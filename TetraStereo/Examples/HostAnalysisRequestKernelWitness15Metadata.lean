import TetraStereo.Examples.HostAnalysisRequestKernelWitness15MetadataBasic
import TetraStereo.Examples.HostAnalysisRequestKernelWitness15MetadataCoverage

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

theorem witness15_metadata : witness15.validateMetadataShape = .ok () := by
  rw [witness_metadata_decompose witness15]
  simp only [witness15_metadata_basic, witness15_names, witness15_metadata_coverage]
  rfl

end TetraStereo.Examples.HostAnalysisRequestKernelProof
