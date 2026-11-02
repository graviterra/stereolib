import TetraStereo.Examples.HostAnalysisRequestKernelWitness5

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo
namespace Examples
namespace HostAnalysisRequestKernelProof

open Engine
open OneCenter
open HostAnalysisRequestBuilder

noncomputable section

theorem witness5_names :
    validateLeanNames "generated target-witness names" witness5.generatedLeanNames = .ok () :=
  names_ok_of_ready witness5 witness5_ready (by rfl) (by rfl) (by rfl)

set_option maxHeartbeats 1000000 in
theorem witness5_metadata : witness5.validateMetadataShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateMetadataShape
  simp only [witness5_imports, witness5_names]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
