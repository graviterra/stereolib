import TetraStereo.Examples.HostAnalysisRequestKernelWitness13

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo
namespace Examples
namespace HostAnalysisRequestKernelProof

open Engine
open OneCenter
open HostAnalysisRequestBuilder

noncomputable section

theorem witness13_names :
    validateLeanNames "generated target-witness names" witness13.generatedLeanNames = .ok () :=
  names_ok_of_ready witness13 witness13_ready (by rfl) (by rfl) (by rfl)

set_option maxHeartbeats 1000000 in
theorem witness13_metadata : witness13.validateMetadataShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateMetadataShape
  simp only [witness13_imports, witness13_names]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
