import TetraStereo.Examples.HostAnalysisRequestKernelWitness14

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo
namespace Examples
namespace HostAnalysisRequestKernelProof

open Engine
open OneCenter
open HostAnalysisRequestBuilder

noncomputable section

theorem witness14_names :
    validateLeanNames "generated target-witness names" witness14.generatedLeanNames = .ok () :=
  names_ok_of_ready witness14 witness14_ready (by rfl) (by rfl) (by rfl)

set_option maxHeartbeats 1000000 in
theorem witness14_metadata : witness14.validateMetadataShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateMetadataShape
  simp only [witness14_imports, witness14_names]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
