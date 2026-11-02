import TetraStereo.Examples.HostAnalysisRequestKernelSupport

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo
namespace Examples
namespace HostAnalysisRequestKernelProof

open Engine
open OneCenter
open HostAnalysisRequestBuilder

noncomputable section

def witness0 : HostMoleculeTargetWitnessRequest := witnessAt 0

set_option maxHeartbeats 1000000 in
theorem witness0_ready : witness0.witness.ready = true := by rfl

set_option maxHeartbeats 1000000 in
theorem witness0_imports : validateModuleNames "imports" witness0.imports = .ok () := by rfl

theorem witness0_names :
    validateLeanNames "generated target-witness names" witness0.generatedLeanNames = .ok () :=
  names_ok_of_ready witness0 witness0_ready (by rfl) (by rfl) (by rfl)

set_option maxHeartbeats 1000000 in
theorem witness0_metadata : witness0.validateMetadataShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateMetadataShape
  simp only [witness0_imports, witness0_names]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
