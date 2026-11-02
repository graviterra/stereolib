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

def witness8 : HostMoleculeTargetWitnessRequest := witnessAt 8

set_option maxHeartbeats 1000000 in
theorem witness8_ready : witness8.witness.ready = true := by rfl

set_option maxHeartbeats 1000000 in
theorem witness8_imports : validateModuleNames "imports" witness8.imports = .ok () := by rfl

theorem witness8_names :
    validateLeanNames "generated target-witness names" witness8.generatedLeanNames = .ok () :=
  names_ok_of_ready witness8 witness8_ready (by rfl) (by rfl) (by rfl)

set_option maxHeartbeats 1000000 in
theorem witness8_metadata : witness8.validateMetadataShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateMetadataShape
  simp only [witness8_imports, witness8_names]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
