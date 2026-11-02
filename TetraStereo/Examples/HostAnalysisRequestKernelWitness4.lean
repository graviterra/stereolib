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

def witness4 : HostMoleculeTargetWitnessRequest := witnessAt 4

set_option maxHeartbeats 1000000 in
theorem witness4_ready : witness4.witness.ready = true := by rfl

set_option maxHeartbeats 1000000 in
theorem witness4_imports : validateModuleNames "imports" witness4.imports = .ok () := by rfl

theorem witness4_names :
    validateLeanNames "generated target-witness names" witness4.generatedLeanNames = .ok () :=
  names_ok_of_ready witness4 witness4_ready (by rfl) (by rfl) (by rfl)

set_option maxHeartbeats 1000000 in
theorem witness4_metadata : witness4.validateMetadataShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateMetadataShape
  simp only [witness4_imports, witness4_names]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
