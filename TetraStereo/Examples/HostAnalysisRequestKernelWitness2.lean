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

def witness2 : HostMoleculeTargetWitnessRequest := witnessAt 2

set_option maxHeartbeats 1000000 in
theorem witness2_ready : witness2.witness.ready = true := by rfl

set_option maxHeartbeats 1000000 in
theorem witness2_imports : validateModuleNames "imports" witness2.imports = .ok () := by rfl

theorem witness2_names :
    validateLeanNames "generated target-witness names" witness2.generatedLeanNames = .ok () :=
  names_ok_of_ready witness2 witness2_ready (by rfl) (by rfl) (by rfl)

set_option maxHeartbeats 1000000 in
theorem witness2_metadata : witness2.validateMetadataShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateMetadataShape
  simp only [witness2_imports, witness2_names]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
