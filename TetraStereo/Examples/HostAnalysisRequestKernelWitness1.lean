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

def witness1 : HostMoleculeTargetWitnessRequest := witnessAt 1

set_option maxHeartbeats 1000000 in
theorem witness1_ready : witness1.witness.ready = true := by rfl

set_option maxHeartbeats 1000000 in
theorem witness1_imports : validateModuleNames "imports" witness1.imports = .ok () := by rfl

theorem witness1_names :
    validateLeanNames "generated target-witness names" witness1.generatedLeanNames = .ok () :=
  names_ok_of_ready witness1 witness1_ready (by rfl) (by rfl) (by rfl)

set_option maxHeartbeats 1000000 in
theorem witness1_metadata : witness1.validateMetadataShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateMetadataShape
  simp only [witness1_imports, witness1_names]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
