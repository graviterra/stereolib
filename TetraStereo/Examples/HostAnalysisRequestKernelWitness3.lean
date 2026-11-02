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

def witness3 : HostMoleculeTargetWitnessRequest := witnessAt 3

set_option maxHeartbeats 1000000 in
theorem witness3_ready : witness3.witness.ready = true := by rfl

set_option maxHeartbeats 1000000 in
theorem witness3_imports : validateModuleNames "imports" witness3.imports = .ok () := by rfl

theorem witness3_names :
    validateLeanNames "generated target-witness names" witness3.generatedLeanNames = .ok () :=
  names_ok_of_ready witness3 witness3_ready (by rfl) (by rfl) (by rfl)

set_option maxHeartbeats 1000000 in
theorem witness3_metadata : witness3.validateMetadataShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateMetadataShape
  simp only [witness3_imports, witness3_names]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
