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

def witness7 : HostMoleculeTargetWitnessRequest := witnessAt 7

set_option maxHeartbeats 1000000 in
theorem witness7_ready : witness7.witness.ready = true := by rfl

set_option maxHeartbeats 1000000 in
theorem witness7_imports : validateModuleNames "imports" witness7.imports = .ok () := by rfl

theorem witness7_names :
    validateLeanNames "generated target-witness names" witness7.generatedLeanNames = .ok () :=
  names_ok_of_ready witness7 witness7_ready (by rfl) (by rfl) (by rfl)

set_option maxHeartbeats 1000000 in
theorem witness7_metadata : witness7.validateMetadataShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateMetadataShape
  simp only [witness7_imports, witness7_names]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
