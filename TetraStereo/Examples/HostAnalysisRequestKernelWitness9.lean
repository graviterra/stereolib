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

def witness9 : HostMoleculeTargetWitnessRequest := witnessAt 9

set_option maxHeartbeats 1000000 in
theorem witness9_ready : witness9.witness.ready = true := by rfl

set_option maxHeartbeats 1000000 in
theorem witness9_imports : validateModuleNames "imports" witness9.imports = .ok () := by rfl

theorem witness9_names :
    validateLeanNames "generated target-witness names" witness9.generatedLeanNames = .ok () :=
  names_ok_of_ready witness9 witness9_ready (by rfl) (by rfl) (by rfl)

set_option maxHeartbeats 1000000 in
theorem witness9_metadata : witness9.validateMetadataShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateMetadataShape
  simp only [witness9_imports, witness9_names]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
