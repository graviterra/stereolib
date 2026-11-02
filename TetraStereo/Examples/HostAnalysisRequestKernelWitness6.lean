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

def witness6 : HostMoleculeTargetWitnessRequest := witnessAt 6

set_option maxHeartbeats 1000000 in
theorem witness6_ready : witness6.witness.ready = true := by rfl

set_option maxHeartbeats 1000000 in
theorem witness6_imports : validateModuleNames "imports" witness6.imports = .ok () := by rfl

theorem witness6_names :
    validateLeanNames "generated target-witness names" witness6.generatedLeanNames = .ok () :=
  names_ok_of_ready witness6 witness6_ready (by rfl) (by rfl) (by rfl)

set_option maxHeartbeats 1000000 in
theorem witness6_metadata : witness6.validateMetadataShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateMetadataShape
  simp only [witness6_imports, witness6_names]
  rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
