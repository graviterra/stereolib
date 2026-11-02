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

def witness12 : HostMoleculeTargetWitnessRequest := witnessAt 12

set_option maxHeartbeats 1000000 in
theorem witness12_ready : witness12.witness.ready = true := by rfl

set_option maxHeartbeats 1000000 in
theorem witness12_imports : validateModuleNames "imports" witness12.imports = .ok () := by rfl


end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
