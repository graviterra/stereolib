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

def witness15 : HostMoleculeTargetWitnessRequest := witnessAt 15

set_option maxHeartbeats 1000000 in
theorem witness15_ready : witness15.witness.ready = true := by rfl

set_option maxHeartbeats 1000000 in
theorem witness15_imports : validateModuleNames "imports" witness15.imports = .ok () := by rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
