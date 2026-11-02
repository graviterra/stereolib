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

def witness13 : HostMoleculeTargetWitnessRequest := witnessAt 13

set_option maxHeartbeats 1000000 in
theorem witness13_ready : witness13.witness.ready = true := by rfl

set_option maxHeartbeats 1000000 in
theorem witness13_imports : validateModuleNames "imports" witness13.imports = .ok () := by rfl


end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
