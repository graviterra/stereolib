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

def witness5 : HostMoleculeTargetWitnessRequest := witnessAt 5

set_option maxHeartbeats 1000000 in
theorem witness5_ready : witness5.witness.ready = true := by rfl

set_option maxHeartbeats 1000000 in
theorem witness5_imports : validateModuleNames "imports" witness5.imports = .ok () := by rfl

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
