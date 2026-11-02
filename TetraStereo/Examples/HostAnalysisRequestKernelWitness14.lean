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

def witness14 : HostMoleculeTargetWitnessRequest := witnessAt 14

set_option maxHeartbeats 1000000 in
theorem witness14_ready : witness14.witness.ready = true := by rfl

set_option maxHeartbeats 1000000 in
theorem witness14_imports : validateModuleNames "imports" witness14.imports = .ok () := by rfl


end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
