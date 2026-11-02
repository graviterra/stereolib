import TetraStereo.Examples.HostAnalysisRequestKernelWitness12

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo
namespace Examples
namespace HostAnalysisRequestKernelProof

open Engine
open OneCenter
open HostAnalysisRequestBuilder

noncomputable section

theorem witness12_names :
    validateLeanNames "generated target-witness names" witness12.generatedLeanNames = .ok () :=
  names_ok_of_ready witness12 witness12_ready (by rfl) (by rfl) (by rfl)

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
