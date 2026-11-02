import TetraStereo.Examples.HostAnalysisRequestKernelWitness15

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

open TetraStereo.Engine

noncomputable section

theorem witness15_names :
    validateLeanNames "generated target-witness names" witness15.generatedLeanNames = .ok () :=
  names_ok_of_ready witness15 witness15_ready (by rfl) (by rfl) (by rfl)

end
end TetraStereo.Examples.HostAnalysisRequestKernelProof
