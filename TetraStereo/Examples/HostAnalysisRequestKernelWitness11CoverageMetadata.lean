import TetraStereo.Examples.HostAnalysisRequestKernelWitness11
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo
namespace Examples
namespace HostAnalysisRequestKernelProof

open Engine
open OneCenter
open HostAnalysisRequestBuilder

noncomputable section

/-! ### Coverage-source metadata of the index-eleven witness

Second of the three compilation units replacing the former all-in-one metadata module.
The two public statements below are unchanged; they are the coverage-source half of
`HostMoleculeTargetWitnessRequest.validateMetadataShape`:

* `witness11ViaRequest_coverageNamesReady` — the selected coverage source declarations all
  belong to the declared source module and the owner declaration is canonical;
* `witness11ViaRequest_coverageOwner` — the owner declaration is the canonical one.

Both are kernel `rfl` evaluations of the fixture request.  Isolating them here means the
final metadata module consumes them as opaque compiled facts instead of re-running the
concrete `witnessRequest?` selection while the rest of `validateMetadataShape` is in scope. -/

set_option maxHeartbeats 1000000 in
theorem witness11ViaRequest_coverageNamesReady :
    witness11ViaRequest.coverageSourceNamesReady = true := by rfl

set_option maxHeartbeats 1000000 in
theorem witness11ViaRequest_coverageOwner :
    (witness11ViaRequest.coverageSourceOwnerName ==
        witness11ViaRequest.expectedCoverageSourceOwnerName) = true := by
  rfl

assert_kernel_only witness11ViaRequest_coverageNamesReady
assert_kernel_only witness11ViaRequest_coverageOwner

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
