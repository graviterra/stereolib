import TetraStereo.Examples.HostAnalysisRequestKernelWitness11
import TetraStereo.Examples.HostWitnessRequestMetadataConstruction
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

/-! ### Canonical generated-name validation for the index-eleven witness

This module is the first of three compilation units that replace the former all-in-one
`HostAnalysisRequestKernelWitness11Metadata` module.  It contains exactly the package-name
part of the public interface:

* `witness11FallbackRequest_not_ready` — the unreachable `getD` fallback is not ready;
* `witness11ViaRequest_definitionName`, `_coverageTheoremName`, `_theoremName` — the three
  canonical generated names of the selected request, derived from the generic structural
  `witnessRequest?` construction lemmas (no concrete fixture witness list is re-evaluated);
* `witness11ViaRequest_names` and `witness11_names` — the public generated-name validation.

Splitting these declarations from the coverage/metadata proofs keeps the cumulative
elaboration of the fixture request below the aggregate memory bound; the remaining heavy
proofs live in `HostAnalysisRequestKernelWitness11CoverageMetadata` and
`HostAnalysisRequestKernelWitness11Metadata`.  Every statement is unchanged from the former
single module. -/

/-- The unreachable fallback request is not ready. -/
theorem witness11FallbackRequest_not_ready : fallbackWitnessRequest.witness.ready = false := by
  rfl

theorem witness11ViaRequest_definitionName :
    witness11ViaRequest.definitionName = witness11ViaRequest.witness.expectedDefinitionName :=
  TetraStereo.Engine.HostMoleculeAnalysisRequest.witnessRequest?_getD_definitionName
    broadSurfaceMoleculeAnalysisRequest witness11OutputTarget fallbackWitnessRequest
    witness11FallbackRequest_not_ready witness11ViaRequest_ready

theorem witness11ViaRequest_coverageTheoremName :
    witness11ViaRequest.coverageTheoremName =
      witness11ViaRequest.witness.expectedCoverageTheoremName :=
  TetraStereo.Engine.HostMoleculeAnalysisRequest.witnessRequest?_getD_coverageTheoremName
    broadSurfaceMoleculeAnalysisRequest witness11OutputTarget fallbackWitnessRequest
    witness11FallbackRequest_not_ready witness11ViaRequest_ready

theorem witness11ViaRequest_theoremName :
    witness11ViaRequest.theoremName = witness11ViaRequest.witness.expectedTheoremName :=
  TetraStereo.Engine.HostMoleculeAnalysisRequest.witnessRequest?_getD_theoremName
    broadSurfaceMoleculeAnalysisRequest witness11OutputTarget fallbackWitnessRequest
    witness11FallbackRequest_not_ready witness11ViaRequest_ready

set_option maxHeartbeats 1000000 in
theorem witness11ViaRequest_names :
    validateLeanNames "generated target-witness names" witness11ViaRequest.generatedLeanNames =
      .ok () :=
  names_ok_of_ready witness11ViaRequest witness11ViaRequest_ready
    witness11ViaRequest_definitionName witness11ViaRequest_coverageTheoremName
    witness11ViaRequest_theoremName

theorem witness11_names :
    validateLeanNames "generated target-witness names" witness11.generatedLeanNames = .ok () := by
  rw [witness11_eq_via]
  exact witness11ViaRequest_names

assert_kernel_only witness11FallbackRequest_not_ready
assert_kernel_only witness11ViaRequest_definitionName
assert_kernel_only witness11ViaRequest_coverageTheoremName
assert_kernel_only witness11ViaRequest_theoremName
assert_kernel_only witness11ViaRequest_names
assert_kernel_only witness11_names

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
