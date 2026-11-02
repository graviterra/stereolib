import TetraStereo.Examples.HostAnalysisRequestKernelWitness11Names
import TetraStereo.Examples.HostAnalysisRequestKernelWitness11CoverageMetadata
import TetraStereo.Examples.HostWitness11MetadataFieldValidation
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

/-! ### Name and metadata validation for the index-eleven witness

Final of the three compilation units replacing the former all-in-one metadata module.
`witness11_names` is produced by `HostAnalysisRequestKernelWitness11Names`; the coverage
facts are produced by `HostAnalysisRequestKernelWitness11CoverageMetadata`.  This module
only adds the two remaining public statements, with unchanged statements:

* `witness11ViaRequest_metadata` — the selected request passes `validateMetadataShape`;
* `witness11_metadata` — the index-eleven fixture witness passes `validateMetadataShape`.

The field validations are proved separately in `HostWitness11MetadataFieldValidation`.
This compatibility module reuses their compiled result, avoiding repeated elaboration of the
large witness construction while preserving the existing public theorem statements. -/

theorem witness11ViaRequest_metadata :
    witness11ViaRequest.validateMetadataShape = .ok () :=
  witness11ViaRequest_metadata_from_fields

theorem witness11_metadata : witness11.validateMetadataShape = .ok () := by
  rw [witness11_eq_via]
  exact witness11ViaRequest_metadata

assert_kernel_only witness11ViaRequest_metadata
assert_kernel_only witness11_metadata

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
