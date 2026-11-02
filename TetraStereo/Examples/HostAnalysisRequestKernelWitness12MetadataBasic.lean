import TetraStereo.Examples.HostAnalysisRequestKernelWitness12Names

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

open TetraStereo.Engine

noncomputable section

def witnessMetadataBasic (request : HostMoleculeTargetWitnessRequest) : Except String Unit := do
  requireHostRequestShape (request.key ≠ "")
    "host molecule target witness key must not be empty"
  requireHostRequestShape (request.description ≠ "")
    "host molecule target witness description must not be empty"
  validateNamespacePath "namespacePath" request.namespacePath
  validateModuleNames "imports" request.imports
  validateOptionLines "options" request.options
  validateImportableLeanFileName "fileName" request.fileName

set_option maxHeartbeats 1000000 in
theorem witness12_metadata_basic : witnessMetadataBasic witness12 = .ok () := by
  unfold witnessMetadataBasic
  simp only [witness12_imports]
  rfl

end
end TetraStereo.Examples.HostAnalysisRequestKernelProof
