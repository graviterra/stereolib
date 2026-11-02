import TetraStereo.Examples.HostAnalysisRequestKernelWitness12

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

open TetraStereo.Engine

noncomputable section

def witnessMetadataCoverage (request : HostMoleculeTargetWitnessRequest) : Except String Unit := do
  validateModuleNames "coverageSourceModule" [request.coverageSourceModule]
  validateModuleNames "coverageSourcePacketName" [request.coverageSourcePacketName]
  validateModuleNames "coverageSourceAnnotationsName" [request.coverageSourceAnnotationsName]
  validateModuleNames "coverageSourceBlueprintName" [request.coverageSourceBlueprintName]
  validateModuleNames "coverageSourceOwnerName" [request.coverageSourceOwnerName]
  requireHostRequestShape
    (request.coverageSourceOwnerName == request.expectedCoverageSourceOwnerName)
    "host molecule target witness coverage owner declaration is not canonical for the source module"
  requireHostRequestShape request.coverageSourceNamesReady
    "host molecule target witness source declarations must belong to the coverage source module"

set_option maxHeartbeats 1000000 in
theorem witness12_metadata_coverage : witnessMetadataCoverage witness12 = .ok () := by
  rfl

end
end TetraStereo.Examples.HostAnalysisRequestKernelProof
