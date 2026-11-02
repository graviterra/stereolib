import TetraStereo.Examples.HostAnalysisRequestKernelWitness12MetadataBasic
import TetraStereo.Examples.HostAnalysisRequestKernelWitness12MetadataCoverage

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

open TetraStereo.Engine

theorem witness_metadata_decompose (request : HostMoleculeTargetWitnessRequest) :
    request.validateMetadataShape = (do
      witnessMetadataBasic request
      validateLeanNames "generated target-witness names" request.generatedLeanNames
      witnessMetadataCoverage request) := by
  simp only [HostMoleculeTargetWitnessRequest.validateMetadataShape, witnessMetadataBasic,
    witnessMetadataCoverage, ← bind_assoc]

end TetraStereo.Examples.HostAnalysisRequestKernelProof
