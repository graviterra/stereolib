import TetraStereo.Examples.HostAnalysisRequestKernelFixture

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo
namespace Examples
namespace HostAnalysisRequestKernelProof

open Engine
open OneCenter
open HostAnalysisRequestBuilder

noncomputable section

/-- Unreachable fallback used to give indexed fixture lookups a total public type. -/
def fallbackWitnessRequest : HostMoleculeTargetWitnessRequest where
  key := ""
  description := ""
  witness :=
    { requestKey := ""
      targetKeySuffix := ""
      targetDescription := ""
      targetLabel := ""
      kind := HostMoleculeTargetWitnessKind.noncenterDescriptor
      coverageField := HostMoleculeTargetCoverageField.axial }
  fileName := ""
  definitionName := ""
  theoremName := ""
  coverageSourceModule := ""
  coverageSourcePacketName := ""
  coverageSourceAnnotationsName := ""
  coverageSourceBlueprintName := ""
  coverageSourceOwnerName := ""
  coverageTheoremName := ""

/-- The concrete source-bearing witness request at one broad-fixture index. -/
def witnessAt (index : Nat) : HostMoleculeTargetWitnessRequest :=
  HostAnalysisRequestBuilder.broadSurfaceMoleculeAnalysisRequest.witnessRequests.getD
    index fallbackWitnessRequest

/-- Canonical ready requests pass generated declaration-name validation structurally. -/
theorem names_ok_of_ready (request : HostMoleculeTargetWitnessRequest)
    (hready : request.witness.ready = true)
    (hdefinition : request.definitionName = request.witness.expectedDefinitionName)
    (hcoverage : request.coverageTheoremName = request.witness.expectedCoverageTheoremName)
    (htheorem : request.theoremName = request.witness.expectedTheoremName) :
    validateLeanNames "generated target-witness names" request.generatedLeanNames = .ok () := by
  apply validateLeanNames_eq_ok_of_all
  apply request.generatedLeanNames_all_safe
  · exact HostMoleculeTargetWitness.nameSuffix_safe_of_ready request.witness hready
  · exact hdefinition
  · exact hcoverage
  · exact htheorem

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
