import TetraStereo.Examples.HostAnalysisRequestKernelSupport
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

def witness10 : HostMoleculeTargetWitnessRequest := witnessAt 10

/-! ### Evaluated snapshot of the fixture request at index ten

`witnessAt 10` is definitionally the eleventh coverage-bearing request of the broad-surface
fixture.  Reducing the whole `List.getD` derivation separately in every field proof is
unnecessarily expensive, so the declarations below expose the single request that index ten
selects.  The snapshot reuses the fixture's own builders (`HostGraphRelationTarget.witness` and
`witnessRequest?`), so every evaluated field stays exactly the same by construction. -/


def witness10Target : HostGraphRelationTarget where
  keySuffix := "graph-classifier-self-same"
  description := "graph descriptor classifier proves a concrete self/same outcome"
  kind := HostGraphRelationTargetKind.descriptorClassifierSound
  minimumDetectedCenters := 1
  configurationPolicy := HostMoleculeGraphConfigurationPolicy.identitySelf
  expectedOutcome? := some CipRSClassRelation.same
  outcomePrecondition := HostMoleculeGraphOutcomePrecondition.none


def witness10OutputTarget : HostStereochemicalOutputTarget :=
  HostStereochemicalOutputTarget.graphRelation witness10Target

/-- The single request that the fixture's witness list holds at index ten. -/
def witness10ViaRequest : HostMoleculeTargetWitnessRequest :=
  (broadSurfaceMoleculeAnalysisRequest.witnessRequest? witness10OutputTarget).getD
    fallbackWitnessRequest

/-- The evaluated target witness carried by that request. -/
def witness10WitnessSnapshot : HostMoleculeTargetWitness :=
  witness10Target.witness broadSurfaceMoleculeAnalysisRequest.key
    broadSurfaceMoleculeAnalysisRequest.packet

-- One selection of the fixture witness list; every later field proof reuses this equation
-- instead of unfolding the whole `witnessAt 10` derivation again.
set_option maxHeartbeats 1000000 in
theorem witness10_eq_via : witness10 = witness10ViaRequest := by rfl

theorem witness10ViaRequest_witness :
    witness10ViaRequest.witness = witness10WitnessSnapshot := by
  unfold witness10ViaRequest
  rfl

set_option maxHeartbeats 1000000 in
theorem witness10WitnessSnapshot_ready : witness10WitnessSnapshot.ready = true := by rfl

theorem witness10ViaRequest_ready : witness10ViaRequest.witness.ready = true := by
  rw [witness10ViaRequest_witness]
  exact witness10WitnessSnapshot_ready

set_option maxHeartbeats 1000000 in
theorem witness10_ready : witness10.witness.ready = true := by
  rw [witness10_eq_via]
  exact witness10ViaRequest_ready

set_option maxHeartbeats 1000000 in
theorem witness10ViaRequest_imports :
    validateModuleNames "imports" witness10ViaRequest.imports = .ok () := by
  unfold witness10ViaRequest
  rfl

theorem witness10_imports : validateModuleNames "imports" witness10.imports = .ok () := by
  rw [witness10_eq_via]
  exact witness10ViaRequest_imports

theorem witness10ViaRequest_definitionName :
    witness10ViaRequest.definitionName = witness10ViaRequest.witness.expectedDefinitionName := by
  rfl

theorem witness10ViaRequest_coverageTheoremName :
    witness10ViaRequest.coverageTheoremName =
      witness10ViaRequest.witness.expectedCoverageTheoremName := by
  rfl

theorem witness10ViaRequest_theoremName :
    witness10ViaRequest.theoremName = witness10ViaRequest.witness.expectedTheoremName := by
  rfl

set_option maxHeartbeats 1000000 in
theorem witness10ViaRequest_names :
    validateLeanNames "generated target-witness names" witness10ViaRequest.generatedLeanNames =
      .ok () :=
  names_ok_of_ready witness10ViaRequest witness10ViaRequest_ready
    witness10ViaRequest_definitionName witness10ViaRequest_coverageTheoremName
    witness10ViaRequest_theoremName

theorem witness10_names :
    validateLeanNames "generated target-witness names" witness10.generatedLeanNames = .ok () := by
  rw [witness10_eq_via]
  exact witness10ViaRequest_names

set_option maxHeartbeats 1000000 in
theorem witness10ViaRequest_coverageNamesReady :
    witness10ViaRequest.coverageSourceNamesReady = true := by rfl

set_option maxHeartbeats 1000000 in
theorem witness10ViaRequest_coverageOwner :
    (witness10ViaRequest.coverageSourceOwnerName ==
        witness10ViaRequest.expectedCoverageSourceOwnerName) = true := by
  rfl

set_option maxHeartbeats 1000000 in
theorem witness10ViaRequest_metadata :
    witness10ViaRequest.validateMetadataShape = .ok () := by
  unfold HostMoleculeTargetWitnessRequest.validateMetadataShape
  simp only [witness10ViaRequest_imports, witness10ViaRequest_names,
    witness10ViaRequest_coverageNamesReady, witness10ViaRequest_coverageOwner]
  rfl

theorem witness10_metadata : witness10.validateMetadataShape = .ok () := by
  rw [witness10_eq_via]
  exact witness10ViaRequest_metadata

assert_kernel_only witness10WitnessSnapshot_ready
assert_kernel_only witness10ViaRequest_ready
assert_kernel_only witness10_ready
assert_kernel_only witness10ViaRequest_imports
assert_kernel_only witness10_imports
assert_kernel_only witness10ViaRequest_names
assert_kernel_only witness10_names
assert_kernel_only witness10ViaRequest_coverageNamesReady
assert_kernel_only witness10ViaRequest_coverageOwner
assert_kernel_only witness10ViaRequest_metadata
assert_kernel_only witness10_metadata

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
