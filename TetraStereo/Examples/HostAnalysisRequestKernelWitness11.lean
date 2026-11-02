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

def witness11 : HostMoleculeTargetWitnessRequest := witnessAt 11

/-! ### Evaluated snapshot of the fixture request at index eleven

`witnessAt 11` is definitionally the twelfth coverage-bearing request of the
broad-surface fixture.  Reducing the whole `List.getD` derivation separately in
every field proof is unnecessarily expensive, so the declarations below expose
the single request that index eleven selects.  The snapshot reuses the
fixture's own builders (`HostGraphRelationTarget.witness` and
`witnessRequest?`), so every evaluated field stays exactly the same by
construction. -/


def witness11Target : HostGraphRelationTarget where
  keySuffix := "graph-classifier-mirror-meso-same"
  description := "graph descriptor classifier proves mirror/same under meso evidence"
  kind := HostGraphRelationTargetKind.descriptorClassifierSound
  expectedOutcome? := some CipRSClassRelation.same
  outcomePrecondition := HostMoleculeGraphOutcomePrecondition.descriptorMesoLeft


def witness11OutputTarget : HostStereochemicalOutputTarget :=
  HostStereochemicalOutputTarget.graphRelation witness11Target

/-- The single request that the fixture's witness list holds at index eleven. -/
def witness11ViaRequest : HostMoleculeTargetWitnessRequest :=
  (broadSurfaceMoleculeAnalysisRequest.witnessRequest? witness11OutputTarget).getD
    fallbackWitnessRequest

/-- The evaluated target witness carried by that request. -/
def witness11WitnessSnapshot : HostMoleculeTargetWitness :=
  witness11Target.witness broadSurfaceMoleculeAnalysisRequest.key
    broadSurfaceMoleculeAnalysisRequest.packet

-- One selection of the fixture witness list; every later field proof reuses this equation
-- instead of unfolding the whole `witnessAt 11` derivation again.
set_option maxHeartbeats 1000000 in
theorem witness11_eq_via : witness11 = witness11ViaRequest := by rfl

theorem witness11ViaRequest_witness :
    witness11ViaRequest.witness = witness11WitnessSnapshot := by
  unfold witness11ViaRequest
  rfl

set_option maxHeartbeats 1000000 in
theorem witness11WitnessSnapshot_ready : witness11WitnessSnapshot.ready = true := by rfl

theorem witness11ViaRequest_ready : witness11ViaRequest.witness.ready = true := by
  rw [witness11ViaRequest_witness]
  exact witness11WitnessSnapshot_ready

set_option maxHeartbeats 1000000 in
theorem witness11_ready : witness11.witness.ready = true := by
  rw [witness11_eq_via]
  exact witness11ViaRequest_ready

set_option maxHeartbeats 1000000 in
theorem witness11ViaRequest_imports :
    validateModuleNames "imports" witness11ViaRequest.imports = .ok () := by
  unfold witness11ViaRequest
  rfl

theorem witness11_imports : validateModuleNames "imports" witness11.imports = .ok () := by
  rw [witness11_eq_via]
  exact witness11ViaRequest_imports

assert_kernel_only witness11WitnessSnapshot_ready
assert_kernel_only witness11ViaRequest_ready
assert_kernel_only witness11_ready
assert_kernel_only witness11ViaRequest_imports
assert_kernel_only witness11_imports

end
end HostAnalysisRequestKernelProof
end Examples
end TetraStereo
