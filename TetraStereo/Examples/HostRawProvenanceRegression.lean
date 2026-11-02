import TetraStereo.Engine.HostModuleCompiler
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192

namespace TetraStereo.Examples.HostRawProvenanceRegression

open OneCenter

/-- The actual parser supplies both independent written rows and source introduction history. -/
def parsedRing : RawMolecule :=
  match parseOpenSMILES "[C@H](F)(C(Cl)C1)1" with
  | .ok molecule => molecule
  | .error _ => { atoms := [], bonds := [] }

def request : Engine.HostOfficialStereoRequest where
  key := "ring-provenance-rendering"
  description := "raw serialization regression"
  moduleFileName := "RingProvenance.lean"
  definitionPrefix := "ringProvenance"
  packet := rawMoleculePacket parsedRing .userSuppliedRawMolecule
  centerAtom := 0
  left := 1
  right := 2
  certificateFileName := "RingProvenanceCertificate.lean"
  certificateTheoremName := "ring_provenance_checked"

/-- Production host rendering retains the exact per-atom ring order and root/predecessor table.
This is a serialization assertion, not an acceptance claim for the request's default query. -/
theorem actual_parsed_ring_metadata_rendered :
    request.rawDeclaration.drop 4 =
      ["  neighborOrder := [[1, 2, 4], [0], [0, 3, 4], [2], [2, 0]]",
       "  introductionPredecessors := [none, some 0, some 0, some 2, some 2]"] := by
  decide +kernel

/-- Legacy unknown provenance remains empty in the emitted declaration. -/
theorem unknown_provenance_rendered :
    ({ request with
      packet := rawMoleculePacket ({ parsedRing with introductionPredecessors := [] })
        .userSuppliedRawMolecule } : Engine.HostOfficialStereoRequest).rawDeclaration[5]? =
      some "  introductionPredecessors := []" := by
  decide +kernel

end TetraStereo.Examples.HostRawProvenanceRegression

assert_kernel_only TetraStereo.Examples.HostRawProvenanceRegression.actual_parsed_ring_metadata_rendered
assert_kernel_only TetraStereo.Examples.HostRawProvenanceRegression.unknown_provenance_rendered
