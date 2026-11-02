import TetraStereo.OneCenter.LocalizedShortCircuitBoundedPipeline
import TetraStereo.OneCenter.LocalizedShortCircuitEngineBridge
import TetraStereo.Examples.LocalizedNoDoubleReferenceFixtures
import TetraStereo.Examples.LocalizedDieneReferenceProbe
import TetraStereo.Examples.LocalizedShortCircuitDoubleBondProbe

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedBoundedPipelineProbe
open OneCenter OneCenter.CertifiedLocalizedCIPInput OneCenter.LocalizedShortCircuit

private def checkTest (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

def main : IO Unit := do
  let fixture := LocalizedNoDoubleReferenceFixtures.interactingVariation
  let .ok (some packaged) := Linear.evaluateSmilesSpatial? fixture.smiles fixture.spatial
    | throw (IO.userError "linear SMILES pipeline failed")
  let input := packaged.1
  let result := packaged.2
  checkTest "full linear SMILES pipeline returns r, S, R"
    (decide (report input result.facts =
      [(1, some (.pseudoasymmetric .r)), (2, some (.chiral .S)), (7, some (.chiral .R))]))
  let cache := Cached.buildRuntimeCache input
  let some ready := input.certified.localizedRule3CallbackFreeCarrierCertificate? (carrierFuel input)
    | throw (IO.userError "interacting readiness missing")
  let some independentlyChecked := Cached.checkUsingCache? input cache result.nodes
    | throw (IO.userError "ordinary checker rejects linear full certificate")
  checkTest "production checker independently accepts all linear facts"
    (decide (independentlyChecked = result.facts))
  let replay := Linear.evaluate input result.nodes
  checkTest "accepted proposal data are retained"
    (decide (replay.nodes = result.nodes ∧ replay.facts = result.facts))
  let corrupted := result.nodes.mapIdx fun index node =>
    if index = 0 then
      { node with outcome :=
          if node.outcome = some (.chiral .R) then some (.chiral .S) else some (.chiral .R) }
    else node
  checkTest "linear checker rejects a corrupted proposal"
    (Linear.checkUsingCache? input cache ready corrupted).isNone
  let recovered := Linear.evaluate input corrupted
  checkTest "rejected proposals construct the identical full reference certificate"
    (decide (recovered.nodes = result.nodes ∧ recovered.facts = result.facts))
  let some tied := admitSource? (LocalizedShortCircuitDoubleBondProbe.source false true)
    | throw (IO.userError "tied alkene intake failed")
  checkTest "fallback fixture really lacks callback-free readiness"
    (tied.certified.localizedRule3CallbackFreeCarrierCertificate? (carrierFuel tied)).isNone
  let fallback := Linear.evaluate tied []
  let original := Cached.referenceUsingCache tied (Cached.buildRuntimeCache tied)
  checkTest "failed readiness executes existing cached reference fallback"
    (decide (fallback.nodes = original.nodes ∧ fallback.facts = original.facts))
  let some engine := Linear.evaluateSource? LocalizedNoDoubleReferenceFixtures.halomethaneSource
      EngineBridge.propose
    | throw (IO.userError "engine source pipeline failed")
  let originalEngine := Cached.evaluate engine.1 []
  checkTest "existing fast engine is connected through checked proposal interface"
    (decide (report engine.1 engine.2.facts = report engine.1 originalEngine.facts))
  let some diene := Linear.evaluateSource? LocalizedDieneReferenceProbe.dieneSource
    | throw (IO.userError "diene source pipeline failed")
  checkTest "full linear diene pipeline returns R"
    (decide (report diene.1 diene.2.facts = [(0, some (.chiral .R))]))

#eval main
end TetraStereo.Examples.LocalizedBoundedPipelineProbe
