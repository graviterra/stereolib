import TetraStereo.OneCenter.LocalizedShortCircuitEngineBridge
import TetraStereo.Examples.LocalizedDieneReferenceProbe
import TetraStereo.Examples.LocalizedNoDoubleReferenceFixtures

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedShortCircuitPipelineProbe
open OneCenter OneCenter.LocalizedShortCircuit Certificate.Dependency
open OneCenter.CertifiedLocalizedCIPInput

private def checkAssertion (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

def main : IO Unit := do
  let some input := admitSource? LocalizedDieneReferenceProbe.dieneSource
    | throw (IO.userError "diene source rejected")
  let result := evaluate input []
  let observed := report input result.facts
  IO.println s!"diene whole-carrier report: {repr observed}; {result.nodes.length} certificate nodes"
  checkAssertion "diene fixed-point result is R"
    (decide (observed = [(0, some (.chiral .R))]))
  checkAssertion "diene certificate covers all 221 occurrences" (result.nodes.length == 221)
  checkAssertion "diene generated certificate independently replays"
    ((checkProposals? input result.nodes).isSome)
  checkAssertion "missing diene certificate rejected" ((checkProposals? input []).isNone)
  checkAssertion "truncated diene certificate rejected"
    ((checkProposals? input (result.nodes.dropLast)).isNone)
  match result.nodes with
  | [] => throw (IO.userError "empty generated certificate")
  | head :: tail =>
      let changed : Option LocalizedAuxiliaryLabel :=
        if head.outcome = some (.chiral .R) then some (.chiral .S) else some (.chiral .R)
      checkAssertion "corrupted diene outcome rejected"
        ((checkProposals? input ({ head with outcome := changed } :: tail)).isNone)
      checkAssertion "invalid diene dependency reference rejected"
        ((checkProposals? input ({ head with references := [0] } :: tail)).isNone)
  let proposals := EngineBridge.propose input
  let some engineFacts := checkProposals? input proposals
    | throw (IO.userError "diene graph-engine certificate rejected")
  checkAssertion "checked graph engine agrees on diene R"
    (decide (report input engineFacts = observed))
  let baseline := LocalizedNoDoubleReferenceFixtures.halomethaneSource
  checkAssertion "source API resolves rejected proposal through reference fallback"
    (decide (analyzeSource? baseline (fun _ => []) = some [(0, some (.chiral .R))]))
  checkAssertion "malformed spatial source rejected"
    ((admitSource? LocalizedNoDoubleReferenceFixtures.shortSpatialHalomethaneSource).isNone)
  let noSpatial := LocalizedNoDoubleReferenceFixtures.halomethaneWithoutSpatialSource
  checkAssertion "missing geometry produces operational refusal"
    (decide (analyzeSource? noSpatial (fun _ => []) = some [(0, none)]))

#eval main
end TetraStereo.Examples.LocalizedShortCircuitPipelineProbe
