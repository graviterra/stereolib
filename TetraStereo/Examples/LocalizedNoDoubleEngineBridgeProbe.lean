import TetraStereo.OneCenter.LocalizedNoDoubleEngineBridge
import TetraStereo.Examples.LocalizedNoDoubleReferenceFixtures

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedNoDoubleEngineBridgeProbe
open TetraStereo.OneCenter
open LocalizedNoDoubleReference LocalizedNoDoubleReferenceFixtures

private def checkAssertion (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

def main : IO Unit := do
  let some baseline := halomethane | throw (IO.userError "baseline rejected")
  let baselineNodes := EngineBridge.propose baseline
  checkAssertion "existing constitutional engine proposals accepted on halomethane"
    ((CachedPublic.checkProposals? baseline baselineNodes).isSome)
  checkAssertion "existing engine checked report assigns baseline R"
    (decide (EngineBridge.analyze baseline = [(0, some (.chiral .R))]))
  let .ok (some interaction) := interactingVariation.admitted
    | throw (IO.userError "interacting fixture rejected")
  let interactionNodes := EngineBridge.propose interaction
  checkAssertion "incomplete constitutional-only proposals rejected on interacting pseudoasymmetry"
    ((CachedPublic.checkProposals? interaction interactionNodes).isNone)
  checkAssertion "existing engine fallback recovers r, S, R at interacting centers"
    (decide (EngineBridge.analyze interaction =
      [(1, some (.pseudoasymmetric .r)), (2, some (.chiral .S)), (7, some (.chiral .R))]))
  IO.println "existing graph engine checked integration complete"

#eval main
end TetraStereo.Examples.LocalizedNoDoubleEngineBridgeProbe
