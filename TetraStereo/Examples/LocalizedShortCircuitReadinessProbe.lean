import TetraStereo.OneCenter.LocalizedShortCircuitReadiness
import TetraStereo.Examples.LocalizedDieneReferenceProbe
import TetraStereo.Examples.LocalizedShortCircuitDoubleBondProbe
import TetraStereo.Examples.LocalizedNoDoubleReferenceFixtures

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedShortCircuitReadinessProbe
open OneCenter OneCenter.LocalizedReference

private def checkAssertion (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

private def ready? (source : AuthoritativeChemicalInput) : Option Bool := do
  let input ← admitSource? source
  pure (input.certified.localizedRule3CallbackFreeCarrierCertificate? (carrierFuel input)).isSome

def main : IO Unit := do
  checkAssertion "diene constructs carrier-wide linear-bound readiness"
    (ready? LocalizedDieneReferenceProbe.dieneSource == some true)
  checkAssertion "structural baseline constructs readiness"
    (ready? LocalizedNoDoubleReferenceFixtures.halomethaneSource == some true)
  for cis in [false, true] do
    checkAssertion "strict-root alkene constructs readiness"
      (ready? (LocalizedShortCircuitDoubleBondProbe.source cis) == some true)
  checkAssertion "tied first-atom endpoint is outside strict-root certificate class"
    (ready? (LocalizedShortCircuitDoubleBondProbe.source false true) == some false)
  let missing := { LocalizedDieneReferenceProbe.dieneSource with spatial? := none }
  checkAssertion "missing diene geometry cannot produce readiness"
    (ready? missing == some false)

#eval main
end TetraStereo.Examples.LocalizedShortCircuitReadinessProbe
