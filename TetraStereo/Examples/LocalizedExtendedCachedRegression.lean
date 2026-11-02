import TetraStereo.OneCenter.LocalizedExtendedShortCircuitCachedPipeline
import TetraStereo.OneCenter.LocalizedExtendedShortCircuitEngineBridge
import TetraStereo.Examples.LocalizedDieneReferenceProbe
import TetraStereo.Examples.LocalizedNoDoubleReferenceFixtures

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedExtendedCachedRegression
open OneCenter OneCenter.CertifiedLocalizedCIPInput OneCenter.LocalizedExtendedShortCircuit

private def checkAssertion (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

private def checkedReport (input : Input) : IO Report := do
  let result := Cached.evaluate input []
  let some facts := Cached.checkProposals? input result.nodes
    | throw (IO.userError "cached generated certificate rejected")
  pure (report input facts)

private def fixtureReport (fixture : LocalizedNoDoubleReferenceFixtures.Fixture) : IO Report := do
  match admitSmilesSpatial? fixture.smiles fixture.spatial with
  | .ok (some input) => checkedReport input
  | _ => throw (IO.userError ("fixture rejected: " ++ fixture.name))

/-- Full successor evaluation and independent certificate replay across the earlier structural,
deep-comparison and interacting-center fixtures, plus the diene recursion regression. -/
def main : IO Unit := do
  let started ← IO.monoMsNow
  let some diene := admitSource? LocalizedDieneReferenceProbe.dieneSource
    | throw (IO.userError "diene rejected")
  let dieneReport ← checkedReport diene
  checkAssertion "cached diene full certificate yields R"
    (decide (dieneReport = [(0, some (.chiral .R))]))
  let proposals := EngineBridge.propose diene
  let some engineFacts := Cached.checkProposals? diene proposals
    | throw (IO.userError "cached engine certificate rejected")
  checkAssertion "cached checked engine matches diene reference"
    (decide (report diene engineFacts = dieneReport))
  let ring ← fixtureReport LocalizedNoDoubleReferenceFixtures.ring
  checkAssertion "successor preserves ring regression"
    (decide (ring = [(0, some (.chiral .S)), (2, some (.chiral .R)), (4, none)]))
  let triple ← fixtureReport LocalizedNoDoubleReferenceFixtures.nitrile
  checkAssertion "successor preserves triple-bond regression"
    (decide (triple = [(0, some (.chiral .S)), (4, some (.chiral .R)), (6, none)]))
  let deep ← fixtureReport LocalizedNoDoubleReferenceFixtures.deep
  checkAssertion "successor preserves deep-comparison regression"
    (decide (deep = [(1, some (.chiral .R)), (2, none), (3, none), (4, none),
      (6, none), (7, none), (8, none)]))
  let before ← fixtureReport LocalizedNoDoubleReferenceFixtures.interacting
  let after ← fixtureReport LocalizedNoDoubleReferenceFixtures.interactingVariation
  checkAssertion "successor preserves interacting-center and pseudoasymmetric response"
    (decide (before = [(1, none), (2, some (.chiral .R)), (7, some (.chiral .R))] ∧
      after = [(1, some (.pseudoasymmetric .r)), (2, some (.chiral .S)), (7, some (.chiral .R))]))

  let finished ← IO.monoMsNow
  IO.println s!"TIMING extended cached regression: {finished - started}ms"

#eval main
end TetraStereo.Examples.LocalizedExtendedCachedRegression
