import TetraStereo.OneCenter.LocalizedShortCircuitStrictCertificate
import TetraStereo.Examples.LocalizedDieneReferenceProbe
import TetraStereo.Examples.LocalizedNoDoubleReferenceFixtures

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedStrictCertificateProbe
open OneCenter OneCenter.CertifiedLocalizedCIPInput OneCenter.LocalizedShortCircuit

private def check (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

/-- Every center and its finite completeness certificate are discovered from molecule data. -/
def certificateReport (input : Input) : Report :=
  input.certified.canonicalTetrahedralCenters.map fun center =>
    let target := input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center
    (center.val.val,
      (input.certified.localizedStrictRule3DescriptorCertificate? target).map
        (fun certificate => (.chiral certificate.1 : LocalizedAuxiliaryLabel)))

private def fixtureReport (fixture : LocalizedNoDoubleReferenceFixtures.Fixture) : IO Report := do
  match admitSmilesSpatial? fixture.smiles fixture.spatial with
  | .ok (some input) => pure (certificateReport input)
  | _ => throw (IO.userError ("fixture rejected: " ++ fixture.name))

/-- Data-only tests of automatic completeness evidence. Positive tests need no hand-written
molecular proof. A negative result means the sufficient class was not certified. -/
def main : IO Unit := do
  let some diene := admitSource? LocalizedDieneReferenceProbe.dieneSource
    | throw (IO.userError "diene rejected")
  let certifiedDiene := certificateReport diene
  check "automatic diene completeness certificate yields R"
    (decide (certifiedDiene = [(0, some (.chiral .R))]))
  let evaluation := Cached.evaluate diene []
  let some replay := Cached.checkProposals? diene evaluation.nodes
    | throw (IO.userError "diene dependency certificate replay failed")
  check "automatic strict certificate agrees with replayed global pipeline"
    (decide (report diene replay = certifiedDiene))
  let ring ← fixtureReport LocalizedNoDoubleReferenceFixtures.ring
  check "ring completeness evidence is constructed"
    (decide (ring = [(0, some (.chiral .S)), (2, some (.chiral .R)), (4, none)]))
  let triple ← fixtureReport LocalizedNoDoubleReferenceFixtures.nitrile
  check "multiple-bond completeness evidence is constructed"
    (decide (triple = [(0, some (.chiral .S)), (4, some (.chiral .R)), (6, none)]))
  let deep ← fixtureReport LocalizedNoDoubleReferenceFixtures.deep
  check "deep-comparison completeness evidence is constructed"
    (decide (deep = [(1, some (.chiral .R)), (2, none), (3, none), (4, none),
      (6, none), (7, none), (8, none)]))
  let before ← fixtureReport LocalizedNoDoubleReferenceFixtures.interacting
  let after ← fixtureReport LocalizedNoDoubleReferenceFixtures.interactingVariation
  check "interacting branch centers certify while central Rule45-dependent center is deferred"
    (decide (before = [(1, none), (2, some (.chiral .R)), (7, some (.chiral .R))] ∧
      after = [(1, none), (2, some (.chiral .S)), (7, some (.chiral .R))]))
  let some missing := admitSource? LocalizedNoDoubleReferenceFixtures.halomethaneWithoutSpatialSource
    | throw (IO.userError "coordinate-free input rejected at intake")
  check "missing geometry does not manufacture completeness evidence"
    (decide (certificateReport missing = [(0, none)]))
  let degenerateSource : AuthoritativeChemicalInput :=
    { LocalizedNoDoubleReferenceFixtures.halomethaneSource with
      spatial? := some { positions := List.replicate 5 { x := 0, y := 0, z := 0 } } }
  let some degenerate := admitSource? degenerateSource
    | throw (IO.userError "degenerate input rejected at intake")
  check "degenerate geometry does not manufacture completeness evidence"
    (decide (certificateReport degenerate = [(0, none)]))

#eval main
end TetraStereo.Examples.LocalizedStrictCertificateProbe
