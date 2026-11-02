import TetraStereo.OneCenter.LocalizedRankedPreparation
import TetraStereo.Examples.LocalizedNoDoubleReferenceFixtures

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedRankedPreparationProbe
open OneCenter OneCenter.CertifiedLocalizedCIPInput OneCenter.LocalizedShortCircuit
open Certificate.Dependency

private def checkTest (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

private def fixtureInput (fixture : LocalizedNoDoubleReferenceFixtures.Fixture) : IO Input := do
  match admitSmilesSpatial? fixture.smiles fixture.spatial with
  | .ok (some input) => pure input
  | _ => throw (IO.userError ("fixture rejected: " ++ fixture.name))

private def targetAt (input : Input) (index : Nat) : IO (Occurrence input) := do
  let some center := input.certified.canonicalTetrahedralCenters.find? (fun c => c.val.val == index)
    | throw (IO.userError "expected tetrahedral candidate missing")
  pure (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)

/-- All molecular evidence is computed from data; finishing takes no expected label or order. -/
def main : IO Unit := do
  let input ← fixtureInput LocalizedNoDoubleReferenceFixtures.interactingVariation
  let target ← targetAt input 1
  let some prepared := prepareSupportedRanked? input target
    | throw (IO.userError "interacting target preparation failed")
  checkTest "finite preparation retains nonzero canonical molecular volume"
    (decide (CartesianPoint3.orientedVolume (prepared.localPreparation.point 0)
      (prepared.localPreparation.point 1) (prepared.localPreparation.point 2)
      (prepared.localPreparation.point 3) ≠ 0))
  let finished := prepared.finish
  checkTest "total finishing computes lowercase r from interacting branches"
    (decide (finished.1 = .pseudoasymmetric .r))
  checkTest "finished certificate retains actually observed pseudo comparisons"
    (finished.2.localEvidence.evidence.tracked.pseudoComparisons > 0)
  let some replayed := check (Cached.systemUsingCache input prepared.cache)
      (Cached.dependenciesUsingCache input prepared.cache) finished.2.nodes
    | throw (IO.userError "prepared target export rejected")
  checkTest "independent checker accepts exported prepared lowercase r"
    (decide (lookup replayed target = some (.pseudoasymmetric .r)))
  checkTest "preparation support excludes the target"
    (decide (target ∉ prepared.support.facts.map Prod.fst))
  let original ← fixtureInput LocalizedNoDoubleReferenceFixtures.interacting
  let originalTarget ← targetAt original 1
  checkTest "unresolved equal branch comparison refuses finite preparation"
    (prepareSupportedRanked? original originalTarget).isNone
  let ring ← fixtureInput LocalizedNoDoubleReferenceFixtures.ring
  let ringTarget ← targetAt ring 0
  checkTest "prepared ring result is S"
    (decide ((certifyPreparedRanked? ring ringTarget).map Sigma.fst = some (.chiral .S)))
  let triple ← fixtureInput LocalizedNoDoubleReferenceFixtures.nitrile
  let tripleTarget ← targetAt triple 0
  checkTest "prepared triple-bond result is S"
    (decide ((certifyPreparedRanked? triple tripleTarget).map Sigma.fst = some (.chiral .S)))
  let deep ← fixtureInput LocalizedNoDoubleReferenceFixtures.deep
  let deepTarget ← targetAt deep 1
  checkTest "prepared deep-comparison result is R"
    (decide ((certifyPreparedRanked? deep deepTarget).map Sigma.fst = some (.chiral .R)))
  let some missing := admitSource? LocalizedNoDoubleReferenceFixtures.halomethaneWithoutSpatialSource
    | throw (IO.userError "coordinate-free input rejected before preparation")
  let missingTarget ← targetAt missing 0
  checkTest "missing coordinates refuse finite preparation"
    (prepareSupportedRanked? missing missingTarget).isNone
  let flatSource : AuthoritativeChemicalInput :=
    { LocalizedNoDoubleReferenceFixtures.halomethaneSource with
      spatial? := some { positions := List.replicate 5 { x := 0, y := 0, z := 0 } } }
  let some flat := admitSource? flatSource
    | throw (IO.userError "degenerate input rejected before preparation")
  let flatTarget ← targetAt flat 0
  checkTest "zero-volume geometry refuses finite preparation"
    (prepareSupportedRanked? flat flatTarget).isNone

#eval main
end TetraStereo.Examples.LocalizedRankedPreparationProbe
