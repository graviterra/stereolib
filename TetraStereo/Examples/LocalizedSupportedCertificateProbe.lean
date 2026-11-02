import TetraStereo.OneCenter.LocalizedShortCircuitSupportedDescriptorCertificate
import TetraStereo.Examples.LocalizedNoDoubleReferenceFixtures

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedSupportedCertificateProbe
open OneCenter OneCenter.CertifiedLocalizedCIPInput OneCenter.LocalizedShortCircuit
open Certificate.Dependency

private def checkTest (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

private def fixtureInput (fixture : LocalizedNoDoubleReferenceFixtures.Fixture) : IO Input := do
  match admitSmilesSpatial? fixture.smiles fixture.spatial with
  | .ok (some input) => pure input
  | _ => throw (IO.userError ("fixture rejected: " ++ fixture.name))

/-- Data alone drive target discovery, dependency evidence and the lowercase descriptor.
Every proposed-node replay below executes the existing checker independently. -/
def main : IO Unit := do
  let input ← fixtureInput LocalizedNoDoubleReferenceFixtures.interactingVariation
  let some result := certifyCenter? input 1
    | throw (IO.userError "pseudoasymmetric target certificate missing")
  checkTest "automatic interacting-center certificate computes lowercase r"
    (decide (result.descriptor = .pseudoasymmetric .r))
  let cache := result.certificate.cache
  let support := result.certificate.support
  let system := Cached.systemUsingCache input cache
  let deps := Cached.dependenciesUsingCache input cache
  let some replayed := check system deps result.certificate.nodes
    | throw (IO.userError "exported target certificate rejected")
  checkTest "independent ordinary checker accepts exported lowercase r"
    (decide (lookup replayed result.target = some (.pseudoasymmetric .r)))
  checkTest "generated support excludes target and explicitly lists every permitted read"
    (decide (result.target ∉ support.facts.map Prod.fst) &&
      (dependencies input result.target).all (fun source => decide (source ∈ support.facts.map Prod.fst)))
  checkTest "independent support checker accepts generated predecessor prefix"
    (checkDependencySupport? input cache result.target support.nodes).isSome
  checkTest "support checker refuses target already present despite valid exported nodes"
    (checkDependencySupport? input cache result.target result.certificate.nodes).isNone
  let index := support.nodes.findIdx (fun node => node.outcome.isNone &&
    decide (node.target ∈ dependencies input result.target))
  checkTest "test fixture contains an explicit required none fact" (index < support.nodes.length)
  let truncated := support.nodes.take index
  checkTest "truncated prefix remains a valid partial certificate"
    (check system deps truncated).isSome
  checkTest "missing required none fact cannot impersonate verified none"
    (checkDependencySupport? input cache result.target truncated).isNone
  let corrupted := support.nodes.mapIdx fun index node =>
    let wrong : Option LocalizedAuxiliaryLabel :=
      if node.outcome = some (.chiral .R) then some (.chiral .S) else some (.chiral .R)
    if index = 0 then { node with outcome := wrong } else node
  checkTest "corrupt predecessor outcome is rejected" (check system deps corrupted).isNone
  let original ← fixtureInput LocalizedNoDoubleReferenceFixtures.interacting
  checkTest "unresolved original central comparison produces no certificate"
    (certifyCenter? original 1).isNone
  let ring ← fixtureInput LocalizedNoDoubleReferenceFixtures.ring
  checkTest "ring target is certified through the same supported constructor"
    (decide ((certifyCenter? ring 0).map (fun result => result.descriptor) = some (.chiral .S)))
  let triple ← fixtureInput LocalizedNoDoubleReferenceFixtures.nitrile
  checkTest "triple-bond target is certified through the same supported constructor"
    (decide ((certifyCenter? triple 0).map (fun result => result.descriptor) = some (.chiral .S)))
  let deep ← fixtureInput LocalizedNoDoubleReferenceFixtures.deep
  checkTest "deep-comparison target is certified through the same supported constructor"
    (decide ((certifyCenter? deep 1).map (fun result => result.descriptor) = some (.chiral .R)))
  checkTest "unperceived atom index returns no target certificate" (certifyCenter? input 999).isNone
  checkTest "public source API refuses missing target geometry"
    (certifySourceCenter? LocalizedNoDoubleReferenceFixtures.halomethaneWithoutSpatialSource 0).isNone

#eval main
end TetraStereo.Examples.LocalizedSupportedCertificateProbe
