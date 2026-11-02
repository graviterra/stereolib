import TetraStereo.Examples.LocalizedNoDoubleReferenceFixtures
import TetraStereo.OneCenter.LocalizedNoDoubleReferencePipeline
import TetraStereo.OneCenter.LocalizedNoDoublePublicPipeline

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedNoDoubleCertificateProbe
open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.LocalizedNoDoubleReference
open TetraStereo.Certificate.Dependency
open LocalizedNoDoubleReferenceFixtures

private def checkAssertion (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

private def differentOutcome : Option LocalizedAuxiliaryLabel → Option LocalizedAuxiliaryLabel
  | some (.chiral .R) => some (.chiral .S)
  | _ => some (.chiral .R)

/-- Produce and replay a molecular certificate, then reject outcome and reference corruption. -/
def main : IO Unit := do
  let some input := halomethane | throw (IO.userError "fixture was not admitted")
  let fuel := carrierFuel input
  let semantics := runtimeSemantics input fuel
  let system := input.certified.localizedCertificateSystem fuel semantics
  let deps := input.certified.localizedCertificateDependencies fuel
  let nodes := input.certified.localizedCertificateNodes fuel semantics
  let some facts := check system deps nodes | throw (IO.userError "generated certificate rejected")
  checkAssertion "25 molecular occurrences certified" (decide (nodes.length = 25))
  checkAssertion "all occurrences covered exactly once"
    (decide (facts.map Prod.fst).Nodup &&
      (input.certified.localizedOccurrenceCarrier fuel).all
        (fun occurrence => decide (occurrence ∈ facts.map Prod.fst)))
  let results := input.certified.canonicalTetrahedralCenters.map fun center =>
    (center.val.val, lookup facts (input.certified.localizedFinalOccurrenceExecutable fuel center))
  checkAssertion "certificate assigns R to center 0"
    (decide (results = [(0, some (.chiral .R))]))
  checkAssertion "certificate agrees with reference evaluation" (decide (results = analyze input))
  match nodes with
  | [] => throw (IO.userError "empty certificate")
  | head :: tail =>
      let wrongOutcome := { head with outcome := differentOutcome head.outcome } :: tail
      checkAssertion "changed proposed outcome rejected" ((check system deps wrongOutcome).isNone)
      let badReference := { head with references := [0] } :: tail
      checkAssertion "forward/out-of-range dependency reference rejected"
        ((check system deps badReference).isNone)
  checkAssertion "public proposal checker accepts generated certificate"
    ((checkProposals? input nodes).isSome)
  checkAssertion "empty proposals rejected for missing coverage"
    ((checkProposals? input []).isNone)
  checkAssertion "truncated proposals rejected for missing coverage"
    ((checkProposals? input (nodes.take (nodes.length - 1))).isNone)
  let fallback := evaluateCheckedOrReference input []
  checkAssertion "rejected proposals fall back to exact reference facts"
    (decide (fallback = evaluatedFacts input))
  let accepted := evaluateCheckedOrReference input nodes
  checkAssertion "accepted proposals retain their checked facts"
    (decide (accepted = facts))
  checkAssertion "public molecular source API generates and checks its own certificate"
    (decide (Public.analyzeSource? halomethaneSource = some results))
  checkAssertion "public molecular source API recovers from an empty proposer"
    (decide (Public.analyzeSource? halomethaneSource (fun _ => []) = some results))
  IO.println "molecular certificate regression complete"

#eval main
end TetraStereo.Examples.LocalizedNoDoubleCertificateProbe
