import TetraStereo.OneCenter.LocalizedCheckedPipeline
import TetraStereo.Examples.LocalizedNoDoubleReferenceFixtures
import TetraStereo.Examples.LocalizedShortCircuitDoubleBondProbe

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedCheckedPipelineProbe
open OneCenter OneCenter.CertifiedLocalizedCIPInput OneCenter.LocalizedReference
open Certificate.Dependency

private def checkAssertion (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

/-- Execute the original eager endpoint frame compiler, including its full Rule-3 callback. -/
def originalGeometry? (source : AuthoritativeChemicalInput) : Option OfficialRule3Geometry := do
  let input ← admitSource? source
  let fuel := carrierFuel input
  let occurrence ← (input.certified.localizedOccurrenceCarrier fuel).find? fun item =>
    decide (item.val.root.val = 0 ∧ item.val.address.length = 1 ∧
      item.val.node.provenance = .realAtom) &&
      (item.val.node.current?.map (fun atom => atom.val) == some 1) &&
      (item.val.node.parent?.map (fun atom => atom.val) == some 0)
  let result ← input.certified.localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec?
    occurrence occurrence (fun _ _ => none)
    (input.certified.buildLocalizedDescriptorBearingRule3FrameExec?
      occurrence (fun _ _ => none) (localizedDescriptorBearingRule3EvaluationFuel fuel))
  pure result.unit.geometry

def main : IO Unit := do
  let source := LocalizedNoDoubleReferenceFixtures.halomethaneSource
  let some bundle := evaluateSource? source | throw (IO.userError "baseline source rejected")
  let input := bundle.1
  let result := bundle.2
  checkAssertion "full-domain pipeline baseline R"
    (decide (report input result.facts = [(0, some (.chiral .R))]))
  checkAssertion "baseline generated certificate has 25 occurrences" (result.nodes.length == 25)
  checkAssertion "certificate independently replays" ((checkProposals? input result.nodes).isSome)
  checkAssertion "incomplete certificate rejected" ((checkProposals? input []).isNone)
  checkAssertion "truncated certificate rejected"
    ((checkProposals? input (result.nodes.dropLast)).isNone)
  match result.nodes with
  | [] => throw (IO.userError "certificate empty")
  | head :: tail =>
      let changed : Option LocalizedAuxiliaryLabel :=
        if head.outcome = some (.chiral .R) then some (.chiral .S) else some (.chiral .R)
      let corrupted := { head with outcome := changed } :: tail
      checkAssertion "corrupt outcome rejected" ((checkProposals? input corrupted).isNone)
      checkAssertion "forward reference rejected"
        ((checkProposals? input ({ head with references := [0] } :: tail)).isNone)
  let fallback := evaluate input []
  checkAssertion "fallback returns a replayable certificate"
    ((checkProposals? input fallback.nodes).isSome)
  checkAssertion "fallback preserves report"
    (decide (report input fallback.facts = report input result.facts))
  checkAssertion "source API preserves answer under rejecting proposer"
    (decide (analyzeSource? source (fun _ => []) = some [(0, some (.chiral .R))]))
  for cis in [false, true] do
    let alkene := LocalizedShortCircuitDoubleBondProbe.source cis
    checkAssertion "order-two source passes general admission" ((admitSource? alkene).isSome)
    checkAssertion "original eager full-key compiler resolves alkene geometry"
      (decide (originalGeometry? alkene = some (if cis then .seqcis else .seqtrans)))
    let some alkeneBundle := evaluateSource? alkene
      | throw (IO.userError "alkene certificate pipeline rejected source")
    checkAssertion "alkene complete certificate independently replays"
      ((checkProposals? alkeneBundle.1 alkeneBundle.2.nodes).isSome)
    checkAssertion "alkene has no tetrahedral candidates"
      (decide (report alkeneBundle.1 alkeneBundle.2.facts = []))
  checkAssertion "malformed coordinate count rejected"
    ((admitSource? LocalizedNoDoubleReferenceFixtures.shortSpatialHalomethaneSource).isNone)
  IO.println "full-domain checked pipeline regression complete"

#eval main
end TetraStereo.Examples.LocalizedCheckedPipelineProbe
