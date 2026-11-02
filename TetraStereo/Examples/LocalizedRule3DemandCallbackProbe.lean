import TetraStereo.OneCenter.LocalizedRule3DemandBoundedDescriptor
import TetraStereo.Examples.LocalizedOrdinaryFamilyProbe

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedRule3DemandCallbackProbe
open OneCenter OneCenter.CertifiedLocalizedCIPInput OneCenter.LocalizedShortCircuit
open Certificate.Dependency

private def checkTest (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

def main : IO Unit := do
  let some input := admitSource? (LocalizedOrdinaryFamilyProbe.interactingSource false)
    | throw (IO.userError "interacting input rejected")
  let some bond := (Families.canonicalDoubleBonds input).head?
    | throw (IO.userError "physical double bond absent")
  let occurrence := input.certified.localizedCanonicalDoubleBondFirstChildOccurrenceExec
    (carrierFuel input) bond
  let cursor : input.certified.LocalizedRerootCursor (carrierFuel input) := { occurrence }
  checkTest "canonical interacting double-bond node has a real endpoint callback request"
    (!(input.certified.rule3NodeCallbackRequests occurrence).isEmpty)
  let .ok plan := input.certified.prepareRule3DemandPlan [cursor]
    | throw (IO.userError "callback-dependent graph did not produce checked ranks")
  let requestCount := plan.ranks.vertices.foldl (fun count item =>
    count + (input.certified.rule3NodeCallbackRequests item.occurrence).length) 0
  IO.println s!"callback plan: vertices={plan.ranks.vertices.length}, callbacks={requestCount}, bound={plan.bound}"
  checkTest "checked callback graph contains nonempty demands and a smaller production bound"
    (requestCount > 0 && plan.bound < localizedDescriptorBearingRule3EvaluationFuel (carrierFuel input))
  let table := plan.ranks.vertices.map (fun item => (item, plan.ranks.height item))
  checkTest "independent checker accepts callback-dependent rank table"
    (input.certified.checkRule3DemandRanks? table).isSome
  checkTest "checker rejects a missing callback or child dependency"
    (input.certified.checkRule3DemandRanks? [(cursor, 10000)]).isNone
  let failed := input.certified.discoverRule3DemandRanks 1 [cursor] [] cursor
  checkTest "an active-path repeat is detected before recursive exploration"
    (match failed with | .error (.cycle _) => true | _ => false)
  let cache := Cached.buildRuntimeCache input
  let evaluation := LocalizedShortCircuit.DemandBounded.referenceUsingCache input cache
  let labels := (report input evaluation.facts).map Prod.snd
  checkTest "demand-bounded dependency producer computes opposite branch R and S"
    (labels.length == 2 && decide (some (.chiral .R) ∈ labels) && decide (some (.chiral .S) ∈ labels))
  let some replayed := check (Cached.systemUsingCache input cache)
      (Cached.dependenciesUsingCache input cache) evaluation.nodes
    | throw (IO.userError "independent production checker rejected new evaluator output")
  checkTest "independent production checker replays every new dependency node"
    (decide (replayed = evaluation.facts))
  let target := OrdinaryPlanar.target input.certified (carrierFuel input) bond
  let view := input.certified.localizedDependencyView (lookup evaluation.facts) target
  let result := plan.evaluate target view
  checkTest "callback-dependent frame succeeds with computed auxiliary descriptors" result.isSome
  let expanded := input.certified.buildLocalizedShortCircuitRule3FrameExec?
    target view (plan.bound + 9) [cursor]
  checkTest "callback-dependent result preserves success or refusal at larger budget"
    (result.isSome == expanded.isSome)
  let families := Families.ofEvaluation input evaluation
  checkTest "new evaluator supplies sequence cis assignment with actual Rule5 endpoint parity"
    (decide (families.ordinaryAcyclic.map (fun a => a.outcome.map fun outcome =>
      (outcome.outcome, outcome.left.selection.enantiomorphic, outcome.right.selection.enantiomorphic)) =
        [some (.enantiomorphicDoubleBond .seqCis, true, false)]))

#eval main
end TetraStereo.Examples.LocalizedRule3DemandCallbackProbe
