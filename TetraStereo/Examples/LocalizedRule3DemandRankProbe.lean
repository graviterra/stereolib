import TetraStereo.OneCenter.LocalizedRule3DemandRankProducer
import TetraStereo.Examples.LocalizedOrdinaryFamilyProbe
import TetraStereo.Examples.LocalizedNoDoubleReferenceFixtures

set_option autoImplicit false
namespace TetraStereo.Examples.LocalizedRule3DemandRankProbe
open OneCenter OneCenter.CertifiedLocalizedCIPInput OneCenter.LocalizedShortCircuit

private def checkTest (name : String) (condition : Bool) : IO Unit :=
  if condition then IO.println ("ok: " ++ name)
  else throw (IO.userError ("failed: " ++ name))

private def failureName {input : CertifiedLocalizedCIPInput} {fuel : Nat} :
    input.Rule3DemandDiscoveryFailure fuel → String
  | .cycle _ => "conservative cycle"
  | .traversalLimit => "traversal limit"
  | .invalidRanks => "invalid ranks"
  | .missingRoot => "missing root"

private def projection (input : CertifiedLocalizedCIPInput) (frame : input.LocalizedRule3CanonicalKeyFrame) :
    List (List (List (OfficialSparseEntry Nat))) × Bool × List (Nat × Nat) ×
      List (List (List (OfficialSparseEntry Nat))) :=
  (frame.rawKeys.map (fun k => k.rule3), frame.coupled,
    frame.excluded.map (fun u => (u.first.val, u.second.val)), frame.keys.map (fun k => k.rule3))

private def runTarget (name : String) (input : Input) (index : Nat) : IO Unit := do
  let some center := input.certified.canonicalTetrahedralCenters.find? (fun c => c.val.val == index)
    | throw (IO.userError (name ++ ": center absent"))
  let target := input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center
  let some base := input.certified.localizedNoDoubleFourLigandFrameExec? target
    | throw (IO.userError (name ++ ": frame absent"))
  match input.certified.prepareRule3DemandPlan base.cursors with
  | .error failure => throw (IO.userError (name ++ ": " ++ failureName failure))
  | .ok plan =>
    let requests := plan.ranks.vertices.foldl (fun count cursor =>
      count + (input.certified.rule3NodeCallbackRequests cursor.occurrence).length) 0
    IO.println s!"demand plan {name}: vertices={plan.ranks.vertices.length}, callbacks={requests}, bound={plan.bound}"
    checkTest (name ++ " automatic rank plan covers all frame roots")
      (base.cursors.all fun root => decide (root ∈ plan.ranks.vertices))
    let table := plan.ranks.vertices.map (fun cursor => (cursor, plan.ranks.height cursor))
    checkTest (name ++ " independent rank checker accepts exported table")
      (input.certified.checkRule3DemandRanks? table).isSome
    checkTest (name ++ " rank checker rejects zeroed table")
      (input.certified.checkRule3DemandRanks? (table.map fun entry => (entry.1, 0))).isNone
    checkTest (name ++ " computed bound fits existing production budget")
      (plan.bound ≤ localizedDescriptorBearingRule3EvaluationFuel (carrierFuel input))
    let frame := plan.evaluate target (fun _ _ => none)
    let expanded := input.certified.buildLocalizedShortCircuitRule3FrameExec?
      target (fun _ _ => none) (plan.bound + 7) base.cursors
    checkTest (name ++ " larger budget preserves optional priorities and physical exclusions")
      (frame.map (projection input.certified) == expanded.map (projection input.certified))

private def runFixture (fixture : LocalizedNoDoubleReferenceFixtures.Fixture) (index : Nat) : IO Unit := do
  let .ok (some input) := admitSmilesSpatial? fixture.smiles fixture.spatial
    | throw (IO.userError (fixture.name ++ ": admission failed"))
  runTarget fixture.name input index

def main : IO Unit := do
  runFixture LocalizedNoDoubleReferenceFixtures.ring 0
  runFixture LocalizedNoDoubleReferenceFixtures.nitrile 0
  runFixture LocalizedNoDoubleReferenceFixtures.deep 1
  runFixture LocalizedNoDoubleReferenceFixtures.interactingVariation 1
  let some interacting := admitSource? (LocalizedOrdinaryFamilyProbe.interactingSource false)
    | throw (IO.userError "double-bond interacting source rejected")
  runTarget "double-bond interacting" interacting 2

#eval main
end TetraStereo.Examples.LocalizedRule3DemandRankProbe
