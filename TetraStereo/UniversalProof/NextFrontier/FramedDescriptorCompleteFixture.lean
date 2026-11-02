import TetraStereo.UniversalProof.NextFrontier.FramedDescriptorRuntime
import TetraStereo.UniversalProof.NextFrontier.FramedDescriptorAdoptionFixture

set_option autoImplicit false






namespace TetraStereo.UniversalProof.FramedDescriptorCompleteFixture

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open FramedDescriptorAdoptionFixtureProofs.FramedDescriptorAdoptionFixture

structure StageTrace where
  constitutional : Ordering
  rule4a : Ordering
  leftReferences : List RS
  rightReferences : List RS
  rule4b : Ordering
  hasLowercase : Bool
  rule5R : Ordering
  rule5S : Ordering
  decision : OccurrenceComparison
  deriving Repr, DecidableEq

def fixtureStages (authoritative : Bool) : Option StageTrace := do
  let mol ← nativeFixtureMol?
  let profile ← FrameRuntime.profile? mol (canonicalCenterRoot 1)
  let fuel := analysisFuel mol
  let state ← if authoritative then buildOccurrenceAuxStateFullyAuthoritative? mol fuel 1
               else buildOccurrenceAuxState? mol fuel 1
  let roots ← occurrenceLigandFrame? mol (canonicalCenterRoot 1)
  let left ← roots.find? (fun cursor => cursor.node.atom == 2)
  let right ← roots.find? (fun cursor => cursor.node.atom == 7)
  let constitutional ← FrameRuntime.compareBranch? mol profile authoritative fuel .rule2
    (.actual left) (.actual right)
  let rule4a ← FrameRuntime.compareDescriptorAtTiedRoot? mol profile authoritative state fuel
    .rule4a (.actual left) (.actual right)
  let leftReferences ← FrameRuntime.rule4bReferences? mol profile state fuel [.actual left]
  let rightReferences ← FrameRuntime.rule4bReferences? mol profile state fuel [.actual right]
  let rule4b ← FrameRuntime.compareRule4b? mol profile authoritative state fuel
    (.actual left) (.actual right)
  let rule5R ← FrameRuntime.compareDescriptorAtTiedRoot? mol profile authoritative state fuel
    (.rule5 RS.R RS.R) (.actual left) (.actual right)
  let rule5S ← FrameRuntime.compareDescriptorAtTiedRoot? mol profile authoritative state fuel
    (.rule5 RS.S RS.S) (.actual left) (.actual right)
  let decision ← FrameRuntime.decisionComplete? mol profile authoritative state fuel left right
  pure
    { constitutional := constitutional
      rule4a := rule4a
      leftReferences := leftReferences
      rightReferences := rightReferences
      rule4b := rule4b
      hasLowercase := state.any (fun fact => !fact.uppercase)
      rule5R := rule5R
      rule5S := rule5S
      decision := decision }

/-- Exact observed stage trace. Expected values are checked below against actual execution. -/
def expectedTrace : StageTrace :=
  { constitutional := .eq
    rule4a := .eq
    leftReferences := [.R]
    rightReferences := [.S]
    rule4b := .eq
    hasLowercase := false
    rule5R := .gt
    rule5S := .lt
    decision := { ordering := .gt, pseudo := true } }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem fixture_fast_trace : fixtureStages false = some expectedTrace := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem fixture_authoritative_trace : fixtureStages true = some expectedTrace := by
  decide +kernel

#eval fixtureStages false
#eval fixtureStages true

end TetraStereo.UniversalProof.FramedDescriptorCompleteFixture
