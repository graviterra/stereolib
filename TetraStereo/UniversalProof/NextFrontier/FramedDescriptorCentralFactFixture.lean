import TetraStereo.UniversalProof.NextFrontier.FramedDescriptorSortingKernelCertificate
import TetraStereo.UniversalProof.NextFrontier.FramedDescriptorCompleteFixtureKernelCertificate

set_option autoImplicit false

namespace TetraStereo.UniversalProof.FramedDescriptorCentralFactFixture

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open FramedDescriptorAdoptionFixtureProofs.FramedDescriptorAdoptionFixture

/-- Actual parsed input and actual existing auxiliary builder, followed by the complete
shared-profile ordinary caller. This does not claim adoption of complete auxiliary discovery. -/
def centralFact? (authoritative : Bool) : Option OccurrenceAuxFact := do
  let mol ← nativeFixtureMol?
  let fuel := analysisFuel mol
  let state ← if authoritative then buildOccurrenceAuxStateFullyAuthoritative? mol fuel 1
               else buildOccurrenceAuxState? mol fuel 1
  FramedCompleteRuntime.occurrenceFactComplete? mol authoritative fuel state (canonicalCenterRoot 1)

/-- Inspect transient insertion count separately from the final fact's lowercase flag. -/
def centralRanking? (authoritative : Bool) : Option (List Nat × Nat) := do
  let mol ← nativeFixtureMol?
  let fuel := analysisFuel mol
  let state ← if authoritative then buildOccurrenceAuxStateFullyAuthoritative? mol fuel 1
               else buildOccurrenceAuxState? mol fuel 1
  let profile ← FrameRuntime.profile? mol (canonicalCenterRoot 1)
  let roots ← occurrenceLigandFrame? mol (canonicalCenterRoot 1)
  let ranked ← FramedCompleteRuntime.trackedSortComplete? mol profile authoritative state fuel roots
  pure (ranked.1.map (fun cursor => cursor.node.atom), ranked.2)

/-- Expected full result, tested against actual parsed input and complete runtime above. -/
def expectedCentralFact : OccurrenceAuxFact :=
  { key := canonicalOccurrenceKey (canonicalCenterRoot 1)
    atom := 1
    descriptor := .S
    uppercase := false
    priorityPositions := [2, 1, 3, 0] }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem central_fast_fact : centralFact? false = some expectedCentralFact := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem central_authoritative_fact : centralFact? true = some expectedCentralFact := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem central_fast_ranking : centralRanking? false = some ([6, 2, 7, 0], 1) := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem central_authoritative_ranking : centralRanking? true = some ([6, 2, 7, 0], 1) := by
  decide +kernel

#eval centralRanking? false
#eval centralRanking? true
#eval centralFact? false
#eval centralFact? true

end TetraStereo.UniversalProof.FramedDescriptorCentralFactFixture
