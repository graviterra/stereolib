import TetraStereo.UniversalProof.NextFrontier.NativeNitrileTrackedSort
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileRuntimeCollection

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge
open TetraStereo.UniversalProof.NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment
open TetraStereo.UniversalProof.RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery

def actualLocalFact (parity : TetrahedralInputParity) : OccurrenceAuxFact :=
  { key := canonicalOccurrenceKey (canonicalCenterRoot 0)
    atom := 0
    descriptor := descriptorOfParity parity false
    uppercase := true
    priorityPositions := [1, 2, 3, 0] }

theorem actual_root_priority_positions (parity : TetrahedralInputParity) (n : Nat) :
    runtimePriorityPositions? (expanded parity n) 0 (orderedRootCursors n) =
      some [1, 2, 3, 0] := by
  unfold runtimePriorityPositions?
  rw [actual_center_ligands]
  simp [orderedRootCursors, nitrileRootCursor, nitrileCursor, aminoCursor,
    canonicalRoot, awayCursor, pathNode]

theorem actual_root_priority_odd : permutationIsEven [1, 2, 3, 0] = false := by decide +kernel

/-- Actual legacy evaluation, reached through the independently proved unavailable framed
profile. The computed priority permutation fixes the returned descriptor and uppercase flag. -/
theorem actual_authoritative_local_fact (parity : TetrahedralInputParity) (n fuel : Nat)
    (state : OccurrenceAuxState) :
    occurrenceFactAuthoritative? (expanded parity n) (fuel + 2) state (canonicalCenterRoot 0) =
      some (actualLocalFact parity) := by
  rw [actual_authoritative_dispatch_legacy]
  have observed := expanded_original_atom parity n 0 _ (raw_center parity n)
  have positions := actual_root_priority_positions parity n
  unfold runtimePriorityPositions? at positions
  rw [actual_center_ligands] at positions
  simp only [legacyOccurrenceFactAuthoritative?, show (canonicalCenterRoot 0).atom = 0 from rfl,
    observed, Bind.bind, Option.bind, materializedAtomSpec, centerSpec,
    actual_center_ligands, actual_center_occurrence_frame,
    (actual_root_tracked_sort parity n fuel state).2, positions,
    actual_root_authoritative_adjacent parity n fuel state]
  rfl

theorem actual_fast_local_fact (parity : TetrahedralInputParity) (n fuel : Nat)
    (state : OccurrenceAuxState) :
    occurrenceFact? (expanded parity n) (fuel + 2) state (canonicalCenterRoot 0) =
      some (actualLocalFact parity) := by
  rw [actual_fast_dispatch_legacy]
  have observed := expanded_original_atom parity n 0 _ (raw_center parity n)
  have positions := actual_root_priority_positions parity n
  unfold runtimePriorityPositions? at positions
  rw [actual_center_ligands] at positions
  have first := (actual_root_priority_callbacks parity n fuel state 0 1 (by decide)).1
  have middle := (actual_root_priority_callbacks parity n fuel state 1 2 (by decide)).1
  have last := (actual_root_priority_callbacks parity n fuel state 2 3 (by decide)).1
  dsimp only [priorityCursor] at first middle last
  change _ = some ({ ordering := Ordering.gt } : OccurrenceComparison) at first
  change _ = some ({ ordering := Ordering.gt } : OccurrenceComparison) at middle
  change _ = some ({ ordering := Ordering.gt } : OccurrenceComparison) at last
  simp only [legacyOccurrenceFact?, show (canonicalCenterRoot 0).atom = 0 from rfl,
    observed, Bind.bind, Option.bind, materializedAtomSpec, centerSpec,
    actual_center_ligands, actual_center_occurrence_frame,
    (actual_root_tracked_sort parity n fuel state).1, positions]
  simp only [orderedRootCursors, compareOccurrenceAdjacentPairs?, first, middle, last]
  rfl

theorem actual_local_runtime_fuel (parity : TetrahedralInputParity) (n : Nat)
    (state : OccurrenceAuxState) :
    occurrenceFactAuthoritative? (expanded parity n) (runtimeFuel n) state
      (canonicalCenterRoot 0) = some (actualLocalFact parity) := by
  change occurrenceFactAuthoritative? _ ((6 * n + 28) + 2) _ _ = _
  exact actual_authoritative_local_fact parity n (6 * n + 28) state

/-- The public occurrence entry point consumes the actual finite collector and actual empty
auxiliary state. Initial seed/discovery conclusions are deliberately proved separately. -/
theorem actual_public_occurrence_fact (parity : TetrahedralInputParity) (n : Nat) :
    tetrahedralOccurrenceFact? (expanded parity n) (runtimeFuel n) 0 =
      some (recoveredPublicFact 0 [1, 2, 3, 0] (descriptorOfParity parity false)) := by
  exact public_fact_of_actual_local_fact _ _ 0 (expanded_only_center_tagged parity n)
    (actualCollectedNodes parity n) (actual_runtime_collector parity n) [1, 2, 3, 0]
    (descriptorOfParity parity false) (actual_local_runtime_fuel parity n [])

theorem actual_public_analysis_fuel (parity : TetrahedralInputParity) (n : Nat) :
    tetrahedralOccurrenceFactAuthoritative? (expanded parity n) (analysisFuel (expanded parity n)) 0 =
      some (recoveredPublicFact 0 [1, 2, 3, 0] (descriptorOfParity parity false)) := by
  have budget : runtimeFuel n = analysisFuel (expanded parity n) :=
    runtimeFuel_eq_public_budget parity n
  simpa only [budget] using actual_public_occurrence_fact parity n

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
