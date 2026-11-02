import TetraStereo.UniversalProof.NextFrontier.NativeNitrileRecordGeometry
import TetraStereo.UniversalProof.TerminalStarCycleGuard

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.TerminalStarCycleGuard

theorem expanded_nitrogen_written_row (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).writtenNeighbors 3 = [2] := by
  have ids : materializedHydrogenIds (raw parity n) 3 = [] := by
    simp [materializedHydrogenIds, (raw_nitrile_hydrogens parity n).2]
  rw [expanded, withExplicitHydrogens_writtenNeighbors _ (raw_wellFormed parity n)
    (raw_written_exact parity n) 3 (by rw [raw_atomCount]; omega)]
  rw [materializedWrittenRow, ids]
  rfl

theorem expanded_nitrogen_records (parity : TetrahedralInputParity) (n : Nat) :
    recordNeighbors (expanded parity n) 3 = [2] := by
  apply List.Perm.eq_singleton
  simpa only [expanded_nitrogen_written_row] using expanded_record_row parity n 3 (by omega)

private theorem nitrogen_blocked_neighbors (parity : TetrahedralInputParity) (n : Nat) :
    blockedNeighbors (expanded parity n) 2 3 = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro neighbor member
  have facts := blockedNeighbors_member (expanded parity n) 2 3 neighbor member
  have same : neighbor = 2 := by
    simpa only [expanded_nitrogen_records, List.mem_singleton] using facts.1
  exact facts.2 same

theorem expanded_reach_from_nitrogen (parity : TetrahedralInputParity) (n fuel : Nat) :
    (expanded parity n).reachableAvoiding fuel 2 [3] [3] = [3] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      change (expanded parity n).reachableAvoiding fuel 2
        ((((blockedNeighbors (expanded parity n) 2 3) ++ []).filter
          (fun atom => !([3] : List Nat).contains atom)).eraseDups)
        ([3] ++ (((blockedNeighbors (expanded parity n) 2 3 ++ []).filter
          (fun atom => !([3] : List Nat).contains atom)).eraseDups)) = [3]
      rw [nitrogen_blocked_neighbors]
      cases fuel <;> rfl

/-- The physical nitrile carbon is acyclic at every production traversal budget. Its two
neighbors are the center and terminal nitrogen; multiplicity does not create a graph cycle. -/
theorem expanded_nitrile_acyclic (parity : TetrahedralInputParity) (n fuel : Nat) :
    (expanded parity n).atomLiesInCycle fuel 2 = false := by
  have rows : (recordNeighbors (expanded parity n) 2).Perm [0, 3] := by
    simpa only [expanded_nitrile_row] using expanded_record_row parity n 2 (by omega)
  have incident : (expanded parity n).incidentAtoms 2 = recordNeighbors (expanded parity n) 2 := by
    rw [incidentAtoms_eq_recordNeighbors_eraseDups]
    exact eraseDups_eq_self_of_nodup _ (expanded_records_nodup parity n 2)
  have forward := reachableAvoiding_singleton_contains_terminal_false (expanded parity n)
    (expanded_admissible parity n).1 2 3 0 fuel (expanded_nitrogen_records parity n)
    (by decide) (by decide)
  have reverse : ((expanded parity n).reachableAvoiding fuel 2 [3] [3]).contains 0 = false := by
    rw [expanded_reach_from_nitrogen]
    rfl
  have noForward : 3 ∉ (expanded parity n).reachableAvoiding fuel 2 [0] [0] := by
    simpa using forward
  have noReverse : 0 ∉ (expanded parity n).reachableAvoiding fuel 2 [3] [3] := by
    simpa using reverse
  have retained := List.mem_permutations'.mpr rows
  change recordNeighbors (expanded parity n) 2 ∈ [[0, 3], [3, 0]] at retained
  simp only [List.mem_cons, List.not_mem_nil, or_false] at retained
  rcases retained with orderEq | orderEq <;>
    simp [atomLiesInCycle, incident, orderEq, ringPairCount, List.range_succ, noForward, noReverse]

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
