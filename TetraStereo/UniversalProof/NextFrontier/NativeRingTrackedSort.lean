import TetraStereo.UniversalProof.NextFrontier.NativeRingRuntimeComparison
import TetraStereo.UniversalProof.NextFrontier.NativeRingRuntimeRoot

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingTrackedSort

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.NativeRingRuntimeAtoms
open TetraStereo.UniversalProof.NativeRingRuntimeChildren
open TetraStereo.UniversalProof.NativeRingRuntimeRoot
open TetraStereo.UniversalProof.NativeRingRuntimeComparison
open TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery

theorem actual_unequal_root_comparison (n fuel : Nat) (parity : TetrahedralInputParity)
    (state : OccurrenceAuxState) (left right leftZ rightZ : Nat)
    (observedLeft : (expanded n parity).atomZAt left = leftZ)
    (observedRight : (expanded n parity).atomZAt right = rightZ)
    (different : leftZ ≠ rightZ) (enough : n + 1 ≤ fuel) :
    compareOccurrenceBranchesComplete? (expanded n parity) state fuel
      (rootCursor left) (rootCursor right) = some { ordering := compare leftZ rightZ } := by
  have distinct : (expanded n parity).atomZAt (rootCursor left).node.atom ≠
      (expanded n parity).atomZAt (rootCursor right).node.atom := by
    change (expanded n parity).atomZAt left ≠ (expanded n parity).atomZAt right
    rwa [observedLeft, observedRight]
  have raw := compareCursorBranchAt_eq_of_rule1a (expanded n parity)
    (rootCursor left) (rootCursor right) rfl rfl distinct fuel .rule2
  change _ = some (compare ((expanded n parity).atomZAt left)
    ((expanded n parity).atomZAt right)) at raw
  rw [observedLeft, observedRight] at raw
  have strict : compare leftZ rightZ ≠ Ordering.eq := fun equal => different (Nat.compare_eq_eq.mp equal)
  have guard := actual_root_guard n fuel parity left right (compare leftZ rightZ) enough
  simp [compareOccurrenceBranchesComplete?, compareOccurrenceBranches?,
    certifiedConstitutionalStage?, raw, guard, strict]

/-- Exhaustion concerns only the four positions of one tetrahedral frame. The molecule and
comparison budget remain parameters; no finite ring sample enters the result. -/
theorem actual_strict_four_sort (raw : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (items : List CanonicalRerootCursor) (a b c d : CanonicalRerootCursor)
    (permutation : items.Perm [a, b, c, d])
    (ab : compareOccurrenceBranchesComplete? raw state fuel a b = some { ordering := .gt })
    (ba : compareOccurrenceBranchesComplete? raw state fuel b a = some { ordering := .lt })
    (ac : compareOccurrenceBranchesComplete? raw state fuel a c = some { ordering := .gt })
    (ca : compareOccurrenceBranchesComplete? raw state fuel c a = some { ordering := .lt })
    (ad : compareOccurrenceBranchesComplete? raw state fuel a d = some { ordering := .gt })
    (da : compareOccurrenceBranchesComplete? raw state fuel d a = some { ordering := .lt })
    (bc : compareOccurrenceBranchesComplete? raw state fuel b c = some { ordering := .gt })
    (cb : compareOccurrenceBranchesComplete? raw state fuel c b = some { ordering := .lt })
    (bd : compareOccurrenceBranchesComplete? raw state fuel b d = some { ordering := .gt })
    (db : compareOccurrenceBranchesComplete? raw state fuel d b = some { ordering := .lt })
    (cd : compareOccurrenceBranchesComplete? raw state fuel c d = some { ordering := .gt })
    (dc : compareOccurrenceBranchesComplete? raw state fuel d c = some { ordering := .lt }) :
    sortOccurrencesTrackedAuthoritative? raw state fuel items = some ([a, b, c, d], 0) := by
  have member := List.mem_permutations'.mpr permutation
  simp only [List.permutations', List.permutations'Aux, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp_all [sortOccurrencesTrackedAuthoritative?, insertOccurrenceTrackedAuthoritative?]

theorem actual_tracked_sort (n fuel : Nat) (parity : TetrahedralInputParity)
    (state : OccurrenceAuxState) (enough : n ≤ fuel) :
    sortOccurrencesTrackedAuthoritative? (expanded n parity) state (fuel + 1)
      (physicalRoots n parity) = some (orderedRoots n, 0) := by
  have permutation := (physical_roots_perm n parity).trans
    (List.perm_append_comm (l₁ := [rootCursor (n + 5)])
      (l₂ := [rootCursor 1, rootCursor 2, rootCursor (n + 4)]))
  have fluorine := expanded_fluorine_z n parity
  have left := expanded_left_z n parity
  have right := expanded_chain_z n parity n (Nat.le_refl _)
  have hydrogen := expanded_hydrogen_z n parity (n + 5) (by omega) (by omega)
  have carbons := actual_complete_both n fuel parity state enough
  apply actual_strict_four_sort _ _ _ _ _ _ _ _ permutation
  · exact actual_unequal_root_comparison n _ parity state 1 2 9 6 fluorine left (by decide) (by omega)
  · exact actual_unequal_root_comparison n _ parity state 2 1 6 9 left fluorine (by decide) (by omega)
  · exact actual_unequal_root_comparison n _ parity state 1 (n + 4) 9 6 fluorine right (by decide) (by omega)
  · exact actual_unequal_root_comparison n _ parity state (n + 4) 1 6 9 right fluorine (by decide) (by omega)
  · exact actual_unequal_root_comparison n _ parity state 1 (n + 5) 9 1 fluorine hydrogen (by decide) (by omega)
  · exact actual_unequal_root_comparison n _ parity state (n + 5) 1 1 9 hydrogen fluorine (by decide) (by omega)
  · exact carbons.1
  · exact carbons.2
  · exact actual_unequal_root_comparison n _ parity state 2 (n + 5) 6 1 left hydrogen (by decide) (by omega)
  · exact actual_unequal_root_comparison n _ parity state (n + 5) 2 1 6 hydrogen left (by decide) (by omega)
  · exact actual_unequal_root_comparison n _ parity state (n + 4) (n + 5) 6 1 right hydrogen (by decide) (by omega)
  · exact actual_unequal_root_comparison n _ parity state (n + 5) (n + 4) 1 6 hydrogen right (by decide) (by omega)

theorem actual_adjacent (n fuel : Nat) (parity : TetrahedralInputParity)
    (state : OccurrenceAuxState) (enough : n ≤ fuel) :
    compareOccurrenceAdjacentPairsAuthoritative? (expanded n parity) state (fuel + 1)
      (orderedRoots n) =
        some [{ ordering := Ordering.gt }, { ordering := Ordering.gt }, { ordering := Ordering.gt }] := by
  have first := actual_unequal_root_comparison n (fuel + 1) parity state 1 2 9 6
    (expanded_fluorine_z n parity) (expanded_left_z n parity) (by decide) (by omega)
  have middle := (actual_complete_both n fuel parity state enough).1
  have last := actual_unequal_root_comparison n (fuel + 1) parity state (n + 4) (n + 5) 6 1
    (expanded_chain_z n parity n (Nat.le_refl _))
    (expanded_hydrogen_z n parity (n + 5) (by omega) (by omega)) (by decide) (by omega)
  simp [orderedRoots, compareOccurrenceAdjacentPairsAuthoritative?, first, middle, last]
  decide

end TetraStereo.UniversalProof.NativeRingTrackedSort
