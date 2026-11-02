import TetraStereo.UniversalProof.NextFrontier.NativeRingRuntimeChildren

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingRuntimeSorting

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.NativeRingRuntimeGraphFacts
open TetraStereo.UniversalProof.NativeRingRuntimeAtoms
open TetraStereo.UniversalProof.NativeRingRuntimeChildren
open TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery
open TetraStereo.UniversalProof.NativeRingSingleBondChildren

/-- Share physical sorting arguments between the two actual constitutional comparators. -/
def childComparator (authoritative : Bool) (raw : RawMolecule) (fuel : Nat)
    (stage : CanonicalRuleStage) : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering :=
  if authoritative then compareCursorBranchAtAuthoritative? raw fuel stage
  else compareCursorBranchAt raw fuel stage

theorem child_comparison_of_z (authoritative : Bool) (raw : RawMolecule)
    (left right parent leftZ rightZ fuel : Nat) (stage : CanonicalRuleStage)
    (observedLeft : raw.atomZAt left = leftZ) (observedRight : raw.atomZAt right = rightZ)
    (different : leftZ ≠ rightZ) :
    childComparator authoritative raw fuel stage (armChild parent left) (armChild parent right) =
      some (compare leftZ rightZ) := by
  have distinct : raw.atomZAt (armChild parent left).node.atom ≠
      raw.atomZAt (armChild parent right).node.atom := by
    change raw.atomZAt left ≠ raw.atomZAt right
    rwa [observedLeft, observedRight]
  cases authoritative
  · have actual := compareCursorBranchAt_eq_of_rule1a raw (armChild parent left)
      (armChild parent right) rfl rfl distinct fuel stage
    simpa only [childComparator, Bool.false_eq_true, ↓reduceIte, armChild, awayCursor,
      pathNode, observedLeft, observedRight] using actual
  · have actual := compareCursorBranchAtAuthoritative?_eq_of_rule1a raw (armChild parent left)
      (armChild parent right) rfl rfl distinct fuel stage
    simpa only [childComparator, ↓reduceIte, armChild, awayCursor, pathNode,
      observedLeft, observedRight] using actual

theorem sort_strict_three (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (items : List CanonicalRerootCursor) (a b c : CanonicalRerootCursor)
    (permutation : items.Perm [a, b, c])
    (ab : before a b = some .gt) (ba : before b a = some .lt)
    (ac : before a c = some .gt) (ca : before c a = some .lt)
    (bc : before b c = some .gt) (cb : before c b = some .lt) :
    sortCursorsBy? before items = some [a, b, c] := by
  rcases perm_three_cases items a b c permutation with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sortCursorsBy?, insertCursorBy?,
      ab, ba, ac, ca, bc, cb]

theorem sort_three_tied_tail
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (items : List CanonicalRerootCursor) (a b c : CanonicalRerootCursor)
    (permutation : items.Perm [a, b, c])
    (ab : before a b = some .gt) (ba : before b a = some .lt)
    (ac : before a c = some .gt) (ca : before c a = some .lt)
    (bc : before b c = some .eq) (cb : before c b = some .eq) :
    sortCursorsBy? before items = some [a, b, c] ∨
      sortCursorsBy? before items = some [a, c, b] := by
  rcases perm_three_cases items a b c permutation with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sortCursorsBy?, insertCursorBy?,
      ab, ba, ac, ca, bc, cb, true_or, or_true]

theorem actual_left_sorted (n fuel : Nat) (parity : TetrahedralInputParity)
    (authoritative : Bool) (stage : CanonicalRuleStage) :
    sortCursorsBy? (childComparator authoritative (expanded n parity) fuel stage)
      ((rootCursor 2).children (expanded n parity)) =
        some [armChild 2 3, armChild 2 4, armChild 2 (n + 6)] := by
  have permutation := (actual_left_children n parity).trans
    (show [armChild 2 (n + 6), armChild 2 3, armChild 2 4].Perm
      [armChild 2 3, armChild 2 4, armChild 2 (n + 6)] from
        List.perm_append_comm (l₁ := [armChild 2 (n + 6)]) (l₂ := [armChild 2 3, armChild 2 4]))
  have chlorine := expanded_chlorine_z n parity
  have carbon := expanded_chain_z n parity 0 (by omega)
  have hydrogen := expanded_hydrogen_z n parity (n + 6) (by omega) (by omega)
  apply sort_strict_three _ _ _ _ _ permutation
  · exact child_comparison_of_z authoritative _ 3 4 2 17 6 fuel stage chlorine carbon (by decide)
  · exact child_comparison_of_z authoritative _ 4 3 2 6 17 fuel stage carbon chlorine (by decide)
  · exact child_comparison_of_z authoritative _ 3 (n + 6) 2 17 1 fuel stage chlorine hydrogen (by decide)
  · exact child_comparison_of_z authoritative _ (n + 6) 3 2 1 17 fuel stage hydrogen chlorine (by decide)
  · exact child_comparison_of_z authoritative _ 4 (n + 6) 2 6 1 fuel stage carbon hydrogen (by decide)
  · exact child_comparison_of_z authoritative _ (n + 6) 4 2 1 6 fuel stage hydrogen carbon (by decide)

theorem right_hydrogen_comparison (n fuel : Nat) (parity : TetrahedralInputParity)
    (authoritative : Bool) (stage : CanonicalRuleStage)
    (left right : Nat) (leftMember : left ∈ [3 * n + 7, 3 * n + 8])
    (rightMember : right ∈ [3 * n + 7, 3 * n + 8]) :
    childComparator authoritative (expanded n parity) fuel stage
      (armChild (n + 4) left) (armChild (n + 4) right) = some .eq := by
  have atoms : ∀ atom ∈ [3 * n + 7, 3 * n + 8], ObservedNaturalHydrogen (expanded n parity) atom := by
    intro atom member
    have lower : n + 5 ≤ atom := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> omega
    have upper : atom < 3 * n + 9 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> omega
    exact ⟨AtomSpec.aliphatic .H, expanded_fresh_hydrogen n parity atom lower upper, rfl, rfl⟩
  have rows : ∀ atom ∈ [3 * n + 7, 3 * n + 8],
      NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery.recordNeighbors (expanded n parity) atom = [n + 4] := by
    intro atom member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact (expanded_right_hydrogen_records n parity).1
    · exact (expanded_right_hydrogen_records n parity).2
  have single : ∀ atom ∈ [3 * n + 7, 3 * n + 8],
      (expanded n parity).bondOrder atom (n + 4) = 1 := by
    intro atom member
    apply expanded_record_bond_one n parity
    rw [rows atom member]
    exact List.mem_cons_self
  cases authoritative
  · exact physical_hydrogen_tie _ left right (n + 4) [0]
      (atoms left leftMember) (atoms right rightMember) (rows left leftMember) (rows right rightMember)
      (single left leftMember) (single right rightMember) fuel stage
  · exact physical_hydrogen_tie_authoritative _ left right (n + 4) [0]
      (atoms left leftMember) (atoms right rightMember) (rows left leftMember) (rows right rightMember)
      (single left leftMember) (single right rightMember) fuel stage

theorem actual_right_sorted (n fuel : Nat) (parity : TetrahedralInputParity)
    (authoritative : Bool) (stage : CanonicalRuleStage) :
    let before := childComparator authoritative (expanded n parity) fuel stage
    let children := (rootCursor (n + 4)).children (expanded n parity)
    sortCursorsBy? before children = some [armChild (n + 4) (rightPredecessor n),
      armChild (n + 4) (3 * n + 7), armChild (n + 4) (3 * n + 8)] ∨
    sortCursorsBy? before children = some [armChild (n + 4) (rightPredecessor n),
      armChild (n + 4) (3 * n + 8), armChild (n + 4) (3 * n + 7)] := by
  have carbon := expanded_right_predecessor_z n parity
  have firstH := expanded_hydrogen_z n parity (3 * n + 7) (by omega) (by omega)
  have secondH := expanded_hydrogen_z n parity (3 * n + 8) (by omega) (by omega)
  apply sort_three_tied_tail _ _ _ _ _ (actual_right_children n parity)
  · exact child_comparison_of_z authoritative _ (rightPredecessor n) (3 * n + 7) (n + 4)
      6 1 fuel stage carbon firstH (by decide)
  · exact child_comparison_of_z authoritative _ (3 * n + 7) (rightPredecessor n) (n + 4)
      1 6 fuel stage firstH carbon (by decide)
  · exact child_comparison_of_z authoritative _ (rightPredecessor n) (3 * n + 8) (n + 4)
      6 1 fuel stage carbon secondH (by decide)
  · exact child_comparison_of_z authoritative _ (3 * n + 8) (rightPredecessor n) (n + 4)
      1 6 fuel stage secondH carbon (by decide)
  · exact right_hydrogen_comparison n fuel parity authoritative stage _ _ (by simp) (by simp)
  · exact right_hydrogen_comparison n fuel parity authoritative stage _ _ (by simp) (by simp)

end TetraStereo.UniversalProof.NativeRingRuntimeSorting
