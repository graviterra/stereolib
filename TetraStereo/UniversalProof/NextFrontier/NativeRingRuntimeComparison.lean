import TetraStereo.UniversalProof.NextFrontier.NativeRingRuntimeSorting
import TetraStereo.UniversalProof.NextFrontier.NativeRingCycleGuard
import TetraStereo.UniversalProof.NextFrontier.NativeSecondSphereComparisonBridge

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingRuntimeComparison

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.NativeRingRuntimeAtoms
open TetraStereo.UniversalProof.NativeRingRuntimeChildren
open TetraStereo.UniversalProof.NativeRingRuntimeSorting
open TetraStereo.UniversalProof.NativeRingCycleGuard
open TetraStereo.UniversalProof.NativeSecondSphereComparisonBridge
open TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery
open TetraStereo.UniversalProof.NativeRingSingleBondChildren

/-- Actual Rule-1a node labels resolve the first child pair as Cl versus C. -/
theorem actual_fast_leading_labels (n : Nat) (parity : TetrahedralInputParity) :
    (expanded n parity).compareCanonicalNodeRule? .rule1a
      (armChild 2 3).node (armChild (n + 4) (rightPredecessor n)).node = some .gt ∧
    (expanded n parity).compareCanonicalNodeRule? .rule1a
      (armChild (n + 4) (rightPredecessor n)).node (armChild 2 3).node = some .lt := by
  have forward := compareCanonicalNodeRule?_rule1a_realAtom (expanded n parity)
    (armChild 2 3).node (armChild (n + 4) (rightPredecessor n)).node rfl rfl
  have reverse := compareCanonicalNodeRule?_rule1a_realAtom (expanded n parity)
    (armChild (n + 4) (rightPredecessor n)).node (armChild 2 3).node rfl rfl
  change _ = some (compare ((expanded n parity).atomZAt 3)
    ((expanded n parity).atomZAt (rightPredecessor n))) at forward
  change _ = some (compare ((expanded n parity).atomZAt (rightPredecessor n))
    ((expanded n parity).atomZAt 3)) at reverse
  have predecessorZ : (expanded n parity).atomZAt (rightPredecessor n) = 6 :=
    expanded_right_predecessor_z n parity
  rw [expanded_chlorine_z, predecessorZ] at forward reverse
  exact ⟨forward, reverse⟩

theorem actual_authoritative_leading_labels (n : Nat) (parity : TetrahedralInputParity) :
    (expanded n parity).compareCanonicalNodeRuleAuthoritative? .rule1a
      (armChild 2 3).node (armChild (n + 4) (rightPredecessor n)).node = some .gt ∧
    (expanded n parity).compareCanonicalNodeRuleAuthoritative? .rule1a
      (armChild (n + 4) (rightPredecessor n)).node (armChild 2 3).node = some .lt := by
  have forward := compareCanonicalNodeRuleAuthoritative?_rule1a_realAtom (expanded n parity)
    (armChild 2 3).node (armChild (n + 4) (rightPredecessor n)).node rfl rfl
  have reverse := compareCanonicalNodeRuleAuthoritative?_rule1a_realAtom (expanded n parity)
    (armChild (n + 4) (rightPredecessor n)).node (armChild 2 3).node rfl rfl
  change _ = some (compare ((expanded n parity).atomZAt 3)
    ((expanded n parity).atomZAt (rightPredecessor n))) at forward
  change _ = some (compare ((expanded n parity).atomZAt (rightPredecessor n))
    ((expanded n parity).atomZAt 3)) at reverse
  have predecessorZ : (expanded n parity).atomZAt (rightPredecessor n) = 6 :=
    expanded_right_predecessor_z n parity
  rw [expanded_chlorine_z, predecessorZ] at forward reverse
  exact ⟨forward, reverse⟩

/-- Both actual constitutional algorithms distinguish the tied carbon arms on their first
expanded sphere. Arbitrary ring length remains outside the fixed three-child sorting proof. -/
theorem actual_raw_both (n fuel : Nat) (parity : TetrahedralInputParity)
    (authoritative : Bool) (stage : CanonicalRuleStage) :
    childComparator authoritative (expanded n parity) (fuel + 1) stage
      (rootCursor 2) (rootCursor (n + 4)) = some .gt ∧
    childComparator authoritative (expanded n parity) (fuel + 1) stage
      (rootCursor (n + 4)) (rootCursor 2) = some .lt := by
  have leftSort := actual_left_sorted n fuel parity authoritative stage
  obtain ⟨firstH, secondH, rightSort⟩ : ∃ firstH secondH,
      sortCursorsBy? (childComparator authoritative (expanded n parity) fuel stage)
        ((rootCursor (n + 4)).children (expanded n parity)) =
          some [armChild (n + 4) (rightPredecessor n), firstH, secondH] := by
    rcases actual_right_sorted n fuel parity authoritative stage with ordered | ordered
    · exact ⟨_, _, ordered⟩
    · exact ⟨_, _, ordered⟩
  have leftCount : ((rootCursor 2).children (expanded n parity)).length = 3 :=
    (actual_left_children n parity).length_eq
  have rightCount : ((rootCursor (n + 4)).children (expanded n parity)).length = 3 :=
    (actual_right_children n parity).length_eq
  have sameZ : (expanded n parity).atomZAt (rootCursor 2).node.atom =
      (expanded n parity).atomZAt (rootCursor (n + 4)).node.atom :=
    (expanded_left_z n parity).trans (expanded_chain_z n parity n (Nat.le_refl _)).symm
  have nonterminal := actual_arms_nonterminal n parity
  cases authoritative with
  | false =>
      have leftRank := ranked_fast_of_sort_three _ _ _ _ _ _ leftCount leftSort
      have rightRank := ranked_fast_of_sort_three _ _ _ _ _ _ rightCount rightSort
      have labels := actual_fast_leading_labels n parity
      constructor
      · exact fast_raw_of_ranked_three _ fuel stage _ _ _ _ _ _ _ _ .gt rfl rfl sameZ
          nonterminal.1 nonterminal.2 leftRank rightRank (.head _ _ _ labels.1) (by decide)
      · exact fast_raw_of_ranked_three _ fuel stage _ _ _ _ _ _ _ _ .lt rfl rfl sameZ.symm
          nonterminal.2 nonterminal.1 rightRank leftRank (.head _ _ _ labels.2) (by decide)
  | true =>
      have leftRank := ranked_authoritative_of_sort_three _ _ _ _ _ _ leftCount leftSort
      have rightRank := ranked_authoritative_of_sort_three _ _ _ _ _ _ rightCount rightSort
      have labels := actual_authoritative_leading_labels n parity
      constructor
      · exact authoritative_raw_of_ranked_three _ fuel stage _ _ _ _ _ _ _ _ .gt rfl rfl sameZ
          nonterminal.1 nonterminal.2 leftRank rightRank (.head _ _ _ labels.1) (by decide)
      · exact authoritative_raw_of_ranked_three _ fuel stage _ _ _ _ _ _ _ _ .lt rfl rfl sameZ.symm
          nonterminal.2 nonterminal.1 rightRank leftRank (.head _ _ _ labels.2) (by decide)

/-- The actual root cycle disables the incompatible atom-swap veto for every pair in this frame. -/
theorem actual_root_guard (n fuel : Nat) (parity : TetrahedralInputParity)
    (left right : Nat) (decision : Ordering) (enough : n + 1 ≤ fuel) :
    occurrenceRootsProvedAutomorphic (expanded n parity) fuel
      (rootCursor left) (rootCursor right) decision = false := by
  have cyclic := actual_root_cycle n fuel parity enough
  simp [occurrenceRootsProvedAutomorphic, rootCursor, awayCursor, pathNode, cyclic]

theorem actual_certified_both (n fuel : Nat) (parity : TetrahedralInputParity)
    (enough : n ≤ fuel) :
    certifiedConstitutionalStage? (expanded n parity) (fuel + 1)
      (rootCursor 2) (rootCursor (n + 4)) = some .gt ∧
    certifiedConstitutionalStage? (expanded n parity) (fuel + 1)
      (rootCursor (n + 4)) (rootCursor 2) = some .lt := by
  have strict := actual_raw_both n fuel parity false .rule2
  change compareCursorBranchAt _ _ _ _ _ = _ ∧ compareCursorBranchAt _ _ _ _ _ = _ at strict
  simp [certifiedConstitutionalStage?, strict.1, strict.2,
    actual_root_guard n (fuel + 1) parity 2 (n + 4) .gt (by omega),
    actual_root_guard n (fuel + 1) parity (n + 4) 2 .lt (by omega)]

theorem actual_complete_both (n fuel : Nat) (parity : TetrahedralInputParity)
    (state : OccurrenceAuxState) (enough : n ≤ fuel) :
    compareOccurrenceBranchesComplete? (expanded n parity) state (fuel + 1)
      (rootCursor 2) (rootCursor (n + 4)) = some { ordering := Ordering.gt } ∧
    compareOccurrenceBranchesComplete? (expanded n parity) state (fuel + 1)
      (rootCursor (n + 4)) (rootCursor 2) = some { ordering := Ordering.lt } := by
  have certified := actual_certified_both n fuel parity enough
  simp [compareOccurrenceBranchesComplete?, compareOccurrenceBranches?, certified.1, certified.2]

end TetraStereo.UniversalProof.NativeRingRuntimeComparison
