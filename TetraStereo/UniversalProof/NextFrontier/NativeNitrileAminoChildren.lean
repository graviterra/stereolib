import TetraStereo.UniversalProof.NextFrontier.NativeNitrileRecordGeometry
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileAtomicLabels
import TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery
open TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge

def aminoCursor : CanonicalRerootCursor := awayCursor 4 0 []

def aminoChild (atom : Nat) : CanonicalRerootCursor := awayCursor atom 4 [0]

private theorem amino_filter_children (children : List Nat)
    (fresh : ∀ atom ∈ children, atom ≠ 0) :
    ((children.map fun atom => pathNode atom [4, 0]).filterMap
      fun neighbor => if neighbor == pathNode 0 [] then none
        else some ({ node := neighbor, previous? := some (pathNode 4 [0]) } :
          CanonicalRerootCursor)) = children.map aminoChild := by
  induction children with
  | nil => rfl
  | cons head tail ih =>
      have different := pathNode_ne head 0 [4, 0] [] (fresh head List.mem_cons_self)
      simp only [List.map_cons, List.filterMap_cons, beq_eq_false_iff_ne.mpr different,
        Bool.false_eq_true, ↓reduceIte]
      rw [ih (by intro atom member; exact fresh atom (List.mem_cons_of_mem head member))]
      rfl

theorem actual_amino_children (parity : TetrahedralInputParity) (n : Nat) :
    (aminoCursor.children (expanded parity n)).Perm
      [aminoChild (n + 8), aminoChild 5, aminoChild 6] := by
  let physical := (recordNeighbors (expanded parity n) 4).erase 0
  have projected : physical.Perm [n + 8, 5, 6] := by
    simpa using (expanded_amino_records parity n).erase 0
  have fresh : ∀ atom ∈ physical, atom ∉ [4, 0] := by
    intro atom retained
    have member := projected.mem_iff.mp retained
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      omega
    · decide
    · decide
  have actual := actual_path_children (expanded parity n) 4 0 [] physical rfl
    (fun other retained => expanded_record_order_one parity n 4 other
      (by decide) (by decide) retained) fresh
  have forced : (pathNode 4 [0]).forcedLeaf = false := rfl
  have children : aminoCursor.children (expanded parity n) = physical.map aminoChild := by
    simp only [aminoCursor, awayCursor, CanonicalRerootCursor.children,
      CanonicalRerootCursor.neighbors, forced,
      Bool.false_eq_true, ↓reduceIte, originalParent_pathNode, actual,
      Option.toList_some, List.singleton_append, List.filterMap_cons, beq_self_eq_true]
    exact amino_filter_children physical (by
      intro atom member same
      subst atom
      exact fresh 0 member (by simp))
  rw [children]
  exact projected.map aminoChild

theorem actual_amino_nonterminal (parity : TetrahedralInputParity) (n : Nat) :
    cursorTerminal (expanded parity n) aminoCursor = false := by
  have count := (actual_amino_children parity n).length_eq
  have nonempty : aminoCursor.children (expanded parity n) ≠ [] := by
    intro empty
    rw [empty] at count
    cases count
  change (false || (aminoCursor.children (expanded parity n)).isEmpty) = false
  simpa only [Bool.false_or, List.isEmpty_eq_false_iff] using nonempty

private theorem amino_pair_compare (parity : TetrahedralInputParity) (n fuel : Nat)
    (stage : CanonicalRuleStage) (left right leftZ rightZ : Nat)
    (leftObserved : (expanded parity n).atomZAt left = leftZ)
    (rightObserved : (expanded parity n).atomZAt right = rightZ)
    (distinct : leftZ ≠ rightZ) :
    compareCursorBranchAt (expanded parity n) fuel stage (aminoChild left) (aminoChild right) =
        some (compare leftZ rightZ) ∧
      compareCursorBranchAtAuthoritative? (expanded parity n) fuel stage
        (aminoChild left) (aminoChild right) = some (compare leftZ rightZ) := by
  have different : (expanded parity n).atomZAt (aminoChild left).node.atom ≠
      (expanded parity n).atomZAt (aminoChild right).node.atom := by
    change (expanded parity n).atomZAt left ≠ (expanded parity n).atomZAt right
    rw [leftObserved, rightObserved]
    exact distinct
  have fast := compareCursorBranchAt_eq_of_rule1a (expanded parity n)
    (aminoChild left) (aminoChild right) rfl rfl different fuel stage
  have authoritative := compareCursorBranchAtAuthoritative?_eq_of_rule1a (expanded parity n)
    (aminoChild left) (aminoChild right) rfl rfl different fuel stage
  simpa only [aminoChild, awayCursor, pathNode, leftObserved, rightObserved] using
    And.intro fast authoritative

private theorem amino_permutation_cases {Alpha : Type} (items : List Alpha) (a b c : Alpha)
    (permutation : items.Perm [a, b, c]) :
    items = [a, b, c] ∨ items = [b, a, c] ∨ items = [b, c, a] ∨
      items = [a, c, b] ∨ items = [c, a, b] ∨ items = [c, b, a] := by
  have retained := List.mem_permutations'.mpr permutation
  change items ∈ [[a, b, c], [b, a, c], [b, c, a], [a, c, b], [c, a, b], [c, b, a]] at retained
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using retained

/-- Actual aminoalkyl children sort as N, C, H at every fuel and stage, including the n=0
terminal methyl endpoint. Sorting is derived for every physical bond-list permutation. -/
theorem actual_amino_sibling_sort (parity : TetrahedralInputParity) (n fuel : Nat)
    (stage : CanonicalRuleStage) :
    sortCursorsBy? (compareCursorBranchAt (expanded parity n) fuel stage)
        (aminoCursor.children (expanded parity n)) =
        some [aminoChild 5, aminoChild 6, aminoChild (n + 8)] ∧
      sortCursorsBy? (compareCursorBranchAtAuthoritative? (expanded parity n) fuel stage)
        (aminoCursor.children (expanded parity n)) =
        some [aminoChild 5, aminoChild 6, aminoChild (n + 8)] := by
  rcases expanded_local_atomic_numbers parity n with
    ⟨_, _, _, _, _, nitrogen, carbon, _, hydrogen⟩
  have nc := amino_pair_compare parity n fuel stage 5 6 7 6 nitrogen carbon (by decide)
  have nh := amino_pair_compare parity n fuel stage 5 (n + 8) 7 1 nitrogen hydrogen (by decide)
  have ch := amino_pair_compare parity n fuel stage 6 (n + 8) 6 1 carbon hydrogen (by decide)
  have cn := amino_pair_compare parity n fuel stage 6 5 6 7 carbon nitrogen (by decide)
  have hn := amino_pair_compare parity n fuel stage (n + 8) 5 1 7 hydrogen nitrogen (by decide)
  have hc := amino_pair_compare parity n fuel stage (n + 8) 6 1 6 hydrogen carbon (by decide)
  change (_ = some Ordering.gt) ∧ (_ = some Ordering.gt) at nc
  change (_ = some Ordering.gt) ∧ (_ = some Ordering.gt) at nh
  change (_ = some Ordering.gt) ∧ (_ = some Ordering.gt) at ch
  change (_ = some Ordering.lt) ∧ (_ = some Ordering.lt) at cn
  change (_ = some Ordering.lt) ∧ (_ = some Ordering.lt) at hn
  change (_ = some Ordering.lt) ∧ (_ = some Ordering.lt) at hc
  rcases amino_permutation_cases _ _ _ _ (actual_amino_children parity n) with
    orderEq | orderEq | orderEq | orderEq | orderEq | orderEq
  all_goals
    simp [orderEq, sortCursorsBy?, insertCursorBy?,
      nc.1, nc.2, nh.1, nh.2, ch.1, ch.2, cn.1, cn.2, hn.1, hn.2, hc.1, hc.2]

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
