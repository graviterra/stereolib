import TetraStereo.OneCenter.LocalizedChemicalRingSelectedStabilizer
import TetraStereo.OneCenter.LocalizedChemicalRingMovedSlotEligibility
import TetraStereo.OneCenter.Rule6Proposed2018PromotionFidelity
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! Finite obstructions used by final-root source applicability. These statements do not
assert molecular transport or source-policy correspondence. In particular, two tied pairs
are allowed; the obstruction is a single pair and two singleton classes. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingRootApplicabilityFinite

open DeclarativeCIP.ProductionOccurrenceRules456
open LocalizedMarkedRetainedOrdinaryRanking

private theorem code_only_pair : ∀ (key : Fin 4 → Fin 4) (left right : Fin 4),
    left ≠ right → key left = key right →
    sourceRule6Applicable (rule6GroupSizes
      (adjacentBy (fun a b => some (compare (key a) (key b)))
        (keyOrder key (List.finRange 4)))) = false →
    ∀ a b, a ≠ b → key a = key b →
      (a = left ∧ b = right) ∨ (a = right ∧ b = left) := by
  decide +kernel

/-- Four arbitrary ordered keys admit a four-value order code, constructed from lower-set
cardinalities rather than a supplied sort or partition. -/
theorem exists_order_code {Key : Type*} [LinearOrder Key] (key : Fin 4 → Key) :
    ∃ code : Fin 4 → Fin 4, ∀ i j, key i < key j ↔ code i < code j := by
  classical
  let lower (i : Fin 4) := Finset.univ.filter (fun j => key j < key i)
  have bounded (i : Fin 4) : (lower i).card < 4 := by
    have proper : lower i ⊂ Finset.univ := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.subset_univ _, ?_⟩
      intro equal
      have member : i ∈ lower i := by rw [equal]; exact Finset.mem_univ i
      simp [lower] at member
    simpa using Finset.card_lt_card proper
  let code (i : Fin 4) : Fin 4 := ⟨(lower i).card, bounded i⟩
  have increasing (i j : Fin 4) (less : key i < key j) : code i < code j := by
    change (lower i).card < (lower j).card
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro k hk
      simp only [lower, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact lt_trans hk less
    · intro equal
      have member : i ∈ lower j := by simpa [lower] using less
      rw [← equal] at member
      simp [lower] at member
  refine ⟨code, fun i j => ⟨increasing i j, ?_⟩⟩
  intro less
  by_contra notLess
  rcases lt_or_eq_of_le (le_of_not_gt notLess) with greater | equal
  · exact (not_lt_of_gt (increasing j i greater)) less
  · have same : code i = code j := by simp only [code, lower, equal]
    exact (ne_of_lt less) same

/-- An inapplicable actual sorted key partition containing a tie has no other tied pair. -/
theorem only_pair_of_inapplicable {Key : Type} [LinearOrder Key]
    (cmp : Key → Key → Ordering)
    (lt_iff : ∀ a b, cmp a b = .lt ↔ a < b)
    (eq_iff : ∀ a b, cmp a b = .eq ↔ a = b)
    (key : Fin 4 → Key) (left right : Fin 4)
    (different : left ≠ right) (tied : key left = key right)
    (inapplicable : sourceRule6Applicable (rule6GroupSizes
      (adjacentBy (fun a b => some (cmp (key a) (key b)))
        (keyOrder key (List.finRange 4)))) = false) :
    ∀ a b, a ≠ b → key a = key b →
      (a = left ∧ b = right) ∨ (a = right ∧ b = left) := by
  obtain ⟨code, order⟩ := exists_order_code key
  have equal (a b : Fin 4) : key a = key b ↔ code a = code b := by
    rw [le_antisymm_iff, le_antisymm_iff]
    simp only [← not_lt, order]
  have comparison (a b : Fin 4) : cmp (key a) (key b) = compare (code a) (code b) := by
    rcases lt_trichotomy (key a) (key b) with less | same | greater
    · rw [(lt_iff _ _).mpr less, (compare_lt_iff_lt).mpr ((order a b).mp less)]
    · rw [(eq_iff _ _).mpr same, (compare_eq_iff_eq).mpr ((equal a b).mp same)]
    · rw [(cmp_gt_iff cmp lt_iff eq_iff _ _).mpr greater,
        (compare_gt_iff_gt).mpr ((order b a).mp greater)]
  have comparisons : (fun a b => some (cmp (key a) (key b))) =
      (fun a b => some (compare (code a) (code b))) := by
    funext a b
    exact congrArg some (comparison a b)
  have sorts : keyOrder key (List.finRange 4) = keyOrder code (List.finRange 4) := by
    have first := sortBy?_key cmp lt_iff key (List.finRange 4)
    have second := sortBy?_key compare (fun _ _ : Fin 4 => compare_lt_iff_lt) code (List.finRange 4)
    rw [comparisons] at first
    exact Option.some.inj (first.symm.trans second)
  rw [comparisons, sorts] at inapplicable
  intro a b distinct tie
  exact code_only_pair code left right different ((equal left right).mp tied)
    inapplicable a b distinct ((equal a b).mp tie)

/-- Exact enumeration of the allowed nonstrict four-slot partitions. -/
theorem applicable_adjacent_iff (a b c : Option Ordering) :
    sourceRule6Applicable (rule6GroupSizes [a, b, c]) = true ↔
      rule6GroupSizes [a, b, c] = [2, 2] ∨
      rule6GroupSizes [a, b, c] = [3, 1] ∨
      rule6GroupSizes [a, b, c] = [1, 3] ∨
      rule6GroupSizes [a, b, c] = [4] := by
  revert a b c
  decide +kernel

/-- With a tie present, every excluded four-slot partition has exactly one pair. Missing
or reversed comparison outcomes are treated as separating boundaries by `rule6GroupSizes`.
The molecular consumer must separately derive valid adjacent comparisons. -/
theorem inapplicable_tied_adjacent_iff (a b c : Option Ordering)
    (tied : a = some .eq ∨ b = some .eq ∨ c = some .eq) :
    sourceRule6Applicable (rule6GroupSizes [a, b, c]) = false ↔
      rule6GroupSizes [a, b, c] = [2, 1, 1] ∨
      rule6GroupSizes [a, b, c] = [1, 2, 1] ∨
      rule6GroupSizes [a, b, c] = [1, 1, 2] := by
  revert a b c
  decide +kernel

private theorem odd_of_fixed_complement :
    ∀ (p : Equiv.Perm (Fin 4)) (left right : Fin 4),
      left ≠ right → p left ≠ left →
      (∀ i, i ≠ left → i ≠ right → p i = i) → permHandedness p = -1 := by
  intro p left right different moves fixed
  have finite : ∀ (q : Equiv.Perm (Fin 4)) (a b : Fin 4),
      a ≠ b → q a ≠ a → (∀ i, i ≠ a → i ≠ b → q i = i) → q.sign = -1 := by
    decide +kernel
  simp [permHandedness, finite p left right different moves fixed]

/-- Any key-preserving action moving the sole tied pair is odd. This excludes a lone pair
without excluding the valid two-pair partition. Actual root symmetry reconstruction and
current-key preservation remain the responsibility of the molecular theorem. -/
theorem lone_pair_action_odd {Key : Type*} (key : Fin 4 → Key)
    (p : Equiv.Perm (Fin 4)) (left right : Fin 4)
    (different : left ≠ right) (moves : p left ≠ left)
    (preserves : ∀ i, key (p i) = key i)
    (onlyPair : ∀ a b, a ≠ b → key a = key b →
      (a = left ∧ b = right) ∨ (a = right ∧ b = left)) :
    permHandedness p = -1 := by
  apply odd_of_fixed_complement p left right different moves
  intro i outsideLeft outsideRight
  by_contra moved
  rcases onlyPair (p i) i moved (preserves i) with first | second
  · exact outsideRight first.2
  · exact outsideLeft second.2

/-- A key-comparison covariant molecular action is enough for the lone-pair obstruction. -/
theorem lone_pair_action_odd_of_order {Key : Type*} [LinearOrder Key]
    (key : Fin 4 → Key) (p : Equiv.Perm (Fin 4)) (left right : Fin 4)
    (different : left ≠ right) (moves : p left ≠ left)
    (order : ∀ i j, key (p i) < key (p j) ↔ key i < key j)
    (onlyPair : ∀ a b, a ≠ b → key a = key b →
      (a = left ∧ b = right) ∨ (a = right ∧ b = left)) :
    permHandedness p = -1 := by
  exact lone_pair_action_odd key p left right different moves
    (fun i => LocalizedChemicalRingMovedSlotEligibility.key_fixed_of_order_action
      key p (fun a b h => (order a b).mpr h) i) onlyPair

end TetraStereo.OneCenter.LocalizedChemicalRingRootApplicabilityFinite

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootApplicabilityFinite.applicable_adjacent_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootApplicabilityFinite.exists_order_code
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootApplicabilityFinite.only_pair_of_inapplicable
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootApplicabilityFinite.inapplicable_tied_adjacent_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootApplicabilityFinite.lone_pair_action_odd
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootApplicabilityFinite.lone_pair_action_odd_of_order
