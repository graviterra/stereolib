import TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking
import TetraStereo.OneCenter.Rule6Proposed2018PromotionFidelity
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Finite ordering connection for the three-equal-ligands case.  The molecular proof
supplies the key equalities; this module derives the actual sorted adjacent partition,
including its source applicability, without assuming a sorting result. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingThreeOnePartition

open LocalizedMarkedRetainedOrdinaryRanking
open DeclarativeCIP.ProductionOccurrenceRules456

private def classCode (parent : Fin 4) (high : Bool) (slot : Fin 4) : Nat :=
  if slot = parent then if high then 1 else 0 else if high then 0 else 1

private theorem code_partition : ∀ (parent : Fin 4) (high : Bool),
    let sizes := rule6GroupSizes
      (adjacentBy (fun a b => some (compare (classCode parent high a) (classCode parent high b)))
        (keyOrder (classCode parent high) (List.finRange 4)))
    sizes = [3, 1] ∨ sizes = [1, 3] := by
  decide +kernel

private theorem compare_congr_of_orders {K L : Type} [LinearOrder K] [LinearOrder L]
    (cmp : K → K → Ordering)
    (lt_iff : ∀ a b, cmp a b = .lt ↔ a < b)
    (eq_iff : ∀ a b, cmp a b = .eq ↔ a = b)
    (a b : K) (c d : L) (less : a < b ↔ c < d) (equal : a = b ↔ c = d) :
    cmp a b = compare c d := by
  rcases lt_trichotomy a b with lt | eq | gt
  · rw [(lt_iff a b).mpr lt, (compare_lt_iff_lt).mpr (less.mp lt)]
  · rw [(eq_iff a b).mpr eq, (compare_eq_iff_eq).mpr (equal.mp eq)]
  · have cd : d < c := lt_of_le_of_ne (le_of_not_gt (fun h => (not_lt_of_gt gt) (less.mpr h)))
      (fun h => (ne_of_gt gt) (equal.mpr h.symm))
    rw [(cmp_gt_iff cmp lt_iff eq_iff a b).mpr gt, (compare_gt_iff_gt).mpr cd]

section
variable {K : Type} [LinearOrder K]
  (cmp : K → K → Ordering)
  (lt_iff : ∀ a b, cmp a b = .lt ↔ a < b)
  (eq_iff : ∀ a b, cmp a b = .eq ↔ a = b)
  (key : Fin 4 → K) (parent other : Fin 4)
  (outsideEqual : ∀ slot, slot ≠ parent → key slot = key other)
  (separated : key other ≠ key parent)

include lt_iff eq_iff outsideEqual separated

/-- A separated singleton and three equal other keys produce exactly the two possible
three-plus-one sorted partitions. The ordering is the actual stable key sort. -/
theorem groupSizes_three_one :
    let sizes := rule6GroupSizes
      (adjacentBy (fun a b => some (cmp (key a) (key b)))
        (keyOrder key (List.finRange 4)))
    sizes = [3, 1] ∨ sizes = [1, 3] := by
  classical
  let high : Bool := decide (key other < key parent)
  let code := classCode parent high
  have rep (slot : Fin 4) : key slot = if slot = parent then key parent else key other := by
    split_ifs with equal
    · rw [equal]
    · exact outsideEqual slot equal
  have order (a b : Fin 4) : key a ≤ key b ↔ code a ≤ code b := by
    rw [rep a, rep b]
    by_cases senior : key other < key parent
    · by_cases ap : a = parent <;> by_cases bp : b = parent <;>
        simp [code, classCode, high, ap, bp, senior, le_of_lt senior, not_le_of_gt senior]
    · have junior : key parent < key other :=
        lt_of_le_of_ne (le_of_not_gt senior) separated.symm
      by_cases ap : a = parent <;> by_cases bp : b = parent <;>
        simp [code, classCode, high, ap, bp, senior, le_of_lt junior, not_le_of_gt junior]
  have eq (a b : Fin 4) : key a = key b ↔ code a = code b := by
    rw [le_antisymm_iff, le_antisymm_iff, order a b, order b a]
  have lt (a b : Fin 4) : key a < key b ↔ code a < code b := by
    rw [lt_iff_le_not_ge, lt_iff_le_not_ge, order a b, order b a]
  have compareEq : (fun a b => some (cmp (key a) (key b))) =
      (fun a b => some (compare (code a) (code b))) := by
    funext a b
    exact congrArg some (compare_congr_of_orders cmp lt_iff eq_iff
      (key a) (key b) (code a) (code b) (lt a b) (eq a b))
  have sortEq : keyOrder key (List.finRange 4) = keyOrder code (List.finRange 4) := by
    have first := sortBy?_key cmp lt_iff key (List.finRange 4)
    have second := sortBy?_key compare (fun _ _ : Nat => compare_lt_iff_lt) code (List.finRange 4)
    rw [compareEq] at first
    exact Option.some.inj (first.symm.trans second)
  dsimp only
  rw [compareEq, sortEq]
  exact code_partition parent high

/-- The derived actual sorted partition is in the proposed-2018 Rule 6 applicability domain. -/
theorem sourceApplicable_three_one :
    sourceRule6Applicable (rule6GroupSizes
      (adjacentBy (fun a b => some (cmp (key a) (key b)))
        (keyOrder key (List.finRange 4)))) = true := by
  rcases groupSizes_three_one cmp lt_iff eq_iff key parent other outsideEqual separated
    with first | second
  · rw [first, sourceRule6Applicable_threeOne]
  · rw [second, sourceRule6Applicable_oneThree]

end
end TetraStereo.OneCenter.LocalizedChemicalRingThreeOnePartition

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingThreeOnePartition.groupSizes_three_one
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingThreeOnePartition.sourceApplicable_three_one
