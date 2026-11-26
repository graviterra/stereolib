import TetraStereo.Engine.RingFullPathTrialReadings

/-! Most-significant-bit-first scoring of like/unlike lists in Hanson et al.,
Figure 8. Arbitrary-precision natural scores retain leading-zero comparisons
whenever the two words have equal length. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingBinaryPairScore
open RingFullPathTrialReadings (bitWord)
attribute [local instance] lexOrd

def accumulate : Nat → List Bool → Nat
  | n, [] => n
  | n, b :: bs => accumulate (2*n + b.toNat) bs

def value := accumulate 0

private theorem increasing {x y : Nat} (h : x < y) (xs ys : List Bool)
    (width : xs.length = ys.length) : accumulate x xs < accumulate y ys := by
  induction xs generalizing ys x y with
  | nil => cases ys <;> simp_all [accumulate]
  | cons a as ih =>
    cases ys with
    | nil => simp at width
    | cons b bs =>
      apply ih (ys := bs) (by cases a <;> cases b <;> simp <;> omega) (by simpa using width)

theorem compare_value (xs ys : List Bool) (width : xs.length = ys.length) :
    compare (value xs) (value ys) = compare xs ys := by
  suffices ∀ n, compare (accumulate n xs) (accumulate n ys) = compare xs ys from this 0
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [accumulate]
  | cons a as ih =>
    cases ys with
    | nil => simp at width
    | cons b bs =>
      have len : as.length = bs.length := by simpa using width
      intro n
      cases a <;> cases b
      · simpa [accumulate,List.compare_cons_cons] using ih bs len (2*n)
      · apply (compare_lt_iff_lt.mpr (increasing (by omega : 2*n+0 < 2*n+1) as bs len)).trans
        rfl
      · apply (compare_gt_iff_gt.mpr (increasing (by omega : 2*n+0 < 2*n+1) bs as len.symm)).trans
        rfl
      · simpa [accumulate,List.compare_cons_cons] using ih bs len (2*n+1)

theorem compare_bits (xs ys : List Bool) : compare (bitWord xs) (bitWord ys) = compare xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons a as ih =>
    cases ys with
    | nil => rfl
    | cons b bs =>
      change compare ([a.toNat] :: bitWord as) ([b.toNat] :: bitWord bs) = compare (a::as) (b::bs)
      rw [List.compare_cons_cons,List.compare_cons_cons]
      cases a <;> cases b <;> rw [ih] <;> rfl

theorem value_max (xs ys : List Bool) (width : xs.length = ys.length) :
    value (max xs ys) = max (value xs) (value ys) := by
  have reflects {a b : List Bool} (lengths : a.length = b.length) (lt : value a < value b) : a < b := by
    apply (OneCenter.DeclarativeCIP.compareLex_eq_lt_iff_of compare
      (fun (x y : Bool) => by cases x <;> cases y <;> decide)
      (fun _ _ => Std.compare_eq_eq_iff_eq) a b).mp
    exact (compare_value a b lengths).symm.trans (Nat.compare_eq_lt.mpr lt)
  rcases le_total xs ys with le | le
  · rw [max_eq_right le, max_eq_right]
    exact le_of_not_gt (fun gt => (not_lt_of_ge le) (reflects width.symm gt))
  · rw [max_eq_left le,max_eq_left]
    exact le_of_not_gt (fun lt => (not_lt_of_ge le) (reflects width lt))

end TetraStereo.Engine.RingBinaryPairScore
assert_kernel_only TetraStereo.Engine.RingBinaryPairScore.compare_value
assert_kernel_only TetraStereo.Engine.RingBinaryPairScore.value_max
