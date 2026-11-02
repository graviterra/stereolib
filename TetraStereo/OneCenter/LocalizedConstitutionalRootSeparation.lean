import TetraStereo.KernelOnly
import TetraStereo.OneCenter.OfficialRuleMajorKey

set_option autoImplicit false











































namespace TetraStereo.OneCenter

/-! ## Generic lexicographic algebra

These lemmas mention only `Ordering`, `Ordering.then`, and `compareLex`.  They carry no CIP
vocabulary, so they apply unchanged to any key whose comparison appends further fields (Rule 2,
Rule 3, Rule 4, descriptor data, ...) after the constitutional component. -/

namespace ConstitutionalLexAlgebra

/-- A strict first `Ordering` component makes `then` return that component; the later component is
not inspected. -/
theorem then_eq_left_of_left_ne_eq {first later : Ordering} (decisive : first ≠ Ordering.eq) :
    first.then later = first := by
  cases first <;> simp_all

/-- A strict first component decides the whole lexicographic comparison and suppresses every
later component. -/
theorem compareLex_eq_left_of_left_ne_eq {α β : Type*}
    (compareFirst : α → β → Ordering) (compareLater : α → β → Ordering)
    (left : α) (right : β)
    (decisive : compareFirst left right ≠ Ordering.eq) :
    compareLex compareFirst compareLater left right = compareFirst left right := by
  unfold compareLex
  exact then_eq_left_of_left_ne_eq decisive

/-- A strict first component prevents a lexicographic tie, whatever the later component is. -/
theorem compareLex_ne_eq_of_left_ne_eq {α β : Type*}
    (compareFirst : α → β → Ordering) (compareLater : α → β → Ordering)
    (left : α) (right : β)
    (decisive : compareFirst left right ≠ Ordering.eq) :
    compareLex compareFirst compareLater left right ≠ Ordering.eq := by
  rw [compareLex_eq_left_of_left_ne_eq compareFirst compareLater left right decisive]
  exact decisive

/-- A tied first component falls through to exactly the later component. -/
theorem compareLex_eq_second_of_first_eq {α β : Type*}
    (compareFirst : α → β → Ordering) (compareLater : α → β → Ordering)
    (left : α) (right : β)
    (firstEq : compareFirst left right = Ordering.eq) :
    compareLex compareFirst compareLater left right = compareLater left right := by
  unfold compareLex
  rw [firstEq, Ordering.eq_then]

end ConstitutionalLexAlgebra

namespace OfficialRuleMajorKey

/-! ## The first Rule-1b entry as a comparator decision -/

/-- Distinct natural numbers are strictly ordered by the constitutional Rule-1b comparator. -/
theorem compareRule1b_ne_eq {left right : ℕ} (different : left ≠ right) :
    compareRule1b left right ≠ Ordering.eq := by
  intro equal
  unfold compareRule1b flip compareNat at equal
  exact different ((compare_eq_iff_eq (a := right) (b := left)).mp equal).symm

/-- A nearer left duplicate root outranks a farther right duplicate root. -/
theorem compareRule1b_eq_gt_of_lt {left right : ℕ} (lower : left < right) :
    compareRule1b left right = Ordering.gt := by
  unfold compareRule1b flip compareNat
  exact compare_gt_iff_gt.mpr lower

/-- A nearer right duplicate root outranks a farther left duplicate root. -/
theorem compareRule1b_eq_lt_of_lt {left right : ℕ} (higher : right < left) :
    compareRule1b left right = Ordering.lt := by
  unfold compareRule1b flip compareNat
  exact compare_lt_iff_lt.mpr higher

/-- Two singleton Rule-1b entries at the empty address compare by their observations alone. -/
theorem compareSparseEntry_rule1b_emptyAddress (left right : ℕ) :
    compareSparseEntry compareRule1b ([], left) ([], right) =
      compareRule1b left right := by
  simp [compareSparseEntry, compareLex, Ordering.byKey, flip, List.compareLex_nil_nil]

/-- A singleton Rule-1b sphere compares exactly by its single observation. -/
theorem compareSparseLayer_rule1b_singleton (left right : ℕ) :
    compareSparseLayer compareRule1b [([], left)] [([], right)] =
      compareRule1b left right := by
  unfold compareSparseLayer
  rw [List.compareLex_cons_cons, compareSparseEntry_rule1b_emptyAddress]
  simp [List.compareLex_nil_nil]

/-- The first Rule-1b sphere of a key whose Rule-1b projection starts with a singleton entry
decides the whole Rule-1b projection, provided the two observations differ. -/
theorem compareSparseLayers_compareRule1b_eq_of_head_distances
    {left right : List (List (OfficialSparseEntry ℕ))} {leftDistance rightDistance : ℕ}
    (leftHead : left.head? = some [([], leftDistance)])
    (rightHead : right.head? = some [([], rightDistance)])
    (different : leftDistance ≠ rightDistance) :
    compareSparseLayers compareRule1b left right =
      compareRule1b leftDistance rightDistance := by
  cases left with
  | nil => simp at leftHead
  | cons leftFirst leftRest =>
      cases right with
      | nil => simp at rightHead
      | cons rightFirst rightRest =>
          simp only [List.head?_cons, Option.some.injEq] at leftHead rightHead
          rw [leftHead, rightHead]
          unfold compareSparseLayers
          rw [List.compareLex_cons_cons, compareSparseLayer_rule1b_singleton]
          exact ConstitutionalLexAlgebra.then_eq_left_of_left_ne_eq
            (first := compareRule1b leftDistance rightDistance)
            (later := List.compareLex (compareSparseLayer compareRule1b) leftRest rightRest)
            (compareRule1b_ne_eq different)

/-- Distinct first Rule-1b entries make the whole Rule-1b projection decisive. -/
theorem compareSparseLayers_compareRule1b_ne_eq_of_head_distances
    {left right : List (List (OfficialSparseEntry ℕ))} {leftDistance rightDistance : ℕ}
    (leftHead : left.head? = some [([], leftDistance)])
    (rightHead : right.head? = some [([], rightDistance)])
    (different : leftDistance ≠ rightDistance) :
    compareSparseLayers compareRule1b left right ≠ Ordering.eq := by
  rw [compareSparseLayers_compareRule1b_eq_of_head_distances leftHead rightHead different]
  exact compareRule1b_ne_eq different

/-! ## Noninterference of the later fields -/

/-- A strict Rule-1a projection decides the comparator; Rule 1b and Rule 2 cannot alter it. -/
theorem compare_eq_rule1a_of_decisive {V : Type*} {left right : OfficialRuleMajorKey V}
    (decisive : compareSparseLayers compareNat left.rule1a right.rule1a ≠ Ordering.eq) :
    compare left right = compareSparseLayers compareNat left.rule1a right.rule1a := by
  unfold OfficialRuleMajorKey.compare
  have := ConstitutionalLexAlgebra.compareLex_eq_left_of_left_ne_eq
    (Ordering.byKey OfficialRuleMajorKey.rule1a (compareSparseLayers compareNat))
    (compareLex
      (Ordering.byKey OfficialRuleMajorKey.rule1b (compareSparseLayers compareRule1b))
      (Ordering.byKey OfficialRuleMajorKey.rule2 (compareSparseLayers compareNat)))
    left right (by simpa [Ordering.byKey] using decisive)
  simpa [Ordering.byKey] using this

/-- Once Rule 1a ties, a strict Rule-1b projection decides the comparator; Rule 2 cannot alter
it. -/
theorem compare_eq_rule1b_of_rule1a_eq_of_decisive {V : Type*}
    {left right : OfficialRuleMajorKey V}
    (rule1aEq : compareSparseLayers compareNat left.rule1a right.rule1a = Ordering.eq)
    (decisive : compareSparseLayers compareRule1b left.rule1b right.rule1b ≠ Ordering.eq) :
    compare left right = compareSparseLayers compareRule1b left.rule1b right.rule1b := by
  unfold OfficialRuleMajorKey.compare
  have firstEq : (Ordering.byKey OfficialRuleMajorKey.rule1a
      (compareSparseLayers compareNat)) left right = Ordering.eq := by
    simpa [Ordering.byKey] using rule1aEq
  rw [ConstitutionalLexAlgebra.compareLex_eq_second_of_first_eq _ _ left right firstEq]
  have inner := ConstitutionalLexAlgebra.compareLex_eq_left_of_left_ne_eq
    (Ordering.byKey OfficialRuleMajorKey.rule1b (compareSparseLayers compareRule1b))
    (Ordering.byKey OfficialRuleMajorKey.rule2 (compareSparseLayers compareNat))
    left right (by simpa [Ordering.byKey] using decisive)
  simpa [Ordering.byKey] using inner

/-- If either Rule 1a or Rule 1b is strict, the constitutional outcome is the first non-tie among
Rule 1a and Rule 1b.  In particular `rule2` is never consulted. -/
theorem compare_eq_rule1a_or_rule1b_of_decisive {V : Type*}
    {left right : OfficialRuleMajorKey V}
    (strict : compareSparseLayers compareNat left.rule1a right.rule1a ≠ Ordering.eq ∨
      compareSparseLayers compareRule1b left.rule1b right.rule1b ≠ Ordering.eq) :
    compare left right =
      if compareSparseLayers compareNat left.rule1a right.rule1a = Ordering.eq
      then compareSparseLayers compareRule1b left.rule1b right.rule1b
      else compareSparseLayers compareNat left.rule1a right.rule1a := by
  by_cases rule1aEq : compareSparseLayers compareNat left.rule1a right.rule1a = Ordering.eq
  · have rule1bNe : compareSparseLayers compareRule1b left.rule1b right.rule1b ≠ Ordering.eq := by
      rcases strict with rule1aNe | rule1bNe
      · exact absurd rule1aEq rule1aNe
      · exact rule1bNe
    rw [compare_eq_rule1b_of_rule1a_eq_of_decisive rule1aEq rule1bNe]
    simp [rule1aEq]
  · rw [compare_eq_rule1a_of_decisive rule1aEq]
    simp [rule1aEq]

/-! ## First-layer separation -/

/-- Two constitutional keys whose Rule-1b projections begin with singleton entries at distinct
original-root distances cannot compare equal.  This is the comparator first-layer separation
theorem; it constrains neither the Rule-1a projection nor any deeper field. -/
theorem compare_ne_eq_of_rule1b_head_distances {V : Type*}
    {left right : OfficialRuleMajorKey V} {leftDistance rightDistance : ℕ}
    (leftHead : left.rule1b.head? = some [([], leftDistance)])
    (rightHead : right.rule1b.head? = some [([], rightDistance)])
    (different : leftDistance ≠ rightDistance) :
    OfficialRuleMajorKey.compare left right ≠ Ordering.eq := by
  have rule1bDecisive :
      compareSparseLayers compareRule1b left.rule1b right.rule1b ≠ Ordering.eq :=
    compareSparseLayers_compareRule1b_ne_eq_of_head_distances leftHead rightHead different
  by_cases rule1aEq : compareSparseLayers compareNat left.rule1a right.rule1a = Ordering.eq
  · rw [compare_eq_rule1b_of_rule1a_eq_of_decisive rule1aEq rule1bDecisive]
    exact rule1bDecisive
  · rw [compare_eq_rule1a_of_decisive rule1aEq]
    exact rule1aEq

/-- When Rule 1a ties, the first Rule-1b entry determines the exact outcome. -/
theorem compare_eq_rule1b_of_rule1a_eq_of_head_distances {V : Type*}
    {left right : OfficialRuleMajorKey V} {leftDistance rightDistance : ℕ}
    (rule1aEq : compareSparseLayers compareNat left.rule1a right.rule1a = Ordering.eq)
    (leftHead : left.rule1b.head? = some [([], leftDistance)])
    (rightHead : right.rule1b.head? = some [([], rightDistance)])
    (different : leftDistance ≠ rightDistance) :
    compare left right = compareRule1b leftDistance rightDistance := by
  rw [compare_eq_rule1b_of_rule1a_eq_of_decisive rule1aEq
      (compareSparseLayers_compareRule1b_ne_eq_of_head_distances leftHead rightHead different),
    compareSparseLayers_compareRule1b_eq_of_head_distances leftHead rightHead different]

/-- After a Rule-1a tie, a nearer left duplicate root strictly outranks a farther right one. -/
theorem compare_eq_gt_of_rule1a_eq_of_head_lt {V : Type*}
    {left right : OfficialRuleMajorKey V} {leftDistance rightDistance : ℕ}
    (rule1aEq : compareSparseLayers compareNat left.rule1a right.rule1a = Ordering.eq)
    (leftHead : left.rule1b.head? = some [([], leftDistance)])
    (rightHead : right.rule1b.head? = some [([], rightDistance)])
    (lower : leftDistance < rightDistance) :
    compare left right = Ordering.gt := by
  rw [compare_eq_rule1b_of_rule1a_eq_of_head_distances rule1aEq leftHead rightHead
    (ne_of_lt lower)]
  exact compareRule1b_eq_gt_of_lt lower

/-- After a Rule-1a tie, a nearer right duplicate root strictly outranks a farther left one. -/
theorem compare_eq_lt_of_rule1a_eq_of_right_lt {V : Type*}
    {left right : OfficialRuleMajorKey V} {leftDistance rightDistance : ℕ}
    (rule1aEq : compareSparseLayers compareNat left.rule1a right.rule1a = Ordering.eq)
    (leftHead : left.rule1b.head? = some [([], leftDistance)])
    (rightHead : right.rule1b.head? = some [([], rightDistance)])
    (higher : rightDistance < leftDistance) :
    compare left right = Ordering.lt := by
  rw [compare_eq_rule1b_of_rule1a_eq_of_head_distances rule1aEq leftHead rightHead
    (ne_of_gt higher)]
  exact compareRule1b_eq_lt_of_lt higher

end OfficialRuleMajorKey

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.ConstitutionalLexAlgebra.then_eq_left_of_left_ne_eq
assert_kernel_only TetraStereo.OneCenter.ConstitutionalLexAlgebra.compareLex_eq_left_of_left_ne_eq
assert_kernel_only TetraStereo.OneCenter.ConstitutionalLexAlgebra.compareLex_ne_eq_of_left_ne_eq
assert_kernel_only TetraStereo.OneCenter.ConstitutionalLexAlgebra.compareLex_eq_second_of_first_eq
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.compareRule1b_ne_eq
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.compareRule1b_eq_gt_of_lt
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.compareRule1b_eq_lt_of_lt
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.compareSparseEntry_rule1b_emptyAddress
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.compareSparseLayer_rule1b_singleton
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.compareSparseLayers_compareRule1b_eq_of_head_distances
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.compareSparseLayers_compareRule1b_ne_eq_of_head_distances
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.compare_eq_rule1a_of_decisive
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.compare_eq_rule1b_of_rule1a_eq_of_decisive
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.compare_eq_rule1a_or_rule1b_of_decisive
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.compare_ne_eq_of_rule1b_head_distances
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.compare_eq_rule1b_of_rule1a_eq_of_head_distances
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.compare_eq_gt_of_rule1a_eq_of_head_lt
assert_kernel_only TetraStereo.OneCenter.OfficialRuleMajorKey.compare_eq_lt_of_rule1a_eq_of_right_lt
