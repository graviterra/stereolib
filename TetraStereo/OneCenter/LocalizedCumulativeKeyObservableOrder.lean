import TetraStereo.OneCenter.LocalizedRerootCumulativeRule45Key

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-!
# Observable projection of cumulative Rules-4a--5 keys

`compareLocalizedRerootCumulativeRule45Keys` reads exactly two components of a
`LocalizedRerootCumulativeRule45Key`: the constitutional component `constitutional`, which
`OfficialRuleMajorKey.compare` compares by exhausting Rule 1a, then Rule 1b, then Rule 2; and the
cumulative descriptor projection `descriptor`.  The components `constitutional.sourceNodes`,
`constitutional.complete`, `labels` and `rankedLabels` are observation state carried for downstream
consumers and are never inspected by the comparator.

This module isolates that comparison-visible projection as `LocalizedCumulativeRule45Observable` and
proves that the comparator is a function of the observable alone.  The payoff is that independently
compiled or independently rerooted child lists which are descending permutations of one another
induce the same observation sequence.

A comparison tie forces equality of the observable only.  It never asserts that the exact labels
agree: a terminal Rule-4a tie (a lowercase `R`/`S` pair) is a genuine tie whose `labels` and
`rankedLabels` entries still differ.
-/

/-- The comparison-visible projection of one cumulative Rules-4a--5 key: the three constitutional
rule projections and the cumulative descriptor projection.  `sourceNodes`, `labels` and
`rankedLabels` are deliberately absent. -/
structure LocalizedCumulativeRule45Observable where
  /-- Addressed Rule-1a atomic-number projection. -/
  rule1a : List (List (OfficialSparseEntry ℕ))
  /-- Addressed Rule-1b duplicate-atom projection. -/
  rule1b : List (List (OfficialSparseEntry ℕ))
  /-- Addressed Rule-2 isotope-mass projection. -/
  rule2 : List (List (OfficialSparseEntry ℕ))
  /-- Addressed cumulative Rules-4a--5 descriptor projection. -/
  descriptor : List (List (OfficialSparseEntry (List ℕ)))
  deriving DecidableEq

/-- Observable comparison, in the nesting used by `compareLocalizedRerootCumulativeRule45Keys`:
Rule 1a, then Rule 1b, then Rule 2, then the cumulative descriptor. -/
def compareLocalizedCumulativeRule45Observable :
    LocalizedCumulativeRule45Observable → LocalizedCumulativeRule45Observable → Ordering :=
  compareLex
    (compareLex
      (Ordering.byKey LocalizedCumulativeRule45Observable.rule1a
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat))
      (compareLex
        (Ordering.byKey LocalizedCumulativeRule45Observable.rule1b
          (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b))
        (Ordering.byKey LocalizedCumulativeRule45Observable.rule2
          (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat))))
    (Ordering.byKey LocalizedCumulativeRule45Observable.descriptor
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority))

/-- Forget a cumulative Rules-4a--5 key down to its comparison-visible projection. -/
def localizedRerootCumulativeRule45Observable
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    LocalizedCumulativeRule45Observable where
  rule1a := key.constitutional.rule1a
  rule1b := key.constitutional.rule1b
  rule2 := key.constitutional.rule2
  descriptor := key.descriptor

@[simp] theorem localizedRerootCumulativeRule45Observable_rule1a
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    (input.localizedRerootCumulativeRule45Observable key).rule1a =
      key.constitutional.rule1a :=
  rfl

@[simp] theorem localizedRerootCumulativeRule45Observable_rule1b
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    (input.localizedRerootCumulativeRule45Observable key).rule1b =
      key.constitutional.rule1b :=
  rfl

@[simp] theorem localizedRerootCumulativeRule45Observable_rule2
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    (input.localizedRerootCumulativeRule45Observable key).rule2 =
      key.constitutional.rule2 :=
  rfl

@[simp] theorem localizedRerootCumulativeRule45Observable_descriptor
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    (input.localizedRerootCumulativeRule45Observable key).descriptor =
      key.descriptor :=
  rfl

/-! ## Exactness of the addressed list comparators

Every comparator below is a lexicographic fold of a comparator that decides equality exactly.
-/

private theorem flip_compare_eq_iff {α : Type*} (cmp : α → α → Ordering)
    (hcmp : ∀ a b, cmp a b = Ordering.eq ↔ a = b) :
    ∀ a b : α, flip cmp a b = Ordering.eq ↔ a = b := by
  intro a b
  show cmp b a = Ordering.eq ↔ a = b
  exact (hcmp b a).trans eq_comm

private theorem listCompareLex_eq_iff {α : Type*} (cmp : α → α → Ordering)
    (hcmp : ∀ a b, cmp a b = Ordering.eq ↔ a = b) :
    ∀ left right : List α, List.compareLex cmp left right = Ordering.eq ↔ left = right := by
  intro left
  induction left with
  | nil =>
      intro right
      exact List.compareLex_nil_left_eq_eq.trans eq_comm
  | cons head tail inductionHypothesis =>
      intro right
      cases right with
      | nil => exact List.compareLex_nil_right_eq_eq
      | cons otherHead otherTail =>
          rw [List.compareLex_cons_cons, Ordering.then_eq_eq]
          constructor
          · rintro ⟨headEq, tailEq⟩
            rw [(hcmp head otherHead).mp headEq,
              (inductionHypothesis otherTail).mp tailEq]
          · intro equal
            injection equal with headEq tailEq
            exact ⟨(hcmp head otherHead).mpr headEq,
              (inductionHypothesis otherTail).mpr tailEq⟩

/-! ## Exactness of the leaf comparators -/

/-- The explicitly typed natural-number comparator decides equality exactly. -/
theorem localizedCompareNat_eq_iff (left right : ℕ) :
    OfficialRuleMajorKey.compareNat left right = Ordering.eq ↔ left = right := by
  unfold OfficialRuleMajorKey.compareNat
  exact compare_eq_iff_eq

/-- The nearest-duplicate comparator decides equality exactly. -/
theorem compareRule1b_eq_iff (left right : ℕ) :
    OfficialRuleMajorKey.compareRule1b left right = Ordering.eq ↔ left = right := by
  unfold OfficialRuleMajorKey.compareRule1b
  exact flip_compare_eq_iff OfficialRuleMajorKey.compareNat localizedCompareNat_eq_iff left right

/-- The cumulative Rule-4a--5 node-vector comparator decides equality exactly. -/
theorem compareLocalizedCumulativeRule45Priority_eq_iff (left right : List ℕ) :
    compareLocalizedCumulativeRule45Priority left right = Ordering.eq ↔ left = right := by
  unfold compareLocalizedCumulativeRule45Priority
  exact listCompareLex_eq_iff OfficialRuleMajorKey.compareNat localizedCompareNat_eq_iff left right

private theorem compareSparseEntry_eq_iff {α : Type*} (cmp : α → α → Ordering)
    (hcmp : ∀ a b, cmp a b = Ordering.eq ↔ a = b) :
    ∀ left right : OfficialSparseEntry α,
      OfficialRuleMajorKey.compareSparseEntry cmp left right = Ordering.eq ↔ left = right := by
  have position : ∀ (left right : List ℕ),
      flip (List.compareLex OfficialRuleMajorKey.compareNat) left right = Ordering.eq ↔
        left = right :=
    flip_compare_eq_iff (List.compareLex OfficialRuleMajorKey.compareNat)
      (listCompareLex_eq_iff OfficialRuleMajorKey.compareNat localizedCompareNat_eq_iff)
  intro left right
  rw [OfficialRuleMajorKey.compareSparseEntry, compareLex_eq_eq, Ordering.byKey, Ordering.byKey,
    position left.1 right.1, hcmp left.2 right.2]
  exact ⟨fun equal => Prod.ext equal.1 equal.2,
    fun equal => ⟨congrArg Prod.fst equal, congrArg Prod.snd equal⟩⟩

private theorem compareSparseLayer_eq_iff {α : Type*} (cmp : α → α → Ordering)
    (hcmp : ∀ a b, cmp a b = Ordering.eq ↔ a = b) :
    ∀ left right : List (OfficialSparseEntry α),
      OfficialRuleMajorKey.compareSparseLayer cmp left right = Ordering.eq ↔ left = right := by
  intro left right
  unfold OfficialRuleMajorKey.compareSparseLayer
  exact listCompareLex_eq_iff (OfficialRuleMajorKey.compareSparseEntry cmp)
    (compareSparseEntry_eq_iff cmp hcmp) left right

/-- A lexicographic layer comparator decides equality exactly whenever its node comparator does. -/
theorem compareSparseLayers_eq_iff {α : Type*} (cmp : α → α → Ordering)
    (hcmp : ∀ a b, cmp a b = Ordering.eq ↔ a = b) :
    ∀ left right : List (List (OfficialSparseEntry α)),
      OfficialRuleMajorKey.compareSparseLayers cmp left right = Ordering.eq ↔ left = right := by
  intro left right
  unfold OfficialRuleMajorKey.compareSparseLayers
  exact listCompareLex_eq_iff (OfficialRuleMajorKey.compareSparseLayer cmp)
    (compareSparseLayer_eq_iff cmp hcmp) left right

/-- The Rule-1a and Rule-2 sphere comparators decide equality exactly on addressed spheres. -/
theorem compareSparseLayers_compareNat_eq_iff
    (left right : List (List (OfficialSparseEntry ℕ))) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat left right =
        Ordering.eq ↔
      left = right :=
  compareSparseLayers_eq_iff OfficialRuleMajorKey.compareNat localizedCompareNat_eq_iff left right

/-- The Rule-1b sphere comparator decides equality exactly on addressed spheres. -/
theorem compareSparseLayers_compareRule1b_eq_iff
    (left right : List (List (OfficialSparseEntry ℕ))) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b left right =
        Ordering.eq ↔
      left = right :=
  compareSparseLayers_eq_iff OfficialRuleMajorKey.compareRule1b compareRule1b_eq_iff left right

/-- The cumulative descriptor sphere comparator decides equality exactly on addressed spheres. -/
theorem compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff
    (left right : List (List (OfficialSparseEntry (List ℕ)))) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        left right = Ordering.eq ↔
      left = right :=
  compareSparseLayers_eq_iff compareLocalizedCumulativeRule45Priority
    compareLocalizedCumulativeRule45Priority_eq_iff left right

/-- The constitutional comparator reads exactly the three rule projections.  `sourceNodes` and
`complete` cannot influence it. -/
theorem officialRuleMajorKey_compare_eq_iff {V : Type*} (left right : OfficialRuleMajorKey V) :
    OfficialRuleMajorKey.compare left right = Ordering.eq ↔
      left.rule1a = right.rule1a ∧ left.rule1b = right.rule1b ∧
        left.rule2 = right.rule2 := by
  simp only [OfficialRuleMajorKey.compare, compareLex_eq_eq, Ordering.byKey,
    compareSparseLayers_compareNat_eq_iff, compareSparseLayers_compareRule1b_eq_iff]

/-! ## Observable exactness -/

/-- The observable comparator decides equality exactly on equal observables. -/
theorem compareLocalizedCumulativeRule45Observable_eq_iff
    (left right : LocalizedCumulativeRule45Observable) :
    compareLocalizedCumulativeRule45Observable left right = Ordering.eq ↔ left = right := by
  have rule1aCompare : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left.rule1a right.rule1a = Ordering.eq ↔ left.rule1a = right.rule1a :=
    compareSparseLayers_compareNat_eq_iff left.rule1a right.rule1a
  have rule1bCompare : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
      left.rule1b right.rule1b = Ordering.eq ↔ left.rule1b = right.rule1b :=
    compareSparseLayers_compareRule1b_eq_iff left.rule1b right.rule1b
  have rule2Compare : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left.rule2 right.rule2 = Ordering.eq ↔ left.rule2 = right.rule2 :=
    compareSparseLayers_compareNat_eq_iff left.rule2 right.rule2
  have descriptorCompare : OfficialRuleMajorKey.compareSparseLayers
      compareLocalizedCumulativeRule45Priority left.descriptor right.descriptor =
        Ordering.eq ↔ left.descriptor = right.descriptor :=
    compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff
      left.descriptor right.descriptor
  rw [compareLocalizedCumulativeRule45Observable, compareLex_eq_eq, compareLex_eq_eq,
    compareLex_eq_eq]
  simp only [Ordering.byKey, rule1aCompare, rule1bCompare, rule2Compare, descriptorCompare]
  constructor
  · rintro ⟨⟨h1a, h1b, h2⟩, hdescriptor⟩
    cases left with
    | mk leftRule1a leftRule1b leftRule2 leftDescriptor =>
      cases right with
      | mk rightRule1a rightRule1b rightRule2 rightDescriptor =>
        simp_all
  · intro equal
    rw [equal]
    exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩

/-- The observable comparator is oriented and transitive.

Instance resolution does not unfold named comparators such as `compareRule1b`, so the three named
leaf comparators are introduced as local instances before the structural comparison combinator is
unfolded to `List.compareLex`/`compareLex`/`Ordering.byKey`/`flip`. -/
theorem compareLocalizedCumulativeRule45Observable_transCmp :
    Std.TransCmp compareLocalizedCumulativeRule45Observable := by
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  haveI : Std.TransCmp OfficialRuleMajorKey.compareRule1b := by
    unfold OfficialRuleMajorKey.compareRule1b
    infer_instance
  haveI : Std.TransCmp compareLocalizedCumulativeRule45Priority := by
    unfold compareLocalizedCumulativeRule45Priority
    infer_instance
  unfold compareLocalizedCumulativeRule45Observable
    compareLocalizedCumulativeRule45Priority
    OfficialRuleMajorKey.compareSparseLayers
    OfficialRuleMajorKey.compareSparseLayer
    OfficialRuleMajorKey.compareSparseEntry
  infer_instance

/-! ## The cumulative key comparator is exactly observable comparison -/

/-- The cumulative recursive-key comparator is the observable comparator applied to the observable
projection. -/
theorem compareLocalizedRerootCumulativeRule45Keys_eq_compareObservable
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCumulativeRule45Key) :
    input.compareLocalizedRerootCumulativeRule45Keys left right =
      compareLocalizedCumulativeRule45Observable
        (input.localizedRerootCumulativeRule45Observable left)
        (input.localizedRerootCumulativeRule45Observable right) :=
  rfl

/-- Two cumulative keys compare equal exactly when their comparison-visible projections agree. -/
theorem compareLocalizedRerootCumulativeRule45Keys_eq_iff_observable_eq
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCumulativeRule45Key) :
    input.compareLocalizedRerootCumulativeRule45Keys left right = Ordering.eq ↔
      input.localizedRerootCumulativeRule45Observable left =
        input.localizedRerootCumulativeRule45Observable right := by
  have factored :=
    input.compareLocalizedRerootCumulativeRule45Keys_eq_compareObservable left right
  rw [factored]
  exact compareLocalizedCumulativeRule45Observable_eq_iff _ _

/-! ## Descending permutations carry the same observation sequence -/

/-- Descending cumulative key order transports to the observable projections. -/
theorem observable_pairwise_of_descending
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootCumulativeRule45Key)
    (descending : input.LocalizedRerootCumulativeRule45KeysDescending keys) :
    (keys.map (input.localizedRerootCumulativeRule45Observable)).Pairwise
      (fun left right =>
        compareLocalizedCumulativeRule45Observable left right ≠ Ordering.lt) := by
  unfold LocalizedRerootCumulativeRule45KeysDescending at descending
  exact List.Pairwise.map (input.localizedRerootCumulativeRule45Observable)
    (fun a b hlt hObservedLt => hlt (by
      rw [input.compareLocalizedRerootCumulativeRule45Keys_eq_compareObservable a b]
      exact hObservedLt))
    descending

/-- Independent descending permutations of the same cumulative keys induce the same sequence of
comparison-visible observations.  The two lists may have been compiled separately, or rerooted
separately, and their `labels` and `rankedLabels` components may still differ. -/
theorem map_localizedRerootCumulativeRule45Observable_eq_of_perm_of_descending
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootCumulativeRule45Key)
    (permutation : left.Perm right)
    (leftDescending : input.LocalizedRerootCumulativeRule45KeysDescending left)
    (rightDescending : input.LocalizedRerootCumulativeRule45KeysDescending right) :
    left.map (input.localizedRerootCumulativeRule45Observable) =
      right.map (input.localizedRerootCumulativeRule45Observable) := by
  haveI : Std.TransCmp compareLocalizedCumulativeRule45Observable :=
    compareLocalizedCumulativeRule45Observable_transCmp
  exact List.Perm.eq_of_pairwise
    (le := fun left right =>
      compareLocalizedCumulativeRule45Observable left right ≠ Ordering.lt)
    (fun a b _ _ lower upper =>
      (compareLocalizedCumulativeRule45Observable_eq_iff a b).mp (by
        refine Ordering.eq_eq_of_isLE_of_isGE ?_ (Ordering.ne_lt_iff_isGE.mp lower)
        rw [← Std.OrientedCmp.isGE_eq_isLE]
        exact Ordering.ne_lt_iff_isGE.mp upper))
    (input.observable_pairwise_of_descending left leftDescending)
    (input.observable_pairwise_of_descending right rightDescending)
    (permutation.map (input.localizedRerootCumulativeRule45Observable))

/-- Re-running the structural descending sort on already descending keys preserves the observation
sequence, so independently compiled sibling lists agree with the compiled sort. -/
theorem map_localizedRerootCumulativeRule45Observable_sort_eq_self
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootCumulativeRule45Key)
    (descending : input.LocalizedRerootCumulativeRule45KeysDescending keys) :
    (input.sortLocalizedRerootCumulativeRule45Keys keys).map
        (input.localizedRerootCumulativeRule45Observable) =
      keys.map (input.localizedRerootCumulativeRule45Observable) :=
  input.map_localizedRerootCumulativeRule45Observable_eq_of_perm_of_descending
    (input.sortLocalizedRerootCumulativeRule45Keys keys)
    keys
    (input.sortLocalizedRerootCumulativeRule45Keys_perm keys)
    (input.sortLocalizedRerootCumulativeRule45Keys_descending keys)
    descending

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
