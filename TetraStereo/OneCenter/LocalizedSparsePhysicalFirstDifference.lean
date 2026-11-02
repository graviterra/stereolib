import TetraStereo.OneCenter.DeclarativeCIPFirstDifferenceSchedule
import TetraStereo.OneCenter.OfficialRuleMajorKey
import TetraStereo.OneCenter.LocalizedCumulativeTreeTableReconstruction
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

open DeclarativeCIP

/-!
# Sparse addressed tables and the independent hierarchy first difference

`OfficialRuleMajorKey.compareSparseLayers` compares two Rule-1a projections by nested
lexicographic list comparison.  In this module we identify that executed comparison with the
independent semantic relation `DeclarativeCIP.FirstDifferenceOutcome` over a finite union
schedule of addresses, with absent positions read as zero.

The development is deliberately layered:

* `AddressCompare` is exactly the address comparator executed inside `compareSparseEntry`
  (flipped lexicographic order on positions).
* `rowValueAt` / `tableValue` read an observation at an address, returning zero when the address
  is absent.  The sphere is determined by the address length, so a table is a total function
  `List ℕ → ℕ` once depth exactness holds.
* `mergeAddressFuel` and `scanAddressFuel` enumerate the finite union of the two tables'
  addresses in strict sphere-major order.
* `compareSparseLayers_eq_compareLex_unionAddresses` proves the executed comparator is the
  pointwise comparison of the two value functions on that union schedule.  Positivity of present
  observations is essential and explicit: it is what lets a present address outrank an absent one.
* `compareSparseLayers_eq_firstDifference` composes that with
  `compareLex_map_iff_firstDifference` to obtain the relational first-difference outcome.
* `sameSupport_of_compareSparseLayers_eq` derives that a Rule-1a tie forces identical address
  supports.
-/

namespace SparsePhysicalFirstDifference

/-! ## The executed address comparator -/

/-- The address comparator executed inside `compareSparseEntry`. -/
def AddressCompare (left right : List ℕ) : Ordering :=
  List.compareLex OfficialRuleMajorKey.compareNat left right

@[simp] theorem AddressCompare_def (left right : List ℕ) :
    AddressCompare left right =
      List.compareLex OfficialRuleMajorKey.compareNat left right := rfl

theorem compareNat_eq_iff_eq {left right : ℕ} :
    OfficialRuleMajorKey.compareNat left right = Ordering.eq ↔ left = right := by
  unfold OfficialRuleMajorKey.compareNat
  exact compare_eq_iff_eq

theorem compareNat_lt_iff_lt {left right : ℕ} :
    OfficialRuleMajorKey.compareNat left right = Ordering.lt ↔ left < right := by
  unfold OfficialRuleMajorKey.compareNat
  exact compare_lt_iff_lt

theorem compareNat_gt_iff_gt {left right : ℕ} :
    OfficialRuleMajorKey.compareNat left right = Ordering.gt ↔ right < left := by
  unfold OfficialRuleMajorKey.compareNat
  exact compare_gt_iff_gt

/-- The explicit comparison is antisymmetric in the `Ordering.swap` sense. -/
theorem compareNat_swap (left right : ℕ) :
    OfficialRuleMajorKey.compareNat right left =
      (OfficialRuleMajorKey.compareNat left right).swap := by
  rcases lt_trichotomy left right with hlt | heq | hgt
  · rw [compareNat_gt_iff_gt.mpr hlt, compareNat_lt_iff_lt.mpr hlt]
    rfl
  · subst heq
    rw [compareNat_eq_iff_eq.mpr rfl]
    rfl
  · rw [compareNat_lt_iff_lt.mpr hgt, compareNat_gt_iff_gt.mpr hgt]
    rfl

theorem compareNat_zero_zero :
    OfficialRuleMajorKey.compareNat 0 0 = Ordering.eq :=
  compareNat_eq_iff_eq.mpr rfl

/-- The executed natural comparator is the descending outcome. -/
theorem compareNat_iff_descendingNatOutcome (left right : ℕ) (outcome : Ordering) :
    OfficialRuleMajorKey.compareNat left right = outcome ↔
      DescendingNatOutcome left right outcome := by
  cases outcome with
  | lt =>
      constructor
      · intro compared
        exact DescendingNatOutcome.lt (compareNat_lt_iff_lt.mp compared)
      · intro observed
        cases observed with
        | lt hlt => exact compareNat_lt_iff_lt.mpr hlt
  | eq =>
      constructor
      · intro compared
        exact DescendingNatOutcome.eq (compareNat_eq_iff_eq.mp compared)
      · intro observed
        cases observed with
        | eq heq => exact compareNat_eq_iff_eq.mpr heq
  | gt =>
      constructor
      · intro compared
        exact DescendingNatOutcome.gt (compareNat_gt_iff_gt.mp compared)
      · intro observed
        cases observed with
        | gt hgt => exact compareNat_gt_iff_gt.mpr hgt

theorem compareLex_refl (address : List ℕ) :
    List.compareLex OfficialRuleMajorKey.compareNat address address = Ordering.eq := by
  induction address with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.compareLex_cons_cons, compareNat_eq_iff_eq.mpr rfl, Ordering.eq_then]
      exact inductionHypothesis

theorem compareLex_swap (left right : List ℕ) :
    List.compareLex OfficialRuleMajorKey.compareNat right left =
      (List.compareLex OfficialRuleMajorKey.compareNat left right).swap := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons value rest => rw [List.compareLex_cons_nil, List.compareLex_nil_cons]; rfl
  | cons head tail inductionHypothesis =>
      cases right with
      | nil => rw [List.compareLex_nil_cons, List.compareLex_cons_nil]; rfl
      | cons value rest =>
          rw [List.compareLex_cons_cons, List.compareLex_cons_cons, Ordering.swap_then,
            ← compareNat_swap, inductionHypothesis rest]

theorem AddressCompare_refl (address : List ℕ) :
    AddressCompare address address = Ordering.eq :=
  compareLex_refl address

/-- Strict address comparison is antisymmetric. -/
theorem AddressCompare_swap (left right : List ℕ) :
    AddressCompare right left = (AddressCompare left right).swap :=
  compareLex_swap left right

theorem AddressCompare_gt_of_lt {left right : List ℕ}
    (before : AddressCompare left right = Ordering.lt) :
    AddressCompare right left = Ordering.gt := by
  rw [AddressCompare_swap, before]
  rfl

theorem AddressCompare_lt_of_gt {left right : List ℕ}
    (after : AddressCompare left right = Ordering.gt) :
    AddressCompare right left = Ordering.lt := by
  rw [AddressCompare_swap, after]
  rfl

/-- Strict address comparison entails distinct addresses. -/
theorem ne_of_AddressCompare_lt {left right : List ℕ}
    (before : AddressCompare left right = Ordering.lt) : left ≠ right := by
  intro same
  rw [same, AddressCompare_refl] at before
  exact Ordering.noConfusion before

theorem AddressCompare_eq_iff {left right : List ℕ} :
    AddressCompare left right = Ordering.eq ↔ left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rw [AddressCompare_def, List.compareLex_nil_nil]; simp
      | cons value rest => rw [AddressCompare_def, List.compareLex_nil_cons]; simp
  | cons head tail inductionHypothesis =>
      cases right with
      | nil => rw [AddressCompare_def, List.compareLex_cons_nil]; simp
      | cons value rest =>
          rw [AddressCompare_def, List.compareLex_cons_cons, Ordering.then_eq_eq,
            compareNat_eq_iff_eq, ← AddressCompare_def,
            show AddressCompare tail rest = Ordering.eq ↔ tail = rest from
              inductionHypothesis]
          simp

/-! ## The lexicographic characterisation of address comparison -/

theorem listLex_cons_cons_iff {headLeft headRight : ℕ} {tailLeft tailRight : List ℕ} :
    List.Lex (· < ·) (headLeft :: tailLeft) (headRight :: tailRight) ↔
      headLeft < headRight ∨
        (headLeft = headRight ∧ List.Lex (· < ·) tailLeft tailRight) := by
  constructor
  · intro related
    cases related with
    | rel before => exact Or.inl before
    | cons tailRelated => exact Or.inr ⟨rfl, tailRelated⟩
  · rintro (before | ⟨rfl, tailRelated⟩)
    · exact List.Lex.rel before
    · exact List.Lex.cons tailRelated

theorem AddressCompare_lt_iff_lex {left right : List ℕ} :
    AddressCompare left right = Ordering.lt ↔ List.Lex (· < ·) left right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rw [AddressCompare_def, List.compareLex_nil_nil]; simp
      | cons head tail =>
          rw [AddressCompare_def, List.compareLex_nil_cons]
          exact ⟨fun _ => List.Lex.nil, fun _ => rfl⟩
  | cons head tail inductionHypothesis =>
      cases right with
      | nil => rw [AddressCompare_def, List.compareLex_cons_nil]; simp
      | cons value rest =>
          rw [AddressCompare_def, List.compareLex_cons_cons, Ordering.then_eq_lt,
            compareNat_lt_iff_lt, compareNat_eq_iff_eq, listLex_cons_cons_iff,
            ← AddressCompare_def,
            show AddressCompare tail rest = Ordering.lt ↔ List.Lex (· < ·) tail rest from
              inductionHypothesis]

theorem listLex_lt_trans {first second third : List ℕ}
    (firstSecond : List.Lex (· < ·) first second)
    (secondThird : List.Lex (· < ·) second third) :
    List.Lex (· < ·) first third :=
  List.lex_trans (l₂ := second) (fun hlt hit => Nat.lt_trans hlt hit) firstSecond secondThird

theorem AddressCompare_lt_trans {first second third : List ℕ}
    (firstSecond : AddressCompare first second = Ordering.lt)
    (secondThird : AddressCompare second third = Ordering.lt) :
    AddressCompare first third = Ordering.lt :=
  AddressCompare_lt_iff_lex.mpr
    (listLex_lt_trans (AddressCompare_lt_iff_lex.mp firstSecond)
      (AddressCompare_lt_iff_lex.mp secondThird))

/-- Equal-depth addresses ordered by `AddressCompare` are ordered by the sphere-major hierarchy
relation. -/
theorem hierarchyAddressBefore_of_AddressCompare_lt {depth : ℕ} {left right : List ℕ}
    (leftLength : left.length = depth) (rightLength : right.length = depth)
    (before : AddressCompare left right = Ordering.lt) :
    HierarchyAddressBefore left right := by
  show List.Lex (· < ·) (left.length :: left) (right.length :: right)
  rw [leftLength, rightLength]
  exact List.Lex.cons (AddressCompare_lt_iff_lex.mp before)

/-- A strictly nearer address precedes every deeper address. -/
theorem hierarchyAddressBefore_of_length_lt {left right : List ℕ}
    (shorter : left.length < right.length) : HierarchyAddressBefore left right := by
  show List.Lex (· < ·) (left.length :: left) (right.length :: right)
  exact List.Lex.rel shorter

/-! ## Reading observations at addresses -/

/-- The observation at one address inside one sphere; absent positions read zero. -/
def rowValueAt : List (OfficialSparseEntry ℕ) → List ℕ → ℕ
  | [], _ => 0
  | entry :: rest, position =>
      if entry.1 = position then entry.2 else rowValueAt rest position

@[simp] theorem rowValueAt_nil (position : List ℕ) : rowValueAt [] position = 0 := rfl

@[simp] theorem rowValueAt_cons_self (entry : OfficialSparseEntry ℕ)
    (rest : List (OfficialSparseEntry ℕ)) :
    rowValueAt (entry :: rest) entry.1 = entry.2 := by
  simp [rowValueAt]

theorem rowValueAt_cons_of_ne (entry : OfficialSparseEntry ℕ)
    (rest : List (OfficialSparseEntry ℕ)) (position : List ℕ)
    (different : entry.1 ≠ position) :
    rowValueAt (entry :: rest) position = rowValueAt rest position := by
  simp [rowValueAt, different]

/-- Absent addresses read zero. -/
theorem rowValueAt_eq_zero_of_absent (row : List (OfficialSparseEntry ℕ))
    (position : List ℕ) (absent : ∀ entry ∈ row, entry.1 ≠ position) :
    rowValueAt row position = 0 := by
  induction row with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [rowValueAt_cons_of_ne head tail position (absent head (by simp))]
      exact inductionHypothesis
        (fun entry present => absent entry (List.mem_cons_of_mem head present))

/-- A present address reads a positive value whenever every observation is positive. -/
theorem rowValueAt_pos_of_mem (row : List (OfficialSparseEntry ℕ)) (position : List ℕ)
    (positive : ∀ entry ∈ row, 0 < entry.2)
    (present : ∃ entry ∈ row, entry.1 = position) :
    0 < rowValueAt row position := by
  induction row with
  | nil =>
      obtain ⟨entry, absent, _⟩ := present
      exact absurd absent (by simp)
  | cons head tail inductionHypothesis =>
      by_cases same : head.1 = position
      · rw [← same, rowValueAt_cons_self]
        exact positive head (by simp)
      · rw [rowValueAt_cons_of_ne head tail position same]
        refine inductionHypothesis
          (fun entry present => positive entry (List.mem_cons_of_mem head present)) ?_
        obtain ⟨entry, entryPresent, entryAt⟩ := present
        rcases List.mem_cons.mp entryPresent with rfl | later
        · exact absurd entryAt same
        · exact ⟨entry, later, entryAt⟩

/-- A non-zero reading exposes a present address. -/
theorem exists_mem_of_rowValueAt_ne_zero (row : List (OfficialSparseEntry ℕ))
    (position : List ℕ) (nonzero : rowValueAt row position ≠ 0) :
    ∃ entry ∈ row, entry.1 = position := by
  induction row with
  | nil => exact absurd rfl nonzero
  | cons head tail inductionHypothesis =>
      by_cases same : head.1 = position
      · exact ⟨head, by simp, same⟩
      · rw [rowValueAt_cons_of_ne head tail position same] at nonzero
        obtain ⟨entry, entryMem, entryAt⟩ := inductionHypothesis nonzero
        exact ⟨entry, List.mem_cons_of_mem head entryMem, entryAt⟩

/-- The observation of a table at an address: the sphere index is the address length. -/
def tableValue (table : List (List (OfficialSparseEntry ℕ))) (position : List ℕ) : ℕ :=
  rowValueAt (table.getD position.length []) position

/-- The observation of a table read at a shifted sphere index. -/
def relativeValueAt (offset : ℕ) (table : List (List (OfficialSparseEntry ℕ)))
    (position : List ℕ) : ℕ :=
  rowValueAt (table.getD (position.length - offset) []) position

theorem tableValue_eq_relativeValueAt_zero (table : List (List (OfficialSparseEntry ℕ)))
    (position : List ℕ) : tableValue table position = relativeValueAt 0 table position := rfl

theorem relativeValueAt_head (offset : ℕ) (head : List (OfficialSparseEntry ℕ))
    (tail : List (List (OfficialSparseEntry ℕ))) (position : List ℕ)
    (lengthEq : position.length = offset) :
    relativeValueAt offset (head :: tail) position = rowValueAt head position := by
  unfold relativeValueAt
  rw [lengthEq, Nat.sub_self, List.getD_cons_zero]

theorem relativeValueAt_tail (offset : ℕ) (head : List (OfficialSparseEntry ℕ))
    (tail : List (List (OfficialSparseEntry ℕ))) (position : List ℕ)
    (shorter : offset + 1 ≤ position.length) :
    relativeValueAt offset (head :: tail) position =
      relativeValueAt (offset + 1) tail position := by
  unfold relativeValueAt
  rw [show position.length - offset = (position.length - (offset + 1)) + 1 from by omega,
    List.getD_cons_succ]

theorem tableValue_eq_zero_of_absent (table : List (List (OfficialSparseEntry ℕ)))
    (position : List ℕ)
    (absent : ∀ depth entry, entry ∈ table.getD depth [] → entry.1 ≠ position) :
    tableValue table position = 0 := by
  unfold tableValue
  exact rowValueAt_eq_zero_of_absent _ _ (fun entry present => absent _ entry present)

/-! ## Merging two increasing address rows -/

/-- Merge two strictly increasing address rows into their union, keeping a single copy of an
address carried by both sides.  The fuel bounds the recursion; `mergeAddresses` supplies the sum
of the lengths, which always suffices. -/
def mergeAddressFuel :
    ℕ → List (OfficialSparseEntry ℕ) → List (OfficialSparseEntry ℕ) → List (List ℕ)
  | 0, _, _ => []
  | _ + 1, [], right => right.map Prod.fst
  | _ + 1, left, [] => left.map Prod.fst
  | fuel + 1, leftEntry :: leftRest, rightEntry :: rightRest =>
      match AddressCompare leftEntry.1 rightEntry.1 with
      | .lt => leftEntry.1 :: mergeAddressFuel fuel leftRest (rightEntry :: rightRest)
      | .gt => rightEntry.1 :: mergeAddressFuel fuel (leftEntry :: leftRest) rightRest
      | .eq => leftEntry.1 :: mergeAddressFuel fuel leftRest rightRest

/-- The address union of two rows. -/
def mergeAddresses (left right : List (OfficialSparseEntry ℕ)) : List (List ℕ) :=
  mergeAddressFuel (left.length + right.length) left right

theorem mergeAddressFuel_zero (left right : List (OfficialSparseEntry ℕ)) :
    mergeAddressFuel 0 left right = [] := rfl

theorem mergeAddressFuel_succ_nil (fuel : ℕ) (right : List (OfficialSparseEntry ℕ)) :
    mergeAddressFuel (fuel + 1) [] right = right.map Prod.fst := rfl

theorem mergeAddressFuel_succ_nil_right (fuel : ℕ) (left : List (OfficialSparseEntry ℕ)) :
    mergeAddressFuel (fuel + 1) left [] = left.map Prod.fst := by
  cases left with
  | nil => rfl
  | cons head tail => rfl

theorem mergeAddressFuel_succ_cons_cons (fuel : ℕ)
    (leftEntry : OfficialSparseEntry ℕ) (leftRest : List (OfficialSparseEntry ℕ))
    (rightEntry : OfficialSparseEntry ℕ) (rightRest : List (OfficialSparseEntry ℕ)) :
    mergeAddressFuel (fuel + 1) (leftEntry :: leftRest) (rightEntry :: rightRest) =
      (match AddressCompare leftEntry.1 rightEntry.1 with
        | .lt => leftEntry.1 :: mergeAddressFuel fuel leftRest (rightEntry :: rightRest)
        | .gt => rightEntry.1 :: mergeAddressFuel fuel (leftEntry :: leftRest) rightRest
        | .eq => leftEntry.1 :: mergeAddressFuel fuel leftRest rightRest) := rfl

theorem mergeAddressFuel_succ_cons_cons_lt (fuel : ℕ)
    (leftEntry : OfficialSparseEntry ℕ) (leftRest : List (OfficialSparseEntry ℕ))
    (rightEntry : OfficialSparseEntry ℕ) (rightRest : List (OfficialSparseEntry ℕ))
    (compared : AddressCompare leftEntry.1 rightEntry.1 = Ordering.lt) :
    mergeAddressFuel (fuel + 1) (leftEntry :: leftRest) (rightEntry :: rightRest) =
      leftEntry.1 :: mergeAddressFuel fuel leftRest (rightEntry :: rightRest) := by
  rw [mergeAddressFuel_succ_cons_cons, compared]

theorem mergeAddressFuel_succ_cons_cons_gt (fuel : ℕ)
    (leftEntry : OfficialSparseEntry ℕ) (leftRest : List (OfficialSparseEntry ℕ))
    (rightEntry : OfficialSparseEntry ℕ) (rightRest : List (OfficialSparseEntry ℕ))
    (compared : AddressCompare leftEntry.1 rightEntry.1 = Ordering.gt) :
    mergeAddressFuel (fuel + 1) (leftEntry :: leftRest) (rightEntry :: rightRest) =
      rightEntry.1 :: mergeAddressFuel fuel (leftEntry :: leftRest) rightRest := by
  rw [mergeAddressFuel_succ_cons_cons, compared]

theorem mergeAddressFuel_succ_cons_cons_eq (fuel : ℕ)
    (leftEntry : OfficialSparseEntry ℕ) (leftRest : List (OfficialSparseEntry ℕ))
    (rightEntry : OfficialSparseEntry ℕ) (rightRest : List (OfficialSparseEntry ℕ))
    (compared : AddressCompare leftEntry.1 rightEntry.1 = Ordering.eq) :
    mergeAddressFuel (fuel + 1) (leftEntry :: leftRest) (rightEntry :: rightRest) =
      leftEntry.1 :: mergeAddressFuel fuel leftRest rightRest := by
  rw [mergeAddressFuel_succ_cons_cons, compared]

/-- Every address of the merge is an address of one of the two rows. -/
theorem mem_mergeAddressFuel {fuel : ℕ} {left right : List (OfficialSparseEntry ℕ)}
    {position : List ℕ} (present : position ∈ mergeAddressFuel fuel left right) :
    (∃ entry ∈ left, entry.1 = position) ∨ (∃ entry ∈ right, entry.1 = position) := by
  induction fuel generalizing left right with
  | zero => simp [mergeAddressFuel] at present
  | succ fuel inductionHypothesis =>
      cases left with
      | nil =>
          rw [mergeAddressFuel_succ_nil] at present
          obtain ⟨entry, mem, addr⟩ := List.mem_map.mp present
          exact Or.inr ⟨entry, mem, addr⟩
      | cons leftEntry leftRest =>
          cases right with
          | nil =>
              rw [mergeAddressFuel_succ_nil_right] at present
              obtain ⟨entry, mem, addr⟩ := List.mem_map.mp present
              exact Or.inl ⟨entry, mem, addr⟩
          | cons rightEntry rightRest =>
              cases compared : AddressCompare leftEntry.1 rightEntry.1 with
              | lt =>
                  rw [mergeAddressFuel_succ_cons_cons_lt fuel leftEntry leftRest rightEntry
                    rightRest compared] at present
                  rcases List.mem_cons.mp present with rfl | later
                  · exact Or.inl ⟨leftEntry, by simp, rfl⟩
                  · rcases inductionHypothesis (left := leftRest)
                      (right := rightEntry :: rightRest) later with
                      ⟨entry, mem, addr⟩ | ⟨entry, mem, addr⟩
                    · exact Or.inl ⟨entry, List.mem_cons_of_mem leftEntry mem, addr⟩
                    · exact Or.inr ⟨entry, mem, addr⟩
              | gt =>
                  rw [mergeAddressFuel_succ_cons_cons_gt fuel leftEntry leftRest rightEntry
                    rightRest compared] at present
                  rcases List.mem_cons.mp present with rfl | later
                  · exact Or.inr ⟨rightEntry, by simp, rfl⟩
                  · rcases inductionHypothesis (left := leftEntry :: leftRest)
                      (right := rightRest) later with
                      ⟨entry, mem, addr⟩ | ⟨entry, mem, addr⟩
                    · exact Or.inl ⟨entry, mem, addr⟩
                    · exact Or.inr ⟨entry, List.mem_cons_of_mem rightEntry mem, addr⟩
              | eq =>
                  rw [mergeAddressFuel_succ_cons_cons_eq fuel leftEntry leftRest rightEntry
                    rightRest compared] at present
                  rcases List.mem_cons.mp present with rfl | later
                  · exact Or.inl ⟨leftEntry, by simp, rfl⟩
                  · rcases inductionHypothesis (left := leftRest) (right := rightRest) later with
                      ⟨entry, mem, addr⟩ | ⟨entry, mem, addr⟩
                    · exact Or.inl ⟨entry, List.mem_cons_of_mem leftEntry mem, addr⟩
                    · exact Or.inr ⟨entry, List.mem_cons_of_mem rightEntry mem, addr⟩

/-- Every address of the merge has the common depth of the two rows. -/
theorem mergeAddressFuel_mem_length {depth : ℕ} (fuel : ℕ) :
    ∀ (left right : List (OfficialSparseEntry ℕ)),
      (∀ entry ∈ left, entry.1.length = depth) →
      (∀ entry ∈ right, entry.1.length = depth) →
      ∀ position ∈ mergeAddressFuel fuel left right, position.length = depth := by
  induction fuel with
  | zero => intro left right _ _ position present; simp [mergeAddressFuel] at present
  | succ fuel inductionHypothesis =>
      intro left right leftDepth rightDepth position present
      cases left with
      | nil =>
          rw [mergeAddressFuel_succ_nil] at present
          obtain ⟨entry, mem, addr⟩ := List.mem_map.mp present
          rw [← addr]
          exact rightDepth entry mem
      | cons leftEntry leftRest =>
          cases right with
          | nil =>
              rw [mergeAddressFuel_succ_nil_right] at present
              obtain ⟨entry, mem, addr⟩ := List.mem_map.mp present
              rw [← addr]
              exact leftDepth entry mem
          | cons rightEntry rightRest =>
              cases compared : AddressCompare leftEntry.1 rightEntry.1 with
              | lt =>
                  rw [mergeAddressFuel_succ_cons_cons_lt fuel leftEntry leftRest rightEntry
                    rightRest compared] at present
                  rcases List.mem_cons.mp present with rfl | later
                  · exact leftDepth leftEntry (by simp)
                  · exact inductionHypothesis leftRest (rightEntry :: rightRest)
                      (fun entry mem => leftDepth entry (List.mem_cons_of_mem _ mem))
                      rightDepth position later
              | gt =>
                  rw [mergeAddressFuel_succ_cons_cons_gt fuel leftEntry leftRest rightEntry
                    rightRest compared] at present
                  rcases List.mem_cons.mp present with rfl | later
                  · exact rightDepth rightEntry (by simp)
                  · exact inductionHypothesis (leftEntry :: leftRest) rightRest leftDepth
                      (fun entry mem => rightDepth entry (List.mem_cons_of_mem _ mem)) position later
              | eq =>
                  rw [mergeAddressFuel_succ_cons_cons_eq fuel leftEntry leftRest rightEntry
                    rightRest compared] at present
                  rcases List.mem_cons.mp present with rfl | later
                  · exact leftDepth leftEntry (by simp)
                  · exact inductionHypothesis leftRest rightRest
                      (fun entry mem => leftDepth entry (List.mem_cons_of_mem _ mem))
                      (fun entry mem => rightDepth entry (List.mem_cons_of_mem _ mem))
                      position later

/-- Every address of the left row occurs in the merge. -/
theorem mem_mergeAddressFuel_of_mem_left (fuel : ℕ) :
    ∀ (left right : List (OfficialSparseEntry ℕ)) (entry : OfficialSparseEntry ℕ),
      entry ∈ left → left.length + right.length ≤ fuel →
      entry.1 ∈ mergeAddressFuel fuel left right := by
  induction fuel with
  | zero =>
      intro left right entry present bound
      cases left with
      | nil => exact absurd present (by simp)
      | cons head tail => simp at bound
  | succ fuel inductionHypothesis =>
      intro left right entry present bound
      cases left with
      | nil => exact absurd present (by simp)
      | cons leftEntry leftRest =>
          cases right with
          | nil =>
              rw [mergeAddressFuel_succ_nil_right]
              exact List.mem_map.mpr ⟨entry, present, rfl⟩
          | cons rightEntry rightRest =>
              simp only [List.length_cons] at bound
              cases compared : AddressCompare leftEntry.1 rightEntry.1 with
              | lt =>
                  rw [mergeAddressFuel_succ_cons_cons_lt fuel leftEntry leftRest rightEntry
                    rightRest compared]
                  rcases List.mem_cons.mp present with rfl | later
                  · exact List.mem_cons_self
                  · exact List.mem_cons_of_mem _
                      (inductionHypothesis leftRest (rightEntry :: rightRest) entry later
                        (by simp only [List.length_cons] at bound ⊢; omega))
              | gt =>
                  rw [mergeAddressFuel_succ_cons_cons_gt fuel leftEntry leftRest rightEntry
                    rightRest compared]
                  exact List.mem_cons_of_mem _
                    (inductionHypothesis (leftEntry :: leftRest) rightRest entry present
                      (by simp only [List.length_cons] at bound ⊢; omega))
              | eq =>
                  rw [mergeAddressFuel_succ_cons_cons_eq fuel leftEntry leftRest rightEntry
                    rightRest compared]
                  rcases List.mem_cons.mp present with rfl | later
                  · exact List.mem_cons_self
                  · exact List.mem_cons_of_mem _
                      (inductionHypothesis leftRest rightRest entry later (by omega))

/-- Every address of the right row occurs in the merge. -/
theorem mem_mergeAddressFuel_of_mem_right (fuel : ℕ) :
    ∀ (left right : List (OfficialSparseEntry ℕ)) (entry : OfficialSparseEntry ℕ),
      entry ∈ right → left.length + right.length ≤ fuel →
      entry.1 ∈ mergeAddressFuel fuel left right := by
  induction fuel with
  | zero =>
      intro left right entry present bound
      cases right with
      | nil => exact absurd present (by simp)
      | cons head tail => simp at bound
  | succ fuel inductionHypothesis =>
      intro left right entry present bound
      cases left with
      | nil =>
          rw [mergeAddressFuel_succ_nil]
          exact List.mem_map.mpr ⟨entry, present, rfl⟩
      | cons leftEntry leftRest =>
          cases right with
          | nil => exact absurd present (by simp)
          | cons rightEntry rightRest =>
              simp only [List.length_cons] at bound
              cases compared : AddressCompare leftEntry.1 rightEntry.1 with
              | lt =>
                  rw [mergeAddressFuel_succ_cons_cons_lt fuel leftEntry leftRest rightEntry
                    rightRest compared]
                  exact List.mem_cons_of_mem _
                    (inductionHypothesis leftRest (rightEntry :: rightRest) entry present
                      (by simp only [List.length_cons] at bound ⊢; omega))
              | gt =>
                  rw [mergeAddressFuel_succ_cons_cons_gt fuel leftEntry leftRest rightEntry
                    rightRest compared]
                  rcases List.mem_cons.mp present with rfl | later
                  · exact List.mem_cons_self
                  · exact List.mem_cons_of_mem _
                      (inductionHypothesis (leftEntry :: leftRest) rightRest entry later
                        (by simp only [List.length_cons] at bound ⊢; omega))
              | eq =>
                  rw [mergeAddressFuel_succ_cons_cons_eq fuel leftEntry leftRest rightEntry
                    rightRest compared]
                  rcases List.mem_cons.mp present with rfl | later
                  · exact List.mem_cons.mpr
                      (Or.inl (AddressCompare_eq_iff.mp compared).symm)
                  · exact List.mem_cons_of_mem _
                      (inductionHypothesis leftRest rightRest entry later (by omega))

/-- A strictly increasing row whose entries all live at one depth yields a strictly increasing
sphere-major address list. -/
theorem pairwise_map_fst_of_row {depth : ℕ} (row : List (OfficialSparseEntry ℕ))
    (rowDepth : ∀ entry ∈ row, entry.1.length = depth)
    (rowSorted : row.Pairwise fun left right => AddressCompare left.1 right.1 = Ordering.lt) :
    (row.map Prod.fst).Pairwise HierarchyAddressBefore := by
  induction row with
  | nil => simp
  | cons head tail inductionHypothesis =>
      rw [List.map_cons, List.pairwise_cons]
      refine ⟨?_, ?_⟩
      · intro position present
        obtain ⟨entry, entryMem, addr⟩ := List.mem_map.mp present
        rw [← addr]
        exact hierarchyAddressBefore_of_AddressCompare_lt
          (rowDepth head (by simp))
          (rowDepth entry (List.mem_cons_of_mem head entryMem))
          ((List.pairwise_cons.mp rowSorted).1 entry entryMem)
      · exact inductionHypothesis
          (fun entry entryMem => rowDepth entry (List.mem_cons_of_mem head entryMem))
          (List.pairwise_cons.mp rowSorted).2

/-- Merging two strictly increasing equal-depth rows yields a strictly increasing sphere-major
address list. -/
theorem mergeAddressFuel_pairwise {depth : ℕ} (fuel : ℕ) :
    ∀ (left right : List (OfficialSparseEntry ℕ)),
      (∀ entry ∈ left, entry.1.length = depth) →
      (∀ entry ∈ right, entry.1.length = depth) →
      (left.Pairwise fun a b => AddressCompare a.1 b.1 = Ordering.lt) →
      (right.Pairwise fun a b => AddressCompare a.1 b.1 = Ordering.lt) →
      (mergeAddressFuel fuel left right).Pairwise HierarchyAddressBefore := by
  induction fuel with
  | zero => intro left right _ _ _ _; simp [mergeAddressFuel]
  | succ fuel inductionHypothesis =>
      intro left right leftDepth rightDepth leftSorted rightSorted
      cases left with
      | nil =>
          rw [mergeAddressFuel_succ_nil]
          exact pairwise_map_fst_of_row right rightDepth rightSorted
      | cons leftEntry leftRest =>
          cases right with
          | nil =>
              rw [mergeAddressFuel_succ_nil_right]
              exact pairwise_map_fst_of_row (leftEntry :: leftRest) leftDepth leftSorted
          | cons rightEntry rightRest =>
              cases compared : AddressCompare leftEntry.1 rightEntry.1 with
              | lt =>
                  rw [mergeAddressFuel_succ_cons_cons_lt fuel leftEntry leftRest rightEntry
                    rightRest compared, List.pairwise_cons]
                  refine ⟨?_, ?_⟩
                  · intro position present
                    have lengthEq : position.length = depth :=
                      mergeAddressFuel_mem_length fuel leftRest (rightEntry :: rightRest)
                        (fun entry mem => leftDepth entry (List.mem_cons_of_mem _ mem))
                        rightDepth position present
                    refine hierarchyAddressBefore_of_AddressCompare_lt
                      (leftDepth leftEntry (by simp)) lengthEq ?_
                    rcases mem_mergeAddressFuel present with ⟨entry, mem, addr⟩ | ⟨entry, mem, addr⟩
                    · rw [← addr]
                      exact (List.pairwise_cons.mp leftSorted).1 entry mem
                    · rw [← addr]
                      rcases List.mem_cons.mp mem with rfl | mem'
                      · exact compared
                      · exact AddressCompare_lt_trans compared
                          ((List.pairwise_cons.mp rightSorted).1 entry mem')
                  · exact inductionHypothesis leftRest (rightEntry :: rightRest)
                      (fun entry mem => leftDepth entry (List.mem_cons_of_mem _ mem)) rightDepth
                      (List.pairwise_cons.mp leftSorted).2 rightSorted
              | gt =>
                  rw [mergeAddressFuel_succ_cons_cons_gt fuel leftEntry leftRest rightEntry
                    rightRest compared, List.pairwise_cons]
                  refine ⟨?_, ?_⟩
                  · intro position present
                    have lengthEq : position.length = depth :=
                      mergeAddressFuel_mem_length fuel (leftEntry :: leftRest) rightRest leftDepth
                        (fun entry mem => rightDepth entry (List.mem_cons_of_mem _ mem))
                        position present
                    refine hierarchyAddressBefore_of_AddressCompare_lt
                      (rightDepth rightEntry (by simp)) lengthEq ?_
                    rcases mem_mergeAddressFuel present with ⟨entry, mem, addr⟩ | ⟨entry, mem, addr⟩
                    · rw [← addr]
                      rcases List.mem_cons.mp mem with rfl | mem'
                      · exact AddressCompare_lt_of_gt compared
                      · exact AddressCompare_lt_trans (AddressCompare_lt_of_gt compared)
                          ((List.pairwise_cons.mp leftSorted).1 entry mem')
                    · rw [← addr]
                      exact (List.pairwise_cons.mp rightSorted).1 entry mem
                  · exact inductionHypothesis (leftEntry :: leftRest) rightRest leftDepth
                      (fun entry mem => rightDepth entry (List.mem_cons_of_mem _ mem))
                      leftSorted (List.pairwise_cons.mp rightSorted).2
              | eq =>
                  have sameAddress : leftEntry.1 = rightEntry.1 := AddressCompare_eq_iff.mp compared
                  rw [mergeAddressFuel_succ_cons_cons_eq fuel leftEntry leftRest rightEntry
                    rightRest compared, List.pairwise_cons]
                  refine ⟨?_, ?_⟩
                  · intro position present
                    have lengthEq : position.length = depth :=
                      mergeAddressFuel_mem_length fuel leftRest rightRest
                        (fun entry mem => leftDepth entry (List.mem_cons_of_mem _ mem))
                        (fun entry mem => rightDepth entry (List.mem_cons_of_mem _ mem))
                        position present
                    refine hierarchyAddressBefore_of_AddressCompare_lt
                      (leftDepth leftEntry (by simp)) lengthEq ?_
                    rcases mem_mergeAddressFuel present with ⟨entry, mem, addr⟩ | ⟨entry, mem, addr⟩
                    · rw [← addr]
                      exact (List.pairwise_cons.mp leftSorted).1 entry mem
                    · rw [← addr, sameAddress]
                      exact (List.pairwise_cons.mp rightSorted).1 entry mem
                  · exact inductionHypothesis leftRest rightRest
                      (fun entry mem => leftDepth entry (List.mem_cons_of_mem _ mem))
                      (fun entry mem => rightDepth entry (List.mem_cons_of_mem _ mem))
                      (List.pairwise_cons.mp leftSorted).2
                      (List.pairwise_cons.mp rightSorted).2

/-! ## Comparing one merged sphere -/

theorem compareSparseEntry_def {α : Type*} (compareObservation : α → α → Ordering)
    (left right : OfficialSparseEntry α) :
    OfficialRuleMajorKey.compareSparseEntry compareObservation left right =
      (AddressCompare right.1 left.1).then (compareObservation left.2 right.2) := rfl

theorem compareSparseEntry_eq_of_address_eq {α : Type*} (compareObservation : α → α → Ordering)
    {left right : OfficialSparseEntry α} (same : left.1 = right.1) :
    OfficialRuleMajorKey.compareSparseEntry compareObservation left right =
      compareObservation left.2 right.2 := by
  rw [compareSparseEntry_def, ← same, AddressCompare_refl, Ordering.eq_then]

theorem compareSparseEntry_gt_of_address_lt {α : Type*} (compareObservation : α → α → Ordering)
    {left right : OfficialSparseEntry α}
    (before : AddressCompare left.1 right.1 = Ordering.lt) :
    OfficialRuleMajorKey.compareSparseEntry compareObservation left right = Ordering.gt := by
  rw [compareSparseEntry_def, AddressCompare_gt_of_lt before]
  rfl

theorem compareSparseEntry_lt_of_address_gt {α : Type*} (compareObservation : α → α → Ordering)
    {left right : OfficialSparseEntry α}
    (after : AddressCompare left.1 right.1 = Ordering.gt) :
    OfficialRuleMajorKey.compareSparseEntry compareObservation left right = Ordering.lt := by
  rw [compareSparseEntry_def, AddressCompare_lt_of_gt after]
  rfl

theorem Ordering_then_assoc (first second third : Ordering) :
    (first.then second).then third = first.then (second.then third) := by
  cases first <;> cases second <;> rfl

theorem compareLex_append_append {α : Type*} (compareValue : α → α → Ordering)
    {leftFirst rightFirst leftSecond rightSecond : List α}
    (lengthEq : leftFirst.length = rightFirst.length) :
    List.compareLex compareValue (leftFirst ++ leftSecond) (rightFirst ++ rightSecond) =
      (List.compareLex compareValue leftFirst rightFirst).then
        (List.compareLex compareValue leftSecond rightSecond) := by
  induction leftFirst generalizing rightFirst with
  | nil =>
      have rightEmpty : rightFirst = [] := by
        cases rightFirst with
        | nil => rfl
        | cons head tail => simp at lengthEq
      subst rightEmpty
      rfl
  | cons head tail inductionHypothesis =>
      cases rightFirst with
      | nil => simp at lengthEq
      | cons value rest =>
          have tailLength : tail.length = rest.length := by simpa using lengthEq
          rw [List.cons_append, List.cons_append, List.compareLex_cons_cons,
            List.compareLex_cons_cons, inductionHypothesis tailLength, Ordering_then_assoc]

/-- Comparing one sphere of two positive, strictly increasing rows is exactly comparing the two
value readings on their merged address union. -/
theorem compareSparseLayer_mergeAddressFuel (fuel : ℕ) :
    ∀ (left right : List (OfficialSparseEntry ℕ)),
      left.length + right.length ≤ fuel →
      (left.Pairwise fun a b => AddressCompare a.1 b.1 = Ordering.lt) →
      (right.Pairwise fun a b => AddressCompare a.1 b.1 = Ordering.lt) →
      (∀ entry ∈ left, 0 < entry.2) →
      (∀ entry ∈ right, 0 < entry.2) →
      OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareNat left right =
        List.compareLex OfficialRuleMajorKey.compareNat
          ((mergeAddressFuel fuel left right).map (rowValueAt left))
          ((mergeAddressFuel fuel left right).map (rowValueAt right)) := by
  induction fuel with
  | zero =>
      intro left right bound _ _ _ _
      have leftEmpty : left = [] := by
        cases left with
        | nil => rfl
        | cons head tail => simp at bound
      have rightEmpty : right = [] := by
        cases right with
        | nil => rfl
        | cons head tail => simp at bound
      subst leftEmpty
      subst rightEmpty
      rfl
  | succ fuel inductionHypothesis =>
      intro left right bound leftSorted rightSorted leftPositive rightPositive
      cases left with
      | nil =>
          cases right with
          | nil => rfl
          | cons rightEntry rightRest =>
              have positiveHead : 0 < rightEntry.2 := rightPositive rightEntry (by simp)
              have layerNil : OfficialRuleMajorKey.compareSparseLayer
                    OfficialRuleMajorKey.compareNat [] (rightEntry :: rightRest) =
                  Ordering.lt := by
                simpa only [OfficialRuleMajorKey.compareSparseLayer] using
                  (List.compareLex_nil_cons (cmp :=
                    OfficialRuleMajorKey.compareSparseEntry OfficialRuleMajorKey.compareNat)
                    (x := rightEntry) (xs := rightRest))
              rw [layerNil, mergeAddressFuel_succ_nil]
              simp only [List.map_cons]
              rw [List.compareLex_cons_cons, rowValueAt_nil, rowValueAt_cons_self,
                compareNat_lt_iff_lt.mpr positiveHead]
              rfl
      | cons leftEntry leftRest =>
          cases right with
          | nil =>
              have positiveHead : 0 < leftEntry.2 := leftPositive leftEntry (by simp)
              have layerNil : OfficialRuleMajorKey.compareSparseLayer
                    OfficialRuleMajorKey.compareNat (leftEntry :: leftRest) [] =
                  Ordering.gt := by
                simpa only [OfficialRuleMajorKey.compareSparseLayer] using
                  (List.compareLex_cons_nil (cmp :=
                    OfficialRuleMajorKey.compareSparseEntry OfficialRuleMajorKey.compareNat)
                    (x := leftEntry) (xs := leftRest))
              rw [layerNil, mergeAddressFuel_succ_nil_right]
              simp only [List.map_cons]
              rw [List.compareLex_cons_cons, rowValueAt_nil, rowValueAt_cons_self,
                compareNat_gt_iff_gt.mpr positiveHead]
              rfl
          | cons rightEntry rightRest =>
              simp only [List.length_cons] at bound
              have layerStep : OfficialRuleMajorKey.compareSparseLayer
                    OfficialRuleMajorKey.compareNat (leftEntry :: leftRest)
                    (rightEntry :: rightRest) =
                  (OfficialRuleMajorKey.compareSparseEntry OfficialRuleMajorKey.compareNat
                      leftEntry rightEntry).then
                    (OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareNat
                      leftRest rightRest) := by
                simpa only [OfficialRuleMajorKey.compareSparseLayer] using
                  (List.compareLex_cons_cons (cmp :=
                    OfficialRuleMajorKey.compareSparseEntry OfficialRuleMajorKey.compareNat)
                    (x := leftEntry) (y := rightEntry) (xs := leftRest) (ys := rightRest))
              rw [layerStep]
              cases compared : AddressCompare leftEntry.1 rightEntry.1 with
              | lt =>
                  have rightAbsent : rowValueAt (rightEntry :: rightRest) leftEntry.1 = 0 := by
                    refine rowValueAt_eq_zero_of_absent _ _ ?_
                    intro entry present same
                    rcases List.mem_cons.mp present with rfl | later
                    · exact ne_of_AddressCompare_lt compared same.symm
                    · have ordered := (List.pairwise_cons.mp rightSorted).1 entry later
                      rw [same, AddressCompare_gt_of_lt compared] at ordered
                      exact Ordering.noConfusion ordered
                  have positiveHead : 0 < leftEntry.2 := leftPositive leftEntry (by simp)
                  have entryStep : OfficialRuleMajorKey.compareSparseEntry
                        OfficialRuleMajorKey.compareNat leftEntry rightEntry = Ordering.gt :=
                    compareSparseEntry_gt_of_address_lt OfficialRuleMajorKey.compareNat compared
                  rw [entryStep, mergeAddressFuel_succ_cons_cons_lt fuel leftEntry leftRest
                    rightEntry rightRest compared]
                  simp only [List.map_cons]
                  rw [List.compareLex_cons_cons, rowValueAt_cons_self, rightAbsent,
                    compareNat_gt_iff_gt.mpr positiveHead]
                  rfl
              | gt =>
                  have leftAbsent : rowValueAt (leftEntry :: leftRest) rightEntry.1 = 0 := by
                    refine rowValueAt_eq_zero_of_absent _ _ ?_
                    intro entry present same
                    rcases List.mem_cons.mp present with rfl | later
                    · exact ne_of_AddressCompare_lt (AddressCompare_lt_of_gt compared) same.symm
                    · have ordered := (List.pairwise_cons.mp leftSorted).1 entry later
                      rw [same, compared] at ordered
                      exact Ordering.noConfusion ordered
                  have positiveHead : 0 < rightEntry.2 := rightPositive rightEntry (by simp)
                  have entryStep : OfficialRuleMajorKey.compareSparseEntry
                        OfficialRuleMajorKey.compareNat leftEntry rightEntry = Ordering.lt :=
                    compareSparseEntry_lt_of_address_gt OfficialRuleMajorKey.compareNat compared
                  rw [entryStep, mergeAddressFuel_succ_cons_cons_gt fuel leftEntry leftRest
                    rightEntry rightRest compared]
                  simp only [List.map_cons]
                  rw [List.compareLex_cons_cons, leftAbsent, rowValueAt_cons_self,
                    compareNat_lt_iff_lt.mpr positiveHead]
                  rfl
              | eq =>
                  have sameAddress : leftEntry.1 = rightEntry.1 :=
                    AddressCompare_eq_iff.mp compared
                  have rightHead : rowValueAt (rightEntry :: rightRest) leftEntry.1 =
                      rightEntry.2 := by
                    rw [sameAddress]
                    exact rowValueAt_cons_self rightEntry rightRest
                  have leftTailMap : (mergeAddressFuel fuel leftRest rightRest).map
                        (rowValueAt (leftEntry :: leftRest)) =
                      (mergeAddressFuel fuel leftRest rightRest).map (rowValueAt leftRest) := by
                    refine List.map_congr_left ?_
                    intro position present
                    refine rowValueAt_cons_of_ne leftEntry leftRest position ?_
                    intro same
                    rcases mem_mergeAddressFuel present with ⟨entry, mem, addr⟩ | ⟨entry, mem, addr⟩
                    · have ordered := (List.pairwise_cons.mp leftSorted).1 entry mem
                      rw [addr, ← same] at ordered
                      rw [AddressCompare_refl] at ordered
                      exact Ordering.noConfusion ordered
                    · have ordered := (List.pairwise_cons.mp rightSorted).1 entry mem
                      rw [addr, ← sameAddress, ← same] at ordered
                      rw [AddressCompare_refl] at ordered
                      exact Ordering.noConfusion ordered
                  have rightTailMap : (mergeAddressFuel fuel leftRest rightRest).map
                        (rowValueAt (rightEntry :: rightRest)) =
                      (mergeAddressFuel fuel leftRest rightRest).map (rowValueAt rightRest) := by
                    refine List.map_congr_left ?_
                    intro position present
                    refine rowValueAt_cons_of_ne rightEntry rightRest position ?_
                    intro same
                    rcases mem_mergeAddressFuel present with ⟨entry, mem, addr⟩ | ⟨entry, mem, addr⟩
                    · have ordered := (List.pairwise_cons.mp leftSorted).1 entry mem
                      rw [addr, ← sameAddress.trans same] at ordered
                      rw [AddressCompare_refl] at ordered
                      exact Ordering.noConfusion ordered
                    · have ordered := (List.pairwise_cons.mp rightSorted).1 entry mem
                      rw [addr, ← same] at ordered
                      rw [AddressCompare_refl] at ordered
                      exact Ordering.noConfusion ordered
                  have entryTie : OfficialRuleMajorKey.compareSparseEntry
                        OfficialRuleMajorKey.compareNat leftEntry rightEntry =
                      OfficialRuleMajorKey.compareNat leftEntry.2 rightEntry.2 :=
                    compareSparseEntry_eq_of_address_eq OfficialRuleMajorKey.compareNat sameAddress
                  rw [entryTie, mergeAddressFuel_succ_cons_cons_eq fuel leftEntry leftRest
                    rightEntry rightRest compared]
                  simp only [List.map_cons]
                  rw [List.compareLex_cons_cons, rowValueAt_cons_self, rightHead,
                    leftTailMap, rightTailMap]
                  exact congrArg
                    (fun rest => (OfficialRuleMajorKey.compareNat leftEntry.2 rightEntry.2).then
                      rest)
                    (inductionHypothesis leftRest rightRest (by omega)
                      (List.pairwise_cons.mp leftSorted).2
                      (List.pairwise_cons.mp rightSorted).2
                      (fun entry mem => leftPositive entry (List.mem_cons_of_mem leftEntry mem))
                      (fun entry mem => rightPositive entry (List.mem_cons_of_mem rightEntry mem)))

/-! ## The union schedule of a whole table -/

/-- Enumerate the union of two tables' address rows sphere by sphere. -/
def scanAddressFuel :
    ℕ → List (List (OfficialSparseEntry ℕ)) → List (List (OfficialSparseEntry ℕ)) →
      List (List ℕ)
  | 0, _, _ => []
  | _ + 1, [], [] => []
  | fuel + 1, [], rightLayer :: rightRest =>
      rightLayer.map Prod.fst ++ scanAddressFuel fuel [] rightRest
  | fuel + 1, leftLayer :: leftRest, [] =>
      leftLayer.map Prod.fst ++ scanAddressFuel fuel leftRest []
  | fuel + 1, leftLayer :: leftRest, rightLayer :: rightRest =>
      mergeAddresses leftLayer rightLayer ++ scanAddressFuel fuel leftRest rightRest

/-- The finite address union of two tables. -/
def unionAddresses (left right : List (List (OfficialSparseEntry ℕ))) : List (List ℕ) :=
  scanAddressFuel (left.length + right.length) left right

theorem scanAddressFuel_zero (left right : List (List (OfficialSparseEntry ℕ))) :
    scanAddressFuel 0 left right = [] := rfl

theorem scanAddressFuel_succ_nil_nil (fuel : ℕ) :
    scanAddressFuel (fuel + 1) [] [] = [] := rfl

theorem scanAddressFuel_succ_nil_cons (fuel : ℕ)
    (rightLayer : List (OfficialSparseEntry ℕ))
    (rightRest : List (List (OfficialSparseEntry ℕ))) :
    scanAddressFuel (fuel + 1) [] (rightLayer :: rightRest) =
      rightLayer.map Prod.fst ++ scanAddressFuel fuel [] rightRest := rfl

theorem scanAddressFuel_succ_cons_nil (fuel : ℕ)
    (leftLayer : List (OfficialSparseEntry ℕ))
    (leftRest : List (List (OfficialSparseEntry ℕ))) :
    scanAddressFuel (fuel + 1) (leftLayer :: leftRest) [] =
      leftLayer.map Prod.fst ++ scanAddressFuel fuel leftRest [] := rfl

theorem scanAddressFuel_succ_cons_cons (fuel : ℕ)
    (leftLayer : List (OfficialSparseEntry ℕ))
    (leftRest : List (List (OfficialSparseEntry ℕ)))
    (rightLayer : List (OfficialSparseEntry ℕ))
    (rightRest : List (List (OfficialSparseEntry ℕ))) :
    scanAddressFuel (fuel + 1) (leftLayer :: leftRest) (rightLayer :: rightRest) =
      mergeAddresses leftLayer rightLayer ++ scanAddressFuel fuel leftRest rightRest := rfl

/-- Row `depth` of a table lies at address length `offset + depth`. -/
def RowsAtDepth (offset : ℕ) (table : List (List (OfficialSparseEntry ℕ))) : Prop :=
  ∀ depth entry, entry ∈ table.getD depth [] → entry.1.length = offset + depth

/-- Rows are strictly increasing in the executed address order. -/
def RowsIncreasing (table : List (List (OfficialSparseEntry ℕ))) : Prop :=
  ∀ depth, (table.getD depth []).Pairwise fun left right =>
    AddressCompare left.1 right.1 = Ordering.lt

/-- Every sphere below the table length is inhabited. -/
def RowsNonempty (table : List (List (OfficialSparseEntry ℕ))) : Prop :=
  ∀ depth, depth < table.length → table.getD depth [] ≠ []

/-- All observations are strictly positive. -/
def TablePositive (table : List (List (OfficialSparseEntry ℕ))) : Prop :=
  ∀ depth entry, entry ∈ table.getD depth [] → 0 < entry.2

/-- The complete structural well-formedness of an addressed table. -/
structure SparseTableWellFormed (table : List (List (OfficialSparseEntry ℕ))) : Prop where
  depthExact : RowsAtDepth 0 table
  increasing : RowsIncreasing table
  nonempty : RowsNonempty table

theorem RowsAtDepth.tail {offset : ℕ} {head : List (OfficialSparseEntry ℕ)}
    {tail : List (List (OfficialSparseEntry ℕ))} (rows : RowsAtDepth offset (head :: tail)) :
    RowsAtDepth (offset + 1) tail := by
  intro depth entry present
  have lifted : entry ∈ (head :: tail).getD (depth + 1) [] := by
    rwa [List.getD_cons_succ]
  have := rows (depth + 1) entry lifted
  omega

theorem RowsAtDepth.head {offset : ℕ} {head : List (OfficialSparseEntry ℕ)}
    {tail : List (List (OfficialSparseEntry ℕ))} (rows : RowsAtDepth offset (head :: tail)) :
    ∀ entry ∈ head, entry.1.length = offset := by
  intro entry present
  have := rows 0 entry (by simpa using present)
  simpa using this

theorem RowsIncreasing.tail {head : List (OfficialSparseEntry ℕ)}
    {tail : List (List (OfficialSparseEntry ℕ))} (increasing : RowsIncreasing (head :: tail)) :
    RowsIncreasing tail := by
  intro depth
  rw [show tail.getD depth [] = (head :: tail).getD (depth + 1) [] from
    (List.getD_cons_succ).symm]
  exact increasing (depth + 1)

theorem RowsNonempty.tail {head : List (OfficialSparseEntry ℕ)}
    {tail : List (List (OfficialSparseEntry ℕ))} (nonempty : RowsNonempty (head :: tail)) :
    RowsNonempty tail := by
  intro depth below
  rw [show tail.getD depth [] = (head :: tail).getD (depth + 1) [] from
    (List.getD_cons_succ).symm]
  exact nonempty (depth + 1) (by simpa using Nat.succ_lt_succ below)

theorem TablePositive.tail {head : List (OfficialSparseEntry ℕ)}
    {tail : List (List (OfficialSparseEntry ℕ))} (positive : TablePositive (head :: tail)) :
    TablePositive tail := by
  intro depth entry present
  refine positive (depth + 1) entry ?_
  rwa [List.getD_cons_succ]

theorem RowsAtDepth_nil (offset : ℕ) :
    RowsAtDepth offset ([] : List (List (OfficialSparseEntry ℕ))) := by
  intro depth entry present
  simp at present

theorem RowsIncreasing_nil :
    RowsIncreasing ([] : List (List (OfficialSparseEntry ℕ))) := by
  intro depth
  exact List.Pairwise.nil

/-- Every address of the scanned union is an address of one of the two tables. -/
theorem mem_scanAddressFuel {fuel : ℕ}
    {left right : List (List (OfficialSparseEntry ℕ))} {position : List ℕ}
    (present : position ∈ scanAddressFuel fuel left right) :
    (∃ depth entry, entry ∈ left.getD depth [] ∧ entry.1 = position) ∨
      (∃ depth entry, entry ∈ right.getD depth [] ∧ entry.1 = position) := by
  induction fuel generalizing left right with
  | zero => simp [scanAddressFuel] at present
  | succ fuel inductionHypothesis =>
      cases left with
      | nil =>
          cases right with
          | nil => simp [scanAddressFuel] at present
          | cons rightLayer rightRest =>
              rw [scanAddressFuel_succ_nil_cons] at present
              rcases List.mem_append.mp present with headPresent | tailPresent
              · obtain ⟨entry, mem, addr⟩ := List.mem_map.mp headPresent
                exact Or.inr ⟨0, entry, by simpa using mem, addr⟩
              · rcases inductionHypothesis tailPresent with
                  ⟨depth, entry, mem, addr⟩ | ⟨depth, entry, mem, addr⟩
                · exact absurd mem (by simp)
                · exact Or.inr ⟨depth + 1, entry, by rwa [List.getD_cons_succ], addr⟩
      | cons leftLayer leftRest =>
          cases right with
          | nil =>
              rw [scanAddressFuel_succ_cons_nil] at present
              rcases List.mem_append.mp present with headPresent | tailPresent
              · obtain ⟨entry, mem, addr⟩ := List.mem_map.mp headPresent
                exact Or.inl ⟨0, entry, by simpa using mem, addr⟩
              · rcases inductionHypothesis tailPresent with
                  ⟨depth, entry, mem, addr⟩ | ⟨depth, entry, mem, addr⟩
                · exact Or.inl ⟨depth + 1, entry, by rwa [List.getD_cons_succ], addr⟩
                · exact absurd mem (by simp)
          | cons rightLayer rightRest =>
              rw [scanAddressFuel_succ_cons_cons] at present
              rcases List.mem_append.mp present with headPresent | tailPresent
              · rcases mem_mergeAddressFuel headPresent with ⟨entry, mem, addr⟩ | ⟨entry, mem, addr⟩
                · exact Or.inl ⟨0, entry, by simpa using mem, addr⟩
                · exact Or.inr ⟨0, entry, by simpa using mem, addr⟩
              · rcases inductionHypothesis tailPresent with
                  ⟨depth, entry, mem, addr⟩ | ⟨depth, entry, mem, addr⟩
                · exact Or.inl ⟨depth + 1, entry, by rwa [List.getD_cons_succ], addr⟩
                · exact Or.inr ⟨depth + 1, entry, by rwa [List.getD_cons_succ], addr⟩

/-- Every address of the left table occurs in the scanned union. -/
theorem mem_scanAddressFuel_of_mem_left (fuel : ℕ) :
    ∀ (left right : List (List (OfficialSparseEntry ℕ))) (position : List ℕ),
      left.length + right.length ≤ fuel →
      (∃ depth entry, entry ∈ left.getD depth [] ∧ entry.1 = position) →
        position ∈ scanAddressFuel fuel left right := by
  induction fuel with
  | zero =>
      intro left right position bound present
      obtain ⟨depth, entry, mem, _⟩ := present
      cases left with
      | nil => simp at mem
      | cons head tail => simp at bound
  | succ fuel inductionHypothesis =>
      intro left right position bound present
      cases left with
      | nil =>
          obtain ⟨depth, entry, mem, _⟩ := present
          simp at mem
      | cons leftLayer leftRest =>
          cases right with
          | nil =>
              rw [scanAddressFuel_succ_cons_nil]
              rcases present with ⟨depth, entry, mem, addr⟩
              cases depth with
              | zero =>
                  exact List.mem_append_left _
                    (List.mem_map.mpr ⟨entry, by simpa using mem, by simpa using addr⟩)
              | succ depth =>
                  refine List.mem_append_right _ ?_
                  exact inductionHypothesis leftRest [] position
                    (by simp only [List.length_cons, List.length_nil] at bound ⊢; omega)
                    ⟨depth, entry, by rwa [List.getD_cons_succ] at mem, addr⟩
          | cons rightLayer rightRest =>
              rw [scanAddressFuel_succ_cons_cons]
              rcases present with ⟨depth, entry, mem, addr⟩
              cases depth with
              | zero =>
                  refine List.mem_append_left _ ?_
                  rw [← addr]
                  exact mem_mergeAddressFuel_of_mem_left (leftLayer.length + rightLayer.length)
                    leftLayer rightLayer entry (by simpa using mem) (Nat.le_refl _)
              | succ depth =>
                  refine List.mem_append_right _ ?_
                  exact inductionHypothesis leftRest rightRest position
                    (by simp only [List.length_cons] at bound ⊢; omega)
                    ⟨depth, entry, by rwa [List.getD_cons_succ] at mem, addr⟩

/-- Every address of the right table occurs in the scanned union. -/
theorem mem_scanAddressFuel_of_mem_right (fuel : ℕ) :
    ∀ (left right : List (List (OfficialSparseEntry ℕ))) (position : List ℕ),
      left.length + right.length ≤ fuel →
      (∃ depth entry, entry ∈ right.getD depth [] ∧ entry.1 = position) →
        position ∈ scanAddressFuel fuel left right := by
  induction fuel with
  | zero =>
      intro left right position bound present
      obtain ⟨depth, entry, mem, _⟩ := present
      cases right with
      | nil => simp at mem
      | cons head tail => simp at bound
  | succ fuel inductionHypothesis =>
      intro left right position bound present
      cases right with
      | nil =>
          obtain ⟨depth, entry, mem, _⟩ := present
          simp at mem
      | cons rightLayer rightRest =>
          cases left with
          | nil =>
              rw [scanAddressFuel_succ_nil_cons]
              rcases present with ⟨depth, entry, mem, addr⟩
              cases depth with
              | zero =>
                  exact List.mem_append_left _
                    (List.mem_map.mpr ⟨entry, by simpa using mem, by simpa using addr⟩)
              | succ depth =>
                  refine List.mem_append_right _ ?_
                  exact inductionHypothesis [] rightRest position
                    (by simp only [List.length_cons, List.length_nil] at bound ⊢; omega)
                    ⟨depth, entry, by rwa [List.getD_cons_succ] at mem, addr⟩
          | cons leftLayer leftRest =>
              rw [scanAddressFuel_succ_cons_cons]
              rcases present with ⟨depth, entry, mem, addr⟩
              cases depth with
              | zero =>
                  refine List.mem_append_left _ ?_
                  rw [← addr]
                  exact mem_mergeAddressFuel_of_mem_right (leftLayer.length + rightLayer.length)
                    leftLayer rightLayer entry (by simpa using mem) (Nat.le_refl _)
              | succ depth =>
                  refine List.mem_append_right _ ?_
                  exact inductionHypothesis leftRest rightRest position
                    (by simp only [List.length_cons] at bound ⊢; omega)
                    ⟨depth, entry, by rwa [List.getD_cons_succ] at mem, addr⟩

/-- Every address of the scan lies at depth at least `offset`. -/
theorem scanAddressFuel_mem_length (fuel : ℕ) :
    ∀ (left right : List (List (OfficialSparseEntry ℕ))) (offset : ℕ),
      RowsAtDepth offset left → RowsAtDepth offset right →
      ∀ position ∈ scanAddressFuel fuel left right, offset ≤ position.length := by
  induction fuel with
  | zero => intro left right offset _ _ position present; simp [scanAddressFuel] at present
  | succ fuel inductionHypothesis =>
      intro left right offset rowsLeft rowsRight position present
      cases left with
      | nil =>
          cases right with
          | nil => simp [scanAddressFuel] at present
          | cons rightLayer rightRest =>
              rw [scanAddressFuel_succ_nil_cons] at present
              rcases List.mem_append.mp present with headPresent | tailPresent
              · obtain ⟨entry, mem, addr⟩ := List.mem_map.mp headPresent
                have := RowsAtDepth.head rowsRight entry mem
                rw [← addr, this]
              · have := inductionHypothesis [] rightRest (offset + 1)
                  (by intro d e h; simp at h) (RowsAtDepth.tail rowsRight) position tailPresent
                omega
      | cons leftLayer leftRest =>
          cases right with
          | nil =>
              rw [scanAddressFuel_succ_cons_nil] at present
              rcases List.mem_append.mp present with headPresent | tailPresent
              · obtain ⟨entry, mem, addr⟩ := List.mem_map.mp headPresent
                have := RowsAtDepth.head rowsLeft entry mem
                rw [← addr, this]
              · have := inductionHypothesis leftRest [] (offset + 1) (RowsAtDepth.tail rowsLeft)
                  (by intro d e h; simp at h) position tailPresent
                omega
          | cons rightLayer rightRest =>
              rw [scanAddressFuel_succ_cons_cons] at present
              rcases List.mem_append.mp present with headPresent | tailPresent
              · have := mergeAddressFuel_mem_length (leftLayer.length + rightLayer.length)
                  leftLayer rightLayer (RowsAtDepth.head rowsLeft) (RowsAtDepth.head rowsRight)
                  position headPresent
                rw [this]
              · have := inductionHypothesis leftRest rightRest (offset + 1)
                  (RowsAtDepth.tail rowsLeft) (RowsAtDepth.tail rowsRight) position tailPresent
                omega

/-- The scan is strictly increasing in the sphere-major hierarchy order. -/
theorem scanAddressFuel_pairwise (fuel : ℕ) :
    ∀ (left right : List (List (OfficialSparseEntry ℕ))) (offset : ℕ),
      RowsAtDepth offset left → RowsAtDepth offset right →
      RowsIncreasing left → RowsIncreasing right →
      (scanAddressFuel fuel left right).Pairwise HierarchyAddressBefore := by
  induction fuel with
  | zero => intro left right offset _ _ _ _; simp [scanAddressFuel]
  | succ fuel inductionHypothesis =>
      intro left right offset rowsLeft rowsRight incLeft incRight
      cases left with
      | nil =>
          cases right with
          | nil => simp [scanAddressFuel]
          | cons rightLayer rightRest =>
              rw [scanAddressFuel_succ_nil_cons]
              have rightHeadDepth : ∀ entry ∈ rightLayer, entry.1.length = offset :=
                RowsAtDepth.head (offset := offset) (head := rightLayer) (tail := rightRest)
                  rowsRight
              have rightHeadSorted : rightLayer.Pairwise
                  (fun a b => AddressCompare a.1 b.1 = Ordering.lt) := by
                simpa using incRight 0
              have rightTailRows := inductionHypothesis [] rightRest (offset + 1)
                (RowsAtDepth_nil (offset + 1))
                (RowsAtDepth.tail (offset := offset) (head := rightLayer) (tail := rightRest)
                  rowsRight)
                RowsIncreasing_nil
                (RowsIncreasing.tail (head := rightLayer) (tail := rightRest) incRight)
              refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
              · exact pairwise_map_fst_of_row rightLayer rightHeadDepth rightHeadSorted
              · exact rightTailRows
              · intro first firstMem second secondMem
                obtain ⟨firstEntry, firstIn, firstAddr⟩ := List.mem_map.mp firstMem
                have firstLength : first.length = offset := by
                  rw [← firstAddr]
                  exact rightHeadDepth firstEntry firstIn
                have secondLength : offset < second.length :=
                  scanAddressFuel_mem_length fuel [] rightRest (offset + 1)
                    (RowsAtDepth_nil (offset + 1))
                    (RowsAtDepth.tail (offset := offset) (head := rightLayer)
                      (tail := rightRest) rowsRight) second secondMem
                exact hierarchyAddressBefore_of_length_lt (by omega)
      | cons leftLayer leftRest =>
          cases right with
          | nil =>
              rw [scanAddressFuel_succ_cons_nil]
              have leftHeadDepth : ∀ entry ∈ leftLayer, entry.1.length = offset :=
                RowsAtDepth.head (offset := offset) (head := leftLayer) (tail := leftRest)
                  rowsLeft
              have leftHeadSorted : leftLayer.Pairwise
                  (fun a b => AddressCompare a.1 b.1 = Ordering.lt) := by
                simpa using incLeft 0
              have leftTailRows := inductionHypothesis leftRest [] (offset + 1)
                (RowsAtDepth.tail (offset := offset) (head := leftLayer) (tail := leftRest)
                  rowsLeft)
                (RowsAtDepth_nil (offset + 1))
                (RowsIncreasing.tail (head := leftLayer) (tail := leftRest) incLeft)
                RowsIncreasing_nil
              refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
              · exact pairwise_map_fst_of_row leftLayer leftHeadDepth leftHeadSorted
              · exact leftTailRows
              · intro first firstMem second secondMem
                obtain ⟨firstEntry, firstIn, firstAddr⟩ := List.mem_map.mp firstMem
                have firstLength : first.length = offset := by
                  rw [← firstAddr]
                  exact leftHeadDepth firstEntry firstIn
                have secondLength : offset < second.length :=
                  scanAddressFuel_mem_length fuel leftRest [] (offset + 1)
                    (RowsAtDepth.tail (offset := offset) (head := leftLayer)
                      (tail := leftRest) rowsLeft)
                    (RowsAtDepth_nil (offset + 1)) second secondMem
                exact hierarchyAddressBefore_of_length_lt (by omega)
          | cons rightLayer rightRest =>
              rw [scanAddressFuel_succ_cons_cons]
              have leftHeadDepth : ∀ entry ∈ leftLayer, entry.1.length = offset :=
                RowsAtDepth.head (offset := offset) (head := leftLayer) (tail := leftRest)
                  rowsLeft
              have rightHeadDepth : ∀ entry ∈ rightLayer, entry.1.length = offset :=
                RowsAtDepth.head (offset := offset) (head := rightLayer) (tail := rightRest)
                  rowsRight
              have leftHeadSorted : leftLayer.Pairwise
                  (fun a b => AddressCompare a.1 b.1 = Ordering.lt) := by
                simpa using incLeft 0
              have rightHeadSorted : rightLayer.Pairwise
                  (fun a b => AddressCompare a.1 b.1 = Ordering.lt) := by
                simpa using incRight 0
              have tailRows := inductionHypothesis leftRest rightRest (offset + 1)
                (RowsAtDepth.tail (offset := offset) (head := leftLayer) (tail := leftRest)
                  rowsLeft)
                (RowsAtDepth.tail (offset := offset) (head := rightLayer) (tail := rightRest)
                  rowsRight)
                (RowsIncreasing.tail (head := leftLayer) (tail := leftRest) incLeft)
                (RowsIncreasing.tail (head := rightLayer) (tail := rightRest) incRight)
              refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
              · exact mergeAddressFuel_pairwise (leftLayer.length + rightLayer.length)
                  leftLayer rightLayer leftHeadDepth rightHeadDepth leftHeadSorted rightHeadSorted
              · exact tailRows
              · intro first firstMem second secondMem
                have firstLength : first.length = offset :=
                  mergeAddressFuel_mem_length (leftLayer.length + rightLayer.length)
                    leftLayer rightLayer leftHeadDepth rightHeadDepth first firstMem
                have secondLength : offset < second.length :=
                  scanAddressFuel_mem_length fuel leftRest rightRest (offset + 1)
                    (RowsAtDepth.tail (offset := offset) (head := leftLayer)
                      (tail := leftRest) rowsLeft)
                    (RowsAtDepth.tail (offset := offset) (head := rightLayer)
                      (tail := rightRest) rowsRight) second secondMem
                exact hierarchyAddressBefore_of_length_lt (by omega)

/-! ## Head blocks against an absent side -/

theorem compareLex_zero_head_lt {offset : ℕ} {right : List (List (OfficialSparseEntry ℕ))}
    {row : List (OfficialSparseEntry ℕ)} (nonempty : row ≠ [])
    (rowDepth : ∀ entry ∈ row, entry.1.length = offset)
    (rowPositive : ∀ entry ∈ row, 0 < entry.2) :
    List.compareLex OfficialRuleMajorKey.compareNat
        ((row.map Prod.fst).map (relativeValueAt offset
          ([] : List (List (OfficialSparseEntry ℕ)))))
        ((row.map Prod.fst).map (relativeValueAt offset (row :: right))) =
      Ordering.lt := by
  cases row with
  | nil => exact absurd rfl nonempty
  | cons entry rest =>
      have leftZero : relativeValueAt offset
          ([] : List (List (OfficialSparseEntry ℕ))) entry.1 = 0 := rfl
      have rightValue : relativeValueAt offset ((entry :: rest) :: right) entry.1 =
          entry.2 := by
        rw [relativeValueAt_head offset (entry :: rest) right entry.1
          (rowDepth entry (by simp))]
        exact rowValueAt_cons_self entry rest
      simp only [List.map_cons, List.compareLex_cons_cons, leftZero, rightValue,
        compareNat_lt_iff_lt.mpr (rowPositive entry (by simp))]
      rfl

theorem compareLex_head_zero_gt {offset : ℕ} {left : List (List (OfficialSparseEntry ℕ))}
    {row : List (OfficialSparseEntry ℕ)} (nonempty : row ≠ [])
    (rowDepth : ∀ entry ∈ row, entry.1.length = offset)
    (rowPositive : ∀ entry ∈ row, 0 < entry.2) :
    List.compareLex OfficialRuleMajorKey.compareNat
        ((row.map Prod.fst).map (relativeValueAt offset (row :: left)))
        ((row.map Prod.fst).map (relativeValueAt offset
          ([] : List (List (OfficialSparseEntry ℕ))))) =
      Ordering.gt := by
  cases row with
  | nil => exact absurd rfl nonempty
  | cons entry rest =>
      have rightZero : relativeValueAt offset
          ([] : List (List (OfficialSparseEntry ℕ))) entry.1 = 0 := rfl
      have leftValue : relativeValueAt offset ((entry :: rest) :: left) entry.1 =
          entry.2 := by
        rw [relativeValueAt_head offset (entry :: rest) left entry.1
          (rowDepth entry (by simp))]
        exact rowValueAt_cons_self entry rest
      simp only [List.map_cons, List.compareLex_cons_cons, leftValue, rightZero,
        compareNat_gt_iff_gt.mpr (rowPositive entry (by simp))]
      rfl

/-! ## The executed comparison on the union schedule -/

/-- The executed Rule-1a comparison is the pointwise comparison of the two tables' value
functions on their finite union address schedule. -/
theorem compareSparseLayers_scanAddressFuel (fuel : ℕ) :
    ∀ (offset : ℕ) (left right : List (List (OfficialSparseEntry ℕ))),
      left.length + right.length ≤ fuel →
      RowsAtDepth offset left → RowsAtDepth offset right →
      RowsIncreasing left → RowsIncreasing right →
      RowsNonempty left → RowsNonempty right →
      TablePositive left → TablePositive right →
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat left right =
        List.compareLex OfficialRuleMajorKey.compareNat
          ((scanAddressFuel fuel left right).map (relativeValueAt offset left))
          ((scanAddressFuel fuel left right).map (relativeValueAt offset right)) := by
  induction fuel with
  | zero =>
      intro offset left right bound _ _ _ _ _ _ _ _
      have leftEmpty : left = [] := by
        cases left with
        | nil => rfl
        | cons head tail => simp at bound
      have rightEmpty : right = [] := by
        cases right with
        | nil => rfl
        | cons head tail => simp at bound
      subst leftEmpty
      subst rightEmpty
      rfl
  | succ fuel inductionHypothesis =>
      intro offset left right bound rowsLeft rowsRight incLeft incRight nonemptyLeft nonemptyRight
        positiveLeft positiveRight
      cases left with
      | nil =>
          cases right with
          | nil => rfl
          | cons rightLayer rightRest =>
              have headDepth : ∀ entry ∈ rightLayer, entry.1.length = offset :=
                RowsAtDepth.head (offset := offset) (head := rightLayer) (tail := rightRest)
                  rowsRight
              rw [show OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
                    [] (rightLayer :: rightRest) = Ordering.lt from rfl,
                scanAddressFuel_succ_nil_cons, List.map_append, List.map_append]
              have splitLex := compareLex_append_append
                (compareValue := OfficialRuleMajorKey.compareNat)
                (leftFirst := (rightLayer.map Prod.fst).map
                  (relativeValueAt offset ([] : List (List (OfficialSparseEntry ℕ)))))
                (rightFirst := (rightLayer.map Prod.fst).map
                  (relativeValueAt offset (rightLayer :: rightRest)))
                (leftSecond := (scanAddressFuel fuel [] rightRest).map
                  (relativeValueAt offset ([] : List (List (OfficialSparseEntry ℕ)))))
                (rightSecond := (scanAddressFuel fuel [] rightRest).map
                  (relativeValueAt offset (rightLayer :: rightRest)))
                (by simp)
              rw [splitLex,
                compareLex_zero_head_lt (offset := offset) (right := rightRest)
                  (row := rightLayer) (nonemptyRight 0 (by simp)) headDepth
                  (fun entry present => positiveRight 0 entry (by simpa using present))]
              rfl
      | cons leftLayer leftRest =>
          cases right with
          | nil =>
              have headDepth : ∀ entry ∈ leftLayer, entry.1.length = offset :=
                RowsAtDepth.head (offset := offset) (head := leftLayer) (tail := leftRest)
                  rowsLeft
              rw [show OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
                    (leftLayer :: leftRest) [] = Ordering.gt from rfl,
                scanAddressFuel_succ_cons_nil, List.map_append, List.map_append]
              have splitLex := compareLex_append_append
                (compareValue := OfficialRuleMajorKey.compareNat)
                (leftFirst := (leftLayer.map Prod.fst).map
                  (relativeValueAt offset (leftLayer :: leftRest)))
                (rightFirst := (leftLayer.map Prod.fst).map
                  (relativeValueAt offset ([] : List (List (OfficialSparseEntry ℕ)))))
                (leftSecond := (scanAddressFuel fuel leftRest []).map
                  (relativeValueAt offset (leftLayer :: leftRest)))
                (rightSecond := (scanAddressFuel fuel leftRest []).map
                  (relativeValueAt offset ([] : List (List (OfficialSparseEntry ℕ)))))
                (by simp)
              rw [splitLex,
                compareLex_head_zero_gt (offset := offset) (left := leftRest)
                  (row := leftLayer) (nonemptyLeft 0 (by simp)) headDepth
                  (fun entry present => positiveLeft 0 entry (by simpa using present))]
              rfl
          | cons rightLayer rightRest =>
              simp only [List.length_cons] at bound
              have leftHeadDepth : ∀ entry ∈ leftLayer, entry.1.length = offset :=
                RowsAtDepth.head (offset := offset) (head := leftLayer) (tail := leftRest)
                  rowsLeft
              have rightHeadDepth : ∀ entry ∈ rightLayer, entry.1.length = offset :=
                RowsAtDepth.head (offset := offset) (head := rightLayer) (tail := rightRest)
                  rowsRight
              have leftHeadSorted : leftLayer.Pairwise
                  (fun a b => AddressCompare a.1 b.1 = Ordering.lt) := by
                simpa using incLeft 0
              have rightHeadSorted : rightLayer.Pairwise
                  (fun a b => AddressCompare a.1 b.1 = Ordering.lt) := by
                simpa using incRight 0
              have leftHeadPositive : ∀ entry ∈ leftLayer, 0 < entry.2 :=
                fun entry present => positiveLeft 0 entry (by simpa using present)
              have rightHeadPositive : ∀ entry ∈ rightLayer, 0 < entry.2 :=
                fun entry present => positiveRight 0 entry (by simpa using present)
              have headValues : (mergeAddresses leftLayer rightLayer).map
                    (relativeValueAt offset (leftLayer :: leftRest)) =
                  (mergeAddresses leftLayer rightLayer).map (rowValueAt leftLayer) := by
                refine List.map_congr_left ?_
                intro position present
                exact relativeValueAt_head offset leftLayer leftRest position
                  (mergeAddressFuel_mem_length (leftLayer.length + rightLayer.length)
                    leftLayer rightLayer leftHeadDepth rightHeadDepth position present)
              have headValuesRight : (mergeAddresses leftLayer rightLayer).map
                    (relativeValueAt offset (rightLayer :: rightRest)) =
                  (mergeAddresses leftLayer rightLayer).map (rowValueAt rightLayer) := by
                refine List.map_congr_left ?_
                intro position present
                exact relativeValueAt_head offset rightLayer rightRest position
                  (mergeAddressFuel_mem_length (leftLayer.length + rightLayer.length)
                    leftLayer rightLayer leftHeadDepth rightHeadDepth position present)
              have headStep : OfficialRuleMajorKey.compareSparseLayer
                    OfficialRuleMajorKey.compareNat leftLayer rightLayer =
                  List.compareLex OfficialRuleMajorKey.compareNat
                    ((mergeAddresses leftLayer rightLayer).map (rowValueAt leftLayer))
                    ((mergeAddresses leftLayer rightLayer).map (rowValueAt rightLayer)) :=
                compareSparseLayer_mergeAddressFuel (leftLayer.length + rightLayer.length)
                  leftLayer rightLayer (by omega) leftHeadSorted rightHeadSorted
                  leftHeadPositive rightHeadPositive
              have tailValues : (scanAddressFuel fuel leftRest rightRest).map
                    (relativeValueAt offset (leftLayer :: leftRest)) =
                  (scanAddressFuel fuel leftRest rightRest).map
                    (relativeValueAt (offset + 1) leftRest) := by
                refine List.map_congr_left ?_
                intro position present
                exact relativeValueAt_tail offset leftLayer leftRest position
                  (scanAddressFuel_mem_length fuel leftRest rightRest (offset + 1)
                    (RowsAtDepth.tail (offset := offset) (head := leftLayer) (tail := leftRest)
                      rowsLeft)
                    (RowsAtDepth.tail (offset := offset) (head := rightLayer) (tail := rightRest)
                      rowsRight) position present)
              have tailValuesRight : (scanAddressFuel fuel leftRest rightRest).map
                    (relativeValueAt offset (rightLayer :: rightRest)) =
                  (scanAddressFuel fuel leftRest rightRest).map
                    (relativeValueAt (offset + 1) rightRest) := by
                refine List.map_congr_left ?_
                intro position present
                exact relativeValueAt_tail offset rightLayer rightRest position
                  (scanAddressFuel_mem_length fuel leftRest rightRest (offset + 1)
                    (RowsAtDepth.tail (offset := offset) (head := leftLayer) (tail := leftRest)
                      rowsLeft)
                    (RowsAtDepth.tail (offset := offset) (head := rightLayer) (tail := rightRest)
                      rowsRight) position present)
              have tailStep := inductionHypothesis (offset + 1) leftRest rightRest
                (by omega)
                (RowsAtDepth.tail (offset := offset) (head := leftLayer) (tail := leftRest)
                  rowsLeft)
                (RowsAtDepth.tail (offset := offset) (head := rightLayer) (tail := rightRest)
                  rowsRight)
                (RowsIncreasing.tail (head := leftLayer) (tail := leftRest) incLeft)
                (RowsIncreasing.tail (head := rightLayer) (tail := rightRest) incRight)
                (RowsNonempty.tail (head := leftLayer) (tail := leftRest) nonemptyLeft)
                (RowsNonempty.tail (head := rightLayer) (tail := rightRest) nonemptyRight)
                (TablePositive.tail (head := leftLayer) (tail := leftRest) positiveLeft)
                (TablePositive.tail (head := rightLayer) (tail := rightRest) positiveRight)
              have layersStep : OfficialRuleMajorKey.compareSparseLayers
                    OfficialRuleMajorKey.compareNat (leftLayer :: leftRest)
                    (rightLayer :: rightRest) =
                  (OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareNat
                      leftLayer rightLayer).then
                    (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
                      leftRest rightRest) := by
                simpa only [OfficialRuleMajorKey.compareSparseLayers] using
                  (List.compareLex_cons_cons (cmp :=
                    OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareNat)
                    (x := leftLayer) (y := rightLayer) (xs := leftRest) (ys := rightRest))
              rw [layersStep,
                scanAddressFuel_succ_cons_cons, List.map_append, List.map_append]
              have splitLex := compareLex_append_append
                (compareValue := OfficialRuleMajorKey.compareNat)
                (leftFirst := (mergeAddresses leftLayer rightLayer).map
                  (relativeValueAt offset (leftLayer :: leftRest)))
                (rightFirst := (mergeAddresses leftLayer rightLayer).map
                  (relativeValueAt offset (rightLayer :: rightRest)))
                (leftSecond := (scanAddressFuel fuel leftRest rightRest).map
                  (relativeValueAt offset (leftLayer :: leftRest)))
                (rightSecond := (scanAddressFuel fuel leftRest rightRest).map
                  (relativeValueAt offset (rightLayer :: rightRest)))
                (by simp)
              rw [splitLex, headValues, headValuesRight, headStep, tailStep,
                tailValues, tailValuesRight]

/-- The executed Rule-1a comparison, read on the finite union schedule. -/
theorem compareSparseLayers_eq_compareLex_unionAddresses
    {left right : List (List (OfficialSparseEntry ℕ))}
    (wellFormedLeft : SparseTableWellFormed left)
    (wellFormedRight : SparseTableWellFormed right)
    (positiveLeft : TablePositive left) (positiveRight : TablePositive right) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat left right =
      List.compareLex OfficialRuleMajorKey.compareNat
        ((unionAddresses left right).map (tableValue left))
        ((unionAddresses left right).map (tableValue right)) :=
  compareSparseLayers_scanAddressFuel (left.length + right.length) 0 left right
    (Nat.le_refl _) wellFormedLeft.depthExact wellFormedRight.depthExact
    wellFormedLeft.increasing wellFormedRight.increasing
    wellFormedLeft.nonempty wellFormedRight.nonempty positiveLeft positiveRight

theorem unionAddresses_pairwise
    {left right : List (List (OfficialSparseEntry ℕ))}
    (wellFormedLeft : SparseTableWellFormed left)
    (wellFormedRight : SparseTableWellFormed right) :
    (unionAddresses left right).Pairwise HierarchyAddressBefore :=
  scanAddressFuel_pairwise (left.length + right.length) left right 0
    wellFormedLeft.depthExact wellFormedRight.depthExact
    wellFormedLeft.increasing wellFormedRight.increasing

theorem unionAddresses_outside
    {left right : List (List (OfficialSparseEntry ℕ))}
    (_wellFormedLeft : SparseTableWellFormed left)
    (_wellFormedRight : SparseTableWellFormed right) :
    ∀ position, position ∉ unionAddresses left right →
      OfficialRuleMajorKey.compareNat (tableValue left position)
        (tableValue right position) = Ordering.eq := by
  intro position absent
  have leftZero : tableValue left position = 0 := by
    refine tableValue_eq_zero_of_absent left position ?_
    intro depth entry present same
    exact absent (mem_scanAddressFuel_of_mem_left (left.length + right.length) left right
      position (Nat.le_refl _) ⟨depth, entry, present, same⟩)
  have rightZero : tableValue right position = 0 := by
    refine tableValue_eq_zero_of_absent right position ?_
    intro depth entry present same
    exact absent (mem_scanAddressFuel_of_mem_right (left.length + right.length) left right
      position (Nat.le_refl _) ⟨depth, entry, present, same⟩)
  rw [leftZero, rightZero, compareNat_zero_zero]

/-- A Rule-1a tie forces both tables to agree at every address. -/
theorem tableValue_eq_of_compareSparseLayers_eq
    {left right : List (List (OfficialSparseEntry ℕ))}
    (wellFormedLeft : SparseTableWellFormed left)
    (wellFormedRight : SparseTableWellFormed right)
    (positiveLeft : TablePositive left) (positiveRight : TablePositive right)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left right = Ordering.eq) :
    ∀ position, tableValue left position = tableValue right position := by
  have allTie : ∀ position, OfficialRuleMajorKey.compareNat (tableValue left position)
      (tableValue right position) = Ordering.eq := by
    refine (compareLex_map_iff_firstDifference OfficialRuleMajorKey.compareNat
      (tableValue left) (tableValue right) (unionAddresses left right)
      (unionAddresses_pairwise wellFormedLeft wellFormedRight)
      (unionAddresses_outside wellFormedLeft wellFormedRight) Ordering.eq).mp ?_
    rw [← compareSparseLayers_eq_compareLex_unionAddresses wellFormedLeft wellFormedRight
      positiveLeft positiveRight]
    exact tied
  intro position
  exact compareNat_eq_iff_eq.mp (allTie position)

/-- A Rule-1a tie forces identical address supports: the same positions carry observations in
both tables. -/
theorem sameSupport_of_compareSparseLayers_eq
    {left right : List (List (OfficialSparseEntry ℕ))}
    (wellFormedLeft : SparseTableWellFormed left)
    (wellFormedRight : SparseTableWellFormed right)
    (positiveLeft : TablePositive left) (positiveRight : TablePositive right)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left right = Ordering.eq) :
    ∀ position,
      (∃ depth entry, entry ∈ left.getD depth [] ∧ entry.1 = position) ↔
        (∃ depth entry, entry ∈ right.getD depth [] ∧ entry.1 = position) := by
  intro position
  have values := tableValue_eq_of_compareSparseLayers_eq wellFormedLeft wellFormedRight
    positiveLeft positiveRight tied position
  constructor
  · rintro ⟨depth, entry, present, addr⟩
    have lengthEq : entry.1.length = depth := by
      simpa using wellFormedLeft.depthExact depth entry present
    have positive : 0 < tableValue left position := by
      unfold tableValue
      rw [← addr, lengthEq]
      exact rowValueAt_pos_of_mem _ _ (fun other otherMem => positiveLeft depth other otherMem)
        ⟨entry, present, rfl⟩
    have nonzero : tableValue right position ≠ 0 := by
      rw [← values]
      omega
    obtain ⟨found, foundMem, foundAt⟩ :=
      exists_mem_of_rowValueAt_ne_zero (right.getD position.length []) position nonzero
    exact ⟨position.length, found, foundMem, foundAt⟩
  · rintro ⟨depth, entry, present, addr⟩
    have lengthEq : entry.1.length = depth := by
      simpa using wellFormedRight.depthExact depth entry present
    have positive : 0 < tableValue right position := by
      unfold tableValue
      rw [← addr, lengthEq]
      exact rowValueAt_pos_of_mem _ _ (fun other otherMem => positiveRight depth other otherMem)
        ⟨entry, present, rfl⟩
    have nonzero : tableValue left position ≠ 0 := by
      rw [values]
      omega
    obtain ⟨found, foundMem, foundAt⟩ :=
      exists_mem_of_rowValueAt_ne_zero (left.getD position.length []) position nonzero
    exact ⟨position.length, found, foundMem, foundAt⟩

/-- The executed Rule-1a comparison *is* the independent relational first difference of the
tables' descending observations over the finite union address schedule. -/
theorem compareSparseLayers_eq_firstDifference
    {left right : List (List (OfficialSparseEntry ℕ))}
    (wellFormedLeft : SparseTableWellFormed left)
    (wellFormedRight : SparseTableWellFormed right)
    (positiveLeft : TablePositive left) (positiveRight : TablePositive right)
    (outcome : Ordering) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat left right =
        outcome ↔
      FirstDifferenceOutcome
        (fun position result =>
          DescendingNatOutcome (tableValue left position) (tableValue right position) result)
        outcome := by
  rw [compareSparseLayers_eq_compareLex_unionAddresses wellFormedLeft wellFormedRight
    positiveLeft positiveRight]
  rw [compareLex_map_iff_firstDifference OfficialRuleMajorKey.compareNat
    (tableValue left) (tableValue right) (unionAddresses left right)
    (unionAddresses_pairwise wellFormedLeft wellFormedRight)
    (unionAddresses_outside wellFormedLeft wellFormedRight) outcome]
  exact FirstDifferenceOutcome.congr
    (fun position result => compareNat_iff_descendingNatOutcome _ _ _) outcome

/-! ## Arbitrary scalar comparator on a common address support

The Rule-1a analysis above reads absent addresses as `0`, which is legitimate only because the
sparse observations are positive natural numbers.  The later Rule-1b distance and isotope mass
comparators are reversed (smaller wins) and have a meaningful `0`, so absence must not be filled
with a default there.  Once Rule 1a has tied, the two addressed supports coincide
(`sameSupport_of_compareSparseLayers_eq`), and every later comparison runs on the common support.
The following results give that common-support scan for an arbitrary scalar comparator: no
zero filling, no positivity, no direction assumption. -/

/-- With equal layer count and equal sphere cardinalities, the layered lexicographic comparison is
the flattened entry comparison. -/
theorem compareLex_layerList_eq_compareLex_flatten {α : Type*}
    (compareObservation : α → α → Ordering) :
    ∀ (left right : List (List (OfficialSparseEntry α))),
      left.length = right.length →
      (∀ depth, (left.getD depth []).length = (right.getD depth []).length) →
      List.compareLex (OfficialRuleMajorKey.compareSparseLayer compareObservation) left right =
        List.compareLex (OfficialRuleMajorKey.compareSparseEntry compareObservation)
          left.flatten right.flatten := by
  intro left
  induction left with
  | nil =>
      intro right lengthEq _
      cases right with
      | nil => rfl
      | cons rightHead rightTail => simp at lengthEq
  | cons head tail inductionHypothesis =>
      intro right lengthEq cardinality
      cases right with
      | nil => simp at lengthEq
      | cons rightHead rightTail =>
          have tailLength : tail.length = rightTail.length := by simpa using lengthEq
          have headLength : head.length = rightHead.length := by
            have zero := cardinality 0
            simpa using zero
          have tailCards : ∀ depth,
              (tail.getD depth []).length = (rightTail.getD depth []).length := by
            intro depth
            have step := cardinality (depth + 1)
            simpa using step
          show List.compareLex
              (List.compareLex (OfficialRuleMajorKey.compareSparseEntry compareObservation))
              (head :: tail) (rightHead :: rightTail) =
            List.compareLex (OfficialRuleMajorKey.compareSparseEntry compareObservation)
              (head :: tail).flatten (rightHead :: rightTail).flatten
          rw [List.compareLex_cons_cons, List.flatten_cons, List.flatten_cons]
          have tailStep :
              List.compareLex
                  (List.compareLex (OfficialRuleMajorKey.compareSparseEntry compareObservation))
                  tail rightTail =
                List.compareLex (OfficialRuleMajorKey.compareSparseEntry compareObservation)
                  tail.flatten rightTail.flatten :=
            inductionHypothesis rightTail tailLength tailCards
          rw [tailStep]
          rw [← compareLex_append_append
            (OfficialRuleMajorKey.compareSparseEntry compareObservation) headLength]

/-- When the two flattened address sequences coincide, comparing entries by the sparse-entry
comparator is comparing the observations pointwise; the paths never decide. -/
theorem compareLex_flatten_eq_compareLex_observations {α : Type*}
    (compareObservation : α → α → Ordering) :
    ∀ (left right : List (OfficialSparseEntry α)),
      left.map Prod.fst = right.map Prod.fst →
      List.compareLex (OfficialRuleMajorKey.compareSparseEntry compareObservation) left right =
        List.compareLex compareObservation (left.map Prod.snd) (right.map Prod.snd) := by
  intro left
  induction left with
  | nil =>
      intro right same
      cases right with
      | nil => rfl
      | cons rightEntry rightTail => simp at same
  | cons leftEntry leftTail inductionHypothesis =>
      intro right same
      cases right with
      | nil => simp at same
      | cons rightEntry rightTail =>
          simp only [List.map_cons, List.cons.injEq] at same
          obtain ⟨headSame, tailSame⟩ := same
          simp only [List.map_cons, List.compareLex_cons_cons]
          rw [compareSparseEntry_eq_of_address_eq compareObservation headSame,
            inductionHypothesis rightTail tailSame]

/-- The executed comparison with an arbitrary scalar comparator on a common address support is
exactly the pointwise comparison of the observations along the shared flattened address sequence.
No absent address is filled, so this covers the reversed Rule-1b distance and mass comparators. -/
theorem compareSparseLayers_eq_compareLex_commonSupport {α : Type*}
    (compareObservation : α → α → Ordering)
    {left right : List (List (OfficialSparseEntry α))}
    (lengthEq : left.length = right.length)
    (cardinality : ∀ depth, (left.getD depth []).length = (right.getD depth []).length)
    (sameAddresses : left.flatten.map Prod.fst = right.flatten.map Prod.fst) :
    OfficialRuleMajorKey.compareSparseLayers compareObservation left right =
      List.compareLex compareObservation
        (left.flatten.map Prod.snd) (right.flatten.map Prod.snd) := by
  have layered :
      List.compareLex (OfficialRuleMajorKey.compareSparseLayer compareObservation) left right =
        List.compareLex (OfficialRuleMajorKey.compareSparseEntry compareObservation)
          left.flatten right.flatten :=
    compareLex_layerList_eq_compareLex_flatten compareObservation left right lengthEq cardinality
  have flattened :=
    compareLex_flatten_eq_compareLex_observations compareObservation
      left.flatten right.flatten sameAddresses
  exact layered.trans flattened

/-! ## Tree-derived row depths -/

/-- The first component of a `zipIdx` pair is one of the zipped values. -/
theorem mem_fst_of_mem_zipIdx {α : Type*} :
    ∀ (values : List α) (start : ℕ) (pair : α × ℕ),
      pair ∈ values.zipIdx start → pair.1 ∈ values
  | [], _, _, present => by simp at present
  | head :: tail, start, pair, present => by
      rw [List.zipIdx_cons] at present
      rcases List.mem_cons.mp present with equal | later
      · rcases equal with rfl
        simp
      · exact List.mem_cons_of_mem head
          (mem_fst_of_mem_zipIdx tail (start + 1) pair later)

/-- Every entry of the compiled table at depth `depth` has address length `depth`; the root sphere
is the only depth-zero entry and child spheres are prefixed by exactly one sibling slot.  This is
derived from the table recursion, independently of the recursive sibling ordering. -/
theorem table_rowsAtDepth {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → ℕ) :
    ∀ tree : LocalizedCumulativeDecoratedTree input carrierFuel,
      RowsAtDepth 0 (LocalizedCumulativeDecoratedTree.table observe tree) := by
  have main : ∀ n : ℕ,
      ∀ candidate : LocalizedCumulativeDecoratedTree input carrierFuel,
        LocalizedCumulativeDecoratedTree.height candidate ≤ n →
          RowsAtDepth 0 (LocalizedCumulativeDecoratedTree.table observe candidate) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro k inductionHypothesis candidate bound depth entry present
    cases depth with
    | zero =>
        rw [LocalizedCumulativeDecoratedTree.table_getD_zero observe candidate] at present
        have entryEq : entry = ([], observe candidate) := by simpa using present
        rw [entryEq]
        simp
    | succ depth =>
        rw [LocalizedCumulativeDecoratedTree.table_eq_root_merge observe candidate] at present
        rw [LocalizedCumulativeDecoratedTree.getD_root_cons] at present
        rw [LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables,
          SparseAddress.mergePairTable_getD] at present
        by_cases inside :
            depth < LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount
              (candidate.children.map (LocalizedCumulativeDecoratedTree.table observe))
        · rw [if_pos inside] at present
          rw [SparseAddress.mergePairs, List.mem_flatMap] at present
          obtain ⟨pair, pairMem, entryMem⟩ := present
          simp only [OfficialRuleMajorKey.prefixLayer, id_eq] at entryMem
          obtain ⟨inner, innerMem, entryEq⟩ := List.mem_map.mp entryMem
          rw [← entryEq]
          have pairFst : pair.1 ∈
              candidate.children.map (LocalizedCumulativeDecoratedTree.table observe) :=
            mem_fst_of_mem_zipIdx
              (candidate.children.map (LocalizedCumulativeDecoratedTree.table observe))
              0 pair pairMem
          obtain ⟨child, childMem, childEq⟩ := List.mem_map.mp pairFst
          rw [← childEq] at innerMem
          have childRows :=
            inductionHypothesis (LocalizedCumulativeDecoratedTree.height child)
              (by
                have smaller :=
                  LocalizedCumulativeDecoratedTree.height_lt_height_of_mem candidate childMem
                omega)
              child (le_refl _)
          have innerLength := childRows depth inner innerMem
          simp only [List.length_cons]
          omega
        · rw [if_neg inside] at present
          simp at present
  intro tree
  exact main (LocalizedCumulativeDecoratedTree.height tree) tree (le_refl _)

/-! ## The compiled cumulative tree table -/

/-- Every sphere below the compiled table's length is inhabited.  This is derived from the tree
reconstruction (`table_sphere_nonempty` together with `table_length_eq_height`), not assumed of
the table. -/
theorem table_rowsNonempty {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → ℕ)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    RowsNonempty (LocalizedCumulativeDecoratedTree.table observe tree) := by
  intro depth below
  refine LocalizedCumulativeDecoratedTree.table_sphere_nonempty observe tree depth ?_
  rwa [LocalizedCumulativeDecoratedTree.table_length_eq_height observe tree] at below

/-- A compiled tree table is well formed as soon as its rows are known to sit at exact depth and
to be increasing in the executed address order; the nonempty-sphere condition is derived from the
tree reconstruction rather than assumed. -/
theorem table_wellFormed_of_rows {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → ℕ)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (depthExact : RowsAtDepth 0 (LocalizedCumulativeDecoratedTree.table observe tree))
    (increasing : RowsIncreasing (LocalizedCumulativeDecoratedTree.table observe tree)) :
    SparseTableWellFormed (LocalizedCumulativeDecoratedTree.table observe tree) :=
  ⟨depthExact, increasing, table_rowsNonempty observe tree⟩





theorem table_wellFormed_of_order {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → ℕ)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (increasing : RowsIncreasing (LocalizedCumulativeDecoratedTree.table observe tree)) :
    SparseTableWellFormed (LocalizedCumulativeDecoratedTree.table observe tree) :=
  ⟨table_rowsAtDepth observe tree, increasing, table_rowsNonempty observe tree⟩

/-- The executed Rule-1a comparison of two complete positive compiled tree tables is exactly the
independent relational first difference of their observations over the finite union address
schedule. -/
theorem table_compareSparseLayers_eq_firstDifference {input : CertifiedLocalizedCIPInput}
    {carrierFuel : ℕ}
    {observeLeft observeRight : LocalizedCumulativeDecoratedTree input carrierFuel → ℕ}
    {leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (wellFormedLeft :
      SparseTableWellFormed (LocalizedCumulativeDecoratedTree.table observeLeft leftTree))
    (wellFormedRight :
      SparseTableWellFormed (LocalizedCumulativeDecoratedTree.table observeRight rightTree))
    (positiveLeft :
      TablePositive (LocalizedCumulativeDecoratedTree.table observeLeft leftTree))
    (positiveRight :
      TablePositive (LocalizedCumulativeDecoratedTree.table observeRight rightTree))
    (outcome : Ordering) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (LocalizedCumulativeDecoratedTree.table observeLeft leftTree)
        (LocalizedCumulativeDecoratedTree.table observeRight rightTree) = outcome ↔
      FirstDifferenceOutcome
        (fun position result =>
          DescendingNatOutcome
            (tableValue (LocalizedCumulativeDecoratedTree.table observeLeft leftTree) position)
            (tableValue (LocalizedCumulativeDecoratedTree.table observeRight rightTree) position)
            result)
        outcome :=
  compareSparseLayers_eq_firstDifference wellFormedLeft wellFormedRight
    positiveLeft positiveRight outcome

end SparsePhysicalFirstDifference

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.compareNat_eq_iff_eq
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.compareNat_lt_iff_lt
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.compareNat_gt_iff_gt
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.compareNat_swap
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.compareNat_zero_zero
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.compareNat_iff_descendingNatOutcome
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.compareLex_refl
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.compareLex_swap
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.AddressCompare_refl
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.AddressCompare_swap
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.AddressCompare_gt_of_lt
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.AddressCompare_lt_of_gt
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.ne_of_AddressCompare_lt
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.AddressCompare_eq_iff
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.listLex_cons_cons_iff
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.AddressCompare_lt_iff_lex
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.listLex_lt_trans
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.AddressCompare_lt_trans
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.hierarchyAddressBefore_of_AddressCompare_lt
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.hierarchyAddressBefore_of_length_lt
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.rowValueAt_cons_of_ne
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.rowValueAt_eq_zero_of_absent
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.rowValueAt_pos_of_mem
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.exists_mem_of_rowValueAt_ne_zero
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.tableValue_eq_relativeValueAt_zero
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.relativeValueAt_head
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.relativeValueAt_tail
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.tableValue_eq_zero_of_absent
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.mergeAddressFuel_zero
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.mergeAddressFuel_succ_nil
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.mergeAddressFuel_succ_nil_right
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.mergeAddressFuel_succ_cons_cons
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.mergeAddressFuel_succ_cons_cons_lt
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.mergeAddressFuel_succ_cons_cons_gt
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.mergeAddressFuel_succ_cons_cons_eq
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.mem_mergeAddressFuel
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.mergeAddressFuel_mem_length
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.mem_mergeAddressFuel_of_mem_left
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.mem_mergeAddressFuel_of_mem_right
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.pairwise_map_fst_of_row
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.mergeAddressFuel_pairwise
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.compareSparseEntry_def
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.compareSparseEntry_eq_of_address_eq
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.compareSparseEntry_gt_of_address_lt
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.compareSparseEntry_lt_of_address_gt
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.Ordering_then_assoc
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.compareLex_append_append
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.compareSparseLayer_mergeAddressFuel
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.scanAddressFuel_zero
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.scanAddressFuel_succ_nil_nil
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.scanAddressFuel_succ_nil_cons
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.scanAddressFuel_succ_cons_nil
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.scanAddressFuel_succ_cons_cons
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.RowsAtDepth.tail
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.RowsAtDepth.head
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.RowsIncreasing.tail
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.RowsNonempty.tail
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.TablePositive.tail
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.RowsAtDepth_nil
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.RowsIncreasing_nil
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.mem_scanAddressFuel
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.mem_scanAddressFuel_of_mem_left
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.mem_scanAddressFuel_of_mem_right
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.scanAddressFuel_mem_length
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.scanAddressFuel_pairwise
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.compareLex_zero_head_lt
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.compareLex_head_zero_gt
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.compareSparseLayers_scanAddressFuel
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.compareSparseLayers_eq_compareLex_unionAddresses
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.unionAddresses_pairwise
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.unionAddresses_outside
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.tableValue_eq_of_compareSparseLayers_eq
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.sameSupport_of_compareSparseLayers_eq
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.compareSparseLayers_eq_firstDifference
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.compareLex_layerList_eq_compareLex_flatten
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.compareLex_flatten_eq_compareLex_observations
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.compareSparseLayers_eq_compareLex_commonSupport
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.mem_fst_of_mem_zipIdx
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.table_rowsAtDepth
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.table_rowsNonempty
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.table_wellFormed_of_rows
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.table_wellFormed_of_order
assert_kernel_only TetraStereo.OneCenter.SparsePhysicalFirstDifference.table_compareSparseLayers_eq_firstDifference
