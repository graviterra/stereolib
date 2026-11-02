import TetraStereo.OneCenter.LocalizedActualMolecularEvidenceRefinement
import TetraStereo.OneCenter.LocalizedRealizedTreeCutIsomorphism
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

/-!
# Same-stage cumulative comparator algebra

The production cumulative key `compareLocalizedRerootCumulativeRule45Keys` compares siblings
*node-major*: the sparse table of cumulative node vectors `localizedCumulativeRule45Priority stage`
is compared sphere by sphere, so every component of one node is read before any component of the
next node.  The independent rule-major family `compareRuleMajorCumulativeDescriptor` compares the
same descriptor columns *rule-major*: the projection of one component over the whole hierarchy is
exhausted before the next component is read.

This module proves that, **at one shared stage** and under the structural hypotheses that the two
compiled trees have the same erased shape, both reader labels are `none` or chiral (no
pseudoasymmetric label), and the labels have the same kind at corresponding positions
(`none ↔ none`), the two comparators agree.  That is pure comparison algebra: no physical
hypothesis, no selected reference, no canonical reading order and no different-stage transport is
used or claimed.

The mathematical content is a first-difference argument.  Under a shared stage, component `0`
(Rule 4a) and component `2` (Rule 4c) are equal wherever the pairs agree in kind; and for
`.rule5 rb r5` the two variable bits (Rule 4b and Rule 5) differ at exactly the same addresses,
because `RS` has two elements, so `(a == r) = (b == r) ↔ a = b` for every reference `r`.  Hence at
the first node where the two node vectors differ the controlling component is the same component
(`controllingComponent stage`) that decides the first rule-major difference, and all earlier
components tie everywhere.  The shared-stage restriction is essential: with different Rule-4b
references on the two sides the 4b and 5 bits would no longer synchronize.

The deliverables of this file are:

* the single-component reduction `controllingComponent_spec`: under a shared stage and matching
  `none`/chiral kinds, every component strictly before `controllingComponent stage` is equal and
  every vector difference is already a difference of that component;
* the entry, layer and table projection identities comparing node-major vectors against the
  projected controlling component;
* `compareSparseLayers_priority_eq_firstNonEq` and `compareSparseLayers_eq_ruleMajorSchedule`: the
  node-major sparse-table comparison is the first non-tie of the rule-major schedule of projected
  columns, which is exactly the descriptor component of `compareRuleMajorCumulativeDescriptor`.

All exported facts are kernel-authority guarded.
-/

namespace TetraStereo.OneCenter

namespace SameStageKindComparison

open CertifiedLocalizedCIPInput

/-! ## Ordering and list algebra -/

/-- `Ord.compare` on `Ordering` against `eq` is the identity: `eq` is the middle constructor. -/
theorem ordering_compare_eq_self (o : Ordering) : compare o Ordering.eq = o := by
  cases o <;> rfl

/-- The production `Nat` comparator decides equality exactly. -/
theorem compareNat_eq_iff (left right : Nat) :
    OfficialRuleMajorKey.compareNat left right = Ordering.eq ↔ left = right := by
  unfold OfficialRuleMajorKey.compareNat
  exact compare_eq_iff_eq

/-- The production `Nat` comparator is reflexive. -/
theorem compareNat_self (value : Nat) : OfficialRuleMajorKey.compareNat value value = Ordering.eq :=
  (compareNat_eq_iff value value).mpr rfl

/-- A lexicographic list comparison is reflexive on a reflexive comparator. -/
theorem listCompareLex_self {α : Type*} (cmp : α → α → Ordering)
    (hcmp : ∀ a, cmp a a = Ordering.eq) :
    ∀ list : List α, List.compareLex cmp list list = Ordering.eq
  | [] => rfl
  | a :: rest => by
      rw [List.compareLex_cons_cons, hcmp a, Ordering.eq_then]
      exact listCompareLex_self cmp hcmp rest

/-- `List.compareLex` distributes over an append when the two leading lists have the same length. -/
theorem listCompareLex_append {α : Type*} (cmp : α → α → Ordering) :
    ∀ {left₁ left₂ : List α}, left₁.length = left₂.length →
      ∀ right₁ right₂ : List α,
        List.compareLex cmp (left₁ ++ right₁) (left₂ ++ right₂) =
          (List.compareLex cmp left₁ left₂).then (List.compareLex cmp right₁ right₂)
  | [], [], _, _, _ => rfl
  | [], _ :: _, hlen, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _ => by simp at hlen
  | _ :: _, _ :: _, hlen, right₁, right₂ => by
      rw [List.cons_append, List.cons_append, List.compareLex_cons_cons,
        List.compareLex_cons_cons,
        listCompareLex_append cmp (by simpa using hlen) right₁ right₂,
        Ordering.then_assoc]

/-- The first non-tie entry of a list of comparison outcomes, with `eq` when every entry ties. -/
def firstNonEq : List Ordering → Ordering
  | [] => Ordering.eq
  | Ordering.eq :: rest => firstNonEq rest
  | outcome :: _ => outcome

/-- `firstNonEq` is the `then`-fold of its entries: the first non-tie value short-circuits. -/
theorem firstNonEq_cons (outcome : Ordering) (rest : List Ordering) :
    firstNonEq (outcome :: rest) = outcome.then (firstNonEq rest) := by
  cases outcome <;> rfl

/-- `firstNonEq` of a singleton is its entry. -/
@[simp] theorem firstNonEq_singleton (outcome : Ordering) :
    firstNonEq [outcome] = outcome := by
  cases outcome <;> rfl

/-- A non-tie outcome is unaffected by the tail. -/
theorem ordering_then_self_of_ne_eq (outcome : Ordering) (rest : Ordering)
    (notEq : outcome ≠ Ordering.eq) : outcome.then rest = outcome := by
  cases outcome <;> simp_all

/-- `firstNonEq` splits over an append exactly like the `then`-fold. -/
theorem firstNonEq_append (left right : List Ordering) :
    firstNonEq (left ++ right) =
      if firstNonEq left = Ordering.eq then firstNonEq right else firstNonEq left := by
  induction left with
  | nil => simp [firstNonEq]
  | cons outcome rest inductionHypothesis =>
      cases outcome with
      | eq =>
          rw [List.cons_append, firstNonEq_cons, Ordering.eq_then, inductionHypothesis,
            firstNonEq_cons, Ordering.eq_then]
      | lt => rw [List.cons_append, firstNonEq_cons, firstNonEq_cons]; rfl
      | gt => rw [List.cons_append, firstNonEq_cons, firstNonEq_cons]; rfl

/-- The rule-major descriptor comparison of a list of per-component outcomes against the all-tie
list is exactly the first non-tie outcome. -/
theorem compareLex_orderings_map_eq {α : Type*} (list : List α) (outcome : α → Ordering) :
    List.compareLex compare (list.map outcome) (list.map fun _ => Ordering.eq) =
      firstNonEq (list.map outcome) := by
  induction list with
  | nil => rfl
  | cons head rest inductionHypothesis =>
      rw [List.map_cons, List.map_cons, List.compareLex_cons_cons,
        ordering_compare_eq_self, firstNonEq_cons, inductionHypothesis]

/-- `Ordering.then` ties exactly when both entries tie. -/
theorem ordering_then_eq_eq {left right : Ordering} :
    left.then right = Ordering.eq ↔ left = Ordering.eq ∧ right = Ordering.eq := by
  cases left <;> cases right <;> simp [Ordering.then]

/-- A lexicographic comparison ties exactly when the lists are equal, for a comparator that ties
exactly on equal elements. -/
theorem listCompareLex_eq_iff {α : Type*} (cmp : α → α → Ordering)
    (hcmp : ∀ left right, cmp left right = Ordering.eq ↔ left = right) :
    ∀ left right : List α, List.compareLex cmp left right = Ordering.eq ↔ left = right
  | [], [] => by rw [List.compareLex_nil_nil]; simp
  | [], _ :: _ => by rw [List.compareLex_nil_cons]; simp
  | _ :: _, [] => by rw [List.compareLex_cons_nil]; simp
  | left :: lefts, right :: rights => by
      rw [List.compareLex_cons_cons, ordering_then_eq_eq, hcmp,
        listCompareLex_eq_iff cmp hcmp lefts rights, List.cons.injEq]

/-- The production sparse-entry comparator, unfolded to its address-then-value form. -/
theorem compareSparseEntry_unfold {α : Type*} (cmp : α → α → Ordering)
    (left right : OfficialSparseEntry α) :
    OfficialRuleMajorKey.compareSparseEntry cmp left right =
      (List.compareLex OfficialRuleMajorKey.compareNat right.1 left.1).then
        (cmp left.2 right.2) := rfl

/-- The production sparse-layer comparator, unfolded to a lexicographic list comparison. -/
theorem compareSparseLayer_unfold {α : Type*} (cmp : α → α → Ordering)
    (left right : List (OfficialSparseEntry α)) :
    OfficialRuleMajorKey.compareSparseLayer cmp left right =
      List.compareLex (OfficialRuleMajorKey.compareSparseEntry cmp) left right := rfl

/-- The production sparse-table comparator, unfolded to a lexicographic list comparison. -/
theorem compareSparseLayers_unfold {α : Type*} (cmp : α → α → Ordering)
    (left right : List (List (OfficialSparseEntry α))) :
    OfficialRuleMajorKey.compareSparseLayers cmp left right =
      List.compareLex (OfficialRuleMajorKey.compareSparseLayer cmp) left right := rfl

/-- The production cumulative vector comparator, unfolded to a lexicographic comparison. -/
theorem compareLocalizedCumulativeRule45Priority_unfold (left right : List Nat) :
    compareLocalizedCumulativeRule45Priority left right =
      List.compareLex OfficialRuleMajorKey.compareNat left right := rfl

/-- The sparse-entry comparator ties exactly on equal entries. -/
theorem compareSparseEntry_eq_iff {α : Type*} (cmp : α → α → Ordering)
    (hcmp : ∀ left right, cmp left right = Ordering.eq ↔ left = right) :
    ∀ left right : OfficialSparseEntry α,
      OfficialRuleMajorKey.compareSparseEntry cmp left right = Ordering.eq ↔ left = right := by
  rintro ⟨leftAddress, leftValue⟩ ⟨rightAddress, rightValue⟩
  rw [compareSparseEntry_unfold]
  dsimp only [Prod.fst, Prod.snd]
  rw [ordering_then_eq_eq,
    listCompareLex_eq_iff OfficialRuleMajorKey.compareNat compareNat_eq_iff rightAddress leftAddress,
    hcmp, Prod.mk.injEq]
  constructor
  · rintro ⟨addresses, values⟩
    exact ⟨addresses.symm, values⟩
  · rintro ⟨addresses, values⟩
    exact ⟨addresses.symm, values⟩

/-- The sparse-layer comparator ties exactly on equal layers. -/
theorem compareSparseLayer_eq_iff {α : Type*} (cmp : α → α → Ordering)
    (hcmp : ∀ left right, cmp left right = Ordering.eq ↔ left = right)
    (left right : List (OfficialSparseEntry α)) :
    OfficialRuleMajorKey.compareSparseLayer cmp left right = Ordering.eq ↔ left = right := by
  rw [compareSparseLayer_unfold]
  exact listCompareLex_eq_iff (OfficialRuleMajorKey.compareSparseEntry cmp)
    (compareSparseEntry_eq_iff cmp hcmp) left right

/-- The sparse-table comparator ties exactly on equal tables. -/
theorem compareSparseLayers_eq_iff {α : Type*} (cmp : α → α → Ordering)
    (hcmp : ∀ left right, cmp left right = Ordering.eq ↔ left = right)
    (left right : List (List (OfficialSparseEntry α))) :
    OfficialRuleMajorKey.compareSparseLayers cmp left right = Ordering.eq ↔ left = right := by
  rw [compareSparseLayers_unfold]
  exact listCompareLex_eq_iff (OfficialRuleMajorKey.compareSparseLayer cmp)
    (compareSparseLayer_eq_iff cmp hcmp) left right

/-- The `Nat` sparse-table comparator is reflexive. -/
theorem compareSparseLayers_self (table : List (List (OfficialSparseEntry Nat))) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat table table =
      Ordering.eq :=
  (compareSparseLayers_eq_iff OfficialRuleMajorKey.compareNat compareNat_eq_iff table table).mpr rfl

/-! ## Folding outcomes over an initial segment of components -/

/-- Fold comparison outcomes over a numeric segment, short-circuiting at the first non-tie. -/
def firstNonEqRange (outcome : Nat → Ordering) (start : Nat) : Nat → Ordering
  | 0 => Ordering.eq
  | count + 1 => (outcome start).then (firstNonEqRange outcome (start + 1) count)

/-- `firstNonEqRange` computes `firstNonEq` of the mapped `List.range'` segment. -/
theorem firstNonEq_range'_map (outcome : Nat → Ordering) (start count : Nat) :
    firstNonEq ((List.range' start count).map outcome) = firstNonEqRange outcome start count := by
  induction count generalizing start with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.range'_succ, List.map_cons, firstNonEq_cons, inductionHypothesis (start + 1)]
      rfl

/-- On a segment, if every component other than `focus` ties, the fold is the `focus` component. -/
theorem firstNonEqRange_eq_of_ne (outcome : Nat → Ordering) :
    ∀ (start count focus : Nat),
      (∀ i, start ≤ i → i < start + count → i ≠ focus → outcome i = Ordering.eq) →
      firstNonEqRange outcome start count =
        if start ≤ focus ∧ focus < start + count then outcome focus else Ordering.eq
  | start, 0, focus, _ => by
      rw [if_neg (by omega)]
      rfl
  | start, count + 1, focus, agree => by
      show (outcome start).then (firstNonEqRange outcome (start + 1) count) =
        if start ≤ focus ∧ focus < start + (count + 1) then outcome focus else Ordering.eq
      have restricted : ∀ i, start + 1 ≤ i → i < start + 1 + count → i ≠ focus →
          outcome i = Ordering.eq :=
        fun i lower upper notFocus => agree i (by omega) (by omega) notFocus
      rw [firstNonEqRange_eq_of_ne outcome (start + 1) count focus restricted]
      by_cases atStart : start = focus
      · subst atStart
        rw [if_neg (by omega : ¬ (start + 1 ≤ start ∧ start < start + 1 + count)),
          if_pos (by omega : start ≤ start ∧ start < start + (count + 1))]
        cases outcome start <;> rfl
      · have tied : outcome start = Ordering.eq := agree start le_rfl (by omega) atStart
        rw [tied, Ordering.eq_then]
        by_cases inTail : start + 1 ≤ focus ∧ focus < start + 1 + count
        · rw [if_pos inTail, if_pos (by omega : start ≤ focus ∧ focus < start + (count + 1))]
        · rw [if_neg inTail,
            if_neg (by omega : ¬ (start ≤ focus ∧ focus < start + (count + 1)))]

/-- If every component of a segment ties, the fold ties. -/
theorem firstNonEqRange_eq_of_all_eq (outcome : Nat → Ordering) :
    ∀ (start count : Nat),
      (∀ i, start ≤ i → i < start + count → outcome i = Ordering.eq) →
      firstNonEqRange outcome start count = Ordering.eq
  | start, 0, _ => rfl
  | start, count + 1, agree => by
      show (outcome start).then (firstNonEqRange outcome (start + 1) count) = Ordering.eq
      rw [agree start le_rfl (by omega), Ordering.eq_then]
      exact firstNonEqRange_eq_of_all_eq outcome (start + 1) count
        (fun i lower upper => agree i (by omega) (by omega))

/-- On `List.range width`, if every component other than `focus` ties, the first non-tie is the
`focus` component (or `eq` when the component is out of range). -/
theorem firstNonEq_range_map_of_eq_of_ne {outcome : Nat → Ordering} {focus width : Nat}
    (agree : ∀ i, i < width → i ≠ focus → outcome i = Ordering.eq) :
    firstNonEq ((List.range width).map outcome) =
      if focus < width then outcome focus else Ordering.eq := by
  rw [List.range_eq_range', firstNonEq_range'_map]
  have general := firstNonEqRange_eq_of_ne outcome 0 width focus
    (fun i _ upper notFocus => agree i (by omega) notFocus)
  rw [general]
  by_cases inRange : focus < width
  · rw [if_pos (by omega : 0 ≤ focus ∧ focus < 0 + width), if_pos inRange]
  · rw [if_neg (by omega : ¬ (0 ≤ focus ∧ focus < 0 + width)), if_neg inRange]

/-- If every component ties, the whole rule-major component schedule ties. -/
theorem firstNonEq_range_map_of_all_eq {outcome : Nat → Ordering} {width : Nat}
    (agree : ∀ i, i < width → outcome i = Ordering.eq) :
    firstNonEq ((List.range width).map outcome) = Ordering.eq := by
  rw [List.range_eq_range', firstNonEq_range'_map]
  exact firstNonEqRange_eq_of_all_eq outcome 0 width (fun i _ upper => agree i (by omega))

/-- A fold whose entries before `focus` all tie and whose `focus` entry does not tie is the `focus`
entry, whatever the later entries do. -/
theorem firstNonEqRange_eq_of_before_eq_of_ne (outcome : Nat → Ordering) :
    ∀ (start count focus : Nat), start ≤ focus → focus < start + count →
      (∀ i, start ≤ i → i < focus → outcome i = Ordering.eq) →
      outcome focus ≠ Ordering.eq →
      firstNonEqRange outcome start count = outcome focus
  | start, 0, focus, lower, upper, _, _ => by omega
  | start, count + 1, focus, lower, upper, before, notEq => by
      show (outcome start).then (firstNonEqRange outcome (start + 1) count) = outcome focus
      by_cases atStart : start = focus
      · subst atStart
        exact ordering_then_self_of_ne_eq _ _ notEq
      · have startEq : outcome start = Ordering.eq := before start le_rfl (by omega)
        rw [startEq, Ordering.eq_then]
        exact firstNonEqRange_eq_of_before_eq_of_ne outcome (start + 1) count focus
          (by omega) (by omega) (fun i lower' upper' => before i (by omega) upper') notEq

/-- If every entry before `focus` ties and a tie at `focus` forces every entry to tie, the first
non-tie of the schedule is the `focus` entry. -/
theorem firstNonEq_range_map_eq_focus {outcome : Nat → Ordering} {focus width : Nat}
    (focusBound : focus < width)
    (before : ∀ i, i < focus → outcome i = Ordering.eq)
    (spread : outcome focus = Ordering.eq → ∀ i, i < width → outcome i = Ordering.eq) :
    firstNonEq ((List.range width).map outcome) = outcome focus := by
  by_cases tied : outcome focus = Ordering.eq
  · rw [firstNonEq_range_map_of_all_eq (fun i hi => spread tied i hi), tied]
  · rw [List.range_eq_range', firstNonEq_range'_map]
    exact firstNonEqRange_eq_of_before_eq_of_ne outcome 0 width focus (by omega) (by omega)
      (fun i _ hi => before i hi) tied

/-! ## Kinds and the controlling component -/

/-- A label is either absent or genuinely chiral: no pseudoasymmetric label occurs. -/
def NoneOrChiral (label : Option LocalizedAuxiliaryLabel) : Prop :=
  label = none ∨ ∃ descriptor : RS, label = some (.chiral descriptor)

/-- Two labels have the same kind: both absent or both present. -/
def SameKind (left right : Option LocalizedAuxiliaryLabel) : Prop :=
  (left = none ↔ right = none)

/-- Matching none-or-chiral kinds give equal Rule-4a ranks. -/
theorem rule4aPriority_eq_of_kind {left right : Option LocalizedAuxiliaryLabel}
    (leftKind : NoneOrChiral left) (rightKind : NoneOrChiral right) (same : SameKind left right) :
    localizedRule4aPriority left = localizedRule4aPriority right := by
  rcases leftKind with rfl | ⟨leftDescriptor, rfl⟩
  · rcases rightKind with rfl | ⟨rightDescriptor, rfl⟩
    · rfl
    · exfalso
      simp [SameKind] at same
  · rcases rightKind with rfl | ⟨rightDescriptor, rfl⟩
    · exfalso
      simp [SameKind] at same
    · rfl

/-- None-or-chiral labels have Rule-4c rank zero. -/
theorem rule4cPriority_eq_zero_of_kind {label : Option LocalizedAuxiliaryLabel}
    (kind : NoneOrChiral label) : localizedRule4cPriority label = 0 := by
  rcases kind with rfl | ⟨descriptor, rfl⟩ <;> rfl

/-- Equal labels have equal Rule-4b bits. -/
theorem rule4bPriority_eq_of_eq {reference : RS} {left right : Option LocalizedAuxiliaryLabel}
    (labels : left = right) :
    localizedRule4bPriority reference left = localizedRule4bPriority reference right := by
  rw [labels]

/-- Under matching none-or-chiral kinds, equal Rule-4b bits force equal labels. -/
theorem eq_of_rule4bPriority_eq {reference : RS} {left right : Option LocalizedAuxiliaryLabel}
    (leftKind : NoneOrChiral left) (rightKind : NoneOrChiral right) (same : SameKind left right)
    (bits : localizedRule4bPriority reference left = localizedRule4bPriority reference right) :
    left = right := by
  rcases leftKind with rfl | ⟨leftDescriptor, rfl⟩
  · rcases rightKind with rfl | ⟨rightDescriptor, rfl⟩
    · rfl
    · exfalso
      simp [SameKind] at same
  · rcases rightKind with rfl | ⟨rightDescriptor, rfl⟩
    · exfalso
      simp [SameKind] at same
    · have descriptors : leftDescriptor = rightDescriptor := by
        cases leftDescriptor <;> cases rightDescriptor <;> cases reference <;>
          first | rfl | (exfalso; exact absurd bits (by decide))
      rw [descriptors]

/-- Equal labels have equal Rule-5 bits. -/
theorem rule5Priority_eq_of_eq {reference : RS} {left right : Option LocalizedAuxiliaryLabel}
    (labels : left = right) :
    localizedRule5Priority reference left = localizedRule5Priority reference right := by
  rw [labels]

/-- Under matching none-or-chiral kinds, equal Rule-5 bits force equal labels. -/
theorem eq_of_rule5Priority_eq {reference : RS} {left right : Option LocalizedAuxiliaryLabel}
    (leftKind : NoneOrChiral left) (rightKind : NoneOrChiral right) (same : SameKind left right)
    (bits : localizedRule5Priority reference left = localizedRule5Priority reference right) :
    left = right := by
  rcases leftKind with rfl | ⟨leftDescriptor, rfl⟩
  · rcases rightKind with rfl | ⟨rightDescriptor, rfl⟩
    · rfl
    · exfalso
      simp [SameKind] at same
  · rcases rightKind with rfl | ⟨rightDescriptor, rfl⟩
    · exfalso
      simp [SameKind] at same
    · have descriptors : leftDescriptor = rightDescriptor := by
        cases leftDescriptor <;> cases rightDescriptor <;> cases reference <;>
          first | rfl | (exfalso; exact absurd bits (by decide))
      rw [descriptors]

/-- The single component that controls every difference of the cumulative priority vectors at a
stage.  For `.rule4a` and `.rule4cNoReference` every component is in fact constant under matching
kinds; the listed component is then an arbitrary valid choice. -/
def controllingComponent : LocalizedCumulativeRule45Stage → Nat
  | .rule4a => 0
  | .rule4b _ => 1
  | .rule4cNoReference => 0
  | .rule4c _ => 1
  | .rule5NoRule4bReference _ => 2
  | .rule5 _ _ => 1

/-- **The one-bit control law.**  At one shared stage, matching none-or-chiral kinds make every
component strictly before `controllingComponent stage` equal, and every difference of the two
cumulative vectors is already a difference of that controlling component. -/
theorem controllingComponent_spec (stage : LocalizedCumulativeRule45Stage)
    (left right : Option LocalizedAuxiliaryLabel)
    (leftKind : NoneOrChiral left) (rightKind : NoneOrChiral right)
    (same : SameKind left right) :
    (∀ j, j < controllingComponent stage →
      (localizedCumulativeRule45Priority stage left).getD j 0 =
        (localizedCumulativeRule45Priority stage right).getD j 0) ∧
    (localizedCumulativeRule45Priority stage left ≠
        localizedCumulativeRule45Priority stage right →
      (localizedCumulativeRule45Priority stage left).getD (controllingComponent stage) 0 ≠
        (localizedCumulativeRule45Priority stage right).getD (controllingComponent stage) 0) := by
  cases stage with
  | rule4a =>
      refine ⟨?_, ?_⟩
      · intro j bound
        simp only [controllingComponent] at bound
        omega
      · intro different
        simp only [controllingComponent, localizedCumulativeRule45Priority,
          List.getD_cons_zero] at different ⊢
        intro tied
        exact different (by rw [tied])
  | rule4b reference =>
      refine ⟨?_, ?_⟩
      · intro j bound
        have jz : j = 0 := by
          simp only [controllingComponent] at bound
          omega
        subst jz
        show localizedRule4aPriority left = localizedRule4aPriority right
        exact rule4aPriority_eq_of_kind leftKind rightKind same
      · intro different
        simp only [controllingComponent, localizedCumulativeRule45Priority,
          List.getD_cons_zero, List.getD_cons_succ] at different ⊢
        intro tied
        exact different (by rw [rule4aPriority_eq_of_kind leftKind rightKind same, tied])
  | rule4cNoReference =>
      have fourcEq : localizedRule4cPriority left = localizedRule4cPriority right := by
        rw [rule4cPriority_eq_zero_of_kind leftKind, rule4cPriority_eq_zero_of_kind rightKind]
      refine ⟨?_, ?_⟩
      · intro j bound
        simp only [controllingComponent] at bound
        omega
      · intro different
        simp only [controllingComponent, localizedCumulativeRule45Priority,
          List.getD_cons_zero] at different ⊢
        intro tied
        exact different (by rw [tied, fourcEq])
  | rule4c reference =>
      have fourcEq : localizedRule4cPriority left = localizedRule4cPriority right := by
        rw [rule4cPriority_eq_zero_of_kind leftKind, rule4cPriority_eq_zero_of_kind rightKind]
      refine ⟨?_, ?_⟩
      · intro j bound
        have jz : j = 0 := by
          simp only [controllingComponent] at bound
          omega
        subst jz
        show localizedRule4aPriority left = localizedRule4aPriority right
        exact rule4aPriority_eq_of_kind leftKind rightKind same
      · intro different
        simp only [controllingComponent, localizedCumulativeRule45Priority,
          List.getD_cons_zero, List.getD_cons_succ] at different ⊢
        intro tied
        exact different (by
          rw [rule4aPriority_eq_of_kind leftKind rightKind same, tied, fourcEq])
  | rule5NoRule4bReference rule5Reference =>
      have fourcEq : localizedRule4cPriority left = localizedRule4cPriority right := by
        rw [rule4cPriority_eq_zero_of_kind leftKind, rule4cPriority_eq_zero_of_kind rightKind]
      refine ⟨?_, ?_⟩
      · intro j bound
        have jcases : j = 0 ∨ j = 1 := by
          simp only [controllingComponent] at bound
          omega
        rcases jcases with jz | jz
        · subst jz
          show localizedRule4aPriority left = localizedRule4aPriority right
          exact rule4aPriority_eq_of_kind leftKind rightKind same
        · subst jz
          show localizedRule4cPriority left = localizedRule4cPriority right
          exact fourcEq
      · intro different
        simp only [controllingComponent, localizedCumulativeRule45Priority,
          List.getD_cons_zero, List.getD_cons_succ] at different ⊢
        intro tied
        exact different (by
          rw [rule4aPriority_eq_of_kind leftKind rightKind same, fourcEq, tied])
  | rule5 rule4bReference rule5Reference =>
      have fourcEq : localizedRule4cPriority left = localizedRule4cPriority right := by
        rw [rule4cPriority_eq_zero_of_kind leftKind, rule4cPriority_eq_zero_of_kind rightKind]
      refine ⟨?_, ?_⟩
      · intro j bound
        have jz : j = 0 := by
          simp only [controllingComponent] at bound
          omega
        subst jz
        show localizedRule4aPriority left = localizedRule4aPriority right
        exact rule4aPriority_eq_of_kind leftKind rightKind same
      · intro different
        simp only [controllingComponent, localizedCumulativeRule45Priority,
          List.getD_cons_zero, List.getD_cons_succ] at different ⊢
        intro tied
        have labels : left = right :=
          eq_of_rule4bPriority_eq leftKind rightKind same tied
        exact different (by rw [labels])

/-- The controlling component is inside the cumulative vector width. -/
theorem controllingComponent_lt_width (stage : LocalizedCumulativeRule45Stage) :
    controllingComponent stage < (localizedCumulativeRule45Priority stage none).length := by
  cases stage <;> simp [controllingComponent, localizedCumulativeRule45Priority]

/-- Every cumulative vector of a fixed stage has the same width. -/
theorem priority_length_eq (stage : LocalizedCumulativeRule45Stage)
    (label : Option LocalizedAuxiliaryLabel) :
    (localizedCumulativeRule45Priority stage label).length =
      (localizedCumulativeRule45Priority stage none).length := by
  cases stage <;> rfl

/-! ## The projected comparison -/

/-- A lexicographic comparison of `Nat` vectors whose prefix agrees up to `index` is decided by the
component at `index`. -/
theorem compareNat_compareLex_eq_getD_of_firstDifference {left right : List Nat} {index : Nat}
    (leftBound : index < left.length) (rightBound : index < right.length)
    (agree : ∀ j, j < index → left.getD j 0 = right.getD j 0)
    (different : left.getD index 0 ≠ right.getD index 0) :
    List.compareLex OfficialRuleMajorKey.compareNat left right =
      OfficialRuleMajorKey.compareNat (left.getD index 0) (right.getD index 0) := by
  induction index generalizing left right with
  | zero =>
      cases left with
      | nil => simp at leftBound
      | cons headLeft tailLeft =>
          cases right with
          | nil => simp at rightBound
          | cons headRight tailRight =>
              rw [List.getD_cons_zero, List.getD_cons_zero] at different
              rw [List.compareLex_cons_cons, List.getD_cons_zero, List.getD_cons_zero]
              have notEq : OfficialRuleMajorKey.compareNat headLeft headRight ≠ Ordering.eq :=
                fun tied => different ((compareNat_eq_iff headLeft headRight).mp tied)
              cases compared : OfficialRuleMajorKey.compareNat headLeft headRight with
              | lt => rfl
              | eq => exact absurd compared notEq
              | gt => rfl
  | succ index inductionHypothesis =>
      cases left with
      | nil => simp at leftBound
      | cons headLeft tailLeft =>
          cases right with
          | nil => simp at rightBound
          | cons headRight tailRight =>
              have headEq : headLeft = headRight := by
                have combined := agree 0 (by omega)
                rwa [List.getD_cons_zero, List.getD_cons_zero] at combined
              rw [List.compareLex_cons_cons, ← headEq]
              rw [compareNat_self, Ordering.eq_then]
              rw [List.getD_cons_succ, List.getD_cons_succ]
              exact inductionHypothesis (by simpa using leftBound) (by simpa using rightBound)
                (fun j hj => by simpa using agree (j + 1) (by omega))
                (by simpa using different)

/-- A lexicographic comparison of `Nat` vectors whose components before `focus` agree is decided by
the `focus` component.  Components after `focus` are irrelevant. -/
theorem compareNat_compareLex_eq_getD_of_before {left right : List Nat} {focus : Nat}
    (lengthEq : left.length = right.length) (bound : focus < left.length)
    (before : ∀ j, j < focus → left.getD j 0 = right.getD j 0)
    (different : left.getD focus 0 ≠ right.getD focus 0) :
    List.compareLex OfficialRuleMajorKey.compareNat left right =
      OfficialRuleMajorKey.compareNat (left.getD focus 0) (right.getD focus 0) := by
  induction focus generalizing left right with
  | zero =>
      exact compareNat_compareLex_eq_getD_of_firstDifference bound (by omega)
        (fun j hj => by omega) different
  | succ focus inductionHypothesis =>
      cases left with
      | nil => simp at bound
      | cons headLeft tailLeft =>
          cases right with
          | nil => simp at lengthEq
          | cons headRight tailRight =>
              have headEq : headLeft = headRight := by
                have combined := before 0 (by omega)
                rwa [List.getD_cons_zero, List.getD_cons_zero] at combined
              rw [List.compareLex_cons_cons, ← headEq, compareNat_self, Ordering.eq_then,
                List.getD_cons_succ, List.getD_cons_succ]
              exact inductionHypothesis (by simpa using lengthEq) (by simpa using bound)
                (fun j hj => by simpa using before (j + 1) (by omega))
                (by simpa using different)

/-- Two addressed cumulative entries are aligned at one stage: they have the same address and the
same vector length, and the stage's controlling component is the only component that can decide a
difference. -/
structure FocusAligned (stage : LocalizedCumulativeRule45Stage)
    (left right : OfficialSparseEntry (List Nat)) : Prop where
  /-- The two entries sit at the same address. -/
  addressEq : left.1 = right.1
  /-- The two cumulative vectors have the same width. -/
  lengthEq : left.2.length = right.2.length
  /-- The controlling component is in range. -/
  bound : controllingComponent stage < left.2.length
  /-- Every component before the controlling component ties. -/
  before : ∀ j, j < controllingComponent stage → left.2.getD j 0 = right.2.getD j 0
  /-- Every vector difference is a difference of the controlling component. -/
  controlled : left.2 ≠ right.2 →
    left.2.getD (controllingComponent stage) 0 ≠ right.2.getD (controllingComponent stage) 0

/-- Two aligned entries are equal as soon as their controlling components agree. -/
theorem eq_of_focus_eq {stage : LocalizedCumulativeRule45Stage}
    {left right : OfficialSparseEntry (List Nat)} (aligned : FocusAligned stage left right)
    (focusEq : left.2.getD (controllingComponent stage) 0 =
      right.2.getD (controllingComponent stage) 0) : left = right := by
  rcases left with ⟨leftAddress, leftValue⟩
  rcases right with ⟨rightAddress, rightValue⟩
  have addressEq : leftAddress = rightAddress := aligned.addressEq
  have valuesEq : leftValue = rightValue := by
    by_contra different
    exact aligned.controlled different focusEq
  rw [addressEq, valuesEq]

/-- **Entry-level projection identity.**  Aligned entries at one shared stage compare exactly as
their controlling components. -/
theorem compareSparseEntry_priority_eq_projection {stage : LocalizedCumulativeRule45Stage}
    {left right : OfficialSparseEntry (List Nat)} (aligned : FocusAligned stage left right) :
    OfficialRuleMajorKey.compareSparseEntry compareLocalizedCumulativeRule45Priority left right =
      OfficialRuleMajorKey.compareSparseEntry OfficialRuleMajorKey.compareNat
        (left.1, left.2.getD (controllingComponent stage) 0)
        (right.1, right.2.getD (controllingComponent stage) 0) := by
  have vectorEq : compareLocalizedCumulativeRule45Priority left.2 right.2 =
      OfficialRuleMajorKey.compareNat (left.2.getD (controllingComponent stage) 0)
        (right.2.getD (controllingComponent stage) 0) := by
    rw [compareLocalizedCumulativeRule45Priority_unfold]
    by_cases tied : left.2.getD (controllingComponent stage) 0 =
        right.2.getD (controllingComponent stage) 0
    · have same : left.2 = right.2 := by
        by_contra different
        exact aligned.controlled different tied
      rw [same, listCompareLex_self _ compareNat_self, compareNat_self]
    · exact compareNat_compareLex_eq_getD_of_before aligned.lengthEq aligned.bound aligned.before
        tied
  rw [compareSparseEntry_unfold, compareSparseEntry_unfold, vectorEq, aligned.addressEq]

/-- **Layer-level projection identity.** -/
theorem compareSparseLayer_priority_eq_projection {stage : LocalizedCumulativeRule45Stage}
    {left right : List (OfficialSparseEntry (List Nat))}
    (aligned : List.Forall₂ (FocusAligned stage) left right) :
    OfficialRuleMajorKey.compareSparseLayer compareLocalizedCumulativeRule45Priority left right =
      OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareNat
        (left.map fun entry => (entry.1, entry.2.getD (controllingComponent stage) 0))
        (right.map fun entry => (entry.1, entry.2.getD (controllingComponent stage) 0)) := by
  rw [compareSparseLayer_unfold, compareSparseLayer_unfold]
  induction aligned with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.map_cons, List.map_cons, List.compareLex_cons_cons, List.compareLex_cons_cons,
        compareSparseEntry_priority_eq_projection head, inductionHypothesis]

/-- **Table-level projection identity.**  The node-major sparse-table comparison at one shared
stage is the sparse-table comparison of the projected controlling components. -/
theorem compareSparseLayers_priority_eq_projection {stage : LocalizedCumulativeRule45Stage}
    {left right : List (List (OfficialSparseEntry (List Nat)))}
    (aligned : List.Forall₂ (List.Forall₂ (FocusAligned stage)) left right) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority left right =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (projectCumulative (controllingComponent stage) left)
        (projectCumulative (controllingComponent stage) right) := by
  rw [compareSparseLayers_unfold, compareSparseLayers_unfold]
  unfold projectCumulative
  induction aligned with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.map_cons, List.map_cons, List.compareLex_cons_cons, List.compareLex_cons_cons,
        compareSparseLayer_priority_eq_projection head, inductionHypothesis]

/-- Projecting one component commutes with mapping a layer: aligned layers have equal projections
as soon as the projected component is before the controlling component. -/
theorem map_projection_eq_of_forall₂ {stage : LocalizedCumulativeRule45Stage} {index : Nat}
    (indexBound : index < controllingComponent stage)
    {left right : List (OfficialSparseEntry (List Nat))}
    (aligned : List.Forall₂ (FocusAligned stage) left right) :
    left.map (fun entry => (entry.1, entry.2.getD index 0)) =
      right.map (fun entry => (entry.1, entry.2.getD index 0)) := by
  induction aligned with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.map_cons, List.map_cons, head.addressEq, head.before index indexBound,
        inductionHypothesis]

/-- Projecting one component commutes with an aligned table as soon as the component is before the
controlling component. -/
theorem projectCumulative_eq_of_forall₂ {stage : LocalizedCumulativeRule45Stage}
    {left right : List (List (OfficialSparseEntry (List Nat)))}
    (aligned : List.Forall₂ (List.Forall₂ (FocusAligned stage)) left right)
    {index : Nat} (indexBound : index < controllingComponent stage) :
    projectCumulative index left = projectCumulative index right := by
  unfold projectCumulative
  induction aligned with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.map_cons, List.map_cons,
        map_projection_eq_of_forall₂ indexBound head, inductionHypothesis]

/-- Aligned rows with equal controlling projections are equal. -/
theorem row_eq_of_map_projection_eq {stage : LocalizedCumulativeRule45Stage} :
    ∀ {left right : List (OfficialSparseEntry (List Nat))},
      List.Forall₂ (FocusAligned stage) left right →
      left.map (fun entry => (entry.1, entry.2.getD (controllingComponent stage) 0)) =
        right.map (fun entry => (entry.1, entry.2.getD (controllingComponent stage) 0)) →
      left = right
  | [], [], _, _ => rfl
  | [], _ :: _, aligned, _ => by cases aligned
  | _ :: _, [], aligned, _ => by cases aligned
  | left :: lefts, right :: rights, aligned, equal => by
      cases aligned with
      | cons head tail =>
          rw [List.map_cons, List.map_cons] at equal
          injection equal with headEq tailEq
          injection headEq with addressEq focusEq
          have valuesEq : left.2 = right.2 := by
            by_contra different
            exact head.controlled different focusEq
          have entriesEq : left = right := by
            rw [← Prod.mk.eta (p := left), ← Prod.mk.eta (p := right), addressEq, valuesEq]
          rw [entriesEq, row_eq_of_map_projection_eq tail tailEq]

/-- Aligned tables with equal controlling projections are equal. -/
theorem eq_of_projectCumulative_eq {stage : LocalizedCumulativeRule45Stage} :
    ∀ {left right : List (List (OfficialSparseEntry (List Nat)))},
      List.Forall₂ (List.Forall₂ (FocusAligned stage)) left right →
      projectCumulative (controllingComponent stage) left =
        projectCumulative (controllingComponent stage) right →
      left = right
  | [], [], _, _ => rfl
  | [], _ :: _, aligned, _ => by cases aligned
  | _ :: _, [], aligned, _ => by cases aligned
  | left :: lefts, right :: rights, aligned, equal => by
      cases aligned with
      | cons head tail =>
          unfold projectCumulative at equal
          rw [List.map_cons, List.map_cons] at equal
          injection equal with headEq tailEq
          have rowEq : left = right := row_eq_of_map_projection_eq head headEq
          rw [rowEq, eq_of_projectCumulative_eq tail tailEq]

/-! ## The descriptor schedule is decided by the controlling component -/

/-- **Main descriptor theorem.**  On an aligned sparse table at one shared stage, the production
node-major cumulative comparison is the first non-tie of the rule-major schedule of projected
components.  All components before the controlling component tie everywhere, so the first rule-major
difference is the controlling column, which is exactly the first node-major difference. -/
theorem compareSparseLayers_priority_eq_firstNonEq {stage : LocalizedCumulativeRule45Stage}
    {tableLeft tableRight : List (List (OfficialSparseEntry (List Nat)))}
    (aligned : List.Forall₂ (List.Forall₂ (FocusAligned stage)) tableLeft tableRight) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        tableLeft tableRight =
      firstNonEq ((List.range (localizedCumulativeRule45Priority stage none).length).map
        (fun index => OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          (projectCumulative index tableLeft) (projectCumulative index tableRight))) := by
  let focus := controllingComponent stage
  let width := (localizedCumulativeRule45Priority stage none).length
  let outcome : Nat → Ordering := fun index =>
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (projectCumulative index tableLeft) (projectCumulative index tableRight)
  have projectionIdentity : OfficialRuleMajorKey.compareSparseLayers
      compareLocalizedCumulativeRule45Priority tableLeft tableRight = outcome focus :=
    compareSparseLayers_priority_eq_projection aligned
  have focusBound : focus < width := controllingComponent_lt_width stage
  have beforeOutcome : ∀ index, index < focus → outcome index = Ordering.eq := by
    intro index indexBound
    have tablesEq : projectCumulative index tableLeft = projectCumulative index tableRight :=
      projectCumulative_eq_of_forall₂ aligned indexBound
    show OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (projectCumulative index tableLeft) (projectCumulative index tableRight) = Ordering.eq
    rw [tablesEq]
    exact compareSparseLayers_self _
  have spread : outcome focus = Ordering.eq → ∀ index, index < width →
      outcome index = Ordering.eq := by
    intro tied index _
    have tablesEq : projectCumulative focus tableLeft = projectCumulative focus tableRight :=
      (compareSparseLayers_eq_iff OfficialRuleMajorKey.compareNat compareNat_eq_iff
        (projectCumulative focus tableLeft) (projectCumulative focus tableRight)).mp tied
    have tablesEqual : tableLeft = tableRight := eq_of_projectCumulative_eq aligned tablesEq
    show OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (projectCumulative index tableLeft) (projectCumulative index tableRight) = Ordering.eq
    rw [tablesEqual]
    exact compareSparseLayers_self _
  rw [projectionIdentity]
  exact (firstNonEq_range_map_eq_focus focusBound beforeOutcome spread).symm

/-- **Descriptor schedule form.**  The node-major comparison is exactly the rule-major lexicographic
comparison of the projected component outcomes against the all-tie schedule, which is the descriptor
component of `compareRuleMajorCumulativeDescriptor`. -/
theorem compareSparseLayers_eq_ruleMajorSchedule {stage : LocalizedCumulativeRule45Stage}
    {tableLeft tableRight : List (List (OfficialSparseEntry (List Nat)))}
    (aligned : List.Forall₂ (List.Forall₂ (FocusAligned stage)) tableLeft tableRight) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        tableLeft tableRight =
      List.compareLex compare
        ((List.range (localizedCumulativeRule45Priority stage none).length).map
          (fun index => OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
            (projectCumulative index tableLeft) (projectCumulative index tableRight)))
        ((List.range (localizedCumulativeRule45Priority stage none).length).map
          fun _ => Ordering.eq) := by
  rw [compareSparseLayers_priority_eq_firstNonEq aligned, ← compareLex_orderings_map_eq]

/-! ## Consumer bridges: from kind data to the production comparators -/

/-- Two same-address cumulative entries whose reader labels meet the none-or-chiral kind
hypotheses are focus-aligned at their shared stage.  This is the constructor a physical owner uses
to feed compiled descriptor tables into the algebra above. -/
theorem focusAligned_of_priority {stage : LocalizedCumulativeRule45Stage}
    (address : List Nat) {leftLabel rightLabel : Option LocalizedAuxiliaryLabel}
    (leftKind : NoneOrChiral leftLabel) (rightKind : NoneOrChiral rightLabel)
    (same : SameKind leftLabel rightLabel) :
    FocusAligned stage
      (address, localizedCumulativeRule45Priority stage leftLabel)
      (address, localizedCumulativeRule45Priority stage rightLabel) where
  addressEq := rfl
  lengthEq := by
    show (localizedCumulativeRule45Priority stage leftLabel).length =
      (localizedCumulativeRule45Priority stage rightLabel).length
    rw [priority_length_eq stage leftLabel, priority_length_eq stage rightLabel]
  bound := by
    show controllingComponent stage < (localizedCumulativeRule45Priority stage leftLabel).length
    rw [priority_length_eq stage leftLabel]
    exact controllingComponent_lt_width stage
  before := by
    intro j bound
    exact (controllingComponent_spec stage leftLabel rightLabel leftKind rightKind same).1 j bound
  controlled := by
    intro different sameFocus
    exact (controllingComponent_spec stage leftLabel rightLabel leftKind rightKind same).2
      (fun sameVector => different (by rw [sameVector])) sameFocus

/-- **Full comparator endpoint under an aligned descriptor table.**  If the two production keys have
focus-aligned descriptor tables at one shared stage, then the production *full* comparator
`compareLocalizedRerootCumulativeRule45Keys` (constitutional part included) agrees with
`compareRuleMajorCumulativeDescriptor` at the matching cumulative width.  Both comparators apply
the *same* constitutional comparison first, so the constitutional outcome is shared on both sides
whatever it is; the only remaining content is the pointwise equality of the descriptor components,
which is `compareSparseLayers_eq_ruleMajorSchedule` above.  Hence this is not a descriptor-only
left-hand side being compared against a constitution-first right-hand side. -/
theorem compareLocalizedRerootCumulativeRule45Keys_eq_ruleMajorDescriptor
    (input : CertifiedLocalizedCIPInput) (stage : LocalizedCumulativeRule45Stage)
    {left right : input.LocalizedRerootCumulativeRule45Key}
    (aligned : List.Forall₂ (List.Forall₂ (FocusAligned stage))
      left.descriptor right.descriptor) :
    input.compareLocalizedRerootCumulativeRule45Keys left right =
      compareRuleMajorCumulativeDescriptor
        input (localizedCumulativeRule45Priority stage none).length left right := by
  have schedule := compareSparseLayers_eq_ruleMajorSchedule aligned
  show (Ordering.byKey (fun key => key.constitutional) OfficialRuleMajorKey.compare
        left right).then
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        left.descriptor right.descriptor) =
    (Ordering.byKey (fun key => key.constitutional) OfficialRuleMajorKey.compare
        left right).then
      (List.compareLex compare
        ((List.range (localizedCumulativeRule45Priority stage none).length).map fun index =>
          OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
            (projectCumulative index left.descriptor)
            (projectCumulative index right.descriptor))
        ((List.range (localizedCumulativeRule45Priority stage none).length).map
          fun _ => Ordering.eq))
  rw [schedule]

end SameStageKindComparison

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.ordering_compare_eq_self
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.compareNat_eq_iff
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.compareNat_self
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.listCompareLex_self
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.listCompareLex_append
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.firstNonEq_cons
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.firstNonEq_singleton
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.ordering_then_self_of_ne_eq
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.firstNonEq_append
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.compareLex_orderings_map_eq
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.ordering_then_eq_eq
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.listCompareLex_eq_iff
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.compareSparseEntry_unfold
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.compareSparseLayer_unfold
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.compareSparseLayers_unfold
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.compareLocalizedCumulativeRule45Priority_unfold
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.compareSparseEntry_eq_iff
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.compareSparseLayer_eq_iff
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.compareSparseLayers_eq_iff
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.compareSparseLayers_self
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.firstNonEqRange
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.firstNonEq_range'_map
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.firstNonEqRange_eq_of_ne
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.firstNonEqRange_eq_of_all_eq
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.firstNonEq_range_map_of_eq_of_ne
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.firstNonEq_range_map_of_all_eq
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.firstNonEqRange_eq_of_before_eq_of_ne
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.firstNonEq_range_map_eq_focus
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.NoneOrChiral
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.SameKind
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.rule4aPriority_eq_of_kind
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.rule4cPriority_eq_zero_of_kind
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.rule4bPriority_eq_of_eq
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.eq_of_rule4bPriority_eq
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.rule5Priority_eq_of_eq
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.eq_of_rule5Priority_eq
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.controllingComponent
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.controllingComponent_spec
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.controllingComponent_lt_width
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.priority_length_eq
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.compareNat_compareLex_eq_getD_of_firstDifference
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.compareNat_compareLex_eq_getD_of_before
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.FocusAligned
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.eq_of_focus_eq
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.compareSparseEntry_priority_eq_projection
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.compareSparseLayer_priority_eq_projection
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.compareSparseLayers_priority_eq_projection
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.map_projection_eq_of_forall₂
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.projectCumulative_eq_of_forall₂
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.row_eq_of_map_projection_eq
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.eq_of_projectCumulative_eq
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.compareSparseLayers_priority_eq_firstNonEq
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.compareSparseLayers_eq_ruleMajorSchedule
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.focusAligned_of_priority
assert_kernel_only TetraStereo.OneCenter.SameStageKindComparison.compareLocalizedRerootCumulativeRule45Keys_eq_ruleMajorDescriptor
