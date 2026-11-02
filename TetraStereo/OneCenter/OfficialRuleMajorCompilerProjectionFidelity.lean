import TetraStereo.OneCenter.OfficialRuleMajorKey
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Compiler projection fidelity under child-enumeration permutation

`OfficialRuleMajorKey` compiles each branch into three rule-major projections (`rule1a`,
`rule1b`, `rule2`), a provenance tree (`sourceNodes`) and a completeness flag.  The compiler
`MoleculeGraph.buildOfficialRuleMajorKey` is parameterized by a child enumerator.  Two child
enumerators may enumerate the same children in different orders; the derived provenance trees
then legitimately differ in `sourceNodes` order, and the raw keys are therefore *not* equal.

This module proves the projection-level contract needed by the executable engine:
for arbitrary fuel and root, if two enumerators are pointwise `List.Perm` related at every
node, then every generated pair of keys satisfies:

* equal Rule-1a projection,
* equal Rule-1b projection,
* equal Rule-2 projection,
* equal completeness flag.

Consequently the safe comparator `compare?` and the rule-tagged `compareTrace` agree for every
pair of physical roots across the two enumerators.  `sourceNodes` is never compared and no full
key equality is assumed.

Failures are handled by an `Option` relation: a build failure on either side makes no claim.
The proofs are independent of the engine's own correctness proof and use only the kernel.
-/

namespace TetraStereo.OneCenter
namespace CompilerProjectionFidelity

open OfficialRuleMajorKey

/-- The full sorting-visible constitution of a rule-major key.  Provenance (`sourceNodes`) is
deliberately excluded: sibling ties may reorder provenance while leaving the constitutional
projections and completeness untouched. -/
def SameConstitution {V : Type*} (left right : OfficialRuleMajorKey V) : Prop :=
  left.rule1a = right.rule1a ∧ left.rule1b = right.rule1b ∧
    left.rule2 = right.rule2 ∧ left.complete = right.complete

/-- Option relation used for build failures.  Two successful builds are related exactly when
their constitutions agree; any failure on either side is related vacuously. -/
def OptionSameConstitution {V : Type*} :
    Option (OfficialRuleMajorKey V) → Option (OfficialRuleMajorKey V) → Prop
  | some left, some right => SameConstitution left right
  | _, _ => True

theorem optionSameConstitution_none_left {V : Type*}
    (right : Option (OfficialRuleMajorKey V)) :
    OptionSameConstitution none right := by
  cases right <;> trivial

theorem optionSameConstitution_none_right {V : Type*}
    (left : Option (OfficialRuleMajorKey V)) :
    OptionSameConstitution left none := by
  cases left <;> trivial

/-! ## Basic comparison identities -/

theorem compareNat_self (value : ℕ) :
    OfficialRuleMajorKey.compareNat value value = Ordering.eq := by
  unfold OfficialRuleMajorKey.compareNat
  exact Std.ReflOrd.compare_self

theorem compareRule1b_self (value : ℕ) :
    OfficialRuleMajorKey.compareRule1b value value = Ordering.eq := by
  unfold OfficialRuleMajorKey.compareRule1b
  exact compareNat_self value

theorem compareNat_eq_eq_iff (left right : ℕ) :
    OfficialRuleMajorKey.compareNat left right = Ordering.eq ↔ left = right := by
  unfold OfficialRuleMajorKey.compareNat
  exact Std.LawfulEqOrd.compare_eq_iff_eq

theorem compareRule1b_eq_eq_iff (left right : ℕ) :
    OfficialRuleMajorKey.compareRule1b left right = Ordering.eq ↔ left = right := by
  unfold OfficialRuleMajorKey.compareRule1b
  change OfficialRuleMajorKey.compareNat right left = Ordering.eq ↔ left = right
  rw [compareNat_eq_eq_iff]
  exact eq_comm

theorem list_compareLex_self {α : Type*} (cmp : α → α → Ordering)
    (refl : ∀ value, cmp value value = Ordering.eq) :
    ∀ values : List α, List.compareLex cmp values values = Ordering.eq
  | [] => rfl
  | value :: values => by
      rw [List.compareLex_cons_cons, refl value]
      exact list_compareLex_self cmp refl values

theorem list_compareLex_eq_eq_iff {α : Type*} (cmp : α → α → Ordering)
    (refl : ∀ value, cmp value value = Ordering.eq)
    (sound : ∀ left right, cmp left right = Ordering.eq → left = right) :
    ∀ left right : List α, List.compareLex cmp left right = Ordering.eq ↔ left = right
  | [], [] => by simp [List.compareLex]
  | [], _ :: _ => by simp [List.compareLex]
  | _ :: _, [] => by simp [List.compareLex]
  | leftHead :: leftTail, rightHead :: rightTail => by
      rw [List.compareLex_cons_cons, Ordering.then_eq_eq]
      constructor
      · rintro ⟨headEqual, tailEqual⟩
        rw [sound leftHead rightHead headEqual,
          (list_compareLex_eq_eq_iff cmp refl sound leftTail rightTail).mp tailEqual]
      · intro equal
        rw [List.cons.injEq] at equal
        rcases equal with ⟨headEqual, tailEqual⟩
        subst headEqual
        subst tailEqual
        exact ⟨refl leftHead,
          (list_compareLex_eq_eq_iff cmp refl sound leftTail leftTail).mpr rfl⟩

theorem compareSparseEntry_self {α : Type*} (cmp : α → α → Ordering)
    (refl : ∀ value, cmp value value = Ordering.eq)
    (entry : OfficialSparseEntry α) :
    OfficialRuleMajorKey.compareSparseEntry cmp entry entry = Ordering.eq := by
  rcases entry with ⟨path, observation⟩
  have pathEqual :
      Ordering.byKey Prod.fst (flip (List.compareLex OfficialRuleMajorKey.compareNat))
          (path, observation) (path, observation) = Ordering.eq := by
    show List.compareLex OfficialRuleMajorKey.compareNat path path = Ordering.eq
    exact list_compareLex_self OfficialRuleMajorKey.compareNat compareNat_self path
  have observationEqual :
      Ordering.byKey Prod.snd cmp (path, observation) (path, observation) = Ordering.eq := by
    show cmp observation observation = Ordering.eq
    exact refl observation
  unfold OfficialRuleMajorKey.compareSparseEntry
  simp only [compareLex]
  rw [pathEqual, observationEqual]
  rfl

theorem compareSparseLayer_self {α : Type*} (cmp : α → α → Ordering)
    (refl : ∀ value, cmp value value = Ordering.eq)
    (layer : List (OfficialSparseEntry α)) :
    OfficialRuleMajorKey.compareSparseLayer cmp layer layer = Ordering.eq :=
  list_compareLex_self (OfficialRuleMajorKey.compareSparseEntry cmp)
    (fun entry => compareSparseEntry_self cmp refl entry) layer

theorem compareSparseLayers_self {α : Type*} (cmp : α → α → Ordering)
    (refl : ∀ value, cmp value value = Ordering.eq)
    (layers : List (List (OfficialSparseEntry α))) :
    OfficialRuleMajorKey.compareSparseLayers cmp layers layers = Ordering.eq :=
  list_compareLex_self (OfficialRuleMajorKey.compareSparseLayer cmp)
    (fun layer => compareSparseLayer_self cmp refl layer) layers

theorem compareSparseEntry_eq_eq_iff {α : Type*} (cmp : α → α → Ordering)
    (refl : ∀ value, cmp value value = Ordering.eq)
    (sound : ∀ left right, cmp left right = Ordering.eq → left = right)
    (left right : OfficialSparseEntry α) :
    OfficialRuleMajorKey.compareSparseEntry cmp left right = Ordering.eq ↔
      left = right := by
  rcases left with ⟨leftPath, leftObservation⟩
  rcases right with ⟨rightPath, rightObservation⟩
  unfold OfficialRuleMajorKey.compareSparseEntry
  rw [compareLex_eq_eq]
  constructor
  · rintro ⟨pathEqual, observationEqual⟩
    have pathEqual' : leftPath = rightPath := by
      have reversed : List.compareLex OfficialRuleMajorKey.compareNat rightPath leftPath =
          Ordering.eq := pathEqual
      exact ((list_compareLex_eq_eq_iff OfficialRuleMajorKey.compareNat compareNat_self
        (fun first second => (compareNat_eq_eq_iff first second).mp)
        rightPath leftPath).mp reversed).symm
    have observationEqual' : leftObservation = rightObservation :=
      sound leftObservation rightObservation observationEqual
    rw [pathEqual', observationEqual']
  · intro equal
    rw [Prod.mk.injEq] at equal
    rcases equal with ⟨pathEqual, observationEqual⟩
    subst pathEqual
    subst observationEqual
    refine ⟨?_, ?_⟩
    · show List.compareLex OfficialRuleMajorKey.compareNat leftPath leftPath = Ordering.eq
      exact list_compareLex_self OfficialRuleMajorKey.compareNat compareNat_self leftPath
    · show cmp leftObservation leftObservation = Ordering.eq
      exact refl leftObservation

theorem compareSparseLayer_eq_eq_iff {α : Type*} (cmp : α → α → Ordering)
    (refl : ∀ value, cmp value value = Ordering.eq)
    (sound : ∀ left right, cmp left right = Ordering.eq → left = right)
    (left right : List (OfficialSparseEntry α)) :
    OfficialRuleMajorKey.compareSparseLayer cmp left right = Ordering.eq ↔
      left = right :=
  list_compareLex_eq_eq_iff (OfficialRuleMajorKey.compareSparseEntry cmp)
    (fun entry => compareSparseEntry_self cmp refl entry)
    (fun first second => (compareSparseEntry_eq_eq_iff cmp refl sound first second).mp)
    left right

theorem compareSparseLayers_eq_eq_iff {α : Type*} (cmp : α → α → Ordering)
    (refl : ∀ value, cmp value value = Ordering.eq)
    (sound : ∀ left right, cmp left right = Ordering.eq → left = right)
    (left right : List (List (OfficialSparseEntry α))) :
    OfficialRuleMajorKey.compareSparseLayers cmp left right = Ordering.eq ↔
      left = right :=
  list_compareLex_eq_eq_iff (OfficialRuleMajorKey.compareSparseLayer cmp)
    (fun layer => compareSparseLayer_self cmp refl layer)
    (fun first second => (compareSparseLayer_eq_eq_iff cmp refl sound first second).mp)
    left right

/-! ## The sorting-visible projection triple -/

/-- The three constitutional projections that the rule-major comparator inspects. -/
structure RuleTriple where
  rule1a : List (List (OfficialSparseEntry ℕ))
  rule1b : List (List (OfficialSparseEntry ℕ))
  rule2 : List (List (OfficialSparseEntry ℕ))

/-- Forget provenance while retaining every field the comparator can observe. -/
def tripleOf {V : Type*} (key : OfficialRuleMajorKey V) : RuleTriple where
  rule1a := key.rule1a
  rule1b := key.rule1b
  rule2 := key.rule2

/-- The comparator on the sorting-visible triple, mirroring `OfficialRuleMajorKey.compare`. -/
def compareTriple (left right : RuleTriple) : Ordering :=
  compareLex
    (Ordering.byKey RuleTriple.rule1a
      (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat))
    (compareLex
      (Ordering.byKey RuleTriple.rule1b
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b))
      (Ordering.byKey RuleTriple.rule2
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat)))
    left right

theorem compare_eq_compareTriple {V : Type*} (left right : OfficialRuleMajorKey V) :
    OfficialRuleMajorKey.compare left right =
      compareTriple (tripleOf left) (tripleOf right) := rfl

theorem compareTriple_self (value : RuleTriple) :
    compareTriple value value = Ordering.eq := by
  unfold compareTriple
  rw [compareLex_eq_eq, compareLex_eq_eq]
  refine ⟨?_, ?_, ?_⟩
  · show OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      value.rule1a value.rule1a = Ordering.eq
    exact compareSparseLayers_self OfficialRuleMajorKey.compareNat compareNat_self value.rule1a
  · show OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
      value.rule1b value.rule1b = Ordering.eq
    exact compareSparseLayers_self OfficialRuleMajorKey.compareRule1b
      compareRule1b_self value.rule1b
  · show OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      value.rule2 value.rule2 = Ordering.eq
    exact compareSparseLayers_self OfficialRuleMajorKey.compareNat compareNat_self value.rule2

theorem compareTriple_eq_eq_iff (left right : RuleTriple) :
    compareTriple left right = Ordering.eq ↔ left = right := by
  rcases left with ⟨left1a, left1b, left2⟩
  rcases right with ⟨right1a, right1b, right2⟩
  constructor
  · intro computed
    unfold compareTriple at computed
    rw [compareLex_eq_eq] at computed
    rcases computed with ⟨firstEqual, secondAndThird⟩
    rw [compareLex_eq_eq] at secondAndThird
    rcases secondAndThird with ⟨secondEqual, thirdEqual⟩
    change OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left1a right1a = Ordering.eq at firstEqual
    change OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
      left1b right1b = Ordering.eq at secondEqual
    change OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left2 right2 = Ordering.eq at thirdEqual
    rw [(compareSparseLayers_eq_eq_iff OfficialRuleMajorKey.compareNat compareNat_self
          (fun first second => (compareNat_eq_eq_iff first second).mp)
          left1a right1a).mp firstEqual,
      (compareSparseLayers_eq_eq_iff OfficialRuleMajorKey.compareRule1b
          compareRule1b_self
          (fun first second => (compareRule1b_eq_eq_iff first second).mp)
          left1b right1b).mp secondEqual,
      (compareSparseLayers_eq_eq_iff OfficialRuleMajorKey.compareNat compareNat_self
          (fun first second => (compareNat_eq_eq_iff first second).mp)
          left2 right2).mp thirdEqual]
  · intro equal
    rw [equal]
    exact compareTriple_self _

theorem compareTriple_eq_of_not_lt_not_lt (left right : RuleTriple)
    (leftNotLt : compareTriple left right ≠ Ordering.lt)
    (rightNotLt : compareTriple right left ≠ Ordering.lt) :
    left = right := by
  haveI oriented : Std.OrientedCmp compareTriple := by
    letI natOriented : Std.OrientedCmp OfficialRuleMajorKey.compareNat := by
      unfold OfficialRuleMajorKey.compareNat
      infer_instance
    letI rule1bOriented : Std.OrientedCmp OfficialRuleMajorKey.compareRule1b := by
      unfold OfficialRuleMajorKey.compareRule1b
      infer_instance
    unfold compareTriple OfficialRuleMajorKey.compareSparseLayers
      OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareSparseEntry
    infer_instance
  cases compared : compareTriple left right with
  | lt => exact absurd compared leftNotLt
  | eq => exact (compareTriple_eq_eq_iff left right).mp compared
  | gt =>
      exact absurd (Std.OrientedCmp.lt_of_gt (cmp := compareTriple) compared) rightNotLt

theorem sameConstitution_triple {V : Type*} {left right : OfficialRuleMajorKey V}
    (aligned : SameConstitution left right) : tripleOf left = tripleOf right := by
  unfold tripleOf
  rw [aligned.1, aligned.2.1, aligned.2.2.1]

/-! ## Comparison agreement from constitution equality -/

theorem compare_eq_eq_of_sameConstitution {V : Type*}
    {left right : OfficialRuleMajorKey V} (aligned : SameConstitution left right) :
    OfficialRuleMajorKey.compare left right = Ordering.eq := by
  rcases aligned with ⟨rule1aEqual, rule1bEqual, rule2Equal, _⟩
  unfold OfficialRuleMajorKey.compare
  simp only [compareLex, Ordering.byKey]
  rw [rule1aEqual, rule1bEqual, rule2Equal]
  rw [compareSparseLayers_self OfficialRuleMajorKey.compareNat compareNat_self,
    compareSparseLayers_self OfficialRuleMajorKey.compareRule1b compareRule1b_self,
    compareSparseLayers_self OfficialRuleMajorKey.compareNat compareNat_self]
  rfl

theorem compare?_eq_of_sameConstitution {V : Type*}
    {left right : OfficialRuleMajorKey V} (aligned : SameConstitution left right) :
    OfficialRuleMajorKey.compare? left right =
      (if left.complete && right.complete then some Ordering.eq else none) := by
  unfold OfficialRuleMajorKey.compare?
  rw [aligned.1]
  rw [compareSparseLayers_self OfficialRuleMajorKey.compareNat compareNat_self]
  by_cases leftComplete : left.complete = true <;>
    by_cases rightComplete : right.complete = true <;>
      simp [leftComplete, rightComplete, compare_eq_eq_of_sameConstitution aligned]

theorem compareTrace_eq_of_sameConstitution {V : Type*}
    {left₁ left₂ right₁ right₂ : OfficialRuleMajorKey V}
    (leftAligned : SameConstitution left₁ left₂)
    (rightAligned : SameConstitution right₁ right₂) :
    OfficialRuleMajorKey.compareTrace left₁ right₁ =
      OfficialRuleMajorKey.compareTrace left₂ right₂ := by
  unfold OfficialRuleMajorKey.compareTrace
  rw [leftAligned.1, rightAligned.1, leftAligned.2.1, rightAligned.2.1,
    leftAligned.2.2.1, rightAligned.2.2.1]

theorem compare_eq_of_sameConstitution {V : Type*}
    {left₁ left₂ right₁ right₂ : OfficialRuleMajorKey V}
    (leftAligned : SameConstitution left₁ left₂)
    (rightAligned : SameConstitution right₁ right₂) :
    OfficialRuleMajorKey.compare left₁ right₁ =
      OfficialRuleMajorKey.compare left₂ right₂ := by
  unfold OfficialRuleMajorKey.compare
  simp only [compareLex, Ordering.byKey]
  rw [leftAligned.1, rightAligned.1, leftAligned.2.1, rightAligned.2.1,
    leftAligned.2.2.1, rightAligned.2.2.1]

theorem compare?_congr_of_sameConstitution {V : Type*}
    {left₁ left₂ right₁ right₂ : OfficialRuleMajorKey V}
    (leftAligned : SameConstitution left₁ left₂)
    (rightAligned : SameConstitution right₁ right₂) :
    OfficialRuleMajorKey.compare? left₁ right₁ =
      OfficialRuleMajorKey.compare? left₂ right₂ := by
  unfold OfficialRuleMajorKey.compare?
  rw [leftAligned.1, rightAligned.1]
  cases compared :
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        left₂.rule1a right₂.rule1a with
  | lt => rfl
  | gt => rfl
  | eq =>
      simp [leftAligned.2.2.2, rightAligned.2.2.2,
        compare_eq_of_sameConstitution leftAligned rightAligned]

/-! ## Permutation-preserving list and option lemmas -/

theorem perm_isEmpty_eq {α : Type*} {left right : List α}
    (perm : left.Perm right) : left.isEmpty = right.isEmpty :=
  perm.isEmpty_eq

/-- Nil-ness transfers across a permutation in either direction. -/
theorem perm_eq_nil_iff {α : Type*} {left right : List α}
    (perm : left.Perm right) : left = [] ↔ right = [] := by
  constructor
  · intro leftEmpty
    have nilPerm : ([] : List α).Perm right := by
      simpa [leftEmpty] using perm
    exact nilPerm.nil_eq.symm
  · intro rightEmpty
    have permNil : left.Perm ([] : List α) := by
      simpa [rightEmpty] using perm
    exact permNil.eq_nil

/-- Extract a head and tail from a successful `mapM` over a cons. -/
private theorem mapM_cons_some {α β : Type*} (step : α → Option β)
    {head : α} {tail : List α} {output : List β}
    (computed : (head :: tail).mapM step = some output) :
    ∃ headResult tailOutput, step head = some headResult ∧
      tail.mapM step = some tailOutput ∧ output = headResult :: tailOutput := by
  rw [List.mapM_cons] at computed
  obtain ⟨headResult, headComputed, restComputed⟩ := Option.bind_eq_some_iff.mp computed
  obtain ⟨tailOutput, tailComputed, finalComputed⟩ :=
    Option.bind_eq_some_iff.mp restComputed
  exact ⟨headResult, tailOutput, headComputed, tailComputed,
    by simpa using finalComputed.symm⟩

/-- `mapM` over a permutation succeeds on the same nodes and returns permuted results. -/
private theorem mapM_perm {α β : Type*} (step : α → Option β) :
    ∀ {left right : List α}, left.Perm right →
      ∀ output, left.mapM step = some output →
        ∃ other, right.mapM step = some other ∧ output.Perm other := by
  intro left right permutation
  induction permutation with
  | nil =>
      intro output computed
      have outputEmpty : output = [] := by
        simpa using computed.symm
      subst output
      exact ⟨[], rfl, List.Perm.refl _⟩
  | cons head permutation ih =>
      intro output computed
      obtain ⟨result, tailOutput, headComputed, tailComputed, outputEqual⟩ :=
        mapM_cons_some step computed
      obtain ⟨tail', tail'Computed, tailPerm⟩ := ih tailOutput tailComputed
      refine ⟨result :: tail', ?_, ?_⟩
      · simp [List.mapM_cons, headComputed, tail'Computed]
      · rw [outputEqual]
        exact List.Perm.cons result tailPerm
  | swap first second rest =>
      intro output computed
      obtain ⟨secondResult, firstTail, secondComputed, firstTailComputed, outputEqual⟩ :=
        mapM_cons_some step computed
      obtain ⟨firstResult, restOutput, firstComputed, restComputed, firstTailEqual⟩ :=
        mapM_cons_some step firstTailComputed
      refine ⟨firstResult :: secondResult :: restOutput, ?_, ?_⟩
      · simp [List.mapM_cons, firstComputed, secondComputed, restComputed]
      · rw [outputEqual, firstTailEqual]
        exact List.Perm.swap firstResult secondResult restOutput
  | trans firstPermutation secondPermutation firstIH secondIH =>
      intro output computed
      obtain ⟨middle, middleComputed, outputPerm⟩ := firstIH output computed
      obtain ⟨other, otherComputed, middlePerm⟩ := secondIH middle middleComputed
      exact ⟨other, otherComputed, outputPerm.trans middlePerm⟩

private theorem mapM_isSome_eq_of_perm {α β : Type*} (step : α → Option β)
    {left right : List α} (permutation : left.Perm right) :
    (left.mapM step).isSome = (right.mapM step).isSome := by
  cases leftComputed : left.mapM step with
  | none =>
      cases rightComputed : right.mapM step with
      | none => rfl
      | some output =>
          obtain ⟨other, otherComputed, _⟩ :=
            mapM_perm step permutation.symm output rightComputed
          rw [leftComputed] at otherComputed
          simp at otherComputed
  | some output =>
      obtain ⟨other, otherComputed, _⟩ := mapM_perm step permutation output leftComputed
      rw [otherComputed]
      rfl

/-- Pointwise successful `mapM` results inherit any pointwise output relation. -/
private theorem mapM_forall₂_of_sound {α V : Type*}
    (first second : α → Option (OfficialRuleMajorKey V)) :
    ∀ (inputs : List α),
      (∀ input, input ∈ inputs →
        ∀ left right, first input = some left → second input = some right →
          SameConstitution left right) →
      ∀ leftOutput rightOutput,
        inputs.mapM first = some leftOutput →
          inputs.mapM second = some rightOutput →
            List.Forall₂ SameConstitution leftOutput rightOutput
  | [], _, leftOutput, rightOutput, leftComputed, rightComputed => by
      have leftEmpty : leftOutput = [] := by simpa using leftComputed.symm
      have rightEmpty : rightOutput = [] := by simpa using rightComputed.symm
      subst leftOutput
      subst rightOutput
      exact List.Forall₂.nil
  | input :: inputs, sound, leftOutput, rightOutput, leftComputed, rightComputed => by
      obtain ⟨firstResult, leftTail, firstComputed, leftTailComputed, leftOutputEqual⟩ :=
        mapM_cons_some first leftComputed
      obtain ⟨secondResult, rightTail, secondComputed, rightTailComputed,
        rightOutputEqual⟩ := mapM_cons_some second rightComputed
      rw [leftOutputEqual, rightOutputEqual]
      exact List.Forall₂.cons
        (sound input (by simp) firstResult secondResult firstComputed secondComputed)
        (mapM_forall₂_of_sound first second inputs
          (fun tailInput present => sound tailInput (by simp [present]))
          leftTail rightTail leftTailComputed rightTailComputed)

theorem forall₂_imp {α β : Type*} {first second : α → β → Prop}
    (implication : ∀ left right, first left right → second left right) :
    ∀ {left right}, List.Forall₂ first left right → List.Forall₂ second left right
  | _, _, List.Forall₂.nil => List.Forall₂.nil
  | _, _, List.Forall₂.cons head tail =>
      List.Forall₂.cons (implication _ _ head) (forall₂_imp implication tail)

/-- Reorder the left list along a permutation of the right list while preserving a `Forall₂`
relation. -/
private theorem forall₂_exists_perm_of_perm_right {α : Type*} {relation : α → α → Prop} :
    ∀ {right right' : List α}, right.Perm right' → ∀ {left : List α},
      List.Forall₂ relation left right →
        ∃ left', left'.Perm left ∧ List.Forall₂ relation left' right'
  | _, _, .nil, _, related => by
      cases related
      exact ⟨[], List.Perm.refl _, List.Forall₂.nil⟩
  | _, _, .cons _ permutation, _, List.Forall₂.cons head tail => by
      obtain ⟨tail', tail'Perm, tail'Related⟩ :=
        forall₂_exists_perm_of_perm_right permutation tail
      exact ⟨_ :: tail', List.Perm.cons _ tail'Perm,
        List.Forall₂.cons head tail'Related⟩
  | _, _, .swap _ _ _, _,
      List.Forall₂.cons head (List.Forall₂.cons secondHead restRelated) =>
      ⟨_, List.Perm.swap _ _ _,
        List.Forall₂.cons secondHead (List.Forall₂.cons head restRelated)⟩
  | _, _, .trans firstPermutation secondPermutation, _, related => by
      obtain ⟨middle, middlePerm, middleRelated⟩ :=
        forall₂_exists_perm_of_perm_right firstPermutation related
      obtain ⟨final, finalPerm, finalRelated⟩ :=
        forall₂_exists_perm_of_perm_right secondPermutation middleRelated
      exact ⟨final, finalPerm.trans middlePerm, finalRelated⟩

theorem map_eq_of_forall₂ {α β : Type*} {relation : α → α → Prop} (project : α → β) :
    ∀ {left right : List α}, List.Forall₂ relation left right →
      (∀ leftValue rightValue, relation leftValue rightValue →
        project leftValue = project rightValue) →
        left.map project = right.map project
  | _, _, List.Forall₂.nil, _ => rfl
  | _, _, List.Forall₂.cons head tail, sound => by
      rw [List.map_cons, List.map_cons, sound _ _ head,
        map_eq_of_forall₂ project tail sound]

theorem all_complete_eq_of_forall₂_sameConstitution {V : Type*}
    {left right : List (OfficialRuleMajorKey V)}
    (related : List.Forall₂ SameConstitution left right) :
    left.all OfficialRuleMajorKey.complete = right.all OfficialRuleMajorKey.complete := by
  induction related with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.all_cons, head.2.2.2, ih]

/-! ## Merging depends only on layer values -/

/-- A merge written directly over the sequence of child layer values. -/
def mergeLayerValues {α : Type*}
    (sequence : List (List (List (OfficialSparseEntry α)))) :
    List (List (OfficialSparseEntry α)) :=
  let count := sequence.foldl (fun longest layers => max longest layers.length) 0
  (List.range count).map fun depth =>
    sequence.zipIdx.flatMap fun entry =>
      prefixLayer entry.2 (entry.1.getD depth [])

theorem childLayerCount_map {V α : Type*} (keys : List (OfficialRuleMajorKey V))
    (layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α))) :
    childLayerCount keys layers =
      (keys.map layers).foldl (fun longest layer => max longest layer.length) 0 := by
  unfold childLayerCount
  generalize 0 = initial
  induction keys generalizing initial with
  | nil => rfl
  | cons key keys inductionHypothesis =>
      simp only [List.foldl_cons, List.map_cons]
      exact inductionHypothesis _

theorem mergeChildren_eq_mergeLayerValues {V α : Type*}
    (keys : List (OfficialRuleMajorKey V))
    (layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α))) :
    mergeChildren keys layers = mergeLayerValues (keys.map layers) := by
  unfold mergeChildren mergeLayerValues
  rw [childLayerCount_map]
  apply List.map_congr_left
  intro depth _
  rw [List.zipIdx_map]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro entry _
  cases entry
  rfl

theorem mergeChildren_eq_of_map_layers_eq {V α : Type*}
    (left right : List (OfficialRuleMajorKey V))
    (layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α)))
    (equal : left.map layers = right.map layers) :
    mergeChildren left layers = mergeChildren right layers := by
  rw [mergeChildren_eq_mergeLayerValues left layers,
    mergeChildren_eq_mergeLayerValues right layers, equal]

/-! ## Sorting only depends on the triple multiset -/

/-- A list is a relation-wise permutation of another when some permutation of the first is
pointwise related to the second. -/
def RelationPerm {α : Type*} (relation : α → α → Prop)
    (left right : List α) : Prop :=
  ∃ arranged, arranged.Perm left ∧ List.Forall₂ relation arranged right

/-- Two descending lists with the same triple multiset have the same triple sequence. -/
theorem map_tripleOf_eq_of_descending {V : Type*}
    (left right : List (OfficialRuleMajorKey V))
    (leftDescending : OfficialRuleMajorKey.Descending left)
    (rightDescending : OfficialRuleMajorKey.Descending right)
    (related : RelationPerm
      (fun first second : OfficialRuleMajorKey V => tripleOf first = tripleOf second)
      left right) :
    left.map tripleOf = right.map tripleOf := by
  rcases related with ⟨arranged, arrangedPerm, arrangedRelated⟩
  have arrangedMap : arranged.map tripleOf = right.map tripleOf :=
    map_eq_of_forall₂ tripleOf arrangedRelated (fun _ _ equal => equal)
  have permuted : (left.map tripleOf).Perm (right.map tripleOf) := by
    rw [← arrangedMap]
    exact (arrangedPerm.map tripleOf).symm
  have leftPairwise : (left.map tripleOf).Pairwise
      (fun first second => compareTriple first second ≠ Ordering.lt) :=
    leftDescending.map tripleOf (fun first second less => by
      rw [← compare_eq_compareTriple]
      exact less)
  have rightPairwise : (right.map tripleOf).Pairwise
      (fun first second => compareTriple first second ≠ Ordering.lt) :=
    rightDescending.map tripleOf (fun first second less => by
      rw [← compare_eq_compareTriple]
      exact less)
  exact List.Perm.eq_of_pairwise
    (fun first second _ _ firstNotLt secondNotLt =>
      compareTriple_eq_of_not_lt_not_lt first second firstNotLt secondNotLt)
    leftPairwise rightPairwise permuted

/-! ## Compiler fidelity -/

/-- Arbitrary-fuel projection fidelity: two pointwise-permuted child enumerators produce
either a failed build on at least one side, or successful keys with equal Rule-1a, Rule-1b,
Rule-2 projections and equal completeness.  Provenance ordering is not constrained. -/
theorem buildOfficialRuleMajorKey_optionSameConstitution_of_children_perm
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V)
    (children replacement : OfficialCIPNode V → List (OfficialCIPNode V))
    (same : ∀ node, (children node).Perm (replacement node)) :
    ∀ fuel node,
      OptionSameConstitution
        (m.buildOfficialRuleMajorKey children fuel node)
        (m.buildOfficialRuleMajorKey replacement fuel node)
  | 0, node => by
      have emptyEqual : (children node).isEmpty = (replacement node).isEmpty :=
        perm_isEmpty_eq (same node)
      unfold OptionSameConstitution SameConstitution
      simp [MoleculeGraph.buildOfficialRuleMajorKey,
        MoleculeGraph.officialRuleMajorRootKey, emptyEqual]
  | fuel + 1, node => by
      by_cases emptyLeft : (children node).isEmpty = true
      · have childrenEmpty : children node = [] := List.isEmpty_iff.mp emptyLeft
        have replacementEmpty : replacement node = [] :=
          (perm_eq_nil_iff (same node)).mp childrenEmpty
        have emptyRight : (replacement node).isEmpty = true := by
          simp [replacementEmpty]
        unfold OptionSameConstitution SameConstitution
        simp [MoleculeGraph.buildOfficialRuleMajorKey,
          MoleculeGraph.officialRuleMajorRootKey, emptyLeft, emptyRight]
      · have emptyRightNot : ¬ (replacement node).isEmpty = true := by
          intro rightTrue
          have replacementEmpty : replacement node = [] := List.isEmpty_iff.mp rightTrue
          have childrenEmpty : children node = [] :=
            (perm_eq_nil_iff (same node)).mpr replacementEmpty
          exact emptyLeft (by simp [childrenEmpty])
        cases leftKeysComputed :
            (children node).mapM (m.buildOfficialRuleMajorKey children fuel) with
        | none =>
            have leftBuild :
                m.buildOfficialRuleMajorKey children (fuel + 1) node = none := by
              simp [MoleculeGraph.buildOfficialRuleMajorKey, emptyLeft,
                leftKeysComputed]
            rw [leftBuild]
            exact optionSameConstitution_none_left _
        | some leftKeys =>
            cases rightKeysComputed :
                (replacement node).mapM
                  (m.buildOfficialRuleMajorKey replacement fuel) with
            | none =>
                have rightBuild :
                    m.buildOfficialRuleMajorKey replacement (fuel + 1) node = none := by
                  simp [MoleculeGraph.buildOfficialRuleMajorKey, emptyRightNot,
                    rightKeysComputed]
                rw [rightBuild]
                exact optionSameConstitution_none_right _
            | some rightKeys =>
                cases leftSortedComputed : OfficialRuleMajorKey.sort? leftKeys with
                | none =>
                    have leftBuild :
                        m.buildOfficialRuleMajorKey children (fuel + 1) node = none := by
                      simp [MoleculeGraph.buildOfficialRuleMajorKey, emptyLeft,
                        leftKeysComputed, leftSortedComputed]
                    rw [leftBuild]
                    exact optionSameConstitution_none_left _
                | some leftSorted =>
                    cases rightSortedComputed : OfficialRuleMajorKey.sort? rightKeys with
                    | none =>
                        have rightBuild :
                            m.buildOfficialRuleMajorKey replacement (fuel + 1) node =
                              none := by
                          simp [MoleculeGraph.buildOfficialRuleMajorKey, emptyRightNot,
                            rightKeysComputed, rightSortedComputed]
                        rw [rightBuild]
                        exact optionSameConstitution_none_right _
                    | some rightSorted =>
                        have leftBuild :
                            m.buildOfficialRuleMajorKey children (fuel + 1) node =
                              some (OfficialRuleMajorKey.assemble
                                (m.officialRuleMajorRootKey node false) leftSorted) := by
                          simp [MoleculeGraph.buildOfficialRuleMajorKey, emptyLeft,
                            leftKeysComputed, leftSortedComputed]
                        have rightBuild :
                            m.buildOfficialRuleMajorKey replacement (fuel + 1) node =
                              some (OfficialRuleMajorKey.assemble
                                (m.officialRuleMajorRootKey node false) rightSorted) := by
                          simp [MoleculeGraph.buildOfficialRuleMajorKey, emptyRightNot,
                            rightKeysComputed, rightSortedComputed]
                        rw [leftBuild, rightBuild]
                        change SameConstitution
                          (OfficialRuleMajorKey.assemble
                            (m.officialRuleMajorRootKey node false) leftSorted)
                          (OfficialRuleMajorKey.assemble
                            (m.officialRuleMajorRootKey node false) rightSorted)
                        -- Recursive projection agreement at every child.
                        have stepSound : ∀ child, child ∈ children node →
                            ∀ left right,
                              m.buildOfficialRuleMajorKey children fuel child = some left →
                              m.buildOfficialRuleMajorKey replacement fuel child = some right →
                              SameConstitution left right := by
                          intro child _ left right leftComputed rightComputed
                          have related :=
                            buildOfficialRuleMajorKey_optionSameConstitution_of_children_perm
                              m children replacement same fuel child
                          unfold OptionSameConstitution at related
                          rw [leftComputed, rightComputed] at related
                          exact related
                        -- Run the replacement enumerator over the reference child list.
                        obtain ⟨leftKeysReplacement, leftKeysReplacementComputed,
                          rightKeysPermLeft⟩ :=
                          mapM_perm (m.buildOfficialRuleMajorKey replacement fuel)
                            (same node).symm rightKeys rightKeysComputed
                        have positionalRelated :
                            List.Forall₂ SameConstitution leftKeys leftKeysReplacement :=
                          mapM_forall₂_of_sound
                            (m.buildOfficialRuleMajorKey children fuel)
                            (m.buildOfficialRuleMajorKey replacement fuel)
                            (children node) stepSound leftKeys leftKeysReplacement
                            leftKeysComputed leftKeysReplacementComputed
                        -- Relation-wise permutation of the sorting-visible triples.
                        have tripleRelated :
                            List.Forall₂
                              (fun first second : OfficialRuleMajorKey V =>
                                tripleOf first = tripleOf second)
                              leftKeys leftKeysReplacement :=
                          forall₂_imp (fun first second aligned =>
                            sameConstitution_triple aligned) positionalRelated
                        obtain ⟨arranged, arrangedPerm, arrangedRelated⟩ :=
                          forall₂_exists_perm_of_perm_right
                            (rightKeysPermLeft.symm) tripleRelated
                        have inputRelation : RelationPerm
                            (fun first second : OfficialRuleMajorKey V =>
                              tripleOf first = tripleOf second)
                            leftKeys rightKeys :=
                          ⟨arranged, arrangedPerm, arrangedRelated⟩
                        -- Sort both sides and compare the triple sequences.
                        have sortedRelation : RelationPerm
                            (fun first second : OfficialRuleMajorKey V =>
                              tripleOf first = tripleOf second)
                            leftSorted rightSorted := by
                          rcases inputRelation with
                            ⟨arranged, arrangedPerm, arrangedRelated⟩
                          have rightKeysPermSorted : rightKeys.Perm rightSorted :=
                            (OfficialRuleMajorKey.sort?_perm rightKeys rightSorted
                              rightSortedComputed).symm
                          obtain ⟨arrangedSorted, arrangedSortedPerm,
                            arrangedSortedRelated⟩ :=
                            forall₂_exists_perm_of_perm_right
                              rightKeysPermSorted arrangedRelated
                          have leftKeysPermSorted : leftKeys.Perm leftSorted :=
                            (OfficialRuleMajorKey.sort?_perm leftKeys leftSorted
                              leftSortedComputed).symm
                          exact ⟨arrangedSorted,
                            arrangedSortedPerm.trans (arrangedPerm.trans leftKeysPermSorted),
                            arrangedSortedRelated⟩
                        have tripleEqual : leftSorted.map tripleOf = rightSorted.map tripleOf :=
                          map_tripleOf_eq_of_descending leftSorted rightSorted
                            (OfficialRuleMajorKey.sort?_descending leftKeys leftSorted
                              leftSortedComputed)
                            (OfficialRuleMajorKey.sort?_descending rightKeys rightSorted
                              rightSortedComputed)
                            sortedRelation
                        have map1a : leftSorted.map
                            (fun key : OfficialRuleMajorKey V => key.rule1a) =
                            rightSorted.map (fun key => key.rule1a) := by
                          have projected := congrArg (List.map RuleTriple.rule1a) tripleEqual
                          simpa [tripleOf, List.map_map, Function.comp_def] using projected
                        have map1b : leftSorted.map
                            (fun key : OfficialRuleMajorKey V => key.rule1b) =
                            rightSorted.map (fun key => key.rule1b) := by
                          have projected := congrArg (List.map RuleTriple.rule1b) tripleEqual
                          simpa [tripleOf, List.map_map, Function.comp_def] using projected
                        have map2 : leftSorted.map
                            (fun key : OfficialRuleMajorKey V => key.rule2) =
                            rightSorted.map (fun key => key.rule2) := by
                          have projected := congrArg (List.map RuleTriple.rule2) tripleEqual
                          simpa [tripleOf, List.map_map, Function.comp_def] using projected
                        have completenessEqual :
                            leftSorted.all OfficialRuleMajorKey.complete =
                              rightSorted.all OfficialRuleMajorKey.complete := by
                          have leftToKeys : leftSorted.all OfficialRuleMajorKey.complete =
                              leftKeys.all OfficialRuleMajorKey.complete :=
                            (OfficialRuleMajorKey.sort?_perm leftKeys leftSorted
                              leftSortedComputed).all_eq
                          have keysPositional : leftKeys.all OfficialRuleMajorKey.complete =
                              leftKeysReplacement.all OfficialRuleMajorKey.complete :=
                            all_complete_eq_of_forall₂_sameConstitution positionalRelated
                          have replacementToRight : leftKeysReplacement.all
                              OfficialRuleMajorKey.complete =
                              rightKeys.all OfficialRuleMajorKey.complete :=
                            rightKeysPermLeft.all_eq.symm
                          have rightToKeys : rightSorted.all OfficialRuleMajorKey.complete =
                              rightKeys.all OfficialRuleMajorKey.complete :=
                            (OfficialRuleMajorKey.sort?_perm rightKeys rightSorted
                              rightSortedComputed).all_eq
                          rw [leftToKeys, keysPositional, replacementToRight, rightToKeys]
                        refine ⟨?_, ?_, ?_, ?_⟩
                        · simp only [OfficialRuleMajorKey.assemble]
                          rw [mergeChildren_eq_of_map_layers_eq leftSorted rightSorted
                            (fun key : OfficialRuleMajorKey V => key.rule1a) map1a]
                        · simp only [OfficialRuleMajorKey.assemble]
                          rw [mergeChildren_eq_of_map_layers_eq leftSorted rightSorted
                            (fun key : OfficialRuleMajorKey V => key.rule1b) map1b]
                        · simp only [OfficialRuleMajorKey.assemble]
                          rw [mergeChildren_eq_of_map_layers_eq leftSorted rightSorted
                            (fun key : OfficialRuleMajorKey V => key.rule2) map2]
                        · simp only [OfficialRuleMajorKey.assemble]
                          exact completenessEqual

/-- Same-root form: two successful compilations of the same physical root from pointwise
permuted child enumerators have equal Rule-1a, Rule-1b, Rule-2 projections and completeness. -/
theorem build_sameConstitution_of_children_perm
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V)
    (children replacement : OfficialCIPNode V → List (OfficialCIPNode V))
    (same : ∀ node, (children node).Perm (replacement node))
    (fuel : ℕ) (node : OfficialCIPNode V)
    (left right : OfficialRuleMajorKey V)
    (leftComputed : m.buildOfficialRuleMajorKey children fuel node = some left)
    (rightComputed : m.buildOfficialRuleMajorKey replacement fuel node = some right) :
    SameConstitution left right := by
  have related :=
    buildOfficialRuleMajorKey_optionSameConstitution_of_children_perm
      m children replacement same fuel node
  unfold OptionSameConstitution at related
  rw [leftComputed, rightComputed] at related
  exact related

/-- Pair-level `compare?` coherence for the same two physical roots across two child
enumerators. -/
theorem compare?_eq_of_children_perm
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V)
    (children replacement : OfficialCIPNode V → List (OfficialCIPNode V))
    (same : ∀ node, (children node).Perm (replacement node))
    (fuel : ℕ) (leftRoot rightRoot : OfficialCIPNode V)
    (leftReference leftExecutable rightReference rightExecutable : OfficialRuleMajorKey V)
    (leftReferenceComputed :
      m.buildOfficialRuleMajorKey children fuel leftRoot = some leftReference)
    (leftExecutableComputed :
      m.buildOfficialRuleMajorKey replacement fuel leftRoot = some leftExecutable)
    (rightReferenceComputed :
      m.buildOfficialRuleMajorKey children fuel rightRoot = some rightReference)
    (rightExecutableComputed :
      m.buildOfficialRuleMajorKey replacement fuel rightRoot = some rightExecutable) :
    OfficialRuleMajorKey.compare? leftReference rightReference =
      OfficialRuleMajorKey.compare? leftExecutable rightExecutable :=
  compare?_congr_of_sameConstitution
    (build_sameConstitution_of_children_perm m children replacement same fuel leftRoot
      leftReference leftExecutable leftReferenceComputed leftExecutableComputed)
    (build_sameConstitution_of_children_perm m children replacement same fuel rightRoot
      rightReference rightExecutable rightReferenceComputed rightExecutableComputed)

/-- Pair-level `compareTrace` coherence for the same two physical roots across two child
enumerators. -/
theorem compareTrace_eq_of_children_perm
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V)
    (children replacement : OfficialCIPNode V → List (OfficialCIPNode V))
    (same : ∀ node, (children node).Perm (replacement node))
    (fuel : ℕ) (leftRoot rightRoot : OfficialCIPNode V)
    (leftReference leftExecutable rightReference rightExecutable : OfficialRuleMajorKey V)
    (leftReferenceComputed :
      m.buildOfficialRuleMajorKey children fuel leftRoot = some leftReference)
    (leftExecutableComputed :
      m.buildOfficialRuleMajorKey replacement fuel leftRoot = some leftExecutable)
    (rightReferenceComputed :
      m.buildOfficialRuleMajorKey children fuel rightRoot = some rightReference)
    (rightExecutableComputed :
      m.buildOfficialRuleMajorKey replacement fuel rightRoot = some rightExecutable) :
    OfficialRuleMajorKey.compareTrace leftReference rightReference =
      OfficialRuleMajorKey.compareTrace leftExecutable rightExecutable :=
  compareTrace_eq_of_sameConstitution
    (build_sameConstitution_of_children_perm m children replacement same fuel leftRoot
      leftReference leftExecutable leftReferenceComputed leftExecutableComputed)
    (build_sameConstitution_of_children_perm m children replacement same fuel rightRoot
      rightReference rightExecutable rightReferenceComputed rightExecutableComputed)

end CompilerProjectionFidelity
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.optionSameConstitution_none_left
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.optionSameConstitution_none_right
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.compareNat_eq_eq_iff
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.compareRule1b_eq_eq_iff
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.compareSparseEntry_eq_eq_iff
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.compareSparseLayer_eq_eq_iff
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.list_compareLex_eq_eq_iff
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.compareSparseLayers_eq_eq_iff
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.compareSparseLayers_self
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.compareTriple_self
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.compareTriple_eq_eq_iff
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.compareTriple_eq_of_not_lt_not_lt
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.sameConstitution_triple
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.compare_eq_eq_of_sameConstitution
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.compare?_eq_of_sameConstitution
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.compareTrace_eq_of_sameConstitution
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.compare_eq_of_sameConstitution
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.compare?_congr_of_sameConstitution
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.perm_isEmpty_eq
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.perm_eq_nil_iff
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.forall₂_imp
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.map_eq_of_forall₂
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.all_complete_eq_of_forall₂_sameConstitution
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.childLayerCount_map
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.mergeChildren_eq_mergeLayerValues
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.mergeChildren_eq_of_map_layers_eq
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.map_tripleOf_eq_of_descending
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.buildOfficialRuleMajorKey_optionSameConstitution_of_children_perm
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.build_sameConstitution_of_children_perm
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.compare?_eq_of_children_perm
assert_kernel_only TetraStereo.OneCenter.CompilerProjectionFidelity.compareTrace_eq_of_children_perm
