import TetraStereo.OneCenter.DeclarativeCIPStereochemical

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section

universe u

/-!
# Global priority coherence

This module proves the algebraic theorem needed by the full declarative CIP program: the
first-decisive-rule composition of all nine sequence-rule slots is a total preorder whenever every
rule-local ligand judgment obeys the laws of an ordered comparison.  The proof is independent of
the executable comparator and does not enumerate the four ligands or hard-code a sorting
algorithm.
-/

namespace SequenceRule

/-- Semantic ranks distinguish sequence rules. -/
theorem rank_injective : Function.Injective rank := by
  intro first second h
  cases first <;> cases second <;> simp_all [rank]

end SequenceRule

/-- The exact local laws needed for composing all sequence rules lexicographically.

The mixed laws are essential: strict priority must survive a tie on either side.  `reverse_lt`
states that a junior outcome in one direction is a senior outcome in the reverse direction. -/
structure RuleOutcomeOrderLaws {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
    (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit) : Prop where
  functional : ∀ rule unit left right first second,
    problem.RuleOutcome descriptorMap rule unit left right first →
    problem.RuleOutcome descriptorMap rule unit left right second →
    first = second
  total : ∀ rule unit left right,
    ∃ outcome, problem.RuleOutcome descriptorMap rule unit left right outcome
  eq_refl : ∀ rule unit ligand,
    problem.RuleOutcome descriptorMap rule unit ligand ligand Ordering.eq
  eq_symm : ∀ rule unit left right,
    problem.RuleOutcome descriptorMap rule unit left right Ordering.eq →
    problem.RuleOutcome descriptorMap rule unit right left Ordering.eq
  eq_trans : ∀ rule unit first second third,
    problem.RuleOutcome descriptorMap rule unit first second Ordering.eq →
    problem.RuleOutcome descriptorMap rule unit second third Ordering.eq →
    problem.RuleOutcome descriptorMap rule unit first third Ordering.eq
  gt_trans : ∀ rule unit first second third,
    problem.RuleOutcome descriptorMap rule unit first second Ordering.gt →
    problem.RuleOutcome descriptorMap rule unit second third Ordering.gt →
    problem.RuleOutcome descriptorMap rule unit first third Ordering.gt
  gt_eq_trans : ∀ rule unit first second third,
    problem.RuleOutcome descriptorMap rule unit first second Ordering.gt →
    problem.RuleOutcome descriptorMap rule unit second third Ordering.eq →
    problem.RuleOutcome descriptorMap rule unit first third Ordering.gt
  eq_gt_trans : ∀ rule unit first second third,
    problem.RuleOutcome descriptorMap rule unit first second Ordering.eq →
    problem.RuleOutcome descriptorMap rule unit second third Ordering.gt →
    problem.RuleOutcome descriptorMap rule unit first third Ordering.gt
  reverse_lt : ∀ rule unit left right,
    problem.RuleOutcome descriptorMap rule unit left right Ordering.lt →
    problem.RuleOutcome descriptorMap rule unit right left Ordering.gt

namespace RuleOutcomeOrderLaws

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
variable {problem : Problem Atom Unit} {descriptorMap : DescriptorMap Unit}

theorem tied_refl (laws : RuleOutcomeOrderLaws problem descriptorMap)
    (unit : Unit) (ligand : Fin 4) :
    problem.Tied descriptorMap unit ligand ligand :=
  fun rule => laws.eq_refl rule unit ligand

theorem tied_symm (laws : RuleOutcomeOrderLaws problem descriptorMap)
    {unit : Unit} {left right : Fin 4}
    (h : problem.Tied descriptorMap unit left right) :
    problem.Tied descriptorMap unit right left :=
  fun rule => laws.eq_symm rule unit left right (h rule)

theorem tied_trans (laws : RuleOutcomeOrderLaws problem descriptorMap)
    {unit : Unit} {first second third : Fin 4}
    (hfirst : problem.Tied descriptorMap unit first second)
    (hsecond : problem.Tied descriptorMap unit second third) :
    problem.Tied descriptorMap unit first third :=
  fun rule => laws.eq_trans rule unit first second third (hfirst rule) (hsecond rule)

theorem higher_tied_trans (laws : RuleOutcomeOrderLaws problem descriptorMap)
    {unit : Unit} {first second third : Fin 4}
    (hfirst : problem.Higher descriptorMap unit first second)
    (hsecond : problem.Tied descriptorMap unit second third) :
    problem.Higher descriptorMap unit first third := by
  rcases hfirst with ⟨rule, hearlier, hdecisive⟩
  refine ⟨rule, ?_, laws.gt_eq_trans rule unit first second third hdecisive (hsecond rule)⟩
  intro earlier hbefore
  exact laws.eq_trans earlier unit first second third
    (hearlier earlier hbefore) (hsecond earlier)

theorem tied_higher_trans (laws : RuleOutcomeOrderLaws problem descriptorMap)
    {unit : Unit} {first second third : Fin 4}
    (hfirst : problem.Tied descriptorMap unit first second)
    (hsecond : problem.Higher descriptorMap unit second third) :
    problem.Higher descriptorMap unit first third := by
  rcases hsecond with ⟨rule, hearlier, hdecisive⟩
  refine ⟨rule, ?_, laws.eq_gt_trans rule unit first second third (hfirst rule) hdecisive⟩
  intro earlier hbefore
  exact laws.eq_trans earlier unit first second third
    (hfirst earlier) (hearlier earlier hbefore)

theorem higher_trans (laws : RuleOutcomeOrderLaws problem descriptorMap)
    {unit : Unit} {first second third : Fin 4}
    (hfirst : problem.Higher descriptorMap unit first second)
    (hsecond : problem.Higher descriptorMap unit second third) :
    problem.Higher descriptorMap unit first third := by
  rcases hfirst with ⟨firstRule, hfirstEarlier, hfirstDecisive⟩
  rcases hsecond with ⟨secondRule, hsecondEarlier, hsecondDecisive⟩
  rcases lt_trichotomy firstRule.rank secondRule.rank with hbefore | hequal | hafter
  · refine ⟨firstRule, ?_, laws.gt_eq_trans firstRule unit first second third
      hfirstDecisive (hsecondEarlier firstRule hbefore)⟩
    intro earlier hearlier
    exact laws.eq_trans earlier unit first second third
      (hfirstEarlier earlier hearlier)
      (hsecondEarlier earlier (Nat.lt_trans hearlier hbefore))
  · have hrule : firstRule = secondRule := SequenceRule.rank_injective hequal
    subst secondRule
    refine ⟨firstRule, ?_, laws.gt_trans firstRule unit first second third
      hfirstDecisive hsecondDecisive⟩
    intro earlier hearlier
    exact laws.eq_trans earlier unit first second third
      (hfirstEarlier earlier hearlier) (hsecondEarlier earlier hearlier)
  · refine ⟨secondRule, ?_, laws.eq_gt_trans secondRule unit first second third
      (hfirstEarlier secondRule hafter) hsecondDecisive⟩
    intro earlier hearlier
    exact laws.eq_trans earlier unit first second third
      (hfirstEarlier earlier (Nat.lt_trans hearlier hafter))
      (hsecondEarlier earlier hearlier)

/-- At any unit, two ligands are comparable by the first decisive rule, or tie at every rule. -/
theorem weakPriority_total (laws : RuleOutcomeOrderLaws problem descriptorMap)
    (unit : Unit) (left right : Fin 4) :
    problem.WeakPriority descriptorMap unit left right ∨
      problem.WeakPriority descriptorMap unit right left := by
  classical
  by_cases hall : ∀ rule,
      problem.RuleOutcome descriptorMap rule unit left right Ordering.eq
  · exact Or.inl (Or.inr hall)
  · push_neg at hall
    let decisiveRank : ℕ → Prop := fun rank =>
      ∃ rule, rule.rank = rank ∧
        ¬problem.RuleOutcome descriptorMap rule unit left right Ordering.eq
    have hexists : ∃ rank, decisiveRank rank := by
      rcases hall with ⟨rule, hrule⟩
      exact ⟨rule.rank, rule, rfl, hrule⟩
    let firstRank := Nat.find hexists
    rcases Nat.find_spec hexists with ⟨rule, hrank, hnotEq⟩
    have hearlier : problem.EarlierRulesTie descriptorMap rule unit left right := by
      intro earlier hbefore
      by_contra hnotEarlierEq
      have hearlierWitness : decisiveRank earlier.rank :=
        ⟨earlier, rfl, hnotEarlierEq⟩
      have hminimal : firstRank ≤ earlier.rank := Nat.find_min' hexists hearlierWitness
      have : earlier.rank < firstRank := by
        simpa [SequenceRule.Before, firstRank, hrank] using hbefore
      exact (Nat.not_lt_of_ge hminimal) this
    rcases laws.total rule unit left right with ⟨outcome, houtcome⟩
    cases outcome with
    | lt =>
        refine Or.inr (Or.inl ⟨rule, ?_, laws.reverse_lt rule unit left right houtcome⟩)
        intro earlier hbefore
        exact laws.eq_symm earlier unit left right (hearlier earlier hbefore)
    | eq => exact (hnotEq houtcome).elim
    | gt => exact Or.inl (Or.inl ⟨rule, hearlier, houtcome⟩)

/-- The complete first-decisive-rule priority relation is a total preorder. -/
theorem priorityIsTotalPreorder
    (laws : RuleOutcomeOrderLaws problem descriptorMap) :
    PriorityIsTotalPreorder problem descriptorMap := by
  refine ⟨?_, ?_, ?_⟩
  · intro unit ligand
    exact Or.inr (laws.tied_refl unit ligand)
  · intro unit first second third hfirst hsecond
    rcases hfirst with hfirstHigher | hfirstTied
    · rcases hsecond with hsecondHigher | hsecondTied
      · exact Or.inl (laws.higher_trans hfirstHigher hsecondHigher)
      · exact Or.inl (laws.higher_tied_trans hfirstHigher hsecondTied)
    · rcases hsecond with hsecondHigher | hsecondTied
      · exact Or.inl (laws.tied_higher_trans hfirstTied hsecondHigher)
      · exact Or.inr (laws.tied_trans hfirstTied hsecondTied)
  · exact laws.weakPriority_total

end RuleOutcomeOrderLaws

/-! ## Contextual laws for actual sequence-rule semantics -/

/-- The local order laws in their chemically correct form.

Later CIP rules need only behave coherently inside a class on which every earlier rule ties.  This
matters already for Rule 1b: a non-duplicate observation is inapplicable and therefore ties with
either duplicate distance, although two distinct duplicate distances need not tie with each other.
The unconditional `RuleOutcomeOrderLaws` above remains a useful sufficient condition; this
contextual package is the one intended for concrete CIP instantiation. -/
structure ContextualRuleOutcomeOrderLaws
    {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
    (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit) : Prop where
  functional : ∀ rule unit left right first second,
    problem.EarlierRulesTie descriptorMap rule unit left right →
    problem.RuleOutcome descriptorMap rule unit left right first →
    problem.RuleOutcome descriptorMap rule unit left right second →
    first = second
  total : ∀ rule unit left right,
    problem.EarlierRulesTie descriptorMap rule unit left right →
    ∃ outcome, problem.RuleOutcome descriptorMap rule unit left right outcome
  eq_refl : ∀ rule unit ligand,
    problem.RuleOutcome descriptorMap rule unit ligand ligand Ordering.eq
  eq_symm : ∀ rule unit left right,
    problem.EarlierRulesTie descriptorMap rule unit left right →
    problem.RuleOutcome descriptorMap rule unit left right Ordering.eq →
    problem.RuleOutcome descriptorMap rule unit right left Ordering.eq
  eq_trans : ∀ rule unit first second third,
    problem.EarlierRulesTie descriptorMap rule unit first second →
    problem.EarlierRulesTie descriptorMap rule unit second third →
    problem.RuleOutcome descriptorMap rule unit first second Ordering.eq →
    problem.RuleOutcome descriptorMap rule unit second third Ordering.eq →
    problem.RuleOutcome descriptorMap rule unit first third Ordering.eq
  gt_trans : ∀ rule unit first second third,
    problem.EarlierRulesTie descriptorMap rule unit first second →
    problem.EarlierRulesTie descriptorMap rule unit second third →
    problem.RuleOutcome descriptorMap rule unit first second Ordering.gt →
    problem.RuleOutcome descriptorMap rule unit second third Ordering.gt →
    problem.RuleOutcome descriptorMap rule unit first third Ordering.gt
  gt_eq_trans : ∀ rule unit first second third,
    problem.EarlierRulesTie descriptorMap rule unit first second →
    problem.EarlierRulesTie descriptorMap rule unit second third →
    problem.RuleOutcome descriptorMap rule unit first second Ordering.gt →
    problem.RuleOutcome descriptorMap rule unit second third Ordering.eq →
    problem.RuleOutcome descriptorMap rule unit first third Ordering.gt
  eq_gt_trans : ∀ rule unit first second third,
    problem.EarlierRulesTie descriptorMap rule unit first second →
    problem.EarlierRulesTie descriptorMap rule unit second third →
    problem.RuleOutcome descriptorMap rule unit first second Ordering.eq →
    problem.RuleOutcome descriptorMap rule unit second third Ordering.gt →
    problem.RuleOutcome descriptorMap rule unit first third Ordering.gt
  reverse_lt : ∀ rule unit left right,
    problem.EarlierRulesTie descriptorMap rule unit left right →
    problem.RuleOutcome descriptorMap rule unit left right Ordering.lt →
    problem.RuleOutcome descriptorMap rule unit right left Ordering.gt

namespace ContextualRuleOutcomeOrderLaws

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
variable {problem : Problem Atom Unit} {descriptorMap : DescriptorMap Unit}

private theorem prefixTie {rule : SequenceRule} {unit : Unit} {left right : Fin 4}
    (h : problem.EarlierRulesTie descriptorMap rule unit left right)
    {earlier : SequenceRule} (hearlier : earlier.Before rule) :
    problem.EarlierRulesTie descriptorMap earlier unit left right := by
  intro prior hprior
  exact h prior (hprior.trans hearlier)

private theorem tiedPrefix {rule : SequenceRule} {unit : Unit} {left right : Fin 4}
    (h : problem.Tied descriptorMap unit left right) :
    problem.EarlierRulesTie descriptorMap rule unit left right :=
  fun earlier _ => h earlier

theorem tied_trans (laws : ContextualRuleOutcomeOrderLaws problem descriptorMap)
    {unit : Unit} {first second third : Fin 4}
    (hfirst : problem.Tied descriptorMap unit first second)
    (hsecond : problem.Tied descriptorMap unit second third) :
    problem.Tied descriptorMap unit first third := by
  intro rule
  exact laws.eq_trans rule unit first second third
    (tiedPrefix hfirst) (tiedPrefix hsecond) (hfirst rule) (hsecond rule)

theorem higher_tied_trans (laws : ContextualRuleOutcomeOrderLaws problem descriptorMap)
    {unit : Unit} {first second third : Fin 4}
    (hfirst : problem.Higher descriptorMap unit first second)
    (hsecond : problem.Tied descriptorMap unit second third) :
    problem.Higher descriptorMap unit first third := by
  rcases hfirst with ⟨rule, hearlier, hdecisive⟩
  refine ⟨rule, ?_, laws.gt_eq_trans rule unit first second third
    hearlier (tiedPrefix hsecond) hdecisive (hsecond rule)⟩
  intro earlier hbefore
  exact laws.eq_trans earlier unit first second third
    (prefixTie hearlier hbefore) (tiedPrefix hsecond)
    (hearlier earlier hbefore) (hsecond earlier)

theorem tied_higher_trans (laws : ContextualRuleOutcomeOrderLaws problem descriptorMap)
    {unit : Unit} {first second third : Fin 4}
    (hfirst : problem.Tied descriptorMap unit first second)
    (hsecond : problem.Higher descriptorMap unit second third) :
    problem.Higher descriptorMap unit first third := by
  rcases hsecond with ⟨rule, hearlier, hdecisive⟩
  refine ⟨rule, ?_, laws.eq_gt_trans rule unit first second third
    (tiedPrefix hfirst) hearlier (hfirst rule) hdecisive⟩
  intro earlier hbefore
  exact laws.eq_trans earlier unit first second third
    (tiedPrefix hfirst) (prefixTie hearlier hbefore)
    (hfirst earlier) (hearlier earlier hbefore)

theorem higher_trans (laws : ContextualRuleOutcomeOrderLaws problem descriptorMap)
    {unit : Unit} {first second third : Fin 4}
    (hfirst : problem.Higher descriptorMap unit first second)
    (hsecond : problem.Higher descriptorMap unit second third) :
    problem.Higher descriptorMap unit first third := by
  rcases hfirst with ⟨firstRule, hfirstEarlier, hfirstDecisive⟩
  rcases hsecond with ⟨secondRule, hsecondEarlier, hsecondDecisive⟩
  rcases lt_trichotomy firstRule.rank secondRule.rank with hbefore | hequal | hafter
  · have hsecondAtFirst := prefixTie hsecondEarlier hbefore
    refine ⟨firstRule, ?_, laws.gt_eq_trans firstRule unit first second third
      hfirstEarlier hsecondAtFirst hfirstDecisive (hsecondEarlier firstRule hbefore)⟩
    intro earlier hearlier
    exact laws.eq_trans earlier unit first second third
      (prefixTie hfirstEarlier hearlier)
      (prefixTie hsecondEarlier (Nat.lt_trans hearlier hbefore))
      (hfirstEarlier earlier hearlier)
      (hsecondEarlier earlier (Nat.lt_trans hearlier hbefore))
  · have hrule : firstRule = secondRule := SequenceRule.rank_injective hequal
    subst secondRule
    refine ⟨firstRule, ?_, laws.gt_trans firstRule unit first second third
      hfirstEarlier hsecondEarlier hfirstDecisive hsecondDecisive⟩
    intro earlier hearlier
    exact laws.eq_trans earlier unit first second third
      (prefixTie hfirstEarlier hearlier) (prefixTie hsecondEarlier hearlier)
      (hfirstEarlier earlier hearlier) (hsecondEarlier earlier hearlier)
  · have hfirstAtSecond := prefixTie hfirstEarlier hafter
    refine ⟨secondRule, ?_, laws.eq_gt_trans secondRule unit first second third
      hfirstAtSecond hsecondEarlier (hfirstEarlier secondRule hafter) hsecondDecisive⟩
    intro earlier hearlier
    exact laws.eq_trans earlier unit first second third
      (prefixTie hfirstEarlier (Nat.lt_trans hearlier hafter))
      (prefixTie hsecondEarlier hearlier)
      (hfirstEarlier earlier (Nat.lt_trans hearlier hafter))
      (hsecondEarlier earlier hearlier)

theorem weakPriority_total (laws : ContextualRuleOutcomeOrderLaws problem descriptorMap)
    (unit : Unit) (left right : Fin 4) :
    problem.WeakPriority descriptorMap unit left right ∨
      problem.WeakPriority descriptorMap unit right left := by
  classical
  by_cases hall : ∀ rule,
      problem.RuleOutcome descriptorMap rule unit left right Ordering.eq
  · exact Or.inl (Or.inr hall)
  · push_neg at hall
    let decisiveRank : ℕ → Prop := fun rank =>
      ∃ rule, rule.rank = rank ∧
        ¬problem.RuleOutcome descriptorMap rule unit left right Ordering.eq
    have hexists : ∃ rank, decisiveRank rank := by
      rcases hall with ⟨rule, hrule⟩
      exact ⟨rule.rank, rule, rfl, hrule⟩
    let firstRank := Nat.find hexists
    rcases Nat.find_spec hexists with ⟨rule, hrank, hnotEq⟩
    have hearlier : problem.EarlierRulesTie descriptorMap rule unit left right := by
      intro earlier hbefore
      by_contra hnotEarlierEq
      have hwitness : decisiveRank earlier.rank := ⟨earlier, rfl, hnotEarlierEq⟩
      have hminimal : firstRank ≤ earlier.rank := Nat.find_min' hexists hwitness
      have : earlier.rank < firstRank := by
        simpa [SequenceRule.Before, firstRank, hrank] using hbefore
      exact (Nat.not_lt_of_ge hminimal) this
    rcases laws.total rule unit left right hearlier with ⟨outcome, houtcome⟩
    cases outcome with
    | lt =>
        have hrearlier : problem.EarlierRulesTie descriptorMap rule unit right left := by
          intro earlier hbefore
          exact laws.eq_symm earlier unit left right (prefixTie hearlier hbefore)
            (hearlier earlier hbefore)
        exact Or.inr (Or.inl ⟨rule, hrearlier,
          laws.reverse_lt rule unit left right hearlier houtcome⟩)
    | eq => exact (hnotEq houtcome).elim
    | gt => exact Or.inl (Or.inl ⟨rule, hearlier, houtcome⟩)

/-- Chemically contextual rule laws still imply the complete global total preorder. -/
theorem priorityIsTotalPreorder
    (laws : ContextualRuleOutcomeOrderLaws problem descriptorMap) :
    PriorityIsTotalPreorder problem descriptorMap := by
  refine ⟨?_, ?_, ?_⟩
  · intro unit ligand
    exact Or.inr (fun rule => laws.eq_refl rule unit ligand)
  · intro unit first second third hfirst hsecond
    rcases hfirst with hfirstHigher | hfirstTied
    · rcases hsecond with hsecondHigher | hsecondTied
      · exact Or.inl (laws.higher_trans hfirstHigher hsecondHigher)
      · exact Or.inl (laws.higher_tied_trans hfirstHigher hsecondTied)
    · rcases hsecond with hsecondHigher | hsecondTied
      · exact Or.inl (laws.tied_higher_trans hfirstTied hsecondHigher)
      · exact Or.inr (laws.tied_trans hfirstTied hsecondTied)
  · exact laws.weakPriority_total

end ContextualRuleOutcomeOrderLaws

/-! ## Opponent-independent complete rule keys -/

/-- A uniform carrier for independent rule keys.  Nested natural lists accommodate scalar
priorities, hierarchy readings, and the canonical list-of-readings Rule-4b signature without
requiring comparisons between keys belonging to different rules. -/
abbrev RuleKey := List (List ℕ)

/-- Descending comparison in any linear order, stated relationally. -/
inductive OrderedKeyOutcome {α : Type*} [LinearOrder α] (left right : α) : Ordering → Prop where
  | gt (h : right < left) : OrderedKeyOutcome left right Ordering.gt
  | lt (h : left < right) : OrderedKeyOutcome left right Ordering.lt
  | eq (h : left = right) : OrderedKeyOutcome left right Ordering.eq

namespace OrderedKeyOutcome

theorem functional {α : Type*} [LinearOrder α] {left right : α} {first second : Ordering}
    (hfirst : OrderedKeyOutcome left right first)
    (hsecond : OrderedKeyOutcome left right second) :
    first = second := by
  cases hfirst <;> cases hsecond
  all_goals try rfl
  all_goals simp_all [lt_asymm]

theorem total {α : Type*} [LinearOrder α] (left right : α) :
    ∃ outcome, OrderedKeyOutcome left right outcome := by
  rcases lt_trichotomy left right with h | h | h
  · exact ⟨Ordering.lt, .lt h⟩
  · exact ⟨Ordering.eq, .eq h⟩
  · exact ⟨Ordering.gt, .gt h⟩

theorem eq_refl {α : Type*} [LinearOrder α] (key : α) :
    OrderedKeyOutcome key key Ordering.eq :=
  .eq rfl

theorem eq_symm {α : Type*} [LinearOrder α] {left right : α}
    (h : OrderedKeyOutcome left right Ordering.eq) :
    OrderedKeyOutcome right left Ordering.eq := by
  cases h with
  | eq heq => exact .eq heq.symm

theorem eq_trans {α : Type*} [LinearOrder α] {first second third : α}
    (hfirst : OrderedKeyOutcome first second Ordering.eq)
    (hsecond : OrderedKeyOutcome second third Ordering.eq) :
    OrderedKeyOutcome first third Ordering.eq := by
  cases hfirst with
  | eq hfirst =>
      cases hsecond with
      | eq hsecond => exact .eq (hfirst.trans hsecond)

theorem gt_trans {α : Type*} [LinearOrder α] {first second third : α}
    (hfirst : OrderedKeyOutcome first second Ordering.gt)
    (hsecond : OrderedKeyOutcome second third Ordering.gt) :
    OrderedKeyOutcome first third Ordering.gt := by
  cases hfirst with
  | gt hfirst =>
      cases hsecond with
      | gt hsecond => exact .gt (hsecond.trans hfirst)

theorem gt_eq_trans {α : Type*} [LinearOrder α] {first second third : α}
    (hfirst : OrderedKeyOutcome first second Ordering.gt)
    (hsecond : OrderedKeyOutcome second third Ordering.eq) :
    OrderedKeyOutcome first third Ordering.gt := by
  cases hfirst with
  | gt hfirst =>
      cases hsecond with
      | eq hsecond => exact .gt (hsecond ▸ hfirst)

theorem eq_gt_trans {α : Type*} [LinearOrder α] {first second third : α}
    (hfirst : OrderedKeyOutcome first second Ordering.eq)
    (hsecond : OrderedKeyOutcome second third Ordering.gt) :
    OrderedKeyOutcome first third Ordering.gt := by
  cases hfirst with
  | eq hfirst =>
      cases hsecond with
      | gt hsecond => exact .gt (hfirst ▸ hsecond)

theorem reverse_lt {α : Type*} [LinearOrder α] {left right : α}
    (h : OrderedKeyOutcome left right Ordering.lt) :
    OrderedKeyOutcome right left Ordering.gt := by
  cases h with
  | lt hlt => exact .gt hlt

end OrderedKeyOutcome

/-- A complete opponent-independent semantic key model for all nine sequence rules.

`key unit rule ligand` is computed from one ligand only.  `characterizes` says that the declarative
rule judgment compares exactly those unary keys.  For Rule 6 this is the strong promotion-
independence condition needed by the global priority theorem: all admissible promotion routes must
induce the same unary key comparison. -/
structure CompleteRuleKeyModel {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
    (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit) where
  key : Unit → SequenceRule → Fin 4 → RuleKey
  characterizes : ∀ rule unit left right outcome,
    problem.RuleOutcome descriptorMap rule unit left right outcome ↔
      OrderedKeyOutcome (key unit rule left) (key unit rule right) outcome

/-- Opponent-independent keys for the eight ordinary slots, with Rule 6 intentionally excluded. -/
structure OrdinaryRuleKeyModel {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
    (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit) where
  key : Unit → SequenceRule → Fin 4 → RuleKey
  characterizes : ∀ rule, rule ≠ SequenceRule.rule6ReferencePromotion →
    ∀ unit left right outcome,
      problem.RuleOutcome descriptorMap rule unit left right outcome ↔
        OrderedKeyOutcome (key unit rule left) (key unit rule right) outcome

/-- The isolated Rule-6 unary promotion key obligation. -/
structure Rule6KeyModel {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
    (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit) where
  key : Unit → Fin 4 → RuleKey
  characterizes : ∀ unit left right outcome,
    problem.RuleOutcome descriptorMap SequenceRule.rule6ReferencePromotion
        unit left right outcome ↔
      OrderedKeyOutcome (key unit left) (key unit right) outcome

namespace CompleteRuleKeyModel

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
variable {problem : Problem Atom Unit} {descriptorMap : DescriptorMap Unit}

/-- Unary key semantics automatically supplies every local comparison law. -/
theorem ruleOutcomeOrderLaws
    (model : CompleteRuleKeyModel problem descriptorMap) :
    RuleOutcomeOrderLaws problem descriptorMap where
  functional := by
    intro rule unit left right first second hfirst hsecond
    exact OrderedKeyOutcome.functional
      ((model.characterizes rule unit left right first).1 hfirst)
      ((model.characterizes rule unit left right second).1 hsecond)
  total := by
    intro rule unit left right
    rcases OrderedKeyOutcome.total (model.key unit rule left) (model.key unit rule right) with
      ⟨outcome, houtcome⟩
    exact ⟨outcome, (model.characterizes rule unit left right outcome).2 houtcome⟩
  eq_refl := by
    intro rule unit ligand
    exact (model.characterizes rule unit ligand ligand Ordering.eq).2
      (OrderedKeyOutcome.eq_refl _)
  eq_symm := by
    intro rule unit left right h
    exact (model.characterizes rule unit right left Ordering.eq).2
      (OrderedKeyOutcome.eq_symm
        ((model.characterizes rule unit left right Ordering.eq).1 h))
  eq_trans := by
    intro rule unit first second third hfirst hsecond
    exact (model.characterizes rule unit first third Ordering.eq).2
      (OrderedKeyOutcome.eq_trans
        ((model.characterizes rule unit first second Ordering.eq).1 hfirst)
        ((model.characterizes rule unit second third Ordering.eq).1 hsecond))
  gt_trans := by
    intro rule unit first second third hfirst hsecond
    exact (model.characterizes rule unit first third Ordering.gt).2
      (OrderedKeyOutcome.gt_trans
        ((model.characterizes rule unit first second Ordering.gt).1 hfirst)
        ((model.characterizes rule unit second third Ordering.gt).1 hsecond))
  gt_eq_trans := by
    intro rule unit first second third hfirst hsecond
    exact (model.characterizes rule unit first third Ordering.gt).2
      (OrderedKeyOutcome.gt_eq_trans
        ((model.characterizes rule unit first second Ordering.gt).1 hfirst)
        ((model.characterizes rule unit second third Ordering.eq).1 hsecond))
  eq_gt_trans := by
    intro rule unit first second third hfirst hsecond
    exact (model.characterizes rule unit first third Ordering.gt).2
      (OrderedKeyOutcome.eq_gt_trans
        ((model.characterizes rule unit first second Ordering.eq).1 hfirst)
        ((model.characterizes rule unit second third Ordering.gt).1 hsecond))
  reverse_lt := by
    intro rule unit left right h
    exact (model.characterizes rule unit right left Ordering.gt).2
      (OrderedKeyOutcome.reverse_lt
        ((model.characterizes rule unit left right Ordering.lt).1 h))

/-- Main global result: a complete opponent-independent key interpretation of Rules 1a--6 makes
declarative ligand priority a total preorder. -/
theorem priorityIsTotalPreorder
    (model : CompleteRuleKeyModel problem descriptorMap) :
    PriorityIsTotalPreorder problem descriptorMap :=
  model.ruleOutcomeOrderLaws.priorityIsTotalPreorder

/-- Assemble the ordinary and promotion key obligations into one complete nine-slot model. -/
def ofOrdinaryAndRule6
    (ordinary : OrdinaryRuleKeyModel problem descriptorMap)
    (rule6 : Rule6KeyModel problem descriptorMap) :
    CompleteRuleKeyModel problem descriptorMap where
  key := fun unit rule ligand =>
    if rule = SequenceRule.rule6ReferencePromotion then
      rule6.key unit ligand
    else ordinary.key unit rule ligand
  characterizes := by
    intro rule unit left right outcome
    by_cases hrule : rule = SequenceRule.rule6ReferencePromotion
    · subst rule
      simpa using rule6.characterizes unit left right outcome
    · simpa [hrule] using ordinary.characterizes rule hrule unit left right outcome

/-- Split form of the global theorem: ordinary opponent-independent semantics plus one Rule-6
promotion key imply the complete priority total preorder. -/
theorem priorityIsTotalPreorder_of_ordinaryAndRule6
    (ordinary : OrdinaryRuleKeyModel problem descriptorMap)
    (rule6 : Rule6KeyModel problem descriptorMap) :
    PriorityIsTotalPreorder problem descriptorMap :=
  (ofOrdinaryAndRule6 ordinary rule6).priorityIsTotalPreorder

end CompleteRuleKeyModel

/-- Opponent-independent keys characterized only on the domain where a rule is semantically
eligible.  Reflexive ties are carried separately to bootstrap the first rule and every later tie
class without assuming eligibility in the characterization field. -/
structure ContextualCompleteRuleKeyModel
    {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
    (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit) where
  key : Unit → SequenceRule → Fin 4 → RuleKey
  characterizes : ∀ rule unit left right outcome,
    problem.EarlierRulesTie descriptorMap rule unit left right →
    (problem.RuleOutcome descriptorMap rule unit left right outcome ↔
      OrderedKeyOutcome (key unit rule left) (key unit rule right) outcome)
  eq_refl : ∀ rule unit ligand,
    problem.RuleOutcome descriptorMap rule unit ligand ligand Ordering.eq
  earlier_symm : ∀ rule unit left right,
    problem.EarlierRulesTie descriptorMap rule unit left right →
    problem.EarlierRulesTie descriptorMap rule unit right left
  earlier_trans : ∀ rule unit first second third,
    problem.EarlierRulesTie descriptorMap rule unit first second →
    problem.EarlierRulesTie descriptorMap rule unit second third →
    problem.EarlierRulesTie descriptorMap rule unit first third

namespace ContextualCompleteRuleKeyModel

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
variable {problem : Problem Atom Unit} {descriptorMap : DescriptorMap Unit}

theorem contextualRuleOutcomeOrderLaws
    (model : ContextualCompleteRuleKeyModel problem descriptorMap) :
    ContextualRuleOutcomeOrderLaws problem descriptorMap where
  functional := by
    intro rule unit left right first second hearlier hfirst hsecond
    exact OrderedKeyOutcome.functional
      ((model.characterizes rule unit left right first hearlier).1 hfirst)
      ((model.characterizes rule unit left right second hearlier).1 hsecond)
  total := by
    intro rule unit left right hearlier
    rcases OrderedKeyOutcome.total (model.key unit rule left) (model.key unit rule right) with
      ⟨outcome, houtcome⟩
    exact ⟨outcome, (model.characterizes rule unit left right outcome hearlier).2 houtcome⟩
  eq_refl := model.eq_refl
  eq_symm := by
    intro rule unit left right hearlier h
    exact (model.characterizes rule unit right left Ordering.eq
      (model.earlier_symm rule unit left right hearlier)).2
      (OrderedKeyOutcome.eq_symm
        ((model.characterizes rule unit left right Ordering.eq hearlier).1 h))
  eq_trans := by
    intro rule unit first second third hfirstEarlier hsecondEarlier hfirst hsecond
    exact (model.characterizes rule unit first third Ordering.eq
      (model.earlier_trans rule unit first second third hfirstEarlier hsecondEarlier)).2
      (OrderedKeyOutcome.eq_trans
        ((model.characterizes rule unit first second Ordering.eq hfirstEarlier).1 hfirst)
        ((model.characterizes rule unit second third Ordering.eq hsecondEarlier).1 hsecond))
  gt_trans := by
    intro rule unit first second third hfirstEarlier hsecondEarlier hfirst hsecond
    exact (model.characterizes rule unit first third Ordering.gt
      (model.earlier_trans rule unit first second third hfirstEarlier hsecondEarlier)).2
      (OrderedKeyOutcome.gt_trans
        ((model.characterizes rule unit first second Ordering.gt hfirstEarlier).1 hfirst)
        ((model.characterizes rule unit second third Ordering.gt hsecondEarlier).1 hsecond))
  gt_eq_trans := by
    intro rule unit first second third hfirstEarlier hsecondEarlier hfirst hsecond
    exact (model.characterizes rule unit first third Ordering.gt
      (model.earlier_trans rule unit first second third hfirstEarlier hsecondEarlier)).2
      (OrderedKeyOutcome.gt_eq_trans
        ((model.characterizes rule unit first second Ordering.gt hfirstEarlier).1 hfirst)
        ((model.characterizes rule unit second third Ordering.eq hsecondEarlier).1 hsecond))
  eq_gt_trans := by
    intro rule unit first second third hfirstEarlier hsecondEarlier hfirst hsecond
    exact (model.characterizes rule unit first third Ordering.gt
      (model.earlier_trans rule unit first second third hfirstEarlier hsecondEarlier)).2
      (OrderedKeyOutcome.eq_gt_trans
        ((model.characterizes rule unit first second Ordering.eq hfirstEarlier).1 hfirst)
        ((model.characterizes rule unit second third Ordering.gt hsecondEarlier).1 hsecond))
  reverse_lt := by
    intro rule unit left right hearlier h
    exact (model.characterizes rule unit right left Ordering.gt
      (model.earlier_symm rule unit left right hearlier)).2
      (OrderedKeyOutcome.reverse_lt
        ((model.characterizes rule unit left right Ordering.lt hearlier).1 h))

theorem priorityIsTotalPreorder
    (model : ContextualCompleteRuleKeyModel problem descriptorMap) :
    PriorityIsTotalPreorder problem descriptorMap :=
  model.contextualRuleOutcomeOrderLaws.priorityIsTotalPreorder

end ContextualCompleteRuleKeyModel

namespace StereochemicalProblemData

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]

/-- The unified independent Rules-1a--5 problem satisfies the global preorder theorem as soon as
its rule observations—including the explicitly separate Rule-6 promotion—are represented by
complete opponent-independent unary keys. -/
theorem priorityIsTotalPreorder_of_completeRuleKeyModel
    (data : StereochemicalProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit)
    (model : CompleteRuleKeyModel data.toProblem descriptorMap) :
    PriorityIsTotalPreorder data.toProblem descriptorMap :=
  model.priorityIsTotalPreorder

/-- Explicit boundary theorem for the combined independent problem: keys for Rules 1a--5 and a
separate, promotion-independent Rule-6 key suffice for the full global preorder. -/
theorem priorityIsTotalPreorder_of_ordinaryAndRule6Keys
    (data : StereochemicalProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit)
    (ordinary : OrdinaryRuleKeyModel data.toProblem descriptorMap)
    (rule6 : Rule6KeyModel data.toProblem descriptorMap) :
    PriorityIsTotalPreorder data.toProblem descriptorMap :=
  CompleteRuleKeyModel.priorityIsTotalPreorder_of_ordinaryAndRule6 ordinary rule6

end StereochemicalProblemData

/-! ## A proof-carrying coherent declarative problem -/

/-- Independent Rules-1a--6 data carrying the semantic coherence needed by the mathematical
program.

This structure does not contain an executable sorting procedure.  It contains unary semantic keys
and propositions identifying the relational rule judgments with comparisons of those keys.  Rule
6 additionally carries the stronger graph-level agreement theorem for all admissible promotion
references. -/
structure CoherentProblemData (Atom Unit : Type u)
    [Fintype Atom] [DecidableEq Atom]
    extends StereochemicalProblemData Atom Unit where
  ordinaryKey : DescriptorMap Unit → Unit → SequenceRule → Fin 4 → RuleKey
  ordinaryKey_characterizes :
    ∀ descriptorMap rule, rule ≠ SequenceRule.rule6ReferencePromotion →
      ∀ unit left right outcome,
        toStereochemicalProblemData.toProblem.RuleOutcome
            descriptorMap rule unit left right outcome ↔
          OrderedKeyOutcome (ordinaryKey descriptorMap unit rule left)
            (ordinaryKey descriptorMap unit rule right) outcome
  rule6Key : DescriptorMap Unit → Unit → Fin 4 → RuleKey
  rule6Key_characterizes :
    ∀ descriptorMap unit left right outcome,
      toStereochemicalProblemData.toProblem.RuleOutcome descriptorMap
          SequenceRule.rule6ReferencePromotion unit left right outcome ↔
        OrderedKeyOutcome (rule6Key descriptorMap unit left)
          (rule6Key descriptorMap unit right) outcome
  rule6_promotion_independent :
    Rule6PromotionIndependent toStereochemicalProblemData.toProblem

namespace CoherentProblemData

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]

def ordinaryRuleKeyModel (data : CoherentProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit) :
    OrdinaryRuleKeyModel data.toStereochemicalProblemData.toProblem descriptorMap where
  key := data.ordinaryKey descriptorMap
  characterizes := data.ordinaryKey_characterizes descriptorMap

def rule6KeyModel (data : CoherentProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit) :
    Rule6KeyModel data.toStereochemicalProblemData.toProblem descriptorMap where
  key := data.rule6Key descriptorMap
  characterizes := data.rule6Key_characterizes descriptorMap

def completeRuleKeyModel (data : CoherentProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit) :
    CompleteRuleKeyModel data.toStereochemicalProblemData.toProblem descriptorMap :=
  CompleteRuleKeyModel.ofOrdinaryAndRule6
    (data.ordinaryRuleKeyModel descriptorMap) (data.rule6KeyModel descriptorMap)

/-- Global result for coherent independent semantics: at every descriptor map and unit, complete
Rules-1a--6 ligand priority is reflexive, transitive, and total. -/
theorem priorityIsTotalPreorder (data : CoherentProblemData Atom Unit)
    (descriptorMap : DescriptorMap Unit) :
    PriorityIsTotalPreorder data.toStereochemicalProblemData.toProblem descriptorMap :=
  (data.completeRuleKeyModel descriptorMap).priorityIsTotalPreorder

/-- In a satisfying global `CIPSpec`, every rule outcome is single-valued as well as the complete
priority being a total preorder. -/
theorem ruleOutcome_functional_of_spec
    (data : CoherentProblemData Atom Unit)
    {descriptorMap : DescriptorMap Unit}
    (spec : CIPSpec data.toStereochemicalProblemData.toProblem descriptorMap)
    (rule : SequenceRule) (unit : Unit) (left right : Fin 4)
    {first second : Ordering}
    (hfirst : data.toStereochemicalProblemData.toProblem.RuleOutcome
      descriptorMap rule unit left right first)
    (hsecond : data.toStereochemicalProblemData.toProblem.RuleOutcome
      descriptorMap rule unit left right second) :
    first = second :=
  data.toStereochemicalProblemData.ruleOutcome_functional_of_spec
    data.rule6_promotion_independent spec rule unit left right hfirst hsecond

end CoherentProblemData

end
end DeclarativeCIP
end OneCenter
end TetraStereo
