import TetraStereo.OneCenter.DeclarativeCIPCarrier

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section

universe u

/-!
# Contextual ordinary priority coherence

Later ordinary rules need order laws only inside the tie class left by earlier rules.  This module
proves the Rules-1a--5 total preorder from exactly that premise, with no Rule-6 comparison law.
-/

/-- Chemically contextual comparison laws, restricted to ordinary Rules 1a--5. -/
structure OrdinaryContextualRuleOutcomeOrderLaws
    {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
    (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit) : Prop where
  functional : ∀ rule, rule.Ordinary → ∀ unit left right first second,
    problem.EarlierRulesTie descriptorMap rule unit left right →
    problem.RuleOutcome descriptorMap rule unit left right first →
    problem.RuleOutcome descriptorMap rule unit left right second → first = second
  total : ∀ rule, rule.Ordinary → ∀ unit left right,
    problem.EarlierRulesTie descriptorMap rule unit left right →
    ∃ outcome, problem.RuleOutcome descriptorMap rule unit left right outcome
  eq_refl : ∀ rule, rule.Ordinary → ∀ unit ligand,
    problem.RuleOutcome descriptorMap rule unit ligand ligand Ordering.eq
  eq_symm : ∀ rule, rule.Ordinary → ∀ unit left right,
    problem.EarlierRulesTie descriptorMap rule unit left right →
    problem.RuleOutcome descriptorMap rule unit left right Ordering.eq →
    problem.RuleOutcome descriptorMap rule unit right left Ordering.eq
  eq_trans : ∀ rule, rule.Ordinary → ∀ unit first second third,
    problem.EarlierRulesTie descriptorMap rule unit first second →
    problem.EarlierRulesTie descriptorMap rule unit second third →
    problem.RuleOutcome descriptorMap rule unit first second Ordering.eq →
    problem.RuleOutcome descriptorMap rule unit second third Ordering.eq →
    problem.RuleOutcome descriptorMap rule unit first third Ordering.eq
  gt_trans : ∀ rule, rule.Ordinary → ∀ unit first second third,
    problem.EarlierRulesTie descriptorMap rule unit first second →
    problem.EarlierRulesTie descriptorMap rule unit second third →
    problem.RuleOutcome descriptorMap rule unit first second Ordering.gt →
    problem.RuleOutcome descriptorMap rule unit second third Ordering.gt →
    problem.RuleOutcome descriptorMap rule unit first third Ordering.gt
  gt_eq_trans : ∀ rule, rule.Ordinary → ∀ unit first second third,
    problem.EarlierRulesTie descriptorMap rule unit first second →
    problem.EarlierRulesTie descriptorMap rule unit second third →
    problem.RuleOutcome descriptorMap rule unit first second Ordering.gt →
    problem.RuleOutcome descriptorMap rule unit second third Ordering.eq →
    problem.RuleOutcome descriptorMap rule unit first third Ordering.gt
  eq_gt_trans : ∀ rule, rule.Ordinary → ∀ unit first second third,
    problem.EarlierRulesTie descriptorMap rule unit first second →
    problem.EarlierRulesTie descriptorMap rule unit second third →
    problem.RuleOutcome descriptorMap rule unit first second Ordering.eq →
    problem.RuleOutcome descriptorMap rule unit second third Ordering.gt →
    problem.RuleOutcome descriptorMap rule unit first third Ordering.gt
  reverse_lt : ∀ rule, rule.Ordinary → ∀ unit left right,
    problem.EarlierRulesTie descriptorMap rule unit left right →
    problem.RuleOutcome descriptorMap rule unit left right Ordering.lt →
    problem.RuleOutcome descriptorMap rule unit right left Ordering.gt

namespace OrdinaryContextualRuleOutcomeOrderLaws

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
variable {problem : Problem Atom Unit} {descriptorMap : DescriptorMap Unit}

private theorem prefixTie {rule : SequenceRule} {unit : Unit} {left right : Fin 4}
    (h : problem.EarlierRulesTie descriptorMap rule unit left right)
    {earlier : SequenceRule} (hearlier : earlier.Before rule) :
    problem.EarlierRulesTie descriptorMap earlier unit left right :=
  fun prior hprior => h prior (hprior.trans hearlier)

private theorem tiedPrefix {rule : SequenceRule} (hrule : rule.Ordinary)
    {unit : Unit} {left right : Fin 4}
    (h : problem.OrdinaryTied descriptorMap unit left right) :
    problem.EarlierRulesTie descriptorMap rule unit left right := by
  intro earlier hbefore
  exact h earlier (SequenceRule.ordinary_of_before_of_ordinary hbefore hrule)

theorem tied_trans (laws : OrdinaryContextualRuleOutcomeOrderLaws problem descriptorMap)
    {unit : Unit} {first second third : Fin 4}
    (hfirst : problem.OrdinaryTied descriptorMap unit first second)
    (hsecond : problem.OrdinaryTied descriptorMap unit second third) :
    problem.OrdinaryTied descriptorMap unit first third := by
  intro rule hordinary
  exact laws.eq_trans rule hordinary unit first second third
    (tiedPrefix hordinary hfirst) (tiedPrefix hordinary hsecond)
    (hfirst rule hordinary) (hsecond rule hordinary)

theorem higher_tied_trans (laws : OrdinaryContextualRuleOutcomeOrderLaws problem descriptorMap)
    {unit : Unit} {first second third : Fin 4}
    (hfirst : problem.OrdinaryHigher descriptorMap unit first second)
    (hsecond : problem.OrdinaryTied descriptorMap unit second third) :
    problem.OrdinaryHigher descriptorMap unit first third := by
  rcases hfirst with ⟨rule, hordinary, hearlier, hdecisive⟩
  refine ⟨rule, hordinary, ?_, laws.gt_eq_trans rule hordinary unit first second third
    hearlier (tiedPrefix hordinary hsecond) hdecisive (hsecond rule hordinary)⟩
  intro earlier hbefore
  have hearlierOrdinary := SequenceRule.ordinary_of_before_of_ordinary hbefore hordinary
  exact laws.eq_trans earlier hearlierOrdinary unit first second third
    (prefixTie hearlier hbefore) (tiedPrefix hearlierOrdinary hsecond)
    (hearlier earlier hbefore) (hsecond earlier hearlierOrdinary)

theorem tied_higher_trans (laws : OrdinaryContextualRuleOutcomeOrderLaws problem descriptorMap)
    {unit : Unit} {first second third : Fin 4}
    (hfirst : problem.OrdinaryTied descriptorMap unit first second)
    (hsecond : problem.OrdinaryHigher descriptorMap unit second third) :
    problem.OrdinaryHigher descriptorMap unit first third := by
  rcases hsecond with ⟨rule, hordinary, hearlier, hdecisive⟩
  refine ⟨rule, hordinary, ?_, laws.eq_gt_trans rule hordinary unit first second third
    (tiedPrefix hordinary hfirst) hearlier (hfirst rule hordinary) hdecisive⟩
  intro earlier hbefore
  have hearlierOrdinary := SequenceRule.ordinary_of_before_of_ordinary hbefore hordinary
  exact laws.eq_trans earlier hearlierOrdinary unit first second third
    (tiedPrefix hearlierOrdinary hfirst) (prefixTie hearlier hbefore)
    (hfirst earlier hearlierOrdinary) (hearlier earlier hbefore)

theorem higher_trans (laws : OrdinaryContextualRuleOutcomeOrderLaws problem descriptorMap)
    {unit : Unit} {first second third : Fin 4}
    (hfirst : problem.OrdinaryHigher descriptorMap unit first second)
    (hsecond : problem.OrdinaryHigher descriptorMap unit second third) :
    problem.OrdinaryHigher descriptorMap unit first third := by
  rcases hfirst with ⟨firstRule, hfirstOrdinary, hfirstEarlier, hfirstDecisive⟩
  rcases hsecond with ⟨secondRule, hsecondOrdinary, hsecondEarlier, hsecondDecisive⟩
  rcases lt_trichotomy firstRule.rank secondRule.rank with hbefore | hequal | hafter
  · have hsecondAtFirst := prefixTie hsecondEarlier hbefore
    refine ⟨firstRule, hfirstOrdinary, ?_,
      laws.gt_eq_trans firstRule hfirstOrdinary unit first second third
        hfirstEarlier hsecondAtFirst hfirstDecisive (hsecondEarlier firstRule hbefore)⟩
    intro earlier hearlier
    have hordinary := SequenceRule.ordinary_of_before_of_ordinary hearlier hfirstOrdinary
    exact laws.eq_trans earlier hordinary unit first second third
      (prefixTie hfirstEarlier hearlier)
      (prefixTie hsecondEarlier (Nat.lt_trans hearlier hbefore))
      (hfirstEarlier earlier hearlier)
      (hsecondEarlier earlier (Nat.lt_trans hearlier hbefore))
  · have hrule : firstRule = secondRule := SequenceRule.rank_injective hequal
    subst secondRule
    refine ⟨firstRule, hfirstOrdinary, ?_,
      laws.gt_trans firstRule hfirstOrdinary unit first second third
        hfirstEarlier hsecondEarlier hfirstDecisive hsecondDecisive⟩
    intro earlier hearlier
    have hordinary := SequenceRule.ordinary_of_before_of_ordinary hearlier hfirstOrdinary
    exact laws.eq_trans earlier hordinary unit first second third
      (prefixTie hfirstEarlier hearlier) (prefixTie hsecondEarlier hearlier)
      (hfirstEarlier earlier hearlier) (hsecondEarlier earlier hearlier)
  · have hfirstAtSecond := prefixTie hfirstEarlier hafter
    refine ⟨secondRule, hsecondOrdinary, ?_,
      laws.eq_gt_trans secondRule hsecondOrdinary unit first second third
        hfirstAtSecond hsecondEarlier (hfirstEarlier secondRule hafter) hsecondDecisive⟩
    intro earlier hearlier
    have hordinary := SequenceRule.ordinary_of_before_of_ordinary hearlier hsecondOrdinary
    exact laws.eq_trans earlier hordinary unit first second third
      (prefixTie hfirstEarlier (Nat.lt_trans hearlier hafter))
      (prefixTie hsecondEarlier hearlier)
      (hfirstEarlier earlier (Nat.lt_trans hearlier hafter))
      (hsecondEarlier earlier hearlier)

theorem higher_irrefl (laws : OrdinaryContextualRuleOutcomeOrderLaws problem descriptorMap)
    (unit : Unit) (ligand : Fin 4) :
    ¬problem.OrdinaryHigher descriptorMap unit ligand ligand := by
  rintro ⟨rule, hordinary, hearlier, hdecisive⟩
  have hfunctional := laws.functional rule hordinary unit ligand ligand
    Ordering.gt Ordering.eq hearlier hdecisive
    (laws.eq_refl rule hordinary unit ligand)
  cases hfunctional

theorem higher_asymmetric
    (laws : OrdinaryContextualRuleOutcomeOrderLaws problem descriptorMap) :
    problem.OrdinaryHigherAsymmetric descriptorMap := by
  intro unit left right hleft hright
  exact laws.higher_irrefl unit left (laws.higher_trans hleft hright)

theorem weakPriority_total (laws : OrdinaryContextualRuleOutcomeOrderLaws problem descriptorMap)
    (unit : Unit) (left right : Fin 4) :
    problem.OrdinaryWeakPriority descriptorMap unit left right ∨
      problem.OrdinaryWeakPriority descriptorMap unit right left := by
  classical
  by_cases hall : ∀ rule, rule.Ordinary →
      problem.RuleOutcome descriptorMap rule unit left right Ordering.eq
  · exact Or.inl (Or.inr hall)
  · push_neg at hall
    let decisiveRank : ℕ → Prop := fun rank =>
      ∃ rule, rule.Ordinary ∧ rule.rank = rank ∧
        ¬problem.RuleOutcome descriptorMap rule unit left right Ordering.eq
    have hexists : ∃ rank, decisiveRank rank := by
      rcases hall with ⟨rule, hordinary, hrule⟩
      exact ⟨rule.rank, rule, hordinary, rfl, hrule⟩
    let firstRank := Nat.find hexists
    rcases Nat.find_spec hexists with ⟨rule, hordinary, hrank, hnotEq⟩
    have hearlier : problem.EarlierRulesTie descriptorMap rule unit left right := by
      intro earlier hbefore
      by_contra hnotEarlierEq
      have hearlierOrdinary :=
        SequenceRule.ordinary_of_before_of_ordinary hbefore hordinary
      have hwitness : decisiveRank earlier.rank :=
        ⟨earlier, hearlierOrdinary, rfl, hnotEarlierEq⟩
      have hminimal : firstRank ≤ earlier.rank := Nat.find_min' hexists hwitness
      have : earlier.rank < firstRank := by
        simpa [SequenceRule.Before, firstRank, hrank] using hbefore
      exact (Nat.not_lt_of_ge hminimal) this
    rcases laws.total rule hordinary unit left right hearlier with ⟨outcome, houtcome⟩
    cases outcome with
    | lt =>
        have hrearlier : problem.EarlierRulesTie descriptorMap rule unit right left := by
          intro earlier hbefore
          have hearlierOrdinary :=
            SequenceRule.ordinary_of_before_of_ordinary hbefore hordinary
          exact laws.eq_symm earlier hearlierOrdinary unit left right
            (prefixTie hearlier hbefore) (hearlier earlier hbefore)
        exact Or.inr (Or.inl ⟨rule, hordinary, hrearlier,
          laws.reverse_lt rule hordinary unit left right hearlier houtcome⟩)
    | eq => exact (hnotEq houtcome).elim
    | gt => exact Or.inl (Or.inl ⟨rule, hordinary, hearlier, houtcome⟩)

theorem ordinaryPriorityIsTotalPreorder
    (laws : OrdinaryContextualRuleOutcomeOrderLaws problem descriptorMap) :
    problem.OrdinaryPriorityIsTotalPreorder descriptorMap := by
  refine ⟨?_, ?_, ?_⟩
  · intro unit ligand
    exact Or.inr (fun rule hordinary => laws.eq_refl rule hordinary unit ligand)
  · intro unit first second third hfirst hsecond
    rcases hfirst with hfirstHigher | hfirstTied
    · rcases hsecond with hsecondHigher | hsecondTied
      · exact Or.inl (laws.higher_trans hfirstHigher hsecondHigher)
      · exact Or.inl (laws.higher_tied_trans hfirstHigher hsecondTied)
    · rcases hsecond with hsecondHigher | hsecondTied
      · exact Or.inl (laws.tied_higher_trans hfirstTied hsecondHigher)
      · exact Or.inr (laws.tied_trans hfirstTied hsecondTied)
  · exact laws.weakPriority_total

end OrdinaryContextualRuleOutcomeOrderLaws

/-! ## Contextual unary-key discharge -/

/-- Opponent-independent ordinary keys characterized only inside each earlier-rule tie class. -/
structure OrdinaryContextualRuleKeyModel
    {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
    (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit) where
  key : Unit → SequenceRule → Fin 4 → RuleKey
  characterizes : ∀ rule, rule.Ordinary → ∀ unit left right outcome,
    problem.EarlierRulesTie descriptorMap rule unit left right →
    (problem.RuleOutcome descriptorMap rule unit left right outcome ↔
      OrderedKeyOutcome (key unit rule left) (key unit rule right) outcome)
  eq_refl : ∀ rule, rule.Ordinary → ∀ unit ligand,
    problem.RuleOutcome descriptorMap rule unit ligand ligand Ordering.eq
  earlier_symm : ∀ rule, rule.Ordinary → ∀ unit left right,
    problem.EarlierRulesTie descriptorMap rule unit left right →
    problem.EarlierRulesTie descriptorMap rule unit right left
  earlier_trans : ∀ rule, rule.Ordinary → ∀ unit first second third,
    problem.EarlierRulesTie descriptorMap rule unit first second →
    problem.EarlierRulesTie descriptorMap rule unit second third →
    problem.EarlierRulesTie descriptorMap rule unit first third

namespace OrdinaryContextualRuleKeyModel

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
variable {problem : Problem Atom Unit} {descriptorMap : DescriptorMap Unit}

theorem orderLaws (model : OrdinaryContextualRuleKeyModel problem descriptorMap) :
    OrdinaryContextualRuleOutcomeOrderLaws problem descriptorMap where
  functional := by
    intro rule hordinary unit left right first second hearlier hfirst hsecond
    exact OrderedKeyOutcome.functional
      ((model.characterizes rule hordinary unit left right first hearlier).1 hfirst)
      ((model.characterizes rule hordinary unit left right second hearlier).1 hsecond)
  total := by
    intro rule hordinary unit left right hearlier
    rcases OrderedKeyOutcome.total (model.key unit rule left) (model.key unit rule right) with
      ⟨outcome, houtcome⟩
    exact ⟨outcome,
      (model.characterizes rule hordinary unit left right outcome hearlier).2 houtcome⟩
  eq_refl := model.eq_refl
  eq_symm := by
    intro rule hordinary unit left right hearlier h
    exact (model.characterizes rule hordinary unit right left Ordering.eq
      (model.earlier_symm rule hordinary unit left right hearlier)).2
      (OrderedKeyOutcome.eq_symm
        ((model.characterizes rule hordinary unit left right Ordering.eq hearlier).1 h))
  eq_trans := by
    intro rule hordinary unit first second third hfirstEarlier hsecondEarlier hfirst hsecond
    exact (model.characterizes rule hordinary unit first third Ordering.eq
      (model.earlier_trans rule hordinary unit first second third
        hfirstEarlier hsecondEarlier)).2
      (OrderedKeyOutcome.eq_trans
        ((model.characterizes rule hordinary unit first second Ordering.eq hfirstEarlier).1 hfirst)
        ((model.characterizes rule hordinary unit second third Ordering.eq hsecondEarlier).1 hsecond))
  gt_trans := by
    intro rule hordinary unit first second third hfirstEarlier hsecondEarlier hfirst hsecond
    exact (model.characterizes rule hordinary unit first third Ordering.gt
      (model.earlier_trans rule hordinary unit first second third
        hfirstEarlier hsecondEarlier)).2
      (OrderedKeyOutcome.gt_trans
        ((model.characterizes rule hordinary unit first second Ordering.gt hfirstEarlier).1 hfirst)
        ((model.characterizes rule hordinary unit second third Ordering.gt hsecondEarlier).1 hsecond))
  gt_eq_trans := by
    intro rule hordinary unit first second third hfirstEarlier hsecondEarlier hfirst hsecond
    exact (model.characterizes rule hordinary unit first third Ordering.gt
      (model.earlier_trans rule hordinary unit first second third
        hfirstEarlier hsecondEarlier)).2
      (OrderedKeyOutcome.gt_eq_trans
        ((model.characterizes rule hordinary unit first second Ordering.gt hfirstEarlier).1 hfirst)
        ((model.characterizes rule hordinary unit second third Ordering.eq hsecondEarlier).1 hsecond))
  eq_gt_trans := by
    intro rule hordinary unit first second third hfirstEarlier hsecondEarlier hfirst hsecond
    exact (model.characterizes rule hordinary unit first third Ordering.gt
      (model.earlier_trans rule hordinary unit first second third
        hfirstEarlier hsecondEarlier)).2
      (OrderedKeyOutcome.eq_gt_trans
        ((model.characterizes rule hordinary unit first second Ordering.eq hfirstEarlier).1 hfirst)
        ((model.characterizes rule hordinary unit second third Ordering.gt hsecondEarlier).1 hsecond))
  reverse_lt := by
    intro rule hordinary unit left right hearlier h
    exact (model.characterizes rule hordinary unit right left Ordering.gt
      (model.earlier_symm rule hordinary unit left right hearlier)).2
      (OrderedKeyOutcome.reverse_lt
        ((model.characterizes rule hordinary unit left right Ordering.lt hearlier).1 h))

/-- Contextual opponent-independent keys prove the ordinary total preorder, independently of all
Rule-6 carrier behavior. -/
theorem ordinaryPriorityIsTotalPreorder
    (model : OrdinaryContextualRuleKeyModel problem descriptorMap) :
    problem.OrdinaryPriorityIsTotalPreorder descriptorMap :=
  model.orderLaws.ordinaryPriorityIsTotalPreorder

theorem ordinaryDescriptorJudgment_unique
    (model : OrdinaryContextualRuleKeyModel problem descriptorMap)
    (orientationFunctional : problem.OrientationJudgmentFunctional)
    (unit : Unit) {first second : Descriptor}
    (hfirst : problem.OrdinaryDescriptorJudgment descriptorMap unit first)
    (hsecond : problem.OrdinaryDescriptorJudgment descriptorMap unit second) :
    first = second :=
  problem.ordinaryDescriptorJudgment_unique descriptorMap
    model.orderLaws.higher_asymmetric orientationFunctional unit hfirst hsecond

end OrdinaryContextualRuleKeyModel

/-! ## Projection from the earlier combined interface -/

namespace ContextualOrdinaryKeyedRule6PromotionSemantics

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]

/-- Forget the former comparison-level Rule-6 key and retain exactly the contextual ordinary key
model.  Thus ordinary priority no longer depends on the stronger Rule-6 promotion assumption. -/
def ordinaryContextualRuleKeyModel
    (data : ContextualOrdinaryKeyedRule6PromotionSemantics Atom Unit)
    (descriptorMap : DescriptorMap Unit) :
    OrdinaryContextualRuleKeyModel
      data.toRule6PromotionSemantics.toStereochemicalProblemData.toProblem descriptorMap where
  key := data.ordinaryKey descriptorMap
  characterizes := by
    intro rule hordinary unit left right outcome hearlier
    exact data.ordinaryKey_characterizes descriptorMap rule hordinary
      unit left right outcome hearlier
  eq_refl := by
    intro rule hordinary unit ligand
    exact data.ordinary_eq_refl descriptorMap rule hordinary unit ligand
  earlier_symm := by
    intro rule _ unit left right hearlier
    exact data.earlier_symm descriptorMap rule unit left right hearlier
  earlier_trans := by
    intro rule _ unit first second third hfirst hsecond
    exact data.earlier_trans descriptorMap rule unit first second third hfirst hsecond

/-- Rules 1a--5 of the former combined semantics satisfy the corrected ordinary total-preorder
theorem without consulting any Rule-6 comparison key. -/
theorem ordinaryPriorityIsTotalPreorder
    (data : ContextualOrdinaryKeyedRule6PromotionSemantics Atom Unit)
    (descriptorMap : DescriptorMap Unit) :
    data.toRule6PromotionSemantics.toStereochemicalProblemData.toProblem
      |>.OrdinaryPriorityIsTotalPreorder descriptorMap :=
  (data.ordinaryContextualRuleKeyModel descriptorMap).ordinaryPriorityIsTotalPreorder

end ContextualOrdinaryKeyedRule6PromotionSemantics

end
end DeclarativeCIP
end OneCenter
end TetraStereo
