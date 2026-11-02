import TetraStereo.OneCenter.DeclarativeCIPRule6

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section

universe u v

/-!
# Ordinary priority and Rule-6 carrier descriptors

Rules 1a--5 establish the ordinary ligand preorder.  Rule 6 is not forced into that pairwise
relation: it acts on an eligible residual tie class and is accepted only when every admissible
promotion carrier licenses one common final descriptor.  This captures both the equivalent-
reference path and the four-way S4 parity quotient.
-/

namespace SequenceRule

/-- The ordinary revised-CIP rules, excluding proposed carrier promotion Rule 6. -/
def Ordinary (rule : SequenceRule) : Prop :=
  rule ≠ SequenceRule.rule6ReferencePromotion

theorem before_rule6_of_ordinary (rule : SequenceRule) (h : rule.Ordinary) :
    rule.Before SequenceRule.rule6ReferencePromotion := by
  cases rule <;> simp_all [Ordinary, Before, rank]

theorem ordinary_of_before_of_ordinary {earlier later : SequenceRule}
    (hbefore : earlier.Before later) (hlater : later.Ordinary) : earlier.Ordinary := by
  cases earlier <;> cases later <;> simp_all [Ordinary, Before, rank]

end SequenceRule

namespace Problem

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]

/-- Strict priority decided by an ordinary Rule 1a--5 slot. -/
def OrdinaryHigher (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit)
    (unit : Unit) (left right : Fin 4) : Prop :=
  ∃ rule,
    rule.Ordinary ∧
    problem.EarlierRulesTie descriptorMap rule unit left right ∧
    problem.RuleOutcome descriptorMap rule unit left right Ordering.gt

/-- An ordinary tie: every Rules-1a--5 slot ties. -/
def OrdinaryTied (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit)
    (unit : Unit) (left right : Fin 4) : Prop :=
  ∀ rule, rule.Ordinary →
    problem.RuleOutcome descriptorMap rule unit left right Ordering.eq

def OrdinaryWeakPriority (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit)
    (unit : Unit) (left right : Fin 4) : Prop :=
  problem.OrdinaryHigher descriptorMap unit left right ∨
    problem.OrdinaryTied descriptorMap unit left right

/-- A strict complete ligand ranking established without Rule 6. -/
def OrdinaryRanks (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit)
    (unit : Unit) (ranking : Equiv.Perm (Fin 4)) : Prop :=
  ∀ i j : Fin 4, i < j →
    problem.OrdinaryHigher descriptorMap unit (ranking i) (ranking j)

def OrdinaryDescriptorJudgment (problem : Problem Atom Unit)
    (descriptorMap : DescriptorMap Unit) (unit : Unit) (descriptor : Descriptor) : Prop :=
  ∃ ranking : Equiv.Perm (Fin 4),
    problem.OrdinaryRanks descriptorMap unit ranking ∧
    problem.orientationJudgment unit ranking descriptor

def OrdinaryHigherAsymmetric (problem : Problem Atom Unit)
    (descriptorMap : DescriptorMap Unit) : Prop :=
  ∀ unit left right,
    problem.OrdinaryHigher descriptorMap unit left right →
    ¬problem.OrdinaryHigher descriptorMap unit right left

def OrientationJudgmentFunctional (problem : Problem Atom Unit) : Prop :=
  ∀ unit ranking first second,
    problem.orientationJudgment unit ranking first →
    problem.orientationJudgment unit ranking second → first = second

/-- A strict ranking of all four ligand positions is unique once strict ordinary priority is
asymmetric. -/
theorem ordinaryRanks_unique (problem : Problem Atom Unit)
    (descriptorMap : DescriptorMap Unit)
    (asymmetric : problem.OrdinaryHigherAsymmetric descriptorMap)
    (unit : Unit) {first second : Equiv.Perm (Fin 4)}
    (hfirst : problem.OrdinaryRanks descriptorMap unit first)
    (hsecond : problem.OrdinaryRanks descriptorMap unit second) :
    first = second := by
  let reindex : Equiv.Perm (Fin 4) := first.trans second.symm
  have hmono : StrictMono reindex := by
    intro i j hij
    by_contra hnot
    have hle : reindex j ≤ reindex i := le_of_not_gt hnot
    have hne : reindex j ≠ reindex i := by
      intro heq
      have : i = j := reindex.injective heq.symm
      exact (ne_of_lt hij) this
    have hji : reindex j < reindex i := lt_of_le_of_ne hle hne
    have hforward := hfirst i j hij
    have hreverse := hsecond (reindex j) (reindex i) hji
    have hreverse' :
        problem.OrdinaryHigher descriptorMap unit (first j) (first i) := by
      simpa [reindex] using hreverse
    exact asymmetric unit (first i) (first j) hforward hreverse'
  apply Equiv.ext
  intro i
  have hreindex : reindex i = i :=
    le_antisymm (hmono.le_id i) (hmono.id_le i)
  have := congrArg second hreindex
  simpa [reindex] using this

theorem ordinaryDescriptorJudgment_unique
    (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit)
    (asymmetric : problem.OrdinaryHigherAsymmetric descriptorMap)
    (orientationFunctional : problem.OrientationJudgmentFunctional)
    (unit : Unit) {first second : Descriptor}
    (hfirst : problem.OrdinaryDescriptorJudgment descriptorMap unit first)
    (hsecond : problem.OrdinaryDescriptorJudgment descriptorMap unit second) :
    first = second := by
  rcases hfirst with ⟨firstRanking, hfirstRanks, hfirstOrientation⟩
  rcases hsecond with ⟨secondRanking, hsecondRanks, hsecondOrientation⟩
  have hranking := problem.ordinaryRanks_unique descriptorMap asymmetric unit
    hfirstRanks hsecondRanks
  subst secondRanking
  exact orientationFunctional unit firstRanking first second
    hfirstOrientation hsecondOrientation

/-- The ordinary weak-priority relation is a total preorder. -/
def OrdinaryPriorityIsTotalPreorder (problem : Problem Atom Unit)
    (descriptorMap : DescriptorMap Unit) : Prop :=
  (∀ unit ligand, problem.OrdinaryWeakPriority descriptorMap unit ligand ligand) ∧
  (∀ unit first second third,
    problem.OrdinaryWeakPriority descriptorMap unit first second →
    problem.OrdinaryWeakPriority descriptorMap unit second third →
    problem.OrdinaryWeakPriority descriptorMap unit first third) ∧
  (∀ unit left right,
    problem.OrdinaryWeakPriority descriptorMap unit left right ∨
    problem.OrdinaryWeakPriority descriptorMap unit right left)

theorem ordinaryTied_iff_earlierRulesTie_rule6
    (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit)
    (unit : Unit) (left right : Fin 4) :
    problem.OrdinaryTied descriptorMap unit left right ↔
      problem.EarlierRulesTie descriptorMap SequenceRule.rule6ReferencePromotion
        unit left right := by
  constructor
  · intro h rule hbefore
    exact h rule (by
      intro hrule
      subst rule
      simp [SequenceRule.Before, SequenceRule.rank] at hbefore)
  · intro h rule hordinary
    exact h rule (rule.before_rule6_of_ordinary hordinary)

end Problem

/-! ## Total preorder through Rule 5 -/

/-- Local comparison laws restricted exactly to ordinary Rules 1a--5. -/
structure OrdinaryRuleOutcomeOrderLaws
    {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
    (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit) : Prop where
  functional : ∀ rule, rule.Ordinary → ∀ unit left right first second,
    problem.RuleOutcome descriptorMap rule unit left right first →
    problem.RuleOutcome descriptorMap rule unit left right second →
    first = second
  total : ∀ rule, rule.Ordinary → ∀ unit left right,
    ∃ outcome, problem.RuleOutcome descriptorMap rule unit left right outcome
  eq_refl : ∀ rule, rule.Ordinary → ∀ unit ligand,
    problem.RuleOutcome descriptorMap rule unit ligand ligand Ordering.eq
  eq_symm : ∀ rule, rule.Ordinary → ∀ unit left right,
    problem.RuleOutcome descriptorMap rule unit left right Ordering.eq →
    problem.RuleOutcome descriptorMap rule unit right left Ordering.eq
  eq_trans : ∀ rule, rule.Ordinary → ∀ unit first second third,
    problem.RuleOutcome descriptorMap rule unit first second Ordering.eq →
    problem.RuleOutcome descriptorMap rule unit second third Ordering.eq →
    problem.RuleOutcome descriptorMap rule unit first third Ordering.eq
  gt_trans : ∀ rule, rule.Ordinary → ∀ unit first second third,
    problem.RuleOutcome descriptorMap rule unit first second Ordering.gt →
    problem.RuleOutcome descriptorMap rule unit second third Ordering.gt →
    problem.RuleOutcome descriptorMap rule unit first third Ordering.gt
  gt_eq_trans : ∀ rule, rule.Ordinary → ∀ unit first second third,
    problem.RuleOutcome descriptorMap rule unit first second Ordering.gt →
    problem.RuleOutcome descriptorMap rule unit second third Ordering.eq →
    problem.RuleOutcome descriptorMap rule unit first third Ordering.gt
  eq_gt_trans : ∀ rule, rule.Ordinary → ∀ unit first second third,
    problem.RuleOutcome descriptorMap rule unit first second Ordering.eq →
    problem.RuleOutcome descriptorMap rule unit second third Ordering.gt →
    problem.RuleOutcome descriptorMap rule unit first third Ordering.gt
  reverse_lt : ∀ rule, rule.Ordinary → ∀ unit left right,
    problem.RuleOutcome descriptorMap rule unit left right Ordering.lt →
    problem.RuleOutcome descriptorMap rule unit right left Ordering.gt

namespace OrdinaryRuleOutcomeOrderLaws

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
variable {problem : Problem Atom Unit} {descriptorMap : DescriptorMap Unit}

theorem tied_refl (laws : OrdinaryRuleOutcomeOrderLaws problem descriptorMap)
    (unit : Unit) (ligand : Fin 4) :
    problem.OrdinaryTied descriptorMap unit ligand ligand :=
  fun rule hordinary => laws.eq_refl rule hordinary unit ligand

theorem tied_trans (laws : OrdinaryRuleOutcomeOrderLaws problem descriptorMap)
    {unit : Unit} {first second third : Fin 4}
    (hfirst : problem.OrdinaryTied descriptorMap unit first second)
    (hsecond : problem.OrdinaryTied descriptorMap unit second third) :
    problem.OrdinaryTied descriptorMap unit first third :=
  fun rule hordinary => laws.eq_trans rule hordinary unit first second third
    (hfirst rule hordinary) (hsecond rule hordinary)

theorem higher_tied_trans (laws : OrdinaryRuleOutcomeOrderLaws problem descriptorMap)
    {unit : Unit} {first second third : Fin 4}
    (hfirst : problem.OrdinaryHigher descriptorMap unit first second)
    (hsecond : problem.OrdinaryTied descriptorMap unit second third) :
    problem.OrdinaryHigher descriptorMap unit first third := by
  rcases hfirst with ⟨rule, hordinary, hearlier, hdecisive⟩
  refine ⟨rule, hordinary, ?_, laws.gt_eq_trans rule hordinary unit first second third
    hdecisive (hsecond rule hordinary)⟩
  intro earlier hbefore
  have hearlierOrdinary := SequenceRule.ordinary_of_before_of_ordinary hbefore hordinary
  exact laws.eq_trans earlier hearlierOrdinary unit first second third
    (hearlier earlier hbefore) (hsecond earlier hearlierOrdinary)

theorem tied_higher_trans (laws : OrdinaryRuleOutcomeOrderLaws problem descriptorMap)
    {unit : Unit} {first second third : Fin 4}
    (hfirst : problem.OrdinaryTied descriptorMap unit first second)
    (hsecond : problem.OrdinaryHigher descriptorMap unit second third) :
    problem.OrdinaryHigher descriptorMap unit first third := by
  rcases hsecond with ⟨rule, hordinary, hearlier, hdecisive⟩
  refine ⟨rule, hordinary, ?_, laws.eq_gt_trans rule hordinary unit first second third
    (hfirst rule hordinary) hdecisive⟩
  intro earlier hbefore
  have hearlierOrdinary := SequenceRule.ordinary_of_before_of_ordinary hbefore hordinary
  exact laws.eq_trans earlier hearlierOrdinary unit first second third
    (hfirst earlier hearlierOrdinary) (hearlier earlier hbefore)

theorem higher_trans (laws : OrdinaryRuleOutcomeOrderLaws problem descriptorMap)
    {unit : Unit} {first second third : Fin 4}
    (hfirst : problem.OrdinaryHigher descriptorMap unit first second)
    (hsecond : problem.OrdinaryHigher descriptorMap unit second third) :
    problem.OrdinaryHigher descriptorMap unit first third := by
  rcases hfirst with ⟨firstRule, hfirstOrdinary, hfirstEarlier, hfirstDecisive⟩
  rcases hsecond with ⟨secondRule, hsecondOrdinary, hsecondEarlier, hsecondDecisive⟩
  rcases lt_trichotomy firstRule.rank secondRule.rank with hbefore | hequal | hafter
  · refine ⟨firstRule, hfirstOrdinary, ?_,
      laws.gt_eq_trans firstRule hfirstOrdinary unit first second third
        hfirstDecisive (hsecondEarlier firstRule hbefore)⟩
    intro earlier hearlier
    have hordinary := SequenceRule.ordinary_of_before_of_ordinary hearlier hfirstOrdinary
    exact laws.eq_trans earlier hordinary unit first second third
      (hfirstEarlier earlier hearlier)
      (hsecondEarlier earlier (Nat.lt_trans hearlier hbefore))
  · have hrule : firstRule = secondRule := SequenceRule.rank_injective hequal
    subst secondRule
    refine ⟨firstRule, hfirstOrdinary, ?_,
      laws.gt_trans firstRule hfirstOrdinary unit first second third
        hfirstDecisive hsecondDecisive⟩
    intro earlier hearlier
    have hordinary := SequenceRule.ordinary_of_before_of_ordinary hearlier hfirstOrdinary
    exact laws.eq_trans earlier hordinary unit first second third
      (hfirstEarlier earlier hearlier) (hsecondEarlier earlier hearlier)
  · refine ⟨secondRule, hsecondOrdinary, ?_,
      laws.eq_gt_trans secondRule hsecondOrdinary unit first second third
        (hfirstEarlier secondRule hafter) hsecondDecisive⟩
    intro earlier hearlier
    have hordinary := SequenceRule.ordinary_of_before_of_ordinary hearlier hsecondOrdinary
    exact laws.eq_trans earlier hordinary unit first second third
      (hfirstEarlier earlier (Nat.lt_trans hearlier hafter))
      (hsecondEarlier earlier hearlier)

theorem weakPriority_total (laws : OrdinaryRuleOutcomeOrderLaws problem descriptorMap)
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
    rcases laws.total rule hordinary unit left right with ⟨outcome, houtcome⟩
    cases outcome with
    | lt =>
        refine Or.inr (Or.inl ⟨rule, hordinary, ?_,
          laws.reverse_lt rule hordinary unit left right houtcome⟩)
        intro earlier hbefore
        have hearlierOrdinary :=
          SequenceRule.ordinary_of_before_of_ordinary hbefore hordinary
        exact laws.eq_symm earlier hearlierOrdinary unit left right
          (hearlier earlier hbefore)
    | eq => exact (hnotEq houtcome).elim
    | gt => exact Or.inl (Or.inl ⟨rule, hordinary, hearlier, houtcome⟩)

theorem ordinaryPriorityIsTotalPreorder
    (laws : OrdinaryRuleOutcomeOrderLaws problem descriptorMap) :
    problem.OrdinaryPriorityIsTotalPreorder descriptorMap := by
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

end OrdinaryRuleOutcomeOrderLaws

namespace OrdinaryRuleKeyModel

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
variable {problem : Problem Atom Unit} {descriptorMap : DescriptorMap Unit}

/-- Opponent-independent keys for Rules 1a--5 discharge all ordinary order laws. -/
theorem ordinaryRuleOutcomeOrderLaws
    (model : OrdinaryRuleKeyModel problem descriptorMap) :
    OrdinaryRuleOutcomeOrderLaws problem descriptorMap where
  functional := by
    intro rule hordinary unit left right first second hfirst hsecond
    exact OrderedKeyOutcome.functional
      ((model.characterizes rule hordinary unit left right first).1 hfirst)
      ((model.characterizes rule hordinary unit left right second).1 hsecond)
  total := by
    intro rule hordinary unit left right
    rcases OrderedKeyOutcome.total (model.key unit rule left) (model.key unit rule right) with
      ⟨outcome, houtcome⟩
    exact ⟨outcome, (model.characterizes rule hordinary unit left right outcome).2 houtcome⟩
  eq_refl := by
    intro rule hordinary unit ligand
    exact (model.characterizes rule hordinary unit ligand ligand Ordering.eq).2
      (OrderedKeyOutcome.eq_refl _)
  eq_symm := by
    intro rule hordinary unit left right h
    exact (model.characterizes rule hordinary unit right left Ordering.eq).2
      (OrderedKeyOutcome.eq_symm
        ((model.characterizes rule hordinary unit left right Ordering.eq).1 h))
  eq_trans := by
    intro rule hordinary unit first second third hfirst hsecond
    exact (model.characterizes rule hordinary unit first third Ordering.eq).2
      (OrderedKeyOutcome.eq_trans
        ((model.characterizes rule hordinary unit first second Ordering.eq).1 hfirst)
        ((model.characterizes rule hordinary unit second third Ordering.eq).1 hsecond))
  gt_trans := by
    intro rule hordinary unit first second third hfirst hsecond
    exact (model.characterizes rule hordinary unit first third Ordering.gt).2
      (OrderedKeyOutcome.gt_trans
        ((model.characterizes rule hordinary unit first second Ordering.gt).1 hfirst)
        ((model.characterizes rule hordinary unit second third Ordering.gt).1 hsecond))
  gt_eq_trans := by
    intro rule hordinary unit first second third hfirst hsecond
    exact (model.characterizes rule hordinary unit first third Ordering.gt).2
      (OrderedKeyOutcome.gt_eq_trans
        ((model.characterizes rule hordinary unit first second Ordering.gt).1 hfirst)
        ((model.characterizes rule hordinary unit second third Ordering.eq).1 hsecond))
  eq_gt_trans := by
    intro rule hordinary unit first second third hfirst hsecond
    exact (model.characterizes rule hordinary unit first third Ordering.gt).2
      (OrderedKeyOutcome.eq_gt_trans
        ((model.characterizes rule hordinary unit first second Ordering.eq).1 hfirst)
        ((model.characterizes rule hordinary unit second third Ordering.gt).1 hsecond))
  reverse_lt := by
    intro rule hordinary unit left right h
    exact (model.characterizes rule hordinary unit right left Ordering.gt).2
      (OrderedKeyOutcome.reverse_lt
        ((model.characterizes rule hordinary unit left right Ordering.lt).1 h))

/-- Main Rules-1a--5 theorem: ordinary declarative priority is a total preorder without any
comparison-level assumption about Rule 6. -/
theorem ordinaryPriorityIsTotalPreorder
    (model : OrdinaryRuleKeyModel problem descriptorMap) :
    problem.OrdinaryPriorityIsTotalPreorder descriptorMap :=
  model.ordinaryRuleOutcomeOrderLaws.ordinaryPriorityIsTotalPreorder

end OrdinaryRuleKeyModel

/-! ## Carrier specification -/

/-- Independent data for descriptor-level Rule-6 promotion over an ordinary CIP problem. -/
structure CarrierProblem (Atom Unit : Type u) (Reference : Type v)
    [Fintype Atom] [DecidableEq Atom] where
  base : Problem Atom Unit
  /-- Units whose ordinary tie partition admits carrier promotion. -/
  rule6Eligible : DescriptorMap Unit → Unit → Prop
  /-- Semantic carrier choices are independent of the molecule's atom representation. -/
  admissiblePromotionReference : DescriptorMap Unit → Unit → Reference → Prop
  /-- Final descriptor licensed by promotion of one admissible reference carrier. -/
  promotionDescriptorJudgment :
    DescriptorMap Unit → Unit → Reference → Descriptor → Prop

namespace CarrierProblem

variable {Atom Unit : Type u} {Reference : Type v} [Fintype Atom] [DecidableEq Atom]

/-- All admissible promotion references license one common final descriptor. -/
def Rule6DescriptorCertificate (problem : CarrierProblem Atom Unit Reference)
    (descriptorMap : DescriptorMap Unit) (unit : Unit) (descriptor : Descriptor) : Prop :=
  (∃ reference, problem.admissiblePromotionReference descriptorMap unit reference) ∧
  ∀ reference,
    problem.admissiblePromotionReference descriptorMap unit reference →
    problem.promotionDescriptorJudgment descriptorMap unit reference descriptor

/-- A final descriptor is licensed either by a strict ordinary ranking or by a certified Rule-6
carrier family. -/
def DescriptorJudgment (problem : CarrierProblem Atom Unit Reference)
    (descriptorMap : DescriptorMap Unit) (unit : Unit) (descriptor : Descriptor) : Prop :=
  problem.base.OrdinaryDescriptorJudgment descriptorMap unit descriptor ∨
  (problem.rule6Eligible descriptorMap unit ∧
    problem.Rule6DescriptorCertificate descriptorMap unit descriptor)

/-- Descriptor agreement between the ordinary and carrier paths. -/
def OrdinaryCarrierCompatible (problem : CarrierProblem Atom Unit Reference) : Prop :=
  ∀ descriptorMap unit ordinaryDescriptor carrierDescriptor,
    problem.base.OrdinaryDescriptorJudgment descriptorMap unit ordinaryDescriptor →
    problem.rule6Eligible descriptorMap unit →
    problem.Rule6DescriptorCertificate descriptorMap unit carrierDescriptor →
    ordinaryDescriptor = carrierDescriptor

/-- Rule 6 is enabled only when Rules 1a--5 leave no strict complete ranking. -/
def Rule6EligibleExcludesOrdinary (problem : CarrierProblem Atom Unit Reference) : Prop :=
  ∀ descriptorMap unit descriptor,
    problem.rule6Eligible descriptorMap unit →
    ¬problem.base.OrdinaryDescriptorJudgment descriptorMap unit descriptor

theorem ordinaryCarrierCompatible_of_exclusive
    (problem : CarrierProblem Atom Unit Reference)
    (exclusive : problem.Rule6EligibleExcludesOrdinary) :
    problem.OrdinaryCarrierCompatible := by
  intro descriptorMap unit ordinaryDescriptor _ hordinary heligible _
  exact (exclusive descriptorMap unit ordinaryDescriptor heligible hordinary).elim

/-- Per-reference functionality of the carrier descriptor judgment. -/
def PromotionDescriptorFunctional (problem : CarrierProblem Atom Unit Reference) : Prop :=
  ∀ descriptorMap unit reference first second,
    problem.promotionDescriptorJudgment descriptorMap unit reference first →
    problem.promotionDescriptorJudgment descriptorMap unit reference second →
    first = second

theorem rule6DescriptorCertificate_unique
    (problem : CarrierProblem Atom Unit Reference)
    (functional : problem.PromotionDescriptorFunctional)
    (descriptorMap : DescriptorMap Unit) (unit : Unit) {first second : Descriptor}
    (hfirst : problem.Rule6DescriptorCertificate descriptorMap unit first)
    (hsecond : problem.Rule6DescriptorCertificate descriptorMap unit second) :
    first = second := by
  rcases hfirst with ⟨⟨reference, href⟩, hallFirst⟩
  exact functional descriptorMap unit reference first second
    (hallFirst reference href) (hsecond.2 reference href)

theorem descriptorJudgment_unique
    (problem : CarrierProblem Atom Unit Reference)
    (ordinaryUnique : ∀ descriptorMap unit first second,
      problem.base.OrdinaryDescriptorJudgment descriptorMap unit first →
      problem.base.OrdinaryDescriptorJudgment descriptorMap unit second →
      first = second)
    (promotionFunctional : problem.PromotionDescriptorFunctional)
    (compatible : problem.OrdinaryCarrierCompatible)
    (descriptorMap : DescriptorMap Unit) (unit : Unit) {first second : Descriptor}
    (hfirst : problem.DescriptorJudgment descriptorMap unit first)
    (hsecond : problem.DescriptorJudgment descriptorMap unit second) :
    first = second := by
  rcases hfirst with hfirstOrdinary | ⟨hfirstEligible, hfirstCarrier⟩
  · rcases hsecond with hsecondOrdinary | ⟨hsecondEligible, hsecondCarrier⟩
    · exact ordinaryUnique descriptorMap unit first second hfirstOrdinary hsecondOrdinary
    · exact compatible descriptorMap unit first second
        hfirstOrdinary hsecondEligible hsecondCarrier
  · rcases hsecond with hsecondOrdinary | ⟨_, hsecondCarrier⟩
    · exact (compatible descriptorMap unit second first
        hsecondOrdinary hfirstEligible hfirstCarrier).symm
    · exact problem.rule6DescriptorCertificate_unique promotionFunctional
        descriptorMap unit hfirstCarrier hsecondCarrier

end CarrierProblem

/-! ## Corrected global descriptor-map relation -/

/-- Global CIP specification with ordinary priority and descriptor-level Rule-6 carriers. -/
def CarrierCIPSpec {Atom Unit : Type u} {Reference : Type v} [Fintype Atom] [DecidableEq Atom]
    (problem : CarrierProblem Atom Unit Reference) (descriptorMap : DescriptorMap Unit) : Prop :=
  (∀ unit ligand, ∃ graph, problem.base.admissibleExpansion unit ligand graph) ∧
  (∀ unit descriptor,
    descriptorMap unit = some descriptor ↔
      problem.DescriptorJudgment descriptorMap unit descriptor)

namespace CarrierCIPSpec

variable {Atom Unit : Type u} {Reference : Type v} [Fintype Atom] [DecidableEq Atom]
variable {problem : CarrierProblem Atom Unit Reference} {descriptorMap : DescriptorMap Unit}

theorem expansion_exists (spec : CarrierCIPSpec problem descriptorMap)
    (unit : Unit) (ligand : Fin 4) :
    ∃ graph, problem.base.admissibleExpansion unit ligand graph :=
  spec.1 unit ligand

theorem descriptor_sound (spec : CarrierCIPSpec problem descriptorMap)
    {unit : Unit} {descriptor : Descriptor}
    (h : descriptorMap unit = some descriptor) :
    problem.DescriptorJudgment descriptorMap unit descriptor :=
  (spec.2 unit descriptor).1 h

theorem descriptor_complete (spec : CarrierCIPSpec problem descriptorMap)
    {unit : Unit} {descriptor : Descriptor}
    (h : problem.DescriptorJudgment descriptorMap unit descriptor) :
    descriptorMap unit = some descriptor :=
  (spec.2 unit descriptor).2 h

theorem descriptor_unique (spec : CarrierCIPSpec problem descriptorMap)
    {unit : Unit} {first second : Descriptor}
    (hfirst : problem.DescriptorJudgment descriptorMap unit first)
    (hsecond : problem.DescriptorJudgment descriptorMap unit second) :
    first = second := by
  exact Option.some.inj
    ((spec.descriptor_complete hfirst).symm.trans (spec.descriptor_complete hsecond))

theorem descriptor_eq_none_iff (spec : CarrierCIPSpec problem descriptorMap)
    (unit : Unit) :
    descriptorMap unit = none ↔
      ¬∃ descriptor, problem.DescriptorJudgment descriptorMap unit descriptor := by
  constructor
  · intro hnone ⟨descriptor, hdescriptor⟩
    have hsome := spec.descriptor_complete hdescriptor
    simp [hnone] at hsome
  · intro hnone
    cases hvalue : descriptorMap unit with
    | none => rfl
    | some descriptor =>
        exact (hnone ⟨descriptor, spec.descriptor_sound hvalue⟩).elim

end CarrierCIPSpec

def CarrierDescriptorMapExists {Atom Unit : Type u} {Reference : Type v}
    [Fintype Atom] [DecidableEq Atom]
    (problem : CarrierProblem Atom Unit Reference) : Prop :=
  ∃ descriptorMap, CarrierCIPSpec problem descriptorMap

def CarrierDescriptorMapUnique {Atom Unit : Type u} {Reference : Type v}
    [Fintype Atom] [DecidableEq Atom]
    (problem : CarrierProblem Atom Unit Reference) : Prop :=
  ∀ left right,
    CarrierCIPSpec problem left → CarrierCIPSpec problem right → left = right

/-! ## Well-founded construction and global uniqueness -/

namespace CarrierProblem

variable {Atom Unit : Type u} {Reference : Type v} [Fintype Atom] [DecidableEq Atom]

/-- A unit's descriptor judgment observes a map only at its strict auxiliary dependencies. -/
def DescriptorJudgmentLocal (problem : CarrierProblem Atom Unit Reference)
    (dependency : Unit → Unit → Prop) : Prop :=
  ∀ left right unit,
    (∀ inner, dependency inner unit → left inner = right inner) →
    ∀ descriptor,
      problem.DescriptorJudgment left unit descriptor ↔
        problem.DescriptorJudgment right unit descriptor

/-- At each unit and under every already supplied auxiliary environment, the semantic judgment
determines one exact optional result.  `none` means that no descriptor is derivable. -/
def DescriptorOutcomeExists (problem : CarrierProblem Atom Unit Reference) : Prop :=
  ∀ descriptorMap unit, ∃ value : Option Descriptor, ∀ descriptor,
    value = some descriptor ↔ problem.DescriptorJudgment descriptorMap unit descriptor

/-- Pointwise single-valuedness is sufficient to select the exact optional semantic outcome.
This removes local outcome existence as an independent premise once descriptor coherence has been
proved. -/
theorem descriptorOutcomeExists_of_unique
    (problem : CarrierProblem Atom Unit Reference)
    (unique : ∀ descriptorMap unit first second,
      problem.DescriptorJudgment descriptorMap unit first →
      problem.DescriptorJudgment descriptorMap unit second → first = second) :
    problem.DescriptorOutcomeExists := by
  classical
  intro descriptorMap unit
  by_cases hexists : ∃ descriptor, problem.DescriptorJudgment descriptorMap unit descriptor
  · let selected := Classical.choose hexists
    have hselected : problem.DescriptorJudgment descriptorMap unit selected :=
      Classical.choose_spec hexists
    refine ⟨some selected, ?_⟩
    intro descriptor
    constructor
    · intro heq
      have : selected = descriptor := Option.some.inj heq
      simpa [this] using hselected
    · intro hdescriptor
      exact congrArg some (unique descriptorMap unit selected descriptor hselected hdescriptor)
  · refine ⟨none, ?_⟩
    intro descriptor
    constructor
    · intro h
      simp at h
    · intro h
      exact (hexists ⟨descriptor, h⟩).elim

theorem descriptorMapUnique_of_wellFounded
    (problem : CarrierProblem Atom Unit Reference) (dependency : Unit → Unit → Prop)
    (wellFounded : WellFounded dependency)
    (locality : problem.DescriptorJudgmentLocal dependency) :
    CarrierDescriptorMapUnique problem := by
  intro left right leftSpec rightSpec
  funext unit
  exact wellFounded.induction unit (fun unit ih => by
    have hagree : ∀ inner, dependency inner unit → left inner = right inner :=
      fun inner hinner => ih inner hinner
    cases hleft : left unit with
    | none =>
        cases hright : right unit with
        | none => rfl
        | some descriptor =>
            have hrightJudgment := rightSpec.descriptor_sound hright
            have hleftJudgment :=
              (locality left right unit hagree descriptor).2 hrightJudgment
            have hsome := leftSpec.descriptor_complete hleftJudgment
            simp [hleft] at hsome
    | some descriptor =>
        have hleftJudgment := leftSpec.descriptor_sound hleft
        have hrightJudgment :=
          (locality left right unit hagree descriptor).1 hleftJudgment
        exact (rightSpec.descriptor_complete hrightJudgment).symm)

/-- Partial environment assembled from the already constructed inner dependencies of one unit. -/
noncomputable def dependencyEnvironment (dependency : Unit → Unit → Prop) (unit : Unit)
    (innerValue : ∀ inner, dependency inner unit → Option Descriptor) :
    DescriptorMap Unit := by
  classical
  exact fun inner =>
    if hinner : dependency inner unit then innerValue inner hinner else none

/-- Well-founded semantic evaluation.  This is a mathematical recursion over the declared
dependency relation, not the production scheduler. -/
noncomputable def buildDescriptorMap
    (problem : CarrierProblem Atom Unit Reference) (dependency : Unit → Unit → Prop)
    (wellFounded : WellFounded dependency) (outcomes : problem.DescriptorOutcomeExists) :
    DescriptorMap Unit :=
  wellFounded.fix fun unit innerValue =>
    Classical.choose (outcomes (dependencyEnvironment dependency unit innerValue) unit)

theorem buildDescriptorMap_spec
    (problem : CarrierProblem Atom Unit Reference) (dependency : Unit → Unit → Prop)
    (wellFounded : WellFounded dependency) (outcomes : problem.DescriptorOutcomeExists)
    (locality : problem.DescriptorJudgmentLocal dependency) (unit : Unit)
    (descriptor : Descriptor) :
    buildDescriptorMap problem dependency wellFounded outcomes unit = some descriptor ↔
      problem.DescriptorJudgment
        (buildDescriptorMap problem dependency wellFounded outcomes) unit descriptor := by
  let recursiveEnvironment : DescriptorMap Unit :=
    dependencyEnvironment dependency unit fun inner _ =>
      buildDescriptorMap problem dependency wellFounded outcomes inner
  have hchosen :
      Classical.choose (outcomes recursiveEnvironment unit) = some descriptor ↔
        problem.DescriptorJudgment recursiveEnvironment unit descriptor :=
    Classical.choose_spec (outcomes recursiveEnvironment unit) descriptor
  have hfix : buildDescriptorMap problem dependency wellFounded outcomes unit =
      Classical.choose (outcomes recursiveEnvironment unit) := by
    rw [buildDescriptorMap, WellFounded.fix_eq]
  have hagree : ∀ inner, dependency inner unit →
      recursiveEnvironment inner =
        buildDescriptorMap problem dependency wellFounded outcomes inner := by
    intro inner hinner
    simp [recursiveEnvironment, dependencyEnvironment, hinner]
  rw [hfix, hchosen]
  exact locality recursiveEnvironment
    (buildDescriptorMap problem dependency wellFounded outcomes) unit hagree descriptor

/-- The independent carrier specification has a model whenever expansions exist, dependencies are
well-founded and local, and each local semantic environment determines an optional descriptor. -/
theorem descriptorMapExists_of_wellFounded
    (problem : CarrierProblem Atom Unit Reference) (dependency : Unit → Unit → Prop)
    (expansions : ∀ unit ligand, ∃ graph,
      problem.base.admissibleExpansion unit ligand graph)
    (wellFounded : WellFounded dependency)
    (locality : problem.DescriptorJudgmentLocal dependency)
    (outcomes : problem.DescriptorOutcomeExists) :
    CarrierDescriptorMapExists problem := by
  let descriptorMap := buildDescriptorMap problem dependency wellFounded outcomes
  refine ⟨descriptorMap, expansions, ?_⟩
  intro unit descriptor
  exact buildDescriptorMap_spec problem dependency wellFounded outcomes locality unit descriptor

/-- Exact global existence-and-uniqueness boundary for the corrected carrier semantics. -/
theorem descriptorMap_existsUnique_of_wellFounded
    (problem : CarrierProblem Atom Unit Reference) (dependency : Unit → Unit → Prop)
    (expansions : ∀ unit ligand, ∃ graph,
      problem.base.admissibleExpansion unit ligand graph)
    (wellFounded : WellFounded dependency)
    (locality : problem.DescriptorJudgmentLocal dependency)
    (outcomes : problem.DescriptorOutcomeExists) :
    (∃ descriptorMap, CarrierCIPSpec problem descriptorMap) ∧
      CarrierDescriptorMapUnique problem :=
  ⟨problem.descriptorMapExists_of_wellFounded dependency expansions wellFounded locality outcomes,
    problem.descriptorMapUnique_of_wellFounded dependency wellFounded locality⟩

end CarrierProblem

end
end DeclarativeCIP
end OneCenter
end TetraStereo
