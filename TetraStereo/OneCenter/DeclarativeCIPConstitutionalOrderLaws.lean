import TetraStereo.OneCenter.DeclarativeCIPConstitutionalTotality

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section

open scoped Classical

universe u

/-!
# Independent order laws for the declarative constitutional rules

`DeclarativeCIPPreorder` proves that first-decisive-rule priority is a total preorder once every
rule-local `Problem.RuleOutcome` obeys order laws.  This module proves those laws for Rules 1a, 1b
and 2 of the canonical declarative semantics, for every molecule whose admissible expansions are
faithful and exist (`withCanonicalAddressing_constitutionalOrderLaws`).

The argument has two layers.

* `LexOutcome` is the first-difference comparison of two integer observation fields in hierarchy
  address order.  Its order laws hold for arbitrary fields (`LexOutcome.gt_trans` and siblings).
* Each constitutional `RuleOutcome` is exactly a `LexOutcome` of priority-oriented rule values read
  through one chosen faithful expansion and canonical addressing per ligand
  (`ruleOutcome_iff_lexOutcome`).  Every other expansion and canonical addressing gives the same
  outcome by addressing independence, expansion isomorphism and transport.
-/

/-! ## First-difference order on observation fields -/

/-- First-difference comparison of two observation fields in hierarchy address order. -/
def LexOutcome {V : Type*} [LinearOrder V] (left right : List ℕ → V) : Ordering → Prop :=
  FirstDifferenceOutcome fun position outcome => compare (left position) (right position) = outcome

namespace LexOutcome

variable {V : Type*} [LinearOrder V] {first second third : List ℕ → V}

theorem eq_iff : LexOutcome first second Ordering.eq ↔ ∀ position, first position = second position := by
  unfold LexOutcome FirstDifferenceOutcome
  simp only [compare_eq_iff_eq]

theorem gt_iff : LexOutcome first second Ordering.gt ↔ ∃ position,
    second position < first position ∧
      ∀ earlier, HierarchyAddressBefore earlier position → first earlier = second earlier := by
  unfold LexOutcome FirstDifferenceOutcome
  simp only [compare_gt_iff_gt, compare_eq_iff_eq]

theorem lt_iff : LexOutcome first second Ordering.lt ↔ ∃ position,
    first position < second position ∧
      ∀ earlier, HierarchyAddressBefore earlier position → first earlier = second earlier := by
  unfold LexOutcome FirstDifferenceOutcome
  simp only [compare_lt_iff_lt, compare_eq_iff_eq]

theorem functional {outcome outcome' : Ordering} (h : LexOutcome first second outcome)
    (h' : LexOutcome first second outcome') : outcome = outcome' :=
  FirstDifferenceOutcome.functional (fun _ _ _ h₁ h₂ => h₁.symm.trans h₂) h h'

theorem eq_refl (field : List ℕ → V) : LexOutcome field field Ordering.eq :=
  eq_iff.2 fun _ => rfl

theorem eq_symm (h : LexOutcome first second Ordering.eq) : LexOutcome second first Ordering.eq :=
  eq_iff.2 fun position => (eq_iff.1 h position).symm

theorem eq_trans (h₁ : LexOutcome first second Ordering.eq)
    (h₂ : LexOutcome second third Ordering.eq) : LexOutcome first third Ordering.eq :=
  eq_iff.2 fun position => (eq_iff.1 h₁ position).trans (eq_iff.1 h₂ position)

theorem gt_eq_trans (h₁ : LexOutcome first second Ordering.gt)
    (h₂ : LexOutcome second third Ordering.eq) : LexOutcome first third Ordering.gt := by
  obtain ⟨position, hlt, hbefore⟩ := gt_iff.1 h₁
  have heq := eq_iff.1 h₂
  exact gt_iff.2 ⟨position, by rw [← heq]; exact hlt,
    fun earlier h => (hbefore earlier h).trans (heq earlier)⟩

theorem eq_gt_trans (h₁ : LexOutcome first second Ordering.eq)
    (h₂ : LexOutcome second third Ordering.gt) : LexOutcome first third Ordering.gt := by
  obtain ⟨position, hlt, hbefore⟩ := gt_iff.1 h₂
  have heq := eq_iff.1 h₁
  exact gt_iff.2 ⟨position, by rw [heq]; exact hlt,
    fun earlier h => (heq earlier).trans (hbefore earlier h)⟩

theorem gt_trans (h₁ : LexOutcome first second Ordering.gt)
    (h₂ : LexOutcome second third Ordering.gt) : LexOutcome first third Ordering.gt := by
  obtain ⟨p, hp, hbeforeP⟩ := gt_iff.1 h₁
  obtain ⟨q, hq, hbeforeQ⟩ := gt_iff.1 h₂
  rcases lt_trichotomy (HierarchyAddressKey p) (HierarchyAddressKey q) with hpq | hpq | hpq
  · refine gt_iff.2 ⟨p, ?_, fun earlier h => ?_⟩
    · rw [← hbeforeQ p hpq]; exact hp
    · exact (hbeforeP earlier h).trans (hbeforeQ earlier (lt_trans h hpq))
  · have hsame : p = q := congrArg List.tail hpq
    subst hsame
    exact gt_iff.2 ⟨p, lt_trans hq hp, fun earlier h =>
      (hbeforeP earlier h).trans (hbeforeQ earlier h)⟩
  · refine gt_iff.2 ⟨q, ?_, fun earlier h => ?_⟩
    · rw [hbeforeP q hpq]; exact hq
    · exact (hbeforeP earlier (lt_trans h hpq)).trans (hbeforeQ earlier h)

theorem reverse_lt (h : LexOutcome first second Ordering.lt) :
    LexOutcome second first Ordering.gt := by
  obtain ⟨position, hlt, hbefore⟩ := lt_iff.1 h
  exact gt_iff.2 ⟨position, hlt, fun earlier h => (hbefore earlier h).symm⟩

end LexOutcome

/-! ## Constitutional hierarchy outcomes are first-difference comparisons -/

theorem descendingNatOutcome_iff_compare (left right : ℕ) (outcome : Ordering) :
    DescendingNatOutcome left right outcome ↔ compare (left : ℤ) (right : ℤ) = outcome := by
  cases outcome
  · rw [compare_lt_iff_lt]
    exact ⟨fun h => by cases h; omega, fun h => DescendingNatOutcome.lt (by omega)⟩
  · rw [compare_eq_iff_eq]
    exact ⟨fun h => by cases h; omega, fun h => DescendingNatOutcome.eq (by omega)⟩
  · rw [compare_gt_iff_gt]
    exact ⟨fun h => by cases h; omega, fun h => DescendingNatOutcome.gt (by omega)⟩

theorem rule1bDistanceOutcome_iff_compare (left right : ℕ) (outcome : Ordering) :
    Rule1bDistanceOutcome left right outcome ↔
      compare (-(left : ℤ)) (-(right : ℤ)) = outcome := by
  cases outcome
  · rw [compare_lt_iff_lt]
    exact ⟨fun h => by cases h; omega, fun h => Rule1bDistanceOutcome.lt (by omega)⟩
  · rw [compare_eq_iff_eq]
    exact ⟨fun h => by cases h; omega, fun h => Rule1bDistanceOutcome.eq (by omega)⟩
  · rw [compare_gt_iff_gt]
    exact ⟨fun h => by cases h; omega, fun h => Rule1bDistanceOutcome.gt (by omega)⟩

theorem ruleValueOutcome_iff_compare (rule : ConstitutionalRule) (left right : ℕ)
    (outcome : Ordering) :
    RuleValueOutcome rule left right outcome ↔
      compare (priorityValue rule left) (priorityValue rule right) = outcome := by
  cases rule
  · exact descendingNatOutcome_iff_compare left right outcome
  · exact rule1bDistanceOutcome_iff_compare left right outcome
  · exact descendingNatOutcome_iff_compare left right outcome

section Fields

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)

/-- The priority-oriented observation field of one rule under one addressing. -/
def observationField {graph : RootedDigraph Atom} (addressing : graph.Addressing)
    (rule : ConstitutionalRule) : List ℕ → ℤ :=
  fun position => priorityValue rule (ruleValue molecule rule position (addressLabel addressing position))

theorem hierarchyOutcome_iff_lexOutcome {left right : RootedDigraph Atom}
    (leftAddressing : left.Addressing) (rightAddressing : right.Addressing)
    (rule : ConstitutionalRule) (outcome : Ordering) :
    ConstitutionalHierarchyOutcome molecule rule left leftAddressing right rightAddressing
        outcome ↔
      LexOutcome (observationField molecule leftAddressing rule)
        (observationField molecule rightAddressing rule) outcome := by
  apply FirstDifferenceOutcome.congr
  intro position outcome
  rw [constitutionalOutcomeAt_iff, ruleValueOutcome_iff_compare]
  rfl

end Fields

/-! ## Rule outcomes through chosen expansions -/

namespace ConstitutionalProblemData

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
  (data : ConstitutionalProblemData Atom Unit)
  (hfaithful : data.ExpansionsFaithful)
  (hexpansion : ∀ unit ligand, ∃ graph, data.admissibleExpansion unit ligand graph)

/-- The chosen admissible expansion of a ligand. -/
def chosenExpansion (unit : Unit) (ligand : Fin 4) : RootedDigraph Atom :=
  Classical.choose (hexpansion unit ligand)

theorem chosenExpansion_admissible (unit : Unit) (ligand : Fin 4) :
    data.admissibleExpansion unit ligand (data.chosenExpansion hexpansion unit ligand) :=
  Classical.choose_spec (hexpansion unit ligand)

include hfaithful in
theorem chosenExpansion_has_canonical (unit : Unit) (ligand : Fin 4) :
    ∃ addressing : (data.chosenExpansion hexpansion unit ligand).Addressing,
      CanonicalAddressing data.molecule addressing := by
  obtain ⟨_, base, _⟩ := (hfaithful _ _ _ (data.chosenExpansion_admissible hexpansion unit ligand)).1
  exact exists_canonicalAddressing data.molecule base

/-- The chosen canonical addressing of the chosen expansion. -/
def chosenAddressing (unit : Unit) (ligand : Fin 4) :
    (data.chosenExpansion hexpansion unit ligand).Addressing :=
  Classical.choose (data.chosenExpansion_has_canonical hfaithful hexpansion unit ligand)

theorem chosenAddressing_canonical (unit : Unit) (ligand : Fin 4) :
    CanonicalAddressing data.molecule (data.chosenAddressing hfaithful hexpansion unit ligand) :=
  Classical.choose_spec (data.chosenExpansion_has_canonical hfaithful hexpansion unit ligand)

/-- The observation field of a ligand for one constitutional rule. -/
def ligandField (unit : Unit) (rule : ConstitutionalRule) (ligand : Fin 4) : List ℕ → ℤ :=
  observationField data.molecule (data.chosenAddressing hfaithful hexpansion unit ligand) rule

theorem outcomeOnGraphs_iff_canonicalOutcome (descriptorMap : DescriptorMap Unit) (unit : Unit)
    (rule : ConstitutionalRule) {left right : RootedDigraph Atom} {outcome : Ordering} :
    data.withCanonicalAddressing.toProblem.OutcomeOnGraphs descriptorMap rule.toSequenceRule
        unit left right outcome ↔
      data.withCanonicalAddressing.CanonicalOutcome descriptorMap unit rule left right outcome := by
  cases rule <;> rfl

/-- **Rule outcomes are first-difference comparisons of ligand observation fields.** -/
theorem ruleOutcome_iff_lexOutcome (descriptorMap : DescriptorMap Unit) (unit : Unit)
    (rule : ConstitutionalRule) (left right : Fin 4) (outcome : Ordering) :
    data.withCanonicalAddressing.toProblem.RuleOutcome descriptorMap rule.toSequenceRule unit
        left right outcome ↔
      LexOutcome (data.ligandField hfaithful hexpansion unit rule left)
        (data.ligandField hfaithful hexpansion unit rule right) outcome := by
  have hleft₀ := data.chosenExpansion_admissible hexpansion unit left
  have hright₀ := data.chosenExpansion_admissible hexpansion unit right
  have hla := data.chosenAddressing_canonical hfaithful hexpansion unit left
  have hra := data.chosenAddressing_canonical hfaithful hexpansion unit right
  constructor
  · intro h
    have hcanonical := (data.outcomeOnGraphs_iff_canonicalOutcome descriptorMap unit rule).1
      (h _ _ hleft₀ hright₀)
    exact (hierarchyOutcome_iff_lexOutcome data.molecule _ _ rule outcome).1
      (hcanonical.2.2 _ _ hla hra)
  · intro hlex graphLeft graphRight hgl hgr
    have hchosen : data.withCanonicalAddressing.CanonicalOutcome descriptorMap unit rule
        (data.chosenExpansion hexpansion unit left) (data.chosenExpansion hexpansion unit right)
        outcome := by
      refine ⟨⟨_, hla⟩, ⟨_, hra⟩, fun la ra hla' hra' => ?_⟩
      exact (hierarchyOutcome_canonical_iff data.molecule hla hla' hra hra' rule outcome).1
        ((hierarchyOutcome_iff_lexOutcome data.molecule _ _ rule outcome).2 hlex)
    obtain ⟨leftIso⟩ := RootedDigraph.faithfulExactExpansion_unique_up_to_iso _ _ _ _ _
      (hfaithful _ _ _ hleft₀) (hfaithful _ _ _ hgl)
    obtain ⟨rightIso⟩ := RootedDigraph.faithfulExactExpansion_unique_up_to_iso _ _ _ _ _
      (hfaithful _ _ _ hright₀) (hfaithful _ _ _ hgr)
    rw [data.outcomeOnGraphs_iff_canonicalOutcome descriptorMap unit rule]
    exact (data.withCanonicalAddressing.canonicalOutcome_transport_iff descriptorMap unit rule
      leftIso rightIso outcome).1 hchosen

end ConstitutionalProblemData

/-! ## The order laws -/

/-- `RuleOutcomeOrderLaws` restricted to the constitutional rules. -/
structure ConstitutionalRuleOutcomeOrderLaws {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
    (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit) : Prop where
  functional : ∀ (rule : ConstitutionalRule) unit left right first second,
    problem.RuleOutcome descriptorMap rule.toSequenceRule unit left right first →
    problem.RuleOutcome descriptorMap rule.toSequenceRule unit left right second → first = second
  total : ∀ (rule : ConstitutionalRule) unit left right,
    ∃ outcome, problem.RuleOutcome descriptorMap rule.toSequenceRule unit left right outcome
  eq_refl : ∀ (rule : ConstitutionalRule) unit ligand,
    problem.RuleOutcome descriptorMap rule.toSequenceRule unit ligand ligand Ordering.eq
  eq_symm : ∀ (rule : ConstitutionalRule) unit left right,
    problem.RuleOutcome descriptorMap rule.toSequenceRule unit left right Ordering.eq →
    problem.RuleOutcome descriptorMap rule.toSequenceRule unit right left Ordering.eq
  eq_trans : ∀ (rule : ConstitutionalRule) unit first second third,
    problem.RuleOutcome descriptorMap rule.toSequenceRule unit first second Ordering.eq →
    problem.RuleOutcome descriptorMap rule.toSequenceRule unit second third Ordering.eq →
    problem.RuleOutcome descriptorMap rule.toSequenceRule unit first third Ordering.eq
  gt_trans : ∀ (rule : ConstitutionalRule) unit first second third,
    problem.RuleOutcome descriptorMap rule.toSequenceRule unit first second Ordering.gt →
    problem.RuleOutcome descriptorMap rule.toSequenceRule unit second third Ordering.gt →
    problem.RuleOutcome descriptorMap rule.toSequenceRule unit first third Ordering.gt
  gt_eq_trans : ∀ (rule : ConstitutionalRule) unit first second third,
    problem.RuleOutcome descriptorMap rule.toSequenceRule unit first second Ordering.gt →
    problem.RuleOutcome descriptorMap rule.toSequenceRule unit second third Ordering.eq →
    problem.RuleOutcome descriptorMap rule.toSequenceRule unit first third Ordering.gt
  eq_gt_trans : ∀ (rule : ConstitutionalRule) unit first second third,
    problem.RuleOutcome descriptorMap rule.toSequenceRule unit first second Ordering.eq →
    problem.RuleOutcome descriptorMap rule.toSequenceRule unit second third Ordering.gt →
    problem.RuleOutcome descriptorMap rule.toSequenceRule unit first third Ordering.gt
  reverse_lt : ∀ (rule : ConstitutionalRule) unit left right,
    problem.RuleOutcome descriptorMap rule.toSequenceRule unit left right Ordering.lt →
    problem.RuleOutcome descriptorMap rule.toSequenceRule unit right left Ordering.gt

namespace ConstitutionalProblemData

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]

/-- **Independent order laws for Rules 1a, 1b, and 2.**  With faithful admissible expansions that
exist, every constitutional rule outcome of the canonical declarative semantics is functional,
total, reflexive, symmetric and transitive on ties, strictly transitive, mixed transitive, and
reversible. -/
theorem withCanonicalAddressing_constitutionalOrderLaws
    (data : ConstitutionalProblemData Atom Unit) (hfaithful : data.ExpansionsFaithful)
    (hexpansion : ∀ unit ligand, ∃ graph, data.admissibleExpansion unit ligand graph)
    (descriptorMap : DescriptorMap Unit) :
    ConstitutionalRuleOutcomeOrderLaws data.withCanonicalAddressing.toProblem descriptorMap := by
  have h := data.ruleOutcome_iff_lexOutcome hfaithful hexpansion descriptorMap
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rule unit left right first second h₁ h₂
    exact LexOutcome.functional ((h unit rule left right first).1 h₁)
      ((h unit rule left right second).1 h₂)
  · intro rule unit left right
    obtain ⟨outcome, houtcome, _⟩ := data.withCanonicalAddressing_ruleOutcome_existsUnique
      hfaithful hexpansion descriptorMap unit rule left right
    exact ⟨outcome, houtcome⟩
  · intro rule unit ligand
    exact (h unit rule ligand ligand _).2 (LexOutcome.eq_refl _)
  · intro rule unit left right h₁
    exact (h unit rule right left _).2 (LexOutcome.eq_symm ((h unit rule left right _).1 h₁))
  · intro rule unit first second third h₁ h₂
    exact (h unit rule first third _).2
      (LexOutcome.eq_trans ((h unit rule first second _).1 h₁) ((h unit rule second third _).1 h₂))
  · intro rule unit first second third h₁ h₂
    exact (h unit rule first third _).2
      (LexOutcome.gt_trans ((h unit rule first second _).1 h₁) ((h unit rule second third _).1 h₂))
  · intro rule unit first second third h₁ h₂
    exact (h unit rule first third _).2 (LexOutcome.gt_eq_trans ((h unit rule first second _).1 h₁)
      ((h unit rule second third _).1 h₂))
  · intro rule unit first second third h₁ h₂
    exact (h unit rule first third _).2 (LexOutcome.eq_gt_trans ((h unit rule first second _).1 h₁)
      ((h unit rule second third _).1 h₂))
  · intro rule unit left right h₁
    exact (h unit rule right left _).2 (LexOutcome.reverse_lt ((h unit rule left right _).1 h₁))

end ConstitutionalProblemData

/-! ## The Rules 1a--2 priority preorder -/

namespace Problem

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
  (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit)

/-- Every constitutional rule preceding `rule` ties. -/
def ConstitutionalEarlierTie (rule : ConstitutionalRule) (unit : Unit) (left right : Fin 4) :
    Prop :=
  ∀ earlier : ConstitutionalRule, ruleIndex earlier < ruleIndex rule →
    problem.RuleOutcome descriptorMap earlier.toSequenceRule unit left right Ordering.eq

/-- Strict priority decided by the first decisive rule among 1a, 1b and 2. -/
def ConstitutionalHigher (unit : Unit) (left right : Fin 4) : Prop :=
  ∃ rule : ConstitutionalRule, problem.ConstitutionalEarlierTie descriptorMap rule unit left right ∧
    problem.RuleOutcome descriptorMap rule.toSequenceRule unit left right Ordering.gt

/-- All of Rules 1a, 1b and 2 tie. -/
def ConstitutionalTied (unit : Unit) (left right : Fin 4) : Prop :=
  ∀ rule : ConstitutionalRule,
    problem.RuleOutcome descriptorMap rule.toSequenceRule unit left right Ordering.eq

def ConstitutionalWeakPriority (unit : Unit) (left right : Fin 4) : Prop :=
  problem.ConstitutionalHigher descriptorMap unit left right ∨
    problem.ConstitutionalTied descriptorMap unit left right

/-- The Rules 1a--2 weak priority is a total preorder. -/
def ConstitutionalPriorityIsTotalPreorder : Prop :=
  (∀ unit ligand, problem.ConstitutionalWeakPriority descriptorMap unit ligand ligand) ∧
  (∀ unit first second third,
    problem.ConstitutionalWeakPriority descriptorMap unit first second →
    problem.ConstitutionalWeakPriority descriptorMap unit second third →
    problem.ConstitutionalWeakPriority descriptorMap unit first third) ∧
  (∀ unit left right,
    problem.ConstitutionalWeakPriority descriptorMap unit left right ∨
    problem.ConstitutionalWeakPriority descriptorMap unit right left)

end Problem

theorem ruleIndex_injective : Function.Injective ruleIndex := by
  intro first second h
  cases first <;> cases second <;> simp_all [ruleIndex]

theorem Problem.constitutionalEarlierTie_mono {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
    {problem : Problem Atom Unit} {descriptorMap : DescriptorMap Unit}
    {rule rule' : ConstitutionalRule} (hle : ruleIndex rule' ≤ ruleIndex rule)
    {unit : Unit} {left right : Fin 4}
    (h : problem.ConstitutionalEarlierTie descriptorMap rule unit left right) :
    problem.ConstitutionalEarlierTie descriptorMap rule' unit left right :=
  fun earlier hlt => h earlier (lt_of_lt_of_le hlt hle)

namespace ConstitutionalRuleOutcomeOrderLaws

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
  {problem : Problem Atom Unit} {descriptorMap : DescriptorMap Unit}
  (laws : ConstitutionalRuleOutcomeOrderLaws problem descriptorMap)

include laws

theorem earlierTie_trans {rule : ConstitutionalRule} {unit : Unit} {first second third : Fin 4}
    (h₁ : problem.ConstitutionalEarlierTie descriptorMap rule unit first second)
    (h₂ : problem.ConstitutionalEarlierTie descriptorMap rule unit second third) :
    problem.ConstitutionalEarlierTie descriptorMap rule unit first third :=
  fun earlier h => laws.eq_trans earlier unit first second third (h₁ earlier h) (h₂ earlier h)

theorem higher_trans {unit : Unit} {first second third : Fin 4}
    (h₁ : problem.ConstitutionalHigher descriptorMap unit first second)
    (h₂ : problem.ConstitutionalHigher descriptorMap unit second third) :
    problem.ConstitutionalHigher descriptorMap unit first third := by
  obtain ⟨r₁, tie₁, gt₁⟩ := h₁
  obtain ⟨r₂, tie₂, gt₂⟩ := h₂
  rcases lt_trichotomy (ruleIndex r₁) (ruleIndex r₂) with h | h | h
  · exact ⟨r₁, laws.earlierTie_trans tie₁ (Problem.constitutionalEarlierTie_mono h.le tie₂),
      laws.gt_eq_trans r₁ unit first second third gt₁ (tie₂ r₁ h)⟩
  · have hr : r₁ = r₂ := ruleIndex_injective h
    subst hr
    exact ⟨r₁, laws.earlierTie_trans tie₁ tie₂, laws.gt_trans r₁ unit first second third gt₁ gt₂⟩
  · exact ⟨r₂, laws.earlierTie_trans (Problem.constitutionalEarlierTie_mono h.le tie₁) tie₂,
      laws.eq_gt_trans r₂ unit first second third (tie₁ r₂ h) gt₂⟩

theorem higher_tied_trans {unit : Unit} {first second third : Fin 4}
    (h₁ : problem.ConstitutionalHigher descriptorMap unit first second)
    (h₂ : problem.ConstitutionalTied descriptorMap unit second third) :
    problem.ConstitutionalHigher descriptorMap unit first third := by
  obtain ⟨r, tie, gt⟩ := h₁
  exact ⟨r, laws.earlierTie_trans tie (fun earlier _ => h₂ earlier),
    laws.gt_eq_trans r unit first second third gt (h₂ r)⟩

theorem tied_higher_trans {unit : Unit} {first second third : Fin 4}
    (h₁ : problem.ConstitutionalTied descriptorMap unit first second)
    (h₂ : problem.ConstitutionalHigher descriptorMap unit second third) :
    problem.ConstitutionalHigher descriptorMap unit first third := by
  obtain ⟨r, tie, gt⟩ := h₂
  exact ⟨r, laws.earlierTie_trans (fun earlier _ => h₁ earlier) tie,
    laws.eq_gt_trans r unit first second third (h₁ r) gt⟩

theorem weakPriority_total (unit : Unit) (left right : Fin 4) :
    problem.ConstitutionalWeakPriority descriptorMap unit left right ∨
      problem.ConstitutionalWeakPriority descriptorMap unit right left := by
  have hdecide : ∀ rule : ConstitutionalRule,
      problem.ConstitutionalEarlierTie descriptorMap rule unit left right →
      problem.RuleOutcome descriptorMap rule.toSequenceRule unit left right Ordering.eq ∨
        problem.ConstitutionalHigher descriptorMap unit left right ∨
        problem.ConstitutionalHigher descriptorMap unit right left := by
    intro rule tie
    obtain ⟨outcome, houtcome⟩ := laws.total rule unit left right
    cases outcome with
    | eq => exact Or.inl houtcome
    | gt => exact Or.inr (Or.inl ⟨rule, tie, houtcome⟩)
    | lt =>
        exact Or.inr (Or.inr ⟨rule, fun earlier h => laws.eq_symm earlier unit left right
          (tie earlier h), laws.reverse_lt rule unit left right houtcome⟩)
  have tie1a : problem.ConstitutionalEarlierTie descriptorMap .rule1aAtomicNumber unit left right :=
    fun earlier h => by cases earlier <;> simp [ruleIndex] at h
  rcases hdecide _ tie1a with e1a | hl | hr
  · have tie1b : problem.ConstitutionalEarlierTie descriptorMap .rule1bDuplicateNodeProximity unit
        left right := fun earlier h => by
      cases earlier
      · exact e1a
      all_goals simp [ruleIndex] at h
    rcases hdecide _ tie1b with e1b | hl | hr
    · have tie2 : problem.ConstitutionalEarlierTie descriptorMap .rule2AtomicMass unit left right :=
        fun earlier h => by
          cases earlier
          · exact e1a
          · exact e1b
          · simp [ruleIndex] at h
      rcases hdecide _ tie2 with e2 | hl | hr
      · exact Or.inl (Or.inr fun rule => by cases rule <;> assumption)
      · exact Or.inl (Or.inl hl)
      · exact Or.inr (Or.inl hr)
    · exact Or.inl (Or.inl hl)
    · exact Or.inr (Or.inl hr)
  · exact Or.inl (Or.inl hl)
  · exact Or.inr (Or.inl hr)

/-- **The Rules 1a--2 priority is a total preorder.** -/
theorem constitutionalPriorityIsTotalPreorder :
    problem.ConstitutionalPriorityIsTotalPreorder descriptorMap := by
  refine ⟨fun unit ligand => Or.inr fun rule => laws.eq_refl rule unit ligand, ?_,
    laws.weakPriority_total⟩
  intro unit first second third h₁ h₂
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact Or.inl (laws.higher_trans h₁ h₂)
  · exact Or.inl (laws.higher_tied_trans h₁ h₂)
  · exact Or.inl (laws.tied_higher_trans h₁ h₂)
  · exact Or.inr fun rule => laws.eq_trans rule unit first second third (h₁ rule) (h₂ rule)

end ConstitutionalRuleOutcomeOrderLaws

namespace ConstitutionalProblemData

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]

/-- **Independent Rules 1a--2 priority.**  For every molecule whose admissible expansions are
faithful and exist, the first-decisive Rules 1a--2 priority of the canonical declarative semantics
is a total preorder. -/
theorem withCanonicalAddressing_constitutionalPriorityIsTotalPreorder
    (data : ConstitutionalProblemData Atom Unit) (hfaithful : data.ExpansionsFaithful)
    (hexpansion : ∀ unit ligand, ∃ graph, data.admissibleExpansion unit ligand graph)
    (descriptorMap : DescriptorMap Unit) :
    data.withCanonicalAddressing.toProblem.ConstitutionalPriorityIsTotalPreorder descriptorMap :=
  (data.withCanonicalAddressing_constitutionalOrderLaws hfaithful hexpansion
    descriptorMap).constitutionalPriorityIsTotalPreorder

end ConstitutionalProblemData

end
end DeclarativeCIP
end OneCenter
end TetraStereo
