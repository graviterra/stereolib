import TetraStereo.OneCenter.DeclarativeCIPPreorder
import Mathlib.Data.Finset.Sort

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section

universe u

/-!
# Declarative Rule-6 promotion semantics

This module isolates the proof missing from the production consistency check.  It defines a unary
promotion key for one reference on one addressed rooted digraph, proves that key invariant under
representation isomorphism, and gives sufficient semantic conditions for both graph-level Rule-6
promotion independence and a ligand-level `Rule6KeyModel`.
-/

/-- One unambiguous encoded Rule-6 node occurrence.

The address length prefix prevents the final promotion bit from being confused with an address
slot.  The last entry is one exactly when this occurrence represents the promoted atom. -/
def rule6AddressEntry {Atom : Type u} [DecidableEq Atom]
    {graph : RootedDigraph Atom} (addressing : graph.Addressing)
    (reference : Atom) (node : graph.Node) : List ℕ :=
  (addressing.address node).length ::
    (addressing.address node ++
      [if (graph.label node).atom? = some reference then 1 else 0])

/-- Opponent-independent Rule-6 key of one addressed hierarchy.

Sorting removes the carrier enumeration while retaining exact semantic addresses and every
occurrence of the promoted atom, including duplicate nodes. -/
noncomputable def rule6GraphKey {Atom : Type u} [DecidableEq Atom]
    (graph : RootedDigraph Atom) (addressing : graph.Addressing)
    (reference : Atom) : RuleKey := by
  classical
  letI : Fintype graph.Node := graph.nodeFintype
  exact (Finset.univ.image (rule6AddressEntry addressing reference)).sort (· ≤ ·)

theorem rule6AddressEntry_transport {Atom : Type u} [DecidableEq Atom]
    {left right : RootedDigraph Atom} (addressing : left.Addressing)
    (iso : RootedDigraph.Iso left right) (reference : Atom) (node : left.Node) :
    rule6AddressEntry (addressing.transport iso) reference (iso.toEquiv node) =
      rule6AddressEntry addressing reference node := by
  simp [rule6AddressEntry, RootedDigraph.Addressing.transport, iso.map_label]

/-- The canonical promotion key is invariant under every rooted-digraph representation
isomorphism, not only atom relabeling. -/
theorem rule6GraphKey_transport {Atom : Type u} [DecidableEq Atom]
    {left right : RootedDigraph Atom} (addressing : left.Addressing)
    (iso : RootedDigraph.Iso left right) (reference : Atom) :
    rule6GraphKey right (addressing.transport iso) reference =
      rule6GraphKey left addressing reference := by
  classical
  letI : Fintype left.Node := left.nodeFintype
  letI : Fintype right.Node := right.nodeFintype
  have hfinset :
      Finset.univ.image (rule6AddressEntry (addressing.transport iso) reference) =
        Finset.univ.image (rule6AddressEntry addressing reference) := by
    ext entry
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨node, rfl⟩
      refine ⟨iso.toEquiv.symm node, ?_⟩
      simpa using (rule6AddressEntry_transport addressing iso reference
        (iso.toEquiv.symm node)).symm
    · rintro ⟨node, rfl⟩
      exact ⟨iso.toEquiv node,
        rule6AddressEntry_transport addressing iso reference node⟩
  simp only [rule6GraphKey]
  rw [hfinset]

/-! ## Descriptor-level promotion independence -/

/-- Chemically relevant Rule-6 independence: every admissible reference licenses the same final
descriptor.  This is intentionally weaker than equality of all pairwise ligand comparisons or
rankings. -/
def PromotionDescriptorIndependent {Context Reference FinalDescriptor : Type*}
    (admissible : Context → Reference → Prop)
    (judgment : Context → Reference → FinalDescriptor → Prop) : Prop :=
  ∀ context reference₁ reference₂ descriptor₁ descriptor₂,
    admissible context reference₁ → admissible context reference₂ →
    judgment context reference₁ descriptor₁ → judgment context reference₂ descriptor₂ →
    descriptor₁ = descriptor₂

/-- A common descriptor witnessed for every admissible reference. -/
def PromotionDescriptorCertificate {Context Reference FinalDescriptor : Type*}
    (admissible : Context → Reference → Prop)
    (judgment : Context → Reference → FinalDescriptor → Prop)
    (context : Context) (descriptor : FinalDescriptor) : Prop :=
  (∃ reference, admissible context reference) ∧
    ∀ reference, admissible context reference → judgment context reference descriptor

/-- A common certificate plus per-reference descriptor functionality proves descriptor-level
promotion independence. -/
theorem promotionDescriptorIndependent_of_certificate
    {Context Reference FinalDescriptor : Type*}
    (admissible : Context → Reference → Prop)
    (judgment : Context → Reference → FinalDescriptor → Prop)
    (functional : ∀ context reference first second,
      judgment context reference first → judgment context reference second → first = second)
    (certificate : ∀ context, ∃ descriptor,
      PromotionDescriptorCertificate admissible judgment context descriptor) :
    PromotionDescriptorIndependent admissible judgment := by
  intro context reference₁ reference₂ descriptor₁ descriptor₂
    href₁ href₂ hdescriptor₁ hdescriptor₂
  rcases certificate context with ⟨common, _, hall⟩
  exact (functional context reference₁ descriptor₁ common
    hdescriptor₁ (hall reference₁ href₁)).trans
      (functional context reference₂ descriptor₂ common
        hdescriptor₂ (hall reference₂ href₂)).symm

/-! ## From graph promotion keys to the declarative Rule-6 obligations -/

/-- Strong comparison-level Rule-6 data over the already constructed Rules-1a--5 problem.

`promotionKey` is unary in both the reference and graph.  The agreement fields express the two
distinct invariances needed by revised Rule 6:

* equivalent admissible references give the same key on every graph;
* every admissible expansion of one ligand gives its common ligand key.

Neither condition chooses a reference, traversal, or expansion algorithm.  This structure is a
sufficient interface for a globally coherent ligand preorder.  It is deliberately stronger than
the descriptor-level agreement certified by `rankRule6EquivalentReferences?`; the production
algorithm must not be claimed as an instance merely from equal final descriptors. -/
structure Rule6PromotionSemantics (Atom Unit : Type u)
    [Fintype Atom] [DecidableEq Atom]
    extends StereochemicalProblemData Atom Unit where
  promotionKey : DescriptorMap Unit → Unit → Atom → RootedDigraph Atom → RuleKey
  judgment_characterizes :
    ∀ descriptorMap unit reference left right outcome,
      rule6Judgment descriptorMap unit reference left right outcome ↔
        OrderedKeyOutcome
          (promotionKey descriptorMap unit reference left)
          (promotionKey descriptorMap unit reference right) outcome
  admissible_reference_exists :
    ∀ descriptorMap unit, ∃ reference,
      admissibleRule6Reference descriptorMap unit reference
  expansion_exists :
    ∀ unit ligand, ∃ graph, admissibleExpansion unit ligand graph
  reference_key_agreement :
    ∀ descriptorMap unit reference₁ reference₂,
      admissibleRule6Reference descriptorMap unit reference₁ →
      admissibleRule6Reference descriptorMap unit reference₂ →
      ∀ graph,
        promotionKey descriptorMap unit reference₁ graph =
          promotionKey descriptorMap unit reference₂ graph
  ligandKey : DescriptorMap Unit → Unit → Fin 4 → RuleKey
  expansion_key_agreement :
    ∀ descriptorMap unit ligand reference graph,
      admissibleRule6Reference descriptorMap unit reference →
      admissibleExpansion unit ligand graph →
      promotionKey descriptorMap unit reference graph =
        ligandKey descriptorMap unit ligand
  promotionKey_invariant :
    ∀ descriptorMap unit reference {left right : RootedDigraph Atom},
      RootedDigraph.Iso left right →
      promotionKey descriptorMap unit reference left =
        promotionKey descriptorMap unit reference right

namespace Rule6PromotionSemantics

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]

/-- Agreement of unary reference keys proves the kernel's graph-level promotion-independence
obligation. -/
theorem promotionIndependent (data : Rule6PromotionSemantics Atom Unit) :
    Rule6PromotionIndependent data.toStereochemicalProblemData.toProblem := by
  intro descriptorMap unit reference₁ reference₂ left right outcome₁ outcome₂
    href₁ href₂ hout₁ hout₂
  have hfirst :=
    (data.judgment_characterizes descriptorMap unit reference₁ left right outcome₁).1 hout₁
  have hsecond :=
    (data.judgment_characterizes descriptorMap unit reference₂ left right outcome₂).1 hout₂
  rw [data.reference_key_agreement descriptorMap unit reference₁ reference₂ href₁ href₂ left,
    data.reference_key_agreement descriptorMap unit reference₁ reference₂ href₁ href₂ right]
    at hfirst
  exact OrderedKeyOutcome.functional hfirst hsecond

/-- The common ligand promotion key characterizes the universal declarative Rule-6 outcome. -/
theorem ruleOutcome_iff_orderedKeyOutcome
    (data : Rule6PromotionSemantics Atom Unit)
    (descriptorMap : DescriptorMap Unit) (unit : Unit) (left right : Fin 4)
    (outcome : Ordering) :
    data.toStereochemicalProblemData.toProblem.RuleOutcome descriptorMap
        SequenceRule.rule6ReferencePromotion unit left right outcome ↔
      OrderedKeyOutcome (data.ligandKey descriptorMap unit left)
        (data.ligandKey descriptorMap unit right) outcome := by
  constructor
  · intro h
    rcases data.expansion_exists unit left with ⟨leftGraph, hleft⟩
    rcases data.expansion_exists unit right with ⟨rightGraph, hright⟩
    rcases h leftGraph rightGraph hleft hright with ⟨reference, href, hjudgment⟩
    have hkey := (data.judgment_characterizes descriptorMap unit reference
      leftGraph rightGraph outcome).1 hjudgment
    rw [data.expansion_key_agreement descriptorMap unit left reference leftGraph href hleft,
      data.expansion_key_agreement descriptorMap unit right reference rightGraph href hright]
      at hkey
    exact hkey
  · intro hkey leftGraph rightGraph hleft hright
    rcases data.admissible_reference_exists descriptorMap unit with ⟨reference, href⟩
    refine ⟨reference, href, ?_⟩
    apply (data.judgment_characterizes descriptorMap unit reference
      leftGraph rightGraph outcome).2
    simpa [data.expansion_key_agreement descriptorMap unit left reference leftGraph href hleft,
      data.expansion_key_agreement descriptorMap unit right reference rightGraph href hright]
      using hkey

def rule6KeyModel (data : Rule6PromotionSemantics Atom Unit)
    (descriptorMap : DescriptorMap Unit) :
    Rule6KeyModel data.toStereochemicalProblemData.toProblem descriptorMap where
  key := data.ligandKey descriptorMap
  characterizes := data.ruleOutcome_iff_orderedKeyOutcome descriptorMap

/-- Unary graph keys also prove representation invariance of the Rule-6 outcome relation. -/
theorem rule6RepresentationInvariant (data : Rule6PromotionSemantics Atom Unit) :
    data.toStereochemicalProblemData.Rule6RepresentationInvariant := by
  intro descriptorMap unit left left' right right' outcome leftIso rightIso
  constructor
  · rintro ⟨reference, href, hjudgment⟩
    refine ⟨reference, href, ?_⟩
    apply (data.judgment_characterizes descriptorMap unit reference
      left' right' outcome).2
    have hkey := (data.judgment_characterizes descriptorMap unit reference
      left right outcome).1 hjudgment
    rw [data.promotionKey_invariant descriptorMap unit reference leftIso,
      data.promotionKey_invariant descriptorMap unit reference rightIso] at hkey
    exact hkey
  · rintro ⟨reference, href, hjudgment⟩
    refine ⟨reference, href, ?_⟩
    apply (data.judgment_characterizes descriptorMap unit reference
      left right outcome).2
    have hkey := (data.judgment_characterizes descriptorMap unit reference
      left' right' outcome).1 hjudgment
    rw [data.promotionKey_invariant descriptorMap unit reference leftIso,
      data.promotionKey_invariant descriptorMap unit reference rightIso]
    exact hkey

/-- All nine rule slots are representation-invariant once Rule 6 is supplied by promotion keys. -/
theorem representationInvariant (data : Rule6PromotionSemantics Atom Unit) :
    RepresentationInvariant data.toStereochemicalProblemData.toProblem :=
  data.toStereochemicalProblemData.representationInvariant_of_rule6
    data.rule6RepresentationInvariant

end Rule6PromotionSemantics

/-! ## Assembly with ordinary Rules 1a--5 -/

/-- A Rule-6 promotion semantics together with opponent-independent keys for the ordinary rule
slots.  This is the direct construction interface for `CoherentProblemData`. -/
structure OrdinaryKeyedRule6PromotionSemantics (Atom Unit : Type u)
    [Fintype Atom] [DecidableEq Atom]
    extends Rule6PromotionSemantics Atom Unit where
  ordinaryKey : DescriptorMap Unit → Unit → SequenceRule → Fin 4 → RuleKey
  ordinaryKey_characterizes :
    ∀ descriptorMap rule, rule ≠ SequenceRule.rule6ReferencePromotion →
      ∀ unit left right outcome,
        toRule6PromotionSemantics.toStereochemicalProblemData.toProblem.RuleOutcome
            descriptorMap rule unit left right outcome ↔
          OrderedKeyOutcome (ordinaryKey descriptorMap unit rule left)
            (ordinaryKey descriptorMap unit rule right) outcome

namespace OrdinaryKeyedRule6PromotionSemantics

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]

def toCoherentProblemData (data : OrdinaryKeyedRule6PromotionSemantics Atom Unit) :
    CoherentProblemData Atom Unit where
  toStereochemicalProblemData :=
    data.toRule6PromotionSemantics.toStereochemicalProblemData
  ordinaryKey := fun descriptorMap unit rule ligand =>
    data.ordinaryKey descriptorMap unit rule ligand
  ordinaryKey_characterizes := data.ordinaryKey_characterizes
  rule6Key := fun descriptorMap unit ligand =>
    data.ligandKey descriptorMap unit ligand
  rule6Key_characterizes :=
    data.toRule6PromotionSemantics.ruleOutcome_iff_orderedKeyOutcome
  rule6_promotion_independent := data.toRule6PromotionSemantics.promotionIndependent

/-- Concrete assembly result: the combined ordinary and promotion semantics has a global total
preorder for every candidate descriptor map. -/
theorem priorityIsTotalPreorder
    (data : OrdinaryKeyedRule6PromotionSemantics Atom Unit)
    (descriptorMap : DescriptorMap Unit) :
    PriorityIsTotalPreorder
      data.toRule6PromotionSemantics.toStereochemicalProblemData.toProblem descriptorMap :=
  (data.toCoherentProblemData).priorityIsTotalPreorder descriptorMap

theorem representationInvariant
    (data : OrdinaryKeyedRule6PromotionSemantics Atom Unit) :
    RepresentationInvariant
      data.toRule6PromotionSemantics.toStereochemicalProblemData.toProblem :=
  data.toRule6PromotionSemantics.representationInvariant

end OrdinaryKeyedRule6PromotionSemantics

/-! ## Chemically contextual assembly -/

/-- Concrete instantiation interface respecting rule applicability.  Ordinary keys characterize a
rule only after all earlier rules tie; Rule 6 is supplied by `Rule6PromotionSemantics` and therefore
has an unconditional unary ligand key. -/
structure ContextualOrdinaryKeyedRule6PromotionSemantics (Atom Unit : Type u)
    [Fintype Atom] [DecidableEq Atom]
    extends Rule6PromotionSemantics Atom Unit where
  ordinaryKey : DescriptorMap Unit → Unit → SequenceRule → Fin 4 → RuleKey
  ordinaryKey_characterizes :
    ∀ descriptorMap rule, rule ≠ SequenceRule.rule6ReferencePromotion →
      ∀ unit left right outcome,
        toRule6PromotionSemantics.toStereochemicalProblemData.toProblem.EarlierRulesTie
          descriptorMap rule unit left right →
        (toRule6PromotionSemantics.toStereochemicalProblemData.toProblem.RuleOutcome
            descriptorMap rule unit left right outcome ↔
          OrderedKeyOutcome (ordinaryKey descriptorMap unit rule left)
            (ordinaryKey descriptorMap unit rule right) outcome)
  ordinary_eq_refl :
    ∀ descriptorMap rule, rule ≠ SequenceRule.rule6ReferencePromotion →
      ∀ unit ligand,
        toRule6PromotionSemantics.toStereochemicalProblemData.toProblem.RuleOutcome
          descriptorMap rule unit ligand ligand Ordering.eq
  earlier_symm :
    ∀ descriptorMap rule unit left right,
      toRule6PromotionSemantics.toStereochemicalProblemData.toProblem.EarlierRulesTie
          descriptorMap rule unit left right →
        toRule6PromotionSemantics.toStereochemicalProblemData.toProblem.EarlierRulesTie
          descriptorMap rule unit right left
  earlier_trans :
    ∀ descriptorMap rule unit first second third,
      toRule6PromotionSemantics.toStereochemicalProblemData.toProblem.EarlierRulesTie
          descriptorMap rule unit first second →
      toRule6PromotionSemantics.toStereochemicalProblemData.toProblem.EarlierRulesTie
          descriptorMap rule unit second third →
        toRule6PromotionSemantics.toStereochemicalProblemData.toProblem.EarlierRulesTie
          descriptorMap rule unit first third

namespace ContextualOrdinaryKeyedRule6PromotionSemantics

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]

def completeRuleKeyModel
    (data : ContextualOrdinaryKeyedRule6PromotionSemantics Atom Unit)
    (descriptorMap : DescriptorMap Unit) :
    ContextualCompleteRuleKeyModel
      data.toRule6PromotionSemantics.toStereochemicalProblemData.toProblem descriptorMap where
  key := fun unit rule ligand =>
    if rule = SequenceRule.rule6ReferencePromotion then
      data.ligandKey descriptorMap unit ligand
    else data.ordinaryKey descriptorMap unit rule ligand
  characterizes := by
    intro rule unit left right outcome hearlier
    by_cases hrule : rule = SequenceRule.rule6ReferencePromotion
    · subst rule
      simpa using data.toRule6PromotionSemantics.ruleOutcome_iff_orderedKeyOutcome
        descriptorMap unit left right outcome
    · simpa [hrule] using
        data.ordinaryKey_characterizes descriptorMap rule hrule
          unit left right outcome hearlier
  eq_refl := by
    intro rule unit ligand
    by_cases hrule : rule = SequenceRule.rule6ReferencePromotion
    · subst rule
      apply (data.toRule6PromotionSemantics.ruleOutcome_iff_orderedKeyOutcome
        descriptorMap unit ligand ligand Ordering.eq).2
      exact OrderedKeyOutcome.eq_refl _
    · exact data.ordinary_eq_refl descriptorMap rule hrule unit ligand
  earlier_symm := data.earlier_symm descriptorMap
  earlier_trans := data.earlier_trans descriptorMap

/-- Actual contextual assembly theorem for revised CIP: ordinary prefix-coherent keys plus the
reference-independent Rule-6 promotion key yield the complete global total preorder. -/
theorem priorityIsTotalPreorder
    (data : ContextualOrdinaryKeyedRule6PromotionSemantics Atom Unit)
    (descriptorMap : DescriptorMap Unit) :
    PriorityIsTotalPreorder
      data.toRule6PromotionSemantics.toStereochemicalProblemData.toProblem descriptorMap :=
  (data.completeRuleKeyModel descriptorMap).priorityIsTotalPreorder

theorem promotionIndependent
    (data : ContextualOrdinaryKeyedRule6PromotionSemantics Atom Unit) :
    Rule6PromotionIndependent
      data.toRule6PromotionSemantics.toStereochemicalProblemData.toProblem :=
  data.toRule6PromotionSemantics.promotionIndependent

theorem representationInvariant
    (data : ContextualOrdinaryKeyedRule6PromotionSemantics Atom Unit) :
    RepresentationInvariant
      data.toRule6PromotionSemantics.toStereochemicalProblemData.toProblem :=
  data.toRule6PromotionSemantics.representationInvariant

end ContextualOrdinaryKeyedRule6PromotionSemantics

end
end DeclarativeCIP
end OneCenter
end TetraStereo
