import TetraStereo.OneCenter.MoleculeGraph

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section

/-!
# Declarative CIP specification kernel

This module is intentionally independent of the executable CIP comparators, hierarchy builders,
descriptor schedulers, stabilization procedures, and refusal paths.  It supplies a proposition-level
surface on which those implementations can later be proved sound and complete.

The kernel separates three things which are easy to conflate in an implementation:

* an admissible finite representation of a rooted hierarchical digraph;
* a rule-local semantic judgment, including an explicit family of Rule-6 promotions;
* a global descriptor map satisfying the priority and orientation judgments simultaneously.

Concrete revised-CIP rule semantics are provided to the kernel as relations, not functions.  In
particular, the definitions below do not assume that rule judgments are decidable, functional,
total, traversal-independent, or promotion-independent.  Those are named proof obligations rather
than hidden premises of `CIPSpec`.
-/

universe u

/-! ## Finite rooted hierarchical digraphs -/

/-- Why a node occurs in a declarative CIP hierarchical digraph. -/
inductive NodeProvenance where
  | realAtom
  | multipleBondDuplicate (duplicateRootDistance : ℕ)
  | ringDuplicate (duplicateRootDistance : ℕ)
  | phantom (rootDistance : ℕ)
  | lonePair (rootDistance : ℕ)
  | auxiliary (rootDistance : ℕ)
  deriving DecidableEq, Repr

/-- A representation-independent semantic label for a hierarchical-digraph node.

`atom?` identifies the molecular atom represented by a real or duplicate node.  Explicit phantom,
lone-pair, and auxiliary nodes may have no molecular atom. -/
structure NodeLabel (Atom : Type u) where
  atom? : Option Atom
  provenance : NodeProvenance

/-- A finite rooted, depth-graded digraph.

The positive depth step makes the child relation well-founded without choosing a traversal order.
Every node is required to be reachable from the root.  The structure deliberately does not choose
an array layout, sibling order, breadth-first frontier, comparison fuel, or canonical atom names. -/
structure RootedDigraph (Atom : Type u) where
  Node : Type u
  nodeFintype : Fintype Node
  root : Node
  child : Node → Node → Prop
  label : Node → NodeLabel Atom
  depth : Node → ℕ
  root_depth : depth root = 0
  child_depth : ∀ {parent node}, child parent node → depth node = depth parent + 1
  reachable : ∀ node, Relation.ReflTransGen child root node

namespace RootedDigraph

variable {Atom : Type u}

/-- The child relation is well-founded solely from the declarative depth grading. -/
theorem child_wellFounded (graph : RootedDigraph Atom) :
    WellFounded graph.child := by
  refine Subrelation.wf ?_ (InvImage.wf graph.depth (Nat.lt_wfRel).2)
  intro parent node hedge
  show graph.depth parent < graph.depth node
  rw [graph.child_depth hedge]
  exact Nat.lt_succ_self _

/-- Isomorphism of rooted hierarchical-digraph representations. -/
structure Iso (left right : RootedDigraph Atom) where
  toEquiv : left.Node ≃ right.Node
  map_root : toEquiv left.root = right.root
  map_child : ∀ a b, left.child a b ↔ right.child (toEquiv a) (toEquiv b)
  map_label : ∀ node, left.label node = right.label (toEquiv node)
  map_depth : ∀ node, left.depth node = right.depth (toEquiv node)

/-- Every rooted digraph representation is isomorphic to itself. -/
def Iso.refl (graph : RootedDigraph Atom) : Iso graph graph where
  toEquiv := Equiv.refl graph.Node
  map_root := rfl
  map_child := by simp
  map_label := by simp
  map_depth := by simp

/-- Rooted-digraph isomorphism is symmetric. -/
def Iso.symm {left right : RootedDigraph Atom} (iso : Iso left right) : Iso right left where
  toEquiv := iso.toEquiv.symm
  map_root := by
    apply iso.toEquiv.injective
    simp [iso.map_root]
  map_child := by
    intro a b
    simpa using (iso.map_child (iso.toEquiv.symm a) (iso.toEquiv.symm b)).symm
  map_label := by
    intro node
    simpa using (iso.map_label (iso.toEquiv.symm node)).symm
  map_depth := by
    intro node
    simpa using (iso.map_depth (iso.toEquiv.symm node)).symm

/-- Rooted-digraph isomorphism is transitive. -/
def Iso.trans {first second third : RootedDigraph Atom}
    (left : Iso first second) (right : Iso second third) : Iso first third where
  toEquiv := left.toEquiv.trans right.toEquiv
  map_root := by simp [left.map_root, right.map_root]
  map_child := by
    intro a b
    exact (left.map_child a b).trans (right.map_child (left.toEquiv a) (left.toEquiv b))
  map_label := by
    intro node
    exact (left.map_label node).trans (right.map_label (left.toEquiv node))
  map_depth := by
    intro node
    exact (left.map_depth node).trans (right.map_depth (left.toEquiv node))

end RootedDigraph

/-! ## Rules and descriptor maps -/

/-- Revised-CIP rule slots in semantic evaluation order, including proposed Rule 6. -/
inductive SequenceRule where
  | rule1aAtomicNumber
  | rule1bDuplicateNodeProximity
  | rule2AtomicMass
  | rule3DoubleBondGeometry
  | rule4aStereogenicUnitKind
  | rule4bLikeUnlikeDescriptorPairs
  | rule4cPseudoasymmetricDescriptor
  | rule5EnantiomorphicDescriptor
  | rule6ReferencePromotion
  deriving DecidableEq, Repr

namespace SequenceRule

/-- Zero-based semantic precedence of revised-CIP rule slots. -/
def rank : SequenceRule → ℕ
  | rule1aAtomicNumber => 0
  | rule1bDuplicateNodeProximity => 1
  | rule2AtomicMass => 2
  | rule3DoubleBondGeometry => 3
  | rule4aStereogenicUnitKind => 4
  | rule4bLikeUnlikeDescriptorPairs => 5
  | rule4cPseudoasymmetricDescriptor => 6
  | rule5EnantiomorphicDescriptor => 7
  | rule6ReferencePromotion => 8

/-- One rule precedes another exactly when its semantic rank is smaller. -/
def Before (earlier later : SequenceRule) : Prop :=
  earlier.rank < later.rank

theorem before_trans {first second third : SequenceRule}
    (h₁ : first.Before second) (h₂ : second.Before third) :
    first.Before third :=
  Nat.lt_trans h₁ h₂

end SequenceRule

/-- Descriptor values emitted by the independent specification.

The type contains final stereodescriptors rather than the implementation's intermediate Rule-3/4/5
context records. -/
inductive Descriptor where
  | R | S
  | r | s
  | Ra | Sa
  | Rp | Sp
  | M | P
  | E | Z
  | seqCis | seqTrans
  deriving DecidableEq, Repr

namespace Descriptor

/-- Semantic action of mirror reflection on descriptor symbols. -/
def mirror : Descriptor → Descriptor
  | R => S
  | S => R
  | r => r
  | s => s
  | Ra => Sa
  | Sa => Ra
  | Rp => Sp
  | Sp => Rp
  | M => P
  | P => M
  | E => E
  | Z => Z
  | seqCis => seqTrans
  | seqTrans => seqCis

@[simp] theorem mirror_mirror (descriptor : Descriptor) :
    mirror (mirror descriptor) = descriptor := by
  cases descriptor <;> rfl

end Descriptor

/-- A partial assignment of final descriptors to stereochemical units. -/
abbrev DescriptorMap (Unit : Type u) := Unit → Option Descriptor

/-! ## A declarative semantic problem -/

/-- Independent semantic input consumed by `CIPSpec`.

The fields ending in `Judgment` are propositions.  They describe what a rule or orientation means;
they do not prescribe how to compute it.

`ordinaryRuleJudgment` is ignored for Rule 6.  Rule 6 instead ranges over
`admissibleRule6Reference` and `rule6Judgment`, so promotion independence has a direct statement.
-/
structure Problem (Atom Unit : Type u) [Fintype Atom] [DecidableEq Atom] where
  molecule : MoleculeGraph Atom
  ligandAtom : Unit → Fin 4 → Atom
  admissibleExpansion : Unit → Fin 4 → RootedDigraph Atom → Prop
  ordinaryRuleJudgment :
    DescriptorMap Unit → SequenceRule → Unit →
      RootedDigraph Atom → RootedDigraph Atom → Ordering → Prop
  admissibleRule6Reference : DescriptorMap Unit → Unit → Atom → Prop
  rule6Judgment :
    DescriptorMap Unit → Unit → Atom →
      RootedDigraph Atom → RootedDigraph Atom → Ordering → Prop
  /-- Descriptor dependencies are directed from the unit being assigned to the auxiliary unit it
  consults. -/
  dependsOn : DescriptorMap Unit → Unit → Unit → Prop
  /-- Geometric/orientational descriptor judgment after the four ligand positions have been placed
  in decreasing priority order. -/
  orientationJudgment : Unit → Equiv.Perm (Fin 4) → Descriptor → Prop

namespace Problem

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]

/-- Rule-local outcome on two particular admissible digraph representations. -/
def OutcomeOnGraphs (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit)
    (rule : SequenceRule) (unit : Unit) (left right : RootedDigraph Atom)
    (outcome : Ordering) : Prop :=
  match rule with
  | SequenceRule.rule6ReferencePromotion =>
      ∃ reference,
        problem.admissibleRule6Reference descriptorMap unit reference ∧
          problem.rule6Judgment descriptorMap unit reference left right outcome
  | _ => problem.ordinaryRuleJudgment descriptorMap rule unit left right outcome

/-- A rule outcome for two ligand positions must hold for every admissible representation of both
rooted digraphs.  Existence of such representations is required separately by `CIPSpec`. -/
def RuleOutcome (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit)
    (rule : SequenceRule) (unit : Unit) (left right : Fin 4) (outcome : Ordering) : Prop :=
  ∀ leftGraph rightGraph,
    problem.admissibleExpansion unit left leftGraph →
      problem.admissibleExpansion unit right rightGraph →
        problem.OutcomeOnGraphs descriptorMap rule unit leftGraph rightGraph outcome

/-- All rules preceding `rule` tie on the two ligand positions. -/
def EarlierRulesTie (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit)
    (rule : SequenceRule) (unit : Unit) (left right : Fin 4) : Prop :=
  ∀ earlier, earlier.Before rule →
    problem.RuleOutcome descriptorMap earlier unit left right Ordering.eq

/-- Strict CIP priority: some first rule is decisive after every earlier rule ties. -/
def Higher (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit)
    (unit : Unit) (left right : Fin 4) : Prop :=
  ∃ rule,
    problem.EarlierRulesTie descriptorMap rule unit left right ∧
      problem.RuleOutcome descriptorMap rule unit left right Ordering.gt

/-- Two ligand positions tie when every revised-CIP rule judges them equal. -/
def Tied (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit)
    (unit : Unit) (left right : Fin 4) : Prop :=
  ∀ rule, problem.RuleOutcome descriptorMap rule unit left right Ordering.eq

/-- Weak priority induced by strict priority and a semantic tie. -/
def WeakPriority (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit)
    (unit : Unit) (left right : Fin 4) : Prop :=
  problem.Higher descriptorMap unit left right ∨ problem.Tied descriptorMap unit left right

/-- A permutation ranks the four ligand positions in decreasing declarative CIP priority. -/
def Ranks (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit)
    (unit : Unit) (ranking : Equiv.Perm (Fin 4)) : Prop :=
  ∀ i j : Fin 4, i < j →
    problem.Higher descriptorMap unit (ranking i) (ranking j)

/-- The descriptor permitted at a unit by a complete ligand ranking and the independent orientation
judgment. -/
def DescriptorJudgment (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit)
    (unit : Unit) (descriptor : Descriptor) : Prop :=
  ∃ ranking : Equiv.Perm (Fin 4),
    problem.Ranks descriptorMap unit ranking ∧
      problem.orientationJudgment unit ranking descriptor

end Problem

/-! ## The independent specification relation -/

/-- A descriptor map satisfies the independent declarative CIP specification.

The first conjunct prevents the universal representation-independent rule judgments from becoming
vacuous.  The second says that the map contains exactly the descriptors licensed by a complete
priority ranking and the independent orientation judgment.  Because descriptor judgments may
consult the whole map, this is a simultaneous relational fixed-point specification, not an
iteration algorithm. -/
def CIPSpec {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
    (problem : Problem Atom Unit) (descriptorMap : DescriptorMap Unit) : Prop :=
  (∀ unit ligand, ∃ graph, problem.admissibleExpansion unit ligand graph) ∧
    (∀ unit descriptor,
      descriptorMap unit = some descriptor ↔
        problem.DescriptorJudgment descriptorMap unit descriptor)

namespace CIPSpec

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
variable {problem : Problem Atom Unit} {descriptorMap : DescriptorMap Unit}

/-- Every ligand of a satisfying specification has an admissible finite rooted digraph. -/
theorem expansion_exists (spec : CIPSpec problem descriptorMap) (unit : Unit) (ligand : Fin 4) :
    ∃ graph, problem.admissibleExpansion unit ligand graph :=
  spec.1 unit ligand

/-- Every descriptor recorded by a satisfying map has a declarative derivation. -/
theorem descriptor_sound (spec : CIPSpec problem descriptorMap) {unit : Unit}
    {descriptor : Descriptor} (h : descriptorMap unit = some descriptor) :
    problem.DescriptorJudgment descriptorMap unit descriptor :=
  (spec.2 unit descriptor).1 h

/-- Every declaratively derivable descriptor is recorded by a satisfying map. -/
theorem descriptor_complete (spec : CIPSpec problem descriptorMap) {unit : Unit}
    {descriptor : Descriptor}
    (h : problem.DescriptorJudgment descriptorMap unit descriptor) :
    descriptorMap unit = some descriptor :=
  (spec.2 unit descriptor).2 h

/-- A satisfying map cannot derive two different descriptors at the same unit. -/
theorem descriptor_unique (spec : CIPSpec problem descriptorMap) {unit : Unit}
    {first second : Descriptor}
    (hfirst : problem.DescriptorJudgment descriptorMap unit first)
    (hsecond : problem.DescriptorJudgment descriptorMap unit second) :
    first = second := by
  have h₁ := spec.descriptor_complete hfirst
  have h₂ := spec.descriptor_complete hsecond
  exact Option.some.inj (h₁.symm.trans h₂)

/-- A unit is unassigned exactly when no final descriptor has a declarative derivation. -/
theorem descriptor_eq_none_iff (spec : CIPSpec problem descriptorMap) (unit : Unit) :
    descriptorMap unit = none ↔
      ¬ ∃ descriptor, problem.DescriptorJudgment descriptorMap unit descriptor := by
  constructor
  · intro hnone ⟨descriptor, hdescriptor⟩
    have := spec.descriptor_complete hdescriptor
    simp [hnone] at this
  · intro hnone
    cases hvalue : descriptorMap unit with
    | none => rfl
    | some descriptor =>
        exfalso
        exact hnone ⟨descriptor, spec.descriptor_sound hvalue⟩

end CIPSpec

/-! ## Named global proof obligations -/

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]

/-- Rule meanings do not depend on the chosen finite representation of either rooted digraph. -/
def RepresentationInvariant (problem : Problem Atom Unit) : Prop :=
  ∀ descriptorMap rule unit left left' right right' outcome,
    RootedDigraph.Iso left left' →
      RootedDigraph.Iso right right' →
        (problem.OutcomeOnGraphs descriptorMap rule unit left right outcome ↔
          problem.OutcomeOnGraphs descriptorMap rule unit left' right' outcome)

/-- Every admissible Rule-6 promotion gives the same comparison outcome. -/
def Rule6PromotionIndependent (problem : Problem Atom Unit) : Prop :=
  ∀ descriptorMap unit reference₁ reference₂ left right outcome₁ outcome₂,
    problem.admissibleRule6Reference descriptorMap unit reference₁ →
      problem.admissibleRule6Reference descriptorMap unit reference₂ →
        problem.rule6Judgment descriptorMap unit reference₁ left right outcome₁ →
          problem.rule6Judgment descriptorMap unit reference₂ left right outcome₂ →
            outcome₁ = outcome₂

/-- The outer-to-inner auxiliary dependency relation is well-founded. -/
def AuxiliaryDependenciesWellFounded (problem : Problem Atom Unit)
    (descriptorMap : DescriptorMap Unit) : Prop :=
  WellFounded (fun inner outer => problem.dependsOn descriptorMap outer inner)

/-- The weak ligand-priority relation is reflexive, transitive, and total at every unit. -/
def PriorityIsTotalPreorder (problem : Problem Atom Unit)
    (descriptorMap : DescriptorMap Unit) : Prop :=
  (∀ unit ligand, problem.WeakPriority descriptorMap unit ligand ligand) ∧
    (∀ unit a b c,
      problem.WeakPriority descriptorMap unit a b →
        problem.WeakPriority descriptorMap unit b c →
          problem.WeakPriority descriptorMap unit a c) ∧
    (∀ unit a b,
      problem.WeakPriority descriptorMap unit a b ∨
        problem.WeakPriority descriptorMap unit b a)

/-- Every semantic problem admits at least one satisfying global descriptor map. -/
def DescriptorMapExists (problem : Problem Atom Unit) : Prop :=
  ∃ descriptorMap, CIPSpec problem descriptorMap

/-- A semantic problem permits at most one satisfying global descriptor map. -/
def DescriptorMapUnique (problem : Problem Atom Unit) : Prop :=
  ∀ left right, CIPSpec problem left → CIPSpec problem right → left = right

theorem rule6_outcome_unique_of_promotion_independent
    (problem : Problem Atom Unit) (independent : Rule6PromotionIndependent problem)
    (descriptorMap : DescriptorMap Unit) (unit : Unit) (left right : Fin 4)
    (leftGraph rightGraph : RootedDigraph Atom)
    (hleft : problem.admissibleExpansion unit left leftGraph)
    (hright : problem.admissibleExpansion unit right rightGraph)
    {first second : Ordering}
    (hfirst : problem.RuleOutcome descriptorMap SequenceRule.rule6ReferencePromotion
      unit left right first)
    (hsecond : problem.RuleOutcome descriptorMap SequenceRule.rule6ReferencePromotion
      unit left right second) :
    first = second := by
  rcases hfirst leftGraph rightGraph hleft hright with ⟨reference₁, href₁, hout₁⟩
  rcases hsecond leftGraph rightGraph hleft hright with ⟨reference₂, href₂, hout₂⟩
  exact independent descriptorMap unit reference₁ reference₂ leftGraph rightGraph first second
    href₁ href₂ hout₁ hout₂

end
end DeclarativeCIP
end OneCenter
end TetraStereo
