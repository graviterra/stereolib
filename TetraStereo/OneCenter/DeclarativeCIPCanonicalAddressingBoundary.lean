import TetraStereo.OneCenter.DeclarativeCIPConstitutional

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section

/-!
# The canonical-addressing boundary

`RootedDigraph.Addressing` deliberately permits arbitrary natural-number names for sibling slots.
That is the right representation-independent primitive, but the family of *all* addressings is not
an admissible canonical family for first-difference constitutional comparison.  This module gives
a finite, kernel-checked counterexample: changing only the sibling-slot names reverses Rule 1a.

Consequently, an end-to-end canonical-addressing theorem must add at least:

* dense sibling slots (to remove irrelevant gaps such as `[0]` versus `[7]`), and
* a complete, independent subtree priority whose ties mean equality of every later observation.

The second condition cannot currently be recovered from `NodeLabel` for every production input:
production Rule 1a includes exact rational mancude/Kekule averages, while `NodeLabel` retains only
an atom and provenance.  The counterexample below concerns the logically prior slot-permutation
problem and does not depend on that additional observation-carrier gap.
-/

inductive AddressingForkNode where
  | root
  | high
  | low
  deriving DecidableEq

instance : Fintype AddressingForkNode where
  elems := {.root, .high, .low}
  complete := by
    intro node
    cases node <;> simp

namespace AddressingForkNode

def child : AddressingForkNode → AddressingForkNode → Prop
  | .root, .high => True
  | .root, .low => True
  | _, _ => False

instance : DecidableRel child := fun parent node => by
  cases parent <;> cases node <;> simp only [child] <;> infer_instance

def depth : AddressingForkNode → ℕ
  | .root => 0
  | .high | .low => 1

def atom : AddressingForkNode → Fin 2
  | .root | .low => 0
  | .high => 1

def graph : RootedDigraph (Fin 2) where
  Node := AddressingForkNode
  nodeFintype := inferInstance
  root := .root
  child := child
  label := fun node => ⟨some node.atom, .realAtom⟩
  depth := depth
  root_depth := rfl
  child_depth := by
    intro parent node hedge
    cases parent <;> cases node <;> simp_all [child, depth]
  reachable := by
    intro node
    cases node with
    | root => exact .refl
    | high => exact Relation.ReflTransGen.single (by simp [child])
    | low => exact Relation.ReflTransGen.single (by simp [child])

def forwardAddress : AddressingForkNode → List ℕ
  | .root => []
  | .high => [0]
  | .low => [1]

def reverseAddress : AddressingForkNode → List ℕ
  | .root => []
  | .high => [1]
  | .low => [0]

def forward : graph.Addressing where
  address := forwardAddress
  address_injective := by
    intro first second h
    cases first <;> cases second <;> simp_all [forwardAddress]
  root_address := rfl
  child_iff := by
    intro parent node
    cases parent <;> cases node <;> simp [graph, child, forwardAddress]

def reverse : graph.Addressing where
  address := reverseAddress
  address_injective := by
    intro first second h
    cases first <;> cases second <;> simp_all [reverseAddress]
  root_address := rfl
  child_iff := by
    intro parent node
    cases parent <;> cases node <;> simp [graph, child, reverseAddress]

@[simp] theorem forward_address_root : forward.address .root = [] := rfl
@[simp] theorem forward_address_high : forward.address .high = [0] := rfl
@[simp] theorem forward_address_low : forward.address .low = [1] := rfl
@[simp] theorem reverse_address_root : reverse.address .root = [] := rfl
@[simp] theorem reverse_address_high : reverse.address .high = [1] := rfl
@[simp] theorem reverse_address_low : reverse.address .low = [0] := rfl

end AddressingForkNode

def addressingForkMolecule : MoleculeGraph (Fin 2) where
  atomZ := fun atom => if atom = 0 then 1 else 8
  bond := fun _ _ => 0
  bond_symm := by simp
  bond_self := by simp

private theorem before_singleton_zero_eq_nil (position : List ℕ)
    (h : HierarchyAddressBefore position [0]) :
    position = [] := by
  unfold HierarchyAddressBefore HierarchyAddressKey at h
  cases position with
  | nil => rfl
  | cons head tail =>
      have hle : (head :: tail).length ≤ 1 := List.head_le_of_lt h
      have hlength : tail.length = 0 := by
        simp only [List.length_cons] at hle
        omega
      have htail : tail = [] := List.eq_nil_of_length_eq_zero hlength
      subst tail
      have hfull : List.Lex (fun first second : ℕ => first < second)
          (1 :: [head]) (1 :: [0]) := by
        apply (List.lt_iff_lex_lt (1 :: [head]) (1 :: [0])).1
        simpa using h
      have hlex : List.Lex (fun first second : ℕ => first < second) [head] [0] :=
        List.lex_cons_iff.1 hfull
      have : head < 0 := (List.lex_singleton_iff head 0).1 hlex
      omega

private theorem fork_root_eq :
    ConstitutionalOutcomeAt addressingForkMolecule
      ConstitutionalRule.rule1aAtomicNumber
      AddressingForkNode.graph AddressingForkNode.forward
      AddressingForkNode.graph AddressingForkNode.reverse [] Ordering.eq := by
  refine ⟨some (AddressingForkNode.graph.label .root),
    some (AddressingForkNode.graph.label .root), ?_, ?_, ?_⟩
  · left
    exact ⟨.root, rfl, rfl⟩
  · left
    exact ⟨.root, rfl, rfl⟩
  · exact DescendingNatOutcome.eq rfl

private theorem fork_at_zero_gt :
    ConstitutionalOutcomeAt addressingForkMolecule
      ConstitutionalRule.rule1aAtomicNumber
      AddressingForkNode.graph AddressingForkNode.forward
      AddressingForkNode.graph AddressingForkNode.reverse [0] Ordering.gt := by
  refine ⟨some (AddressingForkNode.graph.label .high),
    some (AddressingForkNode.graph.label .low), ?_, ?_, ?_⟩
  · left
    exact ⟨.high, rfl, rfl⟩
  · left
    exact ⟨.low, rfl, rfl⟩
  · exact DescendingNatOutcome.gt (by decide)

/-- The same finite rooted hierarchy strictly outranks itself if the left and right copies use
opposite sibling-slot names.  Hence the family of all `Addressing`s is not comparison independent.
-/
theorem rule1a_not_allAddressings_independent :
    ConstitutionalHierarchyOutcome addressingForkMolecule
      ConstitutionalRule.rule1aAtomicNumber
      AddressingForkNode.graph AddressingForkNode.forward
      AddressingForkNode.graph AddressingForkNode.reverse Ordering.gt := by
  refine ⟨[0], fork_at_zero_gt, ?_⟩
  intro earlier hearlier
  rw [before_singleton_zero_eq_nil earlier hearlier]
  exact fork_root_eq

/-- Reversing the two addressings reverses the result, so the discrepancy is not merely a failure
to prove equality: both strict outcomes are inhabited.
-/
theorem rule1a_not_allAddressings_independent_reverse :
    ConstitutionalHierarchyOutcome addressingForkMolecule
      ConstitutionalRule.rule1aAtomicNumber
      AddressingForkNode.graph AddressingForkNode.reverse
      AddressingForkNode.graph AddressingForkNode.forward Ordering.lt := by
  refine ⟨[0], ?_, ?_⟩
  · refine ⟨some (AddressingForkNode.graph.label .low),
      some (AddressingForkNode.graph.label .high), ?_, ?_, ?_⟩
    · left
      exact ⟨.low, rfl, rfl⟩
    · left
      exact ⟨.high, rfl, rfl⟩
    · exact DescendingNatOutcome.lt (by decide)
  · intro earlier hearlier
    rw [before_singleton_zero_eq_nil earlier hearlier]
    refine ⟨some (AddressingForkNode.graph.label .root),
      some (AddressingForkNode.graph.label .root), ?_, ?_, ?_⟩
    · left
      exact ⟨.root, rfl, rfl⟩
    · left
      exact ⟨.root, rfl, rfl⟩
    · exact DescendingNatOutcome.eq rfl

/-- In the exact quantifier shape used by `ConstitutionalProblemData.AddressingIndependent`, the
family containing every parent-preserving addressing fails.  Any admissibility predicate used for
canonical constitutional outcomes therefore has to exclude at least one of these two sibling
orders (unless the siblings' complete constitutional observations tie). -/
theorem rule1a_allAddressings_not_independent :
    ¬ ∀ firstLeft firstRight secondLeft secondRight firstOutcome secondOutcome,
      ConstitutionalHierarchyOutcome addressingForkMolecule
          ConstitutionalRule.rule1aAtomicNumber
          AddressingForkNode.graph firstLeft
          AddressingForkNode.graph firstRight firstOutcome →
        ConstitutionalHierarchyOutcome addressingForkMolecule
          ConstitutionalRule.rule1aAtomicNumber
          AddressingForkNode.graph secondLeft
          AddressingForkNode.graph secondRight secondOutcome →
        firstOutcome = secondOutcome := by
  intro independent
  have impossible := independent
    AddressingForkNode.forward AddressingForkNode.reverse
    AddressingForkNode.reverse AddressingForkNode.forward
    Ordering.gt Ordering.lt
    rule1a_not_allAddressings_independent
    rule1a_not_allAddressings_independent_reverse
  cases impossible

end
end DeclarativeCIP
end OneCenter
end TetraStereo
