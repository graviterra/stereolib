import TetraStereo.UniversalProof.NextFrontier.NativeGeneratedRealNodeInventory
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeGlobalProfileInventory

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeGeneratedRealNodeInventory











def advance (mol : RawMolecule) : Nat → List CanonicalBranchNode → List CanonicalBranchNode
  | 0, nodes => nodes
  | level + 1, nodes => advance mol level (nodes.flatMap mol.canonicalChildren)

def frontier (mol : RawMolecule) (root level : Nat) : List CanonicalBranchNode :=
  advance mol level [canonicalCenterRoot root]

def inventoryFor (mol : RawMolecule) (nodes : List CanonicalBranchNode) (fuel : Nat) :
    List CanonicalBranchNode :=
  (List.range fuel).flatMap (fun level => advance mol level nodes)

def inventory (mol : RawMolecule) (root fuel : Nat) : List CanonicalBranchNode :=
  inventoryFor mol [canonicalCenterRoot root] fuel

/-- Successive iteration is the actual flatMap of canonical children. -/
theorem advance_succ (mol : RawMolecule) (level : Nat) (nodes : List CanonicalBranchNode) :
    advance mol (level + 1) nodes = (advance mol level nodes).flatMap mol.canonicalChildren := by
  induction level generalizing nodes with
  | zero => rfl
  | succ level ih => exact ih (nodes.flatMap mol.canonicalChildren)

/-- Every iterated frontier member has genuine original-root generation. -/
theorem frontier_generated {mol : RawMolecule} {root level : Nat} {node : CanonicalBranchNode}
    (member : node ∈ frontier mol root level) : CanonicalCenterTreeNode mol root node := by
  induction level generalizing node with
  | zero =>
      change node ∈ [canonicalCenterRoot root] at member
      have same := List.mem_singleton.mp member
      subst node
      exact CanonicalCenterTreeNode.root
  | succ level ih =>
      change node ∈ advance mol (level + 1) [canonicalCenterRoot root] at member
      rw [advance_succ] at member
      obtain ⟨parent, parentMember, childMember⟩ := List.mem_flatMap.mp member
      exact CanonicalCenterTreeNode.child (ih parentMember) childMember

/-- Discovery-history length separates all actual breadth levels. -/
theorem frontier_history_length {mol : RawMolecule} {root level : Nat}
    {node : CanonicalBranchNode} (member : node ∈ frontier mol root level) :
    node.history.length = level + 1 := by
  induction level generalizing node with
  | zero =>
      change node ∈ [canonicalCenterRoot root] at member
      have same := List.mem_singleton.mp member
      subst node
      rfl
  | succ level ih =>
      change node ∈ advance mol (level + 1) [canonicalCenterRoot root] at member
      rw [advance_succ] at member
      obtain ⟨parent, parentMember, childMember⟩ := List.mem_flatMap.mp member
      have childLength := child_history_length childMember
      have parentLength := ih parentMember
      omega

/-- Local all-real child observations entail all-real genuine generation. -/
theorem generated_real_of_children_real {mol : RawMolecule} {root : Nat}
    (childrenReal : ∀ parent, CanonicalCenterTreeNode mol root parent →
      ∀ child ∈ mol.canonicalChildren parent, child.provenance = .realAtom)
    {node : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root node) :
    node.provenance = .realAtom := by
  cases generated with
  | root => rfl
  | @child parent child parentGenerated member =>
      exact childrenReal parent parentGenerated _ member

/-- Distinct genuine parents cannot share an actual child: stored parent atom
and accepted real-node identity recover the entire original parent. -/
theorem children_disjoint_of_distinct_parents {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root : Nat} (rootBound : root < mol.atomCount)
    {left right : CanonicalBranchNode}
    (leftGenerated : CanonicalCenterTreeNode mol root left)
    (rightGenerated : CanonicalCenterTreeNode mol root right) (different : left ≠ right) :
    List.Disjoint (mol.canonicalChildren left) (mol.canonicalChildren right) := by
  intro child leftMember rightMember
  have sameAtom : left.atom = right.atom :=
    (canonical_children_parent leftMember).symm.trans (canonical_children_parent rightMember)
  exact different (generated_real_node_unique tree rootBound leftGenerated rightGenerated
    (real_of_child_mem leftMember) (real_of_child_mem rightMember) sameAtom)

/-- Local child Nodup propagates through the actual finite frontier iteration. -/
theorem frontier_nodup {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount)
    (childrenNodup : ∀ parent, CanonicalCenterTreeNode mol root parent →
      (mol.canonicalChildren parent).Nodup) (level : Nat) :
    (frontier mol root level).Nodup := by
  induction level with
  | zero => simp [frontier, advance]
  | succ level ih =>
      change ((advance mol (level + 1) [canonicalCenterRoot root])).Nodup
      rw [advance_succ]
      apply List.nodup_flatMap.mpr
      refine ⟨?_, List.Pairwise.imp_of_mem ?_ ih⟩
      · intro parent member
        exact childrenNodup parent (frontier_generated member)
      · intro left right leftMember rightMember different
        exact children_disjoint_of_distinct_parents tree rootBound
          (frontier_generated leftMember) (frontier_generated rightMember) different

/-- Different levels are disjoint by their original history lengths. -/
theorem frontiers_disjoint {mol : RawMolecule} {root leftLevel rightLevel : Nat}
    (different : leftLevel ≠ rightLevel) :
    List.Disjoint (frontier mol root leftLevel) (frontier mol root rightLevel) := by
  intro node leftMember rightMember
  have leftLength := frontier_history_length leftMember
  have rightLength := frontier_history_length rightMember
  apply different
  omega

/-- Concatenating any number of actual levels has no repeated original node.
This is a global statement, rather than a separate bound on each frontier. -/
theorem inventory_nodes_nodup {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount)
    (childrenNodup : ∀ parent, CanonicalCenterTreeNode mol root parent →
      (mol.canonicalChildren parent).Nodup) (fuel : Nat) :
    (inventory mol root fuel).Nodup := by
  change ((List.range fuel).flatMap (frontier mol root)).Nodup
  apply List.nodup_flatMap.mpr
  refine ⟨?_, (List.nodup_range : (List.range fuel).Nodup).imp ?_⟩
  · intro level _member
    exact frontier_nodup tree rootBound childrenNodup level
  · intro leftLevel rightLevel different
    exact frontiers_disjoint different

/-- Actual real-node identity makes the whole concatenated atom inventory Nodup. -/
theorem inventory_atoms_nodup {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount)
    (childrenNodup : ∀ parent, CanonicalCenterTreeNode mol root parent →
      (mol.canonicalChildren parent).Nodup)
    (childrenReal : ∀ parent, CanonicalCenterTreeNode mol root parent →
      ∀ child ∈ mol.canonicalChildren parent, child.provenance = .realAtom) (fuel : Nat) :
    ((inventory mol root fuel).map CanonicalBranchNode.atom).Nodup := by
  apply List.Nodup.map_on ?_ (inventory_nodes_nodup tree rootBound childrenNodup fuel)
  intro left leftMember right rightMember sameAtom
  obtain ⟨leftLevel, _leftRange, leftFrontier⟩ := List.mem_flatMap.mp leftMember
  obtain ⟨rightLevel, _rightRange, rightFrontier⟩ := List.mem_flatMap.mp rightMember
  have leftGenerated := frontier_generated leftFrontier
  have rightGenerated := frontier_generated rightFrontier
  exact generated_real_node_unique tree rootBound leftGenerated rightGenerated
    (generated_real_of_children_real childrenReal leftGenerated)
    (generated_real_of_children_real childrenReal rightGenerated) sameAtom

/-- The total visited inventory, across all levels, is bounded by physical atom count. -/
theorem inventory_length_le_atomCount {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount)
    (childrenNodup : ∀ parent, CanonicalCenterTreeNode mol root parent →
      (mol.canonicalChildren parent).Nodup)
    (childrenReal : ∀ parent, CanonicalCenterTreeNode mol root parent →
      ∀ child ∈ mol.canonicalChildren parent, child.provenance = .realAtom) (fuel : Nat) :
    (inventory mol root fuel).length ≤ mol.atomCount := by
  have atomNodup := inventory_atoms_nodup tree rootBound childrenNodup childrenReal fuel
  have subset : ((inventory mol root fuel).map CanonicalBranchNode.atom).toFinset ⊆
      Finset.range mol.atomCount := by
    intro atom member
    rcases List.mem_map.mp (List.mem_toFinset.mp member) with ⟨node, nodeMember, rfl⟩
    obtain ⟨level, _levelRange, frontierMember⟩ := List.mem_flatMap.mp nodeMember
    have generated := frontier_generated frontierMember
    have real := generated_real_of_children_real childrenReal generated
    have bounds := (generated.real_history rootBound tree.wellFormed real).2
    exact Finset.mem_range.mpr (bounds node.atom (List.mem_of_head? generated.history_head))
  have cardBound := Finset.card_le_card subset
  simpa only [List.toFinset_card_of_nodup atomNodup, List.length_map,
    Finset.card_range] using cardBound

/-- History length forces every frontier at or beyond atom count to be empty. -/
theorem frontier_empty_at_atomCount {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount)
    (childrenReal : ∀ parent, CanonicalCenterTreeNode mol root parent →
      ∀ child ∈ mol.canonicalChildren parent, child.provenance = .realAtom)
    {level : Nat} (beyond : mol.atomCount ≤ level) : frontier mol root level = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro node member
  have generated := frontier_generated member
  have real := generated_real_of_children_real childrenReal generated
  have bound := generated_real_history_length_le_inventory tree rootBound generated real
  have length := frontier_history_length member
  omega

/-- Genuine generation is constructively represented in an iterated frontier. -/
theorem generated_mem_some_frontier {mol : RawMolecule} {root : Nat}
    {node : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root node) :
    ∃ level, node ∈ frontier mol root level := by
  induction generated with
  | root => exact ⟨0, List.mem_singleton_self _⟩
  | @child parent child parentGenerated member ih =>
      obtain ⟨level, parentMember⟩ := ih
      refine ⟨level + 1, ?_⟩
      change child ∈ advance mol (level + 1) [canonicalCenterRoot root]
      rw [advance_succ]
      exact List.mem_flatMap.mpr ⟨parent, parentMember, member⟩

/-- The finite atom-count inventory covers every genuine generated occurrence,
including the center sought by the archived profile membership guard. -/
theorem generated_mem_inventory {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount)
    (childrenReal : ∀ parent, CanonicalCenterTreeNode mol root parent →
      ∀ child ∈ mol.canonicalChildren parent, child.provenance = .realAtom)
    {node : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root node) :
    node ∈ inventory mol root mol.atomCount := by
  obtain ⟨level, member⟩ := generated_mem_some_frontier generated
  have bound := generated_real_history_length_le_inventory tree rootBound generated
    (generated_real_of_children_real childrenReal generated)
  have length := frontier_history_length member
  have levelBound : level < mol.atomCount := by omega
  exact List.mem_flatMap.mpr ⟨level, List.mem_range.mpr levelBound, member⟩

def enumerate (mol : RawMolecule) : Nat → List CanonicalBranchNode → List CanonicalBranchNode
  | 0, _ => []
  | fuel + 1, nodes => nodes ++ enumerate mol fuel (nodes.flatMap mol.canonicalChildren)

/-- Literal local replica of the private archived FrameRuntime.collect clauses.
This definition does not identify itself with an installed runtime API. -/
def collectReplica : Nat → Nat → RawMolecule → List CanonicalBranchNode →
    Option (List CanonicalBranchNode)
  | 0, _, _, [] => some []
  | 0, _, _, _ :: _ => none
  | _ + 1, _, _, [] => some []
  | fuel + 1, cap, mol, nodes =>
      if cap < nodes.length then none else do
        let tail ← collectReplica fuel (cap - nodes.length) mol
          (nodes.flatMap mol.canonicalChildren)
        some (nodes ++ tail)

private theorem enumerate_nil (mol : RawMolecule) (fuel : Nat) :
    enumerate mol fuel [] = [] := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [enumerate, List.flatMap_nil, List.nil_append] using ih

/-- Recursive concatenation and concatenation of breadth levels are the same inventory. -/
theorem enumerate_eq_inventoryFor (mol : RawMolecule) (fuel : Nat)
    (nodes : List CanonicalBranchNode) : enumerate mol fuel nodes = inventoryFor mol nodes fuel := by
  induction fuel generalizing nodes with
  | zero => rfl
  | succ fuel ih =>
      rw [enumerate, ih]
      simp only [inventoryFor, List.range_succ_eq_map, List.flatMap_cons,
        List.flatMap_map, advance]

/-- Finite termination and a bound on the entire unrolled inventory entail
collector success. Neither a successful collector nor profile is an input. -/
theorem collectReplica_of_global_budget (mol : RawMolecule) (fuel cap : Nat)
    (nodes : List CanonicalBranchNode)
    (terminal : advance mol fuel nodes = [])
    (budget : (enumerate mol fuel nodes).length ≤ cap) :
    collectReplica fuel cap mol nodes = some (enumerate mol fuel nodes) := by
  induction fuel generalizing cap nodes with
  | zero =>
      change nodes = [] at terminal
      subst nodes
      rfl
  | succ fuel ih =>
      cases nodes with
      | nil => simp only [collectReplica, enumerate_nil]
      | cons first rest =>
          have total : (first :: rest).length +
              (enumerate mol fuel ((first :: rest).flatMap mol.canonicalChildren)).length ≤ cap := by
            simpa only [enumerate, List.length_append] using budget
          have fits : ¬ cap < (first :: rest).length := by omega
          have tailBudget :
              (enumerate mol fuel ((first :: rest).flatMap mol.canonicalChildren)).length ≤
                cap - (first :: rest).length := by omega
          have tailTerminal : advance mol fuel ((first :: rest).flatMap mol.canonicalChildren) = [] :=
            terminal
          have tailCollected := ih (cap - (first :: rest).length)
            ((first :: rest).flatMap mol.canonicalChildren) tailTerminal tailBudget
          simp only [collectReplica, if_neg fits, Bind.bind, Option.bind,
            tailCollected, enumerate]

/-- Actual iteration has a global atom-count budget and terminates before
fuel atomCount+1, under the two explicit local structural obligations. -/
theorem collectReplica_root_success {mol : RawMolecule} (tree : mol.ChronologicalPhysicalTree)
    {root : Nat} (rootBound : root < mol.atomCount)
    (childrenNodup : ∀ parent, CanonicalCenterTreeNode mol root parent →
      (mol.canonicalChildren parent).Nodup)
    (childrenReal : ∀ parent, CanonicalCenterTreeNode mol root parent →
      ∀ child ∈ mol.canonicalChildren parent, child.provenance = .realAtom) :
    collectReplica (mol.atomCount + 1) mol.atomCount mol [canonicalCenterRoot root] =
      some (inventory mol root (mol.atomCount + 1)) := by
  have terminal : advance mol (mol.atomCount + 1) [canonicalCenterRoot root] = [] :=
    frontier_empty_at_atomCount tree rootBound childrenReal (Nat.le_succ _)
  have budget : (enumerate mol (mol.atomCount + 1) [canonicalCenterRoot root]).length ≤
      mol.atomCount := by
    rw [enumerate_eq_inventoryFor]
    exact inventory_length_le_atomCount tree rootBound childrenNodup childrenReal _
  have result := collectReplica_of_global_budget mol (mol.atomCount + 1) mol.atomCount
    [canonicalCenterRoot root] terminal budget
  rw [enumerate_eq_inventoryFor] at result
  exact result

end TetraStereo.UniversalProof.NativeGlobalProfileInventory
