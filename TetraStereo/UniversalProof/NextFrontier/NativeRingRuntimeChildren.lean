import TetraStereo.UniversalProof.NextFrontier.NativeRingRuntimeAtoms
import TetraStereo.UniversalProof.NextFrontier.NativeRingSingleBondChildren

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingRuntimeChildren

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.NativeRingRuntimeGraphFacts
open TetraStereo.UniversalProof.NativeRingRuntimeAtoms
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.NativeRingSingleBondChildren

def rootCursor (atom : Nat) : CanonicalRerootCursor := awayCursor atom 0 []

def armChild (parent atom : Nat) : CanonicalRerootCursor := awayCursor atom parent [0]

def rightPredecessor (n : Nat) : Nat := if n = 0 then 2 else n + 3

private theorem filter_path_children (parent atom : Nat) (ancestors children : List Nat)
    (fresh : ∀ other ∈ children, other ≠ parent) :
    ((children.map fun other => pathNode other (atom :: parent :: ancestors)).filterMap
      fun neighbor => if neighbor == pathNode parent ancestors then none
        else some ({ node := neighbor, previous? := some (pathNode atom (parent :: ancestors)) } :
          CanonicalRerootCursor)) =
      children.map (fun other => awayCursor other atom (parent :: ancestors)) := by
  induction children with
  | nil => rfl
  | cons head rest ih =>
      have different := pathNode_ne head parent (atom :: parent :: ancestors) ancestors
        (fresh head List.mem_cons_self)
      simp only [List.map_cons, List.filterMap_cons, beq_eq_false_iff_ne.mpr different,
        Bool.false_eq_true, ↓reduceIte]
      rw [ih (by intro other member; exact fresh other (List.mem_cons_of_mem head member))]
      rfl

/-- The remembered parent is removed from the actual rerooted children. The ancestry of every
remaining real child is preserved, including the minimal three-carbon ring. -/
theorem actual_away_children (raw : RawMolecule) (atom parent : Nat)
    (ancestors children : List Nat)
    (row : (recordNeighbors raw atom).erase parent = children)
    (single : ∀ other ∈ recordNeighbors raw atom, raw.bondOrder atom other = 1)
    (fresh : ∀ other ∈ children, other ∉ atom :: parent :: ancestors) :
    (awayCursor atom parent ancestors).children raw =
      children.map (fun other => awayCursor other atom (parent :: ancestors)) := by
  have actual := actual_path_children raw atom parent ancestors children row single fresh
  have forced : (pathNode atom (parent :: ancestors)).forcedLeaf = false := rfl
  simp only [awayCursor, CanonicalRerootCursor.children, CanonicalRerootCursor.neighbors,
    forced, Bool.false_eq_true, ↓reduceIte, originalParent_pathNode, actual,
    Option.toList_some, List.singleton_append, List.filterMap_cons, beq_self_eq_true]
  exact filter_path_children parent atom ancestors children (by
    intro other member equal
    subst other
    exact fresh parent member (by simp))

theorem left_erased_records (n : Nat) (parity : TetrahedralInputParity) :
    ((recordNeighbors (expanded n parity) 2).erase 0).Perm [n + 6, 3, 4] := by
  simpa using (expanded_left_records n parity).erase 0

theorem right_erased_records (n : Nat) (parity : TetrahedralInputParity) :
    ((recordNeighbors (expanded n parity) (n + 4)).erase 0).Perm
      [rightPredecessor n, 3 * n + 7, 3 * n + 8] := by
  have erased := (expanded_right_records n parity).erase 0
  cases n <;> simpa [rightPredecessor] using erased

theorem actual_left_children (n : Nat) (parity : TetrahedralInputParity) :
    ((rootCursor 2).children (expanded n parity)).Perm
      [armChild 2 (n + 6), armChild 2 3, armChild 2 4] := by
  let physical := (recordNeighbors (expanded n parity) 2).erase 0
  have projected := left_erased_records n parity
  have actual := actual_away_children (expanded n parity) 2 0 [] physical rfl
    (expanded_record_bond_one n parity 2) (by
      intro other member
      have retained := projected.mem_iff.mp member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at retained
      rcases retained with rfl | rfl | rfl <;> simp)
  rw [show (rootCursor 2).children (expanded n parity) =
    physical.map (fun other => armChild 2 other) from actual]
  exact projected.map (armChild 2)

theorem actual_right_children (n : Nat) (parity : TetrahedralInputParity) :
    ((rootCursor (n + 4)).children (expanded n parity)).Perm
      [armChild (n + 4) (rightPredecessor n), armChild (n + 4) (3 * n + 7),
        armChild (n + 4) (3 * n + 8)] := by
  let physical := (recordNeighbors (expanded n parity) (n + 4)).erase 0
  have projected := right_erased_records n parity
  have actual := actual_away_children (expanded n parity) (n + 4) 0 [] physical rfl
    (expanded_record_bond_one n parity (n + 4)) (by
      intro other member
      have retained := projected.mem_iff.mp member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at retained
      rcases retained with rfl | rfl | rfl
      · unfold rightPredecessor
        split <;> simp_all
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        omega)
  rw [show (rootCursor (n + 4)).children (expanded n parity) =
    physical.map (fun other => armChild (n + 4) other) from actual]
  exact projected.map (armChild (n + 4))

theorem actual_arms_nonterminal (n : Nat) (parity : TetrahedralInputParity) :
    cursorTerminal (expanded n parity) (rootCursor 2) = false ∧
      cursorTerminal (expanded n parity) (rootCursor (n + 4)) = false := by
  have leftLength := (actual_left_children n parity).length_eq
  have rightLength := (actual_right_children n parity).length_eq
  have leftNonempty : (rootCursor 2).children (expanded n parity) ≠ [] := by
    intro empty
    rw [empty] at leftLength
    cases leftLength
  have rightNonempty : (rootCursor (n + 4)).children (expanded n parity) ≠ [] := by
    intro empty
    rw [empty] at rightLength
    cases rightLength
  change (false || ((rootCursor 2).children (expanded n parity)).isEmpty) = false ∧
    (false || ((rootCursor (n + 4)).children (expanded n parity)).isEmpty) = false
  simpa only [Bool.false_or, List.isEmpty_eq_false_iff] using ⟨leftNonempty, rightNonempty⟩

/-- All six permutations of the physical three-child inventory are considered. This finite list
identity does not bound ring size or substitute example molecules for the family. -/
theorem perm_three_cases {α : Type*} (items : List α) (a b c : α)
    (permutation : items.Perm [a, b, c]) :
    items = [a, b, c] ∨ items = [b, a, c] ∨ items = [b, c, a] ∨
      items = [a, c, b] ∨ items = [c, a, b] ∨ items = [c, b, a] := by
  have member := List.mem_permutations'.mpr permutation
  change items ∈ [[a, b, c], [b, a, c], [b, c, a], [a, c, b], [c, a, b], [c, b, a]] at member
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using member

end TetraStereo.UniversalProof.NativeRingRuntimeChildren
