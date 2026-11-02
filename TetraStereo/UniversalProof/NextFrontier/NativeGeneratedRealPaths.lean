import TetraStereo.UniversalProof.NextFrontier.NativeOriginFrame
import TetraStereo.OneCenter.ProductionCIPExactExpansion
import Mathlib.Data.List.Chain

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeGeneratedRealPaths

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.InteriorMethylDepthCounterexample

/-- Actual raw bond adjacency along consecutive vertices, not discovery depth. -/
def RawBondedPath (mol : RawMolecule) (vertices : List Nat) : Prop :=
  vertices.IsChain (fun a b => 0 < mol.bondOrder a b)

/-- A supported simple physical path, with explicit endpoints. -/
def RawSupportedPath (mol : RawMolecule) (start finish : Nat) (vertices : List Nat) : Prop :=
  vertices.Nodup ∧ RawBondedPath mol vertices ∧
    vertices.head? = some start ∧ vertices.getLast? = some finish ∧
    (∀ atom ∈ vertices, atom < mol.atomCount)

/-- Graph-only uniqueness obligation for a future tree metric proof. Not proved here. -/
def UniqueRawSimplePaths (mol : RawMolecule) : Prop :=
  ∀ start finish p q, RawSupportedPath mol start finish p →
    RawSupportedPath mol start finish q → p = q

/-- Graph-only connectivity obligation, with no generated-history or metric result fields. -/
def RawPathConnected (mol : RawMolecule) : Prop :=
  ∀ start finish, start < mol.atomCount → finish < mol.atomCount →
    ∃ vertices, RawSupportedPath mol start finish vertices

def edgeCount (vertices : List Nat) : Nat := vertices.length - 1

/-- Positivity is derived from the actual written raw bond witness and copy-index bound. -/
theorem generated_child_bond_positive {mol : RawMolecule}
    {parent child : CanonicalBranchNode}
    (head : parent.history.head? = some parent.atom)
    (member : child ∈ mol.canonicalChildren parent) :
    0 < mol.bondOrder child.atom parent.atom := by
  unfold RawMolecule.canonicalChildren at member
  by_cases leaf : parent.forcedLeaf
  · simp [leaf] at member
  · simp only [leaf, Bool.false_eq_true, ↓reduceIte, List.mem_map] at member
    obtain ⟨copy, copyMember, rfl⟩ := member
    obtain ⟨bond, bondMember, endpoints, copyBound⟩ :=
      mol.canonicalChildCopies_source parent copy copyMember
    have canonicalPositive : 0 < mol.canonicalBondOrder parent copy.1 := by omega
    have physicalPositive := mol.canonicalBondOrder_pos_imp_bondOrder_pos
      parent copy.1 head canonicalPositive
    rwa [mol.bondOrder_symm parent.atom copy.1] at physicalPositive

/-- Every actual generated discovery history follows positive raw bonds. -/
theorem generated_history_bonded {mol : RawMolecule} {root : Nat}
    {node : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root node) :
    RawBondedPath mol node.history := by
  induction generated with
  | root => exact List.isChain_singleton _
  | @child parent child parentGenerated member ih =>
      rw [mol.canonicalChildren_history parent child member]
      cases stored : parent.history with
      | nil =>
          have head := parentGenerated.history_head
          simp [stored] at head
      | cons atom tail =>
          have eq : atom = parent.atom := by
            have head := parentGenerated.history_head
            simpa [stored] using head
          change (child.atom :: atom :: tail).IsChain (fun a b => 0 < mol.bondOrder a b)
          rw [List.isChain_cons_cons]
          refine ⟨?_, ?_⟩
          · rw [eq]
            exact generated_child_bond_positive parentGenerated.history_head member
          · simpa [RawBondedPath, stored] using ih

/-- Stored current-to-root history ends at its actual generation root. -/
theorem generated_history_root_tail {mol : RawMolecule} {root : Nat}
    {node : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root node) :
    node.history.getLast? = some root := by
  induction generated with
  | root => rfl
  | @child parent child parentGenerated member ih =>
      rw [mol.canonicalChildren_history parent child member]
      cases stored : parent.history with
      | nil =>
          have head := parentGenerated.history_head
          simp [stored] at head
      | cons atom tail => simpa [stored] using ih

/-- Reversal preserves physical bonded adjacency, using actual symmetric raw bond order. -/
theorem bonded_reverse {mol : RawMolecule} {vertices : List Nat}
    (path : RawBondedPath mol vertices) : RawBondedPath mol vertices.reverse := by
  unfold RawBondedPath at path ⊢
  rw [List.isChain_reverse]
  have relation : (fun a b : Nat => 0 < mol.bondOrder b a) =
      (fun a b : Nat => 0 < mol.bondOrder a b) := by
    funext a b
    rw [mol.bondOrder_symm b a]
  rw [relation]
  exact path

/-- Real generation plus raw well-formedness derives the entire physical root-to-node path.
Freshness/Nodup and supported bounds use the actual ring-provenance exclusion theorem. -/
theorem generated_real_root_path {mol : RawMolecule} {root : Nat}
    (rootBound : root < mol.atomCount) (wellFormed : mol.WellFormed)
    {node : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root node)
    (real : node.provenance = .realAtom) :
    RawSupportedPath mol root node.atom node.history.reverse := by
  obtain ⟨nodup, bounds⟩ := generated.real_history rootBound wellFormed real
  refine ⟨?_, bonded_reverse (generated_history_bonded generated), ?_, ?_, ?_⟩
  · simpa using nodup
  · simpa using generated_history_root_tail generated
  · simpa using generated.history_head
  · intro atom member
    exact bounds atom (List.mem_reverse.mp member)

theorem generated_real_head {mol : RawMolecule} {root : Nat}
    {node : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root node) :
    node.history.head? = some node.atom := generated.history_head

theorem generated_real_path_length {mol : RawMolecule} {root : Nat}
    {node : CanonicalBranchNode} (_generated : CanonicalCenterTreeNode mol root node) :
    edgeCount node.history.reverse = node.depth := by
  simp [edgeCount, CanonicalBranchNode.depth]

/-- The actual incoming/outgoing methyl occurrence histories give physical paths from root 1. -/
theorem fixture_actual_root_paths :
    RawSupportedPath molecule 1 incoming.node.atom incoming.node.history.reverse ∧
    RawSupportedPath molecule 1 outgoing.node.atom outgoing.node.history.reverse := by
  refine ⟨?_, ?_⟩
  · exact generated_real_root_path (by decide +kernel) raw_wellFormed
      (CanonicalCenterTreeNode.root : CanonicalCenterTreeNode molecule 1 incoming.node)
      (by decide +kernel)
  · have generated : CanonicalCenterTreeNode molecule 1 outgoing.node :=
      .child actual_tag_generated (by decide +kernel)
    exact generated_real_root_path (by decide +kernel) raw_wellFormed generated
      (by decide +kernel)

/-- The fixed physical center has explicit one-edge paths to both methyl atoms. -/
theorem fixture_direct_center_paths :
    RawSupportedPath molecule 0 1 [0,1] ∧ RawSupportedPath molecule 0 2 [0,2] := by
  constructor
  · refine ⟨by decide +kernel, (by unfold RawBondedPath; exact List.isChain_pair.mpr (by decide +kernel)), rfl, rfl, ?_⟩
    intro atom member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide +kernel
  · refine ⟨by decide +kernel, (by unfold RawBondedPath; exact List.isChain_pair.mpr (by decide +kernel)), rfl, rfl, ?_⟩
    intro atom member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide +kernel

theorem fixture_direct_path_edge_tie : edgeCount [0,1] = 1 ∧ edgeCount [0,2] = 1 := by
  decide +kernel

end TetraStereo.UniversalProof.NativeGeneratedRealPaths
