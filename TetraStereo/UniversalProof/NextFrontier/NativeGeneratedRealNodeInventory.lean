import TetraStereo.UniversalProof.NextFrontier.NativeChronologicalTreeSimplePathUniqueness

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeGeneratedRealNodeInventory
open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeGeneratedRealPaths
open TetraStereo.UniversalProof.NativeChronologicalTreeSimplePathUniqueness

/-- Actual child creation stores the physical parent atom. -/
theorem canonical_children_parent {mol : RawMolecule} {parent child : CanonicalBranchNode}
    (member : child ∈ mol.canonicalChildren parent) : child.parent = parent.atom := by
  unfold RawMolecule.canonicalChildren at member
  by_cases leaf : parent.forcedLeaf
  · simp [leaf] at member
  · simp only [leaf, Bool.false_eq_true, ↓reduceIte, List.mem_map] at member
    obtain ⟨copy, _copyMember, rfl⟩ := member
    rfl

/-- Original generation determines the stored parent from history; the root keeps itself. -/
theorem generated_parent_from_history {mol : RawMolecule} {root : Nat}
    {node : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root node) :
    node.parent = node.history.tail.head?.getD root := by
  cases generated with
  | root => rfl
  | @child parent child parentGenerated member =>
      rw [canonical_children_parent member, mol.canonicalChildren_history _ _ member]
      simp only [List.tail_cons, parentGenerated.history_head, Option.getD_some]

/-- Equal physical atoms in one actual generated real tree have equal histories.
Uniqueness is derived from raw tree facts, never supplied as an output field. -/
theorem generated_real_history_unique {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root : Nat} (rootBound : root < mol.atomCount)
    {left right : CanonicalBranchNode}
    (leftGenerated : CanonicalCenterTreeNode mol root left)
    (rightGenerated : CanonicalCenterTreeNode mol root right)
    (leftReal : left.provenance = .realAtom) (rightReal : right.provenance = .realAtom)
    (sameAtom : left.atom = right.atom) : left.history = right.history := by
  have leftPath := generated_real_root_path rootBound tree.wellFormed leftGenerated leftReal
  have rightPath : RawSupportedPath mol root left.atom right.history.reverse := by
    rw [sameAtom]
    exact generated_real_root_path rootBound tree.wellFormed rightGenerated rightReal
  have histories := chronological_uniqueRawSimplePaths tree root left.atom _ _ leftPath rightPath
  exact List.reverse_injective histories

/-- Within one genuine real generated tree, physical atom identity determines the full
original node, including the stored parent and discovery history. -/
theorem generated_real_node_unique {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root : Nat} (rootBound : root < mol.atomCount)
    {left right : CanonicalBranchNode}
    (leftGenerated : CanonicalCenterTreeNode mol root left)
    (rightGenerated : CanonicalCenterTreeNode mol root right)
    (leftReal : left.provenance = .realAtom) (rightReal : right.provenance = .realAtom)
    (sameAtom : left.atom = right.atom) : left = right := by
  have historyEq := generated_real_history_unique tree rootBound leftGenerated rightGenerated
    leftReal rightReal sameAtom
  have parentEq : left.parent = right.parent := by
    rw [generated_parent_from_history leftGenerated, generated_parent_from_history rightGenerated,
      historyEq]
  have provenanceEq : left.provenance = right.provenance := leftReal.trans rightReal.symm
  cases left
  cases right
  simp only [CanonicalBranchNode.mk.injEq]
  exact ⟨sameAtom, parentEq, historyEq, provenanceEq⟩

/-- Same-atom generated real occurrences have the same discovery depth, within one root. -/
theorem generated_real_depth_unique {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root : Nat} (rootBound : root < mol.atomCount)
    {left right : CanonicalBranchNode}
    (leftGenerated : CanonicalCenterTreeNode mol root left)
    (rightGenerated : CanonicalCenterTreeNode mol root right)
    (leftReal : left.provenance = .realAtom) (rightReal : right.provenance = .realAtom)
    (sameAtom : left.atom = right.atom) : left.depth = right.depth := by
  change left.history.length - 1 = right.history.length - 1
  rw [generated_real_history_unique tree rootBound leftGenerated rightGenerated leftReal rightReal sameAtom]

/-- The existing real-history inventory bound applies from the independent raw tree domain. -/
theorem generated_real_history_length_le_inventory {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) {root : Nat} (rootBound : root < mol.atomCount)
    {node : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root node)
    (real : node.provenance = .realAtom) : node.history.length ≤ mol.atomCount :=
  generated.real_history_length_le_atomCount rootBound tree.wellFormed real

end TetraStereo.UniversalProof.NativeGeneratedRealNodeInventory
