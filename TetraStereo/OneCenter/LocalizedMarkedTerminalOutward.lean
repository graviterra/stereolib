import TetraStereo.OneCenter.LocalizedMarkedTerminalCarriedRefusal
import TetraStereo.OneCenter.Rule1bRepresentedAtomObservation

set_option autoImplicit false

/-!
# Molecular terminal ligands yield real outward occurrences

Existing raw neighbor, history and child-copy laws suffice: a terminal atom reached
from a different root has no children, hence cannot occur inside a later real path.
Its appearance beside its center is therefore an outward real child, even with rings.
No auxiliary labels, comparison results or constitutional rigidity enter this argument.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedTerminalOutward

open LocalizedMarkedReachableConfigurations LocalizedMarkedReachedFrameNeighbors
open LocalizedMarkedTerminalReferenceScope LocalizedMarkedUncappedOperations
open AuthoritativeCIPMoleculeCursorRanking Rule1bRepresentedAtomObservation

abbrev Node := RawMolecule.CanonicalBranchNode

theorem child_bond (mol : RawMolecule) (wellFormed : mol.WellFormed) (single : SingleBonded mol)
    (parent child : Node) (edge : child ∈ mol.canonicalChildren parent) :
    0 < mol.bondOrder parent.atom child.atom := by
  have real : parent.forcedLeaf = false := by
    simp [RawMolecule.CanonicalBranchNode.forcedLeaf, real_of_child_mem edge]
  have member : child.atom ∈ (mol.canonicalChildren parent).map (·.atom) :=
    List.mem_map.mpr ⟨child, edge, rfl⟩
  rw [children_atoms mol wellFormed single parent real] at member
  exact (mol.mem_canonicalIncidentNeighbors_iff parent.atom wellFormed child.atom).mp
    (List.mem_of_mem_erase member)

/-- A generated terminal atom cannot continue the path once entered from a different root. -/
theorem terminal_children_nil (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique)
    (root : Nat) (node : Node) (generated : CanonicalCenterTreeNode mol root node)
    (center : Nat) (terminal : TerminalNeighbor mol center node.atom)
    (rootNe : root ≠ node.atom) : mol.canonicalChildren node = [] := by
  cases generated with
  | root => exact (rootNe rfl).elim
  | @child parent node parentGenerated edge =>
      cases leaf : node.forcedLeaf with
      | true => simp [RawMolecule.canonicalChildren, leaf]
      | false =>
          have parentCenter : parent.atom = center := terminal.2 parent.atom
            (by simpa [RawMolecule.bondOrder_symm] using child_bond mol wellFormed single parent node edge)
          have back : node.parent = center := (mol.canonicalChildren_parent_eq parent node edge).trans
            parentCenter
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro next member
          have mapped : next.atom ∈ (mol.canonicalChildren node).map (·.atom) :=
            List.mem_map.mpr ⟨next, member, rfl⟩
          rw [children_atoms mol wellFormed single node leaf, back] at mapped
          have nextCenter := terminal.2 next.atom
            ((mol.mem_canonicalIncidentNeighbors_iff node.atom wellFormed next.atom).mp
              (List.mem_of_mem_erase mapped))
          rw [nextCenter] at mapped
          exact (mol.canonicalIncidentNeighbors_nodup node.atom unique).not_mem_erase mapped

theorem history_avoids_terminal (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique)
    (root center leaf : Nat) (terminal : TerminalNeighbor mol center leaf) (rootNe : root ≠ leaf)
    (node : Node) (generated : CanonicalCenterTreeNode mol root node)
    (currentNe : node.atom ≠ leaf) : leaf ∉ node.history := by
  induction generated with
  | root => simpa [canonicalCenterRoot, eq_comm] using rootNe
  | @child parent node parentGenerated edge ih =>
      have parentNe : parent.atom ≠ leaf := by
        intro equal
        have empty := terminal_children_nil mol wellFormed single unique root parent parentGenerated
          center (by simpa [equal] using terminal) (by simpa [equal] using rootNe)
        simp [empty] at edge
      rw [mol.canonicalChildren_history parent node edge]
      simp only [List.mem_cons, not_or]
      exact ⟨Ne.symm currentNe, ih parentNe⟩

theorem parent_ne_terminal (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique)
    (root center leaf : Nat) (terminal : TerminalNeighbor mol center leaf) (rootNe : root ≠ leaf)
    (node : Node) (generated : CanonicalCenterTreeNode mol root node)
    (currentNe : node.atom ≠ leaf) : node.parent ≠ leaf := by
  cases generated with
  | root => exact currentNe
  | @child parent node parentGenerated edge =>
      rw [mol.canonicalChildren_parent_eq parent node edge]
      intro equal
      have empty := terminal_children_nil mol wellFormed single unique root parent parentGenerated
        center (by simpa [equal] using terminal) (by simpa [equal] using rootNe)
      simp [empty] at edge

/-- The returned cursor is produced by the actual canonical child enumeration and occupies an
actual ligand slot. Freshness derives its real provenance; no occurrence witness is supplied. -/
theorem exists_outward_terminal_cursor (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique)
    (root : Nat) (node : Node) (generated : CanonicalCenterTreeNode mol root node)
    (real : node.provenance = .realAtom) (leaf : Nat)
    (terminal : TerminalNeighbor mol node.atom leaf) (rootNe : root ≠ leaf) :
    ∃ cursor : CanonicalRerootCursor,
      cursor ∈ occurrenceLigandCursors mol node ∧
      cursor.node ∈ mol.canonicalChildren node ∧ cursor.node.atom = leaf ∧
      cursor.node.provenance = .realAtom ∧ cursor.previous? = some node := by
  have currentNe : node.atom ≠ leaf := by
    intro equal
    have positive := terminal.1
    rw [equal, RawMolecule.bondOrder_self] at positive
    exact Nat.lt_irrefl 0 positive
  have fresh := history_avoids_terminal mol wellFormed single unique root node.atom leaf terminal
    rootNe node generated currentNe
  have parentNe := parent_ne_terminal mol wellFormed single unique root node.atom leaf terminal
    rootNe node generated currentNe
  have notLeaf : node.forcedLeaf = false := by
    simp [RawMolecule.CanonicalBranchNode.forcedLeaf, real]
  have order : mol.bondOrder node.atom leaf = 1 :=
    Nat.le_antisymm (single node.atom leaf) (Nat.succ_le_of_lt terminal.1)
  have seed : (leaf, 0) ∈ mol.canonicalSeedCopies node :=
    (mol.mem_canonicalSeedCopies_iff node wellFormed leaf 0).mpr
      ⟨terminal.1, by rw [canonicalBondOrder_one mol node leaf order]; decide⟩
  have copy : (leaf, 0) ∈ mol.canonicalChildCopies node := by
    rw [mol.canonicalChildCopies_eq_erase_seed, RawMolecule.eraseCanonicalParentCopy_eq_erase]
    apply (mol.canonicalSeedCopies_nodup node unique).mem_erase_iff.mpr
    exact ⟨fun equal => parentNe (congrArg Prod.fst equal).symm, seed⟩
  let child := canonicalChildOfCopy node (leaf, 0)
  have childMem : child ∈ mol.canonicalChildren node :=
    canonicalChildOfCopy_mem_canonicalChildren mol node (leaf, 0) copy notLeaf
  refine ⟨{ node := child, previous? := some node }, ?_, childMem, rfl, ?_, rfl⟩
  · unfold occurrenceLigandCursors CanonicalRerootCursor.children
    simp only [notLeaf, Bool.false_eq_true, ↓reduceIte]
    apply List.mem_filterMap.mpr
    refine ⟨child, ?_, rfl⟩
    exact List.mem_append_right _ childMem
  · simp [child, canonicalChildOfCopy, fresh]

end TetraStereo.OneCenter.LocalizedMarkedTerminalOutward

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalOutward.child_bond
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalOutward.terminal_children_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalOutward.history_avoids_terminal
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalOutward.parent_ne_terminal
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalOutward.exists_outward_terminal_cursor
