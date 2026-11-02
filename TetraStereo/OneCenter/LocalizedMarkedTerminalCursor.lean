import TetraStereo.OneCenter.LocalizedMarkedTerminalReferenceScope
import TetraStereo.OneCenter.CIPAuthoritativeOccurrenceDescriptorComparatorLaws
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Terminal molecular ligands stay terminal after actual occurrence rerooting

Both outgoing and incoming-parent slots are covered. The full occurrence neighbor list is
derived from the actual molecular neighborhood, so deleting the remembered edge leaves no
children at a terminal atom. Actual generated promotion snapshots then have silent terminal
reads, and every ordinary descriptor stage ties on a pair of such ligands.

The constitutional comparison and the center's own promoted-reference consensus are separate
remaining steps toward terminal-twin center refusal.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedTerminalCursor

open LocalizedMarkedOperationEvaluator LocalizedMarkedReachableConfigurations
open LocalizedMarkedReachedFrameNeighbors LocalizedMarkedTerminalReferenceScope
open LocalizedMarkedUncappedOperations AuthoritativeCIPMoleculeCursorRanking
open AuthoritativeCIPOccurrenceDescriptorComparatorLaws
open LocalizedGenericMarkedRecalculation (Geometry)

abbrev Node := RawMolecule.CanonicalBranchNode

theorem neighbors_atoms_perm (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (node : Node) (reached : Reached mol node)
    (real : node.forcedLeaf = false) :
    ((({ node := node } : CanonicalRerootCursor).neighbors mol).map (·.atom)).Perm
      (mol.canonicalIncidentNeighbors node.atom) := by
  have perm := occurrence_atoms_perm_neighbors mol wellFormed single node reached real
  rw [occurrence_atoms mol node real] at perm
  simpa [CanonicalRerootCursor.neighbors, List.map_append, Option.toList_map] using perm

theorem cursor_children_nil (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique)
    (node previous : Node) (reached : Reached mol node)
    (remembered : previous ∈ ({ node := node } : CanonicalRerootCursor).neighbors mol)
    (center : Nat) (terminal : TerminalNeighbor mol center node.atom) :
    ({ node := node, previous? := some previous } : CanonicalRerootCursor).children mol = [] := by
  cases leaf : node.forcedLeaf with
  | true => simp [CanonicalRerootCursor.children, leaf]
  | false =>
      let neighbors := ({ node := node } : CanonicalRerootCursor).neighbors mol
      have perm := neighbors_atoms_perm mol wellFormed single node reached leaf
      have nodup : (neighbors.map (·.atom)).Nodup :=
        perm.nodup_iff.mpr (mol.canonicalIncidentNeighbors_nodup node.atom unique)
      have injective := (List.nodup_map_iff_inj_on (List.Nodup.of_map _ nodup)).mp nodup
      have only : ∀ neighbor ∈ neighbors, neighbor.atom = center := by
        intro neighbor member
        apply terminal.2
        exact (mol.mem_canonicalIncidentNeighbors_iff node.atom wellFormed neighbor.atom).mp
          (perm.mem_iff.mp (List.mem_map.mpr ⟨neighbor, member, rfl⟩))
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro child member
      obtain ⟨neighbor, present, different, _⟩ := mem_cursor_children_of_previous member
      exact different (injective neighbor present previous remembered
        ((only neighbor present).trans (only previous remembered).symm))

/-- All actual ligand cursors, including a rerooted incoming-parent slot, retain generated
nodes and are terminal whenever their physical atom is terminal. -/
theorem ligand_terminal (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique)
    (source : Node) (reached : Reached mol source) (cursor : CanonicalRerootCursor)
    (member : cursor ∈ occurrenceLigandCursors mol source) (center : Nat)
    (terminal : TerminalNeighbor mol center cursor.node.atom) :
    Reached mol cursor.node ∧ cursorTerminal mol cursor = true := by
  obtain ⟨root, valid, sourcePath⟩ := reached
  have generated := generated_of_reachedFrom mol root source sourcePath
  have eligible := occurrenceLigandCursor_eligible generated member
  have finish (node previous : Node) (nodeGenerated : CanonicalCenterTreeNode mol root node)
      (remembered : previous ∈ ({ node := node } : CanonicalRerootCursor).neighbors mol)
      (leaf : TerminalNeighbor mol center node.atom) :
      Reached mol node ∧
        cursorTerminal mol { node := node, previous? := some previous } = true := by
    have reachedNode : Reached mol node :=
      ⟨root, valid, reachedFrom_of_generated mol root node nodeGenerated⟩
    refine ⟨reachedNode, ?_⟩
    rw [cursorTerminal, cursor_children_nil mol wellFormed single unique node previous
      reachedNode remembered center leaf]
    simp
  cases eligible with
  | @descending parent node parentGenerated edge =>
      apply finish node parent (.child parentGenerated edge) _ terminal
      simp [CanonicalRerootCursor.neighbors,
        canonicalOriginalParent?_eq_some_of_child parentGenerated edge]
  | @ascending node child nodeGenerated edge =>
      apply finish node child nodeGenerated _ terminal
      simp [CanonicalRerootCursor.neighbors, edge]

/-- The actual promotion forest has no terminal-atom read, even when other generated facts
carry lowercase descriptors. -/
theorem snapshot_factAt_terminal_none (mol : RawMolecule) (ops : Operations)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol) (unique : mol.BondRecordsUnique)
    (depth : Nat) (geom : Geometry) (state : OccurrenceAuxState) (source : Node)
    (reached : Reached mol source) (mark : Nat) (query : Node) (queryReached : Reached mol query)
    (center : Nat) (terminal : TerminalNeighbor mol center query.atom) :
    (underWith mol ops geom state source (facts mol ops depth) mark).factAt? query = none := by
  unfold OccurrenceAuxState.factAt?
  apply List.find?_eq_none.mpr
  intro fact member
  obtain ⟨child, edge, present⟩ := List.mem_flatMap.mp member
  have childReached := reached_child mol source child reached
    (mem_tiedChildren_actual mol ops state source child edge)
  have absent := generated_factAt_terminal_none mol ops wellFormed single unique depth geom state
    (some mark) child childReached query queryReached center terminal
  exact List.find?_eq_none.mp absent fact present

/-- Every actual ordinary descriptor-stage comparison of terminal ligands ties on the internally
generated promotion snapshot. Neither label silence nor comparator success is a premise. -/
theorem generated_terminal_stage_tie (mol : RawMolecule) (ops : Operations)
    (wellFormed : mol.WellFormed) (single : SingleBonded mol) (unique : mol.BondRecordsUnique)
    (depth fuel : Nat) (geom : Geometry) (state : OccurrenceAuxState)
    (source target : Node) (sourceReached : Reached mol source) (targetReached : Reached mol target)
    (mark : Nat) (left right : CanonicalRerootCursor)
    (leftSlot : left ∈ occurrenceLigandCursors mol target)
    (rightSlot : right ∈ occurrenceLigandCursors mol target)
    (leftTerminal : TerminalNeighbor mol target.atom left.node.atom)
    (rightTerminal : TerminalNeighbor mol target.atom right.node.atom)
    (stage : RawDescriptorRuleStage) :
    compareOccurrenceDescriptorAtTiedRootAuthoritative? mol
      (underWith mol ops geom state source (facts mol ops depth) mark) fuel stage left right =
        some .eq := by
  obtain ⟨leftReached, leftLeaf⟩ := ligand_terminal mol wellFormed single unique target
    targetReached left leftSlot target.atom leftTerminal
  obtain ⟨rightReached, rightLeaf⟩ := ligand_terminal mol wellFormed single unique target
    targetReached right rightSlot target.atom rightTerminal
  exact compareOccurrenceDescriptorAtTiedRootAuthoritative?_terminal_silent_eq mol _ fuel stage
      left right leftLeaf rightLeaf
      (snapshot_factAt_terminal_none mol ops wellFormed single unique depth geom state source
        sourceReached mark left.node leftReached target.atom leftTerminal)
      (snapshot_factAt_terminal_none mol ops wellFormed single unique depth geom state source
        sourceReached mark right.node rightReached target.atom rightTerminal)

end TetraStereo.OneCenter.LocalizedMarkedTerminalCursor

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalCursor.cursor_children_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalCursor.ligand_terminal
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalCursor.snapshot_factAt_terminal_none
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalCursor.generated_terminal_stage_tie
