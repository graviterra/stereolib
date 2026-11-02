import TetraStereo.OneCenter.LocalizedMarkedReachableConfigurations
import TetraStereo.OneCenter.RawLocalizedChildCopyTransport
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Reached frames recover molecular neighbors

On a well-formed raw single-bond molecule, an actual non-leaf occurrence frame enumerates the
incident molecular neighbors, independent of its ring-cut history. The incoming parent restores
the one real edge removed by canonical child expansion. This connects reached configurations to
molecular local frames without constitutional-rigidity or acyclicity assumptions.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedReachedFrameNeighbors

open LocalizedGenericMarkedRecalculation LocalizedMarkedReachableConfigurations

def SingleBonded (mol : RawMolecule) : Prop := ∀ a b, mol.bondOrder a b ≤ 1

theorem canonicalBondOrder_one (mol : RawMolecule) (node : Node) (next : Nat)
    (order : mol.bondOrder node.atom next = 1) : mol.canonicalBondOrder node next = 1 := by
  unfold RawMolecule.canonicalBondOrder
  split <;> simp [order]

theorem seeds_eq_neighbors (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (node : Node) :
    mol.canonicalSeedCopies node =
      (mol.canonicalIncidentNeighbors node.atom).map fun atom => (atom, 0) := by
  unfold RawMolecule.canonicalSeedCopies
  have blocks : (mol.canonicalIncidentNeighbors node.atom).flatMap
      (fun next => (List.range (mol.canonicalBondOrder node next)).map fun copy => (next, copy)) =
      (mol.canonicalIncidentNeighbors node.atom).flatMap (fun next => [(next, 0)]) := by
    apply flatMap_congr_mem
    intro next member
    have positive := (mol.mem_canonicalIncidentNeighbors_iff node.atom wellFormed next).mp member
    have upper := single node.atom next
    have order : mol.bondOrder node.atom next = 1 :=
      Nat.le_antisymm upper (Nat.succ_le_of_lt positive)
    rw [canonicalBondOrder_one mol node next order]
    rfl
  simpa only [← List.map_eq_flatMap] using blocks

theorem children_atoms (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (node : Node) (real : node.forcedLeaf = false) :
    (mol.canonicalChildren node).map (·.atom) =
      (mol.canonicalIncidentNeighbors node.atom).erase node.parent := by
  have copies := mol.canonicalChildCopies_eq_erase_seed node
  rw [RawMolecule.eraseCanonicalParentCopy_eq_erase, seeds_eq_neighbors mol wellFormed single] at copies
  have injective : Function.Injective (fun atom : Nat => (atom, (0 : Nat))) := by
    intro a b eq
    exact (Prod.mk.inj eq).1
  rw [← List.map_erase injective] at copies
  simp [RawMolecule.canonicalChildren, real, copies, List.map_map, Function.comp_def]

private def ParentCoherent (mol : RawMolecule) (node : Node) : Prop :=
  node.history.head? = some node.atom ∧
    (((canonicalOriginalParent? node).map (·.atom) = none ∧ node.parent = node.atom) ∨
      ((canonicalOriginalParent? node).map (·.atom) = some node.parent ∧
        0 < mol.bondOrder node.atom node.parent))

private theorem child_shape (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (parent child : Node) (edge : child ∈ mol.canonicalChildren parent) :
    child.history = child.atom :: parent.history ∧ child.parent = parent.atom ∧
      0 < mol.bondOrder parent.atom child.atom := by
  unfold RawMolecule.canonicalChildren at edge
  split at edge
  · simp at edge
  · obtain ⟨copy, member, rfl⟩ := List.mem_map.mp edge
    rw [RawMolecule.canonicalChildCopies_eq_erase_seed] at member
    have seed := mem_eraseCanonicalParentCopy _ _ _ member
    have positive := (mol.mem_canonicalSeedCopies_iff parent wellFormed copy.1 copy.2).mp seed
    exact ⟨rfl, rfl, positive.1⟩

private theorem coherent_child (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (parent child : Node) (coherent : ParentCoherent mol parent)
    (edge : child ∈ mol.canonicalChildren parent) : ParentCoherent mol child := by
  obtain ⟨history, back, positive⟩ := child_shape mol wellFormed parent child edge
  refine ⟨by simp [history], Or.inr ⟨?_, ?_⟩⟩
  · have head := coherent.1
    cases hp : parent.history with
    | nil => simp [hp] at head
    | cons atom tail =>
        have atomEq : atom = parent.atom := by simpa [hp] using head
        cases tail <;> simp [canonicalOriginalParent?, history, hp, back, atomEq]
  · simpa [back, RawMolecule.bondOrder_symm] using positive

private theorem coherent_of_reached (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (node : Node) (reached : Reached mol node) : ParentCoherent mol node := by
  obtain ⟨center, _, path⟩ := reached
  induction path with
  | refl => simp [ParentCoherent, canonicalCenterRoot, canonicalOriginalParent?]
  | tail path edge ih => exact coherent_child mol wellFormed _ _ ih edge

theorem reached_atom_valid (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (node : Node) (reached : Reached mol node) : node.atom < mol.atomCount := by
  obtain ⟨center, valid, path⟩ := reached
  induction path with
  | refl => exact valid
  | tail path edge _ =>
      exact (mol.bondOrder_pos_endpoint_lt wellFormed
        (child_shape mol wellFormed _ _ edge).2.2).2

theorem occurrence_atoms (mol : RawMolecule) (node : Node) (real : node.forcedLeaf = false) :
    frameAtomsOf (occurrenceLigandCursors mol node) =
      ((canonicalOriginalParent? node).map (·.atom)).toList ++
        (mol.canonicalChildren node).map (·.atom) := by
  simp [frameAtomsOf, occurrenceLigandCursors, CanonicalRerootCursor.children,
    CanonicalRerootCursor.neighbors, real, List.map_map, Function.comp_def, Option.toList_map]

/-- Cutting a ring changes occurrence provenance, but does not remove a physical frame neighbor. -/
theorem occurrence_atoms_perm_neighbors (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (node : Node) (reached : Reached mol node)
    (real : node.forcedLeaf = false) :
    (frameAtomsOf (occurrenceLigandCursors mol node)).Perm
      (mol.canonicalIncidentNeighbors node.atom) := by
  rw [occurrence_atoms mol node real, children_atoms mol wellFormed single node real]
  rcases (coherent_of_reached mol wellFormed node reached).2 with ⟨parent, self⟩ | ⟨parent, positive⟩
  · have absent : node.atom ∉ mol.canonicalIncidentNeighbors node.atom := by
      rw [mol.mem_canonicalIncidentNeighbors_iff node.atom wellFormed node.atom,
        RawMolecule.bondOrder_self]
      exact Nat.not_lt_zero _
    simp [parent, self, List.erase_of_not_mem absent]
  · have member := (mol.mem_canonicalIncidentNeighbors_iff node.atom wellFormed node.parent).mpr positive
    simpa [parent] using (List.perm_cons_erase member).symm

/-- A successful reached frame is the physical neighborhood, or that neighborhood plus the
explicit lone-pair phantom. The alternatives retain their exact neighbor counts. -/
theorem frame_atoms_perm_neighbors (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (node : Node) (reached : Reached mol node)
    (atoms : List Nat) (frame : frameAtoms? mol node = some atoms) :
    ((mol.canonicalIncidentNeighbors node.atom).length = 4 ∧
      atoms.Perm (mol.canonicalIncidentNeighbors node.atom)) ∨
    ((mol.canonicalIncidentNeighbors node.atom).length = 3 ∧
      atoms.Perm (mol.canonicalIncidentNeighbors node.atom ++ [mol.atomCount])) := by
  have real : node.forcedLeaf = false := by
    cases leaf : node.forcedLeaf with
    | false => rfl
    | true => simp [frameAtoms?_forcedLeaf mol node leaf] at frame
  have perm := occurrence_atoms_perm_neighbors mol wellFormed single node reached real
  have length : (occurrenceLigandCursors mol node).length =
      (mol.canonicalIncidentNeighbors node.atom).length := by
    simpa [frameAtomsOf] using perm.length_eq
  dsimp [frameAtoms?, occurrenceLigandFrame?] at frame
  split at frame
  · simp at frame
  · split at frame
    · rename_i four
      simp only [Option.map_some, Option.some.injEq] at frame
      subst atoms
      exact Or.inl ⟨by simpa [length] using four, perm⟩
    · split at frame
      · rename_i three
        have count : (occurrenceLigandCursors mol node).length = 3 := by
          simp only [Bool.and_eq_true, beq_iff_eq] at three
          exact three.1
        simp only [Option.map_some, Option.some.injEq] at frame
        subst atoms
        refine Or.inr ⟨by omega, ?_⟩
        simpa [frameAtomsOf, RawMolecule.canonicalPhantom] using
          perm.append_right [mol.atomCount]
      · simp at frame

end TetraStereo.OneCenter.LocalizedMarkedReachedFrameNeighbors

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReachedFrameNeighbors.children_atoms
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReachedFrameNeighbors.occurrence_atoms_perm_neighbors
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReachedFrameNeighbors.frame_atoms_perm_neighbors
