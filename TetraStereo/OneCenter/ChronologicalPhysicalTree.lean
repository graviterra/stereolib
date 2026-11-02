import TetraStereo.OneCenter.ChemistrySemantics

set_option autoImplicit false

namespace TetraStereo.OneCenter.RawMolecule

/-- Shared raw structural domain: one chronological single-bond parent for every nonroot atom.
No generated-history, metric, comparator or final output result is a premise. -/
def ChronologicalPhysicalTree (mol : RawMolecule) : Prop :=
  0 < mol.atomCount ∧
  (∀ bond ∈ mol.bonds, bond.kind = .single ∧ bond.source < bond.target ∧
    bond.target < mol.atomCount) ∧
  (mol.bonds.map RawBond.target).Nodup ∧
  (∀ atom, 0 < atom → atom < mol.atomCount → atom ∈ mol.bonds.map RawBond.target)

theorem ChronologicalPhysicalTree.wellFormed {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) : mol.WellFormed := by
  intro bond member
  obtain ⟨single, chronological, bound⟩ := tree.2.1 bond member
  exact ⟨lt_trans chronological bound, bound, ne_of_lt chronological⟩

theorem ChronologicalPhysicalTree.no_root_target {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) (bond : RawBond) (member : bond ∈ mol.bonds) :
    bond.target ≠ 0 := by
  have chronological := (tree.2.1 bond member).2.1
  omega

theorem ChronologicalPhysicalTree.nonroot_covered {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) (atom : Nat)
    (positive : 0 < atom) (bound : atom < mol.atomCount) :
    atom ∈ mol.bonds.map RawBond.target := tree.2.2.2 atom positive bound

/-- Target uniqueness is exact raw inventory uniqueness, independent of execution. -/
theorem ChronologicalPhysicalTree.target_inventory_nodup {mol : RawMolecule}
    (tree : mol.ChronologicalPhysicalTree) : (mol.bonds.map RawBond.target).Nodup := tree.2.2.1

end TetraStereo.OneCenter.RawMolecule
