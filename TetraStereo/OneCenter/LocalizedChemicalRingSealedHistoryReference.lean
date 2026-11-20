import TetraStereo.OneCenter.LocalizedChemicalRingCoveredPathOrientation
import TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeFrame
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
A reference atom whose neighbors have all been visited cannot reappear below an actual
canonical occurrence, provided it is absent from the immediate children. This excludes
duplicate leaves as well as real occurrences. History membership alone would not suffice:
the promoted marker deliberately counts duplicate occurrences carrying the reference.
This raw traversal result does not assert equality of promoted comparison keys.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingSealedHistoryReference

open LocalizedMarkedTerminalReferenceScope (StrictDescendant)
open LocalizedMarkedReachedFrameNeighbors (SingleBonded)
open LocalizedMarkedTerminalGaugeFrame (child_bond)
open LocalizedChemicalRingCoveredPathOrientation (strictDescendant_outside_history)
open LocalizedGenericMarkedRecalculation (canonicalChildren_forcedLeaf)

variable (mol : RawMolecule) (wellFormed : mol.WellFormed) (single : SingleBonded mol)

include wellFormed single

/-- No strict descendant, including a ring duplicate, can carry a sealed reference. -/
theorem strictDescendant_atom_ne
    (source target : RawMolecule.CanonicalBranchNode) (reference : Nat)
    (sealed : ∀ atom, 0 < mol.bondOrder atom reference → atom ∈ source.history)
    (first : ∀ child ∈ mol.canonicalChildren source, child.atom ≠ reference)
    (descent : StrictDescendant mol source target) : target.atom ≠ reference := by
  obtain ⟨child, edge, rest⟩ := descent
  induction rest with
  | refl => exact first child edge
  | @tail parent target path next _ =>
      intro atReference
      have real : parent.forcedLeaf = false := by
        cases leaf : parent.forcedLeaf with
        | false => rfl
        | true => simp [canonicalChildren_forcedLeaf mol parent leaf] at next
      have bond := child_bond mol wellFormed single parent target next
      rw [atReference] at bond
      exact strictDescendant_outside_history ⟨child, edge, path⟩ real (sealed parent.atom bond)

/-- It suffices that the current atom is not bonded to the reference: immediate-child
absence then follows from actual child membership. -/
theorem strictDescendant_atom_ne_of_not_adjacent
    (source target : RawMolecule.CanonicalBranchNode) (reference : Nat)
    (sealed : ∀ atom, 0 < mol.bondOrder atom reference → atom ∈ source.history)
    (notAdjacent : ¬ 0 < mol.bondOrder source.atom reference)
    (descent : StrictDescendant mol source target) : target.atom ≠ reference := by
  apply strictDescendant_atom_ne mol wellFormed single source target reference sealed _ descent
  intro child member same
  have bond := child_bond mol wellFormed single source child member
  rw [same] at bond
  exact notAdjacent bond

end TetraStereo.OneCenter.LocalizedChemicalRingSealedHistoryReference

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSealedHistoryReference.strictDescendant_atom_ne
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSealedHistoryReference.strictDescendant_atom_ne_of_not_adjacent
