import TetraStereo.OneCenter.LocalizedChemicalRingTwoFixedNeighbors
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! Exact remaining local parity alternatives when only the incoming neighbor is fixed.
A nontrivial action on the other three ligands is either odd or an even three-cycle.
The latter case cannot be silently treated as an odd correcting symmetry. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingFixedParentParity

/-- Finite local-group classification, checked by the kernel over all 24 permutations. -/
theorem fixed_parent_dichotomy (p : Equiv.Perm (Fin 4)) (parent : Fin 4)
    (fixed : p parent = parent) (nontrivial : p ≠ 1) :
    permHandedness p = -1 ∨
      (permHandedness p = 1 ∧ p ^ 3 = 1 ∧ ∀ i, i ≠ parent → p i ≠ i) := by
  have finite : ∀ (p : Equiv.Perm (Fin 4)) (parent : Fin 4),
      p parent = parent → p ≠ 1 →
      p.sign = -1 ∨
        (p.sign = 1 ∧ p ^ 3 = 1 ∧ ∀ i, i ≠ parent → p i ≠ i) := by
    decide +kernel
  rcases finite p parent fixed nontrivial with odd | ⟨even, cube, moved⟩
  · left
    simp [permHandedness, odd]
  · exact Or.inr ⟨by simp [permHandedness, even], cube, moved⟩

noncomputable section
open scoped Classical

/-- Molecular form: the parent slot and its fixedness are derived from actual atoms.
No assumptions about the parity of an inherited-reference stabilizer are made. -/
theorem local_dichotomy {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (e : m.Aut) (c : m.Center)
    (centerFixed : (e : Equiv.Perm V) c.1 = c.1)
    (parent : V) (adjacent : m.mol.Adj c.1 parent)
    (parentFixed : (e : Equiv.Perm V) parent = parent)
    (moved : ∃ atom, m.mol.Adj c.1 atom ∧ (e : Equiv.Perm V) atom ≠ atom) :
    ∃ parentSlot : Fin 4, m.ligandAtomAt c parentSlot = parent ∧
      (permHandedness (m.ligandPermAt e c) = -1 ∨
        (permHandedness (m.ligandPermAt e c) = 1 ∧
          (m.ligandPermAt e c) ^ 3 = 1 ∧
          ∀ i, i ≠ parentSlot → m.ligandPermAt e c i ≠ i)) := by
  have fixed : m.centerPerm e c = c := Subtype.ext centerFixed
  obtain ⟨parentSlot, atParent⟩ := m.ligandAtomAt_surjective c parent adjacent
  have fixedSlot : m.ligandPermAt e c parentSlot = parentSlot := by
    apply m.ligandAtomAt_injective c
    have transported := m.ligandAtomAt_ligandPermAt e c parentSlot
    rw [fixed, atParent, parentFixed] at transported
    exact transported.trans atParent.symm
  have nontrivial : m.ligandPermAt e c ≠ 1 := by
    intro trivial
    obtain ⟨atom, neighbor, changed⟩ := moved
    obtain ⟨slot, atAtom⟩ := m.ligandAtomAt_surjective c atom neighbor
    have transported := m.ligandAtomAt_ligandPermAt e c slot
    rw [fixed, trivial] at transported
    change m.ligandAtomAt c slot = (e : Equiv.Perm V) (m.ligandAtomAt c slot) at transported
    rw [atAtom] at transported
    exact changed transported.symm
  exact ⟨parentSlot, atParent, fixed_parent_dichotomy _ _ fixedSlot nontrivial⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingFixedParentParity

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingFixedParentParity.fixed_parent_dichotomy
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingFixedParentParity.local_dichotomy
