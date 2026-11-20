import TetraStereo.OneCenter.LocalizedChemicalRingFixedParentParity
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# A selected ligand rules out an even residual stabilizer

For a nonconstant four-ligand key, a key-preserving even permutation which fixes a ligand
in a nonsingleton key class is the identity. This covers every nonconstant key partition,
including two pairs, without assuming any particular numerical encoding of the keys.

This is a finite structural lemma. Its molecular consumer must derive preservation of the
actual current keys and fixedness of the promoted ligand; neither follows merely from
preservation of the union of the selected classes.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingSelectedStabilizer

open LocalizedChemicalRingFixedParentParity

/-- The three slots outside the fixed point of a nontrivial even action form one orbit. -/
theorem even_fixed_orbit (p : Equiv.Perm (Fin 4)) (fixed : Fin 4)
    (kept : p fixed = fixed) (nontrivial : p ≠ 1) (even : permHandedness p = 1)
    (a b : Fin 4) (aOutside : a ≠ fixed) (bOutside : b ≠ fixed) :
    b = a ∨ b = p a ∨ b = p (p a) := by
  obtain odd | ⟨_, _, moved⟩ := fixed_parent_dichotomy p fixed kept nontrivial
  · rw [even] at odd
    norm_num at odd
  · have finite : ∀ (q : Equiv.Perm (Fin 4)) (f x y : Fin 4),
        q f = f → (∀ i, i ≠ f → q i ≠ i) → x ≠ f → y ≠ f →
          y = x ∨ y = q x ∨ y = q (q x) := by
      decide +kernel
    exact finite p fixed a b kept moved aOutside bOutside

/-- A nontrivial even stabilizer fixing one member of a tied pair forces all four keys equal. -/
theorem constant_of_selected_even_stabilizer {Key : Type*}
    (key : Fin 4 → Key) (p : Equiv.Perm (Fin 4)) (selected partner : Fin 4)
    (kept : p selected = selected) (nontrivial : p ≠ 1)
    (even : permHandedness p = 1) (preserves : ∀ i, key (p i) = key i)
    (different : partner ≠ selected) (tied : key partner = key selected) :
    ∀ i, key i = key selected := by
  intro i
  by_cases hi : i = selected
  · simp only [hi]
  · rcases even_fixed_orbit p selected kept nontrivial even partner i different hi with
      rfl | rfl | rfl
    · exact tied
    · exact (preserves partner).trans tied
    · exact (preserves (p partner)).trans ((preserves partner).trans tied)

/-- No nonidentity even residual action can fix a selected ligand of a nonconstant key. -/
theorem selected_even_stabilizer_eq_one {Key : Type*}
    (key : Fin 4 → Key) (p : Equiv.Perm (Fin 4)) (selected partner : Fin 4)
    (kept : p selected = selected) (even : permHandedness p = 1)
    (preserves : ∀ i, key (p i) = key i)
    (different : partner ≠ selected) (tied : key partner = key selected)
    (nonconstant : ¬ ∀ i, key i = key selected) : p = 1 := by
  by_contra nontrivial
  exact nonconstant (constant_of_selected_even_stabilizer key p selected partner kept
    nontrivial even preserves different tied)

/-- A period-three action preserving comparisons fixes each value in a linear order. -/
theorem key_invariant_of_cube_and_order {Key : Type*} [LinearOrder Key]
    (key : Fin 4 → Key) (p : Equiv.Perm (Fin 4)) (cube : p ^ 3 = 1)
    (order : ∀ i j, key (p i) < key (p j) ↔ key i < key j) :
    ∀ i, key (p i) = key i := by
  intro i
  have triple : p (p (p i)) = i := by
    have h := congrArg (fun q : Equiv.Perm (Fin 4) => q i) cube
    simpa only [pow_succ, pow_zero, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using h
  rcases lt_trichotomy (key (p i)) (key i) with lower | equal | higher
  · have second := (order (p i) i).mpr lower
    have third := (order (p (p i)) (p i)).mpr second
    rw [triple] at third
    exact False.elim ((lt_irrefl (key i)) (lt_trans third (lt_trans second lower)))
  · exact equal
  · have second := (order i (p i)).mpr higher
    have third := (order (p i) (p (p i))).mpr second
    rw [triple] at third
    exact False.elim ((lt_irrefl (key i)) (lt_trans higher (lt_trans second third)))

/-- Comparator covariance suffices for the selected stabilizer conclusion. Literal equality
of key records need not be supplied by the molecular transport theorem. -/
theorem selected_even_stabilizer_eq_one_of_order {Key : Type*} [LinearOrder Key]
    (key : Fin 4 → Key) (p : Equiv.Perm (Fin 4)) (selected partner : Fin 4)
    (kept : p selected = selected) (even : permHandedness p = 1)
    (order : ∀ i j, key (p i) < key (p j) ↔ key i < key j)
    (different : partner ≠ selected) (tied : key partner = key selected)
    (nonconstant : ¬ ∀ i, key i = key selected) : p = 1 := by
  by_contra nontrivial
  obtain odd | ⟨_, cube, _⟩ := fixed_parent_dichotomy p selected kept nontrivial
  · rw [even] at odd
    norm_num at odd
  · exact nontrivial (selected_even_stabilizer_eq_one key p selected partner kept even
      (key_invariant_of_cube_and_order key p cube order) different tied nonconstant)

end TetraStereo.OneCenter.LocalizedChemicalRingSelectedStabilizer

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSelectedStabilizer.even_fixed_orbit
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSelectedStabilizer.constant_of_selected_even_stabilizer
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSelectedStabilizer.selected_even_stabilizer_eq_one
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSelectedStabilizer.key_invariant_of_cube_and_order
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSelectedStabilizer.selected_even_stabilizer_eq_one_of_order
