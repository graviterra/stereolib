import TetraStereo.KernelOnly
import Mathlib.GroupTheory.Perm.Basic

set_option autoImplicit false

namespace TetraStereo.OneCenter.LocalizedChemicalRingScalarSymmetry

/-- A symmetry of the ranked molecule that fixes the focus and the active reference
but exchanges two different ligands of the focus. -/
def HasExchange {A : Type*} (preserves : Equiv.Perm A → Prop) (focus mark : A)
    (ligand : A → Prop) : Prop :=
  ∃ (e : Equiv.Perm A) (a b : A), preserves e ∧ e focus = focus ∧ e mark = mark ∧
    ligand a ∧ ligand b ∧ a ≠ b ∧ e a = b ∧ e b = a

/-- Every asymmetric priority comparison invariant under the marked molecular
symmetries has an unresolved ligand pair. This includes comparisons without keys. -/
theorem tied_pair {A : Type*} {preserves : Equiv.Perm A → Prop} {focus mark : A}
    {ligand : A → Prop} (exchange : HasExchange preserves focus mark ligand)
    (before : A → A → Prop) (asymm : ∀ a b, before a b → ¬ before b a)
    (invariant : ∀ e : Equiv.Perm A, preserves e → e focus = focus → e mark = mark →
      ∀ a b, before a b → before (e a) (e b)) :
    ∃ a b, ligand a ∧ ligand b ∧ a ≠ b ∧ ¬ before a b ∧ ¬ before b a := by
  obtain ⟨e,a,b,keep,center,ref,la,lb,ne,ab,ba⟩ := exchange
  have swapped := invariant e keep center ref
  refine ⟨a,b,la,lb,ne,?_,?_⟩
  · intro h
    exact asymm a b h (by simpa only [ab,ba] using swapped a b h)
  · intro h
    exact asymm b a h (by simpa only [ab,ba] using swapped b a h)

end TetraStereo.OneCenter.LocalizedChemicalRingScalarSymmetry
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingScalarSymmetry.tied_pair
