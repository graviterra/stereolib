import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

/-- A tetrahedral stereocenter together with an injective ordering of its four ligands. -/
structure TetrahedralCenter (α : Type*) where
  ligand : Fin 4 → α
  injective_ligand : Function.Injective ligand

attribute [simp] TetrahedralCenter.injective_ligand

namespace TetrahedralCenter

variable {α : Type*}

/-- Reindex the local ligand order by a permutation of the tetrahedron. -/
def reindex (c : TetrahedralCenter α) (σ : Equiv.Perm (Fin 4)) : TetrahedralCenter α where
  ligand i := c.ligand (σ i)
  injective_ligand := by
    intro i j hij
    apply σ.injective
    exact c.injective_ligand hij

@[simp] theorem reindex_ligand (c : TetrahedralCenter α) (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    (reindex c σ).ligand i = c.ligand (σ i) := rfl

@[simp] theorem reindex_one (c : TetrahedralCenter α) : reindex c 1 = c := by
  cases c
  rfl

@[simp] theorem reindex_mul (c : TetrahedralCenter α) (σ τ : Equiv.Perm (Fin 4)) :
    reindex (reindex c σ) τ = reindex c (σ * τ) := by
  cases c
  rfl

end TetrahedralCenter

/-- The parity-based handedness carried by a local reindexing, valued in `{-1, 1}`. -/
def permHandedness (σ : Equiv.Perm (Fin 4)) : ℝ := σ.sign

@[simp] theorem permHandedness_one : permHandedness (1 : Equiv.Perm (Fin 4)) = 1 := by
  norm_num [permHandedness, Equiv.Perm.sign_one]

@[simp] theorem permHandedness_mul (σ τ : Equiv.Perm (Fin 4)) :
    permHandedness (σ * τ) = permHandedness σ * permHandedness τ := by
  norm_num [permHandedness, Equiv.Perm.sign_mul]

@[simp] theorem permHandedness_inv (σ : Equiv.Perm (Fin 4)) :
    permHandedness σ⁻¹ = permHandedness σ := by
  norm_num [permHandedness, Equiv.Perm.sign_inv]

@[simp] theorem permHandedness_swap :
    permHandedness (Equiv.swap (0 : Fin 4) 1) = -1 := by
  norm_num [permHandedness, Equiv.Perm.sign_swap (by simp : (0 : Fin 4) ≠ 1)]

theorem permHandedness_eq_one_or_eq_neg_one (σ : Equiv.Perm (Fin 4)) :
    permHandedness σ = 1 ∨ permHandedness σ = -1 := by
  rcases Int.units_eq_one_or σ.sign with hσ | hσ
  · left
    simp [permHandedness, hσ]
  · right
    simp [permHandedness, hσ]

theorem permHandedness_mul_self (σ : Equiv.Perm (Fin 4)) :
    permHandedness σ * permHandedness σ = 1 := by
  rcases permHandedness_eq_one_or_eq_neg_one σ with hσ | hσ <;> simp [hσ]

@[simp] theorem permHandedness_conj (σ τ : Equiv.Perm (Fin 4)) :
    permHandedness (σ * τ * σ⁻¹) = permHandedness τ := by
  have hmul :
      permHandedness σ * permHandedness τ * permHandedness σ =
        (permHandedness σ * permHandedness σ) * permHandedness τ := by
    calc
      permHandedness σ * permHandedness τ * permHandedness σ
          = permHandedness σ * (permHandedness τ * permHandedness σ) := by
              simp [mul_assoc]
      _ = permHandedness σ * (permHandedness σ * permHandedness τ) := by
              simp [mul_comm]
      _ = (permHandedness σ * permHandedness σ) * permHandedness τ := by
              simp [mul_assoc]
  calc
    permHandedness (σ * τ * σ⁻¹)
        = permHandedness σ * permHandedness τ * permHandedness σ := by
            simp [mul_assoc, permHandedness_mul]
    _ = (permHandedness σ * permHandedness σ) * permHandedness τ := hmul
    _ = permHandedness τ := by
          simp [permHandedness_mul_self]

@[simp] theorem permHandedness_conj_inv (σ τ : Equiv.Perm (Fin 4)) :
    permHandedness (σ⁻¹ * τ * σ) = permHandedness τ := by
  simpa [mul_assoc] using (permHandedness_conj (σ := σ⁻¹) (τ := τ))

end OneCenter
end TetraStereo
