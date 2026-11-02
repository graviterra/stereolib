import TetraStereo.OneCenter.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

open scoped Matrix

noncomputable section

/-- A geometric realization of a tetrahedral center by four points in `R^3`. -/
structure TetrahedralGeometry where
  vertex : Fin 4 → EuclideanSpace ℝ (Fin 3)

namespace TetrahedralGeometry

@[ext] theorem ext {g h : TetrahedralGeometry}
    (hvertex : ∀ i, g.vertex i = h.vertex i) : g = h := by
  cases g
  cases h
  congr
  funext i
  exact hvertex i

/-- The homogeneous-coordinate row attached to the `i`-th vertex. -/
def homogeneousRow (g : TetrahedralGeometry) (i : Fin 4) : Fin 4 → ℝ :=
  ![g.vertex i 0, g.vertex i 1, g.vertex i 2, 1]

/-- The `4 x 4` homogeneous-coordinate matrix of a tetrahedron. -/
def homogeneousMatrix (g : TetrahedralGeometry) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i => homogeneousRow g i

/-- The translation vector embedded into homogeneous coordinates. -/
def translationVector (t : EuclideanSpace ℝ (Fin 3)) : Fin 4 → ℝ :=
  ![t 0, t 1, t 2, 0]

/-- The homogeneous-coordinate matrix of translation by `t`. -/
def translationMatrix (t : EuclideanSpace ℝ (Fin 3)) : Matrix (Fin 4) (Fin 4) ℝ :=
  1 + Matrix.vecMulVec (Pi.single (3 : Fin 4) (1 : ℝ)) (translationVector t)

/-- The usual edge-difference matrix anchored at the fourth vertex. -/
def edgeMatrix (g : TetrahedralGeometry) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => g.vertex i.castSucc j - g.vertex 3 j

/-- The oriented volume is the affine determinant of the four homogeneous-coordinate vertices. -/
def orientedVolume (g : TetrahedralGeometry) : ℝ :=
  Matrix.det (homogeneousMatrix g)

/-- Nondegenerate realizations are exactly those with nonzero oriented volume. -/
def Nondegenerate (g : TetrahedralGeometry) : Prop := orientedVolume g ≠ 0

/-- The geometric handedness extracted from oriented volume, valued in `{-1, 0, 1}`. -/
def handedness (g : TetrahedralGeometry) : ℝ := Real.sign (orientedVolume g)

/-- Translation by a common displacement vector. -/
def translate (g : TetrahedralGeometry) (t : EuclideanSpace ℝ (Fin 3)) : TetrahedralGeometry where
  vertex i := g.vertex i + t

/-- Reindex the four vertices by a permutation of the tetrahedron. -/
def reindex (g : TetrahedralGeometry) (sigma : Equiv.Perm (Fin 4)) : TetrahedralGeometry where
  vertex i := g.vertex (sigma i)

@[simp] theorem homogeneousMatrix_reindex
    (g : TetrahedralGeometry) (sigma : Equiv.Perm (Fin 4)) :
    homogeneousMatrix (reindex g sigma) = (homogeneousMatrix g).submatrix sigma id := by
  ext i j
  simp [homogeneousMatrix, homogeneousRow, reindex]

lemma vecMul_vecMulVec (r u v : Fin 4 → ℝ) :
    r ᵥ* Matrix.vecMulVec u v = (r ⬝ᵥ u) • v := by
  ext j
  simp [Matrix.vecMul, Matrix.vecMulVec, dotProduct]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro x hx
  ring

@[simp] theorem homogeneousRow_translate
    (g : TetrahedralGeometry) (t : EuclideanSpace ℝ (Fin 3)) (i : Fin 4) :
    homogeneousRow (translate g t) i = homogeneousRow g i + translationVector t := by
  simp [homogeneousRow, translationVector, translate]

theorem homogeneousRow_mul_translationMatrix
    (g : TetrahedralGeometry) (t : EuclideanSpace ℝ (Fin 3)) (i : Fin 4) :
    homogeneousRow g i ᵥ* translationMatrix t = homogeneousRow (translate g t) i := by
  calc
    homogeneousRow g i ᵥ* translationMatrix t
        = homogeneousRow g i ᵥ* (1 : Matrix (Fin 4) (Fin 4) ℝ) +
            homogeneousRow g i ᵥ* Matrix.vecMulVec (Pi.single (3 : Fin 4) (1 : ℝ))
              (translationVector t) := by
            simp [translationMatrix, Matrix.vecMul_add]
    _ = homogeneousRow g i +
          ((homogeneousRow g i) ⬝ᵥ Pi.single (3 : Fin 4) (1 : ℝ)) • translationVector t := by
          simp [Matrix.vecMul_one, vecMul_vecMulVec]
    _ = homogeneousRow g i + translationVector t := by
          simp [homogeneousRow, dotProduct_single]
    _ = homogeneousRow (translate g t) i := by
          simp [homogeneousRow_translate]

@[simp] theorem homogeneousMatrix_translate
    (g : TetrahedralGeometry) (t : EuclideanSpace ℝ (Fin 3)) :
    homogeneousMatrix (translate g t) = homogeneousMatrix g * translationMatrix t := by
  ext i j
  simpa [homogeneousMatrix, Matrix.mul_apply] using
    congrArg (fun v => v j) (homogeneousRow_mul_translationMatrix g t i).symm

theorem translationMatrix_blockTriangular (t : EuclideanSpace ℝ (Fin 3)) :
    (translationMatrix t).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have hij' : i < j := by
    simpa using hij
  have hi_lt_3 : i < (3 : Fin 4) := lt_of_lt_of_le hij' (Nat.le_of_lt_succ j.2)
  have hi3 : i ≠ (3 : Fin 4) := hi_lt_3.ne
  have hijne : i ≠ j := hij'.ne
  simp [translationMatrix, translationVector, Matrix.vecMulVec, hi3, hijne]

@[simp] theorem translationMatrix_det (t : EuclideanSpace ℝ (Fin 3)) :
    Matrix.det (translationMatrix t) = 1 := by
  rw [Matrix.det_of_lowerTriangular (translationMatrix t) (translationMatrix_blockTriangular t)]
  rw [Fin.prod_univ_four]
  simp [translationMatrix, translationVector, Matrix.vecMulVec]

@[simp] theorem orientedVolume_translate
    (g : TetrahedralGeometry) (t : EuclideanSpace ℝ (Fin 3)) :
    orientedVolume (translate g t) = orientedVolume g := by
  simp [orientedVolume, Matrix.det_mul]

@[simp] theorem nondegenerate_translate
    (g : TetrahedralGeometry) (t : EuclideanSpace ℝ (Fin 3)) :
    Nondegenerate (translate g t) ↔ Nondegenerate g := by
  simp [Nondegenerate]

theorem orientedVolume_eq_edgeMatrix_det (g : TetrahedralGeometry) :
    orientedVolume g = Matrix.det (edgeMatrix g) := by
  have htranslate : orientedVolume g = orientedVolume (translate g (-g.vertex 3)) := by
    exact (orientedVolume_translate g (-g.vertex 3)).symm
  have hs0 : Fin.succAbove (3 : Fin 4) (0 : Fin 3) = 0 := rfl
  have hs1 : Fin.succAbove (3 : Fin 4) (1 : Fin 3) = 1 := rfl
  have hs2 : Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 := rfl
  rw [htranslate, orientedVolume]
  rw [Matrix.det_succ_row _ (3 : Fin 4), Fin.sum_univ_four]
  simp [hs0, hs1, hs2, homogeneousMatrix, homogeneousRow, edgeMatrix, translate,
    Matrix.det_fin_three]
  norm_num
  ring_nf

@[simp] theorem handedness_translate
    (g : TetrahedralGeometry) (t : EuclideanSpace ℝ (Fin 3)) :
    handedness (translate g t) = handedness g := by
  simp [handedness]

@[simp] theorem orientedVolume_reindex
    (g : TetrahedralGeometry) (sigma : Equiv.Perm (Fin 4)) :
    orientedVolume (reindex g sigma) = permHandedness sigma * orientedVolume g := by
  simp [orientedVolume, homogeneousMatrix_reindex, Matrix.det_permute, permHandedness]

@[simp] theorem nondegenerate_reindex
    (g : TetrahedralGeometry) (sigma : Equiv.Perm (Fin 4)) :
    Nondegenerate (reindex g sigma) ↔ Nondegenerate g := by
  rcases permHandedness_eq_one_or_eq_neg_one sigma with hsigma | hsigma <;>
    simp [Nondegenerate, orientedVolume_reindex, hsigma]

theorem orientedVolume_reindex_even
    (g : TetrahedralGeometry) (sigma : Equiv.Perm (Fin 4)) (hsigma : permHandedness sigma = 1) :
    orientedVolume (reindex g sigma) = orientedVolume g := by
  simp [hsigma]

theorem orientedVolume_reindex_odd
    (g : TetrahedralGeometry) (sigma : Equiv.Perm (Fin 4)) (hsigma : permHandedness sigma = -1) :
    orientedVolume (reindex g sigma) = -orientedVolume g := by
  simp [hsigma]

theorem handedness_reindex_even
    (g : TetrahedralGeometry) (sigma : Equiv.Perm (Fin 4)) (hsigma : permHandedness sigma = 1) :
    handedness (reindex g sigma) = handedness g := by
  simp [handedness, hsigma]

theorem handedness_reindex_odd
    (g : TetrahedralGeometry) (sigma : Equiv.Perm (Fin 4)) (hsigma : permHandedness sigma = -1) :
    handedness (reindex g sigma) = -handedness g := by
  simp [handedness, hsigma, Real.sign_neg]

end TetrahedralGeometry

end

end OneCenter
end TetraStereo
