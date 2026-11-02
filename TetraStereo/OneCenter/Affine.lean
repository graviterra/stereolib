import TetraStereo.OneCenter.Geometry
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

open scoped Matrix

noncomputable section

namespace TetrahedralGeometry

/-- Apply a `3 x 3` matrix to a point using the row-vector convention. -/
def applyMatrix (A : Matrix (Fin 3) (Fin 3) ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (x ᵥ* A)

@[simp] theorem applyMatrix_apply
    (A : Matrix (Fin 3) (Fin 3) ℝ) (x : EuclideanSpace ℝ (Fin 3)) (j : Fin 3) :
    applyMatrix A x j = ∑ k, x k * A k j := by
  simp [applyMatrix, Matrix.vecMul, dotProduct, PiLp.toLp_apply]

@[simp] theorem applyMatrix_zero (A : Matrix (Fin 3) (Fin 3) ℝ) :
    applyMatrix A (0 : EuclideanSpace ℝ (Fin 3)) = 0 := by
  ext j
  simp [applyMatrix_apply]

@[simp] theorem applyMatrix_add
    (A : Matrix (Fin 3) (Fin 3) ℝ) (x y : EuclideanSpace ℝ (Fin 3)) :
    applyMatrix A (x + y) = applyMatrix A x + applyMatrix A y := by
  ext j
  simp [applyMatrix_apply, add_mul, Finset.sum_add_distrib]

@[simp] theorem applyMatrix_neg
    (A : Matrix (Fin 3) (Fin 3) ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    applyMatrix A (-x) = -applyMatrix A x := by
  ext j
  simp [applyMatrix_apply]

@[simp] theorem applyMatrix_sub
    (A : Matrix (Fin 3) (Fin 3) ℝ) (x y : EuclideanSpace ℝ (Fin 3)) :
    applyMatrix A (x - y) = applyMatrix A x - applyMatrix A y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, applyMatrix_add, applyMatrix_neg]

@[simp] theorem applyMatrix_mul
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    applyMatrix B (applyMatrix A x) = applyMatrix (A * B) x := by
  ext j
  calc
    applyMatrix B (applyMatrix A x) j
        = ∑ k, (∑ l, x l * A l k) * B k j := by
            simp [applyMatrix_apply]
    _ = ∑ k, ∑ l, x l * A l k * B k j := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [Finset.sum_mul]
    _ = ∑ l, ∑ k, x l * A l k * B k j := by
          rw [Finset.sum_comm]
    _ = ∑ l, x l * ∑ k, A l k * B k j := by
          refine Finset.sum_congr rfl ?_
          intro l hl
          calc
            ∑ k, x l * A l k * B k j = ∑ k, x l * (A l k * B k j) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              ring
            _ = x l * ∑ k, A l k * B k j := by
              rw [Finset.mul_sum]
    _ = applyMatrix (A * B) x j := by
          simp [applyMatrix_apply, Matrix.mul_apply]

/-- Apply the linear map `x ↦ xA` to every vertex of a realization. -/
def mapLinear (g : TetrahedralGeometry) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    TetrahedralGeometry where
  vertex i := applyMatrix A (g.vertex i)

/-- Apply the affine map `x ↦ xA + b` to every vertex of a realization. -/
def mapAffine (g : TetrahedralGeometry) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (b : EuclideanSpace ℝ (Fin 3)) : TetrahedralGeometry :=
  translate (mapLinear g A) b

@[simp] theorem reindex_mapAffine
    (g : TetrahedralGeometry) (sigma : Equiv.Perm (Fin 4))
    (A : Matrix (Fin 3) (Fin 3) ℝ) (b : EuclideanSpace ℝ (Fin 3)) :
    reindex (mapAffine g A b) sigma = mapAffine (reindex g sigma) A b := by
  ext i j
  simp [reindex, mapAffine, translate, mapLinear]

/-- A linear change of coordinates preserves orientation when its determinant is positive. -/
def OrientationPreserving (A : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  0 < Matrix.det A

/-- A linear change of coordinates reverses orientation when its determinant is negative. -/
def OrientationReversing (A : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  Matrix.det A < 0

@[simp] theorem edgeMatrix_translate
    (g : TetrahedralGeometry) (t : EuclideanSpace ℝ (Fin 3)) :
    edgeMatrix (translate g t) = edgeMatrix g := by
  ext i j
  simp [edgeMatrix, translate]

@[simp] theorem edgeMatrix_mapLinear
    (g : TetrahedralGeometry) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    edgeMatrix (mapLinear g A) = edgeMatrix g * A := by
  ext i j
  calc
    edgeMatrix (mapLinear g A) i j
        = (∑ k, g.vertex i.castSucc k * A k j) - ∑ k, g.vertex 3 k * A k j := by
            simp [edgeMatrix, mapLinear, applyMatrix_apply]
    _ = ∑ k, (g.vertex i.castSucc k * A k j - g.vertex 3 k * A k j) := by
          rw [← Finset.sum_sub_distrib]
    _ = ∑ k, (g.vertex i.castSucc k - g.vertex 3 k) * A k j := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          ring
    _ = (edgeMatrix g * A) i j := by
          simp [edgeMatrix, Matrix.mul_apply]

@[simp] theorem edgeMatrix_mapAffine
    (g : TetrahedralGeometry) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (b : EuclideanSpace ℝ (Fin 3)) :
    edgeMatrix (mapAffine g A b) = edgeMatrix g * A := by
  simp [mapAffine]

@[simp] theorem mapLinear_mapLinear
    (g : TetrahedralGeometry) (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    mapLinear (mapLinear g A) B = mapLinear g (A * B) := by
  ext i j
  simp [mapLinear, applyMatrix_mul]

@[simp] theorem mapAffine_mapAffine
    (g : TetrahedralGeometry) (A B : Matrix (Fin 3) (Fin 3) ℝ)
    (b c : EuclideanSpace ℝ (Fin 3)) :
    mapAffine (mapAffine g A b) B c = mapAffine g (A * B) (applyMatrix B b + c) := by
  ext i j
  simp [mapAffine, mapLinear, translate, applyMatrix_add, applyMatrix_mul, add_assoc]

theorem orientedVolume_mapLinear
    (g : TetrahedralGeometry) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    orientedVolume (mapLinear g A) = orientedVolume g * Matrix.det A := by
  rw [orientedVolume_eq_edgeMatrix_det, edgeMatrix_mapLinear, Matrix.det_mul,
    orientedVolume_eq_edgeMatrix_det]

theorem orientedVolume_mapAffine
    (g : TetrahedralGeometry) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (b : EuclideanSpace ℝ (Fin 3)) :
    orientedVolume (mapAffine g A b) = orientedVolume g * Matrix.det A := by
  rw [mapAffine, orientedVolume_translate, orientedVolume_mapLinear]

theorem nondegenerate_mapLinear_iff
    (g : TetrahedralGeometry) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    Nondegenerate (mapLinear g A) ↔ Nondegenerate g ∧ Matrix.det A ≠ 0 := by
  simp [Nondegenerate, orientedVolume_mapLinear]

theorem nondegenerate_mapAffine_iff
    (g : TetrahedralGeometry) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (b : EuclideanSpace ℝ (Fin 3)) :
    Nondegenerate (mapAffine g A b) ↔ Nondegenerate g ∧ Matrix.det A ≠ 0 := by
  simp [Nondegenerate, orientedVolume_mapAffine]

theorem nondegenerate_mapAffine_of_det_ne_zero
    (g : TetrahedralGeometry) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (b : EuclideanSpace ℝ (Fin 3)) (hg : Nondegenerate g) (hA : Matrix.det A ≠ 0) :
    Nondegenerate (mapAffine g A b) := by
  exact (nondegenerate_mapAffine_iff g A b).2 ⟨hg, hA⟩

theorem handedness_mapAffine_of_orientationPreserving
    (g : TetrahedralGeometry) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (b : EuclideanSpace ℝ (Fin 3)) (hA : OrientationPreserving A) :
    handedness (mapAffine g A b) = handedness g := by
  obtain hneg | hzero | hpos := lt_trichotomy (orientedVolume g) 0
  · have hmul : orientedVolume g * Matrix.det A < 0 := mul_neg_of_neg_of_pos hneg hA
    simp [handedness, orientedVolume_mapAffine, Real.sign_of_neg hmul, Real.sign_of_neg hneg]
  · simp [handedness, orientedVolume_mapAffine, hzero]
  · have hmul : 0 < orientedVolume g * Matrix.det A := mul_pos hpos hA
    simp [handedness, orientedVolume_mapAffine, Real.sign_of_pos hmul, Real.sign_of_pos hpos]

theorem handedness_mapAffine_of_orientationReversing
    (g : TetrahedralGeometry) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (b : EuclideanSpace ℝ (Fin 3)) (hA : OrientationReversing A) :
    handedness (mapAffine g A b) = -handedness g := by
  obtain hneg | hzero | hpos := lt_trichotomy (orientedVolume g) 0
  · have hmul : 0 < orientedVolume g * Matrix.det A := mul_pos_of_neg_of_neg hneg hA
    simp [handedness, orientedVolume_mapAffine, Real.sign_of_pos hmul, Real.sign_of_neg hneg]
  · simp [handedness, orientedVolume_mapAffine, hzero]
  · have hmul : orientedVolume g * Matrix.det A < 0 := mul_neg_of_pos_of_neg hpos hA
    simp [handedness, orientedVolume_mapAffine, Real.sign_of_neg hmul, Real.sign_of_pos hpos]

/-- A nondegenerate tetrahedral realization, where handedness is automatically `±1`. -/
abbrev Realization := { g : TetrahedralGeometry // Nondegenerate g }

namespace Realization

@[simp] theorem handedness_eq_one_or_eq_neg_one (g : Realization) :
    handedness g.1 = 1 ∨ handedness g.1 = -1 := by
  by_cases hpos : 0 < orientedVolume g.1
  · left
    simp [handedness, Real.sign_of_pos hpos]
  · right
    have hle : orientedVolume g.1 ≤ 0 := le_of_not_gt hpos
    have hneg : orientedVolume g.1 < 0 := lt_of_le_of_ne hle g.2
    simp [handedness, Real.sign_of_neg hneg]

/-- Affine maps with nonzero determinant act on nondegenerate realizations. -/
def mapAffine (g : Realization) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (b : EuclideanSpace ℝ (Fin 3)) (hA : Matrix.det A ≠ 0) : Realization :=
  ⟨TetrahedralGeometry.mapAffine g.1 A b, nondegenerate_mapAffine_of_det_ne_zero g.1 A b g.2 hA⟩

@[simp] theorem coe_mapAffine
    (g : Realization) (A : Matrix (Fin 3) (Fin 3) ℝ)
    (b : EuclideanSpace ℝ (Fin 3)) (hA : Matrix.det A ≠ 0) :
    (mapAffine g A b hA : TetrahedralGeometry) = TetrahedralGeometry.mapAffine g.1 A b := rfl

end Realization

/-- `h` is an orientation-preserving affine image of `g`. -/
def OrientationPreservingAffineImage (g h : TetrahedralGeometry) : Prop :=
  ∃ A b, OrientationPreserving A ∧ h = mapAffine g A b

/-- `h` is an orientation-reversing affine image of `g`. -/
def OrientationReversingAffineImage (g h : TetrahedralGeometry) : Prop :=
  ∃ A b, OrientationReversing A ∧ h = mapAffine g A b

theorem handedness_eq_of_orientationPreservingAffineImage
    {g h : TetrahedralGeometry} (hgh : OrientationPreservingAffineImage g h) :
    handedness h = handedness g := by
  rcases hgh with ⟨A, b, hA, rfl⟩
  exact handedness_mapAffine_of_orientationPreserving g A b hA

theorem handedness_neg_eq_of_orientationReversingAffineImage
    {g h : TetrahedralGeometry} (hgh : OrientationReversingAffineImage g h) :
    handedness h = -handedness g := by
  rcases hgh with ⟨A, b, hA, rfl⟩
  exact handedness_mapAffine_of_orientationReversing g A b hA

end TetrahedralGeometry

end

end OneCenter
end TetraStereo
