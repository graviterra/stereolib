import TetraStereo.OneCenter.ChiralityClass
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Geometry.Euclidean.Projection

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

open TetrahedralGeometry
open scoped Matrix RealInnerProductSpace

noncomputable section

attribute [local instance] starRingOfComm

namespace TetrahedralGeometry

@[simp] theorem applyMatrix_one (x : EuclideanSpace ℝ (Fin 3)) :
    applyMatrix (1 : Matrix (Fin 3) (Fin 3) ℝ) x = x := by
  ext j
  simp [applyMatrix_apply, Matrix.one_apply]

@[simp] theorem applyMatrix_smul (A : Matrix (Fin 3) (Fin 3) ℝ)
    (c : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    applyMatrix A (c • x) = c • applyMatrix A x := by
  ext j
  simp [applyMatrix_apply, Finset.mul_sum, mul_left_comm, mul_comm]

@[simp] theorem mapLinear_one (g : TetrahedralGeometry) :
    mapLinear g (1 : Matrix (Fin 3) (Fin 3) ℝ) = g := by
  ext i j
  simp [mapLinear]

@[simp] theorem mapAffine_one (g : TetrahedralGeometry)
    (b : EuclideanSpace ℝ (Fin 3)) :
    mapAffine g (1 : Matrix (Fin 3) (Fin 3) ℝ) b = translate g b := by
  simp [mapAffine]

/-- Orthogonal `3 x 3` matrices acting on Euclidean coordinates by the row-vector convention. -/
abbrev OrthogonalMatrix := Matrix.orthogonalGroup (Fin 3) ℝ

@[simp] theorem coe_inv_orthogonalMatrix (Q : OrthogonalMatrix) :
    ((Q : Matrix (Fin 3) (Fin 3) ℝ)⁻¹) =
      (((Q⁻¹ : OrthogonalMatrix) : Matrix (Fin 3) (Fin 3) ℝ)) := by
  apply Matrix.inv_eq_right_inv
  simp

@[simp] theorem coe_inv_mul_orthogonalMatrix (Q : OrthogonalMatrix) :
    (((Q⁻¹ : OrthogonalMatrix) : Matrix (Fin 3) (Fin 3) ℝ) *
      (Q : Matrix (Fin 3) (Fin 3) ℝ)) = 1 := by
  change (((Q⁻¹ : OrthogonalMatrix) * Q : OrthogonalMatrix) :
    Matrix (Fin 3) (Fin 3) ℝ) = 1
  simp

@[simp] theorem coe_mul_inv_orthogonalMatrix (Q : OrthogonalMatrix) :
    ((Q : Matrix (Fin 3) (Fin 3) ℝ) *
      (((Q⁻¹ : OrthogonalMatrix) : Matrix (Fin 3) (Fin 3) ℝ))) = 1 := by
  change ((Q * (Q⁻¹ : OrthogonalMatrix) : OrthogonalMatrix) :
    Matrix (Fin 3) (Fin 3) ℝ) = 1
  simp

/-- Proper rotations are the determinant-`1` orthogonal matrices. -/
abbrev ProperRotation := Matrix.specialOrthogonalGroup (Fin 3) ℝ

/-- Improper rotations are the determinant-`-1` orthogonal matrices.
This is broader than plane reflections: it also includes central inversion and rotoinversions. -/
abbrev ImproperRotation :=
  { A : OrthogonalMatrix // Matrix.det (A : Matrix (Fin 3) (Fin 3) ℝ) = -1 }

namespace ProperRotation

theorem mem_orthogonalGroup (A : ProperRotation) :
    (A : Matrix (Fin 3) (Fin 3) ℝ) ∈ Matrix.orthogonalGroup (Fin 3) ℝ :=
  ((Matrix.mem_specialOrthogonalGroup_iff
    (A := (A : Matrix (Fin 3) (Fin 3) ℝ))).1 A.2).1

@[simp] theorem det_eq_one (A : ProperRotation) :
    Matrix.det (A : Matrix (Fin 3) (Fin 3) ℝ) = 1 :=
  ((Matrix.mem_specialOrthogonalGroup_iff
    (A := (A : Matrix (Fin 3) (Fin 3) ℝ))).1 A.2).2

def toOrthogonalMatrix (A : ProperRotation) : OrthogonalMatrix :=
  ⟨(A : Matrix (Fin 3) (Fin 3) ℝ), ProperRotation.mem_orthogonalGroup A⟩

end ProperRotation

namespace ImproperRotation

@[simp] theorem det_eq_neg_one (A : ImproperRotation) :
    Matrix.det (A.1 : Matrix (Fin 3) (Fin 3) ℝ) = -1 :=
  A.2

/-- Rotate an improper orthogonal map by a proper rotation in the point-space row-action
convention. When the input is a plane reflection, this rotates its reflecting plane accordingly. -/
def rotateBy (R : ProperRotation) (A : ImproperRotation) : ImproperRotation := by
  let Q : OrthogonalMatrix := ProperRotation.toOrthogonalMatrix R
  have hQ : Matrix.det (Q : Matrix (Fin 3) (Fin 3) ℝ) = 1 :=
    ProperRotation.det_eq_one R
  refine ⟨Q⁻¹ * A.1 * Q, ?_⟩
  change Matrix.det
      ((((Q⁻¹ : OrthogonalMatrix) : Matrix (Fin 3) (Fin 3) ℝ) *
        (A.1 : Matrix (Fin 3) (Fin 3) ℝ)) * (Q : Matrix (Fin 3) (Fin 3) ℝ)) = -1
  rw [Matrix.det_mul, Matrix.det_mul]
  simp [hQ, A.det_eq_neg_one, star, Matrix.det_transpose]

end ImproperRotation

/-- Reflection across the `yz`-plane. -/
def reflectYZMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![-(1 : ℝ), 1, 1]

theorem reflectYZMatrix_mem_orthogonalGroup :
    reflectYZMatrix ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reflectYZMatrix]

@[simp] theorem det_reflectYZMatrix :
    Matrix.det reflectYZMatrix = -1 := by
  rw [reflectYZMatrix, Matrix.det_diagonal, Fin.prod_univ_three]
  norm_num
  rfl

/-- The linear reflection fixing the `yz`-plane. -/
def yzPlaneReflection : ImproperRotation :=
  ⟨⟨reflectYZMatrix, reflectYZMatrix_mem_orthogonalGroup⟩, det_reflectYZMatrix⟩

@[simp] theorem apply_reflectYZMatrix_zero (x : EuclideanSpace ℝ (Fin 3)) :
    applyMatrix reflectYZMatrix x 0 = -x 0 := by
  simp [reflectYZMatrix, applyMatrix_apply, Fin.sum_univ_three]

@[simp] theorem apply_reflectYZMatrix_one (x : EuclideanSpace ℝ (Fin 3)) :
    applyMatrix reflectYZMatrix x 1 = x 1 := by
  simp [reflectYZMatrix, applyMatrix_apply, Fin.sum_univ_three]

@[simp] theorem apply_reflectYZMatrix_two (x : EuclideanSpace ℝ (Fin 3)) :
    applyMatrix reflectYZMatrix x 2 = x 2 := by
  simp [reflectYZMatrix, applyMatrix_apply, Fin.sum_univ_three]

theorem apply_reflectYZMatrix_of_first_zero {x : EuclideanSpace ℝ (Fin 3)} (hx : x 0 = 0) :
    applyMatrix reflectYZMatrix x = x := by
  ext j
  fin_cases j <;> simp [reflectYZMatrix, applyMatrix_apply, Fin.sum_univ_three, hx]

theorem apply_reflectYZMatrix_eq_self_iff (x : EuclideanSpace ℝ (Fin 3)) :
    applyMatrix reflectYZMatrix x = x ↔ x 0 = 0 := by
  constructor
  · intro h
    have h0' : applyMatrix reflectYZMatrix x 0 = x 0 := congrArg (fun y => y 0) h
    have h0 : -x 0 = x 0 := by
      simpa [reflectYZMatrix, applyMatrix_apply, Fin.sum_univ_three] using h0'
    have htwo : (2 : ℝ) * x 0 = 0 := by
      calc
        (2 : ℝ) * x 0 = x 0 + x 0 := by ring
        _ = (-x 0) + x 0 := by rw [h0]
        _ = 0 := by ring
    rcases mul_eq_zero.mp htwo with htwo | hx
    · norm_num at htwo
    · exact hx
  · exact apply_reflectYZMatrix_of_first_zero

/-- Euclidean motions are affine maps whose linear part is orthogonal. -/
structure EuclideanMotion where
  linear : OrthogonalMatrix
  translation : EuclideanSpace ℝ (Fin 3)

namespace EuclideanMotion

@[ext] theorem ext {m n : EuclideanMotion}
    (hLinear : m.linear = n.linear) (hTranslation : m.translation = n.translation) :
    m = n := by
  cases m
  cases n
  cases hLinear
  cases hTranslation
  rfl

theorem det_ne_zero (m : EuclideanMotion) :
    Matrix.det (m.linear : Matrix (Fin 3) (Fin 3) ℝ) ≠ 0 := by
  exact Matrix.det_ne_zero_of_right_inverse
    ((Matrix.mem_orthogonalGroup_iff
      (A := (m.linear : Matrix (Fin 3) (Fin 3) ℝ))).1 m.linear.2)

instance : One EuclideanMotion where
  one := ⟨1, 0⟩

instance : Mul EuclideanMotion where
  mul m n :=
    ⟨n.linear * m.linear, applyMatrix m.linear n.translation + m.translation⟩

instance : Inv EuclideanMotion where
  inv m :=
    ⟨m.linear⁻¹, -applyMatrix m.linear⁻¹ m.translation⟩

@[simp] theorem one_linear :
    (1 : EuclideanMotion).linear = 1 :=
  rfl

@[simp] theorem one_translation :
    (1 : EuclideanMotion).translation = 0 :=
  rfl

@[simp] theorem mul_linear (m n : EuclideanMotion) :
    (m * n).linear = n.linear * m.linear :=
  rfl

@[simp] theorem mul_translation (m n : EuclideanMotion) :
    (m * n).translation = applyMatrix m.linear n.translation + m.translation :=
  rfl

@[simp] theorem inv_linear (m : EuclideanMotion) :
    m⁻¹.linear = m.linear⁻¹ :=
  rfl

@[simp] theorem inv_translation (m : EuclideanMotion) :
    m⁻¹.translation = -applyMatrix m.linear⁻¹ m.translation :=
  rfl

/-- The pointwise affine action of a Euclidean motion on `R^3`. -/
def applyPoint (m : EuclideanMotion) (x : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  applyMatrix m.linear x + m.translation

@[simp] theorem applyPoint_one (x : EuclideanSpace ℝ (Fin 3)) :
    (1 : EuclideanMotion).applyPoint x = x := by
  simp [EuclideanMotion.applyPoint]

@[simp] theorem applyPoint_mul (m n : EuclideanMotion) (x : EuclideanSpace ℝ (Fin 3)) :
    (m * n).applyPoint x = m.applyPoint (n.applyPoint x) := by
  simp [EuclideanMotion.applyPoint, applyMatrix_add, applyMatrix_mul, add_assoc]

instance : Group EuclideanMotion where
  one := 1
  mul := (· * ·)
  inv := Inv.inv
  mul_assoc a b c := by
    ext <;> simp [applyMatrix_add, applyMatrix_mul, add_assoc, mul_assoc]
  one_mul a := by
    ext <;> simp
  mul_one a := by
    ext <;> simp
  inv_mul_cancel a := by
    ext
    · simp
    · have hinv : ((↑a.linear)⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) = (↑a.linear)ᵀ := by
        apply Matrix.inv_eq_right_inv
        exact (Matrix.mem_orthogonalGroup_iff
          (A := (a.linear : Matrix (Fin 3) (Fin 3) ℝ))).1 a.linear.2
      simp [applyMatrix_apply, hinv]

instance : SMul EuclideanMotion TetrahedralGeometry where
  smul m g := mapAffine g m.linear m.translation

@[simp] theorem smul_def (m : EuclideanMotion) (g : TetrahedralGeometry) :
    m • g = mapAffine g m.linear m.translation :=
  rfl

instance : MulAction EuclideanMotion TetrahedralGeometry where
  smul := (· • ·)
  one_smul g := by
    ext i j
    simp [EuclideanMotion.smul_def, translate]
  mul_smul m n g := by
    simp [mapAffine_mapAffine]

/-- Euclidean motions send nondegenerate realizations to nondegenerate realizations. -/
def mapRealization (m : EuclideanMotion) (g : Realization) : Realization :=
  Realization.mapAffine g m.linear m.translation m.det_ne_zero

@[simp] theorem coe_mapRealization (m : EuclideanMotion) (g : Realization) :
    (m.mapRealization g : TetrahedralGeometry) = m • (g : TetrahedralGeometry) := rfl

@[simp] theorem one_mapRealization (g : Realization) :
    (1 : EuclideanMotion).mapRealization g = g := by
  apply Subtype.ext
  ext i j
  simp [EuclideanMotion.mapRealization, translate]

@[simp] theorem mul_mapRealization (m n : EuclideanMotion) (g : Realization) :
    (m * n).mapRealization g = m.mapRealization (n.mapRealization g) := by
  apply Subtype.ext
  ext i j
  simp [EuclideanMotion.mapRealization, mapAffine_mapAffine]

def translationMotion (t : EuclideanSpace ℝ (Fin 3)) : EuclideanMotion :=
  ⟨1, t⟩

@[simp] theorem translationMotion_linear (t : EuclideanSpace ℝ (Fin 3)) :
    (translationMotion t).linear = 1 :=
  rfl

@[simp] theorem translationMotion_translation (t : EuclideanSpace ℝ (Fin 3)) :
    (translationMotion t).translation = t :=
  rfl

@[simp] theorem translationMotion_smul (t : EuclideanSpace ℝ (Fin 3)) (g : TetrahedralGeometry) :
    translationMotion t • g = translate g t := by
  simp [translationMotion]

end EuclideanMotion

instance : SMul EuclideanMotion Realization where
  smul m g := m.mapRealization g

@[simp] theorem smul_realization_def (m : EuclideanMotion) (g : Realization) :
    m • g = m.mapRealization g := rfl

@[simp] theorem coe_smul_realization (m : EuclideanMotion) (g : Realization) :
    ((m • g : Realization) : TetrahedralGeometry) = m • (g : TetrahedralGeometry) := rfl

instance : MulAction EuclideanMotion Realization where
  smul := (· • ·)
  one_smul := EuclideanMotion.one_mapRealization
  mul_smul := EuclideanMotion.mul_mapRealization

/-- Orientation-preserving Euclidean motions are exactly those with determinant `1`. -/
abbrev OrientationPreservingEuclideanMotion :=
  { m : EuclideanMotion // Matrix.det (m.linear : Matrix (Fin 3) (Fin 3) ℝ) = 1 }

/-- Orientation-reversing Euclidean motions are exactly those with determinant `-1`. -/
abbrev OrientationReversingEuclideanMotion :=
  { m : EuclideanMotion // Matrix.det (m.linear : Matrix (Fin 3) (Fin 3) ℝ) = -1 }

namespace OrientationPreservingEuclideanMotion

@[simp] theorem det_eq_one (m : OrientationPreservingEuclideanMotion) :
    Matrix.det (m.1.linear : Matrix (Fin 3) (Fin 3) ℝ) = 1 :=
  m.2

instance : One OrientationPreservingEuclideanMotion where
  one := ⟨1, by simp⟩

instance : Mul OrientationPreservingEuclideanMotion where
  mul m n := ⟨m.1 * n.1, by
    simp [EuclideanMotion.mul_linear, Matrix.det_mul, m.2, n.2]⟩

instance : Inv OrientationPreservingEuclideanMotion where
  inv m := ⟨m.1⁻¹, by
    change Matrix.det (star (m.1.linear : Matrix (Fin 3) (Fin 3) ℝ)) = 1
    simp [star, Matrix.det_transpose, m.2]⟩

instance : Group OrientationPreservingEuclideanMotion where
  one := 1
  mul := (· * ·)
  inv := Inv.inv
  mul_assoc a b c := by
    apply Subtype.ext
    change ((a.1 * b.1) * c.1) = (a.1 * (b.1 * c.1))
    simp [mul_assoc]
  one_mul a := by
    apply Subtype.ext
    change ((1 : EuclideanMotion) * a.1) = a.1
    simp
  mul_one a := by
    apply Subtype.ext
    change (a.1 * (1 : EuclideanMotion)) = a.1
    simp
  inv_mul_cancel a := by
    apply Subtype.ext
    change (a.1⁻¹ * a.1) = (1 : EuclideanMotion)
    simp

theorem linear_mem_specialOrthogonalGroup (m : OrientationPreservingEuclideanMotion) :
    ((m.1.linear : Matrix (Fin 3) (Fin 3) ℝ) ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) := by
  exact (Matrix.mem_specialOrthogonalGroup_iff
    (A := (m.1.linear : Matrix (Fin 3) (Fin 3) ℝ))).2 ⟨m.1.linear.2, m.2⟩

def translationMotion (t : EuclideanSpace ℝ (Fin 3)) : OrientationPreservingEuclideanMotion :=
  ⟨EuclideanMotion.translationMotion t, by simp [EuclideanMotion.translationMotion]⟩

def ofProperRotation (A : ProperRotation) : OrientationPreservingEuclideanMotion :=
  ⟨⟨ProperRotation.toOrthogonalMatrix A, 0⟩, ProperRotation.det_eq_one A⟩

instance : SMul OrientationPreservingEuclideanMotion Realization where
  smul m g := m.1 • g

@[simp] theorem smul_realization_def
    (m : OrientationPreservingEuclideanMotion) (g : Realization) :
    m • g = m.1 • g := rfl

instance : MulAction OrientationPreservingEuclideanMotion Realization where
  smul := (· • ·)
  one_smul g := by
    change ((1 : EuclideanMotion).mapRealization g) = g
    simp
  mul_smul m n g := by
    exact EuclideanMotion.mul_mapRealization m.1 n.1 g

theorem handedness_map_eq (m : OrientationPreservingEuclideanMotion)
    (g : TetrahedralGeometry) :
    handedness (m.1 • g) = handedness g := by
  exact handedness_mapAffine_of_orientationPreserving g m.1.linear m.1.translation (by
    simp [OrientationPreserving, m.2])

theorem handedness_mapRealization_eq (m : OrientationPreservingEuclideanMotion)
    (g : Realization) :
    handedness (m.1.mapRealization g).1 = handedness g.1 := by
  simpa [EuclideanMotion.mapRealization, EuclideanMotion.smul_def] using handedness_map_eq m g.1

theorem affineChiralityClass_mapRealization_eq (m : OrientationPreservingEuclideanMotion)
    (g : Realization) :
    (Quotient.mk Realization.realizationSetoid (m.1.mapRealization g) :
      Realization.AffineChiralityClass) =
      Quotient.mk Realization.realizationSetoid g := by
  apply Quotient.sound
  exact (Realization.orientationPreservingAffineEquivalent_iff _ _).2
    (handedness_mapRealization_eq m g)

@[simp] theorem classifyRealization_mapRealization_eq (m : OrientationPreservingEuclideanMotion)
    (g : Realization) :
    Realization.classifyRealization (m.1.mapRealization g) =
      Realization.classifyRealization g := by
  unfold Realization.classifyRealization
  rw [handedness_mapRealization_eq m g]

end OrientationPreservingEuclideanMotion

namespace OrientationReversingEuclideanMotion

def ofImproperRotation (A : ImproperRotation) : OrientationReversingEuclideanMotion :=
  ⟨⟨A.1, 0⟩, A.2⟩

instance : SMul OrientationReversingEuclideanMotion Realization where
  smul m g := m.1 • g

@[simp] theorem smul_realization_def
    (m : OrientationReversingEuclideanMotion) (g : Realization) :
    m • g = m.1 • g := rfl

theorem handedness_map_eq_neg (m : OrientationReversingEuclideanMotion)
    (g : TetrahedralGeometry) :
    handedness (m.1 • g) = -handedness g := by
  exact handedness_mapAffine_of_orientationReversing g m.1.linear m.1.translation (by
    simp [OrientationReversing, m.2])

theorem handedness_mapRealization_eq_neg (m : OrientationReversingEuclideanMotion)
    (g : Realization) :
    handedness (m.1.mapRealization g).1 = -handedness g.1 := by
  simpa [EuclideanMotion.mapRealization, EuclideanMotion.smul_def] using handedness_map_eq_neg m g.1

end OrientationReversingEuclideanMotion

/-- A reflection across an affine plane, modeled as a translation of a rotated `yz`-plane
reflection. -/
structure PlaneReflection where
  rotation : ProperRotation
  point : EuclideanSpace ℝ (Fin 3)

namespace PlaneReflection

/-- The proper rotation placing the reflecting plane into the `yz`-plane frame. -/
abbrev frameRotation (ρ : PlaneReflection) : OrthogonalMatrix :=
  ProperRotation.toOrthogonalMatrix ρ.rotation

/-- The linear part of a plane reflection. -/
def linearImproperRotation (ρ : PlaneReflection) : ImproperRotation :=
  ImproperRotation.rotateBy ρ.rotation yzPlaneReflection

/-- Coordinates of a point in the reflection-adapted frame, centered at the reflecting plane. -/
def frameCoordinates (ρ : PlaneReflection) (x : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  applyMatrix ρ.frameRotation⁻¹ (x - ρ.point)

/-- First reflection-frame coordinate as a linear functional on displacement vectors. -/
def frameFirstCoordinateLinearMap (ρ : PlaneReflection) :
    EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ where
  toFun v := applyMatrix ρ.frameRotation⁻¹ v 0
  map_add' v w := by simp [applyMatrix_add]
  map_smul' c v := by simp [applyMatrix_smul]

/-- Direction subspace of the affine plane fixed by the reflection. -/
def fixedPlaneDirection (ρ : PlaneReflection) : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) :=
  LinearMap.ker (ρ.frameFirstCoordinateLinearMap)

/-- The affine plane fixed pointwise by the reflection. -/
def fixedPlane (ρ : PlaneReflection) : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' ρ.point ρ.fixedPlaneDirection

/-- The `x`-axis of the reflection-adapted coordinate frame. -/
def frameXAxis : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single 0 1

/-- The `y`-axis of the reflection-adapted coordinate frame. -/
def frameYAxis : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single 1 1

/-- The `z`-axis of the reflection-adapted coordinate frame. -/
def frameZAxis : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single 2 1

/-- The rotated `y`-axis direction spanning the fixed plane. -/
def fixedPlaneBasisY (ρ : PlaneReflection) : EuclideanSpace ℝ (Fin 3) :=
  applyMatrix ρ.frameRotation PlaneReflection.frameYAxis

/-- The rotated `z`-axis direction spanning the fixed plane. -/
def fixedPlaneBasisZ (ρ : PlaneReflection) : EuclideanSpace ℝ (Fin 3) :=
  applyMatrix ρ.frameRotation PlaneReflection.frameZAxis

/-- The affine translation part needed to reflect through the plane passing through `ρ.point`. -/
def translation (ρ : PlaneReflection) : EuclideanSpace ℝ (Fin 3) :=
  ρ.point - applyMatrix ρ.linearImproperRotation.1 ρ.point

/-- The Euclidean motion realizing the plane reflection. -/
def toEuclideanMotion (ρ : PlaneReflection) : OrientationReversingEuclideanMotion :=
  ⟨⟨ρ.linearImproperRotation.1, ρ.translation⟩, ρ.linearImproperRotation.2⟩

@[simp] theorem toEuclideanMotion_linear (ρ : PlaneReflection) :
    ρ.toEuclideanMotion.1.linear = ρ.linearImproperRotation.1 :=
  rfl

@[simp] theorem toEuclideanMotion_translation (ρ : PlaneReflection) :
    ρ.toEuclideanMotion.1.translation = ρ.translation :=
  rfl

theorem frameRotation_det_ne_zero (ρ : PlaneReflection) :
    Matrix.det (ρ.frameRotation : Matrix (Fin 3) (Fin 3) ℝ) ≠ 0 := by
  have horth :
      (ρ.frameRotation : Matrix (Fin 3) (Fin 3) ℝ) *
        (ρ.frameRotation : Matrix (Fin 3) (Fin 3) ℝ).transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff
      (A := (ρ.frameRotation : Matrix (Fin 3) (Fin 3) ℝ))).1 ρ.frameRotation.2
  exact Matrix.det_ne_zero_of_right_inverse horth

theorem frameRotation_inv_mul (ρ : PlaneReflection) :
    ((ρ.frameRotation : Matrix (Fin 3) (Fin 3) ℝ)⁻¹) *
      (ρ.frameRotation : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ρ.frameRotation_det_ne_zero)

theorem frameRotation_mul_inv (ρ : PlaneReflection) :
    (ρ.frameRotation : Matrix (Fin 3) (Fin 3) ℝ) *
      ((ρ.frameRotation : Matrix (Fin 3) (Fin 3) ℝ)⁻¹) = 1 := by
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr ρ.frameRotation_det_ne_zero)

@[simp] theorem apply_frameRotation_frameCoordinates (ρ : PlaneReflection)
    (x : EuclideanSpace ℝ (Fin 3)) :
    applyMatrix ρ.frameRotation (ρ.frameCoordinates x) = x - ρ.point := by
  simp [PlaneReflection.frameCoordinates, applyMatrix_mul]

@[simp] theorem point_add_apply_frameRotation_frameCoordinates (ρ : PlaneReflection)
    (x : EuclideanSpace ℝ (Fin 3)) :
    ρ.point + applyMatrix ρ.frameRotation (ρ.frameCoordinates x) = x := by
  calc
    ρ.point + applyMatrix ρ.frameRotation (ρ.frameCoordinates x)
        = ρ.point + (x - ρ.point) := by rw [ρ.apply_frameRotation_frameCoordinates]
    _ = x := by
          simp [sub_eq_add_neg, add_left_comm]

@[simp] theorem frameCoordinates_point_add_apply_frameRotation (ρ : PlaneReflection)
    (y : EuclideanSpace ℝ (Fin 3)) :
    ρ.frameCoordinates (ρ.point + applyMatrix ρ.frameRotation y) = y := by
  rw [PlaneReflection.frameCoordinates]
  simp [sub_eq_add_neg, add_assoc, applyMatrix_mul]

/-- A vector lies in the fixed-plane direction exactly when it is a linear combination of the
rotated `y`- and `z`-axes. -/
theorem mem_fixedPlaneDirection_iff_exists_basisCoordinates (ρ : PlaneReflection)
    (v : EuclideanSpace ℝ (Fin 3)) :
    v ∈ ρ.fixedPlaneDirection ↔
      ∃ a b : ℝ, v = a • ρ.fixedPlaneBasisY + b • ρ.fixedPlaneBasisZ := by
  constructor
  · intro hv
    rw [PlaneReflection.fixedPlaneDirection, LinearMap.mem_ker] at hv
    let y : EuclideanSpace ℝ (Fin 3) := applyMatrix ρ.frameRotation⁻¹ v
    refine ⟨y 1, y 2, ?_⟩
    have hy0 : y 0 = 0 := by
      simpa [PlaneReflection.frameFirstCoordinateLinearMap, y] using hv
    have hy :
        y = (y 1) • PlaneReflection.frameYAxis + (y 2) • PlaneReflection.frameZAxis := by
      ext i
      fin_cases i <;> simp [PlaneReflection.frameYAxis, PlaneReflection.frameZAxis, hy0]
    calc
      v = applyMatrix ρ.frameRotation y := by
        dsimp [y]
        simp [applyMatrix_mul]
      _ = applyMatrix ρ.frameRotation
            ((y 1) • PlaneReflection.frameYAxis + (y 2) • PlaneReflection.frameZAxis) := by
        conv_lhs => rw [hy]
      _ = (y 1) • ρ.fixedPlaneBasisY + (y 2) • ρ.fixedPlaneBasisZ := by
        simp [PlaneReflection.fixedPlaneBasisY, PlaneReflection.fixedPlaneBasisZ, applyMatrix_add]
  · rintro ⟨a, b, rfl⟩
    have hY : ρ.frameFirstCoordinateLinearMap ρ.fixedPlaneBasisY = 0 := by
      change (applyMatrix ρ.frameRotation⁻¹
        (applyMatrix ρ.frameRotation PlaneReflection.frameYAxis)) 0 = 0
      simp [PlaneReflection.frameYAxis, applyMatrix_mul]
    have hZ : ρ.frameFirstCoordinateLinearMap ρ.fixedPlaneBasisZ = 0 := by
      change (applyMatrix ρ.frameRotation⁻¹
        (applyMatrix ρ.frameRotation PlaneReflection.frameZAxis)) 0 = 0
      simp [PlaneReflection.frameZAxis, applyMatrix_mul]
    rw [PlaneReflection.fixedPlaneDirection, LinearMap.mem_ker]
    simp [hY, hZ]

/-- The fixed-plane direction is exactly the span of the rotated `y`- and `z`-axes. -/
theorem fixedPlaneDirection_eq_span (ρ : PlaneReflection) :
    ρ.fixedPlaneDirection = Submodule.span ℝ {ρ.fixedPlaneBasisY, ρ.fixedPlaneBasisZ} := by
  ext v
  constructor
  · intro hv
    rcases (ρ.mem_fixedPlaneDirection_iff_exists_basisCoordinates v).1 hv with ⟨a, b, hv⟩
    exact (Submodule.mem_span_pair).2 ⟨a, b, hv.symm⟩
  · intro hv
    rcases (Submodule.mem_span_pair).1 hv with ⟨a, b, hv⟩
    exact (ρ.mem_fixedPlaneDirection_iff_exists_basisCoordinates v).2 ⟨a, b, hv.symm⟩

/-- The (unit) normal direction to the fixed plane, obtained by rotating the adapted `x`-axis. -/
def fixedPlaneNormal (ρ : PlaneReflection) : EuclideanSpace ℝ (Fin 3) :=
  applyMatrix ρ.frameRotation PlaneReflection.frameXAxis

@[simp] theorem frameFirstCoordinateLinearMap_fixedPlaneNormal (ρ : PlaneReflection) :
    ρ.frameFirstCoordinateLinearMap (ρ.fixedPlaneNormal) = 1 := by
  -- Use the existing frame-coordinate cancellation lemma to avoid expanding `applyMatrix`.
  have hvec :
      applyMatrix ρ.frameRotation⁻¹ (applyMatrix ρ.frameRotation PlaneReflection.frameXAxis) =
        PlaneReflection.frameXAxis := by
    have hcomp :
        applyMatrix ρ.frameRotation⁻¹ (applyMatrix ρ.frameRotation PlaneReflection.frameXAxis) =
          applyMatrix
              ((ρ.frameRotation : Matrix (Fin 3) (Fin 3) ℝ) *
                ((ρ.frameRotation : Matrix (Fin 3) (Fin 3) ℝ)⁻¹))
              PlaneReflection.frameXAxis := by
      exact
        (applyMatrix_mul (ρ.frameRotation : Matrix (Fin 3) (Fin 3) ℝ)
          ((ρ.frameRotation : Matrix (Fin 3) (Fin 3) ℝ)⁻¹) PlaneReflection.frameXAxis)
    calc
      applyMatrix ρ.frameRotation⁻¹ (applyMatrix ρ.frameRotation PlaneReflection.frameXAxis)
          = applyMatrix
              ((ρ.frameRotation : Matrix (Fin 3) (Fin 3) ℝ) *
                ((ρ.frameRotation : Matrix (Fin 3) (Fin 3) ℝ)⁻¹))
              PlaneReflection.frameXAxis := hcomp
      _ = applyMatrix (1 : Matrix (Fin 3) (Fin 3) ℝ) PlaneReflection.frameXAxis := by
            simp
      _ = PlaneReflection.frameXAxis := by simp
  -- Unfold only the linear functional and the normal, then evaluate at coordinate `0`.
  change applyMatrix ρ.frameRotation⁻¹ (ρ.fixedPlaneNormal) 0 = 1
  dsimp [PlaneReflection.fixedPlaneNormal]
  have h0 := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 0) hvec
  -- Conclude by evaluating the RHS explicitly.
  calc
    applyMatrix ρ.frameRotation⁻¹ (applyMatrix ρ.frameRotation PlaneReflection.frameXAxis) 0
        = PlaneReflection.frameXAxis 0 := h0
    _ = 1 := by simp [PlaneReflection.frameXAxis]

theorem fixedPlaneNormal_ne_zero (ρ : PlaneReflection) : ρ.fixedPlaneNormal ≠ 0 := by
  intro h
  have : (1 : ℝ) = 0 := by
    simpa [h] using (ρ.frameFirstCoordinateLinearMap_fixedPlaneNormal)
  exact one_ne_zero this

theorem frameFirstCoordinateLinearMap_surjective (ρ : PlaneReflection) :
    Function.Surjective ρ.frameFirstCoordinateLinearMap := by
  intro t
  refine ⟨t • ρ.fixedPlaneNormal, ?_⟩
  simp [ρ.frameFirstCoordinateLinearMap_fixedPlaneNormal]

theorem frameRotation_inv_eq_transpose (ρ : PlaneReflection) :
    ((ρ.frameRotation : Matrix (Fin 3) (Fin 3) ℝ)⁻¹) =
      (ρ.frameRotation : Matrix (Fin 3) (Fin 3) ℝ)ᵀ := by
  apply Matrix.inv_eq_right_inv
  exact (Matrix.mem_orthogonalGroup_iff
    (A := (ρ.frameRotation : Matrix (Fin 3) (Fin 3) ℝ))).1 ρ.frameRotation.2

theorem frameFirstCoordinateLinearMap_eq_inner_fixedPlaneNormal (ρ : PlaneReflection)
    (v : EuclideanSpace ℝ (Fin 3)) :
    ρ.frameFirstCoordinateLinearMap v = ⟪v, ρ.fixedPlaneNormal⟫ := by
  have hinv :
      (ρ.frameRotation⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) =
        (ρ.frameRotation : Matrix (Fin 3) (Fin 3) ℝ)ᵀ := by
    calc
      (ρ.frameRotation⁻¹ : Matrix (Fin 3) (Fin 3) ℝ)
          = ((ρ.frameRotation : Matrix (Fin 3) (Fin 3) ℝ)⁻¹) := by
              simp
      _ = (ρ.frameRotation : Matrix (Fin 3) (Fin 3) ℝ)ᵀ :=
            ρ.frameRotation_inv_eq_transpose
  -- Expand both sides to the same coordinate sum `∑ k, v k * (ρ.frameRotation 0 k)`.
  simp [PlaneReflection.frameFirstCoordinateLinearMap, PlaneReflection.fixedPlaneNormal,
    PlaneReflection.frameXAxis, PiLp.inner_apply, applyMatrix_apply, Matrix.transpose_apply,
    Fin.sum_univ_three, hinv]
  ring

theorem mem_fixedPlaneDirection_iff_inner_fixedPlaneNormal_eq_zero (ρ : PlaneReflection)
    (v : EuclideanSpace ℝ (Fin 3)) :
    v ∈ ρ.fixedPlaneDirection ↔ ⟪v, ρ.fixedPlaneNormal⟫ = 0 := by
  rw [PlaneReflection.fixedPlaneDirection, LinearMap.mem_ker]
  simp [ρ.frameFirstCoordinateLinearMap_eq_inner_fixedPlaneNormal]

theorem mem_fixedPlane_iff_inner_sub_point_fixedPlaneNormal_eq_zero (ρ : PlaneReflection)
    (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ ρ.fixedPlane ↔ ⟪x - ρ.point, ρ.fixedPlaneNormal⟫ = 0 := by
  -- Membership in the affine plane is membership in its direction after subtracting `ρ.point`.
  rw [PlaneReflection.fixedPlane, AffineSubspace.mem_mk', vsub_eq_sub]
  simpa using
    (ρ.mem_fixedPlaneDirection_iff_inner_fixedPlaneNormal_eq_zero (v := x - ρ.point))

theorem fixedPlaneDirection_eq_orthogonal_span_fixedPlaneNormal (ρ : PlaneReflection) :
    ρ.fixedPlaneDirection = (ℝ ∙ ρ.fixedPlaneNormal)ᗮ := by
  ext v
  simp [ρ.mem_fixedPlaneDirection_iff_inner_fixedPlaneNormal_eq_zero,
    Submodule.mem_orthogonal_singleton_iff_inner_left]

theorem fixedPlane_eq_mk'_orthogonal_span_fixedPlaneNormal (ρ : PlaneReflection) :
    ρ.fixedPlane = AffineSubspace.mk' ρ.point ((ℝ ∙ ρ.fixedPlaneNormal)ᗮ) := by
  simp [PlaneReflection.fixedPlane, ρ.fixedPlaneDirection_eq_orthogonal_span_fixedPlaneNormal]

theorem fixedPlane_eq_setOf_inner_sub_point_fixedPlaneNormal_eq_zero (ρ : PlaneReflection) :
    (ρ.fixedPlane : Set (EuclideanSpace ℝ (Fin 3))) =
      { x | ⟪x - ρ.point, ρ.fixedPlaneNormal⟫ = 0 } := by
  ext x
  exact ρ.mem_fixedPlane_iff_inner_sub_point_fixedPlaneNormal_eq_zero x

theorem fixedPlane_eq_setOf_inner_eq_inner_point_fixedPlaneNormal (ρ : PlaneReflection) :
    (ρ.fixedPlane : Set (EuclideanSpace ℝ (Fin 3))) =
      { x | ⟪x, ρ.fixedPlaneNormal⟫ = ⟪ρ.point, ρ.fixedPlaneNormal⟫ } := by
  ext x
  constructor
  · intro hx
    have h0 : ⟪x - ρ.point, ρ.fixedPlaneNormal⟫ = 0 :=
      (ρ.mem_fixedPlane_iff_inner_sub_point_fixedPlaneNormal_eq_zero x).1 hx
    have : ⟪x, ρ.fixedPlaneNormal⟫ - ⟪ρ.point, ρ.fixedPlaneNormal⟫ = 0 := by
      simpa [inner_sub_left] using h0
    exact sub_eq_zero.mp this
  · intro hx
    have : ⟪x, ρ.fixedPlaneNormal⟫ - ⟪ρ.point, ρ.fixedPlaneNormal⟫ = 0 :=
      sub_eq_zero.mpr hx
    have : ⟪x - ρ.point, ρ.fixedPlaneNormal⟫ = 0 := by
      simpa [inner_sub_left] using this
    exact (ρ.mem_fixedPlane_iff_inner_sub_point_fixedPlaneNormal_eq_zero x).2 this

theorem inner_fixedPlaneBasisY_fixedPlaneNormal_eq_zero (ρ : PlaneReflection) :
    ⟪ρ.fixedPlaneBasisY, ρ.fixedPlaneNormal⟫ = 0 := by
  have hmem : ρ.fixedPlaneBasisY ∈ ρ.fixedPlaneDirection :=
    (ρ.mem_fixedPlaneDirection_iff_exists_basisCoordinates (v := ρ.fixedPlaneBasisY)).2
      ⟨1, 0, by simp⟩
  exact (ρ.mem_fixedPlaneDirection_iff_inner_fixedPlaneNormal_eq_zero (v := ρ.fixedPlaneBasisY)).1 hmem

theorem inner_fixedPlaneBasisZ_fixedPlaneNormal_eq_zero (ρ : PlaneReflection) :
    ⟪ρ.fixedPlaneBasisZ, ρ.fixedPlaneNormal⟫ = 0 := by
  have hmem : ρ.fixedPlaneBasisZ ∈ ρ.fixedPlaneDirection :=
    (ρ.mem_fixedPlaneDirection_iff_exists_basisCoordinates (v := ρ.fixedPlaneBasisZ)).2
      ⟨0, 1, by simp⟩
  exact (ρ.mem_fixedPlaneDirection_iff_inner_fixedPlaneNormal_eq_zero (v := ρ.fixedPlaneBasisZ)).1 hmem

/-- The fixed-plane direction is 2-dimensional inside ambient 3-space. -/
theorem fixedPlaneDirection_finrank (ρ : PlaneReflection) :
    Module.finrank ℝ ρ.fixedPlaneDirection = 2 := by
  have hrange : LinearMap.range ρ.frameFirstCoordinateLinearMap = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact ρ.frameFirstCoordinateLinearMap_surjective
  have hdim :
      Module.finrank ℝ (LinearMap.range ρ.frameFirstCoordinateLinearMap) +
        Module.finrank ℝ (LinearMap.ker ρ.frameFirstCoordinateLinearMap) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) :=
    LinearMap.finrank_range_add_finrank_ker ρ.frameFirstCoordinateLinearMap
  rw [hrange] at hdim
  have hdim' : 1 + Module.finrank ℝ ρ.fixedPlaneDirection = 3 := by
    simpa [PlaneReflection.fixedPlaneDirection] using hdim
  omega

/-- The fixed-plane direction has codimension `1` in ambient 3-space. -/
theorem fixedPlaneDirection_quotient_finrank (ρ : PlaneReflection) :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 3) ⧸ ρ.fixedPlaneDirection) = 1 := by
  have hdim :
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3) ⧸ ρ.fixedPlaneDirection) +
        Module.finrank ℝ ρ.fixedPlaneDirection =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) :=
    Submodule.finrank_quotient_add_finrank ρ.fixedPlaneDirection
  have hdim' :
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3) ⧸ ρ.fixedPlaneDirection) + 2 = 3 := by
    simpa [ρ.fixedPlaneDirection_finrank] using hdim
  omega

theorem fixedPlaneDirection_inf_span_fixedPlaneNormal_eq_bot (ρ : PlaneReflection) :
    ρ.fixedPlaneDirection ⊓ (ℝ ∙ ρ.fixedPlaneNormal) = ⊥ := by
  ext w
  constructor
  · intro hw
    rcases (Submodule.mem_inf).1 hw with ⟨hker, hspan⟩
    rcases (Submodule.mem_span_singleton).1 hspan with ⟨c, rfl⟩
    have hc : c = 0 := by
      have : ρ.frameFirstCoordinateLinearMap (c • ρ.fixedPlaneNormal) = 0 :=
        (LinearMap.mem_ker).1 (by simpa [PlaneReflection.fixedPlaneDirection] using hker)
      simpa [ρ.frameFirstCoordinateLinearMap_fixedPlaneNormal] using this
    simp [hc]
  · intro hw
    have : w = 0 := by simpa using hw
    subst this
    simp

theorem fixedPlaneDirection_sup_span_fixedPlaneNormal_eq_top (ρ : PlaneReflection) :
    ρ.fixedPlaneDirection ⊔ (ℝ ∙ ρ.fixedPlaneNormal) = ⊤ := by
  have hinf : ρ.fixedPlaneDirection ⊓ (ℝ ∙ ρ.fixedPlaneNormal) = ⊥ :=
    ρ.fixedPlaneDirection_inf_span_fixedPlaneNormal_eq_bot
  have hB : Module.finrank ℝ (ℝ ∙ ρ.fixedPlaneNormal) = 1 := by
    simpa using (finrank_span_singleton (K := ℝ) (hv := ρ.fixedPlaneNormal_ne_zero))
  have hsup :
      Module.finrank ℝ (↥(ρ.fixedPlaneDirection ⊔ (ℝ ∙ ρ.fixedPlaneNormal))) = 3 := by
    have hdim :=
      Submodule.finrank_sup_add_finrank_inf_eq (ρ.fixedPlaneDirection) (ℝ ∙ ρ.fixedPlaneNormal)
    -- First simplify the RHS to `3`, then use `inf = ⊥` to drop the inf term.
    have hdim' :
        Module.finrank ℝ (↥(ρ.fixedPlaneDirection ⊔ (ℝ ∙ ρ.fixedPlaneNormal))) +
          Module.finrank ℝ (↥(ρ.fixedPlaneDirection ⊓ (ℝ ∙ ρ.fixedPlaneNormal))) = 3 := by
      simpa [ρ.fixedPlaneDirection_finrank, hB] using hdim
    have hdim'' := hdim'
    rw [hinf] at hdim''
    have hdim''' :
        Module.finrank ℝ (↥(ρ.fixedPlaneDirection ⊔ (ℝ ∙ ρ.fixedPlaneNormal))) + 0 = 3 := by
      simpa using hdim''
    simpa using hdim'''
  apply Submodule.eq_top_of_finrank_eq
  simp [hsup]

theorem fixedPlaneDirection_isCompl_span_fixedPlaneNormal (ρ : PlaneReflection) :
    IsCompl ρ.fixedPlaneDirection (ℝ ∙ ρ.fixedPlaneNormal) := by
  refine ⟨?_, ?_⟩
  · -- `Disjoint`
    rw [disjoint_iff]
    exact ρ.fixedPlaneDirection_inf_span_fixedPlaneNormal_eq_bot
  · -- `sup = ⊤`
    rw [codisjoint_iff]
    exact ρ.fixedPlaneDirection_sup_span_fixedPlaneNormal_eq_top

@[simp] theorem fixedPlane_direction (ρ : PlaneReflection) :
    ρ.fixedPlane.direction = ρ.fixedPlaneDirection := by
  simp [PlaneReflection.fixedPlane, AffineSubspace.direction_mk']

theorem fixedPlane_direction_finrank (ρ : PlaneReflection) :
    Module.finrank ℝ ρ.fixedPlane.direction = 2 := by
  simpa using (ρ.fixedPlane_direction ▸ ρ.fixedPlaneDirection_finrank)

theorem fixedPlane_direction_quotient_finrank (ρ : PlaneReflection) :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 3) ⧸ ρ.fixedPlane.direction) = 1 := by
  simpa using (ρ.fixedPlane_direction ▸ ρ.fixedPlaneDirection_quotient_finrank)

/-- **Geometric package lemma.**

The fixed plane of a plane reflection is the affine hyperplane through `ρ.point` orthogonal to
`ρ.fixedPlaneNormal`. Concretely it is cut out by the single affine equation
`⟪x, ρ.fixedPlaneNormal⟫ = ⟪ρ.point, ρ.fixedPlaneNormal⟫`, and its direction has codimension `1`.
-/
theorem fixedPlane_geometric (ρ : PlaneReflection) :
    (ρ.fixedPlane : Set (EuclideanSpace ℝ (Fin 3))) =
        { x | ⟪x, ρ.fixedPlaneNormal⟫ = ⟪ρ.point, ρ.fixedPlaneNormal⟫ } ∧
      ρ.fixedPlane.direction = (ℝ ∙ ρ.fixedPlaneNormal)ᗮ ∧
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3) ⧸ ρ.fixedPlane.direction) = 1 := by
  refine ⟨ρ.fixedPlane_eq_setOf_inner_eq_inner_point_fixedPlaneNormal, ?_, ?_⟩
  · simp [ρ.fixedPlaneDirection_eq_orthogonal_span_fixedPlaneNormal]
  · exact ρ.fixedPlane_direction_quotient_finrank

theorem applyPoint_sub_point (ρ : PlaneReflection) (x : EuclideanSpace ℝ (Fin 3)) :
    ρ.toEuclideanMotion.1.applyPoint x - ρ.point =
      applyMatrix ρ.linearImproperRotation.1 (x - ρ.point) := by
  ext j
  simp [EuclideanMotion.applyPoint, PlaneReflection.translation, sub_eq_add_neg]
  ring

theorem linearImproperRotation_apply_apply_frameRotation (ρ : PlaneReflection)
    (y : EuclideanSpace ℝ (Fin 3)) :
    applyMatrix ρ.linearImproperRotation.1 (applyMatrix ρ.frameRotation y) =
      applyMatrix ρ.frameRotation (applyMatrix reflectYZMatrix y) := by
  let Q : OrthogonalMatrix := ρ.frameRotation
  have hmul : Q * ρ.linearImproperRotation.1 = yzPlaneReflection.1 * Q := by
    simp [PlaneReflection.linearImproperRotation, ImproperRotation.rotateBy, Q, mul_assoc]
  calc
    applyMatrix ρ.linearImproperRotation.1 (applyMatrix Q y)
        = applyMatrix ((Q : Matrix (Fin 3) (Fin 3) ℝ) *
            (ρ.linearImproperRotation.1 : Matrix (Fin 3) (Fin 3) ℝ)) y := by
            exact applyMatrix_mul (Q : Matrix (Fin 3) (Fin 3) ℝ)
              (ρ.linearImproperRotation.1 : Matrix (Fin 3) (Fin 3) ℝ) y
    _ = applyMatrix (((yzPlaneReflection.1 * Q : OrthogonalMatrix) :
          Matrix (Fin 3) (Fin 3) ℝ)) y := by
          change applyMatrix (((Q * ρ.linearImproperRotation.1 : OrthogonalMatrix) :
            Matrix (Fin 3) (Fin 3) ℝ)) y =
            applyMatrix (((yzPlaneReflection.1 * Q : OrthogonalMatrix) :
              Matrix (Fin 3) (Fin 3) ℝ)) y
          rw [hmul]
    _ = applyMatrix Q (applyMatrix reflectYZMatrix y) := by
          change applyMatrix ((yzPlaneReflection.1 : Matrix (Fin 3) (Fin 3) ℝ) *
            (Q : Matrix (Fin 3) (Fin 3) ℝ)) y =
            applyMatrix (Q : Matrix (Fin 3) (Fin 3) ℝ) (applyMatrix reflectYZMatrix y)
          exact (applyMatrix_mul reflectYZMatrix (Q : Matrix (Fin 3) (Fin 3) ℝ) y).symm

theorem frameCoordinates_applyPoint (ρ : PlaneReflection) (x : EuclideanSpace ℝ (Fin 3)) :
    ρ.frameCoordinates (ρ.toEuclideanMotion.1.applyPoint x) =
      applyMatrix reflectYZMatrix (ρ.frameCoordinates x) := by
  have hsub :
      ρ.toEuclideanMotion.1.applyPoint x - ρ.point =
        applyMatrix ρ.frameRotation (applyMatrix reflectYZMatrix (ρ.frameCoordinates x)) := by
    calc
      ρ.toEuclideanMotion.1.applyPoint x - ρ.point
          = applyMatrix ρ.linearImproperRotation.1 (x - ρ.point) := by
              simpa using (ρ.applyPoint_sub_point x)
      _ = applyMatrix ρ.linearImproperRotation.1
            (applyMatrix ρ.frameRotation (ρ.frameCoordinates x)) := by
            rw [← ρ.apply_frameRotation_frameCoordinates x]
      _ = applyMatrix ρ.frameRotation (applyMatrix reflectYZMatrix (ρ.frameCoordinates x)) := by
            simpa using
              (ρ.linearImproperRotation_apply_apply_frameRotation (ρ.frameCoordinates x))
  have happly :
      ρ.toEuclideanMotion.1.applyPoint x =
        ρ.point + applyMatrix ρ.frameRotation (applyMatrix reflectYZMatrix (ρ.frameCoordinates x)) := by
    have := congrArg (fun t : EuclideanSpace ℝ (Fin 3) => t + ρ.point) hsub
    have happly' :
        ρ.toEuclideanMotion.1.applyPoint x =
          applyMatrix ρ.frameRotation (applyMatrix reflectYZMatrix (ρ.frameCoordinates x)) +
            ρ.point := by
          simpa [sub_add_cancel, add_assoc] using this
    simpa [add_comm, add_left_comm, add_assoc] using happly'
  simpa [happly] using
    (ρ.frameCoordinates_point_add_apply_frameRotation
      (applyMatrix reflectYZMatrix (ρ.frameCoordinates x)))

theorem linearImproperRotation_apply_eq_self_iff (ρ : PlaneReflection)
    (x : EuclideanSpace ℝ (Fin 3)) :
    applyMatrix ρ.linearImproperRotation.1 x = x ↔
      applyMatrix ρ.frameRotation⁻¹ x 0 = 0 := by
  let Q : OrthogonalMatrix := ρ.frameRotation
  let z : EuclideanSpace ℝ (Fin 3) := applyMatrix Q⁻¹ x
  have hcancel_left (w : EuclideanSpace ℝ (Fin 3)) :
      applyMatrix Q (applyMatrix Q⁻¹ w) = w := by
    simp [Q, applyMatrix_mul]
  have hcancel_right (w : EuclideanSpace ℝ (Fin 3)) :
      applyMatrix Q⁻¹ (applyMatrix Q w) = w := by
    simp [Q, applyMatrix_mul]
  have hinjQ : Function.Injective (fun y : EuclideanSpace ℝ (Fin 3) => applyMatrix Q y) :=
    (Function.LeftInverse.injective fun w => hcancel_right w)
  have hx : x = applyMatrix Q z := by
    dsimp [z]
    exact (hcancel_left x).symm
  have hmul : Q * ρ.linearImproperRotation.1 = yzPlaneReflection.1 * Q := by
    simp [PlaneReflection.linearImproperRotation, ImproperRotation.rotateBy, Q, mul_assoc]
  have hrotate :
      applyMatrix ρ.linearImproperRotation.1 (applyMatrix Q z) =
        applyMatrix Q (applyMatrix reflectYZMatrix z) := by
    calc
      applyMatrix ρ.linearImproperRotation.1 (applyMatrix Q z)
          = applyMatrix ((Q : Matrix (Fin 3) (Fin 3) ℝ) *
              (ρ.linearImproperRotation.1 : Matrix (Fin 3) (Fin 3) ℝ)) z := by
              exact applyMatrix_mul (Q : Matrix (Fin 3) (Fin 3) ℝ)
                (ρ.linearImproperRotation.1 : Matrix (Fin 3) (Fin 3) ℝ) z
      _ = applyMatrix (((yzPlaneReflection.1 * Q : OrthogonalMatrix) :
            Matrix (Fin 3) (Fin 3) ℝ)) z := by
            change applyMatrix (((Q * ρ.linearImproperRotation.1 : OrthogonalMatrix) :
              Matrix (Fin 3) (Fin 3) ℝ)) z =
              applyMatrix (((yzPlaneReflection.1 * Q : OrthogonalMatrix) :
                Matrix (Fin 3) (Fin 3) ℝ)) z
            rw [hmul]
      _ = applyMatrix Q (applyMatrix reflectYZMatrix z) := by
            change applyMatrix ((yzPlaneReflection.1 : Matrix (Fin 3) (Fin 3) ℝ) *
              (Q : Matrix (Fin 3) (Fin 3) ℝ)) z =
              applyMatrix (Q : Matrix (Fin 3) (Fin 3) ℝ) (applyMatrix reflectYZMatrix z)
            exact (applyMatrix_mul reflectYZMatrix (Q : Matrix (Fin 3) (Fin 3) ℝ) z).symm
  constructor
  · intro hfix
    have hzfixQ : applyMatrix Q (applyMatrix reflectYZMatrix z) = applyMatrix Q z := by
      calc
        applyMatrix Q (applyMatrix reflectYZMatrix z)
            = applyMatrix ρ.linearImproperRotation.1 (applyMatrix Q z) := by
                rw [hrotate.symm]
        _ = applyMatrix ρ.linearImproperRotation.1 x := by rw [← hx]
        _ = x := hfix
        _ = applyMatrix Q z := hx
    have hzfix : applyMatrix reflectYZMatrix z = z := by
      exact hinjQ hzfixQ
    exact (apply_reflectYZMatrix_eq_self_iff z).1 hzfix
  · intro hz0
    have hzfix : applyMatrix reflectYZMatrix z = z :=
      (apply_reflectYZMatrix_eq_self_iff z).2 hz0
    calc
      applyMatrix ρ.linearImproperRotation.1 x
          = applyMatrix ρ.linearImproperRotation.1 (applyMatrix Q z) := by rw [hx]
      _ = applyMatrix Q (applyMatrix reflectYZMatrix z) := hrotate
      _ = applyMatrix Q z := by rw [hzfix]
      _ = x := hx.symm

theorem applyPoint_eq_self_iff (ρ : PlaneReflection) (x : EuclideanSpace ℝ (Fin 3)) :
    ρ.toEuclideanMotion.1.applyPoint x = x ↔ (ρ.frameCoordinates x) 0 = 0 := by
  constructor
  · intro hfix
    have hsub : ρ.toEuclideanMotion.1.applyPoint x - ρ.point = x - ρ.point := by
      simp [hfix]
    have hlin : applyMatrix ρ.linearImproperRotation.1 (x - ρ.point) = x - ρ.point := by
      rw [PlaneReflection.applyPoint_sub_point] at hsub
      exact hsub
    show applyMatrix ρ.frameRotation⁻¹ (x - ρ.point) 0 = 0
    exact (ρ.linearImproperRotation_apply_eq_self_iff (x - ρ.point)).1 hlin
  · intro hframe
    have hlin : applyMatrix ρ.linearImproperRotation.1 (x - ρ.point) = x - ρ.point := by
      have : applyMatrix ρ.frameRotation⁻¹ (x - ρ.point) 0 = 0 := by
        exact hframe
      exact (ρ.linearImproperRotation_apply_eq_self_iff (x - ρ.point)).2 this
    have hsub : ρ.toEuclideanMotion.1.applyPoint x - ρ.point = x - ρ.point := by
      rw [PlaneReflection.applyPoint_sub_point]
      exact hlin
    exact sub_left_injective hsub

theorem applyPoint_eq_self_iff_exists_frameVector (ρ : PlaneReflection)
    (x : EuclideanSpace ℝ (Fin 3)) :
    ρ.toEuclideanMotion.1.applyPoint x = x ↔
      ∃ y : EuclideanSpace ℝ (Fin 3),
        y 0 = 0 ∧ x = ρ.point + applyMatrix ρ.frameRotation y := by
  constructor
  · intro hfix
    refine ⟨ρ.frameCoordinates x, (ρ.applyPoint_eq_self_iff x).1 hfix, ?_⟩
    exact (ρ.point_add_apply_frameRotation_frameCoordinates x).symm
  · rintro ⟨y, hy0, rfl⟩
    have hframe :
        (ρ.frameCoordinates (ρ.point + applyMatrix ρ.frameRotation y)) 0 = 0 := by
      rw [ρ.frameCoordinates_point_add_apply_frameRotation]
      exact hy0
    exact (ρ.applyPoint_eq_self_iff (ρ.point + applyMatrix ρ.frameRotation y)).2 hframe

@[simp] theorem point_mem_fixedPlane (ρ : PlaneReflection) :
    ρ.point ∈ ρ.fixedPlane := by
  simp [PlaneReflection.fixedPlane]

instance (ρ : PlaneReflection) : Nonempty ρ.fixedPlane :=
  ⟨⟨ρ.point, ρ.point_mem_fixedPlane⟩⟩

@[simp] theorem mem_fixedPlane_iff (ρ : PlaneReflection) (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ ρ.fixedPlane ↔ (ρ.frameCoordinates x) 0 = 0 := by
  rw [PlaneReflection.fixedPlane, AffineSubspace.mem_mk', PlaneReflection.fixedPlaneDirection,
    LinearMap.mem_ker, vsub_eq_sub]
  change applyMatrix ρ.frameRotation⁻¹ (x - ρ.point) 0 = 0 ↔ (ρ.frameCoordinates x) 0 = 0
  rw [PlaneReflection.frameCoordinates]

theorem mem_fixedPlane_iff_applyPoint_eq_self (ρ : PlaneReflection)
    (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ ρ.fixedPlane ↔ ρ.toEuclideanMotion.1.applyPoint x = x := by
  rw [ρ.mem_fixedPlane_iff, ρ.applyPoint_eq_self_iff]

theorem applyPoint_eq_self_iff_mem_fixedPlane (ρ : PlaneReflection)
    (x : EuclideanSpace ℝ (Fin 3)) :
    ρ.toEuclideanMotion.1.applyPoint x = x ↔ x ∈ ρ.fixedPlane :=
  (ρ.mem_fixedPlane_iff_applyPoint_eq_self x).symm

theorem mem_fixedPlane_iff_exists_frameVector (ρ : PlaneReflection)
    (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ ρ.fixedPlane ↔
      ∃ y : EuclideanSpace ℝ (Fin 3),
        y 0 = 0 ∧ x = ρ.point + applyMatrix ρ.frameRotation y := by
  rw [ρ.mem_fixedPlane_iff_applyPoint_eq_self, ρ.applyPoint_eq_self_iff_exists_frameVector]

theorem sub_applyPoint_mem_span_fixedPlaneNormal (ρ : PlaneReflection)
    (x : EuclideanSpace ℝ (Fin 3)) :
    x - ρ.toEuclideanMotion.1.applyPoint x ∈ (ℝ ∙ ρ.fixedPlaneNormal) := by
  -- Freeze the reflected point so rewriting `x` later does not rewrite the argument of `applyPoint`.
  set x' : EuclideanSpace ℝ (Fin 3) := ρ.toEuclideanMotion.1.applyPoint x
  have hx'_def : x' = ρ.toEuclideanMotion.1.applyPoint x := rfl
  have hmem : x - x' ∈ (ℝ ∙ ρ.fixedPlaneNormal) := by
    let v : EuclideanSpace ℝ (Fin 3) := ρ.frameCoordinates x
    have hx : x = ρ.point + applyMatrix ρ.frameRotation v := by
      simp [v]
    have hfc : ρ.frameCoordinates x' = applyMatrix reflectYZMatrix v := by
      simpa [hx'_def, v] using (ρ.frameCoordinates_applyPoint x)
    have hx' : x' = ρ.point + applyMatrix ρ.frameRotation (applyMatrix reflectYZMatrix v) := by
      have : x' = ρ.point + applyMatrix ρ.frameRotation (ρ.frameCoordinates x') := by
        simp
      simpa [hfc] using this
    refine (Submodule.mem_span_singleton).2 ?_
    refine ⟨2 * (v 0), ?_⟩
    have hsubV :
        v - applyMatrix reflectYZMatrix v = (2 * (v 0)) • PlaneReflection.frameXAxis := by
      ext j
      fin_cases j <;>
        simp [PlaneReflection.frameXAxis, reflectYZMatrix, applyMatrix_apply, Fin.sum_univ_three,
          sub_eq_add_neg, two_mul]
    have hxsub : x - x' = (2 * (v 0)) • ρ.fixedPlaneNormal := by
      calc
        x - x'
            = (ρ.point + applyMatrix ρ.frameRotation v) -
                (ρ.point + applyMatrix ρ.frameRotation (applyMatrix reflectYZMatrix v)) := by
                simp [hx, hx']
        _ = applyMatrix ρ.frameRotation v -
              applyMatrix ρ.frameRotation (applyMatrix reflectYZMatrix v) := by
              simp [add_sub_add_left_eq_sub]
        _ = applyMatrix ρ.frameRotation (v - applyMatrix reflectYZMatrix v) := by
              symm
              simp
        _ = applyMatrix ρ.frameRotation ((2 * (v 0)) • PlaneReflection.frameXAxis) := by
              simp [hsubV]
        _ = (2 * (v 0)) • ρ.fixedPlaneNormal := by
              simp [PlaneReflection.fixedPlaneNormal]
    exact hxsub.symm
  simpa [hx'_def] using hmem

theorem sub_applyPoint_eq_smul_fixedPlaneNormal (ρ : PlaneReflection) (x : EuclideanSpace ℝ (Fin 3)) :
    x - ρ.toEuclideanMotion.1.applyPoint x =
      (2 * (ρ.frameCoordinates x 0)) • ρ.fixedPlaneNormal := by
  -- Freeze the reflected point so rewriting `x` later does not rewrite the argument of `applyPoint`.
  set x' : EuclideanSpace ℝ (Fin 3) := ρ.toEuclideanMotion.1.applyPoint x
  have hx'_def : x' = ρ.toEuclideanMotion.1.applyPoint x := rfl
  have hmem : x - x' ∈ (ℝ ∙ ρ.fixedPlaneNormal) := by
    simpa [hx'_def] using ρ.sub_applyPoint_mem_span_fixedPlaneNormal x
  rcases (Submodule.mem_span_singleton).1 hmem with ⟨c, hc⟩
  have hfc : ρ.frameCoordinates x' = applyMatrix reflectYZMatrix (ρ.frameCoordinates x) := by
    simpa [hx'_def] using (ρ.frameCoordinates_applyPoint x)
  have hc_coord : c = 2 * (ρ.frameCoordinates x 0) := by
    have hmap : c = ρ.frameFirstCoordinateLinearMap (x - x') := by
      have := congrArg ρ.frameFirstCoordinateLinearMap hc
      simpa [ρ.frameFirstCoordinateLinearMap_fixedPlaneNormal] using this
    have hfc0 : (ρ.frameCoordinates x') 0 = -(ρ.frameCoordinates x 0) := by
      have := congrArg (fun w : EuclideanSpace ℝ (Fin 3) => w 0) hfc
      simpa using this.trans (apply_reflectYZMatrix_zero (x := ρ.frameCoordinates x))
    have hmap' : ρ.frameFirstCoordinateLinearMap (x - x') = 2 * (ρ.frameCoordinates x 0) := by
      have hxsub : x - x' = (x - ρ.point) - (x' - ρ.point) := by
        simp [sub_eq_add_neg, add_assoc, add_left_comm]
      calc
        ρ.frameFirstCoordinateLinearMap (x - x')
            = ρ.frameFirstCoordinateLinearMap ((x - ρ.point) - (x' - ρ.point)) := by
                rw [hxsub]
        _ = ρ.frameFirstCoordinateLinearMap (x - ρ.point) -
              ρ.frameFirstCoordinateLinearMap (x' - ρ.point) := by
              simp
        _ = (ρ.frameCoordinates x 0) - (ρ.frameCoordinates x' 0) := by
              rfl
        _ = (ρ.frameCoordinates x 0) - (-(ρ.frameCoordinates x 0)) := by
              simp [hfc0]
        _ = 2 * (ρ.frameCoordinates x 0) := by ring
    exact hmap.trans hmap'
  -- Use the coefficient identity to rewrite the span witness equality.
  calc
    x - ρ.toEuclideanMotion.1.applyPoint x = x - x' := by simp [hx'_def]
    _ = c • ρ.fixedPlaneNormal := by simpa using hc.symm
    _ = (2 * (ρ.frameCoordinates x 0)) • ρ.fixedPlaneNormal := by simp [hc_coord]

theorem sub_applyPoint_eq_two_inner_smul_fixedPlaneNormal (ρ : PlaneReflection)
    (x : EuclideanSpace ℝ (Fin 3)) :
    x - ρ.toEuclideanMotion.1.applyPoint x =
      (2 * ⟪x - ρ.point, ρ.fixedPlaneNormal⟫) • ρ.fixedPlaneNormal := by
  have hcoord : (ρ.frameCoordinates x) 0 = ⟪x - ρ.point, ρ.fixedPlaneNormal⟫ := by
    -- `frameCoordinates x 0` is the first-coordinate functional on the displacement `x - ρ.point`.
    calc
      (ρ.frameCoordinates x) 0 = ρ.frameFirstCoordinateLinearMap (x - ρ.point) := rfl
      _ = ⟪x - ρ.point, ρ.fixedPlaneNormal⟫ :=
            ρ.frameFirstCoordinateLinearMap_eq_inner_fixedPlaneNormal (v := x - ρ.point)
  simpa [hcoord] using ρ.sub_applyPoint_eq_smul_fixedPlaneNormal x

theorem applyPoint_eq_sub_two_inner_smul_fixedPlaneNormal (ρ : PlaneReflection)
    (x : EuclideanSpace ℝ (Fin 3)) :
    ρ.toEuclideanMotion.1.applyPoint x =
      x - (2 * ⟪x - ρ.point, ρ.fixedPlaneNormal⟫) • ρ.fixedPlaneNormal := by
  -- Rearrange the explicit displacement formula.
  have h := ρ.sub_applyPoint_eq_two_inner_smul_fixedPlaneNormal x
  -- `sub_eq_iff_eq_add` avoids manual additive juggling.
  have hx : x = (2 * ⟪x - ρ.point, ρ.fixedPlaneNormal⟫) • ρ.fixedPlaneNormal +
      ρ.toEuclideanMotion.1.applyPoint x := (sub_eq_iff_eq_add).1 h
  have hx' : x = ρ.toEuclideanMotion.1.applyPoint x +
      (2 * ⟪x - ρ.point, ρ.fixedPlaneNormal⟫) • ρ.fixedPlaneNormal := by
    simpa [add_comm, add_left_comm, add_assoc] using hx
  exact ((sub_eq_iff_eq_add).2 hx').symm

theorem midpoint_mem_fixedPlane (ρ : PlaneReflection) (x : EuclideanSpace ℝ (Fin 3)) :
    ((1 / 2 : ℝ) • (x + ρ.toEuclideanMotion.1.applyPoint x)) ∈ ρ.fixedPlane := by
  -- Freeze the reflected point so rewriting `x` later does not rewrite the argument of `applyPoint`.
  set x' : EuclideanSpace ℝ (Fin 3) := ρ.toEuclideanMotion.1.applyPoint x
  have hx'_def : x' = ρ.toEuclideanMotion.1.applyPoint x := rfl
  have hmid : ((1 / 2 : ℝ) • (x + x')) ∈ ρ.fixedPlane := by
    let v : EuclideanSpace ℝ (Fin 3) := ρ.frameCoordinates x
    refine (ρ.mem_fixedPlane_iff_exists_frameVector ((1 / 2 : ℝ) • (x + x'))).2 ?_
    refine ⟨(1 / 2 : ℝ) • (v + applyMatrix reflectYZMatrix v), ?_, ?_⟩
    · simp only [PiLp.smul_apply, PiLp.add_apply]
      rw [apply_reflectYZMatrix_zero v]
      simp
    · have hx : x = ρ.point + applyMatrix ρ.frameRotation v := by
        simp [v]
      have hfc : ρ.frameCoordinates x' = applyMatrix reflectYZMatrix v := by
        calc
          ρ.frameCoordinates x'
              = ρ.frameCoordinates (ρ.toEuclideanMotion.1.applyPoint x) := by
                  simp [hx'_def]
          _ = applyMatrix reflectYZMatrix v := by
                simpa [v] using (ρ.frameCoordinates_applyPoint x)
      have hx' : x' = ρ.point + applyMatrix ρ.frameRotation (applyMatrix reflectYZMatrix v) := by
        have : x' = ρ.point + applyMatrix ρ.frameRotation (ρ.frameCoordinates x') := by
          simp
        simpa [hfc] using this
      have hhalf_point : ((1 / 2 : ℝ) • (ρ.point + ρ.point)) = ρ.point := by
        calc
          (1 / 2 : ℝ) • (ρ.point + ρ.point)
              = (1 / 2 : ℝ) • ((2 : ℝ) • ρ.point) := by
                  simpa using congrArg (fun t => (1 / 2 : ℝ) • t)
                    (two_smul ℝ ρ.point).symm
          _ = ((1 / 2 : ℝ) * (2 : ℝ)) • ρ.point := by
                simp [smul_smul]
          _ = ρ.point := by
                norm_num
      calc
        (1 / 2 : ℝ) • (x + x')
            = (1 / 2 : ℝ) •
                ((ρ.point + applyMatrix ρ.frameRotation v) +
                  (ρ.point +
                    applyMatrix ρ.frameRotation (applyMatrix reflectYZMatrix v))) := by
                  simp [hx, hx']
        _ = (1 / 2 : ℝ) •
              ((ρ.point + ρ.point) +
                (applyMatrix ρ.frameRotation v +
                  applyMatrix ρ.frameRotation (applyMatrix reflectYZMatrix v))) := by
              simp [add_left_comm, add_comm]
        _ = (1 / 2 : ℝ) • (ρ.point + ρ.point) +
              (1 / 2 : ℝ) •
                (applyMatrix ρ.frameRotation v +
                  applyMatrix ρ.frameRotation (applyMatrix reflectYZMatrix v)) := by
              simp [smul_add]
        _ = ρ.point +
              (1 / 2 : ℝ) •
                (applyMatrix ρ.frameRotation v +
                  applyMatrix ρ.frameRotation (applyMatrix reflectYZMatrix v)) := by
              rw [hhalf_point]
        _ = ρ.point +
              applyMatrix ρ.frameRotation
                ((1 / 2 : ℝ) • (v + applyMatrix reflectYZMatrix v)) := by
              simp [applyMatrix_add, applyMatrix_smul, smul_add]
  simpa [hx'_def] using hmid

theorem vsub_midpoint_mem_fixedPlane_direction_orthogonal (ρ : PlaneReflection)
    (x : EuclideanSpace ℝ (Fin 3)) :
    x -ᵥ ((1 / 2 : ℝ) • (x + ρ.toEuclideanMotion.1.applyPoint x)) ∈ ρ.fixedPlane.directionᗮ := by
  -- In `P = V`, `vsub` is subtraction.
  change x - ((1 / 2 : ℝ) • (x + ρ.toEuclideanMotion.1.applyPoint x)) ∈ ρ.fixedPlane.directionᗮ
  -- Compute the displacement from `x` to the midpoint using the explicit reflection formula.
  have hxsub :
      x - ((1 / 2 : ℝ) • (x + ρ.toEuclideanMotion.1.applyPoint x)) =
        ⟪x - ρ.point, ρ.fixedPlaneNormal⟫ • ρ.fixedPlaneNormal := by
    let x' : EuclideanSpace ℝ (Fin 3) := ρ.toEuclideanMotion.1.applyPoint x
    have hx' : x' = ρ.toEuclideanMotion.1.applyPoint x := rfl
    calc
      x - ((1 / 2 : ℝ) • (x + ρ.toEuclideanMotion.1.applyPoint x))
          = (1 / 2 : ℝ) • (x - x') := by
            -- A small deterministic calculation: `x - (1/2)(x+x') = (1/2)(x-x')`.
            have hxhalf : x - ((2⁻¹ : ℝ) • x) = (2⁻¹ : ℝ) • x := by
              calc
                x - ((2⁻¹ : ℝ) • x) = (1 : ℝ) • x - (2⁻¹ : ℝ) • x := by simp
                _ = ((1 : ℝ) - (2⁻¹ : ℝ)) • x := by
                      symm
                      simpa [sub_eq_add_neg] using (sub_smul (1 : ℝ) (2⁻¹ : ℝ) x)
                _ = (2⁻¹ : ℝ) • x := by norm_num
            calc
              x - ((1 / 2 : ℝ) • (x + ρ.toEuclideanMotion.1.applyPoint x))
                  = x - ((2⁻¹ : ℝ) • (x + x')) := by
                      simp [hx']
              _ = x - ((2⁻¹ : ℝ) • x + (2⁻¹ : ℝ) • x') := by simp [smul_add]
              _ = (x - (2⁻¹ : ℝ) • x) - (2⁻¹ : ℝ) • x' := by
                    simp [sub_add_eq_sub_sub]
              _ = ((2⁻¹ : ℝ) • x) - (2⁻¹ : ℝ) • x' := by simp [hxhalf]
              _ = (2⁻¹ : ℝ) • (x - x') := by simp [smul_sub]
              _ = (1 / 2 : ℝ) • (x - x') := by norm_num
      _ = (1 / 2 : ℝ) • ((2 * ⟪x - ρ.point, ρ.fixedPlaneNormal⟫) • ρ.fixedPlaneNormal) := by
            simpa [hx'] using congrArg (fun t => (1 / 2 : ℝ) • t)
              (ρ.sub_applyPoint_eq_two_inner_smul_fixedPlaneNormal x)
      _ = ⟪x - ρ.point, ρ.fixedPlaneNormal⟫ • ρ.fixedPlaneNormal := by
            simp [smul_smul]
  -- Show the normal vector lies in the orthogonal complement of the plane direction.
  have hn : ρ.fixedPlaneNormal ∈ ρ.fixedPlane.directionᗮ := by
    -- Work with the concrete direction submodule.
    have : ρ.fixedPlaneNormal ∈ ρ.fixedPlaneDirectionᗮ := by
      -- Use `v ∈ Kᗮ ↔ ∀ u ∈ K, ⟪u, v⟫ = 0`.
      rw [Submodule.mem_orthogonal]
      intro u hu
      have hu' : u ∈ (ℝ ∙ ρ.fixedPlaneNormal)ᗮ := by
        simpa [ρ.fixedPlaneDirection_eq_orthogonal_span_fixedPlaneNormal] using hu
      exact (Submodule.mem_orthogonal_singleton_iff_inner_left (u := ρ.fixedPlaneNormal) (v := u)).1 hu'
    simpa [ρ.fixedPlane_direction] using this
  -- Scale stays in the orthogonal complement.
  have hsmul :
      ⟪x - ρ.point, ρ.fixedPlaneNormal⟫ • ρ.fixedPlaneNormal ∈ ρ.fixedPlane.directionᗮ :=
    Submodule.smul_mem ρ.fixedPlane.directionᗮ _ hn
  have hxsub' :
      x - ((2⁻¹ : ℝ) • x + (2⁻¹ : ℝ) • ρ.toEuclideanMotion.1.applyPoint x) =
        ⟪x - ρ.point, ρ.fixedPlaneNormal⟫ • ρ.fixedPlaneNormal := by
    simpa [smul_add] using hxsub
  simpa [hxsub'] using hsmul

theorem orthogonalProjection_fixedPlane_eq_midpoint (ρ : PlaneReflection)
    (x : EuclideanSpace ℝ (Fin 3)) :
    (EuclideanGeometry.orthogonalProjection ρ.fixedPlane x : EuclideanSpace ℝ (Fin 3)) =
      ((1 / 2 : ℝ) • (x + ρ.toEuclideanMotion.1.applyPoint x)) := by
  classical
  -- Use the characterization of orthogonal projection.
  refine (EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem (s := ρ.fixedPlane)
      (p := x) (q := ((1 / 2 : ℝ) • (x + ρ.toEuclideanMotion.1.applyPoint x)))).2 ?_
  refine ⟨ρ.midpoint_mem_fixedPlane x, ?_⟩
  simpa using ρ.vsub_midpoint_mem_fixedPlane_direction_orthogonal x

theorem reflection_fixedPlane_applyPoint (ρ : PlaneReflection) (x : EuclideanSpace ℝ (Fin 3)) :
    (EuclideanGeometry.reflection ρ.fixedPlane x : EuclideanSpace ℝ (Fin 3)) =
      ρ.toEuclideanMotion.1.applyPoint x := by
  classical
  -- Express the reflection using the orthogonal projection onto the plane.
  have hproj :
      (EuclideanGeometry.orthogonalProjection ρ.fixedPlane x : EuclideanSpace ℝ (Fin 3)) =
        ((1 / 2 : ℝ) • (x + ρ.toEuclideanMotion.1.applyPoint x)) :=
    ρ.orthogonalProjection_fixedPlane_eq_midpoint x
  rw [EuclideanGeometry.reflection_apply' (s := ρ.fixedPlane) (p := x)]
  -- In `P = V`, `vsub` is subtraction and `vadd` is addition.
  simp only [vsub_eq_sub, vadd_eq_add]
  rw [hproj]
  -- The remaining goal is a linear computation in the ambient vector space.
  calc
    ((1 / 2 : ℝ) • (x + ρ.toEuclideanMotion.1.applyPoint x) - x) +
        (1 / 2 : ℝ) • (x + ρ.toEuclideanMotion.1.applyPoint x)
        = ((1 / 2 : ℝ) • (x + ρ.toEuclideanMotion.1.applyPoint x) +
              (1 / 2 : ℝ) • (x + ρ.toEuclideanMotion.1.applyPoint x)) - x := by
            simp [sub_eq_add_neg, add_assoc, add_comm]
    _ = (((1 / 2 : ℝ) + (1 / 2 : ℝ)) • (x + ρ.toEuclideanMotion.1.applyPoint x)) - x := by
          simpa using (add_smul (1 / 2 : ℝ) (1 / 2 : ℝ)
            (x + ρ.toEuclideanMotion.1.applyPoint x)).symm
    _ = (x + ρ.toEuclideanMotion.1.applyPoint x) - x := by
          have h : ((2⁻¹ : ℝ) + (2⁻¹ : ℝ)) = 1 := by norm_num
          simp [div_eq_inv_mul, h]
    _ = ρ.toEuclideanMotion.1.applyPoint x := by
          simp

@[simp] theorem applyPoint_applyPoint (ρ : PlaneReflection) (x : EuclideanSpace ℝ (Fin 3)) :
    ρ.toEuclideanMotion.1.applyPoint (ρ.toEuclideanMotion.1.applyPoint x) = x := by
  -- Identify our map with Mathlib's reflection in the fixed plane, then use involutivity.
  calc
    ρ.toEuclideanMotion.1.applyPoint (ρ.toEuclideanMotion.1.applyPoint x)
        = (EuclideanGeometry.reflection ρ.fixedPlane (ρ.toEuclideanMotion.1.applyPoint x) :
            EuclideanSpace ℝ (Fin 3)) := by
              symm
              exact ρ.reflection_fixedPlane_applyPoint (ρ.toEuclideanMotion.1.applyPoint x)
    _ = (EuclideanGeometry.reflection ρ.fixedPlane
          (EuclideanGeometry.reflection ρ.fixedPlane x) : EuclideanSpace ℝ (Fin 3)) := by
          congr 1
          symm
          exact ρ.reflection_fixedPlane_applyPoint x
    _ = x := by
          simp

theorem dist_applyPoint_applyPoint (ρ : PlaneReflection)
    (x y : EuclideanSpace ℝ (Fin 3)) :
    dist (ρ.toEuclideanMotion.1.applyPoint x) (ρ.toEuclideanMotion.1.applyPoint y) = dist x y := by
  -- Transport distance preservation from Mathlib's `AffineIsometryEquiv` reflection.
  simpa [ρ.reflection_fixedPlane_applyPoint] using
    (EuclideanGeometry.reflection ρ.fixedPlane).dist_map x y

/-- A point lies on the fixed plane exactly when it is obtained from `ρ.point` by moving in the
rotated `y`- and `z`-directions. -/
theorem mem_fixedPlane_iff_exists_basisCoordinates (ρ : PlaneReflection)
    (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ ρ.fixedPlane ↔
      ∃ a b : ℝ, x = ρ.point + (a • ρ.fixedPlaneBasisY + b • ρ.fixedPlaneBasisZ) := by
  constructor
  · intro hx
    rcases (ρ.mem_fixedPlane_iff_exists_frameVector x).1 hx with ⟨y, hy0, rfl⟩
    refine ⟨y 1, y 2, ?_⟩
    have hy :
        y = (y 1) • PlaneReflection.frameYAxis + (y 2) • PlaneReflection.frameZAxis := by
      ext i
      fin_cases i <;> simp [PlaneReflection.frameYAxis, PlaneReflection.frameZAxis, hy0]
    calc
      ρ.point + applyMatrix ρ.frameRotation y
          = ρ.point + applyMatrix ρ.frameRotation
              ((y 1) • PlaneReflection.frameYAxis + (y 2) • PlaneReflection.frameZAxis) := by
              conv_lhs => rw [hy]
      _ = ρ.point + ((y 1) • ρ.fixedPlaneBasisY + (y 2) • ρ.fixedPlaneBasisZ) := by
            simp [PlaneReflection.fixedPlaneBasisY, PlaneReflection.fixedPlaneBasisZ,
              applyMatrix_add]
  · rintro ⟨a, b, rfl⟩
    refine (ρ.mem_fixedPlane_iff_exists_frameVector
      (ρ.point + (a • ρ.fixedPlaneBasisY + b • ρ.fixedPlaneBasisZ))).2 ?_
    refine ⟨a • PlaneReflection.frameYAxis + b • PlaneReflection.frameZAxis, ?_, ?_⟩
    · simp [PlaneReflection.frameYAxis, PlaneReflection.frameZAxis]
    · simp [PlaneReflection.fixedPlaneBasisY, PlaneReflection.fixedPlaneBasisZ, applyMatrix_add]

theorem fixedPlane_eq_setOf_applyPoint_eq_self (ρ : PlaneReflection) :
    (ρ.fixedPlane : Set (EuclideanSpace ℝ (Fin 3))) =
      { x | ρ.toEuclideanMotion.1.applyPoint x = x } := by
  ext x
  exact ρ.mem_fixedPlane_iff_applyPoint_eq_self x

theorem handedness_map_eq_neg (ρ : PlaneReflection) (g : TetrahedralGeometry) :
    handedness (ρ.toEuclideanMotion.1 • g) = -handedness g :=
  OrientationReversingEuclideanMotion.handedness_map_eq_neg ρ.toEuclideanMotion g

theorem handedness_mapRealization_eq_neg (ρ : PlaneReflection) (g : Realization) :
    handedness (ρ.toEuclideanMotion.1.mapRealization g).1 = -handedness g.1 :=
  OrientationReversingEuclideanMotion.handedness_mapRealization_eq_neg ρ.toEuclideanMotion g

end PlaneReflection

@[simp] theorem handedness_translation
    (g : TetrahedralGeometry) (t : EuclideanSpace ℝ (Fin 3)) :
    handedness (EuclideanMotion.translationMotion t • g) = handedness g := by
  simp

theorem handedness_mapAffine_of_properRotation
    (g : TetrahedralGeometry) (A : ProperRotation) :
    handedness (mapAffine g (A : Matrix (Fin 3) (Fin 3) ℝ) 0) = handedness g := by
  exact handedness_mapAffine_of_orientationPreserving g A 0 (by
    simp [OrientationPreserving, ProperRotation.det_eq_one A])

theorem handedness_mapAffine_of_improperRotation
    (g : TetrahedralGeometry) (A : ImproperRotation) :
    handedness (mapAffine g (A.1 : Matrix (Fin 3) (Fin 3) ℝ) 0) = -handedness g := by
  exact handedness_mapAffine_of_orientationReversing g A.1 0 (by
    simp [OrientationReversing, A.det_eq_neg_one])

namespace Realization

/-- Two realizations are Euclidean equivalent when one is obtained from the other by a Euclidean
motion. -/
def EuclideanEquivalent (g h : Realization) : Prop :=
  ∃ m : EuclideanMotion, m • g = h

/-- Two realizations are properly Euclidean equivalent when one is obtained from the other by an
orientation-preserving Euclidean motion. -/
def OrientationPreservingEuclideanEquivalent (g h : Realization) : Prop :=
  ∃ m : OrientationPreservingEuclideanMotion, m • g = h

/-- `h` is an orientation-reversing Euclidean image of `g`. -/
def OrientationReversingEuclideanImage (g h : Realization) : Prop :=
  ∃ m : OrientationReversingEuclideanMotion, m.1 • g = h

theorem euclideanEquivalent_of_orientationPreservingEuclideanEquivalent {g h : Realization}
    (hgh : OrientationPreservingEuclideanEquivalent g h) :
    EuclideanEquivalent g h := by
  rcases hgh with ⟨m, hm⟩
  exact ⟨m.1, hm⟩

theorem euclideanEquivalent_of_orientationReversingEuclideanImage {g h : Realization}
    (hgh : OrientationReversingEuclideanImage g h) :
    EuclideanEquivalent g h := by
  rcases hgh with ⟨m, hm⟩
  exact ⟨m.1, hm⟩

theorem handedness_eq_of_orientationPreservingEuclideanEquivalent {g h : Realization}
    (hgh : OrientationPreservingEuclideanEquivalent g h) :
    handedness g.1 = handedness h.1 := by
  rcases hgh with ⟨m, rfl⟩
  simpa [eq_comm] using m.handedness_mapRealization_eq g

theorem handedness_eq_neg_of_orientationReversingEuclideanImage {g h : Realization}
    (hgh : OrientationReversingEuclideanImage g h) :
    handedness h.1 = -handedness g.1 := by
  rcases hgh with ⟨m, rfl⟩
  simpa using m.handedness_mapRealization_eq_neg g

theorem orientationPreservingAffineEquivalent_of_orientationPreservingEuclideanEquivalent
    {g h : Realization} (hgh : OrientationPreservingEuclideanEquivalent g h) :
    OrientationPreservingAffineEquivalent g h := by
  exact (orientationPreservingAffineEquivalent_iff g h).2
    (handedness_eq_of_orientationPreservingEuclideanEquivalent hgh)

theorem affineChiralityClass_eq_of_orientationPreservingEuclideanEquivalent
    {g h : Realization} (hgh : OrientationPreservingEuclideanEquivalent g h) :
    (Quotient.mk realizationSetoid g : AffineChiralityClass) =
      Quotient.mk realizationSetoid h := by
  apply Quotient.sound
  exact orientationPreservingAffineEquivalent_of_orientationPreservingEuclideanEquivalent hgh

@[simp] theorem classifyRealization_eq_of_orientationPreservingEuclideanEquivalent
    {g h : Realization} (hgh : OrientationPreservingEuclideanEquivalent g h) :
    classifyRealization g = classifyRealization h := by
  unfold classifyRealization
  rw [handedness_eq_of_orientationPreservingEuclideanEquivalent hgh]

theorem euclideanEquivalent_refl (g : Realization) :
    EuclideanEquivalent g g :=
  ⟨1, by simp⟩

theorem euclideanEquivalent_symm {g h : Realization} (hgh : EuclideanEquivalent g h) :
    EuclideanEquivalent h g := by
  rcases hgh with ⟨m, hm⟩
  refine ⟨m⁻¹, ?_⟩
  calc
    m⁻¹ • h = m⁻¹ • (m • g) := by rw [hm]
    _ = (m⁻¹ * m) • g := by rw [← mul_smul]
    _ = g := by simp

theorem euclideanEquivalent_trans {g h k : Realization}
    (hgh : EuclideanEquivalent g h) (hhk : EuclideanEquivalent h k) :
    EuclideanEquivalent g k := by
  rcases hgh with ⟨m, hm⟩
  rcases hhk with ⟨n, hn⟩
  refine ⟨n * m, ?_⟩
  calc
    (n * m) • g = n • (m • g) := by simp [mul_smul]
    _ = n • h := by rw [hm]
    _ = k := hn

theorem orientationPreservingEuclideanEquivalent_refl (g : Realization) :
    OrientationPreservingEuclideanEquivalent g g :=
  ⟨1, by simp⟩

theorem orientationPreservingEuclideanEquivalent_symm {g h : Realization}
    (hgh : OrientationPreservingEuclideanEquivalent g h) :
    OrientationPreservingEuclideanEquivalent h g := by
  rcases hgh with ⟨m, hm⟩
  refine ⟨m⁻¹, ?_⟩
  calc
    m⁻¹ • h = m⁻¹ • (m • g) := by rw [hm]
    _ = (m⁻¹ * m) • g := by rw [← mul_smul]
    _ = g := by simp

theorem orientationPreservingEuclideanEquivalent_trans {g h k : Realization}
    (hgh : OrientationPreservingEuclideanEquivalent g h)
    (hhk : OrientationPreservingEuclideanEquivalent h k) :
    OrientationPreservingEuclideanEquivalent g k := by
  rcases hgh with ⟨m, hm⟩
  rcases hhk with ⟨n, hn⟩
  refine ⟨n * m, ?_⟩
  calc
    (n * m) • g = n • (m • g) := by simp [mul_smul]
    _ = n • h := by rw [hm]
    _ = k := hn

/-- The quotient of realizations by proper Euclidean congruence. -/
def properEuclideanSetoid : Setoid Realization where
  r := OrientationPreservingEuclideanEquivalent
  iseqv := ⟨orientationPreservingEuclideanEquivalent_refl,
            orientationPreservingEuclideanEquivalent_symm,
            orientationPreservingEuclideanEquivalent_trans⟩

/-- The quotient of realizations by full Euclidean congruence. -/
def euclideanSetoid : Setoid Realization where
  r := EuclideanEquivalent
  iseqv := ⟨euclideanEquivalent_refl,
            euclideanEquivalent_symm,
            euclideanEquivalent_trans⟩

/-- Realizations modulo proper Euclidean congruence. -/
abbrev ProperEuclideanClass := Quotient properEuclideanSetoid

/-- Realizations modulo full Euclidean congruence. -/
abbrev EuclideanClass := Quotient euclideanSetoid

/-- Forgetful map from proper Euclidean congruence classes to affine chirality classes. -/
def toAffineChiralityClass : ProperEuclideanClass → AffineChiralityClass :=
  Quotient.lift
    (fun g => (Quotient.mk realizationSetoid g : AffineChiralityClass))
    (fun _ _ hgh => affineChiralityClass_eq_of_orientationPreservingEuclideanEquivalent hgh)

@[simp] theorem toAffineChiralityClass_mk (g : Realization) :
    toAffineChiralityClass (Quotient.mk properEuclideanSetoid g) =
      (Quotient.mk realizationSetoid g : AffineChiralityClass) := rfl

/-- The handedness-based chirality classifier descends to proper Euclidean congruence classes. -/
def classifyProperEuclideanClass : ProperEuclideanClass → StereoQ :=
  Quotient.lift classifyRealization
    (fun _ _ hgh => classifyRealization_eq_of_orientationPreservingEuclideanEquivalent hgh)

@[simp] theorem classifyProperEuclideanClass_mk (g : Realization) :
    classifyProperEuclideanClass (Quotient.mk properEuclideanSetoid g) =
      classifyRealization g := rfl

/-- Proper Euclidean congruence classes forget orientation to full Euclidean congruence classes. -/
def toEuclideanClass : ProperEuclideanClass → EuclideanClass :=
  Quotient.lift
    (fun g => (Quotient.mk euclideanSetoid g : EuclideanClass))
    (fun _ _ hgh => Quotient.sound
      (euclideanEquivalent_of_orientationPreservingEuclideanEquivalent hgh))

@[simp] theorem toEuclideanClass_mk (g : Realization) :
    toEuclideanClass (Quotient.mk properEuclideanSetoid g) =
      (Quotient.mk euclideanSetoid g : EuclideanClass) := rfl

end Realization

end TetrahedralGeometry

end

end OneCenter
end TetraStereo
