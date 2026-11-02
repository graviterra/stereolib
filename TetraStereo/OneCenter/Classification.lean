import TetraStereo.OneCenter.Affine
import TetraStereo.OneCenter.StandardModel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

open TetrahedralGeometry

noncomputable section

namespace TetrahedralGeometry

/-- Affine coordinates of a tetrahedral realization relative to the standard model. -/
structure AffineCoordinates where
  linear : Matrix (Fin 3) (Fin 3) ℝ
  translation : EuclideanSpace ℝ (Fin 3)

/-- Realize affine coordinates by applying them to the standard model tetrahedron. -/
def AffineCoordinates.realize (p : AffineCoordinates) : TetrahedralGeometry :=
  mapAffine modelGeometry p.linear p.translation

/-- Extract affine coordinates from a tetrahedral realization. -/
def AffineCoordinates.ofGeometry (g : TetrahedralGeometry) : AffineCoordinates where
  linear := edgeMatrix g
  translation := g.vertex 3

@[simp] theorem applyMatrix_basisPoint
    (A : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    applyMatrix A (basisPoint i) j = A i j := by
  simp [applyMatrix_apply, basisPoint_apply]

@[simp] theorem AffineCoordinates.realize_ofGeometry_vertex_castSucc
    (g : TetrahedralGeometry) (i : Fin 3) :
    (AffineCoordinates.ofGeometry g).realize.vertex i.castSucc = g.vertex i.castSucc := by
  ext j
  simp [AffineCoordinates.realize, AffineCoordinates.ofGeometry, mapAffine, mapLinear, translate,
    edgeMatrix]

@[simp] theorem AffineCoordinates.realize_ofGeometry_vertex_three
    (g : TetrahedralGeometry) :
    (AffineCoordinates.ofGeometry g).realize.vertex (3 : Fin 4) = g.vertex 3 := by
  ext j
  simp [AffineCoordinates.realize, AffineCoordinates.ofGeometry, mapAffine, mapLinear, translate]

@[simp] theorem AffineCoordinates.realize_ofGeometry
    (g : TetrahedralGeometry) :
    (AffineCoordinates.ofGeometry g).realize = g := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · exact congrArg (fun v => v j) (AffineCoordinates.realize_ofGeometry_vertex_three g)
  · exact congrArg (fun v => v j) (AffineCoordinates.realize_ofGeometry_vertex_castSucc g i)

theorem AffineCoordinates.eq_of_realize_eq
    (p : AffineCoordinates) {g : TetrahedralGeometry} (h : p.realize = g) :
    p = AffineCoordinates.ofGeometry g := by
  cases p with
  | mk A b =>
      have hb : b = g.vertex 3 := by
        have h3 := congrArg (fun geom => geom.vertex (3 : Fin 4)) h
        simpa [AffineCoordinates.realize, mapAffine, mapLinear, translate] using h3
      have hA : A = edgeMatrix g := by
        have hedge := congrArg edgeMatrix h
        simpa [AffineCoordinates.realize, edgeMatrix_mapAffine, edgeMatrix_modelGeometry] using hedge
      simp [AffineCoordinates.ofGeometry, hA, hb]

theorem existsUnique_affineCoordinates (g : TetrahedralGeometry) :
    ∃! p : AffineCoordinates, p.realize = g := by
  refine ⟨AffineCoordinates.ofGeometry g, AffineCoordinates.realize_ofGeometry g, ?_⟩
  intro p hp
  exact AffineCoordinates.eq_of_realize_eq p hp

@[simp] theorem AffineCoordinates.det_linear_ofGeometry
    (g : TetrahedralGeometry) :
    Matrix.det (AffineCoordinates.ofGeometry g).linear = orientedVolume g := by
  simp [AffineCoordinates.ofGeometry, orientedVolume_eq_edgeMatrix_det]

@[simp] theorem AffineCoordinates.nondegenerate_realize_iff
    (p : AffineCoordinates) :
    Nondegenerate p.realize ↔ Matrix.det p.linear ≠ 0 := by
  simpa [AffineCoordinates.realize] using
    nondegenerate_mapAffine_iff modelGeometry p.linear p.translation

/-- Affine coordinates with invertible linear part. -/
abbrev InvertibleAffineCoordinates :=
  { p : AffineCoordinates // Matrix.det p.linear ≠ 0 }

def InvertibleAffineCoordinates.ofRealization (g : Realization) :
    InvertibleAffineCoordinates :=
  ⟨AffineCoordinates.ofGeometry g.1, by
    simpa [AffineCoordinates.ofGeometry, Nondegenerate, orientedVolume_eq_edgeMatrix_det] using g.2⟩

@[simp] theorem InvertibleAffineCoordinates.realize_ofRealization
    (g : Realization) :
    (InvertibleAffineCoordinates.ofRealization g).1.realize = g.1 :=
  AffineCoordinates.realize_ofGeometry g.1

theorem existsUnique_invertibleAffineCoordinates (g : Realization) :
    ∃! p : InvertibleAffineCoordinates, p.1.realize = g.1 := by
  refine ⟨InvertibleAffineCoordinates.ofRealization g,
    InvertibleAffineCoordinates.realize_ofRealization g, ?_⟩
  intro p hp
  apply Subtype.ext
  exact AffineCoordinates.eq_of_realize_eq p.1 hp

@[simp] theorem AffineCoordinates.handedness_realize
    (p : AffineCoordinates) :
    handedness p.realize = Real.sign (Matrix.det p.linear) := by
  rw [AffineCoordinates.realize, handedness, orientedVolume_mapAffine, modelGeometry_orientedVolume]
  simp

theorem handedness_eq_sign_det_affineCoordinates (g : TetrahedralGeometry) :
    handedness g = Real.sign (Matrix.det (AffineCoordinates.ofGeometry g).linear) := by
  simpa using (AffineCoordinates.handedness_realize (AffineCoordinates.ofGeometry g))

end TetrahedralGeometry

end

end OneCenter
end TetraStereo
