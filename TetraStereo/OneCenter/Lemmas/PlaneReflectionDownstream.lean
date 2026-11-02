import TetraStereo.OneCenter.Lemmas.FixedPlaneGeometric

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

open TetrahedralGeometry
open scoped RealInnerProductSpace

namespace Lemmas

/-- Downstream corollary: the displacement from `x` to the midpoint between `x` and its reflected
image is orthogonal to the fixed plane direction. -/
theorem planeReflection_vsub_midpoint_mem_fixedPlane_direction_orthogonal
    (ρ : TetrahedralGeometry.PlaneReflection) (x : EuclideanSpace ℝ (Fin 3)) :
    x -ᵥ ((1 / 2 : ℝ) • (x + ρ.toEuclideanMotion.1.applyPoint x)) ∈ ρ.fixedPlane.directionᗮ := by
  classical
  have ⟨_, _, _, _, hproj, _, _⟩ := Lemmas.planeReflection_api ρ
  simpa [hproj x] using
    (EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal
      (s := ρ.fixedPlane) (p := x))

/-- Re-express the projection-midpoint formula using Mathlib's `EuclideanGeometry.reflection`. -/
theorem planeReflection_orthogonalProjection_fixedPlane_eq_midpoint_reflection
    (ρ : TetrahedralGeometry.PlaneReflection) (x : EuclideanSpace ℝ (Fin 3)) :
    (EuclideanGeometry.orthogonalProjection ρ.fixedPlane x : EuclideanSpace ℝ (Fin 3)) =
      ((1 / 2 : ℝ) • (x + (EuclideanGeometry.reflection ρ.fixedPlane x : EuclideanSpace ℝ (Fin 3)))) := by
  classical
  have ⟨_, _, _, hreflect, hproj, _, _⟩ := Lemmas.planeReflection_api ρ
  simpa [(hreflect x).symm] using (hproj x)

/-- Express the plane-reflection map in terms of orthogonal projection onto the fixed plane. -/
theorem planeReflection_applyPoint_eq_two_smul_orthogonalProjection_sub
    (ρ : TetrahedralGeometry.PlaneReflection) (x : EuclideanSpace ℝ (Fin 3)) :
    ρ.toEuclideanMotion.1.applyPoint x =
      (2 : ℝ) • (EuclideanGeometry.orthogonalProjection ρ.fixedPlane x : EuclideanSpace ℝ (Fin 3)) -
        x := by
  classical
  have ⟨_, _, _, _, hproj, _, _⟩ := Lemmas.planeReflection_api ρ
  have h2 :
      (2 : ℝ) • (EuclideanGeometry.orthogonalProjection ρ.fixedPlane x : EuclideanSpace ℝ (Fin 3)) =
        x + ρ.toEuclideanMotion.1.applyPoint x := by
    have := congrArg (fun z => (2 : ℝ) • z) (hproj x)
    simpa [smul_smul] using this
  have := congrArg (fun z => z - x) h2
  simpa [add_sub_cancel_left] using this.symm

end Lemmas

end OneCenter
end TetraStereo
