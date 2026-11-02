import TetraStereo.OneCenter.Euclidean

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

open TetrahedralGeometry
open scoped RealInnerProductSpace

namespace Lemmas

/-- Copy of the main geometric characterization of a plane reflection's fixed plane.

This lemma is defined (and proved) in `TetraStereo.OneCenter.Euclidean` as
`TetrahedralGeometry.PlaneReflection.fixedPlane_geometric`. We re-export it here under a stable,
searchable name for future reference and downstream reuse.
-/
theorem planeReflection_fixedPlane_geometric (ρ : TetrahedralGeometry.PlaneReflection) :
    (ρ.fixedPlane : Set (EuclideanSpace ℝ (Fin 3))) =
        { x | ⟪x, ρ.fixedPlaneNormal⟫ = ⟪ρ.point, ρ.fixedPlaneNormal⟫ } ∧
      ρ.fixedPlane.direction = (ℝ ∙ ρ.fixedPlaneNormal)ᗮ ∧
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3) ⧸ ρ.fixedPlane.direction) = 1 := by
  simpa using ρ.fixedPlane_geometric

/-- Re-export: the plane reflection map agrees with Mathlib's reflection in the fixed plane. -/
theorem planeReflection_reflection_eq_applyPoint (ρ : TetrahedralGeometry.PlaneReflection)
    (x : EuclideanSpace ℝ (Fin 3)) :
    (EuclideanGeometry.reflection ρ.fixedPlane x : EuclideanSpace ℝ (Fin 3)) =
      ρ.toEuclideanMotion.1.applyPoint x := by
  simpa using ρ.reflection_fixedPlane_applyPoint x

@[simp] theorem planeReflection_applyPoint_applyPoint (ρ : TetrahedralGeometry.PlaneReflection)
    (x : EuclideanSpace ℝ (Fin 3)) :
    ρ.toEuclideanMotion.1.applyPoint (ρ.toEuclideanMotion.1.applyPoint x) = x := by
  simp

theorem planeReflection_dist_applyPoint_applyPoint (ρ : TetrahedralGeometry.PlaneReflection)
    (x y : EuclideanSpace ℝ (Fin 3)) :
    dist (ρ.toEuclideanMotion.1.applyPoint x) (ρ.toEuclideanMotion.1.applyPoint y) = dist x y :=
  ρ.dist_applyPoint_applyPoint x y

theorem planeReflection_midpoint_mem_fixedPlane (ρ : TetrahedralGeometry.PlaneReflection)
    (x : EuclideanSpace ℝ (Fin 3)) :
    ((1 / 2 : ℝ) • (x + ρ.toEuclideanMotion.1.applyPoint x)) ∈ ρ.fixedPlane := by
  simpa using ρ.midpoint_mem_fixedPlane x

theorem planeReflection_orthogonalProjection_fixedPlane_eq_midpoint
    (ρ : TetrahedralGeometry.PlaneReflection) (x : EuclideanSpace ℝ (Fin 3)) :
    (EuclideanGeometry.orthogonalProjection ρ.fixedPlane x : EuclideanSpace ℝ (Fin 3)) =
      ((1 / 2 : ℝ) • (x + ρ.toEuclideanMotion.1.applyPoint x)) := by
  simpa using ρ.orthogonalProjection_fixedPlane_eq_midpoint x

/-- A compact “one-stop” bundle of the key geometric facts about a plane reflection. -/
theorem planeReflection_api (ρ : TetrahedralGeometry.PlaneReflection) :
    (ρ.fixedPlane : Set (EuclideanSpace ℝ (Fin 3))) =
        { x | ⟪x, ρ.fixedPlaneNormal⟫ = ⟪ρ.point, ρ.fixedPlaneNormal⟫ } ∧
      ρ.fixedPlane.direction = (ℝ ∙ ρ.fixedPlaneNormal)ᗮ ∧
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3) ⧸ ρ.fixedPlane.direction) = 1 ∧
      (∀ x, (EuclideanGeometry.reflection ρ.fixedPlane x : EuclideanSpace ℝ (Fin 3)) =
        ρ.toEuclideanMotion.1.applyPoint x) ∧
      (∀ x, (EuclideanGeometry.orthogonalProjection ρ.fixedPlane x : EuclideanSpace ℝ (Fin 3)) =
        ((1 / 2 : ℝ) • (x + ρ.toEuclideanMotion.1.applyPoint x))) ∧
      (∀ x, ρ.toEuclideanMotion.1.applyPoint (ρ.toEuclideanMotion.1.applyPoint x) = x) ∧
      (∀ x y, dist (ρ.toEuclideanMotion.1.applyPoint x) (ρ.toEuclideanMotion.1.applyPoint y) =
        dist x y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (planeReflection_fixedPlane_geometric ρ).1
  · exact (planeReflection_fixedPlane_geometric ρ).2.1
  · exact (planeReflection_fixedPlane_geometric ρ).2.2
  · intro x
    exact planeReflection_reflection_eq_applyPoint ρ x
  · intro x
    exact planeReflection_orthogonalProjection_fixedPlane_eq_midpoint ρ x
  · intro x
    exact planeReflection_applyPoint_applyPoint ρ x
  · intro x y
    exact planeReflection_dist_applyPoint_applyPoint ρ x y

end Lemmas

end OneCenter
end TetraStereo
