import TetraStereo.OneCenter.Geometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

open TetrahedralGeometry

noncomputable section

/-- The `i`-th standard basis point of `R^3`, viewed in the chosen Euclidean model. -/
def basisPoint (i : Fin 3) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (Pi.single i (1 : ℝ))

@[simp] theorem basisPoint_apply (i j : Fin 3) :
    basisPoint i j = if i = j then 1 else 0 := by
  simp [basisPoint, eq_comm]

/-- A standard positively oriented model tetrahedron with the fourth vertex at the origin. -/
def modelGeometry : TetrahedralGeometry where
  vertex := Fin.lastCases 0 basisPoint

@[simp] theorem modelGeometry_vertex_castSucc (i : Fin 3) :
    modelGeometry.vertex i.castSucc = basisPoint i := by
  simp [modelGeometry, Fin.lastCases_castSucc]

@[simp] theorem modelGeometry_vertex_three :
    modelGeometry.vertex (3 : Fin 4) = 0 := by
  rfl

@[simp] theorem edgeMatrix_modelGeometry :
    edgeMatrix modelGeometry = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  simp [edgeMatrix, basisPoint_apply, Matrix.one_apply]

@[simp] theorem modelGeometry_orientedVolume : orientedVolume modelGeometry = 1 := by
  rw [orientedVolume_eq_edgeMatrix_det, edgeMatrix_modelGeometry, Matrix.det_one]

@[simp] theorem modelGeometry_nondegenerate : Nondegenerate modelGeometry := by
  simp [Nondegenerate]

@[simp] theorem modelGeometry_handedness : handedness modelGeometry = 1 := by
  rw [handedness, modelGeometry_orientedVolume]
  exact Real.sign_of_pos (by norm_num)

end

end OneCenter
end TetraStereo
