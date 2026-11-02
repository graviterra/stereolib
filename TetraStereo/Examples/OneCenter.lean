import TetraStereo.OneCenter.Classification
import TetraStereo.OneCenter.Toy
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace TetraStereo
namespace Examples

open OneCenter
open OneCenter.TetrahedralGeometry

def positiveDiagonal : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![(2 : ℝ), 3, 5]

def reflectionZ : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![(1 : ℝ), 1, -1]

@[simp] theorem det_positiveDiagonal : Matrix.det positiveDiagonal = 30 := by
  rw [positiveDiagonal, Matrix.det_diagonal, Fin.prod_univ_three]
  simp
  norm_num

@[simp] theorem det_reflectionZ : Matrix.det reflectionZ = -1 := by
  rw [reflectionZ, Matrix.det_diagonal, Fin.prod_univ_three]
  simp

example : orientedVolume modelGeometry = 1 := modelGeometry_orientedVolume

example : Nondegenerate modelGeometry := modelGeometry_nondegenerate

example (t : EuclideanSpace ℝ (Fin 3)) :
    orientedVolume (translate modelGeometry t) = 1 := by
  simp

example (t : EuclideanSpace ℝ (Fin 3)) :
    handedness (translate modelGeometry t) = 1 := by
  simp [modelGeometry_handedness]

example : handedness (canonicalGeometry rightHandedFrame) = 1 := by
  simpa [rightHandedFrame] using canonicalHandedness_matches_parity rightHandedFrame

example : handedness (canonicalGeometry leftHandedFrame) = -1 := by
  simpa [leftHandedFrame] using canonicalHandedness_matches_parity leftHandedFrame

example (sigma : Frame) : Nondegenerate (canonicalGeometry sigma) := by
  simp [canonicalGeometry]

example (A : Matrix (Fin 3) (Fin 3) ℝ) (b : EuclideanSpace ℝ (Fin 3))
    (hA : Matrix.det A ≠ 0) :
    Nondegenerate (mapAffine modelGeometry A b) := by
  exact nondegenerate_mapAffine_of_det_ne_zero modelGeometry A b modelGeometry_nondegenerate hA

example (g : TetrahedralGeometry) :
    ∃! p : TetrahedralGeometry.AffineCoordinates, p.realize = g := by
  exact existsUnique_affineCoordinates g

example (b : EuclideanSpace ℝ (Fin 3)) :
    handedness (mapAffine modelGeometry positiveDiagonal b) = 1 := by
  have hpos : OrientationPreserving positiveDiagonal := by
    simp [OrientationPreserving]
  simpa [positiveDiagonal] using
    handedness_mapAffine_of_orientationPreserving modelGeometry positiveDiagonal b hpos

example (b : EuclideanSpace ℝ (Fin 3)) :
    handedness (mapAffine modelGeometry reflectionZ b) = -1 := by
  have hneg : OrientationReversing reflectionZ := by
    simp [OrientationReversing]
  rw [handedness_mapAffine_of_orientationReversing modelGeometry reflectionZ b hneg]
  simp [modelGeometry_handedness]

example : qPlus ≠ qMinus := qPlus_ne_qMinus

example : ∀ q : StereoQ, q = qPlus ∨ q = qMinus := quotient_two_point

end Examples
end TetraStereo
