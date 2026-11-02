import TetraStereo.OneCenter.OccurrenceRule6RankingPermutation
import TetraStereo.OneCenter.CIPRationalTetrahedralParityPermutation
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Geometric calibration of an actual marked frame

The actual tracked ranker supplies the permutation, and the existing all-S₄ determinant law
transports the frame's geometric handedness to that priority order. This derives the readback
formula; it does not assume the desired letter or chemical priority. Missing coordinates are
excluded by explicit coordinate correspondence, while zero volume and non-unique ranking keep
their refusal behavior. The molecular calibration and ordering-correctness obligations remain
separate from this geometric bridge.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedFrameCalibration

open LocalizedGenericMarkedRecalculation CertifiedLocalizedCIPInput
open RationalTetrahedralPermutation Rule6HandednessSemantics
open OccurrenceRule6RankingPermutation

theorem permuted_points_readback (points : Fin 4 → CartesianPoint3)
    (ordering : Equiv.Perm (Fin 4)) :
    descriptorOfPriorityOrderedPoints?
        [points (ordering 0), points (ordering 1), points (ordering 2), points (ordering 3)] =
      if RawMolecule.permutationIsEven (finFourPermutationList ordering) then
        descriptorOfPriorityOrderedPoints? [points 0, points 1, points 2, points 3]
      else (descriptorOfPriorityOrderedPoints? [points 0, points 1, points 2, points 3]).map
        RS.swap := by
  have vector : pointVector (points 0) (points 1) (points 2) (points 3) = points := by
    funext i
    fin_cases i <;> rfl
  have volume := permutedOrientedVolume_eq_if_permutationIsEven
    (points 0) (points 1) (points 2) (points 3) ordering
  simp only [permutedOrientedVolume, vector] at volume
  simp only [descriptorOfPriorityOrderedPoints?]
  rw [volume]
  split_ifs <;> simp [descriptorOfOrientedVolume?_neg]

private theorem four_lookup (atoms : Fin 4 → Nat) (i : Fin 4) :
    [atoms 0, atoms 1, atoms 2, atoms 3][i.val]? = some (atoms i) := by
  fin_cases i <;> rfl

theorem select_permutation (atoms : Fin 4 → Nat) (ordering : Equiv.Perm (Fin 4)) :
    atomsAt? [atoms 0, atoms 1, atoms 2, atoms 3] (finFourPermutationList ordering) =
      some [atoms (ordering 0), atoms (ordering 1), atoms (ordering 2), atoms (ordering 3)] := by
  change ([(ordering 0).val, (ordering 1).val, (ordering 2).val, (ordering 3).val].mapM
    fun i => [atoms 0, atoms 1, atoms 2, atoms 3][i]?) = _
  simp only [List.mapM_cons, List.mapM_nil, four_lookup]
  rfl

theorem readback_coordinates (geom : Geometry) (atoms : Fin 4 → Nat)
    (points : Fin 4 → CartesianPoint3) (coordinates : ∀ i, geom (atoms i) = some (points i))
    (i j k l : Fin 4) :
    readback? geom [atoms i, atoms j, atoms k, atoms l] =
      descriptorOfPriorityOrderedPoints? [points i, points j, points k, points l] := by
  simp [readback?, coordinates]

/-- Any actual permutation has its readback fixed by the original frame and its parity. -/
theorem reordered_readback (geom : Geometry) (atoms : Fin 4 → Nat)
    (points : Fin 4 → CartesianPoint3) (coordinates : ∀ i, geom (atoms i) = some (points i))
    (positions : List Nat) (permutation : positions.Perm [0, 1, 2, 3]) :
    (atomsAt? [atoms 0, atoms 1, atoms 2, atoms 3] positions).bind (readback? geom) =
      if RawMolecule.permutationIsEven positions then
        descriptorOfPriorityOrderedPoints? [points 0, points 1, points 2, points 3]
      else (descriptorOfPriorityOrderedPoints? [points 0, points 1, points 2, points 3]).map
        RS.swap := by
  let ordering := finFourEquivOfPermutationList positions (by simpa using permutation)
  have code : finFourPermutationList ordering = positions :=
    finFourPermutationList_equivOfPermutationList positions _
  rw [← code, select_permutation]
  change readback? geom
    [atoms (ordering 0), atoms (ordering 1), atoms (ordering 2), atoms (ordering 3)] = _
  rw [readback_coordinates geom atoms points coordinates, permuted_points_readback]

/-- The marked evaluator's letter is derived from its original frame calibration and the
parity of its actual computed ranking. The ranking permutation is proved from execution. -/
theorem marked_readback_of_calibration (mol : RawMolecule) (fuel : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) (mark : Nat)
    (atoms : Fin 4 → Nat) (points : Fin 4 → CartesianPoint3)
    (frame : frameAtoms? mol node = some [atoms 0, atoms 1, atoms 2, atoms 3])
    (coordinates : ∀ i, geom (atoms i) = some (points i))
    (ranking : Rule6TrackedRanking) (computed : marked? mol fuel state node mark = some ranking) :
    markedReadback? mol fuel geom state node mark =
      if ranking.unique then
        if RawMolecule.permutationIsEven ranking.positions then
          descriptorOfPriorityOrderedPoints? [points 0, points 1, points 2, points 3]
        else (descriptorOfPriorityOrderedPoints? [points 0, points 1, points 2, points 3]).map
          RS.swap
      else none := by
  by_cases unique : ranking.unique = true
  · have formula := reordered_readback geom atoms points coordinates ranking.positions
      (marked_positions_perm mol state fuel node mark ranking computed)
    simpa [markedReadback?, frame, computed, rankedAtoms?, unique, atomsAt?] using formula
  · simp [markedReadback?, frame, computed, rankedAtoms?, unique]

end TetraStereo.OneCenter.LocalizedMarkedFrameCalibration

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedFrameCalibration.permuted_points_readback
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedFrameCalibration.reordered_readback
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedFrameCalibration.marked_readback_of_calibration
