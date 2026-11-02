import TetraStereo.OneCenter.CIPRationalTetrahedralParityPermutation
import TetraStereo.OneCenter.AuthoritativeSemanticParserDiagramRule3Through6Analysis

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Exact point-parity transport for every four-slot permutation

The permutation sends new slots to old slots. The existing all-`S₄` determinant theorem
therefore transports the executable point-to-parity computation with exactly the same
convention as `reindexTetrahedralInputParity`. The equality is an `Option` equality:
coplanar and repeated-point frames retain `none`, rather than acquiring an orientation.

The executable producer uses the calibrated standard right-handed Cartesian convention:
a negative written-order affine determinant is `clockwise` and a positive one is
`anticlockwise`.  Reindexing transports those carriers as before; only which determinant sign
receives which carrier changes.

This is an algebraic statement about four arbitrary rational points. It does not supply
coordinates from a drawing, establish chemical stereogenicity, or approve a source.
-/

open RationalTetrahedralPermutation

/-- Exact executable parity transport, including the zero-volume refusal branch. -/
theorem tetrahedralInputParityOfPoints?_permutedPoints
    (first second third fourth : CartesianPoint3)
    (newToOld : Equiv.Perm (Fin 4)) :
    tetrahedralInputParityOfPoints?
        (permutedPoints first second third fourth newToOld) =
      (tetrahedralInputParityOfPoints? [first, second, third, fourth]).map
        (fun parity => reindexTetrahedralInputParity parity newToOld) := by
  change
    (if permutedOrientedVolume first second third fourth newToOld < 0 then
        some TetrahedralInputParity.clockwise
      else if 0 < permutedOrientedVolume first second third fourth newToOld then
        some TetrahedralInputParity.anticlockwise
      else none) = _
  rw [permutedOrientedVolume_eq_if_permutationIsEven]
  by_cases even : RawMolecule.permutationIsEven
      (Rule6HandednessSemantics.finFourPermutationList newToOld) = true
  · simp [even, tetrahedralInputParityOfPoints?, reindexTetrahedralInputParity]
  · rcases lt_trichotomy
        (CartesianPoint3.orientedVolume first second third fourth) 0 with
      negative | zero | positive
    · have permutedPositive :
          0 < -CartesianPoint3.orientedVolume first second third fourth :=
        neg_pos.mpr negative
      have permutedNotNegative :
          ¬ -CartesianPoint3.orientedVolume first second third fourth < 0 :=
        not_lt_of_ge permutedPositive.le
      have notPositive :
          ¬ 0 < CartesianPoint3.orientedVolume first second third fourth :=
        not_lt_of_ge negative.le
      simp [even, tetrahedralInputParityOfPoints?, reindexTetrahedralInputParity,
        reverseTetrahedralInputParity, negative,
        permutedPositive, permutedNotNegative]
    · simp [even, tetrahedralInputParityOfPoints?, reindexTetrahedralInputParity,
        zero]
    · have permutedNegative :
          -CartesianPoint3.orientedVolume first second third fourth < 0 :=
        neg_neg_of_pos positive
      have permutedNotPositive :
          ¬ 0 < -CartesianPoint3.orientedVolume first second third fourth :=
        not_lt_of_ge permutedNegative.le
      have notNegative :
          ¬ CartesianPoint3.orientedVolume first second third fourth < 0 :=
        not_lt_of_ge positive.le
      simp [even, tetrahedralInputParityOfPoints?, reindexTetrahedralInputParity,
        reverseTetrahedralInputParity, positive, notNegative,
        permutedNegative]

private theorem reindexTetrahedralInputParity_injective
    (newToOld : Equiv.Perm (Fin 4)) :
    Function.Injective (fun parity => reindexTetrahedralInputParity parity newToOld) := by
  intro first second equality
  cases even : RawMolecule.permutationIsEven
      (Rule6HandednessSemantics.finFourPermutationList newToOld) <;>
    cases first <;> cases second <;>
      simp [reindexTetrahedralInputParity, reverseTetrahedralInputParity, even]
        at equality ⊢

/-- A specific successful parity is transported in both directions. -/
theorem tetrahedralInputParityOfPoints?_permutedPoints_eq_some_iff
    (first second third fourth : CartesianPoint3)
    (newToOld : Equiv.Perm (Fin 4)) (parity : TetrahedralInputParity) :
    tetrahedralInputParityOfPoints?
        (permutedPoints first second third fourth newToOld) =
        some (reindexTetrahedralInputParity parity newToOld) ↔
      tetrahedralInputParityOfPoints? [first, second, third, fourth] = some parity := by
  rw [tetrahedralInputParityOfPoints?_permutedPoints]
  cases tetrahedralInputParityOfPoints? [first, second, third, fourth] with
  | none => simp
  | some original =>
      simp only [Option.map_some, Option.some.injEq]
      exact (reindexTetrahedralInputParity_injective newToOld).eq_iff

/-- Reindexing neither introduces nor removes a point-parity refusal. -/
theorem tetrahedralInputParityOfPoints?_permutedPoints_eq_none_iff
    (first second third fourth : CartesianPoint3)
    (newToOld : Equiv.Perm (Fin 4)) :
    tetrahedralInputParityOfPoints?
        (permutedPoints first second third fourth newToOld) = none ↔
      tetrahedralInputParityOfPoints? [first, second, third, fourth] = none := by
  rw [tetrahedralInputParityOfPoints?_permutedPoints]
  cases tetrahedralInputParityOfPoints? [first, second, third, fourth] <;> simp

/-- For exactly four points, refusal is precisely degeneracy of the affine determinant. -/
theorem tetrahedralInputParityOfFourPoints?_eq_none_iff_zero
    (first second third fourth : CartesianPoint3) :
    tetrahedralInputParityOfPoints? [first, second, third, fourth] = none ↔
      CartesianPoint3.orientedVolume first second third fourth = 0 := by
  rcases lt_trichotomy
      (CartesianPoint3.orientedVolume first second third fourth) 0 with
    negative | zero | positive
  · simp [tetrahedralInputParityOfPoints?, negative, ne_of_lt negative]
  · simp [tetrahedralInputParityOfPoints?, zero]
  · have notNegative :
        ¬ CartesianPoint3.orientedVolume first second third fourth < 0 :=
      not_lt_of_ge positive.le
    simp [tetrahedralInputParityOfPoints?, positive, notNegative, ne_of_gt positive]

/-- Every slot permutation preserves precisely the same degenerate frames. -/
theorem tetrahedralInputParityOfPoints?_permutedPoints_eq_none_iff_zero
    (first second third fourth : CartesianPoint3)
    (newToOld : Equiv.Perm (Fin 4)) :
    tetrahedralInputParityOfPoints?
        (permutedPoints first second third fourth newToOld) = none ↔
      CartesianPoint3.orientedVolume first second third fourth = 0 := by
  rw [tetrahedralInputParityOfPoints?_permutedPoints_eq_none_iff,
    tetrahedralInputParityOfFourPoints?_eq_none_iff_zero]

end AuthoritativeChemicalInput

namespace TetrahedralPointParityReindexRegression

open AuthoritativeChemicalInput RationalTetrahedralPermutation

def origin : CartesianPoint3 := ⟨0, 0, 0⟩
def xAxis : CartesianPoint3 := ⟨1, 0, 0⟩
def yAxis : CartesianPoint3 := ⟨0, 1, 0⟩
def zAxis : CartesianPoint3 := ⟨0, 0, 1⟩




theorem calibration_witness_volume :
    CartesianPoint3.orientedVolume ⟨0, 1, 1⟩ ⟨1, -1, 1⟩ ⟨-1, -1, 1⟩ ⟨0, 0, -1⟩ =
      -8 := by
  norm_num [CartesianPoint3.orientedVolume]

/-- The calibrated producer reads that audited negative-volume witness as `clockwise`. -/
theorem calibration_witness_parity :
    tetrahedralInputParityOfPoints?
        [⟨0, 1, 1⟩, ⟨1, -1, 1⟩, ⟨-1, -1, 1⟩, ⟨0, 0, -1⟩] =
      some .clockwise := by
  norm_num [tetrahedralInputParityOfPoints?, CartesianPoint3.orientedVolume]

/-- With an even (identity) priority permutation, the unchanged symbolic SMILES algebra maps the
audited `clockwise` written parity to `R`, matching the primary-source expectation. -/
theorem calibration_witness_descriptor_algebra :
    RawMolecule.descriptorOfParity .clockwise true = RS.R := rfl

/-- The closed test frame has nonzero volume and an actual successful orientation.  Under the
calibrated standard right-handed frame the determinant is `-1`, hence `clockwise`.  The historical
declaration name is retained as a stable API key. -/
theorem coordinate_frame_has_anticlockwise_parity :
    tetrahedralInputParityOfPoints? [origin, xAxis, yAxis, zAxis] =
      some .clockwise := by
  norm_num [tetrahedralInputParityOfPoints?, CartesianPoint3.orientedVolume,
    RationalTetrahedralPermutation.permutedPoints, RationalTetrahedralPermutation.pointVector,
    origin, xAxis, yAxis, zAxis, Equiv.swap_apply_def]

/-- The odd-permutation fixture returns the opposite successful orientation (`anticlockwise`).
The historical declaration name is retained as a stable API key. -/
theorem swapped_coordinate_frame_has_clockwise_parity :
    tetrahedralInputParityOfPoints?
        (permutedPoints origin xAxis yAxis zAxis (Equiv.swap (0 : Fin 4) 1)) =
      some .anticlockwise := by
  rw [tetrahedralInputParityOfPoints?_permutedPoints,
    coordinate_frame_has_anticlockwise_parity]
  have odd : RawMolecule.permutationIsEven
      (Rule6HandednessSemantics.finFourPermutationList (Equiv.swap (0 : Fin 4) 1)) = false := by
    decide
  simp [reindexTetrahedralInputParity, odd, reverseTetrahedralInputParity]

/-- Identity is a closed even-permutation regression on a nondegenerate frame. -/
theorem identity_preserves_parity :
    tetrahedralInputParityOfPoints?
        (permutedPoints origin xAxis yAxis zAxis (Equiv.refl (Fin 4))) =
      tetrahedralInputParityOfPoints? [origin, xAxis, yAxis, zAxis] := by
  rfl

/-- A transposition gives the same exact reversal as the frame-parity algebra. -/
theorem swap_zero_one_reverses_parity :
    tetrahedralInputParityOfPoints?
        (permutedPoints origin xAxis yAxis zAxis (Equiv.swap (0 : Fin 4) 1)) =
      (tetrahedralInputParityOfPoints? [origin, xAxis, yAxis, zAxis]).map
        reverseTetrahedralInputParity := by
  rw [tetrahedralInputParityOfPoints?_permutedPoints]
  have odd : RawMolecule.permutationIsEven
      (Rule6HandednessSemantics.finFourPermutationList (Equiv.swap (0 : Fin 4) 1)) = false := by
    decide
  simp [reindexTetrahedralInputParity, odd]

/-- A nontrivial even permutation preserves the computed parity. -/
theorem double_swap_preserves_parity :
    tetrahedralInputParityOfPoints?
        (permutedPoints origin xAxis yAxis zAxis
          ((Equiv.swap (0 : Fin 4) 1).trans (Equiv.swap (2 : Fin 4) 3))) =
      tetrahedralInputParityOfPoints? [origin, xAxis, yAxis, zAxis] := by
  rw [tetrahedralInputParityOfPoints?_permutedPoints]
  have even : RawMolecule.permutationIsEven
      (Rule6HandednessSemantics.finFourPermutationList
        ((Equiv.swap (0 : Fin 4) 1).trans (Equiv.swap (2 : Fin 4) 3))) = true := by
    decide
  simp [reindexTetrahedralInputParity, even]

/-- A planar frame remains refused after an odd permutation. -/
theorem planar_swap_has_no_parity :
    tetrahedralInputParityOfPoints?
        (permutedPoints origin xAxis yAxis ⟨1, 1, 0⟩
          (Equiv.swap (0 : Fin 4) 3)) = none := by
  rw [tetrahedralInputParityOfPoints?_permutedPoints_eq_none_iff_zero]
  norm_num [CartesianPoint3.orientedVolume, origin, xAxis, yAxis]

/-- Repeated points remain refused, independently of which slot is swapped. -/
theorem repeated_points_have_no_parity (newToOld : Equiv.Perm (Fin 4)) :
    tetrahedralInputParityOfPoints?
        (permutedPoints origin xAxis yAxis origin newToOld) = none := by
  rw [tetrahedralInputParityOfPoints?_permutedPoints]
  have original : tetrahedralInputParityOfPoints? [origin, xAxis, yAxis, origin] =
      none := by
    norm_num [tetrahedralInputParityOfPoints?, CartesianPoint3.orientedVolume,
      origin, xAxis, yAxis]
  rw [original]
  rfl

end TetrahedralPointParityReindexRegression
end TetraStereo.OneCenter
