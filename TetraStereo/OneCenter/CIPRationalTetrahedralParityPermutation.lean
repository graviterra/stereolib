import TetraStereo.OneCenter.AuthoritativeSemanticMancudeMoleculeRule3Through6Analysis
import TetraStereo.OneCenter.Rule6HandednessCore

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace RationalTetrahedralPermutation

/-!
# Exact determinant semantics of the production tetrahedral permutation algebra

The production Rule-6 boundary combines the written-order `@`/`@@` parity with the inversion
parity of a four-position priority ordering.  This module proves that this Boolean algebra is
exactly the sign change of the rational affine determinant after applying the same ordering.

The written-order parity is calibrated against the standard right-handed Cartesian frame
(`x` right, `y` up, `z` toward the viewer): with the fourth position remote, a negative
priority-ordered determinant (equivalently a negative written-order determinant when the written
and priority orders agree) is `clockwise` and `R`; a positive determinant is `anticlockwise` and
`S`.  The determinant and affine-volume algebra below is unchanged; only the sign classification
of the written-order carriers follows that calibration.

The only finite step is ordinary kernel-checked case analysis over the twenty-four elements of
`S₄`; the point coordinates remain arbitrary rational variables in every branch.
-/

open RawMolecule
open Rule6HandednessSemantics

/-- The four exact points as a `Fin 4`-indexed vector. -/
def pointVector (first second third fourth : CartesianPoint3) :
    Fin 4 → CartesianPoint3 :=
  ![first, second, third, fourth]

/-- Exact rational determinant after a group-theoretic reordering of the four points. -/
def permutedOrientedVolume (first second third fourth : CartesianPoint3)
    (ordering : Equiv.Perm (Fin 4)) : ℚ :=
  CartesianPoint3.orientedVolume
    (pointVector first second third fourth (ordering 0))
    (pointVector first second third fourth (ordering 1))
    (pointVector first second third fourth (ordering 2))
    (pointVector first second third fourth (ordering 3))

private theorem toRealPoint_pointVector
    (first second third fourth : CartesianPoint3) (position : Fin 4) :
    (pointVector first second third fourth position).toRealPoint =
      (CartesianPoint3.toRealTetrahedralGeometry
        first second third fourth).vertex position := by
  fin_cases position <;> rfl

private theorem toRealTetrahedralGeometry_permuted
    (first second third fourth : CartesianPoint3)
    (ordering : Equiv.Perm (Fin 4)) :
    CartesianPoint3.toRealTetrahedralGeometry
        (pointVector first second third fourth (ordering 0))
        (pointVector first second third fourth (ordering 1))
        (pointVector first second third fourth (ordering 2))
        (pointVector first second third fourth (ordering 3)) =
      TetrahedralGeometry.reindex
        (CartesianPoint3.toRealTetrahedralGeometry first second third fourth)
        ordering := by
  apply TetrahedralGeometry.ext
  intro position
  fin_cases position <;>
    simp [CartesianPoint3.toRealTetrahedralGeometry, TetrahedralGeometry.reindex,
      toRealPoint_pointVector]

private theorem cast_permutedOrientedVolume
    (first second third fourth : CartesianPoint3)
    (ordering : Equiv.Perm (Fin 4)) :
    (permutedOrientedVolume first second third fourth ordering : ℝ) =
      permHandedness ordering *
        (CartesianPoint3.orientedVolume first second third fourth : ℝ) := by
  rw [← CartesianPoint3.orientedVolume_toRealTetrahedralGeometry]
  rw [← TetrahedralGeometry.orientedVolume_reindex]
  rw [← toRealTetrahedralGeometry_permuted]
  exact (CartesianPoint3.orientedVolume_toRealTetrahedralGeometry
    (pointVector first second third fourth (ordering 0))
    (pointVector first second third fourth (ordering 1))
    (pointVector first second third fourth (ordering 2))
    (pointVector first second third fourth (ordering 3))).symm

/-- A priority ordering preserves the exact determinant precisely when its inversion count is
even, and negates it precisely when that inversion count is odd. -/
theorem permutedOrientedVolume_eq_if_permutationIsEven
    (first second third fourth : CartesianPoint3)
    (ordering : Equiv.Perm (Fin 4)) :
    permutedOrientedVolume first second third fourth ordering =
      if RawMolecule.permutationIsEven (finFourPermutationList ordering) then
        CartesianPoint3.orientedVolume first second third fourth
      else
        -CartesianPoint3.orientedVolume first second third fourth := by
  by_cases even :
      RawMolecule.permutationIsEven (finFourPermutationList ordering) = true
  · have sign : Equiv.Perm.sign ordering = 1 := by
      have paritySign := finFourPermutationIsEven_eq_sign ordering
      rw [even] at paritySign
      simpa using paritySign
    simp only [if_pos even]
    apply Rat.cast_injective (α := ℝ)
    simpa [permHandedness, sign] using
      cast_permutedOrientedVolume first second third fourth ordering
  · have oddBoolean :
        RawMolecule.permutationIsEven (finFourPermutationList ordering) = false :=
      Bool.eq_false_of_not_eq_true even
    have sign : Equiv.Perm.sign ordering = -1 :=
      (finFourPermutationIsOdd_iff_sign_negOne ordering).mp oddBoolean
    simp only [if_neg even]
    apply Rat.cast_injective (α := ℝ)
    simpa [permHandedness, sign] using
      cast_permutedOrientedVolume first second third fourth ordering

/-- The exact point list obtained by applying a priority permutation to a written-order
tetrahedral frame. -/
def permutedPoints (first second third fourth : CartesianPoint3)
    (ordering : Equiv.Perm (Fin 4)) : List CartesianPoint3 :=
  [pointVector first second third fourth (ordering 0),
    pointVector first second third fourth (ordering 1),
    pointVector first second third fourth (ordering 2),
    pointVector first second third fourth (ordering 3)]

/-- Core geometry theorem: for arbitrary exact coordinates and any `S₄` priority ordering, the
production parity/inversion descriptor is precisely the determinant-sign descriptor of the
priority-ordered points, under the calibrated standard right-handed interpretation: a negative
priority-ordered determinant is `R` and a positive one is `S`. -/
theorem rationalTetrahedralDescriptor_permutedPoints
    (first second third fourth : CartesianPoint3)
    (ordering : Equiv.Perm (Fin 4)) (parity : TetrahedralInputParity)
    (inputParity :
      match parity with
      | .clockwise =>
          CartesianPoint3.orientedVolume first second third fourth < 0
      | .anticlockwise =>
          0 < CartesianPoint3.orientedVolume first second third fourth) :
    CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor
      (permutedPoints first second third fourth ordering)
      (RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven (finFourPermutationList ordering))) := by
  let even := RawMolecule.permutationIsEven (finFourPermutationList ordering)
  have volumeEq := permutedOrientedVolume_eq_if_permutationIsEven
    first second third fourth ordering
  cases parity with
  | clockwise =>
      by_cases isEven : even = true
      · refine ⟨pointVector first second third fourth (ordering 0),
          pointVector first second third fourth (ordering 1),
          pointVector first second third fourth (ordering 2),
          pointVector first second third fourth (ordering 3), rfl, ?_⟩
        simp only [RawMolecule.descriptorOfParity, even, isEven, if_true]
        change permutedOrientedVolume first second third fourth ordering < 0
        rw [volumeEq, if_pos isEven]
        exact inputParity
      · refine ⟨pointVector first second third fourth (ordering 0),
          pointVector first second third fourth (ordering 1),
          pointVector first second third fourth (ordering 2),
          pointVector first second third fourth (ordering 3), rfl, ?_⟩
        simp only [RawMolecule.descriptorOfParity, even, isEven]
        change 0 < permutedOrientedVolume first second third fourth ordering
        rw [volumeEq, if_neg isEven]
        exact neg_pos.mpr inputParity
  | anticlockwise =>
      by_cases isEven : even = true
      · refine ⟨pointVector first second third fourth (ordering 0),
          pointVector first second third fourth (ordering 1),
          pointVector first second third fourth (ordering 2),
          pointVector first second third fourth (ordering 3), rfl, ?_⟩
        simp only [RawMolecule.descriptorOfParity, even, isEven, if_true]
        change 0 < permutedOrientedVolume first second third fourth ordering
        rw [volumeEq, if_pos isEven]
        exact inputParity
      · refine ⟨pointVector first second third fourth (ordering 0),
          pointVector first second third fourth (ordering 1),
          pointVector first second third fourth (ordering 2),
          pointVector first second third fourth (ordering 3), rfl, ?_⟩
        simp only [RawMolecule.descriptorOfParity, even, isEven]
        change permutedOrientedVolume first second third fourth ordering < 0
        rw [volumeEq, if_neg isEven]
        exact neg_neg_of_pos inputParity

/-- Declarative meaning of reordering an exact four-point list by one production permutation
list.  The group-theoretic witness makes bijectivity explicit and excludes duplicate, missing, or
out-of-range positions. -/
def FinFourPriorityReordering (points : List CartesianPoint3)
    (positions : List Nat) (reordered : List CartesianPoint3) : Prop :=
  ∃ first second third fourth ordering,
    points = [first, second, third, fourth] ∧
      positions = finFourPermutationList ordering ∧
      reordered = permutedPoints first second third fourth ordering

/-- List-level bridge used by production rankings: every genuine permutation list transforms
exact written-order parity into the determinant descriptor selected by the production
parity/inversion formula. -/
theorem rationalTetrahedralInputParity_priorityReordering
    (points : List CartesianPoint3) (positions : List Nat)
    (parity : TetrahedralInputParity)
    (inputParity : AuthoritativeChemicalInput.RationalTetrahedralInputParity points parity)
    (positionsPermutation : positions.Perm (List.range 4)) :
    ∃ reordered,
      FinFourPriorityReordering points positions reordered ∧
      CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor reordered
        (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven positions)) := by
  rcases inputParity with ⟨first, second, third, fourth, pointsEq, parityVolume⟩
  let ordering := finFourEquivOfPermutationList positions positionsPermutation
  have positionsEq : finFourPermutationList ordering = positions :=
    finFourPermutationList_equivOfPermutationList positions positionsPermutation
  refine ⟨permutedPoints first second third fourth ordering,
    ⟨first, second, third, fourth, ordering, pointsEq, positionsEq.symm, rfl⟩, ?_⟩
  rw [← positionsEq]
  exact rationalTetrahedralDescriptor_permutedPoints
    first second third fourth ordering parity parityVolume

end RationalTetrahedralPermutation
end TetraStereo.OneCenter
