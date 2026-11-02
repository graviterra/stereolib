import TetraStereo.OneCenter.IR9TrigonalPrismSourceIndexCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.TrigonalPrismAbsoluteSymmetry

open FiniteSymmetry
open TrigonalPrismFiniteSymmetry

/-!
# Proper rotations and the two absolute classes of TPR-6

The full ideal-prism vertex group has twelve elements.  A coordinate frame consists of a
permutation of the two triangular faces and one common permutation of their three corners.  Such a
frame preserves spatial orientation exactly when the signs of those two permutations multiply to
`+1`: a face exchange reverses the prism axis, while an odd corner permutation reverses the
orientation of a triangular face.

This file derives the six-element proper subgroup from that criterion, proves that the full group
is its disjoint union with one mirror coset, and instantiates the generic exact-two-absolute-indices
theorem.  The final result applies to injective priority placements, exactly matching the
pairwise-distinct gate currently used before production emits a TPR-6 `A/C` suffix.
-/

theorem coordinatePermutation_mul
    (firstFace secondFace : Equiv.Perm (Fin 2))
    (firstCorner secondCorner : Equiv.Perm (Fin 3)) :
    coordinatePermutation firstFace firstCorner *
        coordinatePermutation secondFace secondCorner =
      coordinatePermutation (firstFace * secondFace) (firstCorner * secondCorner) := by
  apply Equiv.ext
  intro position
  apply coordinates.injective
  simp

theorem coordinatePermutation_inv
    (face : Equiv.Perm (Fin 2)) (corner : Equiv.Perm (Fin 3)) :
    (coordinatePermutation face corner)⁻¹ =
      coordinatePermutation face⁻¹ corner⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [coordinatePermutation_mul]
  apply Equiv.ext
  intro position
  apply coordinates.injective
  simp

/-- Orientation character of a face/corner coordinate frame. -/
def frameOrientationSign
    (face : Equiv.Perm (Fin 2)) (corner : Equiv.Perm (Fin 3)) : ℤˣ :=
  Equiv.Perm.sign face * Equiv.Perm.sign corner

/-- Proper TPR-6 vertex symmetries, derived from the coordinate-frame orientation character. -/
def properSymmetryGroup : SymmetryGroup Position where
  carrier := { symmetry |
    ∃ face : Equiv.Perm (Fin 2), ∃ corner : Equiv.Perm (Fin 3),
      symmetry = coordinatePermutation face corner ∧ frameOrientationSign face corner = 1 }
  one_mem' := by
    exact ⟨1, 1, by ext position; simp [coordinatePermutation], by simp [frameOrientationSign]⟩
  mul_mem' := by
    rintro first second ⟨firstFace, firstCorner, rfl, firstProper⟩
      ⟨secondFace, secondCorner, rfl, secondProper⟩
    refine ⟨firstFace * secondFace, firstCorner * secondCorner,
      coordinatePermutation_mul _ _ _ _, ?_⟩
    unfold frameOrientationSign at firstProper secondProper
    simp only [frameOrientationSign, Equiv.Perm.sign_mul]
    rw [mul_mul_mul_comm, firstProper, secondProper, one_mul]
  inv_mem' := by
    rintro symmetry ⟨face, corner, rfl, proper⟩
    refine ⟨face⁻¹, corner⁻¹, coordinatePermutation_inv face corner, ?_⟩
    simpa [frameOrientationSign, Equiv.Perm.sign_inv] using proper

/-- Coordinate frames satisfying the spatial-orientation criterion. -/
abbrev ProperCoordinateFrame :=
  { frame : CoordinateFrame // frameOrientationSign frame.1 frame.2 = 1 }

noncomputable def properFrameOfSymmetry
    (symmetry : properSymmetryGroup) : ProperCoordinateFrame := by
  let face := Classical.choose symmetry.2
  let faceCertificate := Classical.choose_spec symmetry.2
  let corner := Classical.choose faceCertificate
  let certificate := Classical.choose_spec faceCertificate
  exact ⟨(face, corner), certificate.2⟩

theorem coordinatePermutation_properFrameOfSymmetry
    (symmetry : properSymmetryGroup) :
    coordinatePermutation (properFrameOfSymmetry symmetry).1.1
        (properFrameOfSymmetry symmetry).1.2 = symmetry.1 := by
  unfold properFrameOfSymmetry
  exact (Classical.choose_spec (Classical.choose_spec symmetry.2)).1.symm

/-- Proper coordinate frames and proper vertex symmetries are in exact bijection. -/
noncomputable def properCoordinateFrameEquiv :
    ProperCoordinateFrame ≃ properSymmetryGroup where
  toFun frame :=
    ⟨coordinatePermutation frame.1.1 frame.1.2,
      ⟨frame.1.1, frame.1.2, rfl, frame.2⟩⟩
  invFun := properFrameOfSymmetry
  left_inv := by
    intro frame
    apply Subtype.ext
    apply coordinatePermutation_injective
    change coordinatePermutation (properFrameOfSymmetry
        ⟨coordinatePermutation frame.1.1 frame.1.2,
          ⟨frame.1.1, frame.1.2, rfl, frame.2⟩⟩).1.1
          (properFrameOfSymmetry
            ⟨coordinatePermutation frame.1.1 frame.1.2,
              ⟨frame.1.1, frame.1.2, rfl, frame.2⟩⟩).1.2 =
        coordinatePermutation frame.1.1 frame.1.2
    exact coordinatePermutation_properFrameOfSymmetry _
  right_inv := by
    intro symmetry
    apply Subtype.ext
    exact coordinatePermutation_properFrameOfSymmetry symmetry

noncomputable instance properSymmetryGroupFintype : Fintype properSymmetryGroup :=
  Fintype.ofEquiv ProperCoordinateFrame properCoordinateFrameEquiv

/-- Exactly half of the twelve full prism symmetries preserve spatial orientation. -/
theorem card_properSymmetryGroup : Fintype.card properSymmetryGroup = 6 := by
  rw [← Fintype.card_congr properCoordinateFrameEquiv]
  decide

/-- The chosen vertical reflection is an improper full symmetry. -/
theorem verticalReflection_not_mem_properSymmetryGroup :
    verticalReflection ∉ properSymmetryGroup := by
  rintro ⟨face, corner, same, proper⟩
  have sameFrame : (face, corner) = (1, Equiv.swap 1 2) := by
    apply coordinatePermutation_injective
    simpa [verticalReflection] using same.symm
  cases sameFrame
  simp [frameOrientationSign] at proper

/-- Every full prism symmetry is either proper or the chosen mirror followed by a proper
rotation.  This is the required two-coset decomposition, proved over the exhaustive derived group. -/
theorem fullSymmetryGroup_proper_or_mirror_coset :
    ∀ symmetry : fullSymmetryGroup,
      symmetry.1 ∈ properSymmetryGroup ∨
        ∃ rotation : properSymmetryGroup,
          symmetry.1 = verticalReflection * rotation.1 := by
  intro symmetry
  rcases (mem_fullSymmetryGroup_iff_exists_coordinatePermutation symmetry.1).mp symmetry.2 with
    ⟨face, corner, same⟩
  by_cases proper : frameOrientationSign face corner = 1
  · exact Or.inl ⟨face, corner, same, proper⟩
  · right
    have improper : frameOrientationSign face corner = -1 :=
      (Int.units_eq_one_or (frameOrientationSign face corner)).resolve_left proper
    let reflection : Equiv.Perm (Fin 3) := Equiv.swap 1 2
    have reflectionSign : Equiv.Perm.sign reflection = -1 := by
      simp [reflection]
    have rotationProper : frameOrientationSign face (reflection * corner) = 1 := by
      unfold frameOrientationSign at improper ⊢
      rw [Equiv.Perm.sign_mul]
      calc
        Equiv.Perm.sign face * (Equiv.Perm.sign reflection * Equiv.Perm.sign corner) =
            Equiv.Perm.sign reflection *
              (Equiv.Perm.sign face * Equiv.Perm.sign corner) := by ac_rfl
        _ = (-1) * (-1) := by rw [reflectionSign, improper]
        _ = 1 := by decide
    let rotation : properSymmetryGroup :=
      ⟨coordinatePermutation face (reflection * corner),
        ⟨face, reflection * corner, rfl, rotationProper⟩⟩
    refine ⟨rotation, ?_⟩
    rw [same]
    change coordinatePermutation face corner =
      coordinatePermutation 1 reflection *
        coordinatePermutation face (reflection * corner)
    rw [coordinatePermutation_mul]
    simp [reflection]

/-- With six distinct priority labels, a TPR-6 placement cannot be superimposed on its mirror by a
proper rotation. -/
theorem injectivePlacement_not_properEquivalent_to_mirror
    {Label : Type*} (placement : Position → Label)
    (injective : Function.Injective placement) :
    ¬SymmetryEquivalent properSymmetryGroup placement
      (relabel verticalReflection placement) := by
  rintro ⟨rotation, samePlacement⟩
  have samePermutation : verticalReflection = rotation.1 := by
    apply Equiv.ext
    intro position
    apply injective
    exact congrFun samePlacement position
  exact verticalReflection_not_mem_properSymmetryGroup
    (samePermutation ▸ rotation.2)

/-- **Exact absolute TPR-6 theorem.**

Every full relative orbit of an injectively priority-labelled trigonal prism contains exactly two
proper-rotation canonical indices: one for the placement and one for its mirror. -/
theorem injectivePlacement_has_exactlyTwoAbsoluteIndices
    (placement : Position → BlueBookP93.PriorityNumber)
    (injective : Function.Injective placement) :
    ExactTwoAbsoluteIndices fullSymmetryGroup properSymmetryGroup verticalReflection
      (fun position => priorityDigit (placement position)) := by
  let encodedPlacement := fun position => priorityDigit (placement position)
  have encodedInjective : Function.Injective encodedPlacement :=
    priorityDigit_injective.comp injective
  exact chiralRelativeOrbit_has_exactlyTwoAbsoluteIndices
    fullSymmetryGroup properSymmetryGroup verticalReflection
    verticalReflection_mem_fullSymmetryGroup
    fullSymmetryGroup_proper_or_mirror_coset encodedPlacement
    (injectivePlacement_not_properEquivalent_to_mirror encodedPlacement encodedInjective)

/-- Reversing the observed progression reverses the independent IR-9 `A/C` symbol. -/
def oppositeRotationSense : BlueBookP93.RotationSense → BlueBookP93.RotationSense
  | .clockwise => .counterclockwise
  | .counterclockwise => .clockwise

theorem chiralitySymbol_oppositeRotationSense
    (sense : BlueBookP93.RotationSense) :
    BlueBookP93.chiralitySymbol (oppositeRotationSense sense) =
      match BlueBookP93.chiralitySymbol sense with
      | .A => .C
      | .C => .A := by
  cases sense <;> rfl

end TetraStereo.OneCenter.RedBookIR9.TrigonalPrismAbsoluteSymmetry
