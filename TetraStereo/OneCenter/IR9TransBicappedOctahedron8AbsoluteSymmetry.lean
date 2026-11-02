import TetraStereo.OneCenter.IR9TransBicappedOctahedron8SourceIndexCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.TransBicappedOctahedron8AbsoluteSymmetry

open FiniteSymmetry
open TransBicappedOctahedron8SourceIndexCompleteness

/-!
# Proper and mirror classes of the exact ideal OCT-8 geometry

The side exchange of the two opposite capped faces is spatial inversion and has negative
determinant.  Permuting the three octahedral antipodal-pair axes has its ordinary permutation
sign.  Their product is therefore the exact orientation character of the twelve structural
frames.  Its kernel has six proper rotations, and the remaining six frames form one fixed-mirror
coset.

This yields exactly two mathematical proper-orbit classes for every injectively labelled
relative OCT-8 orbit.  They are not assigned `A` or `C`, because the source module proves that no
OCT-8-specific absolute-orientation route exists in the transcribed IR-9 vocabulary.
-/

def frameOrientationSign (frame : CoordinateFrame) : ℤˣ :=
  Equiv.Perm.sign frame.1 * Equiv.Perm.sign frame.2

@[simp] theorem frameOrientationSign_one :
    frameOrientationSign (1 : CoordinateFrame) = 1 := by
  simp [frameOrientationSign]

theorem frameOrientationSign_mul (first second : CoordinateFrame) :
    frameOrientationSign (first * second) =
      frameOrientationSign first * frameOrientationSign second := by
  rcases first with ⟨firstSide, firstPair⟩
  rcases second with ⟨secondSide, secondPair⟩
  unfold frameOrientationSign
  change Equiv.Perm.sign (firstSide * secondSide) *
      Equiv.Perm.sign (firstPair * secondPair) =
    (Equiv.Perm.sign firstSide * Equiv.Perm.sign firstPair) *
      (Equiv.Perm.sign secondSide * Equiv.Perm.sign secondPair)
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul]
  ac_rfl

theorem frameOrientationSign_inv (frame : CoordinateFrame) :
    frameOrientationSign frame⁻¹ = frameOrientationSign frame := by
  rcases frame with ⟨side, pair⟩
  simp [frameOrientationSign, Equiv.Perm.sign_inv]

def properSymmetryGroup : SymmetryGroup Position where
  carrier := { symmetry |
    ∃ frame : CoordinateFrame,
      symmetry = coordinatePermutation frame.1 frame.2 ∧
        frameOrientationSign frame = 1 }
  one_mem' := ⟨1, coordinatePermutation_one.symm, frameOrientationSign_one⟩
  mul_mem' := by
    rintro first second ⟨firstFrame, rfl, firstProper⟩
      ⟨secondFrame, rfl, secondProper⟩
    refine ⟨firstFrame * secondFrame,
      coordinatePermutation_mul firstFrame.1 secondFrame.1
        firstFrame.2 secondFrame.2, ?_⟩
    rw [frameOrientationSign_mul, firstProper, secondProper, one_mul]
  inv_mem' := by
    rintro symmetry ⟨frame, rfl, proper⟩
    refine ⟨frame⁻¹, coordinatePermutation_inv frame.1 frame.2, ?_⟩
    simpa [frameOrientationSign_inv] using proper

private instance properSymmetryGroupMembershipDecidable :
    DecidablePred (fun symmetry : Equiv.Perm Position => symmetry ∈ properSymmetryGroup) := by
  intro symmetry
  change Decidable (∃ frame : CoordinateFrame,
    symmetry = coordinatePermutation frame.1 frame.2 ∧
      frameOrientationSign frame = 1)
  infer_instance

abbrev ProperFrame := { frame : CoordinateFrame // frameOrientationSign frame = 1 }

def properFrameSymmetry (frame : ProperFrame) : properSymmetryGroup :=
  ⟨coordinatePermutation frame.1.1 frame.1.2, frame.1, rfl, frame.2⟩

theorem properFrameSymmetry_injective : Function.Injective properFrameSymmetry := by
  intro left right same
  apply Subtype.ext
  apply coordinatePermutation_injective
  exact congrArg Subtype.val same

theorem properFrameSymmetry_surjective : Function.Surjective properFrameSymmetry := by
  intro symmetry
  rcases symmetry.2 with ⟨frame, same, proper⟩
  refine ⟨⟨frame, proper⟩, ?_⟩
  apply Subtype.ext
  exact same.symm

noncomputable def properFrameEquiv : ProperFrame ≃ properSymmetryGroup :=
  Equiv.ofBijective properFrameSymmetry
    ⟨properFrameSymmetry_injective, properFrameSymmetry_surjective⟩

noncomputable instance (priority := 2000) properSymmetryGroupFintype :
    Fintype properSymmetryGroup :=
  Fintype.ofEquiv ProperFrame properFrameEquiv

theorem card_properSymmetryGroup : Fintype.card properSymmetryGroup = 6 := by
  rw [← Fintype.card_congr properFrameEquiv]
  decide

def sideReflection : Equiv.Perm (Fin 2) := Equiv.swap 0 1

def mirrorFrame : CoordinateFrame := (sideReflection, 1)

def mirror : Equiv.Perm Position :=
  coordinatePermutation mirrorFrame.1 mirrorFrame.2

theorem mirror_mem_fullSymmetryGroup : mirror ∈ fullSymmetryGroup :=
  ⟨mirrorFrame.1, mirrorFrame.2, rfl⟩

@[simp] theorem frameOrientationSign_mirrorFrame :
    frameOrientationSign mirrorFrame = -1 := by
  decide

theorem mirrorFrame_mul_self : mirrorFrame * mirrorFrame = 1 := by
  apply Prod.ext <;> decide

theorem mirror_mul_self : mirror * mirror = 1 := by
  rw [mirror, coordinatePermutation_mul]
  have frameSame := mirrorFrame_mul_self
  change coordinatePermutation (mirrorFrame * mirrorFrame).1
      (mirrorFrame * mirrorFrame).2 = 1
  rw [frameSame]
  exact coordinatePermutation_one

theorem mirror_not_mem_properSymmetryGroup : mirror ∉ properSymmetryGroup := by
  rintro ⟨frame, same, proper⟩
  have frameSame : frame = mirrorFrame := by
    apply coordinatePermutation_injective
    exact same.symm
  subst frame
  have impossible : (-1 : ℤˣ) = 1 := by
    simp at proper
  exact (by decide : (-1 : ℤˣ) ≠ 1) impossible

theorem fullSymmetryGroup_proper_or_mirror_coset :
    ∀ symmetry : fullSymmetryGroup,
      symmetry.1 ∈ properSymmetryGroup ∨
        ∃ rotation : properSymmetryGroup,
          symmetry.1 = mirror * rotation.1 := by
  intro symmetry
  rcases symmetry.2 with ⟨side, pair, same⟩
  let frame : CoordinateFrame := (side, pair)
  by_cases proper : frameOrientationSign frame = 1
  · exact Or.inl ⟨frame, same, proper⟩
  · right
    have improper : frameOrientationSign frame = -1 :=
      (Int.units_eq_one_or (frameOrientationSign frame)).resolve_left proper
    let rotationFrame : CoordinateFrame := mirrorFrame * frame
    have rotationProper : frameOrientationSign rotationFrame = 1 := by
      unfold rotationFrame
      rw [frameOrientationSign_mul, frameOrientationSign_mirrorFrame, improper]
      decide
    let rotation : properSymmetryGroup :=
      ⟨coordinatePermutation rotationFrame.1 rotationFrame.2,
        rotationFrame, rfl, rotationProper⟩
    refine ⟨rotation, ?_⟩
    rw [same]
    change coordinatePermutation frame.1 frame.2 =
      coordinatePermutation mirrorFrame.1 mirrorFrame.2 *
        coordinatePermutation rotationFrame.1 rotationFrame.2
    rw [coordinatePermutation_mul]
    have frameEquation : mirrorFrame * rotationFrame = frame := by
      unfold rotationFrame
      rw [← mul_assoc, mirrorFrame_mul_self, one_mul]
    exact (congrArg (fun current : CoordinateFrame =>
      coordinatePermutation current.1 current.2) frameEquation).symm

theorem injectivePlacement_not_properEquivalent_to_mirror
    {Label : Type*} (placement : Position → Label)
    (injective : Function.Injective placement) :
    ¬SymmetryEquivalent properSymmetryGroup placement (relabel mirror placement) := by
  rintro ⟨rotation, samePlacement⟩
  have samePermutation : mirror = rotation.1 := by
    apply Equiv.ext
    intro position
    apply injective
    exact congrFun samePlacement position
  exact mirror_not_mem_properSymmetryGroup (samePermutation ▸ rotation.2)

theorem injectivePlacement_has_exactlyTwoAbsoluteIndices
    (placement : Position → BlueBookP93.PriorityNumber)
    (injective : Function.Injective placement) :
    ExactTwoAbsoluteIndices fullSymmetryGroup properSymmetryGroup mirror
      (fun position => priorityDigit (placement position)) := by
  let encodedPlacement := fun position => priorityDigit (placement position)
  have encodedInjective : Function.Injective encodedPlacement :=
    priorityDigit_injective.comp injective
  exact chiralRelativeOrbit_has_exactlyTwoAbsoluteIndices
    fullSymmetryGroup properSymmetryGroup mirror mirror_mem_fullSymmetryGroup
    fullSymmetryGroup_proper_or_mirror_coset encodedPlacement
    (injectivePlacement_not_properEquivalent_to_mirror
      encodedPlacement encodedInjective)

end TetraStereo.OneCenter.RedBookIR9.TransBicappedOctahedron8AbsoluteSymmetry
