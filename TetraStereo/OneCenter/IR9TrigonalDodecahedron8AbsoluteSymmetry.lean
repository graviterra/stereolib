import TetraStereo.OneCenter.IR9TrigonalDodecahedron8SourceIndexCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.TrigonalDodecahedron8AbsoluteSymmetry

open FiniteSymmetry
open TrigonalDodecahedron8SourceIndexCompleteness

/-!
# Proper and mirror classes of the exact ideal DD-8 geometry

The full `D2d` action has eight frames.  In a four-slot dihedral presentation, even cyclic shifts
and odd-offset reflections are proper; odd shifts are the two improper fourfold roto-reflections,
and even-offset reflections are improper.  The resulting orientation character has a four-element
proper kernel and one fixed-mirror coset.

For injective ligand priorities this proves exactly two proper-orbit classes inside every full
relative orbit.  They are mathematical absolute classes only.  The source module proves that the
transcribed IR-9 vocabulary gives DD-8 no geometry-specific `A`/`C` reference-axis convention.
-/

def frameOrientationSign : CoordinateFrame → ℤˣ
  | .r offset => if offset.val % 2 = 0 then 1 else -1
  | .sr offset => if offset.val % 2 = 0 then -1 else 1

@[simp] theorem frameOrientationSign_one :
    frameOrientationSign (1 : CoordinateFrame) = 1 := by
  decide

theorem frameOrientationSign_mul :
    ∀ first second : CoordinateFrame,
      frameOrientationSign (first * second) =
        frameOrientationSign first * frameOrientationSign second := by
  decide

theorem frameOrientationSign_inv :
    ∀ frame : CoordinateFrame,
      frameOrientationSign frame⁻¹ = frameOrientationSign frame := by
  decide

def properSymmetryGroup : SymmetryGroup Position where
  carrier := { symmetry |
    ∃ frame : CoordinateFrame,
      symmetry = coordinatePermutation frame ∧ frameOrientationSign frame = 1 }
  one_mem' := ⟨1, coordinatePermutation_one.symm, frameOrientationSign_one⟩
  mul_mem' := by
    rintro first second ⟨firstFrame, rfl, firstProper⟩
      ⟨secondFrame, rfl, secondProper⟩
    refine ⟨firstFrame * secondFrame,
      coordinatePermutation_mul firstFrame secondFrame, ?_⟩
    rw [frameOrientationSign_mul, firstProper, secondProper, one_mul]
  inv_mem' := by
    rintro symmetry ⟨frame, rfl, proper⟩
    refine ⟨frame⁻¹, coordinatePermutation_inv frame, ?_⟩
    simpa [frameOrientationSign_inv] using proper

private instance properSymmetryGroupMembershipDecidable :
    DecidablePred (fun symmetry : Equiv.Perm Position => symmetry ∈ properSymmetryGroup) := by
  intro symmetry
  change Decidable (∃ frame : CoordinateFrame,
    symmetry = coordinatePermutation frame ∧ frameOrientationSign frame = 1)
  infer_instance

abbrev ProperFrame := { frame : CoordinateFrame // frameOrientationSign frame = 1 }

def properFrameSymmetry (frame : ProperFrame) : properSymmetryGroup :=
  ⟨coordinatePermutation frame.1, frame.1, rfl, frame.2⟩

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

theorem card_properSymmetryGroup : Fintype.card properSymmetryGroup = 4 := by
  rw [← Fintype.card_congr properFrameEquiv]
  decide

def mirrorFrame : CoordinateFrame := .sr 0

def mirror : Equiv.Perm Position := coordinatePermutation mirrorFrame

theorem mirror_mem_fullSymmetryGroup : mirror ∈ fullSymmetryGroup :=
  ⟨mirrorFrame, rfl⟩

@[simp] theorem frameOrientationSign_mirrorFrame :
    frameOrientationSign mirrorFrame = -1 := by
  decide

theorem mirrorFrame_mul_self : mirrorFrame * mirrorFrame = 1 := by
  decide

theorem mirror_mul_self : mirror * mirror = 1 := by
  rw [mirror, coordinatePermutation_mul, mirrorFrame_mul_self,
    coordinatePermutation_one]

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
  rcases symmetry.2 with ⟨frame, same⟩
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
      ⟨coordinatePermutation rotationFrame, rotationFrame, rfl, rotationProper⟩
    refine ⟨rotation, ?_⟩
    rw [same]
    change coordinatePermutation frame =
      coordinatePermutation mirrorFrame * coordinatePermutation rotationFrame
    rw [coordinatePermutation_mul]
    unfold rotationFrame
    rw [← mul_assoc, mirrorFrame_mul_self, one_mul]

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

end TetraStereo.OneCenter.RedBookIR9.TrigonalDodecahedron8AbsoluteSymmetry
