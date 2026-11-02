import TetraStereo.OneCenter.IR9SquareAntiprism8SourceIndexCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.SquareAntiprism8AbsoluteSymmetry

open FiniteSymmetry
open SquareAntiprism8SourceIndexCompleteness

/-!
# Proper and mirror classes of the exact ideal square antiprism

In the alternating-rim coordinates, advancing by one vertex combines a 45-degree axial rotation
with exchange of the two square-face planes and is therefore improper.  Advancing by two vertices
is a proper quarter-turn.  A rim reflection has the opposite orientation character.  The exact
character below formalizes these facts on all sixteen dihedral frames and proves that precisely
eight are proper.

Consequently every injectively priority-labelled SAPR-8 relative orbit contains exactly two
proper-rotation classes exchanged by a fixed mirror.  These are mathematical absolute classes,
not IUPAC `A`/`C` labels: the source-level module proves that the transcribed Red Book vocabulary
contains no SAPR-8-specific absolute-orientation convention.
-/

/-- Spatial orientation character of an alternating-rim frame.  For a rotation frame, odd rim
steps exchange the two face planes.  A reflection reverses the in-plane traversal as well. -/
def frameOrientationSign : CoordinateFrame → ℤˣ
  | .r offset => if offset.val % 2 = 0 then 1 else -1
  | .sr offset => if offset.val % 2 = 0 then -1 else 1

@[simp] theorem frameOrientationSign_one :
    frameOrientationSign (1 : CoordinateFrame) = 1 := by
  decide

/-- The orientation character is multiplicative on all sixteen frames. -/
theorem frameOrientationSign_mul :
    ∀ first second : CoordinateFrame,
      frameOrientationSign (first * second) =
        frameOrientationSign first * frameOrientationSign second := by
  decide

theorem frameOrientationSign_inv :
    ∀ frame : CoordinateFrame,
      frameOrientationSign frame⁻¹ = frameOrientationSign frame := by
  decide

/-- Proper SAPR-8 rotations are precisely the structurally admitted frames of positive spatial
orientation. -/
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

/-- Enumerate the eight proper frames, never the ambient vertex-permutation space. -/
noncomputable instance (priority := 2000) properSymmetryGroupFintype :
    Fintype properSymmetryGroup :=
  Fintype.ofEquiv ProperFrame properFrameEquiv

theorem card_properSymmetryGroup : Fintype.card properSymmetryGroup = 8 := by
  rw [← Fintype.card_congr properFrameEquiv]
  decide

/-- Reflection of the alternating rim through the reference axis. -/
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

/-- Every full SAPR-8 symmetry is proper or lies in the fixed mirror coset. -/
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

/-- An injective placement cannot be superimposed on its mirror by a proper SAPR-8 rotation. -/
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

/-- Every relative orbit of an injectively priority-labelled ideal SAPR-8 placement contains
exactly two proper-rotation canonical classes, exchanged by the fixed mirror. -/
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

end TetraStereo.OneCenter.RedBookIR9.SquareAntiprism8AbsoluteSymmetry
