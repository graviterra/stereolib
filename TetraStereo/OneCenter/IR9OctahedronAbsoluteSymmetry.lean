import TetraStereo.OneCenter.IR9OctahedronSourceIndexCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.OctahedronAbsoluteSymmetry

open FiniteSymmetry
open OctahedronSourceIndexCompleteness

/-!
# Proper rotations and absolute classes of the ideal octahedron

The source-level relative group contains all 48 antipode-preserving signed-axis permutations.
This file derives its spatial orientation character from the determinant of the images of the
positive coordinate axes, defines the 24 proper rotations, proves the full group is the disjoint
union of the proper subgroup and one fixed mirror coset, and instantiates the generic exact-two-
absolute-indices theorem for distinct priorities.
-/

/-- Exact integral coordinate vector of an ideal octahedral vertex. -/
def coordinateVector : Position → Fin 3 → ℤ
  | .xPlus => fun axis => if axis = 0 then 1 else 0
  | .xMinus => fun axis => if axis = 0 then -1 else 0
  | .yPlus => fun axis => if axis = 1 then 1 else 0
  | .yMinus => fun axis => if axis = 1 then -1 else 0
  | .zPlus => fun axis => if axis = 2 then 1 else 0
  | .zMinus => fun axis => if axis = 2 then -1 else 0

/-- Determinant of three column vectors in exact `ℤ³` coordinates. -/
def determinant3 (first second third : Fin 3 → ℤ) : ℤ :=
  first 0 * (second 1 * third 2 - second 2 * third 1) -
    second 0 * (first 1 * third 2 - first 2 * third 1) +
      third 0 * (first 1 * second 2 - first 2 * second 1)

/-- Spatial orientation of an arbitrary vertex permutation, measured on the positive coordinate
frame.  For every full octahedral symmetry the determinant is `±1`; the total definition returns
the improper sign for any non-`+1` determinant. -/
def orientationSign (symmetry : Equiv.Perm Position) : ℤˣ :=
  if determinant3
      (coordinateVector (symmetry .xPlus))
      (coordinateVector (symmetry .yPlus))
      (coordinateVector (symmetry .zPlus)) = 1 then 1 else -1

@[simp] theorem orientationSign_one : orientationSign (1 : Equiv.Perm Position) = 1 := by
  decide

private instance fullSymmetryGroupMembershipDecidable :
    DecidablePred (fun symmetry : Equiv.Perm Position =>
      symmetry ∈ fullSymmetryGroup) := by
  intro symmetry
  change Decidable (∀ position,
    symmetry (opposite position) = opposite (symmetry position))
  infer_instance

/-- Exhaustive determinant multiplication over the independently derived 48-element full group.
The proof uses ordinary kernel `decide`; no native/compiler evaluation is involved. -/
theorem orientationSign_mul_full :
    ∀ first second : fullSymmetryGroup,
      orientationSign (first.1 * second.1) =
        orientationSign first.1 * orientationSign second.1 := by
  set_option maxHeartbeats 1000000 in
    set_option maxRecDepth 10000 in
      decide

/-- Proper ideal-octahedral rotations are exactly the full symmetries of positive determinant. -/
def properSymmetryGroup : SymmetryGroup Position where
  carrier := { symmetry |
    symmetry ∈ fullSymmetryGroup ∧ orientationSign symmetry = 1 }
  one_mem' := ⟨fullSymmetryGroup.one_mem, orientationSign_one⟩
  mul_mem' := by
    intro first second firstMember secondMember
    refine ⟨fullSymmetryGroup.mul_mem firstMember.1 secondMember.1, ?_⟩
    rw [orientationSign_mul_full ⟨first, firstMember.1⟩ ⟨second, secondMember.1⟩,
      firstMember.2, secondMember.2, one_mul]
  inv_mem' := by
    intro symmetry member
    refine ⟨fullSymmetryGroup.inv_mem member.1, ?_⟩
    have multiplied := orientationSign_mul_full
      (⟨symmetry⁻¹, fullSymmetryGroup.inv_mem member.1⟩ : fullSymmetryGroup)
      (⟨symmetry, member.1⟩ : fullSymmetryGroup)
    have equation : (1 : ℤˣ) = orientationSign symmetry⁻¹ * 1 := by
      simpa [member.2] using multiplied
    simpa using equation.symm

private instance properSymmetryGroupMembershipDecidable :
    DecidablePred (fun symmetry : Equiv.Perm Position =>
      symmetry ∈ properSymmetryGroup) := by
  intro symmetry
  change Decidable
    (symmetry ∈ fullSymmetryGroup ∧ orientationSign symmetry = 1)
  infer_instance

/-- Exactly half of the 48 full octahedral symmetries are proper rotations. -/
theorem card_properSymmetryGroup : Fintype.card properSymmetryGroup = 24 := by
  set_option maxHeartbeats 1000000 in
    set_option maxRecDepth 10000 in
      decide

/-- Fixed mirror obtained by exchanging the two vertices of the x axis. -/
def mirror : Equiv.Perm Position := Equiv.swap .xPlus .xMinus

theorem mirror_mem_fullSymmetryGroup : mirror ∈ fullSymmetryGroup := by
  decide

theorem orientationSign_mirror : orientationSign mirror = -1 := by
  decide

theorem mirror_not_mem_properSymmetryGroup : mirror ∉ properSymmetryGroup := by
  intro member
  have impossible : (-1 : ℤˣ) = 1 := by
    simpa [orientationSign_mirror] using member.2
  have negOneNeOne : (-1 : ℤˣ) ≠ 1 := by decide
  exact negOneNeOne impossible

/-- Every full octahedral symmetry is proper or lies in the fixed mirror coset. -/
theorem fullSymmetryGroup_proper_or_mirror_coset :
    ∀ symmetry : fullSymmetryGroup,
      symmetry.1 ∈ properSymmetryGroup ∨
        ∃ rotation : properSymmetryGroup,
          symmetry.1 = mirror * rotation.1 := by
  intro symmetry
  by_cases proper : orientationSign symmetry.1 = 1
  · exact Or.inl ⟨symmetry.2, proper⟩
  · right
    have improper : orientationSign symmetry.1 = -1 :=
      (Int.units_eq_one_or (orientationSign symmetry.1)).resolve_left proper
    let rotationPermutation := mirror * symmetry.1
    have rotationFull : rotationPermutation ∈ fullSymmetryGroup :=
      fullSymmetryGroup.mul_mem mirror_mem_fullSymmetryGroup symmetry.2
    have rotationProper : orientationSign rotationPermutation = 1 := by
      unfold rotationPermutation
      rw [orientationSign_mul_full
        (⟨mirror, mirror_mem_fullSymmetryGroup⟩ : fullSymmetryGroup) symmetry,
        orientationSign_mirror, improper]
      decide
    let rotation : properSymmetryGroup :=
      ⟨rotationPermutation, rotationFull, rotationProper⟩
    refine ⟨rotation, ?_⟩
    change symmetry.1 = mirror * (mirror * symmetry.1)
    simp [mirror]

/-- An injective priority placement is not properly superimposable on its mirror. -/
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

/-- Every relative orbit of an injectively priority-labelled OC-6 placement contains exactly two
proper-rotation canonical indices: the placement class and its mirror class. -/
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
    (injectivePlacement_not_properEquivalent_to_mirror encodedPlacement encodedInjective)

/-- Reversing the observed OC-6 progression exchanges the source A/C symbol. -/
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

end TetraStereo.OneCenter.RedBookIR9.OctahedronAbsoluteSymmetry
