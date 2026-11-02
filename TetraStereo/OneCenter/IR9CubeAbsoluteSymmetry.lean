import TetraStereo.OneCenter.IR9CubeSourceIndexCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.CubeAbsoluteSymmetry

open FiniteSymmetry
open CubeSourceIndexCompleteness

/-!
# Proper and mirror classes of the exact ideal cube

This file proves the orientation classification of the independently derived 48-element CU-8
vertex group.  The determinant character cuts it into 24 proper rotations and 24 improper
symmetries.  A fixed coordinate reflection represents the improper coset.  Consequently every
injectively priority-labelled relative cube class has exactly two proper-orbit classes.

These are mathematical absolute classes.  They are not called `A` or `C`: the transcribed Red Book
has no cube-specific reference-axis observation, as proved in `IR9CubeSourceIndexCompleteness`.
-/

/-- Exact integral coordinates of an ideal cube vertex. -/
def coordinateVector (position : Position) : Fin 3 → ℤ :=
  fun coordinate => if position coordinate then 1 else -1

/-- Determinant of three column vectors in exact `ℤ³` coordinates. -/
def determinant3 (first second third : Fin 3 → ℤ) : ℤ :=
  first 0 * (second 1 * third 2 - second 2 * third 1) -
    second 0 * (first 1 * third 2 - first 2 * third 1) +
      third 0 * (first 1 * second 2 - first 2 * second 1)

def corner (x y z : Bool) : Position
  | 0 => x
  | 1 => y
  | 2 => z

def originCorner : Position := corner false false false
def xNeighbor : Position := corner true false false
def yNeighbor : Position := corner false true false
def zNeighbor : Position := corner false false true

/-- Edge vector from the transported base corner to one transported adjacent corner. -/
def transportedEdgeVector (symmetry : Equiv.Perm Position) (neighbor : Position) : Fin 3 → ℤ :=
  fun coordinate =>
    coordinateVector (symmetry neighbor) coordinate -
      coordinateVector (symmetry originCorner) coordinate

/-- Exact affine orientation determinant.  The identity frame has determinant `8` because its
three edge vectors have length two in integral sign coordinates. -/
def orientationDeterminant (symmetry : Equiv.Perm Position) : ℤ :=
  determinant3
    (transportedEdgeVector symmetry xNeighbor)
    (transportedEdgeVector symmetry yNeighbor)
    (transportedEdgeVector symmetry zNeighbor)

/-- Orientation character of an arbitrary vertex permutation.  On the full ideal-cube symmetry
group, the determinant is exactly `8` or `-8`; this total definition uses the improper sign for
permutations outside the positive case. -/
def orientationSign (symmetry : Equiv.Perm Position) : ℤˣ :=
  if orientationDeterminant symmetry = 8 then 1 else -1

@[simp] theorem orientationSign_one :
    orientationSign (1 : Equiv.Perm Position) = 1 := by
  decide

private instance fullSymmetryGroupMembershipDecidable :
    DecidablePred (fun symmetry : Equiv.Perm Position => symmetry ∈ fullSymmetryGroup) := by
  intro symmetry
  change Decidable (∃ flip : Position, ∃ axis : Equiv.Perm (Fin 3),
    symmetry = coordinatePermutation flip axis)
  infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 12000000 in
/-- Exhaustive kernel proof that the determinant sign is multiplicative on all 48 independently
derived full cube symmetries. -/
theorem orientationSign_mul_full :
    ∀ first second : fullSymmetryGroup,
      orientationSign (first.1 * second.1) =
        orientationSign first.1 * orientationSign second.1 := by
  decide

/-- Proper ideal-cube rotations are the full symmetries of positive determinant. -/
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
    DecidablePred (fun symmetry : Equiv.Perm Position => symmetry ∈ properSymmetryGroup) := by
  intro symmetry
  change Decidable
    (symmetry ∈ fullSymmetryGroup ∧ orientationSign symmetry = 1)
  infer_instance

abbrev ProperFrame :=
  { symmetry : fullSymmetryGroup // orientationSign symmetry.1 = 1 }

def properFrameSymmetry (frame : ProperFrame) : properSymmetryGroup :=
  ⟨frame.1.1, frame.1.2, frame.2⟩

theorem properFrameSymmetry_injective : Function.Injective properFrameSymmetry := by
  intro left right same
  apply Subtype.ext
  apply Subtype.ext
  change left.1.1 = right.1.1
  exact congrArg (fun member : properSymmetryGroup => member.1) same

theorem properFrameSymmetry_surjective : Function.Surjective properFrameSymmetry := by
  intro symmetry
  let full : fullSymmetryGroup := ⟨symmetry.1, symmetry.2.1⟩
  refine ⟨(⟨full, symmetry.2.2⟩ : ProperFrame), ?_⟩
  rfl

noncomputable def properFrameEquiv : ProperFrame ≃ properSymmetryGroup :=
  Equiv.ofBijective properFrameSymmetry
    ⟨properFrameSymmetry_injective, properFrameSymmetry_surjective⟩

/-- Enumerate the proper subgroup by filtering the structural 48-frame group, not the ambient
`8!` vertex permutations. -/
noncomputable instance (priority := 2000) properSymmetryGroupFintype :
    Fintype properSymmetryGroup :=
  Fintype.ofEquiv ProperFrame properFrameEquiv

/-- Exactly half of the 48 full cube symmetries are proper rotations. -/
theorem card_properSymmetryGroup : Fintype.card properSymmetryGroup = 24 := by
  rw [← Fintype.card_congr properFrameEquiv]
  decide

/-- Reflection through the plane perpendicular to the first coordinate axis. -/
def reflectFirstCoordinate (position : Position) : Position :=
  fun coordinate => if coordinate = 0 then !(position coordinate) else position coordinate

theorem reflectFirstCoordinate_involutive : Function.Involutive reflectFirstCoordinate := by
  intro position
  funext coordinate
  by_cases first : coordinate = 0
  · simp [reflectFirstCoordinate, first]
  · simp [reflectFirstCoordinate, first]

def mirror : Equiv.Perm Position where
  toFun := reflectFirstCoordinate
  invFun := reflectFirstCoordinate
  left_inv := reflectFirstCoordinate_involutive
  right_inv := reflectFirstCoordinate_involutive

def firstCoordinateFlip : Position :=
  fun coordinate => decide (coordinate = 0)

theorem mirror_eq_coordinatePermutation :
    mirror = coordinatePermutation firstCoordinateFlip 1 := by
  apply Equiv.ext
  intro position
  funext coordinate
  by_cases first : coordinate = 0
  · simp [mirror, reflectFirstCoordinate, firstCoordinateFlip, coordinatePermutation,
      flipPermutation, axisPermutation, first]
  · simp [mirror, reflectFirstCoordinate, firstCoordinateFlip, coordinatePermutation,
      flipPermutation, axisPermutation, first]

theorem mirror_mem_fullSymmetryGroup : mirror ∈ fullSymmetryGroup := by
  exact ⟨firstCoordinateFlip, 1, mirror_eq_coordinatePermutation⟩

theorem orientationSign_mirror : orientationSign mirror = -1 := by
  decide

theorem mirror_not_mem_properSymmetryGroup : mirror ∉ properSymmetryGroup := by
  intro member
  have impossible : (-1 : ℤˣ) = 1 := by
    simpa [orientationSign_mirror] using member.2
  have negOneNeOne : (-1 : ℤˣ) ≠ 1 := by decide
  exact negOneNeOne impossible

/-- Every full cube symmetry is proper or is a fixed mirror followed by a proper rotation. -/
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
    have mirrorSquared : mirror * mirror = 1 := by
      apply Equiv.ext
      intro position
      change reflectFirstCoordinate (reflectFirstCoordinate position) = position
      exact reflectFirstCoordinate_involutive position
    rw [← mul_assoc, mirrorSquared, one_mul]

/-- An injective placement cannot be properly superimposed on its reflected cube. -/
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

/-- Every relative orbit of an injectively priority-labelled ideal CU-8 placement contains
exactly two proper-rotation canonical classes: the placement class and its mirror class. -/
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

end TetraStereo.OneCenter.RedBookIR9.CubeAbsoluteSymmetry
