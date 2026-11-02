import TetraStereo.OneCenter.IR9SimpleGeometrySourceIndexCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.SimpleGeometryAbsoluteSymmetry

open FiniteSymmetry
open SimpleGeometrySourceIndexCompleteness

/-!
# Proper/mirror classes for SPY-4 and SS-4

SP-4 and T-3 do not receive A/C suffixes in the executable source transcription.  SPY-4 and SS-4
do.  This file derives their proper subgroups, exhaustive fixed-mirror cosets, and exact two
absolute classes for injective priority placements.
-/

namespace FourOpposite

open SimpleGeometrySourceIndexCompleteness.FourOpposite

def successor : Position → Position
  | .site0 => .site1
  | .site1 => .site2
  | .site2 => .site3
  | .site3 => .site0

theorem opposite_eq_successor_successor (position : Position) :
    opposite position = successor (successor position) := by
  cases position <;> rfl

def verticalReflection : Equiv.Perm Position where
  toFun
    | .site0 => .site0
    | .site1 => .site3
    | .site2 => .site2
    | .site3 => .site1
  invFun
    | .site0 => .site0
    | .site1 => .site3
    | .site2 => .site2
    | .site3 => .site1
  left_inv := by intro position; cases position <;> rfl
  right_inv := by intro position; cases position <;> rfl

theorem verticalReflection_mul_self :
    verticalReflection * verticalReflection = 1 := by
  decide

private instance fullSymmetryGroupMembershipDecidable :
    DecidablePred (fun symmetry : Equiv.Perm Position => symmetry ∈ fullSymmetryGroup) := by
  intro symmetry
  change Decidable (∀ position,
    symmetry (opposite position) = opposite (symmetry position))
  infer_instance

theorem verticalReflection_mem_fullSymmetryGroup :
    verticalReflection ∈ fullSymmetryGroup := by
  decide

/-- Proper square-pyramidal four-coordinate rotations preserve the positive base traversal. -/
def properSymmetryGroup : SymmetryGroup Position where
  carrier := { symmetry |
    ∀ position, symmetry (successor position) = successor (symmetry position) }
  one_mem' := by simp
  mul_mem' := by
    intro first second firstMember secondMember position
    change first (second (successor position)) = successor (first (second position))
    rw [secondMember, firstMember]
  inv_mem' := by
    intro symmetry member position
    have transported := member (symmetry⁻¹ position)
    apply symmetry.injective
    simpa using transported.symm

private instance properSymmetryGroupMembershipDecidable :
    DecidablePred (fun symmetry : Equiv.Perm Position => symmetry ∈ properSymmetryGroup) := by
  intro symmetry
  change Decidable (∀ position,
    symmetry (successor position) = successor (symmetry position))
  infer_instance

theorem properSymmetry_mem_fullSymmetryGroup
    {symmetry : Equiv.Perm Position} (proper : symmetry ∈ properSymmetryGroup) :
    symmetry ∈ fullSymmetryGroup := by
  intro position
  rw [opposite_eq_successor_successor, proper, proper]
  exact (opposite_eq_successor_successor (symmetry position)).symm

theorem card_properSymmetryGroup : Fintype.card properSymmetryGroup = 4 := by
  decide

theorem verticalReflection_not_mem_properSymmetryGroup :
    verticalReflection ∉ properSymmetryGroup := by
  decide

/-- Exhaustive D4 dichotomy, reduced by Lean's kernel over the four-vertex permutation type. -/
theorem fullSymmetry_proper_or_reflection_mul_proper :
    ∀ symmetry : Equiv.Perm Position,
      symmetry ∈ fullSymmetryGroup →
        symmetry ∈ properSymmetryGroup ∨
          verticalReflection * symmetry ∈ properSymmetryGroup := by
  decide

theorem fullSymmetryGroup_proper_or_mirror_coset :
    ∀ symmetry : fullSymmetryGroup,
      symmetry.1 ∈ properSymmetryGroup ∨
        ∃ rotation : properSymmetryGroup,
          symmetry.1 = verticalReflection * rotation.1 := by
  intro symmetry
  rcases fullSymmetry_proper_or_reflection_mul_proper symmetry.1 symmetry.2 with
    proper | reflectedProper
  · exact Or.inl proper
  · right
    let rotation : properSymmetryGroup :=
      ⟨verticalReflection * symmetry.1, reflectedProper⟩
    refine ⟨rotation, ?_⟩
    change symmetry.1 = verticalReflection * (verticalReflection * symmetry.1)
    rw [← mul_assoc, verticalReflection_mul_self, one_mul]

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

end FourOpposite

namespace SeeSaw

open SimpleGeometrySourceIndexCompleteness.SeeSaw

def halfTurn : Equiv.Perm Position where
  toFun
    | .wide0 => .wide1
    | .wide1 => .wide0
    | .narrow0 => .narrow1
    | .narrow1 => .narrow0
  invFun
    | .wide0 => .wide1
    | .wide1 => .wide0
    | .narrow0 => .narrow1
    | .narrow1 => .narrow0
  left_inv := by intro position; cases position <;> rfl
  right_inv := by intro position; cases position <;> rfl

def verticalReflection : Equiv.Perm Position where
  toFun
    | .wide0 => .wide1
    | .wide1 => .wide0
    | .narrow0 => .narrow0
    | .narrow1 => .narrow1
  invFun
    | .wide0 => .wide1
    | .wide1 => .wide0
    | .narrow0 => .narrow0
    | .narrow1 => .narrow1
  left_inv := by intro position; cases position <;> rfl
  right_inv := by intro position; cases position <;> rfl

theorem halfTurn_mul_self : halfTurn * halfTurn = 1 := by decide

theorem verticalReflection_mul_self :
    verticalReflection * verticalReflection = 1 := by decide

private instance isWideDecidable : DecidablePred IsWide := by
  intro position
  cases position <;> unfold IsWide <;> infer_instance

private instance fullSymmetryGroupMembershipDecidable :
    DecidablePred (fun symmetry : Equiv.Perm Position => symmetry ∈ fullSymmetryGroup) := by
  intro symmetry
  change Decidable (∀ position, IsWide (symmetry position) ↔ IsWide position)
  infer_instance

theorem verticalReflection_mem_fullSymmetryGroup :
    verticalReflection ∈ fullSymmetryGroup := by decide

/-- The proper see-saw subgroup consists of identity and simultaneous exchange of both geometric
pairs. -/
def properSymmetryGroup : SymmetryGroup Position where
  carrier := { symmetry | symmetry = 1 ∨ symmetry = halfTurn }
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro first second firstMember secondMember
    rcases firstMember with rfl | rfl <;> rcases secondMember with rfl | rfl
    · exact Or.inl (one_mul 1)
    · exact Or.inr (one_mul halfTurn)
    · exact Or.inr (mul_one halfTurn)
    · exact Or.inl halfTurn_mul_self
  inv_mem' := by
    intro symmetry member
    rcases member with rfl | rfl
    · exact Or.inl inv_one
    · right
      apply inv_eq_of_mul_eq_one_right
      exact halfTurn_mul_self

private instance properSymmetryGroupMembershipDecidable :
    DecidablePred (fun symmetry : Equiv.Perm Position => symmetry ∈ properSymmetryGroup) := by
  intro symmetry
  change Decidable (symmetry = 1 ∨ symmetry = halfTurn)
  infer_instance

theorem properSymmetry_mem_fullSymmetryGroup
    {symmetry : Equiv.Perm Position} (proper : symmetry ∈ properSymmetryGroup) :
    symmetry ∈ fullSymmetryGroup := by
  rcases proper with rfl | rfl
  · exact fullSymmetryGroup.one_mem
  · decide

theorem card_properSymmetryGroup : Fintype.card properSymmetryGroup = 2 := by
  decide

theorem verticalReflection_not_mem_properSymmetryGroup :
    verticalReflection ∉ properSymmetryGroup := by decide

/-- Exhaustive four-element full-group/two-element proper-group coset decomposition. -/
theorem fullSymmetryGroup_proper_or_mirror_coset :
    ∀ symmetry : fullSymmetryGroup,
      symmetry.1 ∈ properSymmetryGroup ∨
        ∃ rotation : properSymmetryGroup,
          symmetry.1 = verticalReflection * rotation.1 := by
  decide

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

end SeeSaw

/-- Reversing any accepted polyhedral progression exchanges the independent A/C symbol. -/
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

end TetraStereo.OneCenter.RedBookIR9.SimpleGeometryAbsoluteSymmetry
