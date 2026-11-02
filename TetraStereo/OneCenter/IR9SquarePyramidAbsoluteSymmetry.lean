import TetraStereo.OneCenter.IR9SquarePyramidSourceIndexCompleteness

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 2000

namespace TetraStereo.OneCenter.RedBookIR9.SquarePyramidAbsoluteSymmetry

open FiniteSymmetry
open SquarePyramidSourceIndexCompleteness

/-!
# Proper rotations and the two absolute classes of SPY-5

The proper subgroup consists of the four rotations of the square base.  A fixed vertical mirror
generates the other coset.  This supplies the exact two-class absolute theorem on the same
injective-priority domain used by the relative source-index theorem.
-/

/-- One positive quarter-turn of the square base. -/
def successor : Position → Position
  | .apex => .apex
  | .base0 => .base1
  | .base1 => .base2
  | .base2 => .base3
  | .base3 => .base0

@[simp] theorem successor_apex : successor .apex = .apex := rfl

theorem opposite_eq_successor_successor (position : Position) :
    opposite position = successor (successor position) := by
  cases position <;> rfl

/-- The mirror plane through `base0`, the apex, and `base2`. -/
def verticalReflection : Equiv.Perm Position where
  toFun
    | .apex => .apex
    | .base0 => .base0
    | .base1 => .base3
    | .base2 => .base2
    | .base3 => .base1
  invFun
    | .apex => .apex
    | .base0 => .base0
    | .base1 => .base3
    | .base2 => .base2
    | .base3 => .base1
  left_inv := by intro position; cases position <;> rfl
  right_inv := by intro position; cases position <;> rfl

@[simp] theorem verticalReflection_apex :
    verticalReflection .apex = .apex := rfl

theorem verticalReflection_squared : verticalReflection ^ 2 = 1 := by
  decide

theorem verticalReflection_mul_self :
    verticalReflection * verticalReflection = 1 := by
  decide

@[simp] theorem verticalReflection_mem_fullSymmetryGroup :
    verticalReflection ∈ fullSymmetryGroup := by
  decide

/-- Proper ideal SPY-5 symmetries are exactly the frames commuting with one positive quarter-turn. -/
def properSymmetryGroup : SymmetryGroup Position where
  carrier := { symmetry |
    symmetry .apex = .apex ∧
      ∀ position, symmetry (successor position) = successor (symmetry position) }
  one_mem' := by constructor <;> simp
  mul_mem' := by
    intro first second firstMember secondMember
    constructor
    · simp [firstMember.1, secondMember.1]
    · intro position
      change first (second (successor position)) = successor (first (second position))
      rw [secondMember.2, firstMember.2]
  inv_mem' := by
    intro symmetry member
    constructor
    · apply symmetry.injective
      simpa using member.1.symm
    · intro position
      have transported := member.2 (symmetry.symm position)
      apply symmetry.injective
      simpa using transported.symm

private instance properSymmetryGroupMembershipDecidable :
    DecidablePred (fun symmetry : Equiv.Perm Position => symmetry ∈ properSymmetryGroup) := by
  intro symmetry
  change Decidable (symmetry .apex = .apex ∧
    ∀ position, symmetry (successor position) = successor (symmetry position))
  infer_instance

/-- Every proper rotation is, independently, a member of the complete full symmetry group. -/
theorem properSymmetry_mem_fullSymmetryGroup
    {symmetry : Equiv.Perm Position} (proper : symmetry ∈ properSymmetryGroup) :
    symmetry ∈ fullSymmetryGroup := by
  rcases proper with ⟨fixesApex, preservesSuccessor⟩
  constructor
  · exact fixesApex
  · intro position
    rw [opposite_eq_successor_successor, preservesSuccessor, preservesSuccessor]
    exact (opposite_eq_successor_successor (symmetry position)).symm

theorem card_properSymmetryGroup : Fintype.card properSymmetryGroup = 4 := by
  decide

theorem verticalReflection_not_mem_properSymmetryGroup :
    verticalReflection ∉ properSymmetryGroup := by
  decide

/-- Finite D4 dichotomy: an admitted full frame either preserves the base traversal or becomes
traversal-preserving after the fixed reflection. -/
theorem fullSymmetry_proper_or_reflection_mul_proper
    (symmetry : Equiv.Perm Position) (member : symmetry ∈ fullSymmetryGroup) :
    symmetry ∈ properSymmetryGroup ∨
      verticalReflection * symmetry ∈ properSymmetryGroup := by
  by_cases proper : symmetry ∈ properSymmetryGroup
  · exact Or.inl proper
  · right
    have fixesApex : symmetry .apex = .apex := member.1
    have preservesOpposite : ∀ position,
        symmetry (opposite position) = opposite (symmetry position) := member.2
    have notPreservesSuccessor : ¬∀ position,
        symmetry (successor position) = successor (symmetry position) := by
      intro preserves
      exact proper ⟨fixesApex, preserves⟩
    push_neg at notPreservesSuccessor
    rcases notPreservesSuccessor with ⟨failurePosition, failure⟩
    have mapsOpposite0 := preservesOpposite Position.base0
    have mapsOpposite1 := preservesOpposite Position.base1
    simp only [opposite_base0, opposite_base1] at mapsOpposite0 mapsOpposite1
    clear preservesOpposite member proper
    change
      (verticalReflection * symmetry) .apex = .apex ∧
        ∀ position,
          (verticalReflection * symmetry) (successor position) =
            successor ((verticalReflection * symmetry) position)
    refine ⟨by simp [fixesApex], ?_⟩
    have imageApexBase0 : symmetry .apex ≠ symmetry .base0 :=
      symmetry.injective.ne (by decide)
    have imageApexBase1 : symmetry .apex ≠ symmetry .base1 :=
      symmetry.injective.ne (by decide)
    have imageBase01 : symmetry .base0 ≠ symmetry .base1 :=
      symmetry.injective.ne (by decide)
    intro position
    generalize image0Eq : symmetry .base0 = image0 at *
    generalize image1Eq : symmetry .base1 = image1 at *
    have images01 : image0 ≠ image1 := by simpa [image0Eq, image1Eq] using imageBase01
    have image1NeOppositeImage0 : image1 ≠ opposite image0 := by
      intro same
      have noCollision : symmetry .base1 ≠ symmetry .base2 :=
        symmetry.injective.ne (by decide)
      apply noCollision
      rw [image1Eq, mapsOpposite0, same]
    fin_cases image0 <;> try simp_all [opposite, successor, verticalReflection,
      Equiv.Perm.coe_mul]
    all_goals fin_cases image1 <;> try simp_all
    all_goals fin_cases failurePosition <;> try simp_all
    all_goals fin_cases position <;> simp_all

/-- The full D4 group is the disjoint union of proper rotations and one mirror coset. -/
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

/-- An injectively labelled SPY-5 cannot be superimposed on its mirror by a proper rotation. -/
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

/-- Every injectively priority-labelled SPY-5 relative orbit has exactly two proper-rotation
canonical indices, exchanged by the fixed mirror. -/
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

end TetraStereo.OneCenter.RedBookIR9.SquarePyramidAbsoluteSymmetry
