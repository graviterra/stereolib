import TetraStereo.OneCenter.IR9BipyramidalSourceIndexCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.SimpleGeometrySourceIndexCompleteness

open FiniteSymmetry
open BipyramidalSourceIndexCompleteness

abbrev PriorityNumber := BlueBookP93.PriorityNumber

/-!
# Exact source indices for T-3, SP-4, SPY-4, and SS-4

These are the remaining compact configuration-index recipes currently accepted by the public
polyhedral router.  Each geometry is modeled independently of its compressed index.  At fixed
complete priority multiset, the literal source index is proved equal exactly under the complete
ideal vertex-symmetry group on the distinct-priority domain.
-/

section Matching

variable {Vertex : Type*} [Fintype Vertex] [DecidableEq Vertex]

/-- Canonical complete priority enumeration used only to state fixed molecular composition. -/
noncomputable def placementWord (placement : Vertex → PriorityNumber) : List PriorityNumber :=
  (Finset.univ.toList).map placement

noncomputable def SamePriorityMultiset (left right : Vertex → PriorityNumber) : Prop :=
  (placementWord left).Perm (placementWord right)

omit [DecidableEq Vertex] in
theorem mem_placementWord_iff_exists_position
    (placement : Vertex → PriorityNumber) (priority : PriorityNumber) :
    priority ∈ placementWord placement ↔
      ∃ position, placement position = priority := by
  simp [placementWord, eq_comm]

omit [DecidableEq Vertex] in
/-- Equal finite priority multisets and injectivity determine the unique relabeling permutation. -/
theorem matchingPermutation_of_samePriorityMultiset
    (left right : Vertex → PriorityNumber)
    (rightInjective : Function.Injective right)
    (sameMultiset : SamePriorityMultiset left right) :
    ∃ matching : Equiv.Perm Vertex, right = relabel matching left := by
  have rightOccursOnLeft : ∀ position, ∃ matched, left matched = right position := by
    intro position
    apply (mem_placementWord_iff_exists_position left (right position)).mp
    exact sameMultiset.mem_iff.mpr
      ((mem_placementWord_iff_exists_position right (right position)).mpr
        ⟨position, rfl⟩)
  let matchingFunction : Vertex → Vertex :=
    fun position => Classical.choose (rightOccursOnLeft position)
  have matchingProperty : ∀ position,
      left (matchingFunction position) = right position := by
    intro position
    exact Classical.choose_spec (rightOccursOnLeft position)
  have matchingInjective : Function.Injective matchingFunction := by
    intro first second same
    apply rightInjective
    rw [← matchingProperty first, ← matchingProperty second, same]
  have matchingBijective : Function.Bijective matchingFunction :=
    (Fintype.bijective_iff_injective_and_card matchingFunction).mpr
      ⟨matchingInjective, rfl⟩
  let matching : Equiv.Perm Vertex :=
    Equiv.ofBijective matchingFunction matchingBijective
  refine ⟨matching, ?_⟩
  funext position
  exact (matchingProperty position).symm

end Matching

/-! ## T-shaped three-coordinate geometry -/

namespace TShape

inductive Position where
  | stem
  | arm0
  | arm1
  deriving DecidableEq, Fintype, Repr

/-- The complete ideal T-shape group fixes the stem and may exchange the two transverse arms. -/
def fullSymmetryGroup : SymmetryGroup Position where
  carrier := { symmetry | symmetry .stem = .stem }
  one_mem' := rfl
  mul_mem' := by
    intro first second firstMember secondMember
    change first (second .stem) = .stem
    rw [secondMember, firstMember]
  inv_mem' := by
    intro symmetry member
    apply symmetry.injective
    simpa using member.symm

private instance fullSymmetryGroupMembershipDecidable :
    DecidablePred (fun symmetry : Equiv.Perm Position => symmetry ∈ fullSymmetryGroup) := by
  intro symmetry
  change Decidable (symmetry .stem = .stem)
  infer_instance

theorem card_fullSymmetryGroup : Fintype.card fullSymmetryGroup = 2 := by
  decide

def sourceIndex (placement : Position → PriorityNumber) : List PriorityNumber :=
  BlueBookP93.tShapeIndex (placement .stem)

def Equivalent (left right : Position → PriorityNumber) : Prop :=
  SymmetryEquivalent fullSymmetryGroup left right

theorem sourceIndex_eq_iff_symmetryEquivalent_of_samePriorityMultiset
    (left right : Position → PriorityNumber)
    (leftInjective : Function.Injective left)
    (rightInjective : Function.Injective right)
    (sameMultiset : SamePriorityMultiset left right) :
    sourceIndex left = sourceIndex right ↔ Equivalent left right := by
  constructor
  · intro sameIndex
    have stemSame : left .stem = right .stem := by
      simpa [sourceIndex, BlueBookP93.tShapeIndex] using sameIndex
    rcases matchingPermutation_of_samePriorityMultiset left right rightInjective sameMultiset with
      ⟨matching, samePlacement⟩
    have mapsStem : matching .stem = .stem := by
      apply leftInjective
      calc
        left (matching .stem) = right .stem := by
          simpa [relabel] using (congrFun samePlacement .stem).symm
        _ = left .stem := stemSame.symm
    exact ⟨⟨matching, mapsStem⟩, samePlacement⟩
  · rintro ⟨symmetry, samePlacement⟩
    have stemSame : right .stem = left .stem := by
      calc
        right .stem = left (symmetry.1 .stem) := by
          simpa [relabel] using congrFun samePlacement .stem
        _ = left .stem := by rw [symmetry.2]
    simp [sourceIndex, BlueBookP93.tShapeIndex, stemSame]

theorem blueBook_tShapeIndex_eq_iff_symmetryEquivalent
    (left right : Position → PriorityNumber)
    (leftInjective : Function.Injective left)
    (rightInjective : Function.Injective right)
    (sameMultiset : SamePriorityMultiset left right) :
    BlueBookP93.tShapeIndex (left .stem) =
        BlueBookP93.tShapeIndex (right .stem) ↔ Equivalent left right :=
  sourceIndex_eq_iff_symmetryEquivalent_of_samePriorityMultiset
    left right leftInjective rightInjective sameMultiset

end TShape

/-! ## Four vertices with square opposition: SP-4 and SPY-4 -/

namespace FourOpposite

inductive Position where
  | site0
  | site1
  | site2
  | site3
  deriving DecidableEq, Fintype, Repr

def opposite : Position → Position
  | .site0 => .site2
  | .site1 => .site3
  | .site2 => .site0
  | .site3 => .site1

@[simp] theorem opposite_opposite (position : Position) :
    opposite (opposite position) = position := by
  cases position <;> rfl

theorem opposite_ne (position : Position) : opposite position ≠ position := by
  cases position <;> decide

def PerpendicularTo (axial position : Position) : Prop :=
  position ≠ axial ∧ position ≠ opposite axial

@[simp] theorem perpendicular_opposite_iff (axial position : Position) :
    PerpendicularTo axial (opposite position) ↔ PerpendicularTo axial position := by
  cases axial <;> cases position <;> simp [PerpendicularTo, opposite]

theorem eq_opposite_of_both_perpendicular
    (axis first second : Position)
    (firstPerpendicular : PerpendicularTo axis first)
    (secondPerpendicular : PerpendicularTo axis second)
    (distinct : first ≠ second) :
    second = opposite first := by
  fin_cases axis <;> fin_cases first <;>
    simp [PerpendicularTo, opposite] at firstPerpendicular
  all_goals fin_cases second <;> simp_all [PerpendicularTo, opposite]

def fullSymmetryGroup : SymmetryGroup Position where
  carrier := { symmetry |
    ∀ position, symmetry (opposite position) = opposite (symmetry position) }
  one_mem' := by simp
  mul_mem' := by
    intro first second firstMember secondMember position
    change first (second (opposite position)) = opposite (first (second position))
    rw [secondMember, firstMember]
  inv_mem' := by
    intro symmetry member position
    have transported := member (symmetry⁻¹ position)
    apply symmetry.injective
    simpa using transported.symm

private instance fullSymmetryGroupMembershipDecidable :
    DecidablePred (fun symmetry : Equiv.Perm Position => symmetry ∈ fullSymmetryGroup) := by
  intro symmetry
  change Decidable (∀ position,
    symmetry (opposite position) = opposite (symmetry position))
  infer_instance

theorem card_fullSymmetryGroup : Fintype.card fullSymmetryGroup = 8 := by
  decide

theorem perpendicular_map_of_maps_opposite_pair
    (symmetry : Equiv.Perm Position) {sourceAxis targetAxis position : Position}
    (mapsAxis : symmetry sourceAxis = targetAxis)
    (mapsOpposite : symmetry (opposite sourceAxis) = opposite targetAxis)
    (perpendicular : PerpendicularTo sourceAxis position) :
    PerpendicularTo targetAxis (symmetry position) := by
  constructor
  · intro same
    apply perpendicular.1
    apply symmetry.injective
    simpa [mapsAxis] using same
  · intro same
    apply perpendicular.2
    apply symmetry.injective
    simpa [mapsOpposite] using same

theorem mem_fullSymmetryGroup_of_maps_opposite_pair
    (symmetry : Equiv.Perm Position) (source target : Position)
    (mapsSource : symmetry source = target)
    (mapsOpposite : symmetry (opposite source) = opposite target) :
    symmetry ∈ fullSymmetryGroup := by
  change ∀ position,
    symmetry (opposite position) = opposite (symmetry position)
  intro position
  by_cases atSource : position = source
  · subst position
    rw [mapsOpposite, mapsSource]
  by_cases atOpposite : position = opposite source
  · subst position
    simp [mapsSource, mapsOpposite]
  have positionPerpendicular : PerpendicularTo source position :=
    ⟨atSource, atOpposite⟩
  have oppositePerpendicular : PerpendicularTo source (opposite position) :=
    (perpendicular_opposite_iff source position).mpr positionPerpendicular
  have imagePerpendicular := perpendicular_map_of_maps_opposite_pair symmetry
    mapsSource mapsOpposite positionPerpendicular
  have oppositeImagePerpendicular := perpendicular_map_of_maps_opposite_pair symmetry
    mapsSource mapsOpposite oppositePerpendicular
  exact eq_opposite_of_both_perpendicular target (symmetry position)
    (symmetry (opposite position)) imagePerpendicular oppositeImagePerpendicular
    (symmetry.injective.ne (opposite_ne position).symm)

def IsSenior (placement : Position → PriorityNumber) (senior : Position) : Prop :=
  ∀ position, priorityDigit (placement senior) ≤ priorityDigit (placement position)

def transPriority (placement : Position → PriorityNumber) (senior : Position) :
    PriorityNumber := placement (opposite senior)

def Equivalent (left right : Position → PriorityNumber) : Prop :=
  SymmetryEquivalent fullSymmetryGroup left right

theorem transPriority_eq_iff_symmetryEquivalent_of_samePriorityMultiset
    (left right : Position → PriorityNumber)
    (leftSenior rightSenior : Position)
    (leftInjective : Function.Injective left)
    (rightInjective : Function.Injective right)
    (leftSeniorCorrect : IsSenior left leftSenior)
    (rightSeniorCorrect : IsSenior right rightSenior)
    (sameMultiset : SamePriorityMultiset left right) :
    transPriority left leftSenior = transPriority right rightSenior ↔
      Equivalent left right := by
  constructor
  · intro transSame
    rcases matchingPermutation_of_samePriorityMultiset left right rightInjective sameMultiset with
      ⟨matching, samePlacement⟩
    have leftLeRight : priorityDigit (left leftSenior) ≤
        priorityDigit (right rightSenior) := by
      have := leftSeniorCorrect (matching rightSenior)
      simpa [samePlacement, relabel] using this
    have rightLeLeft : priorityDigit (right rightSenior) ≤
        priorityDigit (left leftSenior) := by
      have := rightSeniorCorrect (matching.symm leftSenior)
      simpa [samePlacement, relabel] using this
    have seniorSame : left leftSenior = right rightSenior :=
      priorityDigit_injective (le_antisymm leftLeRight rightLeLeft)
    have mapsSenior : matching rightSenior = leftSenior := by
      apply leftInjective
      calc
        left (matching rightSenior) = right rightSenior := by
          simpa [relabel] using (congrFun samePlacement rightSenior).symm
        _ = left leftSenior := seniorSame.symm
    have mapsOpposite : matching (opposite rightSenior) = opposite leftSenior := by
      apply leftInjective
      calc
        left (matching (opposite rightSenior)) = right (opposite rightSenior) := by
          simpa [relabel] using (congrFun samePlacement (opposite rightSenior)).symm
        _ = left (opposite leftSenior) := transSame.symm
    exact ⟨⟨matching,
      mem_fullSymmetryGroup_of_maps_opposite_pair matching rightSenior leftSenior
        mapsSenior mapsOpposite⟩, samePlacement⟩
  · rintro ⟨symmetry, samePlacement⟩
    have leftLeRight : priorityDigit (left leftSenior) ≤
        priorityDigit (right rightSenior) := by
      have := leftSeniorCorrect (symmetry.1 rightSenior)
      simpa [samePlacement, relabel] using this
    have rightLeLeft : priorityDigit (right rightSenior) ≤
        priorityDigit (left leftSenior) := by
      have := rightSeniorCorrect (symmetry.1.symm leftSenior)
      simpa [samePlacement, relabel] using this
    have seniorSame : left leftSenior = right rightSenior :=
      priorityDigit_injective (le_antisymm leftLeRight rightLeLeft)
    have mapsSenior : symmetry.1 rightSenior = leftSenior := by
      apply leftInjective
      calc
        left (symmetry.1 rightSenior) = right rightSenior := by
          simpa [relabel] using (congrFun samePlacement rightSenior).symm
        _ = left leftSenior := seniorSame.symm
    calc
      transPriority left leftSenior = left (opposite leftSenior) := rfl
      _ = left (symmetry.1 (opposite rightSenior)) := by
        rw [symmetry.2, mapsSenior]
      _ = right (opposite rightSenior) := by
        simpa [relabel] using (congrFun samePlacement (opposite rightSenior)).symm
      _ = transPriority right rightSenior := rfl

theorem blueBook_squarePlanarIndex_eq_iff_symmetryEquivalent
    (left right : Position → PriorityNumber)
    (leftSenior rightSenior : Position)
    (leftInjective : Function.Injective left)
    (rightInjective : Function.Injective right)
    (leftSeniorCorrect : IsSenior left leftSenior)
    (rightSeniorCorrect : IsSenior right rightSenior)
    (sameMultiset : SamePriorityMultiset left right) :
    BlueBookP93.squarePlanarIndex (transPriority left leftSenior) =
        BlueBookP93.squarePlanarIndex (transPriority right rightSenior) ↔
      Equivalent left right := by
  simpa [BlueBookP93.squarePlanarIndex] using
    transPriority_eq_iff_symmetryEquivalent_of_samePriorityMultiset
      left right leftSenior rightSenior leftInjective rightInjective
      leftSeniorCorrect rightSeniorCorrect sameMultiset

theorem blueBook_squarePyramid4Index_eq_iff_symmetryEquivalent
    (left right : Position → PriorityNumber)
    (leftSenior rightSenior : Position)
    (leftInjective : Function.Injective left)
    (rightInjective : Function.Injective right)
    (leftSeniorCorrect : IsSenior left leftSenior)
    (rightSeniorCorrect : IsSenior right rightSenior)
    (sameMultiset : SamePriorityMultiset left right) :
    BlueBookP93.squarePyramid4Index (transPriority left leftSenior) =
        BlueBookP93.squarePyramid4Index (transPriority right rightSenior) ↔
      Equivalent left right := by
  simpa [BlueBookP93.squarePyramid4Index] using
    transPriority_eq_iff_symmetryEquivalent_of_samePriorityMultiset
      left right leftSenior rightSenior leftInjective rightInjective
      leftSeniorCorrect rightSeniorCorrect sameMultiset

end FourOpposite

/-! ## See-saw four-coordinate geometry -/

namespace SeeSaw

inductive Position where
  | wide0
  | wide1
  | narrow0
  | narrow1
  deriving DecidableEq, Fintype, Repr

def IsWide : Position → Prop
  | .wide0 | .wide1 => True
  | .narrow0 | .narrow1 => False

private instance isWideDecidable : DecidablePred IsWide := by
  intro position
  cases position <;> unfold IsWide <;> infer_instance

def fullSymmetryGroup : SymmetryGroup Position where
  carrier := { symmetry | ∀ position, IsWide (symmetry position) ↔ IsWide position }
  one_mem' := by simp
  mul_mem' := by
    intro first second firstMember secondMember position
    exact (firstMember (second position)).trans (secondMember position)
  inv_mem' := by
    intro symmetry member position
    have transported := member (symmetry⁻¹ position)
    simpa using transported.symm

private instance fullSymmetryGroupMembershipDecidable :
    DecidablePred (fun symmetry : Equiv.Perm Position => symmetry ∈ fullSymmetryGroup) := by
  intro symmetry
  change Decidable (∀ position, IsWide (symmetry position) ↔ IsWide position)
  infer_instance

theorem card_fullSymmetryGroup : Fintype.card fullSymmetryGroup = 4 := by
  decide

theorem mem_fullSymmetryGroup_of_maps_wide_pair
    (symmetry : Equiv.Perm Position)
    (maps :
      (symmetry .wide0 = .wide0 ∧ symmetry .wide1 = .wide1) ∨
      (symmetry .wide0 = .wide1 ∧ symmetry .wide1 = .wide0)) :
    symmetry ∈ fullSymmetryGroup := by
  have imageNarrow0Wide0 : symmetry .narrow0 ≠ symmetry .wide0 :=
    symmetry.injective.ne (by decide)
  have imageNarrow0Wide1 : symmetry .narrow0 ≠ symmetry .wide1 :=
    symmetry.injective.ne (by decide)
  have imageNarrow1Wide0 : symmetry .narrow1 ≠ symmetry .wide0 :=
    symmetry.injective.ne (by decide)
  have imageNarrow1Wide1 : symmetry .narrow1 ≠ symmetry .wide1 :=
    symmetry.injective.ne (by decide)
  rcases maps with maps | maps
  · intro position
    fin_cases position
    · simp [IsWide, maps.1]
    · simp [IsWide, maps.2]
    · generalize imageEq : symmetry .narrow0 = image
      fin_cases image <;> simp_all [IsWide]
    · generalize imageEq : symmetry .narrow1 = image
      fin_cases image <;> simp_all [IsWide]
  · intro position
    fin_cases position
    · simp [IsWide, maps.1]
    · simp [IsWide, maps.2]
    · generalize imageEq : symmetry .narrow0 = image
      fin_cases image <;> simp_all [IsWide]
    · generalize imageEq : symmetry .narrow1 = image
      fin_cases image <;> simp_all [IsWide]

theorem wide_images_unordered (symmetry : fullSymmetryGroup) :
    (symmetry.1 .wide0 = .wide0 ∧ symmetry.1 .wide1 = .wide1) ∨
      (symmetry.1 .wide0 = .wide1 ∧ symmetry.1 .wide1 = .wide0) := by
  have imagesDistinct : symmetry.1 .wide0 ≠ symmetry.1 .wide1 :=
    symmetry.1.injective.ne (by decide)
  have firstWide := (symmetry.2 .wide0).mpr trivial
  have secondWide := (symmetry.2 .wide1).mpr trivial
  generalize firstEq : symmetry.1 .wide0 = first at firstWide
  generalize secondEq : symmetry.1 .wide1 = second at secondWide
  fin_cases first <;> simp [IsWide] at firstWide
  all_goals fin_cases second <;> simp_all [IsWide]

def sourceIndex (placement : Position → PriorityNumber) : List PriorityNumber :=
  BlueBookP93.seeSawIndex (placement .wide0) (placement .wide1)

def Equivalent (left right : Position → PriorityNumber) : Prop :=
  SymmetryEquivalent fullSymmetryGroup left right

theorem sourceIndex_eq_iff_symmetryEquivalent_of_samePriorityMultiset
    (left right : Position → PriorityNumber)
    (leftInjective : Function.Injective left)
    (rightInjective : Function.Injective right)
    (sameMultiset : SamePriorityMultiset left right) :
    sourceIndex left = sourceIndex right ↔ Equivalent left right := by
  constructor
  · intro sameIndex
    have wideEquivalent : UnorderedPairEquivalent
        (left .wide0) (left .wide1) (right .wide0) (right .wide1) :=
      (orderedPair_eq_iff_unorderedPairEquivalent _ _ _ _).mp (by
        simpa [sourceIndex, BlueBookP93.seeSawIndex] using sameIndex)
    rcases matchingPermutation_of_samePriorityMultiset left right rightInjective sameMultiset with
      ⟨matching, samePlacement⟩
    have matchingProperty : ∀ position, left (matching position) = right position := by
      intro position
      simpa [relabel] using (congrFun samePlacement position).symm
    have mapsWide :
        (matching .wide0 = .wide0 ∧ matching .wide1 = .wide1) ∨
          (matching .wide0 = .wide1 ∧ matching .wide1 = .wide0) := by
      rcases wideEquivalent with direct | swapped
      · left
        constructor <;> apply leftInjective
        · simpa [matchingProperty] using direct.1.symm
        · simpa [matchingProperty] using direct.2.symm
      · right
        constructor <;> apply leftInjective
        · simpa [matchingProperty] using swapped.2.symm
        · simpa [matchingProperty] using swapped.1.symm
    exact ⟨⟨matching, mem_fullSymmetryGroup_of_maps_wide_pair matching mapsWide⟩,
      samePlacement⟩
  · rintro ⟨symmetry, samePlacement⟩
    have images := wide_images_unordered symmetry
    apply (orderedPair_eq_iff_unorderedPairEquivalent _ _ _ _).mpr
    rcases images with direct | swapped
    · left
      constructor
      · calc
          left .wide0 = left (symmetry.1 .wide0) := by rw [direct.1]
          _ = right .wide0 := by
            simpa [relabel] using (congrFun samePlacement .wide0).symm
      · calc
          left .wide1 = left (symmetry.1 .wide1) := by rw [direct.2]
          _ = right .wide1 := by
            simpa [relabel] using (congrFun samePlacement .wide1).symm
    · right
      constructor
      · calc
          left .wide0 = left (symmetry.1 .wide1) := by rw [swapped.2]
          _ = right .wide1 := by
            simpa [relabel] using (congrFun samePlacement .wide1).symm
      · calc
          left .wide1 = left (symmetry.1 .wide0) := by rw [swapped.1]
          _ = right .wide0 := by
            simpa [relabel] using (congrFun samePlacement .wide0).symm

theorem blueBook_seeSawIndex_eq_iff_symmetryEquivalent
    (left right : Position → PriorityNumber)
    (leftInjective : Function.Injective left)
    (rightInjective : Function.Injective right)
    (sameMultiset : SamePriorityMultiset left right) :
    BlueBookP93.seeSawIndex (left .wide0) (left .wide1) =
        BlueBookP93.seeSawIndex (right .wide0) (right .wide1) ↔ Equivalent left right :=
  sourceIndex_eq_iff_symmetryEquivalent_of_samePriorityMultiset
    left right leftInjective rightInjective sameMultiset

end SeeSaw

end TetraStereo.OneCenter.RedBookIR9.SimpleGeometrySourceIndexCompleteness
