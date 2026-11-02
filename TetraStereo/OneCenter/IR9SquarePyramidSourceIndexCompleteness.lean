import TetraStereo.OneCenter.IR9BipyramidalSourceIndexCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.SquarePyramidSourceIndexCompleteness

open FiniteSymmetry
open TrigonalPrismSourceIndexCompleteness

abbrev PriorityNumber := BlueBookP93.PriorityNumber
abbrev PriorityDigit := CanonicalPriorityDigit

/-!
# Exact source-index classification for the ideal square pyramid (SPY-5)

The five positions are represented independently of the source index.  The full idealized
square-pyramid symmetry group fixes the apex and preserves the two pairs of opposite base
vertices.  It is therefore the full dihedral symmetry group of the square base.

On the chemically relevant distinct-priority domain, IR-9.3.3.6's two digits -- the apical
priority followed by the priority trans to the senior base ligand -- are proved to be a complete
relative invariant once the complete five-priority multiset is fixed.
-/

/-- The apex and four cyclic base positions of an ideal square pyramid. -/
inductive Position where
  | apex
  | base0
  | base1
  | base2
  | base3
  deriving DecidableEq, Fintype, Repr

/-- Antipodal pairing on the square base; the apex is its own distinguished fixed point. -/
def opposite : Position → Position
  | .apex => .apex
  | .base0 => .base2
  | .base1 => .base3
  | .base2 => .base0
  | .base3 => .base1

@[simp] theorem opposite_apex : opposite .apex = .apex := rfl
@[simp] theorem opposite_base0 : opposite .base0 = .base2 := rfl
@[simp] theorem opposite_base1 : opposite .base1 = .base3 := rfl
@[simp] theorem opposite_base2 : opposite .base2 = .base0 := rfl
@[simp] theorem opposite_base3 : opposite .base3 = .base1 := rfl

@[simp] theorem opposite_opposite (position : Position) :
    opposite (opposite position) = position := by
  cases position <;> rfl

/-- A position is on the square base exactly when it is not the apex. -/
def IsBase (position : Position) : Prop := position ≠ .apex

/-- The complete ideal SPY-5 vertex-symmetry group: the apex is fixed and opposition in the
square base is preserved. -/
def fullSymmetryGroup : SymmetryGroup Position where
  carrier := { symmetry |
    symmetry .apex = .apex ∧
      ∀ position, symmetry (opposite position) = opposite (symmetry position) }
  mul_mem' := by
    intro first second firstMember secondMember
    constructor
    · simp [firstMember.1, secondMember.1]
    · intro position
      change first (second (opposite position)) = opposite (first (second position))
      rw [secondMember.2, firstMember.2]
  one_mem' := by
    constructor <;> simp
  inv_mem' := by
    intro symmetry member
    constructor
    · apply symmetry.injective
      simpa using member.1.symm
    · intro position
      have transported := member.2 (symmetry.symm position)
      apply symmetry.injective
      simpa using transported.symm

private instance fullSymmetryGroupMembershipDecidable :
    DecidablePred (fun symmetry : Equiv.Perm Position => symmetry ∈ fullSymmetryGroup) := by
  intro symmetry
  change Decidable (symmetry .apex = .apex ∧
    ∀ position, symmetry (opposite position) = opposite (symmetry position))
  infer_instance

/-- The independently derived full ideal square-pyramid group has the expected order eight. -/
theorem card_fullSymmetryGroup : Fintype.card fullSymmetryGroup = 8 := by
  decide

/-- Exhaustive finite fact used in the completeness direction.  A permutation fixing the apex
and carrying one complete base-opposite pair to another necessarily preserves every opposite
pair, hence is an ideal square-pyramid symmetry. -/
theorem mem_fullSymmetryGroup_of_maps_opposite_pair
    (symmetry : Equiv.Perm Position) (source target : Position)
    (sourceBase : IsBase source) (targetBase : IsBase target)
    (fixesApex : symmetry .apex = .apex)
    (mapsSource : symmetry source = target)
    (mapsOpposite : symmetry (opposite source) = opposite target) :
    symmetry ∈ fullSymmetryGroup := by
  change symmetry .apex = .apex ∧
    ∀ position, symmetry (opposite position) = opposite (symmetry position)
  refine ⟨fixesApex, ?_⟩
  have imageInjective : ∀ left right,
      symmetry left = symmetry right ↔ left = right := by
    intro left right
    exact symmetry.injective.eq_iff
  have imageApexBase0 : symmetry .apex ≠ symmetry .base0 :=
    symmetry.injective.ne (by decide)
  have imageApexBase1 : symmetry .apex ≠ symmetry .base1 :=
    symmetry.injective.ne (by decide)
  have imageApexBase2 : symmetry .apex ≠ symmetry .base2 :=
    symmetry.injective.ne (by decide)
  have imageApexBase3 : symmetry .apex ≠ symmetry .base3 :=
    symmetry.injective.ne (by decide)
  have imageBase01 : symmetry .base0 ≠ symmetry .base1 :=
    symmetry.injective.ne (by decide)
  have imageBase02 : symmetry .base0 ≠ symmetry .base2 :=
    symmetry.injective.ne (by decide)
  have imageBase03 : symmetry .base0 ≠ symmetry .base3 :=
    symmetry.injective.ne (by decide)
  have imageBase12 : symmetry .base1 ≠ symmetry .base2 :=
    symmetry.injective.ne (by decide)
  have imageBase13 : symmetry .base1 ≠ symmetry .base3 :=
    symmetry.injective.ne (by decide)
  have imageBase23 : symmetry .base2 ≠ symmetry .base3 :=
    symmetry.injective.ne (by decide)
  fin_cases source <;> simp [IsBase] at sourceBase
  all_goals fin_cases target <;> simp [IsBase] at targetBase
  all_goals
    intro position
    generalize image0Eq : symmetry .base0 = image0 at *
    generalize image1Eq : symmetry .base1 = image1 at *
    generalize image2Eq : symmetry .base2 = image2 at *
    generalize image3Eq : symmetry .base3 = image3 at *
    have images01 : image0 ≠ image1 := by simpa [image0Eq, image1Eq] using imageBase01
    have images02 : image0 ≠ image2 := by simpa [image0Eq, image2Eq] using imageBase02
    have images03 : image0 ≠ image3 := by simpa [image0Eq, image3Eq] using imageBase03
    have images12 : image1 ≠ image2 := by simpa [image1Eq, image2Eq] using imageBase12
    have images13 : image1 ≠ image3 := by simpa [image1Eq, image3Eq] using imageBase13
    have images23 : image2 ≠ image3 := by simpa [image2Eq, image3Eq] using imageBase23
    fin_cases image0 <;> try simp_all [opposite]
  all_goals fin_cases image1 <;> try simp_all
  all_goals fin_cases image2 <;> try simp_all
  all_goals fin_cases image3 <;> try simp_all
  all_goals fin_cases position <;> simp_all

/-- Fixed reference word used solely to state equality of the complete priority multiset. -/
def placementWord (placement : Position → PriorityNumber) : List PriorityNumber :=
  [ placement .apex, placement .base0, placement .base1,
    placement .base2, placement .base3 ]

def SamePriorityMultiset (left right : Position → PriorityNumber) : Prop :=
  (placementWord left).Perm (placementWord right)

/-- A supplied base position really carries a (possibly tied) senior base priority. -/
def IsSeniorBase (placement : Position → PriorityNumber) (senior : Position) : Prop :=
  IsBase senior ∧
    ∀ position, IsBase position →
      priorityDigit (placement senior) ≤ priorityDigit (placement position)

/-- IR-9.3.3.6 evaluated from a complete placement and its independently identified senior base
position. -/
def sourceIndex (placement : Position → PriorityNumber) (seniorBase : Position) :
    List PriorityNumber :=
  BlueBookP93.squarePyramidIndex
    (placement .apex) (placement (opposite seniorBase))

/-- Relative equivalence under every full ideal SPY-5 symmetry. -/
def SquarePyramidEquivalent (left right : Position → PriorityNumber) : Prop :=
  SymmetryEquivalent fullSymmetryGroup left right

theorem mem_placementWord_iff_exists_position
    (placement : Position → PriorityNumber) (priority : PriorityNumber) :
    priority ∈ placementWord placement ↔
      ∃ position, placement position = priority := by
  constructor
  · simp only [placementWord, List.mem_cons,
      List.not_mem_nil, or_false]
    intro member
    rcases member with same | same | same | same | same
    · exact ⟨.apex, same.symm⟩
    · exact ⟨.base0, same.symm⟩
    · exact ⟨.base1, same.symm⟩
    · exact ⟨.base2, same.symm⟩
    · exact ⟨.base3, same.symm⟩
  · rintro ⟨position, rfl⟩
    cases position <;> simp [placementWord]

/-- For injective placements, equality of the concrete five-entry words as multisets supplies
the unique position permutation matching equal priority numbers. -/
theorem matchingPermutation_of_samePriorityMultiset
    (left right : Position → PriorityNumber)
    (_leftInjective : Function.Injective left)
    (rightInjective : Function.Injective right)
    (sameMultiset : SamePriorityMultiset left right) :
    ∃ matching : Equiv.Perm Position, right = relabel matching left := by
  have rightOccursOnLeft : ∀ position, ∃ matched, left matched = right position := by
    intro position
    apply (mem_placementWord_iff_exists_position left (right position)).mp
    exact sameMultiset.mem_iff.mpr
      ((mem_placementWord_iff_exists_position right (right position)).mpr
        ⟨position, rfl⟩)
  let matchingFunction : Position → Position :=
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
  let matching : Equiv.Perm Position :=
    Equiv.ofBijective matchingFunction matchingBijective
  refine ⟨matching, ?_⟩
  funext position
  exact (matchingProperty position).symm

/-- A permutation fixing the apex carries base vertices to base vertices. -/
theorem isBase_map_of_fixesApex
    (symmetry : Equiv.Perm Position) (fixesApex : symmetry .apex = .apex)
    {position : Position} (positionBase : IsBase position) :
    IsBase (symmetry position) := by
  intro mappedApex
  apply positionBase
  apply symmetry.injective
  simpa [fixesApex] using mappedApex

/-- The source-spelled SPY-5 index is a complete relative invariant on the distinct-priority
domain.  Equality is considered, as chemical configuration comparison requires, at fixed complete
five-priority multiset. -/
theorem squarePyramidIndex_eq_iff_symmetryEquivalent_of_samePriorityMultiset
    (left right : Position → PriorityNumber)
    (leftSenior rightSenior : Position)
    (leftInjective : Function.Injective left)
    (rightInjective : Function.Injective right)
    (leftSeniorCorrect : IsSeniorBase left leftSenior)
    (rightSeniorCorrect : IsSeniorBase right rightSenior)
    (sameMultiset : SamePriorityMultiset left right) :
    sourceIndex left leftSenior = sourceIndex right rightSenior ↔
      SquarePyramidEquivalent left right := by
  constructor
  · intro sameIndex
    have indexParts :
        left .apex = right .apex ∧
          left (opposite leftSenior) = right (opposite rightSenior) := by
      simpa [sourceIndex, BlueBookP93.squarePyramidIndex] using sameIndex
    rcases matchingPermutation_of_samePriorityMultiset left right leftInjective
        rightInjective sameMultiset with ⟨matching, matchingEq⟩
    have matchingApex : matching .apex = .apex := by
      apply leftInjective
      calc
        left (matching .apex) = right .apex := by
          simpa [relabel] using (congrFun matchingEq .apex).symm
        _ = left .apex := indexParts.1.symm
    have matchingMapsBase : ∀ {position}, IsBase position →
        IsBase (matching position) := by
      intro position positionBase
      exact isBase_map_of_fixesApex matching matchingApex positionBase
    have inverseApex : matching.symm .apex = .apex := by
      apply matching.injective
      simp [matchingApex]
    have inverseMapsBase : ∀ {position}, IsBase position →
        IsBase (matching.symm position) := by
      intro position positionBase
      exact isBase_map_of_fixesApex matching.symm inverseApex positionBase
    have leftLeRight : priorityDigit (left leftSenior) ≤
        priorityDigit (right rightSenior) := by
      have := leftSeniorCorrect.2 (matching rightSenior)
        (matchingMapsBase rightSeniorCorrect.1)
      simpa [matchingEq, relabel] using this
    have rightLeLeft : priorityDigit (right rightSenior) ≤
        priorityDigit (left leftSenior) := by
      have := rightSeniorCorrect.2 (matching.symm leftSenior)
        (inverseMapsBase leftSeniorCorrect.1)
      simpa [matchingEq, relabel] using this
    have seniorPrioritySame : left leftSenior = right rightSenior :=
      priorityDigit_injective (le_antisymm leftLeRight rightLeLeft)
    have mapsSenior : matching rightSenior = leftSenior := by
      apply leftInjective
      calc
        left (matching rightSenior) = right rightSenior := by
          simpa [relabel] using (congrFun matchingEq rightSenior).symm
        _ = left leftSenior := seniorPrioritySame.symm
    have mapsOpposite :
        matching (opposite rightSenior) = opposite leftSenior := by
      apply leftInjective
      calc
        left (matching (opposite rightSenior)) =
            right (opposite rightSenior) := by
          simpa [relabel] using (congrFun matchingEq (opposite rightSenior)).symm
        _ = left (opposite leftSenior) := indexParts.2.symm
    have matchingMember : matching ∈ fullSymmetryGroup :=
      mem_fullSymmetryGroup_of_maps_opposite_pair matching rightSenior leftSenior
        rightSeniorCorrect.1 leftSeniorCorrect.1 matchingApex mapsSenior mapsOpposite
    exact ⟨⟨matching, matchingMember⟩, matchingEq⟩
  · rintro ⟨symmetry, equivalentEq⟩
    have symmetryMember := symmetry.2
    have matchingApex : symmetry.1 .apex = .apex := symmetryMember.1
    have matchingMapsBase : ∀ {position}, IsBase position →
        IsBase (symmetry.1 position) := by
      intro position positionBase
      exact isBase_map_of_fixesApex symmetry.1 matchingApex positionBase
    have inverseApex : symmetry.1.symm .apex = .apex := by
      apply symmetry.1.injective
      simp [matchingApex]
    have inverseMapsBase : ∀ {position}, IsBase position →
        IsBase (symmetry.1.symm position) := by
      intro position positionBase
      exact isBase_map_of_fixesApex symmetry.1.symm inverseApex positionBase
    have leftLeRight : priorityDigit (left leftSenior) ≤
        priorityDigit (right rightSenior) := by
      have := leftSeniorCorrect.2 (symmetry.1 rightSenior)
        (matchingMapsBase rightSeniorCorrect.1)
      simpa [equivalentEq, relabel] using this
    have rightLeLeft : priorityDigit (right rightSenior) ≤
        priorityDigit (left leftSenior) := by
      have := rightSeniorCorrect.2 (symmetry.1.symm leftSenior)
        (inverseMapsBase leftSeniorCorrect.1)
      simpa [equivalentEq, relabel] using this
    have seniorPrioritySame : left leftSenior = right rightSenior :=
      priorityDigit_injective (le_antisymm leftLeRight rightLeLeft)
    have mapsSenior : symmetry.1 rightSenior = leftSenior := by
      apply leftInjective
      calc
        left (symmetry.1 rightSenior) = right rightSenior := by
          simpa [relabel] using (congrFun equivalentEq rightSenior).symm
        _ = left leftSenior := seniorPrioritySame.symm
    have oppositePrioritySame :
        right (opposite rightSenior) = left (opposite leftSenior) := by
      calc
        right (opposite rightSenior) =
            left (symmetry.1 (opposite rightSenior)) := by
          simpa [relabel] using congrFun equivalentEq (opposite rightSenior)
        _ = left (opposite (symmetry.1 rightSenior)) := by
          rw [symmetryMember.2]
        _ = left (opposite leftSenior) := by rw [mapsSenior]
    have apexPrioritySame : left .apex = right .apex := by
      calc
        left .apex = left (symmetry.1 .apex) := by rw [matchingApex]
        _ = right .apex := by
          simpa [relabel] using (congrFun equivalentEq .apex).symm
    simp only [sourceIndex, BlueBookP93.squarePyramidIndex]
    rw [apexPrioritySame, oppositePrioritySame]

/-- Direct Blue Book spelling of the exact SPY-5 theorem. -/
theorem blueBook_squarePyramidIndex_eq_iff_symmetryEquivalent
    (left right : Position → PriorityNumber)
    (leftSenior rightSenior : Position)
    (leftInjective : Function.Injective left)
    (rightInjective : Function.Injective right)
    (leftSeniorCorrect : IsSeniorBase left leftSenior)
    (rightSeniorCorrect : IsSeniorBase right rightSenior)
    (sameMultiset : SamePriorityMultiset left right) :
    BlueBookP93.squarePyramidIndex
        (left .apex) (left (opposite leftSenior)) =
      BlueBookP93.squarePyramidIndex
        (right .apex) (right (opposite rightSenior)) ↔
      SquarePyramidEquivalent left right :=
  squarePyramidIndex_eq_iff_symmetryEquivalent_of_samePriorityMultiset
    left right leftSenior rightSenior leftInjective rightInjective
      leftSeniorCorrect rightSeniorCorrect sameMultiset

/-! ## Production refinement -/

def sourcePlacementOfProduction
    (placement : Position → PolyhedralPriorityNumber) : Position → PriorityNumber :=
  fun position => BlueBookP93.priorityOfProduction (placement position)

def productionPlacementWord
    (placement : Position → PolyhedralPriorityNumber) :
    List PolyhedralPriorityNumber :=
  [ placement .apex, placement .base0, placement .base1,
    placement .base2, placement .base3 ]

def ProductionSamePriorityMultiset
    (left right : Position → PolyhedralPriorityNumber) : Prop :=
  (productionPlacementWord left).Perm (productionPlacementWord right)

def ProductionIsSeniorBase
    (placement : Position → PolyhedralPriorityNumber) (senior : Position) : Prop :=
  IsSeniorBase (sourcePlacementOfProduction placement) senior

def ProductionSquarePyramidEquivalent
    (left right : Position → PolyhedralPriorityNumber) : Prop :=
  SquarePyramidEquivalent
    (sourcePlacementOfProduction left) (sourcePlacementOfProduction right)

def productionSourceIndex
    (placement : Position → PolyhedralPriorityNumber) (seniorBase : Position) :
    List PolyhedralPriorityNumber :=
  squarePyramidConfigurationIndex
    (placement .apex) (placement (opposite seniorBase))

/-- The executable production SPY-5 index has exactly the source theorem's collision boundary on
the distinct-priority domain. -/
theorem productionSquarePyramidConfigurationIndex_eq_iff_symmetryEquivalent
    (left right : Position → PolyhedralPriorityNumber)
    (leftSenior rightSenior : Position)
    (leftInjective : Function.Injective left)
    (rightInjective : Function.Injective right)
    (leftSeniorCorrect : ProductionIsSeniorBase left leftSenior)
    (rightSeniorCorrect : ProductionIsSeniorBase right rightSenior)
    (sameMultiset : ProductionSamePriorityMultiset left right) :
    productionSourceIndex left leftSenior =
        productionSourceIndex right rightSenior ↔
      ProductionSquarePyramidEquivalent left right := by
  have productionPriorityInjective :
      Function.Injective BlueBookP93.priorityOfProduction :=
    BipyramidalSourceIndexCompleteness.priorityOfProduction_injective
  have leftSourceInjective :
      Function.Injective (sourcePlacementOfProduction left) := by
    intro first second same
    apply leftInjective
    exact productionPriorityInjective same
  have rightSourceInjective :
      Function.Injective (sourcePlacementOfProduction right) := by
    intro first second same
    apply rightInjective
    exact productionPriorityInjective same
  have sourceMultiset : SamePriorityMultiset
      (sourcePlacementOfProduction left) (sourcePlacementOfProduction right) := by
    simpa [SamePriorityMultiset, placementWord, ProductionSamePriorityMultiset,
      productionPlacementWord, sourcePlacementOfProduction] using
        sameMultiset.map BlueBookP93.priorityOfProduction
  let mapIndex := List.map BlueBookP93.priorityOfProduction
  have mapIndexInjective : Function.Injective mapIndex :=
    List.map_injective_iff.mpr productionPriorityInjective
  constructor
  · intro same
    have mappedSame := congrArg mapIndex same
    have sourceSame :
        sourceIndex (sourcePlacementOfProduction left) leftSenior =
          sourceIndex (sourcePlacementOfProduction right) rightSenior := by
      simpa [mapIndex, productionSourceIndex, sourceIndex,
        sourcePlacementOfProduction,
        squarePyramidConfigurationIndex_conforms_P93] using mappedSame
    exact (squarePyramidIndex_eq_iff_symmetryEquivalent_of_samePriorityMultiset
      _ _ leftSenior rightSenior leftSourceInjective rightSourceInjective
        leftSeniorCorrect rightSeniorCorrect sourceMultiset).mp sourceSame
  · intro equivalent
    apply mapIndexInjective
    have sourceSame :=
      (squarePyramidIndex_eq_iff_symmetryEquivalent_of_samePriorityMultiset
        _ _ leftSenior rightSenior leftSourceInjective rightSourceInjective
          leftSeniorCorrect rightSeniorCorrect sourceMultiset).mpr equivalent
    simpa [mapIndex, productionSourceIndex, sourceIndex,
      sourcePlacementOfProduction,
      squarePyramidConfigurationIndex_conforms_P93] using sourceSame

end TetraStereo.OneCenter.RedBookIR9.SquarePyramidSourceIndexCompleteness
