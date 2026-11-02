import TetraStereo.OneCenter.IR9FiniteSymmetryCanonicalization

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.OctahedronSourceIndexCompleteness

open FiniteSymmetry

abbrev PriorityNumber := BlueBookP93.PriorityNumber

/-!
# Exact source-index classification for the ideal octahedron (OC-6)

The six vertices are represented independently of the compact two-entry source index.  The full
ideal octahedral vertex group is derived as exactly the permutations preserving the three
opposite pairs.  At fixed complete priority multiset, and on the source's distinct-priority
domain, the priorities opposite priority one and opposite the senior ligand in its perpendicular
plane determine all three opposite pairs.  The main theorem proves that equality of the actual
IR-9/P-93 index is therefore equivalent to full ideal-octahedral symmetry.
-/

/-- Six signed coordinate-axis vertices of an ideal octahedron. -/
inductive Position where
  | xPlus
  | xMinus
  | yPlus
  | yMinus
  | zPlus
  | zMinus
  deriving DecidableEq, Fintype, Repr

/-- The antipodal octahedral vertex. -/
def opposite : Position → Position
  | .xPlus => .xMinus
  | .xMinus => .xPlus
  | .yPlus => .yMinus
  | .yMinus => .yPlus
  | .zPlus => .zMinus
  | .zMinus => .zPlus

@[simp] theorem opposite_opposite (position : Position) :
    opposite (opposite position) = position := by
  cases position <;> rfl

theorem opposite_ne (position : Position) : opposite position ≠ position := by
  cases position <;> decide

/-- A vertex is in the four-vertex plane perpendicular to the selected axial vertex exactly when
it belongs to neither end of that axial opposite pair. -/
def PerpendicularTo (axial position : Position) : Prop :=
  position ≠ axial ∧ position ≠ opposite axial

/-- The complete ideal octahedral vertex group, derived solely from antipodal incidence. -/
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

/-- The independently derived full ideal-octahedral vertex group has order 48. -/
theorem card_fullSymmetryGroup : Fintype.card fullSymmetryGroup = 48 := by
  set_option maxHeartbeats 1000000 in
    decide

@[simp] theorem perpendicular_opposite_iff (axial position : Position) :
    PerpendicularTo axial (opposite position) ↔ PerpendicularTo axial position := by
  cases axial <;> cases position <;> simp [PerpendicularTo, opposite]

/-- Relative to two perpendicular axes, the only two vertices perpendicular to both are an
opposite pair.  This small finite incidence fact is reduced and checked by Lean's kernel. -/
theorem eq_opposite_of_common_perpendiculars
    (firstAxis secondAxis firstPosition secondPosition : Position)
    (axesPerpendicular : PerpendicularTo firstAxis secondAxis)
    (firstPerpendicularFirst : PerpendicularTo firstAxis firstPosition)
    (firstPerpendicularSecond : PerpendicularTo secondAxis firstPosition)
    (secondPerpendicularFirst : PerpendicularTo firstAxis secondPosition)
    (secondPerpendicularSecond : PerpendicularTo secondAxis secondPosition)
    (distinct : firstPosition ≠ secondPosition) :
    secondPosition = opposite firstPosition := by
  fin_cases firstAxis <;> fin_cases secondAxis <;>
    simp [PerpendicularTo, opposite] at axesPerpendicular
  all_goals fin_cases firstPosition <;>
    simp [PerpendicularTo, opposite] at firstPerpendicularFirst
  all_goals fin_cases secondPosition <;> simp_all [PerpendicularTo, opposite]

/-- A bijection carrying both ends of an axial pair carries its perpendicular plane onto the
target perpendicular plane. -/
theorem perpendicular_map_of_maps_opposite_pair
    (symmetry : Equiv.Perm Position) {sourceAxial targetAxial position : Position}
    (mapsAxial : symmetry sourceAxial = targetAxial)
    (mapsOpposite : symmetry (opposite sourceAxial) = opposite targetAxial)
    (perpendicular : PerpendicularTo sourceAxial position) :
    PerpendicularTo targetAxial (symmetry position) := by
  constructor
  · intro same
    apply perpendicular.1
    apply symmetry.injective
    simpa [mapsAxial] using same
  · intro same
    apply perpendicular.2
    apply symmetry.injective
    simpa [mapsOpposite] using same

/-- Four mapped vertices comprising two distinct opposite pairs force a permutation of all six
vertices to preserve the remaining opposite pair as well. -/
theorem mem_fullSymmetryGroup_of_maps_two_opposite_pairs
    (symmetry : Equiv.Perm Position)
    (firstSource firstTarget secondSource secondTarget : Position)
    (secondTargetPerpendicular : PerpendicularTo firstTarget secondTarget)
    (mapsFirst : symmetry firstSource = firstTarget)
    (mapsFirstOpposite : symmetry (opposite firstSource) = opposite firstTarget)
    (mapsSecond : symmetry secondSource = secondTarget)
    (mapsSecondOpposite : symmetry (opposite secondSource) = opposite secondTarget) :
    symmetry ∈ fullSymmetryGroup := by
  change ∀ position,
    symmetry (opposite position) = opposite (symmetry position)
  intro position
  by_cases atFirst : position = firstSource
  · subst position
    rw [mapsFirstOpposite, mapsFirst]
  by_cases atFirstOpposite : position = opposite firstSource
  · subst position
    simp [mapsFirst, mapsFirstOpposite]
  by_cases atSecond : position = secondSource
  · subst position
    rw [mapsSecondOpposite, mapsSecond]
  by_cases atSecondOpposite : position = opposite secondSource
  · subst position
    simp [mapsSecond, mapsSecondOpposite]
  have positionPerpendicularFirst : PerpendicularTo firstSource position :=
    ⟨atFirst, atFirstOpposite⟩
  have positionPerpendicularSecond : PerpendicularTo secondSource position :=
    ⟨atSecond, atSecondOpposite⟩
  have oppositePerpendicularFirst :
      PerpendicularTo firstSource (opposite position) :=
    (perpendicular_opposite_iff firstSource position).mpr positionPerpendicularFirst
  have oppositePerpendicularSecond :
      PerpendicularTo secondSource (opposite position) :=
    (perpendicular_opposite_iff secondSource position).mpr positionPerpendicularSecond
  have imagePerpendicularFirst :=
    perpendicular_map_of_maps_opposite_pair symmetry mapsFirst mapsFirstOpposite
      positionPerpendicularFirst
  have imagePerpendicularSecond :=
    perpendicular_map_of_maps_opposite_pair symmetry mapsSecond mapsSecondOpposite
      positionPerpendicularSecond
  have oppositeImagePerpendicularFirst :=
    perpendicular_map_of_maps_opposite_pair symmetry mapsFirst mapsFirstOpposite
      oppositePerpendicularFirst
  have oppositeImagePerpendicularSecond :=
    perpendicular_map_of_maps_opposite_pair symmetry mapsSecond mapsSecondOpposite
      oppositePerpendicularSecond
  exact eq_opposite_of_common_perpendiculars firstTarget secondTarget
    (symmetry position) (symmetry (opposite position)) secondTargetPerpendicular
    imagePerpendicularFirst imagePerpendicularSecond oppositeImagePerpendicularFirst
    oppositeImagePerpendicularSecond (symmetry.injective.ne (opposite_ne position).symm)

/-- Fixed enumeration used to state equality of the complete six-priority multiset. -/
def placementWord (placement : Position → PriorityNumber) : List PriorityNumber :=
  [ placement .xPlus, placement .xMinus, placement .yPlus,
    placement .yMinus, placement .zPlus, placement .zMinus ]

def SamePriorityMultiset (left right : Position → PriorityNumber) : Prop :=
  (placementWord left).Perm (placementWord right)

/-- A supplied position carries the globally senior priority. -/
def IsSenior (placement : Position → PriorityNumber) (senior : Position) : Prop :=
  ∀ position, priorityDigit (placement senior) ≤ priorityDigit (placement position)

/-- A supplied position carries the senior priority among the four vertices perpendicular to the
selected priority-one axis. -/
def IsSeniorPerpendicular (placement : Position → PriorityNumber)
    (axial senior : Position) : Prop :=
  PerpendicularTo axial senior ∧
    ∀ position, PerpendicularTo axial position →
      priorityDigit (placement senior) ≤ priorityDigit (placement position)

/-- The literal P-93.3.3.7 index evaluated from a complete priority placement. -/
def sourceIndex (placement : Position → PriorityNumber)
    (priorityOne seniorPerpendicular : Position) : List PriorityNumber :=
  BlueBookP93.octahedronIndex
    (placement (opposite priorityOne))
    (placement (opposite seniorPerpendicular))

def OctahedronEquivalent (left right : Position → PriorityNumber) : Prop :=
  SymmetryEquivalent fullSymmetryGroup left right

theorem mem_placementWord_iff_exists_position
    (placement : Position → PriorityNumber) (priority : PriorityNumber) :
    priority ∈ placementWord placement ↔
      ∃ position, placement position = priority := by
  constructor
  · simp only [placementWord, List.mem_cons, List.not_mem_nil, or_false]
    intro member
    rcases member with same | same | same | same | same | same
    · exact ⟨.xPlus, same.symm⟩
    · exact ⟨.xMinus, same.symm⟩
    · exact ⟨.yPlus, same.symm⟩
    · exact ⟨.yMinus, same.symm⟩
    · exact ⟨.zPlus, same.symm⟩
    · exact ⟨.zMinus, same.symm⟩
  · rintro ⟨position, rfl⟩
    cases position <;> simp [placementWord]

/-- Equal finite priority multisets and injectivity determine a unique position matching. -/
theorem matchingPermutation_of_samePriorityMultiset
    (left right : Position → PriorityNumber)
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

/-- The source-spelled OC-6 index is a complete relative invariant on the distinct-priority
domain, at fixed complete six-priority multiset. -/
theorem octahedronIndex_eq_iff_symmetryEquivalent_of_samePriorityMultiset
    (left right : Position → PriorityNumber)
    (leftPriorityOne rightPriorityOne leftSeniorPlane rightSeniorPlane : Position)
    (leftInjective : Function.Injective left)
    (rightInjective : Function.Injective right)
    (leftPriorityOneCorrect : IsSenior left leftPriorityOne)
    (rightPriorityOneCorrect : IsSenior right rightPriorityOne)
    (leftSeniorPlaneCorrect :
      IsSeniorPerpendicular left leftPriorityOne leftSeniorPlane)
    (rightSeniorPlaneCorrect :
      IsSeniorPerpendicular right rightPriorityOne rightSeniorPlane)
    (sameMultiset : SamePriorityMultiset left right) :
    sourceIndex left leftPriorityOne leftSeniorPlane =
        sourceIndex right rightPriorityOne rightSeniorPlane ↔
      OctahedronEquivalent left right := by
  constructor
  · intro sameIndex
    have indexParts :
        left (opposite leftPriorityOne) = right (opposite rightPriorityOne) ∧
          left (opposite leftSeniorPlane) = right (opposite rightSeniorPlane) := by
      simpa [sourceIndex, BlueBookP93.octahedronIndex] using sameIndex
    rcases matchingPermutation_of_samePriorityMultiset left right
        rightInjective sameMultiset with ⟨matching, samePlacement⟩
    have leftLeRight : priorityDigit (left leftPriorityOne) ≤
        priorityDigit (right rightPriorityOne) := by
      have := leftPriorityOneCorrect (matching rightPriorityOne)
      simpa [samePlacement, relabel] using this
    have rightLeLeft : priorityDigit (right rightPriorityOne) ≤
        priorityDigit (left leftPriorityOne) := by
      have := rightPriorityOneCorrect (matching.symm leftPriorityOne)
      simpa [samePlacement, relabel] using this
    have priorityOneSame : left leftPriorityOne = right rightPriorityOne :=
      priorityDigit_injective (le_antisymm leftLeRight rightLeLeft)
    have mapsPriorityOne : matching rightPriorityOne = leftPriorityOne := by
      apply leftInjective
      calc
        left (matching rightPriorityOne) = right rightPriorityOne := by
          simpa [relabel] using (congrFun samePlacement rightPriorityOne).symm
        _ = left leftPriorityOne := priorityOneSame.symm
    have mapsPriorityOneOpposite :
        matching (opposite rightPriorityOne) = opposite leftPriorityOne := by
      apply leftInjective
      calc
        left (matching (opposite rightPriorityOne)) =
            right (opposite rightPriorityOne) := by
          simpa [relabel] using
            (congrFun samePlacement (opposite rightPriorityOne)).symm
        _ = left (opposite leftPriorityOne) := indexParts.1.symm
    have matchingMapsPerpendicular : ∀ {position},
        PerpendicularTo rightPriorityOne position →
          PerpendicularTo leftPriorityOne (matching position) := by
      intro position perpendicular
      exact perpendicular_map_of_maps_opposite_pair matching mapsPriorityOne
        mapsPriorityOneOpposite perpendicular
    have inverseMapsPriorityOne : matching.symm leftPriorityOne = rightPriorityOne := by
      apply matching.injective
      simp [mapsPriorityOne]
    have inverseMapsPriorityOneOpposite :
        matching.symm (opposite leftPriorityOne) = opposite rightPriorityOne := by
      apply matching.injective
      simp [mapsPriorityOneOpposite]
    have inverseMapsPerpendicular : ∀ {position},
        PerpendicularTo leftPriorityOne position →
          PerpendicularTo rightPriorityOne (matching.symm position) := by
      intro position perpendicular
      exact perpendicular_map_of_maps_opposite_pair matching.symm
        inverseMapsPriorityOne inverseMapsPriorityOneOpposite perpendicular
    have leftPlaneLeRight : priorityDigit (left leftSeniorPlane) ≤
        priorityDigit (right rightSeniorPlane) := by
      have := leftSeniorPlaneCorrect.2 (matching rightSeniorPlane)
        (matchingMapsPerpendicular rightSeniorPlaneCorrect.1)
      simpa [samePlacement, relabel] using this
    have rightPlaneLeLeft : priorityDigit (right rightSeniorPlane) ≤
        priorityDigit (left leftSeniorPlane) := by
      have := rightSeniorPlaneCorrect.2 (matching.symm leftSeniorPlane)
        (inverseMapsPerpendicular leftSeniorPlaneCorrect.1)
      simpa [samePlacement, relabel] using this
    have seniorPlaneSame : left leftSeniorPlane = right rightSeniorPlane :=
      priorityDigit_injective (le_antisymm leftPlaneLeRight rightPlaneLeLeft)
    have mapsSeniorPlane : matching rightSeniorPlane = leftSeniorPlane := by
      apply leftInjective
      calc
        left (matching rightSeniorPlane) = right rightSeniorPlane := by
          simpa [relabel] using (congrFun samePlacement rightSeniorPlane).symm
        _ = left leftSeniorPlane := seniorPlaneSame.symm
    have mapsSeniorPlaneOpposite :
        matching (opposite rightSeniorPlane) = opposite leftSeniorPlane := by
      apply leftInjective
      calc
        left (matching (opposite rightSeniorPlane)) =
            right (opposite rightSeniorPlane) := by
          simpa [relabel] using
            (congrFun samePlacement (opposite rightSeniorPlane)).symm
        _ = left (opposite leftSeniorPlane) := indexParts.2.symm
    have matchingMember : matching ∈ fullSymmetryGroup :=
      mem_fullSymmetryGroup_of_maps_two_opposite_pairs matching
        rightPriorityOne leftPriorityOne rightSeniorPlane leftSeniorPlane
        leftSeniorPlaneCorrect.1 mapsPriorityOne
        mapsPriorityOneOpposite mapsSeniorPlane mapsSeniorPlaneOpposite
    exact ⟨⟨matching, matchingMember⟩, samePlacement⟩
  · rintro ⟨symmetry, samePlacement⟩
    have symmetryMember := symmetry.2
    have leftLeRight : priorityDigit (left leftPriorityOne) ≤
        priorityDigit (right rightPriorityOne) := by
      have := leftPriorityOneCorrect (symmetry.1 rightPriorityOne)
      simpa [samePlacement, relabel] using this
    have rightLeLeft : priorityDigit (right rightPriorityOne) ≤
        priorityDigit (left leftPriorityOne) := by
      have := rightPriorityOneCorrect (symmetry.1.symm leftPriorityOne)
      simpa [samePlacement, relabel] using this
    have priorityOneSame : left leftPriorityOne = right rightPriorityOne :=
      priorityDigit_injective (le_antisymm leftLeRight rightLeLeft)
    have mapsPriorityOne : symmetry.1 rightPriorityOne = leftPriorityOne := by
      apply leftInjective
      calc
        left (symmetry.1 rightPriorityOne) = right rightPriorityOne := by
          simpa [relabel] using (congrFun samePlacement rightPriorityOne).symm
        _ = left leftPriorityOne := priorityOneSame.symm
    have mapsPriorityOneOpposite :
        symmetry.1 (opposite rightPriorityOne) = opposite leftPriorityOne := by
      rw [symmetryMember, mapsPriorityOne]
    have matchingMapsPerpendicular : ∀ {position},
        PerpendicularTo rightPriorityOne position →
          PerpendicularTo leftPriorityOne (symmetry.1 position) := by
      intro position perpendicular
      exact perpendicular_map_of_maps_opposite_pair symmetry.1 mapsPriorityOne
        mapsPriorityOneOpposite perpendicular
    have inverseMapsPriorityOne :
        symmetry.1.symm leftPriorityOne = rightPriorityOne := by
      apply symmetry.1.injective
      simp [mapsPriorityOne]
    have inverseMapsPriorityOneOpposite :
        symmetry.1.symm (opposite leftPriorityOne) = opposite rightPriorityOne := by
      apply symmetry.1.injective
      simp [mapsPriorityOneOpposite]
    have inverseMapsPerpendicular : ∀ {position},
        PerpendicularTo leftPriorityOne position →
          PerpendicularTo rightPriorityOne (symmetry.1.symm position) := by
      intro position perpendicular
      exact perpendicular_map_of_maps_opposite_pair symmetry.1.symm
        inverseMapsPriorityOne inverseMapsPriorityOneOpposite perpendicular
    have leftPlaneLeRight : priorityDigit (left leftSeniorPlane) ≤
        priorityDigit (right rightSeniorPlane) := by
      have := leftSeniorPlaneCorrect.2 (symmetry.1 rightSeniorPlane)
        (matchingMapsPerpendicular rightSeniorPlaneCorrect.1)
      simpa [samePlacement, relabel] using this
    have rightPlaneLeLeft : priorityDigit (right rightSeniorPlane) ≤
        priorityDigit (left leftSeniorPlane) := by
      have := rightSeniorPlaneCorrect.2 (symmetry.1.symm leftSeniorPlane)
        (inverseMapsPerpendicular leftSeniorPlaneCorrect.1)
      simpa [samePlacement, relabel] using this
    have seniorPlaneSame : left leftSeniorPlane = right rightSeniorPlane :=
      priorityDigit_injective (le_antisymm leftPlaneLeRight rightPlaneLeLeft)
    have mapsSeniorPlane : symmetry.1 rightSeniorPlane = leftSeniorPlane := by
      apply leftInjective
      calc
        left (symmetry.1 rightSeniorPlane) = right rightSeniorPlane := by
          simpa [relabel] using (congrFun samePlacement rightSeniorPlane).symm
        _ = left leftSeniorPlane := seniorPlaneSame.symm
    have firstPart :
        right (opposite rightPriorityOne) = left (opposite leftPriorityOne) := by
      calc
        right (opposite rightPriorityOne) =
            left (symmetry.1 (opposite rightPriorityOne)) := by
          simpa [relabel] using congrFun samePlacement (opposite rightPriorityOne)
        _ = left (opposite (symmetry.1 rightPriorityOne)) := by rw [symmetryMember]
        _ = left (opposite leftPriorityOne) := by rw [mapsPriorityOne]
    have secondPart :
        right (opposite rightSeniorPlane) = left (opposite leftSeniorPlane) := by
      calc
        right (opposite rightSeniorPlane) =
            left (symmetry.1 (opposite rightSeniorPlane)) := by
          simpa [relabel] using congrFun samePlacement (opposite rightSeniorPlane)
        _ = left (opposite (symmetry.1 rightSeniorPlane)) := by rw [symmetryMember]
        _ = left (opposite leftSeniorPlane) := by rw [mapsSeniorPlane]
    simp [sourceIndex, BlueBookP93.octahedronIndex, firstPart, secondPart]

/-- Direct Blue Book spelling of the exact OC-6 theorem. -/
theorem blueBook_octahedronIndex_eq_iff_symmetryEquivalent
    (left right : Position → PriorityNumber)
    (leftPriorityOne rightPriorityOne leftSeniorPlane rightSeniorPlane : Position)
    (leftInjective : Function.Injective left)
    (rightInjective : Function.Injective right)
    (leftPriorityOneCorrect : IsSenior left leftPriorityOne)
    (rightPriorityOneCorrect : IsSenior right rightPriorityOne)
    (leftSeniorPlaneCorrect :
      IsSeniorPerpendicular left leftPriorityOne leftSeniorPlane)
    (rightSeniorPlaneCorrect :
      IsSeniorPerpendicular right rightPriorityOne rightSeniorPlane)
    (sameMultiset : SamePriorityMultiset left right) :
    BlueBookP93.octahedronIndex
        (left (opposite leftPriorityOne)) (left (opposite leftSeniorPlane)) =
      BlueBookP93.octahedronIndex
        (right (opposite rightPriorityOne)) (right (opposite rightSeniorPlane)) ↔
      OctahedronEquivalent left right :=
  octahedronIndex_eq_iff_symmetryEquivalent_of_samePriorityMultiset
    left right leftPriorityOne rightPriorityOne leftSeniorPlane rightSeniorPlane
    leftInjective rightInjective leftPriorityOneCorrect rightPriorityOneCorrect
    leftSeniorPlaneCorrect rightSeniorPlaneCorrect sameMultiset

/-! ## Production refinement -/

theorem priorityOfProduction_injective :
    Function.Injective BlueBookP93.priorityOfProduction := by
  intro left right same
  cases left
  cases right
  simp [BlueBookP93.priorityOfProduction] at same
  simp_all

/-- The executable two-entry OC-6 constructor has the same exact collision boundary as the
independent source index. -/
theorem productionOctahedronConfigurationIndex_eq_iff_symmetryEquivalent
    (left right : Position → PolyhedralPriorityNumber)
    (leftPriorityOne rightPriorityOne leftSeniorPlane rightSeniorPlane : Position)
    (leftInjective : Function.Injective left)
    (rightInjective : Function.Injective right)
    (leftPriorityOneCorrect : IsSenior
      (fun position => BlueBookP93.priorityOfProduction (left position)) leftPriorityOne)
    (rightPriorityOneCorrect : IsSenior
      (fun position => BlueBookP93.priorityOfProduction (right position)) rightPriorityOne)
    (leftSeniorPlaneCorrect : IsSeniorPerpendicular
      (fun position => BlueBookP93.priorityOfProduction (left position))
      leftPriorityOne leftSeniorPlane)
    (rightSeniorPlaneCorrect : IsSeniorPerpendicular
      (fun position => BlueBookP93.priorityOfProduction (right position))
      rightPriorityOne rightSeniorPlane)
    (sameMultiset : SamePriorityMultiset
      (fun position => BlueBookP93.priorityOfProduction (left position))
      (fun position => BlueBookP93.priorityOfProduction (right position))) :
    octahedronConfigurationIndex
        (left (opposite leftPriorityOne)) (left (opposite leftSeniorPlane)) =
      octahedronConfigurationIndex
        (right (opposite rightPriorityOne)) (right (opposite rightSeniorPlane)) ↔
      OctahedronEquivalent
        (fun position => BlueBookP93.priorityOfProduction (left position))
        (fun position => BlueBookP93.priorityOfProduction (right position)) := by
  let leftSource := fun position => BlueBookP93.priorityOfProduction (left position)
  let rightSource := fun position => BlueBookP93.priorityOfProduction (right position)
  have leftSourceInjective : Function.Injective leftSource :=
    priorityOfProduction_injective.comp leftInjective
  have rightSourceInjective : Function.Injective rightSource :=
    priorityOfProduction_injective.comp rightInjective
  have exactSource :=
    octahedronIndex_eq_iff_symmetryEquivalent_of_samePriorityMultiset
      leftSource rightSource leftPriorityOne rightPriorityOne leftSeniorPlane rightSeniorPlane
      leftSourceInjective rightSourceInjective leftPriorityOneCorrect rightPriorityOneCorrect
      leftSeniorPlaneCorrect rightSeniorPlaneCorrect sameMultiset
  constructor
  · intro sameProduction
    apply exactSource.mp
    have mappedSame := congrArg (List.map BlueBookP93.priorityOfProduction) sameProduction
    simpa [leftSource, rightSource, sourceIndex,
      octahedronConfigurationIndex, BlueBookP93.octahedronIndex] using mappedSame
  · intro equivalent
    have sameSource := exactSource.mpr equivalent
    have parts :
        BlueBookP93.priorityOfProduction (left (opposite leftPriorityOne)) =
            BlueBookP93.priorityOfProduction (right (opposite rightPriorityOne)) ∧
          BlueBookP93.priorityOfProduction (left (opposite leftSeniorPlane)) =
            BlueBookP93.priorityOfProduction (right (opposite rightSeniorPlane)) := by
      simpa [leftSource, rightSource, sourceIndex,
        BlueBookP93.octahedronIndex] using sameSource
    have productionParts :
        left (opposite leftPriorityOne) = right (opposite rightPriorityOne) ∧
          left (opposite leftSeniorPlane) = right (opposite rightSeniorPlane) :=
      ⟨priorityOfProduction_injective parts.1,
        priorityOfProduction_injective parts.2⟩
    simpa [octahedronConfigurationIndex] using productionParts

end TetraStereo.OneCenter.RedBookIR9.OctahedronSourceIndexCompleteness
