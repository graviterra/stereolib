import TetraStereo.OneCenter.P94ExecutableCoordinateRingGeometry

set_option autoImplicit false

namespace TetraStereo.OneCenter

open BlueBookP94

namespace BlueBookP94.ExecutableRingFamilySelection

/-!
# Executable P-94 ring-family selection

These classifiers consume the exact plane-side ledger produced by the executable coordinate
layer.  Their patterns are literal Boolean versions of the P-94 envelope, chair, and boat
relations, with exact reflection theorems and a deterministic chair/boat selector.
-/

/-- Executable five-ring envelope classifier. -/
def isEnvelope? (sides : List PlaneSide) : Bool :=
  sides.length == 5 && sides.count .onPlane == 4

@[simp] theorem isEnvelope?_eq_true_iff (sides : List PlaneSide) :
    isEnvelope? sides = true ↔ IsEnvelope sides := by
  simp [isEnvelope?, IsEnvelope]

/-- Executable opposite-side relation. -/
def oppositeSides? : PlaneSide → PlaneSide → Bool
  | .positive, .negative | .negative, .positive => true
  | _, _ => false

@[simp] theorem oppositeSides?_eq_true_iff (left right : PlaneSide) :
    oppositeSides? left right = true ↔ OppositeSides left right := by
  cases left <;> cases right <;> simp [oppositeSides?, OppositeSides]

/-- Executable same-off-plane-side relation. -/
def sameOffPlaneSide? : PlaneSide → PlaneSide → Bool
  | .positive, .positive | .negative, .negative => true
  | _, _ => false

@[simp] theorem sameOffPlaneSide?_eq_true_iff (left right : PlaneSide) :
    sameOffPlaneSide? left right = true ↔ SameOffPlaneSide left right := by
  cases left <;> cases right <;> simp [sameOffPlaneSide?, SameOffPlaneSide]

/-- Literal executable carbohydrate five-ring twist pattern at a chosen cyclic offset. -/
def isCarbohydrateFiveRingTwist? : List PlaneSide → Bool
  | [.onPlane, .onPlane, .onPlane, firstRemote, secondRemote] =>
      oppositeSides? firstRemote secondRemote
  | _ => false

@[simp] theorem isCarbohydrateFiveRingTwist?_eq_true_iff (sides : List PlaneSide) :
    isCarbohydrateFiveRingTwist? sides = true ↔
      IsCarbohydrateFiveRingTwist sides := by
  rcases sides with _ | ⟨side0, tail0⟩
  · simp [isCarbohydrateFiveRingTwist?, IsCarbohydrateFiveRingTwist]
  rcases tail0 with _ | ⟨side1, tail1⟩
  · simp [isCarbohydrateFiveRingTwist?, IsCarbohydrateFiveRingTwist]
  rcases tail1 with _ | ⟨side2, tail2⟩
  · simp [isCarbohydrateFiveRingTwist?, IsCarbohydrateFiveRingTwist]
  rcases tail2 with _ | ⟨side3, tail3⟩
  · simp [isCarbohydrateFiveRingTwist?, IsCarbohydrateFiveRingTwist]
  rcases tail3 with _ | ⟨side4, tail4⟩
  · simp [isCarbohydrateFiveRingTwist?, IsCarbohydrateFiveRingTwist]
  rcases tail4 with _ | ⟨extra, rest⟩
  · by_cases side0On : side0 = .onPlane
    · by_cases side1On : side1 = .onPlane
      · by_cases side2On : side2 = .onPlane
        · subst side0
          subst side1
          subst side2
          simp [isCarbohydrateFiveRingTwist?, IsCarbohydrateFiveRingTwist]
        · simp [isCarbohydrateFiveRingTwist?, IsCarbohydrateFiveRingTwist,
            side0On, side1On, side2On]
      · simp [isCarbohydrateFiveRingTwist?, IsCarbohydrateFiveRingTwist,
          side0On, side1On]
    · simp [isCarbohydrateFiveRingTwist?, IsCarbohydrateFiveRingTwist, side0On]
  · simp [isCarbohydrateFiveRingTwist?, IsCarbohydrateFiveRingTwist]

/-- Executable exact half-chair observation classifier. -/
def isHalfChair? (observation : HalfChairObservation) : Bool :=
  decide (observation.ringSize = 6) &&
    decide (observation.doubleBondCount = 1) &&
      oppositeSides? observation.firstRemoteSide observation.secondRemoteSide

@[simp] theorem isHalfChair?_eq_true_iff (observation : HalfChairObservation) :
    isHalfChair? observation = true ↔ IsHalfChair observation := by
  simp [isHalfChair?, IsHalfChair]
  tauto

/-- Practical descriptor selection for a derived carbohydrate twist ledger. -/
def executableCarbohydrateTwistDescriptor? (sides : List PlaneSide) :
    Option P94ConformationDescriptor :=
  if isCarbohydrateFiveRingTwist? sides then some .twist else none

@[simp] theorem executableCarbohydrateTwistDescriptor?_eq_some_iff
    (sides : List PlaneSide) :
    executableCarbohydrateTwistDescriptor? sides = some .twist ↔
      IsCarbohydrateFiveRingTwist sides := by
  simp [executableCarbohydrateTwistDescriptor?]

@[simp] theorem executableCarbohydrateTwistDescriptor?_eq_none_iff
    (sides : List PlaneSide) :
    executableCarbohydrateTwistDescriptor? sides = none ↔
      ¬IsCarbohydrateFiveRingTwist sides := by
  by_cases twist : IsCarbohydrateFiveRingTwist sides
  · simp [executableCarbohydrateTwistDescriptor?, twist,
      (isCarbohydrateFiveRingTwist?_eq_true_iff sides).mpr twist]
  · have twistFalse : isCarbohydrateFiveRingTwist? sides = false :=
      Bool.eq_false_of_not_eq_true
        (fun accepted => twist ((isCarbohydrateFiveRingTwist?_eq_true_iff sides).mp accepted))
    simp [executableCarbohydrateTwistDescriptor?, twist, twistFalse]

/-- Practical descriptor selection for a molecule-derived half-chair observation. -/
def executableHalfChairDescriptor? (observation : HalfChairObservation) :
    Option P94ConformationDescriptor :=
  if isHalfChair? observation then some .halfChair else none

@[simp] theorem executableHalfChairDescriptor?_eq_some_iff
    (observation : HalfChairObservation) :
    executableHalfChairDescriptor? observation = some .halfChair ↔
      IsHalfChair observation := by
  simp [executableHalfChairDescriptor?]

@[simp] theorem executableHalfChairDescriptor?_eq_none_iff
    (observation : HalfChairObservation) :
    executableHalfChairDescriptor? observation = none ↔ ¬IsHalfChair observation := by
  by_cases halfChair : IsHalfChair observation
  · simp [executableHalfChairDescriptor?, halfChair,
      (isHalfChair?_eq_true_iff observation).mpr halfChair]
  · have halfChairFalse : isHalfChair? observation = false :=
      Bool.eq_false_of_not_eq_true
        (fun accepted => halfChair ((isHalfChair?_eq_true_iff observation).mp accepted))
    simp [executableHalfChairDescriptor?, halfChair, halfChairFalse]

/-- Public literal meaning of the eight-ring tub pattern at one fixed cyclic offset. -/
def TubPatternMeaning (sides : List PlaneSide) : Prop :=
  sides.length = 8 ∧
    sides[0]? = some .onPlane ∧ sides[1]? = some .onPlane ∧
    sides[4]? = some .onPlane ∧ sides[5]? = some .onPlane ∧
    ((sides[2]? = some .positive ∧ sides[3]? = some .positive ∧
        sides[6]? = some .positive ∧ sides[7]? = some .positive) ∨
      (sides[2]? = some .negative ∧ sides[3]? = some .negative ∧
        sides[6]? = some .negative ∧ sides[7]? = some .negative))

/-- Executable literal tub pattern at one fixed offset. -/
def isTubPattern? : List PlaneSide → Bool
  | [.onPlane, .onPlane, side2, side3, .onPlane, .onPlane, side6, side7] =>
      (side2 == .positive && side3 == .positive &&
          side6 == .positive && side7 == .positive) ||
        (side2 == .negative && side3 == .negative &&
          side6 == .negative && side7 == .negative)
  | _ => false

@[simp] theorem isTubPattern?_eq_true_iff (sides : List PlaneSide) :
    isTubPattern? sides = true ↔ TubPatternMeaning sides := by
  rcases sides with _ | ⟨side0, tail0⟩
  · simp [isTubPattern?, TubPatternMeaning]
  rcases tail0 with _ | ⟨side1, tail1⟩
  · simp [isTubPattern?, TubPatternMeaning]
  rcases tail1 with _ | ⟨side2, tail2⟩
  · simp [isTubPattern?, TubPatternMeaning]
  rcases tail2 with _ | ⟨side3, tail3⟩
  · simp [isTubPattern?, TubPatternMeaning]
  rcases tail3 with _ | ⟨side4, tail4⟩
  · simp [isTubPattern?, TubPatternMeaning]
  rcases tail4 with _ | ⟨side5, tail5⟩
  · simp [isTubPattern?, TubPatternMeaning]
  rcases tail5 with _ | ⟨side6, tail6⟩
  · simp [isTubPattern?, TubPatternMeaning]
  rcases tail6 with _ | ⟨side7, tail7⟩
  · simp [isTubPattern?, TubPatternMeaning]
  rcases tail7 with _ | ⟨extra, rest⟩
  · by_cases side0On : side0 = .onPlane
    · by_cases side1On : side1 = .onPlane
      · by_cases side4On : side4 = .onPlane
        · by_cases side5On : side5 = .onPlane
          · subst side0
            subst side1
            subst side4
            subst side5
            simp [isTubPattern?, TubPatternMeaning, and_assoc]
          · simp [isTubPattern?, TubPatternMeaning,
              side0On, side1On, side4On, side5On]
        · simp [isTubPattern?, TubPatternMeaning, side0On, side1On, side4On]
      · simp [isTubPattern?, TubPatternMeaning, side0On, side1On]
    · simp [isTubPattern?, TubPatternMeaning, side0On]
  · simp [isTubPattern?, TubPatternMeaning]

/-- The private source transcription of a tub is equivalent to the public literal pattern. -/
theorem isTub_iff_exists_tubPatternMeaning (sides : List PlaneSide) :
    IsTub sides ↔ ∃ offset, TubPatternMeaning (sides.rotate offset) := by
  unfold IsTub
  constructor
  · rintro ⟨offset, lengthEight, side0, side1, side4, side5,
      offSide, offChoice, side2, side3, side6, side7⟩
    refine ⟨offset, lengthEight, side0, side1, side4, side5, ?_⟩
    rcases offChoice with rfl | rfl
    · exact .inl ⟨side2, side3, side6, side7⟩
    · exact .inr ⟨side2, side3, side6, side7⟩
  · rintro ⟨offset, lengthEight, side0, side1, side4, side5, pattern⟩
    refine ⟨offset, lengthEight, side0, side1, side4, side5, ?_⟩
    rcases pattern with positive | negative
    · exact ⟨.positive, .inl rfl, positive⟩
    · exact ⟨.negative, .inr rfl, negative⟩

/-- Bounded complete cyclic-offset search for the P-94 tub pattern. -/
def isTub? (sides : List PlaneSide) : Bool :=
  (List.range sides.length).any fun offset => isTubPattern? (sides.rotate offset)

@[simp] theorem isTub?_eq_true_iff (sides : List PlaneSide) :
    isTub? sides = true ↔ IsTub sides := by
  rw [isTub_iff_exists_tubPatternMeaning]
  constructor
  · intro accepted
    rw [isTub?, List.any_eq_true] at accepted
    rcases accepted with ⟨offset, offsetPresent, patternAccepted⟩
    exact ⟨offset, (isTubPattern?_eq_true_iff _).mp patternAccepted⟩
  · rintro ⟨offset, pattern⟩
    have lengthEight : sides.length = 8 := by
      have rotatedLength := pattern.1
      simpa using rotatedLength
    have lengthPositive : 0 < sides.length := by omega
    rw [isTub?, List.any_eq_true]
    refine ⟨offset % sides.length, List.mem_range.mpr (Nat.mod_lt _ lengthPositive), ?_⟩
    apply (isTubPattern?_eq_true_iff _).mpr
    simpa [List.rotate_mod] using pattern

/-- Practical descriptor selection for a derived tub side ledger. -/
def executableTubDescriptor? (sides : List PlaneSide) : Option P94ConformationDescriptor :=
  if isTub? sides then some .tub else none

@[simp] theorem executableTubDescriptor?_eq_some_iff (sides : List PlaneSide) :
    executableTubDescriptor? sides = some .tub ↔ IsTub sides := by
  simp [executableTubDescriptor?]

@[simp] theorem executableTubDescriptor?_eq_none_iff (sides : List PlaneSide) :
    executableTubDescriptor? sides = none ↔ ¬IsTub sides := by
  by_cases tub : IsTub sides
  · simp [executableTubDescriptor?, tub, (isTub?_eq_true_iff sides).mpr tub]
  · have tubFalse : isTub? sides = false := Bool.eq_false_of_not_eq_true
      (fun accepted => tub ((isTub?_eq_true_iff sides).mp accepted))
    simp [executableTubDescriptor?, tub, tubFalse]

/-- Literal executable P-94 chair pattern in ring-traversal order. -/
def isChair? : List PlaneSide → Bool
  | [.onPlane, .onPlane, side3, .onPlane, .onPlane, side6] =>
      oppositeSides? side3 side6
  | _ => false

/-- Literal executable P-94 boat pattern in ring-traversal order. -/
def isBoat? : List PlaneSide → Bool
  | [.onPlane, .onPlane, side3, .onPlane, .onPlane, side6] =>
      sameOffPlaneSide? side3 side6
  | _ => false

@[simp] theorem isChair?_eq_true_iff (sides : List PlaneSide) :
    isChair? sides = true ↔ IsChair sides := by
  rcases sides with _ | ⟨side0, tail0⟩
  · simp [isChair?, IsChair, SixRingReferencePlane]
  rcases tail0 with _ | ⟨side1, tail1⟩
  · simp [isChair?, IsChair, SixRingReferencePlane]
  rcases tail1 with _ | ⟨side2, tail2⟩
  · simp [isChair?, IsChair, SixRingReferencePlane]
  rcases tail2 with _ | ⟨side3, tail3⟩
  · simp [isChair?, IsChair, SixRingReferencePlane]
  rcases tail3 with _ | ⟨side4, tail4⟩
  · simp [isChair?, IsChair, SixRingReferencePlane]
  rcases tail4 with _ | ⟨side5, tail5⟩
  · simp [isChair?, IsChair, SixRingReferencePlane]
  rcases tail5 with _ | ⟨extra, rest⟩
  · by_cases side0On : side0 = .onPlane
    · by_cases side1On : side1 = .onPlane
      · by_cases side3On : side3 = .onPlane
        · by_cases side4On : side4 = .onPlane
          · subst side0
            subst side1
            subst side3
            subst side4
            simp [isChair?, IsChair, SixRingReferencePlane]
          · simp [isChair?, IsChair, SixRingReferencePlane, side0On, side1On,
              side3On, side4On]
        · simp [isChair?, IsChair, SixRingReferencePlane, side0On, side1On, side3On]
      · simp [isChair?, IsChair, SixRingReferencePlane, side0On, side1On]
    · simp [isChair?, IsChair, SixRingReferencePlane, side0On]
  · simp [isChair?, IsChair, SixRingReferencePlane]

@[simp] theorem isBoat?_eq_true_iff (sides : List PlaneSide) :
    isBoat? sides = true ↔ IsBoat sides := by
  rcases sides with _ | ⟨side0, tail0⟩
  · simp [isBoat?, IsBoat, SixRingReferencePlane]
  rcases tail0 with _ | ⟨side1, tail1⟩
  · simp [isBoat?, IsBoat, SixRingReferencePlane]
  rcases tail1 with _ | ⟨side2, tail2⟩
  · simp [isBoat?, IsBoat, SixRingReferencePlane]
  rcases tail2 with _ | ⟨side3, tail3⟩
  · simp [isBoat?, IsBoat, SixRingReferencePlane]
  rcases tail3 with _ | ⟨side4, tail4⟩
  · simp [isBoat?, IsBoat, SixRingReferencePlane]
  rcases tail4 with _ | ⟨side5, tail5⟩
  · simp [isBoat?, IsBoat, SixRingReferencePlane]
  rcases tail5 with _ | ⟨extra, rest⟩
  · by_cases side0On : side0 = .onPlane
    · by_cases side1On : side1 = .onPlane
      · by_cases side3On : side3 = .onPlane
        · by_cases side4On : side4 = .onPlane
          · subst side0
            subst side1
            subst side3
            subst side4
            simp [isBoat?, IsBoat, SixRingReferencePlane]
          · simp [isBoat?, IsBoat, SixRingReferencePlane, side0On, side1On,
              side3On, side4On]
        · simp [isBoat?, IsBoat, SixRingReferencePlane, side0On, side1On, side3On]
      · simp [isBoat?, IsBoat, SixRingReferencePlane, side0On, side1On]
    · simp [isBoat?, IsBoat, SixRingReferencePlane, side0On]
  · simp [isBoat?, IsBoat, SixRingReferencePlane]

/-- Practical envelope selector on an already derived exact side ledger. -/
def executableEnvelopeDescriptor? (sides : List PlaneSide) :
    Option P94ConformationDescriptor :=
  if isEnvelope? sides then some .envelope else none

@[simp] theorem executableEnvelopeDescriptor?_eq_some_iff (sides : List PlaneSide) :
    executableEnvelopeDescriptor? sides = some .envelope ↔ IsEnvelope sides := by
  simp [executableEnvelopeDescriptor?, isEnvelope?_eq_true_iff]

@[simp] theorem executableEnvelopeDescriptor?_eq_none_iff (sides : List PlaneSide) :
    executableEnvelopeDescriptor? sides = none ↔ ¬IsEnvelope sides := by
  by_cases envelope : IsEnvelope sides
  · simp [executableEnvelopeDescriptor?, envelope,
      (isEnvelope?_eq_true_iff sides).mpr envelope]
  · have envelopeFalse : isEnvelope? sides = false := by
      exact Bool.eq_false_of_not_eq_true (fun accepted =>
        envelope ((isEnvelope?_eq_true_iff sides).mp accepted))
    simp [executableEnvelopeDescriptor?, envelope, envelopeFalse]

/-- Deterministic six-ring selector.  The source predicates are disjoint, so checking chair first
does not hide a valid boat result. -/
def executableSixRingDescriptor? (sides : List PlaneSide) :
    Option P94ConformationDescriptor :=
  if isChair? sides then some .chair
  else if isBoat? sides then some .boat
  else none

@[simp] theorem executableSixRingDescriptor?_eq_chair_iff (sides : List PlaneSide) :
    executableSixRingDescriptor? sides = some .chair ↔ IsChair sides := by
  by_cases chair : IsChair sides
  · simp [executableSixRingDescriptor?, chair,
      (isChair?_eq_true_iff sides).mpr chair]
  · have chairFalse : isChair? sides = false := by
      exact Bool.eq_false_of_not_eq_true (fun accepted =>
        chair ((isChair?_eq_true_iff sides).mp accepted))
    simp [executableSixRingDescriptor?, chair, chairFalse]

@[simp] theorem executableSixRingDescriptor?_eq_boat_iff (sides : List PlaneSide) :
    executableSixRingDescriptor? sides = some .boat ↔ IsBoat sides := by
  by_cases boat : IsBoat sides
  · have notChair : ¬IsChair sides := by
      intro chair
      exact chair_not_boat sides chair boat
    have chairFalse : isChair? sides = false := by
      exact Bool.eq_false_of_not_eq_true (fun accepted =>
        notChair ((isChair?_eq_true_iff sides).mp accepted))
    simp [executableSixRingDescriptor?, boat, chairFalse,
      (isBoat?_eq_true_iff sides).mpr boat]
  · have boatFalse : isBoat? sides = false := by
      exact Bool.eq_false_of_not_eq_true (fun accepted =>
        boat ((isBoat?_eq_true_iff sides).mp accepted))
    simp [executableSixRingDescriptor?, boat, boatFalse]

@[simp] theorem executableSixRingDescriptor?_eq_none_iff (sides : List PlaneSide) :
    executableSixRingDescriptor? sides = none ↔
      ¬IsChair sides ∧ ¬IsBoat sides := by
  by_cases chair : IsChair sides
  · simp [executableSixRingDescriptor?, chair,
      (isChair?_eq_true_iff sides).mpr chair]
  · have chairFalse : isChair? sides = false := by
      exact Bool.eq_false_of_not_eq_true (fun accepted =>
        chair ((isChair?_eq_true_iff sides).mp accepted))
    by_cases boat : IsBoat sides
    · simp [executableSixRingDescriptor?, chair, boat, chairFalse,
        (isBoat?_eq_true_iff sides).mpr boat]
    · have boatFalse : isBoat? sides = false := by
        exact Bool.eq_false_of_not_eq_true (fun accepted =>
          boat ((isBoat?_eq_true_iff sides).mp accepted))
      simp [executableSixRingDescriptor?, chair, boat, chairFalse, boatFalse]

end BlueBookP94.ExecutableRingFamilySelection
end TetraStereo.OneCenter
