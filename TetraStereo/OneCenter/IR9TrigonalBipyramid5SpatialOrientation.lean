import TetraStereo.OneCenter.IR9TrigonalBipyramid5SpatialPerception
import TetraStereo.OneCenter.IR9SeeSawSpatialOrientation

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.TrigonalBipyramid5SpatialOrientation

open FourCoordinateSpatialRoles
open SeeSawSpatialOrientation
open TrigonalBipyramid5SpatialPerception

abbrev Frame := TrigonalBipyramid5SpatialPerception.Frame

/-!
# Exact physical A/C progression for idealized TBPY-5

The senior axial donor is the viewpoint.  In the equatorial plane, the reading begins at the
strict CIP-senior donor and proceeds toward the senior of the remaining two donors.  The sign of
the exact scalar triple product determines counterclockwise/A versus clockwise/C.  Axial or
equatorial priority ties, a zero determinant, or an absent exact partition are refused.
-/

/-- Strict priority order on the perceived axial pair. -/
def strictOrderAxialPair?
    (placement : Fin 5 → PolyhedralPriorityNumber) (pair : Fin 5 × Fin 5) :
    Option (Fin 5 × Fin 5) :=
  if (placement pair.1).outranks (placement pair.2) then
    some pair
  else if (placement pair.2).outranks (placement pair.1) then
    some (pair.2, pair.1)
  else none

def IsStrictAxialOrder
    (placement : Fin 5 → PolyhedralPriorityNumber)
    (pair ordered : Fin 5 × Fin 5) : Prop :=
  (ordered = pair ∧ (placement pair.1).outranks (placement pair.2) = true) ∨
    (ordered = (pair.2, pair.1) ∧
      (placement pair.2).outranks (placement pair.1) = true)

theorem strictOrderAxialPair?_eq_some_iff
    (placement : Fin 5 → PolyhedralPriorityNumber)
    (pair ordered : Fin 5 × Fin 5) :
    strictOrderAxialPair? placement pair = some ordered ↔
      IsStrictAxialOrder placement pair ordered := by
  unfold strictOrderAxialPair? IsStrictAxialOrder
  by_cases forward : (placement pair.1).outranks (placement pair.2) = true
  · have reverse := outranks_asymmetric forward
    simp [forward, reverse, eq_comm]
  · have forwardFalse : (placement pair.1).outranks (placement pair.2) = false :=
      Bool.eq_false_of_not_eq_true forward
    by_cases reverse : (placement pair.2).outranks (placement pair.1) = true
    · simp [forwardFalse, reverse, eq_comm]
    · have reverseFalse : (placement pair.2).outranks (placement pair.1) = false :=
        Bool.eq_false_of_not_eq_true reverse
      simp [forwardFalse, reverseFalse]

theorem axialOrder_first_is_viewpoint
    {placement : Fin 5 → PolyhedralPriorityNumber}
    {pair ordered : Fin 5 × Fin 5}
    (strict : IsStrictAxialOrder placement pair ordered) :
    ordered.1 = pair.1 ∨ ordered.1 = pair.2 := by
  rcases strict with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

def equatorialPlacement
    (placement : Fin 5 → PolyhedralPriorityNumber) (pair : Fin 5 × Fin 5) :
    Fin 3 → PolyhedralPriorityNumber :=
  fun position => placement (equatorialOriginalPosition pair position)

def positions3 : List (Fin 3) := [0, 1, 2]

@[simp] theorem mem_positions3 (position : Fin 3) : position ∈ positions3 := by
  fin_cases position <;> simp [positions3]

theorem positions3_nodup : positions3.Nodup := by decide

def IsStrictSenior3
    (placement : Fin 3 → PolyhedralPriorityNumber) (senior : Fin 3) : Prop :=
  ∀ other, other ≠ senior →
    (placement senior).outranks (placement other) = true

def isStrictSenior3?
    (placement : Fin 3 → PolyhedralPriorityNumber) (senior : Fin 3) : Bool :=
  positions3.all fun other =>
    other == senior || (placement senior).outranks (placement other)

theorem isStrictSenior3?_eq_true_iff
    (placement : Fin 3 → PolyhedralPriorityNumber) (senior : Fin 3) :
    isStrictSenior3? placement senior = true ↔ IsStrictSenior3 placement senior := by
  simp only [isStrictSenior3?, List.all_eq_true, Bool.or_eq_true, beq_iff_eq]
  constructor
  · intro checked other different
    rcases checked other (mem_positions3 other) with same | outranks
    · exact (different same).elim
    · exact outranks
  · intro seniority other _
    by_cases same : other = senior
    · exact Or.inl same
    · exact Or.inr (seniority other same)

def strictSeniorPosition3?
    (placement : Fin 3 → PolyhedralPriorityNumber) : Option (Fin 3) :=
  uniqueSatisfying? positions3 (isStrictSenior3? placement)

theorem strictSeniorPosition3?_eq_some_iff
    (placement : Fin 3 → PolyhedralPriorityNumber) (senior : Fin 3) :
    strictSeniorPosition3? placement = some senior ↔
      IsStrictSenior3 placement senior := by
  rw [strictSeniorPosition3?, uniqueSatisfying?_eq_some_iff positions3
    (isStrictSenior3? placement) positions3_nodup senior]
  simp only [mem_positions3, true_and, isStrictSenior3?_eq_true_iff]
  constructor
  · exact fun result => result.1
  · intro seniority
    refine ⟨seniority, ?_⟩
    intro other _ otherSeniority
    by_contra different
    have seniorOverOther := seniority other different
    have otherOverSenior := otherSeniority senior (Ne.symm different)
    rw [outranks_asymmetric seniorOverOther] at otherOverSenior
    contradiction

/-- The two normalized equatorial sites outside the strict senior. -/
def remainingPair3? (senior : Fin 3) : Option (Fin 3 × Fin 3) :=
  match senior with
  | 0 => some (1, 2)
  | 1 => some (0, 2)
  | 2 => some (0, 1)

theorem remainingPair3?_eq_some_iff
    (senior : Fin 3) (pair : Fin 3 × Fin 3) :
    remainingPair3? senior = some pair ↔
      (senior = 0 ∧ pair = (1, 2)) ∨
      (senior = 1 ∧ pair = (0, 2)) ∨
      (senior = 2 ∧ pair = (0, 1)) := by
  fin_cases senior <;> simp [remainingPair3?, eq_comm]

theorem remainingPair3_members_ne_senior
    {senior : Fin 3} {pair : Fin 3 × Fin 3}
    (computed : remainingPair3? senior = some pair) :
    pair.1 ≠ senior ∧ pair.2 ≠ senior ∧ pair.1 ≠ pair.2 := by
  fin_cases senior <;> simp [remainingPair3?] at computed <;>
    subst pair <;> decide

def strictOrderEquatorialPair?
    (placement : Fin 3 → PolyhedralPriorityNumber) (pair : Fin 3 × Fin 3) :
    Option (Fin 3 × Fin 3) :=
  if (placement pair.1).outranks (placement pair.2) then
    some pair
  else if (placement pair.2).outranks (placement pair.1) then
    some (pair.2, pair.1)
  else none

def IsStrictEquatorialOrder
    (placement : Fin 3 → PolyhedralPriorityNumber)
    (pair ordered : Fin 3 × Fin 3) : Prop :=
  (ordered = pair ∧ (placement pair.1).outranks (placement pair.2) = true) ∨
    (ordered = (pair.2, pair.1) ∧
      (placement pair.2).outranks (placement pair.1) = true)

theorem strictOrderEquatorialPair?_eq_some_iff
    (placement : Fin 3 → PolyhedralPriorityNumber)
    (pair ordered : Fin 3 × Fin 3) :
    strictOrderEquatorialPair? placement pair = some ordered ↔
      IsStrictEquatorialOrder placement pair ordered := by
  unfold strictOrderEquatorialPair? IsStrictEquatorialOrder
  by_cases forward : (placement pair.1).outranks (placement pair.2) = true
  · have reverse := outranks_asymmetric forward
    simp [forward, reverse, eq_comm]
  · have forwardFalse : (placement pair.1).outranks (placement pair.2) = false :=
      Bool.eq_false_of_not_eq_true forward
    by_cases reverse : (placement pair.2).outranks (placement pair.1) = true
    · simp [forwardFalse, reverse, eq_comm]
    · have reverseFalse : (placement pair.2).outranks (placement pair.1) = false :=
        Bool.eq_false_of_not_eq_true reverse
      simp [forwardFalse, reverseFalse]

theorem equatorialOrder_first_ne_senior
    {placement : Fin 3 → PolyhedralPriorityNumber}
    {senior : Fin 3} {pair ordered : Fin 3 × Fin 3}
    (remaining : remainingPair3? senior = some pair)
    (strict : IsStrictEquatorialOrder placement pair ordered) :
    senior ≠ ordered.1 := by
  have members := remainingPair3_members_ne_senior remaining
  rcases strict with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact members.1.symm
  · exact members.2.1.symm

def senseOfDeterminant? (determinant : ℚ) : Option PolyhedralRotationSense :=
  SeeSawSpatialOrientation.senseOfDeterminant? determinant

theorem senseOfDeterminant?_eq_some_iff
    (determinant : ℚ) (sense : PolyhedralRotationSense) :
    senseOfDeterminant? determinant = some sense ↔
      (sense = .counterclockwise ∧ 0 < determinant) ∨
      (sense = .clockwise ∧ determinant < 0) :=
  SeeSawSpatialOrientation.senseOfDeterminant?_eq_some_iff determinant sense

/-- Fully coordinate- and priority-derived TBPY-5 physical rotation sense. -/
def rotationSense?
    (frame : Frame) (pair : Fin 5 × Fin 5)
    (placement : Fin 5 → PolyhedralPriorityNumber) :
    Option PolyhedralRotationSense := do
  let axialOrder ← strictOrderAxialPair? placement pair
  let equatorial := equatorialPlacement placement pair
  let senior ← strictSeniorPosition3? equatorial
  let remaining ← remainingPair3? senior
  let remainingOrder ← strictOrderEquatorialPair? equatorial remaining
  senseOfDeterminant?
    (TrigonalBipyramid5SpatialPerception.progressionDeterminant
      frame pair axialOrder.1 senior remainingOrder.1)

/-- Independent operational meaning of the TBPY-5 axial viewpoint and equatorial reading. -/
def Judgment
    (frame : Frame) (pair : Fin 5 × Fin 5)
    (placement : Fin 5 → PolyhedralPriorityNumber)
    (sense : PolyhedralRotationSense) : Prop :=
  ∃ axialOrder senior remaining remainingOrder,
    IsStrictAxialOrder placement pair axialOrder ∧
    IsStrictSenior3 (equatorialPlacement placement pair) senior ∧
    remainingPair3? senior = some remaining ∧
    IsStrictEquatorialOrder
      (equatorialPlacement placement pair) remaining remainingOrder ∧
    ((sense = .counterclockwise ∧
        0 < TrigonalBipyramid5SpatialPerception.progressionDeterminant
          frame pair axialOrder.1 senior remainingOrder.1) ∨
      (sense = .clockwise ∧
        TrigonalBipyramid5SpatialPerception.progressionDeterminant
          frame pair axialOrder.1 senior remainingOrder.1 < 0))

theorem rotationSense?_eq_some_iff
    (frame : Frame) (pair : Fin 5 × Fin 5)
    (placement : Fin 5 → PolyhedralPriorityNumber)
    (sense : PolyhedralRotationSense) :
    rotationSense? frame pair placement = some sense ↔
      Judgment frame pair placement sense := by
  constructor
  · intro computed
    unfold rotationSense? at computed
    cases axialEq : strictOrderAxialPair? placement pair with
    | none => simp [axialEq] at computed
    | some axialOrder =>
        let equatorial := equatorialPlacement placement pair
        cases seniorEq : strictSeniorPosition3? equatorial with
        | none => simp [axialEq, equatorial, seniorEq] at computed
        | some senior =>
            cases remainingEq : remainingPair3? senior with
            | none => simp [axialEq, equatorial, seniorEq, remainingEq] at computed
            | some remaining =>
                cases orderEq : strictOrderEquatorialPair? equatorial remaining with
                | none =>
                    simp [axialEq, equatorial, seniorEq, remainingEq, orderEq] at computed
                | some remainingOrder =>
                    have sign := (senseOfDeterminant?_eq_some_iff _ sense).mp
                      (show senseOfDeterminant?
                          (TrigonalBipyramid5SpatialPerception.progressionDeterminant
                            frame pair axialOrder.1 senior remainingOrder.1) = some sense by
                        simpa [axialEq, equatorial, seniorEq, remainingEq, orderEq]
                          using computed)
                    exact ⟨axialOrder, senior, remaining, remainingOrder,
                      (strictOrderAxialPair?_eq_some_iff placement pair axialOrder).mp axialEq,
                      (strictSeniorPosition3?_eq_some_iff equatorial senior).mp seniorEq,
                      remainingEq,
                      (strictOrderEquatorialPair?_eq_some_iff
                        equatorial remaining remainingOrder).mp orderEq,
                      sign⟩
  · rintro ⟨axialOrder, senior, remaining, remainingOrder, axialOrdered,
      seniority, remainingEq, equatorialOrdered, sign⟩
    let equatorial := equatorialPlacement placement pair
    have axialEq : strictOrderAxialPair? placement pair = some axialOrder :=
      (strictOrderAxialPair?_eq_some_iff placement pair axialOrder).mpr axialOrdered
    have seniorEq : strictSeniorPosition3? equatorial = some senior :=
      (strictSeniorPosition3?_eq_some_iff equatorial senior).mpr seniority
    have orderEq : strictOrderEquatorialPair? equatorial remaining = some remainingOrder :=
      (strictOrderEquatorialPair?_eq_some_iff
        equatorial remaining remainingOrder).mpr equatorialOrdered
    have signEq : senseOfDeterminant?
        (TrigonalBipyramid5SpatialPerception.progressionDeterminant
          frame pair axialOrder.1 senior remainingOrder.1) = some sense :=
      (senseOfDeterminant?_eq_some_iff _ sense).mpr sign
    simp [rotationSense?, axialEq, equatorial, seniorEq, remainingEq, orderEq, signEq]

/-- Exact TBPY-5 geometry makes the priority-selected physical progression nonzero. -/
theorem progression_ne_zero_of_exactGeometry
    (frame : Frame) (pair : Fin 5 × Fin 5)
    (placement : Fin 5 → PolyhedralPriorityNumber)
    (perceived : TrigonalBipyramid5SpatialPerception.Judgment frame pair)
    (axialOrder : Fin 5 × Fin 5) (senior : Fin 3)
    (remaining remainingOrder : Fin 3 × Fin 3)
    (axialOrdered : IsStrictAxialOrder placement pair axialOrder)
    (remainingEq : remainingPair3? senior = some remaining)
    (equatorialOrdered : IsStrictEquatorialOrder
      (equatorialPlacement placement pair) remaining remainingOrder) :
    TrigonalBipyramid5SpatialPerception.progressionDeterminant
      frame pair axialOrder.1 senior remainingOrder.1 ≠ 0 := by
  apply TrigonalBipyramid5SpatialPerception.progressionDeterminant_ne_zero_of_judgment
    perceived (axialOrder_first_is_viewpoint axialOrdered)
  exact equatorialOrder_first_ne_senior remainingEq equatorialOrdered

/-- Total physical sense on the exact geometry and strict-priority domain. -/
theorem rotationSense?_exists_of_exactGeometry
    (frame : Frame) (pair : Fin 5 × Fin 5)
    (placement : Fin 5 → PolyhedralPriorityNumber)
    (perceived : TrigonalBipyramid5SpatialPerception.Judgment frame pair)
    (axialOrder : Fin 5 × Fin 5) (senior : Fin 3)
    (remaining remainingOrder : Fin 3 × Fin 3)
    (axialOrdered : IsStrictAxialOrder placement pair axialOrder)
    (seniority : IsStrictSenior3 (equatorialPlacement placement pair) senior)
    (remainingEq : remainingPair3? senior = some remaining)
    (equatorialOrdered : IsStrictEquatorialOrder
      (equatorialPlacement placement pair) remaining remainingOrder) :
    ∃ sense, rotationSense? frame pair placement = some sense ∧
      Judgment frame pair placement sense := by
  have determinantNonzero := progression_ne_zero_of_exactGeometry frame pair placement perceived
    axialOrder senior remaining remainingOrder axialOrdered remainingEq equatorialOrdered
  let determinant := TrigonalBipyramid5SpatialPerception.progressionDeterminant
    frame pair axialOrder.1 senior remainingOrder.1
  rcases lt_trichotomy determinant 0 with negative | zero | positive
  · let sense : PolyhedralRotationSense := .clockwise
    have judged : Judgment frame pair placement sense :=
      ⟨axialOrder, senior, remaining, remainingOrder, axialOrdered, seniority,
        remainingEq, equatorialOrdered, Or.inr ⟨rfl, negative⟩⟩
    exact ⟨sense, (rotationSense?_eq_some_iff frame pair placement sense).mpr judged, judged⟩
  · exact (determinantNonzero zero).elim
  · let sense : PolyhedralRotationSense := .counterclockwise
    have judged : Judgment frame pair placement sense :=
      ⟨axialOrder, senior, remaining, remainingOrder, axialOrdered, seniority,
        remainingEq, equatorialOrdered, Or.inl ⟨rfl, positive⟩⟩
    exact ⟨sense, (rotationSense?_eq_some_iff frame pair placement sense).mpr judged, judged⟩

theorem rotationSense?_eq_none_iff
    (frame : Frame) (pair : Fin 5 × Fin 5)
    (placement : Fin 5 → PolyhedralPriorityNumber) :
    rotationSense? frame pair placement = none ↔
      ¬ ∃ sense, Judgment frame pair placement sense := by
  constructor
  · intro absent ⟨sense, judged⟩
    have present := (rotationSense?_eq_some_iff frame pair placement sense).mpr judged
    rw [absent] at present
    contradiction
  · intro noJudgment
    cases computed : rotationSense? frame pair placement with
    | none => rfl
    | some sense =>
        exact False.elim (noJudgment ⟨sense,
          (rotationSense?_eq_some_iff frame pair placement sense).mp computed⟩)

end TetraStereo.OneCenter.RedBookIR9.TrigonalBipyramid5SpatialOrientation
