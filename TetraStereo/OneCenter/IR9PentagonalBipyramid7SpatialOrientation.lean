import TetraStereo.OneCenter.IR9PentagonalBipyramid7SpatialPerception
import TetraStereo.OneCenter.IR9SeeSawSpatialOrientation

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.PentagonalBipyramid7SpatialOrientation

open PentagonalBipyramid7SpatialPerception
open FourCoordinateSpatialRoles
open SeeSawSpatialOrientation

abbrev Frame := PentagonalBipyramid7SpatialPerception.Frame
abbrev Partition := PentagonalBipyramid7SpatialPerception.Partition

/-!
# Exact physical A/C progression for PBPY-7

IR-9.3.4.10 views the structure from the higher-priority axial ligand.  Starting at the highest
priority equatorial ligand, the clockwise and anticlockwise priority words are compared at their
first difference.  The physical sense of the lower word is the emitted C/A symbol.
-/

def strictOrderAxialPair?
    (placement : Fin 7 → PolyhedralPriorityNumber) (pair : Fin 7 × Fin 7) :
    Option (Fin 7 × Fin 7) :=
  if (placement pair.1).outranks (placement pair.2) then
    some pair
  else if (placement pair.2).outranks (placement pair.1) then
    some (pair.2, pair.1)
  else none

def IsStrictAxialOrder
    (placement : Fin 7 → PolyhedralPriorityNumber)
    (pair ordered : Fin 7 × Fin 7) : Prop :=
  (ordered = pair ∧ (placement pair.1).outranks (placement pair.2) = true) ∨
    (ordered = (pair.2, pair.1) ∧
      (placement pair.2).outranks (placement pair.1) = true)

theorem strictOrderAxialPair?_eq_some_iff
    (placement : Fin 7 → PolyhedralPriorityNumber)
    (pair ordered : Fin 7 × Fin 7) :
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
    {placement : Fin 7 → PolyhedralPriorityNumber}
    {pair ordered : Fin 7 × Fin 7}
    (strict : IsStrictAxialOrder placement pair ordered) :
    ordered.1 = pair.1 ∨ ordered.1 = pair.2 := by
  rcases strict with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

def positions5 : List (Fin 5) := [0, 1, 2, 3, 4]

@[simp] theorem mem_positions5 (position : Fin 5) : position ∈ positions5 := by
  fin_cases position <;> simp [positions5]

theorem positions5_nodup : positions5.Nodup := by decide

def cyclePlacement (placement : Fin 7 → PolyhedralPriorityNumber)
    (partition : Partition) : Fin 5 → PolyhedralPriorityNumber :=
  fun position => placement (cycleAt partition.equatorialCycle position)

def IsStrictSenior5
    (placement : Fin 5 → PolyhedralPriorityNumber) (senior : Fin 5) : Prop :=
  ∀ other, other ≠ senior →
    (placement senior).outranks (placement other) = true

def isStrictSenior5?
    (placement : Fin 5 → PolyhedralPriorityNumber) (senior : Fin 5) : Bool :=
  positions5.all fun other =>
    other == senior || (placement senior).outranks (placement other)

theorem isStrictSenior5?_eq_true_iff
    (placement : Fin 5 → PolyhedralPriorityNumber) (senior : Fin 5) :
    isStrictSenior5? placement senior = true ↔ IsStrictSenior5 placement senior := by
  simp only [isStrictSenior5?, List.all_eq_true, Bool.or_eq_true, beq_iff_eq]
  constructor
  · intro checked other different
    rcases checked other (mem_positions5 other) with same | outranks
    · exact (different same).elim
    · exact outranks
  · intro seniority other _
    by_cases same : other = senior
    · exact Or.inl same
    · exact Or.inr (seniority other same)

def strictSeniorPosition5?
    (placement : Fin 5 → PolyhedralPriorityNumber) : Option (Fin 5) :=
  FourCoordinateSpatialRoles.uniqueSatisfying? positions5 (isStrictSenior5? placement)

theorem strictSeniorPosition5?_eq_some_iff
    (placement : Fin 5 → PolyhedralPriorityNumber) (senior : Fin 5) :
    strictSeniorPosition5? placement = some senior ↔ IsStrictSenior5 placement senior := by
  rw [strictSeniorPosition5?,
    FourCoordinateSpatialRoles.uniqueSatisfying?_eq_some_iff positions5
      (isStrictSenior5? placement) positions5_nodup senior]
  simp only [mem_positions5, true_and, isStrictSenior5?_eq_true_iff]
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

def forwardIndex5 (start offset : Fin 5) : Fin 5 :=
  ⟨(start.val + offset.val) % 5, Nat.mod_lt _ (by decide)⟩

def reverseIndex5 (start offset : Fin 5) : Fin 5 :=
  ⟨(start.val + 5 - offset.val) % 5, Nat.mod_lt _ (by decide)⟩

inductive CycleDirection where
  | forward
  | reverse
  deriving DecidableEq, Repr

def cycleIndex (direction : CycleDirection) (start offset : Fin 5) : Fin 5 :=
  match direction with
  | .forward => forwardIndex5 start offset
  | .reverse => reverseIndex5 start offset

def cyclePriorityWord (placement : Fin 5 → PolyhedralPriorityNumber)
    (direction : CycleDirection) (start : Fin 5) : List PolyhedralPriorityNumber :=
  positions5.map fun offset => placement (cycleIndex direction start offset)

def IsPreferredCycleDirection
    (placement : Fin 5 → PolyhedralPriorityNumber)
    (start : Fin 5) (direction : CycleDirection) : Prop :=
  (direction = .forward ∧
      comparePolyhedralPrioritySequence
        (cyclePriorityWord placement .forward start)
        (cyclePriorityWord placement .reverse start) = .gt) ∨
    (direction = .reverse ∧
      comparePolyhedralPrioritySequence
        (cyclePriorityWord placement .forward start)
        (cyclePriorityWord placement .reverse start) = .lt)

def preferredCycleDirection?
    (placement : Fin 5 → PolyhedralPriorityNumber) (start : Fin 5) :
    Option CycleDirection :=
  match comparePolyhedralPrioritySequence
      (cyclePriorityWord placement .forward start)
      (cyclePriorityWord placement .reverse start) with
  | .gt => some .forward
  | .lt => some .reverse
  | .eq => none

theorem preferredCycleDirection?_eq_some_iff
    (placement : Fin 5 → PolyhedralPriorityNumber)
    (start : Fin 5) (direction : CycleDirection) :
    preferredCycleDirection? placement start = some direction ↔
      IsPreferredCycleDirection placement start direction := by
  unfold preferredCycleDirection? IsPreferredCycleDirection
  cases compared : comparePolyhedralPrioritySequence
      (cyclePriorityWord placement .forward start)
      (cyclePriorityWord placement .reverse start) <;>
    cases direction <;> simp

theorem cycleIndex_one_ne_start (direction : CycleDirection) (start : Fin 5) :
    cycleIndex direction start 1 ≠ start := by
  cases direction <;> fin_cases start <;>
    decide

def senseOfDeterminant? (determinant : ℚ) : Option PolyhedralRotationSense :=
  SeeSawSpatialOrientation.senseOfDeterminant? determinant

theorem senseOfDeterminant?_eq_some_iff
    (determinant : ℚ) (sense : PolyhedralRotationSense) :
    senseOfDeterminant? determinant = some sense ↔
      (sense = .counterclockwise ∧ 0 < determinant) ∨
      (sense = .clockwise ∧ determinant < 0) :=
  SeeSawSpatialOrientation.senseOfDeterminant?_eq_some_iff determinant sense

/-- Fully coordinate- and priority-derived PBPY-7 physical rotation sense. -/
def rotationSense? (frame : Frame) (partition : Partition)
    (placement : Fin 7 → PolyhedralPriorityNumber) :
    Option PolyhedralRotationSense := do
  let axialOrder ← strictOrderAxialPair? placement partition.axial
  let equatorial := cyclePlacement placement partition
  let senior ← strictSeniorPosition5? equatorial
  let direction ← preferredCycleDirection? equatorial senior
  senseOfDeterminant?
    (PentagonalBipyramid7SpatialPerception.progressionDeterminant
      frame partition axialOrder.1 senior (cycleIndex direction senior 1))

def Judgment (frame : Frame) (partition : Partition)
    (placement : Fin 7 → PolyhedralPriorityNumber)
    (sense : PolyhedralRotationSense) : Prop :=
  ∃ axialOrder senior direction,
    IsStrictAxialOrder placement partition.axial axialOrder ∧
    IsStrictSenior5 (cyclePlacement placement partition) senior ∧
    IsPreferredCycleDirection (cyclePlacement placement partition) senior direction ∧
    ((sense = .counterclockwise ∧
        0 < PentagonalBipyramid7SpatialPerception.progressionDeterminant
          frame partition axialOrder.1 senior (cycleIndex direction senior 1)) ∨
      (sense = .clockwise ∧
        PentagonalBipyramid7SpatialPerception.progressionDeterminant
          frame partition axialOrder.1 senior (cycleIndex direction senior 1) < 0))

theorem rotationSense?_eq_some_iff
    (frame : Frame) (partition : Partition)
    (placement : Fin 7 → PolyhedralPriorityNumber)
    (sense : PolyhedralRotationSense) :
    rotationSense? frame partition placement = some sense ↔
      Judgment frame partition placement sense := by
  constructor
  · intro computed
    unfold rotationSense? at computed
    cases axialEq : strictOrderAxialPair? placement partition.axial with
    | none => simp [axialEq] at computed
    | some axialOrder =>
        let equatorial := cyclePlacement placement partition
        cases seniorEq : strictSeniorPosition5? equatorial with
        | none => simp [axialEq, equatorial, seniorEq] at computed
        | some senior =>
            cases directionEq : preferredCycleDirection? equatorial senior with
            | none => simp [axialEq, equatorial, seniorEq, directionEq] at computed
            | some direction =>
                have sign := (senseOfDeterminant?_eq_some_iff _ sense).mp
                  (show senseOfDeterminant?
                      (PentagonalBipyramid7SpatialPerception.progressionDeterminant
                        frame partition axialOrder.1 senior
                          (cycleIndex direction senior 1)) = some sense by
                    simpa [axialEq, equatorial, seniorEq, directionEq] using computed)
                exact ⟨axialOrder, senior, direction,
                  (strictOrderAxialPair?_eq_some_iff
                    placement partition.axial axialOrder).mp axialEq,
                  (strictSeniorPosition5?_eq_some_iff equatorial senior).mp seniorEq,
                  (preferredCycleDirection?_eq_some_iff
                    equatorial senior direction).mp directionEq,
                  sign⟩
  · rintro ⟨axialOrder, senior, direction, axialOrdered, seniority,
      directionPreferred, sign⟩
    let equatorial := cyclePlacement placement partition
    have axialEq : strictOrderAxialPair? placement partition.axial = some axialOrder :=
      (strictOrderAxialPair?_eq_some_iff
        placement partition.axial axialOrder).mpr axialOrdered
    have seniorEq : strictSeniorPosition5? equatorial = some senior :=
      (strictSeniorPosition5?_eq_some_iff equatorial senior).mpr seniority
    have directionEq : preferredCycleDirection? equatorial senior = some direction :=
      (preferredCycleDirection?_eq_some_iff
        equatorial senior direction).mpr directionPreferred
    have signEq : senseOfDeterminant?
        (PentagonalBipyramid7SpatialPerception.progressionDeterminant
          frame partition axialOrder.1 senior (cycleIndex direction senior 1)) = some sense :=
      (senseOfDeterminant?_eq_some_iff _ sense).mpr sign
    simp [rotationSense?, axialEq, equatorial, seniorEq, directionEq, signEq]

theorem progression_ne_zero_of_exactGeometry
    (frame : Frame) (partition : Partition)
    (placement : Fin 7 → PolyhedralPriorityNumber)
    (perceived : PentagonalBipyramid7SpatialPerception.Judgment frame partition)
    (axialOrder : Fin 7 × Fin 7) (senior : Fin 5) (direction : CycleDirection)
    (axialOrdered : IsStrictAxialOrder placement partition.axial axialOrder) :
    PentagonalBipyramid7SpatialPerception.progressionDeterminant
      frame partition axialOrder.1 senior (cycleIndex direction senior 1) ≠ 0 := by
  apply PentagonalBipyramid7SpatialPerception.progressionDeterminant_ne_zero_of_judgment
    perceived (axialOrder_first_is_viewpoint axialOrdered)
  exact cycleIndex_one_ne_start direction senior |>.symm

theorem rotationSense?_exists_of_exactGeometry
    (frame : Frame) (partition : Partition)
    (placement : Fin 7 → PolyhedralPriorityNumber)
    (perceived : PentagonalBipyramid7SpatialPerception.Judgment frame partition)
    (axialOrder : Fin 7 × Fin 7) (senior : Fin 5) (direction : CycleDirection)
    (axialOrdered : IsStrictAxialOrder placement partition.axial axialOrder)
    (seniority : IsStrictSenior5 (cyclePlacement placement partition) senior)
    (directionPreferred :
      IsPreferredCycleDirection (cyclePlacement placement partition) senior direction) :
    ∃ sense, rotationSense? frame partition placement = some sense ∧
      Judgment frame partition placement sense := by
  have determinantNonzero := progression_ne_zero_of_exactGeometry
    frame partition placement perceived axialOrder senior direction axialOrdered
  let determinant := PentagonalBipyramid7SpatialPerception.progressionDeterminant
    frame partition axialOrder.1 senior (cycleIndex direction senior 1)
  rcases lt_trichotomy determinant 0 with negative | zero | positive
  · let sense : PolyhedralRotationSense := .clockwise
    have judged : Judgment frame partition placement sense :=
      ⟨axialOrder, senior, direction, axialOrdered, seniority, directionPreferred,
        Or.inr ⟨rfl, negative⟩⟩
    exact ⟨sense, (rotationSense?_eq_some_iff frame partition placement sense).mpr judged,
      judged⟩
  · exact (determinantNonzero zero).elim
  · let sense : PolyhedralRotationSense := .counterclockwise
    have judged : Judgment frame partition placement sense :=
      ⟨axialOrder, senior, direction, axialOrdered, seniority, directionPreferred,
        Or.inl ⟨rfl, positive⟩⟩
    exact ⟨sense, (rotationSense?_eq_some_iff frame partition placement sense).mpr judged,
      judged⟩

theorem rotationSense?_eq_none_iff
    (frame : Frame) (partition : Partition)
    (placement : Fin 7 → PolyhedralPriorityNumber) :
    rotationSense? frame partition placement = none ↔
      ¬ ∃ sense, Judgment frame partition placement sense := by
  constructor
  · intro absent ⟨sense, judged⟩
    have present := (rotationSense?_eq_some_iff frame partition placement sense).mpr judged
    rw [absent] at present
    contradiction
  · intro noJudgment
    cases computed : rotationSense? frame partition placement with
    | none => rfl
    | some sense =>
        exact False.elim (noJudgment ⟨sense,
          (rotationSense?_eq_some_iff frame partition placement sense).mp computed⟩)

end TetraStereo.OneCenter.RedBookIR9.PentagonalBipyramid7SpatialOrientation
