import TetraStereo.OneCenter.IR9SquarePyramid4SpatialOrientation

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.SquarePyramid5SpatialOrientation

open FourCoordinateSpatialPerception
open FourCoordinateSpatialRoles
open SeeSawSpatialOrientation

/-!
# Exact physical A/C progression for SPY-5

Red Book IR-9.3.4.6 views an SPY-5 polyhedron from the axial ligand toward the central atom and
compares the clockwise and anticlockwise priority sequences of the four basal ligands.  This file
keeps the axial ligand separate from the four-position base, proves that the source comparison
first differs at the two basal sites adjacent to the strict basal senior, and derives the viewed
sense from an exact rational scalar triple product.
-/

/-- A central atom, the axial ligand, and four basal ligands in presentation order. -/
structure Frame where
  center : CartesianPoint3
  apex : CartesianPoint3
  base0 : CartesianPoint3
  base1 : CartesianPoint3
  base2 : CartesianPoint3
  base3 : CartesianPoint3
  deriving DecidableEq, Repr

namespace Frame

/-- Reuse the exact four-donor affine machinery with the axial ligand as the displaced point. -/
def baseFrame (frame : Frame) : FourCoordinateSpatialPerception.Frame :=
  { center := frame.apex
    donor0 := frame.base0
    donor1 := frame.base1
    donor2 := frame.base2
    donor3 := frame.base3 }

def baseAt (frame : Frame) (position : Fin 4) : CartesianPoint3 :=
  frame.baseFrame.donorAt position

@[simp] theorem baseFrame_center (frame : Frame) : frame.baseFrame.center = frame.apex := rfl

@[simp] theorem baseAt_zero (frame : Frame) : frame.baseAt 0 = frame.base0 := rfl
@[simp] theorem baseAt_one (frame : Frame) : frame.baseAt 1 = frame.base1 := rfl
@[simp] theorem baseAt_two (frame : Frame) : frame.baseAt 2 = frame.base2 := rfl
@[simp] theorem baseAt_three (frame : Frame) : frame.baseAt 3 = frame.base3 := rfl

/-- The central atom lies strictly in the viewing direction from the apex toward the basal
centroid.  No metric distance or distortion threshold is introduced. -/
def AxisTowardCenter (frame : Frame) : Prop :=
  ∃ scale : ℚ, 0 < scale ∧
    frame.center.x - frame.apex.x =
      scale * (SquarePyramid4SpatialOrientation.donorCentroid frame.baseFrame).x -
        scale * frame.apex.x ∧
    frame.center.y - frame.apex.y =
      scale * (SquarePyramid4SpatialOrientation.donorCentroid frame.baseFrame).y -
        scale * frame.apex.y ∧
    frame.center.z - frame.apex.z =
      scale * (SquarePyramid4SpatialOrientation.donorCentroid frame.baseFrame).z -
        scale * frame.apex.z

end Frame

/-- Viewed basal progression, with the actual axial-ligand-to-center ray as the viewing ray. -/
def progressionDeterminant
    (frame : Frame) (senior adjacentSenior : Fin 4) : ℚ :=
  CartesianPoint3.orientedVolume
    (frame.baseAt senior) (frame.baseAt adjacentSenior) frame.apex frame.center

theorem progressionDeterminant_eq_scaled_baseDeterminant
    (frame : Frame) (senior adjacentSenior : Fin 4)
    (axis : frame.AxisTowardCenter) :
    ∃ scale : ℚ, 0 < scale ∧
      progressionDeterminant frame senior adjacentSenior =
        scale * SquarePyramid4SpatialOrientation.progressionDeterminant
          frame.baseFrame senior adjacentSenior := by
  rcases axis with ⟨scale, positive, xAxis, yAxis, zAxis⟩
  have centerX : frame.center.x = frame.apex.x +
      scale * ((SquarePyramid4SpatialOrientation.donorCentroid frame.baseFrame).x -
        frame.apex.x) := by
    linarith
  have centerY : frame.center.y = frame.apex.y +
      scale * ((SquarePyramid4SpatialOrientation.donorCentroid frame.baseFrame).y -
        frame.apex.y) := by
    linarith
  have centerZ : frame.center.z = frame.apex.z +
      scale * ((SquarePyramid4SpatialOrientation.donorCentroid frame.baseFrame).z -
        frame.apex.z) := by
    linarith
  refine ⟨scale, positive, ?_⟩
  simp [progressionDeterminant, SquarePyramid4SpatialOrientation.progressionDeterminant,
    Frame.baseAt, CartesianPoint3.orientedVolume, centerX, centerY, centerZ]
  ring

/-- Exact idealized SPY-5 geometry makes the source progression nondegenerate. -/
theorem progressionDeterminant_ne_zero
    (frame : Frame)
    (placement : Fin 4 → PolyhedralPriorityNumber)
    (senior trans : Fin 4) (remaining adjacentOrder : Fin 4 × Fin 4)
    (apexDisplaced : frame.baseFrame.DonorsCoplanarCenterDisplaced)
    (axis : frame.AxisTowardCenter)
    (opposite : IsOppositePair frame.baseFrame senior trans)
    (remainingEq : SquarePyramid4SpatialOrientation.remainingPair? senior trans = some remaining)
    (adjacentOrdered : IsStrictOrder placement remaining adjacentOrder) :
    progressionDeterminant frame senior adjacentOrder.1 ≠ 0 := by
  obtain ⟨scale, positive, determinantEq⟩ :=
    progressionDeterminant_eq_scaled_baseDeterminant frame senior adjacentOrder.1 axis
  have baseNonzero :
      SquarePyramid4SpatialOrientation.progressionDeterminant
        frame.baseFrame senior adjacentOrder.1 ≠ 0 :=
    SquarePyramid4SpatialOrientation.progressionDeterminant_ne_zero
      frame.baseFrame placement senior trans remaining
      adjacentOrder apexDisplaced opposite remainingEq adjacentOrdered
  rw [determinantEq]
  exact mul_ne_zero (ne_of_gt positive) baseNonzero

/-- A positive determinant is counterclockwise/A and a negative determinant clockwise/C from the
source-prescribed axial-ligand viewpoint. -/
def senseOfDeterminant? (determinant : ℚ) : Option PolyhedralRotationSense :=
  SeeSawSpatialOrientation.senseOfDeterminant? determinant

theorem senseOfDeterminant?_eq_some_iff
    (determinant : ℚ) (sense : PolyhedralRotationSense) :
    senseOfDeterminant? determinant = some sense ↔
      (sense = .counterclockwise ∧ 0 < determinant) ∨
      (sense = .clockwise ∧ determinant < 0) :=
  SeeSawSpatialOrientation.senseOfDeterminant?_eq_some_iff determinant sense

/-- The literal SPY-5 basal cyclic comparison first differs at the ordered adjacent pair. -/
theorem seniorAdjacent_firstDifference
    (placement : Fin 4 → PolyhedralPriorityNumber)
    (senior trans : Fin 4) (remaining adjacentOrder : Fin 4 × Fin 4)
    (ordered : IsStrictOrder placement remaining adjacentOrder) :
    BlueBookP93.comparePrioritySequence
        [BlueBookP93.priorityOfProduction (placement senior),
          BlueBookP93.priorityOfProduction (placement adjacentOrder.1),
          BlueBookP93.priorityOfProduction (placement trans),
          BlueBookP93.priorityOfProduction (placement adjacentOrder.2)]
        [BlueBookP93.priorityOfProduction (placement senior),
          BlueBookP93.priorityOfProduction (placement adjacentOrder.2),
          BlueBookP93.priorityOfProduction (placement trans),
          BlueBookP93.priorityOfProduction (placement adjacentOrder.1)] = .gt :=
  SquarePyramid4SpatialOrientation.seniorAdjacent_firstDifference
    placement senior trans remaining adjacentOrder ordered

/-- Fully coordinate- and basal-priority-derived SPY-5 rotation sense. -/
def rotationSense?
    (frame : Frame) (placement : Fin 4 → PolyhedralPriorityNumber) :
    Option PolyhedralRotationSense := do
  let senior ← strictSeniorPosition? placement
  let trans ← oppositePosition? frame.baseFrame senior
  let remaining ← SquarePyramid4SpatialOrientation.remainingPair? senior trans
  let adjacentOrder ← strictOrderPair? placement remaining
  senseOfDeterminant? (progressionDeterminant frame senior adjacentOrder.1)

/-- Independent operational meaning of the exact SPY-5 cyclic reading. -/
def Judgment
    (frame : Frame) (placement : Fin 4 → PolyhedralPriorityNumber)
    (sense : PolyhedralRotationSense) : Prop :=
  ∃ senior trans remaining adjacentOrder,
    IsStrictSenior placement senior ∧
    IsOppositePair frame.baseFrame senior trans ∧
    (∀ other, IsOppositePair frame.baseFrame senior other → other = trans) ∧
    SquarePyramid4SpatialOrientation.remainingPair? senior trans = some remaining ∧
    IsStrictOrder placement remaining adjacentOrder ∧
    ((sense = .counterclockwise ∧
        0 < progressionDeterminant frame senior adjacentOrder.1) ∨
      (sense = .clockwise ∧
        progressionDeterminant frame senior adjacentOrder.1 < 0))

theorem rotationSense?_eq_some_iff
    (frame : Frame) (placement : Fin 4 → PolyhedralPriorityNumber)
    (sense : PolyhedralRotationSense) :
    rotationSense? frame placement = some sense ↔ Judgment frame placement sense := by
  constructor
  · intro computed
    cases seniorEq : strictSeniorPosition? placement with
    | none => simp [rotationSense?, seniorEq] at computed
    | some senior =>
        cases transEq : oppositePosition? frame.baseFrame senior with
        | none => simp [rotationSense?, seniorEq, transEq] at computed
        | some trans =>
            cases remainingEq : SquarePyramid4SpatialOrientation.remainingPair? senior trans with
            | none => simp [rotationSense?, seniorEq, transEq, remainingEq] at computed
            | some remaining =>
                cases adjacentEq : strictOrderPair? placement remaining with
                | none =>
                    simp [rotationSense?, seniorEq, transEq, remainingEq, adjacentEq] at computed
                | some adjacentOrder =>
                    have seniority := (strictSeniorPosition?_eq_some_iff placement senior).mp seniorEq
                    have transFacts :=
                      (oppositePosition?_eq_some_iff frame.baseFrame senior trans).mp transEq
                    have adjacentOrdered :=
                      (strictOrderPair?_eq_some_iff placement remaining adjacentOrder).mp adjacentEq
                    have sign := (senseOfDeterminant?_eq_some_iff _ sense).mp
                      (show senseOfDeterminant?
                          (progressionDeterminant frame senior adjacentOrder.1) = some sense by
                        simpa [rotationSense?, seniorEq, transEq, remainingEq, adjacentEq]
                          using computed)
                    exact ⟨senior, trans, remaining, adjacentOrder, seniority,
                      transFacts.1, transFacts.2, remainingEq, adjacentOrdered, sign⟩
  · rintro ⟨senior, trans, remaining, adjacentOrder, seniority,
      opposite, unique, remainingEq, adjacentOrdered, sign⟩
    have seniorEq : strictSeniorPosition? placement = some senior :=
      (strictSeniorPosition?_eq_some_iff placement senior).mpr seniority
    have transEq : oppositePosition? frame.baseFrame senior = some trans :=
      (oppositePosition?_eq_some_iff frame.baseFrame senior trans).mpr ⟨opposite, unique⟩
    have adjacentEq : strictOrderPair? placement remaining = some adjacentOrder :=
      (strictOrderPair?_eq_some_iff placement remaining adjacentOrder).mpr adjacentOrdered
    have signEq : senseOfDeterminant?
        (progressionDeterminant frame senior adjacentOrder.1) = some sense :=
      (senseOfDeterminant?_eq_some_iff _ sense).mpr sign
    simp [rotationSense?, seniorEq, transEq, remainingEq, adjacentEq, signEq]

theorem rotationSense?_exists_of_exactGeometry
    (frame : Frame) (placement : Fin 4 → PolyhedralPriorityNumber)
    (senior trans : Fin 4) (remaining adjacentOrder : Fin 4 × Fin 4)
    (apexDisplaced : frame.baseFrame.DonorsCoplanarCenterDisplaced)
    (axis : frame.AxisTowardCenter)
    (seniority : IsStrictSenior placement senior)
    (opposite : IsOppositePair frame.baseFrame senior trans)
    (unique : ∀ other, IsOppositePair frame.baseFrame senior other → other = trans)
    (remainingEq : SquarePyramid4SpatialOrientation.remainingPair? senior trans = some remaining)
    (adjacentOrdered : IsStrictOrder placement remaining adjacentOrder) :
    ∃ sense, rotationSense? frame placement = some sense ∧ Judgment frame placement sense := by
  have determinantNonzero := progressionDeterminant_ne_zero frame placement senior trans remaining
    adjacentOrder apexDisplaced axis opposite remainingEq adjacentOrdered
  rcases lt_trichotomy (progressionDeterminant frame senior adjacentOrder.1) 0 with
    clockwise | zero | counterclockwise
  · let sense : PolyhedralRotationSense := .clockwise
    have judgment : Judgment frame placement sense :=
      ⟨senior, trans, remaining, adjacentOrder, seniority, opposite, unique,
        remainingEq, adjacentOrdered, Or.inr ⟨rfl, clockwise⟩⟩
    exact ⟨sense, (rotationSense?_eq_some_iff frame placement sense).mpr judgment, judgment⟩
  · exact (determinantNonzero zero).elim
  · let sense : PolyhedralRotationSense := .counterclockwise
    have judgment : Judgment frame placement sense :=
      ⟨senior, trans, remaining, adjacentOrder, seniority, opposite, unique,
        remainingEq, adjacentOrdered, Or.inl ⟨rfl, counterclockwise⟩⟩
    exact ⟨sense, (rotationSense?_eq_some_iff frame placement sense).mpr judgment, judgment⟩

theorem rotationSense?_eq_none_iff
    (frame : Frame) (placement : Fin 4 → PolyhedralPriorityNumber) :
    rotationSense? frame placement = none ↔ ¬ ∃ sense, Judgment frame placement sense := by
  constructor
  · intro none ⟨sense, judgment⟩
    have some := (rotationSense?_eq_some_iff frame placement sense).mpr judgment
    rw [none] at some
    contradiction
  · intro noJudgment
    cases computed : rotationSense? frame placement with
    | none => simp
    | some sense =>
        exfalso
        exact noJudgment ⟨sense, (rotationSense?_eq_some_iff frame placement sense).mp computed⟩

end TetraStereo.OneCenter.RedBookIR9.SquarePyramid5SpatialOrientation
