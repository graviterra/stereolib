import TetraStereo.OneCenter.IR9SquarePyramid5SpatialOrientation

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.SquarePyramid5SpatialPerception

open FourCoordinateSpatialPerception
open FourCoordinateSpatialRoles
open SquarePyramid5SpatialOrientation

/-!
# Exact coordinate perception for idealized SPY-5

This module receives one central atom and five unordered donor coordinates.  A donor is accepted
as the axial ligand exactly when the other four donors form the coplanar base with that donor
strictly displaced from its plane and the central atom lies on the positive ray from the donor
toward the basal centroid.  Exactly one donor must satisfy the complete predicate.
-/

/-- Five donor coordinates before an apex/base partition has been selected. -/
structure Frame where
  center : CartesianPoint3
  donor0 : CartesianPoint3
  donor1 : CartesianPoint3
  donor2 : CartesianPoint3
  donor3 : CartesianPoint3
  donor4 : CartesianPoint3
  deriving DecidableEq, Repr

namespace Frame

def donorAt (frame : Frame) : Fin 5 → CartesianPoint3
  | 0 => frame.donor0
  | 1 => frame.donor1
  | 2 => frame.donor2
  | 3 => frame.donor3
  | 4 => frame.donor4

/-- Original five-position index of a normalized basal position. -/
def baseOriginalPosition (apex : Fin 5) : Fin 4 → Fin 5 :=
  match apex with
  | 0 => fun position => match position with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4
  | 1 => fun position => match position with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4
  | 2 => fun position => match position with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4
  | 3 => fun position => match position with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4
  | 4 => fun position => match position with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3

theorem baseOriginalPosition_ne_apex (apex : Fin 5) (position : Fin 4) :
    baseOriginalPosition apex position ≠ apex := by
  fin_cases apex <;> fin_cases position <;> decide

theorem baseOriginalPosition_injective (apex : Fin 5) :
    Function.Injective (baseOriginalPosition apex) := by
  fin_cases apex <;> intro first second <;>
    fin_cases first <;> fin_cases second <;> simp [baseOriginalPosition]

/-- Normalize one candidate apex and the four remaining donors. -/
def normalize (frame : Frame) (apex : Fin 5) : SquarePyramid5SpatialOrientation.Frame :=
  { center := frame.center
    apex := frame.donorAt apex
    base0 := frame.donorAt (baseOriginalPosition apex 0)
    base1 := frame.donorAt (baseOriginalPosition apex 1)
    base2 := frame.donorAt (baseOriginalPosition apex 2)
    base3 := frame.donorAt (baseOriginalPosition apex 3) }

@[simp] theorem normalize_apex (frame : Frame) (apex : Fin 5) :
    (frame.normalize apex).apex = frame.donorAt apex := rfl

@[simp] theorem normalize_baseAt (frame : Frame) (apex : Fin 5) (position : Fin 4) :
    (frame.normalize apex).baseAt position =
      frame.donorAt (baseOriginalPosition apex position) := by
  fin_cases apex <;> fin_cases position <;>
    rfl

end Frame

/-- Coordinate-only positive same-ray relation in three dimensions. -/
def SameRayCoordinates
    (ux uy uz vx vy vz : ℚ) : Prop :=
  uy * vz - uz * vy = 0 ∧
  uz * vx - ux * vz = 0 ∧
  ux * vy - uy * vx = 0 ∧
  0 < ux * vx + uy * vy + uz * vz

instance sameRayCoordinatesDecidable
    (ux uy uz vx vy vz : ℚ) :
    Decidable (SameRayCoordinates ux uy uz vx vy vz) := by
  unfold SameRayCoordinates
  infer_instance

theorem sameRayCoordinates_iff
    (ux uy uz vx vy vz : ℚ) :
    SameRayCoordinates ux uy uz vx vy vz ↔
      ∃ scale : ℚ, 0 < scale ∧ (ux ≠ 0 ∨ uy ≠ 0 ∨ uz ≠ 0) ∧
        vx = scale * ux ∧ vy = scale * uy ∧ vz = scale * uz := by
  have antiparallel := antiparallelCoordinates_iff ux uy uz (-vx) (-vy) (-vz)
  constructor
  · rintro ⟨crossX, crossY, crossZ, dotPositive⟩
    have transformed :
        uy * (-vz) - uz * (-vy) = 0 ∧
        uz * (-vx) - ux * (-vz) = 0 ∧
        ux * (-vy) - uy * (-vx) = 0 ∧
        ux * (-vx) + uy * (-vy) + uz * (-vz) < 0 := by
      constructor
      · linarith
      constructor
      · linarith
      constructor <;> linarith
    rcases antiparallel.mp transformed with
      ⟨scale, positive, nonzero, xEq, yEq, zEq⟩
    refine ⟨scale, positive, nonzero, ?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨scale, positive, nonzero, xEq, yEq, zEq⟩
    have transformed :
        ∃ transformedScale : ℚ, 0 < transformedScale ∧
          (ux ≠ 0 ∨ uy ≠ 0 ∨ uz ≠ 0) ∧
          -vx = -transformedScale * ux ∧
          -vy = -transformedScale * uy ∧
          -vz = -transformedScale * uz :=
      ⟨scale, positive, nonzero, by linarith, by linarith, by linarith⟩
    rcases antiparallel.mpr transformed with ⟨crossX, crossY, crossZ, dotNegative⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private def centroidVector (frame : SquarePyramid5SpatialOrientation.Frame) :
    ℚ × ℚ × ℚ :=
  let centroid := SquarePyramid4SpatialOrientation.donorCentroid frame.baseFrame
  (centroid.x - frame.apex.x,
    centroid.y - frame.apex.y,
    centroid.z - frame.apex.z)

private def centerVector (frame : SquarePyramid5SpatialOrientation.Frame) :
    ℚ × ℚ × ℚ :=
  (frame.center.x - frame.apex.x,
    frame.center.y - frame.apex.y,
    frame.center.z - frame.apex.z)

/-- Nondegenerate declarative form of the exact source viewing axis. -/
def AxisTowardCenterNondegenerate (frame : SquarePyramid5SpatialOrientation.Frame) : Prop :=
  frame.AxisTowardCenter ∧
    let vector := centroidVector frame
    vector.1 ≠ 0 ∨ vector.2.1 ≠ 0 ∨ vector.2.2 ≠ 0

/-- Executable exact same-ray test for the axial-ligand-to-center viewing direction. -/
def axisTowardCenter? (frame : SquarePyramid5SpatialOrientation.Frame) : Bool :=
  let u := centroidVector frame
  let v := centerVector frame
  decide (SameRayCoordinates u.1 u.2.1 u.2.2 v.1 v.2.1 v.2.2)

theorem axisTowardCenter?_eq_true_iff
    (frame : SquarePyramid5SpatialOrientation.Frame) :
    axisTowardCenter? frame = true ↔ AxisTowardCenterNondegenerate frame := by
  let u := centroidVector frame
  let v := centerVector frame
  rw [show axisTowardCenter? frame =
      decide (SameRayCoordinates u.1 u.2.1 u.2.2 v.1 v.2.1 v.2.2) by rfl]
  rw [decide_eq_true_eq, sameRayCoordinates_iff]
  constructor
  · rintro ⟨scale, positive, nonzero, xEq, yEq, zEq⟩
    refine ⟨⟨scale, positive, ?_, ?_, ?_⟩, nonzero⟩
    · change frame.center.x - frame.apex.x =
        scale * (SquarePyramid4SpatialOrientation.donorCentroid frame.baseFrame).x -
          scale * frame.apex.x
      change v.1 = scale * u.1 at xEq
      dsimp [u, v, centroidVector, centerVector] at xEq ⊢
      linarith
    · change frame.center.y - frame.apex.y =
        scale * (SquarePyramid4SpatialOrientation.donorCentroid frame.baseFrame).y -
          scale * frame.apex.y
      change v.2.1 = scale * u.2.1 at yEq
      dsimp [u, v, centroidVector, centerVector] at yEq ⊢
      linarith
    · change frame.center.z - frame.apex.z =
        scale * (SquarePyramid4SpatialOrientation.donorCentroid frame.baseFrame).z -
          scale * frame.apex.z
      change v.2.2 = scale * u.2.2 at zEq
      dsimp [u, v, centroidVector, centerVector] at zEq ⊢
      linarith
  · rintro ⟨⟨scale, positive, xEq, yEq, zEq⟩, nonzero⟩
    refine ⟨scale, positive, nonzero, ?_, ?_, ?_⟩
    · change v.1 = scale * u.1
      dsimp [u, v, centroidVector, centerVector]
      linarith
    · change v.2.1 = scale * u.2.1
      dsimp [u, v, centroidVector, centerVector]
      linarith
    · change v.2.2 = scale * u.2.2
      dsimp [u, v, centroidVector, centerVector]
      linarith

/-- Exact mathematical apex predicate. -/
def IsApexCandidate (frame : Frame) (candidate : Fin 5) : Prop :=
  (frame.normalize candidate).baseFrame.DonorsCoplanarCenterDisplaced ∧
    AxisTowardCenterNondegenerate (frame.normalize candidate)

/-- Executable version of the exact apex predicate. -/
def apexCandidate? (frame : Frame) (candidate : Fin 5) : Bool :=
  FourCoordinateSpatialPerception.observe?
      (frame.normalize candidate).baseFrame ==
      some .donorsCoplanarCenterDisplaced &&
    axisTowardCenter? (frame.normalize candidate)

theorem apexCandidate?_eq_true_iff (frame : Frame) (candidate : Fin 5) :
    apexCandidate? frame candidate = true ↔ IsApexCandidate frame candidate := by
  simp [apexCandidate?, IsApexCandidate,
    FourCoordinateSpatialPerception.observe?_eq_some_iff,
    axisTowardCenter?_eq_true_iff]

def positions : List (Fin 5) := [0, 1, 2, 3, 4]

@[simp] theorem mem_positions (position : Fin 5) : position ∈ positions := by
  fin_cases position <;> simp [positions]

theorem positions_nodup : positions.Nodup := by decide

/-- Accept exactly one exact axial ligand. -/
def uniqueApexPosition? (frame : Frame) : Option (Fin 5) :=
  uniqueSatisfying? positions (apexCandidate? frame)

theorem uniqueApexPosition?_eq_some_iff (frame : Frame) (candidate : Fin 5) :
    uniqueApexPosition? frame = some candidate ↔
      IsApexCandidate frame candidate ∧
        ∀ other, IsApexCandidate frame other → other = candidate := by
  rw [uniqueApexPosition?, uniqueSatisfying?_eq_some_iff
    positions (apexCandidate? frame) positions_nodup candidate]
  simp only [mem_positions, true_and, apexCandidate?_eq_true_iff]
  constructor
  · rintro ⟨candidateApex, unique⟩
    exact ⟨candidateApex, fun other otherApex => unique other trivial otherApex⟩
  · rintro ⟨candidateApex, unique⟩
    exact ⟨candidateApex, fun other _ otherApex => unique other otherApex⟩

theorem uniqueApexPosition?_eq_none_iff (frame : Frame) :
    uniqueApexPosition? frame = none ↔
      ¬ ∃ candidate, IsApexCandidate frame candidate ∧
        ∀ other, IsApexCandidate frame other → other = candidate := by
  constructor
  · intro none ⟨candidate, exactCandidate⟩
    have some := (uniqueApexPosition?_eq_some_iff frame candidate).mpr exactCandidate
    rw [none] at some
    contradiction
  · intro noUnique
    cases computed : uniqueApexPosition? frame with
    | none => simp
    | some candidate =>
        exfalso
        exact noUnique ⟨candidate, (uniqueApexPosition?_eq_some_iff frame candidate).mp computed⟩

/-- Return the unique apex together with its normalized SPY-5 frame. -/
def perceive? (frame : Frame) : Option (Fin 5 × SquarePyramid5SpatialOrientation.Frame) := do
  let apex ← uniqueApexPosition? frame
  some (apex, frame.normalize apex)

theorem perceive?_eq_some_iff
    (frame : Frame) (apex : Fin 5) (normalized : SquarePyramid5SpatialOrientation.Frame) :
    perceive? frame = some (apex, normalized) ↔
      normalized = frame.normalize apex ∧ IsApexCandidate frame apex ∧
        ∀ other, IsApexCandidate frame other → other = apex := by
  constructor
  · intro computed
    cases apexEq : uniqueApexPosition? frame with
    | none => simp [perceive?, apexEq] at computed
    | some found =>
        have pairEq : (found, frame.normalize found) = (apex, normalized) := by
          simpa [perceive?, apexEq] using computed
        cases pairEq
        exact ⟨rfl, (uniqueApexPosition?_eq_some_iff frame apex).mp apexEq⟩
  · rintro ⟨rfl, candidate, unique⟩
    have apexEq := (uniqueApexPosition?_eq_some_iff frame apex).mpr ⟨candidate, unique⟩
    simp [perceive?, apexEq]

end TetraStereo.OneCenter.RedBookIR9.SquarePyramid5SpatialPerception
