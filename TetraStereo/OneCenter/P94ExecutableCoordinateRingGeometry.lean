import TetraStereo.OneCenter.P94CoordinateRingGeometry

set_option autoImplicit false

namespace TetraStereo.OneCenter

open BlueBookP94

namespace BlueBookP94.CoordinateRing

/-!
# Executable exact coordinate geometry for P-94 rings

The original coordinate semantics use proof-level specification choices.  This module provides
code-generatable Boolean gates over the same exact rational determinants and finite point lists,
then proves the executable results equal the existing specification functions on every input.
No floating-point tolerance or approximate geometry is introduced.
-/

namespace ExactPlane

/-- Executable exact nondegeneracy check for a rational witness plane. -/
def nondegenerate? (plane : ExactPlane) : Bool :=
  plane.normal != ({ x := 0, y := 0, z := 0 } : RationalVector3)

@[simp] theorem nondegenerate?_eq_true_iff (plane : ExactPlane) :
    plane.nondegenerate? = true ↔ plane.Nondegenerate := by
  simp [nondegenerate?, Nondegenerate]

@[simp] theorem nondegenerate?_eq_false_iff (plane : ExactPlane) :
    plane.nondegenerate? = false ↔ ¬plane.Nondegenerate := by
  simp [nondegenerate?, Nondegenerate]

/-- Code-generatable determinant-sign classifier. -/
def executableSideOfPlane? (plane : ExactPlane) (point : CartesianPoint3) :
    Option PlaneSide :=
  if plane.nondegenerate? then
    if decide (0 < plane.signedMeasure point) then some .positive
    else if decide (plane.signedMeasure point < 0) then some .negative
    else some .onPlane
  else
    none

/-- The executable classifier is extensionally identical to the original exact specification. -/
theorem executableSideOfPlane?_eq_specification
    (plane : ExactPlane) (point : CartesianPoint3) :
    plane.executableSideOfPlane? point = plane.sideOfPlane? point := by
  classical
  by_cases nondegenerate : plane.Nondegenerate
  · by_cases positive : 0 < plane.signedMeasure point
    · simp [executableSideOfPlane?, sideOfPlane?, nondegenerate, positive]
    · by_cases negative : plane.signedMeasure point < 0
      · simp [executableSideOfPlane?, sideOfPlane?, nondegenerate, positive, negative]
      · simp [executableSideOfPlane?, sideOfPlane?, nondegenerate, positive, negative]
  · simp [executableSideOfPlane?, sideOfPlane?, nondegenerate]

/-- Positive executable results have exactly the independent P-94 plane-side meaning. -/
theorem executableSideOfPlane?_eq_some_iff
    (plane : ExactPlane) (point : CartesianPoint3) (side : PlaneSide) :
    plane.executableSideOfPlane? point = some side ↔
      plane.PointHasSide point side := by
  rw [executableSideOfPlane?_eq_specification]
  exact plane.sideOfPlane?_eq_some_iff point side

/-- Executable refusal occurs exactly for a degenerate plane. -/
theorem executableSideOfPlane?_eq_none_iff
    (plane : ExactPlane) (point : CartesianPoint3) :
    plane.executableSideOfPlane? point = none ↔ ¬plane.Nondegenerate := by
  rw [executableSideOfPlane?_eq_specification]
  exact plane.sideOfPlane?_eq_none_iff point

end ExactPlane

/-- Executable admission of the collected ring-point packet for a witness plane. -/
def ringPointPacketAdmissible? (plane : ExactPlane)
    (points : List CartesianPoint3) : Bool :=
  decide points.Nodup &&
    points.contains plane.first &&
      points.contains plane.second &&
        points.contains plane.third

@[simp] theorem ringPointPacketAdmissible?_eq_true_iff
    (plane : ExactPlane) (points : List CartesianPoint3) :
    ringPointPacketAdmissible? plane points = true ↔
      points.Nodup ∧ plane.SpannedByRingPoints points := by
  simp [ringPointPacketAdmissible?, ExactPlane.SpannedByRingPoints, and_assoc]

private theorem mapM_executableSideOfPlane_eq_specification
    (plane : ExactPlane) (points : List CartesianPoint3) :
    points.mapM plane.executableSideOfPlane? = points.mapM plane.sideOfPlane? := by
  induction points with
  | nil => rfl
  | cons point points inductionHypothesis =>
      rw [List.mapM_cons, List.mapM_cons,
        plane.executableSideOfPlane?_eq_specification point,
        inductionHypothesis]

/-- Fully executable collection and exact side classification for one ordered ring traversal. -/
def executableRingSidesOfPlane? (spatial : SpatialConfiguration) (atoms : List Nat)
    (plane : ExactPlane) : Option (List PlaneSide) :=
  if plane.nondegenerate? then do
    let points ← spatialPointsAt? spatial atoms
    if ringPointPacketAdmissible? plane points then
      points.mapM plane.executableSideOfPlane?
    else
      none
  else
    none

/-- The executable ring-side algorithm is extensionally identical to the original exact
specification selector. -/
theorem executableRingSidesOfPlane?_eq_specification
    (spatial : SpatialConfiguration) (atoms : List Nat) (plane : ExactPlane) :
    executableRingSidesOfPlane? spatial atoms plane =
      ringSidesOfPlane? spatial atoms plane := by
  classical
  by_cases nondegenerate : plane.Nondegenerate
  · cases pointsComputed : spatialPointsAt? spatial atoms with
    | none =>
        simp [executableRingSidesOfPlane?, ringSidesOfPlane?, nondegenerate,
          pointsComputed]
    | some points =>
        by_cases admissible : points.Nodup ∧ plane.SpannedByRingPoints points
        · simp [executableRingSidesOfPlane?, ringSidesOfPlane?, nondegenerate,
            pointsComputed, admissible, mapM_executableSideOfPlane_eq_specification]
        · simp [executableRingSidesOfPlane?, ringSidesOfPlane?, nondegenerate,
            pointsComputed, admissible]
  · simp [executableRingSidesOfPlane?, ringSidesOfPlane?, nondegenerate]

/-- Exact positive characterization of the executable ring-side algorithm. -/
theorem executableRingSidesOfPlane?_eq_some_iff
    (spatial : SpatialConfiguration) (atoms : List Nat)
    (plane : ExactPlane) (sides : List PlaneSide) :
    executableRingSidesOfPlane? spatial atoms plane = some sides ↔
      RingSidesOfPlane spatial atoms plane sides := by
  rw [executableRingSidesOfPlane?_eq_specification]
  exact ringSidesOfPlane?_eq_some_iff spatial atoms plane sides

/-- Exact refusal characterization of the executable ring-side algorithm. -/
theorem executableRingSidesOfPlane?_eq_none_iff
    (spatial : SpatialConfiguration) (atoms : List Nat) (plane : ExactPlane) :
    executableRingSidesOfPlane? spatial atoms plane = none ↔
      ¬∃ sides, RingSidesOfPlane spatial atoms plane sides := by
  rw [executableRingSidesOfPlane?_eq_specification]
  exact ringSidesOfPlane?_eq_none_iff spatial atoms plane

end BlueBookP94.CoordinateRing
end TetraStereo.OneCenter
