import TetraStereo.OneCenter.P94CoordinateTorsion

set_option autoImplicit false

namespace TetraStereo.OneCenter

open BlueBookP94

/-!
# Exact coordinate geometry for P-94 ring conformations

This module is the geometry boundary between an indexed exact spatial configuration and the
plane-side lists used by the P-94.3.2 ring predicates.  A witness plane is oriented by three
ordered rational points.  It is admitted exactly when those points are noncollinear, and every
queried point is classified by the sign of the exact rational affine determinant.  There is no
tolerance, floating-point comparison, or caller-supplied side label.

The list-level relations below are deliberately independent of their `Option` evaluators.  They
state coordinate lookup with `List.Forall₂`, then state the determinant judgment for every
looked-up point.  The exactness theorems cover both successful outputs and every refusal.
-/

namespace BlueBookP94.CoordinateRing

/-- Three ordered exact points defining an oriented affine plane. -/
structure ExactPlane where
  first : CartesianPoint3
  second : CartesianPoint3
  third : CartesianPoint3
  deriving DecidableEq, Repr

namespace ExactPlane

/-- Exact normal of the two plane-spanning edge vectors. -/
def normal (plane : ExactPlane) : RationalVector3 :=
  RationalVector3.cross
    (CartesianPoint3.displacement plane.first plane.second)
    (CartesianPoint3.displacement plane.first plane.third)

/-- The three defining points determine a plane precisely when their exact normal is nonzero. -/
def Nondegenerate (plane : ExactPlane) : Prop :=
  plane.normal ≠ ({ x := 0, y := 0, z := 0 } : RationalVector3)

/-- Signed exact affine measure of a point relative to the oriented witness plane. -/
def signedMeasure (plane : ExactPlane) (point : CartesianPoint3) : ℚ :=
  CartesianPoint3.orientedVolume plane.first plane.second plane.third point

/-- Independent exact meaning of a P-94 plane-side label. -/
def PointHasSide (plane : ExactPlane) (point : CartesianPoint3)
    (side : PlaneSide) : Prop :=
  plane.Nondegenerate ∧
    match side with
    | .onPlane => plane.signedMeasure point = 0
    | .positive => 0 < plane.signedMeasure point
    | .negative => plane.signedMeasure point < 0

/-- Classify one point by exact determinant sign, refusing exactly a degenerate witness plane. -/
noncomputable def sideOfPlane? (plane : ExactPlane) (point : CartesianPoint3) :
    Option PlaneSide := by
  classical
  exact
    if nondegenerate : plane.Nondegenerate then
      if positive : 0 < plane.signedMeasure point then some .positive
      else if negative : plane.signedMeasure point < 0 then some .negative
      else some .onPlane
    else none

/-- Exact positive characterization of the coordinate plane-side evaluator. -/
theorem sideOfPlane?_eq_some_iff (plane : ExactPlane) (point : CartesianPoint3)
    (side : PlaneSide) :
    plane.sideOfPlane? point = some side ↔ plane.PointHasSide point side := by
  classical
  by_cases nondegenerate : plane.Nondegenerate
  · by_cases positive : 0 < plane.signedMeasure point
    · have notNegative : ¬plane.signedMeasure point < 0 :=
        not_lt_of_ge positive.le
      have notZero : plane.signedMeasure point ≠ 0 := ne_of_gt positive
      cases side <;>
        simp [sideOfPlane?, PointHasSide, nondegenerate, positive,
          notNegative, notZero]
    · by_cases negative : plane.signedMeasure point < 0
      · have notZero : plane.signedMeasure point ≠ 0 := ne_of_lt negative
        cases side <;>
          simp [sideOfPlane?, PointHasSide, nondegenerate, positive,
            negative, notZero]
      · have zero : plane.signedMeasure point = 0 :=
          le_antisymm (not_lt.mp positive) (not_lt.mp negative)
        cases side <;>
          simp [sideOfPlane?, PointHasSide, nondegenerate, zero]
  · cases side <;> simp [sideOfPlane?, PointHasSide, nondegenerate]

/-- Exact refusal characterization: determinant sign is total once the plane exists. -/
theorem sideOfPlane?_eq_none_iff (plane : ExactPlane) (point : CartesianPoint3) :
    plane.sideOfPlane? point = none ↔ ¬plane.Nondegenerate := by
  classical
  by_cases nondegenerate : plane.Nondegenerate
  · by_cases positive : 0 < plane.signedMeasure point
    · simp [sideOfPlane?, nondegenerate, positive]
    · by_cases negative : plane.signedMeasure point < 0 <;>
        simp [sideOfPlane?, nondegenerate, positive, negative]
  · simp [sideOfPlane?, nondegenerate]

/-- A nondegenerate exact plane assigns one and only one side to every exact point. -/
theorem exists_unique_side (plane : ExactPlane) (point : CartesianPoint3)
    (nondegenerate : plane.Nondegenerate) :
    ∃! side, plane.PointHasSide point side := by
  classical
  have notNone : plane.sideOfPlane? point ≠ none := by
    intro none
    exact ((plane.sideOfPlane?_eq_none_iff point).mp none) nondegenerate
  cases computed : plane.sideOfPlane? point with
  | none => exact False.elim (notNone computed)
  | some side =>
      refine ⟨side, (plane.sideOfPlane?_eq_some_iff point side).mp computed, ?_⟩
      intro other otherJudgment
      have otherComputed :=
        (plane.sideOfPlane?_eq_some_iff point other).mpr otherJudgment
      rw [computed] at otherComputed
      exact (Option.some.inj otherComputed).symm

end ExactPlane

/-! ## Indexed exact coordinate collection -/

/-- Independent meaning of one atom-indexed point in a fixed spatial configuration. -/
def SpatialPointAt (spatial : SpatialConfiguration) (atom : ℕ)
    (point : CartesianPoint3) : Prop :=
  spatial.positions[atom]? = some point

/-- Independent pointwise meaning of an ordered coordinate collection. -/
def SpatialPointsAt (spatial : SpatialConfiguration) (atoms : List ℕ)
    (points : List CartesianPoint3) : Prop :=
  List.Forall₂ (SpatialPointAt spatial) atoms points

/-- Collect exact coordinates in the ring traversal's atom order. -/
def spatialPointsAt? (spatial : SpatialConfiguration) (atoms : List ℕ) :
    Option (List CartesianPoint3) :=
  atoms.mapM fun atom => spatial.positions[atom]?

private theorem mapM_spatialPointAt?_eq_some_iff_forall₂
    (spatial : SpatialConfiguration) :
    ∀ (atoms : List ℕ) (points : List CartesianPoint3),
      atoms.mapM (fun atom => spatial.positions[atom]?) = some points ↔
        List.Forall₂ (SpatialPointAt spatial) atoms points
  | [], points => by
      constructor
      · intro computed
        simp at computed
        subst points
        exact .nil
      · intro related
        cases related
        rfl
  | atom :: atoms, points => by
      constructor
      · intro computed
        rw [List.mapM_cons] at computed
        cases pointEq : spatial.positions[atom]? with
        | none => simp [pointEq] at computed
        | some point =>
            cases pointsEq : atoms.mapM (fun next => spatial.positions[next]?) with
            | none => simp [pointEq, pointsEq] at computed
            | some tail =>
                simp [pointEq, pointsEq] at computed
                subst points
                exact .cons pointEq
                  ((mapM_spatialPointAt?_eq_some_iff_forall₂
                    spatial atoms tail).mp pointsEq)
      · intro related
        obtain ⟨point, tail, headRelated, tailRelated, rfl⟩ :=
          List.forall₂_cons_left_iff.mp related
        rw [List.mapM_cons, headRelated,
          (mapM_spatialPointAt?_eq_some_iff_forall₂
            spatial atoms tail).mpr tailRelated]
        rfl

/-- Coordinate collection is exact against the independent indexed relation. -/
theorem spatialPointsAt?_eq_some_iff (spatial : SpatialConfiguration)
    (atoms : List ℕ) (points : List CartesianPoint3) :
    spatialPointsAt? spatial atoms = some points ↔
      SpatialPointsAt spatial atoms points := by
  exact mapM_spatialPointAt?_eq_some_iff_forall₂ spatial atoms points

/-- Coordinate refusal is exactly the absence of any point list satisfying all indexed lookups. -/
theorem spatialPointsAt?_eq_none_iff (spatial : SpatialConfiguration)
    (atoms : List ℕ) :
    spatialPointsAt? spatial atoms = none ↔
      ¬∃ points, SpatialPointsAt spatial atoms points := by
  constructor
  · intro computed ⟨points, related⟩
    have someEq := (spatialPointsAt?_eq_some_iff spatial atoms points).mpr related
    rw [computed] at someEq
    contradiction
  · intro absent
    cases computed : spatialPointsAt? spatial atoms with
    | none => rfl
    | some points =>
        exact False.elim (absent ⟨points,
          (spatialPointsAt?_eq_some_iff spatial atoms points).mp computed⟩)

theorem SpatialPointsAt.length_eq (spatial : SpatialConfiguration)
    {atoms : List ℕ} {points : List CartesianPoint3}
    (related : SpatialPointsAt spatial atoms points) :
    points.length = atoms.length :=
  (List.Forall₂.length_eq related).symm

/-! ## Exact plane-side extraction for an ordered ring traversal -/

/-- The witness plane is spanned by actual ring coordinates, rather than by three unrelated
external points.  Together with nondegeneracy this supplies a noncollinear ring-point triple. -/
def ExactPlane.SpannedByRingPoints (plane : ExactPlane)
    (points : List CartesianPoint3) : Prop :=
  plane.first ∈ points ∧ plane.second ∈ points ∧ plane.third ∈ points

/-- Independent meaning of a complete side list for atom-indexed exact coordinates. -/
def RingSidesOfPlane (spatial : SpatialConfiguration) (atoms : List ℕ)
    (plane : ExactPlane) (sides : List PlaneSide) : Prop :=
  plane.Nondegenerate ∧
    ∃ points,
      SpatialPointsAt spatial atoms points ∧
      points.Nodup ∧
      plane.SpannedByRingPoints points ∧
      List.Forall₂ plane.PointHasSide points sides

private theorem mapM_sideOfPlane?_eq_some_iff_forall₂ (plane : ExactPlane) :
    ∀ (points : List CartesianPoint3) (sides : List PlaneSide),
      points.mapM plane.sideOfPlane? = some sides ↔
        List.Forall₂ plane.PointHasSide points sides
  | [], sides => by
      constructor
      · intro computed
        simp at computed
        subst sides
        exact .nil
      · intro related
        cases related
        rfl
  | point :: points, sides => by
      constructor
      · intro computed
        rw [List.mapM_cons] at computed
        cases sideEq : plane.sideOfPlane? point with
        | none => simp [sideEq] at computed
        | some side =>
            cases sidesEq : points.mapM plane.sideOfPlane? with
            | none => simp [sideEq, sidesEq] at computed
            | some tail =>
                simp [sideEq, sidesEq] at computed
                subst sides
                exact .cons
                  ((plane.sideOfPlane?_eq_some_iff point side).mp sideEq)
                  ((mapM_sideOfPlane?_eq_some_iff_forall₂
                    plane points tail).mp sidesEq)
      · intro related
        obtain ⟨side, tail, headRelated, tailRelated, rfl⟩ :=
          List.forall₂_cons_left_iff.mp related
        rw [List.mapM_cons,
          (plane.sideOfPlane?_eq_some_iff point side).mpr headRelated,
          (mapM_sideOfPlane?_eq_some_iff_forall₂
            plane points tail).mpr tailRelated]
        rfl

/-- Read all ring points and derive their exact plane sides.  The explicit outer gate ensures
that even an empty atom list cannot make a degenerate witness plane appear successful. -/
noncomputable def ringSidesOfPlane? (spatial : SpatialConfiguration) (atoms : List ℕ)
    (plane : ExactPlane) : Option (List PlaneSide) := by
  classical
  exact
    if nondegenerate : plane.Nondegenerate then do
      let points ← spatialPointsAt? spatial atoms
      if admissible : points.Nodup ∧ plane.SpannedByRingPoints points then
        points.mapM plane.sideOfPlane?
      else
        none
    else none

/-- Exact positive characterization of ordered ring plane-side extraction. -/
theorem ringSidesOfPlane?_eq_some_iff (spatial : SpatialConfiguration)
    (atoms : List ℕ) (plane : ExactPlane) (sides : List PlaneSide) :
    ringSidesOfPlane? spatial atoms plane = some sides ↔
      RingSidesOfPlane spatial atoms plane sides := by
  classical
  by_cases nondegenerate : plane.Nondegenerate
  · constructor
    · intro computed
      unfold ringSidesOfPlane? at computed
      simp only [dif_pos nondegenerate] at computed
      cases pointsEq : spatialPointsAt? spatial atoms with
      | none => simp [pointsEq] at computed
      | some points =>
          by_cases admissible : points.Nodup ∧ plane.SpannedByRingPoints points
          · have sidesEq : points.mapM plane.sideOfPlane? = some sides := by
              simpa [pointsEq, admissible] using computed
            exact ⟨nondegenerate, points,
              (spatialPointsAt?_eq_some_iff spatial atoms points).mp pointsEq,
              admissible.1, admissible.2,
              (mapM_sideOfPlane?_eq_some_iff_forall₂
                plane points sides).mp sidesEq⟩
          · simp [pointsEq, admissible] at computed
    · rintro ⟨_, points, pointsRelated, pointsNodup, planeSpanned, sidesRelated⟩
      have pointsEq :=
        (spatialPointsAt?_eq_some_iff spatial atoms points).mpr pointsRelated
      have sidesEq :=
        (mapM_sideOfPlane?_eq_some_iff_forall₂
          plane points sides).mpr sidesRelated
      simp [ringSidesOfPlane?, nondegenerate, pointsEq, pointsNodup,
        planeSpanned, sidesEq]
  · simp [ringSidesOfPlane?, RingSidesOfPlane, nondegenerate]

/-- Ring-side refusal is exhaustive against the independent coordinate-and-sign judgment. -/
theorem ringSidesOfPlane?_eq_none_iff (spatial : SpatialConfiguration)
    (atoms : List ℕ) (plane : ExactPlane) :
    ringSidesOfPlane? spatial atoms plane = none ↔
      ¬∃ sides, RingSidesOfPlane spatial atoms plane sides := by
  classical
  constructor
  · intro computed ⟨sides, judged⟩
    have someEq :=
      (ringSidesOfPlane?_eq_some_iff spatial atoms plane sides).mpr judged
    rw [computed] at someEq
    contradiction
  · intro absent
    cases computed : ringSidesOfPlane? spatial atoms plane with
    | none => rfl
    | some sides =>
        exact False.elim (absent ⟨sides,
          (ringSidesOfPlane?_eq_some_iff spatial atoms plane sides).mp computed⟩)

theorem RingSidesOfPlane.length_eq (spatial : SpatialConfiguration)
    {atoms : List ℕ} {plane : ExactPlane} {sides : List PlaneSide}
    (judged : RingSidesOfPlane spatial atoms plane sides) :
    sides.length = atoms.length := by
  rcases judged with ⟨_, points, pointsRelated, _, _, sidesRelated⟩
  calc
    sides.length = points.length := (List.Forall₂.length_eq sidesRelated).symm
    _ = atoms.length := (List.Forall₂.length_eq pointsRelated).symm

/-- Exact ring-side evidence at a fixed plane is unique. -/
theorem RingSidesOfPlane.unique (spatial : SpatialConfiguration)
    (atoms : List ℕ) (plane : ExactPlane) {left right : List PlaneSide}
    (leftJudged : RingSidesOfPlane spatial atoms plane left)
    (rightJudged : RingSidesOfPlane spatial atoms plane right) :
    left = right := by
  classical
  have leftEq :=
    (ringSidesOfPlane?_eq_some_iff spatial atoms plane left).mpr leftJudged
  have rightEq :=
    (ringSidesOfPlane?_eq_some_iff spatial atoms plane right).mpr rightJudged
  rw [leftEq] at rightEq
  exact Option.some.inj rightEq

end BlueBookP94.CoordinateRing
end TetraStereo.OneCenter
