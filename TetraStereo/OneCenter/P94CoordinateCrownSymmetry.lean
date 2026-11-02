import TetraStereo.OneCenter.P94CoordinateRingGeometry

set_option autoImplicit false

namespace TetraStereo.OneCenter

open BlueBookP94

/-!
# Exact finite coordinate symmetry for P-94 crown conformations

P-94.3.2.4 calls a crown a saturated even ring of at least eight atoms whose atoms alternate
between two parallel planes and are symmetrically equivalent.  The authority states those
geometric conditions, but it does not give an executable test for "symmetrically equivalent".

This module supplies that missing mathematical test for an ordered finite ring.  Two planes are
represented by one nonzero exact rational normal and two distinct affine levels.  Even and odd
positions in the cyclic traversal lie on the two levels.  Symmetric equivalence is witnessed by
the one-step cyclic shift preserving every pairwise squared distance.  Since that shift generates
the transitive cyclic action on the ring positions, all positions are metrically equivalent.
Coordinate `Nodup` excludes collapsed, coincident atom positions.

The cyclic-isometry criterion is an explicit exact mathematical completion of the source phrase;
it is not attributed to IUPAC as a separately printed algorithm or as a claim that every crown has
only cyclic point-group symmetry.  Molecular cyclicity and saturation remain separate constitution
gates in the molecule-facing P-94 layer.
-/

namespace BlueBookP94.CoordinateRing

/-! ## Exact alternating parallel planes -/

/-- Exact squared Euclidean distance between rational spatial points. -/
def crownSquaredDistance (left right : CartesianPoint3) : ℚ :=
  let difference := CartesianPoint3.displacement left right
  RationalVector3.dot difference difference

/-- Exact affine coordinate of a point along a proposed plane normal. -/
def pointProjection (normal : RationalVector3) (point : CartesianPoint3) : ℚ :=
  normal.x * point.x + normal.y * point.y + normal.z * point.z

/-- Independent exact meaning of "the ring atoms lie alternately in each of two parallel planes".

The nonzero normal determines a family of parallel affine planes.  Distinct even and odd levels
select two different members of that family, and traversal parity assigns every ring position to
exactly one of them.  For an even cyclic traversal, the closing pair also has opposite parity. -/
def LiesAlternatelyInParallelPlanes (points : List CartesianPoint3) : Prop :=
  ∃ normal : RationalVector3, ∃ evenLevel oddLevel : ℚ,
    0 < RationalVector3.dot normal normal ∧
      evenLevel ≠ oddLevel ∧
      ∀ index : Fin points.length,
        pointProjection normal (points.get index) =
          if Even index.val then evenLevel else oddLevel

/-! ## A finite exact interpretation of symmetric equivalence -/

/-- Reinterpret an index after rotating a list; rotation preserves its length exactly. -/
private def rotatedIndex (points : List CartesianPoint3) (index : Fin points.length) :
    Fin (points.rotate 1).length :=
  ⟨index.val, by simp⟩

/-- The one-step cyclic permutation of ring positions is an exact metric isometry on the complete
finite point configuration.  Testing all pairs, rather than only ring edges, prevents an
edge-equilateral but globally asymmetric polygon from being accepted as symmetric. -/
def CyclicShiftPreservesSquaredDistances (points : List CartesianPoint3) : Prop :=
  ∀ left right : Fin points.length,
    crownSquaredDistance (points.get left) (points.get right) =
      crownSquaredDistance
        ((points.rotate 1).get (rotatedIndex points left))
        ((points.rotate 1).get (rotatedIndex points right))

/-- Chemically honest finite coordinate meaning of the source's "symmetrically equivalent"
ring atoms: distinct spatial positions on which the traversal's cyclic generator acts by a
complete pairwise-distance isometry. -/
def CyclicallySymmetricallyEquivalent (points : List CartesianPoint3) : Prop :=
  points.Nodup ∧ CyclicShiftPreservesSquaredDistances points

/-! ## Canonical plane-side ledger and exact evaluator -/

/-- Alternating off-plane labels.  The Boolean chooses the label of the first traversal position.
The labels are orientation conventions; reversing the witness normal exchanges them without
changing the two physical planes or the crown classification. -/
def alternatingPlaneSides : Bool → ℕ → List PlaneSide
  | _, 0 => []
  | firstPositive, count + 1 =>
      (if firstPositive then .positive else .negative) ::
        alternatingPlaneSides (!firstPositive) count

@[simp] theorem alternatingPlaneSides_length (firstPositive : Bool) (count : ℕ) :
    (alternatingPlaneSides firstPositive count).length = count := by
  induction count generalizing firstPositive with
  | zero => simp [alternatingPlaneSides]
  | succ count ih =>
      simp [alternatingPlaneSides, ih]

/-- The syntactic ledger generated above satisfies the independent P-94 alternating-side
relation for every finite length. -/
theorem alternatingPlaneSides_alternating (firstPositive : Bool) (count : ℕ) :
    AlternatingOffPlane (alternatingPlaneSides firstPositive count) := by
  induction count generalizing firstPositive with
  | zero => simp [alternatingPlaneSides, AlternatingOffPlane]
  | succ count ih =>
      cases count with
      | zero =>
          cases firstPositive <;>
            simp [alternatingPlaneSides, AlternatingOffPlane]
      | succ count =>
          cases firstPositive with
          | false =>
              change OppositeSides .negative .positive ∧
                AlternatingOffPlane
                  (alternatingPlaneSides true (Nat.succ count))
              exact ⟨by simp [OppositeSides], ih true⟩
          | true =>
              change OppositeSides .positive .negative ∧
                AlternatingOffPlane
                  (alternatingPlaneSides false (Nat.succ count))
              exact ⟨by simp [OppositeSides], ih false⟩

/-- Canonical side ledger for a coordinate crown.  We orient the otherwise unoriented pair so
that traversal position zero is positive. -/
def canonicalCrownSides (points : List CartesianPoint3) : List PlaneSide :=
  alternatingPlaneSides true points.length

@[simp] theorem canonicalCrownSides_length (points : List CartesianPoint3) :
    (canonicalCrownSides points).length = points.length := by
  simp [canonicalCrownSides]

theorem canonicalCrownSides_alternating (points : List CartesianPoint3) :
    AlternatingOffPlane (canonicalCrownSides points) := by
  exact alternatingPlaneSides_alternating true points.length

/-- Complete coordinate-only crown geometry.  Saturation and molecular ring validity are
deliberately absent because they are constitutional, not coordinate, facts. -/
def ExactCrownCoordinates (points : List CartesianPoint3) : Prop :=
  8 ≤ points.length ∧
    Even points.length ∧
    LiesAlternatelyInParallelPlanes points ∧
    CyclicallySymmetricallyEquivalent points

/-- Independent positive judgment for the canonical side ledger derived from exact crown
coordinates. -/
def CoordinateCrownSides (points : List CartesianPoint3) (sides : List PlaneSide) : Prop :=
  ExactCrownCoordinates points ∧ canonicalCrownSides points = sides

/-- Specification-level exact evaluator.  It has no tolerance or floating-point branch.  The
classical decision is over the explicit rational finite-geometry proposition above. -/
noncomputable def coordinateCrownSides? (points : List CartesianPoint3) :
    Option (List PlaneSide) := by
  classical
  exact if exact : ExactCrownCoordinates points then
    some (canonicalCrownSides points)
  else none

/-- Successful coordinate crown perception is exactly the independent finite judgment. -/
theorem coordinateCrownSides?_eq_some_iff (points : List CartesianPoint3)
    (sides : List PlaneSide) :
    coordinateCrownSides? points = some sides ↔ CoordinateCrownSides points sides := by
  classical
  by_cases exact : ExactCrownCoordinates points
  · simp [coordinateCrownSides?, CoordinateCrownSides, exact]
  · simp [coordinateCrownSides?, CoordinateCrownSides, exact]

/-- Refusal is exhaustive: precisely no exact crown-coordinate judgment exists. -/
theorem coordinateCrownSides?_eq_none_iff (points : List CartesianPoint3) :
    coordinateCrownSides? points = none ↔ ¬ExactCrownCoordinates points := by
  classical
  by_cases exact : ExactCrownCoordinates points <;>
    simp [coordinateCrownSides?, exact]

namespace CoordinateCrownSides

theorem length_eq {points : List CartesianPoint3} {sides : List PlaneSide}
    (judged : CoordinateCrownSides points sides) :
    sides.length = points.length := by
  rw [← judged.2]
  exact canonicalCrownSides_length points

/-- Exact coordinate success supplies the geometric clauses of the existing independent P-94
crown relation with any separately proved meaning of symmetric equivalence.  This is the theorem
the molecule layer should use when it conjoins spatial symmetry with constitution/label symmetry. -/
theorem isCrown_of_symmetricallyEquivalent
    {points : List CartesianPoint3} {sides : List PlaneSide}
    (judged : CoordinateCrownSides points sides)
    (symmetricallyEquivalent : Prop) (symmetric : symmetricallyEquivalent) :
    IsCrown sides symmetricallyEquivalent := by
  rcases judged with ⟨⟨atLeastEight, even, _parallelPlanes, _spatialSymmetry⟩, sidesEq⟩
  rw [← sidesEq]
  refine ⟨?_, ?_, canonicalCrownSides_alternating points, symmetric⟩
  · simpa using atLeastEight
  · simpa using even

/-- Spatial specialization of `isCrown_of_symmetricallyEquivalent`.  The caller must still prove
the molecule is a saturated valid cyclic carrier; a chemically labeled use may strengthen the
symmetry proposition through the generic theorem above. -/
theorem isCrown {points : List CartesianPoint3} {sides : List PlaneSide}
    (judged : CoordinateCrownSides points sides) :
    IsCrown sides (CyclicallySymmetricallyEquivalent points) := by
  exact isCrown_of_symmetricallyEquivalent judged
    (CyclicallySymmetricallyEquivalent points) judged.1.2.2.2

end CoordinateCrownSides

end BlueBookP94.CoordinateRing
end TetraStereo.OneCenter
