import TetraStereo.OneCenter.IR9FourCoordinateSpatialRoles

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.TrigonalBipyramid5SpatialPerception

open FourCoordinateSpatialPerception
open FourCoordinateSpatialRoles

/-!
# Exact coordinate perception for idealized TBPY-5

The recognizer receives one center and five unordered donor coordinates.  It accepts exactly one
canonical donor pair as the axial pair when those donors are antiparallel at the center, the three
remaining donors and the center are coplanar, and every equatorial donor pair gives a nonzero
viewed determinant about either selected axial direction.  The last condition is the exact
non-boundary condition needed by the physical A/C construction; no metric tolerance is invented.
-/

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

end Frame

/-- Canonical unordered pairs of the five donor positions. -/
def axialPairs : List (Fin 5 × Fin 5) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2),
    (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

theorem axialPairs_nodup : axialPairs.Nodup := by decide

theorem axialPair_distinct {pair : Fin 5 × Fin 5} (member : pair ∈ axialPairs) :
    pair.1 ≠ pair.2 := by
  simp [axialPairs] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

/-- The three donor positions outside a canonical axial pair. -/
def remainingPositions (pair : Fin 5 × Fin 5) : List (Fin 5) :=
  [0, 1, 2, 3, 4].filter fun position =>
    position != pair.1 && position != pair.2

theorem remainingPositions_length
    {pair : Fin 5 × Fin 5} (member : pair ∈ axialPairs) :
    (remainingPositions pair).length = 3 := by
  simp [axialPairs] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

/-- Original five-position index of a normalized equatorial position.  Its default branch is
unreachable for a canonical axial pair. -/
def equatorialOriginalPosition (pair : Fin 5 × Fin 5) (position : Fin 3) : Fin 5 :=
  ((remainingPositions pair)[position.val]?).getD 0

theorem equatorialOriginalPosition_ne_first
    {pair : Fin 5 × Fin 5} (member : pair ∈ axialPairs) (position : Fin 3) :
    equatorialOriginalPosition pair position ≠ pair.1 := by
  simp [axialPairs] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    fin_cases position <;> decide

theorem equatorialOriginalPosition_ne_second
    {pair : Fin 5 × Fin 5} (member : pair ∈ axialPairs) (position : Fin 3) :
    equatorialOriginalPosition pair position ≠ pair.2 := by
  simp [axialPairs] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    fin_cases position <;> decide

theorem equatorialOriginalPosition_injective
    {pair : Fin 5 × Fin 5} (member : pair ∈ axialPairs) :
    Function.Injective (equatorialOriginalPosition pair) := by
  simp [axialPairs] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    intro first second <;> fin_cases first <;> fin_cases second <;>
      simp [equatorialOriginalPosition, remainingPositions]

def equatorialPoint (frame : Frame) (pair : Fin 5 × Fin 5) (position : Fin 3) :
    CartesianPoint3 :=
  frame.donorAt (equatorialOriginalPosition pair position)

/-- Exact center-antiparallel relation for two TBPY-5 donor positions. -/
def IsCenterAntiparallelPair
    (frame : Frame) (first second : Fin 5) : Prop :=
  first ≠ second ∧
  ((frame.donorAt first).y - frame.center.y) *
        ((frame.donorAt second).z - frame.center.z) -
      ((frame.donorAt first).z - frame.center.z) *
        ((frame.donorAt second).y - frame.center.y) = 0 ∧
  ((frame.donorAt first).z - frame.center.z) *
        ((frame.donorAt second).x - frame.center.x) -
      ((frame.donorAt first).x - frame.center.x) *
        ((frame.donorAt second).z - frame.center.z) = 0 ∧
  ((frame.donorAt first).x - frame.center.x) *
        ((frame.donorAt second).y - frame.center.y) -
      ((frame.donorAt first).y - frame.center.y) *
        ((frame.donorAt second).x - frame.center.x) = 0 ∧
  ((frame.donorAt first).x - frame.center.x) *
        ((frame.donorAt second).x - frame.center.x) +
      ((frame.donorAt first).y - frame.center.y) *
        ((frame.donorAt second).y - frame.center.y) +
      ((frame.donorAt first).z - frame.center.z) *
        ((frame.donorAt second).z - frame.center.z) < 0

instance isCenterAntiparallelPairDecidable
    (frame : Frame) (first second : Fin 5) :
    Decidable (IsCenterAntiparallelPair frame first second) := by
  unfold IsCenterAntiparallelPair
  infer_instance

/-- Coplanarity of the center and all three equatorial donors. -/
def EquatorialCenterCoplanar (frame : Frame) (pair : Fin 5 × Fin 5) : Prop :=
  CartesianPoint3.orientedVolume
    (equatorialPoint frame pair 0) (equatorialPoint frame pair 1)
    (equatorialPoint frame pair 2) frame.center = 0

instance equatorialCenterCoplanarDecidable
    (frame : Frame) (pair : Fin 5 × Fin 5) :
    Decidable (EquatorialCenterCoplanar frame pair) := by
  unfold EquatorialCenterCoplanar
  infer_instance

/-- The trigonal donor plane is perpendicular to the unique axial reference line, exactly as in
IR-9.3.4.5.  It suffices to use the first canonical axial endpoint because antiparallelism makes
the other endpoint collinear with it. -/
def EquatorialPlanePerpendicular (frame : Frame) (pair : Fin 5 × Fin 5) : Prop :=
  ∀ position : Fin 3,
    ((equatorialPoint frame pair position).x - frame.center.x) *
          ((frame.donorAt pair.1).x - frame.center.x) +
        ((equatorialPoint frame pair position).y - frame.center.y) *
          ((frame.donorAt pair.1).y - frame.center.y) +
        ((equatorialPoint frame pair position).z - frame.center.z) *
          ((frame.donorAt pair.1).z - frame.center.z) = 0

instance equatorialPlanePerpendicularDecidable
    (frame : Frame) (pair : Fin 5 × Fin 5) :
    Decidable (EquatorialPlanePerpendicular frame pair) := by
  unfold EquatorialPlanePerpendicular
  infer_instance

/-- Viewed determinant for two equatorial sites and one axial viewpoint. -/
def progressionDeterminant
    (frame : Frame) (pair : Fin 5 × Fin 5)
    (viewpoint : Fin 5) (first second : Fin 3) : ℚ :=
  CartesianPoint3.orientedVolume
    (equatorialPoint frame pair first) (equatorialPoint frame pair second)
    (frame.donorAt viewpoint) frame.center

/-- Exact non-boundary equatorial geometry for either axial viewpoint. -/
def EquatorialProgressionsNondegenerate
    (frame : Frame) (pair : Fin 5 × Fin 5) : Prop :=
  ∀ viewpoint, viewpoint = pair.1 ∨ viewpoint = pair.2 →
    ∀ first second : Fin 3, first ≠ second →
      progressionDeterminant frame pair viewpoint first second ≠ 0

instance equatorialProgressionsNondegenerateDecidable
    (frame : Frame) (pair : Fin 5 × Fin 5) :
    Decidable (EquatorialProgressionsNondegenerate frame pair) := by
  unfold EquatorialProgressionsNondegenerate
  infer_instance

/-- Independent exact idealized TBPY-5 partition judgment. -/
def IsAxialPartition (frame : Frame) (pair : Fin 5 × Fin 5) : Prop :=
  pair ∈ axialPairs ∧
    IsCenterAntiparallelPair frame pair.1 pair.2 ∧
    EquatorialCenterCoplanar frame pair ∧
    EquatorialPlanePerpendicular frame pair ∧
    EquatorialProgressionsNondegenerate frame pair

instance isAxialPartitionDecidable (frame : Frame) (pair : Fin 5 × Fin 5) :
    Decidable (IsAxialPartition frame pair) := by
  unfold IsAxialPartition
  infer_instance

def axialPartition? (frame : Frame) (pair : Fin 5 × Fin 5) : Bool :=
  decide (IsAxialPartition frame pair)

@[simp] theorem axialPartition?_eq_true_iff
    (frame : Frame) (pair : Fin 5 × Fin 5) :
    axialPartition? frame pair = true ↔ IsAxialPartition frame pair := by
  simp [axialPartition?]

/-- The complete exact perception judgment, including uniqueness of the axial partition. -/
def Judgment (frame : Frame) (pair : Fin 5 × Fin 5) : Prop :=
  pair ∈ axialPairs ∧
    IsAxialPartition frame pair ∧
    ∀ other ∈ axialPairs, IsAxialPartition frame other → other = pair

def perceive? (frame : Frame) : Option (Fin 5 × Fin 5) :=
  uniqueSatisfying? axialPairs (axialPartition? frame)

theorem perceive?_eq_some_iff (frame : Frame) (pair : Fin 5 × Fin 5) :
    perceive? frame = some pair ↔ Judgment frame pair := by
  rw [perceive?, uniqueSatisfying?_eq_some_iff axialPairs
    (axialPartition? frame) axialPairs_nodup pair]
  simp only [axialPartition?_eq_true_iff]
  rfl

theorem perceive?_eq_none_iff (frame : Frame) :
    perceive? frame = none ↔ ¬ ∃ pair, Judgment frame pair := by
  constructor
  · intro absent ⟨pair, judged⟩
    have present := (perceive?_eq_some_iff frame pair).mpr judged
    rw [absent] at present
    contradiction
  · intro noJudgment
    cases computed : perceive? frame with
    | none => rfl
    | some pair =>
        exact False.elim (noJudgment ⟨pair,
          (perceive?_eq_some_iff frame pair).mp computed⟩)

/-- Every exact perceived partition supplies a nonzero determinant for any two distinct
equatorial sites from either axial viewpoint. -/
theorem progressionDeterminant_ne_zero_of_judgment
    {frame : Frame} {pair : Fin 5 × Fin 5}
    (judged : Judgment frame pair)
    {viewpoint : Fin 5} (viewpointAxial : viewpoint = pair.1 ∨ viewpoint = pair.2)
    {first second : Fin 3} (different : first ≠ second) :
    progressionDeterminant frame pair viewpoint first second ≠ 0 :=
  judged.2.1.2.2.2.2 viewpoint viewpointAxial first second different

end TetraStereo.OneCenter.RedBookIR9.TrigonalBipyramid5SpatialPerception
