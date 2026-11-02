import TetraStereo.OneCenter.IR9CubeSourceIndexCompleteness
import TetraStereo.OneCenter.LocalizedRule3Spatial

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.CubeSpatialPerception

open CubeSourceIndexCompleteness

/-!
# Exact coordinate perception for the ideal CU-8 geometry

CU-8 has eight vertices indexed by three independent binary coordinate signs.  This module takes
one coordination center and eight unordered exact rational donor coordinates and exhausts every
bijection between those coordinates and the typed cube vertices.

For one accepted placement, the squared distance between any two vertices is the positive edge
square multiplied by their Hamming distance, and every body-diagonal pair is centered exactly at
the coordination center.  This is a rigid Euclidean cube criterion: rectangular boxes,
parallelepipeds, collapsed vertices, approximate shapes, and arbitrary tolerance choices are not
accepted.  The module performs no unpublished CU-8 short-index or `A`/`C` assignment.
-/

abbrev Position := CubeSourceIndexCompleteness.Position

/-- One center and eight unordered exact donor coordinates. -/
structure Frame where
  center : CartesianPoint3
  donor0 : CartesianPoint3
  donor1 : CartesianPoint3
  donor2 : CartesianPoint3
  donor3 : CartesianPoint3
  donor4 : CartesianPoint3
  donor5 : CartesianPoint3
  donor6 : CartesianPoint3
  donor7 : CartesianPoint3
  deriving DecidableEq, Repr

namespace Frame

def donorAt (frame : Frame) : Fin 8 → CartesianPoint3
  | 0 => frame.donor0
  | 1 => frame.donor1
  | 2 => frame.donor2
  | 3 => frame.donor3
  | 4 => frame.donor4
  | 5 => frame.donor5
  | 6 => frame.donor6
  | 7 => frame.donor7

end Frame

/-- A complete typed cube-role assignment to the eight unordered donors. -/
abbrev Placement := Position ≃ Fin 8

/-- Every role assignment.  Its proof-carrying order is classical, so this semantic list is
intentionally noncomputable. -/
noncomputable def allPlacements : List Placement := Finset.univ.toList

theorem allPlacements_nodup : allPlacements.Nodup :=
  Finset.nodup_toList _

@[simp] theorem mem_allPlacements (placement : Placement) : placement ∈ allPlacements := by
  simp [allPlacements]

namespace Frame

/-- Exact coordinate occupying one typed cube vertex. -/
def pointAt (frame : Frame) (placement : Placement) (position : Position) : CartesianPoint3 :=
  frame.donorAt (placement position)

end Frame

/-- Exact squared Euclidean distance over rational coordinates. -/
def squaredDistance (left right : CartesianPoint3) : ℚ :=
  let displacement := CartesianPoint3.displacement left right
  RationalVector3.dot displacement displacement

theorem squaredDistance_symmetric (left right : CartesianPoint3) :
    squaredDistance left right = squaredDistance right left := by
  simp [squaredDistance, CartesianPoint3.displacement, RationalVector3.dot]
  ring

/-- The body-diagonally opposite sign vertex. -/
def oppositePosition (position : Position) : Position :=
  fun coordinate => !(position coordinate)

theorem oppositePosition_involutive : Function.Involutive oppositePosition := by
  intro position
  funext coordinate
  simp [oppositePosition]

/-- Exact midpoint agreement with the supplied coordination center. -/
def CenteredOpposite
    (center left right : CartesianPoint3) : Prop :=
  left.x + right.x = 2 * center.x ∧
    left.y + right.y = 2 * center.y ∧
    left.z + right.z = 2 * center.z

instance centeredOppositeDecidable
    (center left right : CartesianPoint3) :
    Decidable (CenteredOpposite center left right) := by
  unfold CenteredOpposite
  infer_instance

/-- Fixed Hamming-neighbour of the all-negative typed origin. -/
def firstNeighbor : Position :=
  fun coordinate => decide (coordinate = 0)

/-- The edge-square reference fixed by the typed origin and its first typed neighbour. -/
def edgeSquared (frame : Frame) (placement : Placement) : ℚ :=
  squaredDistance
    (frame.pointAt placement origin)
    (frame.pointAt placement firstNeighbor)

/-- Independent exact ideal-cube judgment for one complete role placement. -/
def IsExactPlacement (frame : Frame) (placement : Placement) : Prop :=
  Function.Injective (frame.pointAt placement) ∧
    0 < edgeSquared frame placement ∧
    (∀ left right : Position,
      squaredDistance
          (frame.pointAt placement left)
          (frame.pointAt placement right) =
        (pairSignature left right : ℚ) * edgeSquared frame placement) ∧
    ∀ position : Position,
      CenteredOpposite frame.center
        (frame.pointAt placement position)
        (frame.pointAt placement (oppositePosition position))

/-- Boolean reflection of the independent exact judgment. -/
noncomputable def placementJudgment? (frame : Frame) (placement : Placement) : Bool := by
  classical
  exact decide (IsExactPlacement frame placement)

@[simp] theorem placementJudgment?_eq_true_iff
    (frame : Frame) (placement : Placement) :
    placementJudgment? frame placement = true ↔ IsExactPlacement frame placement := by
  classical
  simp [placementJudgment?]

/-- All accepted cube-role assignments.  Keeping the complete list preserves any geometric
ambiguity until the cube-symmetry theorem identifies its structural orbit. -/
noncomputable def recognizedPlacements (frame : Frame) : List Placement :=
  allPlacements.filter (placementJudgment? frame)

@[simp] theorem mem_recognizedPlacements_iff
    (frame : Frame) (placement : Placement) :
    placement ∈ recognizedPlacements frame ↔ IsExactPlacement frame placement := by
  classical
  simp [recognizedPlacements]

theorem recognizedPlacements_nodup (frame : Frame) :
    (recognizedPlacements frame).Nodup :=
  allPlacements_nodup.filter _

/-- Exact finite CU-8 shape recognition. -/
noncomputable def recognize? (frame : Frame) : Bool :=
  allPlacements.any (placementJudgment? frame)

theorem recognize?_eq_true_iff_exists_placement (frame : Frame) :
    recognize? frame = true ↔ ∃ placement, IsExactPlacement frame placement := by
  classical
  simp [recognize?, List.any_eq_true]

/-- Semantic refusal: no assignment of the eight donor coordinates is an exact ideal cube. -/
def Refused (frame : Frame) : Prop :=
  ∀ placement, ¬ IsExactPlacement frame placement

theorem recognize?_eq_false_iff_refusal (frame : Frame) :
    recognize? frame = false ↔ Refused frame := by
  constructor
  · intro rejected placement exact
    have accepted : recognize? frame = true :=
      (recognize?_eq_true_iff_exists_placement frame).mpr ⟨placement, exact⟩
    simp [rejected] at accepted
  · intro refusal
    apply Bool.eq_false_iff.mpr
    intro accepted
    rcases (recognize?_eq_true_iff_exists_placement frame).mp accepted with
      ⟨placement, exact⟩
    exact refusal placement exact

/-- Exhaustive positive/negative classification of every exact rational input frame. -/
theorem exact_or_refused (frame : Frame) :
    (∃ placement, IsExactPlacement frame placement) ∨ Refused frame := by
  classical
  by_cases exact : ∃ placement, IsExactPlacement frame placement
  · exact .inl exact
  · exact .inr (by simpa [Refused] using exact)

theorem recognizedPlacement_pointAt_injective
    (frame : Frame) (placement : Placement)
    (recognized : placement ∈ recognizedPlacements frame) :
    Function.Injective (frame.pointAt placement) :=
  ((mem_recognizedPlacements_iff frame placement).mp recognized).1

theorem recognizedPlacement_edgeSquared_positive
    (frame : Frame) (placement : Placement)
    (recognized : placement ∈ recognizedPlacements frame) :
    0 < edgeSquared frame placement :=
  ((mem_recognizedPlacements_iff frame placement).mp recognized).2.1

theorem recognizedPlacement_exact_metric
    (frame : Frame) (placement : Placement)
    (recognized : placement ∈ recognizedPlacements frame)
    (left right : Position) :
    squaredDistance
        (frame.pointAt placement left)
        (frame.pointAt placement right) =
      (pairSignature left right : ℚ) * edgeSquared frame placement :=
  ((mem_recognizedPlacements_iff frame placement).mp recognized).2.2.1 left right

theorem recognizedPlacement_centered_opposites
    (frame : Frame) (placement : Placement)
    (recognized : placement ∈ recognizedPlacements frame)
    (position : Position) :
    CenteredOpposite frame.center
      (frame.pointAt placement position)
      (frame.pointAt placement (oppositePosition position)) :=
  ((mem_recognizedPlacements_iff frame placement).mp recognized).2.2.2 position

/-- Every input donor appears at exactly one typed position in every accepted placement. -/
theorem recognizedPlacement_everyDonor_has_position
    (frame : Frame) (placement : Placement)
    (_recognized : placement ∈ recognizedPlacements frame)
    (donor : Fin 8) :
    ∃ position : Position,
      frame.pointAt placement position = frame.donorAt donor := by
  exact ⟨placement.symm donor, by simp [Frame.pointAt]⟩

end TetraStereo.OneCenter.RedBookIR9.CubeSpatialPerception
