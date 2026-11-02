import TetraStereo.OneCenter.IR9TransBicappedOctahedron8SourceIndexCompleteness
import TetraStereo.OneCenter.IR9OctahedronSpatialPerception
import TetraStereo.OneCenter.LocalizedRule3Spatial

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.TransBicappedOctahedron8SpatialPerception

/-!
# Exact coordinate perception for idealized OCT-8

The source-side OCT-8 model has two caps on opposite octahedral faces and six base vertices in
three antipodal pairs.  This module recognizes that structure from one center and eight unordered
exact rational donor coordinates.  It exhausts every bijection from the independent eight-role
type to the eight input positions.

A valid placement has an exact OC-6 core, the three prescribed base pairs are centrally opposite,
the caps are centrally opposite, and each cap lies on the positive ray from the center through
the centroid direction of its incident triangular face.  All eight points must be distinct.  No
distance tolerance, unpublished short configuration index, or `A`/`C` convention is introduced.
-/

abbrev Position := TransBicappedOctahedron8SourceIndexCompleteness.Position

/-- Unordered exact OCT-8 coordinate input. -/
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

/-- A complete assignment of the eight independent structural roles to the eight input donors. -/
abbrev Placement := Position ≃ Fin 8

/-- Every role assignment; this is the finite exhaustive specification domain.  The ordering of
the proof-carrying equivalences is classical, so this list is intentionally noncomputable. -/
noncomputable def allPlacements : List Placement := Finset.univ.toList

theorem allPlacements_nodup : allPlacements.Nodup :=
  Finset.nodup_toList _

@[simp] theorem mem_allPlacements (placement : Placement) : placement ∈ allPlacements := by
  simp [allPlacements]

namespace Frame

/-- Coordinate occupying one independent OCT-8 role. -/
def pointAt (frame : Frame) (placement : Placement) (position : Position) : CartesianPoint3 :=
  frame.donorAt (placement position)

/-- The six base roles, in the three prescribed antipodal pairs, as an OC-6 frame. -/
def baseOctahedron (frame : Frame) (placement : Placement) :
    OctahedronSpatialPerception.Frame :=
  { center := frame.center
    donor0 := frame.pointAt placement (.baseVertex 0 0)
    donor1 := frame.pointAt placement (.baseVertex 1 0)
    donor2 := frame.pointAt placement (.baseVertex 0 1)
    donor3 := frame.pointAt placement (.baseVertex 1 1)
    donor4 := frame.pointAt placement (.baseVertex 0 2)
    donor5 := frame.pointAt placement (.baseVertex 1 2) }

end Frame

/-- Exact central opposition about a coordination center. -/
def CentralOpposite
    (center left right : CartesianPoint3) : Prop :=
  left ≠ right ∧
    left.x + right.x = 2 * center.x ∧
    left.y + right.y = 2 * center.y ∧
    left.z + right.z = 2 * center.z

instance centralOppositeDecidable
    (center left right : CartesianPoint3) :
    Decidable (CentralOpposite center left right) := by
  unfold CentralOpposite
  infer_instance

theorem centralOpposite_symmetric
    {center left right : CartesianPoint3}
    (opposite : CentralOpposite center left right) :
    CentralOpposite center right left := by
  rcases opposite with ⟨distinct, x, y, z⟩
  refine ⟨distinct.symm, ?_, ?_, ?_⟩ <;> linarith

/-- Three-times the vector from the center to a triangular face centroid.  Avoiding division keeps
the ray test integral over the exact rational coordinate field. -/
def faceCentroidDirection
    (center first second third : CartesianPoint3) : RationalVector3 :=
  { x := first.x + second.x + third.x - 3 * center.x
    y := first.y + second.y + third.y - 3 * center.y
    z := first.z + second.z + third.z - 3 * center.z }

/-- The cap is strictly outward on the ray through the incident face centroid.  Cross product zero
gives exact collinearity; the positive dot product selects the outward, noncentral half-ray. -/
def CapOnPositiveFaceCentroidRay
    (center cap first second third : CartesianPoint3) : Prop :=
  let faceDirection := faceCentroidDirection center first second third
  let capDirection := CartesianPoint3.displacement center cap
  (faceDirection.x ≠ 0 ∨ faceDirection.y ≠ 0 ∨ faceDirection.z ≠ 0) ∧
    (RationalVector3.cross faceDirection capDirection).x = 0 ∧
    (RationalVector3.cross faceDirection capDirection).y = 0 ∧
    (RationalVector3.cross faceDirection capDirection).z = 0 ∧
    0 < RationalVector3.dot faceDirection capDirection

instance capOnPositiveFaceCentroidRayDecidable
    (center cap first second third : CartesianPoint3) :
    Decidable (CapOnPositiveFaceCentroidRay center cap first second third) := by
  unfold CapOnPositiveFaceCentroidRay
  infer_instance

/-- Independent exact coordinate judgment for one complete OCT-8 role placement. -/
def IsExactPlacement (frame : Frame) (placement : Placement) : Prop :=
  Function.Injective (frame.pointAt placement) ∧
    OctahedronSpatialPerception.IsExactOctahedron (frame.baseOctahedron placement) ∧
    CentralOpposite frame.center
      (frame.pointAt placement (.cap 0))
      (frame.pointAt placement (.cap 1)) ∧
    (∀ pair : Fin 3,
      CentralOpposite frame.center
        (frame.pointAt placement (.baseVertex 0 pair))
        (frame.pointAt placement (.baseVertex 1 pair))) ∧
    CapOnPositiveFaceCentroidRay frame.center
      (frame.pointAt placement (.cap 0))
      (frame.pointAt placement (.baseVertex 0 0))
      (frame.pointAt placement (.baseVertex 0 1))
      (frame.pointAt placement (.baseVertex 0 2)) ∧
    CapOnPositiveFaceCentroidRay frame.center
      (frame.pointAt placement (.cap 1))
      (frame.pointAt placement (.baseVertex 1 0))
      (frame.pointAt placement (.baseVertex 1 1))
      (frame.pointAt placement (.baseVertex 1 2))

/-- Classical Boolean reflection of the exact judgment.  This is a specification decision, not
the production permutation enumerator. -/
noncomputable def placementJudgment? (frame : Frame) (placement : Placement) : Bool := by
  classical
  exact decide (IsExactPlacement frame placement)

@[simp] theorem placementJudgment?_eq_true_iff
    (frame : Frame) (placement : Placement) :
    placementJudgment? frame placement = true ↔ IsExactPlacement frame placement := by
  classical
  simp [placementJudgment?]

/-- Every accepted role placement.  Returning the full list keeps genuine geometric ambiguity
explicit instead of choosing a role frame and silently assuming uniqueness. -/
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

/-- Boolean shape recognition: at least one exhaustive role placement satisfies the independent
exact judgment. -/
noncomputable def recognize? (frame : Frame) : Bool :=
  allPlacements.any (placementJudgment? frame)

theorem recognize?_eq_true_iff_exists_placement (frame : Frame) :
    recognize? frame = true ↔ ∃ placement, IsExactPlacement frame placement := by
  classical
  simp [recognize?, List.any_eq_true]

/-- Exact semantic refusal: no assignment of the eight donor coordinates realizes OCT-8. -/
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

/-- Exhaustive positive/negative coordinate classification. -/
theorem exact_or_refused (frame : Frame) :
    (∃ placement, IsExactPlacement frame placement) ∨ Refused frame := by
  classical
  by_cases exact : ∃ placement, IsExactPlacement frame placement
  · exact .inl exact
  · exact .inr (by simpa [Refused] using exact)

/-- Every recognized role assignment uses eight distinct coordinate points. -/
theorem recognizedPlacement_pointAt_injective
    (frame : Frame) (placement : Placement)
    (recognized : placement ∈ recognizedPlacements frame) :
    Function.Injective (frame.pointAt placement) :=
  ((mem_recognizedPlacements_iff frame placement).mp recognized).1

/-- A recognized role assignment covers every input donor position exactly through its role
bijection; no coordinate is dropped by perception. -/
theorem recognizedPlacement_everyDonor_has_position
    (frame : Frame) (placement : Placement)
    (_recognized : placement ∈ recognizedPlacements frame)
    (donor : Fin 8) :
    ∃ position : Position, frame.pointAt placement position = frame.donorAt donor := by
  exact ⟨placement.symm donor, by simp [Frame.pointAt]⟩

end TetraStereo.OneCenter.RedBookIR9.TransBicappedOctahedron8SpatialPerception
