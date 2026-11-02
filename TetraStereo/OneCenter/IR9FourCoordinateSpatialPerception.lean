import TetraStereo.OneCenter.IR9PolyhedralSemantics
import TetraStereo.OneCenter.AuthoritativeLocalizedTetrahedralDescriptor
import Mathlib.GroupTheory.Perm.Sign

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9.FourCoordinateSpatialPerception

/-!
# Exact four-coordinate spatial perception

IR-9.3.2.2 separates four-coordinate structures by exact incidence questions before any
nearest-idealized high-coordinate judgment is needed: are all five points coplanar, are only the
four donors coplanar, or—when the donors form a tetrahedron—is the center inside or outside that
donor tetrahedron?  This file makes that determinate mathematical part executable over exact
rational coordinates.

A center on a donor-tetrahedron face is refused.  Such a boundary frame is neither strictly
inside nor strictly outside and cannot support a nondegenerate stereochemical geometry judgment.
-/

/-- A self-contained exact affine coordinate-frame change. -/
structure FrameTransform where
  m00 : ℚ
  m01 : ℚ
  m02 : ℚ
  m10 : ℚ
  m11 : ℚ
  m12 : ℚ
  m20 : ℚ
  m21 : ℚ
  m22 : ℚ
  offset : CartesianPoint3
  deriving DecidableEq, Repr

namespace FrameTransform

def determinant (transform : FrameTransform) : ℚ :=
  transform.m00 * (transform.m11 * transform.m22 - transform.m12 * transform.m21) -
    transform.m01 * (transform.m10 * transform.m22 - transform.m12 * transform.m20) +
    transform.m02 * (transform.m10 * transform.m21 - transform.m11 * transform.m20)

def applyPoint (transform : FrameTransform) (point : CartesianPoint3) : CartesianPoint3 :=
  { x := transform.m00 * point.x + transform.m01 * point.y +
      transform.m02 * point.z + transform.offset.x
    y := transform.m10 * point.x + transform.m11 * point.y +
      transform.m12 * point.z + transform.offset.y
    z := transform.m20 * point.x + transform.m21 * point.y +
      transform.m22 * point.z + transform.offset.z }

theorem orientedVolume_applyPoint
    (transform : FrameTransform) (first second third fourth : CartesianPoint3) :
    CartesianPoint3.orientedVolume (transform.applyPoint first) (transform.applyPoint second)
        (transform.applyPoint third) (transform.applyPoint fourth) =
      transform.determinant * CartesianPoint3.orientedVolume first second third fourth := by
  simp [applyPoint, determinant, CartesianPoint3.orientedVolume]
  ring

end FrameTransform

/-- One center and four ordered donor positions.  The order is used only to compute affine
determinants; the geometric cases below are independent of the sign of that ordering. -/
structure Frame where
  center : CartesianPoint3
  donor0 : CartesianPoint3
  donor1 : CartesianPoint3
  donor2 : CartesianPoint3
  donor3 : CartesianPoint3
  deriving DecidableEq, Repr

namespace Frame

@[ext] theorem ext {left right : Frame}
    (center : left.center = right.center)
    (donor0 : left.donor0 = right.donor0)
    (donor1 : left.donor1 = right.donor1)
    (donor2 : left.donor2 = right.donor2)
    (donor3 : left.donor3 = right.donor3) : left = right := by
  cases left
  cases right
  simp_all

/-- Donor coordinates as a four-position function. -/
def donorAt (frame : Frame) : Fin 4 → CartesianPoint3
  | 0 => frame.donor0
  | 1 => frame.donor1
  | 2 => frame.donor2
  | 3 => frame.donor3

/-- Reorder only the donor presentation; the physical center is unchanged. -/
def reorder (frame : Frame) (permutation : Equiv.Perm (Fin 4)) : Frame :=
  { center := frame.center
    donor0 := frame.donorAt (permutation 0)
    donor1 := frame.donorAt (permutation 1)
    donor2 := frame.donorAt (permutation 2)
    donor3 := frame.donorAt (permutation 3) }

@[simp] theorem donorAt_reorder
    (frame : Frame) (permutation : Equiv.Perm (Fin 4)) (position : Fin 4) :
    (frame.reorder permutation).donorAt position = frame.donorAt (permutation position) := by
  fin_cases position <;> rfl

@[simp] theorem reorder_one (frame : Frame) : frame.reorder 1 = frame := by
  cases frame
  rfl

theorem reorder_reorder (frame : Frame) (first second : Equiv.Perm (Fin 4)) :
    (frame.reorder first).reorder second = frame.reorder (first * second) := by
  apply Frame.ext
  · rfl
  · change (frame.reorder first).donorAt (second 0) =
      frame.donorAt ((first * second) 0)
    rw [donorAt_reorder]
    rfl
  · change (frame.reorder first).donorAt (second 1) =
      frame.donorAt ((first * second) 1)
    rw [donorAt_reorder]
    rfl
  · change (frame.reorder first).donorAt (second 2) =
      frame.donorAt ((first * second) 2)
    rw [donorAt_reorder]
    rfl
  · change (frame.reorder first).donorAt (second 3) =
      frame.donorAt ((first * second) 3)
    rw [donorAt_reorder]
    rfl

/-- Oriented volume of the donor tetrahedron. -/
def donorVolume (frame : Frame) : ℚ :=
  CartesianPoint3.orientedVolume frame.donor0 frame.donor1 frame.donor2 frame.donor3

/-- The four Cramer/barycentric numerators obtained by replacing one donor by the center. -/
def centerVolume0 (frame : Frame) : ℚ :=
  CartesianPoint3.orientedVolume frame.center frame.donor1 frame.donor2 frame.donor3

def centerVolume1 (frame : Frame) : ℚ :=
  CartesianPoint3.orientedVolume frame.donor0 frame.center frame.donor2 frame.donor3

def centerVolume2 (frame : Frame) : ℚ :=
  CartesianPoint3.orientedVolume frame.donor0 frame.donor1 frame.center frame.donor3

def centerVolume3 (frame : Frame) : ℚ :=
  CartesianPoint3.orientedVolume frame.donor0 frame.donor1 frame.donor2 frame.center

def centerVolumeAt (frame : Frame) : Fin 4 → ℚ
  | 0 => frame.centerVolume0
  | 1 => frame.centerVolume1
  | 2 => frame.centerVolume2
  | 3 => frame.centerVolume3

/-- All five points lie in an affine plane (possibly a lower-dimensional one).  Testing every
four-point minor avoids choosing an arbitrary donor triple as a plane basis. -/
def AllFiveCoplanar (frame : Frame) : Prop :=
  frame.donorVolume = 0 ∧
    frame.centerVolume0 = 0 ∧ frame.centerVolume1 = 0 ∧
    frame.centerVolume2 = 0 ∧ frame.centerVolume3 = 0

/-- The donors are coplanar but the center is not in their common affine plane. -/
def DonorsCoplanarCenterDisplaced (frame : Frame) : Prop :=
  frame.donorVolume = 0 ∧ ¬frame.AllFiveCoplanar

/-- Strict barycentric interior, expressed without division.  Each replacement volume has the
same strict sign as the donor determinant. -/
def CenterStrictlyInside (frame : Frame) : Prop :=
  0 < frame.donorVolume * frame.centerVolume0 ∧
  0 < frame.donorVolume * frame.centerVolume1 ∧
  0 < frame.donorVolume * frame.centerVolume2 ∧
  0 < frame.donorVolume * frame.centerVolume3

/-- The center lies on at least one donor-tetrahedron face. -/
def CenterOnBoundary (frame : Frame) : Prop :=
  frame.centerVolume0 = 0 ∨ frame.centerVolume1 = 0 ∨
    frame.centerVolume2 = 0 ∨ frame.centerVolume3 = 0

/-- Strict exterior of a nondegenerate donor tetrahedron. -/
def CenterStrictlyOutside (frame : Frame) : Prop :=
  frame.donorVolume ≠ 0 ∧ ¬frame.CenterStrictlyInside ∧ ¬frame.CenterOnBoundary

theorem allFiveCoplanar_iff (frame : Frame) :
    frame.AllFiveCoplanar ↔
      frame.donorVolume = 0 ∧ ∀ position, frame.centerVolumeAt position = 0 := by
  constructor
  · rintro ⟨donor, first, second, third, fourth⟩
    refine ⟨donor, ?_⟩
    intro position
    fin_cases position <;> assumption
  · rintro ⟨donor, centers⟩
    exact ⟨donor, centers 0, centers 1, centers 2, centers 3⟩

theorem centerStrictlyInside_iff (frame : Frame) :
    frame.CenterStrictlyInside ↔
      ∀ position, 0 < frame.donorVolume * frame.centerVolumeAt position := by
  constructor
  · rintro ⟨first, second, third, fourth⟩
    intro position
    fin_cases position <;> assumption
  · intro allPositive
    exact ⟨allPositive 0, allPositive 1, allPositive 2, allPositive 3⟩

theorem centerOnBoundary_iff (frame : Frame) :
    frame.CenterOnBoundary ↔ ∃ position, frame.centerVolumeAt position = 0 := by
  constructor
  · rintro (first | second | third | fourth)
    · exact ⟨0, first⟩
    · exact ⟨1, second⟩
    · exact ⟨2, third⟩
    · exact ⟨3, fourth⟩
  · rintro ⟨position, zero⟩
    fin_cases position
    · exact Or.inl zero
    · exact Or.inr (Or.inl zero)
    · exact Or.inr (Or.inr (Or.inl zero))
    · exact Or.inr (Or.inr (Or.inr zero))

instance allFiveCoplanarDecidable (frame : Frame) : Decidable frame.AllFiveCoplanar := by
  unfold AllFiveCoplanar
  infer_instance

instance centerStrictlyInsideDecidable (frame : Frame) : Decidable frame.CenterStrictlyInside := by
  unfold CenterStrictlyInside
  infer_instance

instance centerOnBoundaryDecidable (frame : Frame) : Decidable frame.CenterOnBoundary := by
  unfold CenterOnBoundary
  infer_instance

/-- The four replacement volumes are barycentric numerators: their sum is exactly the donor
determinant. -/
theorem centerVolumes_sum (frame : Frame) :
    frame.centerVolume0 + frame.centerVolume1 +
        frame.centerVolume2 + frame.centerVolume3 =
      frame.donorVolume := by
  rcases frame with ⟨center, donor0, donor1, donor2, donor3⟩
  simp [centerVolume0, centerVolume1, centerVolume2, centerVolume3, donorVolume,
    CartesianPoint3.orientedVolume]
  ring

theorem centerStrictlyInside_donorVolume_ne
    {frame : Frame} (inside : frame.CenterStrictlyInside) :
    frame.donorVolume ≠ 0 := by
  intro zero
  simp [CenterStrictlyInside, zero] at inside

theorem centerStrictlyInside_not_boundary
    {frame : Frame} (inside : frame.CenterStrictlyInside) :
    ¬frame.CenterOnBoundary := by
  rcases inside with ⟨first, second, third, fourth⟩
  simp only [CenterOnBoundary]
  rintro (zero | zero | zero | zero)
  · simp [zero] at first
  · simp [zero] at second
  · simp [zero] at third
  · simp [zero] at fourth

/-- Apply an arbitrary exact affine coordinate-frame transform to all five points. -/
def map (frame : Frame) (transform : FrameTransform) : Frame :=
  { center := transform.applyPoint frame.center
    donor0 := transform.applyPoint frame.donor0
    donor1 := transform.applyPoint frame.donor1
    donor2 := transform.applyPoint frame.donor2
    donor3 := transform.applyPoint frame.donor3 }

@[simp] theorem donorVolume_map (frame : Frame) (transform : FrameTransform) :
    (frame.map transform).donorVolume = transform.determinant * frame.donorVolume := by
  exact FrameTransform.orientedVolume_applyPoint _ _ _ _ _

@[simp] theorem centerVolume0_map (frame : Frame) (transform : FrameTransform) :
    (frame.map transform).centerVolume0 =
      transform.determinant * frame.centerVolume0 := by
  exact FrameTransform.orientedVolume_applyPoint _ _ _ _ _

@[simp] theorem centerVolume1_map (frame : Frame) (transform : FrameTransform) :
    (frame.map transform).centerVolume1 =
      transform.determinant * frame.centerVolume1 := by
  exact FrameTransform.orientedVolume_applyPoint _ _ _ _ _

@[simp] theorem centerVolume2_map (frame : Frame) (transform : FrameTransform) :
    (frame.map transform).centerVolume2 =
      transform.determinant * frame.centerVolume2 := by
  exact FrameTransform.orientedVolume_applyPoint _ _ _ _ _

@[simp] theorem centerVolume3_map (frame : Frame) (transform : FrameTransform) :
    (frame.map transform).centerVolume3 =
      transform.determinant * frame.centerVolume3 := by
  exact FrameTransform.orientedVolume_applyPoint _ _ _ _ _

private theorem scaled_product_positive_iff
    (factor left right : ℚ) (factorNonzero : factor ≠ 0) :
    0 < (factor * left) * (factor * right) ↔ 0 < left * right := by
  have factorSquaredPositive : 0 < factor ^ 2 := sq_pos_of_ne_zero factorNonzero
  calc
    0 < (factor * left) * (factor * right) ↔ 0 < factor ^ 2 * (left * right) := by ring_nf
    _ ↔ 0 < left * right := mul_pos_iff_of_pos_left factorSquaredPositive

theorem allFiveCoplanar_map_iff
    (frame : Frame) (transform : FrameTransform)
    (determinantNonzero : transform.determinant ≠ 0) :
    (frame.map transform).AllFiveCoplanar ↔ frame.AllFiveCoplanar := by
  simp [AllFiveCoplanar, mul_eq_zero, determinantNonzero]

theorem donorsCoplanarCenterDisplaced_map_iff
    (frame : Frame) (transform : FrameTransform)
    (determinantNonzero : transform.determinant ≠ 0) :
    (frame.map transform).DonorsCoplanarCenterDisplaced ↔
      frame.DonorsCoplanarCenterDisplaced := by
  simp [DonorsCoplanarCenterDisplaced,
    allFiveCoplanar_map_iff frame transform determinantNonzero,
    mul_eq_zero, determinantNonzero]

theorem centerStrictlyInside_map_iff
    (frame : Frame) (transform : FrameTransform)
    (determinantNonzero : transform.determinant ≠ 0) :
    (frame.map transform).CenterStrictlyInside ↔ frame.CenterStrictlyInside := by
  simp only [CenterStrictlyInside, donorVolume_map, centerVolume0_map, centerVolume1_map,
    centerVolume2_map, centerVolume3_map,
    scaled_product_positive_iff _ _ _ determinantNonzero]

theorem centerOnBoundary_map_iff
    (frame : Frame) (transform : FrameTransform)
    (determinantNonzero : transform.determinant ≠ 0) :
    (frame.map transform).CenterOnBoundary ↔ frame.CenterOnBoundary := by
  simp [CenterOnBoundary, mul_eq_zero, determinantNonzero]

theorem centerStrictlyOutside_map_iff
    (frame : Frame) (transform : FrameTransform)
    (determinantNonzero : transform.determinant ≠ 0) :
    (frame.map transform).CenterStrictlyOutside ↔ frame.CenterStrictlyOutside := by
  simp [CenterStrictlyOutside, mul_eq_zero, determinantNonzero,
    centerStrictlyInside_map_iff frame transform determinantNonzero,
    centerOnBoundary_map_iff frame transform determinantNonzero]

end Frame

/-- Executable exact four-coordinate recognition.  Boundary centers are rejected rather than
rounded into either side of a donor face. -/
def observe? (frame : Frame) : Option FourCoordinateObservation :=
  if _donorCoplanar : frame.donorVolume = 0 then
    if _allCoplanar : frame.AllFiveCoplanar then
      some .allFiveCoplanar
    else
      some .donorsCoplanarCenterDisplaced
  else if _inside : frame.CenterStrictlyInside then
    some .donorsNoncoplanarCenterInsideDonorPolyhedron
  else if _boundary : frame.CenterOnBoundary then
    none
  else
    some .donorsNoncoplanarCenterOutsideDonorPolyhedron

/-- Independent mathematical judgment corresponding to the four source branches. -/
inductive Judgment (frame : Frame) : FourCoordinateObservation → Prop where
  | allFiveCoplanar
      (coplanar : frame.AllFiveCoplanar) :
      Judgment frame .allFiveCoplanar
  | donorsCoplanarCenterDisplaced
      (displaced : frame.DonorsCoplanarCenterDisplaced) :
      Judgment frame .donorsCoplanarCenterDisplaced
  | donorsNoncoplanarCenterInside
      (donorNoncoplanar : frame.donorVolume ≠ 0)
      (inside : frame.CenterStrictlyInside) :
      Judgment frame .donorsNoncoplanarCenterInsideDonorPolyhedron
  | donorsNoncoplanarCenterOutside
      (outside : frame.CenterStrictlyOutside) :
      Judgment frame .donorsNoncoplanarCenterOutsideDonorPolyhedron

@[simp] theorem judgment_allFiveCoplanar_iff (frame : Frame) :
    Judgment frame .allFiveCoplanar ↔ frame.AllFiveCoplanar := by
  constructor
  · intro judgment
    cases judgment with
    | allFiveCoplanar coplanar => exact coplanar
  · exact Judgment.allFiveCoplanar

@[simp] theorem judgment_donorsCoplanarCenterDisplaced_iff (frame : Frame) :
    Judgment frame .donorsCoplanarCenterDisplaced ↔
      frame.DonorsCoplanarCenterDisplaced := by
  constructor
  · intro judgment
    cases judgment with
    | donorsCoplanarCenterDisplaced displaced => exact displaced
  · exact Judgment.donorsCoplanarCenterDisplaced

@[simp] theorem judgment_donorsNoncoplanarCenterInside_iff (frame : Frame) :
    Judgment frame .donorsNoncoplanarCenterInsideDonorPolyhedron ↔
      frame.donorVolume ≠ 0 ∧ frame.CenterStrictlyInside := by
  constructor
  · intro judgment
    cases judgment with
    | donorsNoncoplanarCenterInside donorNoncoplanar inside =>
        exact ⟨donorNoncoplanar, inside⟩
  · rintro ⟨donorNoncoplanar, inside⟩
    exact Judgment.donorsNoncoplanarCenterInside donorNoncoplanar inside

@[simp] theorem judgment_donorsNoncoplanarCenterOutside_iff (frame : Frame) :
    Judgment frame .donorsNoncoplanarCenterOutsideDonorPolyhedron ↔
      frame.CenterStrictlyOutside := by
  constructor
  · intro judgment
    cases judgment with
    | donorsNoncoplanarCenterOutside outside => exact outside
  · exact Judgment.donorsNoncoplanarCenterOutside

theorem observe?_eq_some_iff (frame : Frame) (observation : FourCoordinateObservation) :
    observe? frame = some observation ↔ Judgment frame observation := by
  cases observation
  all_goals
    by_cases donorCoplanar : frame.donorVolume = 0
    · by_cases allCoplanar : frame.AllFiveCoplanar
      · simp [observe?, donorCoplanar, allCoplanar,
          Frame.DonorsCoplanarCenterDisplaced, Frame.CenterStrictlyOutside]
      · simp [observe?, donorCoplanar, allCoplanar,
          Frame.DonorsCoplanarCenterDisplaced, Frame.CenterStrictlyOutside]
    · have notAllCoplanar : ¬frame.AllFiveCoplanar :=
        fun allCoplanar => donorCoplanar allCoplanar.1
      by_cases inside : frame.CenterStrictlyInside
      · simp [observe?, donorCoplanar, inside,
          notAllCoplanar, Frame.DonorsCoplanarCenterDisplaced,
          Frame.CenterStrictlyOutside]
      · by_cases boundary : frame.CenterOnBoundary <;>
          simp [observe?, donorCoplanar, inside, boundary, notAllCoplanar,
            Frame.DonorsCoplanarCenterDisplaced, Frame.CenterStrictlyOutside]

theorem observe?_eq_none_iff (frame : Frame) :
    observe? frame = none ↔
      frame.donorVolume ≠ 0 ∧ ¬frame.CenterStrictlyInside ∧ frame.CenterOnBoundary := by
  by_cases donorCoplanar : frame.donorVolume = 0
  · by_cases allCoplanar : frame.AllFiveCoplanar <;>
      simp [observe?, donorCoplanar, allCoplanar]
  · by_cases inside : frame.CenterStrictlyInside
    · simp [observe?, donorCoplanar, inside]
    · by_cases boundary : frame.CenterOnBoundary <;>
        simp [observe?, donorCoplanar, inside, boundary]

theorem observe?_isSome_iff (frame : Frame) :
    (observe? frame).isSome ↔
      frame.donorVolume = 0 ∨
        (frame.donorVolume ≠ 0 ∧
          (frame.CenterStrictlyInside ∨ ¬frame.CenterOnBoundary)) := by
  by_cases donorCoplanar : frame.donorVolume = 0
  · by_cases allCoplanar : frame.AllFiveCoplanar <;>
      simp [observe?, donorCoplanar, allCoplanar]
  · by_cases inside : frame.CenterStrictlyInside
    · simp [observe?, donorCoplanar, inside]
    · by_cases boundary : frame.CenterOnBoundary <;>
        simp [observe?, donorCoplanar, inside, boundary]

theorem observe?_map
    (frame : Frame) (transform : FrameTransform)
    (determinantNonzero : transform.determinant ≠ 0) :
    observe? (frame.map transform) = observe? frame := by
  have donorCoplanarIff :
      (frame.map transform).donorVolume = 0 ↔ frame.donorVolume = 0 := by
    simp [Frame.donorVolume_map, mul_eq_zero, determinantNonzero]
  have allCoplanarIff :=
    Frame.allFiveCoplanar_map_iff frame transform determinantNonzero
  have insideIff :=
    Frame.centerStrictlyInside_map_iff frame transform determinantNonzero
  have boundaryIff :=
    Frame.centerOnBoundary_map_iff frame transform determinantNonzero
  by_cases donorCoplanar : frame.donorVolume = 0
  · have mappedDonorCoplanar := donorCoplanarIff.mpr donorCoplanar
    by_cases allCoplanar : frame.AllFiveCoplanar
    · have mappedAllCoplanar := allCoplanarIff.mpr allCoplanar
      simp [observe?, donorCoplanar, mappedDonorCoplanar, allCoplanar, mappedAllCoplanar]
    · have mappedNotAllCoplanar : ¬(frame.map transform).AllFiveCoplanar :=
        fun mapped => allCoplanar (allCoplanarIff.mp mapped)
      simp [observe?, donorCoplanar, mappedDonorCoplanar, allCoplanar,
        mappedNotAllCoplanar]
  · by_cases inside : frame.CenterStrictlyInside
    · have mappedInside := insideIff.mpr inside
      simp [observe?, Frame.donorVolume_map, determinantNonzero, donorCoplanar,
        inside, mappedInside]
    · have mappedNotInside : ¬(frame.map transform).CenterStrictlyInside :=
        fun mapped => inside (insideIff.mp mapped)
      by_cases boundary : frame.CenterOnBoundary
      · have mappedBoundary := boundaryIff.mpr boundary
        simp [observe?, Frame.donorVolume_map, determinantNonzero, donorCoplanar,
          inside, mappedNotInside, boundary, mappedBoundary]
      · have mappedNotBoundary : ¬(frame.map transform).CenterOnBoundary :=
        fun mapped => boundary (boundaryIff.mp mapped)
        simp [observe?, Frame.donorVolume_map, determinantNonzero, donorCoplanar,
          inside, mappedNotInside, boundary, mappedNotBoundary]

/-- Every nontrivial donor transposition reverses the donor-volume sign. -/
theorem Frame.donorVolume_reorder_swap
    (frame : Frame) (first second : Fin 4) (distinct : first ≠ second) :
    (frame.reorder (Equiv.swap first second)).donorVolume = -frame.donorVolume := by
  fin_cases first <;> fin_cases second <;> simp at distinct ⊢ <;>
    simp [Equiv.swap_apply_def, Frame.reorder, Frame.donorAt, Frame.donorVolume,
      CartesianPoint3.orientedVolume] <;> ring

theorem Frame.centerVolumeAt_reorder_swap
    (frame : Frame) (first second position : Fin 4) (distinct : first ≠ second) :
    (frame.reorder (Equiv.swap first second)).centerVolumeAt position =
      -frame.centerVolumeAt (Equiv.swap first second position) := by
  fin_cases first <;> fin_cases second <;> fin_cases position <;>
    simp at distinct ⊢ <;>
    simp [Equiv.swap_apply_def, Frame.reorder, Frame.donorAt, Frame.centerVolumeAt,
      Frame.centerVolume0, Frame.centerVolume1, Frame.centerVolume2, Frame.centerVolume3,
      CartesianPoint3.orientedVolume] <;> ring

theorem Frame.allFiveCoplanar_reorder_swap_iff
    (frame : Frame) (first second : Fin 4) (distinct : first ≠ second) :
    (frame.reorder (Equiv.swap first second)).AllFiveCoplanar ↔ frame.AllFiveCoplanar := by
  rw [Frame.allFiveCoplanar_iff, Frame.allFiveCoplanar_iff]
  constructor
  · rintro ⟨mappedDonorZero, mappedCentersZero⟩
    have donorEq := Frame.donorVolume_reorder_swap frame first second distinct
    have donorZero : frame.donorVolume = 0 := by
      rw [donorEq] at mappedDonorZero
      simpa using mappedDonorZero
    refine ⟨donorZero, ?_⟩
    intro position
    have mappedZero := mappedCentersZero (Equiv.swap first second position)
    rw [Frame.centerVolumeAt_reorder_swap frame first second _ distinct] at mappedZero
    simpa using mappedZero
  · rintro ⟨donorZero, centersZero⟩
    have donorEq := Frame.donorVolume_reorder_swap frame first second distinct
    refine ⟨?_, ?_⟩
    · rw [donorEq, donorZero, neg_zero]
    · intro position
      rw [Frame.centerVolumeAt_reorder_swap frame first second position distinct]
      simp [centersZero]

theorem Frame.centerStrictlyInside_reorder_swap_iff
    (frame : Frame) (first second : Fin 4) (distinct : first ≠ second) :
    (frame.reorder (Equiv.swap first second)).CenterStrictlyInside ↔
      frame.CenterStrictlyInside := by
  rw [Frame.centerStrictlyInside_iff, Frame.centerStrictlyInside_iff]
  have donorEq := Frame.donorVolume_reorder_swap frame first second distinct
  constructor
  · intro mappedPositive position
    have positive := mappedPositive (Equiv.swap first second position)
    rw [donorEq,
      Frame.centerVolumeAt_reorder_swap frame first second _ distinct] at positive
    simpa only [Equiv.swap_apply_self, neg_mul_neg] using positive
  · intro positive position
    rw [donorEq, Frame.centerVolumeAt_reorder_swap frame first second position distinct]
    simpa only [neg_mul_neg] using positive (Equiv.swap first second position)

theorem Frame.centerOnBoundary_reorder_swap_iff
    (frame : Frame) (first second : Fin 4) (distinct : first ≠ second) :
    (frame.reorder (Equiv.swap first second)).CenterOnBoundary ↔
      frame.CenterOnBoundary := by
  rw [Frame.centerOnBoundary_iff, Frame.centerOnBoundary_iff]
  constructor
  · rintro ⟨position, mappedZero⟩
    refine ⟨Equiv.swap first second position, ?_⟩
    rw [Frame.centerVolumeAt_reorder_swap frame first second position distinct] at mappedZero
    exact neg_eq_zero.mp mappedZero
  · rintro ⟨position, zero⟩
    refine ⟨Equiv.swap first second position, ?_⟩
    rw [Frame.centerVolumeAt_reorder_swap frame first second _ distinct,
      Equiv.swap_apply_self, zero, neg_zero]

/-- A transposition of any two donor-list positions cannot change the perceived geometry. -/
theorem observe?_reorder_swap
    (frame : Frame) (first second : Fin 4) :
    observe? (frame.reorder (Equiv.swap first second)) = observe? frame := by
  by_cases distinct : first ≠ second
  · have donorVolumeEq := Frame.donorVolume_reorder_swap frame first second distinct
    have allCoplanarIff := Frame.allFiveCoplanar_reorder_swap_iff frame first second distinct
    have insideIff := Frame.centerStrictlyInside_reorder_swap_iff frame first second distinct
    have boundaryIff := Frame.centerOnBoundary_reorder_swap_iff frame first second distinct
    by_cases donorCoplanar : frame.donorVolume = 0
    · have mappedDonorCoplanar :
          (frame.reorder (Equiv.swap first second)).donorVolume = 0 := by
        rw [donorVolumeEq, donorCoplanar, neg_zero]
      by_cases allCoplanar : frame.AllFiveCoplanar
      · have mappedAllCoplanar := allCoplanarIff.mpr allCoplanar
        simp [observe?, donorCoplanar, mappedDonorCoplanar, allCoplanar,
          mappedAllCoplanar]
      · have mappedNotAllCoplanar :
            ¬(frame.reorder (Equiv.swap first second)).AllFiveCoplanar :=
          fun mapped => allCoplanar (allCoplanarIff.mp mapped)
        simp [observe?, donorCoplanar, mappedDonorCoplanar, allCoplanar,
          mappedNotAllCoplanar]
    · have mappedNotDonorCoplanar :
          (frame.reorder (Equiv.swap first second)).donorVolume ≠ 0 := by
        rw [donorVolumeEq, neg_ne_zero]
        exact donorCoplanar
      by_cases inside : frame.CenterStrictlyInside
      · have mappedInside := insideIff.mpr inside
        simp [observe?, donorCoplanar, mappedNotDonorCoplanar, inside, mappedInside]
      · have mappedNotInside :
            ¬(frame.reorder (Equiv.swap first second)).CenterStrictlyInside :=
          fun mapped => inside (insideIff.mp mapped)
        by_cases boundary : frame.CenterOnBoundary
        · have mappedBoundary := boundaryIff.mpr boundary
          simp [observe?, donorCoplanar, mappedNotDonorCoplanar, inside,
            mappedNotInside, boundary, mappedBoundary]
        · have mappedNotBoundary :
              ¬(frame.reorder (Equiv.swap first second)).CenterOnBoundary :=
            fun mapped => boundary (boundaryIff.mp mapped)
          simp [observe?, donorCoplanar, mappedNotDonorCoplanar, inside,
            mappedNotInside, boundary, mappedNotBoundary]
  · have same : first = second := not_ne_iff.mp distinct
    subst second
    rw [Equiv.swap_self]
    exact congrArg observe? (Frame.reorder_one frame)

/-- The classifier is independent of every permutation of the four donor inputs. -/
theorem observe?_reorder
    (frame : Frame) (permutation : Equiv.Perm (Fin 4)) :
    observe? (frame.reorder permutation) = observe? frame := by
  induction permutation using Equiv.Perm.swap_induction_on' with
  | one => simp
  | mul_swap permutation first second _ inductionHypothesis =>
      rw [← Frame.reorder_reorder,
        observe?_reorder_swap (frame.reorder permutation) first second,
        inductionHypothesis]

theorem recognizedGeometry?_eq_some_iff
    (frame : Frame) (geometry : Geometry) :
    (observe? frame).map geometryOfFourCoordinateObservation = some geometry ↔
      ∃ observation, Judgment frame observation ∧
        geometryOfFourCoordinateObservation observation = geometry := by
  constructor
  · intro produced
    cases observed : observe? frame with
    | none => simp [observed] at produced
    | some observation =>
        refine ⟨observation, (observe?_eq_some_iff frame observation).mp observed, ?_⟩
        simpa [observed] using produced
  · rintro ⟨observation, judgment, rfl⟩
    rw [← observe?_eq_some_iff] at judgment
    simp [judgment]

end TetraStereo.OneCenter.RedBookIR9.FourCoordinateSpatialPerception
