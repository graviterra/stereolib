import TetraStereo.OneCenter.CIPExactSpatialFrameInvariance
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace TetrahedralAffineViewingNormalization

/-!
# Constructive rational-frame viewing normalization for tetrahedral evidence

An exact spatial observation of a tetrahedral centre is an ordered quadruple of rational points
`p₁ p₂ p₃ p₄`.  The IUPAC viewing calibration used by the `R/S` descriptors is stated in a
particular screen frame: three ligands lie in a screen plane and the fourth lies behind it.
This module *constructs* an explicit rational affine frame change that puts an arbitrary
nondegenerate quadruple into that normal form.  The construction uses only field operations on
`ℚ`; no inverse, choice, irrational rotation, or real-number normalization is involved.

Write

* `u = p₂ - p₁`,
* `v = p₃ - p₁`,
* `d = p₄ - p₁`,
* `V = orientedVolume p₁ p₂ p₃ p₄`, and
* `n = V * (u × v)`.

The linear part `A` has rows `(u, n × u, n)` and the anchor-normalized map is
`T(p) = A (p - p₁)`.  The elementary identities

* `n · u = 0`,
* `n · v = 0`,
* `n · d = -(V ^ 2)`,
* `det A = (u · u) * (n · n)`, and
* `0 < det A` whenever `V ≠ 0`

are proved by exact polynomial algebra over `ℚ`.  Consequently `T` sends the first three points
to the plane `z = 0`, sends `p₁` to the origin, and sends `p₄` to `z = -(V ^ 2) < 0`, while
preserving orientation.  Later source-conformance work may compose these normal-form facts with
an independent viewing calibration.  This module deliberately does **not** claim that `T` is a
rigid motion or that it preserves physical distances; it is an affine coordinate normalization.

The sign convention of `CartesianPoint3.orientedVolume` (the determinant of
`(p₁-p₄, p₂-p₄, p₃-p₄)`) is recorded in `frameVolume_eq_neg_dot_edgeCross`; the correction
status of the surrounding source profile is irrelevant to these polynomial identities.
-/

/-- Componentwise multiplication of an exact rational vector by a rational scalar. -/
def scaleVector (factor : ℚ) (vector : RationalVector3) : RationalVector3 where
  x := factor * vector.x
  y := factor * vector.y
  z := factor * vector.z

/-- A rational three-vector is nonzero when at least one of its coordinates is nonzero.
This predicate is used instead of a `Zero` instance so that the development introduces no new
global algebraic instances. -/
def NonzeroVector (vector : RationalVector3) : Prop :=
  vector.x ≠ 0 ∨ vector.y ≠ 0 ∨ vector.z ≠ 0

/-- The exact rational origin. -/
def origin : CartesianPoint3 where
  x := 0
  y := 0
  z := 0

/-- The oriented volume of the ordered quadruple `p₁ p₂ p₃ p₄`. -/
def frameVolume (first second third fourth : CartesianPoint3) : ℚ :=
  CartesianPoint3.orientedVolume first second third fourth

/-- The anchor edge `p₂ - p₁`. -/
def firstEdge (first second : CartesianPoint3) : RationalVector3 :=
  CartesianPoint3.displacement first second

/-- The anchor edge `p₃ - p₁`. -/
def secondEdge (first third : CartesianPoint3) : RationalVector3 :=
  CartesianPoint3.displacement first third

/-- The anchor edge `p₄ - p₁`. -/
def thirdEdge (first fourth : CartesianPoint3) : RationalVector3 :=
  CartesianPoint3.displacement first fourth

/-- The normal direction `u × v` before scaling by the oriented volume. -/
def edgeCross (first second third : CartesianPoint3) : RationalVector3 :=
  RationalVector3.cross (firstEdge first second) (secondEdge first third)

/-- The viewing normal `n = V * (u × v)`. -/
def viewingNormal (first second third fourth : CartesianPoint3) : RationalVector3 :=
  scaleVector (frameVolume first second third fourth) (edgeCross first second third)

/-- The translation part of the viewing transform, chosen so that `p₁` maps to the origin. -/
def viewingOffset (first second third fourth : CartesianPoint3) : CartesianPoint3 where
  x := -((firstEdge first second).x * first.x +
        (firstEdge first second).y * first.y +
        (firstEdge first second).z * first.z)
  y := -((RationalVector3.cross (viewingNormal first second third fourth)
          (firstEdge first second)).x * first.x +
        (RationalVector3.cross (viewingNormal first second third fourth)
          (firstEdge first second)).y * first.y +
        (RationalVector3.cross (viewingNormal first second third fourth)
          (firstEdge first second)).z * first.z)
  z := -((viewingNormal first second third fourth).x * first.x +
        (viewingNormal first second third fourth).y * first.y +
        (viewingNormal first second third fourth).z * first.z)

/-- The constructive rational viewing normalization of the ordered quadruple
`first second third fourth`.  Its linear part has rows `(u, n × u, n)` and its translation sends
`first` to the origin. -/
def viewingTransform (first second third fourth : CartesianPoint3) :
    RationalAffineFrameTransform where
  m00 := (firstEdge first second).x
  m01 := (firstEdge first second).y
  m02 := (firstEdge first second).z
  m10 := (RationalVector3.cross (viewingNormal first second third fourth)
    (firstEdge first second)).x
  m11 := (RationalVector3.cross (viewingNormal first second third fourth)
    (firstEdge first second)).y
  m12 := (RationalVector3.cross (viewingNormal first second third fourth)
    (firstEdge first second)).z
  m20 := (viewingNormal first second third fourth).x
  m21 := (viewingNormal first second third fourth).y
  m22 := (viewingNormal first second third fourth).z
  offset := viewingOffset first second third fourth

/-! ## Elementary dot-product lemmas -/

/-- Scalar multiplication pulls out of the left argument of the rational dot product. -/
theorem dot_scaleVector_left (factor : ℚ) (left right : RationalVector3) :
    RationalVector3.dot (scaleVector factor left) right =
      factor * RationalVector3.dot left right := by
  simp only [scaleVector, RationalVector3.dot]
  ring

/-- The rational dot product is symmetric. -/
theorem dot_comm (left right : RationalVector3) :
    RationalVector3.dot left right = RationalVector3.dot right left := by
  simp only [RationalVector3.dot]
  ring

/-- A vector with a nonzero coordinate has strictly positive squared length.  The proof is the
sum-of-squares argument, with no order-theoretic or geometric input beyond `ℚ` being an ordered
field. -/
theorem dot_self_pos_of_nonzero {vector : RationalVector3} (nonzero : NonzeroVector vector) :
    0 < RationalVector3.dot vector vector := by
  rcases nonzero with xNonzero | yNonzero | zNonzero
  · simp only [RationalVector3.dot]
    nlinarith [sq_pos_of_ne_zero xNonzero, sq_nonneg vector.y, sq_nonneg vector.z]
  · simp only [RationalVector3.dot]
    nlinarith [sq_pos_of_ne_zero yNonzero, sq_nonneg vector.x, sq_nonneg vector.z]
  · simp only [RationalVector3.dot]
    nlinarith [sq_pos_of_ne_zero zNonzero, sq_nonneg vector.x, sq_nonneg vector.y]

/-! ## Sign convention of the oriented volume -/

/-- The existing oriented volume equals the negative of the scalar triple product
`(u × v) · d`.  The minus sign is forced by the determinant convention
`orientedVolume p₁ p₂ p₃ p₄ = det (p₁-p₄, p₂-p₄, p₃-p₄)`. -/
theorem frameVolume_eq_neg_dot_edgeCross (first second third fourth : CartesianPoint3) :
    frameVolume first second third fourth =
      -RationalVector3.dot (edgeCross first second third) (thirdEdge first fourth) := by
  simp only [frameVolume, edgeCross, firstEdge, secondEdge, thirdEdge,
    CartesianPoint3.orientedVolume, CartesianPoint3.displacement,
    RationalVector3.cross, RationalVector3.dot]
  ring

/-- A quadruple whose first two points coincide has zero oriented volume. -/
theorem frameVolume_eq_zero_of_second_eq_first (first third fourth : CartesianPoint3) :
    frameVolume first first third fourth = 0 := by
  simp only [frameVolume, CartesianPoint3.orientedVolume]
  ring

/-! ## The viewing normal -/

/-- The viewing normal is orthogonal to the first edge. -/
theorem viewingNormal_dot_firstEdge (first second third fourth : CartesianPoint3) :
    RationalVector3.dot (viewingNormal first second third fourth)
      (firstEdge first second) = 0 := by
  rw [viewingNormal, dot_scaleVector_left]
  have crossOrthogonal :
      RationalVector3.dot (edgeCross first second third) (firstEdge first second) = 0 := by
    simp only [edgeCross, firstEdge, secondEdge, RationalVector3.cross,
      RationalVector3.dot]
    ring
  rw [crossOrthogonal]
  ring

/-- The viewing normal is orthogonal to the second edge. -/
theorem viewingNormal_dot_secondEdge (first second third fourth : CartesianPoint3) :
    RationalVector3.dot (viewingNormal first second third fourth)
      (secondEdge first third) = 0 := by
  rw [viewingNormal, dot_scaleVector_left]
  have crossOrthogonal :
      RationalVector3.dot (edgeCross first second third) (secondEdge first third) = 0 := by
    simp only [edgeCross, firstEdge, secondEdge, RationalVector3.cross,
      RationalVector3.dot]
    ring
  rw [crossOrthogonal]
  ring

/-- The viewing normal has scalar product `-(V ^ 2)` with the third edge. -/
theorem viewingNormal_dot_thirdEdge (first second third fourth : CartesianPoint3) :
    RationalVector3.dot (viewingNormal first second third fourth)
      (thirdEdge first fourth) = -(frameVolume first second third fourth) ^ 2 := by
  have volumeRelation := frameVolume_eq_neg_dot_edgeCross first second third fourth
  calc
    RationalVector3.dot (viewingNormal first second third fourth)
        (thirdEdge first fourth)
        = frameVolume first second third fourth *
            RationalVector3.dot (edgeCross first second third)
              (thirdEdge first fourth) := by
            rw [viewingNormal, dot_scaleVector_left]
    _ = -(frameVolume first second third fourth) ^ 2 := by
          rw [volumeRelation]
          ring

/-! ## Determinant of the linear part -/

/-- The determinant of `(u, n × u, n)` is `(u · u) * (n · n)` because `n` is orthogonal to `u`. -/
theorem viewingTransform_determinant (first second third fourth : CartesianPoint3) :
    (viewingTransform first second third fourth).determinant =
      RationalVector3.dot (firstEdge first second) (firstEdge first second) *
        RationalVector3.dot (viewingNormal first second third fourth)
          (viewingNormal first second third fourth) := by
  have orthogonal :
      RationalVector3.dot (firstEdge first second)
        (viewingNormal first second third fourth) = 0 := by
    rw [dot_comm]
    exact viewingNormal_dot_firstEdge first second third fourth
  have determinantIdentity :
      (viewingTransform first second third fourth).determinant =
        RationalVector3.dot (firstEdge first second) (firstEdge first second) *
            RationalVector3.dot (viewingNormal first second third fourth)
              (viewingNormal first second third fourth) -
          (RationalVector3.dot (firstEdge first second)
            (viewingNormal first second third fourth)) ^ 2 := by
    simp only [RationalAffineFrameTransform.determinant, viewingTransform,
      firstEdge, RationalVector3.cross, RationalVector3.dot]
    ring
  rw [determinantIdentity, orthogonal]
  ring

/-- The squared length of the viewing normal is `V ^ 2` times the squared length of `u × v`. -/
theorem viewingNormal_dot_self (first second third fourth : CartesianPoint3) :
    RationalVector3.dot (viewingNormal first second third fourth)
        (viewingNormal first second third fourth) =
      (frameVolume first second third fourth) ^ 2 *
        RationalVector3.dot (edgeCross first second third)
          (edgeCross first second third) := by
  simp only [viewingNormal, scaleVector, RationalVector3.dot]
  ring

/-- A nonzero oriented volume forces the first edge to be a nonzero vector. -/
theorem firstEdge_nonzero_of_volume_ne_zero (first second third fourth : CartesianPoint3)
    (volumeNonzero : frameVolume first second third fourth ≠ 0) :
    NonzeroVector (firstEdge first second) := by
  by_contra zero
  simp only [NonzeroVector, not_or, not_ne_iff] at zero
  have xZero : second.x - first.x = 0 := by
    simpa [firstEdge, CartesianPoint3.displacement] using zero.1
  have yZero : second.y - first.y = 0 := by
    simpa [firstEdge, CartesianPoint3.displacement] using zero.2.1
  have zZero : second.z - first.z = 0 := by
    simpa [firstEdge, CartesianPoint3.displacement] using zero.2.2
  have xEq : second.x = first.x := by linarith
  have yEq : second.y = first.y := by linarith
  have zEq : second.z = first.z := by linarith
  apply volumeNonzero
  simp only [frameVolume, CartesianPoint3.orientedVolume]
  rw [xEq, yEq, zEq]
  ring

/-- A nonzero oriented volume forces `u × v` to be a nonzero vector. -/
theorem edgeCross_nonzero_of_volume_ne_zero (first second third fourth : CartesianPoint3)
    (volumeNonzero : frameVolume first second third fourth ≠ 0) :
    NonzeroVector (edgeCross first second third) := by
  by_contra zero
  simp only [NonzeroVector, not_or, not_ne_iff] at zero
  have crossDotZero :
      RationalVector3.dot (edgeCross first second third) (thirdEdge first fourth) = 0 := by
    simp only [RationalVector3.dot, zero.1, zero.2.1, zero.2.2]
    ring
  apply volumeNonzero
  rw [frameVolume_eq_neg_dot_edgeCross first second third fourth, crossDotZero]
  ring

/-- The viewing transform has strictly positive determinant whenever the oriented volume of the
input quadruple is nonzero.  No division or inverse is used: positivity is the product of three
strictly positive squared lengths. -/
theorem viewingTransform_determinant_pos (first second third fourth : CartesianPoint3)
    (volumeNonzero : frameVolume first second third fourth ≠ 0) :
    0 < (viewingTransform first second third fourth).determinant := by
  have firstEdgeNonzero :=
    firstEdge_nonzero_of_volume_ne_zero first second third fourth volumeNonzero
  have edgeCrossNonzero :=
    edgeCross_nonzero_of_volume_ne_zero first second third fourth volumeNonzero
  have firstLengthPositive :
      0 < RationalVector3.dot (firstEdge first second) (firstEdge first second) :=
    dot_self_pos_of_nonzero firstEdgeNonzero
  have crossLengthPositive :
      0 < RationalVector3.dot (edgeCross first second third) (edgeCross first second third) :=
    dot_self_pos_of_nonzero edgeCrossNonzero
  have volumeSquaredPositive : 0 < (frameVolume first second third fourth) ^ 2 :=
    sq_pos_of_ne_zero volumeNonzero
  rw [viewingTransform_determinant, viewingNormal_dot_self]
  exact mul_pos firstLengthPositive (mul_pos volumeSquaredPositive crossLengthPositive)

/-! ## Coordinates after normalization -/

/-- The `x` coordinate after the viewing transform is the first row of the linear part applied to
the displacement from the anchor. -/
theorem viewingTransform_applyPoint_x (first second third fourth point : CartesianPoint3) :
    ((viewingTransform first second third fourth).applyPoint point).x =
      RationalVector3.dot (firstEdge first second)
        (CartesianPoint3.displacement first point) := by
  simp only [RationalAffineFrameTransform.applyPoint, viewingTransform, viewingOffset,
    firstEdge, CartesianPoint3.displacement, RationalVector3.dot]
  ring

/-- The `y` coordinate after the viewing transform is the second row `n × u` applied to the
displacement from the anchor. -/
theorem viewingTransform_applyPoint_y (first second third fourth point : CartesianPoint3) :
    ((viewingTransform first second third fourth).applyPoint point).y =
      RationalVector3.dot
        (RationalVector3.cross (viewingNormal first second third fourth)
          (firstEdge first second))
        (CartesianPoint3.displacement first point) := by
  simp only [RationalAffineFrameTransform.applyPoint, viewingTransform, viewingOffset,
    firstEdge, CartesianPoint3.displacement, RationalVector3.dot]
  ring

/-- The `z` coordinate after the viewing transform is the viewing normal applied to the
displacement from the anchor. -/
theorem viewingTransform_applyPoint_z (first second third fourth point : CartesianPoint3) :
    ((viewingTransform first second third fourth).applyPoint point).z =
      RationalVector3.dot (viewingNormal first second third fourth)
        (CartesianPoint3.displacement first point) := by
  simp only [RationalAffineFrameTransform.applyPoint, viewingTransform, viewingOffset,
    firstEdge, CartesianPoint3.displacement, RationalVector3.dot]
  ring

/-- The anchor is sent to the origin. -/
theorem viewingTransform_applyPoint_first (first second third fourth : CartesianPoint3) :
    (viewingTransform first second third fourth).applyPoint first = origin := by
  change (⟨((viewingTransform first second third fourth).applyPoint first).x,
            ((viewingTransform first second third fourth).applyPoint first).y,
            ((viewingTransform first second third fourth).applyPoint first).z⟩ :
          CartesianPoint3) = origin
  rw [viewingTransform_applyPoint_x, viewingTransform_applyPoint_y,
    viewingTransform_applyPoint_z]
  simp [origin, CartesianPoint3.displacement, RationalVector3.dot]

/-- The second point is sent to the positive `x` axis; its `x` coordinate is `u · u`. -/
theorem viewingTransform_applyPoint_second_x (first second third fourth : CartesianPoint3) :
    ((viewingTransform first second third fourth).applyPoint second).x =
      RationalVector3.dot (firstEdge first second) (firstEdge first second) := by
  rw [viewingTransform_applyPoint_x]
  simp [firstEdge]

/-- The second point has zero `y` coordinate after normalization. -/
theorem viewingTransform_applyPoint_second_y (first second third fourth : CartesianPoint3) :
    ((viewingTransform first second third fourth).applyPoint second).y = 0 := by
  rw [viewingTransform_applyPoint_y]
  simp only [firstEdge, RationalVector3.cross, RationalVector3.dot]
  ring

/-- The second point has zero `z` coordinate after normalization. -/
theorem viewingTransform_applyPoint_second_z (first second third fourth : CartesianPoint3) :
    ((viewingTransform first second third fourth).applyPoint second).z = 0 := by
  rw [viewingTransform_applyPoint_z]
  simpa [firstEdge] using viewingNormal_dot_firstEdge first second third fourth

/-- The second point is normalized to `(u · u, 0, 0)`. -/
theorem viewingTransform_applyPoint_second (first second third fourth : CartesianPoint3) :
    (viewingTransform first second third fourth).applyPoint second =
      { x := RationalVector3.dot (firstEdge first second) (firstEdge first second)
        y := 0
        z := 0 } := by
  change (⟨((viewingTransform first second third fourth).applyPoint second).x,
            ((viewingTransform first second third fourth).applyPoint second).y,
            ((viewingTransform first second third fourth).applyPoint second).z⟩ :
          CartesianPoint3) =
        ({ x := RationalVector3.dot (firstEdge first second) (firstEdge first second)
           y := 0
           z := 0 } : CartesianPoint3)
  rw [viewingTransform_applyPoint_second_x, viewingTransform_applyPoint_second_y,
    viewingTransform_applyPoint_second_z]

/-- The `x` coordinate of the normalized second point is strictly positive when the oriented
volume is nonzero. -/
theorem viewingTransform_applyPoint_second_x_pos (first second third fourth : CartesianPoint3)
    (volumeNonzero : frameVolume first second third fourth ≠ 0) :
    0 < ((viewingTransform first second third fourth).applyPoint second).x := by
  rw [viewingTransform_applyPoint_second_x]
  exact dot_self_pos_of_nonzero
    (firstEdge_nonzero_of_volume_ne_zero first second third fourth volumeNonzero)

/-- The third point lies in the screen plane `z = 0`. -/
theorem viewingTransform_applyPoint_third_z (first second third fourth : CartesianPoint3) :
    ((viewingTransform first second third fourth).applyPoint third).z = 0 := by
  rw [viewingTransform_applyPoint_z]
  simpa [secondEdge] using viewingNormal_dot_secondEdge first second third fourth

/-- The fourth point has `z = -(V ^ 2)`. -/
theorem viewingTransform_applyPoint_fourth_z (first second third fourth : CartesianPoint3) :
    ((viewingTransform first second third fourth).applyPoint fourth).z =
      -(frameVolume first second third fourth) ^ 2 := by
  rw [viewingTransform_applyPoint_z]
  simpa [thirdEdge] using viewingNormal_dot_thirdEdge first second third fourth

/-! ## Composition with the existing affine determinant law -/

/-- The oriented volume of the normalized quadruple is the determinant of the viewing transform
times the original oriented volume. -/
theorem viewingTransform_orientedVolume (first second third fourth : CartesianPoint3) :
    CartesianPoint3.orientedVolume
        ((viewingTransform first second third fourth).applyPoint first)
        ((viewingTransform first second third fourth).applyPoint second)
        ((viewingTransform first second third fourth).applyPoint third)
        ((viewingTransform first second third fourth).applyPoint fourth) =
      (viewingTransform first second third fourth).determinant *
        frameVolume first second third fourth :=
  RationalAffineFrameTransform.orientedVolume_applyPoint
    (viewingTransform first second third fourth) first second third fourth

/-- The normalized quadruple is nondegenerate whenever the original one is. -/
theorem viewingTransform_orientedVolume_ne_zero (first second third fourth : CartesianPoint3)
    (volumeNonzero : frameVolume first second third fourth ≠ 0) :
    CartesianPoint3.orientedVolume
        ((viewingTransform first second third fourth).applyPoint first)
        ((viewingTransform first second third fourth).applyPoint second)
        ((viewingTransform first second third fourth).applyPoint third)
        ((viewingTransform first second third fourth).applyPoint fourth) ≠ 0 := by
  rw [viewingTransform_orientedVolume]
  exact mul_ne_zero
    (ne_of_gt (viewingTransform_determinant_pos first second third fourth volumeNonzero))
    volumeNonzero

/-! ## Main theorem -/

/-- **Constructive arbitrary rational-frame viewing normalization.**

For every ordered rational quadruple with nonzero oriented volume, there is an explicit
orientation-preserving rational affine frame change whose linear part is `(u, n × u, n)` and whose
translation sends the anchor to the origin, such that:

* the anchor maps to the origin;
* the second point maps to a point of the positive `x` axis (in particular `z = 0`);
* the third point satisfies `z = 0`;
* the fourth point satisfies `z = -(V ^ 2) < 0`;
* the normalized quadruple still has nonzero oriented volume.

The transform is `viewingTransform first second third fourth`; the existential is only a
convenience wrapper and exposes the exact witness.  No inverse, choice principle, irrational
rotation, or real-valued normalization is used. -/
theorem exists_orientationPreserving_viewingNormalization
    (first second third fourth : CartesianPoint3)
    (volumeNonzero : frameVolume first second third fourth ≠ 0) :
    ∃ transform : RationalAffineFrameTransform,
      0 < transform.determinant ∧
      transform.applyPoint first = origin ∧
      (transform.applyPoint second).x =
        RationalVector3.dot (firstEdge first second) (firstEdge first second) ∧
      0 < (transform.applyPoint second).x ∧
      (transform.applyPoint second).y = 0 ∧
      (transform.applyPoint second).z = 0 ∧
      (transform.applyPoint third).z = 0 ∧
      (transform.applyPoint fourth).z =
        -(frameVolume first second third fourth) ^ 2 ∧
      (transform.applyPoint fourth).z < 0 ∧
      CartesianPoint3.orientedVolume (transform.applyPoint first)
        (transform.applyPoint second) (transform.applyPoint third)
        (transform.applyPoint fourth) ≠ 0 := by
  refine ⟨viewingTransform first second third fourth,
    viewingTransform_determinant_pos first second third fourth volumeNonzero,
    viewingTransform_applyPoint_first first second third fourth,
    viewingTransform_applyPoint_second_x first second third fourth,
    viewingTransform_applyPoint_second_x_pos first second third fourth volumeNonzero,
    viewingTransform_applyPoint_second_y first second third fourth,
    viewingTransform_applyPoint_second_z first second third fourth,
    viewingTransform_applyPoint_third_z first second third fourth,
    viewingTransform_applyPoint_fourth_z first second third fourth,
    ?_,
    viewingTransform_orientedVolume_ne_zero first second third fourth volumeNonzero⟩
  rw [viewingTransform_applyPoint_fourth_z]
  have volumeSquaredPositive : 0 < (frameVolume first second third fourth) ^ 2 :=
    sq_pos_of_ne_zero volumeNonzero
  linarith

end TetrahedralAffineViewingNormalization
end TetraStereo.OneCenter

/-! ## Kernel-authority guards

The determinant-positivity, transformed-volume and final-existence results are checked to use
only the standard kernel principles (`propext`, `Classical.choice`, `Quot.sound`). -/

assert_kernel_only TetraStereo.OneCenter.TetrahedralAffineViewingNormalization.viewingTransform_determinant_pos
assert_kernel_only TetraStereo.OneCenter.TetrahedralAffineViewingNormalization.viewingTransform_orientedVolume
assert_kernel_only TetraStereo.OneCenter.TetrahedralAffineViewingNormalization.exists_orientationPreserving_viewingNormalization
