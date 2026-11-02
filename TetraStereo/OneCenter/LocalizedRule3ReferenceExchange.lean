import TetraStereo.OneCenter.LocalizedRule3Spatial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Exact Rule-3 reference-exchange geometry transport

This module proves the *geometric* transport law for the existing exact rational Rule-3 spatial
classifier `rule3GeometryOfSpatialReferences?`: replacing exactly **one** endpoint's selected
senior reference by an opposite-side partner flips `seqcis`/`seqtrans`, while replacing both
endpoints' references independently preserves the classification.

The geometric hypothesis is the explicit opposite-arm relation

    newArm = (-k) • oldArm + t • axis        with k > 0,

where `oldArm`/`newArm` are the displacements from the endpoint to the old/new reference and
`axis` is the *directed* double-bond axis `displacement leftEndpoint rightEndpoint`.  The `t • axis`
summand is a shift along the axis; the `(-k)` factor reverses the side normal.  Both `k` and `t`
are rationals, so every derivation is exact and `ring`/`linarith` close the algebra.

This is a geometric transport lemma only.  It does **not** establish that the count-based
`SmilesTetrahedral.Rule3CenterPolicy.flipped` list is valid: that list records an `flipRule3Geometry`
transport whose justification still needs a *source-derived reference-change witness* mapping a
physical observation to a concrete opposite-side partner.  The local `OfficialRule3Geometry.flip`
below is deliberately an independent definition; it agrees extensionally with
`SmilesTetrahedral.flipRule3Geometry`, but no statement here imports or reasons about the policy.
-/

/-! ## Rational sign helpers -/

namespace RationalRule3OppositeSide

/-- Scaling a rational by a strictly negative factor `-k` with `k > 0` preserves the zero test. -/
theorem neg_mul_eq_zero_iff_of_pos {k s : ℚ} (kpos : 0 < k) :
    (-k) * s = 0 ↔ s = 0 := by
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr (ne_of_gt kpos))
  · intro h
    simp [h]

/-- Scaling a positive rational by a strictly negative factor `-k` yields a negative value. -/
theorem neg_mul_neg_iff_pos_of_pos {k s : ℚ} (kpos : 0 < k) :
    (-k) * s < 0 ↔ 0 < s := by
  constructor
  · intro h
    by_contra hs
    have hnonpos : 0 ≤ (-k) * s :=
      mul_nonneg_of_nonpos_of_nonpos (neg_lt_zero.mpr kpos).le (le_of_not_gt hs)
    linarith
  · intro h
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr kpos) h

/-- Scaling a negative rational by a strictly negative factor `-k` yields a positive value. -/
theorem neg_mul_pos_iff_neg_of_pos {k s : ℚ} (kpos : 0 < k) :
    0 < (-k) * s ↔ s < 0 := by
  constructor
  · intro h
    by_contra hs
    have hnonpos : (-k) * s ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_lt_zero.mpr kpos).le (le_of_not_gt hs)
    linarith
  · intro h
    exact mul_pos_of_neg_of_neg (neg_lt_zero.mpr kpos) h

end RationalRule3OppositeSide

/-! ## The single-endpoint geometry flip -/

namespace OfficialRule3Geometry

/-- Single-endpoint reference exchange: `seqcis` and `seqtrans` swap; `nonstereogenic` is fixed.

This is the exact action asserted by the transport law.  It is kept separate from the count-based
`SmilesTetrahedral.flipRule3Geometry` transport applied through `Rule3CenterPolicy.flipped`, whose
validity still requires a source-derived reference-change witness. -/
def flip : OfficialRule3Geometry → OfficialRule3Geometry
  | .seqcis => .seqtrans
  | .seqtrans => .seqcis
  | .nonstereogenic => .nonstereogenic

@[simp] theorem flip_seqcis : flip .seqcis = .seqtrans := rfl

@[simp] theorem flip_seqtrans : flip .seqtrans = .seqcis := rfl

@[simp] theorem flip_nonstereogenic : flip .nonstereogenic = .nonstereogenic := rfl

@[simp] theorem flip_flip (geometry : OfficialRule3Geometry) :
    flip (flip geometry) = geometry := by
  cases geometry <;> rfl

end OfficialRule3Geometry

/-- Two independent single-endpoint reference exchanges cancel: `Option.map flip` is involutive. -/
theorem map_flip_flip (o : Option OfficialRule3Geometry) :
    (o.map OfficialRule3Geometry.flip).map OfficialRule3Geometry.flip = o := by
  cases o <;> simp [OfficialRule3Geometry.flip_flip]

/-! ## Exact rational vector algebra used by the derivation -/

namespace RationalVector3

/-- The zero exact rational vector. -/
instance : Zero RationalVector3 where
  zero := { x := 0, y := 0, z := 0 }

@[simp] theorem zero_x : (0 : RationalVector3).x = 0 := rfl
@[simp] theorem zero_y : (0 : RationalVector3).y = 0 := rfl
@[simp] theorem zero_z : (0 : RationalVector3).z = 0 := rfl

/-- Scalar multiplication by an exact rational. -/
def vsmul (c : ℚ) (v : RationalVector3) : RationalVector3 :=
  { x := c * v.x, y := c * v.y, z := c * v.z }

/-- Componentwise exact addition. -/
def vadd (u v : RationalVector3) : RationalVector3 :=
  { x := u.x + v.x, y := u.y + v.y, z := u.z + v.z }

/-- Extensionality for exact rational vectors. -/
theorem ext {u v : RationalVector3} (hx : u.x = v.x) (hy : u.y = v.y) (hz : u.z = v.z) :
    u = v := by
  cases u with
  | mk ux uy uz =>
      cases v with
      | mk vx vy vz =>
          change ux = vx at hx
          change uy = vy at hy
          change uz = vz at hz
          subst ux
          subst uy
          subst uz
          rfl

@[simp] theorem vsmul_zero (c : ℚ) : vsmul c 0 = 0 := by
  apply ext <;> simp [vsmul]

@[simp] theorem vadd_zero (v : RationalVector3) : vadd v 0 = v := by
  apply ext <;> simp [vadd]

@[simp] theorem zero_vadd (v : RationalVector3) : vadd 0 v = v := by
  apply ext <;> simp [vadd]

@[simp] theorem dot_zero (u : RationalVector3) : dot u 0 = 0 := by
  simp [dot]

@[simp] theorem zero_dot (u : RationalVector3) : dot 0 u = 0 := by
  simp [dot]

theorem cross_vadd_right (u v w : RationalVector3) :
    cross u (vadd v w) = vadd (cross u v) (cross u w) := by
  apply ext <;> simp [cross, vadd] <;> ring

theorem cross_vsmul_right (u v : RationalVector3) (c : ℚ) :
    cross u (vsmul c v) = vsmul c (cross u v) := by
  apply ext <;> simp [cross, vsmul] <;> ring

theorem cross_vadd_left (u v w : RationalVector3) :
    cross (vadd u v) w = vadd (cross u w) (cross v w) := by
  apply ext <;> simp [cross, vadd] <;> ring

theorem cross_vsmul_left (u v : RationalVector3) (c : ℚ) :
    cross (vsmul c u) v = vsmul c (cross u v) := by
  apply ext <;> simp [cross, vsmul] <;> ring

theorem cross_self (v : RationalVector3) : cross v v = 0 := by
  apply ext <;> simp [cross] <;> ring

theorem dot_vadd_right (u v w : RationalVector3) :
    dot u (vadd v w) = dot u v + dot u w := by
  simp [dot, vadd]; ring

theorem dot_vsmul_right (u v : RationalVector3) (c : ℚ) :
    dot u (vsmul c v) = c * dot u v := by
  simp [dot, vsmul]; ring

theorem dot_vadd_left (u v w : RationalVector3) :
    dot (vadd u v) w = dot u w + dot v w := by
  simp [dot, vadd]; ring

theorem dot_vsmul_left (u v : RationalVector3) (c : ℚ) :
    dot (vsmul c u) v = c * dot u v := by
  simp [dot, vsmul]; ring

/-- The cross product of a vector with itself is orthogonal to that vector. -/
theorem dot_cross_self (u v : RationalVector3) : dot u (cross u v) = 0 := by
  simp [dot, cross]; ring

/-- The cross product of two vectors is orthogonal to the first argument. -/
theorem dot_cross_self_right (u v : RationalVector3) : dot u (cross v u) = 0 := by
  simp [dot, cross]; ring

/-! ## The opposite-side arm relation -/

/-- Vector-level opposite-side relation: `newArm = (-k) • oldArm + t • axis` with positive
rational scaling `k`.  The `t • axis` summand is a free shift along the axis direction; it does not
change either cross normal. -/
def OppositeSideArm (oldArm newArm axis : RationalVector3) (k t : ℚ) : Prop :=
  newArm = vadd (vsmul (-k) oldArm) (vsmul t axis)

/-- With the second arm in the cross replaced by its opposite-side image, the axis-dotted triple
product scales by `-k`. -/
theorem dot_cross_axis_of_oppositeSide
    (axis oldArm otherArm newArm : RationalVector3) (k t : ℚ)
    (arm : OppositeSideArm oldArm newArm axis k t) :
    dot axis (cross otherArm newArm) = -k * dot axis (cross otherArm oldArm) := by
  rw [arm]
  simp only [dot, cross, vadd, vsmul]
  ring

/-- With the first arm in the cross replaced by its opposite-side image, the axis-dotted triple
product scales by `-k`. -/
theorem dot_cross_axis_of_oppositeSide_left
    (axis oldArm otherArm newArm : RationalVector3) (k t : ℚ)
    (arm : OppositeSideArm oldArm newArm axis k t) :
    dot axis (cross newArm otherArm) = -k * dot axis (cross oldArm otherArm) := by
  rw [arm]
  simp only [dot, cross, vadd, vsmul]
  ring

/-- With the second reference arm replaced, the two side normals' dot product scales by `-k`. -/
theorem dot_crossAxis_of_oppositeSide
    (axis oldArm otherArm newArm : RationalVector3) (k t : ℚ)
    (arm : OppositeSideArm oldArm newArm axis k t) :
    dot (cross axis otherArm) (cross axis newArm) =
      -k * dot (cross axis otherArm) (cross axis oldArm) := by
  rw [arm]
  simp only [dot, cross, vadd, vsmul]
  ring

/-- With the first reference arm replaced, the two side normals' dot product scales by `-k`. -/
theorem dot_crossAxis_of_oppositeSide_left
    (axis oldArm otherArm newArm : RationalVector3) (k t : ℚ)
    (arm : OppositeSideArm oldArm newArm axis k t) :
    dot (cross axis newArm) (cross axis otherArm) =
      -k * dot (cross axis oldArm) (cross axis otherArm) := by
  rw [arm]
  simp only [dot, cross, vadd, vsmul]
  ring

end RationalVector3

/-! ## Coplanarity and side product under a single reference exchange -/

namespace CartesianPoint3

/-- Replacing the right-endpoint reference by an opposite-side partner scales exact coplanarity by
`-k`, hence preserves its zero test exactly. -/
theorem rule3Coplanarity_exchangeRightReference
    (leftEndpoint rightEndpoint leftReference rightReference newRightReference : CartesianPoint3)
    (k t : ℚ) (arm : RationalVector3.OppositeSideArm
      (displacement rightEndpoint rightReference)
      (displacement rightEndpoint newRightReference)
      (displacement leftEndpoint rightEndpoint) k t) :
    rule3Coplanarity leftEndpoint rightEndpoint leftReference newRightReference =
      -k * rule3Coplanarity leftEndpoint rightEndpoint leftReference rightReference := by
  simpa [rule3Coplanarity] using RationalVector3.dot_cross_axis_of_oppositeSide
    (displacement leftEndpoint rightEndpoint)
    (displacement rightEndpoint rightReference)
    (displacement leftEndpoint leftReference)
    (displacement rightEndpoint newRightReference) k t arm

/-- Replacing the right-endpoint reference by an opposite-side partner scales the exact side
product by `-k`, hence reverses its strict sign. -/
theorem rule3SideProduct_exchangeRightReference
    (leftEndpoint rightEndpoint leftReference rightReference newRightReference : CartesianPoint3)
    (k t : ℚ) (arm : RationalVector3.OppositeSideArm
      (displacement rightEndpoint rightReference)
      (displacement rightEndpoint newRightReference)
      (displacement leftEndpoint rightEndpoint) k t) :
    rule3SideProduct leftEndpoint rightEndpoint leftReference newRightReference =
      -k * rule3SideProduct leftEndpoint rightEndpoint leftReference rightReference := by
  simpa [rule3SideProduct] using RationalVector3.dot_crossAxis_of_oppositeSide
    (displacement leftEndpoint rightEndpoint)
    (displacement rightEndpoint rightReference)
    (displacement leftEndpoint leftReference)
    (displacement rightEndpoint newRightReference) k t arm

/-- Replacing the left-endpoint reference by an opposite-side partner scales exact coplanarity by
`-k`. -/
theorem rule3Coplanarity_exchangeLeftReference
    (leftEndpoint rightEndpoint leftReference newLeftReference rightReference : CartesianPoint3)
    (k t : ℚ) (arm : RationalVector3.OppositeSideArm
      (displacement leftEndpoint leftReference)
      (displacement leftEndpoint newLeftReference)
      (displacement leftEndpoint rightEndpoint) k t) :
    rule3Coplanarity leftEndpoint rightEndpoint newLeftReference rightReference =
      -k * rule3Coplanarity leftEndpoint rightEndpoint leftReference rightReference := by
  simpa [rule3Coplanarity] using RationalVector3.dot_cross_axis_of_oppositeSide_left
    (displacement leftEndpoint rightEndpoint)
    (displacement leftEndpoint leftReference)
    (displacement rightEndpoint rightReference)
    (displacement leftEndpoint newLeftReference) k t arm

/-- Replacing the left-endpoint reference by an opposite-side partner scales the exact side product
by `-k`. -/
theorem rule3SideProduct_exchangeLeftReference
    (leftEndpoint rightEndpoint leftReference newLeftReference rightReference : CartesianPoint3)
    (k t : ℚ) (arm : RationalVector3.OppositeSideArm
      (displacement leftEndpoint leftReference)
      (displacement leftEndpoint newLeftReference)
      (displacement leftEndpoint rightEndpoint) k t) :
    rule3SideProduct leftEndpoint rightEndpoint newLeftReference rightReference =
      -k * rule3SideProduct leftEndpoint rightEndpoint leftReference rightReference := by
  simpa [rule3SideProduct] using RationalVector3.dot_crossAxis_of_oppositeSide_left
    (displacement leftEndpoint rightEndpoint)
    (displacement leftEndpoint leftReference)
    (displacement rightEndpoint rightReference)
    (displacement leftEndpoint newLeftReference) k t arm

end CartesianPoint3

/-! ## Independent geometry relation under scaled signs -/

/-- The core classification transfer: from `coplanar' = -k • coplanar` and
`sideProduct' = -k • sideProduct` with `k > 0`, the flipped-geometry relation holds for every
geometry class.  The `nonstereogenic` case is included and is immediately false on both sides. -/
theorem rationalRule3SpatialGeometry_flip_iff_of_scaled
    (coplanar sideProduct coplanar' sideProduct' : ℚ)
    (geometry : OfficialRule3Geometry) (k : ℚ) (kpos : 0 < k)
    (hcop : coplanar' = -k * coplanar)
    (hside : sideProduct' = -k * sideProduct) :
    ((coplanar' = 0 ∧
        match OfficialRule3Geometry.flip geometry with
        | .seqcis => 0 < sideProduct'
        | .seqtrans => sideProduct' < 0
        | .nonstereogenic => False) ↔
      (coplanar = 0 ∧
        match geometry with
        | .seqcis => 0 < sideProduct
        | .seqtrans => sideProduct < 0
        | .nonstereogenic => False)) := by
  subst coplanar'
  subst sideProduct'
  cases geometry with
  | seqcis =>
      simp only [OfficialRule3Geometry.flip]
      constructor
      · intro h
        exact ⟨(RationalRule3OppositeSide.neg_mul_eq_zero_iff_of_pos kpos).mp h.1,
          (RationalRule3OppositeSide.neg_mul_neg_iff_pos_of_pos kpos).mp h.2⟩
      · intro h
        exact ⟨(RationalRule3OppositeSide.neg_mul_eq_zero_iff_of_pos kpos).mpr h.1,
          (RationalRule3OppositeSide.neg_mul_neg_iff_pos_of_pos kpos).mpr h.2⟩
  | seqtrans =>
      simp only [OfficialRule3Geometry.flip]
      constructor
      · intro h
        exact ⟨(RationalRule3OppositeSide.neg_mul_eq_zero_iff_of_pos kpos).mp h.1,
          (RationalRule3OppositeSide.neg_mul_pos_iff_neg_of_pos kpos).mp h.2⟩
      · intro h
        exact ⟨(RationalRule3OppositeSide.neg_mul_eq_zero_iff_of_pos kpos).mpr h.1,
          (RationalRule3OppositeSide.neg_mul_pos_iff_neg_of_pos kpos).mpr h.2⟩
  | nonstereogenic =>
      simp only [OfficialRule3Geometry.flip, and_false]

/-- The independent `RationalRule3SpatialGeometry` relation flips under a right-endpoint
reference exchange. -/
theorem rationalRule3SpatialGeometry_exchangeRightReference
    (leftEndpoint rightEndpoint leftReference rightReference newRightReference : CartesianPoint3)
    (geometry : OfficialRule3Geometry) (k t : ℚ) (kpos : 0 < k)
    (arm : RationalVector3.OppositeSideArm
      (CartesianPoint3.displacement rightEndpoint rightReference)
      (CartesianPoint3.displacement rightEndpoint newRightReference)
      (CartesianPoint3.displacement leftEndpoint rightEndpoint) k t) :
    RationalRule3SpatialGeometry leftEndpoint rightEndpoint leftReference newRightReference
      (OfficialRule3Geometry.flip geometry) ↔
      RationalRule3SpatialGeometry leftEndpoint rightEndpoint leftReference rightReference geometry := by
  have hcop := CartesianPoint3.rule3Coplanarity_exchangeRightReference leftEndpoint rightEndpoint
    leftReference rightReference newRightReference k t arm
  have hside := CartesianPoint3.rule3SideProduct_exchangeRightReference leftEndpoint rightEndpoint
    leftReference rightReference newRightReference k t arm
  simpa [RationalRule3SpatialGeometry] using
    (rationalRule3SpatialGeometry_flip_iff_of_scaled
      (CartesianPoint3.rule3Coplanarity leftEndpoint rightEndpoint leftReference rightReference)
      (CartesianPoint3.rule3SideProduct leftEndpoint rightEndpoint leftReference rightReference)
      (CartesianPoint3.rule3Coplanarity leftEndpoint rightEndpoint leftReference newRightReference)
      (CartesianPoint3.rule3SideProduct leftEndpoint rightEndpoint leftReference newRightReference)
      geometry k kpos hcop hside)

/-- The independent `RationalRule3SpatialGeometry` relation flips under a left-endpoint
reference exchange. -/
theorem rationalRule3SpatialGeometry_exchangeLeftReference
    (leftEndpoint rightEndpoint leftReference newLeftReference rightReference : CartesianPoint3)
    (geometry : OfficialRule3Geometry) (k t : ℚ) (kpos : 0 < k)
    (arm : RationalVector3.OppositeSideArm
      (CartesianPoint3.displacement leftEndpoint leftReference)
      (CartesianPoint3.displacement leftEndpoint newLeftReference)
      (CartesianPoint3.displacement leftEndpoint rightEndpoint) k t) :
    RationalRule3SpatialGeometry leftEndpoint rightEndpoint newLeftReference rightReference
      (OfficialRule3Geometry.flip geometry) ↔
      RationalRule3SpatialGeometry leftEndpoint rightEndpoint leftReference rightReference geometry := by
  have hcop := CartesianPoint3.rule3Coplanarity_exchangeLeftReference leftEndpoint rightEndpoint
    leftReference newLeftReference rightReference k t arm
  have hside := CartesianPoint3.rule3SideProduct_exchangeLeftReference leftEndpoint rightEndpoint
    leftReference newLeftReference rightReference k t arm
  simpa [RationalRule3SpatialGeometry] using
    (rationalRule3SpatialGeometry_flip_iff_of_scaled
      (CartesianPoint3.rule3Coplanarity leftEndpoint rightEndpoint leftReference rightReference)
      (CartesianPoint3.rule3SideProduct leftEndpoint rightEndpoint leftReference rightReference)
      (CartesianPoint3.rule3Coplanarity leftEndpoint rightEndpoint newLeftReference rightReference)
      (CartesianPoint3.rule3SideProduct leftEndpoint rightEndpoint newLeftReference rightReference)
      geometry k kpos hcop hside)

/-! ## Exact `Option.map flip` geometry laws -/

/-- The exact classifier flips under a single right-endpoint reference exchange, including the
degenerate/noncoplanar refusals: `none` stays `none`, `seqcis` becomes `seqtrans`, and `seqtrans`
becomes `seqcis`. -/
theorem rule3GeometryOfSpatialReferences?_exchangeRightReference
    (leftEndpoint rightEndpoint leftReference rightReference newRightReference : CartesianPoint3)
    (k t : ℚ) (kpos : 0 < k)
    (arm : RationalVector3.OppositeSideArm
      (CartesianPoint3.displacement rightEndpoint rightReference)
      (CartesianPoint3.displacement rightEndpoint newRightReference)
      (CartesianPoint3.displacement leftEndpoint rightEndpoint) k t) :
    rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint leftReference newRightReference =
      (rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint leftReference rightReference).map
        OfficialRule3Geometry.flip := by
  cases hOld : rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint
      leftReference rightReference with
  | none =>
      have hOldNone : ¬ ∃ geometry,
          RationalRule3SpatialGeometry leftEndpoint rightEndpoint leftReference rightReference geometry :=
        (rule3GeometryOfSpatialReferences?_eq_none_iff leftEndpoint rightEndpoint
          leftReference rightReference).mp hOld
      simp
      rw [rule3GeometryOfSpatialReferences?_eq_none_iff]
      intro hNew
      rcases hNew with ⟨geometry, hgeometry⟩
      have transferred : RationalRule3SpatialGeometry leftEndpoint rightEndpoint
          leftReference rightReference (OfficialRule3Geometry.flip geometry) :=
        (rationalRule3SpatialGeometry_exchangeRightReference leftEndpoint rightEndpoint
          leftReference rightReference newRightReference (OfficialRule3Geometry.flip geometry)
          k t kpos arm).mp (by simpa [OfficialRule3Geometry.flip_flip] using hgeometry)
      exact hOldNone ⟨OfficialRule3Geometry.flip geometry, transferred⟩
  | some geometry =>
      simp
      rw [rule3GeometryOfSpatialReferences?_eq_some_iff]
      exact (rationalRule3SpatialGeometry_exchangeRightReference leftEndpoint rightEndpoint
        leftReference rightReference newRightReference geometry k t kpos arm).mpr
        ((rule3GeometryOfSpatialReferences?_eq_some_iff leftEndpoint rightEndpoint
          leftReference rightReference geometry).mp hOld)

/-- The exact classifier flips under a single left-endpoint reference exchange. -/
theorem rule3GeometryOfSpatialReferences?_exchangeLeftReference
    (leftEndpoint rightEndpoint leftReference newLeftReference rightReference : CartesianPoint3)
    (k t : ℚ) (kpos : 0 < k)
    (arm : RationalVector3.OppositeSideArm
      (CartesianPoint3.displacement leftEndpoint leftReference)
      (CartesianPoint3.displacement leftEndpoint newLeftReference)
      (CartesianPoint3.displacement leftEndpoint rightEndpoint) k t) :
    rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint newLeftReference rightReference =
      (rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint leftReference rightReference).map
        OfficialRule3Geometry.flip := by
  cases hOld : rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint
      leftReference rightReference with
  | none =>
      have hOldNone : ¬ ∃ geometry,
          RationalRule3SpatialGeometry leftEndpoint rightEndpoint leftReference rightReference geometry :=
        (rule3GeometryOfSpatialReferences?_eq_none_iff leftEndpoint rightEndpoint
          leftReference rightReference).mp hOld
      simp
      rw [rule3GeometryOfSpatialReferences?_eq_none_iff]
      intro hNew
      rcases hNew with ⟨geometry, hgeometry⟩
      have transferred : RationalRule3SpatialGeometry leftEndpoint rightEndpoint
          leftReference rightReference (OfficialRule3Geometry.flip geometry) :=
        (rationalRule3SpatialGeometry_exchangeLeftReference leftEndpoint rightEndpoint
          leftReference newLeftReference rightReference (OfficialRule3Geometry.flip geometry)
          k t kpos arm).mp (by simpa [OfficialRule3Geometry.flip_flip] using hgeometry)
      exact hOldNone ⟨OfficialRule3Geometry.flip geometry, transferred⟩
  | some geometry =>
      simp
      rw [rule3GeometryOfSpatialReferences?_eq_some_iff]
      exact (rationalRule3SpatialGeometry_exchangeLeftReference leftEndpoint rightEndpoint
        leftReference newLeftReference rightReference geometry k t kpos arm).mpr
        ((rule3GeometryOfSpatialReferences?_eq_some_iff leftEndpoint rightEndpoint
          leftReference rightReference geometry).mp hOld)

/-- Two independent reference exchanges, one at each endpoint, preserve the exact classification:
the two single-reference flips compose to the identity. -/
theorem rule3GeometryOfSpatialReferences?_exchangeBothReferences
    (leftEndpoint rightEndpoint leftReference rightReference
      newLeftReference newRightReference : CartesianPoint3)
    (kRight tRight kLeft tLeft : ℚ) (kRightPos : 0 < kRight) (kLeftPos : 0 < kLeft)
    (rightArm : RationalVector3.OppositeSideArm
      (CartesianPoint3.displacement rightEndpoint rightReference)
      (CartesianPoint3.displacement rightEndpoint newRightReference)
      (CartesianPoint3.displacement leftEndpoint rightEndpoint) kRight tRight)
    (leftArm : RationalVector3.OppositeSideArm
      (CartesianPoint3.displacement leftEndpoint leftReference)
      (CartesianPoint3.displacement leftEndpoint newLeftReference)
      (CartesianPoint3.displacement leftEndpoint rightEndpoint) kLeft tLeft) :
    rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint
        newLeftReference newRightReference =
      rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint
        leftReference rightReference := by
  calc
    rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint
        newLeftReference newRightReference =
      (rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint
        leftReference newRightReference).map OfficialRule3Geometry.flip := by
          exact rule3GeometryOfSpatialReferences?_exchangeLeftReference
            leftEndpoint rightEndpoint leftReference newLeftReference newRightReference
            kLeft tLeft kLeftPos leftArm
    _ = ((rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint
          leftReference rightReference).map OfficialRule3Geometry.flip).map
            OfficialRule3Geometry.flip := by
          rw [rule3GeometryOfSpatialReferences?_exchangeRightReference
            leftEndpoint rightEndpoint leftReference rightReference newRightReference
            kRight tRight kRightPos rightArm]
    _ = rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint
          leftReference rightReference := by
          rw [map_flip_flip]

/-! ## Molecule-level binding to semantic spatial positions -/

namespace CertifiedLocalizedCIPInput

/-- Independent molecule-backed relation: `otherRight` is an opposite-side reference partner at the
right endpoint of an accepted localized Rule-3 unit.  It uses the explicit two-substituent
selection domain (`localizedRule3ExplicitSubstituents right left`) and one consistent set of
semantic coordinates witnessing both the original `result.geometry` and the opposite-side arm
relation. -/
def DeclarativeLocalizedRule3OppositeSideRightReference
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (result : input.LocalizedRule3SpatialUnitResult) (otherRight : input.Atom) : Prop :=
  input.DeclarativeLocalizedRule3SpatialUnit left right result ∧
  otherRight ∈ input.localizedRule3ExplicitSubstituents right left ∧
    otherRight ≠ result.rightReference ∧
    ∃ leftPoint rightPoint leftReferencePoint rightReferencePoint otherRightPoint k t,
      input.SemanticSpatialPointAt left leftPoint ∧
        input.SemanticSpatialPointAt right rightPoint ∧
        input.SemanticSpatialPointAt result.leftReference leftReferencePoint ∧
        input.SemanticSpatialPointAt result.rightReference rightReferencePoint ∧
        input.SemanticSpatialPointAt otherRight otherRightPoint ∧
        RationalRule3SpatialGeometry leftPoint rightPoint leftReferencePoint rightReferencePoint
          result.geometry ∧
        0 < k ∧
        RationalVector3.OppositeSideArm
          (CartesianPoint3.displacement rightPoint rightReferencePoint)
          (CartesianPoint3.displacement rightPoint otherRightPoint)
          (CartesianPoint3.displacement leftPoint rightPoint) k t

/-- Replacing the right-endpoint senior reference by an opposite-side partner flips the exact
molecule-backed `seqcis`/`seqtrans` geometry of the unit. -/
theorem localizedRule3SpatialUnit_exchangeRightReference_geometry
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (result : input.LocalizedRule3SpatialUnitResult) (otherRight : input.Atom)
    (exchange : input.DeclarativeLocalizedRule3OppositeSideRightReference
      left right result otherRight) :
    ∃ leftPoint rightPoint leftReferencePoint rightReferencePoint otherRightPoint,
      input.SemanticSpatialPointAt left leftPoint ∧
        input.SemanticSpatialPointAt right rightPoint ∧
        input.SemanticSpatialPointAt result.leftReference leftReferencePoint ∧
        input.SemanticSpatialPointAt result.rightReference rightReferencePoint ∧
        input.SemanticSpatialPointAt otherRight otherRightPoint ∧
        rule3GeometryOfSpatialReferences? leftPoint rightPoint leftReferencePoint otherRightPoint =
          some (OfficialRule3Geometry.flip result.geometry) := by
  rcases exchange with ⟨_accepted, _present, _neReference, leftPoint, rightPoint, leftReferencePoint,
    rightReferencePoint, otherRightPoint, k, t, hleft, hright, hleftReference,
    hrightReference, hother, hgeometry, kpos, arm⟩
  have hOriginal := (rule3GeometryOfSpatialReferences?_eq_some_iff
    leftPoint rightPoint leftReferencePoint rightReferencePoint result.geometry).mpr hgeometry
  have hFlipped := rule3GeometryOfSpatialReferences?_exchangeRightReference
    leftPoint rightPoint leftReferencePoint rightReferencePoint otherRightPoint k t kpos arm
  rw [hOriginal] at hFlipped
  refine ⟨leftPoint, rightPoint, leftReferencePoint, rightReferencePoint, otherRightPoint,
    hleft, hright, hleftReference, hrightReference, hother, ?_⟩
  simpa using hFlipped

/-- Independent molecule-backed relation: `otherLeft` is an opposite-side reference partner at the
left endpoint. -/
def DeclarativeLocalizedRule3OppositeSideLeftReference
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (result : input.LocalizedRule3SpatialUnitResult) (otherLeft : input.Atom) : Prop :=
  input.DeclarativeLocalizedRule3SpatialUnit left right result ∧
  otherLeft ∈ input.localizedRule3ExplicitSubstituents left right ∧
    otherLeft ≠ result.leftReference ∧
    ∃ leftPoint rightPoint leftReferencePoint rightReferencePoint otherLeftPoint k t,
      input.SemanticSpatialPointAt left leftPoint ∧
        input.SemanticSpatialPointAt right rightPoint ∧
        input.SemanticSpatialPointAt result.leftReference leftReferencePoint ∧
        input.SemanticSpatialPointAt result.rightReference rightReferencePoint ∧
        input.SemanticSpatialPointAt otherLeft otherLeftPoint ∧
        RationalRule3SpatialGeometry leftPoint rightPoint leftReferencePoint rightReferencePoint
          result.geometry ∧
        0 < k ∧
        RationalVector3.OppositeSideArm
          (CartesianPoint3.displacement leftPoint leftReferencePoint)
          (CartesianPoint3.displacement leftPoint otherLeftPoint)
          (CartesianPoint3.displacement leftPoint rightPoint) k t

/-- Replacing the left-endpoint senior reference by an opposite-side partner flips the exact
molecule-backed `seqcis`/`seqtrans` geometry of the unit. -/
theorem localizedRule3SpatialUnit_exchangeLeftReference_geometry
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (result : input.LocalizedRule3SpatialUnitResult) (otherLeft : input.Atom)
    (exchange : input.DeclarativeLocalizedRule3OppositeSideLeftReference
      left right result otherLeft) :
    ∃ leftPoint rightPoint leftReferencePoint rightReferencePoint otherLeftPoint,
      input.SemanticSpatialPointAt left leftPoint ∧
        input.SemanticSpatialPointAt right rightPoint ∧
        input.SemanticSpatialPointAt result.leftReference leftReferencePoint ∧
        input.SemanticSpatialPointAt result.rightReference rightReferencePoint ∧
        input.SemanticSpatialPointAt otherLeft otherLeftPoint ∧
        rule3GeometryOfSpatialReferences? leftPoint rightPoint otherLeftPoint rightReferencePoint =
          some (OfficialRule3Geometry.flip result.geometry) := by
  rcases exchange with ⟨_accepted, _present, _neReference, leftPoint, rightPoint, leftReferencePoint,
    rightReferencePoint, otherLeftPoint, k, t, hleft, hright, hleftReference,
    hrightReference, hother, hgeometry, kpos, arm⟩
  have hOriginal := (rule3GeometryOfSpatialReferences?_eq_some_iff
    leftPoint rightPoint leftReferencePoint rightReferencePoint result.geometry).mpr hgeometry
  have hFlipped := rule3GeometryOfSpatialReferences?_exchangeLeftReference
    leftPoint rightPoint leftReferencePoint otherLeftPoint rightReferencePoint k t kpos arm
  rw [hOriginal] at hFlipped
  refine ⟨leftPoint, rightPoint, leftReferencePoint, rightReferencePoint, otherLeftPoint,
    hleft, hright, hleftReference, hrightReference, hother, ?_⟩
  simpa using hFlipped

/-- Independent molecule-backed relation for two opposite-side partners, one at each endpoint. -/
def DeclarativeLocalizedRule3OppositeSideReferences
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (result : input.LocalizedRule3SpatialUnitResult)
    (otherLeft otherRight : input.Atom) : Prop :=
  input.DeclarativeLocalizedRule3SpatialUnit left right result ∧
  otherLeft ∈ input.localizedRule3ExplicitSubstituents left right ∧
    otherLeft ≠ result.leftReference ∧
    otherRight ∈ input.localizedRule3ExplicitSubstituents right left ∧
    otherRight ≠ result.rightReference ∧
    ∃ leftPoint rightPoint leftReferencePoint rightReferencePoint
        otherLeftPoint otherRightPoint kLeft tLeft kRight tRight,
      input.SemanticSpatialPointAt left leftPoint ∧
        input.SemanticSpatialPointAt right rightPoint ∧
        input.SemanticSpatialPointAt result.leftReference leftReferencePoint ∧
        input.SemanticSpatialPointAt result.rightReference rightReferencePoint ∧
        input.SemanticSpatialPointAt otherLeft otherLeftPoint ∧
        input.SemanticSpatialPointAt otherRight otherRightPoint ∧
        RationalRule3SpatialGeometry leftPoint rightPoint leftReferencePoint rightReferencePoint
          result.geometry ∧
        0 < kLeft ∧ 0 < kRight ∧
        RationalVector3.OppositeSideArm
          (CartesianPoint3.displacement leftPoint leftReferencePoint)
          (CartesianPoint3.displacement leftPoint otherLeftPoint)
          (CartesianPoint3.displacement leftPoint rightPoint) kLeft tLeft ∧
        RationalVector3.OppositeSideArm
          (CartesianPoint3.displacement rightPoint rightReferencePoint)
          (CartesianPoint3.displacement rightPoint otherRightPoint)
          (CartesianPoint3.displacement leftPoint rightPoint) kRight tRight

/-- Replacing both endpoint senior references by independent opposite-side partners preserves the
exact molecule-backed `seqcis`/`seqtrans` geometry of the unit. -/
theorem localizedRule3SpatialUnit_exchangeBothReferences_geometry
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (result : input.LocalizedRule3SpatialUnitResult)
    (otherLeft otherRight : input.Atom)
    (exchange : input.DeclarativeLocalizedRule3OppositeSideReferences
      left right result otherLeft otherRight) :
    ∃ leftPoint rightPoint leftReferencePoint rightReferencePoint otherLeftPoint otherRightPoint,
      input.SemanticSpatialPointAt left leftPoint ∧
        input.SemanticSpatialPointAt right rightPoint ∧
        input.SemanticSpatialPointAt result.leftReference leftReferencePoint ∧
        input.SemanticSpatialPointAt result.rightReference rightReferencePoint ∧
        input.SemanticSpatialPointAt otherLeft otherLeftPoint ∧
        input.SemanticSpatialPointAt otherRight otherRightPoint ∧
        rule3GeometryOfSpatialReferences? leftPoint rightPoint otherLeftPoint otherRightPoint =
          some result.geometry := by
  rcases exchange with ⟨_accepted, _presentLeft, _neLeft, _presentRight, _neRight, leftPoint, rightPoint,
    leftReferencePoint, rightReferencePoint, otherLeftPoint, otherRightPoint,
    kLeft, tLeft, kRight, tRight, hleft, hright, hleftReference, hrightReference,
    hotherLeft, hotherRight, hgeometry, kLeftPos, kRightPos, leftArm, rightArm⟩
  have hOriginal := (rule3GeometryOfSpatialReferences?_eq_some_iff
    leftPoint rightPoint leftReferencePoint rightReferencePoint result.geometry).mpr hgeometry
  have hBoth := rule3GeometryOfSpatialReferences?_exchangeBothReferences
    leftPoint rightPoint leftReferencePoint rightReferencePoint otherLeftPoint otherRightPoint
    kRight tRight kLeft tLeft kRightPos kLeftPos rightArm leftArm
  rw [hOriginal] at hBoth
  refine ⟨leftPoint, rightPoint, leftReferencePoint, rightReferencePoint, otherLeftPoint,
    otherRightPoint, hleft, hright, hleftReference, hrightReference, hotherLeft, hotherRight, ?_⟩
  simpa using hBoth

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards for the load-bearing transport laws -/

assert_kernel_only TetraStereo.OneCenter.rule3GeometryOfSpatialReferences?_exchangeRightReference
assert_kernel_only TetraStereo.OneCenter.rule3GeometryOfSpatialReferences?_exchangeLeftReference
assert_kernel_only TetraStereo.OneCenter.rule3GeometryOfSpatialReferences?_exchangeBothReferences
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3SpatialUnit_exchangeRightReference_geometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3SpatialUnit_exchangeLeftReference_geometry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3SpatialUnit_exchangeBothReferences_geometry
