import TetraStereo.OneCenter.LocalizedRule3ReferenceExchange
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter










































namespace RationalVector3

/-! ## Exact rational vector algebra used by the witness construction -/

/-- The exact squared norm of a nonzero rational vector is strictly positive. -/
theorem dot_self_pos {v : RationalVector3} (hv : v ≠ 0) : 0 < dot v v := by
  by_cases hx : v.x = 0
  · by_cases hy : v.y = 0
    · have hz : v.z ≠ 0 := by
        intro hz
        exact hv (by
          apply RationalVector3.ext <;> simp [hx, hy, hz])
      have hzpos : 0 < v.z * v.z := mul_self_pos.mpr hz
      have hxzero : v.x * v.x = 0 := by simp [hx]
      have hyzero : v.y * v.y = 0 := by simp [hy]
      simp only [dot]
      linarith
    · have hypos : 0 < v.y * v.y := mul_self_pos.mpr hy
      have hxzero : v.x * v.x = 0 := by simp [hx]
      have hznonneg : 0 ≤ v.z * v.z := mul_self_nonneg v.z
      simp only [dot]
      linarith
  · have hxpos : 0 < v.x * v.x := mul_self_pos.mpr hx
    have hynonneg : 0 ≤ v.y * v.y := mul_self_nonneg v.y
    have hznonneg : 0 ≤ v.z * v.z := mul_self_nonneg v.z
    simp only [dot]
    linarith

/-- Scaling a nonzero vector by a rational scalar gives zero exactly when the scalar is zero. -/
theorem vsmul_eq_zero_iff {c : ℚ} {v : RationalVector3} (hv : v ≠ 0) :
    vsmul c v = 0 ↔ c = 0 := by
  constructor
  · intro h
    by_cases hx : v.x = 0
    · by_cases hy : v.y = 0
      · have hz : v.z ≠ 0 := by
          intro hz
          exact hv (by
            apply RationalVector3.ext <;> simp [hx, hy, hz])
        have hcomp : c * v.z = 0 := by
          have := congrArg RationalVector3.z h
          simpa [vsmul] using this
        exact (mul_eq_zero.mp hcomp).resolve_right hz
      · have hcomp : c * v.y = 0 := by
          have := congrArg RationalVector3.y h
          simpa [vsmul] using this
        exact (mul_eq_zero.mp hcomp).resolve_right hy
    · have hcomp : c * v.x = 0 := by
        have := congrArg RationalVector3.x h
        simpa [vsmul] using this
      exact (mul_eq_zero.mp hcomp).resolve_right hx
  · intro hc
    apply RationalVector3.ext <;> simp [vsmul, hc]

/-- The vector triple-product identity linking the crossed side normals to the scalar triple
product: `(axis × u) × (axis × v) = (axis · (u × v)) • axis`. -/
theorem cross_cross_eq_dot_cross_vsmul (axis u v : RationalVector3) :
    cross (cross axis u) (cross axis v) = vsmul (dot axis (cross u v)) axis := by
  apply RationalVector3.ext <;> simp [cross, dot, vsmul] <;> ring

/-- Two rational vectors with vanishing cross product are parallel.  The nonzero vector `p` is the
direction; the scalar is constructed from a nonzero component of `p`. -/
theorem exists_vsmul_eq_of_cross_eq_zero {p q : RationalVector3}
    (h : cross p q = 0) (hp : p ≠ 0) :
    ∃ c : ℚ, q = vsmul c p := by
  have hx : p.y * q.z - p.z * q.y = 0 := by
    have := congrArg RationalVector3.x h
    simpa [cross] using this
  have hy : p.z * q.x - p.x * q.z = 0 := by
    have := congrArg RationalVector3.y h
    simpa [cross] using this
  have hz : p.x * q.y - p.y * q.x = 0 := by
    have := congrArg RationalVector3.z h
    simpa [cross] using this
  by_cases hpx : p.x = 0
  · by_cases hpy : p.y = 0
    · have hpz : p.z ≠ 0 := by
        intro hpz
        exact hp (by apply RationalVector3.ext <;> simp [hpx, hpy, hpz])
      have hqx : q.x = 0 := by
        have hzero : p.z * q.x = 0 := by
          have hy' := hy
          rw [hpx, zero_mul, sub_zero] at hy'
          exact hy'
        exact (mul_eq_zero.mp hzero).resolve_left hpz
      have hqy : q.y = 0 := by
        have hzero : p.z * q.y = 0 := by
          have hx' := hx
          rw [hpy, zero_mul, zero_sub] at hx'
          linarith
        exact (mul_eq_zero.mp hzero).resolve_left hpz
      refine ⟨q.z / p.z, ?_⟩
      apply RationalVector3.ext
      · show q.x = (q.z / p.z) * p.x
        rw [hpx, mul_zero]
        exact hqx
      · show q.y = (q.z / p.z) * p.y
        rw [hpy, mul_zero]
        exact hqy
      · show q.z = (q.z / p.z) * p.z
        exact (div_mul_cancel₀ q.z hpz).symm
    · have hqx : q.x = 0 := by
        have hzero : p.y * q.x = 0 := by
          have hz' := hz
          rw [hpx, zero_mul, zero_sub] at hz'
          linarith
        exact (mul_eq_zero.mp hzero).resolve_left hpy
      refine ⟨q.y / p.y, ?_⟩
      apply RationalVector3.ext
      · show q.x = (q.y / p.y) * p.x
        rw [hpx, mul_zero]
        exact hqx
      · show q.y = (q.y / p.y) * p.y
        exact (div_mul_cancel₀ q.y hpy).symm
      · show q.z = (q.y / p.y) * p.z
        rw [div_mul_eq_mul_div, eq_div_iff hpy]
        linarith [hx]
  · refine ⟨q.x / p.x, ?_⟩
    apply RationalVector3.ext
    · show q.x = (q.x / p.x) * p.x
      exact (div_mul_cancel₀ q.x hpx).symm
    · show q.y = (q.x / p.x) * p.y
      rw [div_mul_eq_mul_div, eq_div_iff hpx]
      linarith [hz]
    · show q.z = (q.x / p.x) * p.z
      rw [div_mul_eq_mul_div, eq_div_iff hpx]
      linarith [hy]

/-- Coplanarity transfers across a common anchoring arm: if two arms are each coplanar with the
axis and a nondegenerate anchor arm, then they are coplanar with each other and the axis.  This is
the linear-algebra step that turns the four-substituent plane into the exchanged pair's plane. -/
theorem dot_cross_eq_zero_of_anchor_coplanar
    (axis anchor first second : RationalVector3)
    (haxis : axis ≠ 0) (hanchor : cross axis anchor ≠ 0)
    (hfirst : dot axis (cross anchor first) = 0)
    (hsecond : dot axis (cross anchor second) = 0) :
    dot axis (cross first second) = 0 := by
  have hNfirst : cross (cross axis anchor) (cross axis first) = 0 := by
    calc cross (cross axis anchor) (cross axis first)
        = vsmul (dot axis (cross anchor first)) axis :=
          cross_cross_eq_dot_cross_vsmul axis anchor first
      _ = vsmul 0 axis := by rw [hfirst]
      _ = 0 := by
        apply RationalVector3.ext <;> simp [vsmul]
  have hNsecond : cross (cross axis anchor) (cross axis second) = 0 := by
    calc cross (cross axis anchor) (cross axis second)
        = vsmul (dot axis (cross anchor second)) axis :=
          cross_cross_eq_dot_cross_vsmul axis anchor second
      _ = vsmul 0 axis := by rw [hsecond]
      _ = 0 := by
        apply RationalVector3.ext <;> simp [vsmul]
  obtain ⟨c, hc⟩ := exists_vsmul_eq_of_cross_eq_zero hNfirst hanchor
  obtain ⟨d, hd⟩ := exists_vsmul_eq_of_cross_eq_zero hNsecond hanchor
  have hcross : cross (cross axis first) (cross axis second) = 0 := by
    rw [hc, hd]
    simp [cross_vsmul_left, cross_vsmul_right, cross_self]
  have hdet : vsmul (dot axis (cross first second)) axis = 0 := by
    calc vsmul (dot axis (cross first second)) axis
        = cross (cross axis first) (cross axis second) :=
          (cross_cross_eq_dot_cross_vsmul axis first second).symm
      _ = 0 := hcross
  exact (vsmul_eq_zero_iff (v := axis) (c := dot axis (cross first second)) haxis).mp hdet

/-! ## The coordinate opposite-side condition and its arm relation -/

/-- Exact three-vector planar opposite-side condition for one endpoint's two substituent arms.

`axis` is the directed double-bond axis.  `oldArm` is the currently selected reference arm and
`newArm` the alternative substituent arm, both measured from the same endpoint.

The condition says that the axis is nonzero, the old arm has a nonzero side normal `axis × oldArm`,
the three vectors are coplanar (`axis · (oldArm × newArm) = 0`), and the two side normals have
strictly negative dot product, i.e. the arms lie on opposite sides of the axis line.  It mentions no
scale witness and no axis shift. -/
def PlanarOppositeSideArms (axis oldArm newArm : RationalVector3) : Prop :=
  axis ≠ 0 ∧ cross axis oldArm ≠ 0 ∧
    dot axis (cross oldArm newArm) = 0 ∧
      dot (cross axis oldArm) (cross axis newArm) < 0

/-- **Construction direction (positive scale derived).**  The exact planar opposite-side condition
produces a negative scale `k > 0` and an axis shift `t` with `newArm = (-k) • oldArm + t • axis`.

The proof decomposes the problem exactly: coplanarity makes the crossed side normals parallel,
the strictly negative dot product makes the parallel scalar strictly negative, and then
`axis × (newArm + k • oldArm) = 0` forces the residual to lie on the axis. -/
theorem exists_oppositeSideArm_of_planarOppositeSide
    (axis oldArm newArm : RationalVector3)
    (haxis : axis ≠ 0) (hnorm : cross axis oldArm ≠ 0)
    (hcop : dot axis (cross oldArm newArm) = 0)
    (hside : dot (cross axis oldArm) (cross axis newArm) < 0) :
    ∃ k t : ℚ, 0 < k ∧ OppositeSideArm oldArm newArm axis k t := by
  have hnormPos : 0 < dot (cross axis oldArm) (cross axis oldArm) := dot_self_pos hnorm
  have hcrossNorm : cross (cross axis oldArm) (cross axis newArm) = 0 := by
    calc cross (cross axis oldArm) (cross axis newArm)
        = vsmul (dot axis (cross oldArm newArm)) axis :=
          cross_cross_eq_dot_cross_vsmul axis oldArm newArm
      _ = vsmul 0 axis := by rw [hcop]
      _ = 0 := by
        apply RationalVector3.ext <;> simp [vsmul]
  obtain ⟨c, hc⟩ := exists_vsmul_eq_of_cross_eq_zero hcrossNorm hnorm
  have hside' : c * dot (cross axis oldArm) (cross axis oldArm) < 0 := by
    have h := hside
    rw [hc, dot_vsmul_right] at h
    exact h
  have hcneg : c < 0 := by
    by_contra hnonneg
    have hnonneg' : 0 ≤ c := le_of_not_gt hnonneg
    have hnonnegProd : 0 ≤ c * dot (cross axis oldArm) (cross axis oldArm) :=
      mul_nonneg hnonneg' hnormPos.le
    linarith
  let k : ℚ := -c
  have hkpos : 0 < k := by
    show 0 < -c
    linarith
  have hk_eq : -k = c := by
    show -(-c) = c
    ring
  have hNv : cross axis newArm = vsmul (-k) (cross axis oldArm) := by
    rw [hk_eq]
    exact hc
  have hcrossW : cross axis (vadd newArm (vsmul k oldArm)) = 0 := by
    rw [cross_vadd_right, cross_vsmul_right, hNv]
    apply RationalVector3.ext <;> simp [vadd, vsmul]
  obtain ⟨t, ht⟩ := exists_vsmul_eq_of_cross_eq_zero hcrossW haxis
  refine ⟨k, t, hkpos, ?_⟩
  show newArm = vadd (vsmul (-k) oldArm) (vsmul t axis)
  apply RationalVector3.ext
  · have h := congrArg RationalVector3.x ht
    simp [vadd, vsmul] at h ⊢
    linarith
  · have h := congrArg RationalVector3.y ht
    simp [vadd, vsmul] at h ⊢
    linarith
  · have h := congrArg RationalVector3.z ht
    simp [vadd, vsmul] at h ⊢
    linarith

/-- **Converse direction.**  Any negative-scale arm relation with a nonzero axis and a nonzero old
side normal satisfies the exact planar opposite-side condition. -/
theorem planarOppositeSide_of_oppositeSideArm
    (axis oldArm newArm : RationalVector3) (k t : ℚ) (kpos : 0 < k)
    (haxis : axis ≠ 0) (hnorm : cross axis oldArm ≠ 0)
    (arm : OppositeSideArm oldArm newArm axis k t) :
    PlanarOppositeSideArms axis oldArm newArm := by
  unfold PlanarOppositeSideArms
  refine ⟨haxis, hnorm, ?_, ?_⟩
  · show dot axis (cross oldArm newArm) = 0
    rw [arm]
    simp only [dot, cross, vadd, vsmul]
    ring
  · show dot (cross axis oldArm) (cross axis newArm) < 0
    rw [dot_crossAxis_of_oppositeSide axis oldArm oldArm newArm k t arm]
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr kpos) (dot_self_pos hnorm)

/-- **Both directions.**  Over exact rationals the coordinate planar opposite-side condition is
equivalent to the explicit nondegeneracy data plus the existence of the negative scale and axis
shift.  In particular the positive scale is a consequence of the coordinates. -/
theorem planarOppositeSideArms_iff_exists_oppositeSideArm
    (axis oldArm newArm : RationalVector3) :
    PlanarOppositeSideArms axis oldArm newArm ↔
      axis ≠ 0 ∧ cross axis oldArm ≠ 0 ∧
        ∃ k t : ℚ, 0 < k ∧ OppositeSideArm oldArm newArm axis k t := by
  constructor
  · intro h
    unfold PlanarOppositeSideArms at h
    rcases h with ⟨haxis, hnorm, hcop, hside⟩
    obtain ⟨k, t, hk, arm⟩ :=
      exists_oppositeSideArm_of_planarOppositeSide axis oldArm newArm haxis hnorm hcop hside
    exact ⟨haxis, hnorm, k, t, hk, arm⟩
  · rintro ⟨haxis, hnorm, k, t, hk, arm⟩
    exact planarOppositeSide_of_oppositeSideArm axis oldArm newArm k t hk haxis hnorm arm

end RationalVector3

/-! ## The four-substituent coordinate condition at a Cartesian endpoint -/

namespace CartesianPoint3

/-- Exact coordinate form of the planar four-substituent opposite-side condition at the **right**
endpoint of a Rule-3 double bond.

The four substituents are the two substituent points at the left endpoint
(`leftReference`, `leftPartner`) and the two at the right endpoint
(`rightReference`, `newRightReference`).  The `leftReference` arm is the nondegenerate anchor; all
four substituent arms lie in one plane through the directed axis, and at the right endpoint the
selected reference and its alternative lie strictly on opposite sides of the axis

No scale witness or axis shift appears: every field is a coordinate equation. -/
def PlanarFourSubstituentOppositeSideRight
    (leftEndpoint rightEndpoint leftReference leftPartner rightReference
      newRightReference : CartesianPoint3) : Prop :=
  displacement leftEndpoint rightEndpoint ≠ 0 ∧
    RationalVector3.cross (displacement leftEndpoint rightEndpoint)
        (displacement leftEndpoint leftReference) ≠ 0 ∧
      RationalVector3.cross (displacement leftEndpoint rightEndpoint)
          (displacement rightEndpoint rightReference) ≠ 0 ∧
        RationalVector3.dot (displacement leftEndpoint rightEndpoint)
            (RationalVector3.cross (displacement leftEndpoint leftReference)
              (displacement leftEndpoint leftPartner)) = 0 ∧
          RationalVector3.dot (displacement leftEndpoint rightEndpoint)
              (RationalVector3.cross (displacement leftEndpoint leftReference)
                (displacement rightEndpoint rightReference)) = 0 ∧
            RationalVector3.dot (displacement leftEndpoint rightEndpoint)
                (RationalVector3.cross (displacement leftEndpoint leftReference)
                  (displacement rightEndpoint newRightReference)) = 0 ∧
              RationalVector3.dot
                  (RationalVector3.cross (displacement leftEndpoint rightEndpoint)
                    (displacement rightEndpoint rightReference))
                  (RationalVector3.cross (displacement leftEndpoint rightEndpoint)
                    (displacement rightEndpoint newRightReference)) < 0

/-- The four-substituent right-endpoint condition yields the exact three-vector planar
opposite-side condition for the right endpoint's two arms. -/
theorem planarOppositeSideArms_of_planarFourSubstituentOppositeSideRight
    (leftEndpoint rightEndpoint leftReference leftPartner rightReference
      newRightReference : CartesianPoint3)
    (h : PlanarFourSubstituentOppositeSideRight leftEndpoint rightEndpoint
      leftReference leftPartner rightReference newRightReference) :
    RationalVector3.PlanarOppositeSideArms
      (displacement leftEndpoint rightEndpoint)
      (displacement rightEndpoint rightReference)
      (displacement rightEndpoint newRightReference) := by
  unfold PlanarFourSubstituentOppositeSideRight at h
  rcases h with ⟨haxis, hleftNorm, hrightNorm, _hleftPartnerPlane, hleftRightPlane,
    hleftNewPlane, hside⟩
  unfold RationalVector3.PlanarOppositeSideArms
  refine ⟨haxis, hrightNorm, ?_, hside⟩
  exact RationalVector3.dot_cross_eq_zero_of_anchor_coplanar
    (displacement leftEndpoint rightEndpoint)
    (displacement leftEndpoint leftReference)
    (displacement rightEndpoint rightReference)
    (displacement rightEndpoint newRightReference)
    haxis hleftNorm hleftRightPlane hleftNewPlane

/-- A right-endpoint exchange certificate is constructible from the four-substituent coordinate
condition alone: the negative scale and the axis shift are produced, not requested. -/
theorem exists_oppositeSideArm_of_planarFourSubstituentOppositeSideRight
    (leftEndpoint rightEndpoint leftReference leftPartner rightReference
      newRightReference : CartesianPoint3)
    (h : PlanarFourSubstituentOppositeSideRight leftEndpoint rightEndpoint
      leftReference leftPartner rightReference newRightReference) :
    ∃ k t : ℚ, 0 < k ∧
      RationalVector3.OppositeSideArm
        (displacement rightEndpoint rightReference)
        (displacement rightEndpoint newRightReference)
        (displacement leftEndpoint rightEndpoint) k t := by
  have hcond := planarOppositeSideArms_of_planarFourSubstituentOppositeSideRight
    leftEndpoint rightEndpoint leftReference leftPartner rightReference newRightReference h
  unfold RationalVector3.PlanarOppositeSideArms at hcond
  rcases hcond with ⟨haxis, hnorm, hcop, hside⟩
  exact RationalVector3.exists_oppositeSideArm_of_planarOppositeSide
    _ _ _ haxis hnorm hcop hside

/-- **Witness-free right-endpoint flip.**  From the exact planar four-substituent coordinate
condition, the Rule-3 classifier of the exchanged right reference is the flipped classifier of the
selected reference.  The arm relation used is derived in this module; the classifier transport is
the existing GREEN `rule3GeometryOfSpatialReferences?_exchangeRightReference`. -/
theorem rule3GeometryOfSpatialReferences?_exchangeRightReference_of_planarFourSubstituent
    (leftEndpoint rightEndpoint leftReference leftPartner rightReference
      newRightReference : CartesianPoint3)
    (h : PlanarFourSubstituentOppositeSideRight leftEndpoint rightEndpoint
      leftReference leftPartner rightReference newRightReference) :
    rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint leftReference
        newRightReference =
      (rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint leftReference
        rightReference).map OfficialRule3Geometry.flip := by
  obtain ⟨k, t, hk, arm⟩ :=
    exists_oppositeSideArm_of_planarFourSubstituentOppositeSideRight
      leftEndpoint rightEndpoint leftReference leftPartner rightReference newRightReference h
  exact rule3GeometryOfSpatialReferences?_exchangeRightReference leftEndpoint rightEndpoint
    leftReference rightReference newRightReference k t hk arm

/-- Exact coordinate form of the planar four-substituent opposite-side condition at the **left**
endpoint.  The four substituents are the two left-endpoint points (`leftReference`,
`newLeftReference`) and the two right-endpoint points (`rightReference`, `rightPartner`).  The
`rightReference` arm is the nondegenerate anchor. -/
def PlanarFourSubstituentOppositeSideLeft
    (leftEndpoint rightEndpoint leftReference newLeftReference rightReference
      rightPartner : CartesianPoint3) : Prop :=
  displacement leftEndpoint rightEndpoint ≠ 0 ∧
    RationalVector3.cross (displacement leftEndpoint rightEndpoint)
        (displacement rightEndpoint rightReference) ≠ 0 ∧
      RationalVector3.cross (displacement leftEndpoint rightEndpoint)
          (displacement leftEndpoint leftReference) ≠ 0 ∧
        RationalVector3.dot (displacement leftEndpoint rightEndpoint)
            (RationalVector3.cross (displacement rightEndpoint rightReference)
              (displacement rightEndpoint rightPartner)) = 0 ∧
          RationalVector3.dot (displacement leftEndpoint rightEndpoint)
              (RationalVector3.cross (displacement rightEndpoint rightReference)
                (displacement leftEndpoint leftReference)) = 0 ∧
            RationalVector3.dot (displacement leftEndpoint rightEndpoint)
                (RationalVector3.cross (displacement rightEndpoint rightReference)
                  (displacement leftEndpoint newLeftReference)) = 0 ∧
              RationalVector3.dot
                  (RationalVector3.cross (displacement leftEndpoint rightEndpoint)
                    (displacement leftEndpoint leftReference))
                  (RationalVector3.cross (displacement leftEndpoint rightEndpoint)
                    (displacement leftEndpoint newLeftReference)) < 0

/-- The four-substituent left-endpoint condition yields the exact three-vector planar opposite-side
condition for the left endpoint's two arms. -/
theorem planarOppositeSideArms_of_planarFourSubstituentOppositeSideLeft
    (leftEndpoint rightEndpoint leftReference newLeftReference rightReference
      rightPartner : CartesianPoint3)
    (h : PlanarFourSubstituentOppositeSideLeft leftEndpoint rightEndpoint
      leftReference newLeftReference rightReference rightPartner) :
    RationalVector3.PlanarOppositeSideArms
      (displacement leftEndpoint rightEndpoint)
      (displacement leftEndpoint leftReference)
      (displacement leftEndpoint newLeftReference) := by
  unfold PlanarFourSubstituentOppositeSideLeft at h
  rcases h with ⟨haxis, hrightNorm, hleftNorm, _hrightPartnerPlane, hrightLeftPlane,
    hrightNewPlane, hside⟩
  unfold RationalVector3.PlanarOppositeSideArms
  refine ⟨haxis, hleftNorm, ?_, hside⟩
  exact RationalVector3.dot_cross_eq_zero_of_anchor_coplanar
    (displacement leftEndpoint rightEndpoint)
    (displacement rightEndpoint rightReference)
    (displacement leftEndpoint leftReference)
    (displacement leftEndpoint newLeftReference)
    haxis hrightNorm hrightLeftPlane hrightNewPlane

/-- A left-endpoint exchange certificate is constructible from the four-substituent coordinate
condition alone. -/
theorem exists_oppositeSideArm_of_planarFourSubstituentOppositeSideLeft
    (leftEndpoint rightEndpoint leftReference newLeftReference rightReference
      rightPartner : CartesianPoint3)
    (h : PlanarFourSubstituentOppositeSideLeft leftEndpoint rightEndpoint
      leftReference newLeftReference rightReference rightPartner) :
    ∃ k t : ℚ, 0 < k ∧
      RationalVector3.OppositeSideArm
        (displacement leftEndpoint leftReference)
        (displacement leftEndpoint newLeftReference)
        (displacement leftEndpoint rightEndpoint) k t := by
  have hcond := planarOppositeSideArms_of_planarFourSubstituentOppositeSideLeft
    leftEndpoint rightEndpoint leftReference newLeftReference rightReference rightPartner h
  unfold RationalVector3.PlanarOppositeSideArms at hcond
  rcases hcond with ⟨haxis, hnorm, hcop, hside⟩
  exact RationalVector3.exists_oppositeSideArm_of_planarOppositeSide
    _ _ _ haxis hnorm hcop hside

/-- **Witness-free left-endpoint flip.** -/
theorem rule3GeometryOfSpatialReferences?_exchangeLeftReference_of_planarFourSubstituent
    (leftEndpoint rightEndpoint leftReference newLeftReference rightReference
      rightPartner : CartesianPoint3)
    (h : PlanarFourSubstituentOppositeSideLeft leftEndpoint rightEndpoint
      leftReference newLeftReference rightReference rightPartner) :
    rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint newLeftReference
        rightReference =
      (rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint leftReference
        rightReference).map OfficialRule3Geometry.flip := by
  obtain ⟨k, t, hk, arm⟩ :=
    exists_oppositeSideArm_of_planarFourSubstituentOppositeSideLeft
      leftEndpoint rightEndpoint leftReference newLeftReference rightReference rightPartner h
  exact rule3GeometryOfSpatialReferences?_exchangeLeftReference leftEndpoint rightEndpoint
    leftReference newLeftReference rightReference k t hk arm

/-- **Witness-free two-endpoint invariance.**  Independent planar four-substituent coordinate
conditions at both endpoints preserve the exact Rule-3 classification: the two single-endpoint
flips compose to the identity. -/
theorem rule3GeometryOfSpatialReferences?_exchangeBothReferences_of_planarFourSubstituent
    (leftEndpoint rightEndpoint leftReference rightReference newLeftReference
      newRightReference leftPartner rightPartner : CartesianPoint3)
    (hLeft : PlanarFourSubstituentOppositeSideLeft leftEndpoint rightEndpoint
      leftReference newLeftReference rightReference rightPartner)
    (hRight : PlanarFourSubstituentOppositeSideRight leftEndpoint rightEndpoint
      leftReference leftPartner rightReference newRightReference) :
    rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint newLeftReference
        newRightReference =
      rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint leftReference
        rightReference := by
  obtain ⟨kRight, tRight, hkRight, rightArm⟩ :=
    exists_oppositeSideArm_of_planarFourSubstituentOppositeSideRight
      leftEndpoint rightEndpoint leftReference leftPartner rightReference newRightReference hRight
  obtain ⟨kLeft, tLeft, hkLeft, leftArm⟩ :=
    exists_oppositeSideArm_of_planarFourSubstituentOppositeSideLeft
      leftEndpoint rightEndpoint leftReference newLeftReference rightReference rightPartner hLeft
  exact rule3GeometryOfSpatialReferences?_exchangeBothReferences
    leftEndpoint rightEndpoint leftReference rightReference newLeftReference newRightReference
    kRight tRight kLeft tLeft hkRight hkLeft rightArm leftArm

end CartesianPoint3

/-! ## Molecule-backed coordinate source certificates -/

namespace CertifiedLocalizedCIPInput

/-- Molecule-backed right-endpoint source certificate stated purely in coordinates.

This is the coordinate form of
`DeclarativeLocalizedRule3OppositeSideRightReference`: the accepted localized Rule-3 unit is
retained, the alternative right substituent and the fourth (left) substituent are actual explicit
neighbours, and the two computed semantic-coordinate constraints are the exact
`RationalRule3SpatialGeometry` of the accepted result together with the planar four-substituent
opposite-side condition.  No `k`/`t` witness is requested. -/
def DeclarativeLocalizedRule3PlanarOppositeSideRightReference
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (result : input.LocalizedRule3SpatialUnitResult)
    (leftPartner otherRight : input.Atom) : Prop :=
  input.DeclarativeLocalizedRule3SpatialUnit left right result ∧
    otherRight ∈ input.localizedRule3ExplicitSubstituents right left ∧
      otherRight ≠ result.rightReference ∧
        leftPartner ∈ input.localizedRule3ExplicitSubstituents left right ∧
          leftPartner ≠ result.leftReference ∧
            ∃ leftPoint rightPoint leftReferencePoint leftPartnerPoint
                rightReferencePoint otherRightPoint,
              input.SemanticSpatialPointAt left leftPoint ∧
                input.SemanticSpatialPointAt right rightPoint ∧
                  input.SemanticSpatialPointAt result.leftReference leftReferencePoint ∧
                    input.SemanticSpatialPointAt leftPartner leftPartnerPoint ∧
                      input.SemanticSpatialPointAt result.rightReference rightReferencePoint ∧
                        input.SemanticSpatialPointAt otherRight otherRightPoint ∧
                          RationalRule3SpatialGeometry leftPoint rightPoint
                            leftReferencePoint rightReferencePoint result.geometry ∧
                            CartesianPoint3.PlanarFourSubstituentOppositeSideRight
                              leftPoint rightPoint leftReferencePoint leftPartnerPoint
                              rightReferencePoint otherRightPoint

/-- The coordinate source certificate constructs the existing negative-scale arm certificate. -/
theorem declarativeLocalizedRule3PlanarOppositeSideRightReference_implies_oppositeSide
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (result : input.LocalizedRule3SpatialUnitResult)
    (leftPartner otherRight : input.Atom)
    (exchange : input.DeclarativeLocalizedRule3PlanarOppositeSideRightReference
      left right result leftPartner otherRight) :
    input.DeclarativeLocalizedRule3OppositeSideRightReference left right result otherRight := by
  unfold DeclarativeLocalizedRule3PlanarOppositeSideRightReference at exchange
  rcases exchange with ⟨accepted, presentRight, neRight, _presentLeft, _neLeft,
    leftPoint, rightPoint, leftReferencePoint, leftPartnerPoint, rightReferencePoint,
    otherRightPoint, hleft, hright, hleftReference, _hleftPartner, hrightReference,
    hother, hgeometry, hplanar⟩
  obtain ⟨k, t, hk, arm⟩ :=
    CartesianPoint3.exists_oppositeSideArm_of_planarFourSubstituentOppositeSideRight
      leftPoint rightPoint leftReferencePoint leftPartnerPoint rightReferencePoint
      otherRightPoint hplanar
  unfold DeclarativeLocalizedRule3OppositeSideRightReference
  exact ⟨accepted, presentRight, neRight, leftPoint, rightPoint, leftReferencePoint,
    rightReferencePoint, otherRightPoint, k, t, hleft, hright, hleftReference,
    hrightReference, hother, hgeometry, hk, arm⟩

/-- A right-endpoint reference exchange justified only by the coordinate source certificate flips
the exact molecule-backed Rule-3 geometry. -/
theorem localizedRule3SpatialUnit_exchangeRightReference_geometry_of_planarFourSubstituent
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (result : input.LocalizedRule3SpatialUnitResult)
    (leftPartner otherRight : input.Atom)
    (exchange : input.DeclarativeLocalizedRule3PlanarOppositeSideRightReference
      left right result leftPartner otherRight) :
    ∃ leftPoint rightPoint leftReferencePoint rightReferencePoint otherRightPoint,
      input.SemanticSpatialPointAt left leftPoint ∧
        input.SemanticSpatialPointAt right rightPoint ∧
          input.SemanticSpatialPointAt result.leftReference leftReferencePoint ∧
            input.SemanticSpatialPointAt result.rightReference rightReferencePoint ∧
              input.SemanticSpatialPointAt otherRight otherRightPoint ∧
                rule3GeometryOfSpatialReferences? leftPoint rightPoint leftReferencePoint
                    otherRightPoint =
                  some (OfficialRule3Geometry.flip result.geometry) :=
  input.localizedRule3SpatialUnit_exchangeRightReference_geometry left right result otherRight
    (input.declarativeLocalizedRule3PlanarOppositeSideRightReference_implies_oppositeSide
      left right result leftPartner otherRight exchange)

/-- Molecule-backed left-endpoint source certificate stated purely in coordinates.  The fourth
substituent is the right-endpoint partner `rightPartner`. -/
def DeclarativeLocalizedRule3PlanarOppositeSideLeftReference
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (result : input.LocalizedRule3SpatialUnitResult)
    (otherLeft rightPartner : input.Atom) : Prop :=
  input.DeclarativeLocalizedRule3SpatialUnit left right result ∧
    otherLeft ∈ input.localizedRule3ExplicitSubstituents left right ∧
      otherLeft ≠ result.leftReference ∧
        rightPartner ∈ input.localizedRule3ExplicitSubstituents right left ∧
          rightPartner ≠ result.rightReference ∧
            ∃ leftPoint rightPoint leftReferencePoint rightReferencePoint
                otherLeftPoint rightPartnerPoint,
              input.SemanticSpatialPointAt left leftPoint ∧
                input.SemanticSpatialPointAt right rightPoint ∧
                  input.SemanticSpatialPointAt result.leftReference leftReferencePoint ∧
                    input.SemanticSpatialPointAt result.rightReference rightReferencePoint ∧
                      input.SemanticSpatialPointAt otherLeft otherLeftPoint ∧
                        input.SemanticSpatialPointAt rightPartner rightPartnerPoint ∧
                          RationalRule3SpatialGeometry leftPoint rightPoint
                            leftReferencePoint rightReferencePoint result.geometry ∧
                            CartesianPoint3.PlanarFourSubstituentOppositeSideLeft
                              leftPoint rightPoint leftReferencePoint otherLeftPoint
                              rightReferencePoint rightPartnerPoint

/-- The coordinate left-endpoint source certificate constructs the existing negative-scale arm
certificate. -/
theorem declarativeLocalizedRule3PlanarOppositeSideLeftReference_implies_oppositeSide
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (result : input.LocalizedRule3SpatialUnitResult)
    (otherLeft rightPartner : input.Atom)
    (exchange : input.DeclarativeLocalizedRule3PlanarOppositeSideLeftReference
      left right result otherLeft rightPartner) :
    input.DeclarativeLocalizedRule3OppositeSideLeftReference left right result otherLeft := by
  unfold DeclarativeLocalizedRule3PlanarOppositeSideLeftReference at exchange
  rcases exchange with ⟨accepted, presentLeft, neLeft, _presentRight, _neRight,
    leftPoint, rightPoint, leftReferencePoint, rightReferencePoint, otherLeftPoint,
    rightPartnerPoint, hleft, hright, hleftReference, hrightReference, hotherLeft,
    _hrightPartner, hgeometry, hplanar⟩
  obtain ⟨k, t, hk, arm⟩ :=
    CartesianPoint3.exists_oppositeSideArm_of_planarFourSubstituentOppositeSideLeft
      leftPoint rightPoint leftReferencePoint otherLeftPoint rightReferencePoint
      rightPartnerPoint hplanar
  unfold DeclarativeLocalizedRule3OppositeSideLeftReference
  exact ⟨accepted, presentLeft, neLeft, leftPoint, rightPoint, leftReferencePoint,
    rightReferencePoint, otherLeftPoint, k, t, hleft, hright, hleftReference,
    hrightReference, hotherLeft, hgeometry, hk, arm⟩

/-- A left-endpoint reference exchange justified only by the coordinate source certificate flips
the exact molecule-backed Rule-3 geometry. -/
theorem localizedRule3SpatialUnit_exchangeLeftReference_geometry_of_planarFourSubstituent
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (result : input.LocalizedRule3SpatialUnitResult)
    (otherLeft rightPartner : input.Atom)
    (exchange : input.DeclarativeLocalizedRule3PlanarOppositeSideLeftReference
      left right result otherLeft rightPartner) :
    ∃ leftPoint rightPoint leftReferencePoint rightReferencePoint otherLeftPoint,
      input.SemanticSpatialPointAt left leftPoint ∧
        input.SemanticSpatialPointAt right rightPoint ∧
          input.SemanticSpatialPointAt result.leftReference leftReferencePoint ∧
            input.SemanticSpatialPointAt result.rightReference rightReferencePoint ∧
              input.SemanticSpatialPointAt otherLeft otherLeftPoint ∧
                rule3GeometryOfSpatialReferences? leftPoint rightPoint otherLeftPoint
                    rightReferencePoint =
                  some (OfficialRule3Geometry.flip result.geometry) :=
  input.localizedRule3SpatialUnit_exchangeLeftReference_geometry left right result otherLeft
    (input.declarativeLocalizedRule3PlanarOppositeSideLeftReference_implies_oppositeSide
      left right result otherLeft rightPartner exchange)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards for the load-bearing results -/

assert_kernel_only TetraStereo.OneCenter.RationalVector3.dot_self_pos
assert_kernel_only TetraStereo.OneCenter.RationalVector3.vsmul_eq_zero_iff
assert_kernel_only TetraStereo.OneCenter.RationalVector3.cross_cross_eq_dot_cross_vsmul
assert_kernel_only TetraStereo.OneCenter.RationalVector3.exists_vsmul_eq_of_cross_eq_zero
assert_kernel_only TetraStereo.OneCenter.RationalVector3.dot_cross_eq_zero_of_anchor_coplanar
assert_kernel_only TetraStereo.OneCenter.RationalVector3.exists_oppositeSideArm_of_planarOppositeSide
assert_kernel_only TetraStereo.OneCenter.RationalVector3.planarOppositeSide_of_oppositeSideArm
assert_kernel_only TetraStereo.OneCenter.RationalVector3.planarOppositeSideArms_iff_exists_oppositeSideArm
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.planarOppositeSideArms_of_planarFourSubstituentOppositeSideRight
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.exists_oppositeSideArm_of_planarFourSubstituentOppositeSideRight
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.rule3GeometryOfSpatialReferences?_exchangeRightReference_of_planarFourSubstituent
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.planarOppositeSideArms_of_planarFourSubstituentOppositeSideLeft
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.exists_oppositeSideArm_of_planarFourSubstituentOppositeSideLeft
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.rule3GeometryOfSpatialReferences?_exchangeLeftReference_of_planarFourSubstituent
assert_kernel_only TetraStereo.OneCenter.CartesianPoint3.rule3GeometryOfSpatialReferences?_exchangeBothReferences_of_planarFourSubstituent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeLocalizedRule3PlanarOppositeSideRightReference_implies_oppositeSide
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3SpatialUnit_exchangeRightReference_geometry_of_planarFourSubstituent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeLocalizedRule3PlanarOppositeSideLeftReference_implies_oppositeSide
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3SpatialUnit_exchangeLeftReference_geometry_of_planarFourSubstituent
