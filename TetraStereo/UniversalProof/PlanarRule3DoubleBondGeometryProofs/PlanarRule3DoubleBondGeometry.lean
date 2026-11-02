import TetraStereo.OneCenter.LocalizedRule3Spatial

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace TetraStereo.UniversalProof.PlanarRule3DoubleBondGeometryProofs.PlanarRule3DoubleBondGeometry

open TetraStereo.OneCenter

/-!
# Exact planar Rule-3 ordinary-double-bond geometry

The source Rule-3 spatial leaf (`aromaticCanonicalRule3SpatialUnit?`) selects two strict
constitutional senior references and then hardcodes four `source.spatial?` three-dimensional
queries; an ordinary-double diagram-only source has `spatial? = none`, so those queries halt and no
key is compiled.  This module supplies the missing independent planar leaf over the existing
`CartesianPoint2` drawing type only, using the exact directed area
`planarDirectedArea a b p = (b.x - a.x) * (p.y - a.y) - (b.y - a.y) * (p.x - a.x)`.

With the senior references `p` (at endpoint `a`) and `q` (at endpoint `b`), the sign of the product
`planarDirectedArea a b p * planarDirectedArea a b q` is the side relation.  The label type is the
existing `OfficialRule3Geometry` (`seqcis`, `seqtrans`, `nonstereogenic`); positive product is
`seqcis`, negative is `seqtrans`, zero is refused.  `SameSide`, `OppositeSide` and `Noncollinear` are
stated directly on the signs of the two actual areas, and their `iff` theorems are genuine case
analyses, not restatements of the executable branch.

Nothing reads, fakes or transports a source spatial record; the comparison with the existing
three-dimensional primitive is a proof-side algebraic identity on planar lifts only.  The
source-backed reader, reference binding, global cancellation, production-frame integration,
directional parser, the intended scientific two-dimensional `seqcis`/`seqtrans` convention, and
external source adoption remain open obligations in the repair package.
-/

/-- Exact directed doubled area of the ordered drawing-plane triple `(a, b, p)`. -/
def planarDirectedArea (a b p : CartesianPoint2) : ℚ :=
  (b.x - a.x) * (p.y - a.y) - (b.y - a.y) * (p.x - a.x)

/-- Translate every drawing-plane point by one common exact shift. -/
def translatePoint (shift p : CartesianPoint2) : CartesianPoint2 :=
  { x := p.x + shift.x, y := p.y + shift.y }

/-- Uniformly scale every drawing-plane coordinate by one exact rational factor. -/
def scalePoint (factor : ℚ) (p : CartesianPoint2) : CartesianPoint2 :=
  { x := factor * p.x, y := factor * p.y }

/-- The directed area is unchanged by a common translation of all three points. -/
theorem planarDirectedArea_translate (shift a b p : CartesianPoint2) :
    planarDirectedArea (translatePoint shift a) (translatePoint shift b)
        (translatePoint shift p) = planarDirectedArea a b p := by
  simp only [planarDirectedArea, translatePoint]
  ring

/-- Uniform scaling multiplies the directed area by the squared factor. -/
theorem planarDirectedArea_scale (factor : ℚ) (a b p : CartesianPoint2) :
    planarDirectedArea (scalePoint factor a) (scalePoint factor b)
        (scalePoint factor p) = factor * factor * planarDirectedArea a b p := by
  simp only [planarDirectedArea, scalePoint]
  ring

/-- Reversing the oriented base negates the directed area (with the same apex). -/
theorem planarDirectedArea_reverse (a b q : CartesianPoint2) :
    planarDirectedArea b a q = -planarDirectedArea a b q := by
  simp only [planarDirectedArea]
  ring

/-! ## Independent side relations -/

/-- The two senior references lie strictly on the same side of the directed bond base. -/
def SameSide (a b p q : CartesianPoint2) : Prop :=
  (0 < planarDirectedArea a b p ∧ 0 < planarDirectedArea a b q) ∨
    (planarDirectedArea a b p < 0 ∧ planarDirectedArea a b q < 0)

/-- The two senior references lie strictly on opposite sides of the directed bond base. -/
def OppositeSide (a b p q : CartesianPoint2) : Prop :=
  (planarDirectedArea a b p < 0 ∧ 0 < planarDirectedArea a b q) ∨
    (0 < planarDirectedArea a b p ∧ planarDirectedArea a b q < 0)

/-- Neither senior reference is collinear with the directed bond base. -/
def Noncollinear (a b p q : CartesianPoint2) : Prop :=
  planarDirectedArea a b p ≠ 0 ∧ planarDirectedArea a b q ≠ 0

/-- The same-side sign pattern is exactly a strictly positive area product. -/
theorem sameSide_iff_pos_product (a b p q : CartesianPoint2) :
    SameSide a b p q ↔ 0 < planarDirectedArea a b p * planarDirectedArea a b q := by
  unfold SameSide
  constructor
  · rintro (⟨hp, hq⟩ | ⟨hp, hq⟩)
    · exact mul_pos hp hq
    · exact mul_pos_of_neg_of_neg hp hq
  · intro h
    rcases lt_trichotomy (planarDirectedArea a b p) 0 with hp | hp | hp
    · refine Or.inr ⟨hp, ?_⟩
      by_contra hq
      have : planarDirectedArea a b p * planarDirectedArea a b q ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hp.le (le_of_not_gt hq)
      linarith
    · rw [hp, zero_mul] at h
      exact absurd h (lt_irrefl 0)
    · refine Or.inl ⟨hp, ?_⟩
      by_contra hq
      have : planarDirectedArea a b p * planarDirectedArea a b q ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hp.le (le_of_not_gt hq)
      linarith

/-- The opposite-side sign pattern is exactly a strictly negative area product. -/
theorem oppositeSide_iff_neg_product (a b p q : CartesianPoint2) :
    OppositeSide a b p q ↔ planarDirectedArea a b p * planarDirectedArea a b q < 0 := by
  unfold OppositeSide
  constructor
  · rintro (⟨hp, hq⟩ | ⟨hp, hq⟩)
    · exact mul_neg_of_neg_of_pos hp hq
    · exact mul_neg_of_pos_of_neg hp hq
  · intro h
    rcases lt_trichotomy (planarDirectedArea a b p) 0 with hp | hp | hp
    · refine Or.inl ⟨hp, ?_⟩
      by_contra hq
      have : 0 ≤ planarDirectedArea a b p * planarDirectedArea a b q :=
        mul_nonneg_of_nonpos_of_nonpos hp.le (le_of_not_gt hq)
      linarith
    · rw [hp, zero_mul] at h
      exact absurd h (lt_irrefl 0)
    · refine Or.inr ⟨hp, ?_⟩
      by_contra hq
      have : 0 ≤ planarDirectedArea a b p * planarDirectedArea a b q :=
        mul_nonneg hp.le (le_of_not_gt hq)
      linarith

/-- Noncollinearity is exactly a nonvanishing area product. -/
theorem noncollinear_iff_ne_zero_product (a b p q : CartesianPoint2) :
    Noncollinear a b p q ↔ planarDirectedArea a b p * planarDirectedArea a b q ≠ 0 := by
  unfold Noncollinear
  constructor
  · rintro ⟨hp, hq⟩ h
    rcases mul_eq_zero.mp h with h' | h' <;> contradiction
  · intro h
    exact ⟨fun hp => h (by rw [hp, zero_mul]), fun hq => h (by rw [hq, mul_zero])⟩

/-! ## The exact planar classifier -/

/-- Exact planar Rule-3 classification of an ordinary double bond from the directed base
`(a, b)` and the two senior references `p` (at `a`) and `q` (at `b`). -/
def planarDoubleBondGeometry? (a b p q : CartesianPoint2) :
    Option OfficialRule3Geometry :=
  if 0 < planarDirectedArea a b p * planarDirectedArea a b q then
    some OfficialRule3Geometry.seqcis
  else if planarDirectedArea a b p * planarDirectedArea a b q < 0 then
    some OfficialRule3Geometry.seqtrans
  else none

/-- `seqcis` is emitted exactly on the independent same-side relation. -/
theorem planarDoubleBondGeometry?_cis_iff (a b p q : CartesianPoint2) :
    planarDoubleBondGeometry? a b p q = some OfficialRule3Geometry.seqcis ↔
      SameSide a b p q := by
  unfold planarDoubleBondGeometry?
  by_cases hpos : 0 < planarDirectedArea a b p * planarDirectedArea a b q
  · rw [if_pos hpos]
    exact ⟨fun _ => (sameSide_iff_pos_product a b p q).mpr hpos, fun _ => rfl⟩
  · rw [if_neg hpos]
    by_cases hneg : planarDirectedArea a b p * planarDirectedArea a b q < 0
    · rw [if_pos hneg]
      exact ⟨fun h => absurd h (by simp), fun hs =>
        absurd ((sameSide_iff_pos_product a b p q).mp hs) hpos⟩
    · rw [if_neg hneg]
      exact ⟨fun h => absurd h (by simp), fun hs =>
        absurd ((sameSide_iff_pos_product a b p q).mp hs) hpos⟩

/-- `seqtrans` is emitted exactly on the independent opposite-side relation. -/
theorem planarDoubleBondGeometry?_trans_iff (a b p q : CartesianPoint2) :
    planarDoubleBondGeometry? a b p q = some OfficialRule3Geometry.seqtrans ↔
      OppositeSide a b p q := by
  unfold planarDoubleBondGeometry?
  by_cases hpos : 0 < planarDirectedArea a b p * planarDirectedArea a b q
  · rw [if_pos hpos]
    exact ⟨fun h => absurd h (by simp), fun ho =>
      absurd ((oppositeSide_iff_neg_product a b p q).mp ho) (not_lt_of_ge hpos.le)⟩
  · rw [if_neg hpos]
    by_cases hneg : planarDirectedArea a b p * planarDirectedArea a b q < 0
    · rw [if_pos hneg]
      exact ⟨fun _ => (oppositeSide_iff_neg_product a b p q).mpr hneg, fun _ => rfl⟩
    · rw [if_neg hneg]
      exact ⟨fun h => absurd h (by simp), fun ho =>
        absurd ((oppositeSide_iff_neg_product a b p q).mp ho) hneg⟩

/-- Refusal is exactly the vanishing of one of the two actual directed areas: one senior reference
is collinear with the bond base at its own endpoint. -/
theorem planarDoubleBondGeometry?_none_iff_collinear (a b p q : CartesianPoint2) :
    planarDoubleBondGeometry? a b p q = none ↔
      planarDirectedArea a b p = 0 ∨ planarDirectedArea a b q = 0 := by
  unfold planarDoubleBondGeometry?
  by_cases hpos : 0 < planarDirectedArea a b p * planarDirectedArea a b q
  · rw [if_pos hpos]
    exact ⟨fun h => absurd h (by simp), fun hc => by
      rcases hc with ha | hb
      · rw [ha, zero_mul] at hpos; exact absurd hpos (lt_irrefl 0)
      · rw [hb, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)⟩
  · rw [if_neg hpos]
    by_cases hneg : planarDirectedArea a b p * planarDirectedArea a b q < 0
    · rw [if_pos hneg]
      exact ⟨fun h => absurd h (by simp), fun hc => by
        rcases hc with ha | hb
        · rw [ha, zero_mul] at hneg; exact absurd hneg (lt_irrefl 0)
        · rw [hb, mul_zero] at hneg; exact absurd hneg (lt_irrefl 0)⟩
    · rw [if_neg hneg]
      have hzero : planarDirectedArea a b p * planarDirectedArea a b q = 0 :=
        le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
      exact ⟨fun _ => mul_eq_zero.mp hzero, fun _ => rfl⟩

/-- Exact classifier iff the independent predicates, for every label including the never-emitted
`nonstereogenic` case. -/
theorem planarDoubleBondGeometry?_eq_some_iff (a b p q : CartesianPoint2)
    (geometry : OfficialRule3Geometry) :
    planarDoubleBondGeometry? a b p q = some geometry ↔
      (geometry = OfficialRule3Geometry.seqcis ∧ SameSide a b p q) ∨
        (geometry = OfficialRule3Geometry.seqtrans ∧ OppositeSide a b p q) := by
  cases geometry with
  | seqcis =>
      rw [planarDoubleBondGeometry?_cis_iff]
      simp
  | seqtrans =>
      rw [planarDoubleBondGeometry?_trans_iff]
      simp
  | nonstereogenic =>
      have hnever : planarDoubleBondGeometry? a b p q ≠
          some OfficialRule3Geometry.nonstereogenic := by
        intro h
        unfold planarDoubleBondGeometry? at h
        split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · exact absurd h (by simp)
      constructor
      · intro h; exact absurd h hnever
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact absurd h (by simp)

/-! ## Invariance -/

/-- Presenting the opposite physical endpoint first, together with the matching reference exchange,
leaves the classification unchanged.  This is the single physical reversal, not a caller relabel. -/
theorem planarDoubleBondGeometry?_endpoint_reference_swap (a b p q : CartesianPoint2) :
    planarDoubleBondGeometry? b a q p = planarDoubleBondGeometry? a b p q := by
  unfold planarDoubleBondGeometry?
  have hprod : planarDirectedArea b a q * planarDirectedArea b a p =
      planarDirectedArea a b p * planarDirectedArea a b q := by
    rw [planarDirectedArea_reverse a b q, planarDirectedArea_reverse a b p]
    ring
  rw [hprod]

/-- A common translation of all four drawing points leaves the classification unchanged. -/
theorem planarDoubleBondGeometry?_translate (shift a b p q : CartesianPoint2) :
    planarDoubleBondGeometry? (translatePoint shift a) (translatePoint shift b)
        (translatePoint shift p) (translatePoint shift q) =
      planarDoubleBondGeometry? a b p q := by
  unfold planarDoubleBondGeometry?
  simp only [planarDirectedArea_translate]

/-- A nonzero uniform scaling of all four drawing points leaves the classification unchanged. -/
theorem planarDoubleBondGeometry?_scale (factor : ℚ) (hfactor : factor ≠ 0)
    (a b p q : CartesianPoint2) :
    planarDoubleBondGeometry? (scalePoint factor a) (scalePoint factor b)
        (scalePoint factor p) (scalePoint factor q) =
      planarDoubleBondGeometry? a b p q := by
  unfold planarDoubleBondGeometry?
  simp only [planarDirectedArea_scale]
  have hpos : 0 < factor * factor := mul_self_pos.mpr hfactor
  have hcoef : 0 < (factor * factor) * (factor * factor) := mul_pos hpos hpos
  have hprodEq :
      (factor * factor * planarDirectedArea a b p) *
          (factor * factor * planarDirectedArea a b q) =
        ((factor * factor) * (factor * factor)) *
          (planarDirectedArea a b p * planarDirectedArea a b q) := by
    ring
  have hposIff : 0 < (factor * factor * planarDirectedArea a b p) *
        (factor * factor * planarDirectedArea a b q) ↔
      0 < planarDirectedArea a b p * planarDirectedArea a b q := by
    rw [hprodEq]
    constructor
    · intro h
      by_contra hc
      have : ((factor * factor) * (factor * factor)) *
          (planarDirectedArea a b p * planarDirectedArea a b q) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hcoef.le (le_of_not_gt hc)
      linarith
    · intro h
      exact mul_pos hcoef h
  have hnegIff : (factor * factor * planarDirectedArea a b p) *
        (factor * factor * planarDirectedArea a b q) < 0 ↔
      planarDirectedArea a b p * planarDirectedArea a b q < 0 := by
    rw [hprodEq]
    constructor
    · intro h
      by_contra hc
      have : 0 ≤ ((factor * factor) * (factor * factor)) *
          (planarDirectedArea a b p * planarDirectedArea a b q) :=
        mul_nonneg hcoef.le (le_of_not_gt hc)
      linarith
    · intro h
      exact mul_neg_of_pos_of_neg hcoef h
  by_cases hpositive : 0 < planarDirectedArea a b p * planarDirectedArea a b q
  · rw [if_pos (hposIff.mpr hpositive), if_pos hpositive]
  · rw [if_neg (fun hc => hpositive (hposIff.mp hc)), if_neg hpositive]
    by_cases hnegative : planarDirectedArea a b p * planarDirectedArea a b q < 0
    · rw [if_pos (hnegIff.mpr hnegative), if_pos hnegative]
    · rw [if_neg (fun hc => hnegative (hnegIff.mp hc)), if_neg hnegative]

/-! ## Exact comparison with the existing three-dimensional primitive -/

/-- The drawing-plane point embedded at exact depth zero.  This is a proof-side embedding only; it
is never written into a source record. -/
def planeLift (point : CartesianPoint2) : CartesianPoint3 :=
  { x := point.x, y := point.y, z := 0 }

/-- Four planar lifts are always exactly coplanar for the existing three-dimensional primitive. -/
private theorem rule3Coplanarity_planeLift (a b p q : CartesianPoint2) :
    CartesianPoint3.rule3Coplanarity (planeLift a) (planeLift b)
        (planeLift p) (planeLift q) = 0 := by
  simp only [CartesianPoint3.rule3Coplanarity, CartesianPoint3.displacement,
    RationalVector3.dot, RationalVector3.cross, planeLift]
  ring

/-- On planar lifts the existing three-dimensional side product is *exactly* the product of the two
planar directed areas.  This is an algebraic identity, not a transported coordinate record. -/
theorem rule3SideProduct_planeLift (a b p q : CartesianPoint2) :
    CartesianPoint3.rule3SideProduct (planeLift a) (planeLift b)
        (planeLift p) (planeLift q) =
      planarDirectedArea a b p * planarDirectedArea a b q := by
  simp only [CartesianPoint3.rule3SideProduct, CartesianPoint3.displacement,
    RationalVector3.dot, RationalVector3.cross, planeLift, planarDirectedArea]
  ring

/-- The existing three-dimensional Rule-3 classifier agrees with the planar classifier on planar
lifts.  This fixes the orientation comparison against the production primitive. -/
theorem rule3GeometryOfSpatialReferences?_planeLift (a b p q : CartesianPoint2) :
    rule3GeometryOfSpatialReferences? (planeLift a) (planeLift b)
        (planeLift p) (planeLift q) = planarDoubleBondGeometry? a b p q := by
  simp [rule3GeometryOfSpatialReferences?, planarDoubleBondGeometry?,
    rule3Coplanarity_planeLift, rule3SideProduct_planeLift]

/-! ## Closed planar witnesses -/

private def cisLeft : CartesianPoint2 := { x := 0, y := 0 }
private def cisRight : CartesianPoint2 := { x := 2, y := 0 }
private def cisUpperLeft : CartesianPoint2 := { x := 0, y := 1 }
private def cisUpperRight : CartesianPoint2 := { x := 2, y := 1 }
private def transLowerRight : CartesianPoint2 := { x := 2, y := -1 }
private def collinearLeft : CartesianPoint2 := { x := 1, y := 0 }

/-- Closed same-side witness: two references above the base give `seqcis`. -/
theorem cis_witness :
    planarDoubleBondGeometry? cisLeft cisRight cisUpperLeft cisUpperRight =
      some OfficialRule3Geometry.seqcis := by
  decide +kernel

/-- Closed opposite-side witness: one reference below the base gives `seqtrans`. -/
theorem trans_witness :
    planarDoubleBondGeometry? cisLeft cisRight cisUpperLeft transLowerRight =
      some OfficialRule3Geometry.seqtrans := by
  decide +kernel

/-- Closed collinear witness: a reference on the base is refused. -/
theorem collinear_witness :
    planarDoubleBondGeometry? cisLeft cisRight collinearLeft cisUpperRight = none := by
  decide +kernel

end TetraStereo.UniversalProof.PlanarRule3DoubleBondGeometryProofs.PlanarRule3DoubleBondGeometry
