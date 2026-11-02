/-
Copyright (c) 2026 TetraStereo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TetraStereo.OneCenter.OrganicStereoEmbeddedBands
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# A concrete twisted band: the standard Möbius strip

`OrganicStereoEmbeddedBands` defines the structure `Band` (seam mode, continuous strip map,
exact seam gluing, and injectivity modulo the seam relation) but deliberately constructs no
inhabitant.  This module supplies a genuine one.

The strip is the usual parametrised Möbius band of radius `2` and width `1`.  If
`t : [0,1]` runs along the band and `s : [0,1]` runs across it, put
`w = s - 1/2 ∈ [-1/2, 1/2]` and

```
strip (t, s) = ((2 + w cos(π t)) cos(2 π t),
                (2 + w cos(π t)) sin(2 π t),
                w sin(π t)).
```

The radial factor `2 + w cos(π t)` lies in `[3/2, 5/2]`, so it is strictly positive.  Hence the
polar angle `2 π t` is recovered from the first two coordinates.  On the open part of the
parameter square (more precisely, whenever twice the angle is not an endpoint of `[0, 2π]`)
equal images force `t` to agree, and the radius and third coordinate then force `w`, hence `s`,
to agree.  When the angles are the two endpoints, the radius forces `w` to change sign, which is
exactly the twisted seam identification `(1, s) ~ (0, 1 - s)`.

Everything is proved from the explicit formula: no injectivity hypothesis, no existence of a
band, and no extra axioms are assumed.
-/

set_option autoImplicit false

-- The remaining proof scripts use explicit, finite simp lemma sets; some of the listed
-- lemmas are redundant in particular coordinate branches.  Those are style-only linter
-- diagnostics (the arguments are harmless and the proofs are unchanged), so they are
-- disabled here rather than making the simp sets branch-dependent and fragile.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace TetraStereo
namespace OneCenter
namespace OrganicStereoEmbeddedBands

noncomputable section

/-! ## The explicit strip map -/

/-- The width coordinate `w = s - 1/2`, taking values in `[-1/2, 1/2]`. -/
def mobiusWidth (s : unitInterval) : ℝ := (s : ℝ) - 1 / 2

/-- The radial factor `2 + w cos(π t)` of the Möbius strip. -/
def mobiusRadius (x : RibbonDomain) : ℝ :=
  2 + mobiusWidth x.2 * Real.cos (Real.pi * (x.1 : ℝ))

/-- The standard Möbius strip of radius `2` and width `1`, parametrised on the closed square.
The first parameter runs along the band and the second across it. -/
def mobiusStrip (x : RibbonDomain) : real3 :=
  WithLp.toLp 2
    ![mobiusRadius x * Real.cos (2 * Real.pi * (x.1 : ℝ)),
      mobiusRadius x * Real.sin (2 * Real.pi * (x.1 : ℝ)),
      mobiusWidth x.2 * Real.sin (Real.pi * (x.1 : ℝ))]

/-- The first coordinate of the strip map. -/
theorem mobiusStrip_zero (x : RibbonDomain) :
    (mobiusStrip x).ofLp 0 = mobiusRadius x * Real.cos (2 * Real.pi * (x.1 : ℝ)) := rfl

/-- The second coordinate of the strip map. -/
theorem mobiusStrip_one (x : RibbonDomain) :
    (mobiusStrip x).ofLp 1 = mobiusRadius x * Real.sin (2 * Real.pi * (x.1 : ℝ)) := rfl

/-- The third coordinate of the strip map. -/
theorem mobiusStrip_two (x : RibbonDomain) :
    (mobiusStrip x).ofLp 2 = mobiusWidth x.2 * Real.sin (Real.pi * (x.1 : ℝ)) := rfl

/-! ## Elementary bounds -/

/-- The width coordinate is bounded by `1/2` in absolute value. -/
theorem abs_mobiusWidth_le (s : unitInterval) : |mobiusWidth s| ≤ 1 / 2 := by
  rw [abs_le]
  constructor <;> unfold mobiusWidth <;> linarith [s.2.1, s.2.2]

/-- The radial factor is strictly positive: it is at least `3/2`.  Positivity is what makes
the polar angle recoverable from the first two coordinates. -/
theorem mobiusRadius_pos (x : RibbonDomain) : 0 < mobiusRadius x := by
  have hw : |mobiusWidth x.2| ≤ 1 / 2 := abs_mobiusWidth_le x.2
  have hc : |Real.cos (Real.pi * (x.1 : ℝ))| ≤ 1 := Real.abs_cos_le_one _
  have hprod : |mobiusWidth x.2 * Real.cos (Real.pi * (x.1 : ℝ))| ≤ 1 / 2 := by
    rw [abs_mul]
    calc |mobiusWidth x.2| * |Real.cos (Real.pi * (x.1 : ℝ))|
        ≤ (1 / 2) * 1 := mul_le_mul hw hc (abs_nonneg _) (by linarith)
      _ = 1 / 2 := by ring
  have hlow : -(1 / 2) ≤ mobiusWidth x.2 * Real.cos (Real.pi * (x.1 : ℝ)) :=
    (abs_le.mp hprod).1
  unfold mobiusRadius
  linarith

/-! ## Continuity -/

theorem continuous_mobiusWidth : Continuous mobiusWidth := by
  unfold mobiusWidth
  exact continuous_subtype_val.sub continuous_const

theorem continuous_mobiusRadius : Continuous mobiusRadius := by
  unfold mobiusRadius
  exact continuous_const.add
    ((continuous_mobiusWidth.comp continuous_snd).mul
      (Real.continuous_cos.comp
        (continuous_const.mul (continuous_subtype_val.comp continuous_fst))))

theorem continuous_mobiusStrip : Continuous mobiusStrip := by
  have h : Continuous (fun x : RibbonDomain => (mobiusStrip x).ofLp) := by
    apply continuous_pi
    intro i
    fin_cases i
    · simpa only [mobiusStrip_zero] using
        continuous_mobiusRadius.mul
          (Real.continuous_cos.comp
            (continuous_const.mul (continuous_subtype_val.comp continuous_fst)))
    · simpa only [mobiusStrip_one] using
        continuous_mobiusRadius.mul
          (Real.continuous_sin.comp
            (continuous_const.mul (continuous_subtype_val.comp continuous_fst)))
    · simpa only [mobiusStrip_two] using
        (continuous_mobiusWidth.comp continuous_snd).mul
          (Real.continuous_sin.comp
            (continuous_const.mul (continuous_subtype_val.comp continuous_fst)))
  exact continuous_induced_rng.2 h

/-! ## The seam gluing -/

theorem mobiusStrip_seam_zero (s : unitInterval) :
    (mobiusStrip ((1 : unitInterval), s)).ofLp 0 =
      (mobiusStrip ((0 : unitInterval), unitInterval.symm s)).ofLp 0 := by
  rw [mobiusStrip_zero, mobiusStrip_zero]
  simp only [mobiusRadius, mobiusWidth, Set.Icc.coe_one, Set.Icc.coe_zero,
    unitInterval.coe_symm_eq, mul_one, mul_zero, Real.cos_pi, Real.sin_pi,
    Real.cos_zero, Real.sin_zero, Real.cos_two_pi, Real.sin_two_pi] <;> ring

theorem mobiusStrip_seam_one (s : unitInterval) :
    (mobiusStrip ((1 : unitInterval), s)).ofLp 1 =
      (mobiusStrip ((0 : unitInterval), unitInterval.symm s)).ofLp 1 := by
  rw [mobiusStrip_one, mobiusStrip_one]
  simp only [mobiusRadius, mobiusWidth, Set.Icc.coe_one, Set.Icc.coe_zero,
    unitInterval.coe_symm_eq, mul_one, mul_zero, Real.cos_pi, Real.sin_pi,
    Real.cos_zero, Real.sin_zero, Real.cos_two_pi, Real.sin_two_pi] <;> ring

theorem mobiusStrip_seam_two (s : unitInterval) :
    (mobiusStrip ((1 : unitInterval), s)).ofLp 2 =
      (mobiusStrip ((0 : unitInterval), unitInterval.symm s)).ofLp 2 := by
  rw [mobiusStrip_two, mobiusStrip_two]
  simp only [mobiusRadius, mobiusWidth, Set.Icc.coe_one, Set.Icc.coe_zero,
    unitInterval.coe_symm_eq, mul_one, mul_zero, Real.cos_pi, Real.sin_pi,
    Real.cos_zero, Real.sin_zero, Real.cos_two_pi, Real.sin_two_pi] <;> ring

/-- The explicit half-twist seam: the last edge `(1, s)` is the first edge `(0, 1 - s)`. -/
theorem mobiusStrip_seam (s : unitInterval) :
    mobiusStrip ((1 : unitInterval), s) =
      mobiusStrip ((0 : unitInterval), unitInterval.symm s) := by
  apply WithLp.ofLp_injective 2
  funext i
  fin_cases i
  · exact mobiusStrip_seam_zero s
  · exact mobiusStrip_seam_one s
  · exact mobiusStrip_seam_two s

/-! ## Recovery of the parameters -/

/-- If two values have the same cosine and sine, they are equal.  This is the elementary
step that turns the common radius into equality of the width coordinates. -/
theorem width_eq_of_cos_sin_eq {w₁ w₂ a : ℝ}
    (hcos : w₁ * Real.cos a = w₂ * Real.cos a)
    (hsin : w₁ * Real.sin a = w₂ * Real.sin a) : w₁ = w₂ := by
  by_contra hne
  have hC0 : (w₁ - w₂) * Real.cos a = 0 := by
    have h : w₁ * Real.cos a - w₂ * Real.cos a = 0 := sub_eq_zero.mpr hcos
    rwa [← sub_mul] at h
  have hS0 : (w₁ - w₂) * Real.sin a = 0 := by
    have h : w₁ * Real.sin a - w₂ * Real.sin a = 0 := sub_eq_zero.mpr hsin
    rwa [← sub_mul] at h
  have hC : Real.cos a = 0 := by
    rcases mul_eq_zero.mp hC0 with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact h
  have hS : Real.sin a = 0 := by
    rcases mul_eq_zero.mp hS0 with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact h
  have hsq : Real.sin a ^ 2 + Real.cos a ^ 2 = 1 := Real.sin_sq_add_cos_sq a
  rw [hS, hC] at hsq
  have hzero : (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2 = 0 := by ring
  rw [hzero] at hsq
  exact zero_ne_one hsq

set_option maxHeartbeats 1000000 in
/-- The explicit Möbius strip is injective modulo the twisted seam relation. -/
theorem injective_mod_seam_mobiusStrip :
    ∀ x y : RibbonDomain, mobiusStrip x = mobiusStrip y →
      SeamRel SeamMode.twisted x y := by
  intro x y hxy
  have hof : (mobiusStrip x).ofLp = (mobiusStrip y).ofLp :=
    congrArg (fun v : real3 => v.ofLp) hxy
  have h0 := congrFun hof 0
  rw [mobiusStrip_zero, mobiusStrip_zero] at h0
  have h1 := congrFun hof 1
  rw [mobiusStrip_one, mobiusStrip_one] at h1
  have h2 := congrFun hof 2
  rw [mobiusStrip_two, mobiusStrip_two] at h2
  -- The radial factor is recovered from the first two coordinates.
  have hrad_sq : mobiusRadius x ^ 2 = mobiusRadius y ^ 2 := by
    have hs : (mobiusRadius x * Real.cos (2 * Real.pi * (x.1 : ℝ))) ^ 2 +
        (mobiusRadius x * Real.sin (2 * Real.pi * (x.1 : ℝ))) ^ 2 =
        (mobiusRadius y * Real.cos (2 * Real.pi * (y.1 : ℝ))) ^ 2 +
        (mobiusRadius y * Real.sin (2 * Real.pi * (y.1 : ℝ))) ^ 2 := by
      rw [h0, h1]
    have hx := Real.cos_sq_add_sin_sq (2 * Real.pi * (x.1 : ℝ))
    have hy := Real.cos_sq_add_sin_sq (2 * Real.pi * (y.1 : ℝ))
    have hx' : (mobiusRadius x * Real.cos (2 * Real.pi * (x.1 : ℝ))) ^ 2 +
        (mobiusRadius x * Real.sin (2 * Real.pi * (x.1 : ℝ))) ^ 2 =
        mobiusRadius x ^ 2 := by
      calc (mobiusRadius x * Real.cos (2 * Real.pi * (x.1 : ℝ))) ^ 2 +
          (mobiusRadius x * Real.sin (2 * Real.pi * (x.1 : ℝ))) ^ 2 =
          mobiusRadius x ^ 2 *
            (Real.cos (2 * Real.pi * (x.1 : ℝ)) ^ 2 +
              Real.sin (2 * Real.pi * (x.1 : ℝ)) ^ 2) := by ring
        _ = mobiusRadius x ^ 2 := by rw [hx, mul_one]
    have hy' : (mobiusRadius y * Real.cos (2 * Real.pi * (y.1 : ℝ))) ^ 2 +
        (mobiusRadius y * Real.sin (2 * Real.pi * (y.1 : ℝ))) ^ 2 =
        mobiusRadius y ^ 2 := by
      calc (mobiusRadius y * Real.cos (2 * Real.pi * (y.1 : ℝ))) ^ 2 +
          (mobiusRadius y * Real.sin (2 * Real.pi * (y.1 : ℝ))) ^ 2 =
          mobiusRadius y ^ 2 *
            (Real.cos (2 * Real.pi * (y.1 : ℝ)) ^ 2 +
              Real.sin (2 * Real.pi * (y.1 : ℝ)) ^ 2) := by ring
        _ = mobiusRadius y ^ 2 := by rw [hy, mul_one]
    rw [← hx', ← hy']
    exact hs
  have hrad : mobiusRadius x = mobiusRadius y := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hrad_sq with h | h
    · exact h
    · have hx := mobiusRadius_pos x
      have hy := mobiusRadius_pos y
      linarith
  have hcos : Real.cos (2 * Real.pi * (x.1 : ℝ)) =
      Real.cos (2 * Real.pi * (y.1 : ℝ)) := by
    rw [hrad] at h0
    exact mul_left_cancel₀ (ne_of_gt (mobiusRadius_pos y)) h0
  have hsin : Real.sin (2 * Real.pi * (x.1 : ℝ)) =
      Real.sin (2 * Real.pi * (y.1 : ℝ)) := by
    rw [hrad] at h1
    exact mul_left_cancel₀ (ne_of_gt (mobiusRadius_pos y)) h1
  -- Equal cosine and sine of twice the angle, hence the angle difference is an integral
  -- multiple of `2π`.
  have hcos_sub :
      Real.cos (2 * Real.pi * (x.1 : ℝ) - 2 * Real.pi * (y.1 : ℝ)) = 1 := by
    rw [Real.cos_sub, hcos, hsin]
    have h := Real.cos_sq_add_sin_sq (2 * Real.pi * (y.1 : ℝ))
    calc Real.cos (2 * Real.pi * (y.1 : ℝ)) * Real.cos (2 * Real.pi * (y.1 : ℝ)) +
          Real.sin (2 * Real.pi * (y.1 : ℝ)) * Real.sin (2 * Real.pi * (y.1 : ℝ))
        = Real.cos (2 * Real.pi * (y.1 : ℝ)) ^ 2 +
          Real.sin (2 * Real.pi * (y.1 : ℝ)) ^ 2 := by ring
      _ = 1 := h
  -- Both doubled angles lie in `[0, 2π]`.
  have hpi_nonneg : (0 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_pos]
  have htheta_x_ge : 0 ≤ 2 * Real.pi * (x.1 : ℝ) :=
    mul_nonneg hpi_nonneg x.1.2.1
  have htheta_x_le : 2 * Real.pi * (x.1 : ℝ) ≤ 2 * Real.pi := by
    calc 2 * Real.pi * (x.1 : ℝ) ≤ 2 * Real.pi * 1 :=
          mul_le_mul_of_nonneg_left x.1.2.2 hpi_nonneg
      _ = 2 * Real.pi := by ring
  have htheta_y_ge : 0 ≤ 2 * Real.pi * (y.1 : ℝ) :=
    mul_nonneg hpi_nonneg y.1.2.1
  have htheta_y_le : 2 * Real.pi * (y.1 : ℝ) ≤ 2 * Real.pi := by
    calc 2 * Real.pi * (y.1 : ℝ) ≤ 2 * Real.pi * 1 :=
          mul_le_mul_of_nonneg_left y.1.2.2 hpi_nonneg
      _ = 2 * Real.pi := by ring
  have hd_le :
      2 * Real.pi * (x.1 : ℝ) - 2 * Real.pi * (y.1 : ℝ) ≤ 2 * Real.pi := by
    linarith [htheta_x_le, htheta_y_ge]
  have hd_ge :
      -(2 * Real.pi) ≤ 2 * Real.pi * (x.1 : ℝ) - 2 * Real.pi * (y.1 : ℝ) := by
    linarith [htheta_x_ge, htheta_y_le]
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 hcos_sub
  have h2pi : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  have hn_le : (n : ℝ) ≤ 1 := by
    have h : (n : ℝ) * (2 * Real.pi) ≤ 1 * (2 * Real.pi) := by
      rw [hn]
      simpa using hd_le
    exact le_of_mul_le_mul_right h h2pi
  have hn_ge : -1 ≤ (n : ℝ) := by
    have h : (-1 : ℝ) * (2 * Real.pi) ≤ (n : ℝ) * (2 * Real.pi) := by
      rw [hn]
      simpa using hd_ge
    exact le_of_mul_le_mul_right h h2pi
  have hn_int_le : n ≤ 1 := by exact_mod_cast hn_le
  have hn_int_ge : -1 ≤ n := by exact_mod_cast hn_ge
  interval_cases n
  · -- Endpoint case: `t = 0` and `t' = 1`; the radius forces `(0, s) ~ (1, 1 - s)`.
    have hdif : (x.1 : ℝ) - (y.1 : ℝ) = -1 := by
      have hn' : -(2 * Real.pi) =
          2 * Real.pi * (x.1 : ℝ) - 2 * Real.pi * (y.1 : ℝ) := by
        simpa only [Int.cast_neg, Int.cast_one, neg_mul, one_mul] using hn
      have hEq : 2 * Real.pi * ((x.1 : ℝ) - (y.1 : ℝ)) = 2 * Real.pi * (-1) := by
        linarith
      exact mul_left_cancel₀ (ne_of_gt h2pi) hEq
    have htx0 : (x.1 : ℝ) = 0 := by
      linarith [x.1.2.1, y.1.2.2]
    have hty1 : (y.1 : ℝ) = 1 := by
      linarith [x.1.2.1, y.1.2.2]
    have hwx : mobiusWidth x.2 = -mobiusWidth y.2 := by
      have hcosx : Real.cos (Real.pi * (x.1 : ℝ)) = 1 := by
        rw [htx0, mul_zero, Real.cos_zero]
      have hcosy : Real.cos (Real.pi * (y.1 : ℝ)) = -1 := by
        rw [hty1, mul_one, Real.cos_pi]
      have hrr := hrad
      unfold mobiusRadius at hrr
      rw [hcosx, hcosy] at hrr
      linarith
    have hx2 : (x.2 : ℝ) = 1 - (y.2 : ℝ) := by
      have := hwx
      unfold mobiusWidth at this
      linarith
    have hx1 : x.1 = (0 : unitInterval) := Subtype.ext htx0
    have hy1 : y.1 = (1 : unitInterval) := Subtype.ext hty1
    have hx2' : x.2 = unitInterval.symm y.2 := by
      apply Subtype.ext
      rw [unitInterval.coe_symm_eq]
      exact hx2
    exact Or.inr (Or.inr ⟨hy1, hx1, hx2'⟩)
  · -- Interior case: the angles agree; the radius and third coordinate fix the width.
    have hdif : (x.1 : ℝ) = (y.1 : ℝ) := by
      have hn' : (0 : ℝ) =
          2 * Real.pi * (x.1 : ℝ) - 2 * Real.pi * (y.1 : ℝ) := by
        simpa only [Int.cast_zero, zero_mul] using hn
      have hEq : 2 * Real.pi * ((x.1 : ℝ) - (y.1 : ℝ)) = 2 * Real.pi * 0 := by
        linarith
      have hcancel := mul_left_cancel₀ (ne_of_gt h2pi) hEq
      linarith
    have hca : mobiusWidth x.2 * Real.cos (Real.pi * (x.1 : ℝ)) =
        mobiusWidth y.2 * Real.cos (Real.pi * (x.1 : ℝ)) := by
      have hrr := hrad
      unfold mobiusRadius at hrr
      rw [← hdif] at hrr
      linarith
    have hsa : mobiusWidth x.2 * Real.sin (Real.pi * (x.1 : ℝ)) =
        mobiusWidth y.2 * Real.sin (Real.pi * (x.1 : ℝ)) := by
      have hss := h2
      rw [← hdif] at hss
      exact hss
    have hw : mobiusWidth x.2 = mobiusWidth y.2 :=
      width_eq_of_cos_sin_eq hca hsa
    have hwreal : (x.2 : ℝ) = (y.2 : ℝ) := by
      have := hw
      unfold mobiusWidth at this
      linarith
    exact Or.inl (Prod.ext (Subtype.ext hdif) (Subtype.ext hwreal))
  · -- Endpoint case: `t = 1` and `t' = 0`; the radius forces `(1, s) ~ (0, 1 - s)`.
    have hdif : (x.1 : ℝ) - (y.1 : ℝ) = 1 := by
      have hn' : (1 : ℝ) * (2 * Real.pi) =
          2 * Real.pi * (x.1 : ℝ) - 2 * Real.pi * (y.1 : ℝ) := by
        simpa only [Int.cast_one, one_mul] using hn
      have hEq : 2 * Real.pi * ((x.1 : ℝ) - (y.1 : ℝ)) = 2 * Real.pi * 1 := by
        linarith
      exact mul_left_cancel₀ (ne_of_gt h2pi) hEq
    have htx1 : (x.1 : ℝ) = 1 := by
      linarith [x.1.2.2, y.1.2.1]
    have hty0 : (y.1 : ℝ) = 0 := by
      linarith [x.1.2.2, y.1.2.1]
    have hwx : mobiusWidth x.2 = -mobiusWidth y.2 := by
      have hcosx : Real.cos (Real.pi * (x.1 : ℝ)) = -1 := by
        rw [htx1, mul_one, Real.cos_pi]
      have hcosy : Real.cos (Real.pi * (y.1 : ℝ)) = 1 := by
        rw [hty0, mul_zero, Real.cos_zero]
      have hrr := hrad
      unfold mobiusRadius at hrr
      rw [hcosx, hcosy] at hrr
      linarith
    have hy2 : (y.2 : ℝ) = 1 - (x.2 : ℝ) := by
      have := hwx
      unfold mobiusWidth at this
      linarith
    have hx1 : x.1 = (1 : unitInterval) := Subtype.ext htx1
    have hy1 : y.1 = (0 : unitInterval) := Subtype.ext hty0
    have hy2' : y.2 = unitInterval.symm x.2 := by
      apply Subtype.ext
      rw [unitInterval.coe_symm_eq]
      exact hy2
    exact Or.inr (Or.inl ⟨hx1, hy1, hy2'⟩)

/-! ## The concrete twisted band -/

/-- The standard Möbius strip as a `Band`: mode `twisted`, the explicit strip map above,
continuity, the half-twist seam, and injectivity modulo that seam. -/
def mobiusBand : Band where
  mode := SeamMode.twisted
  strip := mobiusStrip
  continuous_strip := continuous_mobiusStrip
  seam := mobiusStrip_seam
  injective_mod_seam := injective_mod_seam_mobiusStrip

@[simp] theorem mobiusBand_mode : mobiusBand.mode = SeamMode.twisted := rfl

@[simp] theorem mobiusBand_strip (x : RibbonDomain) :
    mobiusBand.strip x = mobiusStrip x := rfl

/-- A concrete twisted band exists.  This is a genuine inhabitant: every field of `Band` was
proved from the explicit formula, with no injectivity or existence hypothesis. -/
theorem exists_twisted_band : ∃ G : Band, G.mode = SeamMode.twisted :=
  ⟨mobiusBand, rfl⟩

/-- The type of twisted bands is inhabited. -/
theorem twisted_band_nonempty : Nonempty { G : Band // G.mode = SeamMode.twisted } :=
  ⟨⟨mobiusBand, rfl⟩⟩

/-- The seam relation of the concrete band is exactly the twisted relation, restated. -/
theorem mobiusBand_strip_eq_iff {x y : RibbonDomain} :
    mobiusBand.strip x = mobiusBand.strip y ↔ SeamRel SeamMode.twisted x y :=
  Band.strip_eq_iff_seamRel mobiusBand x y

/-! ## A small source partial attachment across the seam -/

/-- A two-entry source attachment whose parameter points `(1, 0)` and `(0, 1)` are the two
sides of the twist seam.  Both entries record the same real position, as required by the
twisted gluing. -/
def mobiusSeamAttachment : SourceAttachingCore mobiusBand (Fin 2) where
  sourcePosition :=
    ![mobiusStrip ((1 : unitInterval), (0 : unitInterval)),
      mobiusStrip ((0 : unitInterval), (1 : unitInterval))]
  attachment :=
    ![((1 : unitInterval), (0 : unitInterval)),
      ((0 : unitInterval), (1 : unitInterval))]
  agreement := by
    intro i
    fin_cases i <;> rfl

/-- The two parameter points of the attachment are related by the twisted seam. -/
theorem mobiusSeamAttachment_parameters_seamRel :
    SeamRel SeamMode.twisted
      ((1 : unitInterval), (0 : unitInterval))
      ((0 : unitInterval), (1 : unitInterval)) := by
  simpa using seamRel_twisted_edges (0 : unitInterval)

/-- The two attached source positions coincide, as they must for seam-related parameters. -/
theorem mobiusSeamAttachment_positions_eq :
    mobiusSeamAttachment.sourcePosition 0 = mobiusSeamAttachment.sourcePosition 1 := by
  simpa [mobiusSeamAttachment] using mobiusStrip_seam (0 : unitInterval)

end

end OrganicStereoEmbeddedBands
end OneCenter
end TetraStereo
