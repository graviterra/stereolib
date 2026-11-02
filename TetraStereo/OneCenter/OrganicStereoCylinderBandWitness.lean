/-
Copyright (c) 2026 TetraStereo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TetraStereo.OneCenter.OrganicStereoEmbeddedBands
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# A concrete untwisted cylindrical band witness

The module `TetraStereo.OneCenter.OrganicStereoEmbeddedBands` introduces the structure
`Band` of an embedded ribbon band and proves all of its transport, seam, attachment and
reflection theorems *conditionally*: it never constructs a band, so inhabitation of `Band`
is not established there.  This module supplies an independent constructive witness.

The witness is the ordinary cylinder strip

`(t, s) ↦ (cos (2 * π * t), sin (2 * π * t), s)`

on the parameter square `unitInterval × unitInterval`, with the exact untwisted seam
gluing `(1, s) ~ (0, s)` reused from `SeamRel` and `SeamMode.glue`.  We prove, with no
supplied embedding, band, or injectivity hypothesis:

* the strip is continuous (`continuous_cylinderStrip`);
* the exact end seam holds (`cylinderStrip_seam`);
* equal strip images are equivalent to untwisted seam-relatedness
  (`cylinderStrip_eq_iff_seamRel`), using Mathlib's circle-periodicity theory rather than
  redoing trigonometric analysis;
* hence `cylinderBand : Band` is a genuine inhabitant with `mode = .untwisted`.

The key nondegeneracy point is that the only identifications made by the strip are the two
end edges: equality of `exp` values on the circle gives an integer period `m`, and the unit
interval forces `m ∈ {-1, 0, 1}`, i.e. equality of parameters or the two boundary
identifications at the endpoints.

A small source-indexed attachment example over the one-point index type `Fin 1` is
included at the end; it exercises `SourceAttachingCore` without requiring a certified
molecule.  No chirality, classification, knot-theoretic or chemical conclusion is drawn.
-/

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace OrganicStereoEmbeddedBands

noncomputable section

/-! ## The explicit cylinder strip map -/

/-- The explicit cylinder strip: the length coordinate `t` wraps the unit circle in the
first two coordinates with period `2 * π`, and the width coordinate `s` is the height.
This is a genuine function on the closed parameter square, not a supplied surface. -/
def cylinderStrip (x : RibbonDomain) : real3 :=
  WithLp.toLp 2 fun i : Fin 3 =>
    ![Real.cos (2 * Real.pi * (x.1 : ℝ)),
      Real.sin (2 * Real.pi * (x.1 : ℝ)),
      (x.2 : ℝ)] i

/-- First coordinate of the cylinder strip. -/
@[simp] theorem cylinderStrip_apply_zero (x : RibbonDomain) :
    cylinderStrip x 0 = Real.cos (2 * Real.pi * (x.1 : ℝ)) := by
  simp [cylinderStrip]

/-- Second coordinate of the cylinder strip. -/
@[simp] theorem cylinderStrip_apply_one (x : RibbonDomain) :
    cylinderStrip x 1 = Real.sin (2 * Real.pi * (x.1 : ℝ)) := by
  simp [cylinderStrip]

/-- Third coordinate of the cylinder strip: the height coordinate. -/
@[simp] theorem cylinderStrip_apply_two (x : RibbonDomain) :
    cylinderStrip x 2 = (x.2 : ℝ) := by
  simp [cylinderStrip]

/-- The cylinder strip is continuous.  Continuity is checked coordinatewise through the
topology of `PiLp`, which is induced by the coordinate projections. -/
theorem continuous_cylinderStrip : Continuous cylinderStrip := by
  have hcoord : Continuous (fun x : RibbonDomain => fun i : Fin 3 =>
      ![Real.cos (2 * Real.pi * (x.1 : ℝ)),
        Real.sin (2 * Real.pi * (x.1 : ℝ)),
        (x.2 : ℝ)] i) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> continuity
  have hto : Continuous (fun f : Fin 3 → ℝ => WithLp.toLp (p := 2) f) :=
    PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)
  simpa only [cylinderStrip, Function.comp_apply] using hto.comp hcoord

/-! ## The exact untwisted seam -/

/-- The cylinder strip has the exact untwisted end seam: the last edge point `(1, s)` is
identified with the first edge point `(0, s)`.  This is proved, not assumed. -/
theorem cylinderStrip_seam (s : unitInterval) :
    cylinderStrip ((1 : unitInterval), s) =
      cylinderStrip ((0 : unitInterval), SeamMode.glue SeamMode.untwisted s) := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [cylinderStrip, Real.cos_two_pi, Real.sin_two_pi]

/-! ## Equality of strip images is exactly untwisted seam relatedness -/

/-- The cylinder strip is injective modulo the exact untwisted seam relation.  If two
parameter points have the same image, then their exponentials on the unit circle agree;
Mathlib's `Circle.exp_eq_exp` yields an integer period `m`, and the two unit-interval
bounds force `m = 0`, `m = 1` or `m = -1`.  These are respectively equality of parameters,
the identification of `(1, s)` with `(0, s)`, and the symmetric identification of `(0, s)`
with `(1, s)`. -/
theorem injective_mod_seam_cylinderStrip (x y : RibbonDomain)
    (hxy : cylinderStrip x = cylinderStrip y) :
    SeamRel SeamMode.untwisted x y := by
  have hcos : Real.cos (2 * Real.pi * (x.1 : ℝ)) =
      Real.cos (2 * Real.pi * (y.1 : ℝ)) := by
    simpa only [cylinderStrip_apply_zero] using congrArg (fun v : real3 => v 0) hxy
  have hsin : Real.sin (2 * Real.pi * (x.1 : ℝ)) =
      Real.sin (2 * Real.pi * (y.1 : ℝ)) := by
    simpa only [cylinderStrip_apply_one] using congrArg (fun v : real3 => v 1) hxy
  have hheight : (x.2 : ℝ) = (y.2 : ℝ) := by
    simpa only [cylinderStrip_apply_two] using congrArg (fun v : real3 => v 2) hxy
  -- The real trigonometric equalities, pushed into the complex plane.
  have hcosC : Complex.cos (((2 * Real.pi * (x.1 : ℝ)) : ℝ) : ℂ) =
      Complex.cos (((2 * Real.pi * (y.1 : ℝ)) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_cos] using congrArg (fun r : ℝ => (r : ℂ)) hcos
  have hsinC : Complex.sin (((2 * Real.pi * (x.1 : ℝ)) : ℝ) : ℂ) =
      Complex.sin (((2 * Real.pi * (y.1 : ℝ)) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_sin] using congrArg (fun r : ℝ => (r : ℂ)) hsin
  -- Equality of the complex exponentials of the two angles.
  have hcircle : Circle.exp (2 * Real.pi * (x.1 : ℝ)) =
      Circle.exp (2 * Real.pi * (y.1 : ℝ)) := by
    apply Subtype.ext
    rw [Circle.coe_exp, Circle.coe_exp,
      Complex.exp_mul_I, Complex.exp_mul_I, hcosC, hsinC]
  -- The period `m` supplied by the circle exponential.
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hcircle
  -- Cancel the positive factor `2 * π`.
  have hlin : (x.1 : ℝ) = (y.1 : ℝ) + (m : ℝ) := by
    have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    refine mul_left_cancel₀ h2π ?_
    rw [hm]
    ring
  -- Membership of the angles in the unit interval bounds the integer period.
  have hx0 : (0 : ℝ) ≤ (x.1 : ℝ) := unitInterval.nonneg x.1
  have hx1 : (x.1 : ℝ) ≤ 1 := unitInterval.le_one x.1
  have hy0 : (0 : ℝ) ≤ (y.1 : ℝ) := unitInterval.nonneg y.1
  have hy1 : (y.1 : ℝ) ≤ 1 := unitInterval.le_one y.1
  have hmlo : (-1 : ℤ) ≤ m := by
    have h : (-1 : ℝ) ≤ (m : ℝ) := by linarith
    exact_mod_cast h
  have hmhi : m ≤ 1 := by
    have h : (m : ℝ) ≤ 1 := by linarith
    exact_mod_cast h
  have hmcases : m = 0 ∨ m = 1 ∨ m = -1 := by omega
  rcases hmcases with rfl | rfl | rfl
  · -- Period zero: the parameters are equal.
    norm_num at hlin
    have hxeq : (x.1 : ℝ) = (y.1 : ℝ) := by linarith
    exact Or.inl (Prod.ext (Subtype.ext hxeq) (Subtype.ext hheight))
  · -- Period one: `x` is on the last edge and `y` on the first edge at the same width.
    norm_num at hlin
    have hxeq : (x.1 : ℝ) = 1 := by linarith
    have hyeq : (y.1 : ℝ) = 0 := by linarith
    refine Or.inr (Or.inl ⟨Subtype.ext hxeq, Subtype.ext hyeq, ?_⟩)
    simp only [SeamMode.glue_untwisted]
    exact Subtype.ext hheight.symm
  · -- Period minus one: `y` is on the last edge and `x` on the first edge.
    norm_num at hlin
    have hxeq : (x.1 : ℝ) = 0 := by linarith
    have hyeq : (y.1 : ℝ) = 1 := by linarith
    refine Or.inr (Or.inr ⟨Subtype.ext hyeq, Subtype.ext hxeq, ?_⟩)
    simp only [SeamMode.glue_untwisted]
    exact Subtype.ext hheight

/-- Equal cylinder strip images exactly when the parameter points are related by the
untwisted seam relation.  The reverse direction is the exact seam gluing; the forward
direction is the modulo-seam injectivity proved above. -/
theorem cylinderStrip_eq_iff_seamRel (x y : RibbonDomain) :
    cylinderStrip x = cylinderStrip y ↔
      SeamRel SeamMode.untwisted x y := by
  constructor
  · exact injective_mod_seam_cylinderStrip x y
  · intro h
    rcases h with rfl | ⟨hx1, hy1, hy2⟩ | ⟨hy1, hx1, hx2⟩
    · rfl
    · have hx : x = ((1 : unitInterval), x.2) := Prod.ext hx1 rfl
      have hy : y =
          ((0 : unitInterval), SeamMode.glue SeamMode.untwisted x.2) := Prod.ext hy1 hy2
      rw [hx, hy, SeamMode.glue_untwisted]
      exact cylinderStrip_seam x.2
    · have hx : x =
          ((0 : unitInterval), SeamMode.glue SeamMode.untwisted y.2) := Prod.ext hx1 hx2
      have hy : y = ((1 : unitInterval), y.2) := Prod.ext hy1 rfl
      rw [hx, hy, SeamMode.glue_untwisted]
      exact (cylinderStrip_seam y.2).symm

/-! ## The concrete untwisted band -/

/-- The concrete untwisted cylindrical band.  Every field is proved: the strip is the
explicit cylinder map, continuity is `continuous_cylinderStrip`, the seam is
`cylinderStrip_seam`, and modulo-seam injectivity is `injective_mod_seam_cylinderStrip`.
No band, embedding, or injectivity hypothesis is supplied. -/
def cylinderBand : Band where
  mode := SeamMode.untwisted
  strip := cylinderStrip
  continuous_strip := continuous_cylinderStrip
  seam := cylinderStrip_seam
  injective_mod_seam := injective_mod_seam_cylinderStrip

/-- The concrete band has the untwisted seam mode. -/
@[simp] theorem cylinderBand_mode : cylinderBand.mode = SeamMode.untwisted := rfl

/-- The strip map of the concrete band is the explicit cylinder strip. -/
@[simp] theorem cylinderBand_strip : cylinderBand.strip = cylinderStrip := rfl

/-- The concrete band realizes the requested equality criterion: equal strip images are
exactly untwisted seam-related parameter points. -/
theorem cylinderBand_strip_eq_iff_seamRel (x y : RibbonDomain) :
    cylinderBand.strip x = cylinderBand.strip y ↔
      SeamRel SeamMode.untwisted x y :=
  cylinderStrip_eq_iff_seamRel x y

/-- `Band` is inhabited in the untwisted mode, unconditionally. -/
theorem exists_untwisted_band : ∃ G : Band, G.mode = SeamMode.untwisted :=
  ⟨cylinderBand, rfl⟩

/-! ## A small source-indexed attachment example -/

/-- A one-point source-indexed attachment to the concrete cylinder band.  The source
position is exactly the strip image of the attached parameter point, so the attachment
carries positional content rather than a decorative payload.  This example is indexed by
`Fin 1`; attaching to a certified molecular source would additionally require an actual
`CertifiedAuthoritativeChemicalInput`, which is deliberately not constructed here. -/
def cylinderSampleAttachment : SourceAttachingCore cylinderBand (Fin 1) where
  sourcePosition := fun _ => cylinderStrip ((0 : unitInterval), (0 : unitInterval))
  attachment := fun _ => ((0 : unitInterval), (0 : unitInterval))
  agreement := fun _ => rfl

/-- The sample attachment indeed lands on its supplied source position. -/
@[simp] theorem cylinderSampleAttachment_agreement (i : Fin 1) :
    cylinderBand.strip (cylinderSampleAttachment.attachment i) =
      cylinderSampleAttachment.sourcePosition i :=
  cylinderSampleAttachment.agreement i

end

end OrganicStereoEmbeddedBands
end OneCenter
end TetraStereo
