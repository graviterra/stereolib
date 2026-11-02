import TetraStereo.OneCenter.OrganicStereoEmbeddedBondPaths
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Geometric separation of straight segments on the real moment curve in `ℝ³`

This module isolates the purely geometric core needed to place the vertices of an arbitrary
finite loopless multigraph on the real moment curve `t ↦ (t, t², t³)` and to draw every edge as
the straight segment between its endpoint positions.

The central fact is *segment separation*: the straight segments joining two different unordered
pairs of distinct moment-curve samples meet only in a common endpoint.  Equivalently, two chords
of the moment curve with distinct unordered endpoint pairs are disjoint unless they share an
endpoint, and in that case the only common point is the shared endpoint.  The theorem
`segmentPoint_eq_iff_endpointCollision` is the exact parameterized statement: equality of a point
`segmentPoint x y s` on the `x`–`y` chord with a point `segmentPoint u v t` on the `u`–`v` chord,
for distinct sample values `x ≠ y`, `u ≠ v` and distinct unordered endpoint pairs, forces
`s` and `t` to be endpoints (`0` or `1`) and identifies the matching endpoint labels.

The proof uses only elementary affine algebra.  Four distinct moment-curve samples are affinely
independent in `ℝ³`, and three distinct samples are affinely independent; these facts are proved
directly from the Vandermonde matrix lemma
`Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero`.  The public theorem
`momentCurve_affineIndependent_finset` records the consequence for *every* finite set of at most
four distinct real samples, and explicit two-, three- and four-point corollaries are provided.

## Scope and boundaries

This is a self-contained geometric separation result.  It makes no claim about chemical
realizability, molecular bonds, knot or link invariants, excluded volume, or the existence of an
embedding of any particular graph.  The companion graph-layer construction is responsible for
turning these separation laws into a global embedding of an arbitrary finite loopless multigraph.
Nothing here is assumed: all statements are proved in the kernel from Mathlib and the repository's
existing `EmbeddedReal3` type.

## Main results

* `momentCurve_injective` : the moment curve is injective;
* `momentCurve_affineIndependent_fin` and `momentCurve_affineIndependent_finset` : every set of at
  most four distinct samples is affinely independent;
* `momentCurve_affineIndependent_pair`, `..._triple`, `..._quadruple` : the 2-, 3- and 4-point
  cases;
* `segmentPoint_zero`, `segmentPoint_one` : endpoint values;
* `segmentPoint_eq_iff_same_pair` : for a chord with distinct endpoints, the affine parameter is
  injective;
* `segmentPoint_swap_eq_iff` : the reversal identification `s + t = 1` for the same unordered
  endpoint pair;
* `segmentPoint_eq_momentCurve_iff` : a chord meets the vertex set of the moment curve only in its
  own two endpoints (so its relative interior contains no moment-curve sample);
* `segmentPoint_eq_iff_endpointCollision` : the exact segment-collision theorem for distinct
  unordered endpoint pairs;
* `segmentPoint_ne_of_disjoint_endpoints` : the disjoint-endpoint corollary.
-/

namespace TetraStereo.OneCenter
namespace OrganicStereoMomentCurveSeparation

open scoped Convex unitInterval

noncomputable section

/-! ## The moment curve -/

/-- The real moment curve `t ↦ (t, t², t³)` in real three-space. -/
def momentCurve (t : ℝ) : EmbeddedReal3 :=
  !₂[t, t ^ 2, t ^ 3]

/-- Coordinate formula for the moment curve: coordinate `i` is `t ^ (i + 1)`. -/
@[simp] theorem momentCurve_apply_fin (t : ℝ) (i : Fin 3) :
    momentCurve t i = t ^ ((i : ℕ) + 1) := by
  fin_cases i <;> simp [momentCurve]

/-- The moment curve is injective; the first coordinate already recovers the parameter. -/
theorem momentCurve_injective : Function.Injective momentCurve := by
  intro x y h
  have hx := congrArg (fun z : EmbeddedReal3 => z (0 : Fin 3)) h
  simpa using hx

/-- Two moment-curve samples coincide exactly when their parameters coincide. -/
theorem momentCurve_eq_iff {x y : ℝ} : momentCurve x = momentCurve y ↔ x = y := by
  constructor
  · intro h
    exact momentCurve_injective h
  · intro h
    rw [h]

/-- The coordinate projection `EmbeddedReal3 → ℝ` onto one coordinate, as a linear map. -/
def coord (j : Fin 3) : EmbeddedReal3 →ₗ[ℝ] ℝ where
  toFun z := z j
  map_add' a b := by simp
  map_smul' c a := by simp

@[simp] theorem coord_apply (j : Fin 3) (z : EmbeddedReal3) : coord j z = z j := rfl

/-! ## Affine independence of at most four moment-curve samples -/

/-- **Affine independence of at most four distinct moment-curve samples.**  If `t : Fin n → ℝ` is
injective and `n ≤ 4`, then the points `momentCurve (t i)` are affinely independent.

The proof is the Vandermonde argument.  An affine dependence with weights `w` gives the four
moment equations `∑ i, w i * t i ^ k = 0` for `k = 0, 1, 2, 3` (the case `k = 0` is the vanishing
of the weight sum and the other cases are the three coordinates).  Since `n ≤ 4`, the Vandermonde
matrix on the `n` distinct nodes is invertible, so all weights vanish. -/
theorem momentCurve_affineIndependent_fin {n : ℕ} (hn : n ≤ 4) {t : Fin n → ℝ}
    (ht : Function.Injective t) :
    AffineIndependent ℝ (fun i : Fin n => momentCurve (t i)) := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw0 hwv
  -- Move the weighted sum to the origin-based `weightedVSubOfPoint`.
  have hsum : ∑ i : Fin n, w i • (momentCurve (t i) -ᵥ (0 : EmbeddedReal3)) = 0 := by
    rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero (s := Finset.univ) w
      (fun i : Fin n => momentCurve (t i)) hw0 (0 : EmbeddedReal3)] at hwv
    simpa using hwv
  -- The three coordinate equations are the power sums of degrees `1`, `2`, `3`.
  have hcoord : ∀ j : Fin 3, (∑ i : Fin n, w i * t i ^ ((j : ℕ) + 1)) = 0 := by
    intro j
    have h := congrArg (coord j) hsum
    simp only [map_sum, map_smul, coord_apply, vsub_eq_sub,
      PiLp.zero_apply, sub_zero, smul_eq_mul, momentCurve_apply_fin] at h
    exact h
  -- Package all four power sums, including degree `0` from the sum of the weights.
  have hpow : ∀ k : Fin 4, (∑ i : Fin n, w i * t i ^ (k : ℕ)) = 0 := by
    intro k
    fin_cases k
    · simpa using hw0
    · simpa using hcoord (0 : Fin 3)
    · simpa using hcoord (1 : Fin 3)
    · simpa using hcoord (2 : Fin 3)
  -- Restrict to the `n ≤ 4` powers actually needed by the Vandermonde matrix.
  have hV : ∀ i : Fin n, (∑ j : Fin n, w j * t j ^ (i : ℕ)) = 0 := by
    intro i
    have := hpow (Fin.castLE hn i)
    simpa using this
  have hw : w = 0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero ht hV
  intro i
  simpa using congrFun hw i

/-- **Affine independence of every finite set of at most four distinct real samples.** -/
theorem momentCurve_affineIndependent_finset (S : Finset ℝ) (hcard : S.card ≤ 4) :
    AffineIndependent ℝ (fun x : S => momentCurve (x : ℝ)) := by
  let e : Fin S.card ≃ S := (Finset.equivFin S).symm
  have ht : Function.Injective (fun i : Fin S.card => (e i : ℝ)) := by
    intro i j hij
    exact e.injective (Subtype.ext hij)
  have h := momentCurve_affineIndependent_fin (n := S.card) hcard ht
  exact (affineIndependent_equiv e).mp h

/-- The two-point case: two distinct moment-curve samples are affinely independent. -/
theorem momentCurve_affineIndependent_pair {x y : ℝ} (hxy : x ≠ y) :
    AffineIndependent ℝ ![momentCurve x, momentCurve y] := by
  have ht : Function.Injective ![x, y] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h := momentCurve_affineIndependent_fin (n := 2) (by norm_num) ht
  have hfun : (fun i : Fin 2 => momentCurve (![x, y] i)) =
      ![momentCurve x, momentCurve y] := by
    ext i
    fin_cases i <;> simp
  rwa [hfun] at h

/-- The three-point case: three distinct moment-curve samples are affinely independent. -/
theorem momentCurve_affineIndependent_triple {x y z : ℝ}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    AffineIndependent ℝ ![momentCurve x, momentCurve y, momentCurve z] := by
  have ht : Function.Injective ![x, y, z] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h := momentCurve_affineIndependent_fin (n := 3) (by norm_num) ht
  have hfun : (fun i : Fin 3 => momentCurve (![x, y, z] i)) =
      ![momentCurve x, momentCurve y, momentCurve z] := by
    ext i
    fin_cases i <;> simp
  rwa [hfun] at h

/-- The four-point case: four distinct moment-curve samples are affinely independent. -/
theorem momentCurve_affineIndependent_quadruple {x y z w : ℝ}
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    AffineIndependent ℝ ![momentCurve x, momentCurve y, momentCurve z, momentCurve w] := by
  have ht : Function.Injective ![x, y, z, w] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h := momentCurve_affineIndependent_fin (n := 4) (by norm_num) ht
  have hfun : (fun i : Fin 4 => momentCurve (![x, y, z, w] i)) =
      ![momentCurve x, momentCurve y, momentCurve z, momentCurve w] := by
    ext i
    fin_cases i <;> simp
  rwa [hfun] at h

/-! ## Affine combination weights: the elementary Vandermonde eliminations -/

/-- Three distinct nodes with three vanishing moment equations have all weights zero. -/
private theorem weights_zero_three {p q r : ℝ}
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (c₀ c₁ c₂ : ℝ)
    (h0 : c₀ + c₁ + c₂ = 0)
    (h1 : c₀ * p + c₁ * q + c₂ * r = 0)
    (h2 : c₀ * p ^ 2 + c₁ * q ^ 2 + c₂ * r ^ 2 = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 := by
  have hf : Function.Injective ![p, q, r] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hsum : ∀ i : Fin 3,
      (∑ j : Fin 3, (![c₀, c₁, c₂] : Fin 3 → ℝ) j * (![p, q, r] j) ^ (i : ℕ)) =
        0 := by
    intro i
    fin_cases i
    · simpa [Fin.sum_univ_three] using h0
    · simpa [Fin.sum_univ_three] using h1
    · simpa [Fin.sum_univ_three] using h2
  have hw := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hf hsum
  exact ⟨by simpa using congrFun hw (0 : Fin 3),
    by simpa using congrFun hw (1 : Fin 3),
    by simpa using congrFun hw (2 : Fin 3)⟩

/-- Four distinct nodes with four vanishing moment equations have all weights zero. -/
private theorem weights_zero_four {p q r s : ℝ}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) (c₀ c₁ c₂ c₃ : ℝ)
    (h0 : c₀ + c₁ + c₂ + c₃ = 0)
    (h1 : c₀ * p + c₁ * q + c₂ * r + c₃ * s = 0)
    (h2 : c₀ * p ^ 2 + c₁ * q ^ 2 + c₂ * r ^ 2 + c₃ * s ^ 2 = 0)
    (h3 : c₀ * p ^ 3 + c₁ * q ^ 3 + c₂ * r ^ 3 + c₃ * s ^ 3 = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 := by
  have hf : Function.Injective ![p, q, r, s] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hsum : ∀ i : Fin 4,
      (∑ j : Fin 4,
        (![c₀, c₁, c₂, c₃] : Fin 4 → ℝ) j * (![p, q, r, s] j) ^ (i : ℕ)) = 0 := by
    intro i
    fin_cases i
    · simpa [Fin.sum_univ_four] using h0
    · simpa [Fin.sum_univ_four] using h1
    · simpa [Fin.sum_univ_four] using h2
    · simpa [Fin.sum_univ_four] using h3
  have hw := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hf hsum
  exact ⟨by simpa using congrFun hw (0 : Fin 4),
    by simpa using congrFun hw (1 : Fin 4),
    by simpa using congrFun hw (2 : Fin 4),
    by simpa using congrFun hw (3 : Fin 4)⟩

/-! ## Straight segments between moment-curve samples -/

/-- The straight closed segment between two moment-curve samples, parametrized affinely by the
unit interval.  At `0` it is the first sample; at `1` it is the second. -/
def segmentPoint (x y : ℝ) (s : I) : EmbeddedReal3 :=
  (1 - (s : ℝ)) • momentCurve x + (s : ℝ) • momentCurve y

/-- Coordinate formula for a segment point. -/
@[simp] theorem segmentPoint_apply (x y : ℝ) (s : I) (j : Fin 3) :
    segmentPoint x y s j =
      (1 - (s : ℝ)) * x ^ ((j : ℕ) + 1) + (s : ℝ) * y ^ ((j : ℕ) + 1) := by
  simp [segmentPoint, smul_eq_mul]

/-- The segment starts at the first endpoint. -/
@[simp] theorem segmentPoint_zero (x y : ℝ) :
    segmentPoint x y (0 : I) = momentCurve x := by
  simp [segmentPoint]

/-- The segment ends at the second endpoint. -/
@[simp] theorem segmentPoint_one (x y : ℝ) :
    segmentPoint x y (1 : I) = momentCurve y := by
  simp [segmentPoint]

/-- The segment point is the affine line map of the two endpoints. -/
theorem segmentPoint_eq_lineMap (x y : ℝ) (s : I) :
    segmentPoint x y s =
      AffineMap.lineMap (momentCurve x) (momentCurve y) (s : ℝ) := by
  rw [AffineMap.lineMap_apply_module]
  rfl

/-- The segment point is the value of the bundled straight-line path. -/
theorem segmentPoint_eq_path_segment (x y : ℝ) (s : I) :
    segmentPoint x y s = Path.segment (momentCurve x) (momentCurve y) s := by
  rw [segmentPoint_eq_lineMap]
  rfl

/-- The continuous affine parametrization of a segment, as a bundled path. -/
def segmentPath (x y : ℝ) : C(I, EmbeddedReal3) where
  toFun := segmentPoint x y
  continuous_toFun := by
    show Continuous fun s : I =>
      (1 - (s : ℝ)) • momentCurve x + (s : ℝ) • momentCurve y
    have h : Continuous fun s : I => (s : ℝ) := continuous_subtype_val
    exact ((continuous_const.sub h).smul continuous_const).add (h.smul continuous_const)

@[simp] theorem segmentPath_apply (x y : ℝ) (s : I) :
    segmentPath x y s = segmentPoint x y s := rfl

/-- The range of the segment parametrization is the closed segment of the two sample points. -/
theorem range_segmentPoint (x y : ℝ) :
    Set.range (segmentPoint x y) = [momentCurve x -[ℝ] momentCurve y] := by
  have h := Path.range_segment (momentCurve x) (momentCurve y)
  rw [← h]
  congr 1
  funext s
  exact segmentPoint_eq_path_segment x y s

/-- Every segment point belongs to the closed segment of its endpoints. -/
theorem segmentPoint_mem_segment (x y : ℝ) (s : I) :
    segmentPoint x y s ∈ [momentCurve x -[ℝ] momentCurve y] := by
  rw [← range_segmentPoint]
  exact Set.mem_range_self s

/-! ## Parameter injectivity and endpoint positions -/

/-- For a segment with distinct endpoints, the affine parameter is injective: the same chord
cannot be traversed twice at two different parameters. -/
theorem segmentPoint_eq_iff_same_pair {x y : ℝ} (hxy : x ≠ y) {s t : I} :
    segmentPoint x y s = segmentPoint x y t ↔ s = t := by
  constructor
  · intro h
    have hc : (1 - (s : ℝ)) * x + (s : ℝ) * y =
        (1 - (t : ℝ)) * x + (t : ℝ) * y := by
      have := congrArg (fun z : EmbeddedReal3 => z (0 : Fin 3)) h
      simpa using this
    have hprod : ((s : ℝ) - (t : ℝ)) * (y - x) = 0 := by
      linear_combination hc
    rcases mul_eq_zero.mp hprod with hst | hyx
    · exact Subtype.ext (sub_eq_zero.mp hst)
    · exact absurd (sub_eq_zero.mp hyx) (Ne.symm hxy)
  · rintro rfl
    rfl

/-- For the same unordered endpoint pair traversed in the opposite direction, the two parameters
are complementary: `s + t = 1`.  This is the reversal exception to the separation theorem. -/
theorem segmentPoint_swap_eq_iff {x y : ℝ} (hxy : x ≠ y) {s t : I} :
    segmentPoint x y s = segmentPoint y x t ↔ (s : ℝ) + (t : ℝ) = 1 := by
  constructor
  · intro h
    have hc : (1 - (s : ℝ)) * x + (s : ℝ) * y =
        (1 - (t : ℝ)) * y + (t : ℝ) * x := by
      have := congrArg (fun z : EmbeddedReal3 => z (0 : Fin 3)) h
      simpa using this
    have hprod : (1 - (s : ℝ) - (t : ℝ)) * (x - y) = 0 := by
      linear_combination hc
    have hne : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hzero : 1 - (s : ℝ) - (t : ℝ) = 0 := by
      rcases mul_eq_zero.mp hprod with h' | h'
      · exact h'
      · exact absurd h' hne
    linarith
  · intro h
    ext j
    rw [segmentPoint_apply, segmentPoint_apply]
    linear_combination (y ^ ((j : ℕ) + 1) - x ^ ((j : ℕ) + 1)) * h

/-- **A chord meets the moment-curve sample set only at its own endpoints.**  For distinct
`x ≠ y`, a point of the `x`–`y` segment is a moment-curve sample `momentCurve z` exactly when it
is the initial endpoint (`s = 0`, `z = x`) or the final endpoint (`s = 1`, `z = y`).  In
particular the relative interior of a chord contains no moment-curve sample. -/
theorem segmentPoint_eq_momentCurve_iff {x y z : ℝ} (hxy : x ≠ y) {s : I} :
    segmentPoint x y s = momentCurve z ↔
      (s = 0 ∧ z = x) ∨ (s = 1 ∧ z = y) := by
  constructor
  · intro h
    have h0 : (1 - (s : ℝ)) * x + (s : ℝ) * y = z := by
      have := congrArg (fun w : EmbeddedReal3 => w (0 : Fin 3)) h
      simpa using this
    have h1 : (1 - (s : ℝ)) * x ^ 2 + (s : ℝ) * y ^ 2 = z ^ 2 := by
      have := congrArg (fun w : EmbeddedReal3 => w (1 : Fin 3)) h
      simpa using this
    by_cases hs0 : s = 0
    · left
      refine ⟨hs0, ?_⟩
      have hx : momentCurve x = momentCurve z := by
        rw [← h, hs0]
        simp [segmentPoint]
      exact (momentCurve_injective hx).symm
    · by_cases hs1 : s = 1
      · right
        refine ⟨hs1, ?_⟩
        have hy : momentCurve y = momentCurve z := by
          rw [← h, hs1]
          simp [segmentPoint]
        exact (momentCurve_injective hy).symm
      · exfalso
        have hzx : z ≠ x := by
          intro hzx
          apply hs0
          have h0' : (1 - (s : ℝ)) * x + (s : ℝ) * y = x := by
            rwa [hzx] at h0
          have hprod : (s : ℝ) * (y - x) = 0 := by
            linear_combination h0'
          rcases mul_eq_zero.mp hprod with h' | h'
          · exact Subtype.ext h'
          · exact absurd (sub_eq_zero.mp h') (Ne.symm hxy)
        have hzy : z ≠ y := by
          intro hzy
          apply hs1
          have h0' : (1 - (s : ℝ)) * x + (s : ℝ) * y = y := by
            rwa [hzy] at h0
          have hprod : (1 - (s : ℝ)) * (x - y) = 0 := by
            linear_combination h0'
          rcases mul_eq_zero.mp hprod with h' | h'
          · have hs : (s : ℝ) = 1 := by linarith
            exact Subtype.ext hs
          · exact absurd (sub_eq_zero.mp h') hxy
        have hw0 : (1 - (s : ℝ)) + (s : ℝ) + (-1) = 0 := by ring
        have hw1 : (1 - (s : ℝ)) * x + (s : ℝ) * y + (-1) * z = 0 := by
          linear_combination h0
        have hw2 : (1 - (s : ℝ)) * x ^ 2 + (s : ℝ) * y ^ 2 + (-1) * z ^ 2 = 0 := by
          linear_combination h1
        obtain ⟨_, ha0, _⟩ :=
          weights_zero_three hxy (Ne.symm hzx) (Ne.symm hzy)
            (1 - (s : ℝ)) (s : ℝ) (-1) hw0 hw1 hw2
        exact hs0 (Subtype.ext ha0)
  · rintro (⟨hs, hzx⟩ | ⟨hs, hzy⟩)
    · rw [hs]
      simp [segmentPoint, hzx]
    · rw [hs]
      simp [segmentPoint, hzy]

/-- A relative-interior point of a chord is never a moment-curve sample. -/
theorem segmentPoint_interior_ne_momentCurve {x y z : ℝ} (hxy : x ≠ y) {s : I}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    segmentPoint x y s ≠ momentCurve z := by
  intro h
  rcases (segmentPoint_eq_momentCurve_iff hxy).mp h with ⟨hs, hzx'⟩ | ⟨hs, hzy'⟩
  · exact hs0 hs
  · exact hs1 hs

/-! ## Segment separation for distinct unordered endpoint pairs -/

/-- Two ordered endpoint pairs are the same unordered pair.  This is the unordered-pair equality
used in the separation statement. -/
def SameUnorderedPair (x y u v : ℝ) : Prop :=
  (x = u ∧ y = v) ∨ (x = v ∧ y = u)

/-- The endpoint collision alternatives for two chord points.  In each alternative both
parameters are endpoints (`0` or `1`) and the corresponding endpoint labels agree. -/
def EndpointCollision (x y u v : ℝ) (s t : I) : Prop :=
  (s = 0 ∧ t = 0 ∧ x = u) ∨
    (s = 0 ∧ t = 1 ∧ x = v) ∨
      (s = 1 ∧ t = 0 ∧ y = u) ∨
        (s = 1 ∧ t = 1 ∧ y = v)

/-- **Exact segment separation on the moment curve.**

Let `x ≠ y` and `u ≠ v` be distinct chord endpoints, and suppose the unordered endpoint pairs
`{x, y}` and `{u, v}` differ.  Then a point of the `x`–`y` segment coincides with a point of the
`u`–`v` segment if and only if both parameters are endpoints and the corresponding endpoint
labels agree; the four possibilities are listed in `EndpointCollision`.

This is the parameterized separation theorem intended for the graph layer: distinct edges with
different unordered endpoint pairs meet only at an endpoint that they share, and then only at the
parameters `0` or `1` matching that shared label.  The case of identical unordered endpoint pairs
is deliberately excluded here and handled separately by `segmentPoint_eq_iff_same_pair` (same
orientation) and `segmentPoint_swap_eq_iff` (reversed orientation). -/
theorem segmentPoint_eq_iff_endpointCollision {x y u v : ℝ}
    (hxy : x ≠ y) (huv : u ≠ v) (hpair : ¬ SameUnorderedPair x y u v) {s t : I} :
    segmentPoint x y s = segmentPoint u v t ↔ EndpointCollision x y u v s t := by
  constructor
  · intro h
    set a : ℝ := (s : ℝ) with ha
    set b : ℝ := (t : ℝ) with hb
    -- The three coordinate equations.
    have h0 : (1 - a) * x + a * y = (1 - b) * u + b * v := by
      have hc := congrArg (fun z : EmbeddedReal3 => z (0 : Fin 3)) h
      simpa [ha, hb] using hc
    have h1 : (1 - a) * x ^ 2 + a * y ^ 2 = (1 - b) * u ^ 2 + b * v ^ 2 := by
      have hc := congrArg (fun z : EmbeddedReal3 => z (1 : Fin 3)) h
      simpa [ha, hb] using hc
    have h2 : (1 - a) * x ^ 3 + a * y ^ 3 = (1 - b) * u ^ 3 + b * v ^ 3 := by
      have hc := congrArg (fun z : EmbeddedReal3 => z (2 : Fin 3)) h
      simpa [ha, hb] using hc
    -- The same equations with the right-hand side moved to the left.
    have h0' : (1 - a) * x + a * y - (1 - b) * u - b * v = 0 := by
      linear_combination h0
    have h1' : (1 - a) * x ^ 2 + a * y ^ 2 - (1 - b) * u ^ 2 - b * v ^ 2 = 0 := by
      linear_combination h1
    have h2' : (1 - a) * x ^ 3 + a * y ^ 3 - (1 - b) * u ^ 3 - b * v ^ 3 = 0 := by
      linear_combination h2
    -- Useful converters back from the auxiliary reals `a`, `b` to the interval parameters.
    have hs_eq_zero : a = 0 → s = 0 := fun h' => Subtype.ext (by rw [← ha]; exact h')
    have ht_eq_zero : b = 0 → t = 0 := fun h' => Subtype.ext (by rw [← hb]; exact h')
    have hs_eq_one : a = 1 → s = 1 := fun h' => Subtype.ext (by rw [← ha]; exact h')
    have ht_eq_one : b = 1 → t = 1 := fun h' => Subtype.ext (by rw [← hb]; exact h')
    by_cases hxu : x = u
    · -- Shared endpoint `x = u` (unless the two unordered pairs are identical).
      by_cases hyv : y = v
      · exact absurd (Or.inl ⟨hxu, hyv⟩) hpair
      · have hxv : x ≠ v := by
          intro hxv
          exact huv (hxu.symm.trans hxv)
        have hw1 : (b - a) * x + a * y + (-b) * v = 0 := by
          rw [← hxu] at h0'
          linear_combination h0'
        have hw2 : (b - a) * x ^ 2 + a * y ^ 2 + (-b) * v ^ 2 = 0 := by
          rw [← hxu] at h1'
          linear_combination h1'
        have hw0 : (b - a) + a + (-b) = 0 := by ring
        obtain ⟨_, ha0, hnb⟩ :=
          weights_zero_three hxy hxv hyv (b - a) a (-b) hw0 hw1 hw2
        exact Or.inl ⟨hs_eq_zero ha0, ht_eq_zero (neg_eq_zero.mp hnb), hxu⟩
    · by_cases hxv : x = v
      · -- Shared endpoint `x = v` (unless the two unordered pairs are identical).
        by_cases hyu : y = u
        · exact absurd (Or.inr ⟨hxv, hyu⟩) hpair
        · have hw1 : (1 - a - b) * x + a * y + (b - 1) * u = 0 := by
            rw [← hxv] at h0'
            linear_combination h0'
          have hw2 : (1 - a - b) * x ^ 2 + a * y ^ 2 + (b - 1) * u ^ 2 = 0 := by
            rw [← hxv] at h1'
            linear_combination h1'
          have hw0 : (1 - a - b) + a + (b - 1) = 0 := by ring
          obtain ⟨_, ha0, hb1⟩ :=
            weights_zero_three hxy hxu hyu (1 - a - b) a (b - 1) hw0 hw1 hw2
          exact Or.inr (Or.inl ⟨hs_eq_zero ha0, ht_eq_one (sub_eq_zero.mp hb1), hxv⟩)
      · by_cases hyu : y = u
        · -- Shared endpoint `y = u`.
          have hyv : y ≠ v := by
            intro hyv
            exact huv (hyu.symm.trans hyv)
          have hw1 : (1 - a) * x + (a + b - 1) * y + (-b) * v = 0 := by
            rw [← hyu] at h0'
            linear_combination h0'
          have hw2 : (1 - a) * x ^ 2 + (a + b - 1) * y ^ 2 + (-b) * v ^ 2 = 0 := by
            rw [← hyu] at h1'
            linear_combination h1'
          have hw0 : (1 - a) + (a + b - 1) + (-b) = 0 := by ring
          obtain ⟨hcoe, _, hnb⟩ :=
            weights_zero_three hxy hxv hyv (1 - a) (a + b - 1) (-b) hw0 hw1 hw2
          exact Or.inr (Or.inr (Or.inl
            ⟨hs_eq_one (by linarith), ht_eq_zero (neg_eq_zero.mp hnb), hyu⟩))
        · by_cases hyv : y = v
          · -- Shared endpoint `y = v`.
            have hw1 : (1 - a) * x + (a - b) * y + (b - 1) * u = 0 := by
              rw [← hyv] at h0'
              linear_combination h0'
            have hw2 : (1 - a) * x ^ 2 + (a - b) * y ^ 2 + (b - 1) * u ^ 2 = 0 := by
              rw [← hyv] at h1'
              linear_combination h1'
            have hw0 : (1 - a) + (a - b) + (b - 1) = 0 := by ring
            obtain ⟨ha1, _, hb1⟩ :=
              weights_zero_three hxy hxu hyu (1 - a) (a - b) (b - 1) hw0 hw1 hw2
            exact Or.inr (Or.inr (Or.inr
              ⟨hs_eq_one (by linarith), ht_eq_one (sub_eq_zero.mp hb1), hyv⟩))
          · -- No shared endpoint: four distinct samples, so no collision is possible.
            have hw0 : (1 - a) + a + (b - 1) + (-b) = 0 := by ring
            have hw1 : (1 - a) * x + a * y + (b - 1) * u + (-b) * v = 0 := by
              linear_combination h0'
            have hw2 : (1 - a) * x ^ 2 + a * y ^ 2 + (b - 1) * u ^ 2 + (-b) * v ^ 2 = 0 := by
              linear_combination h1'
            have hw3 : (1 - a) * x ^ 3 + a * y ^ 3 + (b - 1) * u ^ 3 + (-b) * v ^ 3 = 0 := by
              linear_combination h2'
            obtain ⟨ha1, ha0, _, _⟩ :=
              weights_zero_four hxy hxu hxv hyu hyv huv
                (1 - a) a (b - 1) (-b) hw0 hw1 hw2 hw3
            exfalso
            linarith
  · rintro (⟨hs, ht, hxu⟩ | ⟨hs, ht, hxv⟩ | ⟨hs, ht, hyu⟩ | ⟨hs, ht, hyv⟩)
    · rw [hs, ht, hxu]
      simp [segmentPoint]
    · rw [hs, ht, hxv]
      simp [segmentPoint]
    · rw [hs, ht, hyu]
      simp [segmentPoint]
    · rw [hs, ht, hyv]
      simp [segmentPoint]

/-- **Disjoint-endpoint separation.**  If two chords have pairwise distinct endpoint labels, the
segments are disjoint. -/
theorem segmentPoint_ne_of_disjoint_endpoints {x y u v : ℝ}
    (hxy : x ≠ y) (huv : u ≠ v)
    (hxu : x ≠ u) (hxv : x ≠ v) (hyu : y ≠ u) (hyv : y ≠ v) (s t : I) :
    segmentPoint x y s ≠ segmentPoint u v t := by
  intro h
  have hpair : ¬ SameUnorderedPair x y u v := by
    rintro (⟨h, _⟩ | ⟨h, _⟩)
    · exact hxu h
    · exact hxv h
  rcases (segmentPoint_eq_iff_endpointCollision hxy huv hpair).mp h with
    ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩
  · exact hxu h
  · exact hxv h
  · exact hyu h
  · exact hyv h

end

end OrganicStereoMomentCurveSeparation
end TetraStereo.OneCenter
