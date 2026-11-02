import TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization
import Mathlib.Analysis.Convex.PathConnected

set_option autoImplicit false

/-!
# Existence of a global embedding for every finite loopless multigraph

The module `OrganicStereoEmbeddedGraphRealization` defines the graph-indexed normal form
`Realization src dst` of a finite multigraph with endpoint maps `src dst : E → V`, the coinduced
topology on it, and the structure `EmbeddedGraph src dst` consisting of *one* global continuous
injective map `Realization src dst → ℝ³`.  That module proves every local embedded-bond-path law
from such a global map, but it takes the global map as a supplied input.

This module removes that input.  For every finite loopless multigraph it *constructs* an
`EmbeddedGraph src dst`, with no supplied global map, no supplied arcs and no local geometric
obligations.  The only hypotheses are `[Fintype V]`, `[Fintype E]` and the per-edge non-loop
condition `∀ e, src e ≠ dst e`.

## Construction

The construction is the classical convex-position embedding of a finite graph in three-space.

* Both the vertex labels and the edge labels are given distinct real parameters by a single
  injection `labelParam : V ⊕ E → ℝ` obtained from a finite enumeration.  The `E` summand is
  the *private subdivision point* of that original edge; parallel edges therefore receive
  different private labels even when they have the same endpoints.
* `momentCurve t = (t, t², t³)` is the moment curve in `ℝ³`.
* The image of the edge `e` is the two-segment polyline from `momentCurve (src e)` through the
  private point `momentCurve (e)` to `momentCurve (dst e)`, bundled with `Path.trans`.
* The global map sends a vertex normal form to the moment-curve point of its label, and an
  interior parameter of the edge `e` to the corresponding point of the edge polyline.  It is
  the map `globalMap`.

## Why it is continuous

The topology on `Realization src dst` is the coinduced topology of the gluing map `glue`
(defined in `OrganicStereoEmbeddedGraphRealization`), so continuity of `globalMap` is proved
through the universal property `continuous_iff_continuous_comp_glue`: the composite with `glue`
is the explicit raw map that is constant on vertex slots and a bundled path on each interval
slot.

## Why it is injective

The moment curve is in convex position: any at most four distinct points on it are affinely
independent.  This is proved here by an elementary nested-difference argument (no determinants),
and yields:

* a moment-curve point never lies on a segment between two other moment-curve points;
* two segments with four distinct moment-curve endpoints are disjoint;
* two segments with three distinct endpoints meet only at the shared endpoint.

Since a segment of the edge `e` has endpoints labelled either by `Sum.inl (src e)`,
`Sum.inr e` (the private point) or `Sum.inl (dst e)`, and `labelParam` is injective, the
injectivity analysis is a finite case analysis on the two possible halves of each edge.
The loop condition is used exactly to keep the two halves of one edge distinct: it forces
`src e ≠ dst e`, so the two segments of an edge meet only at the private point.

## Scope

This module proves *structural inhabitance*: every finite loopless multigraph (parallel edges
and disconnected components included) admits an `EmbeddedGraph`.  It does not match prescribed
atom coordinates or prescribed arcs, does not classify knots or links, and does not claim that
every physically admissible chemical graph is realizable by this canonical embedding.  All
derived local path laws (arc endpoints, arc injectivity, interiors avoiding atoms, distinct
arcs meeting only at common endpoints) follow from the already-proved theorems of
`OrganicStereoEmbeddedGraphRealization.EmbeddedGraph`.
-/

namespace TetraStereo.OneCenter
namespace OrganicStereoFiniteGraphEmbedding

open scoped unitInterval
open AffineMap
open OrganicStereoEmbeddedGraphRealization

noncomputable section

universe u v

variable {V : Type u} {E : Type v}

/-! ## Real parameters from a finite enumeration -/

section Parameters

variable [Fintype V] [Fintype E]

/-- A single injective real parameter assignment on the disjoint union of the vertex labels and
the edge labels.  The `E` summand is the private subdivision point of the edge. -/
def labelParam : V ⊕ E → ℝ :=
  fun x => ((Fintype.equivFin (V ⊕ E)) x : ℕ)

/-- The vertex-label parameter, with both summand types fixed by the local context. -/
local notation "vp" w:max => labelParam (V := V) (E := E) (Sum.inl w)

/-- The private edge-label parameter, with both summand types fixed by the local context. -/
local notation "ep" e:max => labelParam (V := V) (E := E) (Sum.inr e)

theorem labelParam_injective : Function.Injective (labelParam (V := V) (E := E)) := by
  intro x y h
  have h' : ((Fintype.equivFin (V ⊕ E)) x : ℝ) =
      ((Fintype.equivFin (V ⊕ E)) y : ℝ) := h
  have hval : ((Fintype.equivFin (V ⊕ E)) x).val =
      ((Fintype.equivFin (V ⊕ E)) y).val := Nat.cast_injective h'
  exact (Fintype.equivFin (V ⊕ E)).injective (Fin.ext hval)

theorem labelParam_inl_inj {w w' : V} : vp w = vp w' ↔ w = w' := by
  constructor
  · intro h
    exact Sum.inl_injective (labelParam_injective h)
  · intro h
    rw [h]

theorem labelParam_inr_inj {e f : E} : ep e = ep f ↔ e = f := by
  constructor
  · intro h
    exact Sum.inr_injective (labelParam_injective h)
  · intro h
    rw [h]

theorem labelParam_inl_ne_inr (w : V) (e : E) : vp w ≠ ep e := by
  intro h
  exact Sum.inl_ne_inr (labelParam_injective h)

theorem labelParam_inr_ne_inl (e : E) (w : V) : ep e ≠ vp w :=
  (labelParam_inl_ne_inr w e).symm

/-! ## The moment curve and affine independence of at most four of its points -/

/-- The moment curve `t ↦ (t, t², t³)` in real three-space. -/
def momentCurve (t : ℝ) : EmbeddedReal3 :=
  !₂[t, t ^ 2, t ^ 3]

@[simp] theorem momentCurve_zero (t : ℝ) : momentCurve t 0 = t := by
  simp [momentCurve]

@[simp] theorem momentCurve_one (t : ℝ) : momentCurve t 1 = t ^ 2 := by
  simp [momentCurve]

@[simp] theorem momentCurve_two (t : ℝ) : momentCurve t 2 = t ^ 3 := by
  simp [momentCurve]

/-- The moment curve is injective. -/
theorem momentCurve_injective : Function.Injective momentCurve := by
  intro a b h
  have h0 : momentCurve a 0 = momentCurve b 0 := congrArg (fun x : EmbeddedReal3 => x 0) h
  simpa using h0

/-- Coordinate `0` of a point on an affine segment between two moment-curve points. -/
theorem lineMap_momentCurve_coord_zero (a b u : ℝ) :
    (lineMap (momentCurve a) (momentCurve b) u) 0 = (1 - u) * a + u * b := by
  rw [lineMap_apply_module]
  simp

/-- Coordinate `1` of a point on an affine segment between two moment-curve points. -/
theorem lineMap_momentCurve_coord_one (a b u : ℝ) :
    (lineMap (momentCurve a) (momentCurve b) u) 1 = (1 - u) * a ^ 2 + u * b ^ 2 := by
  rw [lineMap_apply_module]
  simp

/-- Coordinate `2` of a point on an affine segment between two moment-curve points. -/
theorem lineMap_momentCurve_coord_two (a b u : ℝ) :
    (lineMap (momentCurve a) (momentCurve b) u) 2 = (1 - u) * a ^ 3 + u * b ^ 3 := by
  rw [lineMap_apply_module]
  simp

/-- Three distinct moment-curve points are affinely independent: an affine relation with zero
coefficient sum is trivial. -/
theorem affineIndependent_three {a b c : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {la lb lc : ℝ}
    (h0 : la + lb + lc = 0)
    (h1 : la * a + lb * b + lc * c = 0)
    (h2 : la * a ^ 2 + lb * b ^ 2 + lc * c ^ 2 = 0) :
    la = 0 ∧ lb = 0 ∧ lc = 0 := by
  have e1 : lb * (b - a) + lc * (c - a) = 0 := by
    linear_combination h1 - a * h0
  have e2 : lb * (b - a) * b + lc * (c - a) * c = 0 := by
    linear_combination h2 - a * h1
  have f : lc * (c - a) * (c - b) = 0 := by
    linear_combination e2 - b * e1
  have hca : c - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hac)
  have hcb : c - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hbc)
  have hlc : lc = 0 := by
    rcases mul_eq_zero.mp f with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' hca
    · exact absurd h hcb
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hlb : lb = 0 := by
    have e1' : lb * (b - a) = 0 := by
      simpa [hlc] using e1
    rcases mul_eq_zero.mp e1' with h | h
    · exact h
    · exact absurd h hba
  have hla : la = 0 := by linarith
  exact ⟨hla, hlb, hlc⟩

/-- Four distinct moment-curve points are affinely independent: an affine relation with zero
coefficient sum is trivial.  The proof is a nested-difference (Vandermonde) argument. -/
theorem affineIndependent_four {a b c d : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {la lb lc ld : ℝ}
    (h0 : la + lb + lc + ld = 0)
    (h1 : la * a + lb * b + lc * c + ld * d = 0)
    (h2 : la * a ^ 2 + lb * b ^ 2 + lc * c ^ 2 + ld * d ^ 2 = 0)
    (h3 : la * a ^ 3 + lb * b ^ 3 + lc * c ^ 3 + ld * d ^ 3 = 0) :
    la = 0 ∧ lb = 0 ∧ lc = 0 ∧ ld = 0 := by
  have e1 : lb * (b - a) + lc * (c - a) + ld * (d - a) = 0 := by
    linear_combination h1 - a * h0
  have e2 : lb * (b - a) * b + lc * (c - a) * c + ld * (d - a) * d = 0 := by
    linear_combination h2 - a * h1
  have e3 : lb * (b - a) * b ^ 2 + lc * (c - a) * c ^ 2 + ld * (d - a) * d ^ 2 = 0 := by
    linear_combination h3 - a * h2
  have f1 : lc * (c - a) * (c - b) + ld * (d - a) * (d - b) = 0 := by
    linear_combination e2 - b * e1
  have f2 : lc * (c - a) * c * (c - b) + ld * (d - a) * d * (d - b) = 0 := by
    linear_combination e3 - b * e2
  have g : ld * (d - a) * (d - b) * (d - c) = 0 := by
    linear_combination f2 - c * f1
  have hda : d - a ≠ 0 := sub_ne_zero.mpr (Ne.symm had)
  have hdb : d - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hbd)
  have hdc : d - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hcd)
  have hld : ld = 0 := by
    rcases mul_eq_zero.mp g with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact h''
        · exact absurd h'' hda
      · exact absurd h' hdb
    · exact absurd h hdc
  have hca : c - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hac)
  have hcb : c - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hbc)
  have hlc : lc = 0 := by
    have f1' : lc * (c - a) * (c - b) = 0 := by
      simpa [hld] using f1
    rcases mul_eq_zero.mp f1' with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' hca
    · exact absurd h hcb
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hlb : lb = 0 := by
    have e1' : lb * (b - a) = 0 := by
      simpa [hlc, hld] using e1
    rcases mul_eq_zero.mp e1' with h | h
    · exact h
    · exact absurd h hba
  have hla : la = 0 := by linarith
  exact ⟨hla, hlb, hlc, hld⟩

/-! ### Segment separation on the moment curve -/

/-- Two segments whose four endpoints are distinct moment-curve points are disjoint. -/
theorem lineMap_momentCurve_disjoint {a b c d u v : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h : lineMap (momentCurve a) (momentCurve b) u =
      lineMap (momentCurve c) (momentCurve d) v) : False := by
  have h1 : (1 - u) * a + u * b + (-(1 - v)) * c + (-v) * d = 0 := by
    have hc := congrArg (fun x : EmbeddedReal3 => x 0) h
    simp only at hc
    rw [lineMap_momentCurve_coord_zero, lineMap_momentCurve_coord_zero] at hc
    linarith
  have h2 : (1 - u) * a ^ 2 + u * b ^ 2 + (-(1 - v)) * c ^ 2 + (-v) * d ^ 2 = 0 := by
    have hc := congrArg (fun x : EmbeddedReal3 => x 1) h
    simp only at hc
    rw [lineMap_momentCurve_coord_one, lineMap_momentCurve_coord_one] at hc
    linarith
  have h3 : (1 - u) * a ^ 3 + u * b ^ 3 + (-(1 - v)) * c ^ 3 + (-v) * d ^ 3 = 0 := by
    have hc := congrArg (fun x : EmbeddedReal3 => x 2) h
    simp only at hc
    rw [lineMap_momentCurve_coord_two, lineMap_momentCurve_coord_two] at hc
    linarith
  have h0 : (1 - u) + u + (-(1 - v)) + (-v) = 0 := by ring
  obtain ⟨hla, hlb, _, _⟩ :=
    affineIndependent_four hab hac had hbc hbd hcd h0 h1 h2 h3
  linarith

/-- Two segments sharing their first endpoint, with three distinct endpoint parameters, meet only
at that shared endpoint. -/
theorem lineMap_momentCurve_shared_first {a b c u v : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : lineMap (momentCurve a) (momentCurve b) u =
      lineMap (momentCurve a) (momentCurve c) v) : u = 0 ∧ v = 0 := by
  have h1 : ((1 - u) - (1 - v)) * a + u * b + (-v) * c = 0 := by
    have hc := congrArg (fun x : EmbeddedReal3 => x 0) h
    simp only at hc
    rw [lineMap_momentCurve_coord_zero, lineMap_momentCurve_coord_zero] at hc
    linarith
  have h2 : ((1 - u) - (1 - v)) * a ^ 2 + u * b ^ 2 + (-v) * c ^ 2 = 0 := by
    have hc := congrArg (fun x : EmbeddedReal3 => x 1) h
    simp only at hc
    rw [lineMap_momentCurve_coord_one, lineMap_momentCurve_coord_one] at hc
    linarith
  have h0 : ((1 - u) - (1 - v)) + u + (-v) = 0 := by ring
  obtain ⟨_, hlb, hlc⟩ := affineIndependent_three hab hac hbc h0 h1 h2
  exact ⟨hlb, by linarith⟩

/-- Two segments where the second starts at the end of the first, with three distinct endpoint
parameters, meet only at the middle point. -/
theorem lineMap_momentCurve_shared_mid {a b c u v : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : lineMap (momentCurve a) (momentCurve b) u =
      lineMap (momentCurve b) (momentCurve c) v) : u = 1 ∧ v = 0 := by
  have h1 : (1 - u) * a + (u - (1 - v)) * b + (-v) * c = 0 := by
    have hc := congrArg (fun x : EmbeddedReal3 => x 0) h
    simp only at hc
    rw [lineMap_momentCurve_coord_zero, lineMap_momentCurve_coord_zero] at hc
    linarith
  have h2 : (1 - u) * a ^ 2 + (u - (1 - v)) * b ^ 2 + (-v) * c ^ 2 = 0 := by
    have hc := congrArg (fun x : EmbeddedReal3 => x 1) h
    simp only at hc
    rw [lineMap_momentCurve_coord_one, lineMap_momentCurve_coord_one] at hc
    linarith
  have h0 : (1 - u) + (u - (1 - v)) + (-v) = 0 := by ring
  obtain ⟨hla, _, hlc⟩ := affineIndependent_three hab hac hbc h0 h1 h2
  exact ⟨by linarith, by linarith⟩

/-- Two segments sharing their second endpoint, with three distinct endpoint parameters, meet
only at that shared endpoint. -/
theorem lineMap_momentCurve_shared_second {a b c u v : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : lineMap (momentCurve a) (momentCurve b) u =
      lineMap (momentCurve c) (momentCurve b) v) : u = 1 ∧ v = 1 := by
  have h1 : (1 - u) * a + (u - v) * b + (-(1 - v)) * c = 0 := by
    have hc := congrArg (fun x : EmbeddedReal3 => x 0) h
    simp only at hc
    rw [lineMap_momentCurve_coord_zero, lineMap_momentCurve_coord_zero] at hc
    linarith
  have h2 : (1 - u) * a ^ 2 + (u - v) * b ^ 2 + (-(1 - v)) * c ^ 2 = 0 := by
    have hc := congrArg (fun x : EmbeddedReal3 => x 1) h
    simp only at hc
    rw [lineMap_momentCurve_coord_one, lineMap_momentCurve_coord_one] at hc
    linarith
  have h0 : (1 - u) + (u - v) + (-(1 - v)) = 0 := by ring
  obtain ⟨hla, _, hlc⟩ := affineIndependent_three hab hac hbc h0 h1 h2
  exact ⟨by linarith, by linarith⟩

/-- Two segments where the second ends at the start of the first, with three distinct endpoint
parameters, meet only at that shared endpoint. -/
theorem lineMap_momentCurve_shared_last {a b c u v : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : lineMap (momentCurve a) (momentCurve b) u =
      lineMap (momentCurve c) (momentCurve a) v) : u = 0 ∧ v = 1 := by
  have h1 : ((1 - u) - v) * a + u * b + (-(1 - v)) * c = 0 := by
    have hc := congrArg (fun x : EmbeddedReal3 => x 0) h
    simp only at hc
    rw [lineMap_momentCurve_coord_zero, lineMap_momentCurve_coord_zero] at hc
    linarith
  have h2 : ((1 - u) - v) * a ^ 2 + u * b ^ 2 + (-(1 - v)) * c ^ 2 = 0 := by
    have hc := congrArg (fun x : EmbeddedReal3 => x 1) h
    simp only at hc
    rw [lineMap_momentCurve_coord_one, lineMap_momentCurve_coord_one] at hc
    linarith
  have h0 : ((1 - u) - v) + u + (-(1 - v)) = 0 := by ring
  obtain ⟨_, hlb, hlc⟩ := affineIndependent_three hab hac hbc h0 h1 h2
  exact ⟨hlb, by linarith⟩

/-- A point of the moment curve lies on a segment between two other moment-curve points only when
it is one of the segment endpoints. -/
theorem lineMap_momentCurve_eq_point {a b c u : ℝ} (hab : a ≠ b)
    (h : lineMap (momentCurve a) (momentCurve b) u = momentCurve c) :
    (u = 0 ∧ c = a) ∨ (u = 1 ∧ c = b) := by
  have h0 : (1 - u) * a + u * b + (-1) * c = 0 := by
    have hc := congrArg (fun x : EmbeddedReal3 => x 0) h
    simp only at hc
    rw [lineMap_momentCurve_coord_zero, momentCurve_zero] at hc
    linarith
  by_cases hua : u = 0
  · left
    refine ⟨hua, ?_⟩
    rw [hua] at h0
    linarith
  · by_cases hub : u = 1
    · right
      refine ⟨hub, ?_⟩
      rw [hub] at h0
      linarith
    · exfalso
      have hca : c ≠ a := by
        intro hc
        rw [hc] at h0
        have hfac : u * (b - a) = 0 := by nlinarith
        rcases mul_eq_zero.mp hfac with h | h
        · exact hua h
        · exact hab (by linarith)
      have hcb : c ≠ b := by
        intro hc
        rw [hc] at h0
        have hfac : (1 - u) * (a - b) = 0 := by nlinarith
        rcases mul_eq_zero.mp hfac with h | h
        · exact hub (by linarith)
        · exact hab (by linarith)
      have h1 : (1 - u) * a ^ 2 + u * b ^ 2 + (-1) * c ^ 2 = 0 := by
        have hc := congrArg (fun x : EmbeddedReal3 => x 1) h
        simp only at hc
        rw [lineMap_momentCurve_coord_one, momentCurve_one] at hc
        linarith
      have hsum : (1 - u) + u + (-1 : ℝ) = 0 := by ring
      obtain ⟨_, _, _⟩ :=
        affineIndependent_three hab hca.symm hcb.symm hsum h0 h1
      linarith

/-! ## The edge polyline and the global map -/

/-- The affine path of the edge `e`: source vertex point, private edge point, destination vertex
point, concatenated with `Path.trans`. -/
def edgePath (src dst : E → V) (e : E) :
    Path (momentCurve (vp (src e))) (momentCurve (vp (dst e))) :=
  (Path.segment (momentCurve (vp (src e))) (momentCurve (ep e))).trans
    (Path.segment (momentCurve (ep e)) (momentCurve (vp (dst e))))

@[simp] theorem edgePath_zero (src dst : E → V) (e : E) :
    edgePath src dst e 0 = momentCurve (vp (src e)) :=
  (edgePath src dst e).source

@[simp] theorem edgePath_one (src dst : E → V) (e : E) :
    edgePath src dst e 1 = momentCurve (vp (dst e)) :=
  (edgePath src dst e).target

/-- Explicit value of the edge polyline: the first affine segment on `[0, 1/2]` and the second
one on `[1/2, 1]`. -/
theorem edgePath_apply (src dst : E → V) (e : E) (t : I) :
    edgePath src dst e t =
      if (t : ℝ) ≤ 1 / 2 then
        lineMap (momentCurve (vp (src e))) (momentCurve (ep e)) (2 * (t : ℝ))
      else
        lineMap (momentCurve (ep e)) (momentCurve (vp (dst e))) (2 * (t : ℝ) - 1) := by
  rw [edgePath, Path.trans_apply]
  split_ifs with h <;> simp

/-- The global embedding map on the graph-indexed normal form. -/
def globalMap (src dst : E → V) : Realization src dst → EmbeddedReal3
  | Realization.vertex w => momentCurve (vp w)
  | Realization.interior e t => edgePath src dst e t.1

@[simp] theorem globalMap_vertex (src dst : E → V) (w : V) :
    globalMap src dst (Realization.vertex w) = momentCurve (vp w) := rfl

@[simp] theorem globalMap_interior (src dst : E → V) (e : E)
    (t : {t : I // t ≠ 0 ∧ t ≠ 1}) :
    globalMap src dst (Realization.interior e t) = edgePath src dst e t.1 := rfl

/-- The value of the global map at an interior parameter on the first half of the edge polyline. -/
theorem globalMap_interior_of_le (src dst : E → V) (e : E)
    (t : {t : I // t ≠ 0 ∧ t ≠ 1}) (ht : (t.1 : ℝ) ≤ 1 / 2) :
    globalMap src dst (Realization.interior e t) =
      lineMap (momentCurve (vp (src e))) (momentCurve (ep e)) (2 * (t.1 : ℝ)) := by
  rw [globalMap_interior, edgePath_apply, if_pos ht]

/-- The value of the global map at an interior parameter on the second half of the edge
polyline. -/
theorem globalMap_interior_of_gt (src dst : E → V) (e : E)
    (t : {t : I // t ≠ 0 ∧ t ≠ 1}) (ht : ¬ (t.1 : ℝ) ≤ 1 / 2) :
    globalMap src dst (Realization.interior e t) =
      lineMap (momentCurve (ep e)) (momentCurve (vp (dst e))) (2 * (t.1 : ℝ) - 1) := by
  rw [globalMap_interior, edgePath_apply, if_neg ht]

/-- The real value of an interior parameter is not `0`. -/
theorem interior_val_ne_zero (t : {t : I // t ≠ 0 ∧ t ≠ 1}) : (t.1 : ℝ) ≠ 0 := by
  intro h
  exact t.2.1 (Subtype.ext h)

/-- The real value of an interior parameter is not `1`. -/
theorem interior_val_ne_one (t : {t : I // t ≠ 0 ∧ t ≠ 1}) : (t.1 : ℝ) ≠ 1 := by
  intro h
  exact t.2.2 (Subtype.ext h)

/-! ## Continuity of the global map -/

/-- The raw map on the coproduct domain whose continuity implies continuity of the global map. -/
def rawMap (src dst : E → V) : RawDomain V E → EmbeddedReal3 :=
  Sum.elim (fun p : RawVertex V => momentCurve (vp (p.1)))
    (fun q : RawInterval E => edgePath src dst q.1 q.2)

theorem rawMap_continuous (src dst : E → V) : Continuous (rawMap src dst) := by
  rw [rawMap, continuous_sumElim]
  constructor
  · apply continuous_sigma
    intro w
    change Continuous (fun _ : Unit => momentCurve (vp w))
    exact continuous_const
  · apply continuous_sigma
    intro e
    change Continuous (fun t : I => edgePath src dst e t)
    exact (edgePath src dst e).continuous

theorem globalMap_comp_glue (src dst : E → V) :
    globalMap src dst ∘ glue src dst = rawMap src dst := by
  funext x
  cases x with
  | inl p =>
      obtain ⟨w, u⟩ := p
      rw [Function.comp_apply, glue_inl]
      rfl
  | inr q =>
      obtain ⟨e, t⟩ := q
      by_cases h0 : t = 0
      · subst h0
        rw [Function.comp_apply, glue_inr, glueInterval_zero]
        change globalMap src dst (Realization.vertex (src e)) = edgePath src dst e 0
        rw [globalMap_vertex, edgePath_zero]
      · by_cases h1 : t = 1
        · subst h1
          rw [Function.comp_apply, glue_inr, glueInterval_one]
          change globalMap src dst (Realization.vertex (dst e)) = edgePath src dst e 1
          rw [globalMap_vertex, edgePath_one]
        · rw [Function.comp_apply, glue_inr, glueInterval_interior src dst e t h0 h1]
          rfl

theorem globalMap_continuous (src dst : E → V) : Continuous (globalMap src dst) := by
  rw [continuous_iff_continuous_comp_glue src dst (globalMap src dst)]
  rw [globalMap_comp_glue]
  exact rawMap_continuous src dst

/-! ## Injectivity of the global map -/

/-- A vertex point is never the image of an interior edge parameter. -/
theorem globalMap_vertex_ne_interior (src dst : E → V) (w : V) (e : E)
    (t : {t : I // t ≠ 0 ∧ t ≠ 1}) :
    globalMap src dst (Realization.vertex w) ≠
      globalMap src dst (Realization.interior e t) := by
  intro h
  by_cases ht : (t.1 : ℝ) ≤ 1 / 2
  · rw [globalMap_vertex, globalMap_interior_of_le src dst e t ht] at h
    have hab : vp (src e) ≠ ep e := labelParam_inl_ne_inr (src e) e
    rcases lineMap_momentCurve_eq_point hab h.symm with ⟨hu, _⟩ | ⟨_, hcb⟩
    · have hz : (t.1 : ℝ) = 0 := by linarith
      exact interior_val_ne_zero t hz
    · exact Sum.inl_ne_inr (labelParam_injective hcb)
  · rw [globalMap_vertex, globalMap_interior_of_gt src dst e t ht] at h
    have hbd : ep e ≠ vp (dst e) := labelParam_inr_ne_inl e (dst e)
    rcases lineMap_momentCurve_eq_point hbd h.symm with ⟨hu, _⟩ | ⟨hu, _⟩
    · have hz : (t.1 : ℝ) = 1 / 2 := by linarith
      exact ht (le_of_eq hz)
    · have ho : (t.1 : ℝ) = 1 := by linarith
      exact interior_val_ne_one t ho

/-- Two interior points on the first halves of the same edge polyline coincide only when they are
the same normal form. -/
theorem interior_eq_of_both_le (src dst : E → V) {e f : E}
    {t s : {t : I // t ≠ 0 ∧ t ≠ 1}}
    (ht : (t.1 : ℝ) ≤ 1 / 2) (hs : (s.1 : ℝ) ≤ 1 / 2)
    (h : edgePath src dst e t.1 = edgePath src dst f s.1) :
    (Realization.interior (src := src) (dst := dst) e t) =
      Realization.interior (src := src) (dst := dst) f s := by
  rw [edgePath_apply, if_pos ht, edgePath_apply, if_pos hs] at h
  by_cases hef : e = f
  · subst hef
    have hcoord : (1 - 2 * (t.1 : ℝ)) * vp (src e) + (2 * (t.1 : ℝ)) * ep e =
        (1 - 2 * (s.1 : ℝ)) * vp (src e) + (2 * (s.1 : ℝ)) * ep e := by
      have hc := congrArg (fun x : EmbeddedReal3 => x 0) h
      simp only at hc
      rw [lineMap_momentCurve_coord_zero, lineMap_momentCurve_coord_zero] at hc
      exact hc
    have hfac : (2 * (t.1 : ℝ) - 2 * (s.1 : ℝ)) * (ep e - vp (src e)) = 0 := by
      linear_combination hcoord
    have hne' : ep e - vp (src e) ≠ 0 :=
      sub_ne_zero.mpr (labelParam_inl_ne_inr (src e) e).symm
    have huv : 2 * (t.1 : ℝ) = 2 * (s.1 : ℝ) := by
      have hsub : 2 * (t.1 : ℝ) - 2 * (s.1 : ℝ) = 0 := by
        rcases mul_eq_zero.mp hfac with h | h
        · exact h
        · exact absurd h hne'
      linarith
    have hts : t = s := by
      apply Subtype.ext
      apply Subtype.ext
      linarith
    subst hts
    rfl
  · exfalso
    by_cases hshared : vp (src e) = vp (src f)
    · have h' : lineMap (momentCurve (vp (src e))) (momentCurve (ep e)) (2 * (t.1 : ℝ)) =
          lineMap (momentCurve (vp (src e))) (momentCurve (ep f)) (2 * (s.1 : ℝ)) := by
        simpa [hshared.symm] using h
      have h1 : vp (src e) ≠ ep e := labelParam_inl_ne_inr (src e) e
      have h2 : vp (src e) ≠ ep f := labelParam_inl_ne_inr (src e) f
      have h3 : ep e ≠ ep f := by
        intro hh
        exact hef ((labelParam_inr_inj).mp hh)
      obtain ⟨hu, _⟩ := lineMap_momentCurve_shared_first h1 h2 h3 h'
      have hz : (t.1 : ℝ) = 0 := by linarith
      exact interior_val_ne_zero t hz
    · have hab : vp (src e) ≠ ep e := labelParam_inl_ne_inr (src e) e
      have hac : vp (src e) ≠ vp (src f) := hshared
      have had : vp (src e) ≠ ep f := labelParam_inl_ne_inr (src e) f
      have hbc : ep e ≠ vp (src f) := labelParam_inr_ne_inl e (src f)
      have hbd : ep e ≠ ep f := by
        intro hh
        exact hef ((labelParam_inr_inj).mp hh)
      have hcd : vp (src f) ≠ ep f := labelParam_inl_ne_inr (src f) f
      exact lineMap_momentCurve_disjoint hab hac had hbc hbd hcd h

/-- Two interior points on the second halves of the same edge polyline coincide only when they
are the same normal form. -/
theorem interior_eq_of_both_gt (src dst : E → V) {e f : E}
    {t s : {t : I // t ≠ 0 ∧ t ≠ 1}}
    (ht : ¬ (t.1 : ℝ) ≤ 1 / 2) (hs : ¬ (s.1 : ℝ) ≤ 1 / 2)
    (h : edgePath src dst e t.1 = edgePath src dst f s.1) :
    (Realization.interior (src := src) (dst := dst) e t) =
      Realization.interior (src := src) (dst := dst) f s := by
  rw [edgePath_apply, if_neg ht, edgePath_apply, if_neg hs] at h
  by_cases hef : e = f
  · subst hef
    have hcoord : (1 - (2 * (t.1 : ℝ) - 1)) * ep e + (2 * (t.1 : ℝ) - 1) * vp (dst e) =
        (1 - (2 * (s.1 : ℝ) - 1)) * ep e + (2 * (s.1 : ℝ) - 1) * vp (dst e) := by
      have hc := congrArg (fun x : EmbeddedReal3 => x 0) h
      simp only at hc
      rw [lineMap_momentCurve_coord_zero, lineMap_momentCurve_coord_zero] at hc
      exact hc
    have hfac : (2 * (t.1 : ℝ) - 1 - (2 * (s.1 : ℝ) - 1)) * (vp (dst e) - ep e) = 0 := by
      linear_combination hcoord
    have hne' : vp (dst e) - ep e ≠ 0 :=
      sub_ne_zero.mpr (labelParam_inr_ne_inl e (dst e)).symm
    have huv : 2 * (t.1 : ℝ) - 1 = 2 * (s.1 : ℝ) - 1 := by
      have hsub : 2 * (t.1 : ℝ) - 1 - (2 * (s.1 : ℝ) - 1) = 0 := by
        rcases mul_eq_zero.mp hfac with h | h
        · exact h
        · exact absurd h hne'
      linarith
    have hts : t = s := by
      apply Subtype.ext
      apply Subtype.ext
      linarith
    subst hts
    rfl
  · exfalso
    by_cases hshared : vp (dst e) = vp (dst f)
    · have h' : lineMap (momentCurve (ep e)) (momentCurve (vp (dst e)))
          (2 * (t.1 : ℝ) - 1) =
          lineMap (momentCurve (ep f)) (momentCurve (vp (dst e))) (2 * (s.1 : ℝ) - 1) := by
        simpa [hshared.symm] using h
      have h1 : ep e ≠ vp (dst e) := labelParam_inr_ne_inl e (dst e)
      have h2 : ep e ≠ ep f := by
        intro hh
        exact hef ((labelParam_inr_inj).mp hh)
      have h3 : vp (dst e) ≠ ep f := labelParam_inl_ne_inr (dst e) f
      obtain ⟨hu, _⟩ := lineMap_momentCurve_shared_second h1 h2 h3 h'
      have ho : (t.1 : ℝ) = 1 := by linarith
      exact interior_val_ne_one t ho
    · have hab : ep e ≠ vp (dst e) := labelParam_inr_ne_inl e (dst e)
      have hac : ep e ≠ ep f := by
        intro hh
        exact hef ((labelParam_inr_inj).mp hh)
      have had : ep e ≠ vp (dst f) := labelParam_inr_ne_inl e (dst f)
      have hbc : vp (dst e) ≠ ep f := labelParam_inl_ne_inr (dst e) f
      have hbd : vp (dst e) ≠ vp (dst f) := hshared
      have hcd : ep f ≠ vp (dst f) := labelParam_inr_ne_inl f (dst f)
      exact lineMap_momentCurve_disjoint hab hac had hbc hbd hcd h

/-- Interior points from the two different halves of edge polylines never coincide. -/
theorem interior_absurd_of_mixed (src dst : E → V) (noLoops : ∀ e, src e ≠ dst e)
    {e f : E} {t s : {t : I // t ≠ 0 ∧ t ≠ 1}}
    (ht : (t.1 : ℝ) ≤ 1 / 2) (hs : ¬ (s.1 : ℝ) ≤ 1 / 2)
    (h : edgePath src dst e t.1 = edgePath src dst f s.1) : False := by
  rw [edgePath_apply, if_pos ht, edgePath_apply, if_neg hs] at h
  by_cases hef : e = f
  · subst hef
    have hab : vp (src e) ≠ ep e := labelParam_inl_ne_inr (src e) e
    have hac : vp (src e) ≠ vp (dst e) := by
      intro hh
      exact noLoops e (Sum.inl_injective (labelParam_injective hh))
    have hbc : ep e ≠ vp (dst e) := labelParam_inr_ne_inl e (dst e)
    obtain ⟨_, hv⟩ := lineMap_momentCurve_shared_mid hab hac hbc h
    have hsval : (s.1 : ℝ) = 1 / 2 := by linarith
    exact hs (le_of_eq hsval)
  · by_cases hshared : vp (src e) = vp (dst f)
    · have h' : lineMap (momentCurve (vp (dst f))) (momentCurve (ep e)) (2 * (t.1 : ℝ)) =
          lineMap (momentCurve (ep f)) (momentCurve (vp (dst f))) (2 * (s.1 : ℝ) - 1) := by
        simpa [hshared] using h
      have hab : vp (dst f) ≠ ep e := labelParam_inl_ne_inr (dst f) e
      have hac : vp (dst f) ≠ ep f := labelParam_inl_ne_inr (dst f) f
      have hbc : ep e ≠ ep f := by
        intro hh
        exact hef ((labelParam_inr_inj).mp hh)
      obtain ⟨hu, _⟩ := lineMap_momentCurve_shared_last hab hac hbc h'
      have hz : (t.1 : ℝ) = 0 := by linarith
      exact interior_val_ne_zero t hz
    · have hab : vp (src e) ≠ ep e := labelParam_inl_ne_inr (src e) e
      have hac : vp (src e) ≠ ep f := labelParam_inl_ne_inr (src e) f
      have had : vp (src e) ≠ vp (dst f) := hshared
      have hbc : ep e ≠ ep f := by
        intro hh
        exact hef ((labelParam_inr_inj).mp hh)
      have hbd : ep e ≠ vp (dst f) := labelParam_inr_ne_inl e (dst f)
      have hcd : ep f ≠ vp (dst f) := labelParam_inr_ne_inl f (dst f)
      exact lineMap_momentCurve_disjoint hab hac had hbc hbd hcd h

/-- The global map is injective for a loopless multigraph. -/
theorem globalMap_injective (src dst : E → V) (noLoops : ∀ e, src e ≠ dst e) :
    Function.Injective (globalMap src dst) := by
  intro x y h
  cases x with
  | vertex w =>
      cases y with
      | vertex w' =>
          have h' : momentCurve (vp w) = momentCurve (vp w') := by
            simpa using h
          have hparam : vp w = vp w' := momentCurve_injective h'
          have hsum : (Sum.inl w : V ⊕ E) = Sum.inl w' := labelParam_injective hparam
          have hww : w = w' := Sum.inl_injective hsum
          subst hww
          rfl
      | interior e t =>
          exact absurd h (globalMap_vertex_ne_interior src dst w e t)
  | interior e t =>
      cases y with
      | vertex w =>
          exact absurd h.symm (globalMap_vertex_ne_interior src dst w e t)
      | interior f s =>
          have h' : edgePath src dst e t.1 = edgePath src dst f s.1 := h
          by_cases ht : (t.1 : ℝ) ≤ 1 / 2
          · by_cases hs : (s.1 : ℝ) ≤ 1 / 2
            · exact interior_eq_of_both_le src dst ht hs h'
            · exact (interior_absurd_of_mixed src dst noLoops ht hs h').elim
          · by_cases hs : (s.1 : ℝ) ≤ 1 / 2
            · exact (interior_absurd_of_mixed src dst noLoops hs ht h'.symm).elim
            · exact interior_eq_of_both_gt src dst ht hs h'

/-! ## The existence theorem -/

/-- **Structural existence of a global embedded-graph realization.**  Every finite loopless
multigraph, with arbitrary endpoint maps `src dst : E → V`, parallel edges and disconnected
components included, admits an `EmbeddedGraph src dst`: one global continuous injective map of
its topological realization into real three-space.  No global map, arc family or local
geometric law is supplied as an input. -/
def finiteGraphEmbedded (src dst : E → V) (noLoops : ∀ e, src e ≠ dst e) :
    EmbeddedGraph src dst where
  map := ⟨globalMap src dst, globalMap_continuous src dst⟩
  injective := globalMap_injective src dst noLoops

/-- The global continuous map underlying `finiteGraphEmbedded`. -/
theorem finiteGraphEmbedded_map (src dst : E → V) (noLoops : ∀ e, src e ≠ dst e) :
    (finiteGraphEmbedded src dst noLoops).map = ⟨globalMap src dst, globalMap_continuous src dst⟩ :=
  rfl

/-- The conformation of `finiteGraphEmbedded` is the moment-curve image of the vertex label. -/
@[simp] theorem finiteGraphEmbedded_conformation (src dst : E → V)
    (noLoops : ∀ e, src e ≠ dst e) (w : V) :
    (finiteGraphEmbedded src dst noLoops).conformation w = momentCurve (vp w) := rfl

/-- Every atomic position of `finiteGraphEmbedded` is distinct. -/
theorem finiteGraphEmbedded_atom_injective (src dst : E → V)
    (noLoops : ∀ e, src e ≠ dst e) :
    Function.Injective (finiteGraphEmbedded src dst noLoops).conformation :=
  (finiteGraphEmbedded src dst noLoops).atom_injective

/-- Every edge arc of `finiteGraphEmbedded` is injective on the unit interval. -/
theorem finiteGraphEmbedded_arc_injective (src dst : E → V)
    (noLoops : ∀ e, src e ≠ dst e) (e : E) :
    Function.Injective ((finiteGraphEmbedded src dst noLoops).arc e) :=
  (finiteGraphEmbedded src dst noLoops).arc_injective_of_noSelfLoops noLoops e

/-- Distinct edge arcs of `finiteGraphEmbedded` meet only at a common endpoint atom. -/
theorem finiteGraphEmbedded_intersects_only_at_common_endpoints (src dst : E → V)
    (noLoops : ∀ e, src e ≠ dst e) {e f : E} {t s : I} (hne : e ≠ f)
    (h : (finiteGraphEmbedded src dst noLoops).arc e t =
      (finiteGraphEmbedded src dst noLoops).arc f s) :
    ∃ atom : V,
      sourceEndpointAt? src dst e t = some atom ∧
        sourceEndpointAt? src dst f s = some atom :=
  (finiteGraphEmbedded src dst noLoops).intersects_only_at_common_endpoints e f t s hne h

end Parameters

end

end OrganicStereoFiniteGraphEmbedding
end TetraStereo.OneCenter
