import TetraStereo.OneCenter.OrganicStereoMomentCurveSeparation
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Finite affine-plane avoidance in real three-space

This module provides the reusable geometric core needed to place *prescribed* atom positions in
`EmbeddedReal3 = EuclideanSpace ℝ (Fin 3)` while drawing a finite family of straight segments.
The central result is that finitely many affine planes can be avoided by a single point: for every
list of affine planes with nonzero normal there is a point of real three-space that lies on none of
them.

## Construction

An affine plane is represented by a nonzero normal vector `normal : Fin 3 → ℝ` and a real
`offset`; the plane is the solution set of `∑ i, normal i * p i = offset`.  Since the normal is
nonzero, such a set is a genuine proper affine plane (it never fills all of space).

The avoidance theorem evaluates the real moment curve `t ↦ (t, t², t³)` of
`OrganicStereoMomentCurveSeparation` in the plane equation.  Substitution turns the plane equation
into a polynomial in `t` of degree at most three whose coefficients are exactly the three normal
coordinates; because the normal is nonzero the polynomial is nonzero, hence it has only finitely
many real roots.  A finite list of planes therefore excludes only finitely many moment-curve
parameters, and since `ℝ` is infinite some parameter remains.  No compactness, measure, or
generic-position hypothesis is used, and no nonemptiness of the complement is assumed.

## Main results

* `AffinePlane.contains` : membership in an affine plane;
* `AffinePlane.planePolynomial` / `AffinePlane.eval_planePolynomial` : the cubic obtained by
  restricting a plane to the moment curve;
* `AffinePlane.finite_contains_momentCurve` : a single plane meets the moment curve in finitely
  many parameters;
* `finite_setOf_exists_contains` : a finite list of planes meets the moment curve in finitely many
  parameters;
* `avoid_finite_planes` : **the main theorem** — a finite list of affine planes admits a common
  avoiding point in `EmbeddedReal3`;
* `exists_affinePlane_through_three` : any three points of `ℝ³` (possibly coincident or
  collinear) lie in some affine plane; the plane is automatically proper;
* `AffinePlane.exists_not_contains` : every affine plane is proper;
* `AffinePlane.contains_lineMap` : the affine segment between two contained points stays in the
  plane;
* `AffinePlane.contains_of_collision` : if a segment from `s` to `p` meets an old segment from
  `a` to `b` at a point of the new segment with nonzero parameter `t ≠ 0`, then `p` lies in every
  affine plane containing `s`, `a`, and `b`.  This is the atomic collision-avoidance step for
  prescribed-position graph embedding.

## Scope and boundaries

Nothing here is assumed: all statements are proved in the kernel from Mathlib and the
repository's existing `EmbeddedReal3` type.  This module makes no claim about chemical
realizability, molecular bonds, knot invariants, or the existence of a global embedding of any
particular graph.  The companion prescribed-position construction is responsible for turning
these local avoidance and collision laws into a global placement.
-/

namespace TetraStereo.OneCenter
namespace OrganicStereoFiniteAffinePlaneAvoidance

open scoped unitInterval
open OrganicStereoMomentCurveSeparation

noncomputable section

/-! ## Affine planes and membership -/

/-- An affine plane of real three-space, represented by a nonzero normal vector and an offset.

The represented set is `{p | ∑ i, normal i * p i = offset}`.  The field `normal_ne_zero` is what
makes the plane *proper*: a nonzero normal cannot vanish on all of space. -/
structure AffinePlane where
  /-- A nonzero normal vector to the plane. -/
  normal : Fin 3 → ℝ
  /-- The offset of the plane along its normal. -/
  offset : ℝ
  /-- The normal vector is nonzero. -/
  normal_ne_zero : normal ≠ 0

namespace AffinePlane

/-- Membership in an affine plane: the normal dot product with the point equals the offset. -/
def contains (P : AffinePlane) (p : EmbeddedReal3) : Prop :=
  (∑ i : Fin 3, P.normal i * p i) = P.offset

/-- Unfolding lemma for `contains`. -/
theorem contains_def (P : AffinePlane) (p : EmbeddedReal3) :
    P.contains p ↔ (∑ i : Fin 3, P.normal i * p i) = P.offset :=
  Iff.rfl

/-- An affine plane never contains all of space: it is a proper subset of `EmbeddedReal3`.

Choose the coordinate `i` on which the nonzero normal does not vanish and move the `i`-th
coordinate one unit beyond the plane. -/
theorem exists_not_contains (P : AffinePlane) : ∃ p : EmbeddedReal3, ¬ P.contains p := by
  have hnormal : ∃ i : Fin 3, P.normal i ≠ 0 := by
    by_contra h
    push_neg at h
    exact P.normal_ne_zero (funext h)
  obtain ⟨i, hi⟩ := hnormal
  let p : EmbeddedReal3 := EuclideanSpace.single i ((P.offset + 1) / P.normal i)
  refine ⟨p, ?_⟩
  intro hcontains
  have hsum : (∑ j : Fin 3, P.normal j * p j) = P.offset + 1 := by
    rw [Finset.sum_eq_single i]
    · simp only [p, EuclideanSpace.single_apply, if_true]
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ hi]
    · intro j _ hji
      simp [p, hji]
    · intro hi_not_mem
      exact absurd (Finset.mem_univ i) hi_not_mem
  rw [contains_def] at hcontains
  rw [hsum] at hcontains
  linarith

/-! ## The plane equation restricted to the moment curve -/

/-- The polynomial in the moment-curve parameter `t` obtained by substituting the moment curve
`t ↦ (t, t², t³)` into the plane equation.  Its coefficients are the three normal coordinates,
and its constant term is `-offset`. -/
def planePolynomial (P : AffinePlane) : Polynomial ℝ :=
  Polynomial.C (P.normal 0) * Polynomial.X +
    Polynomial.C (P.normal 1) * Polynomial.X ^ 2 +
      Polynomial.C (P.normal 2) * Polynomial.X ^ 3 - Polynomial.C P.offset

/-- Evaluation of the restricted plane polynomial at `t` is the plane's left-hand side at
`momentCurve t`, minus the offset. -/
theorem eval_planePolynomial (P : AffinePlane) (t : ℝ) :
    (planePolynomial P).eval t =
      (∑ i : Fin 3, P.normal i * momentCurve t i) - P.offset := by
  simp [planePolynomial, Fin.sum_univ_three]

/-- The restricted plane polynomial is nonzero: the coefficient of `X ^ (i + 1)` is the `i`-th
coordinate of the nonzero normal vector. -/
theorem planePolynomial_ne_zero (P : AffinePlane) : planePolynomial P ≠ 0 := by
  intro h
  apply P.normal_ne_zero
  funext i
  fin_cases i
  · have hc := congrArg (fun q : Polynomial ℝ => q.coeff 1) h
    simpa [planePolynomial] using hc
  · have hc := congrArg (fun q : Polynomial ℝ => q.coeff 2) h
    simpa [planePolynomial] using hc
  · have hc := congrArg (fun q : Polynomial ℝ => q.coeff 3) h
    simpa [planePolynomial] using hc

/-- A single affine plane meets the moment curve in only finitely many parameters. -/
theorem finite_contains_momentCurve (P : AffinePlane) :
    Set.Finite {t : ℝ | P.contains (momentCurve t)} := by
  have hroots := Polynomial.finite_setOf_isRoot (planePolynomial_ne_zero P)
  refine hroots.subset ?_
  intro t ht
  change (planePolynomial P).IsRoot t
  rw [Polynomial.IsRoot.def, eval_planePolynomial]
  simp only [contains_def] at ht
  rw [ht, sub_self]

end AffinePlane

/-- A finite list of affine planes meets the moment curve in only finitely many parameters.

The proof is an induction on the list: the empty list excludes no parameter, and a cons is the
union of the single plane's finite parameter set with the induction hypothesis. -/
theorem finite_setOf_exists_contains (planes : List AffinePlane) :
    Set.Finite {t : ℝ | ∃ a ∈ planes, a.contains (momentCurve t)} := by
  induction planes with
  | nil =>
      simp
  | cons a as ih =>
      have hset : {t : ℝ | ∃ b ∈ a :: as, b.contains (momentCurve t)} =
          {t : ℝ | a.contains (momentCurve t)} ∪
            {t : ℝ | ∃ b ∈ as, b.contains (momentCurve t)} := by
        ext t
        simp only [List.mem_cons, Set.mem_setOf_eq, Set.mem_union]
        constructor
        · rintro ⟨b, rfl | hb, hbt⟩
          · exact Or.inl hbt
          · exact Or.inr ⟨b, hb, hbt⟩
        · rintro (h | ⟨b, hb, hbt⟩)
          · exact ⟨a, Or.inl rfl, h⟩
          · exact ⟨b, Or.inr hb, hbt⟩
      rw [hset]
      exact (AffinePlane.finite_contains_momentCurve a).union ih

/-! ## The avoidance theorem -/

/-- **Finite affine-plane avoidance.**  For every finite list of affine planes there is a point of
real three-space lying on none of them.  The witness is a point of the real moment curve.

No hypotheses are placed on the planes beyond the inherent `normal_ne_zero` field, and no
nonemptiness of a complement is assumed. -/
theorem avoid_finite_planes (planes : List AffinePlane) :
    ∃ p : EmbeddedReal3, ∀ a ∈ planes, ¬ a.contains p := by
  have hfinite := finite_setOf_exists_contains planes
  obtain ⟨t, _htmem, ht⟩ :=
    (Set.infinite_univ (α := ℝ)).exists_notMem_finite hfinite
  refine ⟨momentCurve t, ?_⟩
  intro a ha hcontains
  exact ht ⟨a, ha, hcontains⟩

/-! ## Every three points lie in an affine plane -/

namespace AffinePlane

/-- The linear map recording the two difference vectors from `p` to `q` and from `p` to `r`.
A vector in its kernel is a normal vector orthogonal to both differences, hence a normal to any
affine plane through the three points. -/
def differenceMap (p q r : EmbeddedReal3) : EmbeddedReal3 →ₗ[ℝ] ℝ × ℝ where
  toFun v :=
    (∑ i : Fin 3, (q i - p i) * v i, ∑ i : Fin 3, (r i - p i) * v i)
  map_add' v w := by
    apply Prod.ext
    · simp only [Prod.fst_add, PiLp.add_apply, mul_add, Finset.sum_add_distrib]
    · simp only [Prod.snd_add, PiLp.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    apply Prod.ext
    · simp only [Prod.smul_fst, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum,
        RingHom.id_apply]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · simp only [Prod.smul_snd, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum,
        RingHom.id_apply]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- **Any three points lie in an affine plane**, with no distinctness or non-collinearity
hypothesis: coincident and collinear configurations are included.  The plane is proper because
its normal is nonzero.

The proof is a dimension count.  The codomain `ℝ × ℝ` has dimension two while `ℝ³` has dimension
three, so the kernel of `differenceMap p q r` is nontrivial.  A nonzero kernel vector is a normal
orthogonal to `q - p` and `r - p`; taking the offset to be its pairing with `p` gives a plane
through all three points. -/
theorem exists_affinePlane_through_three (p q r : EmbeddedReal3) :
    ∃ P : AffinePlane, P.contains p ∧ P.contains q ∧ P.contains r := by
  have hdim : Module.finrank ℝ (ℝ × ℝ) < Module.finrank ℝ EmbeddedReal3 := by
    simp
  have hker : LinearMap.ker (differenceMap p q r) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (f := differenceMap p q r) hdim
  obtain ⟨n, hnker, hnne⟩ := (Submodule.ne_bot_iff _).mp hker
  have hn := LinearMap.mem_ker.mp hnker
  have hnq : (∑ i : Fin 3, (q i - p i) * n i) = 0 := by
    simpa [differenceMap] using congrArg Prod.fst hn
  have hnr : (∑ i : Fin 3, (r i - p i) * n i) = 0 := by
    simpa [differenceMap] using congrArg Prod.snd hn
  have hnne' : (fun i : Fin 3 => n i) ≠ 0 := by
    intro h
    apply hnne
    ext i
    simpa using congrFun h i
  have hq : (∑ i : Fin 3, n i * q i) = ∑ i : Fin 3, n i * p i := by
    have hsub : (∑ i : Fin 3, (n i * q i - n i * p i)) = 0 := by
      rw [← hnq]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [Finset.sum_sub_distrib] at hsub
    linarith
  have hr : (∑ i : Fin 3, n i * r i) = ∑ i : Fin 3, n i * p i := by
    have hsub : (∑ i : Fin 3, (n i * r i - n i * p i)) = 0 := by
      rw [← hnr]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [Finset.sum_sub_distrib] at hsub
    linarith
  exact ⟨⟨fun i => n i, ∑ i : Fin 3, n i * p i, hnne'⟩, rfl, hq, hr⟩

/-- The three-point plane is proper: it does not contain every point of space. -/
theorem exists_proper_affinePlane_through_three (p q r : EmbeddedReal3) :
    ∃ P : AffinePlane,
      (P.contains p ∧ P.contains q ∧ P.contains r) ∧ ∃ z : EmbeddedReal3, ¬ P.contains z := by
  obtain ⟨P, hp, hq, hr⟩ := exists_affinePlane_through_three p q r
  exact ⟨P, ⟨hp, hq, hr⟩, P.exists_not_contains⟩

/-! ## Segments between contained points -/

/-- **An affine segment between two points of a plane stays in the plane.**  This is stated for
the bundled linear affine map `AffineMap.lineMap` at an arbitrary real parameter. -/
theorem contains_lineMap (P : AffinePlane) {x y : EmbeddedReal3}
    (hx : P.contains x) (hy : P.contains y) (t : ℝ) :
    P.contains (AffineMap.lineMap x y t) := by
  rw [contains_def] at hx hy ⊢
  rw [AffineMap.lineMap_apply_module]
  have hcoord : ∀ i : Fin 3,
      ((1 - t) • x + t • y : EmbeddedReal3) i = (1 - t) * x i + t * y i := by
    intro i
    simp [smul_eq_mul]
  simp only [hcoord]
  calc
    (∑ i : Fin 3, P.normal i * ((1 - t) * x i + t * y i)) =
        (1 - t) * (∑ i : Fin 3, P.normal i * x i) +
          t * (∑ i : Fin 3, P.normal i * y i) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = P.offset := by
          rw [hx, hy]
          ring

/-- The unit-interval form of `contains_lineMap`: the closed segment between two contained points
stays in the plane. -/
theorem contains_lineMap_unitInterval (P : AffinePlane) {x y : EmbeddedReal3}
    (hx : P.contains x) (hy : P.contains y) (t : I) :
    P.contains (AffineMap.lineMap x y (t : ℝ)) :=
  contains_lineMap P hx hy (t : ℝ)

/-! ## The collision lemma -/

/-- **Atomic collision constraint.**  Suppose the new segment from `s` to `p` meets the old
segment from `a` to `b` at the point `AffineMap.lineMap s p t = AffineMap.lineMap a b u`, with
`t ≠ 0` (so the meeting point is not the pivot `s` whenever `p ≠ s`).  Then `p` lies in *every*
affine plane that contains `s`, `a`, and `b`.

Indeed, the meeting point `q = AffineMap.lineMap s p t` lies in the plane because the old segment
does, and `p = AffineMap.lineMap s q (1 / t)` is on the segment from `s` to `q`, so the segment
closure lemma applies.  No distinctness of `s`, `p`, `a`, `b` is required. -/
theorem contains_of_collision (P : AffinePlane) {s p a b : EmbeddedReal3} {t u : I}
    (hs : P.contains s) (ha : P.contains a) (hb : P.contains b) (ht : t ≠ 0)
    (hmeet : AffineMap.lineMap s p (t : ℝ) = AffineMap.lineMap a b (u : ℝ)) :
    P.contains p := by
  have htR : (t : ℝ) ≠ 0 := fun h => ht (Subtype.ext h)
  have hq : P.contains (AffineMap.lineMap s p (t : ℝ)) := by
    rw [hmeet]
    exact contains_lineMap P ha hb (u : ℝ)
  have hcoef : ∀ a b : ℝ,
      (1 - 1 / (t : ℝ)) * a +
        (1 / (t : ℝ)) * ((1 - (t : ℝ)) * a + (t : ℝ) * b) = b := by
    intro a b
    field_simp [htR]
    ring
  have hp : p = AffineMap.lineMap s (AffineMap.lineMap s p (t : ℝ)) (1 / (t : ℝ)) := by
    ext i
    rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    exact (hcoef (s i) (p i)).symm
  rw [hp]
  exact contains_lineMap P hs hq (1 / (t : ℝ))

/-- Existential-parameter form of `contains_of_collision`: if the new segment meets the old
segment at some point of the new segment with nonzero parameter, then `p` lies in every plane
through `s`, `a`, and `b`. -/
theorem contains_of_collision_exists (P : AffinePlane) {s p a b : EmbeddedReal3}
    (hs : P.contains s) (ha : P.contains a) (hb : P.contains b)
    (hmeet : ∃ (t u : I), t ≠ 0 ∧
      AffineMap.lineMap s p (t : ℝ) = AffineMap.lineMap a b (u : ℝ)) :
    P.contains p := by
  obtain ⟨t, u, ht, htu⟩ := hmeet
  exact contains_of_collision P hs ha hb ht htu

/-- Specialization of `contains_of_collision` to points of the moment curve, expressed with the
`segmentPoint` parametrization of `OrganicStereoMomentCurveSeparation`. -/
theorem contains_of_segmentPoint_collision (P : AffinePlane) {sx px ax bx : ℝ} {t u : I}
    (hs : P.contains (momentCurve sx)) (ha : P.contains (momentCurve ax))
    (hb : P.contains (momentCurve bx)) (ht : t ≠ 0)
    (hmeet : AffineMap.lineMap (momentCurve sx) (momentCurve px) (t : ℝ) =
      AffineMap.lineMap (momentCurve ax) (momentCurve bx) (u : ℝ)) :
    P.contains (momentCurve px) :=
  contains_of_collision P hs ha hb ht hmeet

end AffinePlane

/-! ## Inhabited finite example and kernel assertions -/

/-- Affine planes are inhabited: the plane `x = 0`. -/
instance : Inhabited AffinePlane :=
  ⟨⟨![1, 0, 0], 0, by
    intro h
    have h0 : (1 : ℝ) = 0 := by simpa using congrFun h 0
    norm_num at h0⟩⟩

/-- The coordinate plane `z = 0`. -/
def planeXY : AffinePlane where
  normal := ![0, 0, 1]
  offset := 0
  normal_ne_zero := by
    intro h
    have h2 : (1 : ℝ) = 0 := by simpa using congrFun h 2
    norm_num at h2

/-- The coordinate plane `y = 0`. -/
def planeXZ : AffinePlane where
  normal := ![0, 1, 0]
  offset := 0
  normal_ne_zero := by
    intro h
    have h1 : (1 : ℝ) = 0 := by simpa using congrFun h 1
    norm_num at h1

/-- The coordinate plane `x = 0`. -/
def planeYZ : AffinePlane where
  normal := ![1, 0, 0]
  offset := 0
  normal_ne_zero := by
    intro h
    have h0 : (1 : ℝ) = 0 := by simpa using congrFun h 0
    norm_num at h0

/-- Membership in the plane `z = 0` is vanishing of the third coordinate. -/
theorem planeXY_contains_iff (p : EmbeddedReal3) :
    planeXY.contains p ↔ p 2 = 0 := by
  simp [planeXY, AffinePlane.contains, Fin.sum_univ_three]

/-- Membership in the plane `y = 0` is vanishing of the second coordinate. -/
theorem planeXZ_contains_iff (p : EmbeddedReal3) :
    planeXZ.contains p ↔ p 1 = 0 := by
  simp [planeXZ, AffinePlane.contains, Fin.sum_univ_three]

/-- Membership in the plane `x = 0` is vanishing of the first coordinate. -/
theorem planeYZ_contains_iff (p : EmbeddedReal3) :
    planeYZ.contains p ↔ p 0 = 0 := by
  simp [planeYZ, AffinePlane.contains, Fin.sum_univ_three]

/-- The moment-curve point `(1, 1, 1)` avoids the plane `z = 0`. -/
theorem planeXY_not_contains_momentCurve_one :
    ¬ planeXY.contains (momentCurve 1) := by
  rw [planeXY_contains_iff]
  simp [momentCurve]

/-- The moment-curve point `(1, 1, 1)` avoids the plane `y = 0`. -/
theorem planeXZ_not_contains_momentCurve_one :
    ¬ planeXZ.contains (momentCurve 1) := by
  rw [planeXZ_contains_iff]
  simp [momentCurve]

/-- The moment-curve point `(1, 1, 1)` avoids the plane `x = 0`. -/
theorem planeYZ_not_contains_momentCurve_one :
    ¬ planeYZ.contains (momentCurve 1) := by
  rw [planeYZ_contains_iff]
  simp [momentCurve]

/-- The moment-curve point `(1, 1, 1)` avoids the three coordinate planes. -/
theorem coordinatePlanes_avoid_momentCurve_one :
    ∀ a ∈ [planeXY, planeXZ, planeYZ], ¬ a.contains (momentCurve 1) := by
  intro a ha
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact planeXY_not_contains_momentCurve_one
  · exact planeXZ_not_contains_momentCurve_one
  · exact planeYZ_not_contains_momentCurve_one

/-- Kernel assertion: the main avoidance theorem has the requested type. -/
example (planes : List AffinePlane) :
    ∃ p : EmbeddedReal3, ∀ a ∈ planes, ¬ a.contains p :=
  avoid_finite_planes planes

/-- Kernel assertion: the three-point plane theorem has the requested type. -/
example (p q r : EmbeddedReal3) :
    ∃ P : AffinePlane, P.contains p ∧ P.contains q ∧ P.contains r :=
  AffinePlane.exists_affinePlane_through_three p q r

/-- Kernel assertion: the collision lemma has the requested type. -/
example (P : AffinePlane) (s p a b : EmbeddedReal3) (t u : I)
    (hs : P.contains s) (ha : P.contains a) (hb : P.contains b) (ht : t ≠ 0)
    (hmeet : AffineMap.lineMap s p (t : ℝ) = AffineMap.lineMap a b (u : ℝ)) :
    P.contains p :=
  AffinePlane.contains_of_collision P hs ha hb ht hmeet

/-- Kernel assertion: finitely many coordinate planes are avoided by an explicit point. -/
example : ∃ p : EmbeddedReal3,
    ∀ a ∈ [planeXY, planeXZ, planeYZ], ¬ a.contains p :=
  ⟨momentCurve 1, coordinatePlanes_avoid_momentCurve_one⟩

/-! ## Summary of the public API -/

#check @AffinePlane
#check @AffinePlane.contains
#check @AffinePlane.exists_not_contains
#check @AffinePlane.planePolynomial
#check @AffinePlane.eval_planePolynomial
#check @AffinePlane.finite_contains_momentCurve
#check @finite_setOf_exists_contains
#check @avoid_finite_planes
#check @AffinePlane.differenceMap
#check @AffinePlane.exists_affinePlane_through_three
#check @AffinePlane.exists_proper_affinePlane_through_three
#check @AffinePlane.contains_lineMap
#check @AffinePlane.contains_lineMap_unitInterval
#check @AffinePlane.contains_of_collision
#check @AffinePlane.contains_of_collision_exists
#check @AffinePlane.contains_of_segmentPoint_collision

end

end OrganicStereoFiniteAffinePlaneAvoidance
end TetraStereo.OneCenter
