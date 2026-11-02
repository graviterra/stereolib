import TetraStereo.OneCenter.OrganicStereoIndependentPathEncoding
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order

set_option autoImplicit false

/-!
# Finite multigraph topological realization and global embedded-graph laws

This module supplies the missing *topological* layer between an abstract finite multigraph and
the local embedded-bond-path laws used elsewhere in the repository.  Its input is only

* an arbitrary vertex type `V` and an arbitrary edge type `E` (no finiteness, no `Fintype`, no
  global edge count bound);
* two endpoint maps `src dst : E → V`.

No topology is assumed on `V` or `E`, and no bond-path table, arc family, coverage hypothesis or
other local validity data is an input.  Every local law is *derived* from one supplied global
continuous injective map into real three-space.

## Construction

`Realization src dst` is the graph-indexed normal form of the realization:

* `Realization.vertex v` for `v : V`;
* `Realization.interior e t` for an edge `e : E` and an interior parameter
  `t : {t : I // t ≠ 0 ∧ t ≠ 1}`.

The source and destination maps stay as type parameters of `Realization`; the topology is not
obtained by erasing them.  Self-loops (`src e = dst e`) are permitted by the normal form: they
merely fail the conditional interval-injectivity law, whose statement records that failure.

The raw domain is the coproduct

`(Σ _ : V, Unit) ⊕ (Σ _ : E, I)`

with the coproduct (sum) topology of the Sigma topologies.  The Sigma topology on
`Σ _ : V, Unit` only needs the topology of the fibre `Unit`, and likewise the Sigma topology on
`Σ _ : E, I` only needs the topology of `I`; hence no topology instance on `V` or `E` is
required.  The gluing map `glue` sends a raw vertex slot to that vertex, a raw interval parameter
`0` to the source vertex, `1` to the destination vertex, and every interior parameter to the
corresponding `Realization.interior`.  This is a genuine map (not a setoid quotient), and it is
surjective.

The topology on `Realization src dst` is *definitionally* the coinduced topology
`TopologicalSpace.coinduced (glue src dst)` of the raw coproduct topology.  Consequently the
universal property `Continuous f ↔ Continuous (f ∘ glue)` is `continuous_coinduced_dom`, and the
interval map `edgePoint src dst e` is continuous because it is `glue` composed with the continuous
Sigma/coproduct inclusion.

## Global embedding and derived local laws

`EmbeddedGraph src dst` is a *supplied classical global embedding*: one continuous injective map
`map : C(Realization src dst, EmbeddedReal3)`.  From it we derive, with no further geometric
input:

* `conformation : V → EmbeddedReal3` (the image of the vertex normal forms);
* `arc : E → C(I, EmbeddedReal3)` (the image of the interval edge maps);
* `arc_zero` / `arc_one`: the arc endpoints are the endpoint atom positions;
* `atom_injective`: distinct atoms have distinct positions;
* `arc_injective`: for `src e ≠ dst e`, each arc is injective on `I`;
* `interior_avoids_atoms`: an arc at an interior parameter is never an atom position;
* `intersects_only_at_common_endpoints`: two distinct edge arcs meet only at an atom which is an
  endpoint of both, stated through the shared `sourceEndpointAt?` lookup;
* `edge_eq_of_interior_meet`: two arcs meeting at interior parameters come from the same edge, so
  edge identity, including parallel edges with the same endpoints, is preserved.

The exact collision forms are also exposed as

* `edgePoint_eq_vertex_iff`, and
* `edgePoint_eq_iff`,

the latter valid even for self-loops (the common-endpoint disjunct covers them).

Each individual edge is an interval with two distinct endpoint vertices (when `src e ≠ dst e`), so
a molecular ring is necessarily a cycle of several edges; it is never represented by a self-loop
edge.  `NoSelfLoops` records the per-edge condition and the self-loop failure of injectivity is
proved (`not_edgePoint_injective_of_selfLoop`).

A concrete inhabited single-edge example in `ℝ³` is built (`toyEmbeddedGraph`) from an explicitly
global continuous map, using the coinduced universal property rather than any local construction.

## Scope

This module proves realization *from a supplied global classical embedding*.  It does not
classify knots or links, does not construct an embedding for an arbitrary molecule, and does not
prove that every physically admissible molecule has such a model.  The chemical bridge that turns
selected source pair-bond occurrences into path data is a separate module.
-/

namespace TetraStereo.OneCenter
namespace OrganicStereoEmbeddedGraphRealization

open scoped unitInterval

noncomputable section

universe u v

variable {V : Type u} {E : Type v}

/-! ## The graph-indexed normal form -/

/-- The normal form of the topological realization of a finite multigraph with endpoint maps
`src dst : E → V`.

Vertices are the vertex normal forms.  Each edge contributes one open interval of interior
parameters, indexed by the actual edge label `e : E`.  The endpoint maps remain parameters of the
type, so the topology below never depends on an erased endpoint assignment. -/
inductive Realization (src dst : E → V) : Type (max u v) where
  /-- A vertex of the graph. -/
  | vertex (v : V) : Realization src dst
  /-- A point in the interior of the edge `e`, parametrized by an element of `I` which is
  neither `0` nor `1`. -/
  | interior (e : E) (t : {t : I // t ≠ 0 ∧ t ≠ 1}) : Realization src dst

/-- The vertex normal-form map, exposed as a function for downstream use. -/
abbrev vertex {src dst : E → V} (v : V) : Realization src dst :=
  Realization.vertex v

/-- The raw vertex slots before gluing: a vertex label together with a trivial fibre.  No topology
on `V` is involved; the Sigma topology only uses the topology of `Unit`. -/
abbrev RawVertex (V : Type u) : Type u :=
  Σ _ : V, Unit

/-- The raw interval slots before gluing: an edge label together with a unit-interval parameter.
No topology on `E` is involved; the Sigma topology only uses the topology of `I`. -/
abbrev RawInterval (E : Type v) : Type v :=
  Σ _ : E, I

/-- The raw domain of the realization: coproduct of raw vertex slots and raw interval slots. -/
abbrev RawDomain (V : Type u) (E : Type v) : Type (max u v) :=
  RawVertex V ⊕ RawInterval E

/-- The interval part of the gluing map.  It sends the parameters `0` and `1` to the source and
destination vertices and every interior parameter to an interior normal form. -/
def glueInterval (src dst : E → V) (e : E) (t : I) : Realization src dst :=
  if h0 : t = 0 then Realization.vertex (src e)
  else if h1 : t = 1 then Realization.vertex (dst e)
  else Realization.interior e ⟨t, h0, h1⟩

/-- The gluing map from the raw coproduct domain onto the graph-indexed normal form. -/
def glue (src dst : E → V) : RawDomain V E → Realization src dst
  | Sum.inl p => Realization.vertex p.1
  | Sum.inr q => glueInterval src dst q.1 q.2

@[simp] theorem glue_inl (src dst : E → V) (v : V) (u : Unit) :
    glue src dst (Sum.inl (⟨v, u⟩ : RawVertex V)) = Realization.vertex v := rfl

@[simp] theorem glue_inr (src dst : E → V) (e : E) (t : I) :
    glue src dst (Sum.inr (⟨e, t⟩ : RawInterval E)) = glueInterval src dst e t := rfl

@[simp] theorem glueInterval_zero (src dst : E → V) (e : E) :
    glueInterval src dst e 0 = Realization.vertex (src e) := by
  unfold glueInterval
  rw [dif_pos rfl]

@[simp] theorem glueInterval_one (src dst : E → V) (e : E) :
    glueInterval src dst e 1 = Realization.vertex (dst e) := by
  unfold glueInterval
  rw [dif_neg (one_ne_zero : (1 : I) ≠ 0), dif_pos rfl]

theorem glueInterval_interior (src dst : E → V) (e : E) (t : I)
    (h0 : t ≠ 0) (h1 : t ≠ 1) :
    glueInterval src dst e t = Realization.interior e ⟨t, h0, h1⟩ := by
  unfold glueInterval
  rw [dif_neg h0, dif_neg h1]

/-! ## The coinduced topology -/

/-- The topology on the realization is the coinduced topology of `glue` from the raw coproduct.
It is defined, not a reducible alias, and it keeps the endpoint maps in the type. -/
noncomputable instance realizationTopologicalSpace (src dst : E → V) :
    TopologicalSpace (Realization src dst) :=
  TopologicalSpace.coinduced (glue src dst) inferInstance

/-- The gluing map is continuous for the coinduced topology. -/
theorem glue_continuous (src dst : E → V) : Continuous (glue src dst) :=
  continuous_coinduced_rng

/-- The defining universal property of the realization topology: a map out of the realization is
continuous if and only if its precomposition with the gluing map is continuous on the raw
coproduct. -/
theorem continuous_iff_continuous_comp_glue (src dst : E → V) {X : Type*} [TopologicalSpace X]
    (f : Realization src dst → X) :
    Continuous f ↔ Continuous (f ∘ glue src dst) :=
  continuous_coinduced_dom (f := glue src dst) (g := f)

/-- The introduction direction of the universal property. -/
theorem continuous_of_continuous_comp_glue (src dst : E → V) {X : Type*}
    [TopologicalSpace X] {f : Realization src dst → X}
    (hf : Continuous (f ∘ glue src dst)) : Continuous f :=
  (continuous_iff_continuous_comp_glue src dst f).2 hf

/-- Every normal form is hit by the raw domain. -/
theorem glue_surjective (src dst : E → V) : Function.Surjective (glue src dst) := by
  intro x
  cases x with
  | vertex v => exact ⟨Sum.inl ⟨v, ()⟩, rfl⟩
  | interior e t =>
      refine ⟨Sum.inr (⟨e, t.1⟩ : RawInterval E), ?_⟩
      show glueInterval src dst e t.1 = Realization.interior e t
      rw [glueInterval_interior src dst e t.1 t.2.1 t.2.2]

/-! ## Interval maps and their local laws -/

/-- The edge interval map: the image of the `e`-th edge interval under the gluing map. -/
def edgePoint (src dst : E → V) (e : E) (t : I) : Realization src dst :=
  glue src dst (Sum.inr (⟨e, t⟩ : RawInterval E))

/-- The `e`-th edge interval as a continuous map into the realization. -/
def edgeMap (src dst : E → V) (e : E) : C(I, Realization src dst) :=
  ⟨edgePoint src dst e, by
    have hsig : Continuous (fun t : I => (⟨e, t⟩ : RawInterval E)) :=
      @continuous_sigmaMk E (fun _ : E => I) (fun _ => inferInstance) e
    have h : Continuous (fun t : I => glue src dst (Sum.inr (⟨e, t⟩ : RawInterval E))) :=
      (glue_continuous src dst).comp (continuous_inr.comp hsig)
    simpa [edgePoint] using h⟩

/-- At the left endpoint the edge interval lands on the source vertex. -/
@[simp] theorem edgePoint_zero (src dst : E → V) (e : E) :
    edgePoint src dst e 0 = Realization.vertex (src e) := by
  show glueInterval src dst e 0 = Realization.vertex (src e)
  rw [glueInterval_zero]

/-- At the right endpoint the edge interval lands on the destination vertex. -/
@[simp] theorem edgePoint_one (src dst : E → V) (e : E) :
    edgePoint src dst e 1 = Realization.vertex (dst e) := by
  show glueInterval src dst e 1 = Realization.vertex (dst e)
  rw [glueInterval_one]

/-- At an interior parameter the edge interval lands on an interior normal form. -/
theorem edgePoint_interior (src dst : E → V) (e : E) (t : I)
    (h0 : t ≠ 0) (h1 : t ≠ 1) :
    edgePoint src dst e t = Realization.interior e ⟨t, h0, h1⟩ := by
  show glueInterval src dst e t = Realization.interior e ⟨t, h0, h1⟩
  rw [glueInterval_interior src dst e t h0 h1]

/-- The edge interval map is continuous. -/
theorem edgePoint_continuous (src dst : E → V) (e : E) :
    Continuous (edgePoint src dst e) :=
  (edgeMap src dst e).continuous

/-- Vertex normal forms are injective. -/
theorem vertex_injective (src dst : E → V) :
    Function.Injective (vertex (src := src) (dst := dst)) := by
  intro a b h
  exact Realization.vertex.inj h

/-- An interior normal form is never a vertex.  This is what rules out an edge collapsing to a
single vertex: the open edge interval is disjoint from every vertex normal form. -/
theorem interior_ne_vertex (src dst : E → V) (e : E)
    (t : {t : I // t ≠ 0 ∧ t ≠ 1}) (v : V) :
    Realization.interior (src := src) (dst := dst) e t ≠
      Realization.vertex (src := src) (dst := dst) v := by
  intro h
  cases h

/-- For an edge with distinct endpoints, its interval map is injective, so the edge is a genuine
interval and not a self-loop. -/
theorem edgePoint_injective (src dst : E → V) (e : E) (hne : src e ≠ dst e) :
    Function.Injective (edgePoint src dst e) := by
  intro t s h
  by_cases ht0 : t = 0
  · subst t
    by_cases hs0 : s = 0
    · subst s
      rfl
    · by_cases hs1 : s = 1
      · subst s
        rw [edgePoint_zero src dst e, edgePoint_one src dst e] at h
        exact absurd (Realization.vertex.inj h) hne
      · rw [edgePoint_zero src dst e, edgePoint_interior src dst e s hs0 hs1] at h
        cases h
  · by_cases ht1 : t = 1
    · subst t
      by_cases hs0 : s = 0
      · subst s
        rw [edgePoint_one src dst e, edgePoint_zero src dst e] at h
        exact absurd (Realization.vertex.inj h).symm hne
      · by_cases hs1 : s = 1
        · subst s
          rfl
        · rw [edgePoint_one src dst e, edgePoint_interior src dst e s hs0 hs1] at h
          cases h
    · by_cases hs0 : s = 0
      · subst s
        rw [edgePoint_interior src dst e t ht0 ht1, edgePoint_zero src dst e] at h
        cases h
      · by_cases hs1 : s = 1
        · subst s
          rw [edgePoint_interior src dst e t ht0 ht1, edgePoint_one src dst e] at h
          cases h
        · rw [edgePoint_interior src dst e t ht0 ht1,
              edgePoint_interior src dst e s hs0 hs1] at h
          injection h with _ hsub
          exact congrArg Subtype.val hsub

/-- Two interior edge parameters determine the same edge: edge identity (in particular the
identity of parallel edges with equal endpoints) is preserved by the realization. -/
theorem edge_eq_of_interior_edgePoint_eq (src dst : E → V) {e f : E} {t s : I}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (h : edgePoint src dst e t = edgePoint src dst f s) : e = f := by
  rw [edgePoint_interior src dst e t ht0 ht1,
      edgePoint_interior src dst f s hs0 hs1] at h
  injection h with he _

/-- A self-loop edge cannot be injective: both endpoints collapse to its single endpoint
vertex.  Molecular rings are therefore edge cycles, not self-loop edges. -/
theorem edgePoint_zero_eq_one_of_selfLoop (src dst : E → V) (e : E) (h : src e = dst e) :
    edgePoint src dst e 0 = edgePoint src dst e 1 := by
  rw [edgePoint_zero src dst e, edgePoint_one src dst e, h]

theorem not_edgePoint_injective_of_selfLoop (src dst : E → V) (e : E) (h : src e = dst e) :
    ¬ Function.Injective (edgePoint src dst e) := by
  intro hinj
  have h01 : (0 : I) = 1 := hinj (edgePoint_zero_eq_one_of_selfLoop src dst e h)
  exact zero_ne_one h01

/-! ### Collision of distinct edge intervals -/

/-- The shared endpoint lookup of the imported independent path encoding.  Both endpoint lookups
below are *exactly* `sourceEndpointAt?` applied to the realization's own endpoint maps. -/
abbrev endpointAt? (src dst : E → V) (e : E) (t : I) : Option V :=
  sourceEndpointAt? src dst e t

@[simp] theorem sourceEndpointAt?_zero (src dst : E → V) (e : E) :
    sourceEndpointAt? src dst e 0 = some (src e) := by
  unfold sourceEndpointAt?
  rw [if_pos rfl]

@[simp] theorem sourceEndpointAt?_one (src dst : E → V) (e : E) :
    sourceEndpointAt? src dst e 1 = some (dst e) := by
  unfold sourceEndpointAt?
  rw [if_neg (one_ne_zero : (1 : I) ≠ 0), if_pos rfl]

theorem sourceEndpointAt?_eq_none (src dst : E → V) (e : E) (t : I)
    (h0 : t ≠ 0) (h1 : t ≠ 1) :
    sourceEndpointAt? src dst e t = none := by
  unfold sourceEndpointAt?
  rw [if_neg h0, if_neg h1]

/-- An endpoint lookup that returns an atom forces the edge point to be that atom's vertex. -/
theorem edgePoint_eq_vertex_of_sourceEndpointAt? (src dst : E → V) {e : E} {t : I} {atom : V}
    (h : sourceEndpointAt? src dst e t = some atom) :
    edgePoint src dst e t = Realization.vertex atom := by
  by_cases ht0 : t = 0
  · rw [ht0] at h ⊢
    rw [sourceEndpointAt?_zero] at h
    rw [edgePoint_zero src dst e]
    exact congrArg Realization.vertex (Option.some.inj h)
  · by_cases ht1 : t = 1
    · rw [ht1] at h ⊢
      rw [sourceEndpointAt?_one] at h
      rw [edgePoint_one src dst e]
      exact congrArg Realization.vertex (Option.some.inj h)
    · rw [sourceEndpointAt?_eq_none src dst e t ht0 ht1] at h
      exact absurd h (by simp)

/-- **Distinct edge-point collision.**  If two edge interval points belonging to distinct edge
labels coincide, then both are endpoint points and they share a common endpoint atom.  The
conclusion is stated with the exact `sourceEndpointAt?` equalities used by the independent
path encoding, so downstream consumers can feed it directly to endpoint-based intersection
laws. -/
theorem edgePoint_collision (src dst : E → V) {e f : E} {t s : I}
    (hne : e ≠ f) (h : edgePoint src dst e t = edgePoint src dst f s) :
    ∃ atom : V,
      sourceEndpointAt? src dst e t = some atom ∧
        sourceEndpointAt? src dst f s = some atom := by
  by_cases ht0 : t = 0
  · subst t
    by_cases hs0 : s = 0
    · subst s
      refine ⟨src e, ?_, ?_⟩
      · simp
      · rw [edgePoint_zero src dst e, edgePoint_zero src dst f] at h
        have hsrc : src e = src f := Realization.vertex.inj h
        simp [hsrc]
    · by_cases hs1 : s = 1
      · subst s
        refine ⟨src e, ?_, ?_⟩
        · simp
        · rw [edgePoint_zero src dst e, edgePoint_one src dst f] at h
          have hsrc : src e = dst f := Realization.vertex.inj h
          simp [hsrc]
      · rw [edgePoint_zero src dst e, edgePoint_interior src dst f s hs0 hs1] at h
        cases h
  · by_cases ht1 : t = 1
    · subst t
      by_cases hs0 : s = 0
      · subst s
        refine ⟨dst e, ?_, ?_⟩
        · simp
        · rw [edgePoint_one src dst e, edgePoint_zero src dst f] at h
          have hdst : dst e = src f := Realization.vertex.inj h
          simp [hdst]
      · by_cases hs1 : s = 1
        · subst s
          refine ⟨dst e, ?_, ?_⟩
          · simp
          · rw [edgePoint_one src dst e, edgePoint_one src dst f] at h
            have hdst : dst e = dst f := Realization.vertex.inj h
            simp [hdst]
        · rw [edgePoint_one src dst e, edgePoint_interior src dst f s hs0 hs1] at h
          cases h
    · by_cases hs0 : s = 0
      · subst s
        rw [edgePoint_interior src dst e t ht0 ht1, edgePoint_zero src dst f] at h
        cases h
      · by_cases hs1 : s = 1
        · subst s
          rw [edgePoint_interior src dst e t ht0 ht1, edgePoint_one src dst f] at h
          cases h
        · rw [edgePoint_interior src dst e t ht0 ht1,
              edgePoint_interior src dst f s hs0 hs1] at h
          have hef : e = f := by
            injection h with hef _
          exact absurd hef hne

/-- Exact form of an edge point being a vertex.  This covers self-loops: if `src e = dst e`, both
endpoint alternatives name the same vertex. -/
theorem edgePoint_eq_vertex_iff (src dst : E → V) (e : E) (t : I) (v : V) :
    edgePoint src dst e t = Realization.vertex v ↔
      (t = 0 ∧ src e = v) ∨ (t = 1 ∧ dst e = v) := by
  constructor
  · intro h
    by_cases ht0 : t = 0
    · left
      refine ⟨ht0, ?_⟩
      rw [ht0, edgePoint_zero src dst e] at h
      exact Realization.vertex.inj h
    · by_cases ht1 : t = 1
      · right
        refine ⟨ht1, ?_⟩
        rw [ht1, edgePoint_one src dst e] at h
        exact Realization.vertex.inj h
      · exfalso
        rw [edgePoint_interior src dst e t ht0 ht1] at h
        exact interior_ne_vertex src dst e ⟨t, ht0, ht1⟩ v h
  · rintro (⟨ht, hsv⟩ | ⟨ht, hdv⟩)
    · rw [ht, edgePoint_zero src dst e, hsv]
    · rw [ht, edgePoint_one src dst e, hdv]

/-- Exact form of two edge points coinciding.  The second disjunct is the common-endpoint
alternative and is also what makes the statement valid for self-loops and for two endpoint
parameters of the same edge. -/
theorem edgePoint_eq_iff (src dst : E → V) (e f : E) (t s : I) :
    edgePoint src dst e t = edgePoint src dst f s ↔
      (e = f ∧ t = s) ∨
        ∃ atom : V,
          sourceEndpointAt? src dst e t = some atom ∧
            sourceEndpointAt? src dst f s = some atom := by
  constructor
  · intro h
    by_cases hef : e = f
    · subst f
      by_cases hts : t = s
      · exact Or.inl ⟨rfl, hts⟩
      · right
        by_cases ht0 : t = 0
        · by_cases hs0 : s = 0
          · exact absurd (ht0.trans hs0.symm) hts
          · by_cases hs1 : s = 1
            · rw [ht0, hs1, edgePoint_zero src dst e, edgePoint_one src dst e] at h
              have hsd : dst e = src e := (Realization.vertex.inj h).symm
              refine ⟨src e, ?_, ?_⟩
              · rw [ht0, sourceEndpointAt?_zero]
              · rw [hs1, sourceEndpointAt?_one, hsd]
            · exfalso
              rw [ht0, edgePoint_zero src dst e,
                  edgePoint_interior src dst e s hs0 hs1] at h
              exact interior_ne_vertex src dst e ⟨s, hs0, hs1⟩ (src e) h.symm
        · by_cases ht1 : t = 1
          · by_cases hs0 : s = 0
            · rw [ht1, hs0, edgePoint_one src dst e, edgePoint_zero src dst e] at h
              have hds : dst e = src e := Realization.vertex.inj h
              refine ⟨src e, ?_, ?_⟩
              · rw [ht1, sourceEndpointAt?_one, hds]
              · rw [hs0, sourceEndpointAt?_zero]
            · by_cases hs1 : s = 1
              · exact absurd (ht1.trans hs1.symm) hts
              · exfalso
                rw [ht1, edgePoint_one src dst e,
                    edgePoint_interior src dst e s hs0 hs1] at h
                exact interior_ne_vertex src dst e ⟨s, hs0, hs1⟩ (dst e) h.symm
          · by_cases hs0 : s = 0
            · exfalso
              rw [edgePoint_interior src dst e t ht0 ht1,
                  hs0, edgePoint_zero src dst e] at h
              exact interior_ne_vertex src dst e ⟨t, ht0, ht1⟩ (src e) h
            · by_cases hs1 : s = 1
              · exfalso
                rw [edgePoint_interior src dst e t ht0 ht1,
                    hs1, edgePoint_one src dst e] at h
                exact interior_ne_vertex src dst e ⟨t, ht0, ht1⟩ (dst e) h
              · exfalso
                rw [edgePoint_interior src dst e t ht0 ht1,
                    edgePoint_interior src dst e s hs0 hs1] at h
                have hst : t = s := by
                  injection h with _ hsub
                  exact congrArg Subtype.val hsub
                exact hts hst
    · exact Or.inr (edgePoint_collision src dst hef h)
  · rintro (⟨hef, hts⟩ | ⟨atom, he, hf⟩)
    · subst f
      subst s
      rfl
    · exact (edgePoint_eq_vertex_of_sourceEndpointAt? src dst he).trans
        (edgePoint_eq_vertex_of_sourceEndpointAt? src dst hf).symm

/-! ## Global embedded graphs -/

/-- A supplied global classical embedding of a finite multigraph into real three-space: one
continuous injective map from the graph realization.  No local arc or coverage data is part of the
structure; all local laws below are derived from this single map. -/
structure EmbeddedGraph (src dst : E → V) where
  /-- The global continuous embedding. -/
  map : C(Realization src dst, EmbeddedReal3)
  /-- The global embedding is injective. -/
  injective : Function.Injective (map : Realization src dst → EmbeddedReal3)

/-- The per-edge non-self-loop condition.  It is not an input of `EmbeddedGraph`: the interval
laws above are conditional on it, and a self-loop genuinely fails injectivity. -/
def NoSelfLoops (src dst : E → V) : Prop :=
  ∀ e : E, src e ≠ dst e

namespace EmbeddedGraph

variable {src dst : E → V}

/-- The position of a vertex atom: the image of its vertex normal form. -/
def conformation (G : EmbeddedGraph src dst) : V → EmbeddedReal3 :=
  fun v => G.map (Realization.vertex v)

@[simp] theorem conformation_apply (G : EmbeddedGraph src dst) (v : V) :
    G.conformation v = G.map (Realization.vertex v) := rfl

/-- The embedded arc of an edge: the global embedding restricted to the edge interval map. -/
def arc (G : EmbeddedGraph src dst) (e : E) : C(I, EmbeddedReal3) :=
  G.map.comp (edgeMap src dst e)

@[simp] theorem arc_apply (G : EmbeddedGraph src dst) (e : E) (t : I) :
    G.arc e t = G.map (edgePoint src dst e t) := rfl

/-- The left endpoint of an embedded arc is the source atom position. -/
@[simp] theorem arc_zero (G : EmbeddedGraph src dst) (e : E) :
    G.arc e 0 = G.conformation (src e) := by
  rw [arc_apply, edgePoint_zero]
  rfl

/-- The right endpoint of an embedded arc is the destination atom position. -/
@[simp] theorem arc_one (G : EmbeddedGraph src dst) (e : E) :
    G.arc e 1 = G.conformation (dst e) := by
  rw [arc_apply, edgePoint_one]
  rfl

/-- Distinct atoms occupy distinct points. -/
theorem atom_injective (G : EmbeddedGraph src dst) : Function.Injective G.conformation := by
  intro a b h
  exact vertex_injective src dst (G.injective (by simpa [conformation_apply] using h))

/-- The arc of a non-self-loop edge is injective on the unit interval. -/
theorem arc_injective (G : EmbeddedGraph src dst) (e : E) (h : src e ≠ dst e) :
    Function.Injective (G.arc e) := by
  intro t s hts
  exact edgePoint_injective src dst e h
    (G.injective (by simpa [arc_apply] using hts))

/-- Arc interiors avoid every atom position. -/
theorem interior_avoids_atoms (G : EmbeddedGraph src dst) (e : E) (t : I)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (atom : V) :
    G.arc e t ≠ G.conformation atom := by
  intro h
  have hm : G.map (edgePoint src dst e t) = G.map (Realization.vertex atom) := by
    simpa [arc_apply, conformation_apply] using h
  have heq : edgePoint src dst e t = Realization.vertex atom := G.injective hm
  rw [edgePoint_interior src dst e t ht0 ht1] at heq
  exact interior_ne_vertex src dst e ⟨t, ht0, ht1⟩ atom heq

/-- **Intersection law.**  Two arcs of distinct edges meet only at a common endpoint atom,
expressed with the exact `sourceEndpointAt?` equalities of the independent path encoding. -/
theorem intersects_only_at_common_endpoints (G : EmbeddedGraph src dst) (e f : E)
    (t s : I) (hne : e ≠ f) (h : G.arc e t = G.arc f s) :
    ∃ atom : V,
      sourceEndpointAt? src dst e t = some atom ∧
        sourceEndpointAt? src dst f s = some atom := by
  have hm : G.map (edgePoint src dst e t) = G.map (edgePoint src dst f s) := by
    simpa [arc_apply] using h
  exact edgePoint_collision src dst hne (G.injective hm)

/-- Two arcs meeting at interior parameters belong to the same edge.  This is edge identity,
including the identity of parallel edges with the same endpoint atoms. -/
theorem edge_eq_of_interior_meet (G : EmbeddedGraph src dst) {e f : E} {t s : I}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (h : G.arc e t = G.arc f s) : e = f := by
  have hm : G.map (edgePoint src dst e t) = G.map (edgePoint src dst f s) := by
    simpa [arc_apply] using h
  exact edge_eq_of_interior_edgePoint_eq src dst ht0 ht1 hs0 hs1 (G.injective hm)

/-- Under the per-edge non-self-loop condition, every arc is injective. -/
theorem arc_injective_of_noSelfLoops (G : EmbeddedGraph src dst)
    (h : NoSelfLoops src dst) (e : E) : Function.Injective (G.arc e) :=
  G.arc_injective e (h e)

end EmbeddedGraph

/-! ## A concrete inhabited single-edge example in real three-space

The example has two vertices `false` and `true` and one edge.  The global map sends the vertex
`false` to `0`, the vertex `true` to a chosen nonzero point `p`, and the interior parameter `t` to
`(t : ℝ) • p`.  Continuity is obtained from the coinduced universal property: it is enough that
the composite with `glue` is continuous on the raw coproduct. -/

/-- A nonzero ambient point of real three-space, chosen classically. -/
noncomputable def toyNonzeroPoint : EmbeddedReal3 :=
  Classical.choose (exists_ne (0 : EmbeddedReal3))

theorem toyNonzeroPoint_ne_zero : toyNonzeroPoint ≠ 0 :=
  Classical.choose_spec (exists_ne (0 : EmbeddedReal3))

/-- Source endpoint of the single toy edge. -/
def toySrc : Unit → Bool := fun _ => false

/-- Destination endpoint of the single toy edge. -/
def toyDst : Unit → Bool := fun _ => true

@[simp] theorem toySrc_apply (e : Unit) : toySrc e = false := rfl

@[simp] theorem toyDst_apply (e : Unit) : toyDst e = true := rfl

/-- The two vertex positions of the toy graph. -/
def toyVertexPoint : Bool → EmbeddedReal3
  | false => 0
  | true => toyNonzeroPoint

@[simp] theorem toyVertexPoint_false : toyVertexPoint false = 0 := rfl

@[simp] theorem toyVertexPoint_true : toyVertexPoint true = toyNonzeroPoint := rfl

/-- The global map of the toy realization, defined on the normal form. -/
def toyMap : Realization toySrc toyDst → EmbeddedReal3
  | Realization.vertex b => toyVertexPoint b
  | Realization.interior _ t => (t.1 : ℝ) • toyNonzeroPoint

@[simp] theorem toyMap_vertex (b : Bool) :
    toyMap (Realization.vertex (src := toySrc) (dst := toyDst) b) = toyVertexPoint b := rfl

@[simp] theorem toyMap_interior (e : Unit) (t : {t : I // t ≠ 0 ∧ t ≠ 1}) :
    toyMap (Realization.interior (src := toySrc) (dst := toyDst) e t) =
      (t.1 : ℝ) • toyNonzeroPoint := rfl

/-- The raw-domain map whose continuity implies continuity of `toyMap` by the universal property.
On vertex slots it is the vertex position; on interval slots it is scalar multiplication of the
chosen point. -/
def toyRawMap : RawDomain Bool Unit → EmbeddedReal3 :=
  Sum.elim (fun p : RawVertex Bool => toyVertexPoint p.1)
    (fun q : RawInterval Unit => (q.2 : ℝ) • toyNonzeroPoint)

@[simp] theorem toyRawMap_inl (b : Bool) (u : Unit) :
    toyRawMap (Sum.inl (⟨b, u⟩ : RawVertex Bool)) = toyVertexPoint b := rfl

@[simp] theorem toyRawMap_inr (e : Unit) (t : I) :
    toyRawMap (Sum.inr (⟨e, t⟩ : RawInterval Unit)) = (t : ℝ) • toyNonzeroPoint := rfl

/-- The composite of the toy global map with the gluing map is the explicit raw-domain map. -/
theorem toyMap_comp_glue : toyMap ∘ glue toySrc toyDst = toyRawMap := by
  funext x
  cases x with
  | inl v =>
      obtain ⟨b, u⟩ := v
      cases b <;> rfl
  | inr q =>
      obtain ⟨e, t⟩ := q
      cases e
      by_cases h0 : t = 0
      · rw [h0]
        simp
      · by_cases h1 : t = 1
        · rw [h1]
          simp
        · rw [Function.comp_apply, glue_inr,
              glueInterval_interior toySrc toyDst () t h0 h1]
          simp

/-- The raw-domain map is continuous: each vertex-slot fibre is constant and each interval-slot
fibre is `t ↦ (t : ℝ) • p`. -/
theorem toyRawMap_continuous : Continuous toyRawMap := by
  unfold toyRawMap
  apply Continuous.sumElim
  · apply continuous_sigma
    intro b
    exact (continuous_const : Continuous (fun _ : Unit => toyVertexPoint b))
  · apply continuous_sigma
    intro e
    exact continuous_subtype_val.smul
      (continuous_const : Continuous (fun _ : I => toyNonzeroPoint))

/-- Continuity of the toy global map, obtained purely from the coinduced universal property. -/
theorem toyMap_continuous : Continuous toyMap :=
  (continuous_coinduced_dom (f := glue toySrc toyDst) (g := toyMap)).2 (by
    rw [toyMap_comp_glue]
    exact toyRawMap_continuous)

theorem toyVertexPoint_injective : Function.Injective toyVertexPoint := by
  intro a b h
  cases a <;> cases b
  · rfl
  · exact absurd (show toyNonzeroPoint = 0 from h.symm) toyNonzeroPoint_ne_zero
  · exact absurd (show toyNonzeroPoint = 0 from h) toyNonzeroPoint_ne_zero
  · rfl

theorem toySmul_eq_zero {t : I} (h : (t : ℝ) • toyNonzeroPoint = 0) : t = 0 := by
  have ht : (t : ℝ) = 0 := by
    rcases eq_zero_or_eq_zero_of_smul_eq_zero h with ht | hp
    · exact ht
    · exact absurd hp toyNonzeroPoint_ne_zero
  exact Subtype.ext ht

theorem toySmul_eq_point {t : I} (h : (t : ℝ) • toyNonzeroPoint = toyNonzeroPoint) : t = 1 := by
  have hsub : ((t : ℝ) - 1) • toyNonzeroPoint = 0 := by
    rw [sub_smul, one_smul, h, sub_self]
  have ht : (t : ℝ) - 1 = 0 := by
    rcases eq_zero_or_eq_zero_of_smul_eq_zero hsub with ht | hp
    · exact ht
    · exact absurd hp toyNonzeroPoint_ne_zero
  exact Subtype.ext (by simpa using sub_eq_zero.mp ht)

theorem toySmul_injective {t s : I}
    (h : (t : ℝ) • toyNonzeroPoint = (s : ℝ) • toyNonzeroPoint) : t = s := by
  have hsub : ((t : ℝ) - (s : ℝ)) • toyNonzeroPoint = 0 := by
    rw [sub_smul, h, sub_self]
  have hts : (t : ℝ) - (s : ℝ) = 0 := by
    rcases eq_zero_or_eq_zero_of_smul_eq_zero hsub with h' | h'
    · exact h'
    · exact absurd h' toyNonzeroPoint_ne_zero
  exact Subtype.ext (sub_eq_zero.mp hts)

theorem toyMap_injective : Function.Injective toyMap := by
  intro x y h
  cases x with
  | vertex a =>
      cases y with
      | vertex b =>
          have hab : a = b := toyVertexPoint_injective h
          subst b
          rfl
      | interior e t =>
          cases a
          · exact absurd
              (toySmul_eq_zero (t := t.1)
                (show (t.1 : ℝ) • toyNonzeroPoint = 0 from h.symm)) t.2.1
          · exact absurd
              (toySmul_eq_point (t := t.1)
                (show (t.1 : ℝ) • toyNonzeroPoint = toyNonzeroPoint from h.symm)) t.2.2
  | interior e t =>
      cases y with
      | vertex a =>
          cases a
          · exact absurd
              (toySmul_eq_zero (t := t.1)
                (show (t.1 : ℝ) • toyNonzeroPoint = 0 from h)) t.2.1
          · exact absurd
              (toySmul_eq_point (t := t.1)
                (show (t.1 : ℝ) • toyNonzeroPoint = toyNonzeroPoint from h)) t.2.2
      | interior f s =>
          have h' : (t.1 : ℝ) • toyNonzeroPoint = (s.1 : ℝ) • toyNonzeroPoint := h
          have hts : t.1 = s.1 := toySmul_injective h'
          have hef : e = f := Subsingleton.elim e f
          rw [hef]
          exact congrArg (Realization.interior (src := toySrc) (dst := toyDst) f)
            (Subtype.ext hts)

/-- The concrete inhabited single-edge embedded graph in real three-space. -/
def toyEmbeddedGraph : EmbeddedGraph toySrc toyDst where
  map := ⟨toyMap, toyMap_continuous⟩
  injective := toyMap_injective

/-- The source and destination of the toy edge are distinct. -/
theorem toy_source_ne_dst (e : Unit) : toySrc e ≠ toyDst e := by
  rw [toySrc_apply, toyDst_apply]
  exact Bool.false_ne_true

/-- The toy graph is a genuine single edge: its arc is injective. -/
theorem toy_arc_injective (e : Unit) :
    Function.Injective (toyEmbeddedGraph.arc e) :=
  toyEmbeddedGraph.arc_injective e (toy_source_ne_dst e)

/-- The toy conformation is injective. -/
theorem toy_conformation_injective :
    Function.Injective toyEmbeddedGraph.conformation :=
  toyEmbeddedGraph.atom_injective

/-- The toy arc interior avoids both atom positions. -/
theorem toy_interior_avoids_atoms (e : Unit) (t : I) (h0 : t ≠ 0) (h1 : t ≠ 1)
    (atom : Bool) :
    toyEmbeddedGraph.arc e t ≠ toyEmbeddedGraph.conformation atom :=
  toyEmbeddedGraph.interior_avoids_atoms e t h0 h1 atom

/-- Exact value of the toy conformation. -/
@[simp] theorem toyEmbeddedGraph_conformation :
    toyEmbeddedGraph.conformation = toyVertexPoint := rfl

end

end OrganicStereoEmbeddedGraphRealization
end TetraStereo.OneCenter
