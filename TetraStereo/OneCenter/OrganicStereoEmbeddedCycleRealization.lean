import TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false































































namespace TetraStereo.OneCenter
namespace OrganicStereoEmbeddedCycleRealization

open scoped unitInterval
open OrganicStereoEmbeddedGraphRealization

noncomputable section

universe u v

variable {V : Type u} {E : Type v}

/-! ## The cyclic index successor -/

/-- The cyclic successor on `Fin n`: rotation by one step.  For `n ≥ 2` it has no fixed point,
and for `n ≥ 3` its square has no fixed point; both facts are proved below from `Fin` arithmetic
alone. -/
def cycleNext (n : ℕ) : Fin n → Fin n :=
  finRotate n

/-- The cyclic successor is addition by one. -/
theorem cycleNext_apply {n : ℕ} [NeZero n] (i : Fin n) : cycleNext n i = i + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact finRotate_succ_apply i

/-- The cyclic successor has no fixed point for `n ≥ 2`. -/
theorem cycleNext_ne {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : cycleNext n i ≠ i := by
  haveI : NeZero n := ⟨by rintro rfl; exact absurd hn (by norm_num)⟩
  rw [cycleNext_apply (n := n) i]
  intro h
  have h' : i + (1 : Fin n) = i + 0 := by simpa using h
  have h1 : (1 : Fin n) = 0 := add_left_cancel h'
  have hn1 : n = 1 := Fin.one_eq_zero_iff.mp h1
  exact absurd (hn1 ▸ hn) (by norm_num)

/-- The square of the cyclic successor has no fixed point for `n ≥ 3`. -/
theorem cycleNext_cycleNext_ne {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    cycleNext n (cycleNext n i) ≠ i := by
  haveI : NeZero n := ⟨by rintro rfl; exact absurd hn (by norm_num)⟩
  rw [cycleNext_apply (n := n) i, cycleNext_apply (n := n) (i + 1)]
  intro h
  have h' : i + ((1 : Fin n) + 1) = i + 0 := by simpa [add_assoc] using h
  have h2 : (1 : Fin n) + 1 = 0 := add_left_cancel h'
  have hval : ((1 : Fin n) + 1).val = (0 : Fin n).val := congrArg Fin.val h2
  have hlt : (1 : Fin n).val + (1 : Fin n).val < n := by
    have h1 : (1 : Fin n).val = 1 := by
      rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
    omega
  rw [Fin.val_add_eq_of_add_lt hlt, Fin.val_one', Nat.mod_eq_of_lt (by omega)] at hval
  simp at hval

/-! ## Orientation of the interval parameter -/

/-- The orientation applied to an interval parameter: the identity when the walk follows the
source orientation of the edge, and the unit-interval reflection `unitInterval.symm` when it
traverses the edge in reverse.  The selected edge occurrence itself is never changed. -/
def orient (b : Bool) (t : I) : I :=
  if b then unitInterval.symm t else t

@[simp] theorem orient_false (t : I) : orient false t = t := rfl

@[simp] theorem orient_true (t : I) : orient true t = unitInterval.symm t := rfl

/-- Orientation is an involution. -/
theorem orient_involutive (b : Bool) : Function.Involutive (orient b) := by
  intro t
  cases b
  · rfl
  · simp [orient]

/-- Orientation is injective. -/
theorem orient_injective (b : Bool) : Function.Injective (orient b) := by
  intro s t h
  have h' := congrArg (orient b) h
  rw [orient_involutive b s, orient_involutive b t] at h'
  exact h'

/-- Orientation is continuous. -/
theorem orient_continuous (b : Bool) : Continuous (orient b) := by
  cases b
  · simpa [orient] using (continuous_id : Continuous (fun t : I => t))
  · simpa [orient] using unitInterval.continuous_symm

/-- Orientation preserves interior parameters. -/
theorem orient_mem_intervalInterior {b : Bool} {t : I}
    (h0 : t ≠ 0) (h1 : t ≠ 1) : orient b t ≠ 0 ∧ orient b t ≠ 1 := by
  constructor
  · cases b
    · exact h0
    · simp [orient, h1]
  · cases b
    · exact h1
    · simp [orient, h0]

/-! ## The combinatorial cycle walk -/

/-- A combinatorial cycle walk of length `n ≥ 3` in a multigraph with endpoint maps
`src dst : E → V`.

The endpoint equations orient the `i`-th selected edge from `vertices i` to `vertices (next i)`,
swapping the two when `reverse i = true`.  Edge injectivity and the non-self-loop property of every
selected edge are *theorems* about this data, not fields. -/
structure CycleWalk (src dst : E → V) where
  /-- The number of edges (and of vertices) of the cycle. -/
  n : ℕ
  /-- A cycle has at least three edges. -/
  hn : 3 ≤ n
  /-- The vertex at each cyclic index. -/
  vertices : Fin n → V
  /-- Distinct cyclic indices carry distinct vertices. -/
  vertices_injective : Function.Injective vertices
  /-- The selected edge occurrence at each cyclic index. -/
  edges : Fin n → E
  /-- Whether the walk traverses the selected edge in reverse. -/
  reverse : Fin n → Bool
  /-- The source endpoint of the `i`-th selected edge. -/
  source_eq : ∀ i : Fin n,
    src (edges i) = if reverse i then vertices (cycleNext n i) else vertices i
  /-- The destination endpoint of the `i`-th selected edge. -/
  target_eq : ∀ i : Fin n,
    dst (edges i) = if reverse i then vertices i else vertices (cycleNext n i)

namespace CycleWalk

variable {src dst : E → V}

/-- The cyclic successor has no fixed point. -/
theorem next_ne (W : CycleWalk src dst) (i : Fin W.n) : cycleNext W.n i ≠ i :=
  cycleNext_ne (le_trans (by norm_num : 2 ≤ 3) W.hn) i

/-- The square of the cyclic successor has no fixed point. -/
theorem next_next_ne (W : CycleWalk src dst) (i : Fin W.n) :
    cycleNext W.n (cycleNext W.n i) ≠ i :=
  cycleNext_cycleNext_ne W.hn i

/-- **Edge injectivity is derived.**  Distinct cyclic indices select distinct edge occurrences.
The proof uses injectivity of the vertex map and the fact that `next (next i) ≠ i` for a cyclic
successor with `n ≥ 3`; no injectivity of `edges` is assumed. -/
theorem edges_injective (W : CycleWalk src dst) : Function.Injective W.edges := by
  intro i j hij
  have hsrc : src (W.edges i) = src (W.edges j) := by rw [hij]
  have hdst : dst (W.edges i) = dst (W.edges j) := by rw [hij]
  rw [W.source_eq i, W.source_eq j] at hsrc
  rw [W.target_eq i, W.target_eq j] at hdst
  cases hi : W.reverse i <;> cases hj : W.reverse j
  · exact W.vertices_injective (by simpa [hi, hj] using hsrc)
  · have h1 : W.vertices i = W.vertices (cycleNext W.n j) := by simpa [hi, hj] using hsrc
    have h2 : W.vertices (cycleNext W.n i) = W.vertices j := by simpa [hi, hj] using hdst
    have eA : i = cycleNext W.n j := W.vertices_injective h1
    have eB : cycleNext W.n i = j := W.vertices_injective h2
    have hcyc : cycleNext W.n (cycleNext W.n i) = i := by rw [eB, ← eA]
    exact absurd hcyc (W.next_next_ne i)
  · have h1 : W.vertices (cycleNext W.n i) = W.vertices j := by simpa [hi, hj] using hsrc
    have h2 : W.vertices i = W.vertices (cycleNext W.n j) := by simpa [hi, hj] using hdst
    have eB : cycleNext W.n i = j := W.vertices_injective h1
    have eA : i = cycleNext W.n j := W.vertices_injective h2
    have hcyc : cycleNext W.n (cycleNext W.n i) = i := by rw [eB, ← eA]
    exact absurd hcyc (W.next_next_ne i)
  · exact W.vertices_injective (by simpa [hi, hj] using hdst)

/-- Every selected edge of a cycle walk has distinct endpoints, so it is a genuine interval and
not a self-loop.  This is derived from vertex injectivity and `next i ≠ i`. -/
theorem src_ne_dst (W : CycleWalk src dst) (i : Fin W.n) :
    src (W.edges i) ≠ dst (W.edges i) := by
  intro h
  have hsrc := W.source_eq i
  have hdst := W.target_eq i
  rw [h] at hsrc
  rw [hdst] at hsrc
  have hcontr : W.vertices i = W.vertices (cycleNext W.n i) := by
    cases hb : W.reverse i
    · simpa [hb] using hsrc.symm
    · simpa [hb] using hsrc
  have hnext : i = cycleNext W.n i := W.vertices_injective hcontr
  exact W.next_ne i hnext.symm

end CycleWalk

variable {src dst : E → V}

/-! ## The cycle domain and the realized cycle map -/

/-- The abstract cycle domain on `n` cyclic indices: the graph realization whose `i`-th edge runs
from vertex `i` to vertex `next i`.  This is a finite graph realization, not (yet) a circle. -/
abbrev CycleDomain (n : ℕ) : Type :=
  Realization (id : Fin n → Fin n) (cycleNext n)

/-- The map of a cycle walk into the graph realization, on normal forms. -/
def cycleMap (W : CycleWalk src dst) : CycleDomain W.n → Realization src dst
  | Realization.vertex i => Realization.vertex (W.vertices i)
  | Realization.interior i t =>
      edgePoint src dst (W.edges i) (orient (W.reverse i) t.1)

@[simp] theorem cycleMap_vertex (W : CycleWalk src dst) (i : Fin W.n) :
    cycleMap W (Realization.vertex i) = Realization.vertex (W.vertices i) := rfl

@[simp] theorem cycleMap_interior (W : CycleWalk src dst) (i : Fin W.n)
    (t : {t : I // t ≠ 0 ∧ t ≠ 1}) :
    cycleMap W (Realization.interior i t) =
      edgePoint src dst (W.edges i) (orient (W.reverse i) t.1) := rfl

/-- The point reached by the cycle parametrization on the `i`-th oriented interval. -/
def cycleParam (W : CycleWalk src dst) (i : Fin W.n) (t : I) : Realization src dst :=
  edgePoint src dst (W.edges i) (orient (W.reverse i) t)

@[simp] theorem cycleParam_apply (W : CycleWalk src dst) (i : Fin W.n) (t : I) :
    cycleParam W i t = edgePoint src dst (W.edges i) (orient (W.reverse i) t) := rfl

/-- Each oriented interval parametrization is continuous. -/
theorem cycleParam_continuous (W : CycleWalk src dst) (i : Fin W.n) :
    Continuous (cycleParam W i) :=
  (edgePoint_continuous src dst (W.edges i)).comp (orient_continuous (W.reverse i))

/-- The vertex part of the glued composite, with its codomain made explicit. -/
def cycleVertexMap (W : CycleWalk src dst) : RawVertex (Fin W.n) → Realization src dst :=
  fun p => Realization.vertex (W.vertices p.1)

/-- The interval part of the glued composite, with its codomain made explicit. -/
def cycleIntervalMap (W : CycleWalk src dst) : RawInterval (Fin W.n) → Realization src dst :=
  fun q => cycleParam W q.1 q.2

@[simp] theorem cycleIntervalMap_apply (W : CycleWalk src dst) (i : Fin W.n) (t : I) :
    cycleIntervalMap W (⟨i, t⟩ : RawInterval (Fin W.n)) = cycleParam W i t := rfl

/-- The vertex part is continuous because it is locally constant on the discrete vertex slots. -/
theorem cycleVertexMap_continuous (W : CycleWalk src dst) : Continuous (cycleVertexMap W) := by
  have h : (fun p : (Σ _ : Fin W.n, Unit) => cycleVertexMap W p) = cycleVertexMap W := rfl
  rw [← h]
  refine continuous_sigma (fun i => ?_)
  have hc : (fun a : Unit => cycleVertexMap W ⟨i, a⟩) =
      fun _ => (Realization.vertex (W.vertices i) : Realization src dst) := by
    funext a
    cases a
    rfl
  rw [hc]
  exact continuous_const

/-- The interval part is continuous, by continuity of each oriented parametrization. -/
theorem cycleIntervalMap_continuous (W : CycleWalk src dst) : Continuous (cycleIntervalMap W) := by
  have h : (fun q : (Σ _ : Fin W.n, I) => cycleIntervalMap W q) = cycleIntervalMap W := rfl
  rw [← h]
  exact continuous_sigma (fun i => cycleParam_continuous W i)

/-- The composite of the cycle map with the gluing map of the abstract cycle domain.  On a raw
interval slot `(i, t)` it is the oriented parametrization `cycleParam W i t`. -/
theorem cycleMap_comp_glue (W : CycleWalk src dst) :
    (cycleMap W) ∘ glue (id : Fin W.n → Fin W.n) (cycleNext W.n) =
      Sum.elim (cycleVertexMap W) (cycleIntervalMap W) := by
  funext x
  cases x with
  | inl p =>
      obtain ⟨i, u⟩ := p
      cases u
      rfl
  | inr q =>
      obtain ⟨i, t⟩ := q
      simp only [Function.comp_apply, Sum.elim_inr]
      by_cases h0 : t = 0
      · subst h0
        rw [glue_inr, glueInterval_zero (id : Fin W.n → Fin W.n) (cycleNext W.n) i]
        cases hb : W.reverse i <;>
          simp [cycleParam, orient, hb, W.source_eq i, W.target_eq i]
      · by_cases h1 : t = 1
        · subst h1
          rw [glue_inr, glueInterval_one (id : Fin W.n → Fin W.n) (cycleNext W.n) i]
          cases hb : W.reverse i <;>
            simp [cycleParam, orient, hb, W.source_eq i, W.target_eq i]
        · rw [glue_inr, glueInterval_interior (id : Fin W.n → Fin W.n) (cycleNext W.n) i t h0 h1]
          rfl

/-- The composite of the cycle map with the gluing map is continuous. -/
theorem cycleMap_comp_glue_continuous (W : CycleWalk src dst) :
    Continuous ((cycleMap W) ∘ glue (id : Fin W.n → Fin W.n) (cycleNext W.n)) := by
  rw [cycleMap_comp_glue]
  exact Continuous.sumElim (cycleVertexMap_continuous W) (cycleIntervalMap_continuous W)

/-- **Continuity of the realized cycle map**, obtained from the coinduced (gluing) universal
property of the abstract cycle domain. -/
theorem cycleMap_continuous (W : CycleWalk src dst) : Continuous (cycleMap W) :=
  continuous_of_continuous_comp_glue (id : Fin W.n → Fin W.n) (cycleNext W.n)
    (cycleMap_comp_glue_continuous W)

/-- The vertex normal form is injective as a map into a realization. -/
theorem realizationVertex_injective (src dst : E → V) :
    Function.Injective (fun v : V => (Realization.vertex v : Realization src dst)) := by
  intro a b h
  cases h
  rfl

/-- **Injectivity of the realized cycle map.**  Vertices are separated by vertex injectivity;
a vertex cannot collide with an interior point; and two interior points can collide only when they
belong to the same selected edge occurrence (derived edge injectivity) and have the same parameter
(injectivity of `orient` composed with interval injectivity on a genuine edge). -/
theorem cycleMap_injective (W : CycleWalk src dst) : Function.Injective (cycleMap W) := by
  intro x y h
  cases x with
  | vertex i =>
      cases y with
      | vertex j =>
          have hij : W.vertices i = W.vertices j :=
            realizationVertex_injective src dst (by simpa [cycleMap_vertex] using h)
          rw [W.vertices_injective hij]
      | interior j t =>
          exfalso
          have h' : Realization.vertex (W.vertices i) =
              edgePoint src dst (W.edges j) (orient (W.reverse j) t.1) := by
            simpa [cycleMap_vertex, cycleMap_interior] using h
          rcases (edgePoint_eq_vertex_iff src dst (W.edges j) (orient (W.reverse j) t.1)
              (W.vertices i)).mp h'.symm with ⟨h0, _⟩ | ⟨h1, _⟩
          · exact (orient_mem_intervalInterior t.2.1 t.2.2).1 h0
          · exact (orient_mem_intervalInterior t.2.1 t.2.2).2 h1
  | interior i t =>
      cases y with
      | vertex j =>
          exfalso
          have h' : edgePoint src dst (W.edges i) (orient (W.reverse i) t.1) =
              Realization.vertex (W.vertices j) := by
            simpa [cycleMap_vertex, cycleMap_interior] using h
          rcases (edgePoint_eq_vertex_iff src dst (W.edges i) (orient (W.reverse i) t.1)
              (W.vertices j)).mp h' with ⟨h0, _⟩ | ⟨h1, _⟩
          · exact (orient_mem_intervalInterior t.2.1 t.2.2).1 h0
          · exact (orient_mem_intervalInterior t.2.1 t.2.2).2 h1
      | interior j s =>
          have h' : edgePoint src dst (W.edges i) (orient (W.reverse i) t.1) =
              edgePoint src dst (W.edges j) (orient (W.reverse j) s.1) := by
            simpa [cycleMap_vertex, cycleMap_interior] using h
          have he : W.edges i = W.edges j :=
            edge_eq_of_interior_edgePoint_eq src dst
              (orient_mem_intervalInterior t.2.1 t.2.2).1
              (orient_mem_intervalInterior t.2.1 t.2.2).2
              (orient_mem_intervalInterior s.2.1 s.2.2).1
              (orient_mem_intervalInterior s.2.1 s.2.2).2 h'
          have hij : i = j := W.edges_injective he
          rw [hij] at h' ⊢
          have hpara : orient (W.reverse j) t.1 = orient (W.reverse j) s.1 :=
            edgePoint_injective src dst (W.edges j) (W.src_ne_dst j) h'
          have hts : t = s := Subtype.ext (orient_injective (W.reverse j) hpara)
          rw [hts]

/-! ## The spatial realization -/

/-- The spatial realization of a cycle walk under one supplied global embedding. -/
def cycleSpatialMap (W : CycleWalk src dst) (G : EmbeddedGraph src dst) :
    C(CycleDomain W.n, EmbeddedReal3) :=
  G.map.comp ⟨cycleMap W, cycleMap_continuous W⟩

@[simp] theorem cycleSpatialMap_apply (W : CycleWalk src dst) (G : EmbeddedGraph src dst)
    (x : CycleDomain W.n) :
    cycleSpatialMap W G x = G.map (cycleMap W x) := rfl

@[simp] theorem cycleSpatialMap_vertex (W : CycleWalk src dst) (G : EmbeddedGraph src dst)
    (i : Fin W.n) :
    cycleSpatialMap W G (Realization.vertex i) = G.conformation (W.vertices i) := rfl

@[simp] theorem cycleSpatialMap_interior (W : CycleWalk src dst) (G : EmbeddedGraph src dst)
    (i : Fin W.n) (t : {t : I // t ≠ 0 ∧ t ≠ 1}) :
    cycleSpatialMap W G (Realization.interior i t) =
      G.arc (W.edges i) (orient (W.reverse i) t.1) := rfl

/-- The spatial cycle map is continuous. -/
theorem cycleSpatialMap_continuous (W : CycleWalk src dst) (G : EmbeddedGraph src dst) :
    Continuous (cycleSpatialMap W G) :=
  (cycleSpatialMap W G).continuous

/-- **The spatial cycle map is injective** under one global embedding. -/
theorem cycleSpatialMap_injective (W : CycleWalk src dst) (G : EmbeddedGraph src dst) :
    Function.Injective (cycleSpatialMap W G) := by
  intro x y h
  have h' : G.map (cycleMap W x) = G.map (cycleMap W y) := by
    simpa [cycleSpatialMap] using h
  exact cycleMap_injective W (G.injective h')

/-- The bundled existence statement: one global embedding yields one continuous injective spatial
map of the cycle whose values at the cyclic vertices are the embedded vertex positions. -/
theorem exists_continuous_injective_cycleMap (W : CycleWalk src dst) (G : EmbeddedGraph src dst) :
    ∃ f : C(CycleDomain W.n, EmbeddedReal3), Function.Injective f ∧
      ∀ i : Fin W.n, f (Realization.vertex i) = G.conformation (W.vertices i) :=
  ⟨cycleSpatialMap W G, cycleSpatialMap_injective W G, fun _ => rfl⟩

/-! ## Exact image description -/

/-- The open interior of the unit interval: parameters that are neither endpoint. -/
def intervalInterior : Set I :=
  {t : I | t ≠ 0 ∧ t ≠ 1}

/-- The spatial image of a cycle walk: the cycle vertex positions together with the interiors of
the selected edge arcs. -/
def cycleImage (W : CycleWalk src dst) (G : EmbeddedGraph src dst) : Set EmbeddedReal3 :=
  G.conformation '' Set.range W.vertices ∪
    ⋃ i : Fin W.n, G.arc (W.edges i) '' intervalInterior

@[simp] theorem mem_intervalInterior {t : I} :
    t ∈ intervalInterior ↔ t ≠ 0 ∧ t ≠ 1 := Iff.rfl

/-- Membership characterization of the cycle image. -/
theorem mem_cycleImage_iff (W : CycleWalk src dst) (G : EmbeddedGraph src dst)
    {x : EmbeddedReal3} :
    x ∈ cycleImage W G ↔
      (∃ i : Fin W.n, x = G.conformation (W.vertices i)) ∨
        ∃ (i : Fin W.n) (t : I), t ∈ intervalInterior ∧ x = G.arc (W.edges i) t := by
  constructor
  · intro hx
    simp only [cycleImage, Set.mem_union, Set.mem_image, Set.mem_iUnion, Set.mem_range] at hx
    rcases hx with ⟨v, hvrange, hvx⟩ | ⟨i, hi⟩
    · obtain ⟨i, rfl⟩ := hvrange
      exact Or.inl ⟨i, hvx.symm⟩
    · obtain ⟨t, ht, htx⟩ := hi
      exact Or.inr ⟨i, t, ht, htx.symm⟩
  · rintro (⟨i, rfl⟩ | ⟨i, t, ht, rfl⟩)
    · simp only [cycleImage]
      exact Set.mem_union_left _ (Set.mem_image_of_mem _ (Set.mem_range.mpr ⟨i, rfl⟩))
    · simp only [cycleImage]
      exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨i, Set.mem_image_of_mem _ ht⟩)

/-- **Exact image of the spatial cycle map**: exactly the cycle vertices plus the interiors of the
selected edge arcs. -/
theorem cycleSpatialMap_range (W : CycleWalk src dst) (G : EmbeddedGraph src dst) :
    Set.range (cycleSpatialMap W G) = cycleImage W G := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [mem_cycleImage_iff]
    cases y with
    | vertex i => exact Or.inl ⟨i, rfl⟩
    | interior i t =>
        exact Or.inr ⟨i, orient (W.reverse i) t.1,
          orient_mem_intervalInterior t.2.1 t.2.2, rfl⟩
  · intro hx
    rw [mem_cycleImage_iff] at hx
    rcases hx with ⟨i, rfl⟩ | ⟨i, t, ht, rfl⟩
    · exact ⟨Realization.vertex i, by simp⟩
    · refine ⟨Realization.interior i ⟨orient (W.reverse i) t,
        (orient_mem_intervalInterior ht.1 ht.2).1,
        (orient_mem_intervalInterior ht.1 ht.2).2⟩, ?_⟩
      have hinv : orient (W.reverse i) (orient (W.reverse i) t) = t :=
        orient_involutive (W.reverse i) t
      simp [cycleSpatialMap, cycleMap, hinv]

/-! ## Intersections of two cycles in one embedded graph -/

/-- If the two cycle walks select disjoint families of edge occurrences, then the interiors of
their arcs are disjoint.  This is *derived* from the global embedding: two arc interiors of
distinct edges cannot meet (`edge_eq_of_interior_meet`). -/
theorem arc_interiors_disjoint_of_edges_ne (W₁ W₂ : CycleWalk src dst)
    (G : EmbeddedGraph src dst)
    (hedges : ∀ (i : Fin W₁.n) (j : Fin W₂.n), W₁.edges i ≠ W₂.edges j)
    (i : Fin W₁.n) (j : Fin W₂.n) :
    Disjoint (G.arc (W₁.edges i) '' intervalInterior)
      (G.arc (W₂.edges j) '' intervalInterior) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  rw [Set.mem_image] at hx1 hx2
  obtain ⟨s, hs, hsx⟩ := hx1
  obtain ⟨t, ht, htx⟩ := hx2
  exact hedges i j
    (G.edge_eq_of_interior_meet hs.1 hs.2 ht.1 ht.2 (hsx.trans htx.symm))

/-- **Intersection of two cycle images.**  If the interiors of the selected edge arcs are pairwise
disjoint, the intersection of the two spatial images is exactly the image of the common vertices.
All non-vertex collisions are excluded by the global embedding; disjointness is only needed for the
edge-interior part. -/
theorem cycleImage_inter_eq_commonVertexImages
    (W₁ W₂ : CycleWalk src dst) (G : EmbeddedGraph src dst)
    (hdisj : ∀ (i : Fin W₁.n) (j : Fin W₂.n),
      Disjoint (G.arc (W₁.edges i) '' intervalInterior)
        (G.arc (W₂.edges j) '' intervalInterior)) :
    cycleImage W₁ G ∩ cycleImage W₂ G =
      G.conformation '' (Set.range W₁.vertices ∩ Set.range W₂.vertices) := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_inter_iff] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [mem_cycleImage_iff] at hx1 hx2
    rcases hx1 with ⟨i, rfl⟩ | ⟨i, t, ht, rfl⟩
    · rcases hx2 with ⟨j, hxj⟩ | ⟨j, s, hs, hxj⟩
      · have hv : W₁.vertices i = W₂.vertices j := G.atom_injective hxj
        rw [Set.mem_image]
        exact ⟨W₁.vertices i, ⟨⟨i, rfl⟩, ⟨j, hv.symm⟩⟩, rfl⟩
      · exact absurd hxj.symm
          (G.interior_avoids_atoms (W₂.edges j) s hs.1 hs.2 (W₁.vertices i))
    · rcases hx2 with ⟨j, hxj⟩ | ⟨j, s, hs, hxj⟩
      · exact absurd hxj
          (G.interior_avoids_atoms (W₁.edges i) t ht.1 ht.2 (W₂.vertices j))
      · exfalso
        have hmemB : G.arc (W₂.edges j) s ∈ G.arc (W₂.edges j) '' intervalInterior :=
          Set.mem_image_of_mem _ hs
        have hmemA : G.arc (W₂.edges j) s ∈ G.arc (W₁.edges i) '' intervalInterior := by
          rw [← hxj]
          exact Set.mem_image_of_mem _ ht
        have hd := hdisj i j
        rw [Set.disjoint_left] at hd
        exact hd hmemA hmemB
  · rintro ⟨v, ⟨hv1, hv2⟩, rfl⟩
    constructor
    · rw [mem_cycleImage_iff]
      rcases Set.mem_range.mp hv1 with ⟨i, hi⟩
      exact Or.inl ⟨i, by rw [← hi]⟩
    · rw [mem_cycleImage_iff]
      rcases Set.mem_range.mp hv2 with ⟨j, hj⟩
      exact Or.inl ⟨j, by rw [← hj]⟩

/-- The edge-disjoint form of the intersection theorem: it suffices that the two walks select
pairwise distinct edge occurrences. -/
theorem cycleImage_inter_eq_commonVertexImages_of_edgeDisjoint
    (W₁ W₂ : CycleWalk src dst) (G : EmbeddedGraph src dst)
    (hedges : ∀ (i : Fin W₁.n) (j : Fin W₂.n), W₁.edges i ≠ W₂.edges j) :
    cycleImage W₁ G ∩ cycleImage W₂ G =
      G.conformation '' (Set.range W₁.vertices ∩ Set.range W₂.vertices) :=
  cycleImage_inter_eq_commonVertexImages W₁ W₂ G
    (fun i j => arc_interiors_disjoint_of_edges_ne W₁ W₂ G hedges i j)

/-- If two edge-disjoint cycle walks share exactly one vertex, their spatial images meet in exactly
that vertex position. -/
theorem cycleImage_inter_eq_singleton_of_sole_common_vertex
    (W₁ W₂ : CycleWalk src dst) (G : EmbeddedGraph src dst)
    (hedges : ∀ (i : Fin W₁.n) (j : Fin W₂.n), W₁.edges i ≠ W₂.edges j)
    (v₀ : V) (hcommon : Set.range W₁.vertices ∩ Set.range W₂.vertices = {v₀}) :
    cycleImage W₁ G ∩ cycleImage W₂ G = {G.conformation v₀} := by
  rw [cycleImage_inter_eq_commonVertexImages_of_edgeDisjoint W₁ W₂ G hedges, hcommon,
    Set.image_singleton]

/-- If two edge-disjoint cycle walks share no vertex, their spatial images are disjoint. -/
theorem cycleImage_inter_eq_empty_of_no_common_vertex
    (W₁ W₂ : CycleWalk src dst) (G : EmbeddedGraph src dst)
    (hedges : ∀ (i : Fin W₁.n) (j : Fin W₂.n), W₁.edges i ≠ W₂.edges j)
    (hcommon : Set.range W₁.vertices ∩ Set.range W₂.vertices = ∅) :
    cycleImage W₁ G ∩ cycleImage W₂ G = ∅ := by
  rw [cycleImage_inter_eq_commonVertexImages_of_edgeDisjoint W₁ W₂ G hedges, hcommon,
    Set.image_empty]

/-! ## Compactness of the cycle domain and the closed embedding

The abstract cycle domain is a continuous surjective image of the compact raw coproduct domain, so
it is compact.  Hence `cycleSpatialMap` is a closed topological embedding into real three-space. -/

section CompactEmbedding

open OrganicStereoEmbeddedGraphRealization

/-- The abstract cycle domain is compact: it is the continuous surjective image of the compact raw
coproduct domain of the gluing map. -/
theorem compactSpace_cycleDomain (n : ℕ) : CompactSpace (CycleDomain n) := by
  refine ⟨?_⟩
  rw [← (glue_surjective (id : Fin n → Fin n) (cycleNext n)).range_eq]
  exact isCompact_range (glue_continuous (id : Fin n → Fin n) (cycleNext n))

/-- **The spatial cycle map is a closed topological embedding.**  Under one supplied global
embedding, the finite cycle domain embeds homeomorphically in real three-space.  This is the
honest topological content available without proving a separate circle-homeomorphism theorem. -/
theorem cycleSpatialMap_isClosedEmbedding (W : CycleWalk src dst) (G : EmbeddedGraph src dst) :
    Topology.IsClosedEmbedding (cycleSpatialMap W G) := by
  haveI : CompactSpace (CycleDomain W.n) := compactSpace_cycleDomain W.n
  exact (cycleSpatialMap W G).continuous.isClosedEmbedding (cycleSpatialMap_injective W G)

/-- The same map as a topological embedding. -/
theorem cycleSpatialMap_isEmbedding (W : CycleWalk src dst) (G : EmbeddedGraph src dst) :
    Topology.IsEmbedding (cycleSpatialMap W G) :=
  (cycleSpatialMap_isClosedEmbedding W G).isEmbedding

end CompactEmbedding

end

end OrganicStereoEmbeddedCycleRealization
end TetraStereo.OneCenter
