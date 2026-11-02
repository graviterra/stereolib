import TetraStereo.OneCenter.OrganicStereoFiniteGraphEmbedding
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.FinRange
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Prescribed atom positions for finite loopless multigraphs

`OrganicStereoFiniteGraphEmbedding` proves that every finite loopless multigraph admits an
`EmbeddedGraph src dst` into real three-space, but it puts the vertices on a moment curve: the
conformation of the resulting embedding is a fixed function of the vertex labels, not a supplied
family of atom positions.

This module removes that restriction.  For every finite loopless multigraph, and for every
*injective* family of prescribed atom positions `position : V → EmbeddedReal3`, it constructs an
`EmbeddedGraph src dst` whose conformation is exactly `position`.

## Construction

The edges are enumerated by `edgeIndex : E → ℕ`.  A private waypoint `wpNat j` is chosen for the
`j`-th edge, recursively in `j`.  The arc of the edge `e` is the two-segment polyline

`position (src e) → wpNat (edgeIndex e) → position (dst e)`.

When `wpNat j` is chosen, the already constructed waypoints `wpNat i` for `i < j` are available.
The point `wpNat j` must avoid, for every old edge `i < j` and every choice of far endpoints
`Fᵢ ∈ {position (src i), position (dst i)}`, `Fⱼ ∈ {position (src j), position (dst j)}`, the
affine span of `{Fⱼ, Fᵢ, wpNat i}`; it must avoid the affine span of `{F, position q, position q}`
for every atom `q` and every far endpoint `F` of edge `j`; and it must avoid the line through the
two endpoints of edge `j`.  All these forbidden sets are affine subspaces of dimension at most
two.  They are encoded by a nonzero affine functional `φ` with constant value `c` on the three
points, and the requirement is `φ (wpNat j) ≠ c`, which is stronger than non-membership and hence
sufficient even in the degenerate collinear or coincident cases.

A direction `u` with `φ u ≠ 0` for every forbidden functional is chosen first.  Then the
waypoints `t • u` avoid every forbidden set for all but finitely many `t`, so one parameter `t`
works for all of them simultaneously.

## Why it is injective

Each interior point of the edge `e` lies on exactly one half-segment, parametrized from its far
atom endpoint `F ∈ {position (src e), position (dst e)}` to the private waypoint:
`lineMap F (wpNat (edgeIndex e)) θ` with `θ ∈ (0, 1]`.  If two such half-segments of distinct
edges `i` and `j` meet, the elementary affine lemma `inAffineSpan3_of_lineMap_eq` forces the
later waypoint into the affine span of the earlier waypoint and the two far atoms, contradicting
the avoidance condition.  A point of an edge equal to an atom is excluded by the atom targets.
The two halves of one edge meet only at the waypoint, and the condition that the waypoint is off
the line through the two endpoints rules out any other common point; a scalar identity shows that
the two halves meet only at the waypoint.  Parallel edges have distinct private waypoints because
the avoidance condition for the later edge contains the earlier waypoint among its three points.

## Scope

This module proves structural existence only: it constructs a global continuous injective map of
the graph realization with the prescribed atom positions.  It makes no claim about knot types,
bond lengths, bond angles, energies, or any other chemical or geometric property of the arcs.
-/

namespace TetraStereo.OneCenter
namespace OrganicStereoPrescribedPositionGraphEmbedding

open scoped unitInterval
open AffineMap
open OrganicStereoEmbeddedGraphRealization

noncomputable section

universe u v

variable {V : Type u} {E : Type v}

/-! ## Affine geometry in three-space -/

/-- `P` lies in the affine span of the three points `X`, `Y`, `Z`. -/
def InAffineSpan3 (X Y Z P : EmbeddedReal3) : Prop :=
  ∃ a b c : ℝ, a + b + c = 1 ∧ P = a • X + b • Y + c • Z

/-- A point `P` on the affine line from `X` to `Y`, at a parameter `u ≠ 0`, lies in the affine
span of `X`, `Y`, and `Z`, for every `Z`.

This is the key elementary affine fact behind the collision analysis: the second endpoint of a
half-segment, together with the far endpoint of the other half-segment, spans a forbidden affine
set.  The statement is uniform in all degeneracies (coincident and collinear points included). -/
theorem inAffineSpan3_of_lineMap_eq {X P Y Z : EmbeddedReal3} {u v : ℝ}
    (hu : u ≠ 0) (h : lineMap X P u = lineMap Y Z v) :
    InAffineSpan3 X Y Z P := by
  rw [lineMap_apply_module, lineMap_apply_module] at h
  have huP : u • P = (1 - v) • Y + v • Z - (1 - u) • X := by
    rw [← h]
    module
  have hP : P = (1 / u) • ((1 - v) • Y + v • Z - (1 - u) • X) := by
    calc P = (1 / u) • (u • P) := by
          rw [smul_smul, one_div, inv_mul_cancel₀ hu, one_smul]
      _ = (1 / u) • ((1 - v) • Y + v • Z - (1 - u) • X) := by rw [huP]
  refine ⟨(u - 1) / u, (1 - v) / u, v / u, ?_, ?_⟩
  · field_simp [hu]
    ring
  · rw [hP]
    module

/-- The affine line from `X` to `Y` is the same set as the affine line from `Y` to `X`, with the
complementary parameter. -/
theorem lineMap_eq_swap (X Y : EmbeddedReal3) (u : ℝ) :
    lineMap X Y u = lineMap Y X (1 - u) := by
  rw [lineMap_apply_module, lineMap_apply_module]
  module

/-- The value of the second half of a polyline, written with the far atom first. -/
theorem lineMap_second (X Y : EmbeddedReal3) (t : ℝ) :
    lineMap X Y (2 * t - 1) = lineMap Y X (2 - 2 * t) := by
  rw [lineMap_eq_swap]
  congr 1
  ring

/-- A nondegenerate affine segment is injective in its parameter. -/
theorem lineMap_injective_of_ne {X Y : EmbeddedReal3} (hXY : X ≠ Y) {u v : ℝ}
    (h : lineMap X Y u = lineMap X Y v) : u = v := by
  rw [lineMap_apply_module, lineMap_apply_module] at h
  have hmain : (u - v) • (Y - X) = 0 := by
    have h0 : ((1 - u) • X + u • Y) - ((1 - v) • X + v • Y) = 0 := sub_eq_zero.mpr h
    rw [← h0]
    module
  have hYX : Y - X ≠ 0 := sub_ne_zero.mpr (Ne.symm hXY)
  rcases smul_eq_zero.mp hmain with h' | h'
  · linarith
  · exact absurd h' hYX

/-! ## Nonzero affine functionals through three points -/

/-- Two difference vectors span a proper subspace of three-space. -/
theorem span_pair_range_lt_top (Y Z : EmbeddedReal3) :
    Submodule.span ℝ (Set.range (![Y, Z] : Fin 2 → EmbeddedReal3)) < ⊤ := by
  apply Submodule.lt_top_of_finrank_lt_finrank
  have hdim : Module.finrank ℝ (Submodule.span ℝ (Set.range (![Y, Z] : Fin 2 → EmbeddedReal3))) ≤ 2 := by
    have h := finrank_range_le_card (R := ℝ) (M := EmbeddedReal3) (![Y, Z] : Fin 2 → EmbeddedReal3)
    have h' : (Set.range (![Y, Z] : Fin 2 → EmbeddedReal3)).finrank ℝ ≤ 2 := by
      simpa using h
    simpa [Set.finrank] using h'
  have h3 : Module.finrank ℝ EmbeddedReal3 = 3 := finrank_euclideanSpace_fin
  omega

/-- For arbitrary three points `X`, `Y`, `Z` of three-space there is a nonzero affine functional
which takes the same value `c` on all three.  No distinctness or non-collinearity hypothesis is
needed: the affine span of three points has dimension at most two, so it is contained in a proper
linear hyperplane of directions, which yields a nonzero linear functional annihilating all the
difference vectors. -/
theorem exists_affine_functional (X Y Z : EmbeddedReal3) :
    ∃ (φ : EmbeddedReal3 →ₗ[ℝ] ℝ) (c : ℝ),
      φ ≠ 0 ∧ φ X = c ∧ φ Y = c ∧ φ Z = c := by
  let W : Submodule ℝ EmbeddedReal3 :=
    Submodule.span ℝ (Set.range (![Y - X, Z - X] : Fin 2 → EmbeddedReal3))
  have hWlt : W < ⊤ := by
    have hspan := span_pair_range_lt_top (Y - X) (Z - X)
    simpa [W] using hspan
  obtain ⟨φ, hφ0, hker⟩ := Submodule.exists_le_ker_of_lt_top W hWlt
  refine ⟨φ, φ X, hφ0, rfl, ?_, ?_⟩
  · have hmemW : Y - X ∈ W :=
      Submodule.subset_span (show Y - X ∈ Set.range (![Y - X, Z - X] : Fin 2 → EmbeddedReal3) from
        ⟨0, by simp⟩)
    have h0 : φ (Y - X) = 0 := by
      simpa using hker hmemW
    rw [map_sub] at h0
    linarith
  · have hmemW : Z - X ∈ W :=
      Submodule.subset_span (show Z - X ∈ Set.range (![Y - X, Z - X] : Fin 2 → EmbeddedReal3) from
        ⟨1, by simp⟩)
    have h0 : φ (Z - X) = 0 := by
      simpa using hker hmemW
    rw [map_sub] at h0
    linarith

/-- The affine data of a triple of points: a nonzero linear functional and the common value `c`
taken on the three points.  Its level set `φ = c` is an affine plane containing all three points. -/
structure PlaneData (X Y Z : EmbeddedReal3) where
  /-- The nonzero affine functional. -/
  φ : EmbeddedReal3 →ₗ[ℝ] ℝ
  /-- The common value of the functional on the three points. -/
  c : ℝ
  /-- The functional is nonzero. -/
  nonzero : φ ≠ 0
  /-- The functional takes value `c` on the first point. -/
  evalX : φ X = c
  /-- The functional takes value `c` on the second point. -/
  evalY : φ Y = c
  /-- The functional takes value `c` on the third point. -/
  evalZ : φ Z = c

/-- A choice of affine functional through three points. -/
noncomputable def planeData (X Y Z : EmbeddedReal3) : PlaneData X Y Z :=
  let h := exists_affine_functional X Y Z
  { φ := h.choose
    c := h.choose_spec.choose
    nonzero := h.choose_spec.choose_spec.1
    evalX := h.choose_spec.choose_spec.2.1
    evalY := h.choose_spec.choose_spec.2.2.1
    evalZ := h.choose_spec.choose_spec.2.2.2 }

/-- A point at which the affine functional differs from its constant value is outside the affine
span of the three points.  This sufficient condition is uniform in all degeneracies. -/
theorem planeData_not_inAffineSpan3 {X Y Z P : EmbeddedReal3} (pd : PlaneData X Y Z)
    (h : pd.φ P ≠ pd.c) : ¬ InAffineSpan3 X Y Z P := by
  rintro ⟨a, b, d, hsum, hP⟩
  apply h
  have hcalc : pd.φ P = (a + b + d) * pd.c := by
    rw [hP]
    simp only [map_add, map_smul, pd.evalX, pd.evalY, pd.evalZ, smul_eq_mul]
    ring
  rw [hcalc, hsum, one_mul]

/-- An abbreviation for a triple of points of three-space, used as the key of a forbidden affine
set. -/
abbrev PointTriple : Type := EmbeddedReal3 × EmbeddedReal3 × EmbeddedReal3

/-- The affine data attached to a triple. -/
noncomputable def tripleData (T : PointTriple) : PlaneData T.1 T.2.1 T.2.2 :=
  planeData T.1 T.2.1 T.2.2

/-! ## A common direction for finitely many functionals -/

/-- Given a finite list of nonzero linear functionals on three-space, there is a direction on
which none of them vanishes.  The proof is an induction on the list: along the affine line through
the current point in a direction where the new functional is nonzero, each old functional can
vanish at at most one parameter, and the new one at exactly one parameter, so a parameter outside
the finite forbidden set is available. -/
theorem exists_direction (fs : List (EmbeddedReal3 →ₗ[ℝ] ℝ)) :
    (∀ φ ∈ fs, φ ≠ 0) → ∃ d : EmbeddedReal3, ∀ φ ∈ fs, φ d ≠ 0 := by
  induction fs with
  | nil => intro _; exact ⟨0, by simp⟩
  | cons ψ fs ih =>
      intro hfs
      have htail : ∀ φ ∈ fs, φ ≠ 0 := fun φ hφ => hfs φ (by simp [hφ])
      obtain ⟨d, hd⟩ := ih htail
      have hψ : ψ ≠ 0 := hfs ψ (by simp)
      obtain ⟨u, hu⟩ : ∃ u : EmbeddedReal3, ψ u ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hψ (LinearMap.ext hcon)
      let forbidden : Finset ℝ :=
        (fs.map fun φ => - (φ d) / (φ u)).toFinset ∪ {(- (ψ d) / (ψ u) : ℝ)}
      obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset forbidden
      refine ⟨d + t • u, ?_⟩
      intro φ hφ
      rcases List.mem_cons.mp hφ with hφψ | hφtail
      · subst φ
        intro hzero
        have hfac : ψ d + t * ψ u = 0 := by
          simpa [map_add, map_smul, smul_eq_mul] using hzero
        have htval : t = - (ψ d) / (ψ u) := by
          rw [eq_div_iff hu]
          linarith
        have hmem : - (ψ d) / (ψ u) ∈ forbidden := by
          simp [forbidden]
        exact ht (by simpa [htval] using hmem)
      · intro hzero
        have hdφ : φ d ≠ 0 := hd φ hφtail
        have hfac : φ d + t * φ u = 0 := by
          simpa [map_add, map_smul, smul_eq_mul] using hzero
        have huφ : φ u ≠ 0 := by
          intro hu0
          rw [hu0, mul_zero, add_zero] at hfac
          exact hdφ hfac
        have htval : t = - (φ d) / (φ u) := by
          rw [eq_div_iff huφ]
          linarith
        have hmem : - (φ d) / (φ u) ∈ forbidden := by
          simp only [forbidden, Finset.mem_union, Finset.mem_singleton]
          exact Or.inl (List.mem_toFinset.mpr (List.mem_map.mpr ⟨φ, hφtail, rfl⟩))
        exact ht (by simpa [htval] using hmem)

/-! ## The two halves of one edge meet only at the waypoint -/

/-- If the two half-segments from the two endpoint atoms of one edge to its waypoint meet, then
the waypoint lies on the line through the two atoms, unless the common point is the waypoint
itself (in which case both parameters are `1`).  The scalar identity is proved by a case split on
`θ = η`: equality of the parameters gives collinearity of the far atoms with the waypoint; the
other case expresses the waypoint as an affine combination of the two atoms. -/
theorem same_edge_two_halves {A B W : EmbeddedReal3}
    (hABW : ¬ InAffineSpan3 A B B W) (hAB : A ≠ B)
    {θ η : ℝ} (_hθ : θ ≠ 0) (_hη : η ≠ 0)
    (h : lineMap A W θ = lineMap B W η) : θ = 1 ∧ η = 1 := by
  rw [lineMap_apply_module, lineMap_apply_module] at h
  have hmain : (θ - η) • W = (1 - η) • B - (1 - θ) • A := by
    have h1 : ((1 - θ) • A + θ • W) - ((1 - η) • B + η • W) = 0 := sub_eq_zero.mpr h
    have h2 : ((1 - θ) • A + θ • W) - ((1 - η) • B + η • W) =
        (θ - η) • W - ((1 - η) • B - (1 - θ) • A) := by module
    rw [h2] at h1
    exact sub_eq_zero.mp h1
  by_cases hθη : θ = η
  · subst hθη
    have h3 : (1 - θ) • B - (1 - θ) • A = 0 := by
      rw [← hmain]
      simp
    have hzero : (1 - θ) • (B - A) = 0 := by
      rw [smul_sub]
      exact h3
    have hBA : B - A ≠ 0 := sub_ne_zero.mpr (Ne.symm hAB)
    have hcoef : 1 - θ = 0 := by
      rcases smul_eq_zero.mp hzero with h' | h'
      · exact h'
      · exact absurd h' hBA
    exact ⟨by linarith, by linarith⟩
  · exfalso
    apply hABW
    have hs : θ - η ≠ 0 := sub_ne_zero.mpr hθη
    refine ⟨-((1 - θ) / (θ - η)), (1 - η) / (θ - η), 0, ?_, ?_⟩
    · field_simp
      ring
    · have hW : W = (1 / (θ - η)) • ((1 - η) • B - (1 - θ) • A) := by
        have h1 : (1 / (θ - η)) • ((θ - η) • W) = W := by
          rw [smul_smul, one_div, inv_mul_cancel₀ hs, one_smul]
        rw [← h1, hmain]
      rw [hW]
      module

/-! ## Construction parameters -/

section Construction

variable [Fintype V] [Fintype E]

/-! ### Edge enumeration -/

/-- The number of edges. -/
def edgeCount : ℕ := Fintype.card E

/-- The index of an edge in the chosen finite enumeration. -/
def edgeIndex (e : E) : ℕ := ((Fintype.equivFin E) e).val

/-- The edge at a given index. -/
def edgeAt (i : ℕ) (hi : i < edgeCount (E := E)) : E :=
  (Fintype.equivFin E).symm ⟨i, hi⟩

/-- Every edge index is below the edge count. -/
theorem edgeIndex_lt (e : E) : edgeIndex e < edgeCount (E := E) :=
  ((Fintype.equivFin E) e).isLt

/-- The enumeration is injective on edges. -/
theorem edgeIndex_injective : Function.Injective (fun e : E => edgeIndex e) := by
  intro e f h
  have h' : (Fintype.equivFin E) e = (Fintype.equivFin E) f := Fin.ext h
  exact (Fintype.equivFin E).injective h'

/-- Re-indexing the edge at an edge index recovers the edge, for any proof of the index bound. -/
@[simp] theorem edgeAt_edgeIndex (e : E) (h : edgeIndex e < edgeCount (E := E)) :
    edgeAt (edgeIndex e) h = e := by
  unfold edgeAt
  have hfin : (⟨edgeIndex e, h⟩ : Fin (Fintype.card E)) = (Fintype.equivFin E) e := by
    apply Fin.ext
    rfl
  rw [hfin]
  exact (Fintype.equivFin E).symm_apply_apply e

/-! ### The list of forbidden affine sets -/

/-- An enumeration of all atoms, avoiding the need for decidable equality on `V`. -/
def atomsList : List V :=
  (List.finRange (Fintype.card V)).map fun k => (Fintype.equivFin V).symm k

/-- Every atom occurs in the enumeration. -/
theorem atomsList_mem (q : V) : q ∈ atomsList (V := V) := by
  refine List.mem_map.mpr ⟨Fintype.equivFin V q, List.mem_finRange _, ?_⟩
  simp

/-- The forbidden affine sets coming from the already constructed edges `i < j`, for the edge at
index `j`.  Each old half-segment contributes its far atom and its waypoint, and the new edge
contributes each of its two far atoms. -/
def oldTriples (src : E → V) (dst : E → V) (position : V → EmbeddedReal3)
    (j : ℕ) (hj : j < edgeCount (E := E)) (w : ℕ → EmbeddedReal3) : List PointTriple :=
  (List.range j).flatMap fun i =>
    if hi : i < j then
      let e := edgeAt i (lt_trans hi hj)
      let Aj := position (src (edgeAt j hj))
      let Bj := position (dst (edgeAt j hj))
      [(Aj, position (src e), w i), (Aj, position (dst e), w i),
       (Bj, position (src e), w i), (Bj, position (dst e), w i)]
    else []

/-- The forbidden affine sets which keep the waypoint away from all atom positions. -/
def atomTriples (src : E → V) (dst : E → V) (position : V → EmbeddedReal3)
    (j : ℕ) (hj : j < edgeCount (E := E)) : List PointTriple :=
  (atomsList (V := V)).flatMap fun q =>
    [(position (src (edgeAt j hj)), position q, position q),
     (position (dst (edgeAt j hj)), position q, position q)]

/-- The full list of forbidden affine sets for the waypoint of edge `j`. -/
def targetList (src : E → V) (dst : E → V) (position : V → EmbeddedReal3)
    (j : ℕ) (hj : j < edgeCount (E := E)) (w : ℕ → EmbeddedReal3) : List PointTriple :=
  oldTriples src dst position j hj w ++
    (atomTriples src dst position j hj ++
      [(position (src (edgeAt j hj)), position (dst (edgeAt j hj)),
        position (dst (edgeAt j hj)))])

/-- A triple of the form `(far atom of the new edge, far atom of an old edge, old waypoint)` is
forbidden. -/
theorem mem_oldTriples_of {src : E → V} {dst : E → V} {position : V → EmbeddedReal3}
    {j : ℕ} {hj : j < edgeCount (E := E)} {w : ℕ → EmbeddedReal3} {i : ℕ} (hi : i < j)
    {Fi Fj : EmbeddedReal3}
    (hFi : Fi = position (src (edgeAt i (lt_trans hi hj))) ∨
      Fi = position (dst (edgeAt i (lt_trans hi hj))))
    (hFj : Fj = position (src (edgeAt j hj)) ∨ Fj = position (dst (edgeAt j hj))) :
    (Fj, Fi, w i) ∈ oldTriples src dst position j hj w := by
  rcases hFi with rfl | rfl <;> rcases hFj with rfl | rfl <;>
    exact List.mem_flatMap.mpr
      ⟨i, List.mem_range.mpr hi, by dsimp only; simp [dif_pos hi]⟩

/-- A triple of the form `(source atom of the new edge, atom, atom)` is forbidden. -/
theorem mem_atomTriples_src {src : E → V} {dst : E → V} {position : V → EmbeddedReal3}
    {j : ℕ} {hj : j < edgeCount (E := E)} (q : V) :
    (position (src (edgeAt j hj)), position q, position q) ∈
      atomTriples src dst position j hj := by
  refine List.mem_flatMap.mpr ⟨q, atomsList_mem q, ?_⟩
  simp

/-- A triple of the form `(destination atom of the new edge, atom, atom)` is forbidden. -/
theorem mem_atomTriples_dst {src : E → V} {dst : E → V} {position : V → EmbeddedReal3}
    {j : ℕ} {hj : j < edgeCount (E := E)} (q : V) :
    (position (dst (edgeAt j hj)), position q, position q) ∈
      atomTriples src dst position j hj := by
  refine List.mem_flatMap.mpr ⟨q, atomsList_mem q, ?_⟩
  simp

/-- The line through the two endpoints of the new edge is forbidden. -/
theorem mem_targetList_line {src : E → V} {dst : E → V} {position : V → EmbeddedReal3}
    {j : ℕ} {hj : j < edgeCount (E := E)} {w : ℕ → EmbeddedReal3} :
    (position (src (edgeAt j hj)), position (dst (edgeAt j hj)),
      position (dst (edgeAt j hj))) ∈ targetList src dst position j hj w :=
  List.mem_append_right _ (List.mem_append_right _ (by simp))

/-- A forbidden old triple is a forbidden triple. -/
theorem mem_targetList_old {src : E → V} {dst : E → V} {position : V → EmbeddedReal3}
    {j : ℕ} {hj : j < edgeCount (E := E)} {w : ℕ → EmbeddedReal3} {T : PointTriple}
    (hT : T ∈ oldTriples src dst position j hj w) :
    T ∈ targetList src dst position j hj w :=
  List.mem_append_left _ hT

/-- A forbidden atom triple is a forbidden triple. -/
theorem mem_targetList_atom {src : E → V} {dst : E → V} {position : V → EmbeddedReal3}
    {j : ℕ} {hj : j < edgeCount (E := E)} {w : ℕ → EmbeddedReal3} {T : PointTriple}
    (hT : T ∈ atomTriples src dst position j hj) :
    T ∈ targetList src dst position j hj w :=
  List.mem_append_right _ (List.mem_append_left _ hT)

/-! ### Choosing a waypoint -/

/-- The canonical extension of a recursion hypothesis on the indices `m < j` to a total function,
with junk value `0` outside the range.  The recursive definition of `wpNat` uses exactly this
function, so that the step at `j` sees the previously constructed waypoints as a plain function. -/
noncomputable def heapFun (j : ℕ) (w : ∀ m, m < j → EmbeddedReal3) : ℕ → EmbeddedReal3 :=
  fun m => if hm : m < j then w m hm else 0

/-- The private waypoint of the edge at index `j`, chosen to avoid every affine set in the target
list.  The direction avoids all the functionals; the parameter avoids the finitely many values at
which one of the functionals would hit its constant value. -/
noncomputable def chooseWaypoint (src : E → V) (dst : E → V) (position : V → EmbeddedReal3)
    (j : ℕ) (hj : j < edgeCount (E := E)) (w : ℕ → EmbeddedReal3) :
    {p : EmbeddedReal3 // ∀ T ∈ targetList src dst position j hj w,
      (tripleData T).φ p ≠ (tripleData T).c} := by
  classical
  let Ts := targetList src dst position j hj w
  let fs : List (EmbeddedReal3 →ₗ[ℝ] ℝ) := Ts.map fun T => (tripleData T).φ
  have hfs : ∀ φ ∈ fs, φ ≠ 0 := by
    intro φ hφ
    simp only [fs, List.mem_map] at hφ
    obtain ⟨T, hT, hTeq⟩ := hφ
    rw [← hTeq]
    exact (tripleData T).nonzero
  let u : EmbeddedReal3 := Classical.choose (exists_direction fs hfs)
  have hu : ∀ φ ∈ fs, φ u ≠ 0 := Classical.choose_spec (exists_direction fs hfs)
  let forbidden : Finset ℝ := (Ts.map fun T => (tripleData T).c / (tripleData T).φ u).toFinset
  let t : ℝ := Classical.choose (Infinite.exists_notMem_finset forbidden)
  have ht : t ∉ forbidden := Classical.choose_spec (Infinite.exists_notMem_finset forbidden)
  refine ⟨t • u, ?_⟩
  intro T hT
  have hφmem : (tripleData T).φ ∈ fs := List.mem_map.mpr ⟨T, hT, rfl⟩
  have huT : (tripleData T).φ u ≠ 0 := hu _ hφmem
  have hmem : (tripleData T).c / (tripleData T).φ u ∈ forbidden :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨T, hT, rfl⟩)
  intro hc
  have hval : t = (tripleData T).c / (tripleData T).φ u := by
    have h1 : t * ((tripleData T).φ u) = (tripleData T).c := by
      simpa [map_smul, smul_eq_mul] using hc
    field_simp [huT]
    linarith
  exact ht (by simpa [hval] using hmem)

/-! ### The recursive waypoint sequence -/

/-- One step of the recursive waypoint construction. -/
noncomputable def wpStep (src : E → V) (dst : E → V) (position : V → EmbeddedReal3) :
    ∀ n : ℕ, (∀ m : ℕ, m < n → EmbeddedReal3) → EmbeddedReal3 :=
  fun n ih =>
    if hn : n < Fintype.card E then
      (chooseWaypoint src dst position n (by simpa [edgeCount] using hn) (heapFun n ih)).1
    else 0

/-- The private waypoint of the edge at index `j`, defined by strong recursion on `j`. -/
noncomputable def wpNat (src : E → V) (dst : E → V) (position : V → EmbeddedReal3)
    (j : ℕ) : EmbeddedReal3 :=
  Nat.strongRecOn j (wpStep src dst position)

/-- The defining equation of `wpNat`. -/
theorem wpNat_eq (src : E → V) (dst : E → V) (position : V → EmbeddedReal3) (j : ℕ) :
    wpNat src dst position j =
      if hj : j < edgeCount (E := E) then
        (chooseWaypoint src dst position j hj
          (heapFun j (fun m _ => wpNat src dst position m))).1
      else 0 := by
  change Nat.lt_wfRel.wf.fix (wpStep src dst position) j =
    if hj : j < edgeCount (E := E) then
      (chooseWaypoint src dst position j hj
        (heapFun j (fun m _ => Nat.lt_wfRel.wf.fix (wpStep src dst position) m))).1
    else 0
  rw [WellFounded.fix_eq]
  rfl

/-- The value of the canonical extension of the waypoint sequence on an index in its range. -/
theorem heapFun_wpNat_apply (src : E → V) (dst : E → V) (position : V → EmbeddedReal3)
    {j i : ℕ} (hi : i < j) :
    heapFun j (fun m _ => wpNat src dst position m) i = wpNat src dst position i := by
  simp [heapFun, hi]

/-- Every waypoint avoids every affine set in its target list. -/
theorem wpNat_spec (src : E → V) (dst : E → V) (position : V → EmbeddedReal3)
    (j : ℕ) (hj : j < edgeCount (E := E)) :
    ∀ T ∈ targetList src dst position j hj
        (heapFun j (fun m _ => wpNat src dst position m)),
      (tripleData T).φ (wpNat src dst position j) ≠ (tripleData T).c := by
  rw [wpNat_eq, dif_pos hj]
  exact (chooseWaypoint src dst position j hj
    (heapFun j (fun m _ => wpNat src dst position m))).2

/-! ### The public avoidance statements -/

/-- Later waypoints stay out of the affine span of the far atoms of an old edge and its waypoint. -/
theorem wpNat_avoids_old (src : E → V) (dst : E → V) (position : V → EmbeddedReal3)
    {j : ℕ} (hj : j < edgeCount (E := E)) {i : ℕ} (hi : i < j)
    {Fi Fj : EmbeddedReal3}
    (hFi : Fi = position (src (edgeAt i (lt_trans hi hj))) ∨
      Fi = position (dst (edgeAt i (lt_trans hi hj))))
    (hFj : Fj = position (src (edgeAt j hj)) ∨ Fj = position (dst (edgeAt j hj))) :
    ¬ InAffineSpan3 Fj Fi (wpNat src dst position i) (wpNat src dst position j) := by
  have hmem := mem_oldTriples_of (src := src) (dst := dst) (position := position)
    (j := j) (hj := hj) (w := heapFun j (fun m _ => wpNat src dst position m)) hi hFi hFj
  have hmemT := mem_targetList_old (src := src) (dst := dst) (position := position)
    (j := j) (hj := hj) (w := heapFun j (fun m _ => wpNat src dst position m)) hmem
  have hspec := wpNat_spec src dst position j hj _ hmemT
  rw [heapFun_wpNat_apply src dst position hi] at hspec
  exact planeData_not_inAffineSpan3 (tripleData (Fj, Fi, wpNat src dst position i)) hspec

/-- Later waypoints stay away from the line from the source atom to each atom. -/
theorem wpNat_avoids_src_atom (src : E → V) (dst : E → V) (position : V → EmbeddedReal3)
    (j : ℕ) (hj : j < edgeCount (E := E)) (q : V) :
    ¬ InAffineSpan3 (position (src (edgeAt j hj))) (position q) (position q)
      (wpNat src dst position j) := by
  have hmem := mem_atomTriples_src (src := src) (dst := dst) (position := position)
    (j := j) (hj := hj) q
  have hmemT := mem_targetList_atom (src := src) (dst := dst) (position := position)
    (j := j) (hj := hj) (w := heapFun j (fun m _ => wpNat src dst position m)) hmem
  have hspec := wpNat_spec src dst position j hj _ hmemT
  exact planeData_not_inAffineSpan3
    (tripleData (position (src (edgeAt j hj)), position q, position q)) hspec

/-- Later waypoints stay away from the line from the destination atom to each atom. -/
theorem wpNat_avoids_dst_atom (src : E → V) (dst : E → V) (position : V → EmbeddedReal3)
    (j : ℕ) (hj : j < edgeCount (E := E)) (q : V) :
    ¬ InAffineSpan3 (position (dst (edgeAt j hj))) (position q) (position q)
      (wpNat src dst position j) := by
  have hmem := mem_atomTriples_dst (src := src) (dst := dst) (position := position)
    (j := j) (hj := hj) q
  have hmemT := mem_targetList_atom (src := src) (dst := dst) (position := position)
    (j := j) (hj := hj) (w := heapFun j (fun m _ => wpNat src dst position m)) hmem
  have hspec := wpNat_spec src dst position j hj _ hmemT
  exact planeData_not_inAffineSpan3
    (tripleData (position (dst (edgeAt j hj)), position q, position q)) hspec

/-- The waypoint of the edge at index `j` lies off the line through the two endpoint atoms. -/
theorem wpNat_avoids_line (src : E → V) (dst : E → V) (position : V → EmbeddedReal3)
    (j : ℕ) (hj : j < edgeCount (E := E)) :
    ¬ InAffineSpan3 (position (src (edgeAt j hj))) (position (dst (edgeAt j hj)))
      (position (dst (edgeAt j hj))) (wpNat src dst position j) := by
  have hmem := mem_targetList_line (src := src) (dst := dst) (position := position)
    (j := j) (hj := hj) (w := heapFun j (fun m _ => wpNat src dst position m))
  have hspec := wpNat_spec src dst position j hj _ hmem
  exact planeData_not_inAffineSpan3
    (tripleData (position (src (edgeAt j hj)), position (dst (edgeAt j hj)),
      position (dst (edgeAt j hj)))) hspec

/-- Distinct edges have distinct private waypoints, including parallel edges with the same
endpoints. -/
theorem edgeWaypoint_injective (src : E → V) (dst : E → V) (position : V → EmbeddedReal3) :
    Function.Injective (fun e : E => wpNat src dst position (edgeIndex e)) := by
  intro e f hEq
  by_contra hne
  have hif : edgeIndex e ≠ edgeIndex f := fun hh => hne (edgeIndex_injective hh)
  have hEq' : wpNat src dst position (edgeIndex e) = wpNat src dst position (edgeIndex f) := hEq
  rcases lt_or_gt_of_ne hif with hij | hji
  · apply wpNat_avoids_old (src := src) (dst := dst) (position := position)
      (j := edgeIndex f) (edgeIndex_lt f) (i := edgeIndex e) hij
      (Fi := position (src e)) (Fj := position (src f))
      (Or.inl (by simp [edgeAt_edgeIndex])) (Or.inl (by simp [edgeAt_edgeIndex]))
    rw [← hEq']
    exact ⟨0, 0, 1, by ring, by simp⟩
  · apply wpNat_avoids_old (src := src) (dst := dst) (position := position)
      (j := edgeIndex e) (edgeIndex_lt e) (i := edgeIndex f) hji
      (Fi := position (src f)) (Fj := position (src e))
      (Or.inl (by simp [edgeAt_edgeIndex])) (Or.inl (by simp [edgeAt_edgeIndex]))
    rw [hEq']
    exact ⟨0, 0, 1, by ring, by simp⟩

/-! ### The edge polyline -/

/-- The private waypoint of an edge. -/
def edgeWaypoint (src : E → V) (dst : E → V) (position : V → EmbeddedReal3) (e : E) :
    EmbeddedReal3 :=
  wpNat src dst position (edgeIndex e)

/-- The two-segment polyline of an edge: source atom, private waypoint, destination atom. -/
def edgePath (src : E → V) (dst : E → V) (position : V → EmbeddedReal3) (e : E) :
    Path (position (src e)) (position (dst e)) :=
  (Path.segment (position (src e)) (edgeWaypoint src dst position e)).trans
    (Path.segment (edgeWaypoint src dst position e) (position (dst e)))

/-- The left endpoint of an edge polyline. -/
@[simp] theorem edgePath_zero (src : E → V) (dst : E → V) (position : V → EmbeddedReal3)
    (e : E) : edgePath src dst position e 0 = position (src e) :=
  (edgePath src dst position e).source

/-- The right endpoint of an edge polyline. -/
@[simp] theorem edgePath_one (src : E → V) (dst : E → V) (position : V → EmbeddedReal3)
    (e : E) : edgePath src dst position e 1 = position (dst e) :=
  (edgePath src dst position e).target

/-- The explicit value of the edge polyline. -/
theorem edgePath_apply (src : E → V) (dst : E → V) (position : V → EmbeddedReal3)
    (e : E) (t : I) :
    edgePath src dst position e t =
      if (t : ℝ) ≤ 1 / 2 then
        lineMap (position (src e)) (edgeWaypoint src dst position e) (2 * (t : ℝ))
      else
        lineMap (edgeWaypoint src dst position e) (position (dst e)) (2 * (t : ℝ) - 1) := by
  rw [edgePath, Path.trans_apply]
  split_ifs with h <;> simp

/-- The value on the first half, written from the source atom to the waypoint. -/
theorem edgePath_apply_first (src : E → V) (dst : E → V) (position : V → EmbeddedReal3)
    (e : E) (t : I) (ht : (t : ℝ) ≤ 1 / 2) :
    edgePath src dst position e t =
      lineMap (position (src e)) (edgeWaypoint src dst position e) (2 * (t : ℝ)) := by
  rw [edgePath_apply, if_pos ht]

/-- The value on the second half, written from the destination atom to the waypoint. -/
theorem edgePath_apply_second (src : E → V) (dst : E → V) (position : V → EmbeddedReal3)
    (e : E) (t : I) (ht : ¬ (t : ℝ) ≤ 1 / 2) :
    edgePath src dst position e t =
      lineMap (position (dst e)) (edgeWaypoint src dst position e) (2 - 2 * (t : ℝ)) := by
  rw [edgePath_apply, if_neg ht, lineMap_second]

/-- The first-half parameter of an interior point is nonzero. -/
theorem two_mul_interior_ne_zero (t : {t : I // t ≠ 0 ∧ t ≠ 1}) :
    2 * (t.1 : ℝ) ≠ 0 := by
  intro h
  exact t.2.1 (Subtype.ext (by linarith : (t.1 : ℝ) = 0))

/-- The second-half parameter of an interior point is nonzero. -/
theorem two_sub_two_mul_interior_ne_zero (t : {t : I // t ≠ 0 ∧ t ≠ 1}) :
    2 - 2 * (t.1 : ℝ) ≠ 0 := by
  intro h
  exact t.2.2 (Subtype.ext (by linarith : (t.1 : ℝ) = 1))

/-! ### The global map and its continuity -/

/-- The global map on the graph-indexed normal form. -/
def globalMap (src : E → V) (dst : E → V) (position : V → EmbeddedReal3) :
    Realization src dst → EmbeddedReal3
  | Realization.vertex w => position w
  | Realization.interior e t => edgePath src dst position e t.1

/-- The value of the global map at a vertex. -/
@[simp] theorem globalMap_vertex (src : E → V) (dst : E → V) (position : V → EmbeddedReal3)
    (w : V) : globalMap src dst position (Realization.vertex w) = position w := rfl

/-- The value of the global map at an interior point. -/
@[simp] theorem globalMap_interior (src : E → V) (dst : E → V) (position : V → EmbeddedReal3)
    (e : E) (t : {t : I // t ≠ 0 ∧ t ≠ 1}) :
    globalMap src dst position (Realization.interior e t) = edgePath src dst position e t.1 := rfl

/-- The raw map on the coproduct domain. -/
def rawMap (src : E → V) (dst : E → V) (position : V → EmbeddedReal3) :
    RawDomain V E → EmbeddedReal3 :=
  Sum.elim (fun p : RawVertex V => position p.1)
    (fun q : RawInterval E => edgePath src dst position q.1 q.2)

/-- The raw map is continuous. -/
theorem rawMap_continuous (src : E → V) (dst : E → V) (position : V → EmbeddedReal3) :
    Continuous (rawMap src dst position) := by
  rw [rawMap, continuous_sumElim]
  constructor
  · apply continuous_sigma
    intro w
    change Continuous (fun _ : Unit => position w)
    exact continuous_const
  · apply continuous_sigma
    intro e
    change Continuous (fun t : I => edgePath src dst position e t)
    exact (edgePath src dst position e).continuous

/-- The composite of the global map with the gluing map. -/
theorem globalMap_comp_glue (src : E → V) (dst : E → V) (position : V → EmbeddedReal3) :
    globalMap src dst position ∘ glue src dst = rawMap src dst position := by
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
        change globalMap src dst position (Realization.vertex (src e)) =
          edgePath src dst position e 0
        rw [globalMap_vertex, edgePath_zero]
      · by_cases h1 : t = 1
        · subst h1
          rw [Function.comp_apply, glue_inr, glueInterval_one]
          change globalMap src dst position (Realization.vertex (dst e)) =
            edgePath src dst position e 1
          rw [globalMap_vertex, edgePath_one]
        · rw [Function.comp_apply, glue_inr, glueInterval_interior src dst e t h0 h1]
          rfl

/-- The global map is continuous in the coinduced topology. -/
theorem globalMap_continuous (src : E → V) (dst : E → V) (position : V → EmbeddedReal3) :
    Continuous (globalMap src dst position) := by
  rw [continuous_iff_continuous_comp_glue src dst (globalMap src dst position)]
  rw [globalMap_comp_glue]
  exact rawMap_continuous src dst position

/-! ### Injectivity -/

/-- An atom is never an interior point of an edge polyline. -/
theorem globalMap_vertex_ne_interior (src : E → V) (dst : E → V)
    (position : V → EmbeddedReal3) (w : V) (e : E)
    (t : {t : I // t ≠ 0 ∧ t ≠ 1}) :
    globalMap src dst position (Realization.vertex w) ≠
      globalMap src dst position (Realization.interior e t) := by
  intro h
  have h' : position w = edgePath src dst position e t.1 := by simpa using h
  by_cases ht : (t.1 : ℝ) ≤ 1 / 2
  · have hval : edgePath src dst position e t.1 =
        lineMap (position (src e)) (edgeWaypoint src dst position e) (2 * (t.1 : ℝ)) :=
      edgePath_apply_first src dst position e t.1 ht
    have heq : lineMap (position (src e)) (edgeWaypoint src dst position e) (2 * (t.1 : ℝ)) =
        lineMap (position w) (position w) (1 : ℝ) := by
      rw [← hval, ← h']
      simp
    have hspan := inAffineSpan3_of_lineMap_eq (X := position (src e))
      (P := edgeWaypoint src dst position e) (Y := position w) (Z := position w)
      (u := 2 * (t.1 : ℝ)) (v := 1) (two_mul_interior_ne_zero t) heq
    have hbad := wpNat_avoids_src_atom src dst position (edgeIndex e) (edgeIndex_lt e) w
    have hspan' : InAffineSpan3 (position (src e)) (position w) (position w)
        (wpNat src dst position (edgeIndex e)) := by
      simpa [edgeWaypoint] using hspan
    have hbad' : ¬ InAffineSpan3 (position (src e)) (position w) (position w)
        (wpNat src dst position (edgeIndex e)) := by
      simpa [edgeAt_edgeIndex] using hbad
    exact hbad' hspan'
  · have hval : edgePath src dst position e t.1 =
        lineMap (position (dst e)) (edgeWaypoint src dst position e) (2 - 2 * (t.1 : ℝ)) :=
      edgePath_apply_second src dst position e t.1 ht
    have heq : lineMap (position (dst e)) (edgeWaypoint src dst position e) (2 - 2 * (t.1 : ℝ)) =
        lineMap (position w) (position w) (1 : ℝ) := by
      rw [← hval, ← h']
      simp
    have hspan := inAffineSpan3_of_lineMap_eq (X := position (dst e))
      (P := edgeWaypoint src dst position e) (Y := position w) (Z := position w)
      (u := 2 - 2 * (t.1 : ℝ)) (v := 1) (two_sub_two_mul_interior_ne_zero t) heq
    have hbad := wpNat_avoids_dst_atom src dst position (edgeIndex e) (edgeIndex_lt e) w
    have hspan' : InAffineSpan3 (position (dst e)) (position w) (position w)
        (wpNat src dst position (edgeIndex e)) := by
      simpa [edgeWaypoint] using hspan
    have hbad' : ¬ InAffineSpan3 (position (dst e)) (position w) (position w)
        (wpNat src dst position (edgeIndex e)) := by
      simpa [edgeAt_edgeIndex] using hbad
    exact hbad' hspan'

set_option maxHeartbeats 2000000 in
/-- Interior points on the same edge are equal only for the same normal form. -/
theorem globalMap_interior_injective (src : E → V) (dst : E → V)
    (noLoops : ∀ e : E, src e ≠ dst e) (position : V → EmbeddedReal3)
    (hpos : Function.Injective position) {e f : E}
    {t s : {t : I // t ≠ 0 ∧ t ≠ 1}}
    (h : edgePath src dst position e t.1 = edgePath src dst position f s.1) :
    (Realization.interior (src := src) (dst := dst) e t) = Realization.interior f s := by
  have hAB : position (src e) ≠ position (dst e) := by
    intro hEq
    exact noLoops e (hpos hEq)
  have hline_e : ¬ InAffineSpan3 (position (src e)) (position (dst e)) (position (dst e))
      (edgeWaypoint src dst position e) := by
    have hbad := wpNat_avoids_line src dst position (edgeIndex e) (edgeIndex_lt e)
    simpa [edgeWaypoint, edgeAt_edgeIndex] using hbad
  have hAW : position (src e) ≠ edgeWaypoint src dst position e := by
    intro hEq
    apply hline_e
    rw [← hEq]
    exact ⟨1, 0, 0, by ring, by simp⟩
  have hWB : edgeWaypoint src dst position e ≠ position (dst e) := by
    intro hEq
    apply hline_e
    rw [hEq]
    exact ⟨0, 0, 1, by ring, by simp⟩
  by_cases hef : e = f
  · subst hef
    by_cases ht : (t.1 : ℝ) ≤ 1 / 2
    · by_cases hs : (s.1 : ℝ) ≤ 1 / 2
      · rw [edgePath_apply_first src dst position e t.1 ht,
          edgePath_apply_first src dst position e s.1 hs] at h
        have huv := lineMap_injective_of_ne hAW h
        have hts : t = s := by
          apply Subtype.ext
          apply Subtype.ext
          linarith
        subst hts
        rfl
      · exfalso
        rw [edgePath_apply_first src dst position e t.1 ht,
          edgePath_apply_second src dst position e s.1 hs] at h
        have hres := same_edge_two_halves hline_e hAB
          (two_mul_interior_ne_zero t) (two_sub_two_mul_interior_ne_zero s) h
        have hsval : (s.1 : ℝ) = 1 / 2 := by linarith [hres.2]
        exact hs (le_of_eq hsval)
    · by_cases hs : (s.1 : ℝ) ≤ 1 / 2
      · exfalso
        rw [edgePath_apply_second src dst position e t.1 ht,
          edgePath_apply_first src dst position e s.1 hs] at h
        have hres := same_edge_two_halves hline_e hAB
          (two_mul_interior_ne_zero s) (two_sub_two_mul_interior_ne_zero t) h.symm
        have htval : (t.1 : ℝ) = 1 / 2 := by linarith [hres.2]
        exact ht (le_of_eq htval)
      · rw [edgePath_apply_second src dst position e t.1 ht,
          edgePath_apply_second src dst position e s.1 hs] at h
        have huv := lineMap_injective_of_ne (Ne.symm hWB) h
        have hts : t = s := by
          apply Subtype.ext
          apply Subtype.ext
          linarith
        subst hts
        rfl
  · have hif : edgeIndex e ≠ edgeIndex f := by
      intro hh
      exact hef (edgeIndex_injective hh)
    rcases lt_or_gt_of_ne hif with hij | hji
    · -- edge `e` is earlier: use the target of edge `f`
      by_cases ht : (t.1 : ℝ) ≤ 1 / 2
      · by_cases hs : (s.1 : ℝ) ≤ 1 / 2
        · rw [edgePath_apply_first src dst position e t.1 ht,
            edgePath_apply_first src dst position f s.1 hs] at h
          have hcoll : InAffineSpan3 (position (src f)) (position (src e))
              (edgeWaypoint src dst position e) (edgeWaypoint src dst position f) :=
            inAffineSpan3_of_lineMap_eq (two_mul_interior_ne_zero s) h.symm
          have hcoll' : InAffineSpan3 (position (src f)) (position (src e))
              (wpNat src dst position (edgeIndex e)) (wpNat src dst position (edgeIndex f)) := by
            simpa [edgeWaypoint] using hcoll
          exact absurd hcoll' (wpNat_avoids_old src dst position (edgeIndex_lt f) hij
            (Fi := position (src e)) (Fj := position (src f))
            (Or.inl (by simp [edgeAt_edgeIndex])) (Or.inl (by simp [edgeAt_edgeIndex])))
        · rw [edgePath_apply_first src dst position e t.1 ht,
            edgePath_apply_second src dst position f s.1 hs] at h
          have hcoll : InAffineSpan3 (position (dst f)) (position (src e))
              (edgeWaypoint src dst position e) (edgeWaypoint src dst position f) :=
            inAffineSpan3_of_lineMap_eq (two_sub_two_mul_interior_ne_zero s) h.symm
          have hcoll' : InAffineSpan3 (position (dst f)) (position (src e))
              (wpNat src dst position (edgeIndex e)) (wpNat src dst position (edgeIndex f)) := by
            simpa [edgeWaypoint] using hcoll
          exact absurd hcoll' (wpNat_avoids_old src dst position (edgeIndex_lt f) hij
            (Fi := position (src e)) (Fj := position (dst f))
            (Or.inl (by simp [edgeAt_edgeIndex])) (Or.inr (by simp [edgeAt_edgeIndex])))
      · by_cases hs : (s.1 : ℝ) ≤ 1 / 2
        · rw [edgePath_apply_second src dst position e t.1 ht,
            edgePath_apply_first src dst position f s.1 hs] at h
          have hcoll : InAffineSpan3 (position (src f)) (position (dst e))
              (edgeWaypoint src dst position e) (edgeWaypoint src dst position f) :=
            inAffineSpan3_of_lineMap_eq (two_mul_interior_ne_zero s) h.symm
          have hcoll' : InAffineSpan3 (position (src f)) (position (dst e))
              (wpNat src dst position (edgeIndex e)) (wpNat src dst position (edgeIndex f)) := by
            simpa [edgeWaypoint] using hcoll
          exact absurd hcoll' (wpNat_avoids_old src dst position (edgeIndex_lt f) hij
            (Fi := position (dst e)) (Fj := position (src f))
            (Or.inr (by simp [edgeAt_edgeIndex])) (Or.inl (by simp [edgeAt_edgeIndex])))
        · rw [edgePath_apply_second src dst position e t.1 ht,
            edgePath_apply_second src dst position f s.1 hs] at h
          have hcoll : InAffineSpan3 (position (dst f)) (position (dst e))
              (edgeWaypoint src dst position e) (edgeWaypoint src dst position f) :=
            inAffineSpan3_of_lineMap_eq (two_sub_two_mul_interior_ne_zero s) h.symm
          have hcoll' : InAffineSpan3 (position (dst f)) (position (dst e))
              (wpNat src dst position (edgeIndex e)) (wpNat src dst position (edgeIndex f)) := by
            simpa [edgeWaypoint] using hcoll
          exact absurd hcoll' (wpNat_avoids_old src dst position (edgeIndex_lt f) hij
            (Fi := position (dst e)) (Fj := position (dst f))
            (Or.inr (by simp [edgeAt_edgeIndex])) (Or.inr (by simp [edgeAt_edgeIndex])))
    · -- edge `f` is earlier: use the target of edge `e`
      by_cases ht : (t.1 : ℝ) ≤ 1 / 2
      · by_cases hs : (s.1 : ℝ) ≤ 1 / 2
        · rw [edgePath_apply_first src dst position e t.1 ht,
            edgePath_apply_first src dst position f s.1 hs] at h
          have hcoll : InAffineSpan3 (position (src e)) (position (src f))
              (edgeWaypoint src dst position f) (edgeWaypoint src dst position e) :=
            inAffineSpan3_of_lineMap_eq (two_mul_interior_ne_zero t) h
          have hcoll' : InAffineSpan3 (position (src e)) (position (src f))
              (wpNat src dst position (edgeIndex f)) (wpNat src dst position (edgeIndex e)) := by
            simpa [edgeWaypoint] using hcoll
          exact absurd hcoll' (wpNat_avoids_old src dst position (edgeIndex_lt e) hji
            (Fi := position (src f)) (Fj := position (src e))
            (Or.inl (by simp [edgeAt_edgeIndex])) (Or.inl (by simp [edgeAt_edgeIndex])))
        · rw [edgePath_apply_first src dst position e t.1 ht,
            edgePath_apply_second src dst position f s.1 hs] at h
          have hcoll : InAffineSpan3 (position (src e)) (position (dst f))
              (edgeWaypoint src dst position f) (edgeWaypoint src dst position e) :=
            inAffineSpan3_of_lineMap_eq (two_mul_interior_ne_zero t) h
          have hcoll' : InAffineSpan3 (position (src e)) (position (dst f))
              (wpNat src dst position (edgeIndex f)) (wpNat src dst position (edgeIndex e)) := by
            simpa [edgeWaypoint] using hcoll
          exact absurd hcoll' (wpNat_avoids_old src dst position (edgeIndex_lt e) hji
            (Fi := position (dst f)) (Fj := position (src e))
            (Or.inr (by simp [edgeAt_edgeIndex])) (Or.inl (by simp [edgeAt_edgeIndex])))
      · by_cases hs : (s.1 : ℝ) ≤ 1 / 2
        · rw [edgePath_apply_second src dst position e t.1 ht,
            edgePath_apply_first src dst position f s.1 hs] at h
          have hcoll : InAffineSpan3 (position (dst e)) (position (src f))
              (edgeWaypoint src dst position f) (edgeWaypoint src dst position e) :=
            inAffineSpan3_of_lineMap_eq (two_sub_two_mul_interior_ne_zero t) h
          have hcoll' : InAffineSpan3 (position (dst e)) (position (src f))
              (wpNat src dst position (edgeIndex f)) (wpNat src dst position (edgeIndex e)) := by
            simpa [edgeWaypoint] using hcoll
          exact absurd hcoll' (wpNat_avoids_old src dst position (edgeIndex_lt e) hji
            (Fi := position (src f)) (Fj := position (dst e))
            (Or.inl (by simp [edgeAt_edgeIndex])) (Or.inr (by simp [edgeAt_edgeIndex])))
        · rw [edgePath_apply_second src dst position e t.1 ht,
            edgePath_apply_second src dst position f s.1 hs] at h
          have hcoll : InAffineSpan3 (position (dst e)) (position (dst f))
              (edgeWaypoint src dst position f) (edgeWaypoint src dst position e) :=
            inAffineSpan3_of_lineMap_eq (two_sub_two_mul_interior_ne_zero t) h
          have hcoll' : InAffineSpan3 (position (dst e)) (position (dst f))
              (wpNat src dst position (edgeIndex f)) (wpNat src dst position (edgeIndex e)) := by
            simpa [edgeWaypoint] using hcoll
          exact absurd hcoll' (wpNat_avoids_old src dst position (edgeIndex_lt e) hji
            (Fi := position (dst f)) (Fj := position (dst e))
            (Or.inr (by simp [edgeAt_edgeIndex])) (Or.inr (by simp [edgeAt_edgeIndex])))

/-- The global map is injective. -/
theorem globalMap_injective (src : E → V) (dst : E → V)
    (noLoops : ∀ e : E, src e ≠ dst e) (position : V → EmbeddedReal3)
    (hpos : Function.Injective position) :
    Function.Injective (globalMap src dst position) := by
  intro x y h
  cases x with
  | vertex w =>
      cases y with
      | vertex w' =>
          have h' : position w = position w' := by simpa using h
          exact congrArg Realization.vertex (hpos h')
      | interior e t =>
          exact absurd h (globalMap_vertex_ne_interior src dst position w e t)
  | interior e t =>
      cases y with
      | vertex w =>
          exact absurd h.symm (globalMap_vertex_ne_interior src dst position w e t)
      | interior f s =>
          apply globalMap_interior_injective src dst noLoops position hpos
          simpa using h

/-! ### The prescribed-position embedding -/

/-- **Structural existence of an embedded graph with prescribed atom positions.**  Every finite
loopless multigraph, with arbitrary endpoint maps `src dst : E → V`, and every injective family
`position : V → EmbeddedReal3` of atom positions, admits an `EmbeddedGraph src dst` whose
conformation is exactly `position`.  No paths, arcs, global maps or separation hypotheses are
supplied. -/
def prescribedPositionEmbedded (src : E → V) (dst : E → V)
    (noLoops : ∀ e : E, src e ≠ dst e) (position : V → EmbeddedReal3)
    (hpos : Function.Injective position) : EmbeddedGraph src dst where
  map := ⟨globalMap src dst position, globalMap_continuous src dst position⟩
  injective := globalMap_injective src dst noLoops position hpos

/-- The conformation of the prescribed-position embedding is exactly the supplied position
family. -/
theorem conformation_equality (src : E → V) (dst : E → V)
    (noLoops : ∀ e : E, src e ≠ dst e) (position : V → EmbeddedReal3)
    (hpos : Function.Injective position) :
    (prescribedPositionEmbedded src dst noLoops position hpos).conformation = position := rfl

/-- The pointwise form of `conformation_equality`. -/
@[simp] theorem prescribedPositionEmbedded_conformation_apply
    (src : E → V) (dst : E → V) (noLoops : ∀ e : E, src e ≠ dst e)
    (position : V → EmbeddedReal3) (hpos : Function.Injective position) (w : V) :
    (prescribedPositionEmbedded src dst noLoops position hpos).conformation w = position w := rfl

/-- The typed existence theorem: there is an embedded graph whose conformation is the prescribed
position family. -/
theorem exists_embeddedGraph_with_prescribed_conformation
    (src : E → V) (dst : E → V) (noLoops : ∀ e : E, src e ≠ dst e)
    (position : V → EmbeddedReal3) (hpos : Function.Injective position) :
    ∃ G : EmbeddedGraph src dst, G.conformation = position :=
  ⟨prescribedPositionEmbedded src dst noLoops position hpos,
    conformation_equality src dst noLoops position hpos⟩

end Construction

/-! ## A coplanar four-atom example with parallel edges -/

section Example

/-- Four distinct points in the plane `z = 0`, hence coplanar. -/
def coplanarPosition : Fin 4 → EmbeddedReal3 :=
  fun i => !₂[(i : ℝ), (i : ℝ) ^ 2, 0]

/-- The four coplanar points are distinct. -/
theorem coplanarPosition_injective : Function.Injective coplanarPosition := by
  intro i j h
  have h0 : (i : ℝ) = (j : ℝ) := by
    have := congrArg (fun x : EmbeddedReal3 => x 0) h
    simpa [coplanarPosition] using this
  have h1 : (i : ℕ) = (j : ℕ) := Nat.cast_injective h0
  exact Fin.ext h1

/-- Every one of the four points lies in the plane `z = 0`. -/
theorem coplanarPosition_plane (i : Fin 4) : coplanarPosition i 2 = 0 := by
  simp [coplanarPosition]

/-- The source map of the example graph: two parallel edges from vertex `0` to vertex `1`, and
one edge from vertex `2` to vertex `3`. -/
def exampleSrc : Fin 3 → Fin 4 := fun i => ![0, 0, 2] i

/-- The destination map of the example graph. -/
def exampleDst : Fin 3 → Fin 4 := fun i => ![1, 1, 3] i

/-- The example graph has no self-loops. -/
theorem exampleNoLoops : ∀ e : Fin 3, exampleSrc e ≠ exampleDst e := by
  intro e
  fin_cases e <;> decide

/-- The coplanar four-atom, parallel-edge example: there is an embedded graph with two parallel
edges whose conformation is the explicitly prescribed coplanar family. -/
theorem coplanar_parallel_example :
    ∃ G : EmbeddedGraph exampleSrc exampleDst, G.conformation = coplanarPosition :=
  exists_embeddedGraph_with_prescribed_conformation exampleSrc exampleDst exampleNoLoops
    coplanarPosition coplanarPosition_injective

/-- The pointwise conformation equality in the coplanar parallel-edge example. -/
theorem coplanar_parallel_example_conformation (w : Fin 4) :
    (prescribedPositionEmbedded exampleSrc exampleDst exampleNoLoops coplanarPosition
      coplanarPosition_injective).conformation w = coplanarPosition w :=
  prescribedPositionEmbedded_conformation_apply exampleSrc exampleDst exampleNoLoops
    coplanarPosition coplanarPosition_injective w

/-- The two parallel edges `0 → 1` receive distinct private waypoints. -/
theorem coplanar_parallel_waypoints_distinct :
    edgeWaypoint exampleSrc exampleDst coplanarPosition 0 ≠
      edgeWaypoint exampleSrc exampleDst coplanarPosition 1 := by
  intro h
  exact (by decide : (0 : Fin 3) ≠ 1)
    (edgeWaypoint_injective exampleSrc exampleDst coplanarPosition h)

end Example

/-! ## Kernel-level assertions -/

#check @prescribedPositionEmbedded
#check @conformation_equality
#check @prescribedPositionEmbedded_conformation_apply
#check @exists_embeddedGraph_with_prescribed_conformation
#check @coplanar_parallel_example
#check @coplanar_parallel_waypoints_distinct

#print axioms conformation_equality
#print axioms exists_embeddedGraph_with_prescribed_conformation
#print axioms edgeWaypoint_injective
#print axioms coplanar_parallel_example

end

end OrganicStereoPrescribedPositionGraphEmbedding
end TetraStereo.OneCenter
