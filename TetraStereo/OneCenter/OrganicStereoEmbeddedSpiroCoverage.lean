import TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage
import TetraStereo.OneCenter.IUPACP93SpiroAuthorityCarrier
import TetraStereo.OneCenter.OrganicStereoCyclicCarrierTransport
import TetraStereo.OneCenter.OrganicStereoAuthoritativeSourceBridge
import Mathlib.Data.List.Nodup
import Mathlib.Topology.UnitInterval

set_option autoImplicit false











































namespace TetraStereo.OneCenter

namespace OrganicStereoEmbeddedSpiroCoverage

open scoped unitInterval

open OrganicStereoEmbeddedGraphRealization
open OrganicStereoEmbeddedMolecularGraphCoverage
open P93AuthoritySpiroSystem

noncomputable section

/-! ## The source graph and its selected occurrences -/

/-- The reconstructed source graph of a certified authoritative input, over the shared atom
enumeration `Fin atomCount`.  This is the same chemical graph selected occurrences and embedding
are both taken from. -/
def sourceGraph (certified : CertifiedAuthoritativeChemicalInput) :
    FiniteAtomInteractionHypergraph (Fin certified.input.molecule.atomCount) :=
  reconstructGraph certified.input.molecule certified.structurallyWellFormed.1

@[simp] theorem sourceGraph_interactions (certified : CertifiedAuthoritativeChemicalInput) :
    (sourceGraph certified).interactions =
      reconstructInteractions certified.input.molecule.atomCount
        certified.input.molecule.interactions
        (interactionWellFormed certified.input.molecule
          certified.structurallyWellFormed.1) := rfl

/-! ## From a source binary bond to a selected occurrence -/

/-- The two kinds of binary bond selected by the source relation are exactly the selected pair
kinds of the finite encoding. -/
theorem isSelectedPairKind_of_binary (kind : SemanticInteractionKind)
    (binary : P93AuthorityBinaryInteractionKind kind) :
    SemanticInteractionKind.isSelectedPairKind kind = true := by
  cases kind <;>
    simp [P93AuthorityBinaryInteractionKind, SemanticInteractionKind.isSelectedPairKind] at binary ⊢

/-- The reconstructed participant list of an interaction is exactly as long as the stored one. -/
theorem reconstructParticipants_length (atomCount : Nat) (interaction : SemanticInteraction)
    (wellFormed : interaction.WellFormed atomCount) :
    (reconstructParticipants atomCount interaction wellFormed).length =
      interaction.participants.length := by
  unfold reconstructParticipants
  rw [List.length_pmap]

/-- Positional helper: the zeroth element of a list known to be the pair `[a, b]` is `a`. -/
theorem getElem_zero_of_eq_pair {α : Type} {l : List α} {a b : α}
    (pair : l = [a, b]) (h : 0 < l.length) : l[0]'h = a := by
  cases pair
  rfl

/-- Positional helper: the first element of a list known to be the pair `[a, b]` is `b`. -/
theorem getElem_one_of_eq_pair {α : Type} {l : List α} {a b : α}
    (pair : l = [a, b]) (h : 1 < l.length) : l[1]'h = b := by
  cases pair
  rfl

/-- The first positional endpoint of a selected occurrence, read from a participant list known to
be the ordered pair `[left, right]`. -/
theorem selectedSource_eq_of_participants {V : Type} [DecidableEq V] [Fintype V]
    {graph : FiniteAtomInteractionHypergraph V} (edge : SelectedBondIndex graph)
    {left right : V}
    (pair : (graph.interactions.get edge.1).1 = [left, right]) :
    selectedSource graph edge = left := by
  unfold selectedSource
  exact getElem_zero_of_eq_pair pair _

/-- The second positional endpoint of a selected occurrence, read from a participant list known to
be the ordered pair `[left, right]`. -/
theorem selectedTarget_eq_of_participants {V : Type} [DecidableEq V] [Fintype V]
    {graph : FiniteAtomInteractionHypergraph V} (edge : SelectedBondIndex graph)
    {left right : V}
    (pair : (graph.interactions.get edge.1).1 = [left, right]) :
    selectedTarget graph edge = right := by
  unfold selectedTarget
  exact getElem_one_of_eq_pair pair _

/-- **Source bond to oriented selected occurrence.**  A genuine binary bond between two bounded
source atoms is realized by a selected occurrence of the reconstructed source graph, with an
explicit orientation.  The selected occurrence reports an actual interaction occurrence; no
uniqueness is claimed (parallel occurrences remain distinct). -/
theorem exists_oriented_selectedBond_of_binaryBond
    (certified : CertifiedAuthoritativeChemicalInput)
    {left right : Nat}
    (leftBound : left < certified.input.molecule.atomCount)
    (rightBound : right < certified.input.molecule.atomCount)
    (bond : P93AuthorityBinaryBond certified.input left right) :
    ∃ (edge : SelectedBondIndex (sourceGraph certified)) (orientation : Bool),
      (if orientation then selectedTarget (sourceGraph certified) edge
        else selectedSource (sourceGraph certified) edge) =
          (⟨left, leftBound⟩ : Fin certified.input.molecule.atomCount) ∧
      (if orientation then selectedSource (sourceGraph certified) edge
        else selectedTarget (sourceGraph certified) edge) =
          (⟨right, rightBound⟩ : Fin certified.input.molecule.atomCount) := by
  obtain ⟨leftNeRight, interaction, memInteraction, kindBinary, pair⟩ := bond
  obtain ⟨i, bound, getEq⟩ := List.mem_iff_getElem.mp memInteraction
  let wellFormed := interactionWellFormed certified.input.molecule
    certified.structurallyWellFormed.1 interaction memInteraction
  have lengthTwo :
      (reconstructEdge certified.input.molecule.atomCount interaction wellFormed).1.length = 2 := by
    unfold reconstructEdge
    rw [reconstructParticipants_length]
    rcases pair with pair | pair <;> rw [pair] <;> rfl
  have kindSelected :
      SemanticInteractionKind.isSelectedPairKind
        (reconstructEdge certified.input.molecule.atomCount interaction wellFormed).2 = true := by
    simpa [reconstructEdge] using isSelectedPairKind_of_binary interaction.kind kindBinary
  have memGraph : reconstructEdge certified.input.molecule.atomCount interaction wellFormed ∈
      (sourceGraph certified).interactions := by
    unfold sourceGraph
    rw [reconstructGraph_interactions]
    exact List.mem_pmap.mpr ⟨interaction, memInteraction, rfl⟩
  obtain ⟨k, hk, hkGet⟩ := List.mem_iff_getElem.mp memGraph
  have getEq' : (sourceGraph certified).interactions.get ⟨k, hk⟩ =
      reconstructEdge certified.input.molecule.atomCount interaction wellFormed := by
    simpa only [List.get_eq_getElem] using hkGet
  let edge : SelectedBondIndex (sourceGraph certified) :=
    ⟨⟨k, hk⟩, by rw [getEq']; exact lengthTwo, by rw [getEq']; exact kindSelected⟩
  rcases pair with pair | pair
  · have pairGraph : ((sourceGraph certified).interactions.get edge.1).1 =
        [(⟨left, leftBound⟩ : Fin certified.input.molecule.atomCount),
          (⟨right, rightBound⟩ : Fin certified.input.molecule.atomCount)] := by
      rw [getEq']
      unfold reconstructEdge reconstructParticipants
      simp [pair]
    refine ⟨edge, false, ?_, ?_⟩
    · simpa using selectedSource_eq_of_participants edge pairGraph
    · simpa using selectedTarget_eq_of_participants edge pairGraph
  · have pairGraph : ((sourceGraph certified).interactions.get edge.1).1 =
        [(⟨right, rightBound⟩ : Fin certified.input.molecule.atomCount),
          (⟨left, leftBound⟩ : Fin certified.input.molecule.atomCount)] := by
      rw [getEq']
      unfold reconstructEdge reconstructParticipants
      simp [pair]
    refine ⟨edge, true, ?_, ?_⟩
    · simpa using selectedTarget_eq_of_participants edge pairGraph
    · simpa using selectedSource_eq_of_participants edge pairGraph

/-! ## The cycle successor on `Fin n` -/

/-- The cyclic successor on `Fin n`: `i ↦ i + 1` except at the last index, which wraps to `0`.
The definition only needs the inhabitedness of `Fin n` coming from `i` itself. -/
def cycleSucc {n : Nat} (i : Fin n) : Fin n :=
  if h : i.val + 1 < n then ⟨i.val + 1, h⟩
  else ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt⟩

theorem cycleSucc_val_of_lt {n : Nat} {i : Fin n} (h : i.val + 1 < n) :
    (cycleSucc i).val = i.val + 1 := by
  unfold cycleSucc
  rw [dif_pos h]

theorem cycleSucc_val_of_not_lt {n : Nat} {i : Fin n} (h : ¬ i.val + 1 < n) :
    (cycleSucc i).val = 0 := by
  unfold cycleSucc
  rw [dif_neg h]

/-- The cyclic successor of a cycle of length at least two is never the identity. -/
theorem cycleSucc_ne {n : Nat} (hn : 2 ≤ n) (i : Fin n) : cycleSucc i ≠ i := by
  intro h
  have hval : (cycleSucc i).val = i.val := congrArg Fin.val h
  have hi : i.val < n := i.isLt
  by_cases hlt : i.val + 1 < n
  · rw [cycleSucc_val_of_lt hlt] at hval
    omega
  · rw [cycleSucc_val_of_not_lt hlt] at hval
    omega

/-- The second cyclic successor of a cycle of length at least three is never the identity. -/
theorem cycleSucc_succ_ne {n : Nat} (hn : 3 ≤ n) (i : Fin n) :
    cycleSucc (cycleSucc i) ≠ i := by
  intro h
  have hval : (cycleSucc (cycleSucc i)).val = i.val := congrArg Fin.val h
  have hi : i.val < n := i.isLt
  have hsucc : (cycleSucc i).val < n := (cycleSucc i).isLt
  by_cases h1 : i.val + 1 < n
  · have hj : (cycleSucc i).val = i.val + 1 := cycleSucc_val_of_lt h1
    by_cases h2 : (cycleSucc i).val + 1 < n
    · rw [cycleSucc_val_of_lt h2] at hval
      omega
    · rw [cycleSucc_val_of_not_lt h2] at hval
      omega
  · have hj : (cycleSucc i).val = 0 := cycleSucc_val_of_not_lt h1
    by_cases h2 : (cycleSucc i).val + 1 < n
    · rw [cycleSucc_val_of_lt h2] at hval
      omega
    · rw [cycleSucc_val_of_not_lt h2] at hval
      omega

/-! ## A generic finite cycle walk and its embedded map -/

/-- A finite simple cycle in an abstract multigraph given by endpoint maps `src dst : E → V`.

The vertices are injective and the edge occurrence at position `i` joins vertex `i` to vertex
`i + 1` (cyclically).  Each edge occurrence carries its own `Bool` orientation, because a source
binary interaction may present its two participants in either order; a single global reversal
flag could not represent mixed orientations.  The walk does not assume edge injectivity: it is
derived below from vertex injectivity and endpoint distinctness. -/
structure CycleWalk {V E : Type*} (src dst : E → V) where
  /-- Number of cycle edges. -/
  n : Nat
  /-- Genuine cycles have at least three edges. -/
  n_ge_three : 3 ≤ n
  /-- The cycle vertices. -/
  vertices : Fin n → V
  /-- The cycle vertices are pairwise distinct. -/
  vertex_injective : Function.Injective vertices
  /-- One source edge occurrence per cycle position. -/
  edges : Fin n → E
  /-- Per-edge orientation: `true` reverses the source-to-target order. -/
  orientation : Fin n → Bool
  /-- Every used occurrence has distinct endpoints. -/
  src_ne_dst : ∀ e, src e ≠ dst e
  /-- The oriented first endpoint is the cycle vertex at position `i`. -/
  source_endpoint :
    ∀ i, (if orientation i then dst (edges i) else src (edges i)) = vertices i
  /-- The oriented second endpoint is the next cycle vertex. -/
  target_endpoint :
    ∀ i, (if orientation i then src (edges i) else dst (edges i)) =
      vertices (cycleSucc i)

namespace CycleWalk

variable {V E : Type*} {src dst : E → V}

/-- The oriented source endpoint of the occurrence at a cycle position. -/
def orientedSource (w : CycleWalk src dst) (i : Fin w.n) : V :=
  if w.orientation i then dst (w.edges i) else src (w.edges i)

/-- The oriented target endpoint of the occurrence at a cycle position. -/
def orientedTarget (w : CycleWalk src dst) (i : Fin w.n) : V :=
  if w.orientation i then src (w.edges i) else dst (w.edges i)

/-- The oriented endpoints at each cycle position are distinct. -/
theorem orientedSource_ne_orientedTarget (w : CycleWalk src dst) (i : Fin w.n) :
    w.orientedSource i ≠ w.orientedTarget i := by
  unfold orientedSource orientedTarget
  by_cases h : w.orientation i
  · simp only [if_pos h]
    exact (w.src_ne_dst (w.edges i)).symm
  · simp only [if_neg h]
    exact w.src_ne_dst (w.edges i)

/-- **Edge injectivity of a cycle walk.**  The same source occurrence cannot appear at two
different cycle positions: its two distinct endpoints would then have to match the two endpoint
pairs of those positions, forcing the cyclic two-step map to have a fixed point, which is
impossible for a cycle of length at least three. -/
theorem edges_injective (w : CycleWalk src dst) : Function.Injective w.edges := by
  intro i j hij
  by_cases same : w.orientation i = w.orientation j
  · have hvertices : w.vertices i = w.vertices j := by
      rw [← w.source_endpoint i, ← w.source_endpoint j]
      rw [hij, same]
    exact w.vertex_injective hvertices
  · have hfirst : w.vertices i = w.vertices (cycleSucc j) := by
      rw [← w.source_endpoint i, ← w.target_endpoint j]
      rw [hij]
      cases hi : w.orientation i <;> cases hj : w.orientation j <;> simp_all
    have hsecond : w.vertices (cycleSucc i) = w.vertices j := by
      rw [← w.target_endpoint i, ← w.source_endpoint j]
      rw [hij]
      cases hi : w.orientation i <;> cases hj : w.orientation j <;> simp_all
    have hi : i = cycleSucc j := w.vertex_injective hfirst
    have hj : cycleSucc i = j := w.vertex_injective hsecond
    have fixed : cycleSucc (cycleSucc j) = j := by
      calc cycleSucc (cycleSucc j) = cycleSucc i := by rw [hi]
        _ = j := hj
    exact absurd fixed (cycleSucc_succ_ne w.n_ge_three j)

/-- The orientation-adjusted parameter of an edge at cycle position `i`. -/
def orientationParam (w : CycleWalk src dst) (i : Fin w.n) (t : I) : I :=
  if w.orientation i then σ t else t

/-- The adjusted parameter is interior whenever the original parameter is. -/
theorem orientationParam_ne_zero (w : CycleWalk src dst) (i : Fin w.n) (t : I)
    (h0 : t ≠ 0) (h1 : t ≠ 1) : w.orientationParam i t ≠ 0 := by
  unfold orientationParam
  by_cases h : w.orientation i
  · rw [if_pos h]
    intro hzero
    exact h1 (unitInterval.symm_eq_zero.mp hzero)
  · rw [if_neg h]
    exact h0

/-- The adjusted parameter is not the right endpoint whenever the original parameter is interior. -/
theorem orientationParam_ne_one (w : CycleWalk src dst) (i : Fin w.n) (t : I)
    (h0 : t ≠ 0) (h1 : t ≠ 1) : w.orientationParam i t ≠ 1 := by
  unfold orientationParam
  by_cases h : w.orientation i
  · rw [if_pos h]
    intro hone
    exact h0 (unitInterval.symm_eq_one.mp hone)
  · rw [if_neg h]
    exact h1

/-- At a fixed orientation, adjusted parameters determine the original parameter. -/
theorem orientationParam_injective (w : CycleWalk src dst) (i : Fin w.n) {t s : I}
    (h : w.orientationParam i t = w.orientationParam i s) : t = s := by
  unfold orientationParam at h
  by_cases ho : w.orientation i
  · rw [if_pos ho, if_pos ho] at h
    exact unitInterval.symm_bijective.injective h
  · rw [if_neg ho, if_neg ho] at h
    exact h

end CycleWalk

/-- The canonical cycle realization of length `n`: the vertices and the edge occurrences are both
`Fin n`, with identity source and cyclic successor destination. -/
abbrev CycleDomain (n : Nat) : Type :=
  Realization (fun i : Fin n => i) (cycleSucc (n := n))

namespace CycleWalk

variable {V E : Type*} {src dst : E → V}

/-- The point map of a cycle walk into the supplied global embedding.  Vertices go to the
embedding's conformation; an oriented edge interior goes to the embedding's arc at the
orientation-adjusted parameter. -/
def mapFun (w : CycleWalk src dst) (G : EmbeddedGraph src dst) :
    CycleDomain w.n → EmbeddedReal3
  | Realization.vertex i => G.conformation (w.vertices i)
  | Realization.interior i t => G.arc (w.edges i) (w.orientationParam i t.1)

@[simp] theorem mapFun_vertex (w : CycleWalk src dst) (G : EmbeddedGraph src dst)
    (i : Fin w.n) :
    w.mapFun G (Realization.vertex i) = G.conformation (w.vertices i) := rfl

@[simp] theorem mapFun_interior (w : CycleWalk src dst) (G : EmbeddedGraph src dst)
    (i : Fin w.n) (t : {t : I // t ≠ 0 ∧ t ≠ 1}) :
    w.mapFun G (Realization.interior i t) =
      G.arc (w.edges i) (w.orientationParam i t.1) := rfl

/-- The raw-domain form of the cycle map. -/
def rawMap (w : CycleWalk src dst) (G : EmbeddedGraph src dst) :
    RawDomain (Fin w.n) (Fin w.n) → EmbeddedReal3 :=
  Sum.elim (fun p : RawVertex (Fin w.n) => G.conformation (w.vertices p.1))
    (fun q : RawInterval (Fin w.n) =>
      G.arc (w.edges q.1) (w.orientationParam q.1 q.2))

/-- The raw-domain form is continuous: vertices are constant on their fibre and each edge fibre is
either the embedded arc or the embedded arc precomposed with the interval reversal. -/
theorem rawMap_continuous (w : CycleWalk src dst) (G : EmbeddedGraph src dst) :
    Continuous (w.rawMap G) := by
  unfold rawMap
  apply Continuous.sumElim
  · apply continuous_sigma
    intro i
    show Continuous (fun _ : Unit => G.conformation (w.vertices i))
    exact continuous_const
  · apply continuous_sigma
    intro i
    show Continuous (fun t : I => G.arc (w.edges i) (w.orientationParam i t))
    have hfac : (fun t : I => G.arc (w.edges i) (w.orientationParam i t)) =
        if w.orientation i then (fun t : I => G.arc (w.edges i) (σ t))
        else (fun t : I => G.arc (w.edges i) t) := by
      by_cases h : w.orientation i <;> funext t <;> simp [orientationParam, h]
    rw [hfac]
    split
    · exact (G.arc (w.edges i)).continuous.comp unitInterval.continuous_symm
    · exact (G.arc (w.edges i)).continuous

/-- The composite of the cycle point map with the gluing map is the raw map. -/
theorem mapFun_comp_glue (w : CycleWalk src dst) (G : EmbeddedGraph src dst) :
    w.mapFun G ∘ glue (fun i : Fin w.n => i) (cycleSucc (n := w.n)) = w.rawMap G := by
  funext x
  cases x with
  | inl p =>
      obtain ⟨i, u⟩ := p
      rfl
  | inr q =>
      obtain ⟨i, t⟩ := q
      by_cases h0 : t = 0
      · subst t
        rw [Function.comp_apply, glue_inr, glueInterval_zero]
        change G.conformation (w.vertices i) =
          G.arc (w.edges i) (w.orientationParam i 0)
        by_cases ho : w.orientation i
        · unfold orientationParam
          rw [if_pos ho, unitInterval.symm_zero, G.arc_one]
          rw [← w.source_endpoint i]
          simp [ho]
        · unfold orientationParam
          rw [if_neg ho, G.arc_zero]
          rw [← w.source_endpoint i]
          simp [ho]
      · by_cases h1 : t = 1
        · subst t
          rw [Function.comp_apply, glue_inr, glueInterval_one]
          change G.conformation (w.vertices (cycleSucc i)) =
            G.arc (w.edges i) (w.orientationParam i 1)
          by_cases ho : w.orientation i
          · unfold orientationParam
            rw [if_pos ho, unitInterval.symm_one, G.arc_zero]
            rw [← w.target_endpoint i]
            simp [ho]
          · unfold orientationParam
            rw [if_neg ho, G.arc_one]
            rw [← w.target_endpoint i]
            simp [ho]
        · rw [Function.comp_apply, glue_inr, glueInterval_interior _ _ i t h0 h1]
          rfl

/-- The cycle point map is continuous, by the coinduced universal property of the cycle
realization. -/
theorem continuous_mapFun (w : CycleWalk src dst) (G : EmbeddedGraph src dst) :
    Continuous (w.mapFun G) :=
  continuous_of_continuous_comp_glue (fun i : Fin w.n => i) cycleSucc
    (by rw [w.mapFun_comp_glue G]; exact w.rawMap_continuous G)

/-- The embedded cycle map as a continuous map on the canonical cycle realization. -/
def map (w : CycleWalk src dst) (G : EmbeddedGraph src dst) :
    C(CycleDomain w.n, EmbeddedReal3) :=
  ⟨w.mapFun G, w.continuous_mapFun G⟩

@[simp] theorem map_apply (w : CycleWalk src dst) (G : EmbeddedGraph src dst)
    (x : CycleDomain w.n) : w.map G x = w.mapFun G x := rfl

/-- **Injectivity of the embedded cycle map.**  Distinct cycle points have distinct images: the
embedding separates vertices and arc interiors, distinct occurrences meeting at interior
parameters would have to be the same edge, and the walk's edge map is injective. -/
theorem mapFun_injective (w : CycleWalk src dst) (G : EmbeddedGraph src dst) :
    Function.Injective (w.mapFun G) := by
  intro x y h
  cases x with
  | vertex i =>
      cases y with
      | vertex j =>
          have hv : w.vertices i = w.vertices j := G.atom_injective h
          exact congrArg Realization.vertex (w.vertex_injective hv)
      | interior j s =>
          exact absurd h.symm
            (G.interior_avoids_atoms (w.edges j) (w.orientationParam j s.1)
              (w.orientationParam_ne_zero j s.1 s.2.1 s.2.2)
              (w.orientationParam_ne_one j s.1 s.2.1 s.2.2)
              (w.vertices i))
  | interior i t =>
      cases y with
      | vertex j =>
          exact absurd h
            (G.interior_avoids_atoms (w.edges i) (w.orientationParam i t.1)
              (w.orientationParam_ne_zero i t.1 t.2.1 t.2.2)
              (w.orientationParam_ne_one i t.1 t.2.1 t.2.2)
              (w.vertices j))
      | interior j s =>
          have harc : G.arc (w.edges i) (w.orientationParam i t.1) =
              G.arc (w.edges j) (w.orientationParam j s.1) := h
          have hedge : w.edges i = w.edges j :=
            G.edge_eq_of_interior_meet
              (w.orientationParam_ne_zero i t.1 t.2.1 t.2.2)
              (w.orientationParam_ne_one i t.1 t.2.1 t.2.2)
              (w.orientationParam_ne_zero j s.1 s.2.1 s.2.2)
              (w.orientationParam_ne_one j s.1 s.2.1 s.2.2)
              harc
          have hij : i = j := w.edges_injective hedge
          subst hij
          have hparam : w.orientationParam i t.1 = w.orientationParam i s.1 :=
            G.arc_injective (w.edges i) (w.src_ne_dst (w.edges i)) harc
          have hts : t = s := Subtype.ext (w.orientationParam_injective i hparam)
          rw [hts]

/-- **Exact image decomposition.**  The range of the embedded cycle map is exactly the union of
the embedded vertex positions and the embedded parametrized edge interiors. -/
theorem range_mapFun (w : CycleWalk src dst) (G : EmbeddedGraph src dst) :
    Set.range (w.mapFun G) =
      (Set.range fun i : Fin w.n => G.conformation (w.vertices i)) ∪
        (Set.range fun p : Fin w.n × {t : I // t ≠ 0 ∧ t ≠ 1} =>
          G.arc (w.edges p.1) (w.orientationParam p.1 p.2.1)) := by
  ext x
  constructor
  · rintro ⟨point, rfl⟩
    cases point with
    | vertex i => exact Or.inl ⟨i, rfl⟩
    | interior i t => exact Or.inr ⟨⟨i, t⟩, rfl⟩
  · rintro (⟨i, rfl⟩ | ⟨⟨i, t⟩, rfl⟩)
    · exact ⟨Realization.vertex i, rfl⟩
    · exact ⟨Realization.interior i t, rfl⟩

/-- **Two embedded cycle images intersect exactly at a shared vertex.**  If the two cycles have a
single common vertex and use no occurrence in common, then their spatial images intersect exactly
at the image of that vertex.  No circle or planar separation property is asserted. -/
theorem range_inter_eq_singleton (w₁ w₂ : CycleWalk src dst) (G : EmbeddedGraph src dst)
    (shared : V)
    (sharedFirst : ∃ i, w₁.vertices i = shared)
    (sharedSecond : ∃ j, w₂.vertices j = shared)
    (vertexIntersection : ∀ i j, w₁.vertices i = w₂.vertices j → w₁.vertices i = shared)
    (edgeDisjoint : ∀ i j, w₁.edges i ≠ w₂.edges j) :
    Set.range (w₁.mapFun G) ∩ Set.range (w₂.mapFun G) = {G.conformation shared} := by
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨hx₁, hx₂⟩
    obtain ⟨p, rfl⟩ := hx₁
    obtain ⟨q, hq⟩ := hx₂
    cases p with
    | vertex i =>
        cases q with
        | vertex j =>
            have hconv : G.conformation (w₁.vertices i) =
                G.conformation (w₂.vertices j) := hq.symm
            have hshared : w₁.vertices i = shared :=
              vertexIntersection i j (G.atom_injective hconv)
            rw [Set.mem_singleton_iff]
            change G.conformation (w₁.vertices i) = G.conformation shared
            rw [hshared]
        | interior j s =>
            exact absurd hq
              (G.interior_avoids_atoms (w₂.edges j) (w₂.orientationParam j s.1)
                (w₂.orientationParam_ne_zero j s.1 s.2.1 s.2.2)
                (w₂.orientationParam_ne_one j s.1 s.2.1 s.2.2)
                (w₁.vertices i))
    | interior i t =>
        cases q with
        | vertex j =>
            exact absurd hq.symm
              (G.interior_avoids_atoms (w₁.edges i) (w₁.orientationParam i t.1)
                (w₁.orientationParam_ne_zero i t.1 t.2.1 t.2.2)
                (w₁.orientationParam_ne_one i t.1 t.2.1 t.2.2)
                (w₂.vertices j))
        | interior j s =>
            have harc : G.arc (w₁.edges i) (w₁.orientationParam i t.1) =
                G.arc (w₂.edges j) (w₂.orientationParam j s.1) := hq.symm
            have hedge : w₁.edges i = w₂.edges j :=
              G.edge_eq_of_interior_meet
                (w₁.orientationParam_ne_zero i t.1 t.2.1 t.2.2)
                (w₁.orientationParam_ne_one i t.1 t.2.1 t.2.2)
                (w₂.orientationParam_ne_zero j s.1 s.2.1 s.2.2)
                (w₂.orientationParam_ne_one j s.1 s.2.1 s.2.2)
                harc
            exact absurd hedge (edgeDisjoint i j)
  · rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    constructor
    · obtain ⟨i, hi⟩ := sharedFirst
      exact ⟨Realization.vertex i, by simp [mapFun, hi]⟩
    · obtain ⟨j, hj⟩ := sharedSecond
      exact ⟨Realization.vertex j, by simp [mapFun, hj]⟩

end CycleWalk

/-! ## Ring lists, positions and the closed source path -/

/-- The number of distinct vertices of a ring with the given internal atoms: the center plus one
vertex per internal atom. -/
def ringN (internal : List Nat) : Nat := internal.length + 1

/-- The atom list of a ring, in traversal order without the closing repeat of the center. -/
def ringAtomList (system : P93AuthoritySpiroSystem) (internal : List Nat) : List Nat :=
  system.center :: internal

/-- The closed traversal list of a ring: internal traversal followed by the closing center. -/
def ringClosed (system : P93AuthoritySpiroSystem) (internal : List Nat) : List Nat :=
  ringAtomList system internal ++ [system.center]

theorem ringAtomList_length (system : P93AuthoritySpiroSystem) (internal : List Nat) :
    (ringAtomList system internal).length = ringN internal := by
  simp [ringAtomList, ringN]

theorem ringClosed_length (system : P93AuthoritySpiroSystem) (internal : List Nat) :
    (ringClosed system internal).length = ringN internal + 1 := by
  simp [ringClosed, ringAtomList, ringN]

theorem ringClosed_eq_closedPath (system : P93AuthoritySpiroSystem) (internal : List Nat) :
    system.closedPath internal = ringClosed system internal := by
  simp [P93AuthoritySpiroSystem.closedPath, ringClosed, ringAtomList, List.cons_append]

/-- The ring vertex at position `i`. -/
def ringVertex (system : P93AuthoritySpiroSystem) (internal : List Nat)
    (i : Fin (ringN internal)) : Nat :=
  (ringAtomList system internal)[i.val]'(by rw [ringAtomList_length]; exact i.isLt)

/-- The closed-path vertex at position `j`, including the repeated closing center. -/
def ringClosedVertex (system : P93AuthoritySpiroSystem) (internal : List Nat)
    (j : Fin (ringN internal + 1)) : Nat :=
  (ringClosed system internal)[j.val]'(by rw [ringClosed_length]; exact j.isLt)

theorem ringVertex_mem_ringAtomList (system : P93AuthoritySpiroSystem) (internal : List Nat)
    (i : Fin (ringN internal)) :
    ringVertex system internal i ∈ ringAtomList system internal := by
  unfold ringVertex
  exact List.getElem_mem (l := ringAtomList system internal) (n := i.val) _

theorem ringVertex_zero (system : P93AuthoritySpiroSystem) (internal : List Nat) :
    ringVertex system internal ⟨0, by simp [ringN]⟩ = system.center := by
  unfold ringVertex ringAtomList
  rfl

theorem ringVertex_cycleSucc_of_lt (system : P93AuthoritySpiroSystem) (internal : List Nat)
    (i : Fin (ringN internal)) (h : i.val + 1 < ringN internal) :
    ringVertex system internal (cycleSucc i) =
      internal[i.val]'(by simp [ringN] at h; omega) := by
  have hfin : cycleSucc i = ⟨i.val + 1, h⟩ := Fin.ext (cycleSucc_val_of_lt h)
  rw [hfin]
  unfold ringVertex
  simp only [ringAtomList, List.getElem_cons_succ]

theorem ringVertex_cycleSucc_of_not_lt (system : P93AuthoritySpiroSystem) (internal : List Nat)
    (i : Fin (ringN internal)) (h : ¬ i.val + 1 < ringN internal) :
    ringVertex system internal (cycleSucc i) = system.center := by
  have hfin : cycleSucc i = ⟨0, by simp [ringN]⟩ := Fin.ext (cycleSucc_val_of_not_lt h)
  rw [hfin]
  unfold ringVertex ringAtomList
  rfl

/-- The ring traversal list has no repeated atoms when the spiro system is mechanically valid.
This is derived from `system.atoms.Nodup`; the two interiors are not assumed disjoint. -/
theorem ringAtomList_nodup_of_first {source : AuthoritativeChemicalInput}
    {system : P93AuthoritySpiroSystem} (valid : system.MechanicallyValidFor source) :
    (ringAtomList system system.firstRingInternal).Nodup := by
  refine List.nodup_cons.mpr ⟨?_, ?_⟩
  · exact center_not_mem_firstInternal valid
  · exact (List.nodup_append.mp (List.nodup_cons.mp valid.1).2).1

theorem ringAtomList_nodup_of_second {source : AuthoritativeChemicalInput}
    {system : P93AuthoritySpiroSystem} (valid : system.MechanicallyValidFor source) :
    (ringAtomList system system.secondRingInternal).Nodup := by
  refine List.nodup_cons.mpr ⟨?_, ?_⟩
  · exact center_not_mem_secondInternal valid
  · exact (List.nodup_append.mp (List.nodup_cons.mp valid.1).2).2.1

/-- Ring positions are injective when the ring traversal list is noduplicate. -/
theorem ringVertex_injective (system : P93AuthoritySpiroSystem) (internal : List Nat)
    (nodup : (ringAtomList system internal).Nodup) :
    Function.Injective (ringVertex system internal) := by
  intro i j h
  unfold ringVertex at h
  exact Fin.ext ((nodup.getElem_inj_iff).mp h)

/-- The position `i` inside the closed traversal is the same ring vertex. -/
theorem ringClosedVertex_lt (system : P93AuthoritySpiroSystem) (internal : List Nat)
    (i : Fin (ringN internal)) :
    ringClosedVertex system internal ⟨i.val, by omega⟩ = ringVertex system internal i := by
  unfold ringClosedVertex ringVertex ringClosed
  rw [List.getElem_append_left (as := ringAtomList system internal) (bs := [system.center])
    (i := i.val) (by rw [ringAtomList_length]; exact i.isLt)]

/-- The successor position in the closed traversal is the next ring vertex, in the non-wrapping
case. -/
theorem ringClosedVertex_succ_of_lt (system : P93AuthoritySpiroSystem) (internal : List Nat)
    (i : Fin (ringN internal)) (h : i.val + 1 < ringN internal) :
    ringClosedVertex system internal ⟨i.val + 1, by omega⟩ =
      ringVertex system internal (cycleSucc i) := by
  rw [ringVertex_cycleSucc_of_lt system internal i h]
  unfold ringClosedVertex ringClosed
  rw [List.getElem_append_left (as := ringAtomList system internal) (bs := [system.center])
    (i := i.val + 1) (by rw [ringAtomList_length]; exact h)]
  simp only [ringAtomList, List.getElem_cons_succ]

/-- The successor position in the closed traversal is the next ring vertex, in the wrapping
case. -/
theorem ringClosedVertex_succ_of_not_lt (system : P93AuthoritySpiroSystem) (internal : List Nat)
    (i : Fin (ringN internal)) (h : ¬ i.val + 1 < ringN internal) :
    ringClosedVertex system internal ⟨i.val + 1, by omega⟩ =
      ringVertex system internal (cycleSucc i) := by
  rw [ringVertex_cycleSucc_of_not_lt system internal i h]
  have heq : i.val + 1 = ringN internal := by
    have := i.isLt
    omega
  unfold ringClosedVertex ringClosed
  rw [List.getElem_append_right (as := ringAtomList system internal) (bs := [system.center])
    (i := i.val + 1) (by rw [ringAtomList_length]; omega)]
  simp [ringAtomList_length, heq]

/-- Every consecutive pair of the closed source path is a genuine source binary bond. -/
theorem ringBinaryBond (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem) (internal : List Nat)
    (connected : P93AuthorityConnectedPath certified.input (system.closedPath internal))
    (i : Fin (ringN internal)) :
    P93AuthorityBinaryBond certified.input
      (ringVertex system internal i) (ringVertex system internal (cycleSucc i)) := by
  have chain : (system.closedPath internal).IsChain
      (P93AuthorityBinaryBond certified.input) :=
    (P93AuthorityConnectedPath.isChain_iff certified.input
      (system.closedPath internal)).1 connected
  have chain' : (ringClosed system internal).IsChain
      (P93AuthorityBinaryBond certified.input) := by
    rw [← ringClosed_eq_closedPath system internal]
    exact chain
  have hi : i.val + 1 < (ringClosed system internal).length := by
    rw [ringClosed_length]
    omega
  have bond := chain'.getElem i.val hi
  have hleft : (ringClosed system internal)[i.val]'(by rw [ringClosed_length]; omega) =
      ringVertex system internal i :=
    ringClosedVertex_lt system internal i
  by_cases h : i.val + 1 < ringN internal
  · have hright : (ringClosed system internal)[i.val + 1]'(by rw [ringClosed_length]; omega) =
        ringVertex system internal (cycleSucc i) :=
      ringClosedVertex_succ_of_lt system internal i h
    convert bond using 1
    · exact hleft.symm
    · exact hright.symm
  · have hright : (ringClosed system internal)[i.val + 1]'(by rw [ringClosed_length]; omega) =
        ringVertex system internal (cycleSucc i) :=
      ringClosedVertex_succ_of_not_lt system internal i h
    convert bond using 1
    · exact hleft.symm
    · exact hright.symm

/-! ## Selecting one actual occurrence per consecutive ring pair -/

/-- The atomic ring vertex as a bounded source atom of the reconstructed graph. -/
def ringVertexAtom (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem) (internal : List Nat)
    (bounded : ∀ atom ∈ ringAtomList system internal,
      atom < certified.input.molecule.atomCount)
    (i : Fin (ringN internal)) : Fin certified.input.molecule.atomCount :=
  ⟨ringVertex system internal i,
    bounded _ (ringVertex_mem_ringAtomList system internal i)⟩

/-- The classical selection of an oriented selected occurrence covering a consecutive ring pair.
The selected occurrence is exposed; uniqueness is intentionally not claimed. -/
noncomputable def ringEdgeData (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem) (internal : List Nat)
    (bounded : ∀ atom ∈ ringAtomList system internal,
      atom < certified.input.molecule.atomCount)
    (connected : P93AuthorityConnectedPath certified.input (system.closedPath internal))
    (i : Fin (ringN internal)) :
    { p : SelectedBondIndex (sourceGraph certified) × Bool //
        (if p.2 then selectedTarget (sourceGraph certified) p.1
          else selectedSource (sourceGraph certified) p.1) =
            ringVertexAtom certified system internal bounded i ∧
        (if p.2 then selectedSource (sourceGraph certified) p.1
          else selectedTarget (sourceGraph certified) p.1) =
            ringVertexAtom certified system internal bounded (cycleSucc i) } := by
  let edge : SelectedBondIndex (sourceGraph certified) :=
    Classical.choose (exists_oriented_selectedBond_of_binaryBond certified
      (bounded _ (ringVertex_mem_ringAtomList system internal i))
      (bounded _ (ringVertex_mem_ringAtomList system internal (cycleSucc i)))
      (ringBinaryBond certified system internal connected i))
  have orientationExists : ∃ orientation : Bool,
      (if orientation then selectedTarget (sourceGraph certified) edge
        else selectedSource (sourceGraph certified) edge) =
          ringVertexAtom certified system internal bounded i ∧
      (if orientation then selectedSource (sourceGraph certified) edge
        else selectedTarget (sourceGraph certified) edge) =
          ringVertexAtom certified system internal bounded (cycleSucc i) :=
    Classical.choose_spec (exists_oriented_selectedBond_of_binaryBond certified
      (bounded _ (ringVertex_mem_ringAtomList system internal i))
      (bounded _ (ringVertex_mem_ringAtomList system internal (cycleSucc i)))
      (ringBinaryBond certified system internal connected i))
  let orientation : Bool := Classical.choose orientationExists
  exact ⟨(edge, orientation), Classical.choose_spec orientationExists⟩

noncomputable def ringEdge (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem) (internal : List Nat)
    (bounded : ∀ atom ∈ ringAtomList system internal,
      atom < certified.input.molecule.atomCount)
    (connected : P93AuthorityConnectedPath certified.input (system.closedPath internal))
    (i : Fin (ringN internal)) : SelectedBondIndex (sourceGraph certified) :=
  (ringEdgeData certified system internal bounded connected i).1.1

noncomputable def ringOrientation (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem) (internal : List Nat)
    (bounded : ∀ atom ∈ ringAtomList system internal,
      atom < certified.input.molecule.atomCount)
    (connected : P93AuthorityConnectedPath certified.input (system.closedPath internal))
    (i : Fin (ringN internal)) : Bool :=
  (ringEdgeData certified system internal bounded connected i).1.2

theorem ringEdge_source_endpoint (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem) (internal : List Nat)
    (bounded : ∀ atom ∈ ringAtomList system internal,
      atom < certified.input.molecule.atomCount)
    (connected : P93AuthorityConnectedPath certified.input (system.closedPath internal))
    (i : Fin (ringN internal)) :
    (if ringOrientation certified system internal bounded connected i
      then selectedTarget (sourceGraph certified)
        (ringEdge certified system internal bounded connected i)
      else selectedSource (sourceGraph certified)
        (ringEdge certified system internal bounded connected i)) =
      ringVertexAtom certified system internal bounded i :=
  (ringEdgeData certified system internal bounded connected i).2.1

theorem ringEdge_target_endpoint (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem) (internal : List Nat)
    (bounded : ∀ atom ∈ ringAtomList system internal,
      atom < certified.input.molecule.atomCount)
    (connected : P93AuthorityConnectedPath certified.input (system.closedPath internal))
    (i : Fin (ringN internal)) :
    (if ringOrientation certified system internal bounded connected i
      then selectedSource (sourceGraph certified)
        (ringEdge certified system internal bounded connected i)
      else selectedTarget (sourceGraph certified)
        (ringEdge certified system internal bounded connected i)) =
      ringVertexAtom certified system internal bounded (cycleSucc i) :=
  (ringEdgeData certified system internal bounded connected i).2.2

/-- Both endpoints of a selected ring occurrence lie in the ring whose traversal supplied it. -/
theorem ringEdge_endpoint_val_mem (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem) (internal : List Nat)
    (bounded : ∀ atom ∈ ringAtomList system internal,
      atom < certified.input.molecule.atomCount)
    (connected : P93AuthorityConnectedPath certified.input (system.closedPath internal))
    (ring : List Nat)
    (ringContains : ∀ atom ∈ ringAtomList system internal, atom ∈ ring)
    (i : Fin (ringN internal)) :
    ((selectedSource (sourceGraph certified)
        (ringEdge certified system internal bounded connected i)).val ∈ ring) ∧
      ((selectedTarget (sourceGraph certified)
        (ringEdge certified system internal bounded connected i)).val ∈ ring) := by
  have vertexMember : ∀ k : Fin (ringN internal),
      ringVertex system internal k ∈ ring :=
    fun k => ringContains _ (ringVertex_mem_ringAtomList system internal k)
  have sourceEq := ringEdge_source_endpoint certified system internal bounded connected i
  have targetEq := ringEdge_target_endpoint certified system internal bounded connected i
  by_cases ho : ringOrientation certified system internal bounded connected i
  · rw [if_pos ho] at sourceEq targetEq
    constructor
    · have h := congrArg Fin.val targetEq
      exact h ▸ vertexMember (cycleSucc i)
    · have h := congrArg Fin.val sourceEq
      exact h ▸ vertexMember i
  · rw [if_neg ho] at sourceEq targetEq
    constructor
    · have h := congrArg Fin.val sourceEq
      exact h ▸ vertexMember i
    · have h := congrArg Fin.val targetEq
      exact h ▸ vertexMember (cycleSucc i)

/-- The ring cycle walk, constructed from one ring's closed source path and the selected oriented
occurrences supplied by the global selection. -/
noncomputable def ringWalk (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem) (internal : List Nat)
    (bounded : ∀ atom ∈ ringAtomList system internal,
      atom < certified.input.molecule.atomCount)
    (nodup : (ringAtomList system internal).Nodup)
    (connected : P93AuthorityConnectedPath certified.input (system.closedPath internal))
    (geTwo : 2 ≤ internal.length) :
    CycleWalk (selectedSource (sourceGraph certified)) (selectedTarget (sourceGraph certified)) where
  n := ringN internal
  n_ge_three := by simp [ringN]; omega
  vertices := ringVertexAtom certified system internal bounded
  vertex_injective := by
    intro i j h
    exact ringVertex_injective system internal nodup (congrArg Fin.val h)
  edges := ringEdge certified system internal bounded connected
  orientation := ringOrientation certified system internal bounded connected
  src_ne_dst := selectedSource_ne_target (sourceGraph certified)
  source_endpoint := ringEdge_source_endpoint certified system internal bounded connected
  target_endpoint := ringEdge_target_endpoint certified system internal bounded connected

@[simp] theorem ringWalk_n (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem) (internal : List Nat)
    (bounded : ∀ atom ∈ ringAtomList system internal,
      atom < certified.input.molecule.atomCount)
    (nodup : (ringAtomList system internal).Nodup)
    (connected : P93AuthorityConnectedPath certified.input (system.closedPath internal))
    (geTwo : 2 ≤ internal.length) :
    (ringWalk certified system internal bounded nodup connected geTwo).n = ringN internal := rfl

@[simp] theorem ringWalk_vertices (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem) (internal : List Nat)
    (bounded : ∀ atom ∈ ringAtomList system internal,
      atom < certified.input.molecule.atomCount)
    (nodup : (ringAtomList system internal).Nodup)
    (connected : P93AuthorityConnectedPath certified.input (system.closedPath internal))
    (geTwo : 2 ≤ internal.length) (i : Fin (ringN internal)) :
    (ringWalk certified system internal bounded nodup connected geTwo).vertices i =
      ringVertexAtom certified system internal bounded i := rfl

@[simp] theorem ringWalk_edges (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem) (internal : List Nat)
    (bounded : ∀ atom ∈ ringAtomList system internal,
      atom < certified.input.molecule.atomCount)
    (nodup : (ringAtomList system internal).Nodup)
    (connected : P93AuthorityConnectedPath certified.input (system.closedPath internal))
    (geTwo : 2 ≤ internal.length) (i : Fin (ringN internal)) :
    (ringWalk certified system internal bounded nodup connected geTwo).edges i =
      ringEdge certified system internal bounded connected i := rfl

@[simp] theorem ringWalk_orientation (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem) (internal : List Nat)
    (bounded : ∀ atom ∈ ringAtomList system internal,
      atom < certified.input.molecule.atomCount)
    (nodup : (ringAtomList system internal).Nodup)
    (connected : P93AuthorityConnectedPath certified.input (system.closedPath internal))
    (geTwo : 2 ≤ internal.length) (i : Fin (ringN internal)) :
    (ringWalk certified system internal bounded nodup connected geTwo).orientation i =
      ringOrientation certified system internal bounded connected i := rfl

/-! ## The two spiro rings -/

/-- The atom position of the shared spiro center, as a bounded source atom. -/
def centerAtom (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input) :
    Fin certified.input.molecule.atomCount :=
  ⟨system.center, valid.2.1 system.center (by
    rw [P93AuthoritySpiroSystem.mem_atoms_iff]
    exact Or.inl rfl)⟩

/-- Bounds for the first ring atoms, extracted from mechanical validity. -/
theorem firstRing_bounded (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem) (valid : system.MechanicallyValidFor certified.input) :
    ∀ atom ∈ ringAtomList system system.firstRingInternal,
      atom < certified.input.molecule.atomCount := by
  intro atom member
  exact valid.2.1 atom (firstRing_subset_atoms system member)

/-- Bounds for the second ring atoms, extracted from mechanical validity. -/
theorem secondRing_bounded (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem) (valid : system.MechanicallyValidFor certified.input) :
    ∀ atom ∈ ringAtomList system system.secondRingInternal,
      atom < certified.input.molecule.atomCount := by
  intro atom member
  exact valid.2.1 atom (secondRing_subset_atoms system member)

/-- The embedded cycle walk of the first spiro ring. -/
noncomputable def firstRingWalk (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input) :
    CycleWalk (selectedSource (sourceGraph certified)) (selectedTarget (sourceGraph certified)) :=
  ringWalk certified system system.firstRingInternal
    (firstRing_bounded certified system valid)
    (ringAtomList_nodup_of_first valid)
    valid.2.2.2.2.1
    valid.2.2.1

/-- The embedded cycle walk of the second spiro ring. -/
noncomputable def secondRingWalk (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input) :
    CycleWalk (selectedSource (sourceGraph certified)) (selectedTarget (sourceGraph certified)) :=
  ringWalk certified system system.secondRingInternal
    (secondRing_bounded certified system valid)
    (ringAtomList_nodup_of_second valid)
    valid.2.2.2.2.2
    valid.2.2.2.1

@[simp] theorem firstRingWalk_n (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input) :
    (firstRingWalk certified system valid).n = ringN system.firstRingInternal := rfl

@[simp] theorem secondRingWalk_n (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input) :
    (secondRingWalk certified system valid).n = ringN system.secondRingInternal := rfl

@[simp] theorem firstRingWalk_vertices (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input)
    (i : Fin (ringN system.firstRingInternal)) :
    (firstRingWalk certified system valid).vertices i =
      ringVertexAtom certified system system.firstRingInternal
        (firstRing_bounded certified system valid) i := rfl

@[simp] theorem secondRingWalk_vertices (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input)
    (j : Fin (ringN system.secondRingInternal)) :
    (secondRingWalk certified system valid).vertices j =
      ringVertexAtom certified system system.secondRingInternal
        (secondRing_bounded certified system valid) j := rfl

@[simp] theorem firstRingWalk_edges (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input)
    (i : Fin (ringN system.firstRingInternal)) :
    (firstRingWalk certified system valid).edges i =
      ringEdge certified system system.firstRingInternal
        (firstRing_bounded certified system valid) valid.2.2.2.2.1 i := rfl

@[simp] theorem secondRingWalk_edges (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input)
    (j : Fin (ringN system.secondRingInternal)) :
    (secondRingWalk certified system valid).edges j =
      ringEdge certified system system.secondRingInternal
        (secondRing_bounded certified system valid) valid.2.2.2.2.2 j := rfl

/-- Every first-ring vertex is a bounded atom of the first ring. -/
theorem firstRingWalk_vertex_mem (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input)
    (i : Fin (ringN system.firstRingInternal)) :
    ((firstRingWalk certified system valid).vertices i).val ∈ system.firstRing :=
  ringVertex_mem_ringAtomList system system.firstRingInternal i

/-- Every second-ring vertex is a bounded atom of the second ring. -/
theorem secondRingWalk_vertex_mem (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input)
    (j : Fin (ringN system.secondRingInternal)) :
    ((secondRingWalk certified system valid).vertices j).val ∈ system.secondRing :=
  ringVertex_mem_ringAtomList system system.secondRingInternal j

/-- Every first-ring cycle edge records a genuine source binary bond between its two vertices. -/
theorem firstRingWalk_bond (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input)
    (i : Fin (ringN system.firstRingInternal)) :
    P93AuthorityBinaryBond certified.input
      ((firstRingWalk certified system valid).vertices i).val
      ((firstRingWalk certified system valid).vertices (cycleSucc i)).val :=
  ringBinaryBond certified system system.firstRingInternal valid.2.2.2.2.1 i

/-- Every second-ring cycle edge records a genuine source binary bond between its two vertices. -/
theorem secondRingWalk_bond (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input)
    (j : Fin (ringN system.secondRingInternal)) :
    P93AuthorityBinaryBond certified.input
      ((secondRingWalk certified system valid).vertices j).val
      ((secondRingWalk certified system valid).vertices (cycleSucc j)).val :=
  ringBinaryBond certified system system.secondRingInternal valid.2.2.2.2.2 j

/-- The source-order participant list of every first-ring selected occurrence is exactly the two
oriented endpoints of that occurrence. -/
theorem firstRingWalk_participants (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input)
    (i : Fin (ringN system.firstRingInternal)) :
    ((sourceGraph certified).interactions.get
        ((firstRingWalk certified system valid).edges i).1).1 =
      [selectedSource (sourceGraph certified)
          ((firstRingWalk certified system valid).edges i),
        selectedTarget (sourceGraph certified)
          ((firstRingWalk certified system valid).edges i)] :=
  selectedParticipants (sourceGraph certified) _

/-- Every first-ring selected occurrence is an actual binary interaction occurrence of the source
molecule, with participant order preserved up to the two orientations. -/
theorem firstRingWalk_source_interaction (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input)
    (i : Fin (ringN system.firstRingInternal)) :
    ∃ interaction ∈ certified.input.molecule.interactions,
      P93AuthorityBinaryInteractionKind interaction.kind ∧
        (interaction.participants =
            [((firstRingWalk certified system valid).vertices i).val,
              ((firstRingWalk certified system valid).vertices (cycleSucc i)).val] ∨
          interaction.participants =
            [((firstRingWalk certified system valid).vertices (cycleSucc i)).val,
              ((firstRingWalk certified system valid).vertices i).val]) :=
  (firstRingWalk_bond certified system valid i).2

/-- Every second-ring selected occurrence is an actual binary interaction occurrence of the source
molecule, with participant order preserved up to the two orientations. -/
theorem secondRingWalk_source_interaction (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input)
    (j : Fin (ringN system.secondRingInternal)) :
    ∃ interaction ∈ certified.input.molecule.interactions,
      P93AuthorityBinaryInteractionKind interaction.kind ∧
        (interaction.participants =
            [((secondRingWalk certified system valid).vertices j).val,
              ((secondRingWalk certified system valid).vertices (cycleSucc j)).val] ∨
          interaction.participants =
            [((secondRingWalk certified system valid).vertices (cycleSucc j)).val,
              ((secondRingWalk certified system valid).vertices j).val]) :=
  (secondRingWalk_bond certified system valid j).2

/-- Both endpoints of a first-ring selected occurrence are first-ring atoms. -/
theorem firstRingWalk_edge_endpoints_mem (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input)
    (i : Fin (ringN system.firstRingInternal)) :
    ((selectedSource (sourceGraph certified)
        ((firstRingWalk certified system valid).edges i)).val ∈ system.firstRing) ∧
      ((selectedTarget (sourceGraph certified)
        ((firstRingWalk certified system valid).edges i)).val ∈ system.firstRing) :=
  ringEdge_endpoint_val_mem certified system system.firstRingInternal
    (firstRing_bounded certified system valid) valid.2.2.2.2.1 system.firstRing
    (fun _ member => member) i

/-- Both endpoints of a second-ring selected occurrence are second-ring atoms. -/
theorem secondRingWalk_edge_endpoints_mem (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input)
    (j : Fin (ringN system.secondRingInternal)) :
    ((selectedSource (sourceGraph certified)
        ((secondRingWalk certified system valid).edges j)).val ∈ system.secondRing) ∧
      ((selectedTarget (sourceGraph certified)
        ((secondRingWalk certified system valid).edges j)).val ∈ system.secondRing) :=
  ringEdge_endpoint_val_mem certified system system.secondRingInternal
    (secondRing_bounded certified system valid) valid.2.2.2.2.2 system.secondRing
    (fun _ member => member) j

/-- **No occurrence is used by both rings.**  If one selected occurrence were used by both cycles,
its two distinct endpoints would both lie in both rings; `rings_inter_center` would force both to
be the center, contradicting endpoint distinctness. -/
theorem ringWalk_edges_disjoint (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input)
    (i : Fin (ringN system.firstRingInternal))
    (j : Fin (ringN system.secondRingInternal)) :
    (firstRingWalk certified system valid).edges i ≠
      (secondRingWalk certified system valid).edges j := by
  intro same
  have sourceFirst := (firstRingWalk_edge_endpoints_mem certified system valid i).1
  have targetFirst := (firstRingWalk_edge_endpoints_mem certified system valid i).2
  have sourceSecond := (secondRingWalk_edge_endpoints_mem certified system valid j).1
  have targetSecond := (secondRingWalk_edge_endpoints_mem certified system valid j).2
  have sourceSecond' : ((selectedSource (sourceGraph certified)
      ((firstRingWalk certified system valid).edges i)).val ∈ system.secondRing) := by
    rw [same]
    exact sourceSecond
  have targetSecond' : ((selectedTarget (sourceGraph certified)
      ((firstRingWalk certified system valid).edges i)).val ∈ system.secondRing) := by
    rw [same]
    exact targetSecond
  have centreSource := rings_inter_center valid sourceFirst sourceSecond'
  have centreTarget := rings_inter_center valid targetFirst targetSecond'
  have endpointsEqual :
      selectedSource (sourceGraph certified) ((firstRingWalk certified system valid).edges i) =
        selectedTarget (sourceGraph certified) ((firstRingWalk certified system valid).edges i) :=
    Fin.ext (centreSource.trans centreTarget.symm)
  exact selectedSource_ne_target (sourceGraph certified) _ endpointsEqual

/-- **The two ring vertex sets meet only at the embedded center.**  Equal ring vertices have equal
source atom values; one is a first-ring atom and the other a second-ring atom, so both equal the
center. -/
theorem ringWalk_vertices_inter_center (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input)
    (i : Fin (ringN system.firstRingInternal))
    (j : Fin (ringN system.secondRingInternal))
    (same : (firstRingWalk certified system valid).vertices i =
      (secondRingWalk certified system valid).vertices j) :
    (firstRingWalk certified system valid).vertices i = centerAtom certified system valid := by
  apply Fin.ext
  have valueSame : ringVertex system system.firstRingInternal i =
      ringVertex system system.secondRingInternal j := congrArg Fin.val same
  show ringVertex system system.firstRingInternal i = system.center
  exact rings_inter_center valid
    (ringVertex_mem_ringAtomList system system.firstRingInternal i)
    (by rw [valueSame]
        exact ringVertex_mem_ringAtomList system system.secondRingInternal j)

/-- The center is the zeroth vertex of the first ring. -/
theorem firstRingWalk_center_vertex (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input) :
    (firstRingWalk certified system valid).vertices ⟨0, by simp [ringN]⟩ =
      centerAtom certified system valid := by
  apply Fin.ext
  show ringVertex system system.firstRingInternal ⟨0, by simp [ringN]⟩ = system.center
  exact ringVertex_zero system system.firstRingInternal

/-- The center is the zeroth vertex of the second ring. -/
theorem secondRingWalk_center_vertex (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input) :
    (secondRingWalk certified system valid).vertices ⟨0, by simp [ringN]⟩ =
      centerAtom certified system valid := by
  apply Fin.ext
  show ringVertex system system.secondRingInternal ⟨0, by simp [ringN]⟩ = system.center
  exact ringVertex_zero system system.secondRingInternal

/-- Vertex coordinates of the first embedded ring are exactly the supplied global embedding's
vertex positions. -/
theorem firstRingWalk_map_vertex (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input)
    (G : EmbeddedGraph (selectedSource (sourceGraph certified))
      (selectedTarget (sourceGraph certified)))
    (i : Fin (ringN system.firstRingInternal)) :
    (firstRingWalk certified system valid).map G (Realization.vertex i) =
      G.conformation ((firstRingWalk certified system valid).vertices i) := rfl

/-- Vertex coordinates of the second embedded ring are exactly the supplied global embedding's
vertex positions. -/
theorem secondRingWalk_map_vertex (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input)
    (G : EmbeddedGraph (selectedSource (sourceGraph certified))
      (selectedTarget (sourceGraph certified)))
    (j : Fin (ringN system.secondRingInternal)) :
    (secondRingWalk certified system valid).map G (Realization.vertex j) =
      G.conformation ((secondRingWalk certified system valid).vertices j) := rfl

/-- Every interior point of a first-ring cycle edge is exactly the supplied global embedding's arc
of the selected source occurrence at the orientation-adjusted parameter. -/
theorem firstRingWalk_map_interior (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input)
    (G : EmbeddedGraph (selectedSource (sourceGraph certified))
      (selectedTarget (sourceGraph certified)))
    (i : Fin (ringN system.firstRingInternal)) (t : I) (h0 : t ≠ 0) (h1 : t ≠ 1) :
    (firstRingWalk certified system valid).map G
        (edgePoint (fun i : Fin (ringN system.firstRingInternal) => i)
          (cycleSucc (n := ringN system.firstRingInternal)) i t) =
      G.arc ((firstRingWalk certified system valid).edges i)
        ((firstRingWalk certified system valid).orientationParam i t) := by
  show CycleWalk.mapFun (firstRingWalk certified system valid) G
      (edgePoint (fun i : Fin (ringN system.firstRingInternal) => i)
        (cycleSucc (n := ringN system.firstRingInternal)) i t) =
    G.arc ((firstRingWalk certified system valid).edges i)
      ((firstRingWalk certified system valid).orientationParam i t)
  rw [edgePoint_interior _ _ i t h0 h1]
  rfl

/-- Every interior point of a second-ring cycle edge is exactly the supplied global embedding's
arc of the selected source occurrence at the orientation-adjusted parameter. -/
theorem secondRingWalk_map_interior (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input)
    (G : EmbeddedGraph (selectedSource (sourceGraph certified))
      (selectedTarget (sourceGraph certified)))
    (j : Fin (ringN system.secondRingInternal)) (t : I) (h0 : t ≠ 0) (h1 : t ≠ 1) :
    (secondRingWalk certified system valid).map G
        (edgePoint (fun j : Fin (ringN system.secondRingInternal) => j)
          (cycleSucc (n := ringN system.secondRingInternal)) j t) =
      G.arc ((secondRingWalk certified system valid).edges j)
        ((secondRingWalk certified system valid).orientationParam j t) := by
  show CycleWalk.mapFun (secondRingWalk certified system valid) G
      (edgePoint (fun j : Fin (ringN system.secondRingInternal) => j)
        (cycleSucc (n := ringN system.secondRingInternal)) j t) =
    G.arc ((secondRingWalk certified system valid).edges j)
      ((secondRingWalk certified system valid).orientationParam j t)
  rw [edgePoint_interior _ _ j t h0 h1]
  rfl

/-- **Two embedded spiro cycle images intersect exactly at the embedded center.** -/
theorem firstRingWalk_inter_secondRingWalk_eq_center
    (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input)
    (G : EmbeddedGraph (selectedSource (sourceGraph certified))
      (selectedTarget (sourceGraph certified))) :
    Set.range ((firstRingWalk certified system valid).mapFun G) ∩
        Set.range ((secondRingWalk certified system valid).mapFun G) =
      {G.conformation (centerAtom certified system valid)} :=
  CycleWalk.range_inter_eq_singleton
    (firstRingWalk certified system valid) (secondRingWalk certified system valid) G
    (centerAtom certified system valid)
    ⟨⟨0, by simp [ringN]⟩, firstRingWalk_center_vertex certified system valid⟩
    ⟨⟨0, by simp [ringN]⟩, secondRingWalk_center_vertex certified system valid⟩
    (fun i j same => ringWalk_vertices_inter_center certified system valid i j same)
    (fun i j same => ringWalk_edges_disjoint certified system valid i j same)

/-- **Embedded spiro coverage.**  A mechanically valid spiro system over a certified authoritative
source, together with one global continuous injective embedding of the selected-bond realization
of the exact reconstructed source graph, yields two embedded cycle walks — one for each ring —
such that:

* each walk has the ring's expected number of edges;
* every vertex is a bounded atom of the corresponding ring;
* every cycle edge records a genuine source binary interaction between its two vertices;
* every parametrized edge and every vertex coordinate is the supplied global embedding;
* and the two spatial cycle images intersect exactly at the embedded center.

No circle or planarity claim is made; these are embedded cycle realizations of the source
interaction graph. -/
theorem spiro_embedded_cycle_coverage
    (certified : CertifiedAuthoritativeChemicalInput)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor certified.input)
    (G : EmbeddedGraph (selectedSource (sourceGraph certified))
      (selectedTarget (sourceGraph certified))) :
    ∃ first second : CycleWalk (selectedSource (sourceGraph certified))
        (selectedTarget (sourceGraph certified)),
      first.n = ringN system.firstRingInternal ∧
      second.n = ringN system.secondRingInternal ∧
      (∀ i, (first.vertices i).val ∈ system.firstRing) ∧
      (∀ j, (second.vertices j).val ∈ system.secondRing) ∧
      (∀ i, P93AuthorityBinaryBond certified.input
        (first.vertices i).val (first.vertices (cycleSucc i)).val) ∧
      (∀ j, P93AuthorityBinaryBond certified.input
        (second.vertices j).val (second.vertices (cycleSucc j)).val) ∧
      (∀ i, (first.map G (Realization.vertex i) =
        G.conformation (first.vertices i))) ∧
      (∀ j, (second.map G (Realization.vertex j) =
        G.conformation (second.vertices j))) ∧
      Set.range (first.mapFun G) ∩ Set.range (second.mapFun G) =
        {G.conformation (centerAtom certified system valid)} := by
  refine ⟨firstRingWalk certified system valid, secondRingWalk certified system valid,
    rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact firstRingWalk_vertex_mem certified system valid i
  · intro j
    exact secondRingWalk_vertex_mem certified system valid j
  · intro i
    exact firstRingWalk_bond certified system valid i
  · intro j
    exact secondRingWalk_bond certified system valid j
  · intro i
    exact firstRingWalk_map_vertex certified system valid G i
  · intro j
    exact secondRingWalk_map_vertex certified system valid G j
  · exact firstRingWalk_inter_secondRingWalk_eq_center certified system valid G

end

end OrganicStereoEmbeddedSpiroCoverage

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedSpiroCoverage.exists_oriented_selectedBond_of_binaryBond
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedSpiroCoverage.CycleWalk.edges_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedSpiroCoverage.CycleWalk.mapFun_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedSpiroCoverage.CycleWalk.range_inter_eq_singleton
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedSpiroCoverage.ringBinaryBond
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedSpiroCoverage.ringWalk_edges_disjoint
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedSpiroCoverage.firstRingWalk_inter_secondRingWalk_eq_center
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedSpiroCoverage.spiro_embedded_cycle_coverage
