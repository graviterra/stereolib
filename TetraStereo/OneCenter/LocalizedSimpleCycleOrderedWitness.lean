import TetraStereo.OneCenter.LocalizedMonocyclicDoubleBondPerception
import TetraStereo.KernelOnly
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Set.Card

set_option autoImplicit false

/-!
# Ordered internal paths for graph-perceived simple rings

The declarative simple-cycle predicate `DeclarativeLocalizedSimpleCycleVertexSet` of
`LocalizedMonocyclicDoubleBondPerception` speaks about a *vertex set*: at least three vertices,
exactly two retained neighbours per vertex, and connectivity inside the set.  Downstream
structural inventory needs an actual *order* of that vertex set: a list that starts at a
designated center atom, visits every ring atom exactly once, and whose consecutive entries
(including the closing return to the center) are positive-bond adjacent.

This module supplies that order without assuming any traversal, path, solver output or
Hamiltonicity input:

* `LocalizedSimpleCycleInternalPathSpec` is the independent meaning of such an internal order;
* `localizedSimpleCycleInternalPath?` is an executable canonical selector that enumerates the
  permutations of `(ring.erase center).sort (· ≤ ·)` and returns the first closed adjacency
  chain of length at least two.  It uses no classical choice;
* `localizedSimpleCycleInternalPath?_sound` states that every computed answer satisfies the
  specification;
* `localizedSimpleCycleInternalPath?_complete` states that every declarative simple-cycle
  vertex set containing the center admits a computed answer.

The mathematical content of completeness is the finite-graph fact that a connected graph in
which every vertex has exactly two neighbours is a single cycle through all of its vertices.
It is obtained from Mathlib's `SimpleGraph.IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp`
applied to the induced graph on the ring.  No physical direction, chordlessness certificate,
descriptor or CIP ranking is claimed here: the selector merely orders a graph-perceived ring.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-- Independent meaning of an ordered internal traversal of a graph-perceived simple ring.

`internal` lists the ring atoms other than `center`, in the order in which the traversal visits
them; the full closed walk is `center :: internal ++ [center]`.  The requirements are exactly:

* the center and the listed atoms are pairwise distinct;
* together they are precisely the ring vertex set;
* at least two other atoms are visited (so the ring has at least three vertices);
* consecutive entries of the closed walk are positive-bond adjacent. -/
def LocalizedSimpleCycleInternalPathSpec (input : CertifiedLocalizedCIPInput)
    (ring : Finset input.Atom) (center : input.Atom) (internal : List input.Atom) : Prop :=
  (center :: internal).Nodup ∧ (center :: internal).toFinset = ring ∧
    2 ≤ internal.length ∧
      (center :: internal ++ [center]).IsChain input.moleculeGraph.Adj

/-- Executable canonical selector for the ordered internal traversal of a ring.

The candidate order is the sorted `Finset` canonical list of `ring.erase center`, and the
selector scans its permutations in the canonical `List.permutations` order and returns the first
one which is closed-adjacent and visits at least two atoms besides the center.  When the center
is not a ring atom, or no candidate qualifies, the result is `none`.

The scan is a genuine finite computation: `Finset.sort`, `List.permutations`, `List.filter` and
`List.head?` are all computable, and no classical choice is used.  Being an *ordering* device, it
makes no chordlessness or uniqueness claim about the ring. -/
def localizedSimpleCycleInternalPath? (input : CertifiedLocalizedCIPInput)
    (ring : Finset input.Atom) (center : input.Atom) : Option (List input.Atom) :=
  if center ∈ ring then
    (List.filter
        (fun internal =>
          2 ≤ internal.length ∧
            (center :: internal ++ [center]).IsChain input.moleculeGraph.Adj)
        (List.permutations ((ring.erase center).sort (· ≤ ·)))).head?
  else none

/-- **Soundness of the ordered internal-path selector.**  Every returned list is an ordered
internal traversal of `ring` in the sense of `LocalizedSimpleCycleInternalPathSpec`. -/
theorem localizedSimpleCycleInternalPath?_sound (input : CertifiedLocalizedCIPInput)
    (ring : Finset input.Atom) (center : input.Atom) (internal : List input.Atom)
    (computed : input.localizedSimpleCycleInternalPath? ring center = some internal) :
    input.LocalizedSimpleCycleInternalPathSpec ring center internal := by
  unfold localizedSimpleCycleInternalPath? at computed
  by_cases centerMem : center ∈ ring
  · rw [if_pos centerMem] at computed
    have accepted : internal ∈
        (List.filter
            (fun candidate =>
              2 ≤ candidate.length ∧
                (center :: candidate ++ [center]).IsChain input.moleculeGraph.Adj)
            (List.permutations ((ring.erase center).sort (· ≤ ·)))) := by
      rw [List.head?_eq_some_iff] at computed
      obtain ⟨rest, hrest⟩ := computed
      rw [hrest]
      simp
    have permuted : internal ∈ List.permutations ((ring.erase center).sort (· ≤ ·)) :=
      (List.mem_filter.mp accepted).1
    have acceptedBool :
        decide (2 ≤ internal.length ∧
          (center :: internal ++ [center]).IsChain input.moleculeGraph.Adj) = true :=
      (List.mem_filter.mp accepted).2
    have acceptedProp : 2 ≤ internal.length ∧
        (center :: internal ++ [center]).IsChain input.moleculeGraph.Adj :=
      of_decide_eq_true acceptedBool
    have lengthLower : 2 ≤ internal.length := acceptedProp.1
    have closedChain : (center :: internal ++ [center]).IsChain input.moleculeGraph.Adj :=
      acceptedProp.2
    have permutation : List.Perm internal ((ring.erase center).sort (· ≤ ·)) :=
      List.mem_permutations.mp permuted
    have sortedNodup : ((ring.erase center).sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
    have internalNodup : internal.Nodup :=
      (List.Perm.nodup_iff permutation).mpr sortedNodup
    have sortedFinset : ((ring.erase center).sort (· ≤ ·)).toFinset = ring.erase center :=
      Finset.sort_toFinset (ring.erase center) (· ≤ ·)
    have internalFinset : internal.toFinset = ring.erase center := by
      rw [← sortedFinset]
      ext atom
      rw [List.mem_toFinset, List.mem_toFinset]
      exact List.Perm.mem_iff permutation
    have centerAbsent : center ∉ internal.toFinset := by
      rw [internalFinset]
      exact Finset.notMem_erase center ring
    refine ⟨?_, ?_, lengthLower, closedChain⟩
    · rw [List.nodup_cons]
      exact ⟨fun member => centerAbsent (List.mem_toFinset.mpr member), internalNodup⟩
    · rw [List.toFinset_cons, internalFinset, Finset.insert_erase centerMem]
  · rw [if_neg centerMem] at computed
    simp at computed

/-- **Completeness of the ordered internal-path selector.**  Every declarative simple-cycle
vertex set containing the center admits a computed answer.

The proof runs on the graph `input.localizedInducedCycleGraph ring`.  Its only vertices with a
nonempty neighbour set are the ring atoms, and those have exactly two retained neighbours, so
Mathlib's finite cycle theorem produces a cycle walk based at the center whose vertex set is the
connected component of the center, which is exactly `ring`.  Writing `internal` for the tail of
that walk without its closing center gives a closed adjacency chain visiting every ring atom
exactly once; since it is a permutation of `ring.erase center`, it occurs in the selector's
permutation enumeration and hence in the filtered list whose head the selector returns. -/
theorem localizedSimpleCycleInternalPath?_complete (input : CertifiedLocalizedCIPInput)
    (ring : Finset input.Atom) (center : input.Atom)
    (cycle : input.DeclarativeLocalizedSimpleCycleVertexSet ring)
    (centerMem : center ∈ ring) :
    ∃ internal, input.localizedSimpleCycleInternalPath? ring center = some internal ∧
      input.LocalizedSimpleCycleInternalPathSpec ring center internal := by
  classical
  have hcycle : 3 ≤ ring.card ∧
      (∀ atom, atom ∈ ring → (input.localizedCycleNeighbors ring atom).card = 2) ∧
      (∀ left, left ∈ ring → ∀ right, right ∈ ring →
        (input.localizedInducedCycleGraph ring).Reachable left right) := cycle
  obtain ⟨hcard3, hdegree, hconn⟩ := hcycle
  -- A walk in the induced graph whose endpoint lies in the ring starts in the ring.
  have walkFst_mem : ∀ {a b : input.Atom},
      (input.localizedInducedCycleGraph ring).Walk a b → b ∈ ring → a ∈ ring := by
    intro a b p
    induction p with
    | nil => intro hb; exact hb
    | cons h _ _ => intro _; exact h.1
  -- Neighbour sets inside the ring are the retained cycle neighbours.
  have hneighborSet : ∀ v ∈ ring,
      (input.localizedInducedCycleGraph ring).neighborSet v =
        (↑(input.localizedCycleNeighbors ring v) : Set input.Atom) := by
    intro v hv
    ext w
    rw [SimpleGraph.mem_neighborSet (input.localizedInducedCycleGraph ring) v w,
      Finset.mem_coe, mem_localizedCycleNeighbors_iff,
      localizedInducedCycleGraph_adj input ring v w]
    exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hv, h.1, h.2⟩⟩
  -- The induced graph is a graph of cycles: isolated outside the ring, degree two inside.
  have hcycles : (input.localizedInducedCycleGraph ring).IsCycles := by
    intro v hvNonempty
    obtain ⟨w, hw⟩ := hvNonempty
    have hAdj : (input.localizedInducedCycleGraph ring).Adj v w :=
      (SimpleGraph.mem_neighborSet (input.localizedInducedCycleGraph ring) v w).mp hw
    have hvMem : v ∈ ring :=
      ((localizedInducedCycleGraph_adj input ring v w).mp hAdj).1
    rw [hneighborSet v hvMem, Set.ncard_coe_finset]
    exact hdegree v hvMem
  -- The connected component of the center is exactly the ring.
  let c : (input.localizedInducedCycleGraph ring).ConnectedComponent :=
    (input.localizedInducedCycleGraph ring).connectedComponentMk center
  have hcenterSupp : center ∈ c.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c center).mpr rfl
  have hcompSupp : c.supp = (↑ring : Set input.Atom) := by
    ext x
    constructor
    · intro hx
      have hmk : (input.localizedInducedCycleGraph ring).connectedComponentMk x =
          (input.localizedInducedCycleGraph ring).connectedComponentMk center :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff c x).mp hx
      have hreach : (input.localizedInducedCycleGraph ring).Reachable x center :=
        (SimpleGraph.ConnectedComponent.eq).mp hmk
      obtain ⟨p⟩ := hreach
      exact walkFst_mem p centerMem
    · intro hx
      have hreach : (input.localizedInducedCycleGraph ring).Reachable x center :=
        hconn x hx center centerMem
      have hmk : (input.localizedInducedCycleGraph ring).connectedComponentMk x = c :=
        (SimpleGraph.ConnectedComponent.eq).mpr hreach
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff c x).mpr hmk
  -- The center has a neighbour, so Mathlib's finite cycle theorem applies.
  have hcenterNeighbors :
      ((input.localizedInducedCycleGraph ring).neighborSet center).Nonempty := by
    obtain ⟨w, hw⟩ : (input.localizedCycleNeighbors ring center).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have htwo := hdegree center centerMem
      rw [hempty, Finset.card_empty] at htwo
      omega
    refine ⟨w, ?_⟩
    rw [hneighborSet center centerMem]
    exact Finset.mem_coe.mpr hw
  obtain ⟨walk, walkCycle, walkVerts⟩ :=
    hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (v := center) (c := c) hcenterSupp hcenterNeighbors
  -- The cycle walk visits exactly the ring.
  have supportFinset : walk.support.toFinset = ring := by
    ext x
    rw [List.mem_toFinset]
    constructor
    · intro hx
      have hx' : x ∈ walk.toSubgraph.verts := by
        rwa [SimpleGraph.Walk.mem_verts_toSubgraph]
      rw [walkVerts, hcompSupp] at hx'
      exact Finset.mem_coe.mp hx'
    · intro hx
      have hx' : x ∈ walk.toSubgraph.verts := by
        rw [walkVerts, hcompSupp]
        exact Finset.mem_coe.mpr hx
      rwa [SimpleGraph.Walk.mem_verts_toSubgraph] at hx'
  have hwalkLen : 3 ≤ walk.length := walkCycle.three_le_length
  have htailLen : (walk.support.tail).length = walk.length := by
    rw [List.length_tail, SimpleGraph.Walk.length_support]
    omega
  have htailNe : walk.support.tail ≠ [] := by
    intro hnil
    have hzero : (walk.support.tail).length = 0 := by rw [hnil]; rfl
    omega
  have hsuppLast : walk.support.getLast? = some center := by
    rw [List.getLast?_eq_some_getLast (SimpleGraph.Walk.support_ne_nil walk)]
    exact congrArg some (SimpleGraph.Walk.getLast_support walk)
  have htailLastOpt : (walk.support.tail).getLast? = some center := by
    obtain ⟨b, l, hbl⟩ := List.exists_cons_of_ne_nil htailNe
    rw [hbl]
    have hsupp : walk.support = center :: b :: l := by
      rw [SimpleGraph.Walk.support_eq_cons walk, hbl]
    rw [← List.getLast?_cons_cons (a := center) (b := b) (l := l), ← hsupp]
    exact hsuppLast
  have htailLast : (walk.support.tail).getLast htailNe = center := by
    have hopt := List.getLast?_eq_some_getLast htailNe
    rw [hopt] at htailLastOpt
    exact Option.some.inj htailLastOpt
  set internal : List input.Atom := walk.support.tail.dropLast with hinternal
  have htailEq : walk.support.tail.dropLast ++ [center] = walk.support.tail := by
    have h := List.dropLast_concat_getLast htailNe
    rwa [htailLast] at h
  have hfullEq : center :: internal ++ [center] = walk.support := by
    rw [List.cons_append]
    rw [show internal ++ [center] = walk.support.tail from htailEq]
    exact (SimpleGraph.Walk.support_eq_cons walk).symm
  have htailSplit : walk.support.tail = internal ++ [center] := by
    rw [hinternal]
    exact htailEq.symm
  have hparts := List.nodup_append.mp (htailSplit ▸ walkCycle.support_nodup)
  have hcenterNotInternal : center ∉ internal := by
    intro hmem
    exact hparts.2.2 center hmem center (by simp) rfl
  have hnodupCons : (center :: internal).Nodup := by
    rw [List.nodup_cons]
    exact ⟨hcenterNotInternal, hparts.1⟩
  have hfin : (center :: internal).toFinset = ring := by
    have hfullFin : (center :: internal ++ [center]).toFinset = ring := by
      rw [hfullEq]
      exact supportFinset
    rw [← hfullFin]
    ext x
    simp only [List.mem_toFinset, List.mem_cons, List.mem_append]
    tauto
  have hinternalFin : internal.toFinset = ring.erase center := by
    ext x
    rw [Finset.mem_erase]
    constructor
    · intro hx
      refine ⟨?_, ?_⟩
      · intro hxc
        exact hcenterNotInternal (List.mem_toFinset.mp (hxc ▸ hx))
      · rw [← hfin, List.toFinset_cons]
        exact Finset.mem_insert_of_mem hx
    · rintro ⟨hxc, hxring⟩
      have hx : x ∈ (center :: internal).toFinset := by
        rw [hfin]
        exact hxring
      rw [List.toFinset_cons, Finset.mem_insert] at hx
      rcases hx with hx | hx
      · exact absurd hx hxc
      · exact hx
  have hcard : ring.card = internal.length + 1 := by
    rw [← hfin, List.toFinset_card_of_nodup hnodupCons]
    simp
  have hlength : 2 ≤ internal.length := by omega
  have hchainMol : (center :: internal ++ [center]).IsChain input.moleculeGraph.Adj := by
    rw [hfullEq]
    exact (SimpleGraph.Walk.isChain_adj_support walk).imp
      (fun a b h => ((localizedInducedCycleGraph_adj input ring a b).mp h).2.2)
  -- The traversal is a permutation of the selector's canonical enumeration.
  have hperm : List.Perm internal ((ring.erase center).sort (· ≤ ·)) :=
    List.perm_of_nodup_nodup_toFinset_eq hparts.1
      (Finset.sort_nodup (ring.erase center) (· ≤ ·)) (by
        rw [hinternalFin, Finset.sort_toFinset])
  have hmemPerm : internal ∈ List.permutations ((ring.erase center).sort (· ≤ ·)) :=
    List.mem_permutations.mpr hperm
  have hcond : decide (2 ≤ internal.length ∧
      (center :: internal ++ [center]).IsChain input.moleculeGraph.Adj) = true :=
    decide_eq_true ⟨hlength, hchainMol⟩
  have hmemFiltered : internal ∈
      (List.filter
        (fun candidate =>
          2 ≤ candidate.length ∧
            (center :: candidate ++ [center]).IsChain input.moleculeGraph.Adj)
        (List.permutations ((ring.erase center).sort (· ≤ ·)))) :=
    List.mem_filter.mpr ⟨hmemPerm, hcond⟩
  have hne : (List.filter
        (fun candidate =>
          2 ≤ candidate.length ∧
            (center :: candidate ++ [center]).IsChain input.moleculeGraph.Adj)
        (List.permutations ((ring.erase center).sort (· ≤ ·)))) ≠ [] := by
    intro hnil
    rw [hnil] at hmemFiltered
    exact absurd hmemFiltered (by simp)
  obtain ⟨x, xs, hfl⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨x, ?_, ?_⟩
  · unfold localizedSimpleCycleInternalPath?
    rw [if_pos centerMem, hfl]
    rfl
  · apply localizedSimpleCycleInternalPath?_sound
    unfold localizedSimpleCycleInternalPath?
    rw [if_pos centerMem, hfl]
    rfl

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedSimpleCycleInternalPath?_sound
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedSimpleCycleInternalPath?_complete
