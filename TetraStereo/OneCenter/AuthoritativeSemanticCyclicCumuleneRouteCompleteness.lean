import TetraStereo.OneCenter.AuthoritativeSemanticCyclicCumuleneRouteConformance

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Reverse completeness of the cyclic-cumulene bond route

The forward conformance module proves that every bond of a perceived degree-two component is
owned by the cyclic route.  This module proves the converse.  A nonbranched ordinary-double
component containing an enumerated cycle cannot have a tail: every cycle vertex already has two
cycle neighbors, so the no-branch bound makes the cycle subgraph closed under ambient adjacency.
Connectedness then forces the whole component to be that cycle.  Its least atom is therefore the
canonical perceived representative.
-/

/-- A finite chain ending in a named last vertex is the support of a graph walk. -/
private theorem exists_walk_support_eq_append_singleton_of_isChain
    {V : Type*} {graph : SimpleGraph V}
    (first : V) (middle : List V) (last : V)
    (chain : (first :: (middle ++ [last])).IsChain graph.Adj) :
    ∃ walk : graph.Walk first last,
      walk.support = first :: (middle ++ [last]) := by
  induction middle generalizing first with
  | nil =>
      have adjacent : graph.Adj first last := by
        simpa using chain
      exact ⟨adjacent.toWalk, rfl⟩
  | cons next rest inductionHypothesis =>
      have split : graph.Adj first next ∧
          (next :: (rest ++ [last])).IsChain graph.Adj := by
        simpa using chain
      obtain ⟨walk, supportIdentity⟩ :=
        inductionHypothesis next split.2
      exact ⟨SimpleGraph.Walk.cons split.1 walk, by
        simp [supportIdentity]⟩

/-- A duplicate-free path of length at least three cannot already use its closing edge. -/
private theorem closing_edge_not_mem_walk_edges
    {V : Type*} {graph : SimpleGraph V}
    {first last : V} (walk : graph.Walk first last)
    (supportNodup : walk.support.Nodup)
    (lengthThree : 3 ≤ walk.support.length)
    (closing : graph.Adj last first) :
    s(last, first) ∉ walk.edges := by
  have path : walk.IsPath := SimpleGraph.Walk.IsPath.mk' supportNodup
  cases walk with
  | nil => simp at lengthThree
  | @cons _ second _ adjacent tail =>
      intro present
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at present
      rcases present with firstEdge | laterEdge
      · rw [Sym2.eq_iff] at firstEdge
        rcases firstEdge with direct | reverse
        · exact closing.ne direct.1
        · have secondIdentity : second = last := reverse.1.symm
          subst second
          have tailPath : tail.IsPath := by
            simpa using path.tail
          have tailIdentity : tail = SimpleGraph.Walk.nil :=
            (SimpleGraph.Walk.isPath_iff_eq_nil tail).mp tailPath
          subst tail
          simp at lengthThree
      · have firstInTail : first ∈ tail.support :=
          tail.snd_mem_support_of_mem_edges laterEdge
        have firstAbsent : first ∉ tail.support := by
          simpa using (List.nodup_cons.mp supportNodup).1
        exact firstAbsent firstInTail

/-- Graph reachability is also witnessed by the exhaustive simple-path enumeration. -/
theorem AromaticCanonicalOrdinaryDoubleReachable.connected
    {source : AuthoritativeChemicalInput}
    {left right : source.AromaticCanonicalAtom}
    (reachable :
      source.aromaticCanonicalOrdinaryDoubleSimpleGraph.Reachable left right) :
    source.AromaticCanonicalOrdinaryDoubleConnected left right := by
  let path := reachable.some.toPath
  let walk : source.aromaticCanonicalOrdinaryDoubleSimpleGraph.Walk left right := path
  have walkPath : walk.IsPath := path.property
  have valid : source.AromaticCanonicalOrdinaryCumulenePath walk.support :=
    ⟨walkPath.support_nodup, walk.isChain_adj_support⟩
  refine ⟨walk.support,
    (source.mem_aromaticCanonicalOrdinaryCumulenePaths_iff walk.support).mpr valid,
    ?_, ?_⟩
  · exact walk.start_mem_support
  · exact walk.end_mem_support

/-- Choosing another atom of a connected component does not change its finite atom set. -/
theorem aromaticCanonicalOrdinaryDoubleComponentAtoms_eq_of_mem
    (source : AuthoritativeChemicalInput)
    (anchor representative : source.AromaticCanonicalAtom)
    (representativeIn : representative ∈
      source.aromaticCanonicalOrdinaryDoubleComponentAtoms anchor) :
    source.aromaticCanonicalOrdinaryDoubleComponentAtoms representative =
      source.aromaticCanonicalOrdinaryDoubleComponentAtoms anchor := by
  ext atom
  rw [source.mem_aromaticCanonicalOrdinaryDoubleComponentAtoms_iff,
    source.mem_aromaticCanonicalOrdinaryDoubleComponentAtoms_iff]
  have anchorToRepresentative :=
    (source.mem_aromaticCanonicalOrdinaryDoubleComponentAtoms_iff
      anchor representative).mp representativeIn
  constructor
  · exact fun representativeToAtom =>
      anchorToRepresentative.trans representativeToAtom
  · exact fun anchorToAtom =>
      anchorToRepresentative.symm.trans anchorToAtom

/-- Every walk starting in a vertex set closed under graph adjacency also ends in that set. -/
private theorem walk_end_mem_of_adjacency_closed
    {V : Type*} {graph : SimpleGraph V} {vertices : Set V}
    {start finish : V} (walk : graph.Walk start finish)
    (closed : ∀ {left right}, left ∈ vertices → graph.Adj left right → right ∈ vertices)
    (startIn : start ∈ vertices) : finish ∈ vertices := by
  induction walk with
  | nil => exact startIn
  | cons adjacent tail inductionHypothesis =>
      exact inductionHypothesis (closed startIn adjacent)

/-- The no-branch plus cycle predicate produces a canonical degree-two component containing the
bond's left endpoint. -/
theorem exists_declarativeAromaticCanonicalCyclicCumuleneComponentContains_of_notBranched_cyclic
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (notBranched : ¬ source.AromaticCanonicalOrdinaryDoubleBondBranched bond)
    (cyclic : source.AromaticCanonicalOrdinaryDoubleBondCyclic bond) :
    ∃ component : source.AromaticCanonicalCyclicCumuleneComponent,
      source.DeclarativeAromaticCanonicalCyclicCumuleneComponentContains
        component bond.left := by
  classical
  obtain ⟨cycleAtoms, cyclePresent, bondInCycle⟩ := cyclic
  have cycleDerived :=
    (source.mem_aromaticCanonicalOrdinaryCumuleneCycles_iff cycleAtoms).mp cyclePresent
  obtain ⟨first, middle, last, cycleIdentity, cycleLength,
      cyclePath, closing⟩ := cycleDerived
  have cycleChain :
      (first :: (middle ++ [last])).IsChain
        source.aromaticCanonicalOrdinaryDoubleSimpleGraph.Adj := by
    simpa [cycleIdentity] using cyclePath.2
  obtain ⟨openWalk, openSupport⟩ :=
    exists_walk_support_eq_append_singleton_of_isChain
      first middle last cycleChain
  have openSupportNodup : openWalk.support.Nodup := by
    rw [openSupport, ← cycleIdentity]
    exact cyclePath.1
  have openSupportLength : 3 ≤ openWalk.support.length := by
    rw [openSupport, ← cycleIdentity]
    exact cycleLength
  have closingAbsent : s(last, first) ∉ openWalk.edges :=
    closing_edge_not_mem_walk_edges openWalk openSupportNodup
      openSupportLength closing
  let cycleWalk : source.aromaticCanonicalOrdinaryDoubleSimpleGraph.Walk last last :=
    SimpleGraph.Walk.cons closing openWalk
  have cycleWalkValid : cycleWalk.IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    exact ⟨SimpleGraph.Walk.IsPath.mk' openSupportNodup, closingAbsent⟩
  let cycleSubgraph := cycleWalk.toSubgraph
  let cycleGraph : SimpleGraph source.AromaticCanonicalAtom :=
    cycleSubgraph.spanningCoe

  have leftInCycleAtoms : bond.left ∈ cycleAtoms := by
    rcases bondInCycle with ⟨before, after, forward | reverse⟩
    · rw [forward]
      simp
    · rw [reverse]
      simp
  have cycleWalk_mem_support_iff (atom : source.AromaticCanonicalAtom) :
      atom ∈ cycleWalk.support ↔ atom ∈ cycleAtoms := by
    constructor
    · intro atomIn
      simp only [cycleWalk, SimpleGraph.Walk.support_cons, List.mem_cons] at atomIn
      rcases atomIn with rfl | atomInOpen
      · rw [cycleIdentity]
        simp
      · rw [openSupport] at atomInOpen
        rwa [cycleIdentity]
    · intro atomIn
      simp only [cycleWalk, SimpleGraph.Walk.support_cons, List.mem_cons]
      right
      rw [openSupport, ← cycleIdentity]
      exact atomIn
  have leftInCycleGraph : bond.left ∈ cycleSubgraph.verts := by
    rw [SimpleGraph.Walk.mem_verts_toSubgraph]
    exact (cycleWalk_mem_support_iff bond.left).mpr leftInCycleAtoms

  have connected_of_cycle_vertex : ∀ {atom}, atom ∈ cycleSubgraph.verts →
      source.AromaticCanonicalOrdinaryDoubleConnected bond.left atom := by
    intro atom atomIn
    have atomInCycleAtoms : atom ∈ cycleAtoms := by
      rw [SimpleGraph.Walk.mem_verts_toSubgraph] at atomIn
      exact (cycleWalk_mem_support_iff atom).mp atomIn
    exact ⟨cycleAtoms,
      (source.mem_aromaticCanonicalOrdinaryCumulenePaths_iff cycleAtoms).mpr cyclePath,
      leftInCycleAtoms, atomInCycleAtoms⟩

  have ambientNeighborNcard_le_two : ∀ {atom}, atom ∈ cycleSubgraph.verts →
      (source.aromaticCanonicalOrdinaryDoubleSimpleGraph.neighborSet atom).ncard ≤ 2 := by
    intro atom atomIn
    rw [← source.aromaticCanonicalOrdinaryDoubleNeighbors_length_eq_ncard atom]
    by_contra notLe
    have threeLe : 3 ≤
        (source.aromaticCanonicalOrdinaryDoubleNeighbors atom).length := by omega
    exact notBranched ⟨atom, source.mem_aromaticCanonicalAtomUniverse atom,
      connected_of_cycle_vertex atomIn, threeLe⟩

  have cycleNeighborSet_eq_ambient : ∀ {atom}, atom ∈ cycleSubgraph.verts →
      cycleGraph.neighborSet atom =
        source.aromaticCanonicalOrdinaryDoubleSimpleGraph.neighborSet atom := by
    intro atom atomIn
    have subset : cycleGraph.neighborSet atom ⊆
        source.aromaticCanonicalOrdinaryDoubleSimpleGraph.neighborSet atom := by
      intro neighbor neighborIn
      have subgraphAdjacent : cycleSubgraph.Adj atom neighbor := by
        simpa [cycleGraph, SimpleGraph.mem_neighborSet] using neighborIn
      exact subgraphAdjacent.adj_sub
    have cycleNcard : (cycleGraph.neighborSet atom).ncard = 2 := by
      have atomInSupport : atom ∈ cycleWalk.support :=
        (SimpleGraph.Walk.mem_verts_toSubgraph cycleWalk).mp atomIn
      simpa [cycleGraph] using
        cycleWalkValid.ncard_neighborSet_toSubgraph_eq_two atomInSupport
    apply Set.eq_of_subset_of_ncard_le subset
    rw [cycleNcard]
    exact ambientNeighborNcard_le_two atomIn

  have cycleClosed : ∀ {left right}, left ∈ cycleSubgraph.verts →
      source.aromaticCanonicalOrdinaryDoubleSimpleGraph.Adj left right →
        right ∈ cycleSubgraph.verts := by
    intro left right leftIn adjacent
    have rightNeighbor : right ∈ cycleGraph.neighborSet left := by
      rw [cycleNeighborSet_eq_ambient leftIn]
      exact adjacent
    have subgraphAdjacent : cycleSubgraph.Adj left right := by
      simpa [cycleGraph, SimpleGraph.mem_neighborSet] using rightNeighbor
    exact cycleSubgraph.edge_vert subgraphAdjacent.symm

  have componentAtomInCycle : ∀ {atom},
      atom ∈ source.aromaticCanonicalOrdinaryDoubleComponentAtoms bond.left →
        atom ∈ cycleSubgraph.verts := by
    intro atom atomIn
    have reachable :=
      (source.mem_aromaticCanonicalOrdinaryDoubleComponentAtoms_iff
        bond.left atom).mp atomIn
    exact walk_end_mem_of_adjacency_closed reachable.some cycleClosed leftInCycleGraph

  have cycleAtomInComponent : ∀ {atom}, atom ∈ cycleSubgraph.verts →
      atom ∈ source.aromaticCanonicalOrdinaryDoubleComponentAtoms bond.left := by
    intro atom atomIn
    rw [source.mem_aromaticCanonicalOrdinaryDoubleComponentAtoms_iff]
    exact (connected_of_cycle_vertex atomIn).reachable

  have componentCardThree : 3 ≤
      (source.aromaticCanonicalOrdinaryDoubleComponentAtoms bond.left).card := by
    have cycleToFinsetSubset : cycleAtoms.toFinset ⊆
        source.aromaticCanonicalOrdinaryDoubleComponentAtoms bond.left := by
      intro atom atomIn
      have atomInCycle : atom ∈ cycleSubgraph.verts := by
        rw [SimpleGraph.Walk.mem_verts_toSubgraph]
        exact (cycleWalk_mem_support_iff atom).mpr (by simpa using atomIn)
      exact cycleAtomInComponent atomInCycle
    have cycleCardLe := Finset.card_le_card cycleToFinsetSubset
    rw [List.toFinset_card_of_nodup cyclePath.1] at cycleCardLe
    omega

  have componentDegreeTwo : ∀ atom,
      atom ∈ source.aromaticCanonicalOrdinaryDoubleComponentAtoms bond.left →
        (source.aromaticCanonicalOrdinaryDoubleNeighbors atom).length = 2 := by
    intro atom atomIn
    have atomInCycle := componentAtomInCycle atomIn
    have atomInSupport : atom ∈ cycleWalk.support :=
      (SimpleGraph.Walk.mem_verts_toSubgraph cycleWalk).mp atomInCycle
    rw [source.aromaticCanonicalOrdinaryDoubleNeighbors_length_eq_ncard atom,
      ← cycleNeighborSet_eq_ambient atomInCycle]
    simpa [cycleGraph] using
      cycleWalkValid.ncard_neighborSet_toSubgraph_eq_two atomInSupport

  let leftComponent := source.aromaticCanonicalOrdinaryDoubleComponentAtoms bond.left
  have leftComponentNonempty : leftComponent.Nonempty :=
    ⟨bond.left, source.representative_mem_aromaticCanonicalOrdinaryDoubleComponentAtoms
      bond.left⟩
  let representative := leftComponent.min' leftComponentNonempty
  have representativeIn : representative ∈ leftComponent :=
    Finset.min'_mem leftComponent leftComponentNonempty
  have componentIdentity :
      source.aromaticCanonicalOrdinaryDoubleComponentAtoms representative =
        source.aromaticCanonicalOrdinaryDoubleComponentAtoms bond.left := by
    exact source.aromaticCanonicalOrdinaryDoubleComponentAtoms_eq_of_mem
      bond.left representative representativeIn
  let component : source.AromaticCanonicalCyclicCumuleneComponent :=
    { representative := representative }
  have componentDerived :
      source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component := by
    change source.DeclarativeAromaticCanonicalCyclicCumuleneComponentAt representative
    refine ⟨?_, ?_, ?_⟩
    · rw [componentIdentity]
      exact componentCardThree
    · intro atom atomIn
      apply componentDegreeTwo atom
      rw [← componentIdentity]
      exact atomIn
    · intro atom atomIn
      apply Finset.min'_le leftComponent atom
      change atom ∈ source.aromaticCanonicalOrdinaryDoubleComponentAtoms bond.left
      rw [← componentIdentity]
      exact atomIn
  refine ⟨component, componentDerived, ?_⟩
  rw [componentIdentity]
  exact source.representative_mem_aromaticCanonicalOrdinaryDoubleComponentAtoms bond.left

/-- Exact public reverse conformance: cyclic-route ownership is equivalent to containment of the
left endpoint in a publicly perceived canonical cyclic-cumulene component. -/
@[simp] theorem mem_aromaticCanonicalCyclicCumuleneBondCarriers_iff_exists_component_contains_left
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    bond ∈ source.aromaticCanonicalCyclicCumuleneBondCarriers ↔
      ∃ component ∈ source.aromaticCanonicalCyclicCumuleneComponents,
        source.DeclarativeAromaticCanonicalCyclicCumuleneComponentContains
          component bond.left := by
  constructor
  · intro bondPresent
    obtain ⟨notBranched, cyclic⟩ :=
      (source.mem_aromaticCanonicalCyclicCumuleneBondCarriers_iff bond).mp bondPresent
    obtain ⟨component, contains⟩ :=
      source.exists_declarativeAromaticCanonicalCyclicCumuleneComponentContains_of_notBranched_cyclic
        bond notBranched cyclic
    exact ⟨component,
      (source.mem_aromaticCanonicalCyclicCumuleneComponents_iff component).mpr contains.1,
      contains⟩
  · rintro ⟨component, componentPresent, contains⟩
    have derived :=
      (source.mem_aromaticCanonicalCyclicCumuleneComponents_iff component).mp componentPresent
    exact derived.mem_cyclicBondCarriers_of_left_mem source bond contains.2

/-- The perceived public component containing a cyclic-route bond endpoint exists uniquely. -/
theorem existsUnique_mem_aromaticCanonicalCyclicCumuleneComponents_contains_left_of_mem
    (source : AuthoritativeChemicalInput)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (bondPresent : bond ∈ source.aromaticCanonicalCyclicCumuleneBondCarriers) :
    ∃! component : source.AromaticCanonicalCyclicCumuleneComponent,
      component ∈ source.aromaticCanonicalCyclicCumuleneComponents ∧
        source.DeclarativeAromaticCanonicalCyclicCumuleneComponentContains
          component bond.left := by
  obtain ⟨component, componentPresent, contains⟩ :=
    (source.mem_aromaticCanonicalCyclicCumuleneBondCarriers_iff_exists_component_contains_left
      bond).mp bondPresent
  refine ⟨component, ⟨componentPresent, contains⟩, ?_⟩
  intro other otherDerived
  exact source.declarativeAromaticCanonicalCyclicCumuleneComponentContains_unique
    bond.left otherDerived.2 contains

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
