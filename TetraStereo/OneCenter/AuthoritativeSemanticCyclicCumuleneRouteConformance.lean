import TetraStereo.OneCenter.AuthoritativeSemanticCyclicCumuleneComponentPerception
import Mathlib.Combinatorics.SimpleGraph.Matching

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Conformance of cyclic-cumulene component perception to the bond router

The P-31 component detector and the older P-93 bond topology router are deliberately independent.
This module proves the graph-theoretic bridge between them.  In particular, a source component
accepted by the degree-two component detector has no branch vertex, and every ordinary-double
edge of that component lies on an exhaustively enumerated simple ordinary-double cycle.
-/

/-- The executable neighbor list has exactly the cardinality of the corresponding graph-theoretic
neighbor set. -/
theorem aromaticCanonicalOrdinaryDoubleNeighbors_length_eq_ncard
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom) :
    (source.aromaticCanonicalOrdinaryDoubleNeighbors atom).length =
      (source.aromaticCanonicalOrdinaryDoubleSimpleGraph.neighborSet atom).ncard := by
  classical
  have neighborsNodup :
      (source.aromaticCanonicalOrdinaryDoubleNeighbors atom).Nodup := by
    unfold aromaticCanonicalOrdinaryDoubleNeighbors
    exact source.aromaticCanonicalAtomUniverse_nodup.filter _
  have toFinsetIdentity :
      (source.aromaticCanonicalOrdinaryDoubleNeighbors atom).toFinset =
        (source.aromaticCanonicalOrdinaryDoubleSimpleGraph.neighborSet atom).toFinset := by
    ext neighbor
    simp [source.mem_aromaticCanonicalOrdinaryDoubleNeighbors_iff,
      SimpleGraph.mem_neighborSet]
  calc
    (source.aromaticCanonicalOrdinaryDoubleNeighbors atom).length =
        (source.aromaticCanonicalOrdinaryDoubleNeighbors atom).toFinset.card :=
      (List.toFinset_card_of_nodup neighborsNodup).symm
    _ = (source.aromaticCanonicalOrdinaryDoubleSimpleGraph.neighborSet atom).toFinset.card :=
      congrArg Finset.card toFinsetIdentity
    _ = (source.aromaticCanonicalOrdinaryDoubleSimpleGraph.neighborSet atom).ncard := by
      have finiteNeighbors :
          (source.aromaticCanonicalOrdinaryDoubleSimpleGraph.neighborSet atom).Finite :=
        Set.toFinite _
      simpa [Set.toFinite_toFinset] using
        (Set.ncard_eq_toFinset_card _ finiteNeighbors).symm

/-- Membership in the finite component atom set is the standard simple-graph connected-component
membership relation. -/
theorem mem_aromaticCanonicalOrdinaryDoubleComponentAtoms_iff_mem_component
    (source : AuthoritativeChemicalInput)
    (representative atom : source.AromaticCanonicalAtom) :
    atom ∈ source.aromaticCanonicalOrdinaryDoubleComponentAtoms representative ↔
      atom ∈
        (source.aromaticCanonicalOrdinaryDoubleSimpleGraph.connectedComponentMk
          representative).supp := by
  rw [source.mem_aromaticCanonicalOrdinaryDoubleComponentAtoms_iff,
    SimpleGraph.ConnectedComponent.mem_supp_iff,
    SimpleGraph.ConnectedComponent.eq]
  exact source.aromaticCanonicalOrdinaryDoubleSimpleGraph.reachable_comm

/-- The path-enumeration connectivity predicate implies ordinary-double graph reachability. -/
theorem AromaticCanonicalOrdinaryDoubleConnected.reachable
    {source : AuthoritativeChemicalInput}
    {left right : source.AromaticCanonicalAtom}
    (connected : source.AromaticCanonicalOrdinaryDoubleConnected left right) :
    source.aromaticCanonicalOrdinaryDoubleSimpleGraph.Reachable left right := by
  rcases connected with ⟨path, pathPresent, leftPresent, rightPresent⟩
  have valid :=
    (source.mem_aromaticCanonicalOrdinaryCumulenePaths_iff path).mp pathPresent
  cases path with
  | nil => simp at leftPresent
  | cons first rest =>
      have reachableFromFirst : ∀ atom ∈ first :: rest,
          source.aromaticCanonicalOrdinaryDoubleSimpleGraph.Reachable first atom := by
        apply valid.2.induction
        · intro prior next adjacent reachable
          have graphAdjacent :
              source.aromaticCanonicalOrdinaryDoubleSimpleGraph.Adj prior next := adjacent
          exact reachable.trans graphAdjacent.reachable
        · intro _nonempty
          exact SimpleGraph.Reachable.refl first
      exact (reachableFromFirst left leftPresent).symm.trans
        (reachableFromFirst right rightPresent)

/-- The spanning graph of the connected component selected by `representative`.  Vertices outside
that component are isolated, allowing finite cycle theorems to be applied locally. -/
noncomputable def aromaticCanonicalOrdinaryDoubleComponentGraph
    (source : AuthoritativeChemicalInput)
    (representative : source.AromaticCanonicalAtom) :
    SimpleGraph source.AromaticCanonicalAtom :=
  (source.aromaticCanonicalOrdinaryDoubleSimpleGraph.connectedComponentMk
    representative).toSimpleGraph.spanningCoe

theorem aromaticCanonicalOrdinaryDoubleComponentGraph_le
    (source : AuthoritativeChemicalInput)
    (representative : source.AromaticCanonicalAtom) :
    source.aromaticCanonicalOrdinaryDoubleComponentGraph representative ≤
      source.aromaticCanonicalOrdinaryDoubleSimpleGraph := by
  exact SimpleGraph.spanningCoe_induce_le
    source.aromaticCanonicalOrdinaryDoubleSimpleGraph
    (source.aromaticCanonicalOrdinaryDoubleSimpleGraph.connectedComponentMk
      representative).supp

/-- Degree two on the independently selected component is exactly Mathlib's finite `IsCycles`
condition on its induced spanning graph. -/
theorem DeclarativeAromaticCanonicalCyclicCumuleneComponent.isCycles_componentGraph
    (source : AuthoritativeChemicalInput)
    {component : source.AromaticCanonicalCyclicCumuleneComponent}
    (derived : source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component) :
    (source.aromaticCanonicalOrdinaryDoubleComponentGraph
      component.representative).IsCycles := by
  classical
  let graph := source.aromaticCanonicalOrdinaryDoubleSimpleGraph
  let connectedComponent := graph.connectedComponentMk component.representative
  intro atom nonempty
  obtain ⟨neighbor, adjacent⟩ := nonempty
  have atomInComponent : atom ∈ connectedComponent.supp :=
    (connectedComponent.adj_spanningCoe_toSimpleGraph.mp adjacent).1
  have neighborSetIdentity :
      (source.aromaticCanonicalOrdinaryDoubleComponentGraph
          component.representative).neighborSet atom = graph.neighborSet atom := by
    ext candidate
    simp only [SimpleGraph.mem_neighborSet,
      aromaticCanonicalOrdinaryDoubleComponentGraph,
      SimpleGraph.ConnectedComponent.adj_spanningCoe_toSimpleGraph,
      atomInComponent, true_and, graph, connectedComponent]
  rw [neighborSetIdentity]
  rw [← source.aromaticCanonicalOrdinaryDoubleNeighbors_length_eq_ncard atom]
  exact derived.2.1 atom
    ((source.mem_aromaticCanonicalOrdinaryDoubleComponentAtoms_iff_mem_component
      component.representative atom).mpr atomInComponent)

/-- A component atom connected by the enumeration predicate remains in the same independently
selected component. -/
theorem DeclarativeAromaticCanonicalCyclicCumuleneComponent.mem_of_connected
    (source : AuthoritativeChemicalInput)
    {component : source.AromaticCanonicalCyclicCumuleneComponent}
    (_derived : source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component)
    {anchor atom : source.AromaticCanonicalAtom}
    (anchorIn : anchor ∈ source.aromaticCanonicalOrdinaryDoubleComponentAtoms
      component.representative)
    (connected : source.AromaticCanonicalOrdinaryDoubleConnected anchor atom) :
    atom ∈ source.aromaticCanonicalOrdinaryDoubleComponentAtoms
      component.representative := by
  rw [source.mem_aromaticCanonicalOrdinaryDoubleComponentAtoms_iff]
  exact ((source.mem_aromaticCanonicalOrdinaryDoubleComponentAtoms_iff
    component.representative anchor).mp anchorIn).trans connected.reachable

/-- No bond in a fully cyclic degree-two component can be classified as part of a branched
ordinary-double network. -/
theorem DeclarativeAromaticCanonicalCyclicCumuleneComponent.not_branched_of_left_mem
    (source : AuthoritativeChemicalInput)
    {component : source.AromaticCanonicalCyclicCumuleneComponent}
    (derived : source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftIn : bond.left ∈ source.aromaticCanonicalOrdinaryDoubleComponentAtoms
      component.representative) :
    ¬ source.AromaticCanonicalOrdinaryDoubleBondBranched bond := by
  rintro ⟨atom, _atomPresent, connected, degreeThree⟩
  have atomIn := derived.mem_of_connected source leftIn connected
  have degreeTwo := derived.2.1 atom atomIn
  omega

/-- A graph-theoretic simple cycle gives exactly the list-level cycle accepted by the exhaustive
source enumerator.  `dropLast` removes the repeated closing vertex of the walk. -/
theorem aromaticCanonicalOrdinaryCumuleneCycle_of_isCycle
    (source : AuthoritativeChemicalInput)
    {start : source.AromaticCanonicalAtom}
    (walk : source.aromaticCanonicalOrdinaryDoubleSimpleGraph.Walk start start)
    (cycle : walk.IsCycle) :
    source.AromaticCanonicalOrdinaryCumuleneCycle walk.support.dropLast := by
  classical
  let path := walk.support.dropLast
  have pathLength : path.length = walk.length := by
    simp [path, walk.length_support]
  have lengthThree : 3 ≤ path.length := by
    rw [pathLength]
    exact cycle.three_le_length
  have pathNonempty : path ≠ [] := by
    intro empty
    simp [empty] at lengthThree
  have tailNonempty : path.tail ≠ [] := by
    intro empty
    have short : path.length ≤ 1 := by
      rw [← List.cons_head_tail pathNonempty, empty]
      simp
    omega
  have supportEnds :
      walk.support.head walk.support_ne_nil =
        walk.support.getLast walk.support_ne_nil := by
    simp
  have pathNodup : path.Nodup := by
    exact (List.IsRotated.dropLast_tail walk.support_ne_nil supportEnds).nodup_iff.mpr
      cycle.support_nodup
  have pathChain :
      path.IsChain source.AromaticCanonicalOrdinaryDoubleBond := by
    exact walk.isChain_adj_support.dropLast
  have supportIdentity : path ++ [start] = walk.support := by
    simpa [path] using List.dropLast_append_getLast walk.support_ne_nil
  have closedChain :
      (path ++ [start]).IsChain source.AromaticCanonicalOrdinaryDoubleBond := by
    rw [supportIdentity]
    exact walk.isChain_adj_support
  rw [List.isChain_append] at closedChain
  have closing :
      source.AromaticCanonicalOrdinaryDoubleBond (path.getLast pathNonempty) start := by
    apply closedChain.2.2 (path.getLast pathNonempty)
    · rw [List.getLast?_eq_some_getLast pathNonempty]
      simp
    · simp
  have tailLast :
      path.tail.getLast tailNonempty = path.getLast pathNonempty := by
    have optionIdentity : path.tail.getLast? = path.getLast? := by
      obtain ⟨first, tail, pathIdentity⟩ := List.exists_cons_of_ne_nil pathNonempty
      rw [pathIdentity]
      cases tail with
      | nil => exact (tailNonempty (by simp [pathIdentity])).elim
      | cons second rest => rfl
    rw [List.getLast?_eq_some_getLast tailNonempty,
      List.getLast?_eq_some_getLast pathNonempty] at optionIdentity
    exact Option.some.inj optionIdentity
  refine ⟨path.head pathNonempty, path.tail.dropLast,
    path.getLast pathNonempty, ?_, lengthThree, ⟨pathNodup, pathChain⟩, ?_⟩
  · change path = path.head pathNonempty ::
      (path.tail.dropLast ++ [path.getLast pathNonempty])
    calc
      path = path.head pathNonempty :: path.tail :=
        (List.cons_head_tail pathNonempty).symm
      _ = path.head pathNonempty ::
          (path.tail.dropLast ++ [path.getLast pathNonempty]) := by
        rw [← tailLast, List.dropLast_append_getLast tailNonempty]
  · have headIdentity : path.head pathNonempty = start := by
      cases walk with
      | nil => simp at cycle
      | cons adjacent tail => simp [path, List.dropLast_cons_of_ne_nil tail.support_ne_nil]
    simpa [headIdentity] using closing

/-- If a cycle walk is explicitly begun with `left-right`, removing its repeated closing vertex
retains that physical bond as the first consecutive list edge. -/
theorem aromaticCanonicalPathContainsBond_support_dropLast_cons
    (source : AuthoritativeChemicalInput)
    {left right : source.AromaticCanonicalAtom}
    (ordinary : source.AromaticCanonicalOrdinaryDoubleBond left right)
    (tail : source.aromaticCanonicalOrdinaryDoubleSimpleGraph.Walk right left)
    (tailNotNil : ¬ tail.Nil) :
    AromaticCanonicalPathContainsBond
      ((SimpleGraph.Walk.cons ordinary tail).support.dropLast) left right := by
  cases tail with
  | nil => exact (tailNotNil (by simp)).elim
  | cons adjacent rest =>
      exact ⟨[], rest.support.dropLast, Or.inl (by
        simp [List.dropLast_cons_of_ne_nil rest.support_ne_nil])⟩

/-- Every ordinary-double bond in an independently detected degree-two component is witnessed by
the exhaustive cycle enumeration used by the bond router. -/
theorem DeclarativeAromaticCanonicalCyclicCumuleneComponent.cyclic_of_left_mem
    (source : AuthoritativeChemicalInput)
    {component : source.AromaticCanonicalCyclicCumuleneComponent}
    (derived : source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftIn : bond.left ∈ source.aromaticCanonicalOrdinaryDoubleComponentAtoms
      component.representative) :
    source.AromaticCanonicalOrdinaryDoubleBondCyclic bond := by
  classical
  let componentGraph := source.aromaticCanonicalOrdinaryDoubleComponentGraph
    component.representative
  have leftInGraphComponent : bond.left ∈
      (source.aromaticCanonicalOrdinaryDoubleSimpleGraph.connectedComponentMk
        component.representative).supp :=
    (source.mem_aromaticCanonicalOrdinaryDoubleComponentAtoms_iff_mem_component
      component.representative bond.left).mp leftIn
  have componentAdjacent : componentGraph.Adj bond.left bond.right := by
    change
      (source.aromaticCanonicalOrdinaryDoubleSimpleGraph.connectedComponentMk
        component.representative).toSimpleGraph.spanningCoe.Adj bond.left bond.right
    rw [SimpleGraph.ConnectedComponent.adj_spanningCoe_toSimpleGraph]
    exact ⟨leftInGraphComponent, bond.ordinary⟩
  have alternateReachability :=
    (derived.isCycles_componentGraph source).reachable_deleteEdges componentAdjacent
  change (componentGraph \ SimpleGraph.fromEdgeSet {s(bond.left, bond.right)}).Reachable
    bond.left bond.right at alternateReachability
  obtain ⟨detour, targetAbsent⟩ :=
    SimpleGraph.reachable_delete_edges_iff_exists_walk.mp alternateReachability
  let detourPath : componentGraph.Walk bond.left bond.right := detour.toPath
  have targetAbsentPath : s(bond.left, bond.right) ∉ detourPath.edges := by
    intro present
    exact targetAbsent (detour.edges_toPath_subset present)
  have targetAbsentReverse :
      s(bond.left, bond.right) ∉ detourPath.reverse.edges := by
    simpa [SimpleGraph.Walk.edges_reverse] using targetAbsentPath
  have componentCycle :
      (SimpleGraph.Walk.cons componentAdjacent detourPath.reverse).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    exact ⟨detourPath.isPath_reverse_iff.mpr detour.toPath.property,
      targetAbsentReverse⟩
  have componentGraphLe :=
    source.aromaticCanonicalOrdinaryDoubleComponentGraph_le component.representative
  let sourceTail : source.aromaticCanonicalOrdinaryDoubleSimpleGraph.Walk
      bond.right bond.left := detourPath.reverse.mapLe componentGraphLe
  let sourceCycle : source.aromaticCanonicalOrdinaryDoubleSimpleGraph.Walk
      bond.left bond.left := SimpleGraph.Walk.cons bond.ordinary sourceTail
  have sourceCycleValid : sourceCycle.IsCycle := by
    simpa [sourceCycle, sourceTail] using componentCycle.mapLe componentGraphLe
  have sourceTailNotNil : ¬ sourceTail.Nil :=
    SimpleGraph.Walk.not_nil_of_ne bond.ordered.ne'
  refine ⟨sourceCycle.support.dropLast, ?_, ?_⟩
  · rw [source.mem_aromaticCanonicalOrdinaryCumuleneCycles_iff]
    exact source.aromaticCanonicalOrdinaryCumuleneCycle_of_isCycle
      sourceCycle sourceCycleValid
  · simpa [sourceCycle] using
      source.aromaticCanonicalPathContainsBond_support_dropLast_cons
        bond.ordinary sourceTail sourceTailNotNil

/-- Thus the independently detected P-31 component and the existing bond router agree on every
bond of that component: it is nonbranched and cyclic. -/
theorem DeclarativeAromaticCanonicalCyclicCumuleneComponent.bond_router_conformance
    (source : AuthoritativeChemicalInput)
    {component : source.AromaticCanonicalCyclicCumuleneComponent}
    (derived : source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftIn : bond.left ∈ source.aromaticCanonicalOrdinaryDoubleComponentAtoms
      component.representative) :
    ¬ source.AromaticCanonicalOrdinaryDoubleBondBranched bond ∧
      source.AromaticCanonicalOrdinaryDoubleBondCyclic bond :=
  ⟨derived.not_branched_of_left_mem source bond leftIn,
    derived.cyclic_of_left_mem source bond leftIn⟩

/-- Equivalently, every bond of the component occurs in the public cyclic-cumulene bond carrier
list exactly selected by the older router. -/
theorem DeclarativeAromaticCanonicalCyclicCumuleneComponent.mem_cyclicBondCarriers_of_left_mem
    (source : AuthoritativeChemicalInput)
    {component : source.AromaticCanonicalCyclicCumuleneComponent}
    (derived : source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftIn : bond.left ∈ source.aromaticCanonicalOrdinaryDoubleComponentAtoms
      component.representative) :
    bond ∈ source.aromaticCanonicalCyclicCumuleneBondCarriers := by
  rw [source.mem_aromaticCanonicalCyclicCumuleneBondCarriers_iff]
  exact derived.bond_router_conformance source bond leftIn

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
