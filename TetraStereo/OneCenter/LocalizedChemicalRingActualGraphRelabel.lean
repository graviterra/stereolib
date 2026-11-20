import TetraStereo.OneCenter.LocalizedChemicalRingSourceGraphTransport
import TetraStereo.OneCenter.LocalizedRetainedCursorTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-! The erased graphs of actual retained occurrence expansions transport under a molecular
automorphism. Their sibling lists may differ in order and their readers may differ arbitrarily.
The graph relabelling is derived from actual child enumeration and recursive realization. -/

namespace TetraStereo.OneCenter.LocalizedChemicalRingActualGraphRelabel

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree LocalizedChemicalRingSourceGraphTransport

variable {input : CertifiedLocalizedCIPInput} {fuel : Nat}

theorem realized_graph_relabel (single : input.moleculeGraph.SimpleBonded)
    (e : input.moleculeGraph.Aut)
    {readL readR : input.LocalizedRerootCursor fuel → Option LocalizedAuxiliaryLabel}
    {left : LocalizedCumulativeDecoratedTree input fuel}
    (realL : LocalizedCumulativeTreeRealizes input readL left) :
    ∀ {right : LocalizedCumulativeDecoratedTree input fuel},
      LocalizedCumulativeTreeRealizes input readR right →
      input.transportCursor single e left.source = right.source →
      input.cursorPreviousRootAligned left.source →
      Nonempty (RootedDigraph.Relabel (e : Equiv.Perm input.Atom)
        (ruleMajorTreeGraph left) (ruleMajorTreeGraph right)) := by
  induction realL with
  | mk cursor children trees computed sources realized ih =>
      intro right realR same aligned
      cases realR with
      | mk cursorR childrenR treesR computedR sourcesR realizedR =>
          have sameCursor : input.transportCursor single e cursor = cursorR := same
          have alignedCursor : input.cursorPreviousRootAligned cursor := aligned
          have hc : children = input.executableLocalizedRerootChildren cursor :=
            Option.some.inj (computed.symm.trans
              ((input.executableLocalizedRerootChildren?_eq_localizedRerootChildren cursor).symm.trans
              (input.executableLocalizedRerootChildren?_eq_some cursor)))
          have hcR : childrenR = input.executableLocalizedRerootChildren cursorR :=
            Option.some.inj (computedR.symm.trans
              ((input.executableLocalizedRerootChildren?_eq_localizedRerootChildren cursorR).symm.trans
              (input.executableLocalizedRerootChildren?_eq_some cursorR)))
          have childPerm : (children.map (input.transportCursor single e)).Perm childrenR := by
            rw [hc, hcR, ← sameCursor]
            exact input.executableLocalizedRerootChildren_transport_perm single e alignedCursor
          have sourcePerm : (trees.map fun t => input.transportCursor single e t.source).Perm
              (treesR.map fun t => t.source) := by
            simpa only [List.map_map, Function.comp_def] using
              ((sources.map (input.transportCursor single e)).trans childPerm).trans sourcesR.symm
          obtain ⟨slots0, slotEq⟩ := sourceTreeIndexEquiv_of_perm sourcePerm
          let castL : Fin trees.length ≃ Fin (trees.map fun t => input.transportCursor single e t.source).length :=
            finCongr (List.length_map _).symm
          let castR : Fin (treesR.map fun t => t.source).length ≃ Fin treesR.length :=
            finCongr (List.length_map _)
          let slots : Fin trees.length ≃ Fin treesR.length := (castL.trans slots0).trans castR
          have slotSources : ∀ i : Fin trees.length,
              input.transportCursor single e (trees.get i).source = (treesR.get (slots i)).source := by
            intro i
            simpa [slots, castL, castR, List.get_eq_getElem] using slotEq (castL i)
          have childRel : ∀ i : Fin trees.length,
              RootedDigraph.Relabel (e : Equiv.Perm input.Atom)
                (ruleMajorTreeGraph (trees.get i)) (ruleMajorTreeGraph (treesR.get (slots i))) := by
            intro i
            have member := List.get_mem trees i
            have actual : (trees.get i).source ∈ input.executableLocalizedRerootChildren cursor := by
              rw [← hc]
              exact sources.subset (List.mem_map_of_mem member)
            exact Classical.choice (ih (trees.get i) member
              (realizedR _ (List.get_mem treesR (slots i))) (slotSources i)
              (input.executableLocalizedRerootChildren_cursorAligned cursor _ actual))
          let offL := trees.map toOfficialSourceTree
          let offR := treesR.map toOfficialSourceTree
          let offCastL : Fin offL.length ≃ Fin trees.length := finCongr (List.length_map _)
          let offCastR : Fin treesR.length ≃ Fin offR.length := finCongr (List.length_map _).symm
          let offSlots := (offCastL.trans slots).trans offCastR
          have childrenRel : ∀ i : Fin offL.length,
              RootedDigraph.Relabel (e : Equiv.Perm input.Atom) (offL.get i).toDeclarativeDigraph
                (offR.get (offSlots i)).toDeclarativeDigraph := by
            intro i
            simpa [offL, offR, offSlots, offCastL, offCastR, ruleMajorTreeGraph,
              List.get_eq_getElem] using childRel (offCastL i)
          have rel := nodeRelabel (e : Equiv.Perm input.Atom) cursor.occurrence.1.node
            offL offR offSlots childrenRel
          have nodeEq : mapOfficialNode (e : Equiv.Perm input.Atom) cursor.occurrence.1.node =
              cursorR.occurrence.1.node := by
            rw [← sameCursor, transportCursor_occurrence, transportOccurrence_node]
          rw [nodeEq] at rel
          exact ⟨by simpa [ruleMajorTreeGraph, toOfficialSourceTree_localizedRootTree,
            toOfficialSourceTreeList_eq_map, offL, offR] using rel⟩

end TetraStereo.OneCenter.LocalizedChemicalRingActualGraphRelabel

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualGraphRelabel.realized_graph_relabel
