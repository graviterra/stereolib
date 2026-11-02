import TetraStereo.OneCenter.OfficialHierarchicalDigraph

set_option autoImplicit false

namespace TetraStereo
namespace Examples
namespace OfficialHierarchicalDigraph

open OneCenter

/-- Multiple-bond child copies carry explicit official duplicate-node provenance. -/
example {V : Type*} [DecidableEq V] (node : OfficialCIPNode V) (next : V) :
    node.childProvenance next 1 =
      OfficialCIPNodeProvenance.multipleBondDuplicate node.depth := by
  simp [OfficialCIPNode.childProvenance]

/-- A zero-copy child that has already occurred on the branch is a ring/cycle duplicate. -/
example {V : Type*} [DecidableEq V] (node : OfficialCIPNode V) {next : V}
    (h : next ∈ node.history) :
    node.childProvenance next 0 =
      OfficialCIPNodeProvenance.ringDuplicate (node.duplicateRootDistance next) := by
  simpa using OfficialCIPNode.childProvenance_ring_duplicate node next h

/-- Closer duplicate roots have higher Rule-1b priority. -/
example :
    MoleculeGraph.compareCloserRootDistance 0 2 = Ordering.gt := by
  exact MoleculeGraph.compareCloserRootDistance_eq_gt_of_lt (by decide)

/-- Placeholder and lone-pair nodes are explicit leaves in the current official digraph layer. -/
example {V : Type*} [Fintype V] [DecidableEq V] (m : MoleculeGraph V) :
    m.officialCIPChildren (OfficialCIPNode.placeholder OfficialPhantomNodeKind.lonePair 0) = [] := by
  rfl

/-- Auxiliary descriptor nodes are explicit virtual leaves too. -/
example {V : Type*} [Fintype V] [DecidableEq V] (m : MoleculeGraph V) :
    m.officialCIPChildren (OfficialCIPNode.auxiliary (V := V) 1) = [] := by
  rfl

/-- A frontier made only of duplicate leaves is terminal. -/
example {V : Type*} [Fintype V] [DecidableEq V] (m : MoleculeGraph V)
    (frontier : List (OfficialCIPNode V))
    (hdup : ∀ node, node ∈ frontier → node.isDuplicateLeaf = true) :
    m.OfficialTerminalFrontier frontier := by
  exact m.officialTerminalFrontier_of_duplicateLeaves hdup

/-- Terminal frontiers make additional hierarchical-digraph fuel irrelevant. -/
example {V : Type*} [Fintype V] [DecidableEq V] (m : MoleculeGraph V)
    (left right : List (OfficialCIPNode V))
    (hleft : m.OfficialTerminalFrontier left) (hright : m.OfficialTerminalFrontier right)
    (extra : ℕ) :
    m.compareOfficialHierarchicalDigraphTrace (1 + extra) left right =
      m.compareOfficialLayerTrace left right := by
  exact m.compareOfficialHierarchicalDigraphTrace_eq_layer_of_terminalFrontiers
    hleft hright extra

/-- Ordinary ligand-root branches exhaust by the default finite atom-cardinality fuel. -/
example {V : Type*} [Fintype V] [DecidableEq V] (m : MoleculeGraph V)
    {center ligand : V} (hligand : ligand ≠ center) :
    m.officialCIPFrontier (Fintype.card V + 1)
      [OfficialCIPNode.rootFromEdge center ligand] = [] := by
  exact m.officialCIPFrontier_rootFromEdge_eq_nil_card_add_one hligand

/-- For ordinary ligand-root branches, additional fuel beyond the default cannot change the trace. -/
example {V : Type*} [Fintype V] [DecidableEq V] (m : MoleculeGraph V)
    {center left right : V} (hleft : left ≠ center) (hright : right ≠ center)
    (extra : ℕ) :
    m.compareOfficialHierarchicalDigraphTrace ((Fintype.card V + 1) + extra)
      [OfficialCIPNode.rootFromEdge center left] [OfficialCIPNode.rootFromEdge center right] =
        m.compareOfficialHierarchicalDigraphTrace (Fintype.card V + 1)
          [OfficialCIPNode.rootFromEdge center left]
          [OfficialCIPNode.rootFromEdge center right] := by
  exact m.compareOfficialHierarchicalDigraphTrace_rootFromEdge_stable_default
    hleft hright extra

/-- If the hierarchical digraph itself ties, the new bridge falls through to official context
rules just like the older key-based comparator. -/
example :
    (CIPRuleEngine.compareDigraphThenOfficialCertificate []
      (CIPRuleEngine.OfficialLigandRuleContext.ofRS RS.R)
      (CIPRuleEngine.OfficialLigandRuleContext.ofRS RS.S)).outcome = Ordering.gt := by
  rfl

end OfficialHierarchicalDigraph
end Examples
end TetraStereo
