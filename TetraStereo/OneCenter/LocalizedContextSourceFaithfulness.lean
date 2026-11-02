import TetraStereo.OneCenter.LocalizedRuleMajorCanonicalBridge
import TetraStereo.OneCenter.LocalizedRealizedTreeCutEquivalence
import TetraStereo.OneCenter.LocalizedOuterRootPhysicalPriority
import TetraStereo.OneCenter.DeclarativeCIPFaithfulExpansionBisimulation
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-!
# Faithfulness of actual context source graphs

This module connects an actual localized context tree to its physical incoming-cut branch.  The
context's retained outer-root observer is deliberately separate from the raw declarative labels:
under the simple-bonded acyclic carrier invariant, every represented source node has real-atom
provenance, and `NodeLabel` has no distance field.
-/

namespace TetraStereo.OneCenter

open DeclarativeCIP
open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree
open Rule4aTableBridge

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

private theorem decoratedLookup_isSome_iff
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (address : List Nat) :
    (subtreeAt? tree address).isSome = true ↔
      ∃ subtree, tree.decoratedSubtreeAt? address = some subtree := by
  induction address generalizing tree with
  | nil => simp [subtreeAt?, decoratedSubtreeAt?]
  | cons slot rest ih =>
      cases hchild : tree.children[slot]? with
      | none => simp [subtreeAt?, decoratedSubtreeAt?, hchild]
      | some child => simpa [subtreeAt?, decoratedSubtreeAt?, hchild] using ih child

private theorem subtreeAt_eq_decoratedSubtreeAt
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (address : List Nat) :
    subtreeAt? tree address = tree.decoratedSubtreeAt? address := by
  induction address generalizing tree with
  | nil => rfl
  | cons slot rest ih =>
      cases hchild : tree.children[slot]? <;>
        simp [subtreeAt?, decoratedSubtreeAt?, hchild, ih]

private theorem ruleMajorGraph_depth_lt_of_transGen
    {graph : RootedDigraph input.Atom} {first last : graph.Node}
    (path : Relation.TransGen graph.child first last) : graph.depth first < graph.depth last := by
  induction path with
  | single edge => rw [graph.child_depth edge]; omega
  | tail _ edge ih =>
      exact Nat.lt_trans ih (by rw [graph.child_depth edge]; exact Nat.lt_succ_self _)

/-- The hierarchy-address nodes of the erased source graph and the actual decorated positions
are the same finite carrier, with the address unchanged.  This is the bridge needed to transport
the physical position/cut-branch equivalence to the `RootedDigraph` consumed by the independent
semantics. -/
noncomputable def ruleMajorGraphPositionEquiv
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    (ruleMajorTreeGraph tree).Node ≃ Position tree := by
  classical
  refine Equiv.ofBijective (fun node => ⟨node.1, ?_⟩) ?_
  · obtain ⟨sourceTree, lookup, _sourceAt⟩ :=
      (toOfficialSourceTree tree).exists_source_lookup node
    have erased := toOfficialSourceTree_subtreeAt? tree node.1
    rw [lookup] at erased
    cases hdecorated : tree.decoratedSubtreeAt? node.1 with
    | none => simp [hdecorated] at erased
    | some subtree =>
        have sourceEq : sourceTree = toOfficialSourceTree subtree := by
          simpa [hdecorated] using erased
        subst sourceTree
        exact (decoratedLookup_isSome_iff tree node.1).2 ⟨subtree, hdecorated⟩
  · constructor
    · intro p q hpq
      apply Subtype.ext
      exact congrArg (fun x : Position tree => x.1) hpq
    · intro p
      obtain ⟨subtree, lookup⟩ := (decoratedLookup_isSome_iff tree p.1).1 p.2
      have erased : (toOfficialSourceTree tree).subtreeAt? p.1 =
          some (toOfficialSourceTree subtree) := by
        rw [toOfficialSourceTree_subtreeAt?, lookup]
        rfl
      have occurrence := OfficialCIPSourceTree.mem_occurrences_of_subtreeAt?_eq_some
          p.1 (toOfficialSourceTree tree) (toOfficialSourceTree subtree) erased
      have present :=
        OfficialCIPSourceTree.mem_hierarchyAddresses_of_occurrence
          (toOfficialSourceTree tree)
          (p.1, (toOfficialSourceTree subtree).source) occurrence
      refine ⟨⟨p.1, present⟩, ?_⟩
      apply Subtype.ext
      rfl

/-- Every node label in an actual context source graph is the real atom observed at the matching
decorated position.  No Rule-1b payload is present in these labels. -/
theorem ruleMajorGraphPositionEquiv_label
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (node : (ruleMajorTreeGraph tree).Node) :
    (ruleMajorTreeGraph tree).label node =
      ⟨some (nodeAtom singleBonded acyclic (positionNode
        (ruleMajorGraphPositionEquiv tree node))), .realAtom⟩ := by
  let p := ruleMajorGraphPositionEquiv tree node
  obtain ⟨subtree, lookup⟩ :=
    (decoratedLookup_isSome_iff tree node.1).1 p.property
  have sourceLookup : (toOfficialSourceTree tree).subtreeAt? node.1 =
      some (toOfficialSourceTree subtree) := by
    rw [toOfficialSourceTree_subtreeAt?, lookup]
    rfl
  have labelEq := OfficialCIPSourceTree.declarativeLabel_eq_of_subtreeAt?
    (toOfficialSourceTree tree) (toOfficialSourceTree subtree) node sourceLookup
  have sourceReal : subtree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom :=
    input.carrierOccurrence_provenance_real singleBonded acyclic subtree.source.occurrence
  have atomEq : subtree.source.occurrence.1.node.current? =
      some (nodeAtom singleBonded acyclic subtree) := nodeAtom_spec singleBonded acyclic subtree
  have graphNodeEq : positionNode p = subtree := by
    have h := positionNode_spec p
    have addressEq : p.1 = node.1 := rfl
    rw [addressEq, subtreeAt_eq_decoratedSubtreeAt, lookup] at h
    exact (Option.some.inj h).symm
  change (toOfficialSourceTree tree).declarativeLabel node = _
  rw [labelEq]
  rw [graphNodeEq]
  rw [toOfficialSourceTree_source]
  change ⟨subtree.source.occurrence.1.node.current?,
      subtree.source.occurrence.1.node.provenance.toDeclarative⟩ =
    (⟨some (nodeAtom singleBonded acyclic subtree), .realAtom⟩ : NodeLabel input.Atom)
  rw [atomEq, sourceReal]
  rfl

@[simp] theorem ruleMajorGraphPositionEquiv_root
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    ruleMajorGraphPositionEquiv tree (ruleMajorTreeGraph tree).root = rootPosition tree := by
  apply Subtype.ext
  rfl

/-- The actual erased graph nodes map bijectively to the atoms on the incoming cut branch. -/
noncomputable def ruleMajorGraphCutBranchEquiv
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {currentAtom previousAtom : input.Atom}
    (currentObserved : tree.source.occurrence.1.node.current? = some currentAtom)
    (previousObserved : previous.1.node.current? = some previousAtom)
    (incomingEdge : input.moleculeGraph.Adj previousAtom currentAtom) :
    (ruleMajorTreeGraph tree).Node ≃
      AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph previousAtom currentAtom :=
  (ruleMajorGraphPositionEquiv tree).trans
    (positionCutEquiv singleBonded acyclic enough realizes previous previousEq valid sameRoot
      currentObserved previousObserved incomingEdge)

@[simp] theorem ruleMajorGraphCutBranchEquiv_apply_atom
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {currentAtom previousAtom : input.Atom}
    (currentObserved : tree.source.occurrence.1.node.current? = some currentAtom)
    (previousObserved : previous.1.node.current? = some previousAtom)
    (incomingEdge : input.moleculeGraph.Adj previousAtom currentAtom)
    (node : (ruleMajorTreeGraph tree).Node) :
    ((ruleMajorGraphCutBranchEquiv singleBonded acyclic enough realizes previous previousEq
        valid sameRoot currentObserved previousObserved incomingEdge node :
          AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph previousAtom currentAtom) :
        input.Atom) =
      nodeAtom singleBonded acyclic
        (positionNode (ruleMajorGraphPositionEquiv tree node)) := rfl

/-- Actual source graphs satisfy the local expansion clauses at their physical incoming edge.
This supplies the root label, atom-bearing children, terminal behavior, and bond adjacency without
any key-table equality or source-root normalization assumption. -/
theorem ruleMajorTreeGraph_locallyAdmissibleExpansion
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {currentAtom previousAtom : input.Atom}
    (currentObserved : tree.source.occurrence.1.node.current? = some currentAtom)
    (previousObserved : previous.1.node.current? = some previousAtom)
    (incomingEdge : input.moleculeGraph.Adj previousAtom currentAtom) :
    RootedDigraph.LocallyAdmissibleExpansion input.moleculeGraph currentAtom
      (ruleMajorTreeGraph tree) := by
  let graph := ruleMajorTreeGraph tree
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hroot := ruleMajorGraphPositionEquiv_label singleBonded acyclic graph.root
    rw [ruleMajorGraphPositionEquiv_root] at hroot
    have rootAtom : nodeAtom singleBonded acyclic tree = currentAtom :=
      nodeAtom_eq_of_observed singleBonded acyclic currentObserved
    simpa [graph, rootAtom] using hroot
  · intro node
    rw [ruleMajorGraphPositionEquiv_label singleBonded acyclic node]
    simp [RootedDigraph.LabelCompatible]
  · intro node terminal child childEdge
    rw [ruleMajorGraphPositionEquiv_label singleBonded acyclic node] at terminal
    simp [RootedDigraph.ProvenanceTerminal] at terminal
  · intro parent child parentAtom childAtom childEdge parentLabel childLabel
    have parentLabel' := ruleMajorGraphPositionEquiv_label singleBonded acyclic parent
    have childLabel' := ruleMajorGraphPositionEquiv_label singleBonded acyclic child
    rw [parentLabel'] at parentLabel
    rw [childLabel'] at childLabel
    have parentPhysical :
        nodeAtom singleBonded acyclic (positionNode (ruleMajorGraphPositionEquiv tree parent)) =
          parentAtom := Option.some.inj parentLabel
    have childPhysical :
        nodeAtom singleBonded acyclic (positionNode (ruleMajorGraphPositionEquiv tree child)) =
          childAtom := Option.some.inj childLabel
    have childAddress : ∃ slot,
        child.1 = parent.1 ++ [slot] := by
      exact childEdge
    rcases childAddress with ⟨slot, addressEq⟩
    have positionAdjacent : PositionAdjacent (ruleMajorGraphPositionEquiv tree parent)
        (ruleMajorGraphPositionEquiv tree child) := by
      exact Or.inl ⟨slot, addressEq⟩
    have adjacent := (positionCutEquiv_adj_iff singleBonded acyclic
      enough
      realizes previous previousEq valid sameRoot currentObserved previousObserved incomingEdge
      (ruleMajorGraphPositionEquiv tree parent) (ruleMajorGraphPositionEquiv tree child)).2
        positionAdjacent
    simpa [positionAtom, parentPhysical, childPhysical] using adjacent

private theorem ruleMajorTreeGraph_child_not_suppressed
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {currentAtom previousAtom atom : input.Atom}
    (currentObserved : tree.source.occurrence.1.node.current? = some currentAtom)
    (previousObserved : previous.1.node.current? = some previousAtom)
    (incomingEdge : input.moleculeGraph.Adj previousAtom currentAtom)
    {parent child : (ruleMajorTreeGraph tree).Node}
    (childEdge : (ruleMajorTreeGraph tree).child parent child)
    (childLabel : ((ruleMajorTreeGraph tree).label child).atom? = some atom) :
    ¬ RootedDigraph.SuppressedParentAtom (ruleMajorTreeGraph tree) previousAtom atom parent := by
  intro suppressed
  let cutEquiv := ruleMajorGraphCutBranchEquiv singleBonded acyclic enough realizes previous
    previousEq valid sameRoot currentObserved previousObserved incomingEdge
  have childCut : (cutEquiv child : input.Atom) = atom := by
    rw [ruleMajorGraphCutBranchEquiv_apply_atom]
    have raw := ruleMajorGraphPositionEquiv_label singleBonded acyclic child
    rw [raw] at childLabel
    exact Option.some.inj childLabel
  rcases suppressed with ⟨_parentRoot, atomExternal⟩ | ⟨ancestor, ancestorChild, ancestorLabel⟩
  · have childInCut : (cutEquiv child).val ∈
        AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph previousAtom currentAtom :=
      (cutEquiv child).property
    have externalNotCut := AcyclicCutBranchAutomorphism.center_not_mem_cutBranch
      input.moleculeGraph previousAtom currentAtom
    exact externalNotCut (by simpa [childCut, atomExternal] using childInCut)
  · have ancestorCut : (cutEquiv ancestor : input.Atom) = atom := by
      rw [ruleMajorGraphCutBranchEquiv_apply_atom]
      have raw := ruleMajorGraphPositionEquiv_label singleBonded acyclic ancestor
      rw [raw] at ancestorLabel
      exact Option.some.inj ancestorLabel
    have sameNode : child = ancestor := by
      apply cutEquiv.injective
      apply Subtype.ext
      exact childCut.trans ancestorCut.symm
    obtain ⟨childSlot, childAddress⟩ := childEdge
    obtain ⟨ancestorSlot, ancestorAddress⟩ := ancestorChild
    have address := congrArg Subtype.val sameNode
    change child.1 = ancestor.1 at address
    rw [childAddress, ancestorAddress] at address
    simp at address

private theorem ruleMajorTreeGraph_childAtomCount_eq_if
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {currentAtom previousAtom : input.Atom}
    (currentObserved : tree.source.occurrence.1.node.current? = some currentAtom)
    (previousObserved : previous.1.node.current? = some previousAtom)
    (incomingEdge : input.moleculeGraph.Adj previousAtom currentAtom)
    {parent : (ruleMajorTreeGraph tree).Node} (parentAtom atom : input.Atom)
    (parentLabel : ((ruleMajorTreeGraph tree).label parent).atom? = some parentAtom) :
    RootedDigraph.ChildAtomCount (ruleMajorTreeGraph tree) parent atom =
      @ite Nat
        (input.moleculeGraph.Adj parentAtom atom ∧
          ¬ RootedDigraph.SuppressedParentAtom (ruleMajorTreeGraph tree) previousAtom atom parent)
        (Classical.propDecidable _ ) 1 0 := by
  classical
  let graph := ruleMajorTreeGraph tree
  let cutEquiv := ruleMajorGraphCutBranchEquiv singleBonded acyclic enough realizes previous
    previousEq valid sameRoot currentObserved previousObserved incomingEdge
  have parentPhysical :
      nodeAtom singleBonded acyclic (positionNode (ruleMajorGraphPositionEquiv tree parent)) =
        parentAtom := by
    have raw := ruleMajorGraphPositionEquiv_label singleBonded acyclic parent
    rw [raw] at parentLabel
    exact Option.some.inj parentLabel
  have mapAtom : ∀ node : graph.Node,
      (graph.label node).atom? = some atom → (cutEquiv node : input.Atom) = atom := by
    intro node nodeLabel
    have raw := ruleMajorGraphPositionEquiv_label singleBonded acyclic node
    rw [raw] at nodeLabel
    rw [ruleMajorGraphCutBranchEquiv_apply_atom]
    exact Option.some.inj nodeLabel
  have localFacts := ruleMajorTreeGraph_locallyAdmissibleExpansion singleBonded acyclic enough
    realizes previous previousEq valid sameRoot currentObserved previousObserved incomingEdge
  by_cases hcondition : input.moleculeGraph.Adj parentAtom atom ∧
      ¬ RootedDigraph.SuppressedParentAtom graph previousAtom atom parent
  · rcases hcondition with ⟨adjacent, notSuppressed⟩
    have parentCut : (cutEquiv parent : input.Atom) = parentAtom := by
      rw [ruleMajorGraphCutBranchEquiv_apply_atom]
      exact parentPhysical
    have parentMem : parentAtom ∈
        AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph previousAtom currentAtom := by
      simpa [parentCut] using (cutEquiv parent).property
    have incidence := AcyclicCutBranchAutomorphism.cutBranch_incidence
      input.moleculeGraph acyclic incomingEdge parentMem atom adjacent
    have atomMem : atom ∈
        AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph previousAtom currentAtom := by
      rcases incidence with mem | ⟨parentIsCurrent, atomIsPrevious⟩
      · exact mem
      · have rootCut :
            (cutEquiv graph.root : input.Atom) = currentAtom := by
          rw [ruleMajorGraphCutBranchEquiv_apply_atom, ruleMajorGraphPositionEquiv_root,
            positionNode_rootPosition]
          exact nodeAtom_eq_of_observed singleBonded acyclic currentObserved
        have parentEqRoot : parent = graph.root := by
          apply cutEquiv.injective
          apply Subtype.ext
          rw [parentCut, rootCut, parentIsCurrent]
        exact False.elim (notSuppressed (Or.inl ⟨parentEqRoot, atomIsPrevious⟩))
    let childNode := cutEquiv.symm ⟨atom, atomMem⟩
    have childCutEq := Equiv.apply_symm_apply cutEquiv ⟨atom, atomMem⟩
    have childPhysical :
        nodeAtom singleBonded acyclic
          (positionNode (ruleMajorGraphPositionEquiv tree childNode)) = atom := by
      have h : (cutEquiv childNode : input.Atom) = atom := by
        simpa only [childNode] using congrArg Subtype.val childCutEq
      rw [ruleMajorGraphCutBranchEquiv_apply_atom] at h
      exact h
    have positionAdjacent := (positionCutEquiv_adj_iff singleBonded acyclic enough
      realizes previous previousEq valid sameRoot currentObserved previousObserved incomingEdge
      (ruleMajorGraphPositionEquiv tree parent)
      (ruleMajorGraphPositionEquiv tree childNode)).1 (by
        simpa [positionAtom, parentPhysical, childPhysical] using adjacent)
    have childEdge : graph.child parent childNode := by
      rcases positionAdjacent with ⟨slot, childAddress⟩ | ⟨slot, parentAddress⟩
      · change ∃ slot, childNode.1 = parent.1 ++ [slot]
        exact ⟨slot, childAddress⟩
      · have parentOfParent : graph.child childNode parent := by
          change ∃ slot, parent.1 = childNode.1 ++ [slot]
          exact ⟨slot, parentAddress⟩
        have childLabel : (graph.label childNode).atom? = some atom := by
          rw [ruleMajorGraphPositionEquiv_label singleBonded acyclic childNode]
          simp [childPhysical]
        exact False.elim (notSuppressed (Or.inr ⟨childNode, parentOfParent, childLabel⟩))
    have childLabel : (graph.label childNode).atom? = some atom := by
      rw [ruleMajorGraphPositionEquiv_label singleBonded acyclic childNode]
      simp [childPhysical]
    let fiber := {node : graph.Node // graph.child parent node ∧
      (graph.label node).atom? = some atom}
    have fiberSubsingleton : Subsingleton fiber := by
      constructor
      intro left right
      apply Subtype.ext
      apply cutEquiv.injective
      apply Subtype.ext
      exact (mapAtom left.1 left.2.2).trans (mapAtom right.1 right.2.2).symm
    have fiberNonempty : Nonempty fiber := ⟨⟨childNode, childEdge, childLabel⟩⟩
    unfold RootedDigraph.ChildAtomCount RootedDigraph.ChildCountWhere
    have hcond : input.moleculeGraph.Adj parentAtom atom ∧
        ¬ RootedDigraph.SuppressedParentAtom graph previousAtom atom parent :=
      ⟨adjacent, notSuppressed⟩
    change Nat.card fiber = @ite Nat
      (input.moleculeGraph.Adj parentAtom atom ∧
        ¬ RootedDigraph.SuppressedParentAtom graph previousAtom atom parent)
      (Classical.propDecidable _) 1 0
    rw [if_pos hcond]
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨fiberSubsingleton, fiberNonempty⟩
  · unfold RootedDigraph.ChildAtomCount RootedDigraph.ChildCountWhere
    change Nat.card {node : graph.Node // graph.child parent node ∧
      (graph.label node).atom? = some atom} = @ite Nat
      (input.moleculeGraph.Adj parentAtom atom ∧
        ¬ RootedDigraph.SuppressedParentAtom graph previousAtom atom parent)
      (Classical.propDecidable _) 1 0
    rw [if_neg hcondition]
    rw [Nat.card_eq_zero]
    left
    refine ⟨?_⟩
    intro entry
    rcases entry with ⟨childNode, childEdge, childLabel⟩
    have adjacent : input.moleculeGraph.Adj parentAtom atom :=
      localFacts.2.2.2 parent childNode parentAtom atom childEdge parentLabel childLabel
    have notSuppressed := ruleMajorTreeGraph_child_not_suppressed singleBonded acyclic enough
      realizes previous previousEq valid sameRoot currentObserved previousObserved incomingEdge
      childEdge childLabel
    exact hcondition ⟨adjacent, notSuppressed⟩

private theorem ruleMajorTreeGraph_branchAncestor_suppressed
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {currentAtom previousAtom : input.Atom}
    (currentObserved : tree.source.occurrence.1.node.current? = some currentAtom)
    (previousObserved : previous.1.node.current? = some previousAtom)
    (incomingEdge : input.moleculeGraph.Adj previousAtom currentAtom)
    {parent : (ruleMajorTreeGraph tree).Node} (parentAtom atom : input.Atom)
    (parentLabel : ((ruleMajorTreeGraph tree).label parent).atom? = some parentAtom)
    (adjacent : input.moleculeGraph.Adj parentAtom atom)
    (ancestor : RootedDigraph.BranchAncestorAtom (ruleMajorTreeGraph tree)
      previousAtom atom parent) :
    RootedDigraph.SuppressedParentAtom (ruleMajorTreeGraph tree) previousAtom atom parent := by
  classical
  let graph := ruleMajorTreeGraph tree
  let cutEquiv := ruleMajorGraphCutBranchEquiv singleBonded acyclic enough realizes previous
    previousEq valid sameRoot currentObserved previousObserved incomingEdge
  have parentPhysical : nodeAtom singleBonded acyclic
      (positionNode (ruleMajorGraphPositionEquiv tree parent)) = parentAtom := by
    have raw := ruleMajorGraphPositionEquiv_label singleBonded acyclic parent
    rw [raw] at parentLabel
    exact Option.some.inj parentLabel
  have mapAtom : ∀ node : graph.Node,
      (graph.label node).atom? = some atom → (cutEquiv node : input.Atom) = atom := by
    intro node hlabel
    have raw := ruleMajorGraphPositionEquiv_label singleBonded acyclic node
    rw [raw] at hlabel
    rw [ruleMajorGraphCutBranchEquiv_apply_atom]
    exact Option.some.inj hlabel
  have parentCut : (cutEquiv parent : input.Atom) = parentAtom := by
    rw [ruleMajorGraphCutBranchEquiv_apply_atom]
    exact parentPhysical
  have parentMem : parentAtom ∈
      AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph previousAtom currentAtom := by
    simpa [parentCut] using (cutEquiv parent).property
  rcases ancestor with external | ⟨ancestorNode, ancestorPath, ancestorLabel⟩
  · subst atom
    have parentIsCurrent :=
      (AcyclicCutBranchAutomorphism.cutBranch_adj_center_iff input.moleculeGraph acyclic
        incomingEdge parentMem).mp adjacent
    have rootCut : (cutEquiv graph.root : input.Atom) = currentAtom := by
      rw [ruleMajorGraphCutBranchEquiv_apply_atom, ruleMajorGraphPositionEquiv_root,
        positionNode_rootPosition]
      exact nodeAtom_eq_of_observed singleBonded acyclic currentObserved
    have parentEqRoot : parent = graph.root := by
      apply cutEquiv.injective
      apply Subtype.ext
      rw [parentCut, rootCut, parentIsCurrent]
    exact Or.inl ⟨parentEqRoot, rfl⟩
  · have ancestorPhysical : nodeAtom singleBonded acyclic
        (positionNode (ruleMajorGraphPositionEquiv tree ancestorNode)) = atom := by
      have raw := ruleMajorGraphPositionEquiv_label singleBonded acyclic ancestorNode
      rw [raw] at ancestorLabel
      exact Option.some.inj ancestorLabel
    have ancestorCut : (cutEquiv ancestorNode : input.Atom) = atom := by
      rw [ruleMajorGraphCutBranchEquiv_apply_atom]
      exact ancestorPhysical
    have posAdjacent := (positionCutEquiv_adj_iff singleBonded acyclic enough realizes previous
      previousEq valid sameRoot currentObserved previousObserved incomingEdge
      (ruleMajorGraphPositionEquiv tree parent)
      (ruleMajorGraphPositionEquiv tree ancestorNode)).1 (by
        simpa [positionAtom, parentPhysical, ancestorPhysical] using adjacent)
    have depthLt : graph.depth ancestorNode < graph.depth parent :=
      ruleMajorGraph_depth_lt_of_transGen ancestorPath
    have addressLt :
        (ruleMajorGraphPositionEquiv tree ancestorNode).1.length <
          (ruleMajorGraphPositionEquiv tree parent).1.length := by
      simpa [graph, ruleMajorGraphPositionEquiv] using depthLt
    rcases posAdjacent with ⟨slot, ancestorAddress⟩ | ⟨slot, parentAddress⟩
    · have bad := congrArg List.length ancestorAddress
      simp at bad
      omega
    · have childRelation : graph.child ancestorNode parent := by
        change ∃ slot, parent.1 = ancestorNode.1 ++ [slot]
        exact ⟨slot, parentAddress⟩
      exact Or.inr ⟨ancestorNode, childRelation, ancestorLabel⟩

/-- The actual decorated tree graph is a faithful exact expansion of its incoming physical cut.
The source cursor may point toward or away from the original carrier root: all hypotheses concern
only the actual predecessor edge, the retained root equality, realization, and carrier validity. -/
theorem ruleMajorTreeGraph_faithfulExactExpansion
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {currentAtom previousAtom : input.Atom}
    (currentObserved : tree.source.occurrence.1.node.current? = some currentAtom)
    (previousObserved : previous.1.node.current? = some previousAtom)
    (incomingEdge : input.moleculeGraph.Adj previousAtom currentAtom) :
    RootedDigraph.FaithfulExactExpansion input.moleculeGraph previousAtom currentAtom
      (ruleMajorTreeGraph tree) := by
  classical
  let graph := ruleMajorTreeGraph tree
  let cutEquiv := ruleMajorGraphCutBranchEquiv singleBonded acyclic enough realizes previous
    previousEq valid sameRoot currentObserved previousObserved incomingEdge
  have localFacts := ruleMajorTreeGraph_locallyAdmissibleExpansion singleBonded acyclic enough
    realizes previous previousEq valid sameRoot currentObserved previousObserved incomingEdge
  have allReal : ∀ node : graph.Node,
      graph.label node = ⟨some (nodeAtom singleBonded acyclic
        (positionNode (ruleMajorGraphPositionEquiv tree node))), .realAtom⟩ := by
    intro node
    exact ruleMajorGraphPositionEquiv_label singleBonded acyclic node
  have atomBearing : RootedDigraph.AtomBearingChildren graph := by
    intro parent child _edge
    rw [allReal child]
    exact ⟨nodeAtom singleBonded acyclic (positionNode (ruleMajorGraphPositionEquiv tree child)), rfl⟩
  have address : graph.Addressing := (toOfficialSourceTree tree).declarativeAddressing
  have multiplicities : RootedDigraph.AtomChildMultiplicities input.moleculeGraph
      previousAtom graph := by
    intro parent parentAtom parentLabel parentReal atom
    have parentPhysical : nodeAtom singleBonded acyclic
        (positionNode (ruleMajorGraphPositionEquiv tree parent)) = parentAtom := by
      have raw := allReal parent
      rw [raw] at parentLabel
      exact Option.some.inj parentLabel
    have hcount := ruleMajorTreeGraph_childAtomCount_eq_if singleBonded acyclic enough
      realizes previous previousEq valid sameRoot currentObserved previousObserved incomingEdge
      (parent := parent) parentAtom atom parentLabel
    have atomReal : ∀ node : graph.Node,
        graph.label node = ⟨some (nodeAtom singleBonded acyclic
          (positionNode (ruleMajorGraphPositionEquiv tree node))), .realAtom⟩ := allReal
    have hmultiple : RootedDigraph.ChildAtomProvenanceCount graph parent atom
        RootedDigraph.ProvenanceMultipleBondDuplicate = 0 := by
      unfold RootedDigraph.ChildAtomProvenanceCount RootedDigraph.ChildCountWhere
      rw [Nat.card_eq_zero]
      left
      refine ⟨fun entry => ?_⟩
      rcases entry with ⟨node, ⟨_edge, _atomEq, kind⟩⟩
      rw [atomReal node] at kind
      exact kind
    have hring : RootedDigraph.ChildAtomProvenanceCount graph parent atom
        RootedDigraph.ProvenanceRingDuplicate = 0 := by
      unfold RootedDigraph.ChildAtomProvenanceCount RootedDigraph.ChildCountWhere
      rw [Nat.card_eq_zero]
      left
      refine ⟨fun entry => ?_⟩
      rcases entry with ⟨node, ⟨_edge, _atomEq, kind⟩⟩
      rw [atomReal node] at kind
      exact kind
    have hreal : RootedDigraph.ChildAtomProvenanceCount graph parent atom
        RootedDigraph.ProvenanceRealAtom = RootedDigraph.ChildAtomCount graph parent atom := by
      unfold RootedDigraph.ChildAtomProvenanceCount RootedDigraph.ChildAtomCount
        RootedDigraph.ChildCountWhere
      apply Nat.card_congr
      exact Equiv.subtypeEquiv (Equiv.refl graph.Node) (fun node => by
        simp [atomReal node, RootedDigraph.ProvenanceRealAtom])
    have hancestorSuppressed : ∀ (adj : input.moleculeGraph.Adj parentAtom atom),
        RootedDigraph.BranchAncestorAtom graph previousAtom atom parent →
          RootedDigraph.SuppressedParentAtom graph previousAtom atom parent := by
      intro adj branchAncestor
      exact ruleMajorTreeGraph_branchAncestor_suppressed singleBonded acyclic enough
        realizes previous previousEq valid sameRoot currentObserved previousObserved incomingEdge
        (parent := parent) parentAtom atom parentLabel adj branchAncestor
    have hSuppAdj : RootedDigraph.SuppressedParentAtom graph previousAtom atom parent →
        input.moleculeGraph.Adj parentAtom atom := by
      intro suppressed
      rcases suppressed with ⟨parentRoot, atomExternal⟩ | ⟨ancestor, parentChild, ancestorLabel⟩
      · subst parent
        subst atom
        have rootPhysical : nodeAtom singleBonded acyclic
            (positionNode (ruleMajorGraphPositionEquiv tree graph.root)) = currentAtom := by
          simpa only [ruleMajorGraphPositionEquiv_root, positionNode_rootPosition] using
            (nodeAtom_eq_of_observed singleBonded acyclic currentObserved)
        have parentEq : parentAtom = currentAtom := parentPhysical.symm.trans rootPhysical
        simpa [parentEq] using input.moleculeGraph.adj_symm.mpr incomingEdge
      · have ancestorPhysical : nodeAtom singleBonded acyclic
            (positionNode (ruleMajorGraphPositionEquiv tree ancestor)) = atom := by
          have raw := allReal ancestor
          rw [raw] at ancestorLabel
          exact Option.some.inj ancestorLabel
        have parentEq' : (graph.label parent).atom? = some parentAtom := parentLabel
        exact input.moleculeGraph.adj_symm.mp
          (localFacts.2.2.2 ancestor parent atom parentAtom parentChild ancestorLabel parentLabel)
    have hSuppBranch : RootedDigraph.SuppressedParentAtom graph previousAtom atom parent →
        RootedDigraph.BranchAncestorAtom graph previousAtom atom parent := by
      intro suppressed
      rcases suppressed with ⟨parentRoot, atomExternal⟩ | ⟨ancestor, parentChild, ancestorLabel⟩
      · exact Or.inl atomExternal
      · exact Or.inr ⟨ancestor, Relation.TransGen.single parentChild, ancestorLabel⟩
    have hbond : input.moleculeGraph.bond parentAtom atom =
        if input.moleculeGraph.Adj parentAtom atom then 1 else 0 := by
      by_cases adj : input.moleculeGraph.Adj parentAtom atom
      · simp [adj, singleBonded parentAtom atom adj]
      · have zero : input.moleculeGraph.bond parentAtom atom = 0 :=
          Nat.eq_zero_of_not_pos (by simpa [MoleculeGraph.Adj] using adj)
        simp [adj, zero]
    have htotal : RootedDigraph.ChildAtomCount graph parent atom =
        input.moleculeGraph.bond parentAtom atom -
          (if RootedDigraph.SuppressedParentAtom graph previousAtom atom parent then 1 else 0) := by
      rw [hcount, hbond]
      by_cases adj : input.moleculeGraph.Adj parentAtom atom
      · by_cases suppressed : RootedDigraph.SuppressedParentAtom graph previousAtom atom parent
        · simp [adj, suppressed, graph]
        · simp [adj, suppressed, graph]
      · have noSuppressed : ¬ RootedDigraph.SuppressedParentAtom graph previousAtom atom parent :=
          fun suppressed => adj (hSuppAdj suppressed)
        simp [adj, noSuppressed]
    have hringRhs : ¬ (input.moleculeGraph.Adj parentAtom atom ∧
        RootedDigraph.BranchAncestorAtom graph previousAtom atom parent ∧
        ¬ RootedDigraph.SuppressedParentAtom graph previousAtom atom parent) := by
      rintro ⟨adj, ancestor, notSuppressed⟩
      exact notSuppressed (hancestorSuppressed adj ancestor)
    have hrealRhs : RootedDigraph.ChildAtomProvenanceCount graph parent atom
        RootedDigraph.ProvenanceRealAtom =
          (if input.moleculeGraph.Adj parentAtom atom ∧
            ¬ RootedDigraph.BranchAncestorAtom graph previousAtom atom parent then 1 else 0) := by
      rw [hreal, hcount]
      by_cases adj : input.moleculeGraph.Adj parentAtom atom
      · by_cases branch : RootedDigraph.BranchAncestorAtom graph previousAtom atom parent
        · have suppressed := hancestorSuppressed adj branch
          have suppressedActual : RootedDigraph.SuppressedParentAtom
              (ruleMajorTreeGraph tree) previousAtom atom parent := by
            simpa [graph] using suppressed
          simp [adj, branch, suppressedActual]
        · have notSuppressed : ¬ RootedDigraph.SuppressedParentAtom graph previousAtom atom parent := by
            intro suppressed
            exact branch (hSuppBranch suppressed)
          have notSuppressedActual : ¬ RootedDigraph.SuppressedParentAtom
              (ruleMajorTreeGraph tree) previousAtom atom parent := by
            simpa [graph] using notSuppressed
          simp [adj, branch, notSuppressedActual]
      · have notSuppressed : ¬ RootedDigraph.SuppressedParentAtom graph previousAtom atom parent :=
          fun suppressed => adj (hSuppAdj suppressed)
        simp [adj, graph]
    refine ⟨htotal, ?_, ?_, hrealRhs⟩
    · rw [hmultiple]
      by_cases adj : input.moleculeGraph.Adj parentAtom atom
      · simp [singleBonded _ _ adj]
      · have zero : input.moleculeGraph.bond parentAtom atom = 0 :=
          Nat.eq_zero_of_not_pos (by simpa [MoleculeGraph.Adj] using adj)
        simp [zero]
    · rw [hring]
      simp [hringRhs]
  have exactExpansion : RootedDigraph.ExactExpansion input.moleculeGraph previousAtom
      currentAtom graph :=
    ⟨localFacts, ⟨address, multiplicities⟩⟩
  have distances : ∀ addressing : graph.Addressing,
      RootedDigraph.DuplicateDistancesCorrect graph previousAtom addressing := by
    intro addressing parent child edge
    rw [allReal child]
    simp
  exact ⟨exactExpansion, incomingEdge, atomBearing, distances⟩

/-- Any separately supplied faithful expansion of the same actual incoming edge is isomorphic
to the graph erased from the realized context tree. -/
theorem ruleMajorTreeGraph_iso_of_faithful
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {currentAtom previousAtom : input.Atom}
    (currentObserved : tree.source.occurrence.1.node.current? = some currentAtom)
    (previousObserved : previous.1.node.current? = some previousAtom)
    (incomingEdge : input.moleculeGraph.Adj previousAtom currentAtom)
    (other : RootedDigraph input.Atom)
    (otherFaithful : RootedDigraph.FaithfulExactExpansion input.moleculeGraph
      previousAtom currentAtom other) :
    Nonempty (RootedDigraph.Iso (ruleMajorTreeGraph tree) other) :=
  RootedDigraph.faithfulExactExpansion_unique_up_to_iso input.moleculeGraph previousAtom
    currentAtom (ruleMajorTreeGraph tree) other
    (ruleMajorTreeGraph_faithfulExactExpansion singleBonded acyclic enough realizes previous
      previousEq valid sameRoot currentObserved previousObserved incomingEdge)
    otherFaithful

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.ruleMajorGraphPositionEquiv
assert_kernel_only TetraStereo.OneCenter.ruleMajorGraphPositionEquiv_label
assert_kernel_only TetraStereo.OneCenter.ruleMajorGraphPositionEquiv_root
assert_kernel_only TetraStereo.OneCenter.ruleMajorGraphCutBranchEquiv
assert_kernel_only TetraStereo.OneCenter.ruleMajorGraphCutBranchEquiv_apply_atom
assert_kernel_only TetraStereo.OneCenter.ruleMajorTreeGraph_locallyAdmissibleExpansion
assert_kernel_only TetraStereo.OneCenter.ruleMajorTreeGraph_faithfulExactExpansion
assert_kernel_only TetraStereo.OneCenter.ruleMajorTreeGraph_iso_of_faithful
