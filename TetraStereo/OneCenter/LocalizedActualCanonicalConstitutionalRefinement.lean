import TetraStereo.OneCenter.LocalizedOutwardDecoratedSourceFaithfulness
import TetraStereo.OneCenter.LocalizedActualRecursiveSortTrace
import TetraStereo.OneCenter.LocalizedActualTableAddressOrder
import TetraStereo.OneCenter.DeclarativeCIPConstitutionalOrderLaws
import TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace TetraStereo
namespace OneCenter

noncomputable section

open scoped Classical
open SparsePhysicalFirstDifference

open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree




















































/-! ## Build success recovery from the recursive sort trace -/

namespace LocalizedActualRecursiveSortTrace

/-- **Successful build recovery.**  A recursive sort trace at any fuel describes the exact tree
and key the actual builder produces at that fuel, so the successful build equation is recovered
from the recorded actual frame: the terminal case replays the builder's terminal branch, the
node case replays the recorded actual `mapM` and the exact production sort equation. -/
theorem build_of_trace
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedActualRecursiveSortTrace input stage read fuel tree key) :
    input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel tree.source =
      some key := by
  cases trace with
  | terminal fuel cursor children childrenComputed terminalChildren fullMatch realizes =>
      cases fuel with
      | zero =>
          change input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read 0 cursor =
            some (localizedCumulativeRule45TerminalKey input stage cursor (read cursor))
          unfold CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?
          simp [childrenComputed, terminalChildren]
      | succ fuel =>
          change input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read (fuel + 1) cursor =
            some (localizedCumulativeRule45TerminalKey input stage cursor (read cursor))
          unfold CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?
          simp [childrenComputed, terminalChildren]
  | node fuel cursor children childKeys sortedKeys sortedTrees childrenComputed nonempty
      childKeysComputed sortedEq constitutionalDescending fullMatch realizes childrenTraced =>
      change input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read (fuel + 1) cursor =
        some (localizedCumulativeRule45StepKey input stage cursor (read cursor) sortedKeys)
      unfold CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?
      simp [childrenComputed]
      rw [if_neg nonempty, childKeysComputed]
      simp
      rw [← sortedEq]
      simp

end LocalizedActualRecursiveSortTrace

/-! ## Structural occupancy of the ranked-sibling declarative addressing -/

namespace OfficialCIPSourceTree

/-- **Lookup-to-occurrence converse.**  Every successful recursive lookup is witnessed by the
recorded preorder occurrence at the same address. -/
theorem mem_occurrences_of_subtreeAt?_eq_some {V : Type*} :
    ∀ (address : List ℕ) (tree subtree : OfficialCIPSourceTree V),
      tree.subtreeAt? address = some subtree →
        (address, subtree.source) ∈ tree.occurrences
  | [], .node sourceNode subtrees, subtree, lookup => by
      simp only [OfficialCIPSourceTree.subtreeAt?] at lookup
      have same : OfficialCIPSourceTree.node sourceNode subtrees = subtree :=
        Option.some.inj lookup
      subst subtree
      simp [OfficialCIPSourceTree.occurrences, OfficialCIPSourceTree.source]
  | slot :: address, .node sourceNode subtrees, subtree, lookup => by
      simp only [OfficialCIPSourceTree.subtreeAt?] at lookup
      cases slotLookup : subtrees[slot]? with
      | none => simp [slotLookup] at lookup
      | some child =>
          simp [slotLookup] at lookup
          have ih := mem_occurrences_of_subtreeAt?_eq_some address child subtree lookup
          rw [OfficialCIPSourceTree.occurrences]
          right
          refine (OfficialCIPSourceTree.mem_forestOccurrences_iff_zipIdx subtrees 0
            (slot :: address, subtree.source)).mpr ?_
          refine ⟨(child, slot), ?_, (address, subtree.source), ih, rfl⟩
          exact (List.mk_mem_zipIdx_iff_getElem?.2 slotLookup)

/-- **Prefix-closure membership.**  The address of every recorded occurrence belongs to the finite
prefix closure of hierarchy addresses. -/
theorem mem_hierarchyAddresses_of_occurrence {V : Type*}
    (tree : OfficialCIPSourceTree V) (entry : OfficialSparseEntry (OfficialCIPNode V))
    (present : entry ∈ tree.occurrences) :
    entry.1 ∈ tree.hierarchyAddresses := by
  unfold OfficialCIPSourceTree.hierarchyAddresses
  right
  exact List.mem_flatMap_of_mem present (by
    simp)

/-- **Addressing reads the node's own hierarchy address.**  The ranked-sibling addressing of the
recursive source tree assigns every declarative node exactly its stored sibling path. -/
theorem declarativeAddressing_address {V : Type} [DecidableEq V]
    (tree : OfficialCIPSourceTree V) (node : tree.HierarchyNode) :
    tree.declarativeAddressing.address node = node.1 := by
  simp [OfficialCIPSourceTree.declarativeAddressing]

/-- **Density of the ranked-sibling addressing.**  For every official source tree, the declarative
addressing is dense: below a hierarchy node with address `parent`, the occupied child addresses are
exactly `parent ++ [slot]` for `slot` below the recursive child count of the subtree at `parent`.
This is purely structural — the slot coordinates come from the recursive sibling lists, not from
any priority order. -/
theorem declarativeAddressing_dense {V : Type} [DecidableEq V]
    (tree : OfficialCIPSourceTree V) :
    DeclarativeCIP.Dense (tree.declarativeAddressing) := by
  intro parent
  obtain ⟨subtree, lookup⟩ :=
    tree.exists_subtreeAt?_eq_some_of_mem_hierarchyAddresses parent.1 parent.2
  refine ⟨subtree.children.length, ?_⟩
  intro slot
  constructor
  · intro presentChild
    obtain ⟨child, addressEq⟩ := presentChild
    have childAddress : child.1 = parent.1 ++ [slot] := by
      rw [tree.declarativeAddressing_address child,
        tree.declarativeAddressing_address parent] at addressEq
      exact addressEq
    have childPresent : parent.1 ++ [slot] ∈ tree.hierarchyAddresses := by
      simpa [childAddress] using child.2
    obtain ⟨childSubtree, childLookup⟩ :=
      tree.exists_subtreeAt?_eq_some_of_mem_hierarchyAddresses
        (parent.1 ++ [slot]) childPresent
    cases subtree with
    | node sourceNode subtrees =>
        have childWithin : (OfficialCIPSourceTree.node sourceNode subtrees).subtreeAt? [slot] =
            some childSubtree := by
          rw [tree.subtreeAt?_append, lookup] at childLookup
          simpa using childLookup
        simp only [OfficialCIPSourceTree.subtreeAt?] at childWithin
        cases slotLookup : subtrees[slot]? with
        | none => simp [slotLookup] at childWithin
        | some _ =>
            simpa [OfficialCIPSourceTree.children] using
              (List.getElem?_eq_some_iff.1 slotLookup).1
  · intro slotLt
    cases subtree with
    | node sourceNode subtrees =>
        have slotLt' : slot < subtrees.length := by
          simpa [OfficialCIPSourceTree.children] using slotLt
        have childLookup : (OfficialCIPSourceTree.node sourceNode subtrees).subtreeAt? [slot] =
            some subtrees[slot] := by
          simp [OfficialCIPSourceTree.subtreeAt?, List.getElem?_eq_getElem slotLt']
        have fullLookup : tree.subtreeAt? (parent.1 ++ [slot]) = some subtrees[slot] := by
          rw [tree.subtreeAt?_append, lookup]
          simp [childLookup]
        have occurrence : (parent.1 ++ [slot], (subtrees[slot]).source) ∈ tree.occurrences :=
          mem_occurrences_of_subtreeAt?_eq_some (parent.1 ++ [slot]) tree subtrees[slot]
            fullLookup
        have membership : parent.1 ++ [slot] ∈ tree.hierarchyAddresses :=
          tree.mem_hierarchyAddresses_of_occurrence
            ⟨parent.1 ++ [slot], (subtrees[slot]).source⟩ occurrence
        exact ⟨⟨parent.1 ++ [slot], membership⟩, by
          simp [tree.declarativeAddressing_address ⟨parent.1 ++ [slot], membership⟩,
            tree.declarativeAddressing_address parent]⟩

end OfficialCIPSourceTree

/-! ## Invariants of generated source trees -/

namespace CertifiedLocalizedCIPInput

/-- **Graph-generated provenance at every hierarchy node.**  In a source tree generated by the
executable official child enumerator from a `rootFromEdge` ligand root, every declarative hierarchy
node resolves to a subtree whose source carries real-atom or duplicate provenance — never an
explicit phantom, lone-pair or auxiliary placeholder.  The proof climbs the hierarchy address: the
root is the `rootFromEdge` source, and each sibling slot is an enumerated child of its parent
subtree, so the enumerator's graph-generated invariant transfers step by step. -/
theorem generatedSourceTree_source_graphGenerated
    (input : CertifiedLocalizedCIPInput)
    (tree : OfficialCIPSourceTree input.Atom)
    (center ligand : input.Atom)
    (generated : tree.GeneratedBy input.executableOfficialCIPChildren)
    (root : tree.source = OfficialCIPNode.rootFromEdge center ligand)
    (node : tree.HierarchyNode) (subtree : OfficialCIPSourceTree input.Atom)
    (lookup : tree.subtreeAt? node.1 = some subtree) :
    subtree.source.GraphGenerated := by
  have hgen : ∀ (address : List ℕ) (t : OfficialCIPSourceTree input.Atom),
      t.GeneratedBy input.executableOfficialCIPChildren →
        t.source.GraphGenerated → ∀ subtree : OfficialCIPSourceTree input.Atom,
          t.subtreeAt? address = some subtree → subtree.source.GraphGenerated := by
    intro address
    induction address with
    | nil =>
        intro t generated tSource subtree lookup
        simp only [OfficialCIPSourceTree.subtreeAt?] at lookup
        exact (Option.some.inj lookup) ▸ tSource
    | cons slot address ih =>
        intro t generated tSource subtree lookup
        cases t with
        | node sourceNode subtrees =>
            simp only [OfficialCIPSourceTree.subtreeAt?] at lookup
            cases slotLookup : subtrees[slot]? with
            | none => simp [slotLookup] at lookup
            | some child =>
                simp [slotLookup] at lookup
                have childGenerated : child.GeneratedBy input.executableOfficialCIPChildren :=
                  OfficialCIPSourceTree.GeneratedBy.of_subtreeAt?
                    input.executableOfficialCIPChildren [slot]
                    (OfficialCIPSourceTree.node sourceNode subtrees) child generated
                    (by simp [OfficialCIPSourceTree.subtreeAt?, slotLookup])
                have childPresent : child.source ∈
                    input.executableOfficialCIPChildren sourceNode :=
                  (generated.1.mem_iff).mp (List.mem_map.mpr ⟨child,
                    List.mem_iff_getElem?.2 ⟨slot, slotLookup⟩, rfl⟩)
                have childSource : child.source.GraphGenerated :=
                  input.executableOfficialCIPChildren_graphGenerated
                    sourceNode child.source childPresent
                exact ih child childGenerated childSource subtree lookup
  exact hgen node.1 tree generated
    (by rw [root]; simp [OfficialCIPNode.GraphGenerated, OfficialCIPNode.rootFromEdge])
    subtree lookup

/-- **Atom-bearing source at every hierarchy node.**  In a generated source tree, every hierarchy
node's source carries a current atom. -/
theorem generatedSourceTree_source_current_isSome
    (input : CertifiedLocalizedCIPInput)
    (tree : OfficialCIPSourceTree input.Atom)
    (center ligand : input.Atom)
    (generated : tree.GeneratedBy input.executableOfficialCIPChildren)
    (root : tree.source = OfficialCIPNode.rootFromEdge center ligand)
    (node : tree.HierarchyNode) (subtree : OfficialCIPSourceTree input.Atom)
    (lookup : tree.subtreeAt? node.1 = some subtree) :
    subtree.source.current?.isSome = true := by
  have hgen : ∀ (address : List ℕ) (t : OfficialCIPSourceTree input.Atom),
      t.GeneratedBy input.executableOfficialCIPChildren →
        t.source.current?.isSome = true → ∀ subtree : OfficialCIPSourceTree input.Atom,
          t.subtreeAt? address = some subtree → subtree.source.current?.isSome = true := by
    intro address
    induction address with
    | nil =>
        intro t generated tSource subtree lookup
        simp only [OfficialCIPSourceTree.subtreeAt?] at lookup
        exact (Option.some.inj lookup) ▸ tSource
    | cons slot address ih =>
        intro t generated tSource subtree lookup
        cases t with
        | node sourceNode subtrees =>
            simp only [OfficialCIPSourceTree.subtreeAt?] at lookup
            cases slotLookup : subtrees[slot]? with
            | none => simp [slotLookup] at lookup
            | some child =>
                simp [slotLookup] at lookup
                have childGenerated : child.GeneratedBy input.executableOfficialCIPChildren :=
                  OfficialCIPSourceTree.GeneratedBy.of_subtreeAt?
                    input.executableOfficialCIPChildren [slot]
                    (OfficialCIPSourceTree.node sourceNode subtrees) child generated
                    (by simp [OfficialCIPSourceTree.subtreeAt?, slotLookup])
                have childPresent : child.source ∈
                    input.executableOfficialCIPChildren sourceNode :=
                  (generated.1.mem_iff).mp (List.mem_map.mpr ⟨child,
                    List.mem_iff_getElem?.2 ⟨slot, slotLookup⟩, rfl⟩)
                have childCurrent : child.source.current?.isSome = true := by
                  obtain ⟨atom, _copyIndex, childExtends⟩ :=
                    input.executableOfficialCIPChildren_extension
                      sourceNode child.source childPresent
                  rw [childExtends]
                  simp [Option.isSome]
                exact ih child childGenerated childCurrent subtree lookup
  exact hgen node.1 tree generated (by rw [root]; simp [Option.isSome,
    OfficialCIPNode.rootFromEdge]) subtree lookup

/-- The current atom carried by a generated hierarchy node's source. -/
theorem generatedSourceTree_source_current
    (input : CertifiedLocalizedCIPInput)
    (tree : OfficialCIPSourceTree input.Atom)
    (center ligand : input.Atom)
    (generated : tree.GeneratedBy input.executableOfficialCIPChildren)
    (root : tree.source = OfficialCIPNode.rootFromEdge center ligand)
    (node : tree.HierarchyNode) (subtree : OfficialCIPSourceTree input.Atom)
    (lookup : tree.subtreeAt? node.1 = some subtree) :
    ∃ atom : input.Atom, subtree.source.current? = some atom :=
  Option.isSome_iff_exists.mp
    (generatedSourceTree_source_current_isSome input tree center ligand generated root
      node subtree lookup)

/-! ## The actual original-root arm package -/





structure OriginalRootArm (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel) where
  /-- The actual cumulative Rules-4a--5 key built by the shipped builder. -/
  key : input.LocalizedRerootCumulativeRule45Key
  /-- The actual decorated occurrence tree, kept identical in every field below. -/
  tree : LocalizedCumulativeDecoratedTree input
    (input.certified.input.molecule.atomCount + 1)
  /-- The successful actual build equation at twice the carrier fuel. -/
  built : input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read
      (2 * (input.certified.input.molecule.atomCount + 1 + 1))
      (input.localizedLigandRootCursor center index) = some key
  /-- The tree is rooted at the actual final original-root ligand cursor. -/
  source : tree.source = input.localizedLigandRootCursor center index

  tableMatch : LocalizedCumulativeTreeTableMatch stage tree key

  realizes : LocalizedCumulativeTreeRealizes input read tree
  /-- The erased source tree is generated by the executable official child enumerator. -/
  generated : (toOfficialSourceTree tree).GeneratedBy input.executableOfficialCIPChildren
  /-- The erased source tree is rooted exactly at `rootFromEdge center ligand`. -/
  root : (toOfficialSourceTree tree).source =
    OfficialCIPNode.rootFromEdge center.1 (input.canonicalLigandAtom center index)
  /-- The erased source tree is a faithful exact declarative expansion of the actual graph. -/
  faithful : DeclarativeCIP.RootedDigraph.FaithfulExactExpansion input.moleculeGraph center.1
    (input.canonicalLigandAtom center index) (toOfficialSourceTree tree).toDeclarativeDigraph

  trace : LocalizedActualRecursiveSortTrace input stage read
    (2 * (input.certified.input.molecule.atomCount + 1 + 1)) tree key










theorem exists_originalRootArm
    (input : CertifiedLocalizedCIPInput) (center : input.TetrahedralCenter) (index : Fin 4)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel) :
    Nonempty (input.OriginalRootArm center index stage read) := by
  let cursor := input.localizedLigandRootCursor center index
  have incoming : LocalizedRerootCursorIncomingParent input cursor :=
    input.localizedLigandRootCursor_incoming center index
  have valid : input.LocalizedRerootCursorValid cursor :=
    input.localizedRerootCursorValid_of_incoming cursor incoming
  obtain ⟨tree, key, source, trace⟩ :=
    exists_trace_of_buildWithRead_at_twice input stage read cursor valid
  have built : input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read
      (2 * (input.certified.input.molecule.atomCount + 1 + 1)) cursor = some key := by
    rw [← source]
    exact LocalizedActualRecursiveSortTrace.build_of_trace trace
  have tableMatch : LocalizedCumulativeTreeTableMatch stage tree key :=
    (LocalizedActualRecursiveSortTrace.fullMatch_of_trace trace).tableMatch
  have realizes : LocalizedCumulativeTreeRealizes input read tree :=
    LocalizedActualRecursiveSortTrace.realizes_of_trace trace
  have positive : LocalizedCumulativeTreePositive tree :=
    input.localizedCumulativeTreePositive_of_atomCount_le
      (fuel := input.certified.input.molecule.atomCount + 1) (by omega) tree
  have treeIncoming : LocalizedCumulativeTreeIncoming input tree := by
    apply input.localizedCumulativeTreeIncoming_of_realizes read tree realizes
    rwa [source]
  have generated : (toOfficialSourceTree tree).GeneratedBy
      input.executableOfficialCIPChildren :=
    input.toOfficialSourceTree_generatedBy read tree realizes positive treeIncoming
  have treeRoot : (toOfficialSourceTree tree).source =
      OfficialCIPNode.rootFromEdge center.1 (input.canonicalLigandAtom center index) := by
    rw [toOfficialSourceTree_source, source]
    exact input.localizedLigandRootNode_eq_rootFromEdge center index
  have faithful : DeclarativeCIP.RootedDigraph.FaithfulExactExpansion input.moleculeGraph
      center.1 (input.canonicalLigandAtom center index)
      (toOfficialSourceTree tree).toDeclarativeDigraph :=
    input.generatedExecutableSourceTree_faithfulExactExpansion (toOfficialSourceTree tree)
      center.1 (input.canonicalLigandAtom center index) generated treeRoot
      (input.canonicalLigandAtom_adj center index)
  exact ⟨⟨key, tree, built, source, tableMatch, realizes, generated, treeRoot, faithful,
    trace⟩⟩

/-! ## Root observation correspondence -/

/-- The actual decorated observation read by one constitutional rule. -/
def armObservation (rule : DeclarativeCIP.ConstitutionalRule)
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) : Nat :=
  match rule with
  | .rule1aAtomicNumber => tree.atomicNumber
  | .rule1bDuplicateNodeProximity => tree.rule1bDistance
  | .rule2AtomicMass => tree.isotopeMass








theorem arm_root_nodeObservation_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (label : Option LocalizedAuxiliaryLabel)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel))
    (center ligand : input.Atom)
    (root : (toOfficialSourceTree (localizedRootTree input cursor label children)).source =
      OfficialCIPNode.rootFromEdge center ligand)
    (rule : DeclarativeCIP.ConstitutionalRule) :
    DeclarativeCIP.nodeObservation input.moleculeGraph
        (toOfficialSourceTree (localizedRootTree input cursor label children)).toDeclarativeDigraph
        rule (toOfficialSourceTree (localizedRootTree input cursor label children)).toDeclarativeDigraph.root =
      DeclarativeCIP.priorityValue rule
        (armObservation rule (localizedRootTree input cursor label children)) := by
  have nodeEq : cursor.occurrence.1.node = OfficialCIPNode.rootFromEdge center ligand := by
    simpa [toOfficialSourceTree_localizedRootTree] using root
  have rootLabel : ((toOfficialSourceTree (localizedRootTree input cursor label children)).toDeclarativeDigraph.label
      (toOfficialSourceTree (localizedRootTree input cursor label children)).toDeclarativeDigraph.root) =
      cursor.occurrence.1.node.toDeclarativeLabel := by
    change (toOfficialSourceTree (localizedRootTree input cursor label children)).declarativeLabel
        ⟨[], (toOfficialSourceTree (localizedRootTree input cursor label children)).nil_mem_hierarchyAddresses⟩ =
      cursor.occurrence.1.node.toDeclarativeLabel
    unfold OfficialCIPSourceTree.declarativeLabel
    rw [toOfficialSourceTree_localizedRootTree]
    simp [OfficialCIPSourceTree.sourceAtAddress?, OfficialCIPSourceTree.subtreeAt?,
      OfficialCIPSourceTree.source]
  have rootDepth : ((toOfficialSourceTree (localizedRootTree input cursor label children)).toDeclarativeDigraph.depth
      (toOfficialSourceTree (localizedRootTree input cursor label children)).toDeclarativeDigraph.root) = 0 := by
    change (([] : List ℕ).length = 0)
    rfl
  have currentEq : cursor.occurrence.1.node.current? = some ligand := by
    rw [nodeEq]
    rfl
  unfold DeclarativeCIP.nodeObservation
  rw [rootDepth, rootLabel]
  congr 1
  cases rule with
  | rule1aAtomicNumber =>
      change DeclarativeCIP.nodeAtomicNumber input.moleculeGraph
          (some (cursor.occurrence.1.node.toDeclarativeLabel)) =
        (ofLex (input.moleculeGraph.officialNodeAtomLabel cursor.occurrence.1.node)).1
      simp only [DeclarativeCIP.nodeAtomicNumber, OfficialCIPNode.toDeclarativeLabel, currentEq]
      exact (MoleculeGraph.officialNodeAtomLabel_first_eq_atomZ_of_current
        input.moleculeGraph cursor.occurrence.1.node ligand currentEq).symm
  | rule1bDuplicateNodeProximity =>
      change DeclarativeCIP.nodeRule1bRootDistance []
          (some (cursor.occurrence.1.node.toDeclarativeLabel)) =
        cursor.occurrence.1.node.rule1bRootDistance
      have historyLength : cursor.occurrence.1.node.history.length =
          (([] : List ℕ).length + 2) := by
        rw [nodeEq]
        rfl
      have graphGenerated : cursor.occurrence.1.node.GraphGenerated := by
        rw [nodeEq]
        simp [OfficialCIPNode.GraphGenerated, OfficialCIPNode.rootFromEdge]
      exact (OfficialCIPNode.rule1bRootDistance_eq_independent
        cursor.occurrence.1.node [] historyLength graphGenerated).symm
  | rule2AtomicMass =>
      change DeclarativeCIP.nodeAtomicMass input.moleculeGraph
          (some (cursor.occurrence.1.node.toDeclarativeLabel)) =
        (ofLex (input.moleculeGraph.officialNodeAtomLabel cursor.occurrence.1.node)).2
      have realProv : cursor.occurrence.1.node.provenance =
          OfficialCIPNodeProvenance.realAtom := by
        rw [nodeEq]
        rfl
      have labelSecond : (ofLex (input.moleculeGraph.officialNodeAtomLabel
          cursor.occurrence.1.node)).2 = input.moleculeGraph.atomMass ligand := by
        simp [MoleculeGraph.officialNodeAtomLabel, MoleculeGraph.rawCIPAtomLabel,
          currentEq, realProv]
      rw [labelSecond]
      simp only [DeclarativeCIP.nodeAtomicMass, OfficialCIPNode.toDeclarativeLabel,
        OfficialCIPNodeProvenance.toDeclarative, currentEq, realProv]

namespace OriginalRootArm

/-- **Root observation correspondence of an arm.**  The independent `nodeObservation` of each
constitutional rule at the arm digraph's root equals the priority-oriented reading of the actual
decorated root observation of the arm's own tree. -/
theorem root_nodeObservation_eq
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index stage read)
    (rule : DeclarativeCIP.ConstitutionalRule) :
    DeclarativeCIP.nodeObservation input.moleculeGraph
        (toOfficialSourceTree arm.tree).toDeclarativeDigraph rule
        (toOfficialSourceTree arm.tree).toDeclarativeDigraph.root =
      DeclarativeCIP.priorityValue rule (armObservation rule arm.tree) := by
  have hTrace := arm.trace
  generalize hTree : arm.tree = tree₀ at hTrace
  generalize hKey : arm.key = key₀ at hTrace
  cases hTrace with
  | terminal fuel cursor children childrenComputed terminalChildren fullMatch realizes =>
      exact arm_root_nodeObservation_eq input cursor (read cursor) [] center.1
        (input.canonicalLigandAtom center index) (by simpa [hTree] using arm.root) rule
  | node fuel cursor children childKeys sortedKeys sortedTrees childrenComputed nonempty
      childKeysComputed sortedEq constitutionalDescending fullMatch realizes childrenTraced =>
      exact arm_root_nodeObservation_eq input cursor (read cursor) sortedTrees center.1
        (input.canonicalLigandAtom center index) (by simpa [hTree] using arm.root) rule

end OriginalRootArm

end CertifiedLocalizedCIPInput

/-! ## Slot selection through one sparse sphere -/

/-- Reading a sphere at a cons address equals reading the dropped-head layer of the entries whose
leading slot matches: the matching entry keeps its observation, non-matching entries are skipped. -/
theorem rowValueAt_cons_eq_entriesAtSlot (slot : Nat) (address : List Nat) :
    ∀ layer : List (OfficialSparseEntry ℕ),
      rowValueAt layer (slot :: address) =
        rowValueAt (SparseAddress.dropAddressHeadLayer (SparseAddress.entriesAtSlot slot layer))
          address := by
  intro layer
  induction layer with
  | nil => simp [SparseAddress.entriesAtSlot, SparseAddress.dropAddressHeadLayer]
  | cons entry rest ih =>
      by_cases hEq : entry.1 = slot :: address
      · rw [← hEq, rowValueAt_cons_self]
        rw [SparseAddress.entriesAtSlot]
        rw [List.filter_cons_of_pos (by rw [hEq]; simp)]
        rw [SparseAddress.dropAddressHeadLayer]
        change entry.2 = rowValueAt ((entry.1.tail, entry.2) ::
            (SparseAddress.entriesAtSlot slot rest).map SparseAddress.dropAddressHead) address
        have tailEq : entry.1.tail = address := by
          simpa using congrArg List.tail hEq
        rw [← tailEq, rowValueAt_cons_self]
      · rw [rowValueAt_cons_of_ne entry rest (slot :: address) hEq]
        by_cases hHead : entry.1.head? = some slot
        · have hE : entry.1 = slot :: entry.1.tail := by
            cases eAddr : entry.1 with
            | nil => rw [eAddr] at hHead; simp at hHead
            | cons head tail =>
                have headEq : head = slot :=
                  Option.some.inj (by simpa [eAddr] using hHead)
                simp [headEq]
          have tailNe : entry.1.tail ≠ address := by
            intro h
            exact hEq (by rw [hE, h])
          rw [SparseAddress.entriesAtSlot]
          rw [List.filter_cons_of_pos (by rw [hHead]; simp)]
          rw [SparseAddress.dropAddressHeadLayer]
          change rowValueAt rest (slot :: address) = rowValueAt ((entry.1.tail, entry.2) ::
              (SparseAddress.entriesAtSlot slot rest).map SparseAddress.dropAddressHead) address
          rw [rowValueAt_cons_of_ne (entry.1.tail, entry.2)
            ((SparseAddress.entriesAtSlot slot rest).map SparseAddress.dropAddressHead)
            address tailNe]
          exact ih
        · rw [SparseAddress.entriesAtSlot]
          rw [List.filter_cons_of_neg (by intro h; exact hHead (by simpa using h))]
          exact ih

/-! ## Decorated-tree address lookup and table readback -/

namespace LocalizedCumulativeDecoratedTree

/-- Recursive lookup of the decorated subtree at one ranked sibling address, mirroring
`OfficialCIPSourceTree.subtreeAt?` on the erased source. -/
def decoratedSubtreeAt? {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} :
    LocalizedCumulativeDecoratedTree input carrierFuel → List ℕ →
      Option (LocalizedCumulativeDecoratedTree input carrierFuel)
  | tree, [] => some tree
  | tree, slot :: address =>
      match tree.children[slot]? with
      | none => none
      | some child => decoratedSubtreeAt? child address

/-- The observation at one ranked sibling address, reading zero at absent addresses. -/
def observeAt {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → ℕ)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (address : List ℕ) : ℕ :=
  (tree.decoratedSubtreeAt? address).elim 0 observe

private theorem le_foldl_max {α : Type*} (measure : α → ℕ) :
    ∀ (values : List α) (initial : ℕ),
      initial ≤ values.foldl (fun longest value => max longest (measure value)) initial
  | [], initial => le_refl initial
  | value :: values, initial =>
      le_trans (le_max_left initial (measure value))
        (le_foldl_max measure values (max initial (measure value)))

private theorem foldl_max_mono {α : Type*} (measure : α → ℕ) :
    ∀ (values : List α) {initial other : ℕ},
      initial ≤ other →
        values.foldl (fun longest value => max longest (measure value)) initial ≤
          values.foldl (fun longest value => max longest (measure value)) other
  | [], _initial, _other, monotone => monotone
  | value :: values, initial, other, monotone =>
      have step : max initial (measure value) ≤ max other (measure value) := by
        exact max_le_max monotone le_rfl
      foldl_max_mono measure values step

private theorem length_le_foldl_max {α : Type*} :
    ∀ (values : List (List (List (OfficialSparseEntry α))))
      (value : List (List (OfficialSparseEntry α))),
      value ∈ values → value.length ≤ localizedTreeChildLayerCount values
  | [], value, present => (List.not_mem_nil present).elim
  | head :: tail, value, present => by
      rcases List.mem_cons.mp present with same | later
      · subst value
        change head.length ≤ tail.foldl (fun longest value => max longest value.length)
          (max 0 head.length)
        have headLe : head.length ≤ max 0 head.length := le_max_right 0 head.length
        have initialLe : max 0 head.length ≤ tail.foldl (fun longest value => max longest value.length)
            (max 0 head.length) :=
          le_foldl_max (fun value => value.length) tail (max 0 head.length)
        exact le_trans headLe initialLe
      · have ih := length_le_foldl_max tail value later
        change value.length ≤ tail.foldl (fun longest value => max longest value.length)
          (max 0 head.length)
        have monotone : tail.foldl (fun longest value => max longest value.length) 0 ≤
            tail.foldl (fun longest value => max longest value.length) (max 0 head.length) :=
          foldl_max_mono (fun value => value.length) tail (Nat.zero_le _)
        exact le_trans ih monotone

/-- Every stored child table's sphere count is bounded by the merged table's recorded layer count,
so sphere reads beyond the merged count are empty on the child side as well. -/
theorem table_length_le_localizedTreeChildLayerCount {α : Type*}
    (tables : List (List (List (OfficialSparseEntry α))))
    {slot : Nat} (childTable : List (List (OfficialSparseEntry α)))
    (atSlot : tables[slot]? = some childTable) :
    childTable.length ≤ localizedTreeChildLayerCount tables := by
  obtain ⟨hslot, tableEq⟩ := List.getElem?_eq_some_iff.mp atSlot
  rw [← tableEq]
  exact length_le_foldl_max tables (tables[slot]'hslot) (List.getElem_mem hslot)

/-- **Addressed readback of the decorated sparse table.**  Reading the `observe`-table at one
ranked sibling address returns exactly the observation of the decorated subtree at that address:
the root sphere is read at the empty address, and each cons step passes through the slot selection
of the child merge, dropping the leading slot both in the stored row and in the address. -/
theorem tableValue_table_eq_observeAt {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → ℕ) :
    ∀ (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (address : List ℕ),
      tableValue (table observe tree) address = observeAt observe tree address := by
  intro tree address
  induction address generalizing tree with
  | nil =>
      unfold observeAt
      rw [decoratedSubtreeAt?]
      change rowValueAt ((table observe tree).getD 0 []) [] = observe tree
      rw [table_eq_root_merge]
      change rowValueAt [([], observe tree)] [] = observe tree
      rfl
  | cons slot address ih =>
      unfold observeAt
      rw [decoratedSubtreeAt?]
      change rowValueAt ((table observe tree).getD (address.length + 1) []) (slot :: address) =
        (match tree.children[slot]? with
         | none => none
         | some child => child.decoratedSubtreeAt? address).elim 0 observe
      cases hSlotLookup : tree.children[slot]? with
      | none =>
          change rowValueAt ((table observe tree).getD (address.length + 1) []) (slot :: address) = 0
          rw [table_eq_root_merge]
          change rowValueAt ((mergeLocalizedTreeChildTables (tree.children.map (table observe))).getD
            address.length []) (slot :: address) = 0
          unfold mergeLocalizedTreeChildTables
          rw [SparseAddress.mergePairTable_getD]
          by_cases hIn : address.length < localizedTreeChildLayerCount (tree.children.map (table observe))
          · rw [if_pos hIn]
            rw [rowValueAt_cons_eq_entriesAtSlot slot address]
            unfold SparseAddress.mergePairs
            rw [SparseAddress.entriesAtSlot_flatMap_prefixLayer
              (pairs := (tree.children.map (table observe)).zipIdx)
              (block := fun value => (id value).getD address.length [])
              (selected := slot)]
            have filterEmpty : (tree.children.map (table observe)).zipIdx.filter
                (fun pair => pair.2 == slot) = [] := by
              apply List.eq_nil_iff_forall_not_mem.mpr
              intro pair present
              have sndLt : pair.2 < (tree.children.map (table observe)).length := by
                have zipPresent : pair ∈ (tree.children.map (table observe)).zipIdx :=
                  (List.mem_filter.mp present).1
                have lt := List.snd_lt_of_mem_zipIdx (k := 0) zipPresent
                simpa using lt
              have noSlot : tree.children.length ≤ slot :=
                (List.getElem?_eq_none_iff.mp hSlotLookup)
              have ltLen : pair.2 < tree.children.length := by simpa using sndLt
              have selected : pair.2 = slot := by
                simpa using (List.mem_filter.mp present).2
              omega
            rw [filterEmpty]
            simp [SparseAddress.dropAddressHeadLayer]
          · rw [if_neg hIn]
            simp [rowValueAt]
      | some child =>
          change rowValueAt ((table observe tree).getD (address.length + 1) []) (slot :: address) =
            (child.decoratedSubtreeAt? address).elim 0 observe
          rw [table_eq_root_merge]
          change rowValueAt ((mergeLocalizedTreeChildTables (tree.children.map (table observe))).getD
            address.length []) (slot :: address) =
            (child.decoratedSubtreeAt? address).elim 0 observe
          unfold mergeLocalizedTreeChildTables
          rw [SparseAddress.mergePairTable_getD]
          by_cases hIn : address.length < localizedTreeChildLayerCount (tree.children.map (table observe))
          · rw [if_pos hIn]
            rw [rowValueAt_cons_eq_entriesAtSlot slot address]
            have entriesEq : SparseAddress.entriesAtSlot slot (SparseAddress.mergePairs
                (tree.children.map (table observe)).zipIdx (fun value => (id value).getD address.length [])) =
              SparseAddress.entriesAtSlot slot ((SparseAddress.mergePairTable
                (tree.children.map (table observe)).zipIdx id
                (localizedTreeChildLayerCount (tree.children.map (table observe)))).getD
                  address.length []) := by
              rw [SparseAddress.mergePairTable_getD, if_pos hIn]
            rw [entriesEq]
            have atSlot : (tree.children.map (table observe))[slot]? = some (table observe child) := by
              rw [List.getElem?_map, hSlotLookup]
              rfl
            have childBound : (table observe child).length ≤
                localizedTreeChildLayerCount (tree.children.map (table observe)) :=
              table_length_le_localizedTreeChildLayerCount
                (tree.children.map (table observe)) (table observe child) atSlot
            rw [SparseAddress.mergePairTable_getD_entriesAtSlot_zipIdx
              (values := tree.children.map (table observe)) (layers := id)
              (count := localizedTreeChildLayerCount (tree.children.map (table observe)))
              (depth := address.length) (slot := slot) (chosen := table observe child)
              childBound atSlot]
            change tableValue (table observe child) address = observeAt observe child address
            exact ih child
          · rw [if_neg hIn]
            simp [rowValueAt]
            change 0 = observeAt observe child address
            rw [← ih child]
            unfold tableValue
            have atSlot : (tree.children.map (table observe))[slot]? = some (table observe child) := by
              rw [List.getElem?_map, hSlotLookup]
              rfl
            have childBound : (table observe child).length ≤
                localizedTreeChildLayerCount (tree.children.map (table observe)) :=
              table_length_le_localizedTreeChildLayerCount
                (tree.children.map (table observe)) (table observe child) atSlot
            have short : (table observe child).length ≤ address.length :=
              le_trans childBound (Nat.le_of_not_lt hIn)
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none short]
            rfl

/-- One cons step of the erased lookup: after one ranked sibling slot, the source tree lookup
descends exactly through the erased child stored at that slot. -/
private theorem toOfficialSourceTree_subtreeAt?_cons {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat} (source : input.LocalizedRerootCursor carrierFuel)
    (atomicNumber rule1bDistance isotopeMass : ℕ) (label : Option LocalizedAuxiliaryLabel)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel))
    (slot : Nat) (address : List ℕ) :
    (toOfficialSourceTree (LocalizedCumulativeDecoratedTree.mk source atomicNumber
        rule1bDistance isotopeMass label children)).subtreeAt? (slot :: address) =
      (match Option.map toOfficialSourceTree children[slot]? with
       | none => none
       | some subtree => subtree.subtreeAt? address) := by
  simp only [toOfficialSourceTree_mk, OfficialCIPSourceTree.subtreeAt?,
    toOfficialSourceTreeList_eq_map]
  cases hSlot : children[slot]? with
  | none => simp [hSlot]
  | some child => simp [hSlot]

/-- Recursive decorated lookup commutes with source erasure: the erased subtree at an address is
the erasure of the decorated subtree at the same address. -/
theorem toOfficialSourceTree_subtreeAt? {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} :
    ∀ (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (address : List ℕ),
      (toOfficialSourceTree tree).subtreeAt? address =
        (tree.decoratedSubtreeAt? address).map toOfficialSourceTree := by
  intro tree address
  induction address generalizing tree with
  | nil =>
      rw [decoratedSubtreeAt?, OfficialCIPSourceTree.subtreeAt?]
      rfl
  | cons slot address ih =>
      cases tree with
      | mk source atomicNumber rule1bDistance isotopeMass label children =>
          rw [decoratedSubtreeAt?]
          rw [toOfficialSourceTree_subtreeAt?_cons source atomicNumber rule1bDistance isotopeMass
            label children slot address]
          cases slotLookup : children[slot]? with
          | none => simp
          | some child => simp [ih child]

/-- Realization descends along ranked sibling addresses: every addressed decorated subtree is the
actual `localizedRootTree` built at its own source cursor from its own sorted children. -/
theorem realizes_of_decoratedSubtreeAt? {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree) (address : List ℕ)
    (subtree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (lookup : tree.decoratedSubtreeAt? address = some subtree) :
    subtree = localizedRootTree input subtree.source (read subtree.source) subtree.children := by
  induction address generalizing tree subtree with
  | nil =>
      rw [decoratedSubtreeAt?] at lookup
      have same : tree = subtree := Option.some.inj lookup
      subst subtree
      cases realizes with
      | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealize =>
          rfl
  | cons slot address ih =>
      cases realizes with
      | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealize =>
          rw [decoratedSubtreeAt?] at lookup
          change (match sortedChildren[slot]? with
            | none => none
            | some child => child.decoratedSubtreeAt? address) = some subtree at lookup
          cases slotLookup : sortedChildren[slot]? with
          | none => simp [slotLookup] at lookup
          | some child =>
              simp [slotLookup] at lookup
              exact ih child
                (childrenRealize child (List.mem_iff_getElem?.2 ⟨slot, slotLookup⟩)) subtree lookup

/-! ## Address composition, cons readback and recursive realization descent -/

/-- Recursive decorated lookup composes along address concatenation: the subtree at
`first ++ second` is the `second`-subtree of the `first`-subtree. -/
theorem decoratedSubtreeAt?_append {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} :
    ∀ (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (first second : List ℕ),
      tree.decoratedSubtreeAt? (first ++ second) =
        (tree.decoratedSubtreeAt? first).bind fun subtree => subtree.decoratedSubtreeAt? second := by
  intro tree first
  induction first generalizing tree with
  | nil =>
      intro second
      simp [decoratedSubtreeAt?]
  | cons slot first ih =>
      intro second
      simp only [List.cons_append, decoratedSubtreeAt?]
      cases slotLookup : tree.children[slot]? with
      | none => simp
      | some child =>
          simp only
          exact ih child second

/-- A cons address is occupied exactly when the slot selects a child whose own lookup at the
remaining address succeeds. -/
theorem decoratedSubtreeAt?_cons_some {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (digit : ℕ) (path : List ℕ) :
    (∃ subtree, tree.decoratedSubtreeAt? (digit :: path) = some subtree) ↔
      ∃ child subtree, tree.children[digit]? = some child ∧
        child.decoratedSubtreeAt? path = some subtree := by
  constructor
  · rintro ⟨subtree, lookup⟩
    rw [decoratedSubtreeAt?] at lookup
    cases slotLookup : tree.children[digit]? with
    | none => simp [slotLookup] at lookup
    | some child =>
        exact ⟨child, subtree, rfl, by simpa [slotLookup] using lookup⟩
  · rintro ⟨child, subtree, slotLookup, lookup⟩
    exact ⟨subtree, by rw [decoratedSubtreeAt?, slotLookup]; exact lookup⟩

/-- Observation readback descends one cons step: the value at `digit :: path` is the `path`-value
of the child selected at `digit`, or zero when the slot is absent. -/
theorem observeAt_cons {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → ℕ)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (digit : ℕ) (path : List ℕ) :
    observeAt observe tree (digit :: path) =
      ((tree.children[digit]?).map fun child => observeAt observe child path).elim 0 id := by
  unfold observeAt
  rw [decoratedSubtreeAt?]
  cases slotLookup : tree.children[digit]? with
  | none => rfl
  | some child => rfl

/-- Addressed sparse readback descends one cons step. -/
theorem tableValue_table_cons {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → ℕ) :
    ∀ (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (digit : ℕ) (path : List ℕ),
      tableValue (table observe tree) (digit :: path) =
        ((tree.children[digit]?).map fun child =>
          tableValue (table observe child) path).elim 0 id := by
  intro tree digit path
  rw [tableValue_table_eq_observeAt observe tree (digit :: path),
    observeAt_cons observe tree digit path]
  cases slotLookup : tree.children[digit]? with
  | none => rfl
  | some child =>
      change observeAt observe child path = tableValue (table observe child) path
      exact (tableValue_table_eq_observeAt observe child path).symm

/-- Realization descends recursively through arbitrary ranked sibling addresses: every addressed
decorated subtree realizes itself, not only the one-step children. -/
theorem realizes_of_decoratedSubtreeAt?_rec {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel} :
    ∀ {tree : LocalizedCumulativeDecoratedTree input carrierFuel},
      LocalizedCumulativeTreeRealizes input read tree → ∀ (path : List ℕ)
        (subtree : LocalizedCumulativeDecoratedTree input carrierFuel),
        tree.decoratedSubtreeAt? path = some subtree →
          LocalizedCumulativeTreeRealizes input read subtree := by
  intro tree realizes path subtree lookup
  induction path generalizing tree realizes subtree with
  | nil =>
      rw [decoratedSubtreeAt?] at lookup
      have same : tree = subtree := Option.some.inj lookup
      subst subtree
      exact realizes
  | cons slot path ih =>
      cases realizes with
      | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealize =>
          rw [decoratedSubtreeAt?] at lookup
          change (match sortedChildren[slot]? with
            | none => none
            | some child => child.decoratedSubtreeAt? path) = some subtree at lookup
          cases slotLookup : sortedChildren[slot]? with
          | none => simp [slotLookup] at lookup
          | some child =>
              simp [slotLookup] at lookup
              exact ih (tree := child)
                (childrenRealize child (List.mem_iff_getElem?.2 ⟨slot, slotLookup⟩))
                subtree lookup

end LocalizedCumulativeDecoratedTree

/-! ## Actual source-node label components versus independent constitutional observations -/

namespace MoleculeGraph

/-- The atomic number read from the official production label equals the independent Rule-1a
atomic-number observation, for every provenance class: real atoms read the raw CIP label,
duplicates and placeholders keep the atomic number under the production Rule-1a convention. -/
theorem officialNodeAtomLabel_first_eq_nodeAtomicNumber {Atom : Type*} [Fintype Atom]
    [DecidableEq Atom] (m : MoleculeGraph Atom) (node : OfficialCIPNode Atom) :
    (ofLex (m.officialNodeAtomLabel node)).1 =
      DeclarativeCIP.nodeAtomicNumber m (some node.toDeclarativeLabel) := by
  cases node with
  | mk current _history provenance =>
      cases current with
      | none =>
          simp [MoleculeGraph.officialNodeAtomLabel, OfficialCIPNode.toDeclarativeLabel,
            DeclarativeCIP.nodeAtomicNumber]
      | some atom =>
          cases provenance with
          | realAtom =>
              simp [MoleculeGraph.officialNodeAtomLabel, OfficialCIPNode.toDeclarativeLabel,
                DeclarativeCIP.nodeAtomicNumber, MoleculeGraph.rawCIPAtomLabel]
          | multipleBondDuplicate distance =>
              simp [MoleculeGraph.officialNodeAtomLabel, OfficialCIPNode.toDeclarativeLabel,
                DeclarativeCIP.nodeAtomicNumber]
          | ringDuplicate distance =>
              simp [MoleculeGraph.officialNodeAtomLabel, OfficialCIPNode.toDeclarativeLabel,
                DeclarativeCIP.nodeAtomicNumber]
          | placeholder kind distance =>
              simp [MoleculeGraph.officialNodeAtomLabel, OfficialCIPNode.toDeclarativeLabel,
                DeclarativeCIP.nodeAtomicNumber]

/-- The isotope mass read from the official production label equals the independent Rule-2 mass
observation: real atoms read the raw CIP mass, every duplicate, placeholder and absent node reads
zero under the production Rule-2 convention. -/
theorem officialNodeAtomLabel_second_eq_nodeAtomicMass {Atom : Type*} [Fintype Atom]
    [DecidableEq Atom] (m : MoleculeGraph Atom) (node : OfficialCIPNode Atom) :
    (ofLex (m.officialNodeAtomLabel node)).2 =
      DeclarativeCIP.nodeAtomicMass m (some node.toDeclarativeLabel) := by
  cases node with
  | mk current _history provenance =>
      cases current with
      | none =>
          simp [MoleculeGraph.officialNodeAtomLabel, OfficialCIPNode.toDeclarativeLabel,
            DeclarativeCIP.nodeAtomicMass]
      | some atom =>
          cases provenance with
          | realAtom =>
              simp [MoleculeGraph.officialNodeAtomLabel, OfficialCIPNodeProvenance.toDeclarative,
                OfficialCIPNode.toDeclarativeLabel, DeclarativeCIP.nodeAtomicMass,
                MoleculeGraph.rawCIPAtomLabel]
          | multipleBondDuplicate distance =>
              simp [MoleculeGraph.officialNodeAtomLabel, OfficialCIPNodeProvenance.toDeclarative,
                OfficialCIPNode.toDeclarativeLabel, DeclarativeCIP.nodeAtomicMass]
          | ringDuplicate distance =>
              simp [MoleculeGraph.officialNodeAtomLabel, OfficialCIPNodeProvenance.toDeclarative,
                OfficialCIPNode.toDeclarativeLabel, DeclarativeCIP.nodeAtomicMass]
          | placeholder kind distance =>
              cases kind <;> simp [MoleculeGraph.officialNodeAtomLabel,
                OfficialCIPNodeProvenance.toDeclarative, OfficialCIPNode.toDeclarativeLabel,
                DeclarativeCIP.nodeAtomicMass]

end MoleculeGraph

/-! ## All-address observation correspondence in the fixed original-arm digraph -/

namespace CertifiedLocalizedCIPInput

/-- The addressed sparse column read by one constitutional rule inside an actual cumulative key:
Rule 1a reads the atomic-number column, Rule 1b the original-root distance column and Rule 2 the
isotope-mass column. -/
def armTableColumn {input : CertifiedLocalizedCIPInput}
    (key : input.LocalizedRerootCumulativeRule45Key) :
    DeclarativeCIP.ConstitutionalRule → List (List (OfficialSparseEntry ℕ))
  | .rule1aAtomicNumber => key.constitutional.rule1a
  | .rule1bDuplicateNodeProximity => key.constitutional.rule1b
  | .rule2AtomicMass => key.constitutional.rule2

/-- The actual source-node observation read by one constitutional rule at an actual cursor: the
atomic number and isotope mass come from the official production node label, the Rule-1b value is
the stored original-root distance. -/
def armSourceObservation (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (rule : DeclarativeCIP.ConstitutionalRule) (cursor : input.LocalizedRerootCursor carrierFuel) : Nat :=
  match rule with
  | .rule1aAtomicNumber => (ofLex (input.moleculeGraph.officialNodeAtomLabel cursor.occurrence.1.node)).1
  | .rule1bDuplicateNodeProximity => cursor.occurrence.1.node.rule1bRootDistance
  | .rule2AtomicMass => (ofLex (input.moleculeGraph.officialNodeAtomLabel cursor.occurrence.1.node)).2

namespace OriginalRootArm

/-- **All-address observation correspondence of an arm.**  At every declarative hierarchy node of
the arm digraph — not only the root — the independent `nodeObservation` of each constitutional
rule equals the priority-oriented sparse-table reading of the actual key's column at the node's
own ranked sibling address.  The proof resolves the node's address to a concrete decorated
subtree (the erased lookup descends exactly as the decorated lookup does), reads the table column
back to the observation of that same decorated subtree (the sparse readback follows the stored
child merge), and identifies the actual decoration with the source-node semantics: Rule 1a atomic
number and Rule 2 isotope mass through the official production label, Rule 1b through the stored
original-root distance against the independent positional semantics at the generated node. -/
theorem nodeObservation_eq_actualTableValue
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index stage read)
    (rule : DeclarativeCIP.ConstitutionalRule)
    (node : (toOfficialSourceTree arm.tree).toDeclarativeDigraph.Node) :
    DeclarativeCIP.nodeObservation input.moleculeGraph
        (toOfficialSourceTree arm.tree).toDeclarativeDigraph rule node =
      DeclarativeCIP.priorityValue rule (tableValue (armTableColumn arm.key rule) node.1) := by
  obtain ⟨subtree, lookup⟩ :=
    (toOfficialSourceTree arm.tree).exists_subtreeAt?_eq_some_of_mem_hierarchyAddresses
      node.1 node.2
  unfold DeclarativeCIP.nodeObservation
  have depthEq : (toOfficialSourceTree arm.tree).toDeclarativeDigraph.depth node = node.1.length :=
    rfl
  rw [depthEq]
  have labelEq : (toOfficialSourceTree arm.tree).toDeclarativeDigraph.label node =
      subtree.source.toDeclarativeLabel :=
    (toOfficialSourceTree arm.tree).declarativeLabel_eq_of_subtreeAt? subtree node lookup
  rw [labelEq]
  congr 1
  have erasedLookup : (arm.tree.decoratedSubtreeAt? node.1).map toOfficialSourceTree = some subtree :=
    (lookup.symm.trans (toOfficialSourceTree_subtreeAt? arm.tree node.1)).symm
  obtain ⟨dsub, decLookup, dsubEq⟩ := Option.map_eq_some_iff.mp erasedLookup
  have shape : dsub = localizedRootTree input dsub.source (read dsub.source) dsub.children :=
    realizes_of_decoratedSubtreeAt? arm.tree arm.realizes node.1 dsub decLookup
  have sourceEq : dsub.source.occurrence.1.node = subtree.source := by
    simpa [dsubEq] using (toOfficialSourceTree_source dsub).symm
  have tableEq : tableValue (armTableColumn arm.key rule) node.1 = armObservation rule dsub := by
    cases rule with
    | rule1aAtomicNumber =>
        have match1a : table (fun node => node.atomicNumber) arm.tree =
            arm.key.constitutional.rule1a := by
          simpa [LocalizedCumulativeTreeTableMatch, tables_rule1a] using arm.tableMatch.1
        calc
          tableValue (armTableColumn arm.key .rule1aAtomicNumber) node.1 =
              tableValue arm.key.constitutional.rule1a node.1 := rfl
          _ = tableValue (table (fun node => node.atomicNumber) arm.tree) node.1 := by
              rw [← match1a]
          _ = observeAt (fun node => node.atomicNumber) arm.tree node.1 := by
              rw [tableValue_table_eq_observeAt]
          _ = armObservation .rule1aAtomicNumber dsub := by
              rw [observeAt, decLookup]
              rfl
    | rule1bDuplicateNodeProximity =>
        have match1b : table (fun node => node.rule1bDistance) arm.tree =
            arm.key.constitutional.rule1b := by
          simpa [LocalizedCumulativeTreeTableMatch, tables_rule1b] using arm.tableMatch.2.1
        calc
          tableValue (armTableColumn arm.key .rule1bDuplicateNodeProximity) node.1 =
              tableValue arm.key.constitutional.rule1b node.1 := rfl
          _ = tableValue (table (fun node => node.rule1bDistance) arm.tree) node.1 := by
              rw [← match1b]
          _ = observeAt (fun node => node.rule1bDistance) arm.tree node.1 := by
              rw [tableValue_table_eq_observeAt]
          _ = armObservation .rule1bDuplicateNodeProximity dsub := by
              rw [observeAt, decLookup]
              rfl
    | rule2AtomicMass =>
        have match2 : table (fun node => node.isotopeMass) arm.tree =
            arm.key.constitutional.rule2 := by
          simpa [LocalizedCumulativeTreeTableMatch, tables_rule2] using arm.tableMatch.2.2.1
        calc
          tableValue (armTableColumn arm.key .rule2AtomicMass) node.1 =
              tableValue arm.key.constitutional.rule2 node.1 := rfl
          _ = tableValue (table (fun node => node.isotopeMass) arm.tree) node.1 := by
              rw [← match2]
          _ = observeAt (fun node => node.isotopeMass) arm.tree node.1 := by
              rw [tableValue_table_eq_observeAt]
          _ = armObservation .rule2AtomicMass dsub := by
              rw [observeAt, decLookup]
              rfl
  rw [tableEq]
  have shapeObs : armObservation rule dsub = armSourceObservation input rule dsub.source := by
    rw [shape]
    cases rule <;> rfl
  rw [shapeObs]
  cases rule with
  | rule1aAtomicNumber =>
      simpa [DeclarativeCIP.ruleValue, armSourceObservation, sourceEq] using
        (MoleculeGraph.officialNodeAtomLabel_first_eq_nodeAtomicNumber
          input.moleculeGraph subtree.source).symm
  | rule1bDuplicateNodeProximity =>
      have historyLength : subtree.source.history.length = node.1.length + 2 :=
        generatedSourceTree_history_length input (toOfficialSourceTree arm.tree) center.1
          (input.canonicalLigandAtom center index) arm.generated arm.root node subtree lookup
      have graphGenerated : subtree.source.GraphGenerated :=
        generatedSourceTree_source_graphGenerated input (toOfficialSourceTree arm.tree)
          center.1 (input.canonicalLigandAtom center index) arm.generated arm.root node subtree
          lookup
      have historyLength' : subtree.source.history.length =
          (List.replicate node.1.length 0).length + 2 := by
        simpa using historyLength
      simpa [DeclarativeCIP.ruleValue, armSourceObservation, sourceEq] using
        (OfficialCIPNode.rule1bRootDistance_eq_independent subtree.source
          (List.replicate node.1.length 0) historyLength' graphGenerated).symm
  | rule2AtomicMass =>
      simpa [DeclarativeCIP.ruleValue, armSourceObservation, sourceEq] using
        (MoleculeGraph.officialNodeAtomLabel_second_eq_nodeAtomicMass
          input.moleculeGraph subtree.source).symm

end OriginalRootArm

/-! ## Sparse support, actual key well-formedness and encoded cons readback -/




theorem hasAddress_atomicNumber_table_iff_subtree {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat} {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) (path : List ℕ) :
    SparseSupportAlignment.HasAddress (table (fun node => node.atomicNumber) tree) path ↔
      ∃ subtree, tree.decoratedSubtreeAt? path = some subtree := by
  rw [(OfficialSparseCanonicalVectorComparison.tableValue_pos_iff_hasAddress
    (LocalizedActualTableAddressOrder.table_wellFormed (fun node => node.atomicNumber) tree)
    (LocalizedActualTableAddressOrder.table_atomicNumber_positive_of_realizes_general realizes)
      path).symm]
  rw [tableValue_table_eq_observeAt (fun node => node.atomicNumber) tree path]
  unfold observeAt
  constructor
  · intro positive
    cases lookup : tree.decoratedSubtreeAt? path with
    | none => simp [lookup] at positive
    | some subtree => exact ⟨subtree, rfl⟩
  · rintro ⟨subtree, lookup⟩
    rw [lookup]
    exact LocalizedActualTableAddressOrder.atomicNumber_positive_of_realizes_general
      (realizes_of_decoratedSubtreeAt?_rec realizes path subtree lookup)





theorem wellFormedRuleMajorKey_of_tableMatch {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (tableMatch : LocalizedCumulativeTreeTableMatch stage tree key)
    (realizes : LocalizedCumulativeTreeRealizes input read tree) :
    OfficialSparseCanonicalVectorComparison.WellFormedRuleMajorKey key.constitutional := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [← tableMatch.1, tables_rule1a] using
      (LocalizedActualTableAddressOrder.table_wellFormed (fun node => node.atomicNumber) tree)
  · simpa [← tableMatch.2.1, tables_rule1b] using
      (LocalizedActualTableAddressOrder.table_wellFormed (fun node => node.rule1bDistance) tree)
  · simpa [← tableMatch.2.2.1, tables_rule2] using
      (LocalizedActualTableAddressOrder.table_wellFormed (fun node => node.isotopeMass) tree)
  · simpa [← tableMatch.1, tables_rule1a] using
      (LocalizedActualTableAddressOrder.table_atomicNumber_positive_of_realizes_general realizes)
  · simpa [← tableMatch.1, ← tableMatch.2.1, tables_rule1a, tables_rule1b] using
      (LocalizedActualTableAddressOrder.SameAddressRows_table_observations
        (fun node => node.rule1bDistance) (fun node => node.atomicNumber) tree)
  · simpa [← tableMatch.1, ← tableMatch.2.2.1, tables_rule1a, tables_rule2] using
      (LocalizedActualTableAddressOrder.SameAddressRows_table_observations
        (fun node => node.isotopeMass) (fun node => node.atomicNumber) tree)

/-- Encoded observation descends one cons step of a table-matched realized key: the parent's
encoded observation at `digit :: path` is the selected sorted child key's encoded observation at
`path`, or `⊥` when the slot is unoccupied. -/
theorem encodedObservation_cons_of_key {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {dsub : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (tableMatch : LocalizedCumulativeTreeTableMatch stage dsub key)
    (realizes : LocalizedCumulativeTreeRealizes input read dsub)
    {sortedKeys : List input.LocalizedRerootCumulativeRule45Key}
    (paired : List.Forall₂ (fun childKey childTree =>
        LocalizedCumulativeTreeTableMatch stage childTree childKey ∧
          LocalizedCumulativeTreeRealizes input read childTree) sortedKeys dsub.children)
    (rule : DeclarativeCIP.ConstitutionalRule) (digit : ℕ) (path : List ℕ) :
    OfficialSparseCanonicalVectorComparison.encodedObservation key.constitutional rule
        (digit :: path) =
      ((sortedKeys[digit]?).map fun childKey =>
        OfficialSparseCanonicalVectorComparison.encodedObservation childKey.constitutional rule
          path).getD ⊥ := by
  unfold OfficialSparseCanonicalVectorComparison.encodedObservation
  by_cases hpresent : SparseSupportAlignment.HasAddress key.constitutional.rule1a (digit :: path)
  · rw [if_pos hpresent]
    have guardTable : SparseSupportAlignment.HasAddress
        (table (fun node => node.atomicNumber) dsub) (digit :: path) := by
      simpa [← tableMatch.1, tables_rule1a] using hpresent
    obtain ⟨subtree, subtreeLookup⟩ :=
      (hasAddress_atomicNumber_table_iff_subtree realizes (digit :: path)).1 guardTable
    obtain ⟨child, subtree', childGet, childPath⟩ :=
      (decoratedSubtreeAt?_cons_some dsub digit path).1 ⟨subtree, subtreeLookup⟩
    have digitLtChildren : digit < dsub.children.length := (List.getElem?_eq_some_iff.1 childGet).1
    have keysLength : sortedKeys.length = dsub.children.length := List.Forall₂.length_eq paired
    have digitLtKeys : digit < sortedKeys.length := by simpa [keysLength] using digitLtChildren
    have keysGet : sortedKeys[digit]? = some (sortedKeys[digit]'digitLtKeys) :=
      List.getElem?_eq_getElem digitLtKeys
    have childIs : child = dsub.children[digit]'digitLtChildren :=
      (Option.some.inj ((List.getElem?_eq_getElem digitLtChildren).symm.trans childGet)).symm
    have slotPaired : LocalizedCumulativeTreeTableMatch stage
        (dsub.children[digit]'digitLtChildren) (sortedKeys[digit]'digitLtKeys) ∧
        LocalizedCumulativeTreeRealizes input read (dsub.children[digit]'digitLtChildren) :=
      List.Forall₂.get (i := digit) paired digitLtKeys digitLtChildren
    have childGuard : SparseSupportAlignment.HasAddress
        (sortedKeys[digit]'digitLtKeys).constitutional.rule1a path := by
      have childSubtree : (dsub.children[digit]'digitLtChildren).decoratedSubtreeAt? path =
          some subtree' := by
        simpa [childIs] using childPath
      have viaChildTable : SparseSupportAlignment.HasAddress
          (table (fun node => node.atomicNumber) (dsub.children[digit]'digitLtChildren)) path :=
        (hasAddress_atomicNumber_table_iff_subtree slotPaired.2 path).2 ⟨subtree', childSubtree⟩
      simpa [← slotPaired.1.1, tables_rule1a] using viaChildTable
    rw [keysGet]
    change ((DeclarativeCIP.priorityValue rule (tableValue
        (OfficialSparseCanonicalVectorComparison.column key.constitutional rule)
        (digit :: path)) : ℤ) : WithBot ℤ) =
      OfficialSparseCanonicalVectorComparison.encodedObservation
        (sortedKeys[digit]'digitLtKeys).constitutional rule path
    unfold OfficialSparseCanonicalVectorComparison.encodedObservation
    rw [if_pos childGuard]
    congr 1
    congr 1
    have colEq : OfficialSparseCanonicalVectorComparison.column key.constitutional rule =
        table (armObservation rule) dsub := by
      cases rule with
      | rule1aAtomicNumber =>
          change key.constitutional.rule1a = table (fun node => node.atomicNumber) dsub
          simpa [tables_rule1a] using (tableMatch.1).symm
      | rule1bDuplicateNodeProximity =>
          change key.constitutional.rule1b = table (fun node => node.rule1bDistance) dsub
          simpa [tables_rule1b] using (tableMatch.2.1).symm
      | rule2AtomicMass =>
          change key.constitutional.rule2 = table (fun node => node.isotopeMass) dsub
          simpa [tables_rule2] using (tableMatch.2.2.1).symm
    have colEqChild : OfficialSparseCanonicalVectorComparison.column
        (sortedKeys[digit]'digitLtKeys).constitutional rule =
        table (armObservation rule) (dsub.children[digit]'digitLtChildren) := by
      cases rule with
      | rule1aAtomicNumber =>
          change (sortedKeys[digit]'digitLtKeys).constitutional.rule1a =
            table (fun node => node.atomicNumber) (dsub.children[digit]'digitLtChildren)
          simpa [tables_rule1a] using (slotPaired.1.1).symm
      | rule1bDuplicateNodeProximity =>
          change (sortedKeys[digit]'digitLtKeys).constitutional.rule1b =
            table (fun node => node.rule1bDistance) (dsub.children[digit]'digitLtChildren)
          simpa [tables_rule1b] using (slotPaired.1.2.1).symm
      | rule2AtomicMass =>
          change (sortedKeys[digit]'digitLtKeys).constitutional.rule2 =
            table (fun node => node.isotopeMass) (dsub.children[digit]'digitLtChildren)
          simpa [tables_rule2] using (slotPaired.1.2.2.1).symm
    rw [colEq, colEqChild]
    rw [tableValue_table_cons (armObservation rule) dsub digit path]
    rw [childGet, ← childIs]
    rfl
  · rw [if_neg hpresent]
    cases keysLookup : sortedKeys[digit]? with
    | none => rfl
    | some childKey =>
        have digitLtKeys : digit < sortedKeys.length := (List.getElem?_eq_some_iff.1 keysLookup).1
        have keysLength : sortedKeys.length = dsub.children.length := List.Forall₂.length_eq paired
        have digitLtChildren : digit < dsub.children.length := by simpa [keysLength] using digitLtKeys
        have childKeyEq : childKey = sortedKeys[digit]'digitLtKeys :=
          (Option.some.inj ((List.getElem?_eq_getElem digitLtKeys).symm.trans keysLookup)).symm
        have slotPaired : LocalizedCumulativeTreeTableMatch stage
            (dsub.children[digit]'digitLtChildren) (sortedKeys[digit]'digitLtKeys) ∧
            LocalizedCumulativeTreeRealizes input read (dsub.children[digit]'digitLtChildren) :=
          List.Forall₂.get (i := digit) paired digitLtKeys digitLtChildren
        have childAbsent : ¬ SparseSupportAlignment.HasAddress childKey.constitutional.rule1a path := by
          intro present
          have viaChildTable : SparseSupportAlignment.HasAddress
              (table (fun node => node.atomicNumber) (dsub.children[digit]'digitLtChildren)) path := by
            simpa [← slotPaired.1.1, tables_rule1a, childKeyEq] using present
          obtain ⟨subtree, childPath⟩ :=
            (hasAddress_atomicNumber_table_iff_subtree slotPaired.2 path).1 viaChildTable
          have parentSub : ∃ subtree, dsub.decoratedSubtreeAt? (digit :: path) = some subtree :=
            (decoratedSubtreeAt?_cons_some dsub digit path).2
              ⟨dsub.children[digit]'digitLtChildren, subtree,
                List.getElem?_eq_getElem digitLtChildren, childPath⟩
          have guardTable : SparseSupportAlignment.HasAddress
              (table (fun node => node.atomicNumber) dsub) (digit :: path) :=
            (hasAddress_atomicNumber_table_iff_subtree realizes (digit :: path)).2 parentSub
          exact hpresent (by simpa [← tableMatch.1, tables_rule1a] using guardTable)
        change ⊥ = OfficialSparseCanonicalVectorComparison.encodedObservation
          childKey.constitutional rule path
        unfold OfficialSparseCanonicalVectorComparison.encodedObservation
        rw [if_neg childAbsent]

/-! ## Recursive trace extraction, the actual-to-independent bridge, canonicality and comparison -/

/-- **Recursive trace extraction.**  Every decorated subtree reached from a traced tree at one
ranked sibling address is again traced, at the fuel left over after the descent.  The proof is by
induction on the trace fuel: the root case replays the same trace, and each cons step descends
through the stored sorted child selected at the slot, whose trace is exposed by the `Forall₂`
pairing of the trace list certificate. -/
theorem trace_of_subtree (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    {fuel : Nat} {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedActualRecursiveSortTrace input stage read fuel tree key) :
    ∀ (path : List ℕ) (subtree : LocalizedCumulativeDecoratedTree input carrierFuel),
      tree.decoratedSubtreeAt? path = some subtree →
        ∃ (fuel' : Nat) (key' : input.LocalizedRerootCumulativeRule45Key),
          LocalizedActualRecursiveSortTrace input stage read fuel' subtree key' := by
  induction fuel generalizing tree key with
  | zero =>
      intro path subtree lookup
      cases path with
      | nil =>
          rw [decoratedSubtreeAt?] at lookup
          have same : tree = subtree := Option.some.inj lookup
          subst subtree
          exact ⟨0, key, trace⟩
      | cons _slot _path =>
          cases trace with
          | terminal _fuel cursor _children _childrenComputed _terminalChildren _fullMatch
              _realizes =>
              have childrenEq : (localizedRootTree input cursor (read cursor) []).children = [] :=
                by unfold localizedRootTree; rfl
              rw [decoratedSubtreeAt?] at lookup
              simp [childrenEq] at lookup
  | succ fuel ih =>
      intro path subtree lookup
      cases path with
      | nil =>
          rw [decoratedSubtreeAt?] at lookup
          have same : tree = subtree := Option.some.inj lookup
          subst subtree
          exact ⟨fuel + 1, key, trace⟩
      | cons slot path' =>
          cases trace with
          | terminal _fuel cursor _children _childrenComputed _terminalChildren _fullMatch
              _realizes =>
              have childrenEq : (localizedRootTree input cursor (read cursor) []).children = [] :=
                by unfold localizedRootTree; rfl
              rw [decoratedSubtreeAt?] at lookup
              simp [childrenEq] at lookup
          | node _fuel cursor children childKeys sortedKeys sortedTrees childrenComputed nonempty
              childKeysComputed sortedEq constitutionalDescending fullMatch realizes childrenTraced =>
              have childrenEq : (localizedRootTree input cursor (read cursor) sortedTrees).children =
                  sortedTrees := by
                unfold localizedRootTree; rfl
              rw [decoratedSubtreeAt?] at lookup
              cases slotLookup : sortedTrees[slot]? with
              | none => simp [childrenEq, slotLookup] at lookup
              | some child =>
                  simp [childrenEq, slotLookup] at lookup
                  have paired := LocalizedActualRecursiveSortTraceList.to_forall₂ childrenTraced
                  have slotLtTrees : slot < sortedTrees.length :=
                    (List.getElem?_eq_some_iff.1 slotLookup).1
                  have lengthEq : sortedKeys.length = sortedTrees.length :=
                    List.Forall₂.length_eq paired
                  have slotLtKeys : slot < sortedKeys.length := by
                    simpa [lengthEq] using slotLtTrees
                  have childTrace : LocalizedActualRecursiveSortTrace input stage read fuel
                      (sortedTrees[slot]'slotLtTrees) (sortedKeys[slot]'slotLtKeys) :=
                    List.Forall₂.get (i := slot) paired slotLtKeys slotLtTrees
                  have childEq : sortedTrees[slot]'slotLtTrees = child :=
                    Option.some.inj ((List.getElem?_eq_getElem slotLtTrees).symm.trans slotLookup)
                  have childLookup : (sortedTrees[slot]'slotLtTrees).decoratedSubtreeAt? path' =
                      some subtree := by
                    simpa [childEq] using lookup
                  exact ih (tree := sortedTrees[slot]'slotLtTrees)
                    (key := sortedKeys[slot]'slotLtKeys) childTrace path' subtree childLookup

namespace OriginalRootArm

/-- The declarative digraph of an arm: the ranked-sibling hierarchy of the arm's erased actual
source tree, the one fixed graph throughout the bridge. -/
abbrev armGraph {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
    {index : Fin 4} {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index stage read) : DeclarativeCIP.RootedDigraph input.Atom :=
  (toOfficialSourceTree arm.tree).toDeclarativeDigraph

/-- Every declarative node of the arm graph resolves to a decorated subtree of the arm's own tree,
and its erasure is exactly the erased subtree at the node's address. -/
theorem decoratedSubtree_of_node
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index stage read) (node : (armGraph arm).Node) :
    ∃ dsub : LocalizedCumulativeDecoratedTree input
        (input.certified.input.molecule.atomCount + 1),
      arm.tree.decoratedSubtreeAt? node.1 = some dsub ∧
        (toOfficialSourceTree arm.tree).subtreeAt? node.1 = some (toOfficialSourceTree dsub) := by
  obtain ⟨subtree, lookup⟩ :=
    (toOfficialSourceTree arm.tree).exists_subtreeAt?_eq_some_of_mem_hierarchyAddresses
      node.1 node.2
  have erasedLookup : (arm.tree.decoratedSubtreeAt? node.1).map toOfficialSourceTree =
      some subtree :=
    (lookup.symm.trans (toOfficialSourceTree_subtreeAt? arm.tree node.1)).symm
  obtain ⟨dsub, decLookup, dsubEq⟩ := Option.map_eq_some_iff.mp erasedLookup
  exact ⟨dsub, decLookup, by rw [lookup, ← dsubEq]⟩

/-- **Density at a resolved node.**  Below an arm-graph node that resolves to the decorated
subtree `dsub`, the occupied sibling slots are exactly the indices below `dsub.children.length`:
the erased lookup at `parent ++ [slot]` descends through the stored child merge, and every stored
child produces the corresponding hierarchy occurrence. -/
theorem denseAt_of_lookup
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index stage read) (node : (armGraph arm).Node)
    (dsub : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1))
    (lookup : arm.tree.decoratedSubtreeAt? node.1 = some dsub) :
    DeclarativeCIP.DenseAt (toOfficialSourceTree arm.tree).declarativeAddressing node
      dsub.children.length := by
  have erasedLookup : (toOfficialSourceTree arm.tree).subtreeAt? node.1 =
      some (toOfficialSourceTree dsub) := by
    rw [toOfficialSourceTree_subtreeAt? arm.tree node.1, lookup]
    rfl
  intro slot
  constructor
  · intro present
    obtain ⟨child, addressEq⟩ := present
    have childAddr : child.1 = node.1 ++ [slot] := by
      rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address child,
        (toOfficialSourceTree arm.tree).declarativeAddressing_address node] at addressEq
      exact addressEq
    have childPresent : node.1 ++ [slot] ∈ (toOfficialSourceTree arm.tree).hierarchyAddresses := by
      simpa [childAddr] using child.2
    obtain ⟨childSubtree, childLookup⟩ :=
      (toOfficialSourceTree arm.tree).exists_subtreeAt?_eq_some_of_mem_hierarchyAddresses
        (node.1 ++ [slot]) childPresent
    have childWithin : (toOfficialSourceTree dsub).subtreeAt? [slot] = some childSubtree := by
      rw [(toOfficialSourceTree arm.tree).subtreeAt?_append, erasedLookup] at childLookup
      simpa using childLookup
    have decoratedWithin : (dsub.decoratedSubtreeAt? [slot]).map toOfficialSourceTree =
        some childSubtree := by
      simpa [toOfficialSourceTree_subtreeAt? dsub [slot]] using childWithin
    obtain ⟨dchild, dLookup, _⟩ := Option.map_eq_some_iff.mp decoratedWithin
    rw [decoratedSubtreeAt?] at dLookup
    cases slotLookup : dsub.children[slot]? with
    | none => simp [slotLookup] at dLookup
    | some child =>
        simp [slotLookup, decoratedSubtreeAt?] at dLookup
        exact (List.getElem?_eq_some_iff.1 slotLookup).1
  · intro slotLt
    have childLookup : (toOfficialSourceTree dsub).subtreeAt? [slot] =
        some (toOfficialSourceTree (dsub.children[slot]'slotLt)) := by
      rw [toOfficialSourceTree_subtreeAt? dsub [slot]]
      simp [decoratedSubtreeAt?, List.getElem?_eq_getElem slotLt]
    have fullLookup : (toOfficialSourceTree arm.tree).subtreeAt? (node.1 ++ [slot]) =
        some (toOfficialSourceTree (dsub.children[slot]'slotLt)) := by
      rw [(toOfficialSourceTree arm.tree).subtreeAt?_append, erasedLookup]
      simpa using childLookup
    have occurrence : (node.1 ++ [slot],
        (toOfficialSourceTree (dsub.children[slot]'slotLt)).source) ∈
        (toOfficialSourceTree arm.tree).occurrences :=
      OfficialCIPSourceTree.mem_occurrences_of_subtreeAt?_eq_some (node.1 ++ [slot])
        (toOfficialSourceTree arm.tree) (toOfficialSourceTree (dsub.children[slot]'slotLt))
        fullLookup
    have membership : node.1 ++ [slot] ∈ (toOfficialSourceTree arm.tree).hierarchyAddresses :=
      (toOfficialSourceTree arm.tree).mem_hierarchyAddresses_of_occurrence
        ⟨node.1 ++ [slot], (toOfficialSourceTree (dsub.children[slot]'slotLt)).source⟩ occurrence
    exact ⟨⟨node.1 ++ [slot], membership⟩, by
      simp [(toOfficialSourceTree arm.tree).declarativeAddressing_address
          ⟨node.1 ++ [slot], membership⟩,
        (toOfficialSourceTree arm.tree).declarativeAddressing_address node]⟩

/-- The actual key's column read at a resolved node's address equals the observation of the
decorated subtree at that address, for every constitutional rule. -/
theorem armTableValue_eq_armObservation
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index stage read) (rule : DeclarativeCIP.ConstitutionalRule)
    (node : (armGraph arm).Node)
    (dsub : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1))
    (lookup : arm.tree.decoratedSubtreeAt? node.1 = some dsub) :
    tableValue (armTableColumn arm.key rule) node.1 = armObservation rule dsub := by
  cases rule with
  | rule1aAtomicNumber =>
      have match1a : table (fun node => node.atomicNumber) arm.tree =
          arm.key.constitutional.rule1a := by
        simpa [LocalizedCumulativeTreeTableMatch, tables_rule1a] using arm.tableMatch.1
      calc
        tableValue (armTableColumn arm.key .rule1aAtomicNumber) node.1 =
            tableValue arm.key.constitutional.rule1a node.1 := rfl
        _ = tableValue (table (fun node => node.atomicNumber) arm.tree) node.1 := by
            rw [← match1a]
        _ = observeAt (fun node => node.atomicNumber) arm.tree node.1 := by
            rw [tableValue_table_eq_observeAt]
        _ = armObservation .rule1aAtomicNumber dsub := by
            rw [observeAt, lookup]
            rfl
  | rule1bDuplicateNodeProximity =>
      have match1b : table (fun node => node.rule1bDistance) arm.tree =
          arm.key.constitutional.rule1b := by
        simpa [LocalizedCumulativeTreeTableMatch, tables_rule1b] using arm.tableMatch.2.1
      calc
        tableValue (armTableColumn arm.key .rule1bDuplicateNodeProximity) node.1 =
            tableValue arm.key.constitutional.rule1b node.1 := rfl
        _ = tableValue (table (fun node => node.rule1bDistance) arm.tree) node.1 := by
            rw [← match1b]
        _ = observeAt (fun node => node.rule1bDistance) arm.tree node.1 := by
            rw [tableValue_table_eq_observeAt]
        _ = armObservation .rule1bDuplicateNodeProximity dsub := by
            rw [observeAt, lookup]
            rfl
  | rule2AtomicMass =>
      have match2 : table (fun node => node.isotopeMass) arm.tree =
          arm.key.constitutional.rule2 := by
        simpa [LocalizedCumulativeTreeTableMatch, tables_rule2] using arm.tableMatch.2.2.1
      calc
        tableValue (armTableColumn arm.key .rule2AtomicMass) node.1 =
            tableValue arm.key.constitutional.rule2 node.1 := rfl
        _ = tableValue (table (fun node => node.isotopeMass) arm.tree) node.1 := by
            rw [← match2]
        _ = observeAt (fun node => node.isotopeMass) arm.tree node.1 := by
            rw [tableValue_table_eq_observeAt]
        _ = armObservation .rule2AtomicMass dsub := by
            rw [observeAt, lookup]
            rfl

/-- **Node observation correspondence at a resolved subtree.**  At a node resolving to the
decorated subtree `dsub`, the independent `nodeObservation` equals the priority-oriented reading of
`dsub`'s own observation: the all-address readback theorem reduces it to the actual table reading,
which the previous theorem identifies with the decorated observation. -/
theorem nodeObservation_eq_priorityValue_armObservation
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index stage read) (rule : DeclarativeCIP.ConstitutionalRule)
    (node : (armGraph arm).Node)
    (dsub : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1))
    (lookup : arm.tree.decoratedSubtreeAt? node.1 = some dsub) :
    DeclarativeCIP.nodeObservation input.moleculeGraph (armGraph arm) rule node =
      DeclarativeCIP.priorityValue rule (armObservation rule dsub) := by
  rw [nodeObservation_eq_actualTableValue arm rule node,
    armTableValue_eq_armObservation arm rule node dsub lookup]

/-! ## Recursive actual-key / independent-vector-key bridge at one fixed original-arm graph -/

/-- **Single-node observation readback at the empty path.**  At a node of the arm graph resolving
to a decorated subtree `dsub` matched by an actual key, the independent `nodePathObservation` at the
empty path equals the encoded observation of the actual key at `[]`: Rule-1a support at the root
address is present, the `nodeObservation` readback reduces it to the priority-oriented decorated
observation, and the column readback identifies the encoded value with the same observation. -/
theorem arm_nil_observation
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index stage read)
    {W D : ℕ} (node : (armGraph arm).Node)
    (dsub : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1))
    (key : input.LocalizedRerootCumulativeRule45Key)
    (tableMatch : LocalizedCumulativeTreeTableMatch stage dsub key)
    (realizes : LocalizedCumulativeTreeRealizes input read dsub)
    (lookup : arm.tree.decoratedSubtreeAt? node.1 = some dsub)
    {r : ℕ} (hr : r < 3) :
    DeclarativeCIP.nodePathObservation input.moleculeGraph (armGraph arm) W D r node [] =
      OfficialSparseCanonicalVectorComparison.encodedObservation key.constitutional
        (DeclarativeCIP.ruleOfIndex r) [] := by
  rw [DeclarativeCIP.nodePathObservation_nil input.moleculeGraph (armGraph arm) hr]
  unfold OfficialSparseCanonicalVectorComparison.encodedObservation
  have hpresent : SparseSupportAlignment.HasAddress key.constitutional.rule1a [] := by
    have viaTable : SparseSupportAlignment.HasAddress
        (table (fun node => node.atomicNumber) dsub) [] :=
      (hasAddress_atomicNumber_table_iff_subtree realizes []).2 ⟨dsub, rfl⟩
    simpa [← tableMatch.1, tables_rule1a] using viaTable
  rw [if_pos hpresent]
  rw [nodeObservation_eq_priorityValue_armObservation arm (DeclarativeCIP.ruleOfIndex r) node dsub
    lookup]
  have colEq : OfficialSparseCanonicalVectorComparison.column key.constitutional
      (DeclarativeCIP.ruleOfIndex r) =
      table (armObservation (DeclarativeCIP.ruleOfIndex r)) dsub := by
    interval_cases r
    · change key.constitutional.rule1a = table (fun node => node.atomicNumber) dsub
      simpa [tables_rule1a] using (tableMatch.1).symm
    · change key.constitutional.rule1b = table (fun node => node.rule1bDistance) dsub
      simpa [tables_rule1b] using (tableMatch.2.1).symm
    · change key.constitutional.rule2 = table (fun node => node.isotopeMass) dsub
      simpa [tables_rule2] using (tableMatch.2.2.1).symm
  rw [colEq, tableValue_table_eq_observeAt (armObservation (DeclarativeCIP.ruleOfIndex r)) dsub []]
  change ((DeclarativeCIP.priorityValue (DeclarativeCIP.ruleOfIndex r)
      (armObservation (DeclarativeCIP.ruleOfIndex r) dsub) : ℤ) : WithBot ℤ) =
    ((DeclarativeCIP.priorityValue (DeclarativeCIP.ruleOfIndex r)
      (armObservation (DeclarativeCIP.ruleOfIndex r) dsub) : ℤ) : WithBot ℤ)
  rfl

/-- **Terminal bridge.**  At a node of the arm graph resolving to a root-only decorated tree
(`children = []`) matched by the terminal actual key, the occupied sibling slots are the empty list
(so the slot list is pairwise trivially ordered) and the terminal key is represented by the
independent vector key: the empty path reads back through `arm_nil_observation`, and every cons
path is absent on both sides — the encoded cons readback with the empty sorted-key pairing is `⊥`,
while the vector side is `⊥` by the empty slot list and the layout gate. -/
theorem arm_terminal_bridge
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index stage read)
    (cursor : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (fullMatch : LocalizedCumulativeTreeFullMatch stage
      (localizedRootTree input cursor (read cursor) [])
      (localizedCumulativeRule45TerminalKey input stage cursor (read cursor)))
    (realizes : LocalizedCumulativeTreeRealizes input read
      (localizedRootTree input cursor (read cursor) []))
    {W D : ℕ} (node : (armGraph arm).Node)
    (lookup : arm.tree.decoratedSubtreeAt? node.1 =
      some (localizedRootTree input cursor (read cursor) [])) :
    (((DeclarativeCIP.slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
          (localizedRootTree input cursor (read cursor) []).children.length).map
        (DeclarativeCIP.ruleKey input.moleculeGraph (armGraph arm) W D)).Pairwise
      fun x y => y ≤ x) ∧
      OfficialSparseCanonicalVectorComparison.Represents W D
        (DeclarativeCIP.ruleKey input.moleculeGraph (armGraph arm) W D node)
        (localizedCumulativeRule45TerminalKey input stage cursor (read cursor)).constitutional := by
  have slotKeySorted : ((DeclarativeCIP.slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
        (localizedRootTree input cursor (read cursor) []).children.length).map
      (DeclarativeCIP.ruleKey input.moleculeGraph (armGraph arm) W D)).Pairwise
      fun x y => y ≤ x := by
    simp [DeclarativeCIP.slotList]
    exact List.Pairwise.nil
  constructor
  · exact slotKeySorted
  · unfold OfficialSparseCanonicalVectorComparison.Represents
    intro r hr path
    cases path with
    | nil =>
        exact arm_nil_observation arm (W := W) (D := D) node
          (localizedRootTree input cursor (read cursor) [])
          (localizedCumulativeRule45TerminalKey input stage cursor (read cursor))
          fullMatch.tableMatch realizes lookup hr
    | cons digit path =>
        change DeclarativeCIP.nodePathObservation input.moleculeGraph (armGraph arm) W D r node
            (digit :: path) =
          OfficialSparseCanonicalVectorComparison.encodedObservation
            (localizedCumulativeRule45TerminalKey input stage cursor (read cursor)).constitutional
            (DeclarativeCIP.ruleOfIndex r) (digit :: path)
        have hdense : DeclarativeCIP.DenseAt (toOfficialSourceTree arm.tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) []).children.length :=
          denseAt_of_lookup arm node (localizedRootTree input cursor (read cursor) []) lookup
        rw [DeclarativeCIP.nodePathObservation_cons input.moleculeGraph (armGraph arm) hr node
          (ranked := DeclarativeCIP.slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) []).children.length)
          (DeclarativeCIP.slotList_perm (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing)
            (parent := node)
            (count := (localizedRootTree input cursor (read cursor) []).children.length) hdense)
          slotKeySorted digit path]
        rw [encodedObservation_cons_of_key fullMatch.tableMatch realizes (sortedKeys := [])
          List.Forall₂.nil (DeclarativeCIP.ruleOfIndex r) digit path]
        have childrenEq : (localizedRootTree input cursor (read cursor) []).children = [] :=
          by unfold localizedRootTree; rfl
        by_cases hgate : digit < W ∧ path.length < D
        · rw [if_pos hgate]
          simp [childrenEq, DeclarativeCIP.slotList]
        · rw [if_neg hgate]
          simp














theorem arm_node_bridge
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index stage read)
    {W D : ℕ} (hW : (armGraph arm).width ≤ W) (hD : (armGraph arm).height ≤ D)
    {fuel : Nat} (node : (armGraph arm).Node)
    (dsub : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1))
    (key : input.LocalizedRerootCumulativeRule45Key)
    (trace : LocalizedActualRecursiveSortTrace input stage read fuel dsub key)
    (lookup : arm.tree.decoratedSubtreeAt? node.1 = some dsub) :
    (((DeclarativeCIP.slotList (toOfficialSourceTree arm.tree).declarativeAddressing node dsub.children.length).map
        (DeclarativeCIP.ruleKey input.moleculeGraph (armGraph arm) W D)).Pairwise
      fun x y => y ≤ x) ∧
      OfficialSparseCanonicalVectorComparison.Represents W D
        (DeclarativeCIP.ruleKey input.moleculeGraph (armGraph arm) W D node) key.constitutional := by
  induction fuel generalizing dsub key node lookup with
  | zero =>
      cases trace with
      | terminal _fuel cursor _children _childrenComputed _terminalChildren fullMatch realizes =>
          exact arm_terminal_bridge arm cursor fullMatch realizes (W := W) (D := D) node lookup
  | succ fuel ih =>
      have fullMatch := LocalizedActualRecursiveSortTrace.fullMatch_of_trace trace
      have realizes := LocalizedActualRecursiveSortTrace.realizes_of_trace trace
      rcases LocalizedActualRecursiveSortTrace.structure_of_trace trace with
        ⟨cursor, _children, dsubEq, keyEq, _childrenEq, _childrenComputed, _terminalChildren⟩ |
        ⟨cursor, _children, _childKeys, sortedKeys, sortedTrees, dsubEq, keyEq, childrenEq,
          _childrenComputed, _nonempty, _childKeysComputed, _sortedEq, constitutionalDescending,
          childrenTraced⟩
      · subst dsub
        subst key
        exact arm_terminal_bridge arm cursor fullMatch realizes (W := W) (D := D) node lookup
      · subst dsub
        subst key
        have hdense : DeclarativeCIP.DenseAt (toOfficialSourceTree arm.tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length :=
          denseAt_of_lookup arm node (localizedRootTree input cursor (read cursor) sortedTrees)
            lookup
        have paired := LocalizedActualRecursiveSortTraceList.to_forall₂ childrenTraced
        have lengthEq : sortedKeys.length = sortedTrees.length := List.Forall₂.length_eq paired
        have slotKeySorted : ((DeclarativeCIP.slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length).map
            (DeclarativeCIP.ruleKey input.moleculeGraph (armGraph arm) W D)).Pairwise
            fun x y => y ≤ x := by
          rw [List.pairwise_iff_getElem]
          intro i j hi hj hij
          have iLtCount : i < sortedTrees.length := by
            simpa [DeclarativeCIP.slotList] using hi
          have jLtCount : j < sortedTrees.length := by
            simpa [DeclarativeCIP.slotList] using hj
          have iLtSlot : i < (DeclarativeCIP.slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length).length := by
            simpa [DeclarativeCIP.slotList] using iLtCount
          have jLtSlot : j < (DeclarativeCIP.slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length).length := by
            simpa [DeclarativeCIP.slotList] using jLtCount
          obtain ⟨childI, slotI, addrI⟩ := DeclarativeCIP.slotList_getD_of_lt
            (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing) (parent := node)
            (count := (localizedRootTree input cursor (read cursor) sortedTrees).children.length)
            hdense iLtCount
          obtain ⟨childJ, slotJ, addrJ⟩ := DeclarativeCIP.slotList_getD_of_lt
            (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing) (parent := node)
            (count := (localizedRootTree input cursor (read cursor) sortedTrees).children.length)
            hdense jLtCount
          have slotIEq : (DeclarativeCIP.slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[i]'iLtSlot =
              childI :=
            Option.some.inj ((List.getElem?_eq_getElem iLtSlot).symm.trans slotI)
          have slotJEq : (DeclarativeCIP.slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[j]'jLtSlot =
              childJ :=
            Option.some.inj ((List.getElem?_eq_getElem jLtSlot).symm.trans slotJ)
          have addrIFlat : childI.1 = node.1 ++ [i] := by
            rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address childI,
              (toOfficialSourceTree arm.tree).declarativeAddressing_address node] at addrI
            exact addrI
          have addrJFlat : childJ.1 = node.1 ++ [j] := by
            rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address childJ,
              (toOfficialSourceTree arm.tree).declarativeAddressing_address node] at addrJ
            exact addrJ
          have childLookupAtI : arm.tree.decoratedSubtreeAt? (node.1 ++ [i]) =
              some (sortedTrees[i]'iLtCount) := by
            rw [decoratedSubtreeAt?_append arm.tree node.1 [i], lookup]
            simp [childrenEq, decoratedSubtreeAt?, List.getElem?_eq_getElem iLtCount]
          have childLookupAtJ : arm.tree.decoratedSubtreeAt? (node.1 ++ [j]) =
              some (sortedTrees[j]'jLtCount) := by
            rw [decoratedSubtreeAt?_append arm.tree node.1 [j], lookup]
            simp [childrenEq, decoratedSubtreeAt?, List.getElem?_eq_getElem jLtCount]
          have childLookupAtISorted : arm.tree.decoratedSubtreeAt? childI.1 =
              some (sortedTrees[i]'iLtCount) := by
            rw [addrIFlat]
            exact childLookupAtI
          have childLookupAtJSorted : arm.tree.decoratedSubtreeAt? childJ.1 =
              some (sortedTrees[j]'jLtCount) := by
            rw [addrJFlat]
            exact childLookupAtJ
          have iLtKeys : i < sortedKeys.length := by simpa [lengthEq] using iLtCount
          have jLtKeys : j < sortedKeys.length := by simpa [lengthEq] using jLtCount
          have childTraceI : LocalizedActualRecursiveSortTrace input stage read fuel
              (sortedTrees[i]'iLtCount) (sortedKeys[i]'iLtKeys) :=
            List.Forall₂.get (i := i) paired iLtKeys iLtCount
          have childTraceJ : LocalizedActualRecursiveSortTrace input stage read fuel
              (sortedTrees[j]'jLtCount) (sortedKeys[j]'jLtKeys) :=
            List.Forall₂.get (i := j) paired jLtKeys jLtCount
          have ihI := ih (dsub := sortedTrees[i]'iLtCount) (key := sortedKeys[i]'iLtKeys)
            (node := childI) (lookup := childLookupAtISorted) childTraceI
          have ihJ := ih (dsub := sortedTrees[j]'jLtCount) (key := sortedKeys[j]'jLtKeys)
            (node := childJ) (lookup := childLookupAtJSorted) childTraceJ
          have ihRepI : OfficialSparseCanonicalVectorComparison.Represents W D
              (DeclarativeCIP.ruleKey input.moleculeGraph (armGraph arm) W D childI)
              (sortedKeys[i]'iLtKeys).constitutional := ihI.2
          have ihRepJ : OfficialSparseCanonicalVectorComparison.Represents W D
              (DeclarativeCIP.ruleKey input.moleculeGraph (armGraph arm) W D childJ)
              (sortedKeys[j]'jLtKeys).constitutional := ihJ.2
          have actualNe : OfficialRuleMajorKey.compare (sortedKeys[i]'iLtKeys).constitutional
              (sortedKeys[j]'jLtKeys).constitutional ≠ Ordering.lt := by
            have hne := (List.pairwise_iff_getElem.1 constitutionalDescending) i j
              (by simpa [lengthEq, List.length_map] using iLtCount)
              (by simpa [lengthEq, List.length_map] using jLtCount) hij
            simpa [List.getElem_map] using hne
          have hle : DeclarativeCIP.ruleKey input.moleculeGraph (armGraph arm) W D childJ ≤
              DeclarativeCIP.ruleKey input.moleculeGraph (armGraph arm) W D childI :=
            (OfficialSparseCanonicalVectorComparison.compare_ne_lt_iff_rightVector_le
              (leftWellFormed := wellFormedRuleMajorKey_of_tableMatch
                (LocalizedActualRecursiveSortTrace.fullMatch_of_trace childTraceI).tableMatch
                (LocalizedActualRecursiveSortTrace.realizes_of_trace childTraceI))
              (rightWellFormed := wellFormedRuleMajorKey_of_tableMatch
                (LocalizedActualRecursiveSortTrace.fullMatch_of_trace childTraceJ).tableMatch
                (LocalizedActualRecursiveSortTrace.realizes_of_trace childTraceJ))
              (leftShaped := DeclarativeCIP.ruleKey_vectorWellShaped input.moleculeGraph
                (armGraph arm) W D childI)
              (rightShaped := DeclarativeCIP.ruleKey_vectorWellShaped input.moleculeGraph
                (armGraph arm) W D childJ)
              (leftRepresents := ihRepI) (rightRepresents := ihRepJ)).1 actualNe
          simpa [List.getElem_map, slotIEq, slotJEq] using hle
        constructor
        · exact slotKeySorted
        · unfold OfficialSparseCanonicalVectorComparison.Represents
          intro r hr path
          cases path with
          | nil =>
              exact arm_nil_observation arm (W := W) (D := D) node
                (localizedRootTree input cursor (read cursor) sortedTrees)
                (localizedCumulativeRule45StepKey input stage cursor (read cursor) sortedKeys)
                fullMatch.tableMatch realizes lookup hr
          | cons digit path =>
              change DeclarativeCIP.nodePathObservation input.moleculeGraph (armGraph arm) W D r
                  node (digit :: path) =
                OfficialSparseCanonicalVectorComparison.encodedObservation
                  (localizedCumulativeRule45StepKey input stage cursor (read cursor)
                    sortedKeys).constitutional
                  (DeclarativeCIP.ruleOfIndex r) (digit :: path)
              have pairedMatch : List.Forall₂ (fun childKey childTree =>
                  LocalizedCumulativeTreeTableMatch stage childTree childKey ∧
                    LocalizedCumulativeTreeRealizes input read childTree) sortedKeys sortedTrees :=
                List.Forall₂.imp (fun childKey childTree related =>
                  ⟨(LocalizedActualRecursiveSortTrace.fullMatch_of_trace related).tableMatch,
                    LocalizedActualRecursiveSortTrace.realizes_of_trace related⟩)
                  (LocalizedActualRecursiveSortTraceList.to_forall₂ childrenTraced)
              rw [DeclarativeCIP.nodePathObservation_cons input.moleculeGraph (armGraph arm) hr node
                (ranked := DeclarativeCIP.slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
                  (localizedRootTree input cursor (read cursor) sortedTrees).children.length)
                (DeclarativeCIP.slotList_perm (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing)
                  (parent := node)
                  (count := (localizedRootTree input cursor (read cursor)
                    sortedTrees).children.length) hdense) slotKeySorted digit path]
              rw [encodedObservation_cons_of_key fullMatch.tableMatch realizes
                (sortedKeys := sortedKeys) pairedMatch (DeclarativeCIP.ruleOfIndex r) digit path]
              by_cases hdigit : digit < sortedTrees.length
              · have digitLtSlot : digit < (DeclarativeCIP.slotList
                    (toOfficialSourceTree arm.tree).declarativeAddressing node
                    (localizedRootTree input cursor (read cursor) sortedTrees).children.length).length := by
                  simpa [DeclarativeCIP.slotList] using hdigit
                obtain ⟨child, slotSome, childAddr⟩ := DeclarativeCIP.slotList_getD_of_lt
                  (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing) (parent := node)
                  (count := (localizedRootTree input cursor (read cursor) sortedTrees).children.length)
                  hdense hdigit
                have childAddrFlat : child.1 = node.1 ++ [digit] := by
                  rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address child,
                    (toOfficialSourceTree arm.tree).declarativeAddressing_address node] at childAddr
                  exact childAddr
                have childLookupAt : arm.tree.decoratedSubtreeAt? (node.1 ++ [digit]) =
                    some (sortedTrees[digit]'hdigit) := by
                  rw [decoratedSubtreeAt?_append arm.tree node.1 [digit], lookup]
                  simp [childrenEq, decoratedSubtreeAt?, List.getElem?_eq_getElem hdigit]
                have childLookupAtSorted : arm.tree.decoratedSubtreeAt? child.1 =
                    some (sortedTrees[digit]'hdigit) := by
                  rw [childAddrFlat]
                  exact childLookupAt
                have digitLtKeys : digit < sortedKeys.length := by simpa [lengthEq] using hdigit
                have childTrace : LocalizedActualRecursiveSortTrace input stage read fuel
                    (sortedTrees[digit]'hdigit) (sortedKeys[digit]'digitLtKeys) :=
                  List.Forall₂.get (i := digit) paired digitLtKeys hdigit
                have ihChild := ih (dsub := sortedTrees[digit]'hdigit)
                  (key := sortedKeys[digit]'digitLtKeys) (node := child)
                  (lookup := childLookupAtSorted) childTrace
                have ihRepChild : OfficialSparseCanonicalVectorComparison.Represents W D
                    (DeclarativeCIP.ruleKey input.moleculeGraph (armGraph arm) W D child)
                    (sortedKeys[digit]'digitLtKeys).constitutional := ihChild.2
                by_cases hgate : digit < W ∧ path.length < D
                · rw [if_pos hgate]
                  simp [slotSome]
                  rw [List.getElem?_eq_getElem digitLtKeys]
                  simp
                  exact ihRepChild r hr path
                · rw [if_neg hgate]
                  have childObsBot : DeclarativeCIP.nodePathObservation input.moleculeGraph
                      (armGraph arm) W D r child path = ⊥ := by
                    by_contra hne
                    have bound := DeclarativeCIP.depth_add_length_le_of_nodePathObservation
                      input.moleculeGraph (armGraph arm) hr path child hne
                    have childDepth : (armGraph arm).depth child =
                        (armGraph arm).depth node + 1 :=
                      (armGraph arm).child_depth ⟨digit, childAddrFlat⟩
                    have hdigitLtW : digit < W := by
                      have countLeWidth := DeclarativeCIP.count_le_width
                        (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing) (parent := node)
                        (count := (localizedRootTree input cursor (read cursor)
                          sortedTrees).children.length) hdense
                      have countLeWidth' : sortedTrees.length ≤ (armGraph arm).width := by
                        simpa using countLeWidth
                      omega
                    have hpathNotLt : ¬ path.length < D := by
                      intro hlt
                      exact hgate ⟨hdigitLtW, hlt⟩
                    have hpathGe : D ≤ path.length := Nat.le_of_not_gt hpathNotLt
                    omega
                  rw [List.getElem?_eq_getElem digitLtKeys]
                  simp
                  rw [(ihRepChild r hr path).symm]
                  exact childObsBot.symm
              · have hdigitGe : sortedTrees.length ≤ digit := Nat.le_of_not_gt hdigit
                have hslotGe : (DeclarativeCIP.slotList
                    (toOfficialSourceTree arm.tree).declarativeAddressing node
                    (localizedRootTree input cursor (read cursor) sortedTrees).children.length).length ≤
                    digit := by
                  simpa [childrenEq, DeclarativeCIP.slotList] using hdigitGe
                have hkeyGe : sortedKeys.length ≤ digit := by
                  omega
                by_cases hgate : digit < W ∧ path.length < D
                · rw [if_pos hgate]
                  rw [List.getElem?_eq_none hslotGe]
                  rw [List.getElem?_eq_none hkeyGe]
                  simp
                · rw [if_neg hgate]
                  rw [List.getElem?_eq_none hkeyGe]
                  simp





theorem arm_root_represents
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index stage read) :
    OfficialSparseCanonicalVectorComparison.Represents (armGraph arm).width (armGraph arm).height
      (DeclarativeCIP.ruleKey input.moleculeGraph (armGraph arm) (armGraph arm).width
        (armGraph arm).height (armGraph arm).root)
      arm.key.constitutional :=
  (arm_node_bridge arm (W := (armGraph arm).width) (D := (armGraph arm).height)
    (hW := le_rfl) (hD := le_rfl) (node := (armGraph arm).root) (dsub := arm.tree)
    (key := arm.key) arm.trace (by
      change arm.tree.decoratedSubtreeAt? [] = some arm.tree
      rw [decoratedSubtreeAt?])).2









theorem arm_canonicalAddressing
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index stage read) :
    DeclarativeCIP.CanonicalAddressing input.moleculeGraph
      (toOfficialSourceTree arm.tree).declarativeAddressing := by
  constructor
  · exact (toOfficialSourceTree arm.tree).declarativeAddressing_dense
  · intro parent first second firstSlot secondSlot addrFirst addrSecond hlt
    obtain ⟨dsub, lookup, _⟩ := decoratedSubtree_of_node arm parent
    have hdense : DeclarativeCIP.DenseAt (toOfficialSourceTree arm.tree).declarativeAddressing
        parent dsub.children.length := denseAt_of_lookup arm parent dsub lookup
    rcases trace_of_subtree input stage read arm.trace parent.1 dsub lookup with
      ⟨fuel', key', trace'⟩
    have bridge := arm_node_bridge arm (W := (armGraph arm).width) (D := (armGraph arm).height)
      (hW := le_rfl) (hD := le_rfl) (node := parent) (dsub := dsub) (key := key')
      trace' lookup
    have slotKeySorted := bridge.1
    have firstLt : firstSlot < dsub.children.length := (hdense firstSlot).1 ⟨first, addrFirst⟩
    have secondLt : secondSlot < dsub.children.length := (hdense secondSlot).1 ⟨second, addrSecond⟩
    have firstSlotLt : firstSlot < (DeclarativeCIP.slotList
        (toOfficialSourceTree arm.tree).declarativeAddressing parent dsub.children.length).length := by
      simpa [DeclarativeCIP.slotList] using firstLt
    have secondSlotLt : secondSlot < (DeclarativeCIP.slotList
        (toOfficialSourceTree arm.tree).declarativeAddressing parent dsub.children.length).length := by
      simpa [DeclarativeCIP.slotList] using secondLt
    obtain ⟨childI, slotI, addrI⟩ := DeclarativeCIP.slotList_getD_of_lt
      (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing) (parent := parent)
      (count := dsub.children.length) hdense firstLt
    obtain ⟨childJ, slotJ, addrJ⟩ := DeclarativeCIP.slotList_getD_of_lt
      (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing) (parent := parent)
      (count := dsub.children.length) hdense secondLt
    have addrIFlat : first.1 = parent.1 ++ [firstSlot] := by
      rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address first,
        (toOfficialSourceTree arm.tree).declarativeAddressing_address parent] at addrFirst
      exact addrFirst
    have addrJFlat : second.1 = parent.1 ++ [secondSlot] := by
      rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address second,
        (toOfficialSourceTree arm.tree).declarativeAddressing_address parent] at addrSecond
      exact addrSecond
    have childIFlat : childI.1 = parent.1 ++ [firstSlot] := by
      rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address childI,
        (toOfficialSourceTree arm.tree).declarativeAddressing_address parent] at addrI
      exact addrI
    have childJFlat : childJ.1 = parent.1 ++ [secondSlot] := by
      rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address childJ,
        (toOfficialSourceTree arm.tree).declarativeAddressing_address parent] at addrJ
      exact addrJ
    have firstEq : first = childI := Subtype.ext (addrIFlat.trans childIFlat.symm)
    have secondEq : second = childJ := Subtype.ext (addrJFlat.trans childJFlat.symm)
    have slotIEq : (DeclarativeCIP.slotList (toOfficialSourceTree arm.tree).declarativeAddressing
        parent dsub.children.length)[firstSlot]'firstSlotLt = childI :=
      Option.some.inj ((List.getElem?_eq_getElem firstSlotLt).symm.trans slotI)
    have slotJEq : (DeclarativeCIP.slotList (toOfficialSourceTree arm.tree).declarativeAddressing
        parent dsub.children.length)[secondSlot]'secondSlotLt = childJ :=
      Option.some.inj ((List.getElem?_eq_getElem secondSlotLt).symm.trans slotJ)
    have firstSlotMapLt : firstSlot < ((DeclarativeCIP.slotList
        (toOfficialSourceTree arm.tree).declarativeAddressing parent dsub.children.length).map
      (DeclarativeCIP.ruleKey input.moleculeGraph (armGraph arm) (armGraph arm).width
        (armGraph arm).height)).length := by
      simpa using firstSlotLt
    have secondSlotMapLt : secondSlot < ((DeclarativeCIP.slotList
        (toOfficialSourceTree arm.tree).declarativeAddressing parent dsub.children.length).map
      (DeclarativeCIP.ruleKey input.moleculeGraph (armGraph arm) (armGraph arm).width
        (armGraph arm).height)).length := by
      simpa using secondSlotLt
    have hle : DeclarativeCIP.ruleKey input.moleculeGraph (armGraph arm) (armGraph arm).width
        (armGraph arm).height childJ ≤
        DeclarativeCIP.ruleKey input.moleculeGraph (armGraph arm) (armGraph arm).width
          (armGraph arm).height childI := by
      have hpair := (List.pairwise_iff_getElem.1 slotKeySorted) firstSlot secondSlot
        firstSlotMapLt secondSlotMapLt hlt
      simpa [List.getElem_map, slotIEq, slotJEq] using hpair
    simpa [firstEq, secondEq] using hle

/-- **Representation lift to adequate layouts.**  A root representation at the arm graph's own
width and height extends to any larger layout `W D`: the vector-component path observations at the
larger layout agree with the intrinsic ones by the width-independence of `nodePathObservation`,
and the actual encoded side does not depend on `W D` at all. -/
theorem represents_of_bounds
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index stage read)
    {W D : ℕ} (hW : (armGraph arm).width ≤ W) (hD : (armGraph arm).height ≤ D) :
    OfficialSparseCanonicalVectorComparison.Represents W D
      (DeclarativeCIP.ruleKey input.moleculeGraph (armGraph arm) W D (armGraph arm).root)
      arm.key.constitutional := by
  unfold OfficialSparseCanonicalVectorComparison.Represents
  intro r hr path
  change DeclarativeCIP.nodePathObservation input.moleculeGraph (armGraph arm) W D r
      (armGraph arm).root path =
    OfficialSparseCanonicalVectorComparison.encodedObservation arm.key.constitutional
      (DeclarativeCIP.ruleOfIndex r) path
  rw [DeclarativeCIP.nodePathObservation_width_independent input.moleculeGraph (armGraph arm) hW
    le_rfl hD le_rfl (armGraph arm).root r path]
  exact arm_root_represents arm r hr path







theorem arm_compare_eq_compare_vector
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
    {index1 index2 : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm1 : input.OriginalRootArm center index1 stage read)
    (arm2 : input.OriginalRootArm center index2 stage read)
    {W D : ℕ} (hW1 : (armGraph arm1).width ≤ W) (hD1 : (armGraph arm1).height ≤ D)
    (hW2 : (armGraph arm2).width ≤ W) (hD2 : (armGraph arm2).height ≤ D) :
    OfficialRuleMajorKey.compare arm1.key.constitutional arm2.key.constitutional =
      compare (DeclarativeCIP.ruleKey input.moleculeGraph (armGraph arm1) W D (armGraph arm1).root)
        (DeclarativeCIP.ruleKey input.moleculeGraph (armGraph arm2) W D (armGraph arm2).root) :=
  OfficialSparseCanonicalVectorComparison.compare_eq_compare_vector
    (leftWellFormed := wellFormedRuleMajorKey_of_tableMatch arm1.tableMatch arm1.realizes)
    (rightWellFormed := wellFormedRuleMajorKey_of_tableMatch arm2.tableMatch arm2.realizes)
    (leftShaped := DeclarativeCIP.ruleKey_vectorWellShaped input.moleculeGraph (armGraph arm1) W D
      (armGraph arm1).root)
    (rightShaped := DeclarativeCIP.ruleKey_vectorWellShaped input.moleculeGraph (armGraph arm2) W D
      (armGraph arm2).root)
    (leftRepresents := represents_of_bounds arm1 hW1 hD1)
    (rightRepresents := represents_of_bounds arm2 hW2 hD2)




theorem arm_compare_ne_lt_iff_rightRuleKey_le
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
    {index1 index2 : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm1 : input.OriginalRootArm center index1 stage read)
    (arm2 : input.OriginalRootArm center index2 stage read)
    {W D : ℕ} (hW1 : (armGraph arm1).width ≤ W) (hD1 : (armGraph arm1).height ≤ D)
    (hW2 : (armGraph arm2).width ≤ W) (hD2 : (armGraph arm2).height ≤ D) :
    OfficialRuleMajorKey.compare arm1.key.constitutional arm2.key.constitutional ≠ Ordering.lt ↔
      DeclarativeCIP.ruleKey input.moleculeGraph (armGraph arm2) W D (armGraph arm2).root ≤
        DeclarativeCIP.ruleKey input.moleculeGraph (armGraph arm1) W D (armGraph arm1).root :=
  OfficialSparseCanonicalVectorComparison.compare_ne_lt_iff_rightVector_le
    (leftWellFormed := wellFormedRuleMajorKey_of_tableMatch arm1.tableMatch arm1.realizes)
    (rightWellFormed := wellFormedRuleMajorKey_of_tableMatch arm2.tableMatch arm2.realizes)
    (leftShaped := DeclarativeCIP.ruleKey_vectorWellShaped input.moleculeGraph (armGraph arm1) W D
      (armGraph arm1).root)
    (rightShaped := DeclarativeCIP.ruleKey_vectorWellShaped input.moleculeGraph (armGraph arm2) W D
      (armGraph arm2).root)
    (leftRepresents := represents_of_bounds arm1 hW1 hD1)
    (rightRepresents := represents_of_bounds arm2 hW2 hD2)

end OriginalRootArm

/-! ## The independent canonical outcome API, localized

The independent specification's `ConstitutionalProblemData` for a certified localized input: the
molecule is the actual molecule graph, the units are the input's tetrahedral centers, the ligand
atoms are the canonical ligand positions, and the admissible expansions of a ligand are exactly
the faithful exact declarative expansions of the actual graph.  The canonical addressing family is
the admissible addressing family, so the independent `withCanonicalAddressing` problem data used
below is exactly this data with its own canonical family; the later Rules 4a--5 judgments are left
relational (`False`) as they are outside this constitutional subtheorem. -/
def localizedConstitutionalProblemData (input : CertifiedLocalizedCIPInput) :
    DeclarativeCIP.ConstitutionalProblemData input.Atom input.TetrahedralCenter where
  molecule := input.moleculeGraph
  centerAtom := fun center => center.1
  ligandAtom := fun center index => input.canonicalLigandAtom center index
  admissibleExpansion := fun center index graph =>
    DeclarativeCIP.RootedDigraph.FaithfulExactExpansion input.moleculeGraph center.1
      (input.canonicalLigandAtom center index) graph
  expansion_sound := by
    intro center index graph h
    exact h.1
  admissibleAddressing := fun _ _ _ addressing =>
    DeclarativeCIP.CanonicalAddressing input.moleculeGraph addressing
  addressing_invariant := by
    intro descriptorMap unit left right iso addressing
    exact DeclarativeCIP.canonicalAddressing_transport_iff input.moleculeGraph iso addressing
  laterRuleJudgment := fun _ _ _ _ _ _ => False
  admissibleRule6Reference := fun _ _ _ => False
  rule6Judgment := fun _ _ _ _ _ _ => False
  dependsOn := fun _ _ _ => False
  orientationJudgment := fun _ _ _ => False

/-- The localized problem data admits exactly the faithful expansions: its `ExpansionsFaithful`
obligation holds by definition, with no build, canonicality or sortedness hypothesis. -/
theorem localizedConstitutionalProblemData_expansionsFaithful
    (input : CertifiedLocalizedCIPInput) :
    (input.localizedConstitutionalProblemData).ExpansionsFaithful := by
  unfold DeclarativeCIP.ConstitutionalProblemData.ExpansionsFaithful
  intro unit ligand graph h
  simpa [localizedConstitutionalProblemData] using h

/-- Every center and ligand position of a certified localized input admits a faithful exact
expansion: the original-root arm graph of the actual shipped builder at the given stage and label
reader.  The arm exists unconditionally (`exists_originalRootArm`), so no build success is assumed
here. -/
theorem localizedConstitutionalProblemData_expansionsExist
    (input : CertifiedLocalizedCIPInput)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel) :
    ∀ unit ligand, ∃ graph, input.localizedConstitutionalProblemData.admissibleExpansion
      unit ligand graph := by
  intro unit ligand
  let arm := Classical.choice (exists_originalRootArm input unit ligand stage read)
  refine ⟨(toOfficialSourceTree arm.tree).toDeclarativeDigraph, ?_⟩
  simpa [localizedConstitutionalProblemData] using arm.faithful

/-- Installing the canonical addressing family changes nothing: the localized data already admits
exactly the canonical addressings, so the generic `withCanonicalAddressing` API used below speaks
about this very data. -/
theorem localizedConstitutionalProblemData_withCanonicalAddressing
    (input : CertifiedLocalizedCIPInput) :
    input.localizedConstitutionalProblemData.withCanonicalAddressing =
      input.localizedConstitutionalProblemData :=
  rfl

/-- A table-matched key's constitutional column is the decorated table of the same rule's
observation. -/
theorem armTableColumn_eq_table {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (tableMatch : LocalizedCumulativeTreeTableMatch stage tree key)
    (rule : DeclarativeCIP.ConstitutionalRule) :
    armTableColumn key rule = table (armObservation rule) tree := by
  cases rule with
  | rule1aAtomicNumber =>
      change key.constitutional.rule1a = table (fun node => node.atomicNumber) tree
      simpa [tables_rule1a] using (tableMatch.1).symm
  | rule1bDuplicateNodeProximity =>
      change key.constitutional.rule1b = table (fun node => node.rule1bDistance) tree
      simpa [tables_rule1b] using (tableMatch.2.1).symm
  | rule2AtomicMass =>
      change key.constitutional.rule2 = table (fun node => node.isotopeMass) tree
      simpa [tables_rule2] using (tableMatch.2.2.1).symm

namespace OriginalRootArm

/-! ## Reading the actual addressing at every address -/

/-- The actual ranked-sibling addressing of an arm graph. -/
abbrev armAddressing {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
    {index : Fin 4} {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index stage read) : (armGraph arm).Addressing :=
  (toOfficialSourceTree arm.tree).declarativeAddressing

/-- An address is occupied by the actual addressing exactly when the decorated lookup of the arm's
own tree succeeds there. -/
theorem occupied_iff_decoratedSubtreeAt?
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index stage read) (position : List ℕ) :
    (∃ node, (armAddressing arm).address node = position) ↔
      ∃ dsub, arm.tree.decoratedSubtreeAt? position = some dsub := by
  constructor
  · rintro ⟨node, addressEq⟩
    obtain ⟨dsub, lookup, _⟩ := decoratedSubtree_of_node arm node
    refine ⟨dsub, ?_⟩
    have nodeAddress : (armAddressing arm).address node = node.1 :=
      (toOfficialSourceTree arm.tree).declarativeAddressing_address node
    rw [← addressEq, nodeAddress]
    exact lookup
  · rintro ⟨dsub, lookup⟩
    have erased : (toOfficialSourceTree arm.tree).subtreeAt? position =
        some (toOfficialSourceTree dsub) := by
      rw [toOfficialSourceTree_subtreeAt? arm.tree position, lookup]
      rfl
    have membership : position ∈ (toOfficialSourceTree arm.tree).hierarchyAddresses :=
      (toOfficialSourceTree arm.tree).mem_hierarchyAddresses_of_occurrence
        ⟨position, (toOfficialSourceTree dsub).source⟩
        (OfficialCIPSourceTree.mem_occurrences_of_subtreeAt?_eq_some position
          (toOfficialSourceTree arm.tree) (toOfficialSourceTree dsub) erased)
    exact ⟨⟨position, membership⟩,
      (toOfficialSourceTree arm.tree).declarativeAddressing_address ⟨position, membership⟩⟩

/-- The occupied addresses of the actual addressing are exactly the Rule-1a address support of the
actual key. -/
theorem occupied_iff_hasAddress
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index stage read) (position : List ℕ) :
    (∃ node, (armAddressing arm).address node = position) ↔
      SparseSupportAlignment.HasAddress arm.key.constitutional.rule1a position := by
  have match1a : table (fun node => node.atomicNumber) arm.tree =
      arm.key.constitutional.rule1a := by
    simpa [LocalizedCumulativeTreeTableMatch, tables_rule1a] using arm.tableMatch.1
  rw [occupied_iff_decoratedSubtreeAt?, ← match1a,
    hasAddress_atomicNumber_table_iff_subtree arm.realizes position]

/-- An unoccupied address carries no label in the actual addressing. -/
theorem addressLabel_eq_none_of_unoccupied
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index stage read) {position : List ℕ}
    (absent : ¬ ∃ node, (armAddressing arm).address node = position) :
    DeclarativeCIP.addressLabel (armAddressing arm) position = none := by
  unfold DeclarativeCIP.addressLabel
  rw [dif_neg absent]

/-- Every constitutional column of the actual key reads zero at an unoccupied address. -/
theorem tableValue_eq_zero_of_unoccupied
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index stage read)
    (rule : DeclarativeCIP.ConstitutionalRule) {position : List ℕ}
    (absent : ¬ ∃ node, (armAddressing arm).address node = position) :
    tableValue (armTableColumn arm.key rule) position = 0 := by
  rw [armTableColumn_eq_table arm.tableMatch rule, tableValue_table_eq_observeAt]
  unfold observeAt
  cases lookup : arm.tree.decoratedSubtreeAt? position with
  | none => rfl
  | some dsub =>
      exact absurd ((occupied_iff_decoratedSubtreeAt? arm position).2 ⟨dsub, lookup⟩) absent

/-- **Occupied-address readback.**  At an occupied address, the independent rule value read
through the actual addressing's own label equals the actual key's column at that address: the
node readback `nodeObservation_eq_actualTableValue`, the address length of the node and the
injectivity of the priority orientation. -/
theorem ruleValue_addressLabel_eq_tableValue
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index stage read)
    (rule : DeclarativeCIP.ConstitutionalRule) {position : List ℕ}
    (occupied : ∃ node, (armAddressing arm).address node = position) :
    DeclarativeCIP.ruleValue input.moleculeGraph rule position
        (DeclarativeCIP.addressLabel (armAddressing arm) position) =
      tableValue (armTableColumn arm.key rule) position := by
  obtain ⟨node, addressEq⟩ := occupied
  have occupiedAt : ∃ found, (armAddressing arm).address found = position := ⟨node, addressEq⟩
  have labelEq : DeclarativeCIP.addressLabel (armAddressing arm) position =
      some ((armGraph arm).label node) := by
    unfold DeclarativeCIP.addressLabel
    rw [dif_pos occupiedAt]
    congr 2
    exact (armAddressing arm).address_injective
      ((Classical.choose_spec occupiedAt).trans addressEq.symm)
  have lengthEq : (List.replicate ((armGraph arm).depth node) 0).length = position.length := by
    rw [List.length_replicate, ← addressEq, (armAddressing arm).address_length_eq_depth]
  have nodeAddress : (armAddressing arm).address node = node.1 :=
    (toOfficialSourceTree arm.tree).declarativeAddressing_address node
  have observed := nodeObservation_eq_actualTableValue arm rule node
  rw [← nodeAddress, addressEq] at observed
  rw [labelEq, ← DeclarativeCIP.ruleValue_eq_of_length_eq input.moleculeGraph rule lengthEq]
  exact DeclarativeCIP.priorityValue_injective rule observed

/-- **All-address readback for Rules 1a and 2.**  For the atomic-number and atomic-mass rules the
readback holds at every address: unoccupied addresses read zero on both sides. -/
theorem ruleValue_addressLabel_eq_tableValue_of_ne_rule1b
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index stage read)
    (rule : DeclarativeCIP.ConstitutionalRule)
    (notRule1b : rule ≠ .rule1bDuplicateNodeProximity) (position : List ℕ) :
    DeclarativeCIP.ruleValue input.moleculeGraph rule position
        (DeclarativeCIP.addressLabel (armAddressing arm) position) =
      tableValue (armTableColumn arm.key rule) position := by
  by_cases occupied : ∃ node, (armAddressing arm).address node = position
  · exact ruleValue_addressLabel_eq_tableValue arm rule occupied
  · rw [tableValue_eq_zero_of_unoccupied arm rule occupied,
      addressLabel_eq_none_of_unoccupied arm occupied]
    cases rule with
    | rule1aAtomicNumber => rfl
    | rule1bDuplicateNodeProximity => exact absurd rfl notRule1b
    | rule2AtomicMass => rfl

/-! ## Actual column comparisons are independent hierarchy outcomes -/

/-- **Rule 1a.**  The independent first-difference Rule-1a outcome of two arm graphs at their
actual addressings is exactly the executed Rule-1a column comparison of the two actual keys. -/
theorem hierarchyOutcome_rule1a_iff_compare
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
    {index1 index2 : Fin 4} {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm1 : input.OriginalRootArm center index1 stage read)
    (arm2 : input.OriginalRootArm center index2 stage read) (outcome : Ordering) :
    DeclarativeCIP.ConstitutionalHierarchyOutcome input.moleculeGraph .rule1aAtomicNumber
        (armGraph arm1) (armAddressing arm1) (armGraph arm2) (armAddressing arm2) outcome ↔
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        arm1.key.constitutional.rule1a arm2.key.constitutional.rule1a = outcome := by
  have wellFormed1 := wellFormedRuleMajorKey_of_tableMatch arm1.tableMatch arm1.realizes
  have wellFormed2 := wellFormedRuleMajorKey_of_tableMatch arm2.tableMatch arm2.realizes
  rw [compareSparseLayers_eq_firstDifference wellFormed1.wellFormed1a wellFormed2.wellFormed1a
    wellFormed1.positive1a wellFormed2.positive1a outcome]
  apply DeclarativeCIP.FirstDifferenceOutcome.congr
  intro position result
  rw [DeclarativeCIP.constitutionalOutcomeAt_iff,
    ruleValue_addressLabel_eq_tableValue_of_ne_rule1b arm1 .rule1aAtomicNumber (by decide)
      position,
    ruleValue_addressLabel_eq_tableValue_of_ne_rule1b arm2 .rule1aAtomicNumber (by decide)
      position]
  rfl

/-- **Rule 1b, after a Rule-1a tie.**  Once the executed Rule-1a columns tie, the two actual
address supports coincide, and the independent Rule-1b outcome at the actual addressings is
exactly the executed Rule-1b column comparison: common occupied addresses read the actual
distances, common unoccupied addresses tie on both sides. -/
theorem hierarchyOutcome_rule1b_iff_compare
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
    {index1 index2 : Fin 4} {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm1 : input.OriginalRootArm center index1 stage read)
    (arm2 : input.OriginalRootArm center index2 stage read)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      arm1.key.constitutional.rule1a arm2.key.constitutional.rule1a = Ordering.eq)
    (outcome : Ordering) :
    DeclarativeCIP.ConstitutionalHierarchyOutcome input.moleculeGraph
        .rule1bDuplicateNodeProximity
        (armGraph arm1) (armAddressing arm1) (armGraph arm2) (armAddressing arm2) outcome ↔
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
        arm1.key.constitutional.rule1b arm2.key.constitutional.rule1b = outcome := by
  have wellFormed1 := wellFormedRuleMajorKey_of_tableMatch arm1.tableMatch arm1.realizes
  have wellFormed2 := wellFormedRuleMajorKey_of_tableMatch arm2.tableMatch arm2.realizes
  have support : ∀ position,
      SparseSupportAlignment.HasAddress arm1.key.constitutional.rule1a position ↔
        SparseSupportAlignment.HasAddress arm2.key.constitutional.rule1a position :=
    sameSupport_of_compareSparseLayers_eq wellFormed1.wellFormed1a wellFormed2.wellFormed1a
      wellFormed1.positive1a wellFormed2.positive1a tied
  rw [OfficialSparseCanonicalVectorComparison.later_compareSparseLayers_eq_firstDifference
    OfficialRuleMajorKey.compareRule1b
    OfficialSparseCanonicalVectorComparison.compareRule1b_zero_zero
    wellFormed1.wellFormed1a wellFormed2.wellFormed1a wellFormed1.positive1a
    wellFormed2.positive1a tied wellFormed1.rows1b wellFormed2.rows1b
    wellFormed1.wellFormed1b wellFormed2.wellFormed1b outcome]
  apply DeclarativeCIP.FirstDifferenceOutcome.congr
  intro position result
  rw [DeclarativeCIP.constitutionalOutcomeAt_iff,
    OfficialRuleMajorKey.compareRule1b_eq_iff_rule1bDistanceOutcome]
  by_cases occupied1 : ∃ node, (armAddressing arm1).address node = position
  · have occupied2 : ∃ node, (armAddressing arm2).address node = position :=
      (occupied_iff_hasAddress arm2 position).2
        ((support position).1 ((occupied_iff_hasAddress arm1 position).1 occupied1))
    rw [ruleValue_addressLabel_eq_tableValue arm1 .rule1bDuplicateNodeProximity occupied1,
      ruleValue_addressLabel_eq_tableValue arm2 .rule1bDuplicateNodeProximity occupied2]
    rfl
  · have occupied2 : ¬ ∃ node, (armAddressing arm2).address node = position :=
      fun occupied2 => occupied1 ((occupied_iff_hasAddress arm1 position).2
        ((support position).2 ((occupied_iff_hasAddress arm2 position).1 occupied2)))
    have zero1 := tableValue_eq_zero_of_unoccupied arm1 .rule1bDuplicateNodeProximity occupied1
    have zero2 := tableValue_eq_zero_of_unoccupied arm2 .rule1bDuplicateNodeProximity occupied2
    change DeclarativeCIP.Rule1bDistanceOutcome
        (DeclarativeCIP.ruleValue input.moleculeGraph .rule1bDuplicateNodeProximity position
          (DeclarativeCIP.addressLabel (armAddressing arm1) position))
        (DeclarativeCIP.ruleValue input.moleculeGraph .rule1bDuplicateNodeProximity position
          (DeclarativeCIP.addressLabel (armAddressing arm2) position)) result ↔
      DeclarativeCIP.Rule1bDistanceOutcome
        (tableValue (armTableColumn arm1.key .rule1bDuplicateNodeProximity) position)
        (tableValue (armTableColumn arm2.key .rule1bDuplicateNodeProximity) position) result
    rw [addressLabel_eq_none_of_unoccupied arm1 occupied1,
      addressLabel_eq_none_of_unoccupied arm2 occupied2, zero1, zero2]
    cases result <;> simp

/-- **Rule 2, after a Rule-1a tie.**  The independent Rule-2 outcome at the actual addressings is
exactly the executed Rule-2 column comparison on the common Rule-1a support. -/
theorem hierarchyOutcome_rule2_iff_compare
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
    {index1 index2 : Fin 4} {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm1 : input.OriginalRootArm center index1 stage read)
    (arm2 : input.OriginalRootArm center index2 stage read)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      arm1.key.constitutional.rule1a arm2.key.constitutional.rule1a = Ordering.eq)
    (outcome : Ordering) :
    DeclarativeCIP.ConstitutionalHierarchyOutcome input.moleculeGraph .rule2AtomicMass
        (armGraph arm1) (armAddressing arm1) (armGraph arm2) (armAddressing arm2) outcome ↔
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        arm1.key.constitutional.rule2 arm2.key.constitutional.rule2 = outcome := by
  have wellFormed1 := wellFormedRuleMajorKey_of_tableMatch arm1.tableMatch arm1.realizes
  have wellFormed2 := wellFormedRuleMajorKey_of_tableMatch arm2.tableMatch arm2.realizes
  rw [OfficialSparseCanonicalVectorComparison.later_compareSparseLayers_eq_firstDifference
    OfficialRuleMajorKey.compareNat compareNat_zero_zero
    wellFormed1.wellFormed1a wellFormed2.wellFormed1a wellFormed1.positive1a
    wellFormed2.positive1a tied wellFormed1.rows2 wellFormed2.rows2
    wellFormed1.wellFormed2 wellFormed2.wellFormed2 outcome]
  apply DeclarativeCIP.FirstDifferenceOutcome.congr
  intro position result
  rw [DeclarativeCIP.constitutionalOutcomeAt_iff,
    ruleValue_addressLabel_eq_tableValue_of_ne_rule1b arm1 .rule2AtomicMass (by decide) position,
    ruleValue_addressLabel_eq_tableValue_of_ne_rule1b arm2 .rule2AtomicMass (by decide) position,
    SparsePhysicalFirstDifference.compareNat_iff_descendingNatOutcome]
  rfl

/-! ## Independent rule outcomes over every faithful exact expansion -/

/-- **Rule outcomes are read at the actual addressings.**  For every constitutional rule, the
independent `Problem.RuleOutcome` of the localized data — quantified over *all* faithful exact
expansions of both ligands and all their canonical addressings — holds exactly when the
first-difference hierarchy outcome holds at the two actual arm graphs and their actual
addressings.  Forward: the actual arm graphs are admissible and the actual addressings canonical.
Backward: canonical addressings of the actual graphs agree (`hierarchyOutcome_canonical_iff`), and
every admissible expansion is isomorphic to the actual graph
(`faithfulExactExpansion_unique_up_to_iso`), along which canonical outcomes transport
(`canonicalOutcome_transport_iff`). -/
theorem ruleOutcome_iff_hierarchyOutcome
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
    {index1 index2 : Fin 4} {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm1 : input.OriginalRootArm center index1 stage read)
    (arm2 : input.OriginalRootArm center index2 stage read)
    (descriptorMap : DeclarativeCIP.DescriptorMap input.TetrahedralCenter)
    (rule : DeclarativeCIP.ConstitutionalRule) (outcome : Ordering) :
    input.localizedConstitutionalProblemData.withCanonicalAddressing.toProblem.RuleOutcome
        descriptorMap rule.toSequenceRule center index1 index2 outcome ↔
      DeclarativeCIP.ConstitutionalHierarchyOutcome input.moleculeGraph rule
        (armGraph arm1) (armAddressing arm1) (armGraph arm2) (armAddressing arm2) outcome := by
  have canonical1 := arm_canonicalAddressing arm1
  have canonical2 := arm_canonicalAddressing arm2
  constructor
  · intro holds
    have onArms := (input.localizedConstitutionalProblemData.outcomeOnGraphs_iff_canonicalOutcome
      descriptorMap center rule).1
        (holds (armGraph arm1) (armGraph arm2) arm1.faithful arm2.faithful)
    exact onArms.2.2 (armAddressing arm1) (armAddressing arm2) canonical1 canonical2
  · intro atActual leftGraph rightGraph leftAdmissible rightAdmissible
    have leftFaithful : DeclarativeCIP.RootedDigraph.FaithfulExactExpansion input.moleculeGraph
        center.1 (input.canonicalLigandAtom center index1) leftGraph := leftAdmissible
    have rightFaithful : DeclarativeCIP.RootedDigraph.FaithfulExactExpansion input.moleculeGraph
        center.1 (input.canonicalLigandAtom center index2) rightGraph := rightAdmissible
    have onArms : input.localizedConstitutionalProblemData.withCanonicalAddressing.CanonicalOutcome
        descriptorMap center rule (armGraph arm1) (armGraph arm2) outcome := by
      refine ⟨⟨armAddressing arm1, canonical1⟩, ⟨armAddressing arm2, canonical2⟩,
        fun leftAddressing rightAddressing leftCanonical rightCanonical => ?_⟩
      exact (DeclarativeCIP.hierarchyOutcome_canonical_iff input.moleculeGraph canonical1
        leftCanonical canonical2 rightCanonical rule outcome).1 atActual
    obtain ⟨leftIso⟩ := DeclarativeCIP.RootedDigraph.faithfulExactExpansion_unique_up_to_iso
      _ _ _ _ _ arm1.faithful leftFaithful
    obtain ⟨rightIso⟩ := DeclarativeCIP.RootedDigraph.faithfulExactExpansion_unique_up_to_iso
      _ _ _ _ _ arm2.faithful rightFaithful
    exact (input.localizedConstitutionalProblemData.outcomeOnGraphs_iff_canonicalOutcome
      descriptorMap center rule).2
        ((DeclarativeCIP.ConstitutionalProblemData.canonicalOutcome_transport_iff
          input.localizedConstitutionalProblemData.withCanonicalAddressing
          descriptorMap center rule leftIso rightIso outcome).1 onArms)

/-- **Rule 1a over every faithful expansion.**  The independent Rule-1a outcome of the two ligands
is exactly the executed Rule-1a column comparison of the two actual keys. -/
theorem ruleOutcome_rule1a_iff_compare
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
    {index1 index2 : Fin 4} {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm1 : input.OriginalRootArm center index1 stage read)
    (arm2 : input.OriginalRootArm center index2 stage read)
    (descriptorMap : DeclarativeCIP.DescriptorMap input.TetrahedralCenter) (outcome : Ordering) :
    input.localizedConstitutionalProblemData.withCanonicalAddressing.toProblem.RuleOutcome
        descriptorMap DeclarativeCIP.ConstitutionalRule.rule1aAtomicNumber.toSequenceRule
        center index1 index2 outcome ↔
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        arm1.key.constitutional.rule1a arm2.key.constitutional.rule1a = outcome :=
  (ruleOutcome_iff_hierarchyOutcome arm1 arm2 descriptorMap .rule1aAtomicNumber outcome).trans
    (hierarchyOutcome_rule1a_iff_compare arm1 arm2 outcome)

/-- **Rule 1b over every faithful expansion, after a Rule-1a tie.** -/
theorem ruleOutcome_rule1b_iff_compare
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
    {index1 index2 : Fin 4} {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm1 : input.OriginalRootArm center index1 stage read)
    (arm2 : input.OriginalRootArm center index2 stage read)
    (descriptorMap : DeclarativeCIP.DescriptorMap input.TetrahedralCenter)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      arm1.key.constitutional.rule1a arm2.key.constitutional.rule1a = Ordering.eq)
    (outcome : Ordering) :
    input.localizedConstitutionalProblemData.withCanonicalAddressing.toProblem.RuleOutcome
        descriptorMap DeclarativeCIP.ConstitutionalRule.rule1bDuplicateNodeProximity.toSequenceRule
        center index1 index2 outcome ↔
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
        arm1.key.constitutional.rule1b arm2.key.constitutional.rule1b = outcome :=
  (ruleOutcome_iff_hierarchyOutcome arm1 arm2 descriptorMap .rule1bDuplicateNodeProximity
    outcome).trans (hierarchyOutcome_rule1b_iff_compare arm1 arm2 tied outcome)

/-- **Rule 2 over every faithful expansion, after a Rule-1a tie.** -/
theorem ruleOutcome_rule2_iff_compare
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
    {index1 index2 : Fin 4} {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm1 : input.OriginalRootArm center index1 stage read)
    (arm2 : input.OriginalRootArm center index2 stage read)
    (descriptorMap : DeclarativeCIP.DescriptorMap input.TetrahedralCenter)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      arm1.key.constitutional.rule1a arm2.key.constitutional.rule1a = Ordering.eq)
    (outcome : Ordering) :
    input.localizedConstitutionalProblemData.withCanonicalAddressing.toProblem.RuleOutcome
        descriptorMap DeclarativeCIP.ConstitutionalRule.rule2AtomicMass.toSequenceRule
        center index1 index2 outcome ↔
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        arm1.key.constitutional.rule2 arm2.key.constitutional.rule2 = outcome :=
  (ruleOutcome_iff_hierarchyOutcome arm1 arm2 descriptorMap .rule2AtomicMass outcome).trans
    (hierarchyOutcome_rule2_iff_compare arm1 arm2 tied outcome)

/-! ## The actual signed comparator is the independent first-decisive Rules 1a--2 priority -/

/-- **Actual `gt` is independent first-decisive priority.**  The actual constitutional comparator
ranks the first arm above the second exactly when, in the independent semantics over every
faithful exact expansion, some rule among 1a, 1b and 2 decides `gt` after every earlier one tied
(`Problem.ConstitutionalHigher`).  The comparator is split into its executed Rule-1a, Rule-1b and
Rule-2 column comparisons; the lower columns are consulted only after the Rule-1a tie, exactly
where their correspondence holds. -/
theorem compare_eq_gt_iff_constitutionalHigher
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
    {index1 index2 : Fin 4} {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm1 : input.OriginalRootArm center index1 stage read)
    (arm2 : input.OriginalRootArm center index2 stage read)
    (descriptorMap : DeclarativeCIP.DescriptorMap input.TetrahedralCenter) :
    OfficialRuleMajorKey.compare arm1.key.constitutional arm2.key.constitutional = Ordering.gt ↔
      DeclarativeCIP.Problem.ConstitutionalHigher
        input.localizedConstitutionalProblemData.withCanonicalAddressing.toProblem
        descriptorMap center index1 index2 := by
  have rule1a := ruleOutcome_rule1a_iff_compare arm1 arm2 descriptorMap
  have rule1b := ruleOutcome_rule1b_iff_compare arm1 arm2 descriptorMap
  have rule2 := ruleOutcome_rule2_iff_compare arm1 arm2 descriptorMap
  change (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        arm1.key.constitutional.rule1a arm2.key.constitutional.rule1a).then
      ((OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
          arm1.key.constitutional.rule1b arm2.key.constitutional.rule1b).then
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          arm1.key.constitutional.rule2 arm2.key.constitutional.rule2)) = Ordering.gt ↔ _
  rw [Ordering.then_eq_gt, Ordering.then_eq_gt]
  constructor
  · rintro (decisive | ⟨tied1a, decisive | ⟨tied1b, decisive⟩⟩)
    · refine ⟨.rule1aAtomicNumber, fun earlier before => ?_, (rule1a _).2 decisive⟩
      cases earlier <;> simp [DeclarativeCIP.ruleIndex] at before
    · refine ⟨.rule1bDuplicateNodeProximity, fun earlier before => ?_,
        (rule1b tied1a _).2 decisive⟩
      cases earlier with
      | rule1aAtomicNumber => exact (rule1a _).2 tied1a
      | rule1bDuplicateNodeProximity => simp [DeclarativeCIP.ruleIndex] at before
      | rule2AtomicMass => simp [DeclarativeCIP.ruleIndex] at before
    · refine ⟨.rule2AtomicMass, fun earlier before => ?_, (rule2 tied1a _).2 decisive⟩
      cases earlier with
      | rule1aAtomicNumber => exact (rule1a _).2 tied1a
      | rule1bDuplicateNodeProximity => exact (rule1b tied1a _).2 tied1b
      | rule2AtomicMass => simp [DeclarativeCIP.ruleIndex] at before
  · rintro ⟨rule, earlierTie, decisive⟩
    cases rule with
    | rule1aAtomicNumber => exact Or.inl ((rule1a _).1 decisive)
    | rule1bDuplicateNodeProximity =>
        have tied1a := (rule1a _).1 (earlierTie .rule1aAtomicNumber (by decide))
        exact Or.inr ⟨tied1a, Or.inl ((rule1b tied1a _).1 decisive)⟩
    | rule2AtomicMass =>
        have tied1a := (rule1a _).1 (earlierTie .rule1aAtomicNumber (by decide))
        have tied1b := (rule1b tied1a _).1
          (earlierTie .rule1bDuplicateNodeProximity (by decide))
        exact Or.inr ⟨tied1a, Or.inr ⟨tied1b, (rule2 tied1a _).1 decisive⟩⟩

/-- **Actual `eq` is the independent constitutional tie.**  The actual constitutional comparator
ties the two arms exactly when each of Rules 1a, 1b and 2 ties in the independent semantics over
every faithful exact expansion (`Problem.ConstitutionalTied`; later rules are not consulted). -/
theorem compare_eq_eq_iff_constitutionalTied
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
    {index1 index2 : Fin 4} {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm1 : input.OriginalRootArm center index1 stage read)
    (arm2 : input.OriginalRootArm center index2 stage read)
    (descriptorMap : DeclarativeCIP.DescriptorMap input.TetrahedralCenter) :
    OfficialRuleMajorKey.compare arm1.key.constitutional arm2.key.constitutional = Ordering.eq ↔
      DeclarativeCIP.Problem.ConstitutionalTied
        input.localizedConstitutionalProblemData.withCanonicalAddressing.toProblem
        descriptorMap center index1 index2 := by
  have rule1a := ruleOutcome_rule1a_iff_compare arm1 arm2 descriptorMap
  have rule1b := ruleOutcome_rule1b_iff_compare arm1 arm2 descriptorMap
  have rule2 := ruleOutcome_rule2_iff_compare arm1 arm2 descriptorMap
  change (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        arm1.key.constitutional.rule1a arm2.key.constitutional.rule1a).then
      ((OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
          arm1.key.constitutional.rule1b arm2.key.constitutional.rule1b).then
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          arm1.key.constitutional.rule2 arm2.key.constitutional.rule2)) = Ordering.eq ↔ _
  rw [Ordering.then_eq_eq, Ordering.then_eq_eq]
  constructor
  · rintro ⟨tied1a, tied1b, tied2⟩ rule
    cases rule with
    | rule1aAtomicNumber => exact (rule1a _).2 tied1a
    | rule1bDuplicateNodeProximity => exact (rule1b tied1a _).2 tied1b
    | rule2AtomicMass => exact (rule2 tied1a _).2 tied2
  · intro tied
    have tied1a := (rule1a _).1 (tied .rule1aAtomicNumber)
    exact ⟨tied1a, (rule1b tied1a _).1 (tied .rule1bDuplicateNodeProximity),
      (rule2 tied1a _).1 (tied .rule2AtomicMass)⟩

/-- **Actual `lt` is the reverse independent priority.**  The actual constitutional comparator
ranks the first arm below the second exactly when the independent first-decisive Rules 1a--2
priority ranks the second ligand above the first: the comparator is oriented, and the `gt`
correspondence holds for the swapped pair of actual arms. -/
theorem compare_eq_lt_iff_reverse_constitutionalHigher
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
    {index1 index2 : Fin 4} {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm1 : input.OriginalRootArm center index1 stage read)
    (arm2 : input.OriginalRootArm center index2 stage read)
    (descriptorMap : DeclarativeCIP.DescriptorMap input.TetrahedralCenter) :
    OfficialRuleMajorKey.compare arm1.key.constitutional arm2.key.constitutional = Ordering.lt ↔
      DeclarativeCIP.Problem.ConstitutionalHigher
        input.localizedConstitutionalProblemData.withCanonicalAddressing.toProblem
        descriptorMap center index2 index1 := by
  letI : Std.TransCmp (@OfficialRuleMajorKey.compare input.Atom) :=
    OfficialRuleMajorKey.compare_transCmp
  exact (Std.OrientedCmp.gt_iff_lt (cmp := @OfficialRuleMajorKey.compare input.Atom)
    (a := arm2.key.constitutional) (b := arm1.key.constitutional)).symm.trans
      (compare_eq_gt_iff_constitutionalHigher arm2 arm1 descriptorMap)

end OriginalRootArm

/-! ## Original-input facade -/

/-- **Actual constitutional comparison is the independent first-decisive Rules 1a--2 priority.**
For every certified localized input, tetrahedral center, pair of ligand indices, stage and label
reader, the shipped builder succeeds on both original-root ligand cursors, and the two actual
arms — the same trees throughout — satisfy:

* both exact successful build equations at the adequate fuel, and both tree roots are the actual
  ligand-root cursors;
* both arm graphs are faithful exact expansions of the actual molecule (admissible in the
  independent localized data), and both actual addressings are canonical;
* for every descriptor map and constitutional rule, the independent `Problem.RuleOutcome`
  (quantified over all faithful exact expansions and canonical addressings) is the hierarchy
  outcome at the two actual addressings; Rule 1a is the executed Rule-1a column comparison, and
  after a Rule-1a tie Rules 1b and 2 are the executed Rule-1b and Rule-2 column comparisons;
* the actual comparator returns `gt`, `eq` or `lt` exactly when the independent semantics gives
  `ConstitutionalHigher`, `ConstitutionalTied` or the reverse `ConstitutionalHigher`.

No success, sortedness, canonicality, reader, acyclicity or bond-order premise is assumed: arbitrary
comparison depth, rings and multiple-bond duplicates are those of the actual arm constructor.  This
is a constitutional statement only — the localized data's later-rule judgments are `False`, so it
makes no full-descriptor claim. -/
theorem exists_originalRootArms_constitutionalPriority
    (input : CertifiedLocalizedCIPInput) (center : input.TetrahedralCenter)
    (index1 index2 : Fin 4) (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel) :
    ∃ (arm1 : input.OriginalRootArm center index1 stage read)
      (arm2 : input.OriginalRootArm center index2 stage read),
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read
          (2 * (input.certified.input.molecule.atomCount + 1 + 1))
          (input.localizedLigandRootCursor center index1) = some arm1.key ∧
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read
          (2 * (input.certified.input.molecule.atomCount + 1 + 1))
          (input.localizedLigandRootCursor center index2) = some arm2.key ∧
      arm1.tree.source = input.localizedLigandRootCursor center index1 ∧
      arm2.tree.source = input.localizedLigandRootCursor center index2 ∧
      DeclarativeCIP.RootedDigraph.FaithfulExactExpansion input.moleculeGraph center.1
        (input.canonicalLigandAtom center index1) (OriginalRootArm.armGraph arm1) ∧
      DeclarativeCIP.RootedDigraph.FaithfulExactExpansion input.moleculeGraph center.1
        (input.canonicalLigandAtom center index2) (OriginalRootArm.armGraph arm2) ∧
      DeclarativeCIP.CanonicalAddressing input.moleculeGraph
        (OriginalRootArm.armAddressing arm1) ∧
      DeclarativeCIP.CanonicalAddressing input.moleculeGraph
        (OriginalRootArm.armAddressing arm2) ∧
      ∀ descriptorMap : DeclarativeCIP.DescriptorMap input.TetrahedralCenter,
        (∀ (rule : DeclarativeCIP.ConstitutionalRule) (outcome : Ordering),
          input.localizedConstitutionalProblemData.withCanonicalAddressing.toProblem.RuleOutcome
              descriptorMap rule.toSequenceRule center index1 index2 outcome ↔
            DeclarativeCIP.ConstitutionalHierarchyOutcome input.moleculeGraph rule
              (OriginalRootArm.armGraph arm1) (OriginalRootArm.armAddressing arm1)
              (OriginalRootArm.armGraph arm2) (OriginalRootArm.armAddressing arm2) outcome) ∧
        (∀ outcome : Ordering,
          input.localizedConstitutionalProblemData.withCanonicalAddressing.toProblem.RuleOutcome
              descriptorMap DeclarativeCIP.ConstitutionalRule.rule1aAtomicNumber.toSequenceRule
              center index1 index2 outcome ↔
            OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
              arm1.key.constitutional.rule1a arm2.key.constitutional.rule1a = outcome) ∧
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
            arm1.key.constitutional.rule1a arm2.key.constitutional.rule1a = Ordering.eq →
          ∀ outcome : Ordering,
            input.localizedConstitutionalProblemData.withCanonicalAddressing.toProblem.RuleOutcome
                descriptorMap
                DeclarativeCIP.ConstitutionalRule.rule1bDuplicateNodeProximity.toSequenceRule
                center index1 index2 outcome ↔
              OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
                arm1.key.constitutional.rule1b arm2.key.constitutional.rule1b = outcome) ∧
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
            arm1.key.constitutional.rule1a arm2.key.constitutional.rule1a = Ordering.eq →
          ∀ outcome : Ordering,
            input.localizedConstitutionalProblemData.withCanonicalAddressing.toProblem.RuleOutcome
                descriptorMap DeclarativeCIP.ConstitutionalRule.rule2AtomicMass.toSequenceRule
                center index1 index2 outcome ↔
              OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
                arm1.key.constitutional.rule2 arm2.key.constitutional.rule2 = outcome) ∧
        (OfficialRuleMajorKey.compare arm1.key.constitutional arm2.key.constitutional =
            Ordering.gt ↔
          DeclarativeCIP.Problem.ConstitutionalHigher
            input.localizedConstitutionalProblemData.withCanonicalAddressing.toProblem
            descriptorMap center index1 index2) ∧
        (OfficialRuleMajorKey.compare arm1.key.constitutional arm2.key.constitutional =
            Ordering.eq ↔
          DeclarativeCIP.Problem.ConstitutionalTied
            input.localizedConstitutionalProblemData.withCanonicalAddressing.toProblem
            descriptorMap center index1 index2) ∧
        (OfficialRuleMajorKey.compare arm1.key.constitutional arm2.key.constitutional =
            Ordering.lt ↔
          DeclarativeCIP.Problem.ConstitutionalHigher
            input.localizedConstitutionalProblemData.withCanonicalAddressing.toProblem
            descriptorMap center index2 index1) := by
  obtain ⟨arm1⟩ := exists_originalRootArm input center index1 stage read
  obtain ⟨arm2⟩ := exists_originalRootArm input center index2 stage read
  exact ⟨arm1, arm2, arm1.built, arm2.built, arm1.source, arm2.source, arm1.faithful,
    arm2.faithful, OriginalRootArm.arm_canonicalAddressing arm1,
    OriginalRootArm.arm_canonicalAddressing arm2, fun descriptorMap =>
      ⟨OriginalRootArm.ruleOutcome_iff_hierarchyOutcome arm1 arm2 descriptorMap,
        OriginalRootArm.ruleOutcome_rule1a_iff_compare arm1 arm2 descriptorMap,
        OriginalRootArm.ruleOutcome_rule1b_iff_compare arm1 arm2 descriptorMap,
        OriginalRootArm.ruleOutcome_rule2_iff_compare arm1 arm2 descriptorMap,
        OriginalRootArm.compare_eq_gt_iff_constitutionalHigher arm1 arm2 descriptorMap,
        OriginalRootArm.compare_eq_eq_iff_constitutionalTied arm1 arm2 descriptorMap,
        OriginalRootArm.compare_eq_lt_iff_reverse_constitutionalHigher arm1 arm2
          descriptorMap⟩⟩

end CertifiedLocalizedCIPInput

end

end OneCenter
end TetraStereo

/-! ## Direct kernel-authority guards

Every public export of this module is checked here against
`TetraStereo.KernelOnly.assert_kernel_only`: only `propext`, `Classical.choice` and
`Quot.sound` may appear in the closure. -/

assert_kernel_only TetraStereo.OneCenter.LocalizedActualRecursiveSortTrace.build_of_trace
assert_kernel_only TetraStereo.OneCenter.OfficialCIPSourceTree.mem_occurrences_of_subtreeAt?_eq_some
assert_kernel_only TetraStereo.OneCenter.OfficialCIPSourceTree.mem_hierarchyAddresses_of_occurrence
assert_kernel_only TetraStereo.OneCenter.OfficialCIPSourceTree.declarativeAddressing_address
assert_kernel_only TetraStereo.OneCenter.OfficialCIPSourceTree.declarativeAddressing_dense
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.generatedSourceTree_source_graphGenerated
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.generatedSourceTree_source_current_isSome
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.generatedSourceTree_source_current
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_originalRootArm
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.armObservation
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.arm_root_nodeObservation_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.root_nodeObservation_eq
assert_kernel_only TetraStereo.OneCenter.rowValueAt_cons_eq_entriesAtSlot
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.decoratedSubtreeAt?
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.observeAt
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.table_length_le_localizedTreeChildLayerCount
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.tableValue_table_eq_observeAt
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.toOfficialSourceTree_subtreeAt?
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.realizes_of_decoratedSubtreeAt?
assert_kernel_only TetraStereo.OneCenter.MoleculeGraph.officialNodeAtomLabel_first_eq_nodeAtomicNumber
assert_kernel_only TetraStereo.OneCenter.MoleculeGraph.officialNodeAtomLabel_second_eq_nodeAtomicMass
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.armTableColumn
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.armSourceObservation
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.nodeObservation_eq_actualTableValue
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.decoratedSubtreeAt?_append
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.decoratedSubtreeAt?_cons_some
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.observeAt_cons
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.tableValue_table_cons
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.realizes_of_decoratedSubtreeAt?_rec
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.hasAddress_atomicNumber_table_iff_subtree
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.wellFormedRuleMajorKey_of_tableMatch
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.encodedObservation_cons_of_key
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.trace_of_subtree
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.armGraph
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.decoratedSubtree_of_node
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.denseAt_of_lookup
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.armTableValue_eq_armObservation
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.nodeObservation_eq_priorityValue_armObservation
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.arm_nil_observation
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.arm_terminal_bridge
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.arm_node_bridge
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.arm_root_represents
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.arm_canonicalAddressing
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.represents_of_bounds
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.arm_compare_eq_compare_vector
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.arm_compare_ne_lt_iff_rightRuleKey_le
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedConstitutionalProblemData
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedConstitutionalProblemData_expansionsFaithful
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedConstitutionalProblemData_expansionsExist
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedConstitutionalProblemData_withCanonicalAddressing
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.armTableColumn_eq_table
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.armAddressing
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.occupied_iff_decoratedSubtreeAt?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.occupied_iff_hasAddress
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.addressLabel_eq_none_of_unoccupied
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.tableValue_eq_zero_of_unoccupied
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.ruleValue_addressLabel_eq_tableValue
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.ruleValue_addressLabel_eq_tableValue_of_ne_rule1b
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.hierarchyOutcome_rule1a_iff_compare
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.hierarchyOutcome_rule1b_iff_compare
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.hierarchyOutcome_rule2_iff_compare
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.ruleOutcome_iff_hierarchyOutcome
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.ruleOutcome_rule1a_iff_compare
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.ruleOutcome_rule1b_iff_compare
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.ruleOutcome_rule2_iff_compare
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.compare_eq_gt_iff_constitutionalHigher
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.compare_eq_eq_iff_constitutionalTied
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OriginalRootArm.compare_eq_lt_iff_reverse_constitutionalHigher
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_originalRootArms_constitutionalPriority
