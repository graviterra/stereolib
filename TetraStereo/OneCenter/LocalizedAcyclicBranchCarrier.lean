import TetraStereo.OneCenter.LocalizedOccurrenceRerootFrame
import TetraStereo.OneCenter.LocalizedOccurrenceCarrierCoverage
import TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# The physical outward branch carrier on a finite acyclic single-bond molecule

This module connects the executable localized CIP occurrence carrier to the physical graph of a
finite molecular graph.  The central domain is the honest chemical one: a certified localized CIP
input whose actual covalent bond orders are all one on positive adjacencies
(`MoleculeGraph.SimpleBonded`) and whose underlying simple graph is acyclic
(`MoleculeGraph.Acyclic`).  Neither rings nor multiple bonds are assumed away in the occurrence
machinery; instead their absence from this domain is *proved* from the actual executable walk.

The first result is the graph-theoretic branch disjointness needed by rooted branch symmetry:
deleting a tetrahedral center separates its four ligand branches because two branches sharing a
physical atom would produce two distinct simple paths between the center and that atom.

The rest of the module is developed in the namespace `CertifiedLocalizedCIPInput`.  It proves that
the executable official expansion of a real atom in this domain is a simple physical path: no ring
duplicate and no positive multiple-bond copy can occur.  Consequently every physical atom in a
deleted-root connected component is represented by an occurrence whose `node.current?` is that
atom; this module proves the coverage (surjectivity) half at the sharp atom-count fuel.  Uniqueness
at a fixed original root (hence the full bijection) is owned by the companion module
`LocalizedAcyclicCarrierInjectivity.lean`; it is not claimed here.  The root occurrence is the
distinguished `localizedAtomRootOccurrence`.

Explicit hydrogens are ordinary atom vertices throughout: they are represented exactly like any
other physical atom.  Implicit hydrogens are not vertices of `MoleculeGraph` and therefore are not
represented by this carrier; statements below never claim to count them.
-/

namespace TetraStereo.OneCenter

open RootedTetrahedralBranchSymmetry

namespace CertifiedLocalizedCIPInput

/-- A certified localized input together with the physical single-bond acyclic hypotheses used by
the carrier bijection. -/
structure AcyclicSingleBondDomain (input : CertifiedLocalizedCIPInput) : Prop where
  acyclic : input.moleculeGraph.Acyclic
  singleBonded : input.moleculeGraph.SimpleBonded

/-- **Physical branch disjointness at a tetrahedral root.**  In an acyclic molecular graph the
four ligand branches obtained by deleting a tetrahedral center are pairwise disjoint.

The proof is the standard tree uniqueness argument.  Two branch walks from distinct ligand atoms
to the same physical atom, each avoiding the center, become two simple center-rooted paths after
prepending the corresponding center-ligand edge.  Acyclicity forces those paths to be equal, so
their first vertices, the two ligand atoms, are equal; ligand injectivity then makes the indices
equal. -/
theorem pairwiseDisjointLigandBranches_of_acyclic
    (input : CertifiedLocalizedCIPInput)
    (acyclic : input.moleculeGraph.Acyclic)
    (center : input.detectedMultiCenterMolecule.Center) :
    PairwiseDisjointLigandBranches input.detectedMultiCenterMolecule center := by
  intro i j distinct v leftReaches rightReaches
  let m := input.detectedMultiCenterMolecule
  let graph := input.moleculeGraph.underlyingSimpleGraph
  obtain ⟨leftWalk, leftAvoids⟩ := leftReaches
  obtain ⟨rightWalk, rightAvoids⟩ := rightReaches
  let leftPath := leftWalk.toPath
  let rightPath := rightWalk.toPath
  have leftPathAvoids : center.1 ∉ leftPath.1.support := by
    intro present
    exact leftAvoids (SimpleGraph.Walk.support_toPath_subset leftWalk present)
  have rightPathAvoids : center.1 ∉ rightPath.1.support := by
    intro present
    exact rightAvoids (SimpleGraph.Walk.support_toPath_subset rightWalk present)
  let leftCenterWalk : graph.Walk center.1 v :=
    SimpleGraph.Walk.cons (m.ligandAtomAt_adj center i) leftPath.1
  let rightCenterWalk : graph.Walk center.1 v :=
    SimpleGraph.Walk.cons (m.ligandAtomAt_adj center j) rightPath.1
  have leftCenterPath : leftCenterWalk.IsPath :=
    (SimpleGraph.Walk.cons_isPath_iff (m.ligandAtomAt_adj center i) leftPath.1).2
      ⟨leftPath.2, leftPathAvoids⟩
  have rightCenterPath : rightCenterWalk.IsPath :=
    (SimpleGraph.Walk.cons_isPath_iff (m.ligandAtomAt_adj center j) rightPath.1).2
      ⟨rightPath.2, rightPathAvoids⟩
  let leftCenter : graph.Path center.1 v := ⟨leftCenterWalk, leftCenterPath⟩
  let rightCenter : graph.Path center.1 v := ⟨rightCenterWalk, rightCenterPath⟩
  have pathsEqual := input.moleculeGraph.acyclic_path_unique acyclic leftCenter rightCenter
  have walksEqual : leftCenterWalk = rightCenterWalk := congrArg Subtype.val pathsEqual
  have supportsEqual : leftCenterWalk.support = rightCenterWalk.support :=
    congrArg SimpleGraph.Walk.support walksEqual
  have vertexEqual : leftCenterWalk.getVert 1 = rightCenterWalk.getVert 1 :=
    congrArg (fun walk => walk.getVert 1) walksEqual
  have leftVertex : leftCenterWalk.getVert 1 = m.ligandAtomAt center i := by
    simp [leftCenterWalk]
  have rightVertex : rightCenterWalk.getVert 1 = m.ligandAtomAt center j := by
    simp [rightCenterWalk]
  rw [leftVertex, rightVertex] at vertexEqual
  exact distinct (m.ligandAtomAt_injective center vertexEqual)

/-- Domain-specialized form of physical branch disjointness, phrased for an automatically detected
tetrahedral center of the certified input. -/
theorem pairwiseDisjointLigandBranches_of_acyclic_tetrahedralCenter
    (input : CertifiedLocalizedCIPInput)
    (acyclic : input.moleculeGraph.Acyclic)
    (center : input.TetrahedralCenter) :
    PairwiseDisjointLigandBranches input.detectedMultiCenterMolecule ⟨center.1, center.2⟩ :=
  input.pairwiseDisjointLigandBranches_of_acyclic acyclic ⟨center.1, center.2⟩

/-! ## Real official nodes as simple physical paths

The executable official node stores a history in reverse walk order.  The following invariant
records that, for a real node, the history is exactly the reverse support of an actual simple walk
from the original root to `node.current?`, and that the stored parent is the walk's penultimate
atom.  This is the bridge from runtime provenance data to physical graph paths. -/

/-- A real official node whose history is the reverse of an actual simple root walk. -/
def RealPathNode (input : CertifiedLocalizedCIPInput) (root : input.Atom)
    (node : OfficialCIPNode input.Atom) : Prop :=
  ∃ (current : input.Atom)
      (path : input.moleculeGraph.underlyingSimpleGraph.Walk root current),
    node.current? = some current ∧
      node.history.head? = some current ∧
      node.provenance = OfficialCIPNodeProvenance.realAtom ∧
      path.IsPath ∧
      path.support.reverse = node.history ∧
      (∀ parent, node.parent? = some parent → path.penultimate = parent)

/-- The root node is a real empty physical path. -/
theorem realPathNode_root (input : CertifiedLocalizedCIPInput) (root : input.Atom) :
    input.RealPathNode root (OfficialCIPNode.root root) := by
  refine ⟨root, SimpleGraph.Walk.nil, rfl, rfl, rfl, by simp, by simp [OfficialCIPNode.root], ?_⟩
  intro parent parentObserved
  simp [OfficialCIPNode.root, OfficialCIPNode.parent?] at parentObserved

/-- A raw child copy of a real node is positively bonded to the observed current atom. -/
theorem mem_executableOfficialChildCopies_adjacent_bound
    (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) (current next : input.Atom) (copyIndex : Nat)
    (currentObserved : node.current? = some current)
    (present : (next, copyIndex) ∈ input.executableOfficialChildCopies node) :
    input.moleculeGraph.Adj current next ∧
      copyIndex < input.moleculeGraph.bond current next := by
  unfold executableOfficialChildCopies at present
  rw [currentObserved] at present
  cases parentObserved : node.parent? with
  | none =>
      simp only [parentObserved] at present
      exact (input.mem_executableOfficialNeighborCopies_iff current next copyIndex).mp present
  | some parent =>
      simp only [parentObserved] at present
      exact (input.mem_executableOfficialNeighborCopies_iff current next copyIndex).mp
        (List.mem_of_mem_filter present)

/-- The executable raw child copies remove the zero-copy back edge to the stored parent. -/
theorem not_parent_of_zero_mem_executableOfficialChildCopies
    (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) (next parent : input.Atom)
    (present : (next, 0) ∈ input.executableOfficialChildCopies node)
    (parentObserved : node.parent? = some parent) :
    next ≠ parent := by
  intro same
  subst next
  unfold executableOfficialChildCopies at present
  cases currentObserved : node.current? with
  | none => simp [currentObserved] at present
  | some current =>
      simp [currentObserved, parentObserved] at present

/-- **A real zero-copy step cannot revisit the stored history.**  At a non-root node the actual
support is a simple path ending at the observed current atom; the acyclicity lemma puts a
non-parent neighbor of the endpoint outside that support, while the history is exactly the reverse
support.  At the root the only history atom is the current atom, and adjacency is loopless. -/
theorem not_mem_history_of_real_zero_step
    (input : CertifiedLocalizedCIPInput)
    (acyclic : input.moleculeGraph.Acyclic)
    {root : input.Atom} {node : OfficialCIPNode input.Atom}
    {current next : input.Atom}
    (real : input.RealPathNode root node)
    (currentObserved : node.current? = some current)
    (adjacent : input.moleculeGraph.Adj current next)
    (notParent : node.parent? ≠ some next) :
    next ∉ node.history := by
  obtain ⟨current', path, currentObserved', headObserved, _provenance, pathIsPath,
    supportReverse, penultimateEq⟩ := real
  have currentEq : current = current' :=
    Option.some.inj (currentObserved.symm.trans currentObserved')
  subst current'
  intro visited
  have inSupport : next ∈ path.support := by
    have reversed : next ∈ path.support.reverse := by
      rw [supportReverse]
      exact visited
    simpa using reversed
  cases parentObserved : node.parent? with
  | none =>
      have singleton : node.history = [current] := by
        cases historyCase : node.history with
        | nil => simp [historyCase] at headObserved
        | cons first rest =>
            cases rest with
            | nil =>
                have firstEq : first = current := by
                  simpa [historyCase] using headObserved
                subst first
                rfl
            | cons second tail =>
                simp [OfficialCIPNode.parent?, historyCase] at parentObserved
      have nextEq : next = current := by simpa [singleton] using visited
      have adjacentGraph : input.moleculeGraph.underlyingSimpleGraph.Adj current next :=
        adjacent
      exact SimpleGraph.Adj.ne' adjacentGraph nextEq
  | some parent =>
      have nextNeParent : next ≠ parent := by
        intro nextEq
        exact notParent (by rw [nextEq]; exact parentObserved)
      have outside :=
        MoleculeGraph.Acyclic.not_mem_support_of_adj_ne_penultimate
          input.moleculeGraph acyclic pathIsPath
          (penultimateEq parent parentObserved) adjacent nextNeParent
      exact outside inSupport

/-- **One executable step stays a simple physical path.**  In an acyclic single-bond graph the
zero-copy executable child of a real path node is another real path node.  A visit to an earlier
history atom is impossible by `not_mem_history_of_real_zero_step`.  The single-bond hypothesis
forces the copy index to zero, so a positive multiple-bond copy cannot occur either. -/
theorem realPathNode_step
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {root : input.Atom} {node child : OfficialCIPNode input.Atom} {slot : Nat}
    (real : input.RealPathNode root node)
    (childAtSlot : (child, slot) ∈
      (input.executableOfficialCIPChildren node).zipIdx) :
    input.RealPathNode root child := by
  obtain ⟨current, path, currentObserved, headObserved, provenance, pathIsPath,
    supportReverse, penultimateEq⟩ := real
  have realNode : input.RealPathNode root node :=
    ⟨current, path, currentObserved, headObserved, provenance, pathIsPath,
      supportReverse, penultimateEq⟩
  have childPresent : child ∈ input.executableOfficialCIPChildren node :=
    List.fst_mem_of_mem_zipIdx childAtSlot
  have nonduplicate : node.isDuplicateLeaf = false :=
    input.isDuplicateLeaf_eq_false_of_provenance_real node provenance
  unfold executableOfficialCIPChildren at childPresent
  rw [if_neg (by simpa using nonduplicate), List.mem_map] at childPresent
  obtain ⟨copy, copyPresent, childIdentity⟩ := childPresent
  obtain ⟨next, copyIndex⟩ := copy
  change node.extend next copyIndex = child at childIdentity
  obtain ⟨adjacent, bound⟩ :=
    input.mem_executableOfficialChildCopies_adjacent_bound node current next copyIndex
      currentObserved copyPresent
  have bondOne := singleBonded current next adjacent
  have copyZero : copyIndex = 0 := by
    have boundOne : copyIndex < 1 := by simpa [bondOne] using bound
    omega
  subst copyIndex
  have notParent : ∀ parent, node.parent? = some parent → next ≠ parent := by
    intro parent parentObserved
    exact input.not_parent_of_zero_mem_executableOfficialChildCopies node next parent
      copyPresent parentObserved
  have noParent : node.parent? ≠ some next := by
    intro equality
    cases parentObserved : node.parent? with
    | none =>
        rw [parentObserved] at equality
        simp at equality
    | some parent =>
        have parentEq : parent = next :=
          Option.some.inj (by simpa [parentObserved] using equality)
        exact notParent parent parentObserved parentEq.symm
  have fresh : next ∉ node.history :=
    input.not_mem_history_of_real_zero_step acyclic realNode currentObserved adjacent noParent
  have historyHead : node.history = current :: node.history.tail := by
    cases historyCase : node.history with
    | nil => simp [historyCase] at headObserved
    | cons first rest =>
        have firstEq : first = current := by
          simpa [historyCase] using headObserved
        subst first
        rfl
  have newReal : input.RealPathNode root (node.extend next 0) := by
    refine ⟨next, path.concat adjacent, by simp, by simp, ?_, ?_, ?_, ?_⟩
    · rw [OfficialCIPNode.extend_provenance]
      exact OfficialCIPNode.childProvenance_real node next fresh
    · have outside : next ∉ path.support := by
        intro present
        exact fresh (by
          rw [← supportReverse]
          exact List.mem_reverse.mpr present)
      exact pathIsPath.concat outside adjacent
    · simp [OfficialCIPNode.extend_history, SimpleGraph.Walk.support_concat, supportReverse]
    · intro parent parentObserved
      simp only [OfficialCIPNode.parent?] at parentObserved
      rw [OfficialCIPNode.extend_history, historyHead] at parentObserved
      change some current = some parent at parentObserved
      have parentEq : parent = current := (Option.some.inj parentObserved).symm
      subst parent
      simp [SimpleGraph.Walk.penultimate_concat]
  simpa [childIdentity] using newReal

/-- Every addressed simple occurrence is a real path node.  This is the graph-path content of
`SimpleOccurrencePath`, independent of any bond-order or acyclicity hypothesis. -/
theorem simpleOccurrencePath_realPathNode
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (path : SimpleOccurrencePath input root node address) :
    input.RealPathNode root node := by
  induction path with
  | root => exact input.realPathNode_root root
  | step earlier currentObserved adjacent notParent fresh ih =>
      rename_i branchNode branchAddress branchCurrent branchNext
      obtain ⟨observed, walk, observedEq, headObserved, provenance, walkIsPath, supportReverse,
        _penultimateEq⟩ := ih
      have currentEq : branchCurrent = observed :=
        Option.some.inj (currentObserved.symm.trans observedEq)
      subst observed
      have historyHead : branchNode.history = branchCurrent :: branchNode.history.tail := by
        cases historyCase : branchNode.history with
        | nil => simp [historyCase] at headObserved
        | cons first rest =>
            have firstEq : first = branchCurrent := by
              simpa [historyCase] using headObserved
            subst first
            rfl
      refine ⟨branchNext, walk.concat adjacent, by simp, by simp, ?_, ?_, ?_, ?_⟩
      · rw [OfficialCIPNode.extend_provenance]
        exact OfficialCIPNode.childProvenance_real branchNode branchNext fresh
      · have outside : branchNext ∉ walk.support := by
          intro present
          exact fresh (by
            rw [← supportReverse]
            exact List.mem_reverse.mpr present)
        exact walkIsPath.concat outside adjacent
      · simp [OfficialCIPNode.extend_history, SimpleGraph.Walk.support_concat, supportReverse]
      · intro parent parentObserved
        simp only [OfficialCIPNode.parent?] at parentObserved
        rw [OfficialCIPNode.extend_history, historyHead] at parentObserved
        change some branchCurrent = some parent at parentObserved
        have parentEq : parent = branchCurrent := (Option.some.inj parentObserved).symm
        subst parent
        simp [SimpleGraph.Walk.penultimate_concat]

/-- Address uniqueness for simple occurrences with the same final official node.  In the
single-bond setting each physical step has a unique executable raw-copy slot, so the full sibling
address is determined by the final node.  This is the injectivity half of the physical branch
coordinate; it does not assume any carrier membership. -/
theorem simpleOccurrencePath_address_unique
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {leftNode rightNode : OfficialCIPNode input.Atom}
    {leftAddress rightAddress : List Nat}
    (left : SimpleOccurrencePath input root leftNode leftAddress)
    (right : SimpleOccurrencePath input root rightNode rightAddress)
    (sameNode : leftNode = rightNode) :
    leftAddress = rightAddress := by
  induction left generalizing rightNode rightAddress with
  | root =>
      cases right with
      | root => rfl
      | step rightEarlier rightCurrentObserved rightAdjacent rightNotParent rightFresh =>
          rename_i rnode raddress rcurrent rnext
          have currentEq : root = rnext := by
            have observed := congrArg OfficialCIPNode.current? sameNode
            have someEq : some root = some rnext := by
              simpa [OfficialCIPNode.root, OfficialCIPNode.extend_current?] using observed
            exact Option.some.inj someEq
          obtain ⟨_observed, walk, _observedEq, _head, _provenance, _simple, supportReverse,
            _penultimate⟩ := input.simpleOccurrencePath_realPathNode rightEarlier
          have rootMem : root ∈ rnode.history := by
            rw [← supportReverse]
            exact List.mem_reverse.mpr (SimpleGraph.Walk.start_mem_support walk)
          exact False.elim (rightFresh (currentEq ▸ rootMem))
  | step earlier currentObserved adjacent notParent fresh ih =>
      rename_i node address current next
      cases right with
      | root =>
          have currentEq : next = root := by
            have observed := congrArg OfficialCIPNode.current? sameNode
            have someEq : some next = some root := by
              simpa [OfficialCIPNode.root, OfficialCIPNode.extend_current?] using observed
            exact Option.some.inj someEq
          obtain ⟨_observed, walk, _observedEq, _head, _provenance, _simple, supportReverse,
            _penultimate⟩ := input.simpleOccurrencePath_realPathNode earlier
          have rootMem : root ∈ node.history := by
            rw [← supportReverse]
            exact List.mem_reverse.mpr (SimpleGraph.Walk.start_mem_support walk)
          exact False.elim (fresh (currentEq ▸ rootMem))
      | step rightEarlier rightCurrentObserved rightAdjacent rightNotParent rightFresh =>
          rename_i priorNode priorAddress priorCurrent priorNext
          have nextEq : next = priorNext := by
            have observed := congrArg OfficialCIPNode.current? sameNode
            have someEq : some next = some priorNext := by
              simpa [OfficialCIPNode.extend_current?] using observed
            exact Option.some.inj someEq
          have historyEq : node.history = priorNode.history := by
            have histories := congrArg OfficialCIPNode.history sameNode
            simp only [OfficialCIPNode.extend_history] at histories
            exact (List.cons.inj histories).2
          obtain ⟨currentAtom, _walk, _currentObserved, headObserved, _provenance, _simple,
            _support, _penultimate⟩ := input.simpleOccurrencePath_realPathNode earlier
          obtain ⟨rightCurrentAtom, _rightWalk, _rightCurrentObserved, rightHeadObserved,
            _rightProvenance, _rightSimple, _rightSupport, _rightPenultimate⟩ :=
            input.simpleOccurrencePath_realPathNode rightEarlier
          have headEq : some currentAtom = some rightCurrentAtom := by
            rw [← headObserved, historyEq, rightHeadObserved]
          have atomEq : currentAtom = rightCurrentAtom := Option.some.inj headEq
          have nodeEq : node = priorNode := by
            cases node with
            | mk nodeCurrent nodeHistory nodeProvenance =>
                cases priorNode with
                | mk priorCurrentField priorHistory priorProvenanceField =>
                    simp_all
          have addressEq : address = priorAddress := ih rightEarlier nodeEq
          have slotEq : input.executableOfficialChildCopySlot node next 0 =
              input.executableOfficialChildCopySlot priorNode priorNext 0 := by
            rw [nodeEq, nextEq]
          rw [addressEq, slotEq]

/-- The stored parent of an official node is literally an atom of its stored history. -/
theorem parent_mem_history_of_parent?
    (input : CertifiedLocalizedCIPInput)
    {node : OfficialCIPNode input.Atom} {parent : input.Atom}
    (parentObserved : node.parent? = some parent) :
    parent ∈ node.history := by
  cases node with
  | mk current history provenance =>
      cases history with
      | nil => simp [OfficialCIPNode.parent?] at parentObserved
      | cons first rest =>
          cases rest with
          | nil => simp [OfficialCIPNode.parent?] at parentObserved
          | cons second tail =>
              simp [OfficialCIPNode.parent?] at parentObserved
              subst parent
              simp

/-- A duplicate-free chain of physical atoms starting at the current atom of a simple occurrence
extends that occurrence along exactly that chain.  The side condition says the remaining chain is
disjoint from the already stored history, which is the invariant maintained at every step.  No
bond-order or acyclicity assumption is used: freshness comes from the global duplicate-freeness,
and the official parent edge is excluded because its stored parent is already in the history. -/
theorem simpleOccurrencePath_of_chain_aux
    (input : CertifiedLocalizedCIPInput) {root : input.Atom} :
    ∀ (current : input.Atom) (rest : List input.Atom)
      (node : OfficialCIPNode input.Atom) (address : List Nat),
      SimpleOccurrencePath input root node address →
      node.current? = some current →
      (current :: rest).Nodup →
      (current :: rest).IsChain (fun a b => input.moleculeGraph.Adj a b) →
      (∀ x ∈ node.history, x ∉ rest) →
      ∃ finalNode finalAddress,
        SimpleOccurrencePath input root finalNode finalAddress ∧
        finalNode.current? = (current :: rest).getLast? := by
  intro current rest
  induction rest generalizing current with
  | nil =>
      intro node address path currentObserved _nodup _chain _disjoint
      refine ⟨node, address, path, ?_⟩
      simpa using currentObserved
  | cons next tail inductionHypothesis =>
      intro node address path currentObserved nodup chain disjoint
      have nodupTail : (next :: tail).Nodup := (List.nodup_cons.mp nodup).2
      have nextNotTail : next ∉ tail := (List.nodup_cons.mp nodupTail).1
      have adjacent : input.moleculeGraph.Adj current next := chain.rel_head
      have fresh : next ∉ node.history := by
        intro present
        exact disjoint next present List.mem_cons_self
      have notParent : node.parent? ≠ some next := by
        intro parentObserved
        exact disjoint next
          (input.parent_mem_history_of_parent? parentObserved)
          List.mem_cons_self
      have nextPath : SimpleOccurrencePath input root (node.extend next 0)
          (address ++ [input.executableOfficialChildCopySlot node next 0]) :=
        SimpleOccurrencePath.step path currentObserved adjacent notParent fresh
      have nextDisjoint : ∀ x ∈ (node.extend next 0).history, x ∉ tail := by
        intro x present inTail
        rw [OfficialCIPNode.extend_history] at present
        rcases List.mem_cons.mp present with same | earlier
        · subst same
          exact nextNotTail inTail
        · exact disjoint x earlier (List.mem_cons_of_mem next inTail)
      obtain ⟨finalNode, finalAddress, finalPath, finalObserved⟩ :=
        inductionHypothesis next (node.extend next 0)
          (address ++ [input.executableOfficialChildCopySlot node next 0])
          nextPath rfl nodupTail chain.tail nextDisjoint
      refine ⟨finalNode, finalAddress, finalPath, ?_⟩
      simpa using finalObserved

/-- Every simple physical walk from an atom root yields a simple occurrence path ending at the
walk's final atom.  The occurrence address is the executable sibling address produced along the
walk; the physical walk itself only has to be duplicate-free. -/
theorem simpleOccurrencePath_of_simple_walk
    (input : CertifiedLocalizedCIPInput) {root v : input.Atom}
    (walk : input.moleculeGraph.underlyingSimpleGraph.Walk root v)
    (simple : walk.IsPath) :
    ∃ node address,
      SimpleOccurrencePath input root node address ∧ node.current? = some v := by
  let rest := walk.support.tail
  have supportCons : walk.support = root :: rest := by
    cases walk with
    | nil => simp [rest, SimpleGraph.Walk.support]
    | cons adjacent tail => rfl
  have nodup : (root :: rest).Nodup := by
    simpa [supportCons] using simple.support_nodup
  have chain : (root :: rest).IsChain
      (fun a b => input.moleculeGraph.Adj a b) := by
    simpa [supportCons] using SimpleGraph.Walk.isChain_adj_support walk
  have disjoint : ∀ x ∈ (OfficialCIPNode.root root).history, x ∉ rest := by
    intro x present inRest
    have xRoot : x = root := by
      simpa [OfficialCIPNode.root] using present
    have rootNotRest : root ∉ rest := (List.nodup_cons.mp nodup).1
    exact rootNotRest (by simpa [xRoot] using inRest)
  obtain ⟨node, address, path, observed⟩ :=
    input.simpleOccurrencePath_of_chain_aux root rest (OfficialCIPNode.root root) []
      SimpleOccurrencePath.root rfl nodup chain disjoint
  have lastEq : (root :: rest).getLast? = some v := by
    rw [← supportCons]
    rw [List.getLast?_eq_getLast_of_ne_nil (by cases walk <;> simp [SimpleGraph.Walk.support])]
    exact congrArg some (SimpleGraph.Walk.getLast_support walk)
  exact ⟨node, address, path, by rw [observed, lastEq]⟩

/-- Every simple physical walk from a root atom is represented by an actual occurrence in the
finite carrier at the sharp atom-count fuel, with the exact terminal atom.  This is the
original-root surjectivity half of the branch bijection; terminal physical atoms are included
because the statement is uniform in the walk endpoint. -/
theorem carrierOccurrence_exists_of_simple_walk
    (input : CertifiedLocalizedCIPInput) {root target : input.Atom}
    (walk : input.moleculeGraph.underlyingSimpleGraph.Walk root target)
    (simple : walk.IsPath) :
    ∃ occurrence : input.LocalizedCIPOccurrence
        (input.certified.input.molecule.atomCount),
      occurrence.1.root = root ∧
        occurrence.1.node.current? = some target ∧
        occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
        occurrence.1.address.length ≤ input.certified.input.molecule.atomCount ∧
        0 < occurrence.1.remaining ∧
        occurrence ∈ input.localizedOccurrenceCarrier
          (input.certified.input.molecule.atomCount) := by
  obtain ⟨node, address, path, observed⟩ :=
    input.simpleOccurrencePath_of_simple_walk walk simple
  let legitimate : LegitimateOccurrence input root node address :=
    LegitimateOccurrence.simple path
  let carrier := input.legitimateOccurrenceCarrier legitimate
  refine ⟨carrier, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [carrier, legitimate] using observed
  · simpa [carrier, legitimate] using input.simpleOccurrencePath_provenance path
  · simpa [carrier, legitimate] using
      input.legitimateOccurrence_address_length_le_atomCount legitimate
  · simpa [carrier, legitimate] using
      input.legitimateOccurrenceCarrier_remaining_pos legitimate
  · simpa [carrier, legitimate] using
      input.legitimateOccurrenceCarrier_mem_carrier legitimate

/-- **Deleted-root physical branch coverage.**  Every physical atom in the component of a root
neighbor after deleting the root is represented by an actual carrier occurrence rooted at the
original root.  The hypotheses are the actual chemistry: a positive root-ligand bond, a physical
walk from that ligand to the target which is simple and never returns to the root.  No occurrence,
address, or coverage fact is assumed; the occurrence is built by the executable expansion along
the walk. -/
theorem carrierOccurrence_exists_of_avoiding_walk
    (input : CertifiedLocalizedCIPInput) {root ligand target : input.Atom}
    (adjacent : input.moleculeGraph.Adj root ligand)
    (walk : input.moleculeGraph.underlyingSimpleGraph.Walk ligand target)
    (simple : walk.IsPath)
    (avoidsRoot : root ∉ walk.support) :
    ∃ occurrence : input.LocalizedCIPOccurrence
        (input.certified.input.molecule.atomCount),
      occurrence.1.root = root ∧
        occurrence.1.node.current? = some target ∧
        occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
        occurrence.1.address.length ≤ input.certified.input.molecule.atomCount ∧
        0 < occurrence.1.remaining ∧
        occurrence ∈ input.localizedOccurrenceCarrier
          (input.certified.input.molecule.atomCount) := by
  let fullWalk : input.moleculeGraph.underlyingSimpleGraph.Walk root target :=
    SimpleGraph.Walk.cons adjacent walk
  have fullSimple : fullWalk.IsPath :=
    (SimpleGraph.Walk.cons_isPath_iff adjacent walk).2 ⟨simple, avoidsRoot⟩
  exact input.carrierOccurrence_exists_of_simple_walk fullWalk fullSimple

/-- **Outward ligand-branch coverage at a detected tetrahedral center.**  Any physical atom in a
ligand branch of the detected multi-center graph (a walk from `ligandAtomAt center i` to the atom
which avoids the center) is represented by an actual carrier occurrence rooted at that physical
center.  This is the root-outward form consumed by branch comparison; it makes no reroot or
inward claim and assumes no carrier membership. -/
theorem carrierOccurrence_exists_of_ligandBranch
    (input : CertifiedLocalizedCIPInput)
    {center : input.detectedMultiCenterMolecule.Center} {i : Fin 4}
    {target : input.Atom}
    (reaches : LigandBranchReaches input.detectedMultiCenterMolecule center i target) :
    ∃ occurrence : input.LocalizedCIPOccurrence
        (input.certified.input.molecule.atomCount),
      occurrence.1.root = center.1 ∧
        occurrence.1.node.current? = some target ∧
        occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
        occurrence.1.address.length ≤ input.certified.input.molecule.atomCount ∧
        0 < occurrence.1.remaining ∧
        occurrence ∈ input.localizedOccurrenceCarrier
          (input.certified.input.molecule.atomCount) := by
  obtain ⟨walk, avoidsCenter⟩ := reaches
  let path := walk.toPath
  have pathAvoids : center.1 ∉ path.1.support := by
    intro present
    exact avoidsCenter (SimpleGraph.Walk.support_toPath_subset walk present)
  exact input.carrierOccurrence_exists_of_avoiding_walk
    (input.detectedMultiCenterMolecule.ligandAtomAt_adj center i)
    path.1 path.2 pathAvoids

/-- Chain extension starting from an arbitrary official node.  The result is an executable
descendant of that supplied start, with the exact appended sibling suffix, unchanged real
provenance, and the terminal atom of the supplied physical chain.  This is the parent-side form
needed by a directed edge cut: the start node can be `rootFromEdge parent current`, which already
stores the first cut edge, so the returned address is relative to the cut rather than to the
original atom root. -/
theorem unboundedOfficialSubtree_of_chain_aux
    (input : CertifiedLocalizedCIPInput) {start : OfficialCIPNode input.Atom} :
    ∀ (current : input.Atom) (rest : List input.Atom)
      (node : OfficialCIPNode input.Atom) (address : List Nat),
      input.UnboundedOfficialSubtree start address node →
      node.current? = some current →
      node.provenance = OfficialCIPNodeProvenance.realAtom →
      (current :: rest).Nodup →
      (current :: rest).IsChain (fun a b => input.moleculeGraph.Adj a b) →
      (∀ x ∈ node.history, x ∉ rest) →
      ∃ finalNode suffix,
        input.UnboundedOfficialSubtree start (address ++ suffix) finalNode ∧
        suffix.length = rest.length ∧
        finalNode.current? = (current :: rest).getLast? ∧
        finalNode.provenance = OfficialCIPNodeProvenance.realAtom := by
  intro current rest
  induction rest generalizing current with
  | nil =>
      intro node address reachable currentObserved provenance _nodup _chain _disjoint
      exact ⟨node, [], by simpa using reachable, rfl, by simpa using currentObserved,
        provenance⟩
  | cons next tail inductionHypothesis =>
      intro node address reachable currentObserved provenance nodup chain disjoint
      have nodupTail : (next :: tail).Nodup := (List.nodup_cons.mp nodup).2
      have nextNotTail : next ∉ tail := (List.nodup_cons.mp nodupTail).1
      have adjacent : input.moleculeGraph.Adj current next := chain.rel_head
      have fresh : next ∉ node.history := by
        intro present
        exact disjoint next present List.mem_cons_self
      have notParent : node.parent? ≠ some next := by
        intro parentObserved
        exact disjoint next
          (input.parent_mem_history_of_parent? parentObserved)
          List.mem_cons_self
      have copyPresent := input.mem_executableOfficialChildCopies_of_adjacent
        node current next 0 currentObserved adjacent adjacent (Or.inr notParent)
      have nonduplicate :=
        input.isDuplicateLeaf_eq_false_of_provenance_real node provenance
      have atSlot := input.executableOfficialChildCopySlot_mem node next 0
        nonduplicate copyPresent
      have extendedReach := input.unboundedOfficialSubtree_append_last reachable atSlot
      have extendedProvenance : (node.extend next 0).provenance =
          OfficialCIPNodeProvenance.realAtom := by
        rw [OfficialCIPNode.extend_provenance]
        exact OfficialCIPNode.childProvenance_real node next fresh
      have nextDisjoint : ∀ x ∈ (node.extend next 0).history, x ∉ tail := by
        intro x present inTail
        rw [OfficialCIPNode.extend_history] at present
        rcases List.mem_cons.mp present with same | earlier
        · subst same
          exact nextNotTail inTail
        · exact disjoint x earlier (List.mem_cons_of_mem next inTail)
      obtain ⟨finalNode, suffix, finalReach, suffixLength, finalObserved,
        finalProvenance⟩ :=
        inductionHypothesis next (node.extend next 0)
          (address ++ [input.executableOfficialChildCopySlot node next 0])
          extendedReach rfl extendedProvenance nodupTail chain.tail nextDisjoint
      refine ⟨finalNode,
        input.executableOfficialChildCopySlot node next 0 :: suffix, ?_, ?_, ?_,
        finalProvenance⟩
      · have addressEq : address ++
            (input.executableOfficialChildCopySlot node next 0 :: suffix) =
            (address ++ [input.executableOfficialChildCopySlot node next 0]) ++ suffix := by
          simp [List.append_assoc]
        rw [addressEq]
        exact finalReach
      · simpa using congrArg Nat.succ suffixLength
      · simpa using finalObserved

/-- Directed-edge-cut coverage.  Given a positively bonded cut `parent -- current` and a physical
simple walk from `current` to `target` that never returns to `parent`, there is an actual
executable descendant of the edge-rooted official node `rootFromEdge parent current` whose
current atom is exactly `target`.  The address is measured from the cut edge, and its length is
the number of physical steps after the first cut edge.  The walk's duplicate-freeness is the
actual acyclicity-side premise; no carrier membership or completed-expansion result is assumed. -/
theorem unboundedOfficialSubtree_of_walk_avoiding
    (input : CertifiedLocalizedCIPInput) {parent current target : input.Atom}
    (adjacent : input.moleculeGraph.Adj parent current)
    (walk : input.moleculeGraph.underlyingSimpleGraph.Walk current target)
    (simple : walk.IsPath)
    (avoidsParent : parent ∉ walk.support) :
    ∃ node suffix,
      input.UnboundedOfficialSubtree
        (OfficialCIPNode.rootFromEdge parent current) suffix node ∧
        suffix.length = walk.support.length - 1 ∧
        node.current? = some target ∧
        node.provenance = OfficialCIPNodeProvenance.realAtom := by
  let rest := walk.support.tail
  have supportCons : walk.support = current :: rest := by
    cases walk with
    | nil => simp [rest, SimpleGraph.Walk.support]
    | cons edge tail => rfl
  have nodup : (current :: rest).Nodup := by
    simpa [supportCons] using simple.support_nodup
  have chain : (current :: rest).IsChain
      (fun a b => input.moleculeGraph.Adj a b) := by
    simpa [supportCons] using SimpleGraph.Walk.isChain_adj_support walk
  have currentNotRest : current ∉ rest := (List.nodup_cons.mp nodup).1
  have parentNotRest : parent ∉ rest := by
    intro present
    exact avoidsParent (by
      rw [supportCons]
      exact List.mem_cons_of_mem current present)
  have disjoint : ∀ x ∈ (OfficialCIPNode.rootFromEdge parent current).history,
      x ∉ rest := by
    intro x present
    simp only [OfficialCIPNode.rootFromEdge, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with same | same
    · subst same
      exact currentNotRest
    · subst same
      exact parentNotRest
  obtain ⟨finalNode, suffix, finalReach, suffixLength, finalObserved,
    finalProvenance⟩ :=
    input.unboundedOfficialSubtree_of_chain_aux
      (start := OfficialCIPNode.rootFromEdge parent current)
      current rest (OfficialCIPNode.rootFromEdge parent current) []
      (UnboundedOfficialSubtree.refl _) rfl rfl nodup chain disjoint
  have lastEq : (current :: rest).getLast? = some target := by
    rw [← supportCons]
    rw [List.getLast?_eq_getLast_of_ne_nil
      (by cases walk <;> simp [SimpleGraph.Walk.support])]
    exact congrArg some (SimpleGraph.Walk.getLast_support walk)
  refine ⟨finalNode, suffix, ?_, ?_, ?_, finalProvenance⟩
  · simpa using finalReach
  · simpa [rest, List.length_tail] using suffixLength
  · rw [finalObserved, lastEq]

/-- Every unbounded executable descendant of a real path node is again a real simple physical path
in the single-bond acyclic domain. -/
theorem unboundedOfficialSubtree_realPath_of_real
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {root : input.Atom} {start : OfficialCIPNode input.Atom} :
    ∀ {address : List Nat} {node : OfficialCIPNode input.Atom},
      input.UnboundedOfficialSubtree start address node →
        input.RealPathNode root start → input.RealPathNode root node := by
  intro address node reachable
  induction reachable with
  | refl node =>
      intro real
      exact real
  | step childAtSlot rest inductionHypothesis =>
      intro real
      exact inductionHypothesis
        (input.realPathNode_step singleBonded acyclic real childAtSlot)

/-- Every unbounded executable descendant of a real atom root is a real simple physical path in
the single-bond acyclic domain. -/
theorem unboundedOfficialSubtree_realPath
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {root : input.Atom} {address : List Nat} {node : OfficialCIPNode input.Atom}
    (reachable : input.UnboundedOfficialSubtree (OfficialCIPNode.root root) address node) :
    input.RealPathNode root node :=
  input.unboundedOfficialSubtree_realPath_of_real singleBonded acyclic reachable
    (input.realPathNode_root root)

/-- Every bounded declarative occurrence below a real path node remains a real path node.  This is
the carrier-facing form of the step invariant: no bounded truncation can create a ring duplicate,
a multiple-bond duplicate, or a placeholder in the single-bond acyclic domain. -/
theorem declarativeLocalizedOccurrenceSubtree_realPath
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {root : input.Atom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode input.Atom}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrenceSubtree root path fuel node occurrence) :
    input.RealPathNode root node → input.RealPathNode root occurrence.node := by
  induction derived with
  | subtreeRoot =>
      intro real
      exact real
  | subtreeDescendant childAtSlot descendant inductionHypothesis =>
      intro real
      exact inductionHypothesis
        (input.realPathNode_step singleBonded acyclic real childAtSlot)

/-- Every occurrence in the actual finite carrier, at any fuel, is a real simple physical path in
the single-bond acyclic domain.  In particular its `current?` is an actual physical atom. -/
theorem carrierOccurrence_realPath
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {fuel : Nat} (occurrence : input.LocalizedCIPOccurrence fuel) :
    input.RealPathNode occurrence.1.root occurrence.1.node := by
  have derived := (input.mem_localizedOccurrences_iff fuel occurrence.1).mp occurrence.2
  have rooted : input.DeclarativeLocalizedOccurrenceSubtree occurrence.1.root []
      (fuel + 1) (OfficialCIPNode.root occurrence.1.root) occurrence.1 := derived
  exact (input.declarativeLocalizedOccurrenceSubtree_realPath
    singleBonded acyclic rooted) (input.realPathNode_root occurrence.1.root)

/-- Carrier occurrences carry real provenance; the duplicate and placeholder provenance
constructors are absent in the single-bond acyclic domain. -/
theorem carrierOccurrence_provenance_real
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {fuel : Nat} (occurrence : input.LocalizedCIPOccurrence fuel) :
    occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  obtain ⟨_current, _path, _observed, _head, provenance, _simple, _support, _penultimate⟩ :=
    input.carrierOccurrence_realPath singleBonded acyclic occurrence
  exact provenance

/-- A carrier occurrence cannot be a duplicate leaf. -/
theorem carrierOccurrence_not_duplicateLeaf
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {fuel : Nat} (occurrence : input.LocalizedCIPOccurrence fuel) :
    occurrence.1.node.isDuplicateLeaf = false :=
  input.isDuplicateLeaf_eq_false_of_provenance_real occurrence.1.node
    (input.carrierOccurrence_provenance_real singleBonded acyclic occurrence)

/-- The physical history of a carrier occurrence has no repeated atom. -/
theorem carrierOccurrence_history_nodup
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {fuel : Nat} (occurrence : input.LocalizedCIPOccurrence fuel) :
    occurrence.1.node.history.Nodup := by
  obtain ⟨_current, _path, _observed, _head, _provenance, simple, supportReverse, _penultimate⟩ :=
    input.carrierOccurrence_realPath singleBonded acyclic occurrence
  rw [← supportReverse]
  exact List.nodup_reverse.mpr simple.support_nodup

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.AcyclicSingleBondDomain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RealPathNode
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.pairwiseDisjointLigandBranches_of_acyclic
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.pairwiseDisjointLigandBranches_of_acyclic_tetrahedralCenter
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realPathNode_root
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.parent_mem_history_of_parent?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.simpleOccurrencePath_of_chain_aux
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.simpleOccurrencePath_of_simple_walk
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.simpleOccurrencePath_realPathNode
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.simpleOccurrencePath_address_unique
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.carrierOccurrence_exists_of_simple_walk
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.carrierOccurrence_exists_of_avoiding_walk
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.carrierOccurrence_exists_of_ligandBranch
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unboundedOfficialSubtree_of_chain_aux
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unboundedOfficialSubtree_of_walk_avoiding
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_executableOfficialChildCopies_adjacent_bound
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.not_parent_of_zero_mem_executableOfficialChildCopies
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.not_mem_history_of_real_zero_step
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realPathNode_step
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unboundedOfficialSubtree_realPath_of_real
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unboundedOfficialSubtree_realPath
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeLocalizedOccurrenceSubtree_realPath
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.carrierOccurrence_realPath
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.carrierOccurrence_provenance_real
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.carrierOccurrence_not_duplicateLeaf
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.carrierOccurrence_history_nodup
