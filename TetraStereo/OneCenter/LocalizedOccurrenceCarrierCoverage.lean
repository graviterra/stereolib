import TetraStereo.OneCenter.LocalizedAllRootUniversalDepth
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Structural occurrence coverage for the finite localized carrier

`LocalizedAllRootUniversalDepth` proved that *every* unbounded executable descendant of an
arbitrary atom root is stored by the shared occurrence enumeration at carrier fuel
`atomCount + 1`.  Its hypothesis is `UnboundedOfficialSubtree`, an executable-reachability
relation: it already assumes that the descendant arises by following the executable child
enumeration.

This module supplies the missing graph-theoretic direction.  It defines the legitimate molecular
comparison occurrences directly on the molecule graph:

* `SimpleOccurrencePath` is an oriented simple atom path starting at an arbitrary root atom,
  following positively bonded graph edges, never repeating an atom, and never stepping back to
  the stored parent;
* `LegitimateOccurrence` additionally permits exactly one terminal occurrence of the two
  chemically meaningful duplicate kinds: a ring-duplicate step to an atom already on the simple
  path, and a multiple-bond duplicate copy (`copyIndex ≠ 0`) of a positively bonded edge.

Addresses are derived from the raw executable copy enumeration
`executableOfficialChildCopies`: a step's slot is the position of the raw copy
`(next, copyIndex)`, transported elementwise through the `extend` map that defines
`executableOfficialCIPChildren`.  This matters for multiple bonds: `extend next 1` and
`extend next 2` are the *same* node (`childProvenance` records only the parent depth), although
the runtime carrier retains both copies.  Taking the `idxOf` of the extended node would alias
them to one slot; `executableOfficialChildCopySlot_ne_of_copyIndex_ne` and
`legitimateOccurrence_multiple_address_ne_of_copyIndex_ne` prove that distinct positive copy
indices receive distinct address slots under the raw-copy addressing used here.

For every such legitimate occurrence it is proved, without any carrier-membership premise and
without assuming a completed expansion, that

* the walk is realizable in the executable official child enumeration
  (`legitimateOccurrence_unbounded`);
* its address length is at most the atom count (`legitimateOccurrence_address_length_le_atomCount`),
  a bound strictly sharper than the existing `atomCount + 1` expansion bound because a simple
  atom path cannot use more than `atomCount` distinct atoms;
* the exact occurrence frame is present in the shared molecule-wide enumeration at fuel
  `atomCount` (and at every larger fuel), with remaining depth `fuel + 1 - address.length`;
* the same frame belongs to the executable proof-relevant carrier
  `localizedOccurrenceCarrier atomCount`.

The converse structural classification is also proved: every executable descendant reachable
from a real atom root is either a real simple-path node (with noduplicate history), a ring
duplicate (with an actually visited duplicated atom), or a multiple-bond duplicate (with a
positive copy index).  The duplicate cases are consequences of the real constructor
`OfficialCIPNode.childProvenance`, not of an assumed cutoff: the ring case records the visited
history witness in `LegitimateOccurrence.ring`, and the multiple case records `copyIndex ≠ 0` in
`LegitimateOccurrence.multiple`.

The module is independent of descriptor semantics.  It reuses the existing unbounded-reachability
bridge `mem_localizedOccurrenceSubtree_of_unbounded` and the existing universal-depth theorem
`localizedOccurrenceUniversalDepth_covers_atom`; it does not duplicate either of them.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-! ## Graph adjacency versus the executable child enumerations -/

/-- Exact membership characterization of the executable neighbor-copy list: a pair is listed
exactly when the target atom is positively bonded and the copy index is below the bond order.
This is the forward graph-to-runtime direction used by every later theorem. -/
theorem mem_executableOfficialNeighborCopies_iff
    (input : CertifiedLocalizedCIPInput) (atom neighbor : input.Atom) (copyIndex : Nat) :
    (neighbor, copyIndex) ∈ input.executableOfficialNeighborCopies atom ↔
      input.moleculeGraph.Adj atom neighbor ∧
        copyIndex < input.moleculeGraph.bond atom neighbor := by
  constructor
  · intro present
    unfold executableOfficialNeighborCopies at present
    rw [List.mem_flatMap] at present
    obtain ⟨source, sourcePresent, mappedPresent⟩ := present
    rw [List.mem_map] at mappedPresent
    obtain ⟨index, indexPresent, pairEquality⟩ := mappedPresent
    have sourceEq : source = neighbor := (Prod.mk.inj pairEquality).1
    have indexEq : index = copyIndex := (Prod.mk.inj pairEquality).2
    subst source
    subst index
    exact ⟨(input.moleculeGraph.mem_neighborFinset atom neighbor).mp
        ((Finset.mem_sort (r := (· ≤ ·))).mp sourcePresent),
      List.mem_range.mp indexPresent⟩
  · rintro ⟨adjacent, bound⟩
    unfold executableOfficialNeighborCopies
    rw [List.mem_flatMap]
    refine ⟨neighbor, ?_, ?_⟩
    · exact (Finset.mem_sort (r := (· ≤ ·))).mpr
        ((input.moleculeGraph.mem_neighborFinset atom neighbor).mpr adjacent)
    · rw [List.mem_map]
      exact ⟨copyIndex, List.mem_range.mpr bound, rfl⟩

/-- A positively bonded non-parent zero-copy edge is present in the executable child-copy list.
The side condition `allowed` says that the pair is not the removed parent zero-copy: it holds
automatically for positive copy indices (multiple-bond duplicates) and is the non-parent
condition for the real zero-copy step. -/
theorem mem_executableOfficialChildCopies_of_adjacent
    (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) (current next : input.Atom) (copyIndex : Nat)
    (currentObserved : node.current? = some current)
    (adjacent : input.moleculeGraph.Adj current next)
    (bound : copyIndex < input.moleculeGraph.bond current next)
    (allowed : copyIndex ≠ 0 ∨ node.parent? ≠ some next) :
    (next, copyIndex) ∈ input.executableOfficialChildCopies node := by
  unfold executableOfficialChildCopies
  rw [currentObserved]
  cases parentObserved : node.parent? with
  | none =>
      simpa [parentObserved] using
        (input.mem_executableOfficialNeighborCopies_iff current next copyIndex).mpr
          ⟨adjacent, bound⟩
  | some parent =>
      have filtered : (next, copyIndex) ∈
          (input.executableOfficialNeighborCopies current).filter
            (fun copy => !(copy.1 == parent && copy.2 == 0)) := by
        rw [List.mem_filter]
        refine ⟨(input.mem_executableOfficialNeighborCopies_iff current next copyIndex).mpr
          ⟨adjacent, bound⟩, ?_⟩
        by_cases zero : copyIndex = 0
        · rcases allowed with positive | notParent
          · exact absurd zero positive
          · have nextNeParent : next ≠ parent := by
              intro same
              subst next
              exact notParent parentObserved
            simp [zero, nextNeParent]
        · simp [zero]
      simpa [parentObserved] using filtered

/-- A real official node is not a duplicate leaf. -/
theorem isDuplicateLeaf_eq_false_of_provenance_real
    (input : CertifiedLocalizedCIPInput) (node : OfficialCIPNode input.Atom)
    (real : node.provenance = OfficialCIPNodeProvenance.realAtom) :
    node.isDuplicateLeaf = false := by
  simp [OfficialCIPNode.isDuplicateLeaf, real]

/-- Any positively bonded non-duplicate child copy is listed in the executable official children,
provided it is not the removed parent zero-copy pair. -/
theorem mem_executableOfficialCIPChildren_of_adjacent
    (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) (current next : input.Atom) (copyIndex : Nat)
    (nonduplicate : node.isDuplicateLeaf = false)
    (currentObserved : node.current? = some current)
    (adjacent : input.moleculeGraph.Adj current next)
    (bound : copyIndex < input.moleculeGraph.bond current next)
    (allowed : copyIndex ≠ 0 ∨ node.parent? ≠ some next) :
    node.extend next copyIndex ∈ input.executableOfficialCIPChildren node := by
  unfold executableOfficialCIPChildren
  rw [if_neg (by simpa using nonduplicate)]
  exact List.mem_map.mpr
    ⟨(next, copyIndex),
      input.mem_executableOfficialChildCopies_of_adjacent node current next copyIndex
        currentObserved adjacent bound allowed,
      rfl⟩

/-- Every executable official child extends the parent history by exactly one atom.  This is the
structural fact needed to relate unbounded addresses to histories; it is derived from the actual
`OfficialCIPNode.extend` constructor, not assumed. -/
theorem executableOfficialCIPChildren_history_length
    (input : CertifiedLocalizedCIPInput)
    (node child : OfficialCIPNode input.Atom)
    (present : child ∈ input.executableOfficialCIPChildren node) :
    child.history.length = node.history.length + 1 := by
  by_cases duplicate : node.isDuplicateLeaf = true
  · have empty : input.executableOfficialCIPChildren node = [] := by
      simp [executableOfficialCIPChildren, duplicate]
    simp [empty] at present
  · rw [executableOfficialCIPChildren, if_neg (by simpa using duplicate),
      List.mem_map] at present
    obtain ⟨copy, _copyPresent, childIdentity⟩ := present
    obtain ⟨next, copyIndex⟩ := copy
    exact (congrArg (fun extended : OfficialCIPNode input.Atom =>
        extended.history.length) childIdentity.symm).trans
      (OfficialCIPNode.extend_history_length node next copyIndex)

/-! ## Multiplicity-faithful executable addressing

The extended node `node.extend next copyIndex` forgets the copy index: every positive copy of one
edge extends to the same `multipleBondDuplicate` node, because `childProvenance` records only the
parent depth and `extend` stores the same current atom and history.  Addressing a multiple-bond
occurrence by `List.idxOf (node.extend next copyIndex) (executableOfficialCIPChildren node)`
therefore aliases all positive copies of that edge to the slot of the first copy.  The runtime
carrier does retain every copy; the address construction must retain them too.

The slot below is the position of the *raw* copy `(next, copyIndex)` in
`executableOfficialChildCopies node`.  `executableOfficialCIPChildren` maps that raw list
elementwise to extended nodes, so the raw position is also an executable child slot with the same
index, and distinct raw copies have distinct positions. -/

/-- The image of a list position under any map is a position of the mapped list with the same
index.  This is the general list fact behind multiplicity-faithful addressing. -/
theorem mem_zipIdx_map_of_mem {α β : Type*} [BEq α] [LawfulBEq α]
    {l : List α} {a : α} (present : a ∈ l) (f : α → β) :
    (f a, l.idxOf a) ∈ (l.map f).zipIdx := by
  apply (List.mem_zipIdx_iff_getElem?).mpr
  rw [List.getElem?_map, List.getElem?_idxOf present]
  rfl

/-- Executable slot of the raw child copy `(next, copyIndex)`: its position in the node's raw
child-copy enumeration.  Unlike the `idxOf` of the extended node, this distinguishes the positive
multiple-bond copies of one edge. -/
def executableOfficialChildCopySlot (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) (next : input.Atom) (copyIndex : Nat) : Nat :=
  (input.executableOfficialChildCopies node).idxOf (next, copyIndex)

/-- A raw child copy's slot is an actual slot of the executable official children, carrying the
extended node built from that raw copy. -/
theorem executableOfficialChildCopySlot_mem
    (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) (next : input.Atom) (copyIndex : Nat)
    (nonduplicate : node.isDuplicateLeaf = false)
    (present : (next, copyIndex) ∈ input.executableOfficialChildCopies node) :
    (node.extend next copyIndex, input.executableOfficialChildCopySlot node next copyIndex) ∈
      (input.executableOfficialCIPChildren node).zipIdx := by
  have mapped := mem_zipIdx_map_of_mem present
    (fun copy : input.Atom × Nat => node.extend copy.1 copy.2)
  unfold executableOfficialCIPChildren
  rw [if_neg (by simpa using nonduplicate)]
  simpa [executableOfficialChildCopySlot] using mapped

/-- Raw child-copy slots are injective: equal slots force equal raw copies.  The proof reads the
element stored at each slot from `getElem?_idxOf`, so it does not depend on list uniqueness. -/
theorem executableOfficialChildCopySlot_inj
    (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom)
    {next next' : input.Atom} {copyIndex copyIndex' : Nat}
    (present : (next, copyIndex) ∈ input.executableOfficialChildCopies node)
    (present' : (next', copyIndex') ∈ input.executableOfficialChildCopies node) :
    input.executableOfficialChildCopySlot node next copyIndex =
        input.executableOfficialChildCopySlot node next' copyIndex' ↔
      (next, copyIndex) = (next', copyIndex') := by
  unfold executableOfficialChildCopySlot
  constructor
  · intro same
    have first := List.getElem?_idxOf present
    have second := List.getElem?_idxOf present'
    rw [← same] at second
    exact Option.some.inj (first.symm.trans second)
  · intro same
    rw [same]

/-- **Multiplicity faithfulness.**  Distinct positive copy indices of the same edge give distinct
executable address slots, even though `node.extend next copyIndex` is the same node for all of
them.  This is the property that the extended-node `idxOf` cannot provide. -/
theorem executableOfficialChildCopySlot_ne_of_copyIndex_ne
    (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) (next : input.Atom)
    {copyIndex copyIndex' : Nat}
    (present : (next, copyIndex) ∈ input.executableOfficialChildCopies node)
    (present' : (next, copyIndex') ∈ input.executableOfficialChildCopies node)
    (different : copyIndex ≠ copyIndex') :
    input.executableOfficialChildCopySlot node next copyIndex ≠
      input.executableOfficialChildCopySlot node next copyIndex' := by
  intro same
  have pairEqual :=
    (input.executableOfficialChildCopySlot_inj (node := node) present present').mp same
  exact different (Prod.mk.inj pairEqual).2

/-! ## Legitimate graph-level occurrences

`SimpleOccurrencePath` records the simple atom path by its endpoint node and its sibling address.
Each step uses the executable raw-copy slot `executableOfficialChildCopySlot` of the edge it
follows, so the address is the one produced by the executable enumeration itself and multiple-bond
copies remain distinct.  `LegitimateOccurrence` adds at most one terminal duplicate step, of
exactly the two kinds that `OfficialCIPNode.childProvenance` creates: a ring duplicate
(`next ∈ node.history`, zero copy) and a multiple-bond duplicate (positive copy). -/

/-- Oriented simple atom path from `root`, following positive graph edges and never repeating an
atom or returning to the stored parent. -/
inductive SimpleOccurrencePath (input : CertifiedLocalizedCIPInput) (root : input.Atom) :
    OfficialCIPNode input.Atom → List Nat → Prop where
  | root :
      SimpleOccurrencePath input root (OfficialCIPNode.root root) []
  | step {node : OfficialCIPNode input.Atom} {address : List Nat}
      {current next : input.Atom}
      (path : SimpleOccurrencePath input root node address)
      (currentObserved : node.current? = some current)
      (adjacent : input.moleculeGraph.Adj current next)
      (notParent : node.parent? ≠ some next)
      (fresh : next ∉ node.history) :
      SimpleOccurrencePath input root
        (node.extend next 0)
        (address ++ [input.executableOfficialChildCopySlot node next 0])

/-- A legitimate molecular comparison occurrence: a simple path, or a simple path followed by one
real ring-duplicate or multiple-bond-duplicate step.  The duplicate constructors are the only two
provenance kinds generated by `OfficialCIPNode.childProvenance` besides `realAtom`. -/
inductive LegitimateOccurrence (input : CertifiedLocalizedCIPInput) (root : input.Atom) :
    OfficialCIPNode input.Atom → List Nat → Prop where
  | simple {node : OfficialCIPNode input.Atom} {address : List Nat}
      (path : SimpleOccurrencePath input root node address) :
      LegitimateOccurrence input root node address
  | ring {node : OfficialCIPNode input.Atom} {address : List Nat}
      {current next : input.Atom}
      (path : SimpleOccurrencePath input root node address)
      (currentObserved : node.current? = some current)
      (adjacent : input.moleculeGraph.Adj current next)
      (notParent : node.parent? ≠ some next)
      (visited : next ∈ node.history) :
      LegitimateOccurrence input root
        (node.extend next 0)
        (address ++ [input.executableOfficialChildCopySlot node next 0])
  | multiple {node : OfficialCIPNode input.Atom} {address : List Nat}
      {current next : input.Atom} {copyIndex : Nat}
      (path : SimpleOccurrencePath input root node address)
      (currentObserved : node.current? = some current)
      (adjacent : input.moleculeGraph.Adj current next)
      (bound : copyIndex < input.moleculeGraph.bond current next)
      (positive : copyIndex ≠ 0) :
      LegitimateOccurrence input root
        (node.extend next copyIndex)
        (address ++ [input.executableOfficialChildCopySlot node next copyIndex])

/-! ## Structural facts about simple paths -/

/-- Every simple-path node is a real atom. -/
theorem simpleOccurrencePath_provenance
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (path : SimpleOccurrencePath input root node address) :
    node.provenance = OfficialCIPNodeProvenance.realAtom := by
  induction path with
  | root => rfl
  | @step node address current next path currentObserved adjacent notParent fresh ih =>
      rw [OfficialCIPNode.extend_provenance]
      exact OfficialCIPNode.childProvenance_real node next fresh

/-- Every simple-path node has a noduplicate atom history. -/
theorem simpleOccurrencePath_history_nodup
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (path : SimpleOccurrencePath input root node address) :
    node.history.Nodup := by
  induction path with
  | root => simp [OfficialCIPNode.root]
  | @step node address current next path currentObserved adjacent notParent fresh ih =>
      rw [OfficialCIPNode.extend_history]
      exact List.nodup_cons.mpr ⟨fresh, ih⟩

/-- The history of a simple path consists exactly of the root plus the addressed atoms. -/
theorem simpleOccurrencePath_history_length
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (path : SimpleOccurrencePath input root node address) :
    node.history.length = address.length + 1 := by
  induction path with
  | root => simp [OfficialCIPNode.root]
  | @step node address current next path currentObserved adjacent notParent fresh ih =>
      rw [OfficialCIPNode.extend_history_length, ih]
      simp only [List.length_append, List.length_singleton]

/-- A simple-path node is an active simple official node. -/
theorem simpleOccurrencePath_activeSimple
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (path : SimpleOccurrencePath input root node address) :
    node.ActiveSimple :=
  ⟨input.simpleOccurrencePath_provenance path,
    input.simpleOccurrencePath_history_nodup path⟩

/-! ## Reversing the executable-reachability relation across one appended step -/

/-- Unbounded executable reachability is stable under appending one executable child step at the
far end of its address.  The `UnboundedOfficialSubtree.step` constructor builds addresses by
prepending slots, whereas a forward graph walk appends its slot; this lemma converts between the
two conventions. -/
theorem unboundedOfficialSubtree_append_last
    (input : CertifiedLocalizedCIPInput)
    {start : OfficialCIPNode input.Atom} {address : List Nat}
    {node : OfficialCIPNode input.Atom} :
    ∀ {targetChild : OfficialCIPNode input.Atom} {targetSlot : Nat},
      input.UnboundedOfficialSubtree start address node →
      (targetChild, targetSlot) ∈
        (input.executableOfficialCIPChildren node).zipIdx →
      input.UnboundedOfficialSubtree start (address ++ [targetSlot]) targetChild := by
  intro targetChild targetSlot reachable
  induction reachable with
  | refl node =>
      intro targetAtSlot
      simpa using UnboundedOfficialSubtree.step targetAtSlot
        (UnboundedOfficialSubtree.refl targetChild)
  | @step node child inner descendant slot childAtSlot rest ih =>
      intro targetAtSlot
      simpa using UnboundedOfficialSubtree.step childAtSlot (ih targetAtSlot)

/-! ## Legitimate occurrences are executable-reachable -/

/-- Every simple graph path is realizable as an unbounded executable subtree descendant. -/
theorem simpleOccurrencePath_unbounded
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (path : SimpleOccurrencePath input root node address) :
    input.UnboundedOfficialSubtree (OfficialCIPNode.root root) address node := by
  induction path with
  | root => exact UnboundedOfficialSubtree.refl (OfficialCIPNode.root root)
  | @step node address current next path currentObserved adjacent notParent fresh ih =>
      have real := input.simpleOccurrencePath_provenance path
      have nonduplicate := input.isDuplicateLeaf_eq_false_of_provenance_real node real
      have copyPresent := input.mem_executableOfficialChildCopies_of_adjacent
        node current next 0 currentObserved adjacent adjacent (Or.inr notParent)
      have atSlot := input.executableOfficialChildCopySlot_mem node next 0
        nonduplicate copyPresent
      exact input.unboundedOfficialSubtree_append_last ih atSlot

/-- **Graph-to-executable reachability.**  Every legitimate occurrence, including a terminal
ring-duplicate or multiple-bond-duplicate step, is a descendant of the root in the executable
official subtree.  No carrier membership or completed-expansion hypothesis is used: the proof
derives the executable child from the graph edge and the `childProvenance` case. -/
theorem legitimateOccurrence_unbounded
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (occ : LegitimateOccurrence input root node address) :
    input.UnboundedOfficialSubtree (OfficialCIPNode.root root) address node := by
  cases occ with
  | @simple simpleNode simpleAddress path =>
      exact input.simpleOccurrencePath_unbounded path
  | @ring prefixNode prefixAddress current next path currentObserved adjacent notParent visited =>
      have reachPrefix := input.simpleOccurrencePath_unbounded path
      have real := input.simpleOccurrencePath_provenance path
      have nonduplicate := input.isDuplicateLeaf_eq_false_of_provenance_real prefixNode real
      have copyPresent := input.mem_executableOfficialChildCopies_of_adjacent
        prefixNode current next 0 currentObserved adjacent adjacent (Or.inr notParent)
      have atSlot := input.executableOfficialChildCopySlot_mem prefixNode next 0
        nonduplicate copyPresent
      exact input.unboundedOfficialSubtree_append_last reachPrefix atSlot
  | @multiple prefixNode prefixAddress current next copyIndex path currentObserved adjacent bound positive =>
      have reachPrefix := input.simpleOccurrencePath_unbounded path
      have real := input.simpleOccurrencePath_provenance path
      have nonduplicate := input.isDuplicateLeaf_eq_false_of_provenance_real prefixNode real
      have copyPresent := input.mem_executableOfficialChildCopies_of_adjacent
        prefixNode current next copyIndex currentObserved adjacent bound (Or.inl positive)
      have atSlot := input.executableOfficialChildCopySlot_mem prefixNode next copyIndex
        nonduplicate copyPresent
      exact input.unboundedOfficialSubtree_append_last reachPrefix atSlot

/-- **Distinct multiple-bond copies receive distinct addresses.**  For the same simple prefix and
the same graph edge, two positive copy indices produce legitimate occurrences whose terminal slots
(and hence full addresses) differ.  The corresponding extended nodes coincide
(`node.extend next c` is independent of the positive copy index), so this distinction is visible
only in the raw-copy address. -/
theorem legitimateOccurrence_multiple_address_ne_of_copyIndex_ne
    (input : CertifiedLocalizedCIPInput)
    {node : OfficialCIPNode input.Atom} {current next : input.Atom}
    {prefixAddress : List Nat} {copyIndex copyIndex' : Nat}
    (currentObserved : node.current? = some current)
    (adjacent : input.moleculeGraph.Adj current next)
    (bound : copyIndex < input.moleculeGraph.bond current next)
    (bound' : copyIndex' < input.moleculeGraph.bond current next)
    (positive : copyIndex ≠ 0) (positive' : copyIndex' ≠ 0)
    (different : copyIndex ≠ copyIndex') :
    (prefixAddress ++ [input.executableOfficialChildCopySlot node next copyIndex]) ≠
      (prefixAddress ++ [input.executableOfficialChildCopySlot node next copyIndex']) := by
  intro same
  have slotSame : input.executableOfficialChildCopySlot node next copyIndex =
      input.executableOfficialChildCopySlot node next copyIndex' := by
    have tails := List.append_cancel_left same
    simpa using tails
  have present := input.mem_executableOfficialChildCopies_of_adjacent
    node current next copyIndex currentObserved adjacent bound (Or.inl positive)
  have present' := input.mem_executableOfficialChildCopies_of_adjacent
    node current next copyIndex' currentObserved adjacent bound' (Or.inl positive')
  exact input.executableOfficialChildCopySlot_ne_of_copyIndex_ne node next present
    present' different slotSame

/-! ## Provenance classification of legitimate occurrences -/

/-- A simple-path node has real provenance and a noduplicate history. -/
theorem simpleOccurrencePath_provenance_and_nodup
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (path : SimpleOccurrencePath input root node address) :
    node.provenance = OfficialCIPNodeProvenance.realAtom ∧ node.history.Nodup :=
  ⟨input.simpleOccurrencePath_provenance path,
    input.simpleOccurrencePath_history_nodup path⟩

/-- **Actual duplicate provenance, ring case.**  A terminal ring step has the genuine
`ringDuplicate` provenance with the distance computed by `OfficialCIPNode.childProvenance`; the
visited-history witness is part of `LegitimateOccurrence.ring`, so this is not a cutoff
assumption. -/
theorem legitimateOccurrence_ring_provenance
    (input : CertifiedLocalizedCIPInput)
    {node : OfficialCIPNode input.Atom} {next : input.Atom}
    (visited : next ∈ node.history) :
    (node.extend next 0).provenance =
      OfficialCIPNodeProvenance.ringDuplicate (node.duplicateRootDistance next) := by
  rw [OfficialCIPNode.extend_provenance]
  exact OfficialCIPNode.childProvenance_ring_duplicate node next visited

/-- **Actual duplicate provenance, multiple-bond case.**  A positive copy index produces the
genuine `multipleBondDuplicate` provenance at the parent sphere depth. -/
theorem legitimateOccurrence_multiple_provenance
    (input : CertifiedLocalizedCIPInput)
    {node : OfficialCIPNode input.Atom} {next : input.Atom} {copyIndex : Nat}
    (positive : copyIndex ≠ 0) :
    (node.extend next copyIndex).provenance =
      OfficialCIPNodeProvenance.multipleBondDuplicate node.depth := by
  rw [OfficialCIPNode.extend_provenance]
  exact OfficialCIPNode.childProvenance_copy_pos node next positive

/-- **Provenance trichotomy for legitimate occurrences.**  Every legitimate molecular comparison
occurrence ends in exactly one of the three graph-generated provenance kinds: a real atom, a ring
duplicate, or a multiple-bond duplicate.  Placeholders never occur. -/
theorem legitimateOccurrence_provenance_trichotomy
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (occ : LegitimateOccurrence input root node address) :
    (node.provenance = OfficialCIPNodeProvenance.realAtom ∧ node.history.Nodup) ∨
      (∃ distance, node.provenance =
        OfficialCIPNodeProvenance.ringDuplicate distance) ∨
      (∃ distance, node.provenance =
        OfficialCIPNodeProvenance.multipleBondDuplicate distance) := by
  cases occ with
  | @simple simpleNode simpleAddress path =>
      exact Or.inl (input.simpleOccurrencePath_provenance_and_nodup path)
  | @ring prefixNode prefixAddress current next path currentObserved adjacent notParent visited =>
      refine Or.inr (Or.inl ⟨prefixNode.duplicateRootDistance next, ?_⟩)
      exact input.legitimateOccurrence_ring_provenance visited
  | @multiple prefixNode prefixAddress current next copyIndex path currentObserved adjacent bound positive =>
      refine Or.inr (Or.inr ⟨prefixNode.depth, ?_⟩)
      exact input.legitimateOccurrence_multiple_provenance positive

/-! ## The sharp atom-count depth bound -/

/-- A legitimate occurrence from a simple prefix cannot use more than `atomCount` sibling slots.
A simple path uses `address.length + 1` distinct atoms, so `address.length ≤ atomCount` already
for the simple case; a terminal duplicate contributes one further slot, still bounded by the
number of distinct atoms on the simple prefix. -/
theorem legitimateOccurrence_address_length_le_atomCount
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (occ : LegitimateOccurrence input root node address) :
    address.length ≤ input.certified.input.molecule.atomCount := by
  cases occ with
  | @simple simpleNode simpleAddress path =>
      have nodup := input.simpleOccurrencePath_history_nodup path
      have lengthEq := input.simpleOccurrencePath_history_length path
      have cardLe := nodup.length_le_card
      simp only [Fintype.card_fin] at cardLe
      omega
  | @ring prefixNode prefixAddress current next path currentObserved adjacent notParent visited =>
      have nodup := input.simpleOccurrencePath_history_nodup path
      have lengthEq := input.simpleOccurrencePath_history_length path
      have cardLe : prefixNode.history.length ≤ input.certified.input.molecule.atomCount := by
        simpa using nodup.length_le_card
      simp only [List.length_append, List.length_singleton]
      omega
  | @multiple prefixNode prefixAddress current next copyIndex path currentObserved adjacent bound positive =>
      have nodup := input.simpleOccurrencePath_history_nodup path
      have lengthEq := input.simpleOccurrencePath_history_length path
      have cardLe : prefixNode.history.length ≤ input.certified.input.molecule.atomCount := by
        simpa using nodup.length_le_card
      simp only [List.length_append, List.length_singleton]
      omega

/-- The remaining depth at the sharp bound is strictly positive for every legitimate
occurrence. -/
theorem legitimateOccurrence_remaining_pos
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (occ : LegitimateOccurrence input root node address) :
    0 < input.certified.input.molecule.atomCount + 1 - address.length := by
  have bound := input.legitimateOccurrence_address_length_le_atomCount occ
  omega

/-! ## Representation in the shared occurrence enumeration -/

/-- Every legitimate occurrence is present in the atom-rooted occurrence subtree at any fuel
covering its address length, with exact node, address and remaining depth. -/
theorem legitimateOccurrence_mem_localizedOccurrencesAtAtom_of_fuel
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (occ : LegitimateOccurrence input root node address) {fuel : Nat}
    (enough : address.length ≤ fuel) :
    { root := root
      address := address
      node := node
      remaining := fuel + 1 - address.length } ∈
      input.localizedOccurrencesAtAtom fuel root := by
  have reachable := input.legitimateOccurrence_unbounded occ
  have covered := input.mem_localizedOccurrenceSubtree_of_unbounded
    (root := root) (fuel := fuel + 1) (path := []) reachable (by omega)
  simpa [localizedOccurrencesAtAtom] using covered

/-- Molecule-wide form: every legitimate occurrence is present in the shared deduplicated
enumeration at any fuel covering its address length. -/
theorem legitimateOccurrence_mem_localizedOccurrences_of_fuel
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (occ : LegitimateOccurrence input root node address) {fuel : Nat}
    (enough : address.length ≤ fuel) :
    { root := root
      address := address
      node := node
      remaining := fuel + 1 - address.length } ∈
      input.localizedOccurrences fuel := by
  have rooted := input.legitimateOccurrence_mem_localizedOccurrencesAtAtom_of_fuel occ enough
  unfold localizedOccurrences
  rw [List.mem_dedup, List.mem_flatMap]
  exact ⟨root, by simp, rooted⟩

/-- **Sharp atom-count coverage.**  Every legitimate occurrence is present in the shared
occurrence enumeration at the explicit graph-derived fuel `atomCount`, with remaining depth
`atomCount + 1 - address.length`. -/
theorem legitimateOccurrence_mem_localizedOccurrences
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (occ : LegitimateOccurrence input root node address) :
    { root := root
      address := address
      node := node
      remaining := input.certified.input.molecule.atomCount + 1 - address.length } ∈
      input.localizedOccurrences (input.certified.input.molecule.atomCount) :=
  input.legitimateOccurrence_mem_localizedOccurrences_of_fuel occ
    (input.legitimateOccurrence_address_length_le_atomCount occ)

/-- Proof-relevant carrier occurrence assigned to a legitimate graph-level occurrence at the
sharp atom-count fuel. -/
def legitimateOccurrenceCarrier
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (occ : LegitimateOccurrence input root node address) :
    input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount) :=
  ⟨{ root := root
     address := address
     node := node
     remaining := input.certified.input.molecule.atomCount + 1 - address.length },
   input.legitimateOccurrence_mem_localizedOccurrences occ⟩

@[simp] theorem legitimateOccurrenceCarrier_root
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (occ : LegitimateOccurrence input root node address) :
    (input.legitimateOccurrenceCarrier occ).1.root = root := rfl

@[simp] theorem legitimateOccurrenceCarrier_address
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (occ : LegitimateOccurrence input root node address) :
    (input.legitimateOccurrenceCarrier occ).1.address = address := rfl

@[simp] theorem legitimateOccurrenceCarrier_node
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (occ : LegitimateOccurrence input root node address) :
    (input.legitimateOccurrenceCarrier occ).1.node = node := rfl

@[simp] theorem legitimateOccurrenceCarrier_remaining
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (occ : LegitimateOccurrence input root node address) :
    (input.legitimateOccurrenceCarrier occ).1.remaining =
      input.certified.input.molecule.atomCount + 1 - address.length := rfl

/-- The proof-relevant occurrence is an actual member of the executable finite carrier. -/
theorem legitimateOccurrenceCarrier_mem_carrier
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (occ : LegitimateOccurrence input root node address) :
    input.legitimateOccurrenceCarrier occ ∈
      input.localizedOccurrenceCarrier (input.certified.input.molecule.atomCount) :=
  input.localizedOccurrenceCarrier_complete
    (input.certified.input.molecule.atomCount)
    (input.legitimateOccurrenceCarrier occ)

@[simp] theorem legitimateOccurrenceCarrier_remaining_pos
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (occ : LegitimateOccurrence input root node address) :
    0 < (input.legitimateOccurrenceCarrier occ).1.remaining := by
  rw [input.legitimateOccurrenceCarrier_remaining]
  exact input.legitimateOccurrence_remaining_pos occ

/-- **Main structural coverage theorem.**  Every legitimate simple-path, ring-duplicate or
multiple-bond-duplicate occurrence reachable from an admitted molecule's atom is represented in
the actual finite carrier, with an explicit atom-count bound, exact address and node, strictly
positive remaining depth, and no assumed carrier membership or completed expansion. -/
theorem legitimateOccurrence_represented_in_carrier
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (occ : LegitimateOccurrence input root node address) :
    ∃ occurrence : input.LocalizedCIPOccurrence
        (input.certified.input.molecule.atomCount),
      occurrence.1.root = root ∧
        occurrence.1.address = address ∧
        occurrence.1.node = node ∧
        occurrence.1.remaining =
          input.certified.input.molecule.atomCount + 1 - address.length ∧
        0 < occurrence.1.remaining ∧
        address.length ≤ input.certified.input.molecule.atomCount ∧
        occurrence ∈ input.localizedOccurrenceCarrier
          (input.certified.input.molecule.atomCount) := by
  refine ⟨input.legitimateOccurrenceCarrier occ, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact input.legitimateOccurrenceCarrier_remaining_pos occ
  · exact input.legitimateOccurrence_address_length_le_atomCount occ
  · exact input.legitimateOccurrenceCarrier_mem_carrier occ

/-- **Bridge to the existing universal-depth pipeline.**  The same legitimate occurrence is
covered by the already-established universal-depth theorem
`localizedOccurrenceUniversalDepth_covers_atom` at carrier fuel `atomCount + 1`.  This is a direct
reuse of the existing theorem, recorded so that downstream Rule-3/Rule-4 consumers can obtain the
legitimate occurrence from either the sharp `atomCount` carrier or the pre-existing universal
carrier. -/
theorem legitimateOccurrence_coversInUniversalDepth
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (occ : LegitimateOccurrence input root node address) :
    { root := root
      address := address
      node := node
      remaining := input.certified.input.molecule.atomCount + 1 + 1 - address.length } ∈
      input.localizedOccurrencesAtAtom
        (input.certified.input.molecule.atomCount + 1) root :=
  input.localizedOccurrenceUniversalDepth_covers_atom root
    (input.legitimateOccurrence_unbounded occ)

/-! ## Converse classification of executable descendants

The forward direction above converts graph walks into executable descendants.  The present
section proves the converse provenance classification: every executable descendant of a real
root is real, ring-duplicate, or multiple-bond-duplicate.  This is what rules out hidden
placeholder or cutoff-only nodes in the carrier. -/

/-- A shape invariant for executable descendants: real with noduplicate history, or a duplicate
whose *tail* history (the real prefix before the duplicate atom) is noduplicate.  The tail
condition is exactly what is needed to bound the address by the atom count. -/
def ReachableOccurrenceShape (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) : Prop :=
  (node.provenance = OfficialCIPNodeProvenance.realAtom ∧ node.history.Nodup) ∨
    ((∃ distance, node.provenance =
        OfficialCIPNodeProvenance.ringDuplicate distance) ∧ node.history.tail.Nodup) ∨
    ((∃ distance, node.provenance =
        OfficialCIPNodeProvenance.multipleBondDuplicate distance) ∧ node.history.tail.Nodup)

/-- The root node satisfies the reachable shape invariant. -/
theorem reachableOccurrenceShape_root
    (input : CertifiedLocalizedCIPInput) (root : input.Atom) :
    input.ReachableOccurrenceShape (OfficialCIPNode.root root) := by
  unfold ReachableOccurrenceShape
  exact Or.inl ⟨rfl, by simp [OfficialCIPNode.root]⟩

/-- A real node with noduplicate history has no duplicate-leaf marker. -/
theorem isDuplicateLeaf_eq_true_of_ring_provenance
    (input : CertifiedLocalizedCIPInput) (node : OfficialCIPNode input.Atom)
    {distance : Nat}
    (ring : node.provenance = OfficialCIPNodeProvenance.ringDuplicate distance) :
    node.isDuplicateLeaf = true := by
  simp [OfficialCIPNode.isDuplicateLeaf, ring]

/-- A real node with noduplicate history has no duplicate-leaf marker. -/
theorem isDuplicateLeaf_eq_true_of_multiple_provenance
    (input : CertifiedLocalizedCIPInput) (node : OfficialCIPNode input.Atom)
    {distance : Nat}
    (multiple : node.provenance =
      OfficialCIPNodeProvenance.multipleBondDuplicate distance) :
    node.isDuplicateLeaf = true := by
  simp [OfficialCIPNode.isDuplicateLeaf, multiple]

/-- The reachable shape invariant is preserved by one executable child step.  A node satisfying
the invariant cannot be a duplicate leaf, so its executable children are the copies generated by
`OfficialCIPNode.extend`; the provenance of the step is then exactly the `childProvenance`
trichotomy, and the tail history of a duplicate child is the noduplicate parent history. -/
theorem reachableOccurrenceShape_step
    (input : CertifiedLocalizedCIPInput) {node child : OfficialCIPNode input.Atom}
    {slot : Nat}
    (shape : input.ReachableOccurrenceShape node)
    (childAtSlot : (child, slot) ∈
      (input.executableOfficialCIPChildren node).zipIdx) :
    input.ReachableOccurrenceShape child := by
  have childPresent := List.fst_mem_of_mem_zipIdx childAtSlot
  have realAndNodup : node.provenance = OfficialCIPNodeProvenance.realAtom ∧
      node.history.Nodup := by
    unfold ReachableOccurrenceShape at shape
    rcases shape with ⟨real, nodup⟩ | ⟨⟨distance, ring⟩, _tailNodup⟩ |
      ⟨⟨distance, multiple⟩, _tailNodup⟩
    · exact ⟨real, nodup⟩
    · exfalso
      have duplicate := input.isDuplicateLeaf_eq_true_of_ring_provenance node ring
      have empty : input.executableOfficialCIPChildren node = [] := by
        simp [executableOfficialCIPChildren, duplicate]
      simp [empty] at childPresent
    · exfalso
      have duplicate := input.isDuplicateLeaf_eq_true_of_multiple_provenance node multiple
      have empty : input.executableOfficialCIPChildren node = [] := by
        simp [executableOfficialCIPChildren, duplicate]
      simp [empty] at childPresent
  obtain ⟨real, nodup⟩ := realAndNodup
  have nonduplicate : node.isDuplicateLeaf = false :=
    input.isDuplicateLeaf_eq_false_of_provenance_real node real
  unfold executableOfficialCIPChildren at childPresent
  rw [if_neg (by simpa using nonduplicate)] at childPresent
  rw [List.mem_map] at childPresent
  obtain ⟨copy, copyPresent, childEq⟩ := childPresent
  obtain ⟨next, copyIndex⟩ := copy
  change node.extend next copyIndex = child at childEq
  rw [← childEq]
  unfold ReachableOccurrenceShape
  rw [OfficialCIPNode.extend_provenance]
  by_cases zero : copyIndex = 0
  · rw [zero]
    by_cases visited : next ∈ node.history
    · refine Or.inr (Or.inl ⟨⟨node.duplicateRootDistance next, ?_⟩, ?_⟩)
      · exact OfficialCIPNode.childProvenance_ring_duplicate node next visited
      · simpa [OfficialCIPNode.extend_history] using nodup
    · refine Or.inl ⟨?_, ?_⟩
      · exact OfficialCIPNode.childProvenance_real node next visited
      · rw [OfficialCIPNode.extend_history]
        exact List.nodup_cons.mpr ⟨visited, nodup⟩
  · refine Or.inr (Or.inr ⟨⟨node.depth, ?_⟩, ?_⟩)
    · exact OfficialCIPNode.childProvenance_copy_pos node next zero
    · simpa [OfficialCIPNode.extend_history] using nodup

/-- Every executable descendant of an executable occurrence satisfying the shape invariant again
satisfies it. -/
theorem unboundedOfficialSubtree_shape
    (input : CertifiedLocalizedCIPInput) :
    ∀ {start : OfficialCIPNode input.Atom} {address : List Nat}
      {node : OfficialCIPNode input.Atom},
      input.UnboundedOfficialSubtree start address node →
      input.ReachableOccurrenceShape start →
      input.ReachableOccurrenceShape node := by
  intro start address node reachable
  induction reachable with
  | refl node =>
      intro shape
      exact shape
  | @step node child inner descendant slot childAtSlot rest ih =>
      intro shape
      exact ih (input.reachableOccurrenceShape_step shape childAtSlot)

/-- The history length of an executable descendant grows exactly with the address length. -/
theorem unboundedOfficialSubtree_history_length
    (input : CertifiedLocalizedCIPInput) :
    ∀ {start : OfficialCIPNode input.Atom} {address : List Nat}
      {node : OfficialCIPNode input.Atom},
      input.UnboundedOfficialSubtree start address node →
      node.history.length = start.history.length + address.length := by
  intro start address node reachable
  induction reachable with
  | refl node => simp
  | @step node child inner descendant slot childAtSlot rest ih =>
      rw [ih]
      have childLength := input.executableOfficialCIPChildren_history_length node child
        (List.fst_mem_of_mem_zipIdx childAtSlot)
      rw [childLength]
      simp only [List.length_cons]
      omega

/-- **Converse atom-count bound.**  Every executable descendant of a real atom root has address
length at most the atom count.  For a real descendant this follows from the noduplicate history;
for a duplicate descendant it follows from the noduplicate tail history, i.e. from the real
simple prefix that actually generated the duplicate.  This is a structural improvement over the
existing `atomCount + 1` completeness bound of
`unboundedOfficialSubtree_address_length_le_of_complete`. -/
theorem unboundedOfficialSubtree_address_length_le_atomCount
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {address : List Nat} {node : OfficialCIPNode input.Atom}
    (reachable : input.UnboundedOfficialSubtree (OfficialCIPNode.root root) address node) :
    address.length ≤ input.certified.input.molecule.atomCount := by
  have shape := input.unboundedOfficialSubtree_shape reachable
    (input.reachableOccurrenceShape_root root)
  have length := input.unboundedOfficialSubtree_history_length reachable
  simp [OfficialCIPNode.root] at length
  unfold ReachableOccurrenceShape at shape
  rcases shape with ⟨_real, nodup⟩ | ⟨⟨_distance, _ring⟩, tailNodup⟩ |
    ⟨⟨_distance, _multiple⟩, tailNodup⟩
  · have cardLe : node.history.length ≤ input.certified.input.molecule.atomCount := by
      simpa using nodup.length_le_card
    omega
  · have tailCard : node.history.tail.length ≤
        input.certified.input.molecule.atomCount := by
      simpa using tailNodup.length_le_card
    have tailLength : node.history.tail.length = address.length := by
      simp only [List.length_tail]
      omega
    omega
  · have tailCard : node.history.tail.length ≤
        input.certified.input.molecule.atomCount := by
      simpa using tailNodup.length_le_card
    have tailLength : node.history.tail.length = address.length := by
      simp only [List.length_tail]
      omega
    omega

/-- **Converse provenance classification.**  Every executable descendant of a real atom root is
real with a concrete atom history or carries a genuine ring/multiple-bond duplicate provenance.
No placeholder nodes occur. -/
theorem unboundedOfficialSubtree_provenance_trichotomy
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {address : List Nat} {node : OfficialCIPNode input.Atom}
    (reachable : input.UnboundedOfficialSubtree (OfficialCIPNode.root root) address node) :
    (node.provenance = OfficialCIPNodeProvenance.realAtom ∧ node.history.Nodup) ∨
      (∃ distance, node.provenance =
        OfficialCIPNodeProvenance.ringDuplicate distance) ∨
      (∃ distance, node.provenance =
        OfficialCIPNodeProvenance.multipleBondDuplicate distance) := by
  have shape := input.unboundedOfficialSubtree_shape reachable
    (input.reachableOccurrenceShape_root root)
  unfold ReachableOccurrenceShape at shape
  rcases shape with ⟨real, nodup⟩ | ⟨⟨distance, ring⟩, _tailNodup⟩ |
    ⟨⟨distance, multiple⟩, _tailNodup⟩
  · exact Or.inl ⟨real, nodup⟩
  · exact Or.inr (Or.inl ⟨distance, ring⟩)
  · exact Or.inr (Or.inr ⟨distance, multiple⟩)

/-- **Converse carrier coverage at the sharp bound.**  Every executable descendant of an
arbitrary atom root is present in the shared occurrence enumeration at fuel `atomCount`, with
remaining depth `atomCount + 1 - address.length`.  This is the exact-shape counterpart of the
forward coverage theorem, and it is derived from the structural bound
`unboundedOfficialSubtree_address_length_le_atomCount` rather than from a completeness
hypothesis. -/
theorem unboundedOfficialSubtree_mem_localizedOccurrences
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {address : List Nat} {node : OfficialCIPNode input.Atom}
    (reachable : input.UnboundedOfficialSubtree (OfficialCIPNode.root root) address node) :
    { root := root
      address := address
      node := node
      remaining := input.certified.input.molecule.atomCount + 1 - address.length } ∈
      input.localizedOccurrences (input.certified.input.molecule.atomCount) := by
  have bound := input.unboundedOfficialSubtree_address_length_le_atomCount reachable
  have enough : address.length ≤ input.certified.input.molecule.atomCount + 1 := by
    omega
  have covered := input.mem_localizedOccurrenceSubtree_of_unbounded
    (root := root) (fuel := input.certified.input.molecule.atomCount + 1)
    (path := []) reachable enough
  unfold localizedOccurrences
  rw [List.mem_dedup, List.mem_flatMap]
  refine ⟨root, by simp, ?_⟩
  simpa [localizedOccurrencesAtAtom] using covered

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority assertions

`assert_kernel_only` permits exactly `propext`, `Classical.choice` and `Quot.sound`; it rejects
`sorryAx`, project axioms and native/compiler trust.  The guarded declarations are the decisive
endpoints of this module. -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_executableOfficialNeighborCopies_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_executableOfficialChildCopies_of_adjacent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_executableOfficialCIPChildren_of_adjacent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableOfficialCIPChildren_history_length
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_zipIdx_map_of_mem
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableOfficialChildCopySlot_mem
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableOfficialChildCopySlot_inj
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableOfficialChildCopySlot_ne_of_copyIndex_ne
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.legitimateOccurrence_multiple_address_ne_of_copyIndex_ne
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.simpleOccurrencePath_unbounded
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unboundedOfficialSubtree_append_last
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.legitimateOccurrence_unbounded
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.legitimateOccurrence_provenance_trichotomy
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.legitimateOccurrence_address_length_le_atomCount
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.legitimateOccurrence_mem_localizedOccurrences_of_fuel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.legitimateOccurrence_mem_localizedOccurrences
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.legitimateOccurrenceCarrier_mem_carrier
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.legitimateOccurrence_represented_in_carrier
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.legitimateOccurrence_coversInUniversalDepth
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.reachableOccurrenceShape_step
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unboundedOfficialSubtree_shape
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unboundedOfficialSubtree_history_length
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unboundedOfficialSubtree_address_length_le_atomCount
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unboundedOfficialSubtree_provenance_trichotomy
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unboundedOfficialSubtree_mem_localizedOccurrences
