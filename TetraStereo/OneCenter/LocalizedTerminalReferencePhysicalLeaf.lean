import TetraStereo.OneCenter.LocalizedParentFrameHistory
import TetraStereo.OneCenter.LocalizedPhysicalReferenceUniqueness
import TetraStereo.OneCenter.LocalizedRule3ShortCircuitExecutable
import TetraStereo.OneCenter.LocalizedOccurrenceCarrierCoverage
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-!
# Physical terminal leaves behind an actual Rule-3 reference lookup

`LocalizedRule3OccurrenceReferenceCursor` selects a physical reference atom from the uncut
cut-neighborhood of an endpoint cursor.  The selected cursor is an occurrence in the *finite*
localized carrier, so an empty executable children list at that cursor is only a statement about
the truncation depth of the carrier unless the selected occurrence is shown to be an actual
molecular neighbor of the reference atom.

This module proves that bridge for the real-atom branch of the lookup:

* `carrier_child_address_eq_cut` shows that any executable child slot of the selected cursor has
  to be the address of the incoming endpoint occurrence, because the intended cut-neighborhood of
  the selected cursor is empty;
* `carrier_neighbor_eq_cut_of_intended_empty` upgrades this from child slots to all carrier-tree
  neighbors of the selected cursor;
* `neighborFinset_eq_singleton_of_childCopies_nil` and
  `neighborFinset_eq_singleton_of_neighborCopies_all_eq` turn the resulting multiplicity
  classification of the official child copies into an exact graph statement
  `neighborFinset a = {e}` and `bond a e = 1`.

The main theorem `terminalReferencePhysicalLeafBridge` derives every structural premise from the
actual reference lookup soundness (`CanonicalLocalizedRule3ReferenceCursor`), keeps the
`ringDuplicate` branch explicit (it is *not* a real molecular terminal atom), and therefore closes
the real-atom chemical premise independently of the finite solver's shape equality.

The second part of the module records how the strict positivity premise
`0 < occurrence.remaining` is obtained at the complete universal carrier budget
`atomCount + 1`, using the existing universal-depth and bounded/unbounded bridge.
-/

/-! ## Parent history after one executable extension -/

/-- The official parent of one executable extension is the head of the parent node's branch
history.  This is the history-side form of `OfficialCIPNode.parent?` used to recover the endpoint
atom from an actual executable edge. -/
theorem executableExtend_parent?_eq_history_head?
    (input : CertifiedLocalizedCIPInput) (node : OfficialCIPNode input.Atom)
    (next : input.Atom) (copyIndex : Nat) :
    (node.extend next copyIndex).parent? = node.history.head? := by
  cases h : node.history <;> simp [OfficialCIPNode.parent?, OfficialCIPNode.extend, h]

/-! ## Graph-level multiplicity lemmas

The official child copies of an atom-bearing node are the executable neighbor copies of its
current atom, with the zero-index copy of the official parent removed.  The two lemmas below
classify the whole neighbor list from the shape of this copy list and conclude the exact bond
order. -/

/-- If a node with an observed current atom and an observed official parent has no child copies,
then its only graph neighbor is the official parent and the bond to it is a single bond.  The
surviving-copy argument is purely combinatorial: every neighbor copy other than the zero-index
parent copy would have survived the parent filter. -/
theorem neighborFinset_eq_singleton_of_childCopies_nil
    (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) (current adjacentAtom : input.Atom)
    (currentObserved : node.current? = some current)
    (parentObserved : node.parent? = some adjacentAtom)
    (copiesNil : input.executableOfficialChildCopies node = [])
    (adjacent : input.moleculeGraph.Adj current adjacentAtom) :
    input.moleculeGraph.neighborFinset current = {adjacentAtom} ∧
      input.moleculeGraph.bond current adjacentAtom = 1 := by
  have copiesEq : input.executableOfficialChildCopies node =
      (input.executableOfficialNeighborCopies current).filter
        (fun copy => !(copy.1 == adjacentAtom && copy.2 == 0)) := by
    unfold executableOfficialChildCopies
    rw [currentObserved]
    simp [parentObserved]
  have survivor : ∀ {x : input.Atom} {c : Nat},
      (x, c) ∈ input.executableOfficialNeighborCopies current →
      ¬ (x = adjacentAtom ∧ c = 0) → False := by
    intro x c present notCut
    have filtered : (x, c) ∈
        (input.executableOfficialNeighborCopies current).filter
          (fun copy => !(copy.1 == adjacentAtom && copy.2 == 0)) := by
      rw [List.mem_filter]
      refine ⟨present, ?_⟩
      by_cases same : x = adjacentAtom
      · have nonzero : c ≠ 0 := by
          intro zero
          exact notCut ⟨same, zero⟩
        simp [same, nonzero]
      · simp [same]
    rw [← copiesEq] at filtered
    rw [copiesNil] at filtered
    simp at filtered
  have neighborEq : ∀ x, input.moleculeGraph.Adj current x → x = adjacentAtom := by
    intro x adjX
    have positiveBond : 0 < input.moleculeGraph.bond current x := adjX
    have present : (x, 0) ∈ input.executableOfficialNeighborCopies current :=
      (input.mem_executableOfficialNeighborCopies_iff current x 0).mpr
        ⟨adjX, positiveBond⟩
    by_contra different
    exact survivor present (by rintro ⟨same, _zero⟩; exact different same)
  constructor
  · apply Finset.ext
    intro x
    constructor
    · intro mem
      have adjX := (input.moleculeGraph.mem_neighborFinset current x).mp mem
      have xEq : x = adjacentAtom := neighborEq x adjX
      rw [Finset.mem_singleton]
      exact xEq
    · intro mem
      rw [Finset.mem_singleton] at mem
      rw [mem]
      exact (input.moleculeGraph.mem_neighborFinset current adjacentAtom).mpr adjacent
  · have positive : 0 < input.moleculeGraph.bond current adjacentAtom := adjacent
    by_contra different
    have oneLe : 1 ≤ input.moleculeGraph.bond current adjacentAtom := positive
    have two : 1 < input.moleculeGraph.bond current adjacentAtom :=
      lt_of_le_of_ne oneLe (Ne.symm different)
    have present : (adjacentAtom, 1) ∈
        input.executableOfficialNeighborCopies current :=
      (input.mem_executableOfficialNeighborCopies_iff current adjacentAtom 1).mpr
        ⟨adjacent, two⟩
    exact survivor present (by rintro ⟨_same, zero⟩; exact Nat.one_ne_zero zero)

/-- If all executable neighbor copies of a current atom coincide with one seed copy, then the
neighbor set is the singleton of that copy's atom and the bond to it is a single bond.  The pair
`(seed.1, 0)` and `(seed.1, 1)` are both neighbor copies when the bond has positive order, so the
seed's copy index is forced to be `0` and the bond order is forced to be `1`. -/
theorem neighborFinset_eq_singleton_of_neighborCopies_all_eq
    (input : CertifiedLocalizedCIPInput)
    (current : input.Atom) (seed : input.Atom × Nat)
    (seedPresent : seed ∈ input.executableOfficialNeighborCopies current)
    (allEq : ∀ copy ∈ input.executableOfficialNeighborCopies current, copy = seed) :
    input.moleculeGraph.neighborFinset current = {seed.1} ∧
      input.moleculeGraph.bond current seed.1 = 1 := by
  have adjacency : input.moleculeGraph.Adj current seed.1 :=
    ((input.mem_executableOfficialNeighborCopies_iff current seed.1 seed.2).mp
      seedPresent).1
  have positiveBond : 0 < input.moleculeGraph.bond current seed.1 := adjacency
  have zeroPresent : (seed.1, 0) ∈
      input.executableOfficialNeighborCopies current :=
    (input.mem_executableOfficialNeighborCopies_iff current seed.1 0).mpr
      ⟨adjacency, positiveBond⟩
  have seedZero : seed = (seed.1, 0) := (allEq (seed.1, 0) zeroPresent).symm
  have seedSecondZero : seed.2 = 0 := by
    have := congrArg Prod.snd seedZero
    simpa using this
  constructor
  · apply Finset.ext
    intro x
    constructor
    · intro mem
      have adjX := (input.moleculeGraph.mem_neighborFinset current x).mp mem
      have positiveX : 0 < input.moleculeGraph.bond current x := adjX
      have present : (x, 0) ∈ input.executableOfficialNeighborCopies current :=
        (input.mem_executableOfficialNeighborCopies_iff current x 0).mpr
          ⟨adjX, positiveX⟩
      have eq := allEq (x, 0) present
      have xEq : x = seed.1 := (Prod.mk.inj eq).1
      rw [Finset.mem_singleton]
      exact xEq
    · intro mem
      rw [Finset.mem_singleton] at mem
      rw [mem]
      exact (input.moleculeGraph.mem_neighborFinset current seed.1).mpr adjacency
  · have positive : 0 < input.moleculeGraph.bond current seed.1 := adjacency
    by_contra different
    have oneLe : 1 ≤ input.moleculeGraph.bond current seed.1 := positive
    have two : 1 < input.moleculeGraph.bond current seed.1 :=
      lt_of_le_of_ne oneLe (Ne.symm different)
    have present : (seed.1, 1) ∈
        input.executableOfficialNeighborCopies current :=
      (input.mem_executableOfficialNeighborCopies_iff current seed.1 1).mpr
        ⟨adjacency, two⟩
    have eq := allEq (seed.1, 1) present
    have secondEq : 1 = seed.2 := (Prod.mk.inj eq).2
    omega

/-! ## Empty intended expansion pins every carrier child to the incoming cut -/

/-- **Child-slot bridge.**  If the intended cut-neighborhood of a selected cursor is empty, then
every executable child slot of its node is the address of the incoming endpoint occurrence.  The
child frame at that slot is an actual carrier member and an actual outward carrier child; since it
cannot be the cut address, it would otherwise belong to the intended neighborhood. -/
theorem carrier_child_address_eq_cut
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (previous : input.LocalizedCIPOccurrence fuel)
    (previousEq : cursor.previous? = some previous)
    (nonduplicate : cursor.occurrence.1.node.isDuplicateLeaf = false)
    (positive : 0 < cursor.occurrence.1.remaining)
    (empty : input.intendedLocalizedRerootChildFrames cursor = [])
    (child : OfficialCIPNode input.Atom) (slot : Nat)
    (childAtSlot : (child, slot) ∈
      (input.executableOfficialCIPChildren cursor.occurrence.1.node).zipIdx) :
    cursor.occurrence.1.address ++ [slot] = previous.1.address := by
  let childFrame : input.LocalizedCIPOccurrenceFrame :=
    { root := cursor.occurrence.1.root
      address := cursor.occurrence.1.address ++ [slot]
      node := child
      remaining := cursor.occurrence.1.remaining - 1 }
  have sourceDerived :=
    (input.mem_localizedOccurrences_iff fuel cursor.occurrence.1).mp cursor.occurrence.2
  have childDerived : input.DeclarativeLocalizedOccurrence fuel childFrame :=
    sourceDerived.immediateChild input positive childAtSlot
  have childPresent : childFrame ∈ input.localizedOccurrences fuel :=
    (input.mem_localizedOccurrences_iff fuel childFrame).mpr childDerived
  have neighbor : childFrame ∈
      input.localizedRerootNeighborFrames (fuel := fuel) cursor.occurrence.1 := by
    rw [localizedRerootNeighborFrames, List.mem_append]
    refine Or.inr ?_
    rw [localizedCarrierOutwardChildFrames, List.mem_filter]
    refine ⟨childPresent, ?_⟩
    simp [childFrame]
  by_contra different
  have memIntended : childFrame ∈ input.intendedLocalizedRerootChildFrames cursor := by
    unfold intendedLocalizedRerootChildFrames
    rw [if_neg (by simpa using nonduplicate), previousEq, List.mem_filter]
    exact ⟨neighbor, by simpa [childFrame] using different⟩
  rw [empty] at memIntended
  simp at memIntended

/-- **Neighbor-frame bridge.**  Under the hypotheses of `carrier_child_address_eq_cut` together
with cursor validity, every carrier-tree neighbor of the selected cursor is the incoming endpoint
occurrence.  Root equality is supplied by the neighbor-frame characterization, and carrier
functionality at a fixed root and address identifies the frames. -/
theorem carrier_neighbor_eq_cut_of_intended_empty
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (previous : input.LocalizedCIPOccurrence fuel)
    (previousEq : cursor.previous? = some previous)
    (nonduplicate : cursor.occurrence.1.node.isDuplicateLeaf = false)
    (empty : input.intendedLocalizedRerootChildFrames cursor = [])
    (valid : input.LocalizedRerootCursorValid cursor)
    (frame : input.LocalizedCIPOccurrenceFrame)
    (present : frame ∈
      input.localizedRerootNeighborFrames (fuel := fuel) cursor.occurrence.1) :
    frame = previous.1 := by
  have frameAddress : frame.address = previous.1.address := by
    by_contra different
    have memIntended : frame ∈ input.intendedLocalizedRerootChildFrames cursor := by
      unfold intendedLocalizedRerootChildFrames
      rw [if_neg (by simpa using nonduplicate), previousEq, List.mem_filter]
      exact ⟨present, by simpa using different⟩
    rw [empty] at memIntended
    simp at memIntended
  have frameRoot : frame.root = cursor.occurrence.1.root :=
    input.localizedRerootNeighborFrames_root_eq cursor.occurrence.1 frame present
  have previousRoot : cursor.occurrence.1.root = previous.1.root := by
    unfold LocalizedRerootCursorValid at valid
    rw [previousEq] at valid
    exact ((input.mem_localizedRerootNeighborFrames_iff
      previous.1 cursor.occurrence.1).mp valid).2.1
  have framePresent : frame ∈ input.localizedOccurrences fuel :=
    input.mem_localizedOccurrences_of_mem_localizedRerootNeighborFrames
      cursor.occurrence.1 frame present
  exact input.declarativeLocalizedOccurrence_functional_at_root_address
    ((input.mem_localizedOccurrences_iff fuel frame).mp framePresent)
    ((input.mem_localizedOccurrences_iff fuel previous.1).mp previous.2)
    (frameRoot.trans previousRoot) frameAddress

/-! ## The real-atom terminal reference bridge -/

/-- **Exact physical-leaf bridge for a real selected reference atom.**

Let `endpointCursor` be an endpoint whose current official atom is `endpointAtom`, and let
`cursor` be the actual cursor selected by the executable Rule-3 reference lookup for
`reference`.  The selected node has real-atom provenance, strictly positive remaining depth, and
its executable reroot expansion is the empty list.  Then `reference` has exactly one molecular
neighbor, namely the endpoint atom, and the bond between them is a single bond.

No structural premise is assumed: the carrier membership, incoming-cut coordinate, current atom,
physical provenance, and cursor validity are all derived from the reference lookup soundness
`CanonicalLocalizedRule3ReferenceCursor`.  The two carrier-tree orientations are handled
separately.  In the parent orientation the endpoint is the unique executable child copy of the
selected node, so all neighbor copies coincide with the endpoint copy.  In the outward
orientation the selected node is *an* executable child of the endpoint (the endpoint may have
other executable children); its own child copy list is empty, and the uniqueness in the conclusion
is the singleton physical-neighbor set of the selected reference, namely the endpoint atom, which
survives the parent cut as the only neighbor copy. -/
theorem terminalReferencePhysicalLeafBridge
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor : input.LocalizedRerootCursor fuel)
    {endpointAtom reference : input.Atom}
    (endpointCurrent :
      endpointCursor.occurrence.1.node.current? = some endpointAtom)
    (cursor : input.LocalizedRerootCursor fuel)
    (selected : input.localizedRule3ReferenceCursorExec?
      endpointCursor reference = some cursor)
    (real : cursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (positive : 0 < cursor.occurrence.1.remaining)
    (leaf : input.executableLocalizedRerootChildren? cursor = some []) :
    input.moleculeGraph.neighborFinset reference = {endpointAtom} ∧
      input.moleculeGraph.bond reference endpointAtom = 1 := by
  have computed : input.localizedRule3ReferenceCursor?
      endpointCursor reference = some cursor := by
    rw [input.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?]
    exact selected
  have canonical : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor cursor reference :=
    (input.localizedRule3ReferenceCursor?_eq_some_iff
      endpointCursor cursor reference).mp computed
  have valid : input.LocalizedRerootCursorValid cursor :=
    CanonicalLocalizedRule3ReferenceCursor.valid input
      endpointCursor cursor reference canonical
  rcases canonical with ⟨children, childrenComputed, childrenDerived, cursorPresent,
    cursorCurrent, cursorPhysical, cursorPrevious, unique⟩
  have childrenEq : children =
      input.executableLocalizedRerootChildren endpointCursor := by
    have computedExecutable := childrenComputed
    rw [input.localizedRerootChildren?_eq_some_executable endpointCursor]
      at computedExecutable
    exact (Option.some.inj computedExecutable).symm
  have executablePresent : cursor ∈
      input.executableLocalizedRerootChildren endpointCursor := by
    rw [← childrenEq]
    exact cursorPresent
  have executableNil : input.executableLocalizedRerootChildren cursor = [] := by
    have someNil := leaf
    rw [input.executableLocalizedRerootChildren?_eq_some cursor] at someNil
    exact Option.some.inj someNil
  have intendedNil : input.intendedLocalizedRerootChildFrames cursor = [] := by
    rw [← input.executableLocalizedRerootChildren_map cursor, executableNil]
    rfl
  have nonduplicate : cursor.occurrence.1.node.isDuplicateLeaf = false := by
    simp [OfficialCIPNode.isDuplicateLeaf, real]
  have cursorNeighbor : cursor.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := fuel)
        endpointCursor.occurrence.1 := by
    unfold LocalizedRerootCursorValid at valid
    rw [cursorPrevious] at valid
    exact valid
  have cursorAdjacent : input.LocalizedCarrierTreeAdjacent
      cursor.occurrence.1 endpointCursor.occurrence.1 :=
    ((input.mem_localizedRerootNeighborFrames_iff
      endpointCursor.occurrence.1 cursor.occurrence.1).mp cursorNeighbor).2
  have neighborEqCut : ∀ frame ∈
      input.localizedRerootNeighborFrames (fuel := fuel) cursor.occurrence.1,
      frame = endpointCursor.occurrence.1 :=
    input.carrier_neighbor_eq_cut_of_intended_empty cursor
      endpointCursor.occurrence cursorPrevious nonduplicate intendedNil valid
  rcases cursorAdjacent with ⟨sameRoot, cursorParentCase | cursorOutwardCase⟩
  · -- The selected reference cursor is the carrier parent of the endpoint occurrence.
    obtain ⟨slotE, endpointAddress⟩ :=
      exists_eq_append_singleton_of_eq_dropLast cursorParentCase.1 cursorParentCase.2
    obtain ⟨child, seedAtSlot, endpointFrame⟩ :=
      input.declarativeLocalizedOccurrence_immediate_child
        ((input.mem_localizedOccurrences_iff fuel cursor.occurrence.1).mp
          cursor.occurrence.2)
        ((input.mem_localizedOccurrences_iff fuel endpointCursor.occurrence.1).mp
          endpointCursor.occurrence.2)
        sameRoot.symm slotE endpointAddress
    have endpointNodeEq : endpointCursor.occurrence.1.node = child :=
      congrArg LocalizedCIPOccurrenceFrame.node endpointFrame
    have childMember : child ∈
        input.executableOfficialCIPChildren cursor.occurrence.1.node :=
      List.fst_mem_of_mem_zipIdx seedAtSlot
    rw [executableOfficialCIPChildren, if_neg (by simpa using nonduplicate),
      List.mem_map] at childMember
    obtain ⟨copy, copyMem, copyEq⟩ := childMember
    obtain ⟨copyAtom, copyIndex⟩ := copy
    have copyAtomEq : copyAtom = endpointAtom := by
      have observed := congrArg OfficialCIPNode.current? copyEq
      have childCurrent : child.current? = some endpointAtom := by
        rw [← endpointNodeEq]
        exact endpointCurrent
      rw [childCurrent, OfficialCIPNode.extend_current?] at observed
      exact Option.some.inj observed
    have allEqual : ∀ cp ∈
        input.executableOfficialChildCopies cursor.occurrence.1.node,
        cp = (copyAtom, copyIndex) := by
      intro cp cpMem
      obtain ⟨x, i⟩ := cp
      have cpSlotMem : (cursor.occurrence.1.node.extend x i,
          input.executableOfficialChildCopySlot cursor.occurrence.1.node x i) ∈
          (input.executableOfficialCIPChildren cursor.occurrence.1.node).zipIdx :=
        input.executableOfficialChildCopySlot_mem cursor.occurrence.1.node x i
          nonduplicate cpMem
      have seedSlotMem : (cursor.occurrence.1.node.extend copyAtom copyIndex,
          input.executableOfficialChildCopySlot
            cursor.occurrence.1.node copyAtom copyIndex) ∈
          (input.executableOfficialCIPChildren cursor.occurrence.1.node).zipIdx :=
        input.executableOfficialChildCopySlot_mem cursor.occurrence.1.node
          copyAtom copyIndex nonduplicate copyMem
      have cpAddress :=
        input.carrier_child_address_eq_cut cursor endpointCursor.occurrence
          cursorPrevious nonduplicate positive intendedNil _ _ cpSlotMem
      have seedAddress :=
        input.carrier_child_address_eq_cut cursor endpointCursor.occurrence
          cursorPrevious nonduplicate positive intendedNil _ _ seedSlotMem
      have slotsEq : input.executableOfficialChildCopySlot
            cursor.occurrence.1.node x i =
          input.executableOfficialChildCopySlot
            cursor.occurrence.1.node copyAtom copyIndex := by
        have combined : cursor.occurrence.1.address ++
            [input.executableOfficialChildCopySlot cursor.occurrence.1.node x i] =
            cursor.occurrence.1.address ++
            [input.executableOfficialChildCopySlot
              cursor.occurrence.1.node copyAtom copyIndex] := by
          rw [cpAddress, seedAddress]
        simpa using combined
      have pairEq :=
        (input.executableOfficialChildCopySlot_inj (node := cursor.occurrence.1.node)
          cpMem copyMem).mp slotsEq
      simpa using pairEq
    have allEqualEndpoint : ∀ cp ∈
        input.executableOfficialChildCopies cursor.occurrence.1.node,
        cp = (endpointAtom, copyIndex) := by
      intro cp cpMem
      have := allEqual cp cpMem
      rw [copyAtomEq] at this
      exact this
    have seedMemEndpoint : (endpointAtom, copyIndex) ∈
        input.executableOfficialChildCopies cursor.occurrence.1.node := by
      simpa [copyAtomEq] using copyMem
    have rAddressNil : cursor.occurrence.1.address = [] := by
      by_contra nonroot
      obtain ⟨parentFrame, parentPresent, parentRoot, parentAddress,
        parentRemaining, parentActive, parentExtendExists, parentCurrent,
        parentCurrentEq, parentHistory⟩ :=
        input.exists_parentFrame_of_mem_localizedOccurrences
          cursor.occurrence.2 nonroot
      have parentLength : parentFrame.address.length + 1 =
          cursor.occurrence.1.address.length := by
        have length := congrArg List.length parentAddress
        rw [List.length_dropLast] at length
        have positiveLength : 0 < cursor.occurrence.1.address.length :=
          List.length_pos_iff.mpr nonroot
        omega
      have parentInParentFrames : parentFrame ∈
          input.localizedCarrierParentFrames (fuel := fuel)
            cursor.occurrence.1 := by
        rw [localizedCarrierParentFrames, List.mem_filter]
        refine ⟨parentPresent, ?_⟩
        simp only [Bool.and_eq_true, beq_iff_eq]
        exact ⟨⟨parentRoot, parentLength⟩, parentAddress⟩
      have parentInNeighbor : parentFrame ∈
          input.localizedRerootNeighborFrames (fuel := fuel)
            cursor.occurrence.1 := by
        rw [localizedRerootNeighborFrames, List.mem_append]
        exact Or.inl parentInParentFrames
      have parentEqEndpoint : parentFrame = endpointCursor.occurrence.1 :=
        neighborEqCut parentFrame parentInNeighbor
      have lengthEq : parentFrame.address.length =
          endpointCursor.occurrence.1.address.length := by
        rw [parentEqEndpoint]
      omega
    have rootFrame := input.declarativeLocalizedOccurrence_eq_root_of_address_nil
      ((input.mem_localizedOccurrences_iff fuel cursor.occurrence.1).mp
        cursor.occurrence.2) rAddressNil
    have cursorNodeRoot : cursor.occurrence.1.node =
        OfficialCIPNode.root cursor.occurrence.1.root :=
      congrArg LocalizedCIPOccurrenceFrame.node rootFrame
    have cursorParentNone : cursor.occurrence.1.node.parent? = none := by
      rw [cursorNodeRoot]
      simp [OfficialCIPNode.root, OfficialCIPNode.parent?]
    have copiesEq : input.executableOfficialChildCopies cursor.occurrence.1.node =
        input.executableOfficialNeighborCopies reference := by
      unfold executableOfficialChildCopies
      rw [cursorCurrent]
      simp [cursorParentNone]
    have neighborAllEq : ∀ cp ∈
        input.executableOfficialNeighborCopies reference,
        cp = (endpointAtom, copyIndex) := by
      intro cp cpMem
      rw [← copiesEq] at cpMem
      exact allEqualEndpoint cp cpMem
    have neighborSeedMem : (endpointAtom, copyIndex) ∈
        input.executableOfficialNeighborCopies reference := by
      rw [← copiesEq]
      exact seedMemEndpoint
    have result := input.neighborFinset_eq_singleton_of_neighborCopies_all_eq
      reference (endpointAtom, copyIndex) neighborSeedMem neighborAllEq
    simpa using result
  · -- The selected reference cursor is an official outward child of the endpoint.
    obtain ⟨slotR, cursorAddress⟩ :=
      exists_eq_append_singleton_of_eq_dropLast cursorOutwardCase.1 cursorOutwardCase.2
    obtain ⟨child, childAtSlot, cursorFrame⟩ :=
      input.declarativeLocalizedOccurrence_immediate_child
        ((input.mem_localizedOccurrences_iff fuel endpointCursor.occurrence.1).mp
          endpointCursor.occurrence.2)
        ((input.mem_localizedOccurrences_iff fuel cursor.occurrence.1).mp
          cursor.occurrence.2)
        sameRoot slotR cursorAddress
    have cursorNodeEq : cursor.occurrence.1.node = child :=
      congrArg LocalizedCIPOccurrenceFrame.node cursorFrame
    have cursorMember : cursor.occurrence.1.node ∈
        input.executableOfficialCIPChildren endpointCursor.occurrence.1.node := by
      rw [cursorNodeEq]
      exact List.fst_mem_of_mem_zipIdx childAtSlot
    have childrenNil : input.executableOfficialCIPChildren
        cursor.occurrence.1.node = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro child' childMem
      rw [List.mem_iff_getElem?] at childMem
      obtain ⟨slot, childAtSlot'⟩ := childMem
      have zipMem : (child', slot) ∈
          (input.executableOfficialCIPChildren cursor.occurrence.1.node).zipIdx :=
        (List.mk_mem_zipIdx_iff_getElem?).mpr childAtSlot'
      have addressEq :=
        input.carrier_child_address_eq_cut cursor endpointCursor.occurrence
          cursorPrevious nonduplicate positive intendedNil child' slot zipMem
      rw [cursorAddress] at addressEq
      have lengthEq := congrArg List.length addressEq
      simp only [List.length_append, List.length_singleton] at lengthEq
      omega
    have copiesNil : input.executableOfficialChildCopies
        cursor.occurrence.1.node = [] := by
      rw [executableOfficialCIPChildren,
        if_neg (by simpa using nonduplicate)] at childrenNil
      exact List.map_eq_nil_iff.mp childrenNil
    have adjacencyEA : input.moleculeGraph.Adj endpointAtom reference :=
      input.adj_of_mem_executableOfficialCIPChildren
        endpointCursor.occurrence.1.node cursor.occurrence.1.node
        endpointAtom reference endpointCurrent cursorCurrent cursorMember
    have adjacencyAE : input.moleculeGraph.Adj reference endpointAtom :=
      (input.moleculeGraph.adj_symm).mp adjacencyEA
    have endpointHistoryHead :
        endpointCursor.occurrence.1.node.history.head? = some endpointAtom :=
      (input.declarativeLocalizedOccurrence_history_head_eq_current
        ((input.mem_localizedOccurrences_iff fuel endpointCursor.occurrence.1).mp
          endpointCursor.occurrence.2)).trans endpointCurrent
    have cursorParent : cursor.occurrence.1.node.parent? = some endpointAtom := by
      obtain ⟨next, copyIndex, cursorExtend⟩ :=
        input.eq_extend_of_mem_executableOfficialCIPChildren
          endpointCursor.occurrence.1.node cursor.occurrence.1.node cursorMember
      rw [cursorExtend, executableExtend_parent?_eq_history_head?,
        endpointHistoryHead]
    exact input.neighborFinset_eq_singleton_of_childCopies_nil
      cursor.occurrence.1.node reference endpointAtom cursorCurrent
      cursorParent copiesNil adjacencyAE

/-- **Two selected real references at one endpoint.**  Both references have the endpoint atom as
their unique molecular neighbor, with bond order one.  This is the form consumed by the H/H
witness: equal official labels on the two references can be compared as molecular terminal
ligands, independently of finite carrier or solver equality. -/
theorem terminalReferencePair_physical_leaf_bridge
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor : input.LocalizedRerootCursor fuel)
    {endpointAtom firstReference secondReference : input.Atom}
    (endpointCurrent :
      endpointCursor.occurrence.1.node.current? = some endpointAtom)
    (firstCursor secondCursor : input.LocalizedRerootCursor fuel)
    (firstSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor firstReference = some firstCursor)
    (secondSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor secondReference = some secondCursor)
    (firstReal : firstCursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (secondReal : secondCursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (firstPositive : 0 < firstCursor.occurrence.1.remaining)
    (secondPositive : 0 < secondCursor.occurrence.1.remaining)
    (firstLeaf : input.executableLocalizedRerootChildren? firstCursor = some [])
    (secondLeaf : input.executableLocalizedRerootChildren? secondCursor = some []) :
    (input.moleculeGraph.neighborFinset firstReference = {endpointAtom} ∧
      input.moleculeGraph.bond firstReference endpointAtom = 1) ∧
    (input.moleculeGraph.neighborFinset secondReference = {endpointAtom} ∧
      input.moleculeGraph.bond secondReference endpointAtom = 1) :=
  ⟨input.terminalReferencePhysicalLeafBridge endpointCursor endpointCurrent
      firstCursor firstSelected firstReal firstPositive firstLeaf,
   input.terminalReferencePhysicalLeafBridge endpointCursor endpointCurrent
      secondCursor secondSelected secondReal secondPositive secondLeaf⟩

/-! ## Remaining depth at the complete universal carrier budget

The terminal guard requires `0 < occurrence.remaining` to rule out a truncation leaf.  At the
universal carrier budget `atomCount + 1` this is automatic for every occurrence whose coordinate
is realized by an actual unbounded executable path: the universal-depth theorem bounds the
address length by `atomCount + 1`, so the remaining depth is strictly positive.  The statements
below use the existing bounded/unbounded bridge and are independent of the finite solver shape. -/

/-- The proof-relevant occurrence assigned to an unbounded atom-rooted descendant at the
universal carrier budget has strictly positive remaining depth. -/
theorem universalDepthUnboundedOccurrence_remaining_pos
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    {address : List Nat} {descendant : OfficialCIPNode input.Atom}
    (reachable : input.UnboundedOfficialSubtree
      (OfficialCIPNode.root atom) address descendant) :
    0 < (input.localizedUnboundedOccurrenceAtAtom atom reachable).1.remaining := by
  rw [localizedUnboundedOccurrenceAtAtom_remaining]
  exact input.localizedOccurrenceUniversalDepth_atom_remaining_pos atom reachable

/-- **Source-faithful positivity at universal depth.**  A carrier occurrence at fuel
`atomCount + 1` whose root and address are shared with an actual unbounded executable descendant
has strictly positive remaining depth.  Carrier functionality identifies the occurrence with the
proof-relevant universal occurrence, so the positivity is derived from the unbounded witness and
not from a trusted finite enumeration. -/
theorem carrierOccurrence_remaining_pos_of_unbounded
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    {address : List Nat} {descendant : OfficialCIPNode input.Atom}
    (reachable : input.UnboundedOfficialSubtree
      (OfficialCIPNode.root atom) address descendant)
    (occurrence : input.LocalizedCIPOccurrence
      (input.certified.input.molecule.atomCount + 1))
    (rootEq : occurrence.1.root = atom)
    (addressEq : occurrence.1.address = address) :
    0 < occurrence.1.remaining := by
  let universal := input.localizedUnboundedOccurrenceAtAtom atom reachable
  have sameRoot : occurrence.1.root = universal.1.root := by
    rw [rootEq]
    rfl
  have sameAddress : occurrence.1.address = universal.1.address := by
    rw [addressEq]
    rfl
  have frameEq : occurrence.1 = universal.1 :=
    input.declarativeLocalizedOccurrence_functional_at_root_address
      ((input.mem_localizedOccurrences_iff _ occurrence.1).mp occurrence.2)
      ((input.mem_localizedOccurrences_iff _ universal.1).mp universal.2)
      sameRoot sameAddress
  rw [frameEq]
  exact input.universalDepthUnboundedOccurrence_remaining_pos atom reachable

/-- A legitimate (source-faithful) occurrence has strictly positive remaining depth at the
complete universal budget `atomCount + 1`: its address length is bounded by the atom count, so at
least one full level of the budget remains. -/
theorem legitimateOccurrence_universalDepth_remaining_pos
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (occ : LegitimateOccurrence input root node address) :
    0 < input.certified.input.molecule.atomCount + 1 + 1 - address.length := by
  have bound := input.legitimateOccurrence_address_length_le_atomCount occ
  omega

/-- The universal-depth frame of a legitimate occurrence is an actual member of the shared
deduplicated carrier at fuel `atomCount + 1`. -/
theorem legitimateOccurrence_universalDepth_frame_mem
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (occ : LegitimateOccurrence input root node address) :
    { root := root
      address := address
      node := node
      remaining := input.certified.input.molecule.atomCount + 1 + 1 -
        address.length } ∈
      input.localizedOccurrences (input.certified.input.molecule.atomCount + 1) :=
  input.localizedOccurrenceUniversalDepth_covers_atom_moleculeWide root
    (input.legitimateOccurrence_unbounded occ)

/-- The universal-depth frame of a legitimate occurrence is a genuine carrier occurrence with
strictly positive remaining depth. -/
theorem legitimateOccurrence_universalDepth_remaining_pos_and_mem
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (occ : LegitimateOccurrence input root node address) :
    0 < input.certified.input.molecule.atomCount + 1 + 1 - address.length ∧
      { root := root
        address := address
        node := node
        remaining := input.certified.input.molecule.atomCount + 1 + 1 -
          address.length } ∈
        input.localizedOccurrences
          (input.certified.input.molecule.atomCount + 1) :=
  ⟨input.legitimateOccurrence_universalDepth_remaining_pos occ,
   input.legitimateOccurrence_universalDepth_frame_mem occ⟩

/-- **Physical-leaf bridge at the complete universal carrier budget.**  The positivity premise of
`terminalReferencePhysicalLeafBridge` is derived from an actual unbounded executable path sharing
the reference cursor's root and address, rather than assumed about the finite carrier. -/
theorem terminalReferencePhysicalLeafBridge_universalDepth
    (input : CertifiedLocalizedCIPInput) {rootAtom : input.Atom}
    {address : List Nat} {descendant : OfficialCIPNode input.Atom}
    (reachable : input.UnboundedOfficialSubtree
      (OfficialCIPNode.root rootAtom) address descendant)
    (endpointCursor : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1))
    {endpointAtom reference : input.Atom}
    (endpointCurrent :
      endpointCursor.occurrence.1.node.current? = some endpointAtom)
    (cursor : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1))
    (selected : input.localizedRule3ReferenceCursorExec?
      endpointCursor reference = some cursor)
    (real : cursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (cursorRoot : cursor.occurrence.1.root = rootAtom)
    (cursorAddress : cursor.occurrence.1.address = address)
    (leaf : input.executableLocalizedRerootChildren? cursor = some []) :
    input.moleculeGraph.neighborFinset reference = {endpointAtom} ∧
      input.moleculeGraph.bond reference endpointAtom = 1 :=
  input.terminalReferencePhysicalLeafBridge endpointCursor endpointCurrent
    cursor selected real
    (input.carrierOccurrence_remaining_pos_of_unbounded rootAtom reachable
      cursor.occurrence cursorRoot cursorAddress)
    leaf

/-! ## The ring-duplicate branch is kept explicit

The executable reference lookup admits both real-atom and ring-duplicate provenances.  A
ring-duplicate node is a duplicate leaf, so its executable expansion is empty for free.  The empty
leaf check therefore cannot by itself distinguish a ring closure from a fresh molecular terminal
atom, and the `realAtom` hypothesis of `terminalReferencePhysicalLeafBridge` is chemically
essential.  The theorems below record the residual branch without claiming that ring duplicates
are real molecular leaves. -/

/-- A ring-duplicate official node is a duplicate leaf and has no executable official children. -/
theorem ringDuplicate_executableOfficialCIPChildren_eq_nil
    (input : CertifiedLocalizedCIPInput) (node : OfficialCIPNode input.Atom)
    {distance : Nat}
    (ring : node.provenance =
      OfficialCIPNodeProvenance.ringDuplicate distance) :
    node.isDuplicateLeaf = true ∧ input.executableOfficialCIPChildren node = [] := by
  have duplicate : node.isDuplicateLeaf = true := by
    simp [OfficialCIPNode.isDuplicateLeaf, ring]
  exact ⟨duplicate, by simp [executableOfficialCIPChildren, duplicate]⟩

/-- A ring-duplicate reference cursor has an empty executable reroot expansion vacuously.  This is
exactly the sense in which the finite leaf check can be satisfied by a ring duplicate. -/
theorem ringDuplicate_executableLocalizedRerootChildren?_eq_some_nil
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) {distance : Nat}
    (ring : cursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.ringDuplicate distance) :
    input.executableLocalizedRerootChildren? cursor = some [] := by
  have duplicate : cursor.occurrence.1.node.isDuplicateLeaf = true := by
    simp [OfficialCIPNode.isDuplicateLeaf, ring]
  unfold executableLocalizedRerootChildren? executableLocalizedRerootChildren
  simp [intendedLocalizedRerootChildFrames, duplicate]

/-- The actual executable reference lookup admits exactly two physical provenance branches: a
real atom or a ring duplicate.  This is the source-faithful guard domain; the real branch is
closed by `terminalReferencePhysicalLeafBridge`, and the ring branch is the explicitly retained
residual. -/
theorem terminalReference_provenance_cases
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor cursor : input.LocalizedRerootCursor fuel)
    (reference : input.Atom)
    (selected : input.localizedRule3ReferenceCursorExec?
      endpointCursor reference = some cursor) :
    cursor.occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.realAtom ∨
      ∃ distance, cursor.occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.ringDuplicate distance := by
  have computed : input.localizedRule3ReferenceCursor?
      endpointCursor reference = some cursor := by
    rw [input.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?]
    exact selected
  have canonical : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor cursor reference :=
    (input.localizedRule3ReferenceCursor?_eq_some_iff
      endpointCursor cursor reference).mp computed
  rcases canonical with ⟨children, childrenComputed, childrenDerived, cursorPresent,
    cursorCurrent, cursorPhysical, cursorPrevious, unique⟩
  cases provenance : cursor.occurrence.1.node.provenance <;>
    simp [LocalizedRule3PhysicalReferenceProvenance, provenance] at cursorPhysical
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

/-- **Residual ring branch.**  The ring-duplicate reference is still a declarative reference
cursor and still a physical provenance for the lookup, but it is a duplicate leaf whose empty
expansion is vacuous.  It is *not* a real molecular terminal atom, so this branch is reported as
residual rather than substituted for the real-atom conclusion. -/
theorem terminalReference_ringDuplicate_residual
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor cursor : input.LocalizedRerootCursor fuel)
    (reference : input.Atom) {distance : Nat}
    (selected : input.localizedRule3ReferenceCursorExec?
      endpointCursor reference = some cursor)
    (ring : cursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.ringDuplicate distance) :
    input.DeclarativeLocalizedRule3ReferenceCursor endpointCursor cursor reference ∧
      LocalizedRule3PhysicalReferenceProvenance
        cursor.occurrence.1.node.provenance ∧
      cursor.occurrence.1.node.isDuplicateLeaf = true ∧
      input.executableLocalizedRerootChildren? cursor = some [] := by
  have computed : input.localizedRule3ReferenceCursor?
      endpointCursor reference = some cursor := by
    rw [input.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?]
    exact selected
  have supported := input.localizedRule3ReferenceCursor?_ringDuplicate_supported
    endpointCursor cursor reference distance computed ring
  have duplicate := input.ringDuplicate_executableOfficialCIPChildren_eq_nil
    cursor.occurrence.1.node ring
  exact ⟨supported.1, supported.2, duplicate.1,
    input.ringDuplicate_executableLocalizedRerootChildren?_eq_some_nil cursor ring⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Direct kernel-authority guards for the exported declarations

Each exported declaration of this module is checked directly with `assert_kernel_only`, which
collects the kernel axioms of the declaration and rejects anything other than `propext`,
`Classical.choice`, and `Quot.sound`.  The guard is applied to the fully qualified names, after the
namespaces have been closed, so the checked constants are exactly the exported ones. -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableExtend_parent?_eq_history_head?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.neighborFinset_eq_singleton_of_childCopies_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.neighborFinset_eq_singleton_of_neighborCopies_all_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.carrier_child_address_eq_cut
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.carrier_neighbor_eq_cut_of_intended_empty
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalReferencePhysicalLeafBridge
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalReferencePair_physical_leaf_bridge
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.universalDepthUnboundedOccurrence_remaining_pos
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.carrierOccurrence_remaining_pos_of_unbounded
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.legitimateOccurrence_universalDepth_remaining_pos
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.legitimateOccurrence_universalDepth_frame_mem
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.legitimateOccurrence_universalDepth_remaining_pos_and_mem
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalReferencePhysicalLeafBridge_universalDepth
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ringDuplicate_executableOfficialCIPChildren_eq_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ringDuplicate_executableLocalizedRerootChildren?_eq_some_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalReference_provenance_cases
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalReference_ringDuplicate_residual
