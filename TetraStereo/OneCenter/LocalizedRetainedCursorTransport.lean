import TetraStereo.OneCenter.LocalizedRetainedOccurrenceTransport

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Cursor transport along one molecular automorphism

Consumer of `LocalizedRetainedOccurrenceTransport`. The accepted occurrence file is unchanged.

On one finite `SimpleBonded` input, `e` and `e⁻¹` invert `transportOccurrence` and
`transportCursor`. An executable child of a cursor transports to an executable child of the
transported cursor, and the two child lists are permutations. The matching is the carrier
parent or outward step plus the stored previous cut. It is not equality of the atom-index
slot lists, and it is not a supplied child matching.

`previous?` must be absent or rooted at the cursor. Both hold for a fresh cursor and for every
cursor emitted by `executableLocalizedRerootChildren`. A previous occurrence from another root
is outside this edge: its filter compares raw addresses, which are the locality gap.

`frameParity` stays the `ligandEquivOfIsTetrahedralCenter` enumeration. Canonical frame-slot
order is not derived here. `CutAnchor` and `KeptAfterCut` are not renamed here. No `Acyclic`,
no `descriptorMap`, no desired label, no `RootedDigraph.Iso`.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

open DeclarativeCIP.RetainedOccurrenceCarrier

variable (input : CertifiedLocalizedCIPInput)

private theorem aut_inv_coe_symm (e : input.moleculeGraph.Aut) :
    ((e⁻¹ : input.moleculeGraph.Aut) : Equiv.Perm input.Atom) =
      (e : Equiv.Perm input.Atom).symm := by
  rw [Subgroup.coe_inv]
  rfl

private theorem history_reverse_cons {α : Type*} {atoms : List α} {root : α}
    (headEq : atoms.head? = some root) : atoms = root :: atoms.tail := by
  cases atoms with
  | nil => simp at headEq
  | cons atom rest =>
      simp at headEq
      subst headEq
      rfl

/-- Image slots of a mapped history, read by `e⁻¹`, are the source canonical address. -/
theorem transportedAddress_symm_apply (e : input.moleculeGraph.Aut) (root : input.Atom)
    (node : OfficialCIPNode input.Atom)
    (head : node.history.reverse.head? = some root) :
    input.transportedAddress (e⁻¹) ((e : Equiv.Perm input.Atom) root)
        (mapOfficialNode (e : Equiv.Perm input.Atom) node) =
      input.canonicalAddress root node := by
  have hrev : node.history.reverse = root :: node.history.reverse.tail :=
    history_reverse_cons head
  have mappedRev : (mapOfficialNode (e : Equiv.Perm input.Atom) node).history.reverse =
      node.history.reverse.map (e : Equiv.Perm input.Atom) := by
    simp [mapOfficialNode, List.map_reverse]
  have mappedTail : (mapOfficialNode (e : Equiv.Perm input.Atom) node).history.reverse.tail =
      node.history.reverse.tail.map (e : Equiv.Perm input.Atom) := by
    rw [mappedRev, hrev]
    simp
  have roundTail :
      ((node.history.reverse.tail.map (e : Equiv.Perm input.Atom)).map
        (e : Equiv.Perm input.Atom).symm) = node.history.reverse.tail := by
    simp [List.map_map]
  rw [transportedAddress, canonicalAddress, mappedTail, input.aut_inv_coe_symm e,
    roundTail, Equiv.symm_apply_apply]

theorem transportOccurrence_inv_apply
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (occ : input.LocalizedCIPOccurrence fuel) :
    input.transportOccurrence singleBonded (e⁻¹)
        (input.transportOccurrence singleBonded e occ) = occ := by
  have packed := input.legitimateOccurrence_transport singleBonded e
    (input.carrierOccurrence_legitimate singleBonded occ)
  apply Subtype.ext
  apply LocalizedCIPOccurrenceFrame.ext input
  · simp only [transportOccurrence_root, input.aut_inv_coe_symm e, Equiv.symm_apply_apply]
  · rw [transportOccurrence_address, transportOccurrence_root, transportOccurrence_node,
      input.transportedAddress_symm_apply e occ.1.root occ.1.node packed.sourceHead]
    exact packed.sourceAddress.symm
  · simp only [transportOccurrence_node, input.aut_inv_coe_symm e]
    exact mapOfficialNode_symm_apply (e : Equiv.Perm input.Atom) occ.1.node
  · exact (input.transportOccurrence_remaining singleBonded (e⁻¹)
      (input.transportOccurrence singleBonded e occ)).trans
      (input.transportOccurrence_remaining singleBonded e occ)

theorem transportOccurrence_apply_inv
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (occ : input.LocalizedCIPOccurrence fuel) :
    input.transportOccurrence singleBonded e
        (input.transportOccurrence singleBonded (e⁻¹) occ) = occ := by
  simpa [inv_inv] using input.transportOccurrence_inv_apply singleBonded (e⁻¹) occ

theorem transportCursor_inv_apply
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    input.transportCursor singleBonded (e⁻¹)
        (input.transportCursor singleBonded e cursor) = cursor := by
  apply LocalizedRerootCursor.ext input
  · exact input.transportOccurrence_inv_apply singleBonded e cursor.occurrence
  · simp only [transportCursor_previous?]
    cases cursor.previous? with
    | none => rfl
    | some previous =>
        simp [input.transportOccurrence_inv_apply singleBonded e previous]

theorem transportCursor_apply_inv
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    input.transportCursor singleBonded e
        (input.transportCursor singleBonded (e⁻¹) cursor) = cursor := by
  simpa [inv_inv] using input.transportCursor_inv_apply singleBonded (e⁻¹) cursor

theorem transportCursor_injective
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) (fuel : Nat) :
    Function.Injective (input.transportCursor singleBonded e (fuel := fuel)) := by
  intro left right equal
  apply congrArg (input.transportCursor singleBonded (e⁻¹) (fuel := fuel)) at equal
  simpa [input.transportCursor_inv_apply singleBonded e left,
    input.transportCursor_inv_apply singleBonded e right] using equal

theorem isDuplicateLeaf_transport
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (occ : input.LocalizedCIPOccurrence fuel) :
    (input.transportOccurrence singleBonded e occ).1.node.isDuplicateLeaf =
      occ.1.node.isDuplicateLeaf := by
  simp [transportOccurrence_node, mapOfficialNode, OfficialCIPNode.isDuplicateLeaf]

/-- Under `SimpleBonded` every executable child copy is the zero copy. -/
theorem executableOfficialChildCopy_index_zero
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (node : OfficialCIPNode input.Atom) (next : input.Atom) (copyIndex : Nat)
    (present : (next, copyIndex) ∈ input.executableOfficialChildCopies node) :
    copyIndex = 0 := by
  have inNeighbors : ∃ current,
      (next, copyIndex) ∈ input.executableOfficialNeighborCopies current := by
    unfold executableOfficialChildCopies at present
    cases hcurrent : node.current? with
    | none => simp [hcurrent] at present
    | some current =>
        cases hparent : node.parent? with
        | none =>
            rw [hcurrent, hparent] at present
            exact ⟨current, present⟩
        | some parent =>
            rw [hcurrent, hparent] at present
            exact ⟨current, List.mem_of_mem_filter present⟩
  obtain ⟨current, neighborPresent⟩ := inNeighbors
  have adjacent := input.adj_of_mem_executableOfficialNeighborCopies current next copyIndex
    neighborPresent
  have bondOne := singleBonded current next adjacent
  rw [executableOfficialNeighborCopies, List.mem_flatMap] at neighborPresent
  obtain ⟨_source, _sourcePresent, mapped⟩ := neighborPresent
  rw [List.mem_map] at mapped
  obtain ⟨index, indexPresent, pairEq⟩ := mapped
  cases pairEq
  have copyLt : copyIndex < 1 := by
    simpa [bondOne] using List.mem_range.mp indexPresent
  exact Nat.lt_one_iff.mp copyLt

theorem transportOccurrence_address_eq_iff_of_sameRoot
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    {left right : input.LocalizedCIPOccurrence fuel}
    (sameRoot : left.1.root = right.1.root) :
    left.1.address = right.1.address ↔
      (input.transportOccurrence singleBonded e left).1.address =
        (input.transportOccurrence singleBonded e right).1.address := by
  constructor
  · intro sameAddress
    have leftDerived := (input.mem_localizedOccurrences_iff fuel left.1).mp left.2
    have rightDerived := (input.mem_localizedOccurrences_iff fuel right.1).mp right.2
    have frameEq := input.declarativeLocalizedOccurrence_functional_at_root_address
      leftDerived rightDerived sameRoot sameAddress
    have occEq : left = right := Subtype.ext frameEq
    rw [occEq]
  · intro sameImage
    have imageRoot : (input.transportOccurrence singleBonded e left).1.root =
        (input.transportOccurrence singleBonded e right).1.root := by
      simp [transportOccurrence_root, sameRoot]
    have leftImage := (input.mem_localizedOccurrences_iff fuel
      (input.transportOccurrence singleBonded e left).1).mp
      (input.transportOccurrence singleBonded e left).2
    have rightImage := (input.mem_localizedOccurrences_iff fuel
      (input.transportOccurrence singleBonded e right).1).mp
      (input.transportOccurrence singleBonded e right).2
    have frameEq := input.declarativeLocalizedOccurrence_functional_at_root_address
      leftImage rightImage imageRoot sameImage
    have imageEq : input.transportOccurrence singleBonded e left =
        input.transportOccurrence singleBonded e right := Subtype.ext frameEq
    have sourceEq := congrArg (input.transportOccurrence singleBonded (e⁻¹)) imageEq
    have sourceId : left = right := by
      simpa [input.transportOccurrence_inv_apply singleBonded e left,
        input.transportOccurrence_inv_apply singleBonded e right] using sourceEq
    rw [sourceId]

private theorem mem_outward_transport_forward
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (parent child : input.LocalizedCIPOccurrence fuel)
    (present : child.1 ∈ input.localizedCarrierOutwardChildFrames (fuel := fuel) parent.1) :
    (input.transportOccurrence singleBonded e child).1 ∈
      input.localizedCarrierOutwardChildFrames (fuel := fuel)
        (input.transportOccurrence singleBonded e parent).1 := by
  rw [localizedCarrierOutwardChildFrames, List.mem_filter] at present
  simp only [Bool.and_eq_true, beq_iff_eq] at present
  have sameRoot : child.1.root = parent.1.root := present.2.1.1
  have lengthStep : child.1.address.length = parent.1.address.length + 1 := present.2.1.2
  have dropSource : child.1.address.dropLast = parent.1.address := present.2.2
  have hne : child.1.address ≠ [] := by
    intro hempty
    have : parent.1.address.length + 1 = 0 := by simpa [hempty] using lengthStep.symm
    omega
  let slot := child.1.address.getLast hne
  have haddr : child.1.address = parent.1.address ++ [slot] := by
    simpa [dropSource] using (List.dropLast_concat_getLast hne).symm
  have parentDerived := (input.mem_localizedOccurrences_iff fuel parent.1).mp parent.2
  have childDerived := (input.mem_localizedOccurrences_iff fuel child.1).mp child.2
  obtain ⟨execNode, slotMem, frameEq⟩ :=
    input.declarativeLocalizedOccurrence_immediate_child parentDerived childDerived sameRoot slot
      haddr
  have nodeEq : child.1.node = execNode :=
    congrArg LocalizedCIPOccurrenceFrame.node frameEq
  cases hdup : parent.1.node.isDuplicateLeaf with
  | true =>
      simp [executableOfficialCIPChildren, hdup] at slotMem
  | false =>
      have slotMem' : (execNode, slot) ∈
          ((input.executableOfficialChildCopies parent.1.node).map
            (fun copy => parent.1.node.extend copy.1 copy.2)).zipIdx := by
        simpa [executableOfficialCIPChildren, hdup] using slotMem
      rw [List.mk_mem_zipIdx_iff_getElem?, List.getElem?_map] at slotMem'
      cases hcopy : (input.executableOfficialChildCopies parent.1.node)[slot]? with
      | none => simp [hcopy] at slotMem'
      | some copy =>
          simp [hcopy] at slotMem'
          have copyMem := List.mem_of_getElem? hcopy
          have copyZero := input.executableOfficialChildCopy_index_zero singleBonded
            parent.1.node copy.1 copy.2 copyMem
          have extendEq : execNode = parent.1.node.extend copy.1 0 := by
            simpa [copyZero] using slotMem'.symm
          have prov := input.carrierOccurrence_provenance_simple_or_ring singleBonded parent
          rcases prov with real | ⟨_distance, ring⟩
          · have path := input.simpleOccurrencePath_of_carrier_real singleBonded parent real
            have dropImage := input.transportedAddress_extend_dropLast e path copy.1
            rw [localizedCarrierOutwardChildFrames, List.mem_filter]
            refine ⟨(input.transportOccurrence singleBonded e child).2, ?_⟩
            simp only [Bool.and_eq_true, beq_iff_eq]
            refine ⟨⟨?_, ?_⟩, ?_⟩
            · rw [transportOccurrence_root, transportOccurrence_root, sameRoot]
            · rw [input.transportOccurrence_address_length singleBonded e child,
                input.transportOccurrence_address_length singleBonded e parent, lengthStep]
            · rw [input.transportOccurrence_address singleBonded e child,
                input.transportOccurrence_address singleBonded e parent, sameRoot, nodeEq,
                extendEq]
              exact dropImage
          · have ringDup := input.isDuplicateLeaf_eq_true_of_ring_provenance parent.1.node ring
            simp [ringDup] at hdup

/-- Outward carrier step, preserved and reflected. The image address is recomputed. -/
theorem mem_localizedCarrierOutwardChildFrames_transport_iff
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (parent child : input.LocalizedCIPOccurrence fuel) :
    child.1 ∈ input.localizedCarrierOutwardChildFrames (fuel := fuel) parent.1 ↔
      (input.transportOccurrence singleBonded e child).1 ∈
        input.localizedCarrierOutwardChildFrames (fuel := fuel)
          (input.transportOccurrence singleBonded e parent).1 := by
  constructor
  · exact input.mem_outward_transport_forward singleBonded e parent child
  · intro present
    have back := input.mem_outward_transport_forward singleBonded (e⁻¹)
      (input.transportOccurrence singleBonded e parent)
      (input.transportOccurrence singleBonded e child) present
    have parentFrame : (input.transportOccurrence singleBonded (e⁻¹)
        (input.transportOccurrence singleBonded e parent)).1 = parent.1 := by
      rw [input.transportOccurrence_inv_apply singleBonded e parent]
    have childFrame : (input.transportOccurrence singleBonded (e⁻¹)
        (input.transportOccurrence singleBonded e child)).1 = child.1 := by
      rw [input.transportOccurrence_inv_apply singleBonded e child]
    rw [parentFrame, childFrame] at back
    exact back

/-- Carrier parent and outward child are the same address step, read from either end. -/
theorem mem_localizedCarrierParentFrames_iff_outward {fuel : Nat}
    (shorter longer : input.LocalizedCIPOccurrence fuel) :
    shorter.1 ∈ input.localizedCarrierParentFrames (fuel := fuel) longer.1 ↔
      longer.1 ∈ input.localizedCarrierOutwardChildFrames (fuel := fuel) shorter.1 := by
  constructor
  · intro present
    rw [localizedCarrierParentFrames, List.mem_filter] at present
    simp only [Bool.and_eq_true, beq_iff_eq] at present
    have sameRoot : shorter.1.root = longer.1.root := present.2.1.1
    have lengthStep : shorter.1.address.length + 1 = longer.1.address.length := present.2.1.2
    have dropSource : shorter.1.address = longer.1.address.dropLast := present.2.2
    rw [localizedCarrierOutwardChildFrames, List.mem_filter]
    refine ⟨longer.2, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨sameRoot.symm, lengthStep.symm⟩, dropSource.symm⟩
  · intro present
    rw [localizedCarrierOutwardChildFrames, List.mem_filter] at present
    simp only [Bool.and_eq_true, beq_iff_eq] at present
    have sameRoot : longer.1.root = shorter.1.root := present.2.1.1
    have lengthStep : longer.1.address.length = shorter.1.address.length + 1 := present.2.1.2
    have dropSource : longer.1.address.dropLast = shorter.1.address := present.2.2
    rw [localizedCarrierParentFrames, List.mem_filter]
    refine ⟨shorter.2, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨sameRoot.symm, lengthStep.symm⟩, dropSource.symm⟩

private theorem mem_parent_transport_forward
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (shorter longer : input.LocalizedCIPOccurrence fuel)
    (present : shorter.1 ∈ input.localizedCarrierParentFrames (fuel := fuel) longer.1) :
    (input.transportOccurrence singleBonded e shorter).1 ∈
      input.localizedCarrierParentFrames (fuel := fuel)
        (input.transportOccurrence singleBonded e longer).1 := by
  have swapped := (input.mem_localizedCarrierParentFrames_iff_outward shorter longer).mp present
  have image := (input.mem_localizedCarrierOutwardChildFrames_transport_iff singleBonded e
    shorter longer).mp swapped
  exact (input.mem_localizedCarrierParentFrames_iff_outward
    (input.transportOccurrence singleBonded e shorter)
    (input.transportOccurrence singleBonded e longer)).mpr image

/-- Rootward carrier step, preserved and reflected. -/
theorem mem_localizedCarrierParentFrames_transport_iff
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (shorter longer : input.LocalizedCIPOccurrence fuel) :
    shorter.1 ∈ input.localizedCarrierParentFrames (fuel := fuel) longer.1 ↔
      (input.transportOccurrence singleBonded e shorter).1 ∈
        input.localizedCarrierParentFrames (fuel := fuel)
          (input.transportOccurrence singleBonded e longer).1 := by
  constructor
  · exact input.mem_parent_transport_forward singleBonded e shorter longer
  · intro present
    have back := input.mem_parent_transport_forward singleBonded (e⁻¹)
      (input.transportOccurrence singleBonded e shorter)
      (input.transportOccurrence singleBonded e longer) present
    have shorterFrame : (input.transportOccurrence singleBonded (e⁻¹)
        (input.transportOccurrence singleBonded e shorter)).1 = shorter.1 := by
      rw [input.transportOccurrence_inv_apply singleBonded e shorter]
    have longerFrame : (input.transportOccurrence singleBonded (e⁻¹)
        (input.transportOccurrence singleBonded e longer)).1 = longer.1 := by
      rw [input.transportOccurrence_inv_apply singleBonded e longer]
    rw [shorterFrame, longerFrame] at back
    exact back

theorem mem_localizedRerootNeighborFrames_transport
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (source neighbor : input.LocalizedCIPOccurrence fuel)
    (present : neighbor.1 ∈ input.localizedRerootNeighborFrames (fuel := fuel) source.1) :
    (input.transportOccurrence singleBonded e neighbor).1 ∈
      input.localizedRerootNeighborFrames (fuel := fuel)
        (input.transportOccurrence singleBonded e source).1 := by
  rw [localizedRerootNeighborFrames, List.mem_append] at present ⊢
  rcases present with rootward | outward
  · exact Or.inl ((input.mem_localizedCarrierParentFrames_transport_iff singleBonded e
      neighbor source).mp rootward)
  · exact Or.inr ((input.mem_localizedCarrierOutwardChildFrames_transport_iff singleBonded e
      source neighbor).mp outward)

/-- `previous?` shares the cursor root, or there is no incoming occurrence.
Fresh cursors and executable children satisfy this. A foreign root does not: the cut filter
then compares raw addresses, which need not transport. -/
def cursorPreviousRootAligned {fuel : Nat} (cursor : input.LocalizedRerootCursor fuel) : Prop :=
  ∀ previous, cursor.previous? = some previous →
    previous.1.root = cursor.occurrence.1.root

theorem cursorPreviousRootAligned_of_none {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) (nonePrev : cursor.previous? = none) :
    input.cursorPreviousRootAligned cursor := by
  intro previous hprev
  simp [nonePrev] at hprev

theorem cursorPreviousRootAligned_transport
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    {cursor : input.LocalizedRerootCursor fuel}
    (aligned : input.cursorPreviousRootAligned cursor) :
    input.cursorPreviousRootAligned (input.transportCursor singleBonded e cursor) := by
  intro previous hprev
  rw [transportCursor_previous?] at hprev
  cases hsource : cursor.previous? with
  | none => simp [hsource] at hprev
  | some source =>
      simp [hsource] at hprev
      cases hprev
      have rootEq := aligned source hsource
      simp [transportCursor_occurrence, transportOccurrence_root, rootEq]

theorem mem_intendedLocalizedRerootChildFrames_iff {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) (frame : input.LocalizedCIPOccurrenceFrame) :
    frame ∈ input.intendedLocalizedRerootChildFrames cursor ↔
      cursor.occurrence.1.node.isDuplicateLeaf = false ∧
        frame ∈ input.localizedRerootNeighborFrames (fuel := fuel) cursor.occurrence.1 ∧
        ∀ previous, cursor.previous? = some previous → frame.address ≠ previous.1.address := by
  unfold intendedLocalizedRerootChildFrames
  cases hdup : cursor.occurrence.1.node.isDuplicateLeaf with
  | true =>
      constructor
      · intro present
        simp at present
      · intro kept
        simp at kept
  | false =>
      constructor
      · intro present
        cases hprev : cursor.previous? with
        | none =>
            refine ⟨rfl, ?_, ?_⟩
            · simpa [hprev] using present
            · intro prev hp
              simp at hp
        | some previous =>
            have filtered : frame ∈
                (input.localizedRerootNeighborFrames (fuel := fuel)
                  cursor.occurrence.1).filter
                  (fun item => item.address != previous.1.address) := by
              simpa [hprev] using present
            rw [List.mem_filter] at filtered
            refine ⟨rfl, filtered.1, ?_⟩
            intro prev hp
            have prevEq : previous = prev := Option.some_inj.mp hp
            rw [← prevEq]
            simpa [bne_iff_ne] using filtered.2
      · intro kept
        cases hprev : cursor.previous? with
        | none =>
            simpa [hprev] using kept.2.1
        | some previous =>
            have addrNe : frame.address ≠ previous.1.address := kept.2.2 previous hprev
            have filtered : frame ∈
                (input.localizedRerootNeighborFrames (fuel := fuel)
                  cursor.occurrence.1).filter
                  (fun item => item.address != previous.1.address) := by
              rw [List.mem_filter]
              refine ⟨kept.2.1, ?_⟩
              simpa [bne_iff_ne] using addrNe
            simpa [hprev] using filtered

theorem executableLocalizedRerootChildren_mem_iff {fuel : Nat}
    (cursor child : input.LocalizedRerootCursor fuel) :
    child ∈ input.executableLocalizedRerootChildren cursor ↔
      child.previous? = some cursor.occurrence ∧
        child.occurrence.1 ∈ input.intendedLocalizedRerootChildFrames cursor := by
  constructor
  · intro present
    refine ⟨input.executableLocalizedRerootChildren_previous cursor child present, ?_⟩
    have frameMem : child.occurrence.1 ∈
        (input.executableLocalizedRerootChildren cursor).map (fun item => item.occurrence.1) :=
      List.mem_map.mpr ⟨child, present, rfl⟩
    rw [input.executableLocalizedRerootChildren_map cursor] at frameMem
    exact frameMem
  · intro ⟨prevEq, framePresent⟩
    unfold executableLocalizedRerootChildren
    refine List.mem_map.mpr
      ⟨⟨child.occurrence.1, framePresent⟩, List.mem_attach _ _, ?_⟩
    apply LocalizedRerootCursor.ext input
    · apply Subtype.ext
      rfl
    · exact prevEq.symm

private theorem executableLocalizedRerootChildren_transport_mem_forward
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    {cursor : input.LocalizedRerootCursor fuel}
    (aligned : input.cursorPreviousRootAligned cursor)
    (child : input.LocalizedRerootCursor fuel)
    (present : child ∈ input.executableLocalizedRerootChildren cursor) :
    input.transportCursor singleBonded e child ∈
      input.executableLocalizedRerootChildren
        (input.transportCursor singleBonded e cursor) := by
  rw [input.executableLocalizedRerootChildren_mem_iff cursor child] at present
  rw [input.executableLocalizedRerootChildren_mem_iff
    (input.transportCursor singleBonded e cursor) (input.transportCursor singleBonded e child)]
  obtain ⟨prevEq, framePresent⟩ := present
  refine ⟨?_, ?_⟩
  · simp [transportCursor_previous?, transportCursor_occurrence, prevEq]
  · rw [input.mem_intendedLocalizedRerootChildFrames_iff] at framePresent ⊢
    obtain ⟨notDup, neighbor, kept⟩ := framePresent
    refine ⟨?_, ?_, ?_⟩
    · rw [transportCursor_occurrence, input.isDuplicateLeaf_transport singleBonded e
        cursor.occurrence, notDup]
    · exact input.mem_localizedRerootNeighborFrames_transport singleBonded e cursor.occurrence
        child.occurrence neighbor
    · intro imagePrevious himage
      rw [transportCursor_previous?] at himage
      cases hsource : cursor.previous? with
      | none => simp [hsource] at himage
      | some source =>
          simp [hsource] at himage
          cases himage
          have addrNe := kept source hsource
          have childRoot := input.localizedRerootNeighborFrames_root_eq cursor.occurrence.1
            child.occurrence.1 neighbor
          have sourceRoot := aligned source hsource
          have same : child.occurrence.1.root = source.1.root := by
            rw [childRoot, sourceRoot]
          exact (not_congr (input.transportOccurrence_address_eq_iff_of_sameRoot singleBonded e
            same)).mp addrNe

/-- Executable-child membership. Alignment is the zipper invariant, not a label hypothesis. -/
theorem executableLocalizedRerootChildren_transport_mem_iff
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    {cursor : input.LocalizedRerootCursor fuel}
    (aligned : input.cursorPreviousRootAligned cursor)
    (child : input.LocalizedRerootCursor fuel) :
    child ∈ input.executableLocalizedRerootChildren cursor ↔
      input.transportCursor singleBonded e child ∈
        input.executableLocalizedRerootChildren
          (input.transportCursor singleBonded e cursor) := by
  constructor
  · exact input.executableLocalizedRerootChildren_transport_mem_forward singleBonded e aligned
      child
  · intro present
    have alignedImage := input.cursorPreviousRootAligned_transport singleBonded e aligned
    have back := input.executableLocalizedRerootChildren_transport_mem_forward singleBonded (e⁻¹)
      alignedImage (input.transportCursor singleBonded e child) present
    simpa [input.transportCursor_inv_apply singleBonded e child,
      input.transportCursor_inv_apply singleBonded e cursor] using back

theorem executableLocalizedRerootChildren_cursorAligned {fuel : Nat}
    (cursor child : input.LocalizedRerootCursor fuel)
    (present : child ∈ input.executableLocalizedRerootChildren cursor) :
    input.cursorPreviousRootAligned child := by
  intro previous hprev
  have prevEq := input.executableLocalizedRerootChildren_previous cursor child present
  rw [prevEq] at hprev
  cases hprev
  have derived := input.executableLocalizedRerootChildren_declarative cursor
  exact (input.localizedRerootChildren_root_eq cursor child
    (input.executableLocalizedRerootChildren cursor) derived present).symm

theorem executableLocalizedRerootChildren_transport_mem_iff_of_none
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) (nonePrev : cursor.previous? = none)
    (child : input.LocalizedRerootCursor fuel) :
    child ∈ input.executableLocalizedRerootChildren cursor ↔
      input.transportCursor singleBonded e child ∈
        input.executableLocalizedRerootChildren
          (input.transportCursor singleBonded e cursor) :=
  input.executableLocalizedRerootChildren_transport_mem_iff singleBonded e
    (input.cursorPreviousRootAligned_of_none cursor nonePrev) child

theorem executableLocalizedRerootChildren_transport_mem_iff_of_child
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (parent cursor child : input.LocalizedRerootCursor fuel)
    (parentPresent : cursor ∈ input.executableLocalizedRerootChildren parent) :
    child ∈ input.executableLocalizedRerootChildren cursor ↔
      input.transportCursor singleBonded e child ∈
        input.executableLocalizedRerootChildren
          (input.transportCursor singleBonded e cursor) :=
  input.executableLocalizedRerootChildren_transport_mem_iff singleBonded e
    (input.executableLocalizedRerootChildren_cursorAligned parent cursor parentPresent) child

/-- Child-list permutation. Nodup of both executable lists and injectivity of transport.
Not equality of atom-index slot numbers. -/
theorem executableLocalizedRerootChildren_transport_perm
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    {cursor : input.LocalizedRerootCursor fuel}
    (aligned : input.cursorPreviousRootAligned cursor) :
    List.Perm
      ((input.executableLocalizedRerootChildren cursor).map
        (input.transportCursor singleBonded e))
      (input.executableLocalizedRerootChildren
        (input.transportCursor singleBonded e cursor)) := by
  have mapNodup : ((input.executableLocalizedRerootChildren cursor).map
      (input.transportCursor singleBonded e)).Nodup :=
    List.Nodup.map (input.transportCursor_injective singleBonded e fuel)
      (input.executableLocalizedRerootChildren_nodup cursor)
  have imageNodup := input.executableLocalizedRerootChildren_nodup
    (input.transportCursor singleBonded e cursor)
  apply (List.perm_ext_iff_of_nodup mapNodup imageNodup).2
  intro item
  constructor
  · intro hitem
    rcases List.mem_map.1 hitem with ⟨source, sourcePresent, rfl⟩
    exact (input.executableLocalizedRerootChildren_transport_mem_iff singleBonded e aligned
      source).1 sourcePresent
  · intro hitem
    have round := input.transportCursor_apply_inv singleBonded e item
    have preimagePresent : input.transportCursor singleBonded (e⁻¹) item ∈
        input.executableLocalizedRerootChildren cursor := by
      apply (input.executableLocalizedRerootChildren_transport_mem_iff singleBonded e aligned
        (input.transportCursor singleBonded (e⁻¹) item)).2
      simpa [round] using hitem
    exact List.mem_map.2 ⟨input.transportCursor singleBonded (e⁻¹) item, preimagePresent, round⟩

theorem executableLocalizedRerootChildren_rootward_or_outward {fuel : Nat}
    (cursor child : input.LocalizedRerootCursor fuel)
    (present : child ∈ input.executableLocalizedRerootChildren cursor) :
    child.previous? = some cursor.occurrence ∧
      (child.occurrence.1 ∈ input.localizedCarrierParentFrames (fuel := fuel)
          cursor.occurrence.1 ∨
        child.occurrence.1 ∈ input.localizedCarrierOutwardChildFrames (fuel := fuel)
          cursor.occurrence.1) := by
  have unpacked := (input.executableLocalizedRerootChildren_mem_iff cursor child).1 present
  have intended := (input.mem_intendedLocalizedRerootChildFrames_iff cursor
    child.occurrence.1).1 unpacked.2
  rw [localizedRerootNeighborFrames, List.mem_append] at intended
  exact ⟨unpacked.1, intended.2.1⟩

/-- Image executable child, with the previous cut and the rootward or outward step. -/
theorem executableLocalizedRerootChildren_transport_cut
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    {cursor : input.LocalizedRerootCursor fuel}
    (aligned : input.cursorPreviousRootAligned cursor)
    (child : input.LocalizedRerootCursor fuel)
    (present : child ∈ input.executableLocalizedRerootChildren cursor) :
    input.transportCursor singleBonded e child ∈
        input.executableLocalizedRerootChildren
          (input.transportCursor singleBonded e cursor) ∧
      (input.transportCursor singleBonded e child).previous? =
        some (input.transportCursor singleBonded e cursor).occurrence ∧
      ((input.transportCursor singleBonded e child).occurrence.1 ∈
          input.localizedCarrierParentFrames (fuel := fuel)
            (input.transportCursor singleBonded e cursor).occurrence.1 ∨
        (input.transportCursor singleBonded e child).occurrence.1 ∈
          input.localizedCarrierOutwardChildFrames (fuel := fuel)
            (input.transportCursor singleBonded e cursor).occurrence.1) := by
  have imagePresent := (input.executableLocalizedRerootChildren_transport_mem_iff singleBonded e
    aligned child).1 present
  have direction := input.executableLocalizedRerootChildren_rootward_or_outward
    (input.transportCursor singleBonded e cursor)
    (input.transportCursor singleBonded e child) imagePresent
  exact ⟨imagePresent, direction.1, direction.2⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportedAddress_symm_apply
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportOccurrence_inv_apply
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportOccurrence_apply_inv
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportCursor_inv_apply
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportCursor_apply_inv
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportCursor_injective
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.isDuplicateLeaf_transport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableOfficialChildCopy_index_zero
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportOccurrence_address_eq_iff_of_sameRoot
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_localizedCarrierOutwardChildFrames_transport_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_localizedCarrierParentFrames_iff_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_localizedCarrierParentFrames_transport_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_localizedRerootNeighborFrames_transport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.cursorPreviousRootAligned_of_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.cursorPreviousRootAligned_transport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_intendedLocalizedRerootChildFrames_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableLocalizedRerootChildren_mem_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableLocalizedRerootChildren_transport_mem_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableLocalizedRerootChildren_cursorAligned
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableLocalizedRerootChildren_transport_mem_iff_of_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableLocalizedRerootChildren_transport_mem_iff_of_child
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableLocalizedRerootChildren_transport_perm
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableLocalizedRerootChildren_rootward_or_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableLocalizedRerootChildren_transport_cut
