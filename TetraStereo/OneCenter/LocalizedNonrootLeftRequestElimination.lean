import TetraStereo.OneCenter.LocalizedUnbranchedRule3RequestPhase
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Elimination of left-endpoint requests at a nonroot carrier parent

Let `O` be an actual physical endpoint occurrence of an open even axis and let `initial` be the
physical endpoint cursor frame declared at `O`.  Write `P := initial.leftCursor.occurrence` for the
carrier parent of `O`.  This module proves that whenever `P` is nonroot, the left-endpoint request
list

`input.rule3ShortEndpointCallbackRequests initial.left initial.right initial.leftCursor`

is literally empty, with no terminality, double-bond branching, or global unbranchedness
hypothesis.

The mathematical content is a carrier-parent exclusion.  The two explicit Rule-3 substituents of
`initial.left` are the graph neighbours of `initial.left` other than `initial.right`.  If `P` is
the actual carrier parent of `O`, then the carrier parent `Q` of `P` is adjacent to
`initial.left` and distinct from `initial.right`, hence one of the two explicit substituents.

Every emitted left-endpoint request has both selected reference cursors outward of `P`
(`rule3ShortEndpointCallbackRequests_left_outward`), so each selected cursor is a genuine child of
`P` at the address `P.address ++ [slot]` with physical (real or ring-duplicate) provenance.  If the
substituent `Q` is the first (or second) one, the corresponding selected cursor carries the atom
`Q` at such an outward physical child.  The immediate-child representation and
`eq_extend_zero_and_not_parent_of_mem_executableOfficialCIPChildren` then force

`P.node.parent? ≠ some Q`,

while the actual parent-frame certificate of `P` gives `P.node.parent? = some Q` from its stored
branch history.  This is a direct contradiction, so no request can be emitted.  No lookup totality
or ancestor-selection premise is used anywhere.

## Exports

* `physicalProvenance_dichotomy` -- a physical provenance is real or ring-duplicate.
* `referenceCursor_address_dropLast_of_carrierParent` -- actual recovery of the carrier-parent
  reference coordinate from the canonical physical reference lookup.
* `rule3ShortEndpointCallbackRequests_eq_nil_of_neighbor_card_ne_three` -- shape refusal: no
  request is emitted when the left endpoint does not have exactly three physical neighbours.
* `rule3ShortEndpointCallbackRequests_eq_nil_of_nonroot` -- the main nonroot elimination.
* `rule3ShortSpatialCallbackRequests_eq_right_of_nonroot` -- the same fact read on the actual
  spatial request list.
* `rule3ShortOddCallbackRequests_eq_right_of_nonroot` -- the odd cumulene route.
* `rule3ActualRequest_rightEndpoint_and_outward` -- the target-rooted package at the original
  descriptor target `T`.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-- A node provenance that counts as a physical reference position is either the real atom
provenance or a ring-duplicate provenance. -/
theorem physicalProvenance_dichotomy
    (input : CertifiedLocalizedCIPInput) {provenance : OfficialCIPNodeProvenance}
    (physical : LocalizedRule3PhysicalReferenceProvenance provenance) :
    provenance = OfficialCIPNodeProvenance.realAtom ∨
      ∃ distance, provenance = OfficialCIPNodeProvenance.ringDuplicate distance := by
  cases provenance <;> simp [LocalizedRule3PhysicalReferenceProvenance] at physical
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

/-- **Nonroot left-endpoint request elimination.**

Let `O` be an actual physical endpoint occurrence, `initial` its declared physical endpoint cursor
frame, and `P := initial.leftCursor.occurrence` its carrier parent.  If `P` has a nonempty carrier
address, then the left-endpoint request list at `P` is empty.

No terminality, double-bond branching, or global unbranchedness hypothesis is used.  The only
inputs are the actual frame declaration and the nonroot address of `P`. -/
theorem rule3ShortEndpointCallbackRequests_eq_nil_of_nonroot
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O initial)
    (nonroot : initial.leftCursor.occurrence.1.address ≠ []) :
    input.rule3ShortEndpointCallbackRequests initial.left initial.right initial.leftCursor = [] := by
  let certificate := input.localizedParentFrameHistory initial.leftCursor.occurrence nonroot
  have PActive : initial.leftCursor.occurrence.1.node.ActiveSimple :=
    input.carrierParent_active_of_frame O initial frameDecl
  rcases frameDecl with
    ⟨OReal, OCurrent, OParent, OBond, OParentMem, PCurrent, PPrevious, ROcc, RPrev⟩
  have parentFacts := input.localizedCarrierParentFrame_facts O.1
    initial.leftCursor.occurrence.1 OParentMem
  -- The carrier parent `Q` of `P` is the second head of the stored history of `P`.
  obtain ⟨_Pcurrent, Qatom, _tail, _PcurrentEq, QatomEq, PhistoryEq, _QhistoryEq⟩ :=
    certificate.history_shape input
  have QParent : initial.leftCursor.occurrence.1.node.parent? = some Qatom := by
    unfold OfficialCIPNode.parent?
    rw [PhistoryEq]
  -- `O` sits one carrier step below `P`, at the address `P.address ++ [slotO]`.
  have ONonempty : O.1.address ≠ [] := by
    intro empty
    have lengthO : initial.leftCursor.occurrence.1.address.length + 1 = 0 := by
      simpa [empty] using parentFacts.2.1
    omega
  set slotO : Nat := O.1.address.getLast ONonempty with slotODef
  have OAddress : O.1.address = initial.leftCursor.occurrence.1.address ++ [slotO] := by
    rw [parentFacts.2.2]
    exact (List.dropLast_append_getLast ONonempty).symm
  have ODerived : input.DeclarativeLocalizedOccurrence carrierFuel O.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel O.1).mp O.2
  have PDerived : input.DeclarativeLocalizedOccurrence carrierFuel
      initial.leftCursor.occurrence.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel
      initial.leftCursor.occurrence.1).mp initial.leftCursor.occurrence.2
  obtain ⟨ONode, OAtSlot, OFrame⟩ :=
    input.declarativeLocalizedOccurrence_immediate_child PDerived ODerived
      parentFacts.1.symm slotO OAddress
  have ONodeEq : O.1.node = ONode := by
    simpa using congrArg LocalizedCIPOccurrenceFrame.node OFrame
  have ONodePresent : O.1.node ∈
      input.executableOfficialCIPChildren initial.leftCursor.occurrence.1.node := by
    rw [ONodeEq]
    exact List.fst_mem_of_mem_zipIdx OAtSlot
  -- The physical child `O` of `P` excludes its own atom as the stored parent atom of `P`.
  obtain ⟨ONext, OExtend, ONotParent⟩ :=
    input.eq_extend_zero_and_not_parent_of_mem_executableOfficialCIPChildren
      initial.leftCursor.occurrence.1.node O.1.node
      ONodePresent (Or.inl OReal)
  have ONextEq : ONext = initial.right := by
    have observed : some ONext = some initial.right := by
      rw [← OfficialCIPNode.extend_current?
        initial.leftCursor.occurrence.1.node ONext 0, ← OExtend, OCurrent]
    exact Option.some.inj observed
  have notParentRight : initial.leftCursor.occurrence.1.node.parent? ≠ some initial.right := by
    intro sameRight
    apply ONotParent
    rw [sameRight, ONextEq]
  have QatomNeRight : Qatom ≠ initial.right := by
    intro same
    exact notParentRight (by rw [QParent, same])
  -- `P` is an immediate child of `Q` in the occurrence carrier, so `Q` is adjacent to `P`.
  set slotP : Nat := initial.leftCursor.occurrence.1.address.getLast nonroot with slotPDef
  have childAddressP : initial.leftCursor.occurrence.1.address =
      certificate.parent.1.address ++ [slotP] := by
    rw [certificate.parent_address]
    exact (List.dropLast_append_getLast nonroot).symm
  have QDerived : input.DeclarativeLocalizedOccurrence carrierFuel certificate.parent.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel certificate.parent.1).mp certificate.parent.2
  obtain ⟨PNode, PAtSlot, PFrame⟩ :=
    input.declarativeLocalizedOccurrence_immediate_child QDerived PDerived
      certificate.parent_root.symm slotP childAddressP
  have PNodeEq : initial.leftCursor.occurrence.1.node = PNode := by
    simpa using congrArg LocalizedCIPOccurrenceFrame.node PFrame
  have PNodePresent : initial.leftCursor.occurrence.1.node ∈
      input.executableOfficialCIPChildren certificate.parent.1.node := by
    rw [PNodeEq]
    exact List.fst_mem_of_mem_zipIdx PAtSlot
  have adjQP : input.moleculeGraph.Adj Qatom initial.left :=
    input.adj_of_mem_executableOfficialCIPChildren certificate.parent.1.node
      initial.leftCursor.occurrence.1.node Qatom initial.left QatomEq PCurrent PNodePresent
  have adjPQ : input.moleculeGraph.Adj initial.left Qatom := by
    unfold MoleculeGraph.Adj at adjQP ⊢
    rw [input.moleculeGraph.bond_symm]
    exact adjQP
  -- Read the emission gate structurally.
  cases hrequests : input.rule3ShortEndpointCallbackRequests
      initial.left initial.right initial.leftCursor with
  | nil => rfl
  | cons head tail =>
    exfalso
    have member : head ∈ input.rule3ShortEndpointCallbackRequests
        initial.left initial.right initial.leftCursor := by
      rw [hrequests]
      simp
    obtain ⟨first, second, firstCursor, secondCursor, subs, firstSel, secondSel,
      _rootCmp, _constCmp, requestEq⟩ :=
      input.rule3ShortEndpointCallbackRequests_structure initial.left initial.right
        initial.leftCursor head member
    have qMem : Qatom ∈ input.localizedRule3ExplicitSubstituents initial.left initial.right :=
      (input.mem_localizedRule3ExplicitSubstituents_iff initial.left initial.right Qatom).mpr
        ⟨adjPQ, QatomNeRight⟩
    have qCase : Qatom = first ∨ Qatom = second := by
      rw [subs] at qMem
      simpa using qMem
    -- Every emitted cursor is outward of `P` itself.
    have outward := input.rule3ShortEndpointCallbackRequests_left_outward
      initial.leftCursor.occurrence initial.leftCursor initial.left initial.right
      rfl (Nat.le_refl _) PActive head member
    have firstMem : firstCursor ∈ head := by
      rw [requestEq]
      simp
    have secondMem : secondCursor ∈ head := by
      rw [requestEq]
      simp
    have firstOutward : OutwardRerootCursor input initial.leftCursor.occurrence firstCursor :=
      outward firstCursor firstMem
    have secondOutward : OutwardRerootCursor input initial.leftCursor.occurrence secondCursor :=
      outward secondCursor secondMem
    obtain ⟨_firstChild, _firstPrevious, firstCurrent, firstPhysical⟩ :=
      input.localizedRule3ReferenceCursorExec?_facts initial.leftCursor firstCursor first firstSel
    obtain ⟨_secondChild, _secondPrevious, secondCurrent, secondPhysical⟩ :=
      input.localizedRule3ReferenceCursorExec?_facts initial.leftCursor secondCursor second secondSel
    rcases qCase with qFirst | qSecond
    · -- The first selected cursor carries the carrier-parent atom `Q`.
      have firstCurrentQ : firstCursor.occurrence.1.node.current? = some Qatom := by
        rw [firstCurrent, qFirst]
      have firstAddressOutward : ∃ slot,
          firstCursor.occurrence.1.address =
            initial.leftCursor.occurrence.1.address ++ [slot] := by
        rcases input.executableLocalizedRerootChild_dichotomy initial.leftCursor
            firstCursor _firstChild with
          ⟨parentLength, _parentAddress⟩ | ⟨slot, slotAddress⟩
        · exfalso
          have firstDeeper : initial.leftCursor.occurrence.1.address.length <
              firstCursor.occurrence.1.address.length := firstOutward.2.1.2
          omega
        · exact ⟨slot, slotAddress⟩
      obtain ⟨slot, slotAddress⟩ := firstAddressOutward
      obtain ⟨firstNode, firstAtSlot, firstFrame⟩ :=
        input.declarativeLocalizedOccurrence_immediate_child PDerived
          ((input.mem_localizedOccurrences_iff carrierFuel
            firstCursor.occurrence.1).mp firstCursor.occurrence.2)
          firstOutward.2.1.1 slot slotAddress
      have firstNodeEq : firstCursor.occurrence.1.node = firstNode := by
        simpa using congrArg LocalizedCIPOccurrenceFrame.node firstFrame
      have firstNodePresent : firstCursor.occurrence.1.node ∈
          input.executableOfficialCIPChildren initial.leftCursor.occurrence.1.node := by
        rw [firstNodeEq]
        exact List.fst_mem_of_mem_zipIdx firstAtSlot
      obtain ⟨next, nextEq, notParent⟩ :=
        input.eq_extend_zero_and_not_parent_of_mem_executableOfficialCIPChildren
          initial.leftCursor.occurrence.1.node firstCursor.occurrence.1.node
          firstNodePresent (input.physicalProvenance_dichotomy firstPhysical)
      have nextEqQ : next = Qatom := by
        have observed : some next = some Qatom := by
          rw [← OfficialCIPNode.extend_current?
            initial.leftCursor.occurrence.1.node next 0, ← nextEq, firstCurrentQ]
        exact Option.some.inj observed
      exact notParent (by rw [nextEqQ]; exact QParent)
    · -- The second selected cursor carries the carrier-parent atom `Q`.
      have secondCurrentQ : secondCursor.occurrence.1.node.current? = some Qatom := by
        rw [secondCurrent, qSecond]
      have secondAddressOutward : ∃ slot,
          secondCursor.occurrence.1.address =
            initial.leftCursor.occurrence.1.address ++ [slot] := by
        rcases input.executableLocalizedRerootChild_dichotomy initial.leftCursor
            secondCursor _secondChild with
          ⟨parentLength, _parentAddress⟩ | ⟨slot, slotAddress⟩
        · exfalso
          have secondDeeper : initial.leftCursor.occurrence.1.address.length <
              secondCursor.occurrence.1.address.length := secondOutward.2.1.2
          omega
        · exact ⟨slot, slotAddress⟩
      obtain ⟨slot, slotAddress⟩ := secondAddressOutward
      obtain ⟨secondNode, secondAtSlot, secondFrame⟩ :=
        input.declarativeLocalizedOccurrence_immediate_child PDerived
          ((input.mem_localizedOccurrences_iff carrierFuel
            secondCursor.occurrence.1).mp secondCursor.occurrence.2)
          secondOutward.2.1.1 slot slotAddress
      have secondNodeEq : secondCursor.occurrence.1.node = secondNode := by
        simpa using congrArg LocalizedCIPOccurrenceFrame.node secondFrame
      have secondNodePresent : secondCursor.occurrence.1.node ∈
          input.executableOfficialCIPChildren initial.leftCursor.occurrence.1.node := by
        rw [secondNodeEq]
        exact List.fst_mem_of_mem_zipIdx secondAtSlot
      obtain ⟨next, nextEq, notParent⟩ :=
        input.eq_extend_zero_and_not_parent_of_mem_executableOfficialCIPChildren
          initial.leftCursor.occurrence.1.node secondCursor.occurrence.1.node
          secondNodePresent (input.physicalProvenance_dichotomy secondPhysical)
      have nextEqQ : next = Qatom := by
        have observed : some next = some Qatom := by
          rw [← OfficialCIPNode.extend_current?
            initial.leftCursor.occurrence.1.node next 0, ← nextEq, secondCurrentQ]
        exact Option.some.inj observed
      exact notParent (by rw [nextEqQ]; exact QParent)

/-- **Spatial route: only the right endpoint can emit requests.**  For the frame actually
recovered by the physical endpoint cursor recovery on `O`, the actual spatial request list is
exactly the right-endpoint request list. -/
theorem rule3ShortSpatialCallbackRequests_eq_right_of_nonroot
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec? O = some frame)
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O frame)
    (nonroot : frame.leftCursor.occurrence.1.address ≠ []) :
    input.rule3ShortSpatialCallbackRequests O =
      input.rule3ShortEndpointCallbackRequests frame.right frame.left frame.rightCursor := by
  unfold rule3ShortSpatialCallbackRequests
  rw [computed]
  simp [rule3ShortEndpointCallbackRequests_eq_nil_of_nonroot input O frame frameDecl nonroot]

/-- **Odd cumulene route: only the right endpoint can emit requests.**  When the odd cumulene
endpoint frame is recovered, the left-endpoint requests of its initial frame vanish and the odd
request list is exactly the right-endpoint request list. -/
theorem rule3ShortOddCallbackRequests_eq_right_of_nonroot
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) O = some topology)
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O topology.initial)
    (nonroot : topology.initial.leftCursor.occurrence.1.address ≠ []) :
    input.rule3ShortOddCallbackRequests O =
      input.rule3ShortEndpointCallbackRequests topology.right topology.rightPartner
        topology.rightCursor := by
  unfold rule3ShortOddCallbackRequests
  rw [computed]
  simp [rule3ShortEndpointCallbackRequests_eq_nil_of_nonroot input O topology.initial frameDecl nonroot]

/-- **Target-rooted original request package.**  Let `T` be an original descriptor target strictly
shallower than the physical endpoint occurrence `O`.  For the frame actually recovered at `O`, if
its carrier parent is nonroot then the actual spatial request list is exactly the right-endpoint
list, and every cursor in every actually emitted request is an outward cursor of the original
target `T`. -/
theorem rule3ActualRequest_rightEndpoint_and_outward
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O T : input.LocalizedCIPOccurrence carrierFuel)
    (deeper : input.LocalizedDepthDependency O T)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3PhysicalEndpointCursorFrameExec? O = some frame)
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O frame)
    (nonroot : frame.leftCursor.occurrence.1.address ≠ []) :
    input.rule3ShortSpatialCallbackRequests O =
        input.rule3ShortEndpointCallbackRequests frame.right frame.left frame.rightCursor ∧
      (∀ request ∈ input.rule3ShortSpatialCallbackRequests O,
        ∀ cursor ∈ request, OutwardRerootCursor input T cursor) :=
  ⟨rule3ShortSpatialCallbackRequests_eq_right_of_nonroot input O frame computed frameDecl nonroot,
    input.rule3ActualRequest_outward O T deeper⟩

/-- **Recovery of the carrier-parent reference cursor.**

Let `start` be an actual reroot cursor with active-simple occurrence, and let
`certificate : LocalizedParentFrameHistory start.occurrence` be the actual parent-frame
certificate of the starting occurrence.  Suppose the incoming cut of `start` is an occurrence
`previous` whose address differs from the certificate parent's address.  Then the canonical
physical reference lookup at the certificate parent's current atom, when it succeeds, returns
exactly the carrier-parent coordinate `start.occurrence.address.dropLast`.

The proof does not assume that the lookup selects the ancestor.  It exhibits the ancestor cursor
`⟨certificate.parent, some start.occurrence⟩` as an actual executable child of `start`: the
occurrence is a genuine carrier neighbour, the duplicate-leaf guard is disabled by
`ActiveSimple`, and the cut filter keeps it because its address differs from the incoming cut.
Physical-reference uniqueness then forces the selected cursor to be that ancestor. -/
theorem referenceCursor_address_dropLast_of_carrierParent
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (start : input.LocalizedRerootCursor fuel)
    (certificate : input.LocalizedParentFrameHistory start.occurrence)
    (previous : input.LocalizedCIPOccurrence fuel)
    (previousEq : start.previous? = some previous)
    (previousAddressNe : certificate.parent.1.address ≠ previous.1.address)
    (startActive : start.occurrence.1.node.ActiveSimple)
    (reference : input.Atom)
    (referenceEq : certificate.parent.1.node.current? = some reference)
    (selected : input.LocalizedRerootCursor fuel)
    (selectedOk : input.localizedRule3ReferenceCursorExec? start reference = some selected) :
    selected.occurrence.1.address = start.occurrence.1.address.dropLast := by
  obtain ⟨selectedPresent, _selectedPrevious, selectedCurrent, selectedPhysical⟩ :=
    input.localizedRule3ReferenceCursorExec?_facts start selected reference selectedOk
  have notDuplicate : ¬ (start.occurrence.1.node.isDuplicateLeaf = true) := by
    simp [OfficialCIPNode.isDuplicateLeaf, startActive.1]
  have ancestorIntended : certificate.parent.1 ∈
      input.intendedLocalizedRerootChildFrames start := by
    unfold intendedLocalizedRerootChildFrames
    rw [if_neg notDuplicate]
    cases previousCase : start.previous? with
    | none =>
        rw [previousEq] at previousCase
        simp at previousCase
    | some found =>
        have foundEq : found = previous := by
          rw [previousEq] at previousCase
          exact (Option.some.inj previousCase).symm
        subst found
        rw [List.mem_filter]
        exact ⟨certificate.parent_mem_neighborFrames input,
          by simpa using previousAddressNe⟩
  have ancestorMapped : certificate.parent.1 ∈
      (input.executableLocalizedRerootChildren start).map
        (fun child => child.occurrence.1) := by
    rw [input.executableLocalizedRerootChildren_map start]
    exact ancestorIntended
  obtain ⟨ancestor, ancestorPresent, ancestorOccurrence⟩ := List.mem_map.mp ancestorMapped
  have ancestorEq : ancestor =
      { occurrence := certificate.parent, previous? := some start.occurrence } :=
    LocalizedRerootCursor.ext input (Subtype.ext ancestorOccurrence)
      (by rw [input.executableLocalizedRerootChildren_previous start ancestor ancestorPresent])
  have ancestorCurrent : ancestor.occurrence.1.node.current? = some reference := by
    rw [ancestorOccurrence]
    exact referenceEq
  have ancestorPhysical : LocalizedRule3PhysicalReferenceProvenance
      ancestor.occurrence.1.node.provenance := by
    rw [ancestorOccurrence, certificate.parent_provenance input]
    simp [LocalizedRule3PhysicalReferenceProvenance]
  have selectedEq : selected = ancestor :=
    input.localizedRule3PhysicalReferenceCursor_unique start selected ancestor reference
      (input.executableLocalizedRerootChildren start)
      (input.executableLocalizedRerootChildren_declarative start)
      selectedPresent ancestorPresent selectedCurrent ancestorCurrent
      selectedPhysical ancestorPhysical
  calc
    selected.occurrence.1.address = ancestor.occurrence.1.address := by rw [selectedEq]
    _ = certificate.parent.1.address := by rw [ancestorOccurrence]
    _ = start.occurrence.1.address.dropLast := certificate.parent_address

/-- **Neighbour-cardinality shape refusal.**  If the physical neighbour count of the left
endpoint is not three, then the two explicit Rule-3 substituents cannot exist, so the request
list is empty.  At a root carrier parent this is the root shape refusal: only a root with exactly
three physical neighbours can even reach the emission gate. -/
theorem rule3ShortEndpointCallbackRequests_eq_nil_of_neighbor_card_ne_three
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O initial)
    (cardNe : (input.moleculeGraph.neighborFinset initial.left).card ≠ 3) :
    input.rule3ShortEndpointCallbackRequests initial.left initial.right initial.leftCursor = [] := by
  rcases frameDecl with
    ⟨_OReal, _OCurrent, _OParent, OBond, _OParentMem, _PCurrent, _PPrevious, _ROcc, _RPrev⟩
  have partnerMem : initial.right ∈ input.moleculeGraph.neighborFinset initial.left := by
    rw [input.moleculeGraph.mem_neighborFinset]
    unfold MoleculeGraph.Adj
    rw [OBond]
    exact Nat.zero_lt_two
  cases hsubs : input.localizedRule3ExplicitSubstituents initial.left initial.right with
  | nil => simp [rule3ShortEndpointCallbackRequests, hsubs]
  | cons first rest =>
    cases rest with
    | nil => simp [rule3ShortEndpointCallbackRequests, hsubs]
    | cons second rest' =>
      cases rest' with
      | cons third rest'' => simp [rule3ShortEndpointCallbackRequests, hsubs]
      | nil =>
        exfalso
        have lengthTwo :
            (input.localizedRule3ExplicitSubstituents initial.left initial.right).length = 2 := by
          rw [hsubs]
          rfl
        have sortCard : ((input.moleculeGraph.neighborFinset initial.left).erase
            initial.right).card = 2 := by
          have lengthEq : (((input.moleculeGraph.neighborFinset initial.left).erase
              initial.right).sort (· ≤ ·)).length = 2 := by
            simpa [localizedRule3ExplicitSubstituents] using lengthTwo
          rw [Finset.length_sort] at lengthEq
          exact lengthEq
        have cardEq : (input.moleculeGraph.neighborFinset initial.left).card = 3 := by
          have eraseAdd := Finset.card_erase_add_one partnerMem
          rw [sortCard] at eraseAdd
          exact eraseAdd.symm
        exact cardNe cardEq

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.physicalProvenance_dichotomy
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.referenceCursor_address_dropLast_of_carrierParent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortEndpointCallbackRequests_eq_nil_of_neighbor_card_ne_three
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortEndpointCallbackRequests_eq_nil_of_nonroot
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortSpatialCallbackRequests_eq_right_of_nonroot
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortOddCallbackRequests_eq_right_of_nonroot
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ActualRequest_rightEndpoint_and_outward

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
