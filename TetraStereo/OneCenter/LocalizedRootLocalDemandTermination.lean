import TetraStereo.OneCenter.LocalizedUnbranchedActualDemandTermination
import TetraStereo.OneCenter.LocalizedUnbranchedRule3RequestPhase
import TetraStereo.OneCenter.LocalizedUnbranchedExtendedDemandTotality
import TetraStereo.OneCenter.LocalizedNonrootLeftRequestElimination
import TetraStereo.OneCenter.LocalizedTetrahedralRootDoubleBondBound
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

open TetraStereo.Certificate.WeightedDemand

































/-! ## The root-local order-two bound -/

/-- **Root-local order-two bound.**  At the original carrier root atom only, at most two distinct
order-two neighbours.  This is an input-graph fact at one atom.  It deliberately says nothing about
interior atoms, which may be internally branched and hypervalent. -/
def LocalizedRootLocalDoubleBondBound (input : CertifiedLocalizedCIPInput)
    (root : input.Atom) : Prop :=
  (input.localizedOrderTwoNeighbors root).length ≤ 2

/-- **Three-neighbour elimination at a bounded atom.**  At an atom with at most two distinct
order-two neighbours, three atoms doubly bonded to it cannot be pairwise distinct.  This is the
pointwise form of `eq_of_three_doubleBond_neighbors`. -/
theorem eq_of_three_doubleBond_neighbors_of_rootBound
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (bound : (input.localizedOrderTwoNeighbors center).length ≤ 2)
    (first second third : input.Atom)
    (firstBond : input.moleculeGraph.bond center first = 2)
    (secondBond : input.moleculeGraph.bond center second = 2)
    (thirdBond : input.moleculeGraph.bond center third = 2) :
    first = second ∨ first = third ∨ second = third := by
  by_contra distinct
  push_neg at distinct
  obtain ⟨firstNeSecond, firstNeThird, secondNeThird⟩ := distinct
  have nodup := input.localizedOrderTwoNeighbors_nodup center
  have firstMem : first ∈ (input.localizedOrderTwoNeighbors center).toFinset :=
    List.mem_toFinset.mpr
      ((input.mem_localizedOrderTwoNeighbors_iff center first).mpr firstBond)
  have secondMem : second ∈ (input.localizedOrderTwoNeighbors center).toFinset :=
    List.mem_toFinset.mpr
      ((input.mem_localizedOrderTwoNeighbors_iff center second).mpr secondBond)
  have thirdMem : third ∈ (input.localizedOrderTwoNeighbors center).toFinset :=
    List.mem_toFinset.mpr
      ((input.mem_localizedOrderTwoNeighbors_iff center third).mpr thirdBond)
  have subset : ({first, second, third} : Finset input.Atom) ⊆
      (input.localizedOrderTwoNeighbors center).toFinset := by
    intro atom member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with same | same | same
    · simpa [same] using firstMem
    · simpa [same] using secondMem
    · simpa [same] using thirdMem
  have cardLe := Finset.card_le_card subset
  have cardThree : ({first, second, third} : Finset input.Atom).card = 3 := by
    simp [Finset.card_insert_of_notMem, firstNeSecond, firstNeThird, secondNeThird]
  have listCard : (input.localizedOrderTwoNeighbors center).toFinset.card =
      (input.localizedOrderTwoNeighbors center).length :=
    List.toFinset_card_of_nodup nodup
  omega

/-! ## Direct numeric rank inequalities -/










theorem extendedDemandRank_request_of_budget_le
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {cursor reference : input.LocalizedRerootCursor fuel}
    (sourceDouble : input.LocalizedOccurrenceHasRule3DoubleBondEdge cursor.occurrence)
    (budgetLe : input.localizedRerootCursorBudget reference ≤
      input.localizedRerootCursorBudget cursor)
    (sameNotDouble : input.localizedRerootCursorBudget reference =
        input.localizedRerootCursorBudget cursor →
      ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge reference.occurrence) :
    input.extendedDemandRank reference + 2 ≤ input.extendedDemandRank cursor := by
  unfold extendedDemandRank
  rw [if_pos sourceDouble]
  by_cases referenceDouble :
      input.LocalizedOccurrenceHasRule3DoubleBondEdge reference.occurrence
  · rw [if_pos referenceDouble]
    have strict : input.localizedRerootCursorBudget reference <
        input.localizedRerootCursorBudget cursor := by
      rcases lt_or_eq_of_le budgetLe with lt | eq
      · exact lt
      · exact absurd referenceDouble (sameNotDouble eq)
    omega
  · rw [if_neg referenceDouble]
    omega

/-! ## Budget comparison from an outward child -/

/-- **At-least-depth outward reference: the reference budget is no larger.**  The reference is an
executable child of `start` at the appended sibling slot, so its budget is its remaining depth;
the depth grading then compares it with any cursor budget at no greater address depth. -/
theorem localizedRerootCursorBudget_le_of_outward_atLeastDepth
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (start reference cursor : input.LocalizedRerootCursor fuel)
    (present : reference ∈ input.executableLocalizedRerootChildren start)
    (slot : Nat)
    (address : reference.occurrence.1.address = start.occurrence.1.address ++ [slot])
    (atLeast : cursor.occurrence.1.address.length ≤
      reference.occurrence.1.address.length) :
    input.localizedRerootCursorBudget reference ≤
      input.localizedRerootCursorBudget cursor := by
  have referenceBudget := input.localizedRerootCursorBudget_outward_child start reference
    present slot address
  have referenceGrade := input.localizedCIPOccurrence_depthGrade reference.occurrence
  have cursorGrade := input.localizedCIPOccurrence_depthGrade cursor.occurrence
  have referenceLength : reference.occurrence.1.address.length =
      start.occurrence.1.address.length + 1 := by
    rw [address, List.length_append]
    simp
  rw [address, List.length_append] at referenceGrade
  simp only [List.length_singleton] at referenceGrade
  cases cursorPrevious : cursor.previous? with
  | none =>
      rw [referenceBudget,
        input.localizedRerootCursorBudget_eq_address_add_of_none cursor cursorPrevious]
      omega
  | some previous =>
      by_cases shorter : previous.1.address.length < cursor.occurrence.1.address.length
      · rw [referenceBudget,
          input.localizedRerootCursorBudget_eq_remaining_of_previous_shorter
            cursor previous cursorPrevious shorter]
        omega
      · rw [referenceBudget,
          input.localizedRerootCursorBudget_eq_address_add_of_not_shorter
            cursor previous cursorPrevious shorter]
        omega



theorem localizedRerootCursorBudget_lt_of_outward_deeper
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (start reference cursor : input.LocalizedRerootCursor fuel)
    (present : reference ∈ input.executableLocalizedRerootChildren start)
    (slot : Nat)
    (address : reference.occurrence.1.address = start.occurrence.1.address ++ [slot])
    (deeper : cursor.occurrence.1.address.length <
      reference.occurrence.1.address.length) :
    input.localizedRerootCursorBudget reference <
      input.localizedRerootCursorBudget cursor := by
  have referenceBudget := input.localizedRerootCursorBudget_outward_child start reference
    present slot address
  have referenceGrade := input.localizedCIPOccurrence_depthGrade reference.occurrence
  have cursorGrade := input.localizedCIPOccurrence_depthGrade cursor.occurrence
  have referenceLength : reference.occurrence.1.address.length =
      start.occurrence.1.address.length + 1 := by
    rw [address, List.length_append]
    simp
  rw [address, List.length_append] at referenceGrade
  simp only [List.length_singleton] at referenceGrade
  cases cursorPrevious : cursor.previous? with
  | none =>
      rw [referenceBudget,
        input.localizedRerootCursorBudget_eq_address_add_of_none cursor cursorPrevious]
      omega
  | some previous =>
      by_cases shorter : previous.1.address.length < cursor.occurrence.1.address.length
      · rw [referenceBudget,
          input.localizedRerootCursorBudget_eq_remaining_of_previous_shorter
            cursor previous cursorPrevious shorter]
        omega
      · rw [referenceBudget,
          input.localizedRerootCursorBudget_eq_address_add_of_not_shorter
            cursor previous cursorPrevious shorter]
        omega

/-! ## Outward request references carry membership, slot and root data -/

/-- **Every outward short-endpoint reference is an outward executable child.**  The request list is
the explicit two-element list of selected physical references, and the strict depth increase forces
the outward alternative of the carrier-parent dichotomy.  The rooted carrier is preserved. -/
theorem outwardEndpointReference_facts
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (left right : input.Atom)
    (start reference : input.LocalizedRerootCursor fuel)
    (request : List (input.LocalizedRerootCursor fuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests left right start)
    (referenceMem : reference ∈ request)
    (outward : OutwardRerootCursor input start.occurrence reference) :
    reference ∈ input.executableLocalizedRerootChildren start ∧
      (∃ slot, reference.occurrence.1.address =
        start.occurrence.1.address ++ [slot]) ∧
      reference.occurrence.1.root = start.occurrence.1.root := by
  obtain ⟨_valid, ⟨rootEq, deeper⟩, _previous, _previousEq, _previousShorter⟩ := outward
  obtain ⟨first, second, firstCursor, secondCursor, _subs, firstSel, secondSel, _rootCmp,
    _constCmp, requestEq⟩ :=
    input.rule3ShortEndpointCallbackRequests_structure left right start request member
  rw [requestEq] at referenceMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at referenceMem
  rcases referenceMem with same | same
  · subst reference
    obtain ⟨present, _previous', _current, _physical⟩ :=
      input.localizedRule3ReferenceCursorExec?_facts start firstCursor first firstSel
    refine ⟨present, ?_, rootEq⟩
    rcases input.executableLocalizedRerootChild_dichotomy start firstCursor present with
      ⟨parentLength, _parentAddress⟩ | ⟨slot, address⟩
    · omega
    · exact ⟨slot, address⟩
  · subst reference
    obtain ⟨present, _previous', _current, _physical⟩ :=
      input.localizedRule3ReferenceCursorExec?_facts start secondCursor second secondSel
    refine ⟨present, ?_, rootEq⟩
    rcases input.executableLocalizedRerootChild_dichotomy start secondCursor present with
      ⟨parentLength, _parentAddress⟩ | ⟨slot, address⟩
    · omega
    · exact ⟨slot, address⟩

/-! ## Non-root parent: left-endpoint requests are empty -/

/-- **No left-endpoint short request below a non-root carrier parent.**  This is the published
nonroot elimination of `LocalizedNonrootLeftRequestElimination`: if the carrier parent `P` of the
requested occurrence has non-empty original address, the left endpoint emits the empty request
list, with no terminality, branching, or global degree hypothesis.  It is re-exported here because
the root-local request analysis uses it in the branched certificate case. -/
theorem rule3ShortEndpointCallbackRequests_left_eq_nil_of_parent_nonroot
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (O : input.LocalizedCIPOccurrence fuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame fuel)
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O initial)
    (parentNonroot : initial.leftCursor.occurrence.1.address ≠ []) :
    input.rule3ShortEndpointCallbackRequests initial.left initial.right initial.leftCursor = [] :=
  input.rule3ShortEndpointCallbackRequests_eq_nil_of_nonroot O initial frameDecl parentNonroot

/-! ## The root-local exclusion of the branched axis -/

/-- **A branched axis at the carrier root contradicts the root-local bound.**  The declarative
branched topology at `P = initial.leftCursor` supplies two distinct physical continuations `first`,
`second` and the retained right atom as three double-bond neighbours of `P`'s current atom.  When
`P` is the carrier root, its address is empty, hence its node is the official root node and its
current atom is the original root atom.  The root-local order-two bound then forces two of the
three atoms to coincide, contradicting physical-reference uniqueness and the retained-partner
separation. -/
theorem noBranchedAxis_at_rootBound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (root : input.Atom)
    (bound : input.LocalizedRootLocalDoubleBondBound root)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (first second : input.LocalizedRerootCursor carrierFuel)
    (rest : List (input.LocalizedRerootCursor carrierFuel))
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame occurrence initial)
    (rootAddress : initial.leftCursor.occurrence.1.address = [])
    (rootEq : initial.leftCursor.occurrence.1.root = root) :
    ¬ input.DeclarativeLocalizedRule3AxisTopology initial.leftCursor
        (.branched first second rest) := by
  intro branchedAxis
  have frameDeclCopy := frameDecl
  rcases frameDecl with
    ⟨_OReal, _OCurrent, _OParent, OBond, OParentMem, PCurrent, PPrevious, _ROcc, _RPrev⟩
  have PDerived : input.DeclarativeLocalizedOccurrence carrierFuel
      initial.leftCursor.occurrence.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel initial.leftCursor.occurrence.1).mp
      initial.leftCursor.occurrence.2
  have rootFrame :=
    input.declarativeLocalizedOccurrence_eq_root_of_address_nil PDerived rootAddress
  have nodeEq : initial.leftCursor.occurrence.1.node =
      OfficialCIPNode.root initial.leftCursor.occurrence.1.root :=
    congrArg LocalizedCIPOccurrenceFrame.node rootFrame
  have rootCurrent : initial.leftCursor.occurrence.1.node.current? =
      some initial.leftCursor.occurrence.1.root := by
    rw [nodeEq]
    rfl
  have leftEq : initial.left = initial.leftCursor.occurrence.1.root :=
    Option.some.inj (PCurrent.symm.trans rootCurrent)
  have boundAt : (input.localizedOrderTwoNeighbors initial.left).length ≤ 2 := by
    rw [leftEq, rootEq]
    exact bound
  cases branchedAxis with
  | branched branchedFrame distinct =>
      rcases branchedFrame with ⟨children, childrenComputed, childrenDecl, membership⟩
      have childrenEq : children = input.executableLocalizedRerootChildren initial.leftCursor := by
        apply Option.some.inj
        rw [← childrenComputed,
          input.localizedRerootChildren?_eq_some_executable initial.leftCursor]
      have firstAll := (membership first).mp (by simp)
      have secondAll := (membership second).mp (by simp)
      have firstPhysical : input.LocalizedRule3AxisPhysicalContinuation
          initial.leftCursor first := firstAll.2
      have secondPhysical : input.LocalizedRule3AxisPhysicalContinuation
          initial.leftCursor second := secondAll.2
      have firstPresent : first ∈ input.executableLocalizedRerootChildren initial.leftCursor := by
        rw [← childrenEq]
        exact firstAll.1
      have secondPresent : second ∈ input.executableLocalizedRerootChildren initial.leftCursor := by
        rw [← childrenEq]
        exact secondAll.1
      have firstHasCurrent : ∃ atom, first.occurrence.1.node.current? = some atom := by
        rcases firstPhysical with ⟨_, _, matchProp⟩
        simp only [PCurrent] at matchProp
        cases current : first.occurrence.1.node.current? with
        | none => simp [current] at matchProp
        | some atom => exact ⟨atom, rfl⟩
      have secondHasCurrent : ∃ atom, second.occurrence.1.node.current? = some atom := by
        rcases secondPhysical with ⟨_, _, matchProp⟩
        simp only [PCurrent] at matchProp
        cases current : second.occurrence.1.node.current? with
        | none => simp [current] at matchProp
        | some atom => exact ⟨atom, rfl⟩
      obtain ⟨firstAtom, firstCurrent⟩ := firstHasCurrent
      obtain ⟨secondAtom, secondCurrent⟩ := secondHasCurrent
      have atomsNe : firstAtom ≠ secondAtom :=
        input.physicalContinuation_current_ne initial.leftCursor first second firstAtom
          secondAtom firstPresent secondPresent firstPhysical secondPhysical firstCurrent
          secondCurrent distinct
      have firstBond : input.moleculeGraph.bond initial.left firstAtom = 2 := by
        have raw := firstPhysical.2.2
        simpa [PCurrent, firstCurrent] using raw
      have secondBond : input.moleculeGraph.bond initial.left secondAtom = 2 := by
        have raw := secondPhysical.2.2
        simpa [PCurrent, secondCurrent] using raw
      have rightNeFirst : initial.right ≠ firstAtom :=
        input.carrierParent_right_ne_physicalContinuation_current occurrence initial
          frameDeclCopy first firstPresent firstPhysical firstAtom firstCurrent
      have rightNeSecond : initial.right ≠ secondAtom :=
        input.carrierParent_right_ne_physicalContinuation_current occurrence initial
          frameDeclCopy second secondPresent secondPhysical secondAtom secondCurrent
      rcases input.eq_of_three_doubleBond_neighbors_of_rootBound initial.left boundAt
          firstAtom secondAtom initial.right firstBond secondBond OBond with same | same | same
      · exact atomsNe same
      · exact rightNeFirst same.symm
      · exact rightNeSecond same.symm

/-! ## Left-endpoint reference rank facts -/






theorem shortEndpointLeftReference_facts
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (root : input.Atom)
    (cursor : input.LocalizedRerootCursor fuel)
    (cursorRoot : cursor.occurrence.1.root = root)
    (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge cursor.occurrence)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame fuel)
    (physical : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame cursor.occurrence initial)
    (terminal : input.DeclarativeLocalizedRule3AxisTopology initial.leftCursor .terminal)
    (leftCurrent : initial.leftCursor.occurrence.1.node.current? = some initial.left)
    (request : List (input.LocalizedRerootCursor fuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests initial.left initial.right
      initial.leftCursor)
    (reference : input.LocalizedRerootCursor fuel)
    (referenceMem : reference ∈ request) :
    input.LocalizedRerootCursorValid reference ∧
      reference.occurrence.1.root = root ∧
      input.extendedDemandRank reference + 2 ≤ input.extendedDemandRank cursor := by
  have physicalCopy := physical
  obtain ⟨_realO, _occurrenceCurrent, _occurrenceParent, _bond, parentDecl,
    _leftCurrentField, _leftPrevious, _rightOccurrence, _rightPrevious⟩ := physicalCopy
  have startActive := input.carrierParent_active_of_frame cursor.occurrence initial physical
  have outward := input.rule3ShortEndpointCallbackRequests_left_outward
    initial.leftCursor.occurrence initial.leftCursor initial.left initial.right rfl le_rfl
    startActive request member
  obtain ⟨referencePresent, ⟨slot, referenceAddress⟩, referenceNotDouble⟩ :=
    input.shortEndpointReference_facts_of_outward initial.leftCursor reference
      initial.left initial.right terminal initial.left leftCurrent request member referenceMem
      (outward reference referenceMem)
  have parentFacts := input.localizedCarrierParentFrame_facts cursor.occurrence.1
    initial.leftCursor.occurrence.1 parentDecl
  have referenceLength : reference.occurrence.1.address.length =
      initial.leftCursor.occurrence.1.address.length + 1 := by
    rw [referenceAddress, List.length_append]
    simp
  have atLeast : cursor.occurrence.1.address.length ≤
      reference.occurrence.1.address.length := by
    have lenEq := parentFacts.2.1
    omega
  have budgetLe := input.localizedRerootCursorBudget_le_of_outward_atLeastDepth
    initial.leftCursor reference cursor referencePresent slot referenceAddress atLeast
  have referenceRootOut : reference.occurrence.1.root =
      initial.leftCursor.occurrence.1.root := (outward reference referenceMem).2.1.1
  exact ⟨input.localizedRerootChild_valid initial.leftCursor reference
      (input.executableLocalizedRerootChildren initial.leftCursor)
      (input.executableLocalizedRerootChildren_declarative initial.leftCursor) referencePresent,
    referenceRootOut.trans (parentFacts.1.trans cursorRoot),
    input.extendedDemandRank_request_of_budget_le edge budgetLe
      (fun _ => referenceNotDouble)⟩

/-! ## Right-endpoint reference rank facts -/






theorem shortEndpointRightReference_facts
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (root : input.Atom)
    (cursor : input.LocalizedRerootCursor fuel)
    (cursorRoot : cursor.occurrence.1.root = root)
    (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge cursor.occurrence)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame fuel)
    (physical : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame cursor.occurrence initial)
    (request : List (input.LocalizedRerootCursor fuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests initial.right initial.left
      initial.rightCursor)
    (reference : input.LocalizedRerootCursor fuel)
    (referenceMem : reference ∈ request) :
    input.LocalizedRerootCursorValid reference ∧
      reference.occurrence.1.root = root ∧
      input.extendedDemandRank reference + 2 ≤ input.extendedDemandRank cursor := by
  obtain ⟨_realO, _occurrenceCurrent, _occurrenceParent, _bond, parentDecl,
    _leftCurrent, _leftPrevious, rightOccurrence, rightPrevious⟩ := physical
  have outward := input.rule3ShortEndpointCallbackRequests_right_outward_of_parent
    initial.rightCursor.occurrence initial.rightCursor initial.leftCursor.occurrence
    rightPrevious (by rw [rightOccurrence]; exact parentDecl) rfl le_rfl
    initial.right initial.left request member
  obtain ⟨referencePresent, ⟨slot, referenceAddress⟩, referenceRootRight⟩ :=
    input.outwardEndpointReference_facts initial.right initial.left initial.rightCursor
      reference request member referenceMem (outward reference referenceMem)
  have rightRoot : initial.rightCursor.occurrence.1.root = root := by
    rw [rightOccurrence]
    exact cursorRoot
  have referenceLength : reference.occurrence.1.address.length =
      initial.rightCursor.occurrence.1.address.length + 1 := by
    rw [referenceAddress, List.length_append]
    simp
  have sameLength : initial.rightCursor.occurrence.1.address.length =
      cursor.occurrence.1.address.length := by
    rw [rightOccurrence]
  have deeper : cursor.occurrence.1.address.length <
      reference.occurrence.1.address.length := by
    omega
  have budgetLt := input.localizedRerootCursorBudget_lt_of_outward_deeper
    initial.rightCursor reference cursor referencePresent slot referenceAddress deeper
  exact ⟨input.localizedRerootChild_valid initial.rightCursor reference
      (input.executableLocalizedRerootChildren initial.rightCursor)
      (input.executableLocalizedRerootChildren_declarative initial.rightCursor) referencePresent,
    referenceRootRight.trans rightRoot,
    input.extendedDemandRank_request_of_budget_le edge (le_of_lt budgetLt)
      (fun same => absurd same (ne_of_lt budgetLt))⟩

/-! ## The ordinary (one-bond spatial) route -/

/-- **Every actual request reference of the ordinary spatial route pays the callback weight, under
the root-local bound only.**  The route certificate is either branched or a one-bond terminal
axis.  A branched axis can only contribute a left request when its carrier parent is the root
(the nonroot left list is empty), and at the root it contradicts the root-local bound.  In the
terminal-axis route, left references are handled by `shortEndpointLeftReference_facts` and right
references by `shortEndpointRightReference_facts`; neither needs any bound at interior atoms. -/
theorem requestReference_facts_of_shortSpatial_of_rootBound
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (root : input.Atom)
    (bound : input.LocalizedRootLocalDoubleBondBound root)
    (cursor : input.LocalizedRerootCursor fuel)
    (cursorRoot : cursor.occurrence.1.root = root)
    (certificate : input.LocalizedRule3OrdinaryRouteCertificate cursor.occurrence)
    (_computed : input.localizedRule3OrdinaryRouteCertificate? cursor.occurrence = some certificate)
    (request : List (input.LocalizedRerootCursor fuel))
    (member : request ∈ input.rule3ShortSpatialCallbackRequests cursor.occurrence)
    (reference : input.LocalizedRerootCursor fuel)
    (referenceMem : reference ∈ request) :
    input.LocalizedRerootCursorValid reference ∧
      reference.occurrence.1.root = root ∧
      input.extendedDemandRank reference + 2 ≤ input.extendedDemandRank cursor := by
  rcases certificate.valid with ⟨edge, route⟩
  rcases input.rule3ShortSpatialCallbackRequests_structure cursor.occurrence request member with
    ⟨frame, frameComputed, memberRest⟩
  have frameOriginal : input.localizedRule3PhysicalEndpointCursorFrame? cursor.occurrence =
      some frame := by
    rw [← input.localizedRule3PhysicalEndpointCursorFrameExec?_eq_original cursor.occurrence]
    exact frameComputed
  rcases route with branchedRoute | oneBond
  · rcases branchedRoute with ⟨initial, first, second, rest, entryDecl⟩
    cases entryDecl with
    | branched physical branchTopology =>
        have axisComputed :=
          input.localizedRule3PhysicalEndpointCursorFrame?_eq_some_of_declarative
            cursor.occurrence initial physical
        have frameEq : frame = initial := by
          rw [frameOriginal] at axisComputed
          exact Option.some.inj axisComputed
        subst frame
        have parentFacts := input.localizedCarrierParentFrame_facts cursor.occurrence.1
          initial.leftCursor.occurrence.1 physical.2.2.2.2.1
        have parentRoot : initial.leftCursor.occurrence.1.root = root :=
          parentFacts.1.trans cursorRoot
        rcases memberRest with memberLeft | memberRight
        · by_cases rootAddress : initial.leftCursor.occurrence.1.address = []
          · exact (input.noBranchedAxis_at_rootBound root bound cursor.occurrence initial
              first second rest physical rootAddress parentRoot branchTopology).elim
          · have empty := input.rule3ShortEndpointCallbackRequests_eq_nil_of_nonroot
              cursor.occurrence initial physical rootAddress
            rw [empty] at memberLeft
            simp at memberLeft
        · exact input.shortEndpointRightReference_facts root cursor cursorRoot edge initial
            physical request memberRight reference referenceMem
  · obtain ⟨axis, axisDecl, _countOne⟩ := oneBond
    rcases axisDecl with ⟨entryDecl, _walkDecl, _reverseDecl, _rightPartnerCurrent, _rightCurrent⟩
    cases entryDecl with
    | terminalStart physical terminalLeft =>
        have physicalCopy := physical
        have axisComputed :=
          input.localizedRule3PhysicalEndpointCursorFrame?_eq_some_of_declarative
            cursor.occurrence axis.initial physical
        have frameEq : frame = axis.initial := by
          rw [frameOriginal] at axisComputed
          exact Option.some.inj axisComputed
        subst frame
        obtain ⟨_realO, _occurrenceCurrent, _occurrenceParent, _bond, _parentDecl,
          leftCurrent, _leftPrevious, _rightOccurrence, _rightPrevious⟩ := physicalCopy
        rcases memberRest with memberLeft | memberRight
        · exact input.shortEndpointLeftReference_facts root cursor cursorRoot edge axis.initial
            physical terminalLeft leftCurrent request memberLeft reference referenceMem
        · exact input.shortEndpointRightReference_facts root cursor cursorRoot edge axis.initial
            physical request memberRight reference referenceMem

/-! ## The odd-cumulene route -/







theorem rootLocal_oddRightRequest_outward
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame fuel)
    (decl : input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame cursor.occurrence
      topology)
    (request : List (input.LocalizedRerootCursor fuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests topology.right
      topology.rightPartner topology.rightCursor) :
    (∀ reference ∈ request,
      OutwardRerootCursor input topology.rightCursor.occurrence reference) ∧
      topology.rightCursor.occurrence.1.root = cursor.occurrence.1.root := by
  obtain ⟨physicalDecl, _terminalLeft, walkDecl, reverseDecl, _rightPartnerCurrent,
    _rightCurrent, _oneLt, _odd⟩ := decl
  obtain ⟨_realO, _occurrenceCurrent, _occurrenceParent, _bond, parentDecl, _leftCurrent,
    _leftPrevious, rightOccurrence, rightPrevious⟩ := physicalDecl
  obtain ⟨reverseRest, reverseEq⟩ := reverseDecl
  have parentFacts := input.localizedCarrierParentFrame_facts cursor.occurrence.1
    topology.initial.leftCursor.occurrence.1 parentDecl
  have parentInNeighbors : topology.initial.leftCursor.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := fuel) cursor.occurrence.1 := by
    rw [localizedRerootNeighborFrames, List.mem_append]
    exact Or.inl parentDecl
  have initialValid : input.LocalizedRerootCursorValid topology.initial.rightCursor := by
    unfold LocalizedRerootCursorValid
    simp only [rightPrevious, rightOccurrence]
    exact input.mem_localizedRerootNeighborFrames_symm cursor.occurrence
      topology.initial.leftCursor.occurrence.1 parentInNeighbors
  have initialShorter : topology.initial.leftCursor.occurrence.1.address.length <
      topology.initial.rightCursor.occurrence.1.address.length := by
    rw [rightOccurrence]
    omega
  have initialDependency : input.LocalizedDepthDependency
      topology.initial.rightCursor.occurrence topology.initial.leftCursor.occurrence := by
    refine ⟨?_, ?_⟩
    · rw [rightOccurrence]
      exact parentFacts.1.symm
    · rw [rightOccurrence]
      omega
  have initialOutward : OutwardRerootCursor input topology.initial.leftCursor.occurrence
      topology.initial.rightCursor :=
    ⟨initialValid, initialDependency, topology.initial.leftCursor.occurrence, rightPrevious,
      initialShorter⟩
  have allOutward := input.declarativeWalk_cursor_outward
    topology.initial.leftCursor.occurrence topology.initial.rightCursor topology.rightward
    walkDecl initialOutward
  have rightMember : topology.rightCursor ∈ topology.rightward := by
    have memRev : topology.rightCursor ∈ topology.rightward.reverse := by
      rw [reverseEq]
      simp
    exact List.mem_reverse.mp memRev
  have rightRoot : topology.rightCursor.occurrence.1.root =
      topology.initial.leftCursor.occurrence.1.root :=
    (allOutward topology.rightCursor rightMember).2.1.1
  have partnerMem : topology.rightPartnerCursor ∈ topology.rightward := by
    rw [← List.mem_reverse, reverseEq]
    simp
  have partnerOutward := allOutward topology.rightPartnerCursor partnerMem
  obtain ⟨partnerValid, _partnerDependency, partnerPrevious, partnerPreviousEq,
    partnerShorter⟩ := partnerOutward
  have lastPair := input.declarativeWalk_reverse_last_pair
    topology.initial.rightCursor topology.rightward walkDecl
    topology.rightCursor topology.rightPartnerCursor reverseRest reverseEq
  have edge : E input topology.rightPartnerCursor topology.rightCursor := lastPair.1
  have rightPrevious' : topology.rightCursor.previous? =
      some topology.rightPartnerCursor.occurrence := lastPair.2
  obtain ⟨stepDropLast, _stepLength, stepRoot, _stepPrevious, _stepValid⟩ :=
    input.outward_edge topology.rightPartnerCursor topology.rightCursor partnerValid
      partnerPrevious partnerPreviousEq partnerShorter edge
  have previousParent : topology.rightPartnerCursor.occurrence.1 ∈
      input.localizedCarrierParentFrames (fuel := fuel) topology.rightCursor.occurrence.1 := by
    rw [localizedCarrierParentFrames, List.mem_filter]
    refine ⟨topology.rightPartnerCursor.occurrence.2, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨stepRoot.symm, by omega⟩, stepDropLast.symm⟩
  exact ⟨input.rule3ShortEndpointCallbackRequests_right_outward_of_parent
      topology.rightCursor.occurrence topology.rightCursor
      topology.rightPartnerCursor.occurrence rightPrevious' previousParent rfl le_rfl
      topology.right topology.rightPartner request member,
    rightRoot.trans parentFacts.1⟩

/-- **Every odd left-endpoint reference pays the callback weight under the root-local bound
only.**  The odd left endpoint is the terminal left endpoint of the initial physical frame, so the
ordinary terminal-frame reference analysis applies verbatim. -/
theorem requestReference_facts_of_oddLeft_of_rootBound
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (root : input.Atom)
    (cursor : input.LocalizedRerootCursor fuel)
    (cursorRoot : cursor.occurrence.1.root = root)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame fuel)
    (decl : input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame cursor.occurrence
      topology)
    (edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge cursor.occurrence)
    (request : List (input.LocalizedRerootCursor fuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests topology.initial.left
      topology.initial.right topology.initial.leftCursor)
    (reference : input.LocalizedRerootCursor fuel)
    (referenceMem : reference ∈ request) :
    input.LocalizedRerootCursorValid reference ∧
      reference.occurrence.1.root = root ∧
      input.extendedDemandRank reference + 2 ≤ input.extendedDemandRank cursor := by
  obtain ⟨physicalDecl, terminalLeft, _walk, _reverse, _rightPartnerCurrent, _rightCurrent,
    _oneLt, _odd⟩ := decl
  have physicalCopy := physicalDecl
  obtain ⟨_realO, _occurrenceCurrent, _occurrenceParent, _bond, _parentDecl, leftCurrent,
    _leftPrevious, _rightOccurrence, _rightPrevious⟩ := physicalCopy
  exact input.shortEndpointLeftReference_facts root cursor cursorRoot edge topology.initial
    physicalDecl terminalLeft leftCurrent request member reference referenceMem






theorem requestReference_facts_of_oddRight_of_rootBound
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (root : input.Atom)
    (cursor : input.LocalizedRerootCursor fuel)
    (cursorRoot : cursor.occurrence.1.root = root)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame fuel)
    (decl : input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame cursor.occurrence
      topology)
    (request : List (input.LocalizedRerootCursor fuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests topology.right
      topology.rightPartner topology.rightCursor)
    (reference : input.LocalizedRerootCursor fuel)
    (referenceMem : reference ∈ request) :
    input.LocalizedRerootCursorValid reference ∧
      reference.occurrence.1.root = root ∧
      input.extendedDemandRank reference + 2 ≤ input.extendedDemandRank cursor := by
  obtain ⟨referenceValid, step⟩ :=
    input.requestReference_facts_of_oddRight cursor topology decl request member reference
      referenceMem
  obtain ⟨outward, rightRoot⟩ :=
    input.rootLocal_oddRightRequest_outward cursor topology decl request member
  exact ⟨referenceValid,
    (outward reference referenceMem).2.1.1.trans (rightRoot.trans cursorRoot),
    input.extendedDemandRank_request step⟩

/-! ## Every actual extended request reference -/

/-- **Every actual extended request reference pays the callback weight and stays in the rooted
carrier, under the root-local bound only.**  The route branch is the actual certificate branch of
the extended evaluator; the joint-failure branch emits no request at all.  The odd branch is
dispatched to the left/right odd lemmas, and the ordinary branch to the spatial analysis. -/
theorem requestReference_facts_of_extendedRequest_of_rootBound
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (root : input.Atom)
    (bound : input.LocalizedRootLocalDoubleBondBound root)
    (cursor : input.LocalizedRerootCursor fuel)
    (cursorRoot : cursor.occurrence.1.root = root)
    (request : List (input.LocalizedRerootCursor fuel))
    (member : request ∈ input.rule3ExtendedNodeCallbackRequests cursor.occurrence)
    (reference : input.LocalizedRerootCursor fuel)
    (referenceMem : reference ∈ request) :
    input.LocalizedRerootCursorValid reference ∧
      reference.occurrence.1.root = root ∧
      input.extendedDemandRank reference + 2 ≤ input.extendedDemandRank cursor := by
  unfold rule3ExtendedNodeCallbackRequests at member
  cases routed : input.localizedRule3OddRouteCertificate? cursor.occurrence with
  | some certificate =>
      simp only [routed] at member
      unfold rule3ShortOddCallbackRequests at member
      cases computed : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
          (input.localizedRule3CumulatedTraversalFuel fuel) cursor.occurrence with
      | none => simp [computed] at member
      | some topology =>
          simp only [computed] at member
          have originalComputed : input.localizedRule3OddCumuleneEndpointCursorFrame?
              (input.localizedRule3CumulatedTraversalFuel fuel) cursor.occurrence =
                some topology := by
            rw [← input.localizedRule3OddCumuleneEndpointCursorFrameExec?_eq_original
              (input.localizedRule3CumulatedTraversalFuel fuel) cursor.occurrence]
            exact computed
          have sound := input.localizedRule3OddCumuleneEndpointCursorFrame?_sound
            (input.localizedRule3CumulatedTraversalFuel fuel) cursor.occurrence topology
            originalComputed
          rcases List.mem_append.mp member with leftMember | rightMember
          · exact input.requestReference_facts_of_oddLeft_of_rootBound root cursor cursorRoot
              topology sound certificate.valid.1 request leftMember reference referenceMem
          · exact input.requestReference_facts_of_oddRight_of_rootBound root cursor cursorRoot
              topology sound request rightMember reference referenceMem
  | none =>
      simp only [routed] at member
      unfold rule3NodeCallbackRequests at member
      cases ordinary : input.localizedRule3OrdinaryRouteCertificate? cursor.occurrence with
      | none =>
          have empty := input.rule3OriginalNodeCallbackRequests_eq_nil_of_jointRouteCertificateNone
            cursor.occurrence ordinary routed
          simp only [ordinary, empty, List.mem_nil_iff] at member
      | some certificate =>
          simp only [ordinary] at member
          exact input.requestReference_facts_of_shortSpatial_of_rootBound root bound cursor
            cursorRoot certificate ordinary request member reference referenceMem





theorem rootLocalDoubleBondBound_of_neighbourBound
    (input : CertifiedLocalizedCIPInput) (root : input.Atom)
    (bound : input.LocalizedRootDoubleBondNeighbourBound root) :
    input.LocalizedRootLocalDoubleBondBound root :=
  (input.localizedRootDoubleBondNeighbourBound_iff_orderTwoNeighbors_length root).mp bound





theorem rootLocalDoubleBondBound_of_fourLigandFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (rootAddress : target.1.address = [])
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame) :
    input.LocalizedRootLocalDoubleBondBound target.1.root :=
  input.rootLocalDoubleBondBound_of_neighbourBound target.1.root
    (input.doubleBondNeighbourFinset_card_le_two_of_fourLigandFrame target rootAddress frame
      computed)

/-! ## The root-local demand domain and rank certificate -/

/-- **The root-local demand domain.**  A cursor is admitted when it is a valid reroot orientation
whose occurrence is still rooted at the designated original carrier root.  There is no condition
on interior atoms. -/
def LocalizedRootLocalDemandDomain (input : CertifiedLocalizedCIPInput)
    (root : input.Atom) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) : Prop :=
  input.LocalizedRerootCursorValid cursor ∧ cursor.occurrence.1.root = root

/-- **Every actual extended demand successor stays at the original root and strictly decreases the
rank, under the root-local bound only.**  Child edges preserve the root through the rooted carrier
and decrease the rank by at least one.  Request edges are classified by the actual structural route
analysis `requestReference_facts_of_extendedRequest_of_rootBound`, which pays the callback weight
`2`. -/
theorem rootLocalSuccessor_decreases
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (root : input.Atom)
    (bound : input.LocalizedRootLocalDoubleBondBound root)
    (cursor : input.LocalizedRerootCursor fuel)
    (domain : input.LocalizedRootLocalDemandDomain root cursor)
    (successor : input.LocalizedRerootCursor fuel)
    (edge : successor ∈ input.extendedRule3DemandSuccessors cursor) :
    input.LocalizedRootLocalDemandDomain root successor ∧
      input.extendedDemandRank successor < input.extendedDemandRank cursor := by
  rcases domain with ⟨cursorValid, cursorRoot⟩
  simp only [extendedRule3DemandSuccessors, List.mem_append] at edge
  rcases edge with childEdge | requestEdge
  · have childValid := input.localizedRerootChild_valid cursor successor
      (input.executableLocalizedRerootChildren cursor)
      (input.executableLocalizedRerootChildren_declarative cursor) childEdge
    have childRoot : successor.occurrence.1.root = cursor.occurrence.1.root :=
      input.localizedRerootChildren_root_eq cursor successor
        (input.executableLocalizedRerootChildren cursor)
        (input.executableLocalizedRerootChildren_declarative cursor) childEdge
    refine ⟨⟨childValid, childRoot.trans cursorRoot⟩, ?_⟩
    have childRank := input.extendedDemandRank_child cursor successor cursorValid childEdge
    omega
  · obtain ⟨request, requested, successorMem⟩ := List.mem_flatten.mp requestEdge
    have facts := input.requestReference_facts_of_extendedRequest_of_rootBound root bound
      cursor cursorRoot request requested successor successorMem
    exact ⟨⟨facts.1, facts.2.1⟩, by have := facts.2.2; omega⟩

/-! ## Actual root-local graph-domain consequences -/






theorem rootLocalExtendedRule3DemandAcyclic
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (root : input.Atom)
    (bound : input.LocalizedRootLocalDoubleBondBound root)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootDomain : ∀ rootCursor ∈ roots,
      input.LocalizedRootLocalDemandDomain root rootCursor) :
    input.ExtendedRule3DemandAcyclic roots := by
  intro cursor reachable
  exact acyclic_reachable_of_decreasing input.ExtendedRule3DemandEdge roots
    (input.LocalizedRootLocalDemandDomain (fuel := fuel) root)
    input.extendedDemandRank rootDomain
    (fun parent member child edge =>
      input.rootLocalSuccessor_decreases root bound parent member child edge)
    cursor reachable

/-- Actual root-local weighted-demand acyclicity, transported through the existing generic
weighted-graph equivalence. -/
theorem rootLocalWeightedExtendedDemandAcyclic
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (root : input.Atom)
    (bound : input.LocalizedRootLocalDoubleBondBound root)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootDomain : ∀ rootCursor ∈ roots,
      input.LocalizedRootLocalDemandDomain root rootCursor) :
    Acyclic (input.extendedWeightedDemandGraph fuel) roots :=
  (input.extendedWeightedDemandGraph_acyclic fuel roots).mpr
    (input.rootLocalExtendedRule3DemandAcyclic root bound roots rootDomain)



theorem rootLocalExtendedRule3DemandPlan_total
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (root : input.Atom)
    (bound : input.LocalizedRootLocalDoubleBondBound root)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootDomain : ∀ rootCursor ∈ roots,
      input.LocalizedRootLocalDemandDomain root rootCursor) :
    ∃ plan, input.prepareExtendedRule3DemandPlan roots = .ok plan :=
  input.prepareExtendedRule3DemandPlan_total_of_acyclic roots
    (input.rootLocalExtendedRule3DemandAcyclic root bound roots rootDomain)

/-- Actual root-local discovery totality of the existing DFS at the rank budget
`6 * (fuel + 1) + 3`.  This bounds discovery, not the evaluator. -/
theorem rootLocalExtendedRule3DemandDiscovery_total
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (root : input.Atom)
    (bound : input.LocalizedRootLocalDoubleBondBound root)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootDomain : ∀ rootCursor ∈ roots,
      input.LocalizedRootLocalDemandDomain root rootCursor) :
    ∃ table,
      roots.foldlM (fun known rootCursor =>
        input.discoverExtendedRule3DemandRanks (6 * (fuel + 1) + 3) [] known rootCursor) [] =
          .ok table ∧
      input.ExtendedRule3DemandRankTableValid table ∧
      (∀ rootCursor ∈ roots, rootCursor ∈ table.map Prod.fst) := by
  refine input.discoverExtendedRule3DemandRoots_total_of_measure
    (input.LocalizedRootLocalDemandDomain (fuel := fuel) root)
    input.extendedDemandRank
    (fun parent member child edge =>
      input.rootLocalSuccessor_decreases root bound parent member child edge)
    (6 * (fuel + 1) + 3) roots rootDomain ?_
  intro rootCursor _rootPresent
  have bounded := input.extendedDemandRank_le_bound rootCursor
  unfold extendedDemandRankBound at bounded
  omega






theorem rootLocalExtendedDemandTotality
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (root : input.Atom)
    (bound : input.LocalizedRootLocalDoubleBondBound root)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootDomain : ∀ rootCursor ∈ roots,
      input.LocalizedRootLocalDemandDomain root rootCursor) :
    ∃ plan : input.ExtendedRule3DemandPlan roots,
      input.prepareExtendedRule3DemandPlan roots = .ok plan ∧
      input.ExtendedRule3DemandAcyclic roots ∧
      Acyclic (input.extendedWeightedDemandGraph fuel) roots ∧
      (∀ rootCursor ∈ roots, rootCursor ∈ plan.ranks.vertices) ∧
      plan.bound = rule3CursorListHeight plan.ranks.height roots + 1 ∧
      plan.toWeightedPlan.bound = plan.bound ∧
      (∀ (target : input.LocalizedCIPOccurrence fuel)
        (view : input.LocalizedDependencyView target) (budget : Nat),
        plan.bound ≤ budget →
          plan.evaluate target view =
            input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget roots) ∧
      (∀ (target : input.LocalizedCIPOccurrence fuel)
        (view : input.LocalizedDependencyView target)
        (frame : input.LocalizedRule3CanonicalKeyFrame),
        plan.evaluate target view = some frame →
          input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view plan.bound roots
            frame) := by
  obtain ⟨plan, succeeds⟩ :=
    input.rootLocalExtendedRule3DemandPlan_total root bound roots rootDomain
  have acyclic := input.rootLocalExtendedRule3DemandAcyclic root bound roots rootDomain
  exact ⟨plan, succeeds, acyclic,
    (input.extendedWeightedDemandGraph_acyclic fuel roots).mp acyclic,
    plan.covers, rfl, ExtendedRule3DemandPlan.toWeightedPlan_bound plan,
    fun target view budget enough => plan.evaluate_eq_above target view budget enough,
    fun target view frame computed => plan.evaluate_sound target view frame computed⟩

/-- The actual constructor never returns a cycle refusal on the root-local domain. -/
theorem rootLocalExtendedRule3DemandPlan_noCycleError
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (root : input.Atom)
    (bound : input.LocalizedRootLocalDoubleBondBound root)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootDomain : ∀ rootCursor ∈ roots,
      input.LocalizedRootLocalDemandDomain root rootCursor) :
    ∀ cursor, input.prepareExtendedRule3DemandPlan roots ≠ .error (.cycle cursor) := by
  intro cursor failed
  obtain ⟨plan, succeeds⟩ :=
    input.rootLocalExtendedRule3DemandPlan_total root bound roots rootDomain
  rw [succeeds] at failed
  cases failed

/-- The actual constructor returns no error at all on the root-local domain. -/
theorem rootLocalExtendedRule3DemandPlan_noError
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (root : input.Atom)
    (bound : input.LocalizedRootLocalDoubleBondBound root)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootDomain : ∀ rootCursor ∈ roots,
      input.LocalizedRootLocalDemandDomain root rootCursor)
    (failure : input.Rule3DemandDiscoveryFailure fuel) :
    input.prepareExtendedRule3DemandPlan roots ≠ .error failure := by
  intro failed
  obtain ⟨plan, succeeds⟩ :=
    input.rootLocalExtendedRule3DemandPlan_total root bound roots rootDomain
  rw [succeeds] at failed
  cases failed

/-! ## The assembled tetrahedral-root theorem -/













theorem fourLigandRootLocalExtendedDemandAcyclic
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (rootAddress : target.1.address = [])
    (frame : input.LocalizedOccurrenceFourLigandFrame fuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootDomain : ∀ rootCursor ∈ roots,
      input.LocalizedRootLocalDemandDomain target.1.root rootCursor) :
    input.ExtendedRule3DemandAcyclic roots ∧
      Acyclic (input.extendedWeightedDemandGraph fuel) roots ∧
      (∃ plan, input.prepareExtendedRule3DemandPlan roots = .ok plan) ∧
      (∃ table,
        roots.foldlM (fun known rootCursor =>
          input.discoverExtendedRule3DemandRanks (6 * (fuel + 1) + 3) [] known rootCursor) [] =
            .ok table ∧
        input.ExtendedRule3DemandRankTableValid table ∧
        (∀ rootCursor ∈ roots, rootCursor ∈ table.map Prod.fst)) := by
  have bound :=
    input.rootLocalDoubleBondBound_of_fourLigandFrame target rootAddress frame computed
  exact ⟨input.rootLocalExtendedRule3DemandAcyclic target.1.root bound roots rootDomain,
    input.rootLocalWeightedExtendedDemandAcyclic target.1.root bound roots rootDomain,
    input.rootLocalExtendedRule3DemandPlan_total target.1.root bound roots rootDomain,
    input.rootLocalExtendedRule3DemandDiscovery_total target.1.root bound roots rootDomain⟩

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRootLocalDoubleBondBound
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.eq_of_three_doubleBond_neighbors_of_rootBound
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendedDemandRank_request_of_budget_le
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootCursorBudget_le_of_outward_atLeastDepth
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootCursorBudget_lt_of_outward_deeper
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outwardEndpointReference_facts
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortEndpointCallbackRequests_left_eq_nil_of_parent_nonroot
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.noBranchedAxis_at_rootBound
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.shortEndpointLeftReference_facts
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.shortEndpointRightReference_facts
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.requestReference_facts_of_shortSpatial_of_rootBound
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rootLocal_oddRightRequest_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.requestReference_facts_of_oddLeft_of_rootBound
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.requestReference_facts_of_oddRight_of_rootBound
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.requestReference_facts_of_extendedRequest_of_rootBound
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rootLocalDoubleBondBound_of_neighbourBound
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rootLocalDoubleBondBound_of_fourLigandFrame
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRootLocalDemandDomain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rootLocalSuccessor_decreases
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rootLocalExtendedRule3DemandAcyclic
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rootLocalWeightedExtendedDemandAcyclic
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rootLocalExtendedRule3DemandPlan_total
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rootLocalExtendedRule3DemandDiscovery_total
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rootLocalExtendedDemandTotality
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rootLocalExtendedRule3DemandPlan_noCycleError
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rootLocalExtendedRule3DemandPlan_noError
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.fourLigandRootLocalExtendedDemandAcyclic
