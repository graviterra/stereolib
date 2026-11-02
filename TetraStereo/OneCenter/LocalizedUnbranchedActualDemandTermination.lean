import TetraStereo.OneCenter.LocalizedUnbranchedExtendedDemandRank
import TetraStereo.OneCenter.LocalizedUnbranchedExtendedDemandTotality
import TetraStereo.OneCenter.LocalizedUnbranchedRule3RequestPhase
import TetraStereo.OneCenter.LocalizedRule3OriginalTargetDemand
import TetraStereo.OneCenter.LocalizedRule3RouteCompleteness
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

open TetraStereo.Certificate.WeightedDemand
























/-! ## Graph-domain equivalence: list neighbours versus the Finset domain -/




theorem localizedDoubleBondNeighbourFinset_card_eq_orderTwoNeighbors_length
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom) :
    (input.localizedDoubleBondNeighbourFinset atom).card =
      (input.localizedOrderTwoNeighbors atom).length := by
  unfold localizedDoubleBondNeighbourFinset localizedOrderTwoNeighbors
  rw [Finset.length_sort]

/-- The list-based unbranched graph domain is exactly the Finset-based domain of the rank core. -/
theorem unbranchedDoubleBondGraph_iff_neighbourDomain
    (input : CertifiedLocalizedCIPInput) :
    input.LocalizedUnbranchedDoubleBondGraph ↔
      input.LocalizedUnbranchedDoubleBondNeighbourDomain := by
  unfold LocalizedUnbranchedDoubleBondGraph LocalizedUnbranchedDoubleBondNeighbourDomain
  constructor
  · intro domain atom
    have cardEq := input.localizedDoubleBondNeighbourFinset_card_eq_orderTwoNeighbors_length atom
    have bound := domain atom
    omega
  · intro domain atom
    have cardEq := input.localizedDoubleBondNeighbourFinset_card_eq_orderTwoNeighbors_length atom
    have bound := domain atom
    omega

/-- The list-based graph domain as an admission fact for the rank witness. -/
theorem unbranchedDoubleBondInput_of_graphDomain
    (input : CertifiedLocalizedCIPInput)
    (domain : input.LocalizedUnbranchedDoubleBondGraph) :
    input.UnbranchedDoubleBondInput := by
  intro atom
  have cardEq := input.localizedDoubleBondNeighbourFinset_card_eq_orderTwoNeighbors_length atom
  have bound := (input.unbranchedDoubleBondGraph_iff_neighbourDomain).mp domain atom
  omega

/-! ## Budget arithmetic at the three cursor orientations -/

/-- A cursor with no incoming cut has the round-trip budget `|address| + (fuel + 1)`. -/
theorem localizedRerootCursorBudget_eq_address_add_of_none
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (previousEq : cursor.previous? = none) :
    input.localizedRerootCursorBudget cursor =
      cursor.occurrence.1.address.length + (fuel + 1) := by
  unfold localizedRerootCursorBudget
  rw [previousEq]

/-- A cursor reached from a strictly shallower incoming cut only has its remaining depth: the
parent-oriented budget case. -/
theorem localizedRerootCursorBudget_eq_remaining_of_previous_shorter
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (previous : input.LocalizedCIPOccurrence fuel)
    (previousEq : cursor.previous? = some previous)
    (shorter : previous.1.address.length < cursor.occurrence.1.address.length) :
    input.localizedRerootCursorBudget cursor = cursor.occurrence.1.remaining := by
  unfold localizedRerootCursorBudget
  rw [previousEq]
  simp [shorter]

/-- A cursor whose incoming cut is not strictly shallower keeps the round-trip budget. -/
theorem localizedRerootCursorBudget_eq_address_add_of_not_shorter
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (previous : input.LocalizedCIPOccurrence fuel)
    (previousEq : cursor.previous? = some previous)
    (notShorter : ¬ previous.1.address.length < cursor.occurrence.1.address.length) :
    input.localizedRerootCursorBudget cursor =
      cursor.occurrence.1.address.length + (fuel + 1) := by
  unfold localizedRerootCursorBudget
  rw [previousEq]
  simp [notShorter]

/-- An outward executable child records the endpoint occurrence as its incoming cut, so its budget
is exactly its remaining depth.  This is the orientation-sensitive fact behind every request
reference decrease. -/
theorem localizedRerootCursorBudget_outward_child
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (start reference : input.LocalizedRerootCursor fuel)
    (present : reference ∈ input.executableLocalizedRerootChildren start)
    (slot : Nat)
    (address : reference.occurrence.1.address = start.occurrence.1.address ++ [slot]) :
    input.localizedRerootCursorBudget reference = reference.occurrence.1.remaining := by
  have previous := input.executableLocalizedRerootChildren_previous start reference present
  have shorter : start.occurrence.1.address.length <
      reference.occurrence.1.address.length := by
    rw [address, List.length_append]
    simp
  exact input.localizedRerootCursorBudget_eq_remaining_of_previous_shorter
    reference start.occurrence previous shorter

/-! ## Request steps from actual outward structural facts -/



theorem extendedDemandRequestStep_right_of_outward
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor start reference : input.LocalizedRerootCursor fuel)
    (startOccurrence : start.occurrence.1 = cursor.occurrence.1)
    (cursorNonroot : 0 < cursor.occurrence.1.address.length)
    (referencePresent : reference ∈ input.executableLocalizedRerootChildren start)
    (slot : Nat)
    (referenceAddress : reference.occurrence.1.address =
      start.occurrence.1.address ++ [slot])
    (referenceNotDouble : ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge reference.occurrence) :
    input.ExtendedDemandRequestStep cursor reference := by
  have referenceBudget := input.localizedRerootCursorBudget_outward_child start reference
    referencePresent slot referenceAddress
  have referenceGrade := input.localizedCIPOccurrence_depthGrade reference.occurrence
  have cursorGrade := input.localizedCIPOccurrence_depthGrade cursor.occurrence
  cases cursorPrevious : cursor.previous? with
  | none =>
      refine ExtendedDemandRequestStep.reset ?_
      rw [referenceBudget,
        input.localizedRerootCursorBudget_eq_address_add_of_none cursor cursorPrevious]
      rw [referenceAddress, startOccurrence, List.length_append] at referenceGrade
      simp only [List.length_singleton] at referenceGrade
      omega
  | some previous =>
      by_cases shorter : previous.1.address.length < cursor.occurrence.1.address.length
      · refine ExtendedDemandRequestStep.outwardNonDouble ?_ referenceNotDouble
        rw [referenceBudget,
          input.localizedRerootCursorBudget_eq_remaining_of_previous_shorter
            cursor previous cursorPrevious shorter]
        rw [referenceAddress, startOccurrence, List.length_append] at referenceGrade
        simp only [List.length_singleton] at referenceGrade
        omega
      · refine ExtendedDemandRequestStep.reset ?_
        rw [referenceBudget,
          input.localizedRerootCursorBudget_eq_address_add_of_not_shorter
            cursor previous cursorPrevious shorter]
        rw [referenceAddress, startOccurrence, List.length_append] at referenceGrade
        simp only [List.length_singleton] at referenceGrade
        omega




theorem extendedDemandRequestStep_left_of_outward
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor start reference : input.LocalizedRerootCursor fuel)
    (startLength : start.occurrence.1.address.length + 1 =
      cursor.occurrence.1.address.length)
    (referencePresent : reference ∈ input.executableLocalizedRerootChildren start)
    (slot : Nat)
    (referenceAddress : reference.occurrence.1.address =
      start.occurrence.1.address ++ [slot])
    (parentPhase : input.LocalizedOccurrenceHasRule3DoubleBondEdge cursor.occurrence)
    (referenceNotDouble : ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge reference.occurrence) :
    input.ExtendedDemandRequestStep cursor reference := by
  have referenceBudget := input.localizedRerootCursorBudget_outward_child start reference
    referencePresent slot referenceAddress
  have referenceLength : reference.occurrence.1.address.length =
      cursor.occurrence.1.address.length := by
    rw [referenceAddress, List.length_append]
    simp only [List.length_singleton]
    omega
  have referenceGrade := input.localizedCIPOccurrence_depthGrade reference.occurrence
  have cursorGrade := input.localizedCIPOccurrence_depthGrade cursor.occurrence
  cases cursorPrevious : cursor.previous? with
  | none =>
      refine ExtendedDemandRequestStep.reset ?_
      rw [referenceBudget,
        input.localizedRerootCursorBudget_eq_address_add_of_none cursor cursorPrevious]
      omega
  | some previous =>
      by_cases shorter : previous.1.address.length < cursor.occurrence.1.address.length
      · refine ExtendedDemandRequestStep.sameDepthPhase ?_ parentPhase referenceNotDouble
        rw [referenceBudget,
          input.localizedRerootCursorBudget_eq_remaining_of_previous_shorter
            cursor previous cursorPrevious shorter]
        omega
      · refine ExtendedDemandRequestStep.reset ?_
        rw [referenceBudget,
          input.localizedRerootCursorBudget_eq_address_add_of_not_shorter
            cursor previous cursorPrevious shorter]
        omega




theorem extendedDemandRequestStep_reset_of_deeper
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor start reference : input.LocalizedRerootCursor fuel)
    (cursorNonroot : 0 < cursor.occurrence.1.address.length)
    (referencePresent : reference ∈ input.executableLocalizedRerootChildren start)
    (slot : Nat)
    (referenceAddress : reference.occurrence.1.address =
      start.occurrence.1.address ++ [slot])
    (deeperBy : cursor.occurrence.1.address.length + 2 ≤
      reference.occurrence.1.address.length) :
    input.ExtendedDemandRequestStep cursor reference := by
  have referenceBudget := input.localizedRerootCursorBudget_outward_child start reference
    referencePresent slot referenceAddress
  have referenceGrade := input.localizedCIPOccurrence_depthGrade reference.occurrence
  have cursorGrade := input.localizedCIPOccurrence_depthGrade cursor.occurrence
  cases cursorPrevious : cursor.previous? with
  | none =>
      refine ExtendedDemandRequestStep.reset ?_
      rw [referenceBudget,
        input.localizedRerootCursorBudget_eq_address_add_of_none cursor cursorPrevious]
      omega
  | some previous =>
      by_cases shorter : previous.1.address.length < cursor.occurrence.1.address.length
      · refine ExtendedDemandRequestStep.reset ?_
        rw [referenceBudget,
          input.localizedRerootCursorBudget_eq_remaining_of_previous_shorter
            cursor previous cursorPrevious shorter]
        omega
      · refine ExtendedDemandRequestStep.reset ?_
        rw [referenceBudget,
          input.localizedRerootCursorBudget_eq_address_add_of_not_shorter
            cursor previous cursorPrevious shorter]
        omega

/-! ## Walk endpoints: terminal last cursor and exact last depth -/

/-- A one-element walk is a terminal topology at its start. -/
theorem declarativeWalk_terminal_of_length_one
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {start : input.LocalizedRerootCursor carrierFuel}
    {path : List (input.LocalizedRerootCursor carrierFuel)}
    (walk : input.DeclarativeLocalizedRule3CumulatedAxisWalk start path)
    (lengthOne : path.length = 1) :
    input.DeclarativeLocalizedRule3AxisTopology start .terminal := by
  cases walk with
  | terminal topology => exact topology
  | step _topology rest =>
      exfalso
      have positive := input.declarativeWalk_length_pos rest
      simp only [List.length_cons] at lengthOne
      omega

/-- The last cursor of a declarative walk is terminal. -/
theorem declarativeWalk_getLast?_terminal
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {start : input.LocalizedRerootCursor carrierFuel}
    {path : List (input.LocalizedRerootCursor carrierFuel)}
    (walk : input.DeclarativeLocalizedRule3CumulatedAxisWalk start path) :
    ∃ last, path.getLast? = some last ∧
      input.DeclarativeLocalizedRule3AxisTopology last .terminal := by
  induction walk with
  | terminal topology => exact ⟨_, rfl, topology⟩
  | step _topology rest ih =>
      obtain ⟨last, lastEq, lastTerminal⟩ := ih
      refine ⟨last, ?_, lastTerminal⟩
      rw [List.getLast?_cons, lastEq]
      rfl

/-! ## Common structural facts for one short-endpoint reference -/

/-- A reference of an actual short-endpoint request below a terminal cursor is an executable
outward child one slot below it, and carries no Rule-3 double-bond edge.  The outward address is
forced by the strict depth increase; the parent-side alternative would shorten the address. -/
theorem shortEndpointReference_facts_of_outward
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (start : input.LocalizedRerootCursor fuel)
    (reference : input.LocalizedRerootCursor fuel)
    (left right : input.Atom)
    (terminal : input.DeclarativeLocalizedRule3AxisTopology start .terminal)
    (startAtom : input.Atom)
    (startCurrent : start.occurrence.1.node.current? = some startAtom)
    (request : List (input.LocalizedRerootCursor fuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests left right start)
    (referenceMem : reference ∈ request)
    (outward : OutwardRerootCursor input start.occurrence reference) :
    reference ∈ input.executableLocalizedRerootChildren start ∧
      (∃ slot, reference.occurrence.1.address =
        start.occurrence.1.address ++ [slot]) ∧
      ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge reference.occurrence := by
  obtain ⟨_valid, ⟨_root, deeper⟩, _previous, _previousEq, _previousShorter⟩ := outward
  obtain ⟨first, second, firstCursor, secondCursor, _subs, firstSel, secondSel,
    _rootCmp, _constCmp, requestEq⟩ :=
    input.rule3ShortEndpointCallbackRequests_structure left right start request member
  rw [requestEq] at referenceMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at referenceMem
  obtain ⟨firstPresent, _firstPrevious, firstCurrent, firstPhysical⟩ :=
    input.localizedRule3ReferenceCursorExec?_facts start firstCursor first firstSel
  obtain ⟨secondPresent, _secondPrevious, secondCurrent, secondPhysical⟩ :=
    input.localizedRule3ReferenceCursorExec?_facts start secondCursor second secondSel
  rcases referenceMem with same | same
  · subst reference
    obtain ⟨_lengthEq, notDouble⟩ := input.terminal_child_at_successor_depth start terminal
      startAtom first startCurrent firstCursor firstPresent firstPhysical firstCurrent deeper
      (start.occurrence.1.address.length + 1) rfl
    refine ⟨firstPresent, ?_, notDouble⟩
    rcases input.executableLocalizedRerootChild_dichotomy start firstCursor firstPresent with
      ⟨parentLength, _parentAddress⟩ | ⟨slot, outwardAddress⟩
    · omega
    · exact ⟨slot, outwardAddress⟩
  · subst reference
    obtain ⟨_lengthEq, notDouble⟩ := input.terminal_child_at_successor_depth start terminal
      startAtom second startCurrent secondCursor secondPresent secondPhysical secondCurrent deeper
      (start.occurrence.1.address.length + 1) rfl
    refine ⟨secondPresent, ?_, notDouble⟩
    rcases input.executableLocalizedRerootChild_dichotomy start secondCursor secondPresent with
      ⟨parentLength, _parentAddress⟩ | ⟨slot, outwardAddress⟩
    · omega
    · exact ⟨slot, outwardAddress⟩

/-! ## The ordinary (one-bond spatial) route -/

/-- Every actual request reference of the ordinary short-circuit spatial route pays the callback
weight on the rank.  The unbranched graph domain excludes the branched alternative of the ordinary
certificate, so the certificate is the one-bond terminal axis.  Its left endpoint is the carrier
parent `P` of `O` and its right endpoint is `O` itself; the references sit at depth `|O|` and
`|O|+1` respectively. -/
theorem requestReference_facts_of_shortSpatial
    (input : CertifiedLocalizedCIPInput) (graphDomain : input.LocalizedUnbranchedDoubleBondGraph)
    {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (certificate : input.LocalizedRule3OrdinaryRouteCertificate cursor.occurrence)
    (_computed : input.localizedRule3OrdinaryRouteCertificate? cursor.occurrence = some certificate)
    (request : List (input.LocalizedRerootCursor fuel))
    (member : request ∈ input.rule3ShortSpatialCallbackRequests cursor.occurrence)
    (reference : input.LocalizedRerootCursor fuel)
    (referenceMem : reference ∈ request) :
    input.LocalizedRerootCursorValid reference ∧
      input.ExtendedDemandRequestStep cursor reference := by
  rcases certificate.valid with ⟨edge, route⟩
  rcases route with branched | oneBond
  · rcases branched with ⟨initial, first, second, rest, entryDecl⟩
    cases entryDecl with
    | branched physical branchTopology =>
        exact (input.noActualBranchedAxis_of_unbranchedDoubleBondGraph graphDomain fuel
          cursor.occurrence initial first second rest physical branchTopology).elim
  · obtain ⟨axis, axisDecl, countOne⟩ := oneBond
    rcases axisDecl with ⟨entryDecl, walkDecl, _reverseDecl, _rightPartnerCurrent,
      _rightCurrent⟩
    cases entryDecl with
    | terminalStart physical terminalLeft =>
        have physicalCopy := physical
        have lengthOne : axis.rightward.length = 1 := by
          have unfolded := countOne
          unfold LocalizedRule3CumulatedEndpointCursorFrame.doubleBondCount at unfolded
          exact unfolded
        have rightTerminal := input.declarativeWalk_terminal_of_length_one walkDecl lengthOne
        obtain ⟨_realO, occurrenceCurrent, _occurrenceParent, _bond, parentDecl,
          _leftCurrent, _leftPrevious, rightOccurrence, rightPrevious⟩ := physicalCopy
        have parentFacts := input.localizedCarrierParentFrame_facts cursor.occurrence.1
          axis.initial.leftCursor.occurrence.1 parentDecl
        have cursorNonroot : 0 < cursor.occurrence.1.address.length := by omega
        have rightCurrent : axis.initial.rightCursor.occurrence.1.node.current? =
            some axis.initial.right := by
          rw [rightOccurrence]
          exact occurrenceCurrent
        rcases input.rule3ShortSpatialCallbackRequests_structure cursor.occurrence request
          member with ⟨frame, frameComputed, memberRest⟩
        have axisComputed :=
          input.localizedRule3PhysicalEndpointCursorFrame?_eq_some_of_declarative
            cursor.occurrence axis.initial physical
        have frameOriginal : input.localizedRule3PhysicalEndpointCursorFrame?
            cursor.occurrence = some frame := by
          rw [← input.localizedRule3PhysicalEndpointCursorFrameExec?_eq_original
            cursor.occurrence]
          exact frameComputed
        have frameEq : frame = axis.initial := by
          rw [frameOriginal] at axisComputed
          exact Option.some.inj axisComputed
        subst frame
        rcases memberRest with memberLeft | memberRight
        · have startActive := input.carrierParent_active_of_frame cursor.occurrence
            axis.initial physical
          have outward := input.rule3ShortEndpointCallbackRequests_left_outward
            axis.initial.leftCursor.occurrence axis.initial.leftCursor
            axis.initial.left axis.initial.right rfl le_rfl startActive request memberLeft
          obtain ⟨referencePresent, ⟨slot, referenceAddress⟩, referenceNotDouble⟩ :=
            input.shortEndpointReference_facts_of_outward axis.initial.leftCursor reference
              axis.initial.left axis.initial.right terminalLeft axis.initial.left
              _leftCurrent request memberLeft referenceMem (outward reference referenceMem)
          exact ⟨input.localizedRerootChild_valid axis.initial.leftCursor reference
              (input.executableLocalizedRerootChildren axis.initial.leftCursor)
              (input.executableLocalizedRerootChildren_declarative axis.initial.leftCursor)
              referencePresent,
            input.extendedDemandRequestStep_left_of_outward cursor axis.initial.leftCursor
              reference parentFacts.2.1 referencePresent slot referenceAddress edge
              referenceNotDouble⟩
        · have previousParent : axis.initial.leftCursor.occurrence.1 ∈
              input.localizedCarrierParentFrames (fuel := fuel)
                axis.initial.rightCursor.occurrence.1 := by
            rw [rightOccurrence]
            exact parentDecl
          have outward := input.rule3ShortEndpointCallbackRequests_right_outward_of_parent
            axis.initial.rightCursor.occurrence axis.initial.rightCursor
            axis.initial.leftCursor.occurrence rightPrevious previousParent rfl le_rfl
            axis.initial.right axis.initial.left request memberRight
          obtain ⟨referencePresent, ⟨slot, referenceAddress⟩, referenceNotDouble⟩ :=
            input.shortEndpointReference_facts_of_outward axis.initial.rightCursor reference
              axis.initial.right axis.initial.left rightTerminal axis.initial.right
              rightCurrent request memberRight referenceMem (outward reference referenceMem)
          have startOccurrence : axis.initial.rightCursor.occurrence.1 = cursor.occurrence.1 := by
            rw [rightOccurrence]
          exact ⟨input.localizedRerootChild_valid axis.initial.rightCursor reference
              (input.executableLocalizedRerootChildren axis.initial.rightCursor)
              (input.executableLocalizedRerootChildren_declarative axis.initial.rightCursor)
              referencePresent,
            input.extendedDemandRequestStep_right_of_outward cursor
              axis.initial.rightCursor reference startOccurrence cursorNonroot referencePresent
              slot referenceAddress referenceNotDouble⟩

/-! ## The odd-cumulene route -/

/-- Left-endpoint odd-cumulene references sit at the depth of `O` below the terminal carrier
parent; the source vertex is double-bonded and the reference is not. -/
theorem requestReference_facts_of_oddLeft
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
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
      input.ExtendedDemandRequestStep cursor reference := by
  obtain ⟨physicalDecl, terminalLeft, _walk, _reverse, _rightPartnerCurrent, _rightCurrent,
    _oneLt, _odd⟩ := decl
  have physicalCopy := physicalDecl
  obtain ⟨_realO, _occurrenceCurrent, _occurrenceParent, _bond, parentDecl, leftCurrent,
    _leftPrevious, _rightOccurrence, _rightPrevious⟩ := physicalCopy
  have parentFacts := input.localizedCarrierParentFrame_facts cursor.occurrence.1
    topology.initial.leftCursor.occurrence.1 parentDecl
  have startActive := input.carrierParent_active_of_frame cursor.occurrence topology.initial
    physicalDecl
  have outward := input.rule3ShortEndpointCallbackRequests_left_outward
    topology.initial.leftCursor.occurrence topology.initial.leftCursor
    topology.initial.left topology.initial.right rfl le_rfl startActive request member
  obtain ⟨referencePresent, ⟨slot, referenceAddress⟩, referenceNotDouble⟩ :=
    input.shortEndpointReference_facts_of_outward topology.initial.leftCursor reference
      topology.initial.left topology.initial.right terminalLeft topology.initial.left
      leftCurrent request member referenceMem (outward reference referenceMem)
  exact ⟨input.localizedRerootChild_valid topology.initial.leftCursor reference
      (input.executableLocalizedRerootChildren topology.initial.leftCursor)
      (input.executableLocalizedRerootChildren_declarative topology.initial.leftCursor)
      referencePresent,
    input.extendedDemandRequestStep_left_of_outward cursor topology.initial.leftCursor
      reference parentFacts.2.1 referencePresent slot referenceAddress edge
      referenceNotDouble⟩






theorem requestReference_facts_of_oddRight
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame fuel)
    (decl : input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame cursor.occurrence
      topology)
    (request : List (input.LocalizedRerootCursor fuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests topology.right
      topology.rightPartner topology.rightCursor)
    (reference : input.LocalizedRerootCursor fuel)
    (referenceMem : reference ∈ request) :
    input.LocalizedRerootCursorValid reference ∧
      input.ExtendedDemandRequestStep cursor reference := by
  obtain ⟨physicalDecl, _terminalLeft, walkDecl, reverseDecl, _rightPartnerCurrent,
    rightCurrent, _oneLt, _odd⟩ := decl
  obtain ⟨_realO, _occurrenceCurrent, _occurrenceParent, _bond, parentDecl, _leftCurrent,
    _leftPrevious, rightOccurrence, rightPrevious⟩ := physicalDecl
  obtain ⟨reverseRest, reverseEq⟩ := reverseDecl
  have parentFacts := input.localizedCarrierParentFrame_facts cursor.occurrence.1
    topology.initial.leftCursor.occurrence.1 parentDecl
  have cursorNonroot : 0 < cursor.occurrence.1.address.length := by omega
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
  have partnerMem : topology.rightPartnerCursor ∈ topology.rightward := by
    rw [← List.mem_reverse, reverseEq]
    simp
  have partnerOutward := allOutward topology.rightPartnerCursor partnerMem
  obtain ⟨partnerValid, partnerDependency, partnerPrevious, partnerPreviousEq,
    partnerShorter⟩ := partnerOutward
  have lastPair := input.declarativeWalk_reverse_last_pair
    topology.initial.rightCursor topology.rightward walkDecl
    topology.rightCursor topology.rightPartnerCursor reverseRest reverseEq
  have edge : E input topology.rightPartnerCursor topology.rightCursor := lastPair.1
  have rightPrevious' : topology.rightCursor.previous? =
      some topology.rightPartnerCursor.occurrence := lastPair.2
  obtain ⟨stepDropLast, stepLength, stepRoot, _stepPrevious, _stepValid⟩ :=
    input.outward_edge topology.rightPartnerCursor topology.rightCursor partnerValid
      partnerPrevious partnerPreviousEq partnerShorter edge
  have previousParent : topology.rightPartnerCursor.occurrence.1 ∈
      input.localizedCarrierParentFrames (fuel := fuel)
        topology.rightCursor.occurrence.1 := by
    rw [localizedCarrierParentFrames, List.mem_filter]
    refine ⟨topology.rightPartnerCursor.occurrence.2, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨stepRoot.symm, by omega⟩, stepDropLast.symm⟩
  have outward := input.rule3ShortEndpointCallbackRequests_right_outward_of_parent
    topology.rightCursor.occurrence topology.rightCursor
    topology.rightPartnerCursor.occurrence rightPrevious' previousParent rfl le_rfl
    topology.right topology.rightPartner request member
  have lastEq : topology.rightward.getLast? = some topology.rightCursor := by
    rw [List.getLast?_eq_head?_reverse, reverseEq]
    rfl
  obtain ⟨last, lastComputed, lastTerminal⟩ :=
    input.declarativeWalk_getLast?_terminal walkDecl
  have lastIsRight : last = topology.rightCursor :=
    Option.some.inj (lastComputed.symm.trans lastEq)
  have terminalRight : input.DeclarativeLocalizedRule3AxisTopology topology.rightCursor
      .terminal := by
    rw [← lastIsRight]
    exact lastTerminal
  obtain ⟨referencePresent, ⟨slot, referenceAddress⟩, _referenceNotDouble⟩ :=
    input.shortEndpointReference_facts_of_outward topology.rightCursor reference
      topology.right topology.rightPartner terminalRight topology.right rightCurrent
      request member referenceMem (outward reference referenceMem)
  have partnerDeeper : topology.initial.leftCursor.occurrence.1.address.length <
      topology.rightPartnerCursor.occurrence.1.address.length := partnerDependency.2
  have parentLength : topology.initial.leftCursor.occurrence.1.address.length + 1 =
      cursor.occurrence.1.address.length := parentFacts.2.1
  have referenceDepth : cursor.occurrence.1.address.length + 2 ≤
      reference.occurrence.1.address.length := by
    rw [referenceAddress, List.length_append]
    simp only [List.length_singleton]
    omega
  exact ⟨input.localizedRerootChild_valid topology.rightCursor reference
      (input.executableLocalizedRerootChildren topology.rightCursor)
      (input.executableLocalizedRerootChildren_declarative topology.rightCursor)
      referencePresent,
    input.extendedDemandRequestStep_reset_of_deeper cursor topology.rightCursor reference
      cursorNonroot referencePresent slot referenceAddress referenceDepth⟩

/-! ## Every actual extended request reference -/

/-- Every cursor of every request actually emitted by `rule3ExtendedNodeCallbackRequests O` is a
valid reroot orientation and pays the extended demand callback weight on the rank.  The route
branch is the actual certificate branch of the extended evaluator; the joint-failure branch emits
no request at all. -/
theorem requestReference_facts_of_extendedRequest
    (input : CertifiedLocalizedCIPInput) (graphDomain : input.LocalizedUnbranchedDoubleBondGraph)
    {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (request : List (input.LocalizedRerootCursor fuel))
    (member : request ∈ input.rule3ExtendedNodeCallbackRequests cursor.occurrence)
    (reference : input.LocalizedRerootCursor fuel)
    (referenceMem : reference ∈ request) :
    input.LocalizedRerootCursorValid reference ∧
      input.ExtendedDemandRequestStep cursor reference := by
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
          · exact input.requestReference_facts_of_oddLeft cursor topology sound
              certificate.valid.1 request leftMember reference referenceMem
          · exact input.requestReference_facts_of_oddRight cursor topology sound
              request rightMember reference referenceMem
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
          exact input.requestReference_facts_of_shortSpatial graphDomain cursor certificate
            ordinary request member reference referenceMem







theorem extendedDemandRankPhase_of_unbranched
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (graphDomain : input.LocalizedUnbranchedDoubleBondGraph) :
    input.ExtendedDemandRankPhase
      (input.LocalizedUnbranchedExtendedDemandDomain (fuel := fuel)) where
  unbranched := input.unbranchedDoubleBondGraph_iff_neighbourDomain.mp graphDomain
  valid := fun _cursor member => member
  childDomain := by
    intro cursor _member child present
    exact input.localizedRerootChild_valid cursor child
      (input.executableLocalizedRerootChildren cursor)
      (input.executableLocalizedRerootChildren_declarative cursor) present
  requestDomain := by
    intro cursor _member request requested reference inRequest
    exact (input.requestReference_facts_of_extendedRequest graphDomain cursor request requested
      reference inRequest).1
  requestStep := by
    intro cursor _member request requested reference inRequest
    exact (input.requestReference_facts_of_extendedRequest graphDomain cursor request requested
      reference inRequest).2

/-! ## Actual graph-domain consequences -/

/-- Actual graph-domain acyclicity of the extended demand graph for every list of valid reroot
orientations. -/
theorem unbranchedActualExtendedRule3DemandAcyclic
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (graphDomain : input.LocalizedUnbranchedDoubleBondGraph)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root) :
    input.ExtendedRule3DemandAcyclic roots :=
  input.unbranchedExtendedRule3DemandAcyclic_of_phase
    (input.extendedDemandRankPhase_of_unbranched (fuel := fuel) graphDomain) roots rootValid

/-- Actual graph-domain weighted-demand acyclicity. -/
theorem unbranchedActualWeightedExtendedDemandAcyclic
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (graphDomain : input.LocalizedUnbranchedDoubleBondGraph)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root) :
    Acyclic (input.extendedWeightedDemandGraph fuel) roots :=
  input.unbranchedWeightedExtendedDemandAcyclic_of_phase
    (input.extendedDemandRankPhase_of_unbranched (fuel := fuel) graphDomain) roots rootValid


theorem unbranchedActualExtendedRule3DemandPlan_total
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (graphDomain : input.LocalizedUnbranchedDoubleBondGraph)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root) :
    ∃ plan, input.prepareExtendedRule3DemandPlan roots = .ok plan :=
  input.unbranchedExtendedRule3DemandPlan_total_of_phase
    (input.extendedDemandRankPhase_of_unbranched (fuel := fuel) graphDomain) roots rootValid

/-- Actual graph-domain discovery totality of the existing DFS at the rank budget
`6 * (fuel + 1) + 3`.  This bounds discovery, not the evaluator. -/
theorem unbranchedActualExtendedRule3DemandDiscovery_total
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (graphDomain : input.LocalizedUnbranchedDoubleBondGraph)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root) :
    ∃ table,
      roots.foldlM (fun known root =>
        input.discoverExtendedRule3DemandRanks (6 * (fuel + 1) + 3) [] known root) [] =
          .ok table ∧
      input.ExtendedRule3DemandRankTableValid table ∧
      (∀ root ∈ roots, root ∈ table.map Prod.fst) :=
  input.unbranchedExtendedRule3DemandDiscovery_total_of_phase
    (input.extendedDemandRankPhase_of_unbranched (fuel := fuel) graphDomain) roots rootValid

/-! ## The actual rank witness and its bundled consequences -/




def unbranchedActualExtendedDemandRank
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (graphDomain : input.LocalizedUnbranchedDoubleBondGraph)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root) :
    input.UnbranchedExtendedDemandRank fuel roots where
  unbranched := input.unbranchedDoubleBondInput_of_graphDomain graphDomain
  rootValid := rootValid
  domain := input.LocalizedUnbranchedExtendedDemandDomain (fuel := fuel)
  measure := fun cursor => input.extendedDemandRank cursor
  rootDomain := rootValid
  decreases := by
    intro cursor member child edge
    exact input.extendedDemandRank_successor_decreases
      (input.extendedDemandRankPhase_of_unbranched (fuel := fuel) graphDomain)
      cursor member child edge

/-- Bundled actual graph-domain totality for the extended constructor. -/
theorem unbranchedActualExtendedDemandTotality
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (graphDomain : input.LocalizedUnbranchedDoubleBondGraph)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root) :
    ∃ plan : input.ExtendedRule3DemandPlan roots,
      input.prepareExtendedRule3DemandPlan roots = .ok plan ∧
      input.ExtendedRule3DemandAcyclic roots ∧
      Acyclic (input.extendedWeightedDemandGraph fuel) roots ∧
      (∀ root ∈ roots, root ∈ plan.ranks.vertices) ∧
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
            frame) :=
  input.unbranchedExtendedDemandTotality roots
    (input.unbranchedActualExtendedDemandRank graphDomain roots rootValid)

/-- The actual constructor never returns a cycle refusal on the unbranched graph domain. -/
theorem unbranchedActualExtendedDemandPlan_noCycleError
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (graphDomain : input.LocalizedUnbranchedDoubleBondGraph)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root) :
    ∀ cursor, input.prepareExtendedRule3DemandPlan roots ≠ .error (.cycle cursor) :=
  input.unbranchedExtendedDemandPlan_noCycleError roots
    (input.unbranchedActualExtendedDemandRank graphDomain roots rootValid)

/-- The actual constructor returns no error at all on the unbranched graph domain. -/
theorem unbranchedActualExtendedDemandPlan_noError
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (graphDomain : input.LocalizedUnbranchedDoubleBondGraph)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root)
    (failure : input.Rule3DemandDiscoveryFailure fuel) :
    input.prepareExtendedRule3DemandPlan roots ≠ .error failure :=
  input.unbranchedExtendedDemandPlan_noError roots
    (input.unbranchedActualExtendedDemandRank graphDomain roots rootValid) failure

/-- The preflight-pruned constructor is total on the unbranched graph domain. -/
theorem unbranchedActualPreflightPlan_total
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (graphDomain : input.LocalizedUnbranchedDoubleBondGraph)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root) :
    ∃ plan, input.preparePreflightExtendedDemandPlan roots = .ok plan :=
  input.unbranchedPreflightPlan_total roots
    (input.unbranchedActualExtendedDemandRank graphDomain roots rootValid)

/-- The preflight constructor never returns a cycle refusal on the unbranched graph domain. -/
theorem unbranchedActualPreflightPlan_noCycleError
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (graphDomain : input.LocalizedUnbranchedDoubleBondGraph)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root) :
    ∀ cursor, input.preparePreflightExtendedDemandPlan roots ≠ .error (.cycle cursor) :=
  input.unbranchedPreflightPlan_noCycleError roots
    (input.unbranchedActualExtendedDemandRank graphDomain roots rootValid)

/-- Bundled preflight result on the unbranched graph domain. -/
theorem unbranchedActualPreflightTotality
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (graphDomain : input.LocalizedUnbranchedDoubleBondGraph)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root)
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) :
    ∃ plan : Plan (input.preflightExtendedWeightedDemandGraph fuel) roots,
      input.preparePreflightExtendedDemandPlan roots = .ok plan ∧
      Acyclic (input.preflightExtendedWeightedDemandGraph fuel) roots ∧
      (∀ root ∈ roots, root ∈ plan.ranks.vertices) ∧
      plan.bound = listHeight plan.ranks.height roots + 1 ∧
      (∀ budget, plan.bound ≤ budget →
        preflightExtendedDemandEvaluate plan target view =
          input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget roots) ∧
      (∀ frame, preflightExtendedDemandEvaluate plan target view = some frame →
        input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view plan.bound roots
          frame) :=
  input.unbranchedPreflightTotality roots
    (input.unbranchedActualExtendedDemandRank graphDomain roots rootValid) target view

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedDoubleBondNeighbourFinset_card_eq_orderTwoNeighbors_length
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unbranchedDoubleBondGraph_iff_neighbourDomain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unbranchedDoubleBondInput_of_graphDomain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootCursorBudget_eq_address_add_of_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootCursorBudget_eq_remaining_of_previous_shorter
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootCursorBudget_eq_address_add_of_not_shorter
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootCursorBudget_outward_child
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendedDemandRequestStep_right_of_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendedDemandRequestStep_left_of_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendedDemandRequestStep_reset_of_deeper
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeWalk_terminal_of_length_one
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeWalk_getLast?_terminal
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.shortEndpointReference_facts_of_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.requestReference_facts_of_shortSpatial
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.requestReference_facts_of_oddLeft
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.requestReference_facts_of_oddRight
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.requestReference_facts_of_extendedRequest
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendedDemandRankPhase_of_unbranched
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unbranchedActualExtendedRule3DemandAcyclic
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unbranchedActualWeightedExtendedDemandAcyclic
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unbranchedActualExtendedRule3DemandPlan_total
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unbranchedActualExtendedRule3DemandDiscovery_total
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unbranchedActualExtendedDemandRank
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unbranchedActualExtendedDemandTotality
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unbranchedActualExtendedDemandPlan_noCycleError
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unbranchedActualExtendedDemandPlan_noError
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unbranchedActualPreflightPlan_total
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unbranchedActualPreflightPlan_noCycleError
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.unbranchedActualPreflightTotality
