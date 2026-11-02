import TetraStereo.OneCenter.LocalizedUnbranchedRule3RequestPhase
import TetraStereo.OneCenter.LocalizedUnbranchedActualDemandTermination
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput




































/-! ## Physical copies -/





theorem physicalReferenceProvenance_extend_copyIndex_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (node : OfficialCIPNode V) (next : V) (copyIndex : Nat)
    (physical : LocalizedRule3PhysicalReferenceProvenance
      (node.extend next copyIndex).provenance) :
    copyIndex = 0 := by
  by_contra positive
  have provenanceEq : (node.extend next copyIndex).provenance =
      OfficialCIPNodeProvenance.multipleBondDuplicate node.depth := by
    rw [OfficialCIPNode.extend_provenance]
    exact OfficialCIPNode.childProvenance_copy_pos node next positive
  rw [provenanceEq] at physical
  exact physical

/-! ## Geometry of the odd-cumulene axis walk -/

/-- **No inverse edges along the realized axis walk.**  Every cursor of a declarative cumulated
axis walk whose start cursor is cut at its carrier parent has an incoming cut that is *that
carrier parent*: a physically earlier occurrence of strictly smaller address length.  The walk
therefore never traverses an edge backwards.  This is the trace invariant used by the right
endpoint request gate; it assumes nothing about the global history of the carrier. -/
theorem declarativeWalk_incoming_carrierParent
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {start : input.LocalizedRerootCursor carrierFuel}
    {path : List (input.LocalizedRerootCursor carrierFuel)}
    (walk : input.DeclarativeLocalizedRule3CumulatedAxisWalk start path) :
    ∀ (previous : input.LocalizedCIPOccurrence carrierFuel),
      start.previous? = some previous →
      previous.1 ∈ input.localizedCarrierParentFrames (fuel := carrierFuel)
        start.occurrence.1 →
      previous.1.address.length < start.occurrence.1.address.length →
      ∀ cursor ∈ path,
        ∃ incoming : input.LocalizedCIPOccurrence carrierFuel,
          cursor.previous? = some incoming ∧
            incoming.1 ∈ input.localizedCarrierParentFrames (fuel := carrierFuel)
              cursor.occurrence.1 ∧
            incoming.1.address.length < cursor.occurrence.1.address.length := by
  induction walk with
  | terminal _topology =>
      intro previous startPrevious previousParent previousShorter cursor cursorMem
      simp only [List.mem_singleton] at cursorMem
      subst cursor
      exact ⟨previous, startPrevious, previousParent, previousShorter⟩
  | step topology restWalk ih =>
      rename_i stepStart stepNext stepTail
      intro previous startPrevious previousParent previousShorter cursor cursorMem
      rw [List.mem_cons] at cursorMem
      rcases cursorMem with cursorEq | inTail
      · subst cursor
        exact ⟨previous, startPrevious, previousParent, previousShorter⟩
      · have startValid : input.LocalizedRerootCursorValid stepStart := by
          unfold LocalizedRerootCursorValid
          rw [startPrevious]
          exact input.mem_localizedRerootNeighborFrames_symm stepStart.occurrence previous.1
            (by
              rw [localizedRerootNeighborFrames, List.mem_append]
              exact Or.inl previousParent)
        have edge : E input stepStart stepNext :=
          declarativeLinearStep_edge input topology
        obtain ⟨stepDropLast, _stepLength, stepRoot, stepPrevious, _stepValid⟩ :=
          input.outward_edge stepStart stepNext startValid previous startPrevious
            previousShorter edge
        have nextParent : stepStart.occurrence.1 ∈
            input.localizedCarrierParentFrames (fuel := carrierFuel)
              stepNext.occurrence.1 := by
          rw [localizedCarrierParentFrames, List.mem_filter]
          refine ⟨stepStart.occurrence.2, ?_⟩
          simp only [Bool.and_eq_true, beq_iff_eq]
          exact ⟨⟨stepRoot.symm, by omega⟩, stepDropLast.symm⟩
        have nextShorter : stepStart.occurrence.1.address.length <
            stepNext.occurrence.1.address.length := by
          have stepLength := input.outward_edge stepStart stepNext startValid previous
            startPrevious previousShorter edge
          omega
        exact ih stepStart.occurrence stepPrevious nextParent nextShorter cursor inTail

/-- The realized odd-cumulene rightward walk never traverses an inverse edge: each of its cursors
is entered from its carrier parent.  This is the frame-level form of
`declarativeWalk_incoming_carrierParent`, driven by the physical initial frame `P -> O`. -/
theorem oddCumuleneWalk_incoming_carrierParent
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (decl : input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame
      cursor.occurrence topology) :
    ∀ walkCursor ∈ topology.rightward,
      ∃ incoming : input.LocalizedCIPOccurrence carrierFuel,
        walkCursor.previous? = some incoming ∧
          incoming.1 ∈ input.localizedCarrierParentFrames (fuel := carrierFuel)
            walkCursor.occurrence.1 ∧
          incoming.1.address.length < walkCursor.occurrence.1.address.length := by
  obtain ⟨physicalDecl, _terminalLeft, walkDecl, _reverseDecl, _rightPartnerCurrent,
    _rightCurrent, _oneLt, _odd⟩ := decl
  obtain ⟨_realO, _occurrenceCurrent, _occurrenceParent, _bond, parentDecl, _leftCurrent,
    _leftPrevious, rightOccurrence, rightPrevious⟩ := physicalDecl
  have parentFacts := input.localizedCarrierParentFrame_facts cursor.occurrence.1
    topology.initial.leftCursor.occurrence.1 parentDecl
  have initialParent : topology.initial.leftCursor.occurrence.1 ∈
      input.localizedCarrierParentFrames (fuel := carrierFuel)
        topology.initial.rightCursor.occurrence.1 := by
    rw [rightOccurrence]
    exact parentDecl
  have initialShorter : topology.initial.leftCursor.occurrence.1.address.length <
      topology.initial.rightCursor.occurrence.1.address.length := by
    rw [rightOccurrence]
    have parentLength : topology.initial.leftCursor.occurrence.1.address.length + 1 =
        cursor.occurrence.1.address.length := parentFacts.2.1
    omega
  exact input.declarativeWalk_incoming_carrierParent walkDecl
    topology.initial.leftCursor.occurrence rightPrevious initialParent initialShorter

/-- **The odd cumulene has at least three physical double bonds.**  The realized frame is accepted
only when its double-bond count is odd and greater than one, hence `3 ≤ rightward.length`. -/
theorem oddCumuleneWalk_minLength
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (decl : input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame
      cursor.occurrence topology) :
    3 ≤ topology.rightward.length := by
  have bounded : 1 < topology.rightward.length := by
    have unfolded := decl.2.2.2.2.2.2.1
    unfold LocalizedRule3OddCumuleneEndpointCursorFrame.doubleBondCount at unfolded
    exact unfolded
  have oddCount : Odd topology.rightward.length := by
    have unfolded := decl.2.2.2.2.2.2.2
    unfold LocalizedRule3OddCumuleneEndpointCursorFrame.doubleBondCount at unfolded
    exact unfolded
  obtain ⟨half, halfEq⟩ := oddCount
  omega

/-! ## The terminal right endpoint -/

/-- The terminal axis topology at the right endpoint of the realized odd-cumulene walk. -/
theorem oddRightEndpoint_terminal
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (decl : input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame
      cursor.occurrence topology) :
    input.DeclarativeLocalizedRule3AxisTopology topology.rightCursor .terminal := by
  obtain ⟨_physical, _terminalLeft, walkDecl, reverseDecl, _rightPartnerCurrent,
    _rightCurrent, _oneLt, _odd⟩ := decl
  obtain ⟨_reverseRest, reverseEq⟩ := reverseDecl
  have lastEq : topology.rightward.getLast? = some topology.rightCursor := by
    rw [List.getLast?_eq_head?_reverse, reverseEq]
    rfl
  obtain ⟨last, lastComputed, lastTerminal⟩ :=
    input.declarativeWalk_getLast?_terminal walkDecl
  have lastIsRight : last = topology.rightCursor :=
    Option.some.inj (lastComputed.symm.trans lastEq)
  rw [← lastIsRight]
  exact lastTerminal

/-- **The right endpoint is strictly deeper than the source occurrence.**  The walk begins at `O`
(= the initial right cursor) and advances one address slot per `.linear` step, so the terminal
right cursor is at least one slot below `O`. -/
theorem oddRightEndpoint_deeper
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (decl : input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame
      cursor.occurrence topology) :
    cursor.occurrence.1.address.length <
      topology.rightCursor.occurrence.1.address.length := by
  obtain ⟨physicalDecl, _terminalLeft, walkDecl, reverseDecl, _rightPartnerCurrent,
    _rightCurrent, _oneLt, _odd⟩ := decl
  obtain ⟨_realO, _occurrenceCurrent, _occurrenceParent, _bond, parentDecl, _leftCurrent,
    _leftPrevious, rightOccurrence, rightPrevious⟩ := physicalDecl
  obtain ⟨reverseRest, reverseEq⟩ := reverseDecl
  have parentFacts := input.localizedCarrierParentFrame_facts cursor.occurrence.1
    topology.initial.leftCursor.occurrence.1 parentDecl
  have parentInNeighbors : topology.initial.leftCursor.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel) cursor.occurrence.1 := by
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
  obtain ⟨_stepDropLast, stepLength, _stepRoot, _stepPrevious, _stepValid⟩ :=
    input.outward_edge topology.rightPartnerCursor topology.rightCursor partnerValid
      partnerPrevious partnerPreviousEq partnerShorter edge
  have partnerDeeper : topology.initial.leftCursor.occurrence.1.address.length <
      topology.rightPartnerCursor.occurrence.1.address.length := partnerDependency.2
  have parentLength : topology.initial.leftCursor.occurrence.1.address.length + 1 =
      cursor.occurrence.1.address.length := parentFacts.2.1
  omega

/-- Successor-depth form of `oddRightEndpoint_deeper`. -/
theorem oddRightEndpoint_depth
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (decl : input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame
      cursor.occurrence topology) :
    cursor.occurrence.1.address.length + 1 ≤
      topology.rightCursor.occurrence.1.address.length :=
  input.oddRightEndpoint_deeper cursor topology decl

/-! ## The source occurrence is an actual double-bond edge -/

/-- The source occurrence of the right request is a real atom whose declared parent edge is a
double bond: `LocalizedOccurrenceHasRule3DoubleBondEdge cursor.occurrence`.  This is derived from
the actual initial physical frame `P -> O`, with no global degree hypothesis. -/
theorem oddRightRequest_sourceDouble
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (decl : input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame
      cursor.occurrence topology) :
    input.LocalizedOccurrenceHasRule3DoubleBondEdge cursor.occurrence := by
  obtain ⟨physicalDecl, _terminalLeft, _walkDecl, _reverseDecl, _rightPartnerCurrent,
    _rightCurrent, _oneLt, _odd⟩ := decl
  obtain ⟨realO, occurrenceCurrent, occurrenceParent, bond, _parentDecl, _leftCurrent,
    _leftPrevious, _rightOccurrence, _rightPrevious⟩ := physicalDecl
  exact ⟨realO, topology.initial.right, topology.initial.left,
    occurrenceCurrent, occurrenceParent, bond⟩

/-! ## Physical provenance of the selected right references -/

/-- Every reference of an actual short-endpoint request below a cursor is a physical reference:
its provenance is `realAtom` or a `ringDuplicate`, never a multiple-bond duplicate or a
placeholder.  This uses only the structure of the emitted request list. -/
theorem rule3ShortEndpointRequest_referencePhysical
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpoint partner : input.Atom)
    (start : input.LocalizedRerootCursor fuel)
    (request : List (input.LocalizedRerootCursor fuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests endpoint partner start)
    (reference : input.LocalizedRerootCursor fuel)
    (referenceMem : reference ∈ request) :
    LocalizedRule3PhysicalReferenceProvenance reference.occurrence.1.node.provenance := by
  obtain ⟨first, second, firstCursor, secondCursor, _subs, firstSel, secondSel, _rootCmp,
    _constCmp, requestEq⟩ :=
    input.rule3ShortEndpointCallbackRequests_structure endpoint partner start request member
  have firstPhysical : LocalizedRule3PhysicalReferenceProvenance
      firstCursor.occurrence.1.node.provenance :=
    (input.localizedRule3ReferenceCursorExec?_facts start firstCursor first firstSel).2.2.2
  have secondPhysical : LocalizedRule3PhysicalReferenceProvenance
      secondCursor.occurrence.1.node.provenance :=
    (input.localizedRule3ReferenceCursorExec?_facts start secondCursor second secondSel).2.2.2
  rw [requestEq] at referenceMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at referenceMem
  rcases referenceMem with referenceEq | referenceEq
  · rw [referenceEq]
    exact firstPhysical
  · rw [referenceEq]
    exact secondPhysical

/-- The right-selected reference of the actual odd endpoint request is physical. -/
theorem oddRightRequest_referencePhysical
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame fuel)
    (decl : input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame
      cursor.occurrence topology)
    (request : List (input.LocalizedRerootCursor fuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests topology.right
      topology.rightPartner topology.rightCursor)
    (reference : input.LocalizedRerootCursor fuel)
    (referenceMem : reference ∈ request) :
    LocalizedRule3PhysicalReferenceProvenance reference.occurrence.1.node.provenance :=
  input.rule3ShortEndpointRequest_referencePhysical topology.right topology.rightPartner
    topology.rightCursor request member reference referenceMem

/-- A physical right-selected reference is either a genuine atom or a ring duplicate. -/
theorem oddRightRequest_referenceProvenance
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame fuel)
    (decl : input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame
      cursor.occurrence topology)
    (request : List (input.LocalizedRerootCursor fuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests topology.right
      topology.rightPartner topology.rightCursor)
    (reference : input.LocalizedRerootCursor fuel)
    (referenceMem : reference ∈ request) :
    reference.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∨
      ∃ distance, reference.occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.ringDuplicate distance :=
  input.physicalReferenceProvenance_cases reference
    (input.oddRightRequest_referencePhysical cursor topology decl request member reference
      referenceMem)

/-! ## The exact cursor facts of every emitted right request -/

/-- **Right-request cursor facts.**  Every reference actually selected by the odd right-endpoint
gate `rule3ShortEndpointCallbackRequests topology.right topology.rightPartner
topology.rightCursor` is

1. a valid reroot cursor;
2. rooted at the same carrier root as the source occurrence `O = cursor.occurrence`;
3. entered through an incoming cut of strictly smaller address length;
4. an executable child of the terminal right endpoint `topology.rightCursor`;
5. one slot below that endpoint;
6. at depth at least `O.depth + 2`.

No unbranched/degree-bound hypothesis, no history `Nodup`, and no graph acyclicity is used. -/
theorem oddRightRequest_cursorFacts
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame fuel)
    (decl : input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame
      cursor.occurrence topology)
    (request : List (input.LocalizedRerootCursor fuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests topology.right
      topology.rightPartner topology.rightCursor)
    (reference : input.LocalizedRerootCursor fuel)
    (referenceMem : reference ∈ request) :
    input.LocalizedRerootCursorValid reference ∧
      reference.occurrence.1.root = cursor.occurrence.1.root ∧
      (∃ previous : input.LocalizedCIPOccurrence fuel,
        reference.previous? = some previous ∧
          previous.1.address.length < reference.occurrence.1.address.length) ∧
      reference ∈ input.executableLocalizedRerootChildren topology.rightCursor ∧
      (∃ slot, reference.occurrence.1.address =
        topology.rightCursor.occurrence.1.address ++ [slot]) ∧
      cursor.occurrence.1.address.length + 2 ≤
        reference.occurrence.1.address.length := by
  obtain ⟨physicalDecl, _terminalLeft, walkDecl, reverseDecl, _rightPartnerCurrent,
    rightCurrent, _oneLt, _odd⟩ := decl
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
  have outwardRight := input.rule3ShortEndpointCallbackRequests_right_outward_of_parent
    topology.rightCursor.occurrence topology.rightCursor
    topology.rightPartnerCursor.occurrence rightPrevious' previousParent rfl le_rfl
    topology.right topology.rightPartner request member
  obtain ⟨referenceValid, referenceDependency, referencePrevious, referencePreviousEq,
    referenceShorter⟩ := outwardRight reference referenceMem
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
      request member referenceMem (outwardRight reference referenceMem)
  have partnerDeeper : topology.initial.leftCursor.occurrence.1.address.length <
      topology.rightPartnerCursor.occurrence.1.address.length := partnerDependency.2
  have parentLength : topology.initial.leftCursor.occurrence.1.address.length + 1 =
      cursor.occurrence.1.address.length := parentFacts.2.1
  have referenceDepth : cursor.occurrence.1.address.length + 2 ≤
      reference.occurrence.1.address.length := by
    rw [referenceAddress, List.length_append]
    simp only [List.length_singleton]
    omega
  have rightRoot : topology.rightCursor.occurrence.1.root = cursor.occurrence.1.root :=
    stepRoot.trans (partnerDependency.1.trans parentFacts.1)
  exact ⟨referenceValid,
    referenceDependency.1.trans rightRoot,
    ⟨referencePrevious, referencePreviousEq, referenceShorter⟩,
    referencePresent, ⟨slot, referenceAddress⟩, referenceDepth⟩

/-- Packaged form of the cursor facts: every emitted right reference is an *outward cursor* of
the source occurrence itself.  This is the exact shape consumed by rank/decreasing-measure
arguments that treat the source occurrence as the target. -/
theorem oddRightRequest_outward
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame fuel)
    (decl : input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame
      cursor.occurrence topology)
    (request : List (input.LocalizedRerootCursor fuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests topology.right
      topology.rightPartner topology.rightCursor)
    (reference : input.LocalizedRerootCursor fuel)
    (referenceMem : reference ∈ request) :
    OutwardRerootCursor input cursor.occurrence reference := by
  obtain ⟨valid, root, ⟨previous, previousEq, previousShorter⟩, _present, _slot,
    depth⟩ :=
    input.oddRightRequest_cursorFacts cursor topology decl request member reference
      referenceMem
  exact ⟨valid, ⟨root, by omega⟩, previous, previousEq, previousShorter⟩

/-! ## The callback weight is paid -/





theorem oddRightRequest_extendedDemandStep
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame fuel)
    (decl : input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame
      cursor.occurrence topology)
    (request : List (input.LocalizedRerootCursor fuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests topology.right
      topology.rightPartner topology.rightCursor)
    (reference : input.LocalizedRerootCursor fuel)
    (referenceMem : reference ∈ request) :
    input.ExtendedDemandRequestStep cursor reference :=
  (input.requestReference_facts_of_oddRight cursor topology decl request member reference
    referenceMem).2

/-- Strict weighted-rank decrease at the source cursor: `rank reference + 2 ≤ rank cursor`. -/
theorem oddRightRequest_rankGap
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame fuel)
    (decl : input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame
      cursor.occurrence topology)
    (request : List (input.LocalizedRerootCursor fuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests topology.right
      topology.rightPartner topology.rightCursor)
    (reference : input.LocalizedRerootCursor fuel)
    (referenceMem : reference ∈ request) :
    input.extendedDemandRank reference + 2 ≤ input.extendedDemandRank cursor :=
  input.extendedDemandRank_request
    (input.oddRightRequest_extendedDemandStep cursor topology decl request member reference
      referenceMem)

/-- The unweighted cursor budget also drops by at least two along every emitted right request. -/
theorem oddRightRequest_budgetGap
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame fuel)
    (decl : input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame
      cursor.occurrence topology)
    (request : List (input.LocalizedRerootCursor fuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests topology.right
      topology.rightPartner topology.rightCursor)
    (reference : input.LocalizedRerootCursor fuel)
    (referenceMem : reference ∈ request) :
    input.localizedRerootCursorBudget reference + 2 ≤
      input.localizedRerootCursorBudget cursor := by
  obtain ⟨_valid, _root, _cut, present, ⟨slot, referenceAddress⟩, depth⟩ :=
    input.oddRightRequest_cursorFacts cursor topology decl request member reference
      referenceMem
  have referenceBudget := input.localizedRerootCursorBudget_outward_child
    topology.rightCursor reference present slot referenceAddress
  have referenceGrade := input.localizedCIPOccurrence_depthGrade reference.occurrence
  have cursorGrade := input.localizedCIPOccurrence_depthGrade cursor.occurrence
  have addressLength : reference.occurrence.1.address.length =
      topology.rightCursor.occurrence.1.address.length + 1 := by
    rw [referenceAddress, List.length_append]
    simp only [List.length_singleton]
  cases cursorPrevious : cursor.previous? with
  | none =>
      rw [referenceBudget,
        input.localizedRerootCursorBudget_eq_address_add_of_none cursor cursorPrevious]
      omega
  | some previous =>
      by_cases shorter : previous.1.address.length < cursor.occurrence.1.address.length
      · rw [referenceBudget,
          input.localizedRerootCursorBudget_eq_remaining_of_previous_shorter cursor previous
            cursorPrevious shorter]
        omega
      · rw [referenceBudget,
          input.localizedRerootCursorBudget_eq_address_add_of_not_shorter cursor previous
            cursorPrevious shorter]
        omega

/-! ## Entry point from the actually computed frame -/

/-- Cursor facts for the references of an actually *computed* odd-cumulene frame.  The caller
supplies the evaluator equality at the executable function
`localizedRule3OddCumuleneEndpointCursorFrameExec?`; the declarative frame is recovered through
the existing original/executable bridge and soundness theorem.  No condition on the surrounding
graph is required. -/
theorem oddRightRequest_cursorFacts_of_computed
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame fuel)
    (computed : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel fuel) cursor.occurrence = some topology)
    (request : List (input.LocalizedRerootCursor fuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests topology.right
      topology.rightPartner topology.rightCursor)
    (reference : input.LocalizedRerootCursor fuel)
    (referenceMem : reference ∈ request) :
    input.LocalizedRerootCursorValid reference ∧
      reference.occurrence.1.root = cursor.occurrence.1.root ∧
      (∃ previous : input.LocalizedCIPOccurrence fuel,
        reference.previous? = some previous ∧
          previous.1.address.length < reference.occurrence.1.address.length) ∧
      reference ∈ input.executableLocalizedRerootChildren topology.rightCursor ∧
      (∃ slot, reference.occurrence.1.address =
        topology.rightCursor.occurrence.1.address ++ [slot]) ∧
      cursor.occurrence.1.address.length + 2 ≤
        reference.occurrence.1.address.length := by
  have original : input.localizedRule3OddCumuleneEndpointCursorFrame?
      (input.localizedRule3CumulatedTraversalFuel fuel) cursor.occurrence = some topology := by
    rw [← input.localizedRule3OddCumuleneEndpointCursorFrameExec?_eq_original
      (input.localizedRule3CumulatedTraversalFuel fuel) cursor.occurrence]
    exact computed
  have sound := input.localizedRule3OddCumuleneEndpointCursorFrame?_sound
    (input.localizedRule3CumulatedTraversalFuel fuel) cursor.occurrence topology original
  exact input.oddRightRequest_cursorFacts cursor topology sound request member reference
    referenceMem

/-- Endpoint successor-depth bound for an actually computed odd-cumulene frame. -/
theorem oddRightEndpoint_depth_of_computed
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame fuel)
    (computed : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel fuel) cursor.occurrence = some topology) :
    cursor.occurrence.1.address.length + 1 ≤
      topology.rightCursor.occurrence.1.address.length := by
  have original : input.localizedRule3OddCumuleneEndpointCursorFrame?
      (input.localizedRule3CumulatedTraversalFuel fuel) cursor.occurrence = some topology := by
    rw [← input.localizedRule3OddCumuleneEndpointCursorFrameExec?_eq_original
      (input.localizedRule3CumulatedTraversalFuel fuel) cursor.occurrence]
    exact computed
  exact input.oddRightEndpoint_depth cursor topology
    (input.localizedRule3OddCumuleneEndpointCursorFrame?_sound
      (input.localizedRule3CumulatedTraversalFuel fuel) cursor.occurrence topology original)

/-- Outward support of the emitted right references for an actually computed odd-cumulene frame. -/
theorem oddRightRequest_outward_of_computed
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame fuel)
    (computed : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel fuel) cursor.occurrence = some topology)
    (request : List (input.LocalizedRerootCursor fuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests topology.right
      topology.rightPartner topology.rightCursor)
    (reference : input.LocalizedRerootCursor fuel)
    (referenceMem : reference ∈ request) :
    OutwardRerootCursor input cursor.occurrence reference := by
  have original : input.localizedRule3OddCumuleneEndpointCursorFrame?
      (input.localizedRule3CumulatedTraversalFuel fuel) cursor.occurrence = some topology := by
    rw [← input.localizedRule3OddCumuleneEndpointCursorFrameExec?_eq_original
      (input.localizedRule3CumulatedTraversalFuel fuel) cursor.occurrence]
    exact computed
  exact input.oddRightRequest_outward cursor topology
    (input.localizedRule3OddCumuleneEndpointCursorFrame?_sound
      (input.localizedRule3CumulatedTraversalFuel fuel) cursor.occurrence topology original)
    request member reference referenceMem




theorem oddRightRequest_budgetGap_of_computed
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (topology : input.LocalizedRule3OddCumuleneEndpointCursorFrame fuel)
    (computed : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel fuel) cursor.occurrence = some topology)
    (request : List (input.LocalizedRerootCursor fuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests topology.right
      topology.rightPartner topology.rightCursor)
    (reference : input.LocalizedRerootCursor fuel)
    (referenceMem : reference ∈ request) :
    input.localizedRerootCursorBudget reference + 2 ≤
      input.localizedRerootCursorBudget cursor := by
  have original : input.localizedRule3OddCumuleneEndpointCursorFrame?
      (input.localizedRule3CumulatedTraversalFuel fuel) cursor.occurrence = some topology := by
    rw [← input.localizedRule3OddCumuleneEndpointCursorFrameExec?_eq_original
      (input.localizedRule3CumulatedTraversalFuel fuel) cursor.occurrence]
    exact computed
  exact input.oddRightRequest_budgetGap cursor topology
    (input.localizedRule3OddCumuleneEndpointCursorFrame?_sound
      (input.localizedRule3CumulatedTraversalFuel fuel) cursor.occurrence topology original)
    request member reference referenceMem

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.physicalReferenceProvenance_extend_copyIndex_zero
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeWalk_incoming_carrierParent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.oddCumuleneWalk_incoming_carrierParent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.oddCumuleneWalk_minLength
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.oddRightEndpoint_terminal
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.oddRightEndpoint_deeper
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.oddRightEndpoint_depth
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.oddRightRequest_sourceDouble
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortEndpointRequest_referencePhysical
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.oddRightRequest_referencePhysical
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.oddRightRequest_referenceProvenance
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.oddRightRequest_cursorFacts
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.oddRightRequest_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.oddRightRequest_extendedDemandStep
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.oddRightRequest_rankGap
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.oddRightRequest_budgetGap
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.oddRightRequest_cursorFacts_of_computed
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.oddRightEndpoint_depth_of_computed
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.oddRightRequest_outward_of_computed
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.oddRightRequest_budgetGap_of_computed
