import TetraStereo.OneCenter.LocalizedRule3CumulatedFuelCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Exact zipper topology of perceived axial occurrence paths

This module closes the local seam between graph perception and the exhaustive occurrence zipper.
The first lemmas show that an uncut child reached after a certified incoming tree edge must be an
official outward child, and that every physical order-two zipper continuation is therefore one of
the molecule-level forward neighbours used by axial perception.
-/

namespace CertifiedLocalizedCIPInput

/-- Once the incoming parent coordinate is cut, every intended neighbour is one sibling-address
step outward. -/
theorem address_eq_append_singleton_of_mem_intended_of_incoming_parent
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (previous : input.LocalizedCIPOccurrence fuel) (incomingSlot : Nat)
    (previousExact : cursor.previous? = some previous)
    (cursorAddress : cursor.occurrence.1.address =
      previous.1.address ++ [incomingSlot])
    (frame : input.LocalizedCIPOccurrenceFrame)
    (present : frame ∈ input.intendedLocalizedRerootChildFrames cursor) :
    ∃ slot, frame.address = cursor.occurrence.1.address ++ [slot] := by
  have uncut := input.address_ne_previous_of_mem_intended
    cursor previous previousExact frame present
  have neighbor := input.mem_localizedRerootNeighborFrames_of_mem_intended
    cursor frame present
  have characterized :=
    (input.mem_localizedRerootNeighborFrames_iff cursor.occurrence.1 frame).mp neighbor
  rcases characterized.2 with ⟨_sameRoot, parent | outward⟩
  · have parentAddress : frame.address = previous.1.address := by
      rw [parent.2, cursorAddress]
      simp
    exact (uncut parentAddress).elim
  · have nonempty : frame.address ≠ [] := by
      intro empty
      rw [empty] at outward
      simp at outward
    let slot := frame.address.getLast nonempty
    refine ⟨slot, ?_⟩
    have rebuilt := List.dropLast_append_getLast nonempty
    calc
      frame.address = frame.address.dropLast ++ [slot] := rebuilt.symm
      _ = cursor.occurrence.1.address ++ [slot] := by rw [← outward.2]

-- Keep `sameRoot` explicit for source-compatible named theorem applications.
set_option linter.unusedVariables false in
/-- A physical zipper continuation from an embedded real occurrence is exactly a zero-copy
official child whose atom belongs to the graph perception walk's forward-neighbour list. -/
theorem localizedRule3AxisPhysicalContinuation_of_embedded_cursor
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor child : input.LocalizedRerootCursor fuel)
    (previousOccurrence : input.LocalizedCIPOccurrence fuel)
    (previous current : input.Atom) (incomingSlot : Nat)
    (previousExact : cursor.previous? = some previousOccurrence)
    (previousCurrent : previousOccurrence.1.node.current? = some previous)
    (cursorCurrent : cursor.occurrence.1.node.current? = some current)
    (cursorParent : cursor.occurrence.1.node.parent? =
      previousOccurrence.1.node.current?)
    (sameRoot : cursor.occurrence.1.root = previousOccurrence.1.root)
    (cursorAddress : cursor.occurrence.1.address =
      previousOccurrence.1.address ++ [incomingSlot])
    (children : List (input.LocalizedRerootCursor fuel))
    (childrenDerived : input.DeclarativeLocalizedRerootChildren cursor children)
    (childPresent : child ∈ children)
    (physical : input.LocalizedRule3AxisPhysicalContinuation cursor child) :
    ∃ next slot,
      child.occurrence.1.node.current? = some next ∧
      next ∈ input.localizedAxialForwardNeighbors previous current ∧
      child.occurrence.1.node = cursor.occurrence.1.node.extend next 0 ∧
      child.occurrence.1.address = cursor.occurrence.1.address ++ [slot] ∧
      (child.occurrence.1.node, slot) ∈
        (input.executableOfficialCIPChildren cursor.occurrence.1.node).zipIdx := by
  have childIntended : child.occurrence.1 ∈
      input.intendedLocalizedRerootChildFrames cursor := by
    rw [← childrenDerived.1]
    exact List.mem_map.mpr ⟨child, childPresent, rfl⟩
  obtain ⟨slot, childAddress⟩ :=
    input.address_eq_append_singleton_of_mem_intended_of_incoming_parent
      cursor previousOccurrence incomingSlot previousExact cursorAddress
      child.occurrence.1 childIntended
  have childRoot : child.occurrence.1.root = cursor.occurrence.1.root :=
    input.localizedRerootChildren_root_eq cursor child children
      childrenDerived childPresent
  obtain ⟨officialChild, officialAtSlot, childFrame⟩ :=
    input.declarativeLocalizedOccurrence_immediate_child
      ((input.mem_localizedOccurrences_iff fuel cursor.occurrence.1).mp
        cursor.occurrence.2)
      ((input.mem_localizedOccurrences_iff fuel child.occurrence.1).mp
        child.occurrence.2)
      childRoot slot childAddress
  have physicalProvenance :
      officialChild.provenance = OfficialCIPNodeProvenance.realAtom ∨
        ∃ distance, officialChild.provenance =
          OfficialCIPNodeProvenance.ringDuplicate distance := by
    have admitted := physical.2.1
    have childNode : child.occurrence.1.node = officialChild := by
      simpa using congrArg LocalizedCIPOccurrenceFrame.node childFrame
    rw [childNode] at admitted
    cases provenance : officialChild.provenance <;>
      simp [LocalizedRule3PhysicalReferenceProvenance, provenance] at admitted
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩
  obtain ⟨next, officialIdentity, notParent⟩ :=
    input.eq_extend_zero_and_not_parent_of_mem_executableOfficialCIPChildren
      cursor.occurrence.1.node officialChild
      (List.fst_mem_of_mem_zipIdx officialAtSlot) physicalProvenance
  have childNode : child.occurrence.1.node = officialChild := by
    simpa using congrArg LocalizedCIPOccurrenceFrame.node childFrame
  have childCurrent : child.occurrence.1.node.current? = some next := by
    rw [childNode, officialIdentity]
    rfl
  have doubleBond : input.moleculeGraph.bond current next = 2 := by
    have bondPart := physical.2.2
    rw [cursorCurrent, childCurrent] at bondPart
    exact bondPart
  have nextNePrevious : next ≠ previous := by
    intro identity
    subst next
    apply notParent
    rw [cursorParent, previousCurrent]
  refine ⟨next, slot, childCurrent,
    (input.mem_localizedAxialForwardNeighbors_iff previous current next).mpr
      ⟨doubleBond, nextNePrevious⟩, ?_, childAddress, ?_⟩
  · exact childNode.trans officialIdentity
  · simpa [childNode] using officialAtSlot

/-- An embedded outward occurrence is present in the exact executable zipper expansion of its
predecessor cursor. -/
theorem exists_localizedRerootChildren_containing_embedded_outward
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor child : input.LocalizedRerootCursor fuel)
    (previousOccurrence : input.LocalizedCIPOccurrence fuel)
    (incomingSlot childSlot : Nat)
    (cursorReal : cursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (previousExact : cursor.previous? = some previousOccurrence)
    (cursorAddress : cursor.occurrence.1.address =
      previousOccurrence.1.address ++ [incomingSlot])
    (childPrevious : child.previous? = some cursor.occurrence)
    (childRoot : child.occurrence.1.root = cursor.occurrence.1.root)
    (childAddress : child.occurrence.1.address =
      cursor.occurrence.1.address ++ [childSlot]) :
    ∃ children,
      input.localizedRerootChildren? cursor = some children ∧
      child ∈ children := by
  have childNeighbor : child.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := fuel) cursor.occurrence.1 := by
    rw [localizedRerootNeighborFrames, List.mem_append]
    apply Or.inr
    rw [localizedCarrierOutwardChildFrames, List.mem_filter]
    refine ⟨child.occurrence.2, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨childRoot, ?_⟩, ?_⟩
    · simp [childAddress]
    · simp [childAddress]
  have childNePrevious : child.occurrence.1.address ≠
      previousOccurrence.1.address := by
    intro equality
    have lengths := congrArg List.length equality
    rw [childAddress, cursorAddress] at lengths
    simp at lengths
  have childIntended : child.occurrence.1 ∈
      input.intendedLocalizedRerootChildFrames cursor := by
    unfold intendedLocalizedRerootChildFrames
    have nonduplicate : cursor.occurrence.1.node.isDuplicateLeaf = false := by
      simp [OfficialCIPNode.isDuplicateLeaf, cursorReal]
    rw [if_neg (by simpa using nonduplicate), previousExact]
    rw [List.mem_filter]
    exact ⟨childNeighbor, by simpa using childNePrevious⟩
  obtain ⟨children, childrenComputed⟩ :=
    input.exists_localizedRerootChildren cursor
  have childrenDerived := input.localizedRerootChildren?_sound
    cursor children childrenComputed
  have mappedPresent : child.occurrence.1 ∈
      children.map (fun candidate => candidate.occurrence.1) := by
    rw [childrenDerived.1]
    exact childIntended
  rw [List.mem_map] at mappedPresent
  rcases mappedPresent with ⟨candidate, candidatePresent, candidateFrame⟩
  have candidateOccurrence : candidate.occurrence = child.occurrence :=
    Subtype.ext candidateFrame
  have candidatePrevious : candidate.previous? = child.previous? := by
    exact (childrenDerived.2 candidate candidatePresent).trans childPrevious.symm
  have candidateIdentity : candidate = child :=
    LocalizedRerootCursor.ext input candidateOccurrence candidatePrevious
  subst candidate
  exact ⟨children, childrenComputed, candidatePresent⟩

/-- Exact physical-continuation list for one embedded path cursor.  The molecule-level forward
list controls the zipper cardinality: terminal perception gives `[]`; a singleton forward atom
and its embedded next cursor give exactly `[nextCursor]`. -/
theorem localizedRule3AxisPhysicalContinuationCursors?_of_embedded_forward
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (previousOccurrence : input.LocalizedCIPOccurrence fuel)
    (previous current : input.Atom) (incomingSlot : Nat)
    (previousExact : cursor.previous? = some previousOccurrence)
    (previousCurrent : previousOccurrence.1.node.current? = some previous)
    (cursorCurrent : cursor.occurrence.1.node.current? = some current)
    (cursorParent : cursor.occurrence.1.node.parent? =
      previousOccurrence.1.node.current?)
    (sameRoot : cursor.occurrence.1.root = previousOccurrence.1.root)
    (cursorAddress : cursor.occurrence.1.address =
      previousOccurrence.1.address ++ [incomingSlot]) :
    (forward : input.localizedAxialForwardNeighbors previous current = []) →
      input.localizedRule3AxisPhysicalContinuationCursors? cursor = some [] := by
  intro forward
  obtain ⟨children, childrenComputed⟩ :=
    input.exists_localizedRerootChildren cursor
  have childrenDerived := input.localizedRerootChildren?_sound
    cursor children childrenComputed
  have noPhysical : ∀ child,
      child ∉ input.localizedRule3AxisPhysicalContinuationCursors cursor children := by
    intro child childPresent
    have characterized :=
      (input.mem_localizedRule3AxisPhysicalContinuationCursors_iff
        cursor child children).mp childPresent
    obtain ⟨next, slot, childCurrent, nextForward, childNode,
      childAddress, childAtSlot⟩ :=
      input.localizedRule3AxisPhysicalContinuation_of_embedded_cursor
        cursor child previousOccurrence previous current incomingSlot
        previousExact previousCurrent cursorCurrent cursorParent sameRoot cursorAddress
        children childrenDerived characterized.1 characterized.2
    rw [forward] at nextForward
    simp at nextForward
  have filteredEmpty :
      input.localizedRule3AxisPhysicalContinuationCursors cursor children = [] :=
    List.eq_nil_iff_forall_not_mem.mpr noPhysical
  simp [localizedRule3AxisPhysicalContinuationCursors?, childrenComputed,
    filteredEmpty]

/-- Singleton form of the exact physical-continuation theorem. -/
theorem localizedRule3AxisPhysicalContinuationCursors?_of_embedded_singleton
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor nextCursor : input.LocalizedRerootCursor fuel)
    (previousOccurrence : input.LocalizedCIPOccurrence fuel)
    (previous current next : input.Atom) (incomingSlot nextSlot : Nat)
    (previousExact : cursor.previous? = some previousOccurrence)
    (previousCurrent : previousOccurrence.1.node.current? = some previous)
    (cursorCurrent : cursor.occurrence.1.node.current? = some current)
    (cursorParent : cursor.occurrence.1.node.parent? =
      previousOccurrence.1.node.current?)
    (sameRoot : cursor.occurrence.1.root = previousOccurrence.1.root)
    (cursorAddress : cursor.occurrence.1.address =
      previousOccurrence.1.address ++ [incomingSlot])
    (cursorReal : cursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (nextPrevious : nextCursor.previous? = some cursor.occurrence)
    (nextRoot : nextCursor.occurrence.1.root = cursor.occurrence.1.root)
    (nextAddress : nextCursor.occurrence.1.address =
      cursor.occurrence.1.address ++ [nextSlot])
    (nextReal : nextCursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (nextCurrent : nextCursor.occurrence.1.node.current? = some next)
    (forward : input.localizedAxialForwardNeighbors previous current = [next]) :
    input.localizedRule3AxisPhysicalContinuationCursors? cursor =
      some [nextCursor] := by
  obtain ⟨children, childrenComputed, nextPresent⟩ :=
    input.exists_localizedRerootChildren_containing_embedded_outward
      cursor nextCursor previousOccurrence incomingSlot nextSlot cursorReal
      previousExact cursorAddress nextPrevious nextRoot nextAddress
  have childrenDerived := input.localizedRerootChildren?_sound
    cursor children childrenComputed
  have nextDouble : input.moleculeGraph.bond current next = 2 :=
    (input.mem_localizedAxialForwardNeighbors_iff previous current next).mp
      (by simp [forward]) |>.1
  have nextPhysical : input.LocalizedRule3AxisPhysicalContinuation
      cursor nextCursor := by
    exact ⟨cursorReal, by simp [nextReal, LocalizedRule3PhysicalReferenceProvenance], by
      rw [cursorCurrent, nextCurrent]
      exact nextDouble⟩
  have nextFiltered : nextCursor ∈
      input.localizedRule3AxisPhysicalContinuationCursors cursor children :=
    (input.mem_localizedRule3AxisPhysicalContinuationCursors_iff
      cursor nextCursor children).mpr ⟨nextPresent, nextPhysical⟩
  have onlyNext : ∀ child,
      child ∈ input.localizedRule3AxisPhysicalContinuationCursors cursor children →
        child = nextCursor := by
    intro child childPresent
    have characterized :=
      (input.mem_localizedRule3AxisPhysicalContinuationCursors_iff
        cursor child children).mp childPresent
    obtain ⟨childAtom, childSlot, childCurrent, childForward, childNode,
      childAddress, childAtSlot⟩ :=
      input.localizedRule3AxisPhysicalContinuation_of_embedded_cursor
        cursor child previousOccurrence previous current incomingSlot
        previousExact previousCurrent cursorCurrent cursorParent sameRoot cursorAddress
        children childrenDerived characterized.1 characterized.2
    have childAtomIdentity : childAtom = next := by simpa [forward] using childForward
    subst childAtom
    have nextNode : nextCursor.occurrence.1.node =
        cursor.occurrence.1.node.extend next 0 := by
      have nextAtSlot := input.declarativeLocalizedOccurrence_immediate_child
        ((input.mem_localizedOccurrences_iff fuel cursor.occurrence.1).mp
          cursor.occurrence.2)
        ((input.mem_localizedOccurrences_iff fuel nextCursor.occurrence.1).mp
          nextCursor.occurrence.2)
        nextRoot nextSlot nextAddress
      rcases nextAtSlot with ⟨node, nodeAtSlot, frameIdentity⟩
      have nodeIdentity : node = nextCursor.occurrence.1.node := by
        simpa using congrArg LocalizedCIPOccurrenceFrame.node frameIdentity.symm
      subst node
      obtain ⟨atom, officialIdentity, notParent⟩ :=
        input.eq_extend_zero_and_not_parent_of_mem_executableOfficialCIPChildren
          cursor.occurrence.1.node nextCursor.occurrence.1.node
          (List.fst_mem_of_mem_zipIdx nodeAtSlot) (Or.inl nextReal)
      have atomIdentity : atom = next := by
        have observed := congrArg OfficialCIPNode.current? officialIdentity
        simpa [nextCurrent] using observed.symm
      subst atom
      exact officialIdentity
    have slotIdentity : childSlot = nextSlot :=
      input.physical_executableOfficialCIPChild_slot_unique
        cursor.occurrence.1.node nextCursor.occurrence.1.node childSlot nextSlot
        (by simpa [childNode, nextNode] using childAtSlot)
        (by
          have nextAtSlot := input.declarativeLocalizedOccurrence_immediate_child
            ((input.mem_localizedOccurrences_iff fuel cursor.occurrence.1).mp
              cursor.occurrence.2)
            ((input.mem_localizedOccurrences_iff fuel nextCursor.occurrence.1).mp
              nextCursor.occurrence.2)
            nextRoot nextSlot nextAddress
          rcases nextAtSlot with ⟨node, nodeAtSlot, frameIdentity⟩
          have nodeIdentity : node = nextCursor.occurrence.1.node := by
            simpa using congrArg LocalizedCIPOccurrenceFrame.node frameIdentity.symm
          simpa [nodeIdentity] using nodeAtSlot)
        (Or.inl nextReal)
    have frameIdentity : child.occurrence.1 = nextCursor.occurrence.1 :=
      input.declarativeLocalizedOccurrence_functional_at_root_address
        ((input.mem_localizedOccurrences_iff fuel child.occurrence.1).mp
          child.occurrence.2)
        ((input.mem_localizedOccurrences_iff fuel nextCursor.occurrence.1).mp
          nextCursor.occurrence.2)
        (by
          have childRoot := input.localizedRerootChildren_root_eq
            cursor child children childrenDerived characterized.1
          exact childRoot.trans nextRoot.symm)
        (by rw [childAddress, nextAddress, slotIdentity])
    have occurrenceIdentity : child.occurrence = nextCursor.occurrence :=
      Subtype.ext frameIdentity
    have previousIdentity : child.previous? = nextCursor.previous? := by
      rw [childrenDerived.2 child characterized.1, nextPrevious]
    exact LocalizedRerootCursor.ext input occurrenceIdentity previousIdentity
  have filteredNodup :
      (input.localizedRule3AxisPhysicalContinuationCursors cursor children).Nodup := by
    unfold localizedRule3AxisPhysicalContinuationCursors
    exact (input.localizedRerootChildren_nodup cursor children childrenDerived).filter _
  have sameMembers : ∀ child,
      child ∈ input.localizedRule3AxisPhysicalContinuationCursors cursor children ↔
        child ∈ [nextCursor] := by
    intro child
    constructor
    · intro present
      simp [onlyNext child present]
    · intro present
      simp only [List.mem_singleton] at present
      subst child
      exact nextFiltered
  have permutation : List.Perm
      (input.localizedRule3AxisPhysicalContinuationCursors cursor children)
      [nextCursor] :=
    (List.perm_ext_iff_of_nodup filteredNodup (by simp)).mpr sameMembers
  have filteredSingleton :
      input.localizedRule3AxisPhysicalContinuationCursors cursor children =
        [nextCursor] := List.perm_singleton.mp permutation
  unfold localizedRule3AxisPhysicalContinuationCursors?
  rw [childrenComputed]
  exact congrArg some filteredSingleton

/-- The exhaustive topology classifier is terminal exactly when graph perception has no forward
order-two neighbour at this embedded cursor. -/
theorem localizedRule3AxisTopology?_of_embedded_terminal
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (previousOccurrence : input.LocalizedCIPOccurrence fuel)
    (previous current : input.Atom) (incomingSlot : Nat)
    (previousExact : cursor.previous? = some previousOccurrence)
    (previousCurrent : previousOccurrence.1.node.current? = some previous)
    (cursorCurrent : cursor.occurrence.1.node.current? = some current)
    (cursorParent : cursor.occurrence.1.node.parent? =
      previousOccurrence.1.node.current?)
    (sameRoot : cursor.occurrence.1.root = previousOccurrence.1.root)
    (cursorAddress : cursor.occurrence.1.address =
      previousOccurrence.1.address ++ [incomingSlot])
    (forward : input.localizedAxialForwardNeighbors previous current = []) :
    input.localizedRule3AxisTopology? cursor = some .terminal := by
  have exactContinuations :=
    input.localizedRule3AxisPhysicalContinuationCursors?_of_embedded_forward
      cursor previousOccurrence previous current incomingSlot previousExact
      previousCurrent cursorCurrent cursorParent sameRoot cursorAddress forward
  simp [localizedRule3AxisTopology?, exactContinuations]

/-- The exhaustive topology classifier returns the exact next embedded cursor when graph
perception has one forward order-two neighbour. -/
theorem localizedRule3AxisTopology?_of_embedded_linear
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor nextCursor : input.LocalizedRerootCursor fuel)
    (previousOccurrence : input.LocalizedCIPOccurrence fuel)
    (previous current next : input.Atom) (incomingSlot nextSlot : Nat)
    (previousExact : cursor.previous? = some previousOccurrence)
    (previousCurrent : previousOccurrence.1.node.current? = some previous)
    (cursorCurrent : cursor.occurrence.1.node.current? = some current)
    (cursorParent : cursor.occurrence.1.node.parent? =
      previousOccurrence.1.node.current?)
    (sameRoot : cursor.occurrence.1.root = previousOccurrence.1.root)
    (cursorAddress : cursor.occurrence.1.address =
      previousOccurrence.1.address ++ [incomingSlot])
    (cursorReal : cursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (nextPrevious : nextCursor.previous? = some cursor.occurrence)
    (nextRoot : nextCursor.occurrence.1.root = cursor.occurrence.1.root)
    (nextAddress : nextCursor.occurrence.1.address =
      cursor.occurrence.1.address ++ [nextSlot])
    (nextReal : nextCursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (nextCurrent : nextCursor.occurrence.1.node.current? = some next)
    (forward : input.localizedAxialForwardNeighbors previous current = [next]) :
    input.localizedRule3AxisTopology? cursor = some (.linear nextCursor) := by
  have exactContinuations :=
    input.localizedRule3AxisPhysicalContinuationCursors?_of_embedded_singleton
      cursor nextCursor previousOccurrence previous current next incomingSlot nextSlot
      previousExact previousCurrent cursorCurrent cursorParent sameRoot cursorAddress
      cursorReal nextPrevious nextRoot nextAddress nextReal nextCurrent forward
  simp [localizedRule3AxisTopology?, exactContinuations, nextReal]

/-- The reverse cursor at any exact maximal open-chain terminal cuts its unique first-axis child
and therefore has no remaining physical order-two continuation. -/
theorem localizedRule3AxisTopology?_axialRootInitialLeft_terminal
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axialRoot : input.LocalizedAxialRoot) :
    input.localizedRule3AxisTopology?
        (input.localizedAxialRootInitialPhysicalEndpointCursorFrame
          fuel axialRoot).leftCursor = some .terminal := by
  classical
  let initial := input.localizedAxialRootInitialPhysicalEndpointCursorFrame fuel axialRoot
  let cursor := initial.leftCursor
  let previousOccurrence := input.localizedAxialRootFirstChildOccurrence fuel axialRoot
  have previousExact : cursor.previous? = some previousOccurrence := by
    rfl
  obtain ⟨children, childrenComputed⟩ :=
    input.exists_localizedRerootChildren cursor
  have childrenDerived := input.localizedRerootChildren?_sound
    cursor children childrenComputed
  have rootValid := (input.mem_localizedAxialRootCandidates_iff axialRoot.1).mp axialRoot.2
  have noPhysical : ∀ child,
      child ∉ input.localizedRule3AxisPhysicalContinuationCursors cursor children := by
    intro child childPresent
    have characterized :=
      (input.mem_localizedRule3AxisPhysicalContinuationCursors_iff
        cursor child children).mp childPresent
    have childIntended : child.occurrence.1 ∈
        input.intendedLocalizedRerootChildFrames cursor := by
      rw [← childrenDerived.1]
      exact List.mem_map.mpr ⟨child, characterized.1, rfl⟩
    have childNePrevious := input.address_ne_previous_of_mem_intended
      cursor previousOccurrence previousExact child.occurrence.1 childIntended
    have childNeighbor := input.mem_localizedRerootNeighborFrames_of_mem_intended
      cursor child.occurrence.1 childIntended
    have adjacent :=
      (input.mem_localizedRerootNeighborFrames_iff
        cursor.occurrence.1 child.occurrence.1).mp childNeighbor
    have outward : cursor.occurrence.1.address.length + 1 =
          child.occurrence.1.address.length ∧
        cursor.occurrence.1.address = child.occurrence.1.address.dropLast := by
      rcases adjacent.2.2 with parent | outward
      · have rootAddress : cursor.occurrence.1.address = [] := by rfl
        rw [rootAddress] at parent
        simp at parent
      · exact outward
    have childNonempty : child.occurrence.1.address ≠ [] := by
      intro empty
      rw [empty] at outward
      simp at outward
    let slot := child.occurrence.1.address.getLast childNonempty
    have childAddress : child.occurrence.1.address =
        cursor.occurrence.1.address ++ [slot] := by
      calc
        child.occurrence.1.address =
            child.occurrence.1.address.dropLast ++ [slot] :=
          (List.dropLast_append_getLast childNonempty).symm
        _ = cursor.occurrence.1.address ++ [slot] := by rw [← outward.2]
    have childRoot : child.occurrence.1.root = cursor.occurrence.1.root :=
      input.localizedRerootChildren_root_eq cursor child children
        childrenDerived characterized.1
    obtain ⟨officialChild, officialAtSlot, childFrame⟩ :=
      input.declarativeLocalizedOccurrence_immediate_child
        ((input.mem_localizedOccurrences_iff fuel cursor.occurrence.1).mp
          cursor.occurrence.2)
        ((input.mem_localizedOccurrences_iff fuel child.occurrence.1).mp
          child.occurrence.2)
        childRoot slot childAddress
    have childNode : child.occurrence.1.node = officialChild := by
      simpa using congrArg LocalizedCIPOccurrenceFrame.node childFrame
    have physicalProvenance :
        officialChild.provenance = OfficialCIPNodeProvenance.realAtom ∨
          ∃ distance, officialChild.provenance =
            OfficialCIPNodeProvenance.ringDuplicate distance := by
      have admitted := characterized.2.2.1
      rw [childNode] at admitted
      cases provenance : officialChild.provenance <;>
        simp [LocalizedRule3PhysicalReferenceProvenance, provenance] at admitted
      · exact Or.inl rfl
      · exact Or.inr ⟨_, rfl⟩
    obtain ⟨next, officialIdentity, _notParent⟩ :=
      input.eq_extend_zero_and_not_parent_of_mem_executableOfficialCIPChildren
        cursor.occurrence.1.node officialChild
        (List.fst_mem_of_mem_zipIdx officialAtSlot) physicalProvenance
    have childCurrent : child.occurrence.1.node.current? = some next := by
      rw [childNode, officialIdentity]
      rfl
    have nextDouble : input.moleculeGraph.bond axialRoot.1.terminal next = 2 := by
      have bondPart := characterized.2.2.2
      rw [show cursor.occurrence.1.node.current? = some axialRoot.1.terminal by rfl,
        childCurrent] at bondPart
      exact bondPart
    have nextIdentity : next = axialRoot.1.firstAxis :=
      rootValid.2 next nextDouble
    subst next
    have canonicalAtSlot := input.localizedAxialRootFirstChildSlot_mem axialRoot
    have officialIsCanonical : officialChild =
        input.localizedAxialRootFirstChildNode axialRoot := by
      simpa [localizedAxialRootFirstChildNode] using officialIdentity
    have slotIdentity : slot = input.localizedAxialRootFirstChildSlot axialRoot :=
      input.physical_executableOfficialCIPChild_slot_unique
        cursor.occurrence.1.node officialChild slot
        (input.localizedAxialRootFirstChildSlot axialRoot)
        officialAtSlot (by simpa [officialIsCanonical] using canonicalAtSlot)
        physicalProvenance
    apply childNePrevious
    rw [childAddress, slotIdentity]
    rfl
  have exactContinuations :
      input.localizedRule3AxisPhysicalContinuationCursors? cursor = some [] := by
    have filteredEmpty :
        input.localizedRule3AxisPhysicalContinuationCursors cursor children = [] :=
      List.eq_nil_iff_forall_not_mem.mpr noPhysical
    unfold localizedRule3AxisPhysicalContinuationCursors?
    rw [childrenComputed]
    exact congrArg some filteredEmpty
  simp [cursor, initial, localizedRule3AxisTopology?, exactContinuations]

/-- Every exact maximal open-chain root is recognized as a terminal-start cumulated axis at its
canonical real first child, independently of later odd/even parity classification. -/
theorem localizedRule3CumulatedAxisEntry?_axialRootFirstChild
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axialRoot : input.LocalizedAxialRoot) :
    input.localizedRule3CumulatedAxisEntry?
        (input.localizedAxialRootFirstChildOccurrence fuel axialRoot) =
      some (.terminalStart
        (input.localizedAxialRootInitialPhysicalEndpointCursorFrame fuel axialRoot)) := by
  unfold localizedRule3CumulatedAxisEntry?
  rw [input.localizedRule3PhysicalEndpointCursorFrame?_axialRootFirstChild fuel axialRoot]
  simp [input.localizedRule3AxisTopology?_axialRootInitialLeft_terminal fuel axialRoot]

/-- The reverse cursor at the canonical terminal cuts the first axis child and therefore has no
remaining physical order-two continuation.  This proves the exact terminal-start classification
needed by the cumulated endpoint constructor. -/
theorem localizedRule3AxisTopology?_evenAxialInitialLeft_terminal
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) :
    input.localizedRule3AxisTopology?
        (input.localizedEvenAxialInitialPhysicalEndpointCursorFrame fuel axis).leftCursor =
      some .terminal := by
  classical
  let initial := input.localizedEvenAxialInitialPhysicalEndpointCursorFrame fuel axis
  let cursor := initial.leftCursor
  let previousOccurrence := input.localizedEvenAxialFirstChildOccurrence fuel axis
  let rootOccurrence := input.localizedEvenAxialRootOccurrence fuel axis
  have previousExact : cursor.previous? = some previousOccurrence := by
    rfl
  obtain ⟨children, childrenComputed⟩ :=
    input.exists_localizedRerootChildren cursor
  have childrenDerived := input.localizedRerootChildren?_sound
    cursor children childrenComputed
  have axisValid := (input.mem_localizedEvenAxialChains_iff axis.1).mp axis.2
  have rootValid := axisValid.1.1
  have noPhysical : ∀ child,
      child ∉ input.localizedRule3AxisPhysicalContinuationCursors cursor children := by
    intro child childPresent
    have characterized :=
      (input.mem_localizedRule3AxisPhysicalContinuationCursors_iff
        cursor child children).mp childPresent
    have childIntended : child.occurrence.1 ∈
        input.intendedLocalizedRerootChildFrames cursor := by
      rw [← childrenDerived.1]
      exact List.mem_map.mpr ⟨child, characterized.1, rfl⟩
    have childNePrevious := input.address_ne_previous_of_mem_intended
      cursor previousOccurrence previousExact child.occurrence.1 childIntended
    have childNeighbor := input.mem_localizedRerootNeighborFrames_of_mem_intended
      cursor child.occurrence.1 childIntended
    have adjacent :=
      (input.mem_localizedRerootNeighborFrames_iff
        cursor.occurrence.1 child.occurrence.1).mp childNeighbor
    have outward : cursor.occurrence.1.address.length + 1 =
          child.occurrence.1.address.length ∧
        cursor.occurrence.1.address = child.occurrence.1.address.dropLast := by
      rcases adjacent.2.2 with parent | outward
      · have rootAddress : cursor.occurrence.1.address = [] := by rfl
        rw [rootAddress] at parent
        simp at parent
      · exact outward
    have childNonempty : child.occurrence.1.address ≠ [] := by
      intro empty
      rw [empty] at outward
      simp at outward
    let slot := child.occurrence.1.address.getLast childNonempty
    have childAddress : child.occurrence.1.address =
        cursor.occurrence.1.address ++ [slot] := by
      calc
        child.occurrence.1.address =
            child.occurrence.1.address.dropLast ++ [slot] :=
          (List.dropLast_append_getLast childNonempty).symm
        _ = cursor.occurrence.1.address ++ [slot] := by rw [← outward.2]
    have childRoot : child.occurrence.1.root = cursor.occurrence.1.root :=
      input.localizedRerootChildren_root_eq cursor child children
        childrenDerived characterized.1
    obtain ⟨officialChild, officialAtSlot, childFrame⟩ :=
      input.declarativeLocalizedOccurrence_immediate_child
        ((input.mem_localizedOccurrences_iff fuel cursor.occurrence.1).mp
          cursor.occurrence.2)
        ((input.mem_localizedOccurrences_iff fuel child.occurrence.1).mp
          child.occurrence.2)
        childRoot slot childAddress
    have childNode : child.occurrence.1.node = officialChild := by
      simpa using congrArg LocalizedCIPOccurrenceFrame.node childFrame
    have physicalProvenance :
        officialChild.provenance = OfficialCIPNodeProvenance.realAtom ∨
          ∃ distance, officialChild.provenance =
            OfficialCIPNodeProvenance.ringDuplicate distance := by
      have admitted := characterized.2.2.1
      rw [childNode] at admitted
      cases provenance : officialChild.provenance <;>
        simp [LocalizedRule3PhysicalReferenceProvenance, provenance] at admitted
      · exact Or.inl rfl
      · exact Or.inr ⟨_, rfl⟩
    obtain ⟨next, officialIdentity, _notParent⟩ :=
      input.eq_extend_zero_and_not_parent_of_mem_executableOfficialCIPChildren
        cursor.occurrence.1.node officialChild
        (List.fst_mem_of_mem_zipIdx officialAtSlot) physicalProvenance
    have childCurrent : child.occurrence.1.node.current? = some next := by
      rw [childNode, officialIdentity]
      rfl
    have nextDouble : input.moleculeGraph.bond axis.1.root.terminal next = 2 := by
      have bondPart := characterized.2.2.2
      rw [show cursor.occurrence.1.node.current? = some axis.1.root.terminal by rfl,
        childCurrent] at bondPart
      exact bondPart
    have nextIdentity : next = axis.1.root.firstAxis :=
      rootValid.2 next nextDouble
    subst next
    have canonicalAtSlot := input.localizedEvenAxialFirstChildSlot_mem axis
    have officialIsCanonical : officialChild =
        input.localizedEvenAxialFirstChildNode axis.1 := by
      simpa [localizedEvenAxialFirstChildNode] using officialIdentity
    have slotIdentity : slot = input.localizedEvenAxialFirstChildSlot axis :=
      input.physical_executableOfficialCIPChild_slot_unique
        cursor.occurrence.1.node officialChild slot
        (input.localizedEvenAxialFirstChildSlot axis)
        officialAtSlot (by simpa [officialIsCanonical] using canonicalAtSlot)
        physicalProvenance
    apply childNePrevious
    rw [childAddress, slotIdentity]
    rfl
  have exactContinuations :
      input.localizedRule3AxisPhysicalContinuationCursors? cursor = some [] := by
    have filteredEmpty :
        input.localizedRule3AxisPhysicalContinuationCursors cursor children = [] :=
      List.eq_nil_iff_forall_not_mem.mpr noPhysical
    unfold localizedRule3AxisPhysicalContinuationCursors?
    rw [childrenComputed]
    exact congrArg some filteredEmpty
  simp [cursor, initial, localizedRule3AxisTopology?, exactContinuations]

/-- Every perceived canonical open even axis is recognized as a terminal-start cumulated axis at
its canonical first child. -/
theorem localizedRule3CumulatedAxisEntry?_evenAxialFirstChild
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) :
    input.localizedRule3CumulatedAxisEntry?
        (input.localizedEvenAxialFirstChildOccurrence fuel axis) =
      some (.terminalStart
        (input.localizedEvenAxialInitialPhysicalEndpointCursorFrame fuel axis)) := by
  unfold localizedRule3CumulatedAxisEntry?
  rw [input.localizedRule3PhysicalEndpointCursorFrame?_evenAxialFirstChild fuel axis]
  simp [input.localizedRule3AxisTopology?_evenAxialInitialLeft_terminal fuel axis]

/-- A fully computed open-axis zipper path: every internal topology computation returns its exact
next cursor, and the final computation returns terminal. -/
inductive LocalizedRule3ComputedCumulatedAxisWalk
    (input : CertifiedLocalizedCIPInput) {fuel : Nat} :
    List (input.LocalizedRerootCursor fuel) → Prop
  | terminal {cursor}
      (topology : input.localizedRule3AxisTopology? cursor = some .terminal) :
      input.LocalizedRule3ComputedCumulatedAxisWalk [cursor]
  | linear {cursor next tail}
      (topology : input.localizedRule3AxisTopology? cursor = some (.linear next))
      (rest : input.LocalizedRule3ComputedCumulatedAxisWalk (next :: tail)) :
      input.LocalizedRule3ComputedCumulatedAxisWalk (cursor :: next :: tail)

/-- Prepend the uniquely computed predecessor of any already computed nonempty path. -/
theorem LocalizedRule3ComputedCumulatedAxisWalk.prepend
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {cursors : List (input.LocalizedRerootCursor fuel)}
    (derived : input.LocalizedRule3ComputedCumulatedAxisWalk cursors)
    (cursor : input.LocalizedRerootCursor fuel)
    (topology : ∀ next, next ∈ cursors.head? →
      input.localizedRule3AxisTopology? cursor = some (.linear next)) :
    input.LocalizedRule3ComputedCumulatedAxisWalk (cursor :: cursors) := by
  cases derived with
  | @terminal next nextTopology =>
      exact LocalizedRule3ComputedCumulatedAxisWalk.linear
        (topology next (by simp))
        (LocalizedRule3ComputedCumulatedAxisWalk.terminal nextTopology)
  | @linear next after more nextTopology rest =>
      exact LocalizedRule3ComputedCumulatedAxisWalk.linear
        (topology next (by simp))
        (LocalizedRule3ComputedCumulatedAxisWalk.linear nextTopology rest)

/-- A completely computed zipper path executes exactly once fuel covers its number of linear
steps. -/
theorem LocalizedRule3ComputedCumulatedAxisWalk.executes
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {cursors : List (input.LocalizedRerootCursor carrierFuel)}
    (derived : input.LocalizedRule3ComputedCumulatedAxisWalk cursors) :
    ∀ traversalFuel, cursors.length ≤ traversalFuel + 1 →
      ∃ first, cursors.head? = some first ∧
        input.walkLocalizedRule3CumulatedAxis? traversalFuel first = some cursors := by
  induction derived with
  | @terminal cursor topology =>
      intro traversalFuel enough
      exact ⟨cursor, rfl, by
        cases traversalFuel <;>
          simp [walkLocalizedRule3CumulatedAxis?, topology]⟩
  | @linear cursor next tail topology rest inductionHypothesis =>
      intro traversalFuel enough
      cases traversalFuel with
      | zero => simp at enough
      | succ traversalFuel =>
          have tailEnough : (next :: tail).length ≤ traversalFuel + 1 := by
            simpa using Nat.le_of_succ_le_succ enough
          obtain ⟨first, headIdentity, tailComputed⟩ :=
            inductionHypothesis traversalFuel tailEnough
          simp only [List.head?_cons, Option.some.injEq] at headIdentity
          subst first
          exact ⟨cursor, rfl, by
            simp [walkLocalizedRule3CumulatedAxis?, topology, tailComputed]⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
