import TetraStereo.OneCenter.LocalizedRule3OccurrenceReferenceCursor

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# General uniqueness of physical Rule-3 reference cursors

`LocalizedRule3OccurrenceReferenceCursor` proves that two *outward* physical reference children of
the same endpoint cursor coincide.  The endpoint-frame construction, however, also admits the
carrier-parent coordinate as an uncut child, so the outward-only lemma does not yet upgrade an
arbitrary declarative reference selection to the canonical relation.

This module closes that gap.  The exact reroot children are a filtered sublist of the physical
carrier neighbors, and a neighbor of a carrier occurrence is either its carrier parent (one
sibling address shorter) or an outward immediate child (one sibling address longer):

* two parent-side candidates have the same root and the same address, hence coincide by
  occurrence-address functionality;
* two outward candidates coincide by the existing outward uniqueness theorem;
* a parent-side and an outward candidate cannot disagree: the parent-side coordinate determines
  the endpoint's official parent atom, while a *physical* outward child is a zero-copy official
  child, and the official child-copy enumeration removes exactly the zero-copy parent occurrence
  (positive copies are multiple-bond bookkeeping, not physical real/ring positions).

Nothing here assumes an endpoint-shape hypothesis.  The cut performed by an arbitrary incoming
coordinate only removes neighbors from the exact intended list; it cannot create a second cursor
at the same physical atom.  Ring-duplicate closures are admitted physical representations
throughout, so each distinct physical ring closure is still represented exactly once.
-/

/-- If `source` is the parent address of `candidate` (one sibling slot shorter), then `candidate`
is `source` followed by exactly one sibling slot. -/
theorem exists_eq_append_singleton_of_eq_dropLast
    {source candidate : List Nat}
    (lengthStep : source.length + 1 = candidate.length)
    (dropLastEq : source = candidate.dropLast) :
    ∃ slot, candidate = source ++ [slot] := by
  have nonempty : candidate ≠ [] := by
    intro empty
    rw [empty] at lengthStep
    simp at lengthStep
  refine ⟨candidate.getLast nonempty, ?_⟩
  calc
    candidate = candidate.dropLast ++ [candidate.getLast nonempty] :=
      (List.dropLast_append_getLast nonempty).symm
    _ = source ++ [candidate.getLast nonempty] := by rw [← dropLastEq]

namespace CertifiedLocalizedCIPInput

/-- Every executable official child is an `extend` of its parent node at some atom and copy index. -/
theorem eq_extend_of_mem_executableOfficialCIPChildren
    (input : CertifiedLocalizedCIPInput)
    (node child : OfficialCIPNode input.Atom)
    (present : child ∈ input.executableOfficialCIPChildren node) :
    ∃ next copyIndex, child = node.extend next copyIndex := by
  unfold executableOfficialCIPChildren at present
  split at present
  · simp at present
  · rw [List.mem_map] at present
    rcases present with ⟨copy, _copyPresent, childIdentity⟩
    exact ⟨copy.1, copy.2, childIdentity.symm⟩

/-- Reachable official nodes remember their current atom as the head of the stored branch
history.  This structural invariant holds for the root node and is preserved by official child
extension. -/
theorem DeclarativeLocalizedOccurrenceSubtree_history_head_eq_current
    (input : CertifiedLocalizedCIPInput)
    {root : input.Atom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode input.Atom}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrenceSubtree root path fuel node occurrence) :
    node.history.head? = node.current? →
      occurrence.node.history.head? = occurrence.node.current? := by
  induction derived with
  | subtreeRoot =>
      intro head
      exact head
  | @subtreeDescendant path fuel node child slot occurrence childAtSlot descendant ih =>
      intro head
      apply ih
      obtain ⟨next, copyIndex, childIdentity⟩ :=
        input.eq_extend_of_mem_executableOfficialCIPChildren node child
          (List.fst_mem_of_mem_zipIdx childAtSlot)
      rw [childIdentity]
      simp

/-- Every molecule-wide occurrence node remembers its current atom as the history head. -/
theorem declarativeLocalizedOccurrence_history_head_eq_current
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrence fuel occurrence) :
    occurrence.node.history.head? = occurrence.node.current? := by
  have rooted := input.declarativeLocalizedOccurrence_as_rootSubtree derived
  exact input.DeclarativeLocalizedOccurrenceSubtree_history_head_eq_current rooted
    (by simp [OfficialCIPNode.root])

/-- A candidate occupying the carrier-parent coordinate of an endpoint determines that endpoint's
official parent atom.  The endpoint is the official child one sibling slot below the candidate, and
the node-history invariant reads the candidate's current atom back as the endpoint's `parent?`. -/
theorem endpoint_parent?_eq_of_parent_candidate
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor candidate : input.LocalizedRerootCursor fuel)
    (reference : input.Atom)
    (candidateCurrent : candidate.occurrence.1.node.current? = some reference)
    (sameRoot : candidate.occurrence.1.root = endpointCursor.occurrence.1.root)
    (parentAddress :
      candidate.occurrence.1.address.length + 1 =
        endpointCursor.occurrence.1.address.length ∧
      candidate.occurrence.1.address =
        endpointCursor.occurrence.1.address.dropLast) :
    endpointCursor.occurrence.1.node.parent? = some reference := by
  have endpointNonempty : endpointCursor.occurrence.1.address ≠ [] := by
    intro empty
    rw [empty] at parentAddress
    simp at parentAddress
  let slot := endpointCursor.occurrence.1.address.getLast endpointNonempty
  have endpointAddress : endpointCursor.occurrence.1.address =
      candidate.occurrence.1.address ++ [slot] := by
    calc
      endpointCursor.occurrence.1.address =
          endpointCursor.occurrence.1.address.dropLast ++ [slot] :=
        (List.dropLast_append_getLast endpointNonempty).symm
      _ = candidate.occurrence.1.address ++ [slot] := by rw [← parentAddress.2]
  obtain ⟨child, childAtSlot, endpointFrame⟩ :=
    input.declarativeLocalizedOccurrence_immediate_child
      ((input.mem_localizedOccurrences_iff fuel candidate.occurrence.1).mp
        candidate.occurrence.2)
      ((input.mem_localizedOccurrences_iff fuel endpointCursor.occurrence.1).mp
        endpointCursor.occurrence.2)
      sameRoot.symm slot endpointAddress
  have endpointNode : endpointCursor.occurrence.1.node = child := by
    simpa using congrArg LocalizedCIPOccurrenceFrame.node endpointFrame
  obtain ⟨next, copyIndex, childIdentity⟩ :=
    input.eq_extend_of_mem_executableOfficialCIPChildren
      candidate.occurrence.1.node child (List.fst_mem_of_mem_zipIdx childAtSlot)
  have headObserved : candidate.occurrence.1.node.history.head? = some reference :=
    (input.declarativeLocalizedOccurrence_history_head_eq_current
      ((input.mem_localizedOccurrences_iff fuel candidate.occurrence.1).mp
        candidate.occurrence.2)).trans candidateCurrent
  obtain ⟨rest, historyEq⟩ := List.head?_eq_some_iff.mp headObserved
  have extendHistory :
      (candidate.occurrence.1.node.extend next copyIndex).history =
        next :: reference :: rest := by
    rw [OfficialCIPNode.extend_history, historyEq]
  have parentEq :
      (candidate.occurrence.1.node.extend next copyIndex).parent? = some reference := by
    unfold OfficialCIPNode.parent?
    rw [extendHistory]
  simpa [endpointNode, childIdentity] using parentEq

/-- A physical outward candidate one sibling slot below an endpoint makes the endpoint's official
parent atom differ from the candidate's current atom.  A physical official child is necessarily a
zero copy, and the zero-copy parent occurrence is removed from the official child-copy list;
positive copies are multiple-bond bookkeeping rather than physical real/ring positions. -/
theorem endpoint_parent?_ne_of_outward_candidate
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor candidate : input.LocalizedRerootCursor fuel)
    (reference : input.Atom)
    (candidateCurrent : candidate.occurrence.1.node.current? = some reference)
    (candidatePhysical : LocalizedRule3PhysicalReferenceProvenance
      candidate.occurrence.1.node.provenance)
    (sameRoot : candidate.occurrence.1.root = endpointCursor.occurrence.1.root)
    (slot : Nat)
    (candidateAddress : candidate.occurrence.1.address =
      endpointCursor.occurrence.1.address ++ [slot]) :
    endpointCursor.occurrence.1.node.parent? ≠ some reference := by
  obtain ⟨child, childAtSlot, candidateFrame⟩ :=
    input.declarativeLocalizedOccurrence_immediate_child
      ((input.mem_localizedOccurrences_iff fuel endpointCursor.occurrence.1).mp
        endpointCursor.occurrence.2)
      ((input.mem_localizedOccurrences_iff fuel candidate.occurrence.1).mp
        candidate.occurrence.2)
      sameRoot slot candidateAddress
  have candidateNode : candidate.occurrence.1.node = child := by
    simpa using congrArg LocalizedCIPOccurrenceFrame.node candidateFrame
  have physicalChild :
      child.provenance = OfficialCIPNodeProvenance.realAtom ∨
        ∃ distance, child.provenance =
          OfficialCIPNodeProvenance.ringDuplicate distance := by
    rw [← candidateNode]
    cases provenance : candidate.occurrence.1.node.provenance <;>
      simp [LocalizedRule3PhysicalReferenceProvenance, provenance] at candidatePhysical
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩
  obtain ⟨next, officialIdentity, notParent⟩ :=
    input.eq_extend_zero_and_not_parent_of_mem_executableOfficialCIPChildren
      endpointCursor.occurrence.1.node child
      (List.fst_mem_of_mem_zipIdx childAtSlot) physicalChild
  have childCurrent : child.current? = some reference := by
    rw [← candidateNode]
    exact candidateCurrent
  have nextIdentity : next = reference := by
    have observed := congrArg OfficialCIPNode.current? officialIdentity
    have observedCurrent : child.current? = some next := by
      simpa using observed
    rw [childCurrent] at observedCurrent
    exact (Option.some.inj observedCurrent).symm
  simpa [nextIdentity] using notParent

/-- General uniqueness of physical reference cursors.  Among the exact uncut children of *any*
admitted endpoint cursor, at most one cursor can carry a requested physical atom with real or
ring-duplicate provenance.  No endpoint-shape hypothesis is needed: the children split into the
carrier-parent coordinate and outward sibling coordinates. -/
theorem localizedRule3PhysicalReferenceCursor_unique
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor first second : input.LocalizedRerootCursor fuel)
    (reference : input.Atom)
    (children : List (input.LocalizedRerootCursor fuel))
    (childrenDerived : input.DeclarativeLocalizedRerootChildren
      endpointCursor children)
    (firstPresent : first ∈ children)
    (secondPresent : second ∈ children)
    (firstCurrent : first.occurrence.1.node.current? = some reference)
    (secondCurrent : second.occurrence.1.node.current? = some reference)
    (firstPhysical : LocalizedRule3PhysicalReferenceProvenance
      first.occurrence.1.node.provenance)
    (secondPhysical : LocalizedRule3PhysicalReferenceProvenance
      second.occurrence.1.node.provenance) :
    first = second := by
  have firstIntended : first.occurrence.1 ∈
      input.intendedLocalizedRerootChildFrames endpointCursor := by
    rw [← childrenDerived.1]
    exact List.mem_map.mpr ⟨first, firstPresent, rfl⟩
  have secondIntended : second.occurrence.1 ∈
      input.intendedLocalizedRerootChildFrames endpointCursor := by
    rw [← childrenDerived.1]
    exact List.mem_map.mpr ⟨second, secondPresent, rfl⟩
  have firstNeighbor := input.mem_localizedRerootNeighborFrames_of_mem_intended
    endpointCursor first.occurrence.1 firstIntended
  have secondNeighbor := input.mem_localizedRerootNeighborFrames_of_mem_intended
    endpointCursor second.occurrence.1 secondIntended
  have firstCharacterized :=
    (input.mem_localizedRerootNeighborFrames_iff
      endpointCursor.occurrence.1 first.occurrence.1).mp firstNeighbor
  have secondCharacterized :=
    (input.mem_localizedRerootNeighborFrames_iff
      endpointCursor.occurrence.1 second.occurrence.1).mp secondNeighbor
  rcases firstCharacterized.2 with ⟨firstRootEq, firstParent | firstOutward⟩
  · rcases secondCharacterized.2 with ⟨secondRootEq, secondParent | secondOutward⟩
    · -- Both candidates occupy the carrier-parent coordinate.
      have sameRoot : first.occurrence.1.root = second.occurrence.1.root :=
        firstRootEq.trans secondRootEq.symm
      have sameAddress : first.occurrence.1.address =
          second.occurrence.1.address :=
        firstParent.2.trans secondParent.2.symm
      have frameIdentity : first.occurrence.1 = second.occurrence.1 :=
        input.declarativeLocalizedOccurrence_functional_at_root_address
          ((input.mem_localizedOccurrences_iff fuel first.occurrence.1).mp
            first.occurrence.2)
          ((input.mem_localizedOccurrences_iff fuel second.occurrence.1).mp
            second.occurrence.2)
          sameRoot sameAddress
      apply LocalizedRerootCursor.ext input
      · exact Subtype.ext frameIdentity
      · exact (childrenDerived.2 first firstPresent).trans
          (childrenDerived.2 second secondPresent).symm
    · -- A parent candidate and an outward candidate are incompatible.
      have endpointParent := input.endpoint_parent?_eq_of_parent_candidate
        endpointCursor first reference firstCurrent firstRootEq firstParent
      obtain ⟨secondSlot, secondAddress⟩ :=
        exists_eq_append_singleton_of_eq_dropLast secondOutward.1 secondOutward.2
      have endpointNotParent := input.endpoint_parent?_ne_of_outward_candidate
        endpointCursor second reference secondCurrent secondPhysical
        secondRootEq secondSlot secondAddress
      exact (endpointNotParent endpointParent).elim
  · rcases secondCharacterized.2 with ⟨secondRootEq, secondParent | secondOutward⟩
    · -- An outward candidate and a parent candidate are incompatible.
      have endpointParent := input.endpoint_parent?_eq_of_parent_candidate
        endpointCursor second reference secondCurrent secondRootEq secondParent
      obtain ⟨firstSlot, firstAddress⟩ :=
        exists_eq_append_singleton_of_eq_dropLast firstOutward.1 firstOutward.2
      have endpointNotParent := input.endpoint_parent?_ne_of_outward_candidate
        endpointCursor first reference firstCurrent firstPhysical
        firstRootEq firstSlot firstAddress
      exact (endpointNotParent endpointParent).elim
    · -- Both candidates are outward immediate children.
      obtain ⟨firstSlot, firstAddress⟩ :=
        exists_eq_append_singleton_of_eq_dropLast firstOutward.1 firstOutward.2
      obtain ⟨secondSlot, secondAddress⟩ :=
        exists_eq_append_singleton_of_eq_dropLast secondOutward.1 secondOutward.2
      exact input.localizedRule3PhysicalReferenceCursor_unique_of_outward
        endpointCursor first second reference children childrenDerived
        firstPresent secondPresent firstCurrent secondCurrent firstPhysical secondPhysical
        ⟨firstSlot, firstAddress⟩ ⟨secondSlot, secondAddress⟩

/-- Every admitted declarative physical reference selection is already canonical: the exact
cut-neighborhood contains exactly one physical cursor at the requested atom.  This is the general
upgrade that removes the outward-only endpoint hypothesis from canonical reference selection. -/
theorem canonicalLocalizedRule3ReferenceCursor_of_declarative
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor cursor : input.LocalizedRerootCursor fuel)
    (reference : input.Atom)
    (declarative : input.DeclarativeLocalizedRule3ReferenceCursor
      endpointCursor cursor reference) :
    input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor cursor reference := by
  rcases declarative with ⟨children, childrenComputed, childrenDerived,
    cursorPresent, cursorCurrent, cursorPhysical, cursorPrevious⟩
  refine ⟨children, childrenComputed, childrenDerived, cursorPresent,
    cursorCurrent, cursorPhysical, cursorPrevious, ?_⟩
  intro candidate candidatePresent candidateCurrent candidatePhysical
  exact input.localizedRule3PhysicalReferenceCursor_unique
    endpointCursor candidate cursor reference children childrenDerived
    candidatePresent cursorPresent candidateCurrent cursorCurrent
    candidatePhysical cursorPhysical

/-- Canonical and declarative physical reference selection coincide at every admitted occurrence
cursor.  The canonical form is exactly the declarative relation plus the uniqueness that follows
from exact official child-copy removal. -/
theorem canonicalLocalizedRule3ReferenceCursor_iff_declarative
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor cursor : input.LocalizedRerootCursor fuel)
    (reference : input.Atom) :
    input.CanonicalLocalizedRule3ReferenceCursor endpointCursor cursor reference ↔
      input.DeclarativeLocalizedRule3ReferenceCursor
        endpointCursor cursor reference := by
  constructor
  · intro canonical
    rcases canonical with ⟨children, childrenComputed, childrenDerived,
      cursorPresent, cursorCurrent, cursorPhysical, cursorPrevious, _unique⟩
    exact ⟨children, childrenComputed, childrenDerived, cursorPresent,
      cursorCurrent, cursorPhysical, cursorPrevious⟩
  · exact input.canonicalLocalizedRule3ReferenceCursor_of_declarative
      endpointCursor cursor reference

/-- Any declarative physical reference selection is exactly the executable singleton
cut-neighborhood lookup at its endpoint.  This exposes the general uniqueness result in the form
consumed by endpoint-frame compilation, without any endpoint-shape hypothesis. -/
theorem localizedRule3ReferenceCursor?_eq_some_of_declarative
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor cursor : input.LocalizedRerootCursor fuel)
    (reference : input.Atom)
    (declarative : input.DeclarativeLocalizedRule3ReferenceCursor
      endpointCursor cursor reference) :
    input.localizedRule3ReferenceCursor? endpointCursor reference = some cursor :=
  (input.localizedRule3ReferenceCursor?_eq_some_iff endpointCursor cursor reference).mpr
    (input.canonicalLocalizedRule3ReferenceCursor_of_declarative
      endpointCursor cursor reference declarative)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
