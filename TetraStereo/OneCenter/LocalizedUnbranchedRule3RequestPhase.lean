import TetraStereo.OneCenter.LocalizedRule3OddOriginalTargetDemand
import TetraStereo.OneCenter.LocalizedRule3ShortCircuitOddNode
import TetraStereo.OneCenter.LocalizedExtendedFallbackNoRead
import TetraStereo.OneCenter.LocalizedAxialRootPerception
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false




























namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

/-! ## The explicit unbranched graph domain -/

/-- **Unbranched order-two graph domain.**  Every atom has at most two distinct order-two
neighbours.  This is a fact about the input molecule graph, stated independently of any
evaluator, route certificate or descriptor outcome. -/
def LocalizedUnbranchedDoubleBondGraph (input : CertifiedLocalizedCIPInput) : Prop :=
  ∀ atom : input.Atom, (input.localizedOrderTwoNeighbors atom).length ≤ 2

/-- **Three-neighbour elimination.**  At an atom of the unbranched domain, three atoms that are
each doubly bonded to it cannot be pairwise distinct. -/
theorem eq_of_three_doubleBond_neighbors
    (input : CertifiedLocalizedCIPInput)
    (domain : input.LocalizedUnbranchedDoubleBondGraph)
    (center : input.Atom) (first second third : input.Atom)
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
  have bound := domain center
  omega

/-! ## The semantic no-actual-branched-axis predicate -/

/-- **No actual branched axis, stated semantically.**  No occurrence with a declarative physical
endpoint frame has a declarative branched axis topology at its parent-side endpoint cursor.  This
is an independent meaning of the geometry, phrased over declarative frames only. -/
def LocalizedNoActualBranchedAxis (input : CertifiedLocalizedCIPInput) : Prop :=
  ∀ (carrierFuel : Nat) (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (first second : input.LocalizedRerootCursor carrierFuel)
    (rest : List (input.LocalizedRerootCursor carrierFuel)),
    input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame occurrence initial →
      ¬ input.DeclarativeLocalizedRule3AxisTopology initial.leftCursor
          (.branched first second rest)

/-! ## Carrier provenance recovery -/

/-- A derived occurrence never carries placeholder provenance.  The top official node of a
molecule-wide occurrence is a real root; every generated child copy is either real or a
duplicate, so placeholders are unreachable from the carrier. -/
theorem DeclarativeLocalizedOccurrenceSubtree_provenance_ne_placeholder
    (input : CertifiedLocalizedCIPInput)
    {root : input.Atom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode input.Atom}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrenceSubtree root path fuel node occurrence)
    (nodeNonplaceholder : ∀ kind distance,
      node.provenance ≠ OfficialCIPNodeProvenance.placeholder kind distance) :
    ∀ kind distance,
      occurrence.node.provenance ≠ OfficialCIPNodeProvenance.placeholder kind distance := by
  induction derived with
  | subtreeRoot => exact nodeNonplaceholder
  | @subtreeDescendant path fuel node child slot occurrence childAtSlot descendant ih =>
      intro kind distance
      apply ih
      obtain ⟨next, copyIndex, childIdentity⟩ :=
        input.eq_extend_of_mem_executableOfficialCIPChildren node child
          (List.fst_mem_of_mem_zipIdx childAtSlot)
      intro otherKind otherDistance equality
      rw [childIdentity, OfficialCIPNode.extend_provenance] at equality
      simp only [OfficialCIPNode.childProvenance] at equality
      split at equality <;> (try split at equality) <;> simp at equality

/-- Molecule-wide occurrence provenance is never a placeholder. -/
theorem declarativeLocalizedOccurrence_provenance_ne_placeholder
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrence fuel occurrence) :
    ∀ kind distance,
      occurrence.node.provenance ≠ OfficialCIPNodeProvenance.placeholder kind distance := by
  have rooted := input.declarativeLocalizedOccurrence_as_rootSubtree derived
  exact input.DeclarativeLocalizedOccurrenceSubtree_provenance_ne_placeholder rooted
    (by simp [OfficialCIPNode.root])

/-- **A cursor with an executable child has a real-atom occurrence.**  The cut-neighbourhood is
empty for duplicate leaves, so a child forces non-duplicate provenance; placeholders are
unreachable from the carrier. -/
theorem provenance_real_of_mem_executableLocalizedRerootChildren
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (child : input.LocalizedRerootCursor fuel)
    (childPresent : child ∈ input.executableLocalizedRerootChildren cursor) :
    cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  have notDuplicate : cursor.occurrence.1.node.isDuplicateLeaf = false := by
    by_cases duplicate : cursor.occurrence.1.node.isDuplicateLeaf = true
    · have empty : input.executableLocalizedRerootChildren cursor = [] := by
        simp [executableLocalizedRerootChildren,
          intendedLocalizedRerootChildFrames, duplicate]
      rw [empty] at childPresent
      simp at childPresent
    · exact Bool.eq_false_of_not_eq_true duplicate
  have notPlaceholder := input.declarativeLocalizedOccurrence_provenance_ne_placeholder
    ((input.mem_localizedOccurrences_iff fuel cursor.occurrence.1).mp cursor.occurrence.2)
  cases provenance : cursor.occurrence.1.node.provenance with
  | realAtom => rfl
  | multipleBondDuplicate distance =>
      simp [OfficialCIPNode.isDuplicateLeaf, provenance] at notDuplicate
  | ringDuplicate distance =>
      simp [OfficialCIPNode.isDuplicateLeaf, provenance] at notDuplicate
  | placeholder kind distance =>
      exact absurd provenance (notPlaceholder kind distance)

/-! ## Official-node child geometry -/

/-- The stored parent of an official extension is the previous current atom. -/
theorem OfficialCIPNode.parent?_extend
    {V : Type*} [DecidableEq V] (node : OfficialCIPNode V) (next : V) (copyIndex : Nat) :
    (node.extend next copyIndex).parent? = node.history.head? := by
  cases history : node.history with
  | nil => simp [OfficialCIPNode.parent?, OfficialCIPNode.extend, history]
  | cons first rest => simp [OfficialCIPNode.parent?, OfficialCIPNode.extend, history]

/-- **An outward executable child has the cursor's current atom as its official parent.**  The
child is the official extension at its sibling slot, and every derived occurrence remembers its
current atom as the head of its stored branch history. -/
theorem outward_executableLocalizedRerootChild_parent?_eq_current
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor child : input.LocalizedRerootCursor fuel)
    (childPresent : child ∈ input.executableLocalizedRerootChildren cursor)
    (slot : Nat)
    (childAddress : child.occurrence.1.address = cursor.occurrence.1.address ++ [slot]) :
    child.occurrence.1.node.parent? = cursor.occurrence.1.node.current? := by
  have cursorDerived :=
    (input.mem_localizedOccurrences_iff fuel cursor.occurrence.1).mp cursor.occurrence.2
  have childDerived :=
    (input.mem_localizedOccurrences_iff fuel child.occurrence.1).mp child.occurrence.2
  have childRoot : child.occurrence.1.root = cursor.occurrence.1.root :=
    input.localizedRerootChildren_root_eq cursor child
      (input.executableLocalizedRerootChildren cursor)
      (input.executableLocalizedRerootChildren_declarative cursor) childPresent
  obtain ⟨childNode, childAtSlot, childFrame⟩ :=
    input.declarativeLocalizedOccurrence_immediate_child cursorDerived childDerived
      childRoot slot childAddress
  have childNodeEq : child.occurrence.1.node = childNode := by
    simpa using congrArg LocalizedCIPOccurrenceFrame.node childFrame
  obtain ⟨next, copyIndex, extendEq⟩ :=
    input.eq_extend_of_mem_executableOfficialCIPChildren cursor.occurrence.1.node childNode
      (List.fst_mem_of_mem_zipIdx childAtSlot)
  have headEq := input.declarativeLocalizedOccurrence_history_head_eq_current cursorDerived
  calc
    child.occurrence.1.node.parent? = childNode.parent? := by rw [childNodeEq]
    _ = (cursor.occurrence.1.node.extend next copyIndex).parent? := by rw [extendEq]
    _ = cursor.occurrence.1.node.history.head? :=
      OfficialCIPNode.parent?_extend cursor.occurrence.1.node next copyIndex
    _ = cursor.occurrence.1.node.current? := headEq

/-! ## Physical-continuation uniqueness and the cut atom -/

/-- A physical reference provenance is either a real atom or a ring duplicate. -/
theorem physicalReferenceProvenance_cases
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (physical : LocalizedRule3PhysicalReferenceProvenance
      cursor.occurrence.1.node.provenance) :
    cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∨
      ∃ distance, cursor.occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.ringDuplicate distance := by
  cases provenance : cursor.occurrence.1.node.provenance <;>
    simp [LocalizedRule3PhysicalReferenceProvenance, provenance] at physical ⊢

/-- **Two physical continuations of one cursor carry distinct current atoms.**  Physical-reference
uniqueness at the exact cut-neighbourhood keeps a single physical cursor per requested atom. -/
theorem physicalContinuation_current_ne
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (start first second : input.LocalizedRerootCursor fuel)
    (firstAtom secondAtom : input.Atom)
    (firstPresent : first ∈ input.executableLocalizedRerootChildren start)
    (secondPresent : second ∈ input.executableLocalizedRerootChildren start)
    (firstPhysical : input.LocalizedRule3AxisPhysicalContinuation start first)
    (secondPhysical : input.LocalizedRule3AxisPhysicalContinuation start second)
    (firstCurrent : first.occurrence.1.node.current? = some firstAtom)
    (secondCurrent : second.occurrence.1.node.current? = some secondAtom)
    (firstNeSecond : first ≠ second) :
    firstAtom ≠ secondAtom := by
  intro sameAtom
  obtain ⟨_, firstPhysicalProv, _⟩ := firstPhysical
  obtain ⟨_, secondPhysicalProv, _⟩ := secondPhysical
  have secondCurrentAtFirst : second.occurrence.1.node.current? = some firstAtom := by
    rw [secondCurrent, ← sameAtom]
  have equality : first = second :=
    input.localizedRule3PhysicalReferenceCursor_unique start first second firstAtom
      (input.executableLocalizedRerootChildren start)
      (input.executableLocalizedRerootChildren_declarative start)
      firstPresent secondPresent firstCurrent secondCurrentAtFirst
      firstPhysicalProv secondPhysicalProv
  exact firstNeSecond equality

/-- **The retained right atom is not a physical continuation of the parent-side cursor.**  The
requested occurrence `O` is itself the zero-copy outward child of the parent `P` carrying
`frame.right`; a physical continuation carrying the same atom would have to be the same official
child copy, hence the same sibling slot and address, which the incoming-cut address separation
forbids. -/
theorem carrierParent_right_ne_physicalContinuation_current
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O initial)
    (child : input.LocalizedRerootCursor carrierFuel)
    (childPresent : child ∈ input.executableLocalizedRerootChildren initial.leftCursor)
    (childPhysical : input.LocalizedRule3AxisPhysicalContinuation initial.leftCursor child)
    (childAtom : input.Atom)
    (childCurrent : child.occurrence.1.node.current? = some childAtom) :
    initial.right ≠ childAtom := by
  intro sameAtom
  rcases frameDecl with
    ⟨OReal, OCurrent, _OParent, _OBond, OParentMem, _PCurrent, PPrevious, _ROcc, _RPrev⟩
  have parentFacts := input.localizedCarrierParentFrame_facts O.1
    initial.leftCursor.occurrence.1 OParentMem
  have ONonempty : O.1.address ≠ [] := by
    intro empty
    have lenZero : initial.leftCursor.occurrence.1.address.length + 1 = 0 := by
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
  have OProvNode : ONode.provenance = OfficialCIPNodeProvenance.realAtom ∨
      ∃ distance, ONode.provenance =
        OfficialCIPNodeProvenance.ringDuplicate distance := by
    left
    rw [← ONodeEq]
    exact OReal
  obtain ⟨ONext, OExtend, ONotParent⟩ :=
    input.eq_extend_zero_and_not_parent_of_mem_executableOfficialCIPChildren
      initial.leftCursor.occurrence.1.node ONode
      (List.fst_mem_of_mem_zipIdx OAtSlot) OProvNode
  have OCurrentNode : ONode.current? = some initial.right := by
    rw [← ONodeEq]
    exact OCurrent
  have ONextEq : ONext = initial.right := by
    have observed : some ONext = some initial.right := by
      rw [← OfficialCIPNode.extend_current? initial.leftCursor.occurrence.1.node ONext 0,
        ← OExtend, OCurrentNode]
    exact Option.some.inj observed
  rcases input.executableLocalizedRerootChild_dichotomy initial.leftCursor child
      childPresent with
    ⟨childLen, childParentAddress⟩ | ⟨childSlot, childAddress⟩
  · have childParent := input.endpoint_parent?_eq_of_parent_candidate
      initial.leftCursor child childAtom childCurrent
      (input.localizedRerootChildren_root_eq initial.leftCursor child
        (input.executableLocalizedRerootChildren initial.leftCursor)
        (input.executableLocalizedRerootChildren_declarative initial.leftCursor) childPresent)
      ⟨childLen, childParentAddress⟩
    apply ONotParent
    rw [ONextEq]
    exact childParent.trans (congrArg some sameAtom).symm
  · have childDerived : input.DeclarativeLocalizedOccurrence carrierFuel
        child.occurrence.1 :=
      (input.mem_localizedOccurrences_iff carrierFuel child.occurrence.1).mp
        child.occurrence.2
    have childRoot := input.localizedRerootChildren_root_eq initial.leftCursor child
      (input.executableLocalizedRerootChildren initial.leftCursor)
      (input.executableLocalizedRerootChildren_declarative initial.leftCursor) childPresent
    obtain ⟨childNode, childAtSlot, childFrame⟩ :=
      input.declarativeLocalizedOccurrence_immediate_child PDerived childDerived
        childRoot childSlot childAddress
    have childNodeEq : child.occurrence.1.node = childNode := by
      simpa using congrArg LocalizedCIPOccurrenceFrame.node childFrame
    have childPhysicalProv : LocalizedRule3PhysicalReferenceProvenance
        child.occurrence.1.node.provenance := childPhysical.2.1
    have childProvNode : childNode.provenance = OfficialCIPNodeProvenance.realAtom ∨
        ∃ distance, childNode.provenance =
          OfficialCIPNodeProvenance.ringDuplicate distance := by
      rcases input.physicalReferenceProvenance_cases child childPhysicalProv with
        real | ⟨distance, ring⟩
      · exact Or.inl (by rw [← childNodeEq]; exact real)
      · exact Or.inr ⟨distance, by rw [← childNodeEq]; exact ring⟩
    obtain ⟨childNext, childExtend, _childNotParent⟩ :=
      input.eq_extend_zero_and_not_parent_of_mem_executableOfficialCIPChildren
        initial.leftCursor.occurrence.1.node childNode
        (List.fst_mem_of_mem_zipIdx childAtSlot) childProvNode
    have childCurrentNode : childNode.current? = some childAtom := by
      rw [← childNodeEq]
      exact childCurrent
    have childNextEq : childNext = childAtom := by
      have observed : some childNext = some childAtom := by
        rw [← OfficialCIPNode.extend_current?
          initial.leftCursor.occurrence.1.node childNext 0, ← childExtend, childCurrentNode]
      exact Option.some.inj observed
    have nodeIdentity : childNode = ONode := by
      rw [childExtend, childNextEq, ← sameAtom, ← ONextEq, OExtend]
    have secondAtSlot : (childNode, slotO) ∈
        (input.executableOfficialCIPChildren
          initial.leftCursor.occurrence.1.node).zipIdx := by
      rw [nodeIdentity]
      exact OAtSlot
    have slotsEq : childSlot = slotO :=
      input.physical_executableOfficialCIPChild_slot_unique
        initial.leftCursor.occurrence.1.node childNode childSlot slotO
        childAtSlot secondAtSlot childProvNode
    have sameAddress : child.occurrence.1.address = O.1.address := by
      rw [childAddress, OAddress, slotsEq]
    have childIntended : child.occurrence.1 ∈
        input.intendedLocalizedRerootChildFrames initial.leftCursor := by
      rw [← input.executableLocalizedRerootChildren_map initial.leftCursor]
      exact List.mem_map.mpr ⟨child, childPresent, rfl⟩
    exact input.address_ne_previous_of_mem_intended initial.leftCursor O PPrevious
      child.occurrence.1 childIntended sameAddress

/-- **A terminal cursor has no double-bond edge at an outward physical child.**  The child's
official parent is the terminal cursor's current atom, so a double-bond edge at the child would be
a physical order-two continuation of the terminal, which the declarative terminal frame excludes.
-/
theorem terminal_executableChild_not_doubleBondEdge
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (start : input.LocalizedRerootCursor fuel)
    (terminal : input.DeclarativeLocalizedRule3AxisTopology start .terminal)
    (startAtom childAtom : input.Atom)
    (startCurrent : start.occurrence.1.node.current? = some startAtom)
    (child : input.LocalizedRerootCursor fuel)
    (childPresent : child ∈ input.executableLocalizedRerootChildren start)
    (childPhysical : LocalizedRule3PhysicalReferenceProvenance
      child.occurrence.1.node.provenance)
    (childCurrent : child.occurrence.1.node.current? = some childAtom)
    (slot : Nat)
    (childAddress : child.occurrence.1.address = start.occurrence.1.address ++ [slot]) :
    ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge child.occurrence := by
  intro edge
  obtain ⟨children, childrenComputed, childrenDecl, noPhysical⟩ :=
    DeclarativeLocalizedRule3AxisTopology.terminal_no_physical_continuation input terminal
  have childrenEq : children = input.executableLocalizedRerootChildren start := by
    apply Option.some.inj
    rw [← childrenComputed, input.localizedRerootChildren?_eq_some_executable]
  have childMem : child ∈ children := by
    rw [childrenEq]
    exact childPresent
  have noPhysicalChild := noPhysical child childMem
  have startReal :=
    input.provenance_real_of_mem_executableLocalizedRerootChildren start child childPresent
  have childParent := input.outward_executableLocalizedRerootChild_parent?_eq_current
    start child childPresent slot childAddress
  rcases edge with ⟨_childReal, current, parent, childCurrentEdge, childParentEdge, bond⟩
  have currentEq : current = childAtom :=
    Option.some.inj (childCurrentEdge.symm.trans childCurrent)
  have parentEq : parent = startAtom := by
    have observed : some parent = some startAtom :=
      childParentEdge.symm.trans (childParent.trans startCurrent)
    exact Option.some.inj observed
  have bondStart : input.moleculeGraph.bond startAtom childAtom = 2 := by
    simpa [currentEq, parentEq] using bond
  refine noPhysicalChild ⟨startReal, childPhysical, ?_⟩
  rw [startCurrent, childCurrent]
  exact bondStart

/-- **The unbranched graph domain excludes actual branched axes.**  A declarative branched axis at
the parent-side cursor of a physical endpoint frame supplies two distinct physical continuations
`first`, `second` together with the retained right atom as a third double-bond neighbour of the
parent's current atom.  Physical-reference uniqueness keeps `first` and `second` at distinct
atoms, and the incoming-cut argument keeps the right atom distinct from both; three distinct
order-two neighbours contradict the graph bound. -/
theorem noActualBranchedAxis_of_unbranchedDoubleBondGraph
    (input : CertifiedLocalizedCIPInput)
    (domain : input.LocalizedUnbranchedDoubleBondGraph) :
    input.LocalizedNoActualBranchedAxis := by
  intro carrierFuel occurrence initial first second rest frameDecl branchedAxis
  have frameDeclCopy := frameDecl
  rcases frameDecl with
    ⟨_OReal, _OCurrent, _OParent, OBond, OParentMem, PCurrent, PPrevious, _ROcc, _RPrev⟩
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
    rcases input.eq_of_three_doubleBond_neighbors domain initial.left firstAtom secondAtom
        initial.right firstBond secondBond OBond with same | same | same
    · exact atomsNe same
    · exact rightNeFirst same.symm
    · exact rightNeSecond same.symm







def LocalizedRule3RequestPhase (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (O : input.LocalizedCIPOccurrence fuel)
    (Q : input.LocalizedRerootCursor fuel) : Prop :=
  input.LocalizedRerootCursorValid Q ∧
    Q.occurrence.1.root = O.1.root ∧
    (∃ previous, Q.previous? = some previous ∧
      previous.1.address.length < Q.occurrence.1.address.length) ∧
    (O.1.address.length < Q.occurrence.1.address.length ∨
      (Q.occurrence.1.address.length = O.1.address.length ∧
        ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge Q.occurrence))


theorem phase_of_outward
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (Q : input.LocalizedRerootCursor carrierFuel)
    (outward : OutwardRerootCursor input O Q) :
    input.LocalizedRule3RequestPhase O Q := by
  obtain ⟨valid, ⟨rootEq, deeper⟩, previous, previousEq, shorter⟩ := outward
  exact ⟨valid, rootEq, ⟨previous, previousEq, shorter⟩, Or.inl deeper⟩

/-- **A terminal continuation at successor depth has no double-bond edge.**  An executable
physical child strictly below the terminal cursor either is the carrier-parent coordinate, which is
strictly shorter and contradicts the depth increase, or is an outward child at exactly one slot
below the terminal.  In the outward case the terminal's no-continuation property forbids a
double-bond edge at the child. -/
theorem terminal_child_at_successor_depth
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (start : input.LocalizedRerootCursor carrierFuel)
    (terminal : input.DeclarativeLocalizedRule3AxisTopology start .terminal)
    (startAtom childAtom : input.Atom)
    (startCurrent : start.occurrence.1.node.current? = some startAtom)
    (child : input.LocalizedRerootCursor carrierFuel)
    (childPresent : child ∈ input.executableLocalizedRerootChildren start)
    (childPhysical : LocalizedRule3PhysicalReferenceProvenance
      child.occurrence.1.node.provenance)
    (childCurrent : child.occurrence.1.node.current? = some childAtom)
    (startShorter : start.occurrence.1.address.length <
      child.occurrence.1.address.length)
    (depth : Nat)
    (depthEq : start.occurrence.1.address.length + 1 = depth) :
    child.occurrence.1.address.length = depth ∧
      ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge child.occurrence := by
  rcases input.executableLocalizedRerootChild_dichotomy start child childPresent with
    ⟨parentLength, _parentAddress⟩ | ⟨slot, childAddress⟩
  · omega
  · refine ⟨?_, ?_⟩
    · rw [childAddress, List.length_append]
      simp
      exact depthEq
    · exact input.terminal_executableChild_not_doubleBondEdge start terminal startAtom
        childAtom startCurrent child childPresent childPhysical childCurrent slot childAddress

/-- **The carrier parent of a physical endpoint occurrence is active-simple.**  The requested
occurrence is nonroot because it has a stored parent atom; its unique carrier parent is therefore
the certified active-simple centre. -/
theorem carrierParent_active_of_frame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O initial) :
    initial.leftCursor.occurrence.1.node.ActiveSimple := by
  rcases frameDecl with
    ⟨_OReal, _OCurrent, OParent, _OBond, OParentMem, _PCurrent, _PPrevious,
      _ROcc, _RPrev⟩
  have ONonempty : O.1.address ≠ [] := by
    intro empty
    have derivedO := (input.mem_localizedOccurrences_iff carrierFuel O.1).mp O.2
    have rootFrame :=
      input.declarativeLocalizedOccurrence_eq_root_of_address_nil derivedO empty
    have nodeEq : O.1.node = OfficialCIPNode.root O.1.root :=
      congrArg LocalizedCIPOccurrenceFrame.node rootFrame
    rw [nodeEq] at OParent
    simp [OfficialCIPNode.root, OfficialCIPNode.parent?] at OParent
  have certificateO : input.LocalizedParentFrameHistory O :=
    input.localizedParentFrameHistory O ONonempty
  have parentIsP : certificateO.parent.1 = initial.leftCursor.occurrence.1 := by
    have memP : initial.leftCursor.occurrence.1 ∈
        input.localizedCarrierParentFrames (fuel := carrierFuel) O.1 := OParentMem
    rw [certificateO.carrierParentFrames_eq_singleton input] at memP
    exact (List.mem_singleton.mp memP).symm
  rw [← parentIsP]
  exact certificateO.parent_active






theorem rule3ShortEndpointCallbackRequests_left_phase
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (frameDecl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O initial)
    (terminal : input.DeclarativeLocalizedRule3AxisTopology initial.leftCursor .terminal)
    (startActive : initial.leftCursor.occurrence.1.node.ActiveSimple)
    (request : List (input.LocalizedRerootCursor carrierFuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests
      initial.left initial.right initial.leftCursor)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (cursorMem : cursor ∈ request) :
    input.LocalizedRule3RequestPhase O cursor := by
  rcases frameDecl with
    ⟨_OReal, _OCurrent, _OParent, _OBond, OParentMem, PCurrent, _PPrevious,
      _ROcc, _RPrev⟩
  have parentFacts := input.localizedCarrierParentFrame_facts O.1
    initial.leftCursor.occurrence.1 OParentMem
  have outward := input.rule3ShortEndpointCallbackRequests_left_outward
    initial.leftCursor.occurrence initial.leftCursor initial.left initial.right rfl le_rfl
    startActive request member
  obtain ⟨valid, ⟨rootEq, deeper⟩, previous, previousEq, previousShorter⟩ :=
    outward cursor cursorMem
  obtain ⟨first, second, firstCursor, secondCursor, _subs, firstSel, secondSel,
    _rootCmp, _constCmp, requestEq⟩ :=
    input.rule3ShortEndpointCallbackRequests_structure initial.left initial.right
      initial.leftCursor request member
  rw [requestEq] at cursorMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at cursorMem
  rcases cursorMem with hc | hc <;> subst cursor
  · obtain ⟨firstPresent, _firstPrevious, firstCurrent, firstPhysical⟩ :=
      input.localizedRule3ReferenceCursorExec?_facts initial.leftCursor firstCursor
        first firstSel
    obtain ⟨firstDepth, firstNotDouble⟩ :=
      input.terminal_child_at_successor_depth initial.leftCursor terminal initial.left
        first PCurrent firstCursor firstPresent firstPhysical firstCurrent deeper
        O.1.address.length parentFacts.2.1
    exact ⟨valid, rootEq.trans parentFacts.1,
      ⟨previous, previousEq, previousShorter⟩, Or.inr ⟨firstDepth, firstNotDouble⟩⟩
  · obtain ⟨secondPresent, _secondPrevious, secondCurrent, secondPhysical⟩ :=
      input.localizedRule3ReferenceCursorExec?_facts initial.leftCursor secondCursor
        second secondSel
    obtain ⟨secondDepth, secondNotDouble⟩ :=
      input.terminal_child_at_successor_depth initial.leftCursor terminal initial.left
        second PCurrent secondCursor secondPresent secondPhysical secondCurrent deeper
        O.1.address.length parentFacts.2.1
    exact ⟨valid, rootEq.trans parentFacts.1,
      ⟨previous, previousEq, previousShorter⟩, Or.inr ⟨secondDepth, secondNotDouble⟩⟩

/-- **Right-endpoint requests below an incoming-cut parent are outward.**  The parent coordinate is
the incoming cut and is excluded from the intended child list; every selected reference cursor is
therefore an outward child one slot below the endpoint, hence an outward cursor of any target `T` at
or above the endpoint. -/
theorem rule3ShortEndpointCallbackRequests_right_outward_of_parent
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (T : input.LocalizedCIPOccurrence carrierFuel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : start.previous? = some previous)
    (previousParent : previous.1 ∈ input.localizedCarrierParentFrames
      (fuel := carrierFuel) start.occurrence.1)
    (startRoot : start.occurrence.1.root = T.1.root)
    (startNotShorter : T.1.address.length ≤ start.occurrence.1.address.length)
    (left right : input.Atom)
    (request : List (input.LocalizedRerootCursor carrierFuel))
    (member : request ∈ input.rule3ShortEndpointCallbackRequests left right start) :
    ∀ cursor ∈ request, OutwardRerootCursor input T cursor := by
  intro cursor cursorMem
  obtain ⟨first, second, firstCursor, secondCursor, _subs, firstSel, secondSel,
    _rootCmp, _constCmp, requestEq⟩ :=
    input.rule3ShortEndpointCallbackRequests_structure left right start request member
  rw [requestEq] at cursorMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at cursorMem
  obtain ⟨firstChild, _firstPrevious, _firstCurrent, _firstPhysical⟩ :=
    input.localizedRule3ReferenceCursorExec?_facts start firstCursor first firstSel
  obtain ⟨secondChild, _secondPrevious, _secondCurrent, _secondPhysical⟩ :=
    input.localizedRule3ReferenceCursorExec?_facts start secondCursor second secondSel
  rcases cursorMem with hc | hc <;> subst cursor
  · have notParent := input.executableLocalizedRerootChild_not_parentSide_of_parent
      start previous previousEq previousParent firstCursor firstChild
    rcases input.executableLocalizedRerootChild_dichotomy start firstCursor firstChild with
      ⟨firstLength, _firstAddress⟩ | ⟨slot, firstAddress⟩
    · exact absurd firstLength notParent
    · exact input.outwardRerootCursor_of_cursor_child T start firstCursor startRoot
        startNotShorter firstChild ⟨slot, firstAddress⟩
  · have notParent := input.executableLocalizedRerootChild_not_parentSide_of_parent
      start previous previousEq previousParent secondCursor secondChild
    rcases input.executableLocalizedRerootChild_dichotomy start secondCursor secondChild with
      ⟨secondLength, _secondAddress⟩ | ⟨slot, secondAddress⟩
    · exact absurd secondLength notParent
    · exact input.outwardRerootCursor_of_cursor_child T start secondCursor startRoot
        startNotShorter secondChild ⟨slot, secondAddress⟩









theorem rule3ShortOddCallbackRequests_phase
    (input : CertifiedLocalizedCIPInput) (domain : input.LocalizedUnbranchedDoubleBondGraph)
    {carrierFuel : Nat}
    (O : input.LocalizedCIPOccurrence carrierFuel) :
    ∀ request ∈ input.rule3ShortOddCallbackRequests O,
      ∀ cursor ∈ request, input.LocalizedRule3RequestPhase O cursor := by
  intro request member cursor cursorMem
  unfold rule3ShortOddCallbackRequests at member
  cases computed : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) O with
  | none => simp [computed] at member
  | some topology =>
    simp only [computed] at member
    have originalComputed : input.localizedRule3OddCumuleneEndpointCursorFrame?
        (input.localizedRule3CumulatedTraversalFuel carrierFuel) O = some topology := by
      rw [← input.localizedRule3OddCumuleneEndpointCursorFrameExec?_eq_original
        (input.localizedRule3CumulatedTraversalFuel carrierFuel) O]
      exact computed
    have sound := input.localizedRule3OddCumuleneEndpointCursorFrame?_sound
      (input.localizedRule3CumulatedTraversalFuel carrierFuel) O topology originalComputed
    obtain ⟨physical, terminalLeft, walkDecl, reverseDecl, _rightPartnerCurrent,
      _rightCurrent, _oneLt, _odd⟩ := sound
    obtain ⟨reverseRest, reverseEq⟩ := reverseDecl
    have physicalDecl := physical
    obtain ⟨_realO, _currentO, _parentO, _bondO, parentDecl, _leftCurrent, _leftPrevious,
      rightOccurrence, rightPrevious⟩ := physicalDecl
    have parentFacts := input.localizedCarrierParentFrame_facts O.1
      topology.initial.leftCursor.occurrence.1 parentDecl
    have parentLength : topology.initial.leftCursor.occurrence.1.address.length + 1 =
        O.1.address.length := parentFacts.2.1
    rcases List.mem_append.mp member with leftMember | rightMember
    · exact input.rule3ShortEndpointCallbackRequests_left_phase O topology.initial physical
        terminalLeft (input.carrierParent_active_of_frame O topology.initial physical)
        request leftMember cursor cursorMem
    · have rightCursorMem : topology.rightCursor ∈ topology.rightward := by
        rw [← List.mem_reverse, reverseEq]
        simp
      have partnerMem : topology.rightPartnerCursor ∈ topology.rightward := by
        rw [← List.mem_reverse, reverseEq]
        simp
      have initialOutward : OutwardRerootCursor input
          topology.initial.leftCursor.occurrence topology.initial.rightCursor := by
        have initialValid : input.LocalizedRerootCursorValid topology.initial.rightCursor := by
          have parentInNeighbors : topology.initial.leftCursor.occurrence.1 ∈
              input.localizedRerootNeighborFrames (fuel := carrierFuel) O.1 := by
            rw [localizedRerootNeighborFrames, List.mem_append]
            exact Or.inl parentDecl
          unfold LocalizedRerootCursorValid
          simp only [rightPrevious, rightOccurrence]
          exact input.mem_localizedRerootNeighborFrames_symm O
            topology.initial.leftCursor.occurrence.1 parentInNeighbors
        refine ⟨initialValid, ?_, topology.initial.leftCursor.occurrence, rightPrevious, ?_⟩
        · refine ⟨?_, ?_⟩
          · rw [rightOccurrence]
            exact parentFacts.1.symm
          · rw [rightOccurrence]
            omega
        · rw [rightOccurrence]
          omega
      have allOutward := input.declarativeWalk_cursor_outward
        topology.initial.leftCursor.occurrence topology.initial.rightCursor
        topology.rightward walkDecl initialOutward
      have startOutward : OutwardRerootCursor input
          topology.initial.leftCursor.occurrence topology.rightCursor :=
        allOutward topology.rightCursor rightCursorMem
      have partnerOutward : OutwardRerootCursor input
          topology.initial.leftCursor.occurrence topology.rightPartnerCursor :=
        allOutward topology.rightPartnerCursor partnerMem
      have lastPair := input.declarativeWalk_reverse_last_pair
        topology.initial.rightCursor topology.rightward walkDecl
        topology.rightCursor topology.rightPartnerCursor reverseRest reverseEq
      have edge : E input topology.rightPartnerCursor topology.rightCursor := lastPair.1
      obtain ⟨partnerValid, _partnerDependency, partnerPrevious, partnerPreviousEq,
        partnerShorter⟩ := partnerOutward
      obtain ⟨dropLastStep, _lengthStep, stepRoot, stepPrevious, _stepValid⟩ :=
        outward_edge input topology.rightPartnerCursor topology.rightCursor
          partnerValid partnerPrevious partnerPreviousEq partnerShorter edge
      have previousParent : topology.rightPartnerCursor.occurrence.1 ∈
          input.localizedCarrierParentFrames (fuel := carrierFuel)
            topology.rightCursor.occurrence.1 := by
        rw [localizedCarrierParentFrames, List.mem_filter]
        refine ⟨topology.rightPartnerCursor.occurrence.2, ?_⟩
        simp only [Bool.and_eq_true, beq_iff_eq]
        exact ⟨⟨stepRoot.symm, by omega⟩, dropLastStep.symm⟩
      have startRoot : topology.rightCursor.occurrence.1.root = O.1.root :=
        startOutward.2.1.1.trans parentFacts.1
      have startNotShorter : O.1.address.length ≤
          topology.rightCursor.occurrence.1.address.length := by
        have shorter := startOutward.2.1.2
        omega
      exact input.phase_of_outward O cursor
        (input.rule3ShortEndpointCallbackRequests_right_outward_of_parent O
          topology.rightCursor topology.rightPartnerCursor.occurrence stepPrevious
          previousParent startRoot startNotShorter topology.right topology.rightPartner
          request rightMember cursor cursorMem)

/-- **The ordinary route certificate exposes a terminal physical entry.**  Under the unbranched
double-bond graph domain the certificate cannot have been produced by a branched entry; it was
therefore produced by a terminal entry, whose physical frame is the executable endpoint frame of
the occurrence and whose left cursor carries the declarative terminal topology. -/
theorem ordinaryRouteCertificate_frame_terminal
    (input : CertifiedLocalizedCIPInput) (domain : input.LocalizedUnbranchedDoubleBondGraph)
    {carrierFuel : Nat}
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (certificate : input.LocalizedRule3OrdinaryRouteCertificate O)
    (computed : input.localizedRule3OrdinaryRouteCertificate? O = some certificate) :
    ∃ initial, input.localizedRule3PhysicalEndpointCursorFrameExec? O = some initial ∧
      input.DeclarativeLocalizedRule3AxisTopology initial.leftCursor .terminal := by
  rcases certificate.valid with ⟨_edge, branched | terminal⟩
  · rcases branched with ⟨initial, first, second, rest, entryDecl⟩
    cases entryDecl with
    | branched physical branchTopology =>
        exact False.elim (input.noActualBranchedAxis_of_unbranchedDoubleBondGraph domain
          carrierFuel O initial first second rest physical branchTopology)
  · rcases terminal with ⟨axis, axisDecl, _ordinary⟩
    rcases axisDecl with ⟨entryDecl, _walk, _reverse, _partnerCurrent, _rightCurrent⟩
    cases entryDecl with
    | terminalStart physical terminal =>
        exact ⟨axis.initial, by
          rw [input.localizedRule3PhysicalEndpointCursorFrameExec?_eq_original O]
          exact input.localizedRule3PhysicalEndpointCursorFrame?_eq_some_of_declarative
            O axis.initial physical, terminal⟩





theorem rule3ShortSpatialCallbackRequests_phase
    (input : CertifiedLocalizedCIPInput) (domain : input.LocalizedUnbranchedDoubleBondGraph)
    {carrierFuel : Nat}
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (certificate : input.LocalizedRule3OrdinaryRouteCertificate O)
    (computed : input.localizedRule3OrdinaryRouteCertificate? O = some certificate) :
    ∀ request ∈ input.rule3ShortSpatialCallbackRequests O,
      ∀ cursor ∈ request, input.LocalizedRule3RequestPhase O cursor := by
  intro request member cursor cursorMem
  rcases input.rule3ShortSpatialCallbackRequests_structure O request member with
    ⟨frame, frameComputed, memberLeft | memberRight⟩
  · obtain ⟨initial, initialComputed, terminal⟩ :=
      input.ordinaryRouteCertificate_frame_terminal domain O certificate computed
    have frameEq : frame = initial := by
      rw [frameComputed] at initialComputed
      exact Option.some.inj initialComputed
    have terminalFrame : input.DeclarativeLocalizedRule3AxisTopology
        frame.leftCursor .terminal := by
      rw [frameEq]
      exact terminal
    have frameDecl :=
      input.localizedRule3PhysicalEndpointCursorFrameExec?_sound O frame frameComputed
    exact input.rule3ShortEndpointCallbackRequests_left_phase O frame frameDecl terminalFrame
      (input.carrierParent_active_of_frame O frame frameDecl) request memberLeft cursor cursorMem
  · rcases input.localizedRule3PhysicalEndpointCursorFrameExec?_sound O frame frameComputed with
      ⟨_realO, _currentO, _parentO, _bond, parentDecl, _leftCurrent, _leftPrevious,
        rightOccurrence, rightPrevious⟩
    have parentPresentRight : frame.leftCursor.occurrence.1 ∈
        input.localizedCarrierParentFrames (fuel := carrierFuel)
          frame.rightCursor.occurrence.1 := by
      rw [rightOccurrence]
      exact parentDecl
    have startRoot : frame.rightCursor.occurrence.1.root = O.1.root := by
      rw [rightOccurrence]
    have startNotShorter : O.1.address.length ≤
        frame.rightCursor.occurrence.1.address.length := by
      rw [rightOccurrence]
    exact input.phase_of_outward O cursor
      (input.rule3ShortEndpointCallbackRequests_right_outward_of_parent O frame.rightCursor
        frame.leftCursor.occurrence rightPrevious parentPresentRight startRoot startNotShorter
        frame.right frame.left request memberRight cursor cursorMem)







theorem rule3ExtendedNodeCallbackRequests_phase
    (input : CertifiedLocalizedCIPInput) (domain : input.LocalizedUnbranchedDoubleBondGraph)
    {carrierFuel : Nat}
    (O : input.LocalizedCIPOccurrence carrierFuel) :
    ∀ request ∈ input.rule3ExtendedNodeCallbackRequests O,
      ∀ cursor ∈ request, input.LocalizedRule3RequestPhase O cursor := by
  intro request member cursor cursorMem
  unfold rule3ExtendedNodeCallbackRequests at member
  cases routed : input.localizedRule3OddRouteCertificate? O with
  | some certificate =>
      simp only [routed] at member
      exact input.rule3ShortOddCallbackRequests_phase domain O request member cursor cursorMem
  | none =>
      simp only [routed] at member
      unfold rule3NodeCallbackRequests at member
      cases ordinary : input.localizedRule3OrdinaryRouteCertificate? O with
      | none =>
          have empty := input.rule3OriginalNodeCallbackRequests_eq_nil_of_jointRouteCertificateNone
            O ordinary routed
          simp only [rule3NodeCallbackRequests, ordinary, empty, List.mem_nil_iff] at member
      | some certificate =>
          simp only [ordinary] at member
          exact input.rule3ShortSpatialCallbackRequests_phase domain O certificate ordinary
            request member cursor cursorMem

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.eq_of_three_doubleBond_neighbors
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.DeclarativeLocalizedOccurrenceSubtree_provenance_ne_placeholder
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeLocalizedOccurrence_provenance_ne_placeholder
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.provenance_real_of_mem_executableLocalizedRerootChildren
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.OfficialCIPNode.parent?_extend
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outward_executableLocalizedRerootChild_parent?_eq_current
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.physicalReferenceProvenance_cases
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.physicalContinuation_current_ne
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.carrierParent_right_ne_physicalContinuation_current
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminal_executableChild_not_doubleBondEdge
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.noActualBranchedAxis_of_unbranchedDoubleBondGraph
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.phase_of_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminal_child_at_successor_depth
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.carrierParent_active_of_frame
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortEndpointCallbackRequests_left_phase
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortEndpointCallbackRequests_right_outward_of_parent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortOddCallbackRequests_phase
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ordinaryRouteCertificate_frame_terminal
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ShortSpatialCallbackRequests_phase
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule3ExtendedNodeCallbackRequests_phase
