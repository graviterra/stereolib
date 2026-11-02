import TetraStereo.OneCenter.LocalizedOccurrenceCarrier

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-!
# Executable refinements of the true-choice localized child slots

`LocalizedOccurrenceCarrier` pins three distinguished physical children to sibling slots using
`Classical.choose` on an existence proof:

* the first child of a perceived open even-cumulene axis,
* the first child of a maximal open consecutive-double-bond root, and
* the first child of a canonically oriented physical double bond.

Those choices are sound but not executable.  This module supplies computable replacements that
compute each slot as `List.idxOf child (input.executableOfficialCIPChildren root)`.

The executable child list is *not* required to be `Nodup`: positive multiple-bond copies may be
structurally equal, and `List.idxOf` merely selects the leftmost matching copy.  For *physical*
children (`realAtom` or `ringDuplicate` provenance) the existing
`physical_executableOfficialCIPChild_slot_unique` theorem shows that the sibling slot is unique,
so the leftmost index coincides with the previous `Classical.choose` slot and with every other
witness of membership.
-/

/-- The `List.idxOf` slot of any executable child is itself a valid indexed sibling slot: the
child really is the element stored at that index. -/
theorem executableOfficialCIPChild_idxOf_mem
    (input : CertifiedLocalizedCIPInput)
    (node child : OfficialCIPNode input.Atom)
    (childPresent : child ∈ input.executableOfficialCIPChildren node) :
    (child, List.idxOf child (input.executableOfficialCIPChildren node)) ∈
      (input.executableOfficialCIPChildren node).zipIdx := by
  apply (List.mem_zipIdx_iff_getElem?).mpr
  exact List.getElem?_idxOf childPresent

/-- The `List.idxOf` slot of any executable child is strictly below the child-list length. -/
theorem executableOfficialCIPChild_idxOf_lt
    (input : CertifiedLocalizedCIPInput)
    (node child : OfficialCIPNode input.Atom)
    (childPresent : child ∈ input.executableOfficialCIPChildren node) :
    List.idxOf child (input.executableOfficialCIPChildren node) <
      (input.executableOfficialCIPChildren node).length :=
  List.idxOf_lt_length_of_mem childPresent

/-- For a physical executable child, the leftmost `List.idxOf` slot equals any sibling slot
witnessing membership in the executable child list. -/
theorem physical_executableOfficialCIPChild_idxOf_eq_slot
    (input : CertifiedLocalizedCIPInput)
    (node child : OfficialCIPNode input.Atom) (slot : Nat)
    (childPresent : child ∈ input.executableOfficialCIPChildren node)
    (atSlot : (child, slot) ∈ (input.executableOfficialCIPChildren node).zipIdx)
    (physical : child.provenance = OfficialCIPNodeProvenance.realAtom ∨
      ∃ distance, child.provenance =
        OfficialCIPNodeProvenance.ringDuplicate distance) :
    List.idxOf child (input.executableOfficialCIPChildren node) = slot := by
  have idxOfMem : (child, List.idxOf child (input.executableOfficialCIPChildren node)) ∈
      (input.executableOfficialCIPChildren node).zipIdx :=
    input.executableOfficialCIPChild_idxOf_mem node child childPresent
  exact input.physical_executableOfficialCIPChild_slot_unique node child
    (List.idxOf child (input.executableOfficialCIPChildren node)) slot
    idxOfMem atSlot physical

/-! ## Even-axial first child -/

/-- The even-axial first child is a physical real zero-copy node. -/
theorem localizedEvenAxialFirstChildNode_provenance
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain) :
    (input.localizedEvenAxialFirstChildNode axis.1).provenance =
      OfficialCIPNodeProvenance.realAtom := by
  have axisValid := (input.mem_localizedEvenAxialChains_iff axis.1).mp axis.2
  have doubleBond := axisValid.1.1.1
  have distinct : axis.1.root.firstAxis ≠ axis.1.root.terminal := by
    intro equal
    rw [equal] at doubleBond
    simp [input.moleculeGraph.bond_self] at doubleBond
  simp [localizedEvenAxialFirstChildNode, OfficialCIPNode.extend,
    OfficialCIPNode.childProvenance, OfficialCIPNode.root, distinct]

/-- Executable sibling slot of the real zero-copy child entering a perceived even axis. -/
def localizedEvenAxialFirstChildSlotExec
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain) : Nat :=
  List.idxOf (input.localizedEvenAxialFirstChildNode axis.1)
    (input.executableOfficialCIPChildren (OfficialCIPNode.root axis.1.root.terminal))

/-- The executable even-axial slot is backed by the executable official child enumeration. -/
theorem localizedEvenAxialFirstChildSlotExec_mem
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain) :
    (input.localizedEvenAxialFirstChildNode axis.1,
        input.localizedEvenAxialFirstChildSlotExec axis) ∈
      (input.executableOfficialCIPChildren
        (OfficialCIPNode.root axis.1.root.terminal)).zipIdx := by
  unfold localizedEvenAxialFirstChildSlotExec
  exact input.executableOfficialCIPChild_idxOf_mem
    (OfficialCIPNode.root axis.1.root.terminal)
    (input.localizedEvenAxialFirstChildNode axis.1)
    (input.localizedEvenAxialFirstChildNode_mem axis.1
      ((input.mem_localizedEvenAxialChains_iff axis.1).mp axis.2))

/-- The executable even-axial slot is strictly below the executable child-list length. -/
theorem localizedEvenAxialFirstChildSlotExec_lt
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain) :
    input.localizedEvenAxialFirstChildSlotExec axis <
      (input.executableOfficialCIPChildren
        (OfficialCIPNode.root axis.1.root.terminal)).length := by
  unfold localizedEvenAxialFirstChildSlotExec
  exact input.executableOfficialCIPChild_idxOf_lt
    (OfficialCIPNode.root axis.1.root.terminal)
    (input.localizedEvenAxialFirstChildNode axis.1)
    (input.localizedEvenAxialFirstChildNode_mem axis.1
      ((input.mem_localizedEvenAxialChains_iff axis.1).mp axis.2))

/-- The executable even-axial slot equals the previous `Classical.choose` slot. -/
theorem localizedEvenAxialFirstChildSlotExec_eq
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain) :
    input.localizedEvenAxialFirstChildSlotExec axis =
      input.localizedEvenAxialFirstChildSlot axis := by
  unfold localizedEvenAxialFirstChildSlotExec
  exact input.physical_executableOfficialCIPChild_idxOf_eq_slot
    (OfficialCIPNode.root axis.1.root.terminal)
    (input.localizedEvenAxialFirstChildNode axis.1)
    (input.localizedEvenAxialFirstChildSlot axis)
    (input.localizedEvenAxialFirstChildNode_mem axis.1
      ((input.mem_localizedEvenAxialChains_iff axis.1).mp axis.2))
    (input.localizedEvenAxialFirstChildSlot_mem axis)
    (Or.inl (input.localizedEvenAxialFirstChildNode_provenance axis))

/-- Distinguished real child occurrence entering a perceived even axis, reconstructed with the
executable slot. -/
def localizedEvenAxialFirstChildOccurrenceExec
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) :
    input.LocalizedCIPOccurrence fuel := by
  let slot := input.localizedEvenAxialFirstChildSlotExec axis
  let child := input.localizedEvenAxialFirstChildNode axis.1
  refine ⟨
    { root := axis.1.root.terminal
      address := [slot]
      node := child
      remaining := fuel }, ?_⟩
  apply (input.mem_localizedOccurrences_iff fuel _).mpr
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input.localizedEvenAxialFirstChildSlotExec_mem axis)
    (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [slot] fuel child)

@[simp] theorem localizedEvenAxialFirstChildOccurrenceExec_root
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) :
    (input.localizedEvenAxialFirstChildOccurrenceExec fuel axis).1.root =
      axis.1.root.terminal := rfl

@[simp] theorem localizedEvenAxialFirstChildOccurrenceExec_address
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) :
    (input.localizedEvenAxialFirstChildOccurrenceExec fuel axis).1.address =
      [input.localizedEvenAxialFirstChildSlotExec axis] := rfl

@[simp] theorem localizedEvenAxialFirstChildOccurrenceExec_node
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) :
    (input.localizedEvenAxialFirstChildOccurrenceExec fuel axis).1.node =
      input.localizedEvenAxialFirstChildNode axis.1 := rfl

@[simp] theorem localizedEvenAxialFirstChildOccurrenceExec_remaining
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) :
    (input.localizedEvenAxialFirstChildOccurrenceExec fuel axis).1.remaining =
      fuel := rfl

/-- The executable occurrence is exactly the previously selected occurrence. -/
theorem localizedEvenAxialFirstChildOccurrenceExec_eq
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) :
    input.localizedEvenAxialFirstChildOccurrenceExec fuel axis =
      input.localizedEvenAxialFirstChildOccurrence fuel axis := by
  apply Subtype.ext
  apply LocalizedCIPOccurrenceFrame.ext
  · rfl
  · simp [input.localizedEvenAxialFirstChildSlotExec_eq axis]
  · rfl
  · rfl

/-! ## Axial-root first child -/

/-- The axial-root first child is a physical real zero-copy node. -/
theorem localizedAxialRootFirstChildNode_provenance
    (input : CertifiedLocalizedCIPInput)
    (root : input.LocalizedAxialRoot) :
    (input.localizedAxialRootFirstChildNode root).provenance =
      OfficialCIPNodeProvenance.realAtom := by
  have rootValid := (input.mem_localizedAxialRootCandidates_iff root.1).mp root.2
  have doubleBond := rootValid.1
  have distinct : root.1.firstAxis ≠ root.1.terminal := by
    intro equal
    rw [equal] at doubleBond
    simp [input.moleculeGraph.bond_self] at doubleBond
  simp [localizedAxialRootFirstChildNode, OfficialCIPNode.extend,
    OfficialCIPNode.childProvenance, OfficialCIPNode.root, distinct]

/-- Executable sibling slot of the real zero-copy child entering a maximal open chain. -/
def localizedAxialRootFirstChildSlotExec
    (input : CertifiedLocalizedCIPInput)
    (root : input.LocalizedAxialRoot) : Nat :=
  List.idxOf (input.localizedAxialRootFirstChildNode root)
    (input.executableOfficialCIPChildren (OfficialCIPNode.root root.1.terminal))

/-- The executable axial-root slot is backed by the executable official child enumeration. -/
theorem localizedAxialRootFirstChildSlotExec_mem
    (input : CertifiedLocalizedCIPInput)
    (root : input.LocalizedAxialRoot) :
    (input.localizedAxialRootFirstChildNode root,
        input.localizedAxialRootFirstChildSlotExec root) ∈
      (input.executableOfficialCIPChildren
        (OfficialCIPNode.root root.1.terminal)).zipIdx := by
  unfold localizedAxialRootFirstChildSlotExec
  exact input.executableOfficialCIPChild_idxOf_mem
    (OfficialCIPNode.root root.1.terminal)
    (input.localizedAxialRootFirstChildNode root)
    (input.localizedAxialRootFirstChildNode_mem root)

/-- The executable axial-root slot is strictly below the executable child-list length. -/
theorem localizedAxialRootFirstChildSlotExec_lt
    (input : CertifiedLocalizedCIPInput)
    (root : input.LocalizedAxialRoot) :
    input.localizedAxialRootFirstChildSlotExec root <
      (input.executableOfficialCIPChildren
        (OfficialCIPNode.root root.1.terminal)).length := by
  unfold localizedAxialRootFirstChildSlotExec
  exact input.executableOfficialCIPChild_idxOf_lt
    (OfficialCIPNode.root root.1.terminal)
    (input.localizedAxialRootFirstChildNode root)
    (input.localizedAxialRootFirstChildNode_mem root)

/-- The executable axial-root slot equals the previous `Classical.choose` slot. -/
theorem localizedAxialRootFirstChildSlotExec_eq
    (input : CertifiedLocalizedCIPInput)
    (root : input.LocalizedAxialRoot) :
    input.localizedAxialRootFirstChildSlotExec root =
      input.localizedAxialRootFirstChildSlot root := by
  unfold localizedAxialRootFirstChildSlotExec
  exact input.physical_executableOfficialCIPChild_idxOf_eq_slot
    (OfficialCIPNode.root root.1.terminal)
    (input.localizedAxialRootFirstChildNode root)
    (input.localizedAxialRootFirstChildSlot root)
    (input.localizedAxialRootFirstChildNode_mem root)
    (input.localizedAxialRootFirstChildSlot_mem root)
    (Or.inl (input.localizedAxialRootFirstChildNode_provenance root))

/-- Distinguished real child occurrence entering a maximal open chain, reconstructed with the
executable slot. -/
def localizedAxialRootFirstChildOccurrenceExec
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (root : input.LocalizedAxialRoot) :
    input.LocalizedCIPOccurrence fuel := by
  let slot := input.localizedAxialRootFirstChildSlotExec root
  let child := input.localizedAxialRootFirstChildNode root
  refine ⟨
    { root := root.1.terminal
      address := [slot]
      node := child
      remaining := fuel }, ?_⟩
  apply (input.mem_localizedOccurrences_iff fuel _).mpr
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input.localizedAxialRootFirstChildSlotExec_mem root)
    (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [slot] fuel child)

@[simp] theorem localizedAxialRootFirstChildOccurrenceExec_root
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (root : input.LocalizedAxialRoot) :
    (input.localizedAxialRootFirstChildOccurrenceExec fuel root).1.root =
      root.1.terminal := rfl

@[simp] theorem localizedAxialRootFirstChildOccurrenceExec_address
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (root : input.LocalizedAxialRoot) :
    (input.localizedAxialRootFirstChildOccurrenceExec fuel root).1.address =
      [input.localizedAxialRootFirstChildSlotExec root] := rfl

@[simp] theorem localizedAxialRootFirstChildOccurrenceExec_node
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (root : input.LocalizedAxialRoot) :
    (input.localizedAxialRootFirstChildOccurrenceExec fuel root).1.node =
      input.localizedAxialRootFirstChildNode root := rfl

@[simp] theorem localizedAxialRootFirstChildOccurrenceExec_remaining
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (root : input.LocalizedAxialRoot) :
    (input.localizedAxialRootFirstChildOccurrenceExec fuel root).1.remaining =
      fuel := rfl

/-- The executable occurrence is exactly the previously selected occurrence. -/
theorem localizedAxialRootFirstChildOccurrenceExec_eq
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (root : input.LocalizedAxialRoot) :
    input.localizedAxialRootFirstChildOccurrenceExec fuel root =
      input.localizedAxialRootFirstChildOccurrence fuel root := by
  apply Subtype.ext
  apply LocalizedCIPOccurrenceFrame.ext
  · rfl
  · simp [input.localizedAxialRootFirstChildSlotExec_eq root]
  · rfl
  · rfl

/-! ## Canonical double-bond first child -/

/-- The canonical double-bond first child is a physical real zero-copy node. -/
theorem localizedCanonicalDoubleBondFirstChildNode_provenance
    (input : CertifiedLocalizedCIPInput)
    (bond : input.LocalizedCanonicalDoubleBond) :
    (input.localizedCanonicalDoubleBondFirstChildNode bond).provenance =
      OfficialCIPNodeProvenance.realAtom := by
  have bondFacts :=
    (input.mem_localizedCanonicalDoubleBondPairs_iff bond.1.1 bond.1.2).mp bond.2
  have distinct : bond.1.2 ≠ bond.1.1 := ne_of_gt bondFacts.1
  simp [localizedCanonicalDoubleBondFirstChildNode, OfficialCIPNode.extend,
    OfficialCIPNode.childProvenance, OfficialCIPNode.root, distinct]

/-- Executable sibling slot of the real zero-copy child entering a canonical double bond. -/
def localizedCanonicalDoubleBondFirstChildSlotExec
    (input : CertifiedLocalizedCIPInput)
    (bond : input.LocalizedCanonicalDoubleBond) : Nat :=
  List.idxOf (input.localizedCanonicalDoubleBondFirstChildNode bond)
    (input.executableOfficialCIPChildren (OfficialCIPNode.root bond.1.1))

/-- The executable double-bond slot is backed by the executable official child enumeration. -/
theorem localizedCanonicalDoubleBondFirstChildSlotExec_mem
    (input : CertifiedLocalizedCIPInput)
    (bond : input.LocalizedCanonicalDoubleBond) :
    (input.localizedCanonicalDoubleBondFirstChildNode bond,
        input.localizedCanonicalDoubleBondFirstChildSlotExec bond) ∈
      (input.executableOfficialCIPChildren
        (OfficialCIPNode.root bond.1.1)).zipIdx := by
  unfold localizedCanonicalDoubleBondFirstChildSlotExec
  exact input.executableOfficialCIPChild_idxOf_mem
    (OfficialCIPNode.root bond.1.1)
    (input.localizedCanonicalDoubleBondFirstChildNode bond)
    (input.localizedCanonicalDoubleBondFirstChildNode_mem bond)

/-- The executable double-bond slot is strictly below the executable child-list length. -/
theorem localizedCanonicalDoubleBondFirstChildSlotExec_lt
    (input : CertifiedLocalizedCIPInput)
    (bond : input.LocalizedCanonicalDoubleBond) :
    input.localizedCanonicalDoubleBondFirstChildSlotExec bond <
      (input.executableOfficialCIPChildren
        (OfficialCIPNode.root bond.1.1)).length := by
  unfold localizedCanonicalDoubleBondFirstChildSlotExec
  exact input.executableOfficialCIPChild_idxOf_lt
    (OfficialCIPNode.root bond.1.1)
    (input.localizedCanonicalDoubleBondFirstChildNode bond)
    (input.localizedCanonicalDoubleBondFirstChildNode_mem bond)

/-- The executable double-bond slot equals the previous `Classical.choose` slot. -/
theorem localizedCanonicalDoubleBondFirstChildSlotExec_eq
    (input : CertifiedLocalizedCIPInput)
    (bond : input.LocalizedCanonicalDoubleBond) :
    input.localizedCanonicalDoubleBondFirstChildSlotExec bond =
      input.localizedCanonicalDoubleBondFirstChildSlot bond := by
  unfold localizedCanonicalDoubleBondFirstChildSlotExec
  exact input.physical_executableOfficialCIPChild_idxOf_eq_slot
    (OfficialCIPNode.root bond.1.1)
    (input.localizedCanonicalDoubleBondFirstChildNode bond)
    (input.localizedCanonicalDoubleBondFirstChildSlot bond)
    (input.localizedCanonicalDoubleBondFirstChildNode_mem bond)
    (input.localizedCanonicalDoubleBondFirstChildSlot_mem bond)
    (Or.inl (input.localizedCanonicalDoubleBondFirstChildNode_provenance bond))

/-- Distinguished real child occurrence representing a canonical double bond, reconstructed with
the executable slot. -/
def localizedCanonicalDoubleBondFirstChildOccurrenceExec
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond) :
    input.LocalizedCIPOccurrence fuel := by
  let slot := input.localizedCanonicalDoubleBondFirstChildSlotExec bond
  let child := input.localizedCanonicalDoubleBondFirstChildNode bond
  refine ⟨
    { root := bond.1.1
      address := [slot]
      node := child
      remaining := fuel }, ?_⟩
  apply (input.mem_localizedOccurrences_iff fuel _).mpr
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input.localizedCanonicalDoubleBondFirstChildSlotExec_mem bond)
    (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [slot] fuel child)

@[simp] theorem localizedCanonicalDoubleBondFirstChildOccurrenceExec_root
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond) :
    (input.localizedCanonicalDoubleBondFirstChildOccurrenceExec fuel bond).1.root =
      bond.1.1 := rfl

@[simp] theorem localizedCanonicalDoubleBondFirstChildOccurrenceExec_address
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond) :
    (input.localizedCanonicalDoubleBondFirstChildOccurrenceExec fuel bond).1.address =
      [input.localizedCanonicalDoubleBondFirstChildSlotExec bond] := rfl

@[simp] theorem localizedCanonicalDoubleBondFirstChildOccurrenceExec_node
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond) :
    (input.localizedCanonicalDoubleBondFirstChildOccurrenceExec fuel bond).1.node =
      input.localizedCanonicalDoubleBondFirstChildNode bond := rfl

@[simp] theorem localizedCanonicalDoubleBondFirstChildOccurrenceExec_remaining
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond) :
    (input.localizedCanonicalDoubleBondFirstChildOccurrenceExec fuel bond).1.remaining =
      fuel := rfl

/-- The executable occurrence is exactly the previously selected occurrence. -/
theorem localizedCanonicalDoubleBondFirstChildOccurrenceExec_eq
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond) :
    input.localizedCanonicalDoubleBondFirstChildOccurrenceExec fuel bond =
      input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond := by
  apply Subtype.ext
  apply LocalizedCIPOccurrenceFrame.ext
  · rfl
  · simp [input.localizedCanonicalDoubleBondFirstChildSlotExec_eq bond]
  · rfl
  · rfl

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
