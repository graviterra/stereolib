import TetraStereo.OneCenter.LocalizedRerootChildrenExecutable
import TetraStereo.OneCenter.LocalizedRule3OccurrenceReferenceCursor
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Carrier parent frames and their branch histories

`LocalizedOccurrenceCarrier` enumerates proof-relevant occurrences with exact provenance nodes
and histories.  `LocalizedOccurrenceRerootFrame` and `LocalizedRerootChildrenExecutable` expose
the finite carrier tree and its total executable zipper expansion.

The present module proves the *parent-side* structural facts of that tree.  For every reachable
carrier occurrence whose sibling address is not the root address:

* there is an actual carrier occurrence at `target.address.dropLast` with the same root, the exact
  one-step `remaining` increment, real (`realAtom`) provenance, and a duplicate-free history;
* the target node is the parent node extended by exactly one atom, so the parent's stored history
  is precisely the tail of the target history:
  `target.node.history = current :: parentCurrent :: tail` with
  `parent.node.history = parentCurrent :: tail`;
* the parent coordinate is unique, so the certificate is a function of the target;
* the parent distance in the carrier tree is exactly one.

These are the facts needed to instantiate a "parent distance" primitive from actual carrier
membership rather than from a supplied exact-history assumption.  The same result is transported
to reroot cursors: an executable reroot child reached in the outward direction records its source
cursor as `previous?`, and that `previous?` coordinate is exactly the carrier parent frame of the
child occurrence.  This covers the `previous = context` instantiation of the primitive.

Everything is derived from the declarative reachability relation of
`LocalizedOccurrenceCarrier`, by induction on the actual derivation.  No carrier is traversed with
a decision procedure, no exact-history premise is assumed, and no child list is inspected
element-by-element at runtime.
-/

namespace CertifiedLocalizedCIPInput

/-! ## Executable children are `extend` steps -/

/-- Every executable official child is the `extend` of its parent node at some atom and copy
index.  This is read directly from the executable child enumeration; an occurrence that has no
children (a duplicate leaf) cannot be the parent of a derivation step. -/
theorem mem_executableOfficialCIPChildren_extend
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

/-- An executable child that itself has an executable child is active simple: real provenance and
a duplicate-free history.  The premise that the child has a child rules out both duplicate kinds,
because duplicate leaves have empty executable child lists.  This is the structural fact that
makes every carrier parent frame (rather than only the target) provenance-bearing. -/
theorem activeSimple_of_mem_executableOfficialCIPChildren_of_hasChild
    (input : CertifiedLocalizedCIPInput)
    {parent child : OfficialCIPNode input.Atom}
    (parentActive : parent.ActiveSimple)
    (present : child ∈ input.executableOfficialCIPChildren parent)
    (hasChild : ∃ grandchild slot,
      (grandchild, slot) ∈
        (input.executableOfficialCIPChildren child).zipIdx) :
    child.ActiveSimple := by
  obtain ⟨parentReal, parentNodup⟩ := parentActive
  obtain ⟨next, copyIndex, childExtend⟩ :=
    input.mem_executableOfficialCIPChildren_extend parent child present
  obtain ⟨grandchild, slot, grandchildAtSlot⟩ := hasChild
  rw [childExtend] at grandchildAtSlot ⊢
  by_cases zero : copyIndex = 0
  · by_cases visited : next ∈ parent.history
    · exfalso
      have duplicate : (parent.extend next 0).isDuplicateLeaf = true := by
        simp [OfficialCIPNode.isDuplicateLeaf, OfficialCIPNode.extend_provenance,
          OfficialCIPNode.childProvenance, visited]
      have empty : input.executableOfficialCIPChildren (parent.extend next 0) = [] := by
        simp [executableOfficialCIPChildren, duplicate]
      rw [zero] at grandchildAtSlot
      rw [empty] at grandchildAtSlot
      simp at grandchildAtSlot
    · refine ⟨?_, ?_⟩
      · simpa [zero, OfficialCIPNode.extend_provenance] using
          OfficialCIPNode.childProvenance_real parent next visited
      · simpa [zero, OfficialCIPNode.extend_history] using
          (List.nodup_cons.mpr ⟨visited, parentNodup⟩)
  · exfalso
    have duplicate : (parent.extend next copyIndex).isDuplicateLeaf = true := by
      simp [OfficialCIPNode.isDuplicateLeaf, OfficialCIPNode.extend_provenance,
        OfficialCIPNode.childProvenance, zero]
    have empty : input.executableOfficialCIPChildren (parent.extend next copyIndex) = [] := by
      simp [executableOfficialCIPChildren, duplicate]
    rw [empty] at grandchildAtSlot
    simp at grandchildAtSlot

/-! ## Node histories start at the current atom -/

/-- A derivation's node remembers its current atom as the head of the stored branch history,
provided the subtree root does.  This is preserved by every official `extend` step. -/
theorem DeclarativeLocalizedOccurrenceSubtree.node_history_head_eq_current
    (input : CertifiedLocalizedCIPInput)
    {root : input.Atom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode input.Atom}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrenceSubtree root path fuel node occurrence)
    (rootHead : node.history.head? = node.current?) :
    occurrence.node.history.head? = occurrence.node.current? := by
  induction derived with
  | subtreeRoot => exact rootHead
  | @subtreeDescendant path fuel node child slot occurrence childAtSlot below ih =>
      apply ih
      obtain ⟨next, copyIndex, childExtend⟩ :=
        input.mem_executableOfficialCIPChildren_extend node child
          (List.fst_mem_of_mem_zipIdx childAtSlot)
      rw [childExtend]
      simp [OfficialCIPNode.extend_history]

/-- A derivation's node is atom-bearing whenever the subtree root is.  In particular every
carrier occurrence has `current? = some atom`. -/
theorem DeclarativeLocalizedOccurrenceSubtree.node_current_isSome
    (input : CertifiedLocalizedCIPInput)
    {root : input.Atom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode input.Atom}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrenceSubtree root path fuel node occurrence)
    (rootCurrent : node.current?.isSome = true) :
    occurrence.node.current?.isSome = true := by
  induction derived with
  | subtreeRoot => exact rootCurrent
  | @subtreeDescendant path fuel node child slot occurrence childAtSlot below ih =>
      apply ih
      obtain ⟨next, copyIndex, childExtend⟩ :=
        input.mem_executableOfficialCIPChildren_extend node child
          (List.fst_mem_of_mem_zipIdx childAtSlot)
      rw [childExtend]
      rfl

/-- Every molecule-wide carrier occurrence remembers its current atom as the history head. -/
theorem declarativeLocalizedOccurrence_node_history_head_eq_current
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrence fuel occurrence) :
    occurrence.node.history.head? = occurrence.node.current? := by
  have rooted := input.declarativeLocalizedOccurrence_as_rootSubtree derived
  exact DeclarativeLocalizedOccurrenceSubtree.node_history_head_eq_current input rooted
    (by simp [OfficialCIPNode.root])

/-- Every molecule-wide carrier occurrence is atom-bearing. -/
theorem declarativeLocalizedOccurrence_node_current_isSome
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrence fuel occurrence) :
    occurrence.node.current?.isSome = true := by
  have rooted := input.declarativeLocalizedOccurrence_as_rootSubtree derived
  exact DeclarativeLocalizedOccurrenceSubtree.node_current_isSome input rooted
    (by simp [OfficialCIPNode.root])

/-! ## Inverting one derivation step to recover the parent frame -/

/-- A subtree derivation with a non-root occurrence cannot stop at its root constructor; the
occurrence is then strictly below the subtree root, so the derivation has an executable first
step. -/
theorem declarativeSubtree_has_executableChild_of_address_ne
    (input : CertifiedLocalizedCIPInput)
    {root : input.Atom} {path : List Nat} {fuel : Nat}
    {child : OfficialCIPNode input.Atom} {slot : Nat}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (below : input.DeclarativeLocalizedOccurrenceSubtree root (path ++ [slot]) fuel child
      occurrence)
    (ne : occurrence.address ≠ path ++ [slot]) :
    ∃ grandchild grandSlot,
      (grandchild, grandSlot) ∈
        (input.executableOfficialCIPChildren child).zipIdx := by
  cases below with
  | subtreeRoot => exact absurd rfl ne
  | subtreeDescendant childAtSlot rest => exact ⟨_, _, childAtSlot⟩

/-- **Parent-frame inversion of a declarative occurrence derivation.**  If the derivation has an
active-simple subtree root and the occurrence lies strictly below that root, then the immediate
carrier parent is itself a derived occurrence of the same bounded subtree.  The parent has the
same root, the `dropLast` address, remaining depth one larger, active-simple provenance, and its
stored history is exactly the tail of the target's history after the target's current atom. -/
theorem declarativeSubtree_exists_active_parent
    (input : CertifiedLocalizedCIPInput)
    {root : input.Atom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode input.Atom}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrenceSubtree root path fuel node occurrence)
    (rootActive : node.ActiveSimple)
    (belowRoot : occurrence.address ≠ path) :
    ∃ parent : input.LocalizedCIPOccurrenceFrame,
      input.DeclarativeLocalizedOccurrenceSubtree root path fuel node parent ∧
      parent.root = occurrence.root ∧
      parent.address = occurrence.address.dropLast ∧
      parent.remaining = occurrence.remaining + 1 ∧
      parent.node.ActiveSimple ∧
      (∃ next copyIndex, occurrence.node = parent.node.extend next copyIndex) ∧
      ∃ current, occurrence.node.current? = some current ∧
        occurrence.node.history = current :: parent.node.history := by
  induction derived with
  | subtreeRoot =>
      exact absurd rfl belowRoot
  | @subtreeDescendant path fuel node child slot occurrence childAtSlot below ih =>
      by_cases direct : occurrence.address = path ++ [slot]
      · -- The occurrence is exactly the direct executable child of the subtree root.
        have rootFrame := input.declarativeLocalizedOccurrenceSubtree_eq_root_of_address_eq
          below direct
        obtain ⟨next, copyIndex, childExtend⟩ :=
          input.mem_executableOfficialCIPChildren_extend node child
            (List.fst_mem_of_mem_zipIdx childAtSlot)
        refine ⟨{ root := root, address := path, node := node, remaining := fuel + 1 },
          DeclarativeLocalizedOccurrenceSubtree.subtreeRoot path (fuel + 1) node,
          ?_, ?_, ?_, rootActive, ⟨next, copyIndex, ?_⟩, ⟨next, ?_, ?_⟩⟩
        · rw [rootFrame]
        · rw [direct]
          simp
        · rw [rootFrame]
        · rw [rootFrame]
          exact childExtend
        · rw [rootFrame, childExtend]
          rfl
        · rw [rootFrame, childExtend]
          rfl
      · -- The occurrence is strictly below the executable child; recurse into that subtree.
        have childHasChild :
            ∃ grandchild grandSlot,
              (grandchild, grandSlot) ∈
                (input.executableOfficialCIPChildren child).zipIdx :=
          input.declarativeSubtree_has_executableChild_of_address_ne below direct
        have childActive : child.ActiveSimple :=
          input.activeSimple_of_mem_executableOfficialCIPChildren_of_hasChild
            rootActive (List.fst_mem_of_mem_zipIdx childAtSlot) childHasChild
        obtain ⟨parent, parentDerived, parentRoot, parentAddress, parentRemaining,
          parentActive, parentExtend, current, currentEq, historyEq⟩ :=
          ih childActive direct
        exact ⟨parent,
          DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant childAtSlot parentDerived,
          parentRoot, parentAddress, parentRemaining, parentActive, parentExtend,
          current, currentEq, historyEq⟩

/-! ## Reachable carrier occurrences have actual parent frames -/

/-- **Frame-level parent-frame existence.**  Every occurrence of the finite molecule-wide carrier
whose sibling address is non-root has a parent frame that is itself a carrier member.  The parent
has real provenance, a duplicate-free history, and its history is the tail of the target history
after the target's current atom.  The proof inverts the actual declarative derivation; it does
not scan the carrier and does not assume an exact history. -/
theorem exists_parentFrame_of_mem_localizedOccurrences
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrenceFrame}
    (present : target ∈ input.localizedOccurrences fuel)
    (nonroot : target.address ≠ []) :
    ∃ parent : input.LocalizedCIPOccurrenceFrame,
      parent ∈ input.localizedOccurrences fuel ∧
      parent.root = target.root ∧
      parent.address = target.address.dropLast ∧
      parent.remaining = target.remaining + 1 ∧
      parent.node.ActiveSimple ∧
      (∃ next copyIndex, target.node = parent.node.extend next copyIndex) ∧
      ∃ current, target.node.current? = some current ∧
        target.node.history = current :: parent.node.history := by
  have derived := (input.mem_localizedOccurrences_iff fuel target).mp present
  have rootActive : (OfficialCIPNode.root target.root).ActiveSimple :=
    ⟨rfl, by simp [OfficialCIPNode.root]⟩
  obtain ⟨parent, parentDerived, parentRoot, parentAddress, parentRemaining,
    parentActive, parentExtend, current, currentEq, historyEq⟩ :=
    input.declarativeSubtree_exists_active_parent
      (root := target.root) (path := []) (fuel := fuel + 1) derived rootActive
      (by simpa using nonroot)
  refine ⟨parent, ?_, parentRoot, parentAddress, parentRemaining, parentActive,
    parentExtend, current, currentEq, historyEq⟩
  apply (input.mem_localizedOccurrences_iff fuel parent).mpr
  show input.DeclarativeLocalizedOccurrenceAtAtom fuel parent.root parent
  unfold DeclarativeLocalizedOccurrenceAtAtom
  rw [parentRoot]
  exact parentDerived

/-- A parent-frame history certificate for one non-root carrier occurrence: the actual parent
occurrence together with the exact provenance, address, remaining-depth, and branch-history
relations derived from carrier reachability. -/
structure LocalizedParentFrameHistory (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) where
  /-- The actual carrier parent occurrence at `target.address.dropLast`. -/
  parent : input.LocalizedCIPOccurrence fuel
  /-- The parent retains the target's stereogenic root. -/
  parent_root : parent.1.root = target.1.root
  /-- The parent occupies the immediate shorter carrier address. -/
  parent_address : parent.1.address = target.1.address.dropLast
  /-- The common depth grading forces the parent's remaining expansion depth to be one more. -/
  parent_remaining : parent.1.remaining = target.1.remaining + 1
  /-- The parent is provenance-bearing: real atom and duplicate-free history. -/
  parent_active : parent.1.node.ActiveSimple
  /-- The target node is literally a parent-side `extend` child of the parent node. -/
  parent_extend : ∃ next copyIndex, target.1.node = parent.1.node.extend next copyIndex
  /-- The target's current atom, retained explicitly. -/
  current : input.Atom
  current_eq : target.1.node.current? = some current
  /-- The target node is the parent node extended by the current atom. -/
  history_eq : target.1.node.history = current :: parent.1.node.history
  /-- A parent frame only exists for non-root carrier addresses. -/
  nonroot : target.1.address ≠ []

/-- Every non-root reachable carrier occurrence has a parent-frame history certificate. -/
theorem exists_localizedParentFrameHistory
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (nonroot : target.1.address ≠ []) :
    Nonempty (input.LocalizedParentFrameHistory target) := by
  obtain ⟨parent, parentPresent, parentRoot, parentAddress, parentRemaining,
    parentActive, parentExtend, current, currentEq, historyEq⟩ :=
    input.exists_parentFrame_of_mem_localizedOccurrences target.2 nonroot
  exact ⟨
    { parent := ⟨parent, parentPresent⟩
      parent_root := parentRoot
      parent_address := parentAddress
      parent_remaining := parentRemaining
      parent_active := parentActive
      parent_extend := parentExtend
      current := current
      current_eq := currentEq
      history_eq := historyEq
      nonroot := nonroot }⟩

/-- The canonical parent-frame certificate of a non-root occurrence. -/
noncomputable def localizedParentFrameHistory
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (nonroot : target.1.address ≠ []) :
    input.LocalizedParentFrameHistory target :=
  Classical.choice (input.exists_localizedParentFrameHistory target nonroot)

/-! ## Consequences of the certificate -/

/-- The parent coordinate is `target.address.dropLast`. -/
theorem LocalizedParentFrameHistory.parent_address_eq
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    (certificate : input.LocalizedParentFrameHistory target) :
    certificate.parent.1.address = target.1.address.dropLast :=
  certificate.parent_address

/-- The parent's provenance is the real-atom provenance; duplicates never parent a carrier
occurrence. -/
theorem LocalizedParentFrameHistory.parent_provenance
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    (certificate : input.LocalizedParentFrameHistory target) :
    certificate.parent.1.node.provenance = OfficialCIPNodeProvenance.realAtom :=
  certificate.parent_active.1

/-- The parent's stored history has no duplicate atom. -/
theorem LocalizedParentFrameHistory.parent_history_nodup
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    (certificate : input.LocalizedParentFrameHistory target) :
    certificate.parent.1.node.history.Nodup :=
  certificate.parent_active.2

/-- The parent's history is exactly the tail of the target history after the target's current
atom. -/
theorem LocalizedParentFrameHistory.target_history_tail
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    (certificate : input.LocalizedParentFrameHistory target) :
    target.1.node.history.tail = certificate.parent.1.node.history := by
  rw [certificate.history_eq]
  rfl

/-- The parent address is exactly one carrier step shorter than the target address. -/
theorem LocalizedParentFrameHistory.parent_address_length
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    (certificate : input.LocalizedParentFrameHistory target) :
    certificate.parent.1.address.length + 1 = target.1.address.length := by
  have length := congrArg List.length certificate.parent_address
  rw [List.length_dropLast] at length
  have positive : 0 < target.1.address.length :=
    List.length_pos_iff.mpr certificate.nonroot
  omega

/-- The carrier parent distance of a non-root occurrence is exactly one sibling step. -/
def LocalizedParentFrameHistory.parentDistance
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    (certificate : input.LocalizedParentFrameHistory target) : Nat :=
  target.1.address.length - certificate.parent.1.address.length

/-- **Parent-distance primitive instantiation.**  The signed carrier distance from a non-root
occurrence to its actual parent frame is one. -/
theorem LocalizedParentFrameHistory.parentDistance_eq_one
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    (certificate : input.LocalizedParentFrameHistory target) :
    certificate.parentDistance input = 1 := by
  have step := certificate.parent_address_length input
  unfold LocalizedParentFrameHistory.parentDistance
  omega

/-- **Target history shape `current :: parent :: tail`.**  The target history is the target's
current atom followed by the parent's current atom and a shared tail; the parent's stored history
is exactly `parent :: tail`.  This is the history bridge consumed by the parent-distance
primitive. -/
theorem LocalizedParentFrameHistory.history_shape
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    (certificate : input.LocalizedParentFrameHistory target) :
    ∃ current parentCurrent tail,
      target.1.node.current? = some current ∧
      certificate.parent.1.node.current? = some parentCurrent ∧
      target.1.node.history = current :: parentCurrent :: tail ∧
      certificate.parent.1.node.history = parentCurrent :: tail := by
  have parentDerived :=
    (input.mem_localizedOccurrences_iff fuel certificate.parent.1).mp certificate.parent.2
  have parentCurrentSome :=
    input.declarativeLocalizedOccurrence_node_current_isSome parentDerived
  obtain ⟨parentCurrent, parentCurrentEq⟩ :=
    Option.isSome_iff_exists.mp parentCurrentSome
  have headEq :=
    input.declarativeLocalizedOccurrence_node_history_head_eq_current parentDerived
  have headSome : certificate.parent.1.node.history.head? = some parentCurrent :=
    headEq.trans parentCurrentEq
  obtain ⟨tail, tailEq⟩ := List.head?_eq_some_iff.mp headSome
  exact ⟨certificate.current, parentCurrent, tail, certificate.current_eq,
    parentCurrentEq, by rw [certificate.history_eq, tailEq], tailEq⟩

/-- The parent coordinate is unique: two parent-frame certificates of the same target have the
same carrier parent. -/
theorem LocalizedParentFrameHistory.parent_unique
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    (first second : input.LocalizedParentFrameHistory target) :
    first.parent = second.parent := by
  have sameRoot : first.parent.1.root = second.parent.1.root :=
    first.parent_root.trans second.parent_root.symm
  have sameAddress : first.parent.1.address = second.parent.1.address :=
    first.parent_address.trans second.parent_address.symm
  have frameEq := input.declarativeLocalizedOccurrence_functional_at_root_address
    ((input.mem_localizedOccurrences_iff fuel first.parent.1).mp first.parent.2)
    ((input.mem_localizedOccurrences_iff fuel second.parent.1).mp second.parent.2)
    sameRoot sameAddress
  exact Subtype.ext frameEq

/-! ## Binding to the certified carrier-parent list and zipper neighborhood -/

/-- **Direct binding to `localizedCarrierParentFrames`.**  The actual parent frame is a member of
the certified shorter-address carrier-parent list of the target.  This is the bridge that lets
existing singleton carrier-parent selectors consume the provenance-bearing parent. -/
theorem LocalizedParentFrameHistory.parent_mem_carrierParentFrames
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    (certificate : input.LocalizedParentFrameHistory target) :
    certificate.parent.1 ∈ input.localizedCarrierParentFrames (fuel := fuel) target.1 := by
  rw [localizedCarrierParentFrames, List.mem_filter]
  refine ⟨certificate.parent.2, ?_⟩
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨certificate.parent_root, certificate.parent_address_length input⟩,
    certificate.parent_address⟩

/-- The certified carrier-parent list of a non-root occurrence is exactly the singleton of the
actual parent frame, so parent selection is a function of the target. -/
theorem LocalizedParentFrameHistory.carrierParentFrames_eq_singleton
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    (certificate : input.LocalizedParentFrameHistory target) :
    input.localizedCarrierParentFrames (fuel := fuel) target.1 = [certificate.parent.1] := by
  have parentInFrames := certificate.parent_mem_carrierParentFrames input
  have parentPresent := parentInFrames
  rw [localizedCarrierParentFrames, List.mem_filter] at parentPresent
  obtain ⟨_parentCarrier, parentConditions⟩ := parentPresent
  simp only [Bool.and_eq_true, beq_iff_eq] at parentConditions
  have parentDerived :=
    (input.mem_localizedOccurrences_iff fuel certificate.parent.1).mp certificate.parent.2
  have onlyParent : ∀ candidate,
      candidate ∈ input.localizedCarrierParentFrames (fuel := fuel) target.1 →
        candidate = certificate.parent.1 := by
    intro candidate candidatePresent
    rw [localizedCarrierParentFrames, List.mem_filter] at candidatePresent
    obtain ⟨candidateCarrier, candidateConditions⟩ := candidatePresent
    simp only [Bool.and_eq_true, beq_iff_eq] at candidateConditions
    have candidateDerived :=
      (input.mem_localizedOccurrences_iff fuel candidate).mp candidateCarrier
    exact input.declarativeLocalizedOccurrence_functional_at_root_address
      candidateDerived parentDerived
      (candidateConditions.1.1.trans parentConditions.1.1.symm)
      (candidateConditions.2.trans parentConditions.2.symm)
  have parentNodup :
      (input.localizedCarrierParentFrames (fuel := fuel) target.1).Nodup := by
    unfold localizedCarrierParentFrames
    exact (input.localizedOccurrences_nodup fuel).filter _
  have sameMembers : ∀ candidate,
      candidate ∈ input.localizedCarrierParentFrames (fuel := fuel) target.1 ↔
        candidate ∈ [certificate.parent.1] := by
    intro candidate
    constructor
    · intro candidatePresent
      simp [onlyParent candidate candidatePresent]
    · intro candidatePresent
      simp only [List.mem_singleton] at candidatePresent
      subst candidate
      exact parentInFrames
  have permutation :
      List.Perm (input.localizedCarrierParentFrames (fuel := fuel) target.1)
        [certificate.parent.1] :=
    (List.perm_ext_iff_of_nodup parentNodup (by simp)).mpr sameMembers
  exact List.perm_singleton.mp permutation

/-- The certified parent list's first (and only) element is the actual parent frame. -/
theorem LocalizedParentFrameHistory.carrierParentFrames_head?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    (certificate : input.LocalizedParentFrameHistory target) :
    (input.localizedCarrierParentFrames (fuel := fuel) target.1).head? =
      some certificate.parent.1 := by
  rw [certificate.carrierParentFrames_eq_singleton input]
  rfl

/-- **Direct binding to `localizedRule3CarrierParentFrame?`.**  On a non-root carrier occurrence
the executable singleton carrier-parent selector returns exactly the provenance-bearing parent
frame of this certificate. -/
theorem LocalizedParentFrameHistory.localizedRule3CarrierParentFrame?_eq_some
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    (certificate : input.LocalizedParentFrameHistory target) :
    input.localizedRule3CarrierParentFrame? target = some certificate.parent.1 := by
  have singleton := certificate.carrierParentFrames_eq_singleton input
  simp [localizedRule3CarrierParentFrame?, singleton]

/-- The target is a parent-side carrier child of the actual parent frame: it lies in the parent's
outward immediate-child list. -/
theorem LocalizedParentFrameHistory.target_mem_carrierOutwardChildFrames
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    (certificate : input.LocalizedParentFrameHistory target) :
    target.1 ∈
      input.localizedCarrierOutwardChildFrames (fuel := fuel) certificate.parent.1 := by
  rw [localizedCarrierOutwardChildFrames, List.mem_filter]
  refine ⟨target.2, ?_⟩
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨certificate.parent_root.symm, ?_⟩, certificate.parent_address.symm⟩
  have step := certificate.parent_address_length input
  omega

/-- The actual parent frame lies in the target's uncut zipper neighborhood. -/
theorem LocalizedParentFrameHistory.parent_mem_neighborFrames
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    (certificate : input.LocalizedParentFrameHistory target) :
    certificate.parent.1 ∈ input.localizedRerootNeighborFrames (fuel := fuel) target.1 :=
  List.mem_append_left _ (certificate.parent_mem_carrierParentFrames input)

/-- The target lies in the parent frame's uncut zipper neighborhood. -/
theorem LocalizedParentFrameHistory.target_mem_neighborFrames
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    (certificate : input.LocalizedParentFrameHistory target) :
    target.1 ∈ input.localizedRerootNeighborFrames (fuel := fuel) certificate.parent.1 :=
  List.mem_append_right _ (certificate.target_mem_carrierOutwardChildFrames input)

/-! ## Activity-retaining certificate -/

/-- Parent-frame certificate that retains the target occurrence's own activity.  The distance
primitive is invoked on active occurrences; parent activity is proved separately and does not by
itself record that the target is real and branch-history simple. -/
structure ActiveLocalizedParentFrameHistory (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    extends input.LocalizedParentFrameHistory target where
  /-- The target occurrence is active simple: real provenance and a duplicate-free history. -/
  target_active : target.1.node.ActiveSimple

/-- Every active non-root reachable carrier occurrence has an activity-retaining parent-frame
certificate. -/
theorem exists_activeLocalizedParentFrameHistory
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (active : target.1.node.ActiveSimple)
    (nonroot : target.1.address ≠ []) :
    Nonempty (input.ActiveLocalizedParentFrameHistory target) := by
  obtain ⟨certificate⟩ := input.exists_localizedParentFrameHistory target nonroot
  exact ⟨{ toLocalizedParentFrameHistory := certificate, target_active := active }⟩

/-- The canonical activity-retaining parent-frame certificate. -/
noncomputable def localizedActiveParentFrameHistory
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (active : target.1.node.ActiveSimple)
    (nonroot : target.1.address ≠ []) :
    input.ActiveLocalizedParentFrameHistory target :=
  Classical.choice (input.exists_activeLocalizedParentFrameHistory target active nonroot)

/-- **Active-occurrence parent-distance instantiation.**  For an active non-root occurrence the
retained certificate still yields carrier parent distance one. -/
theorem ActiveLocalizedParentFrameHistory.parentDistance_eq_one
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    (certificate : input.ActiveLocalizedParentFrameHistory target) :
    certificate.toLocalizedParentFrameHistory.parentDistance input = 1 :=
  certificate.toLocalizedParentFrameHistory.parentDistance_eq_one input

/-- **Explicit parent-frame history at the carrier level.**  A single statement providing the
actual parent frame, its real provenance, its duplicate-free history, and the exact
`current :: parent :: tail` history matching. -/
theorem exists_parentFrame_history_shape
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (nonroot : target.1.address ≠ []) :
    ∃ parent : input.LocalizedCIPOccurrence fuel,
      parent.1.root = target.1.root ∧
      parent.1.address = target.1.address.dropLast ∧
      parent.1.remaining = target.1.remaining + 1 ∧
      parent.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
      parent.1.node.history.Nodup ∧
      (∃ next copyIndex, target.1.node = parent.1.node.extend next copyIndex) ∧
      ∃ current parentCurrent tail,
        target.1.node.current? = some current ∧
        target.1.node.history = current :: parentCurrent :: tail ∧
        parent.1.node.history = parentCurrent :: tail := by
  obtain ⟨certificate⟩ := input.exists_localizedParentFrameHistory target nonroot
  obtain ⟨current, parentCurrent, tail, currentEq, _parentCurrentEq,
    historyEq, parentHistoryEq⟩ := certificate.history_shape input
  exact ⟨certificate.parent, certificate.parent_root, certificate.parent_address,
    certificate.parent_remaining, certificate.parent_provenance input,
    certificate.parent_history_nodup input, certificate.parent_extend,
    current, parentCurrent, tail, currentEq, historyEq, parentHistoryEq⟩

/-! ## Reroot cursors with `previous = context` -/

/-- **Outward parent-frame identification.**  If a carrier occurrence `target` sits one sibling
slot below `context`, then the actual carrier parent of `target` is `context`, and the target
history is the context history preceded by the target's current atom.  The address and root
relations are the only inputs; the parent identity follows from carrier-address functionality. -/
theorem localizedParentFrameHistory_of_outward
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target context : input.LocalizedCIPOccurrence fuel)
    (sameRoot : target.1.root = context.1.root)
    (slot : Nat)
    (address : target.1.address = context.1.address ++ [slot]) :
    ∃ certificate : input.LocalizedParentFrameHistory target,
      certificate.parent = context ∧
      context.1.node.ActiveSimple ∧
      target.1.node.history = certificate.current :: context.1.node.history := by
  have nonroot : target.1.address ≠ [] := by
    rw [address]
    simp
  obtain ⟨certificate⟩ := input.exists_localizedParentFrameHistory target nonroot
  have parentRoot : certificate.parent.1.root = context.1.root :=
    certificate.parent_root.trans sameRoot
  have parentAddress : certificate.parent.1.address = context.1.address := by
    rw [certificate.parent_address, address]
    simp
  have parentFrameEq := input.declarativeLocalizedOccurrence_functional_at_root_address
    ((input.mem_localizedOccurrences_iff fuel certificate.parent.1).mp certificate.parent.2)
    ((input.mem_localizedOccurrences_iff fuel context.1).mp context.2)
    parentRoot parentAddress
  have parentEq : certificate.parent = context := Subtype.ext parentFrameEq
  have valueEq : certificate.parent.1 = context.1 := congrArg Subtype.val parentEq
  have contextActive : context.1.node.ActiveSimple := by
    rw [← valueEq]
    exact certificate.parent_active
  have historyEq : target.1.node.history =
      certificate.current :: context.1.node.history := by
    rw [certificate.history_eq, valueEq]
  exact ⟨certificate, parentEq, contextActive, historyEq⟩

/-- **Reroot-cursor `previous = context` instantiation.**  Every outward executable reroot child
of a context cursor records that context as its `previous?` coordinate, and the carrier parent
frame of the child occurrence is exactly that context occurrence.  Consequently the child history
is the child's current atom followed by the context history, with real parent provenance and a
duplicate-free parent history. -/
theorem executableLocalizedRerootChildren_outward_parentFrameHistory
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (context child : input.LocalizedRerootCursor fuel)
    (childPresent : child ∈ input.executableLocalizedRerootChildren context)
    (slot : Nat)
    (address : child.occurrence.1.address = context.occurrence.1.address ++ [slot]) :
    child.previous? = some context.occurrence ∧
    ∃ certificate : input.LocalizedParentFrameHistory child.occurrence,
      certificate.parent = context.occurrence ∧
      context.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
      context.occurrence.1.node.history.Nodup ∧
      child.occurrence.1.node.history =
        certificate.current :: context.occurrence.1.node.history := by
  have intended : child.occurrence.1 ∈
      input.intendedLocalizedRerootChildFrames context := by
    have mapped : child.occurrence.1 ∈
        (input.executableLocalizedRerootChildren context).map
          (fun cursor => cursor.occurrence.1) :=
      List.mem_map.mpr ⟨child, childPresent, rfl⟩
    rwa [input.executableLocalizedRerootChildren_map] at mapped
  have neighbor : child.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := fuel) context.occurrence.1 := by
    unfold intendedLocalizedRerootChildFrames at intended
    split at intended
    · simp at intended
    · split at intended
      · exact intended
      · exact List.mem_of_mem_filter intended
  have sameRoot : child.occurrence.1.root = context.occurrence.1.root :=
    input.localizedRerootNeighborFrames_root_eq context.occurrence.1
      child.occurrence.1 neighbor
  have previous :=
    input.executableLocalizedRerootChildren_previous context child childPresent
  obtain ⟨certificate, parentEq, contextActive, historyEq⟩ :=
    input.localizedParentFrameHistory_of_outward child.occurrence context.occurrence
      sameRoot slot address
  exact ⟨previous, certificate, parentEq, contextActive.1, contextActive.2, historyEq⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority assertions

The guarded declarations are the decisive exported endpoints: carrier parent existence,
provenance and history recovery, parent-distance instantiation, and the reroot-cursor
`previous = context` bridge.  `assert_kernel_only` permits exactly `propext`,
`Classical.choice` and `Quot.sound`, and rejects `sorryAx`, project axioms and native/compiler
trust. -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_executableOfficialCIPChildren_extend
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.activeSimple_of_mem_executableOfficialCIPChildren_of_hasChild
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.DeclarativeLocalizedOccurrenceSubtree.node_history_head_eq_current
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.DeclarativeLocalizedOccurrenceSubtree.node_current_isSome
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeLocalizedOccurrence_node_history_head_eq_current
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeLocalizedOccurrence_node_current_isSome
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeSubtree_has_executableChild_of_address_ne
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeSubtree_exists_active_parent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_parentFrame_of_mem_localizedOccurrences
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_localizedParentFrameHistory
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedParentFrameHistory.parent_address_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedParentFrameHistory.parent_provenance
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedParentFrameHistory.parent_history_nodup
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedParentFrameHistory.target_history_tail
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedParentFrameHistory.parent_address_length
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedParentFrameHistory.parentDistance_eq_one
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedParentFrameHistory.history_shape
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedParentFrameHistory.parent_unique
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedParentFrameHistory.parent_mem_carrierParentFrames
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedParentFrameHistory.carrierParentFrames_eq_singleton
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedParentFrameHistory.carrierParentFrames_head?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedParentFrameHistory.localizedRule3CarrierParentFrame?_eq_some
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedParentFrameHistory.target_mem_carrierOutwardChildFrames
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedParentFrameHistory.parent_mem_neighborFrames
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedParentFrameHistory.target_mem_neighborFrames
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_activeLocalizedParentFrameHistory
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActiveLocalizedParentFrameHistory.parentDistance_eq_one
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_parentFrame_history_shape
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedParentFrameHistory_of_outward
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableLocalizedRerootChildren_outward_parentFrameHistory
