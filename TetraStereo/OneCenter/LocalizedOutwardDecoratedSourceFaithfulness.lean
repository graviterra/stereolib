import TetraStereo.OneCenter.LocalizedCumulativeTreeObservableFaithfulness
import TetraStereo.OneCenter.LocalizedExecutableSourceTreeFaithfulness
import TetraStereo.OneCenter.LocalizedOccurrenceRerootFrame
import TetraStereo.OneCenter.LocalizedOutwardRerootDependencySupport
import TetraStereo.OneCenter.LocalizedOccurrenceUniversalDepth
import TetraStereo.OneCenter.LocalizedOccurrenceCarrierCoverage
import TetraStereo.OneCenter.FullStateParentNoninterference
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput












































namespace LocalizedCumulativeDecoratedTree

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-! ## Source erasure -/

mutual
  /-- Erase the auxiliary decoration and every child ordering, keeping the actual official source
  occurrence (current atom, full history and provenance) at each node. -/
  def toOfficialSourceTree :
      LocalizedCumulativeDecoratedTree input carrierFuel → OfficialCIPSourceTree input.Atom
    | ⟨source, _atomicNumber, _rule1bDistance, _isotopeMass, _label, children⟩ =>
        OfficialCIPSourceTree.node source.occurrence.1.node (toOfficialSourceTreeList children)
    termination_by tree => sizeOf tree
    decreasing_by
      simp_wf

  /-- Source erasure of a list of decorated siblings, in the stored order. -/
  def toOfficialSourceTreeList :
      List (LocalizedCumulativeDecoratedTree input carrierFuel) →
        List (OfficialCIPSourceTree input.Atom)
    | [] => []
    | tree :: trees => toOfficialSourceTree tree :: toOfficialSourceTreeList trees
    termination_by trees => sizeOf trees
    decreasing_by
      all_goals (simp_wf <;> omega)
end

/-! ### Unfolding equations

`toOfficialSourceTree` is defined by well-founded recursion, so its defining equations are not
definitional.  These lemmas record them explicitly; every later source statement rewrites through
them rather than relying on reduction. -/

/-- Defining equation of `toOfficialSourceTree` at one concrete node. -/
theorem toOfficialSourceTree_mk {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (source : input.LocalizedRerootCursor carrierFuel)
    (atomicNumber rule1bDistance isotopeMass : Nat)
    (label : Option LocalizedAuxiliaryLabel)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) :
    toOfficialSourceTree ⟨source, atomicNumber, rule1bDistance, isotopeMass, label, children⟩ =
      OfficialCIPSourceTree.node source.occurrence.1.node
        (toOfficialSourceTreeList children) := by
  rw [toOfficialSourceTree]

/-- Defining equation of `toOfficialSourceTreeList` at the empty list. -/
theorem toOfficialSourceTreeList_nil {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} :
    toOfficialSourceTreeList
        ([] : List (LocalizedCumulativeDecoratedTree input carrierFuel)) = [] := by
  rw [toOfficialSourceTreeList]

/-- Defining equation of `toOfficialSourceTreeList` at a cons. -/
theorem toOfficialSourceTreeList_cons {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (child : LocalizedCumulativeDecoratedTree input carrierFuel)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) :
    toOfficialSourceTreeList (child :: children) =
      toOfficialSourceTree child :: toOfficialSourceTreeList children := by
  rw [toOfficialSourceTreeList]

/-- The erased root source is exactly the actual occurrence node. -/
theorem toOfficialSourceTree_source (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    (toOfficialSourceTree tree).source = tree.source.occurrence.1.node := by
  obtain ⟨source, atomicNumber, rule1bDistance, isotopeMass, label, children⟩ := tree
  rw [toOfficialSourceTree_mk]
  rfl

/-- Defining equation of `toOfficialSourceTree` at an actual builder root. -/
theorem toOfficialSourceTree_localizedRootTree (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat} (cursor : input.LocalizedRerootCursor carrierFuel)
    (label : Option LocalizedAuxiliaryLabel)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) :
    toOfficialSourceTree (localizedRootTree input cursor label children) =
      OfficialCIPSourceTree.node cursor.occurrence.1.node
        (toOfficialSourceTreeList children) := by
  unfold localizedRootTree
  rw [toOfficialSourceTree_mk]

/-- Erasing a sibling list and then reading its sources is the same as reading the source node of
every decorated sibling.  This is the list-level form used to pass from the actual child-source
permutation to the executable child enumeration. -/
theorem toOfficialSourceTreeList_map_source :
    ∀ trees : List (LocalizedCumulativeDecoratedTree input carrierFuel),
      (toOfficialSourceTreeList trees).map OfficialCIPSourceTree.source =
        trees.map (fun tree => tree.source.occurrence.1.node)
  | [] => by rw [toOfficialSourceTreeList_nil]; rfl
  | tree :: trees => by
      rw [toOfficialSourceTreeList_cons, List.map_cons, List.map_cons,
        toOfficialSourceTree_source, toOfficialSourceTreeList_map_source trees]

/-- Erasing a sibling list is the same as mapping the erasure over the stored siblings. -/
theorem toOfficialSourceTreeList_eq_map :
    ∀ trees : List (LocalizedCumulativeDecoratedTree input carrierFuel),
      toOfficialSourceTreeList trees = trees.map toOfficialSourceTree
  | [] => by rw [toOfficialSourceTreeList_nil]; rfl
  | tree :: trees => by
      rw [toOfficialSourceTreeList_cons, List.map_cons,
        toOfficialSourceTreeList_eq_map trees]

/-- A source tree belongs to an erased sibling forest exactly when it is the erasure of one
stored decorated sibling.  This preserves multiplicity: the witness is the decorated sibling in
its stored slot, never a quotient by source-node equality. -/
theorem mem_toOfficialSourceTreeList
    {tree : OfficialCIPSourceTree input.Atom}
    {trees : List (LocalizedCumulativeDecoratedTree input carrierFuel)} :
    tree ∈ toOfficialSourceTreeList trees ↔
      ∃ decorated ∈ trees, toOfficialSourceTree decorated = tree := by
  rw [toOfficialSourceTreeList_eq_map, List.mem_map]

/-! ## Adequacy: strictly positive carrier depth at every node -/

mutual
  /-- Every node of the decorated tree carries a strictly positive remaining carrier depth.  This
  is the exact adequacy condition under which the actual reroot frame recovers the whole executable
  child enumeration; the final original-root arm discharges it from the sharp atom-count bound. -/
  def LocalizedCumulativeTreePositive :
      LocalizedCumulativeDecoratedTree input carrierFuel → Prop
    | ⟨source, _atomicNumber, _rule1bDistance, _isotopeMass, _label, children⟩ =>
        0 < source.occurrence.1.remaining ∧ LocalizedCumulativeTreePositiveList children
    termination_by tree => sizeOf tree
    decreasing_by
      simp_wf

  /-- Pointwise positivity for a sibling forest. -/
  def LocalizedCumulativeTreePositiveList :
      List (LocalizedCumulativeDecoratedTree input carrierFuel) → Prop
    | [] => True
    | tree :: trees =>
        LocalizedCumulativeTreePositive tree ∧ LocalizedCumulativeTreePositiveList trees
    termination_by trees => sizeOf trees
    decreasing_by
      all_goals (simp_wf <;> omega)
end

/-- Defining equation of `LocalizedCumulativeTreePositive` at a concrete node. -/
theorem localizedCumulativeTreePositive_mk {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat}
    (source : input.LocalizedRerootCursor carrierFuel)
    (atomicNumber rule1bDistance isotopeMass : Nat)
    (label : Option LocalizedAuxiliaryLabel)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) :
    LocalizedCumulativeTreePositive
        ⟨source, atomicNumber, rule1bDistance, isotopeMass, label, children⟩ ↔
      (0 < source.occurrence.1.remaining ∧
        LocalizedCumulativeTreePositiveList children) := by
  rw [LocalizedCumulativeTreePositive]

/-- Defining equation of `LocalizedCumulativeTreePositive` at an actual builder root. -/
theorem localizedCumulativeTreePositive_localizedRootTree
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (label : Option LocalizedAuxiliaryLabel)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) :
    LocalizedCumulativeTreePositive (localizedRootTree input cursor label children) ↔
      (0 < cursor.occurrence.1.remaining ∧
        LocalizedCumulativeTreePositiveList children) := by
  unfold localizedRootTree
  rw [localizedCumulativeTreePositive_mk]

/-- Defining equation of `LocalizedCumulativeTreePositiveList` at the empty list. -/
theorem localizedCumulativeTreePositiveList_nil :
    LocalizedCumulativeTreePositiveList
      ([] : List (LocalizedCumulativeDecoratedTree input carrierFuel)) := by
  rw [LocalizedCumulativeTreePositiveList]
  trivial

/-- Defining equation of `LocalizedCumulativeTreePositiveList` at a cons. -/
theorem localizedCumulativeTreePositiveList_cons
    (child : LocalizedCumulativeDecoratedTree input carrierFuel)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) :
    LocalizedCumulativeTreePositiveList (child :: children) ↔
      (LocalizedCumulativeTreePositive child ∧
        LocalizedCumulativeTreePositiveList children) := by
  rw [LocalizedCumulativeTreePositiveList]

/-- A sibling of a positive forest is itself positive. -/
theorem localizedCumulativeTreePositive_of_mem
    {trees : List (LocalizedCumulativeDecoratedTree input carrierFuel)}
    (all : LocalizedCumulativeTreePositiveList trees) :
    ∀ {tree : LocalizedCumulativeDecoratedTree input carrierFuel},
      tree ∈ trees → LocalizedCumulativeTreePositive tree := by
  induction trees with
  | nil =>
      intro tree present
      exact absurd present (by simp)
  | cons head tail ih =>
      intro tree present
      rw [localizedCumulativeTreePositiveList_cons] at all
      rcases List.mem_cons.mp present with rfl | present
      · exact all.1
      · exact ih all.2 present

/-! ## Incoming-parent provenance at every node -/

/-- The cursor arrived from an actual carrier parent: its recorded incoming coordinate is exactly
the carrier parent coordinate — the same source root, the address with its final slot removed, and
one level shorter.  This is the local hypothesis transported along actual outward child steps; it
is not a supplied alignment and it never identifies equal source nodes. -/
def LocalizedRerootCursorIncomingParent
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel) : Prop :=
  ∃ previous : input.LocalizedCIPOccurrence carrierFuel,
    cursor.previous? = some previous ∧
      previous.1.root = cursor.occurrence.1.root ∧
        previous.1.address = cursor.occurrence.1.address.dropLast ∧
          previous.1.address.length + 1 = cursor.occurrence.1.address.length

mutual
  /-- Every node of the decorated tree actually arrived from its carrier parent. -/
  def LocalizedCumulativeTreeIncoming
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
      LocalizedCumulativeDecoratedTree input carrierFuel → Prop
    | ⟨source, _atomicNumber, _rule1bDistance, _isotopeMass, _label, children⟩ =>
        LocalizedRerootCursorIncomingParent input source ∧
          LocalizedCumulativeTreeIncomingList input children
  termination_by tree => sizeOf tree
  decreasing_by
    simp_wf

  /-- Incoming-parent provenance for a sibling forest. -/
  def LocalizedCumulativeTreeIncomingList
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
      List (LocalizedCumulativeDecoratedTree input carrierFuel) → Prop
    | [] => True
    | tree :: trees =>
        LocalizedCumulativeTreeIncoming input tree ∧
          LocalizedCumulativeTreeIncomingList input trees
  termination_by trees => sizeOf trees
  decreasing_by
    all_goals (simp_wf <;> omega)
end

/-- Defining equation of `LocalizedCumulativeTreeIncoming` at a concrete node. -/
theorem localizedCumulativeTreeIncoming_mk {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat}
    (source : input.LocalizedRerootCursor carrierFuel)
    (atomicNumber rule1bDistance isotopeMass : Nat)
    (label : Option LocalizedAuxiliaryLabel)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) :
    LocalizedCumulativeTreeIncoming input
        ⟨source, atomicNumber, rule1bDistance, isotopeMass, label, children⟩ ↔
      (LocalizedRerootCursorIncomingParent input source ∧
        LocalizedCumulativeTreeIncomingList input children) := by
  rw [LocalizedCumulativeTreeIncoming]

/-- Defining equation of `LocalizedCumulativeTreeIncoming` at an actual builder root. -/
theorem localizedCumulativeTreeIncoming_localizedRootTree
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (label : Option LocalizedAuxiliaryLabel)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) :
    LocalizedCumulativeTreeIncoming input (localizedRootTree input cursor label children) ↔
      (LocalizedRerootCursorIncomingParent input cursor ∧
        LocalizedCumulativeTreeIncomingList input children) := by
  unfold localizedRootTree
  rw [localizedCumulativeTreeIncoming_mk]

/-- Defining equation of `LocalizedCumulativeTreeIncomingList` at the empty list. -/
theorem localizedCumulativeTreeIncomingList_nil {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat} :
    LocalizedCumulativeTreeIncomingList input
      ([] : List (LocalizedCumulativeDecoratedTree input carrierFuel)) := by
  rw [LocalizedCumulativeTreeIncomingList]
  trivial

/-- Defining equation of `LocalizedCumulativeTreeIncomingList` at a cons. -/
theorem localizedCumulativeTreeIncomingList_cons {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat}
    (child : LocalizedCumulativeDecoratedTree input carrierFuel)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) :
    LocalizedCumulativeTreeIncomingList input (child :: children) ↔
      (LocalizedCumulativeTreeIncoming input child ∧
        LocalizedCumulativeTreeIncomingList input children) := by
  rw [LocalizedCumulativeTreeIncomingList]

/-- A sibling of an incoming-provenance forest has incoming provenance itself. -/
theorem localizedCumulativeTreeIncoming_of_mem {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat}
    {trees : List (LocalizedCumulativeDecoratedTree input carrierFuel)}
    (all : LocalizedCumulativeTreeIncomingList input trees) :
    ∀ {tree : LocalizedCumulativeDecoratedTree input carrierFuel},
      tree ∈ trees → LocalizedCumulativeTreeIncoming input tree := by
  induction trees with
  | nil =>
      intro tree present
      exact absurd present (by simp)
  | cons head tail ih =>
      intro tree present
      rw [localizedCumulativeTreeIncomingList_cons] at all
      rcases List.mem_cons.mp present with rfl | present
      · exact all.1
      · exact ih all.2 present

end LocalizedCumulativeDecoratedTree

open LocalizedCumulativeDecoratedTree

/-! ## The canonical frame of one executable child slot -/

/-- The occurrence frame reached from one actual frame by following the executable child stored at
one `zipIdx` slot.  This is the exact carrier coordinate of that child: the address appends the
slot, and the remaining depth decreases by one.  It is a coordinate construction only; no
injectivity of source nodes is involved. -/
def localizedOutwardCanonicalFrame (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedCIPOccurrenceFrame) (entry : OfficialCIPNode input.Atom × Nat) :
    input.LocalizedCIPOccurrenceFrame where
  root := frame.root
  address := frame.address ++ [entry.2]
  node := entry.1
  remaining := frame.remaining - 1

/-- The canonical frame stores exactly the child of the indexed slot. -/
@[simp] theorem localizedOutwardCanonicalFrame_node
    (input : CertifiedLocalizedCIPInput) (frame : input.LocalizedCIPOccurrenceFrame)
    (entry : OfficialCIPNode input.Atom × Nat) :
    (localizedOutwardCanonicalFrame input frame entry).node = entry.1 :=
  rfl

/-- The canonical frame keeps the source root. -/
@[simp] theorem localizedOutwardCanonicalFrame_root
    (input : CertifiedLocalizedCIPInput) (frame : input.LocalizedCIPOccurrenceFrame)
    (entry : OfficialCIPNode input.Atom × Nat) :
    (localizedOutwardCanonicalFrame input frame entry).root = frame.root :=
  rfl

/-- The canonical frame address is the source address extended by the slot. -/
@[simp] theorem localizedOutwardCanonicalFrame_address
    (input : CertifiedLocalizedCIPInput) (frame : input.LocalizedCIPOccurrenceFrame)
    (entry : OfficialCIPNode input.Atom × Nat) :
    (localizedOutwardCanonicalFrame input frame entry).address = frame.address ++ [entry.2] :=
  rfl

/-- The canonical frame depth is one below the source depth. -/
@[simp] theorem localizedOutwardCanonicalFrame_remaining
    (input : CertifiedLocalizedCIPInput) (frame : input.LocalizedCIPOccurrenceFrame)
    (entry : OfficialCIPNode input.Atom × Nat) :
    (localizedOutwardCanonicalFrame input frame entry).remaining = frame.remaining - 1 :=
  rfl

/-! ## Prop-level membership characterizations -/

namespace CertifiedLocalizedCIPInput

/-- Carrier outward-child membership in propositional form: same root, one slot deeper, and the
same drop-last address. -/
theorem mem_localizedCarrierOutwardChildFrames_iff
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (frame candidate : input.LocalizedCIPOccurrenceFrame) :
    candidate ∈ input.localizedCarrierOutwardChildFrames (fuel := fuel) frame ↔
      candidate ∈ input.localizedOccurrences fuel ∧
        candidate.root = frame.root ∧
          candidate.address.length = frame.address.length + 1 ∧
            candidate.address.dropLast = frame.address := by
  constructor
  · intro present
    rw [localizedCarrierOutwardChildFrames, List.mem_filter] at present
    simp only [Bool.and_eq_true, beq_iff_eq] at present
    simpa only [and_assoc] using present
  · rintro ⟨mem, rootEq, lengthEq, dropLastEq⟩
    rw [localizedCarrierOutwardChildFrames, List.mem_filter]
    simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]
    exact ⟨mem, rootEq, lengthEq, dropLastEq⟩

/-- Neighbor membership cut at one excluded incoming address. -/
theorem mem_localizedRerootNeighborFrames_filter_previous
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (source previous : input.LocalizedCIPOccurrenceFrame)
    (frame : input.LocalizedCIPOccurrenceFrame) :
    frame ∈ (input.localizedRerootNeighborFrames (fuel := fuel) source).filter
        (fun candidate => candidate.address != previous.address) ↔
      frame ∈ input.localizedRerootNeighborFrames (fuel := fuel) source ∧
        frame.address ≠ previous.address := by
  simp only [List.mem_filter, bne_iff_ne]

/-! ## The local outward child bijection -/

/-- **Local outward expansion.**  For an actual molecule-wide occurrence with positive remaining
depth, the carrier's outward child frames carry exactly the executable official children, with
multiplicities.  Both directions are proved through the independent derivation relation: every
executable child slot is itself a carrier occurrence, and every carrier outward child is the
executable child stored at its final slot.  Distinct slots are never identified even when their
nodes coincide (positive multiple-bond copies), because the slot address is the coordinate. -/
theorem localizedOutwardChildFrames_nodes_perm_executable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedCIPOccurrenceFrame)
    (derived : input.DeclarativeLocalizedOccurrence carrierFuel frame)
    (positive : 0 < frame.remaining) :
    ((input.localizedCarrierOutwardChildFrames (fuel := carrierFuel) frame).map
        (fun child => child.node)).Perm
      (input.executableOfficialCIPChildren frame.node) := by
  let exec := input.executableOfficialCIPChildren frame.node
  let indexed := exec.zipIdx
  let canonical := localizedOutwardCanonicalFrame input frame
  let nodeProj : input.LocalizedCIPOccurrenceFrame → OfficialCIPNode input.Atom :=
    fun child => child.node
  have canonMem : ∀ entry ∈ indexed,
      canonical entry ∈
        input.localizedCarrierOutwardChildFrames (fuel := carrierFuel) frame := by
    intro entry present
    have entryAtSlot : (entry.1, entry.2) ∈ exec.zipIdx := by
      simpa only [indexed] using present
    have entryDerived : input.DeclarativeLocalizedOccurrence carrierFuel (canonical entry) := by
      have immediate :=
        DeclarativeLocalizedOccurrence.immediateChild input derived positive entryAtSlot
      simpa only [canonical, localizedOutwardCanonicalFrame] using immediate
    refine (input.mem_localizedCarrierOutwardChildFrames_iff
      (fuel := carrierFuel) frame (canonical entry)).mpr
      ⟨(input.mem_localizedOccurrences_iff carrierFuel _).mpr entryDerived, rfl, ?_, ?_⟩
    · simp only [canonical, localizedOutwardCanonicalFrame, List.length_append,
        List.length_singleton]
    · simp only [canonical, localizedOutwardCanonicalFrame, List.dropLast_concat]
  have canonCover : ∀ candidate ∈
      input.localizedCarrierOutwardChildFrames (fuel := carrierFuel) frame,
      ∃ entry ∈ indexed, canonical entry = candidate := by
    intro candidate present
    have parts :=
      (input.mem_localizedCarrierOutwardChildFrames_iff
        (fuel := carrierFuel) frame candidate).mp present
    have candidateDerived : input.DeclarativeLocalizedOccurrence carrierFuel candidate :=
      (input.mem_localizedOccurrences_iff carrierFuel candidate).mp parts.1
    have lengthEq : candidate.address.length = frame.address.length + 1 := parts.2.2.1
    have dropLastEq : candidate.address.dropLast = frame.address := parts.2.2.2
    have nonempty : candidate.address ≠ [] := by
      intro empty
      rw [empty] at lengthEq
      simp at lengthEq
    let slot := candidate.address.getLast nonempty
    have addressEq : candidate.address = frame.address ++ [slot] := by
      have split := List.dropLast_append_getLast nonempty
      rw [dropLastEq] at split
      exact split.symm
    obtain ⟨child, childAtSlot, candidateEq⟩ :=
      input.declarativeLocalizedOccurrence_immediate_child derived candidateDerived
        parts.2.1 slot addressEq
    refine ⟨(child, slot), ?_, ?_⟩
    · simpa only [indexed] using childAtSlot
    · rw [candidateEq]
      rfl
  have canonInjective : ∀ first second,
      canonical first = canonical second → first = second := by
    intro first second equal
    have addressEqual : frame.address ++ [first.2] = frame.address ++ [second.2] := by
      simpa only [canonical, localizedOutwardCanonicalFrame] using
        congrArg (fun child => child.address) equal
    have slotEqual : first.2 = second.2 := by
      simpa using List.append_cancel_left addressEqual
    have nodeEqual : first.1 = second.1 := by
      simpa only [canonical, localizedOutwardCanonicalFrame] using
        congrArg (fun child => child.node) equal
    exact Prod.ext nodeEqual slotEqual
  have indexedNodup : indexed.Nodup := by
    apply List.Nodup.of_map Prod.snd
    simp only [indexed, List.zipIdx_map_snd]
    exact List.nodup_range'
  have mappedNodup : (indexed.map canonical).Nodup :=
    List.Nodup.map_on (fun first _ second _ equal => canonInjective first second equal)
      indexedNodup
  have outwardNodup :
      (input.localizedCarrierOutwardChildFrames (fuel := carrierFuel) frame).Nodup := by
    unfold localizedCarrierOutwardChildFrames
    exact (input.localizedOccurrences_nodup carrierFuel).filter _
  have mappedPerm : (indexed.map canonical).Perm
      (input.localizedCarrierOutwardChildFrames (fuel := carrierFuel) frame) := by
    rw [List.perm_ext_iff_of_nodup mappedNodup outwardNodup]
    intro candidate
    constructor
    · intro present
      rw [List.mem_map] at present
      obtain ⟨entry, entryPresent, entryEq⟩ := present
      simpa only [entryEq] using canonMem entry entryPresent
    · intro present
      obtain ⟨entry, entryPresent, entryEq⟩ := canonCover candidate present
      exact List.mem_map.mpr ⟨entry, entryPresent, entryEq⟩
  have nodesIdentity : (indexed.map canonical).map nodeProj = exec := by
    rw [List.map_map]
    have entrywise : indexed.map (nodeProj ∘ canonical) = indexed.map Prod.fst := by
      apply List.map_congr_left
      intro entry _
      rfl
    rw [entrywise]
    simpa only [indexed] using List.zipIdx_map_fst 0 exec
  have mapped := mappedPerm.map nodeProj
  rw [nodesIdentity] at mapped
  exact mapped.symm

/-! ## Cutting the incoming parent leaves exactly the outward children -/

/-- **Incoming-parent cut.**  When a cursor arrived from its actual carrier parent, the cut removes
exactly the parent coordinate and nothing else.  The intended child frames are therefore exactly
the carrier outward child frames, up to the carrier's own duplicate-free ordering. -/
theorem intendedLocalizedRerootChildFrames_perm_outward
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous)
    (_previousRoot : previous.1.root = cursor.occurrence.1.root)
    (previousAddress : previous.1.address =
      cursor.occurrence.1.address.dropLast)
    (previousLength : previous.1.address.length + 1 =
      cursor.occurrence.1.address.length)
    (nonDuplicate : cursor.occurrence.1.node.isDuplicateLeaf = false) :
    (input.intendedLocalizedRerootChildFrames cursor).Perm
      (input.localizedCarrierOutwardChildFrames (fuel := carrierFuel) cursor.occurrence.1) := by
  have cut : input.intendedLocalizedRerootChildFrames cursor =
      (input.localizedRerootNeighborFrames (fuel := carrierFuel)
        cursor.occurrence.1).filter
        (fun frame => frame.address != previous.1.address) := by
    simp [intendedLocalizedRerootChildFrames, nonDuplicate, previousEq]
  rw [cut]
  have leftNodup : ((input.localizedRerootNeighborFrames (fuel := carrierFuel)
      cursor.occurrence.1).filter
        (fun frame => frame.address != previous.1.address)).Nodup :=
    (input.localizedRerootNeighborFrames_nodup
      (fuel := carrierFuel) cursor.occurrence.1).filter _
  have rightNodup : (input.localizedCarrierOutwardChildFrames (fuel := carrierFuel)
      cursor.occurrence.1).Nodup := by
    unfold localizedCarrierOutwardChildFrames
    exact (input.localizedOccurrences_nodup carrierFuel).filter _
  rw [List.perm_ext_iff_of_nodup leftNodup rightNodup]
  intro frame
  constructor
  · intro present
    have parts :=
      (input.mem_localizedRerootNeighborFrames_filter_previous
        (fuel := carrierFuel) cursor.occurrence.1 previous.1 frame).mp present
    have neighbor := parts.1
    have differentAddress := parts.2
    have characterized :=
      (input.mem_localizedRerootNeighborFrames_iff (fuel := carrierFuel)
        cursor.occurrence.1 frame).mp neighbor
    have mem := characterized.1
    have sameRoot := characterized.2.1
    have adjacent := characterized.2.2
    rcases adjacent with ⟨_lengthShorter, dropLastShorter⟩ | ⟨lengthLonger, dropLastLonger⟩
    · exact absurd (dropLastShorter.trans previousAddress.symm) differentAddress
    · exact (input.mem_localizedCarrierOutwardChildFrames_iff
        (fuel := carrierFuel) cursor.occurrence.1 frame).mpr
        ⟨mem, sameRoot, lengthLonger.symm, dropLastLonger.symm⟩
  · intro present
    have parts :=
      (input.mem_localizedCarrierOutwardChildFrames_iff
        (fuel := carrierFuel) cursor.occurrence.1 frame).mp present
    have mem := parts.1
    have sameRoot := parts.2.1
    have lengthLonger := parts.2.2.1
    have dropLastLonger := parts.2.2.2
    have neighborMem : frame ∈ input.localizedRerootNeighborFrames
        (fuel := carrierFuel) cursor.occurrence.1 :=
      (input.mem_localizedRerootNeighborFrames_iff (fuel := carrierFuel)
        cursor.occurrence.1 frame).mpr
        ⟨mem, sameRoot, Or.inr ⟨lengthLonger.symm, dropLastLonger.symm⟩⟩
    have differentLength : frame.address.length ≠ previous.1.address.length := by
      omega
    have differentAddress : frame.address ≠ previous.1.address :=
      fun same => differentLength (congrArg List.length same)
    exact (input.mem_localizedRerootNeighborFrames_filter_previous
      (fuel := carrierFuel) cursor.occurrence.1 previous.1 frame).mpr
      ⟨neighborMem, differentAddress⟩

/-- **Local intended-child expansion.**  Combining the incoming-parent cut with the slot bijection:
the intended reroot child frames of an actual cursor carry exactly the executable official
children. -/
theorem intendedLocalizedRerootChildFrames_nodes_perm_executable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (sourceDerived : input.DeclarativeLocalizedOccurrence carrierFuel cursor.occurrence.1)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous)
    (previousRoot : previous.1.root = cursor.occurrence.1.root)
    (previousAddress : previous.1.address =
      cursor.occurrence.1.address.dropLast)
    (previousLength : previous.1.address.length + 1 =
      cursor.occurrence.1.address.length)
    (nonDuplicate : cursor.occurrence.1.node.isDuplicateLeaf = false)
    (positive : 0 < cursor.occurrence.1.remaining) :
    ((input.intendedLocalizedRerootChildFrames cursor).map
        (fun child => child.node)).Perm
      (input.executableOfficialCIPChildren cursor.occurrence.1.node) := by
  refine (input.intendedLocalizedRerootChildFrames_perm_outward
    cursor previous previousEq previousRoot previousAddress previousLength
    nonDuplicate).map (fun child => child.node) |>.trans ?_
  exact input.localizedOutwardChildFrames_nodes_perm_executable
    cursor.occurrence.1 sourceDerived positive

/-! ## Actual decorated source erasure is executable-generated -/

/-- **Executable generatedness of the actual decorated source erasure.**  Consider an actual
`LocalizedCumulativeTreeRealizes` decorated tree (at any actual reroot cursor, with an arbitrary
auxiliary reader) every node of which arrived from its actual carrier parent and whose remaining
carrier depth is strictly positive.  Then the erased official source tree is generated by the
kernel-executable official child enumerator, sibling multiplicity included.

No supplied child alignment, coverage or label correspondence is assumed: at every node the actual
realization itself provides the emitted children, and the local outward slot bijection converts them
to the executable enumeration.  The auxiliary reader does not influence source multiplicities. -/
theorem toOfficialSourceTree_generatedBy
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree) :
    LocalizedCumulativeTreePositive tree →
      LocalizedCumulativeTreeIncoming input tree →
        (toOfficialSourceTree tree).GeneratedBy input.executableOfficialCIPChildren := by
  induction realizes with
  | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealize ih =>
      intro positive incoming
      rw [localizedCumulativeTreePositive_localizedRootTree] at positive
      rw [localizedCumulativeTreeIncoming_localizedRootTree] at incoming
      rw [toOfficialSourceTree_localizedRootTree]
      have cursorPositive : 0 < cursor.occurrence.1.remaining := positive.1
      have sortedPositive : LocalizedCumulativeTreePositiveList sortedChildren := positive.2
      have sortedIncoming : LocalizedCumulativeTreeIncomingList input sortedChildren := incoming.2
      rcases incoming.1 with
        ⟨previous, previousEq, previousRoot, previousAddress, previousLength⟩
      have childrenEq : children = input.executableLocalizedRerootChildren cursor := by
        have computed := childrenComputed
        rw [input.localizedRerootChildren?_eq_some_executable cursor] at computed
        exact (Option.some.inj computed).symm
      by_cases duplicate : cursor.occurrence.1.node.isDuplicateLeaf = true
      · -- Duplicate terminal leaves: both the cut and the executable enumerator are empty.
        have intendedNil : input.intendedLocalizedRerootChildFrames cursor = [] := by
          simp [intendedLocalizedRerootChildFrames, duplicate]
        have executableNil : input.executableLocalizedRerootChildren cursor = [] := by
          simp [executableLocalizedRerootChildren, intendedNil]
        have childrenNil : children = [] := by
          rw [childrenEq, executableNil]
        have sortedNil : sortedChildren = [] := by
          apply List.eq_nil_of_length_eq_zero
          have mapLen : (sortedChildren.map (fun child => child.source)).length =
              children.length := sourcePerm.length_eq
          rw [childrenNil] at mapLen
          simpa using mapLen
        have executableEmpty :
            input.executableOfficialCIPChildren cursor.occurrence.1.node = [] := by
          simp [executableOfficialCIPChildren, duplicate]
        rw [sortedNil, toOfficialSourceTreeList_nil]
        show ([] : List (OfficialCIPNode input.Atom)).Perm
            (input.executableOfficialCIPChildren cursor.occurrence.1.node) ∧
          OfficialCIPSourceTree.ForestGeneratedBy input.executableOfficialCIPChildren []
        rw [executableEmpty]
        exact ⟨List.Perm.refl [], trivial⟩
      · -- Positive copies: the actual intended frames are exactly the executable children.
        have nonDuplicate : cursor.occurrence.1.node.isDuplicateLeaf = false := by
          cases h : cursor.occurrence.1.node.isDuplicateLeaf
          · rfl
          · exact absurd h duplicate
        have derived : input.DeclarativeLocalizedOccurrence carrierFuel cursor.occurrence.1 :=
          (input.mem_localizedOccurrences_iff carrierFuel cursor.occurrence.1).mp
            cursor.occurrence.2
        have executableNodes :
            ((input.executableLocalizedRerootChildren cursor).map
                (fun child => child.occurrence.1.node)).Perm
              (input.executableOfficialCIPChildren cursor.occurrence.1.node) := by
          have frames :
              (input.executableLocalizedRerootChildren cursor).map
                  (fun child => child.occurrence.1.node) =
                (input.intendedLocalizedRerootChildFrames cursor).map
                  (fun frame => frame.node) := by
            simpa only [List.map_map] using congrArg
              (List.map (fun frame : input.LocalizedCIPOccurrenceFrame => frame.node))
              (input.executableLocalizedRerootChildren_map cursor)
          rw [frames]
          exact input.intendedLocalizedRerootChildFrames_nodes_perm_executable
            cursor derived previous previousEq previousRoot previousAddress previousLength
            nonDuplicate cursorPositive
        constructor
        · have mappedSource : (toOfficialSourceTreeList sortedChildren).map
              OfficialCIPSourceTree.source =
              sortedChildren.map (fun child => child.source.occurrence.1.node) :=
            toOfficialSourceTreeList_map_source sortedChildren
          have childNodesPerm :
              (sortedChildren.map (fun child => child.source.occurrence.1.node)).Perm
                ((input.executableLocalizedRerootChildren cursor).map
                  (fun child => child.occurrence.1.node)) := by
            have mapped := sourcePerm.map
              (fun child : input.LocalizedRerootCursor carrierFuel => child.occurrence.1.node)
            simpa only [List.map_map, childrenEq] using mapped
          rw [mappedSource]
          exact childNodesPerm.trans executableNodes
        · apply (OfficialCIPSourceTree.forestGeneratedBy_iff_forall
            input.executableOfficialCIPChildren
            (toOfficialSourceTreeList sortedChildren)).mpr
          intro erased present
          obtain ⟨child, childMem, childEq⟩ :=
            (mem_toOfficialSourceTreeList (input := input) (trees := sortedChildren)).mp present
          rw [← childEq]
          exact ih child childMem
            (localizedCumulativeTreePositive_of_mem sortedPositive childMem)
            (localizedCumulativeTreeIncoming_of_mem sortedIncoming childMem)

/-! ## Incoming provenance of every actual node -/

/-- A cursor whose recorded incoming coordinate is its actual carrier parent is path-valid: the
recorded predecessor is exactly a carrier-tree neighbor of the cursor occurrence. -/
theorem localizedRerootCursorValid_of_incoming
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (incoming : LocalizedRerootCursorIncomingParent input cursor) :
    input.LocalizedRerootCursorValid cursor := by
  rcases incoming with
    ⟨previous, previousEq, previousRoot, previousAddress, previousLength⟩
  unfold LocalizedRerootCursorValid
  rw [previousEq]
  exact (input.mem_localizedRerootNeighborFrames_iff (fuel := carrierFuel)
    previous.1 cursor.occurrence.1).mpr
    ⟨cursor.occurrence.2, previousRoot.symm,
      Or.inr ⟨previousLength, previousAddress⟩⟩

/-- Pointwise form of incoming provenance for one sibling forest. -/
theorem localizedCumulativeTreeIncomingList_iff_forall
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (trees : List (LocalizedCumulativeDecoratedTree input carrierFuel)) :
    LocalizedCumulativeTreeIncomingList input trees ↔
      ∀ tree ∈ trees, LocalizedCumulativeTreeIncoming input tree := by
  induction trees with
  | nil =>
      constructor
      · intro _ tree present
        simp at present
      · intro _
        exact localizedCumulativeTreeIncomingList_nil
          (input := input) (carrierFuel := carrierFuel)
  | cons head tail ih =>
      rw [localizedCumulativeTreeIncomingList_cons]
      constructor
      · rintro ⟨headIncoming, tailAll⟩ tree present
        rcases List.mem_cons.mp present with same | later
        · subst same
          exact headIncoming
        · exact ih.mp tailAll tree later
      · intro all
        exact ⟨all head (by simp),
          ih.mpr (fun tree present => all tree (by simp [present]))⟩

/-- **Incoming provenance from actual realization.**  If the root of an actual decorated
realization arrived from its carrier parent, then every node did: each sorted child is an actual
emitted child cursor, hence an outward executable step whose recorded incoming coordinate is the
parent occurrence.  This is read off the realization itself; no alignment is supplied. -/
theorem localizedCumulativeTreeIncoming_of_realizes
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (rootIncoming : LocalizedRerootCursorIncomingParent input tree.source) :
    LocalizedCumulativeTreeIncoming input tree := by
  induction realizes with
  | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealize ih =>
      rw [localizedCumulativeTreeIncoming_localizedRootTree]
      have cursorIncoming : LocalizedRerootCursorIncomingParent input cursor := by
        simpa using rootIncoming
      refine ⟨cursorIncoming, ?_⟩
      rw [localizedCumulativeTreeIncomingList_iff_forall]
      intro child childMem
      have childSourceMem : child.source ∈ children :=
        sourcePerm.mem_iff.mp (List.mem_map.mpr ⟨child, childMem, rfl⟩)
      have childrenEq : children = input.executableLocalizedRerootChildren cursor := by
        have computed := childrenComputed
        rw [input.localizedRerootChildren?_eq_some_executable cursor] at computed
        exact (Option.some.inj computed).symm
      have edge : E input cursor child.source := by
        show child.source ∈ input.executableLocalizedRerootChildren cursor
        rw [← childrenEq]
        exact childSourceMem
      rcases cursorIncoming with
        ⟨previous, previousEq, previousRoot, previousAddress, previousLength⟩
      have valid : input.LocalizedRerootCursorValid cursor :=
        input.localizedRerootCursorValid_of_incoming cursor
          ⟨previous, previousEq, previousRoot, previousAddress, previousLength⟩
      have parentShorter : previous.1.address.length <
          cursor.occurrence.1.address.length := by omega
      rcases input.outward_edge cursor child.source valid previous previousEq
          parentShorter edge with
        ⟨childDropLast, childLength, childRoot, childPrevious, _childValid⟩
      exact ih child childMem
        ⟨cursor.occurrence, childPrevious, childRoot.symm, childDropLast.symm,
          childLength.symm⟩

/-! ## Unbounded reachability of every actual occurrence -/

/-- Every declaratively derivable bounded occurrence is an unbounded executable descendant of the
subtree-root node, with the residual address appended to the subtree path. -/
theorem declarativeLocalizedOccurrenceSubtree_unbounded
    (input : CertifiedLocalizedCIPInput) {root : input.Atom}
    {path : List Nat} {fuel : Nat} {node : OfficialCIPNode input.Atom}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrenceSubtree root path fuel node occurrence) :
    ∃ inner, occurrence.address = path ++ inner ∧
      input.UnboundedOfficialSubtree node inner occurrence.node := by
  induction derived with
  | subtreeRoot path fuel node =>
      exact ⟨[], by simp, UnboundedOfficialSubtree.refl node⟩
  | @subtreeDescendant _ _ _ _ slot occurrence childAtSlot descendant ih =>
      obtain ⟨inner, addressEq, reachable⟩ := ih
      refine ⟨slot :: inner, ?_, UnboundedOfficialSubtree.step childAtSlot reachable⟩
      rw [addressEq, List.append_assoc]
      rfl

/-- Every molecule-wide bounded occurrence is an unbounded executable descendant of the official
root of its own stored root atom, at exactly its stored address. -/
theorem declarativeLocalizedOccurrence_unbounded
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrence fuel occurrence) :
    input.UnboundedOfficialSubtree (OfficialCIPNode.root occurrence.root)
      occurrence.address occurrence.node := by
  have rooted := input.declarativeLocalizedOccurrence_as_rootSubtree derived
  obtain ⟨inner, addressEq, reachable⟩ :=
    input.declarativeLocalizedOccurrenceSubtree_unbounded rooted
  have innerEq : inner = occurrence.address := by
    simpa using addressEq.symm
  rwa [innerEq] at reachable

/-! ## Adequacy of the sharp carrier -/

/-- **Sharp remaining-depth positivity.**  At any carrier fuel at least the atom count, every
actual molecule-wide occurrence has strictly positive remaining depth.  Each carrier occurrence is
an unbounded executable descendant of its stored root, so the converse atom-count address bound
applies; the exact depth grading then leaves at least one unit of remaining depth. -/
theorem localizedOccurrences_remaining_pos_of_atomCount_le
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ fuel)
    (occurrence : input.LocalizedCIPOccurrenceFrame)
    (present : occurrence ∈ input.localizedOccurrences fuel) :
    0 < occurrence.remaining := by
  have derived := (input.mem_localizedOccurrences_iff fuel occurrence).mp present
  have reachable := input.declarativeLocalizedOccurrence_unbounded derived
  have bound := input.unboundedOfficialSubtree_address_length_le_atomCount reachable
  have grade := input.declarativeLocalizedOccurrence_depthGrade derived
  omega

mutual
  /-- Every node of a decorated tree drawn from a carrier at least as deep as the atom count has
  strictly positive remaining depth.  This is the adequate-carrier hypothesis of the executable
  generatedness theorem, discharged here from the sharp address bound rather than assumed. -/
  theorem localizedCumulativeTreePositive_of_atomCount_le
      (input : CertifiedLocalizedCIPInput) {fuel : Nat}
      (enough : input.certified.input.molecule.atomCount ≤ fuel) :
      ∀ tree : LocalizedCumulativeDecoratedTree input fuel,
        LocalizedCumulativeTreePositive tree
    | ⟨source, _atomicNumber, _rule1bDistance, _isotopeMass, _label, children⟩ => by
        rw [localizedCumulativeTreePositive_mk]
        exact ⟨input.localizedOccurrences_remaining_pos_of_atomCount_le
            (fuel := fuel) enough source.occurrence.1 source.occurrence.2,
          localizedCumulativeTreePositiveList_of_atomCount_le input enough children⟩
    termination_by tree => sizeOf tree
    decreasing_by
      simp_wf

  /-- Pointwise adequacy for a sibling forest. -/
  theorem localizedCumulativeTreePositiveList_of_atomCount_le
      (input : CertifiedLocalizedCIPInput) {fuel : Nat}
      (enough : input.certified.input.molecule.atomCount ≤ fuel) :
      ∀ trees : List (LocalizedCumulativeDecoratedTree input fuel),
        LocalizedCumulativeTreePositiveList trees
    | [] => by
        exact localizedCumulativeTreePositiveList_nil (input := input) (carrierFuel := fuel)
    | head :: tail => by
        rw [localizedCumulativeTreePositiveList_cons]
        exact ⟨localizedCumulativeTreePositive_of_atomCount_le input enough head,
          localizedCumulativeTreePositiveList_of_atomCount_le input enough tail⟩
    termination_by trees => sizeOf trees
    decreasing_by
      all_goals (simp_wf <;> omega)
end

/-! ## The actual final original-root cursor -/

/-- The actual final original-root outward cursor: the canonical ligand root occurrence of `center`
at carrier fuel `atomCount + 1`, carrying the actual center root occurrence as its recorded
incoming coordinate.  This is a genuine original-root coordinate, not an auxiliary reroot. -/
noncomputable def localizedLigandRootCursor (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) where
  occurrence :=
    ⟨{ root := center.1
       address := [input.localizedLigandRootSlot center index]
       node := input.localizedLigandRootNode center index
       remaining := input.certified.input.molecule.atomCount + 1 }, by
      have reachable : input.UnboundedOfficialSubtree
          (OfficialCIPNode.rootFromEdge center.1 (input.canonicalLigandAtom center index))
          [] (input.localizedLigandRootNode center index) := by
        rw [← input.localizedLigandRootNode_eq_rootFromEdge center index]
        exact UnboundedOfficialSubtree.refl _
      simpa using
        (input.localizedOccurrenceUniversalDepth_covers_ligand_moleculeWide
          center index reachable)⟩
  previous? := some (input.localizedAtomRootOccurrence
    (input.certified.input.molecule.atomCount + 1) center.1)

@[simp] theorem localizedLigandRootCursor_root (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    (input.localizedLigandRootCursor center index).occurrence.1.root = center.1 := rfl

@[simp] theorem localizedLigandRootCursor_address (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    (input.localizedLigandRootCursor center index).occurrence.1.address =
      [input.localizedLigandRootSlot center index] := rfl

@[simp] theorem localizedLigandRootCursor_node (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    (input.localizedLigandRootCursor center index).occurrence.1.node =
      input.localizedLigandRootNode center index := rfl

@[simp] theorem localizedLigandRootCursor_previous (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    (input.localizedLigandRootCursor center index).previous? =
      some (input.localizedAtomRootOccurrence
        (input.certified.input.molecule.atomCount + 1) center.1) := rfl

/-- The final original-root cursor really arrived from the actual center root occurrence: same
root, the ligand address with its last slot removed, and one level shorter. -/
theorem localizedLigandRootCursor_incoming (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    LocalizedRerootCursorIncomingParent input
      (input.localizedLigandRootCursor center index) := by
  refine ⟨input.localizedAtomRootOccurrence
      (input.certified.input.molecule.atomCount + 1) center.1,
    by simp, by simp, by simp, by simp⟩

/-! ## The final original-root faithful exact expansion -/

/-- **Final original-root arm.**  At the canonical ligand root of an actual tetrahedral center, the
actual cumulative Rules-4a--5 builder succeeds at twice the carrier fuel for every stage and every
label reader, and the resulting actual decorated occurrence tree erases to an official source tree
that is executable-generated, is rooted exactly at `rootFromEdge center ligand`, and is therefore a
faithful exact declarative expansion of the actual molecular graph.

The carrier fuel is `atomCount + 1`, one above the sharp executable address bound, so every actual
occurrence in the tree has strictly positive remaining depth.  The incoming parent is the actual
center root occurrence: this is the final original-root outward arm, not an auxiliary reroot.  No
acyclic, simple-bond, injectivity, desired-reader or sorting assumption is used. -/
theorem localizedLigandRoot_sourceTree_faithfulExactExpansion
    (input : CertifiedLocalizedCIPInput) (center : input.TetrahedralCenter) (index : Fin 4)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
        (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel) :
    ∃ key : input.LocalizedRerootCumulativeRule45Key,
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read
          (2 * (input.certified.input.molecule.atomCount + 1 + 1))
          (input.localizedLigandRootCursor center index) = some key ∧
        ∃ tree : LocalizedCumulativeDecoratedTree input
            (input.certified.input.molecule.atomCount + 1),
          tree.source = input.localizedLigandRootCursor center index ∧
            LocalizedCumulativeTreeTableMatch stage tree key ∧
              LocalizedCumulativeTreeRealizes input read tree ∧
                (toOfficialSourceTree tree).GeneratedBy
                    input.executableOfficialCIPChildren ∧
                  (toOfficialSourceTree tree).source =
                      OfficialCIPNode.rootFromEdge center.1
                        (input.canonicalLigandAtom center index) ∧
                    DeclarativeCIP.RootedDigraph.FaithfulExactExpansion input.moleculeGraph
                      center.1 (input.canonicalLigandAtom center index)
                      (toOfficialSourceTree tree).toDeclarativeDigraph := by
  let cursor := input.localizedLigandRootCursor center index
  have incoming : LocalizedRerootCursorIncomingParent input cursor :=
    input.localizedLigandRootCursor_incoming center index
  have valid : input.LocalizedRerootCursorValid cursor :=
    input.localizedRerootCursorValid_of_incoming cursor incoming
  obtain ⟨key, built⟩ :=
    CertifiedLocalizedCIPInput.WholeStateCumulativeLabels.exists_buildLocalizedRerootCumulativeRule45KeyWithRead?_at_twice
      input stage read cursor valid
  obtain ⟨tree, treeSource, tableMatch, realizes, _children, _childrenComputed, _sourcePerm⟩ :=
    exists_decoratedTree_of_buildWithRead input stage read
      (2 * (input.certified.input.molecule.atomCount + 1 + 1)) cursor key built
  have positive : LocalizedCumulativeTreePositive tree :=
    input.localizedCumulativeTreePositive_of_atomCount_le
      (fuel := input.certified.input.molecule.atomCount + 1) (by omega) tree
  have treeIncoming : LocalizedCumulativeTreeIncoming input tree := by
    apply input.localizedCumulativeTreeIncoming_of_realizes read tree realizes
    rwa [treeSource]
  have generated : (toOfficialSourceTree tree).GeneratedBy
      input.executableOfficialCIPChildren :=
    input.toOfficialSourceTree_generatedBy read tree realizes positive treeIncoming
  have treeRoot : (toOfficialSourceTree tree).source =
      OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center index) := by
    rw [toOfficialSourceTree_source, treeSource]
    exact input.localizedLigandRootNode_eq_rootFromEdge center index
  exact ⟨key, built, tree, treeSource, tableMatch, realizes, generated, treeRoot,
    input.generatedExecutableSourceTree_faithfulExactExpansion
      (toOfficialSourceTree tree) center.1 (input.canonicalLigandAtom center index)
      generated treeRoot (input.canonicalLigandAtom_adj center index)⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Direct kernel-authority guards

Every public export of this module is checked here against
`TetraStereo.KernelOnly.assert_kernel_only`: only `propext`, `Classical.choice` and
`Quot.sound` may appear in the closure. -/

assert_kernel_only
  TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.toOfficialSourceTree
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.toOfficialSourceTree_mk
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList_nil
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList_cons
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.toOfficialSourceTree_source
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.toOfficialSourceTree_localizedRootTree
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList_map_source
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.toOfficialSourceTreeList_eq_map
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.mem_toOfficialSourceTreeList
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.LocalizedCumulativeTreePositive
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.LocalizedCumulativeTreePositiveList
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.localizedCumulativeTreePositive_mk
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.localizedCumulativeTreePositive_localizedRootTree
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.localizedCumulativeTreePositiveList_nil
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.localizedCumulativeTreePositiveList_cons
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.localizedCumulativeTreePositive_of_mem
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.LocalizedRerootCursorIncomingParent
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.LocalizedCumulativeTreeIncoming
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.LocalizedCumulativeTreeIncomingList
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.localizedCumulativeTreeIncoming_mk
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.localizedCumulativeTreeIncoming_localizedRootTree
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.localizedCumulativeTreeIncomingList_nil
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.localizedCumulativeTreeIncomingList_cons
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.localizedCumulativeTreeIncoming_of_mem
assert_kernel_only
  TetraStereo.OneCenter.localizedOutwardCanonicalFrame
assert_kernel_only
  TetraStereo.OneCenter.localizedOutwardCanonicalFrame_node
assert_kernel_only
  TetraStereo.OneCenter.localizedOutwardCanonicalFrame_root
assert_kernel_only
  TetraStereo.OneCenter.localizedOutwardCanonicalFrame_address
assert_kernel_only
  TetraStereo.OneCenter.localizedOutwardCanonicalFrame_remaining
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_localizedCarrierOutwardChildFrames_iff
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_localizedRerootNeighborFrames_filter_previous
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOutwardChildFrames_nodes_perm_executable
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.intendedLocalizedRerootChildFrames_perm_outward
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.intendedLocalizedRerootChildFrames_nodes_perm_executable
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.toOfficialSourceTree_generatedBy
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootCursorValid_of_incoming
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCumulativeTreeIncomingList_iff_forall
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCumulativeTreeIncoming_of_realizes
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeLocalizedOccurrenceSubtree_unbounded
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeLocalizedOccurrence_unbounded
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrences_remaining_pos_of_atomCount_le
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCumulativeTreePositive_of_atomCount_le
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCumulativeTreePositiveList_of_atomCount_le
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedLigandRootCursor
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedLigandRootCursor_root
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedLigandRootCursor_address
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedLigandRootCursor_node
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedLigandRootCursor_previous
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedLigandRootCursor_incoming
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedLigandRoot_sourceTree_faithfulExactExpansion
