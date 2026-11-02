import TetraStereo.OneCenter.LocalizedAcyclicRerootNeighborCorrespondence
import TetraStereo.KernelOnly

set_option autoImplicit false





















































namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

variable (input : CertifiedLocalizedCIPInput)

/-! ## Real provenance produces simple physical paths at any bond order -/

/-- **A real executable child of a real path node is a real path node.**  `realAtom` provenance of
the child forces the raw copy index to be zero and forces the child atom to be absent from the
stored branch history; prepending that atom therefore extends the stored simple physical walk.

This is the multiplicity-generic replacement for `realPathNode_step`: the copy-index
classification is read from provenance rather than from `bond = 1`. -/
theorem realPathNode_child_of_mem_executableOfficialCIPChildren
    {root : input.Atom} {node child : OfficialCIPNode input.Atom}
    (real : input.RealPathNode root node)
    (present : child ∈ input.executableOfficialCIPChildren node)
    (childReal : child.provenance = OfficialCIPNodeProvenance.realAtom) :
    input.RealPathNode root child := by
  obtain ⟨current, path, currentObserved, headObserved, provenance, pathIsPath,
    supportReverse, penultimateEq⟩ := real
  have realNode : input.RealPathNode root node :=
    ⟨current, path, currentObserved, headObserved, provenance, pathIsPath,
      supportReverse, penultimateEq⟩
  obtain ⟨next, copyIndex, childExtend⟩ :=
    input.mem_executableOfficialCIPChildren_extend node child present
  have childCurrent : child.current? = some next := by
    rw [childExtend]
    rfl
  have adjacent : input.moleculeGraph.Adj current next :=
    input.adj_of_mem_executableOfficialCIPChildren node child current next
      currentObserved childCurrent present
  have copyZero : copyIndex = 0 := by
    by_contra nonzero
    rw [childExtend, OfficialCIPNode.extend_provenance,
      OfficialCIPNode.childProvenance_copy_pos node next nonzero] at childReal
    exact OfficialCIPNodeProvenance.noConfusion childReal
  subst copyIndex
  have fresh : next ∉ node.history := by
    intro visited
    rw [childExtend, OfficialCIPNode.extend_provenance,
      OfficialCIPNode.childProvenance_ring_duplicate node next visited] at childReal
    exact OfficialCIPNodeProvenance.noConfusion childReal
  have historyHead : node.history = current :: node.history.tail := by
    cases historyCase : node.history with
    | nil => simp [historyCase] at headObserved
    | cons first rest =>
        have firstEq : first = current := by
          simpa [historyCase] using headObserved
        subst first
        rfl
  have newReal : input.RealPathNode root (node.extend next 0) := by
    refine ⟨next, path.concat adjacent, by simp, by simp, ?_, ?_, ?_, ?_⟩
    · rw [OfficialCIPNode.extend_provenance]
      exact OfficialCIPNode.childProvenance_real node next fresh
    · have outside : next ∉ path.support := by
        intro inSupport
        exact fresh (by
          rw [← supportReverse]
          exact List.mem_reverse.mpr inSupport)
      exact pathIsPath.concat outside adjacent
    · simp [OfficialCIPNode.extend_history, SimpleGraph.Walk.support_concat, supportReverse]
    · intro parent parentObserved
      simp only [OfficialCIPNode.parent?] at parentObserved
      rw [OfficialCIPNode.extend_history, historyHead] at parentObserved
      change some current = some parent at parentObserved
      have parentEq : parent = current := (Option.some.inj parentObserved).symm
      subst parent
      simp [SimpleGraph.Walk.penultimate_concat]
  simpa [childExtend] using newReal

/-- **Real provenance propagates down a declarative occurrence subtree.**  If the subtree root is a
real path node and the bottom occurrence's node is real, then every node on the actual derivation
is a real path node; in particular the bottom node is a simple physical path from the stored
original root at arbitrary bond order.

The induction step reuses `childProvenance_real_of_descendant` (which already classifies an
intermediate child as real whenever the bottom occurrence is real) together with the copy-zero
step above. -/
theorem realPathNode_of_declarativeSubtree_real
    {root : input.Atom} :
    ∀ {path : List Nat} {fuel : Nat} {node : OfficialCIPNode input.Atom}
      {occurrence : input.LocalizedCIPOccurrenceFrame},
      input.DeclarativeLocalizedOccurrenceSubtree root path fuel node occurrence →
        input.RealPathNode root node →
          occurrence.node.provenance = OfficialCIPNodeProvenance.realAtom →
            input.RealPathNode root occurrence.node := by
  intro path fuel node occurrence derived
  induction derived with
  | subtreeRoot =>
      intro real _finalReal
      exact real
  | @subtreeDescendant path fuel node child slot occurrence childAtSlot below ih =>
      intro real finalReal
      have childPresent : child ∈ input.executableOfficialCIPChildren node :=
        List.fst_mem_of_mem_zipIdx childAtSlot
      have childReal : child.provenance = OfficialCIPNodeProvenance.realAtom :=
        input.childProvenance_real_of_descendant childAtSlot below finalReal
      exact ih
        (input.realPathNode_child_of_mem_executableOfficialCIPChildren real
          childPresent childReal)
        finalReal

/-- **Every real carrier occurrence is a real path node at any bond order.**  The occurrence is
reached from the official root through its actual declarative derivation; real provenance is
preserved at every step by `realPathNode_of_declarativeSubtree_real`. -/
theorem carrierOccurrence_realPath_of_provenance_real
    {fuel : Nat} (occurrence : input.LocalizedCIPOccurrence fuel)
    (real : occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    input.RealPathNode occurrence.1.root occurrence.1.node := by
  have derived :=
    (input.mem_localizedOccurrences_iff fuel occurrence.1).mp occurrence.2
  exact input.realPathNode_of_declarativeSubtree_real
    (input.declarativeLocalizedOccurrence_as_rootSubtree derived)
    (input.realPathNode_root occurrence.1.root) real

/-- The stored history of a real path node is duplicate-free: it is the reverse support of a
simple walk. -/
theorem realPathNode_history_nodup
    {root : input.Atom} {node : OfficialCIPNode input.Atom}
    (real : input.RealPathNode root node) : node.history.Nodup := by
  obtain ⟨_current, path, _observed, _head, _provenance, simple, supportReverse,
    _penultimate⟩ := real
  rw [← supportReverse]
  exact List.nodup_reverse.mpr simple.support_nodup

/-- **Real carrier occurrences occupy at most `atomCount` sibling slots.**  This is the
multiplicity-generic counterpart of `carrierOccurrence_address_length_le_atomCount`: the history
bound comes from the real simple path rather than from a single-bond carrier proof. -/
theorem realCarrierOccurrence_address_length_le_atomCount
    {fuel : Nat} (occurrence : input.LocalizedCIPOccurrence fuel)
    (real : occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    occurrence.1.address.length ≤ input.certified.input.molecule.atomCount := by
  have derived :=
    (input.mem_localizedOccurrences_iff fuel occurrence.1).mp occurrence.2
  have rooted := input.declarativeLocalizedOccurrence_as_rootSubtree derived
  have historyLength :
      occurrence.1.node.history.length = occurrence.1.address.length + 1 :=
    input.declarativeLocalizedOccurrenceSubtree_history_length rooted
      (by simp [OfficialCIPNode.root])
  have nodup :=
    input.realPathNode_history_nodup
      (input.carrierOccurrence_realPath_of_provenance_real occurrence real)
  have cardLe := nodup.length_le_card
  simp only [Fintype.card_fin] at cardLe
  omega

/-- **Real carrier occurrences have positive remaining expansion depth** at any carrier fuel at
least `atomCount`.  The address bound above and the exact depth grading `address.length +
remaining = fuel + 1` force this. -/
theorem multipleBondRealCarrierOccurrence_remaining_pos
    {fuel : Nat} (enough : input.certified.input.molecule.atomCount ≤ fuel)
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (real : occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    0 < occurrence.1.remaining := by
  have grade := input.declarativeLocalizedOccurrence_depthGrade
    ((input.mem_localizedOccurrences_iff fuel occurrence.1).mp occurrence.2)
  have bound :=
    input.realCarrierOccurrence_address_length_le_atomCount occurrence real
  omega

/-- **Carrier depth is the sibling address length.**  The node depth (`history.length - 1`) is
exactly the number of carrier edges from the original root, i.e. the address length.  The grading
is provenance-independent, so this is stated for every carrier occurrence; on the real spine it is
the depth API needed to compare real positions with physical distances. -/
theorem realCarrierOccurrence_depth_eq_address_length
    {fuel : Nat} (occurrence : input.LocalizedCIPOccurrence fuel) :
    occurrence.1.node.depth = occurrence.1.address.length := by
  have derived :=
    (input.mem_localizedOccurrences_iff fuel occurrence.1).mp occurrence.2
  have rooted := input.declarativeLocalizedOccurrence_as_rootSubtree derived
  have historyLength :
      occurrence.1.node.history.length = occurrence.1.address.length + 1 :=
    input.declarativeLocalizedOccurrenceSubtree_history_length rooted
      (by simp [OfficialCIPNode.root])
  unfold OfficialCIPNode.depth
  omega

/-! ## Fixed-original-root injectivity on the real spine -/







theorem realOccurrence_current_injective_at_fixedRoot
    (acyclic : input.moleculeGraph.Acyclic)
    {fuel : Nat} (a b : input.LocalizedCIPOccurrence fuel)
    (sameRoot : a.1.root = b.1.root)
    (sameCurrent : a.1.node.current? = b.1.node.current?)
    (aReal : a.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (bReal : b.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    a = b := by
  rcases a with ⟨⟨aRoot, aAddress, aNode, aRemaining⟩, aMember⟩
  rcases b with ⟨⟨bRoot, bAddress, bNode, bRemaining⟩, bMember⟩
  cases sameRoot
  have aDerived : input.DeclarativeLocalizedOccurrence fuel
      { root := aRoot, address := aAddress, node := aNode, remaining := aRemaining } :=
    (input.mem_localizedOccurrences_iff fuel _).mp aMember
  have bDerived : input.DeclarativeLocalizedOccurrence fuel
      { root := aRoot, address := bAddress, node := bNode, remaining := bRemaining } :=
    (input.mem_localizedOccurrences_iff fuel _).mp bMember
  have frameEq :
      ({ root := aRoot, address := aAddress, node := aNode, remaining := aRemaining } :
        input.LocalizedCIPOccurrenceFrame) =
      { root := aRoot, address := bAddress, node := bNode, remaining := bRemaining } :=
    input.declarativeLocalizedOccurrenceSubtree_determined_of_current acyclic
      (fuel := fuel + 1) (path := []) (node := OfficialCIPNode.root aRoot)
      (left := { root := aRoot, address := aAddress, node := aNode, remaining := aRemaining })
      (right := { root := aRoot, address := bAddress, node := bNode, remaining := bRemaining })
      (input.realRootedPath_root aRoot)
      (by simp [OfficialCIPNode.root])
      (by simpa using aDerived)
      (by simpa using bDerived)
      (input.carrierOccurrence_realPath_of_provenance_real
        ⟨{ root := aRoot, address := aAddress, node := aNode, remaining := aRemaining },
          aMember⟩ aReal)
      (input.carrierOccurrence_realPath_of_provenance_real
        ⟨{ root := aRoot, address := bAddress, node := bNode, remaining := bRemaining },
          bMember⟩ bReal)
      sameCurrent
  exact Subtype.ext (by simpa using frameEq)

/-- Address uniqueness of two real carrier occurrences at the same stored original root and the
same current atom. -/
theorem realOccurrence_address_eq_of_current_eq
    (acyclic : input.moleculeGraph.Acyclic)
    {fuel : Nat} (a b : input.LocalizedCIPOccurrence fuel)
    (sameRoot : a.1.root = b.1.root)
    (sameCurrent : a.1.node.current? = b.1.node.current?)
    (aReal : a.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (bReal : b.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    a.1.address = b.1.address := by
  have occurrenceEq :=
    input.realOccurrence_current_injective_at_fixedRoot acyclic a b
      sameRoot sameCurrent aReal bReal
  rw [occurrenceEq]

/-! ## The fresh copy-zero real child

This is the constructive half of the correspondence.  Unlike the accepted single-bond
`carrierChildFrame_of_adjacent_notParent`, the freshness of the new atom and hence the real
provenance of the child are derived from the actual simple real path and the incoming-parent
exclusion, not from `bond = 1`. -/

/-- **Fresh copy-zero real child frame.**  If the target is a carrier occurrence whose node has
`realAtom` provenance, `w` is a physical neighbor of its current atom, and `w` is not the stored
parent atom, then the executable raw copy `(w, 0)` exists at its actual address slot and yields a
child frame that

* sits at `target.address ++ [slot]` with the same stored original root,
* has current atom `w`,
* is literally `target.node.extend w 0` with `realAtom` provenance,
* belongs to the shared carrier and to the target's outward carrier children,
* and is a real path node from the original root.

The child atom is fresh on the stored branch by `not_mem_history_of_real_zero_step`, so
`childProvenance` at copy zero is `realAtom` (a ring duplicate is impossible).  No bond order
restriction is used. -/
theorem realChildFrame_of_adjacent_notParent
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {oAtom w : input.Atom}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (realProvenance : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (oObserved : target.1.node.current? = some oAtom)
    (adjacent : input.moleculeGraph.Adj oAtom w)
    (notParent : target.1.node.parent? ≠ some w) :
    ∃ (childFrame : input.LocalizedCIPOccurrenceFrame) (slot : Nat),
      childFrame.address = target.1.address ++ [slot] ∧
      childFrame.root = target.1.root ∧
      childFrame.node.current? = some w ∧
      childFrame.node = target.1.node.extend w 0 ∧
      childFrame.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
      childFrame ∈ input.localizedOccurrences carrierFuel ∧
      childFrame ∈ input.localizedCarrierOutwardChildFrames
        (fuel := carrierFuel) target.1 ∧
      input.RealPathNode target.1.root childFrame.node := by
  have realPath :=
    input.carrierOccurrence_realPath_of_provenance_real target realProvenance
  have nonduplicate : target.1.node.isDuplicateLeaf = false :=
    input.isDuplicateLeaf_eq_false_of_provenance_real target.1.node realProvenance
  have copyPresent : (w, 0) ∈ input.executableOfficialChildCopies target.1.node :=
    input.mem_executableOfficialChildCopies_of_adjacent target.1.node oAtom w 0
      oObserved adjacent adjacent (Or.inr notParent)
  let slot := input.executableOfficialChildCopySlot target.1.node w 0
  have atSlot : (target.1.node.extend w 0, slot) ∈
      (input.executableOfficialCIPChildren target.1.node).zipIdx :=
    input.executableOfficialChildCopySlot_mem target.1.node w 0 nonduplicate copyPresent
  have sourceDerived :=
    (input.mem_localizedOccurrences_iff carrierFuel target.1).mp target.2
  have positive :=
    input.multipleBondRealCarrierOccurrence_remaining_pos enough target realProvenance
  let childFrame : input.LocalizedCIPOccurrenceFrame :=
    { root := target.1.root
      address := target.1.address ++ [slot]
      node := target.1.node.extend w 0
      remaining := target.1.remaining - 1 }
  have childDerived : input.DeclarativeLocalizedOccurrence carrierFuel childFrame :=
    DeclarativeLocalizedOccurrence.immediateChild input sourceDerived positive atSlot
  have childMember : childFrame ∈ input.localizedOccurrences carrierFuel :=
    (input.mem_localizedOccurrences_iff carrierFuel childFrame).mpr childDerived
  have outwardPresent : childFrame ∈
      input.localizedCarrierOutwardChildFrames (fuel := carrierFuel) target.1 := by
    rw [localizedCarrierOutwardChildFrames, List.mem_filter]
    refine ⟨childMember, ?_⟩
    simp [childFrame]
  have fresh : w ∉ target.1.node.history :=
    input.not_mem_history_of_real_zero_step acyclic realPath oObserved adjacent notParent
  have childReal : (target.1.node.extend w 0).provenance =
      OfficialCIPNodeProvenance.realAtom := by
    rw [OfficialCIPNode.extend_provenance]
    exact OfficialCIPNode.childProvenance_real target.1.node w fresh
  have childRealPath : input.RealPathNode target.1.root (target.1.node.extend w 0) :=
    input.realPathNode_child_of_mem_executableOfficialCIPChildren realPath
      (List.fst_mem_of_mem_zipIdx atSlot) childReal
  refine ⟨childFrame, slot, rfl, rfl, ?_, rfl, ?_, childMember, outwardPresent, ?_⟩
  · simp [childFrame]
  · simpa [childFrame] using childReal
  · simpa [childFrame] using childRealPath

/-- **Copy-zero address slot uniqueness.**  For a real path node, any executable child slot that
holds the extension `node.extend w 0` is exactly the raw-copy slot of `(w, 0)`.  This is where the
multiplicity-faithful slot API `executableOfficialChildCopySlot` pins the real child coordinate:
the extended node alone does not determine the slot, but the real provenance of the child does.

`simpleOccurrencePath_address_unique` is the corresponding uniqueness for graph-level simple
occurrence addresses; this theorem is its executable-enumeration counterpart. -/
theorem realChildFrame_slot_eq_copySlot
    (acyclic : input.moleculeGraph.Acyclic)
    {root : input.Atom} {node : OfficialCIPNode input.Atom}
    {current w : input.Atom}
    (realPath : input.RealPathNode root node)
    (currentObserved : node.current? = some current)
    (adjacent : input.moleculeGraph.Adj current w)
    (notParent : node.parent? ≠ some w)
    {slot : Nat}
    (atSlot : (node.extend w 0, slot) ∈
      (input.executableOfficialCIPChildren node).zipIdx) :
    slot = input.executableOfficialChildCopySlot node w 0 := by
  have nonduplicate : node.isDuplicateLeaf = false :=
    input.isDuplicateLeaf_eq_false_of_provenance_real node
      (input.realPathNode_provenance realPath)
  have copyPresent : (w, 0) ∈ input.executableOfficialChildCopies node :=
    input.mem_executableOfficialChildCopies_of_adjacent node current w 0
      currentObserved adjacent adjacent (Or.inr notParent)
  have canonicalAtSlot :=
    input.executableOfficialChildCopySlot_mem node w 0 nonduplicate copyPresent
  have fresh : w ∉ node.history :=
    input.not_mem_history_of_real_zero_step acyclic realPath currentObserved adjacent notParent
  have extendedReal : (node.extend w 0).provenance =
      OfficialCIPNodeProvenance.realAtom := by
    rw [OfficialCIPNode.extend_provenance]
    exact OfficialCIPNode.childProvenance_real node w fresh
  exact input.physical_executableOfficialCIPChild_slot_unique node (node.extend w 0) slot
    (input.executableOfficialChildCopySlot node w 0) atSlot canonicalAtSlot (Or.inl extendedReal)

/-- **Reverse real parent edge.**  For a non-root carrier occurrence whose stored parent atom is
`w`, the actual parent frame is a real-provenance occurrence at `target.address.dropLast`, its
current atom is exactly `w`, and `w` is physically adjacent to the target's current atom.  This
is the `previous`-independent endpoint fact used by the reverse direction of the correspondence. -/
theorem realParentFrame_adjacent_and_current
    {carrierFuel : Nat}
    {oAtom w : input.Atom}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (oObserved : target.1.node.current? = some oAtom)
    (nonroot : target.1.address ≠ [])
    (sameParent : target.1.node.parent? = some w) :
    ∃ certificate : input.LocalizedParentFrameHistory target,
      certificate.parent.1.node.current? = some w ∧
      certificate.parent.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
      certificate.parent.1.address = target.1.address.dropLast ∧
      input.moleculeGraph.Adj oAtom w := by
  obtain ⟨certificate⟩ := input.exists_localizedParentFrameHistory target nonroot
  obtain ⟨_current, parentCurrent, _tail, _currentEq, parentCurrentEq, historyEq,
    _parentHistoryEq⟩ := certificate.history_shape input
  have parentObserved : target.1.node.parent? = some parentCurrent := by
    simp [OfficialCIPNode.parent?, historyEq]
  have parentEq : parentCurrent = w := by
    rw [parentObserved] at sameParent
    exact Option.some.inj sameParent
  have certificateCurrent : certificate.parent.1.node.current? = some w := by
    rw [← parentEq]
    exact parentCurrentEq
  obtain ⟨parentCurrent', parentCurrentObserved', adjacent'⟩ :=
    input.parentFrame_current_adjacent oObserved nonroot certificate
  have currentEq : parentCurrent' = w :=
    Option.some.inj (parentCurrentObserved'.symm.trans certificateCurrent)
  rw [currentEq] at adjacent'
  exact ⟨certificate, certificateCurrent, certificate.parent_provenance input,
    certificate.parent_address, adjacent'⟩

/-! ## Provenance-free physical adjacency of intended child frames

Every intended child frame -- including a multiple-bond duplicate copy -- projects to a physical
neighbor of the source current atom.  This direction is true at arbitrary bond order and is the
honest part of "all children are neighbors".  It does *not* claim injectivity or the exclusion of
the incoming atom for duplicate copies; those hold only on the real spine. -/

/-- **Every intended child frame's current atom is a physical neighbor.**  The frame is classified
either as the actual carrier parent (shorter address) or as a strict outward carrier child; both
cases are physically adjacent by the executable child enumeration.  No provenance, acyclicity or
bond-order hypothesis is used. -/
theorem intendedChildFrame_current_adjacent
    {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    {frame : input.LocalizedCIPOccurrenceFrame}
    (intended : frame ∈ input.intendedLocalizedRerootChildFrames cursor)
    {oAtom w : input.Atom}
    (oObserved : cursor.occurrence.1.node.current? = some oAtom)
    (frameCurrent : frame.node.current? = some w) :
    input.moleculeGraph.Adj oAtom w := by
  have neighbor :=
    input.mem_localizedRerootNeighborFrames_of_mem_intended cursor frame intended
  have characterized :=
    (input.mem_localizedRerootNeighborFrames_iff cursor.occurrence.1 frame).mp neighbor
  obtain ⟨framePresent, sameFrameRoot, classified⟩ := characterized
  rcases classified with parentCase | childCase
  · have parentCase' := parentCase
    have nonroot : cursor.occurrence.1.address ≠ [] := by
      intro empty
      rw [empty] at parentCase'
      simp at parentCase'
    obtain ⟨certificate⟩ :=
      input.exists_localizedParentFrameHistory cursor.occurrence nonroot
    have frameEq : frame = certificate.parent.1 :=
      input.declarativeLocalizedOccurrence_functional_at_root_address
        ((input.mem_localizedOccurrences_iff carrierFuel frame).mp framePresent)
        ((input.mem_localizedOccurrences_iff carrierFuel certificate.parent.1).mp
          certificate.parent.2)
        (sameFrameRoot.trans certificate.parent_root.symm)
        (parentCase'.2.trans certificate.parent_address.symm)
    obtain ⟨parentCurrent, parentCurrentObserved, parentAdjacent⟩ :=
      input.parentFrame_current_adjacent oObserved nonroot certificate
    have frameCurrent' : certificate.parent.1.node.current? = some w := by
      rw [frameEq] at frameCurrent
      exact frameCurrent
    have wEq : w = parentCurrent :=
      Option.some.inj (frameCurrent'.symm.trans parentCurrentObserved)
    rw [wEq]
    exact parentAdjacent
  · have childCase' := childCase
    have nonempty : frame.address ≠ [] := by
      intro empty
      rw [empty] at childCase'
      simp at childCase'
    refine input.outwardChildFrame_current_adjacent oObserved frame neighbor
      (frame.address.getLast nonempty) ?_ frameCurrent
    calc frame.address
        = frame.address.dropLast ++ [frame.address.getLast nonempty] :=
          (List.dropLast_append_getLast (l := frame.address) nonempty).symm
      _ = cursor.occurrence.1.address ++ [frame.address.getLast nonempty] := by
          rw [← childCase'.2]

/-! ## The real-spine reroot-neighbor correspondence -/

/-- **Real children realize exactly the parent-deleted physical neighborhood at arbitrary bond
order.**  Let `cursor` be an actual reroot cursor whose current occurrence is a real path node,
let `previous` be its recorded incoming coordinate, also a real path node at the same stored
original root, and let `localizedRerootChildren? cursor = some children`.  Then a physical atom
`w` is the current atom of some **real-provenance** child of the expansion if and only if `w` is
a physical neighbor of the current atom `oAtom` and `w` is not the incoming atom `pAtom`.

Compared with the accepted single-bond theorem
`localizedRerootChildren?_current_iff_adjacent_of_previous`, the global `SimpleBonded` hypothesis
is replaced by exactly two real-spine witnesses (`sourceReal`, `previousReal`).  `Acyclic` is
retained.  Emitted multiple-bond duplicate children are intentionally excluded from the
existential: their current atom can be the incoming atom, and they are not part of the real
position slice (see `localizedRerootChildren?_multipleBondCopy_survives`).

Forward: every intended child is physically adjacent
(`intendedChildFrame_current_adjacent`); a real child equal to the incoming atom in current
position would be the incoming carrier coordinate by
`realOccurrence_current_injective_at_fixedRoot`, but the address cut removed exactly that
coordinate.  Reverse: the neighbor is either the stored parent atom, realized by the actual
parent frame, or a fresh copy-zero real child constructed at its raw-copy slot. -/
theorem localizedRerootChildren?_realChild_exists_iff_adjacent
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous)
    (incomingRoot : previous.1.root = cursor.occurrence.1.root)
    (sourceReal : input.RealPathNode cursor.occurrence.1.root cursor.occurrence.1.node)
    (previousReal : input.RealPathNode previous.1.root previous.1.node)
    {oAtom pAtom : input.Atom}
    (oObserved : cursor.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (children : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRerootChildren? cursor = some children) :
    ∀ w, (∃ child ∈ children,
            child.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
              child.occurrence.1.node.current? = some w) ↔
          input.moleculeGraph.Adj oAtom w ∧ w ≠ pAtom := by
  have derived := input.localizedRerootChildren?_sound cursor children computed
  have previousDerived :=
    (input.mem_localizedOccurrences_iff carrierFuel previous.1).mp previous.2
  have previousRealSource : input.RealPathNode cursor.occurrence.1.root previous.1.node :=
    incomingRoot ▸ previousReal
  have previousProvenance := input.realPathNode_provenance previousRealSource
  intro w
  constructor
  · rintro ⟨child, childPresent, childReal, childCurrent⟩
    have intended : child.occurrence.1 ∈
        input.intendedLocalizedRerootChildFrames cursor := by
      rw [← derived.1]
      exact List.mem_map.mpr ⟨child, childPresent, rfl⟩
    have physical :=
      input.intendedChildFrame_current_adjacent cursor intended oObserved childCurrent
    have childNotPrevious : child.occurrence.1.address ≠ previous.1.address :=
      input.address_ne_previous_of_mem_intended cursor previous previousEq
        child.occurrence.1 intended
    have currentNe : w ≠ pAtom := by
      intro wEq
      have childRoot : child.occurrence.1.root = previous.1.root :=
        (input.localizedRerootChildren?_root_eq cursor children computed child
          childPresent).trans incomingRoot.symm
      have occurrenceEq := input.realOccurrence_current_injective_at_fixedRoot acyclic
        child.occurrence previous childRoot (by rw [childCurrent, pObserved, wEq])
        childReal previousProvenance
      have addressEq : child.occurrence.1.address = previous.1.address :=
        congrArg (fun occurrence : input.LocalizedCIPOccurrence carrierFuel =>
          occurrence.1.address) occurrenceEq
      exact childNotPrevious addressEq
    exact ⟨physical, currentNe⟩
  · rintro ⟨adjacent, wNeP⟩
    have nonduplicate : cursor.occurrence.1.node.isDuplicateLeaf = false :=
      input.isDuplicateLeaf_eq_false_of_provenance_real cursor.occurrence.1.node
        (input.realPathNode_provenance sourceReal)
    by_cases sameParent : cursor.occurrence.1.node.parent? = some w
    · -- The neighbor is the stored parent atom: realize the actual parent frame.
      have nonroot : cursor.occurrence.1.address ≠ [] := by
        intro empty
        have targetDerived :=
          (input.mem_localizedOccurrences_iff carrierFuel cursor.occurrence.1).mp
            cursor.occurrence.2
        have rootShape :=
          input.declarativeLocalizedOccurrence_eq_root_of_address_nil targetDerived empty
        have parentNone : cursor.occurrence.1.node.parent? = none := by
          rw [rootShape]
          simp [OfficialCIPNode.root, OfficialCIPNode.parent?]
        rw [parentNone] at sameParent
        simp at sameParent
      obtain ⟨certificate⟩ :=
        input.exists_localizedParentFrameHistory cursor.occurrence nonroot
      obtain ⟨_current, parentCurrent, _tail, _currentEq, parentCurrentEq,
        historyEq, _parentHistoryEq⟩ := certificate.history_shape input
      have parentObserved : cursor.occurrence.1.node.parent? = some parentCurrent := by
        simp [OfficialCIPNode.parent?, historyEq]
      have parentEq : parentCurrent = w := by
        rw [parentObserved] at sameParent
        exact Option.some.inj sameParent
      have certificateCurrent : certificate.parent.1.node.current? = some w := by
        rw [← parentEq]
        exact parentCurrentEq
      have addressNe : certificate.parent.1.address ≠ previous.1.address := by
        intro sameAddress
        have frameEq := input.declarativeLocalizedOccurrence_functional_at_root_address
          ((input.mem_localizedOccurrences_iff carrierFuel certificate.parent.1).mp
            certificate.parent.2)
          previousDerived
          (certificate.parent_root.trans incomingRoot.symm) sameAddress
        have currentSame :
            certificate.parent.1.node.current? = previous.1.node.current? :=
          congrArg (fun frame => frame.node.current?) frameEq
        rw [certificateCurrent, pObserved] at currentSame
        exact wNeP (Option.some.inj currentSame)
      have intended : certificate.parent.1 ∈
          input.intendedLocalizedRerootChildFrames cursor := by
        unfold intendedLocalizedRerootChildFrames
        rw [if_neg (by simpa using nonduplicate)]
        rw [previousEq]
        rw [List.mem_filter]
        exact ⟨certificate.parent_mem_neighborFrames input,
          by simpa using addressNe⟩
      have member : certificate.parent.1 ∈
          children.map (fun child => child.occurrence.1) := by
        rw [derived.1]
        exact intended
      rw [List.mem_map] at member
      obtain ⟨childCursor, childPresent, childOccurrenceEq⟩ := member
      exact ⟨childCursor, childPresent, by
        rw [childOccurrenceEq]
        exact certificate.parent_provenance input, by
        rw [childOccurrenceEq]
        exact certificateCurrent⟩
    · -- The neighbor is fresh: realize the actual executable zero-copy real child.
      have notParent : cursor.occurrence.1.node.parent? ≠ some w := sameParent
      obtain ⟨childFrame, slot, addressEq, rootEq, frameCurrent, _nodeEq, frameProvenance,
        childMember, outwardPresent, _childRealPath⟩ :=
        input.realChildFrame_of_adjacent_notParent acyclic enough cursor.occurrence
          (input.realPathNode_provenance sourceReal) oObserved adjacent notParent
      have childDerived :=
        (input.mem_localizedOccurrences_iff carrierFuel childFrame).mp childMember
      have neighborPresent : childFrame ∈
          input.localizedRerootNeighborFrames (fuel := carrierFuel)
            cursor.occurrence.1 :=
        List.mem_append_right _ outwardPresent
      have addressNe : childFrame.address ≠ previous.1.address := by
        intro sameAddress
        have frameEq := input.declarativeLocalizedOccurrence_functional_at_root_address
          childDerived previousDerived (rootEq.trans incomingRoot.symm) sameAddress
        have currentSame : childFrame.node.current? = previous.1.node.current? :=
          congrArg (fun frame => frame.node.current?) frameEq
        rw [frameCurrent, pObserved] at currentSame
        exact wNeP (Option.some.inj currentSame)
      have intended : childFrame ∈
          input.intendedLocalizedRerootChildFrames cursor := by
        unfold intendedLocalizedRerootChildFrames
        rw [if_neg (by simpa using nonduplicate)]
        rw [previousEq]
        rw [List.mem_filter]
        exact ⟨neighborPresent, by simpa using addressNe⟩
      have member : childFrame ∈ children.map (fun child => child.occurrence.1) := by
        rw [derived.1]
        exact intended
      rw [List.mem_map] at member
      obtain ⟨childCursor, childPresent', childOccurrenceEq⟩ := member
      exact ⟨childCursor, childPresent', by
        rw [childOccurrenceEq]
        exact frameProvenance, by
        rw [childOccurrenceEq]
        exact frameCurrent⟩

/-- **Real-child uniqueness.**  Two children of one actual expansion with `realAtom` provenance
and the same current atom are the same cursor.  Only `Acyclic` and the realness of the two
children are used; no fuel bound and no incoming coordinate are needed.  This is the
real-spine replacement for `localizedRerootChildren?_current_injective`, which requires
`SimpleBonded`. -/
theorem localizedRerootChildren?_realChild_unique
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (children : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRerootChildren? cursor = some children) :
    ∀ left ∈ children, ∀ right ∈ children,
      left.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom →
      right.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom →
      left.occurrence.1.node.current? = right.occurrence.1.node.current? →
      left = right := by
  intro left leftPresent right rightPresent leftReal rightReal sameCurrent
  have derived := input.localizedRerootChildren?_sound cursor children computed
  have leftRoot :=
    input.localizedRerootChildren?_root_eq cursor children computed left leftPresent
  have rightRoot :=
    input.localizedRerootChildren?_root_eq cursor children computed right rightPresent
  have occurrenceEq := input.realOccurrence_current_injective_at_fixedRoot acyclic
    left.occurrence right.occurrence (leftRoot.trans rightRoot.symm) sameCurrent
    leftReal rightReal
  exact LocalizedRerootCursor.ext input occurrenceEq
    ((derived.2 left leftPresent).trans (derived.2 right rightPresent).symm)

/-- **Every emitted child projects to a physical neighbor.**  This includes multiple-bond
duplicate children and hence does not exclude the incoming atom.  It records the honest
provenance-free half of the correspondence at arbitrary bond order. -/
theorem localizedRerootChildren?_child_current_adjacent
    {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (children : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRerootChildren? cursor = some children)
    {oAtom w : input.Atom}
    (oObserved : cursor.occurrence.1.node.current? = some oAtom)
    (child : input.LocalizedRerootCursor carrierFuel)
    (childPresent : child ∈ children)
    (childCurrent : child.occurrence.1.node.current? = some w) :
    input.moleculeGraph.Adj oAtom w := by
  have derived := input.localizedRerootChildren?_sound cursor children computed
  have intended : child.occurrence.1 ∈
      input.intendedLocalizedRerootChildFrames cursor := by
    rw [← derived.1]
    exact List.mem_map.mpr ⟨child, childPresent, rfl⟩
  exact input.intendedChildFrame_current_adjacent cursor intended oObserved childCurrent

/-- **The uncut multiple-bond copy survives.**  If the incoming physical edge has bond order at
least two, the expansion of a real source contains a child whose provenance is
`multipleBondDuplicate source.depth` and whose current atom is the incoming atom `pAtom`.  Since
`pAtom ≠ oAtom`, this child is not a real-spine cut neighbor; it proves that blanket
"children ↔ parent-deleted neighborhood" statements and blanket current-atom injectivity are
false and that the real-provenance restriction in
`localizedRerootChildren?_realChild_exists_iff_adjacent` is necessary. -/
theorem localizedRerootChildren?_multipleBondCopy_survives
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous)
    (incomingRoot : previous.1.root = cursor.occurrence.1.root)
    (sourceReal : input.RealPathNode cursor.occurrence.1.root cursor.occurrence.1.node)
    (previousReal : input.RealPathNode previous.1.root previous.1.node)
    {oAtom pAtom : input.Atom}
    (oObserved : cursor.occurrence.1.node.current? = some oAtom)
    (_pObserved : previous.1.node.current? = some pAtom)
    (adjacent : input.moleculeGraph.Adj oAtom pAtom)
    (bondTwo : 1 < input.moleculeGraph.bond oAtom pAtom)
    (children : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRerootChildren? cursor = some children) :
    ∃ child ∈ children,
      child.occurrence.1.node.provenance =
          OfficialCIPNodeProvenance.multipleBondDuplicate cursor.occurrence.1.node.depth ∧
        child.occurrence.1.node.current? = some pAtom := by
  have sourceProvenance := input.realPathNode_provenance sourceReal
  have nonduplicate : cursor.occurrence.1.node.isDuplicateLeaf = false :=
    input.isDuplicateLeaf_eq_false_of_provenance_real cursor.occurrence.1.node
      sourceProvenance
  have positive :=
    input.multipleBondRealCarrierOccurrence_remaining_pos enough cursor.occurrence sourceProvenance
  have copyPresent : (pAtom, 1) ∈ input.executableOfficialChildCopies cursor.occurrence.1.node :=
    input.mem_executableOfficialChildCopies_of_adjacent cursor.occurrence.1.node oAtom pAtom 1
      oObserved adjacent bondTwo (Or.inl (by decide))
  let slot := input.executableOfficialChildCopySlot cursor.occurrence.1.node pAtom 1
  have atSlot : (cursor.occurrence.1.node.extend pAtom 1, slot) ∈
      (input.executableOfficialCIPChildren cursor.occurrence.1.node).zipIdx :=
    input.executableOfficialChildCopySlot_mem cursor.occurrence.1.node pAtom 1
      nonduplicate copyPresent
  have sourceDerived :=
    (input.mem_localizedOccurrences_iff carrierFuel cursor.occurrence.1).mp
      cursor.occurrence.2
  let childFrame : input.LocalizedCIPOccurrenceFrame :=
    { root := cursor.occurrence.1.root
      address := cursor.occurrence.1.address ++ [slot]
      node := cursor.occurrence.1.node.extend pAtom 1
      remaining := cursor.occurrence.1.remaining - 1 }
  have childDerived : input.DeclarativeLocalizedOccurrence carrierFuel childFrame :=
    DeclarativeLocalizedOccurrence.immediateChild input sourceDerived positive atSlot
  have childMember : childFrame ∈ input.localizedOccurrences carrierFuel :=
    (input.mem_localizedOccurrences_iff carrierFuel childFrame).mpr childDerived
  have outwardPresent : childFrame ∈
      input.localizedCarrierOutwardChildFrames (fuel := carrierFuel) cursor.occurrence.1 := by
    rw [localizedCarrierOutwardChildFrames, List.mem_filter]
    refine ⟨childMember, ?_⟩
    simp [childFrame]
  have neighborPresent : childFrame ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel) cursor.occurrence.1 :=
    List.mem_append_right _ outwardPresent
  have childProvenance : childFrame.node.provenance =
      OfficialCIPNodeProvenance.multipleBondDuplicate cursor.occurrence.1.node.depth := by
    rw [OfficialCIPNode.extend_provenance]
    exact OfficialCIPNode.childProvenance_copy_pos cursor.occurrence.1.node pAtom (by omega)
  have previousDerived :=
    (input.mem_localizedOccurrences_iff carrierFuel previous.1).mp previous.2
  have addressNe : childFrame.address ≠ previous.1.address := by
    intro sameAddress
    have frameEq := input.declarativeLocalizedOccurrence_functional_at_root_address
      childDerived previousDerived incomingRoot.symm sameAddress
    have provenanceEq : childFrame.node.provenance = previous.1.node.provenance :=
      congrArg (fun frame => frame.node.provenance) frameEq
    rw [childProvenance, input.realPathNode_provenance previousReal] at provenanceEq
    exact OfficialCIPNodeProvenance.noConfusion provenanceEq
  have intended : childFrame ∈
      input.intendedLocalizedRerootChildFrames cursor := by
    unfold intendedLocalizedRerootChildFrames
    rw [if_neg (by simpa using nonduplicate)]
    rw [previousEq]
    rw [List.mem_filter]
    exact ⟨neighborPresent, by simpa using addressNe⟩
  have derived := input.localizedRerootChildren?_sound cursor children computed
  have member : childFrame ∈ children.map (fun child => child.occurrence.1) := by
    rw [derived.1]
    exact intended
  rw [List.mem_map] at member
  obtain ⟨childCursor, childCursorPresent, childOccurrenceEq⟩ := member
  exact ⟨childCursor, childCursorPresent, by
    rw [childOccurrenceEq]
    exact childProvenance, by
    rw [childOccurrenceEq]
    simp [childFrame]⟩

/-- **Bundled real-spine correspondence and uniqueness.**  The real children of one actual
expansion realize exactly the parent-deleted physical neighborhood, and their current-atom
projection is injective on the real spine.  The second component is independent of the incoming
coordinate and of the fuel bound. -/
theorem localizedRerootChildren?_realChild_correspondence
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous)
    (incomingRoot : previous.1.root = cursor.occurrence.1.root)
    (sourceReal : input.RealPathNode cursor.occurrence.1.root cursor.occurrence.1.node)
    (previousReal : input.RealPathNode previous.1.root previous.1.node)
    {oAtom pAtom : input.Atom}
    (oObserved : cursor.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (children : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRerootChildren? cursor = some children) :
    (∀ w, (∃ child ∈ children,
            child.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
              child.occurrence.1.node.current? = some w) ↔
          input.moleculeGraph.Adj oAtom w ∧ w ≠ pAtom) ∧
      (∀ left ∈ children, ∀ right ∈ children,
        left.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom →
        right.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom →
        left.occurrence.1.node.current? = right.occurrence.1.node.current? →
        left = right) ∧
      (∀ child ∈ children, ∀ w, child.occurrence.1.node.current? = some w →
        input.moleculeGraph.Adj oAtom w) :=
  ⟨input.localizedRerootChildren?_realChild_exists_iff_adjacent acyclic enough cursor
      previous previousEq incomingRoot sourceReal previousReal oObserved pObserved children
      computed,
    input.localizedRerootChildren?_realChild_unique acyclic cursor children computed,
    fun child childPresent _w childCurrent =>
      input.localizedRerootChildren?_child_current_adjacent cursor children computed
        oObserved child childPresent childCurrent⟩

/-! ## Simple-occurrence callers

The correspondence can be fed directly by graph-level `SimpleOccurrencePath` witnesses, which is
the interface produced by the accepted simple-walk carrier constructions.  The conversion uses
`simpleOccurrencePath_realPathNode`; no single-bond hypothesis is added. -/

/-- Graph-level simple occurrence paths have a unique sibling address at a fixed node.  This is the
existing multiplicity-generic `simpleOccurrencePath_address_unique`, exposed for callers of the
real-spine correspondence. -/
theorem simpleOccurrencePath_address_eq_of_node_eq
    {root : input.Atom} {node : OfficialCIPNode input.Atom}
    {leftAddress rightAddress : List Nat}
    (left : SimpleOccurrencePath input root node leftAddress)
    (right : SimpleOccurrencePath input root node rightAddress) :
    leftAddress = rightAddress :=
  input.simpleOccurrencePath_address_unique left right rfl

/-- **Real-spine correspondence from `SimpleOccurrencePath` witnesses.**  Same statement as
`localizedRerootChildren?_realChild_exists_iff_adjacent`, with the two real-spine witnesses given
as graph-level simple occurrences.  This is the intended entry point for callers that construct
occurrences from simple physical walks. -/
theorem localizedRerootChildren?_realChild_exists_iff_adjacent_of_simplePaths
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous)
    (incomingRoot : previous.1.root = cursor.occurrence.1.root)
    {sourceAddress previousAddress : List Nat}
    (sourcePath : SimpleOccurrencePath input cursor.occurrence.1.root
      cursor.occurrence.1.node sourceAddress)
    (previousPath : SimpleOccurrencePath input previous.1.root
      previous.1.node previousAddress)
    {oAtom pAtom : input.Atom}
    (oObserved : cursor.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (children : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRerootChildren? cursor = some children) :
    ∀ w, (∃ child ∈ children,
            child.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
              child.occurrence.1.node.current? = some w) ↔
          input.moleculeGraph.Adj oAtom w ∧ w ≠ pAtom :=
  input.localizedRerootChildren?_realChild_exists_iff_adjacent acyclic enough cursor previous
    previousEq incomingRoot
    (input.simpleOccurrencePath_realPathNode sourcePath)
    (input.simpleOccurrencePath_realPathNode previousPath)
    oObserved pObserved children computed

/-! ## Restricted real-slice cut equivalence

The local real-spine correspondence is iterated exactly as the accepted single-bond
`actualChildReachable_current_iff_cutBranch`, with one change: the step relation is restricted to
children whose provenance is `realAtom`.  This restriction is not a convenience -- it is forced by
`localizedRerootChildren?_multipleBondCopy_survives`, which shows that a positive-bond duplicate
child can carry the deleted incoming atom as its current atom.

The resulting statement is the honest cut equivalence at arbitrary bond order: on the real
position slice, reachable current atoms are exactly the physical cut branch after deleting the
genuine incoming atom.  Every step is still an actual executable child-list member; no synthetic
rerooted graph or assumed child bijection is introduced. -/

/-- Reachability through actual executable child steps whose target child has real provenance.
The zero-step path is included. -/
def RealChildReachable (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (start target : input.LocalizedRerootCursor carrierFuel) : Prop :=
  Relation.ReflTransGen
    (fun left right : input.LocalizedRerootCursor carrierFuel =>
      E input left right ∧
        right.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    start target

/-- Geometric state of a real-reachable cursor.  In addition to the accepted
`ActualCutReachableState` invariants (validity, preserved original root, monotone address length,
strictly shorter incoming coordinate), the recorded incoming occurrence and the cursor's own node
are both required to have `realAtom` provenance.  Those two witnesses are exactly what the local
real-spine correspondence needs at every step. -/
structure RealCutReachableState (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (start cursor : input.LocalizedRerootCursor carrierFuel) : Prop where
  valid : input.LocalizedRerootCursorValid cursor
  root : cursor.occurrence.1.root = start.occurrence.1.root
  atLeast : start.occurrence.1.address.length ≤ cursor.occurrence.1.address.length
  strictlyDeeper : cursor ≠ start →
    start.occurrence.1.address.length < cursor.occurrence.1.address.length
  incomingRealShorter : ∃ previous : input.LocalizedCIPOccurrence carrierFuel,
    cursor.previous? = some previous ∧
      previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
        previous.1.address.length < cursor.occurrence.1.address.length
  currentReal : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom

/-- **One real executable step preserves the reachable geometric state and the cut branch.**  The
proof is the accepted single-bond step with the local neighbor theorem replaced by
`localizedRerootChildren?_realChild_exists_iff_adjacent`.  The source cursor and its recorded
incoming occurrence are real by the state invariant, so no `SimpleBonded` hypothesis is needed.
The deleted root is excluded exactly as in the accepted proof: a real child whose current atom
were `pAtom` would be the unique fixed-root real occurrence `previous` (real-spine injectivity),
but its address is strictly longer than the start address while `previous` is strictly shorter. -/
theorem realCutReachableState_step
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (sameRootStart : start.occurrence.1.root = previous.1.root)
    (parentShorter : previous.1.address.length < start.occurrence.1.address.length)
    (previousReal : previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {oAtom pAtom : input.Atom}
    (pObserved : previous.1.node.current? = some pAtom)
    (b c : input.LocalizedRerootCursor carrierFuel)
    (stateB : input.RealCutReachableState start b)
    (branchB : ∀ w, b.occurrence.1.node.current? = some w →
      w ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom)
    (step : E input b c)
    (cReal : c.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    input.RealCutReachableState start c ∧
      ∀ w, c.occurrence.1.node.current? = some w →
        w ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom := by
  obtain ⟨previousB, previousEqB, previousBReal, previousShorterB⟩ :=
    stateB.incomingRealShorter
  obtain ⟨_dropLast, childLength, childRoot, childPrevious, childValid⟩ :=
    input.outward_edge b c stateB.valid previousB previousEqB previousShorterB step
  have stateC : input.RealCutReachableState start c :=
    { valid := childValid
      root := childRoot.trans stateB.root
      atLeast := by
        rw [childLength]
        exact Nat.le_trans stateB.atLeast (Nat.le_succ _)
      strictlyDeeper := by
        intro _notStart
        rw [childLength]
        exact Nat.lt_of_le_of_lt stateB.atLeast (Nat.lt_succ_self _)
      incomingRealShorter := ⟨b.occurrence, childPrevious, stateB.currentReal, by
        rw [childLength]
        exact Nat.lt_succ_self _⟩
      currentReal := cReal }
  refine ⟨stateC, ?_⟩
  intro w observed
  have cursorNeighbor : b.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel) previousB.1 := by
    have validB : input.LocalizedRerootCursorValid b := stateB.valid
    unfold LocalizedRerootCursorValid at validB
    rw [previousEqB] at validB
    change b.occurrence.1 ∈ input.localizedRerootNeighborFrames
      (fuel := carrierFuel) previousB.1 at validB
    exact validB
  have sameRootB : b.occurrence.1.root = previousB.1.root :=
    ((input.mem_localizedRerootNeighborFrames_iff previousB.1 b.occurrence.1).mp
      cursorNeighbor).2.1
  have bDerived : input.DeclarativeLocalizedOccurrence carrierFuel b.occurrence.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel b.occurrence.1).mp b.occurrence.2
  have previousBDerived :
      input.DeclarativeLocalizedOccurrence carrierFuel previousB.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel previousB.1).mp previousB.2
  obtain ⟨x, xObserved⟩ := Option.isSome_iff_exists.mp
    (input.declarativeLocalizedOccurrence_node_current_isSome bDerived)
  obtain ⟨z, zObserved⟩ := Option.isSome_iff_exists.mp
    (input.declarativeLocalizedOccurrence_node_current_isSome previousBDerived)
  have localIff :=
    input.localizedRerootChildren?_realChild_exists_iff_adjacent (acyclic := acyclic)
      (enough := enough) (cursor := b) (previous := previousB) previousEqB sameRootB.symm
      (input.carrierOccurrence_realPath_of_provenance_real b.occurrence stateB.currentReal)
      (input.carrierOccurrence_realPath_of_provenance_real previousB previousBReal)
      xObserved zObserved (input.executableLocalizedRerootChildren b)
      (input.localizedRerootChildren?_eq_some_executable b)
  obtain ⟨adjacent, _notZ⟩ :=
    (localIff w).mp ⟨c, step, cReal, observed⟩
  have xBranch : x ∈ AcyclicCutBranchAutomorphism.CutBranch
      input.moleculeGraph pAtom oAtom :=
    branchB x xObserved
  have wNeRoot : w ≠ pAtom := by
    intro wEq
    have occurrenceEq : c.occurrence = previous :=
      input.realOccurrence_current_injective_at_fixedRoot acyclic c.occurrence previous
        (stateC.root.trans sameRootStart)
        (by rw [observed, pObserved, wEq]) cReal previousReal
    have lengthEq : c.occurrence.1.address.length = previous.1.address.length :=
      congrArg
        (fun occurrence : input.LocalizedCIPOccurrence carrierFuel =>
          occurrence.1.address.length)
        occurrenceEq
    by_cases sameStart : c = start
    · rw [sameStart] at lengthEq
      omega
    · have deeper := stateC.strictlyDeeper sameStart
      omega
  exact AcyclicCutBranchAutomorphism.cutBranch_adj_mem input.moleculeGraph
    xBranch adjacent wNeRoot

/-- **Forward direction: every real-reachable current atom lies in the parent-deleted physical
branch.**  The state invariant and the branch membership are proved together by induction over the
real child-list closure. -/
theorem realChildReachable_state_and_mem_cutBranch
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : start.previous? = some previous)
    (sameRootStart : start.occurrence.1.root = previous.1.root)
    (validStart : input.LocalizedRerootCursorValid start)
    (parentShorter : previous.1.address.length < start.occurrence.1.address.length)
    (startReal : start.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (previousReal : previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {oAtom pAtom : input.Atom}
    (oObserved : start.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (target : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen
      (fun left right : input.LocalizedRerootCursor carrierFuel =>
        E input left right ∧
          right.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
      start target) :
    input.RealCutReachableState start target ∧
      ∀ w, target.occurrence.1.node.current? = some w →
        w ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom := by
  induction reachable with
  | refl =>
      refine ⟨?_, ?_⟩
      · exact
          { valid := validStart
            root := rfl
            atLeast := le_rfl
            strictlyDeeper := by
              intro sameStart
              exact absurd rfl sameStart
            incomingRealShorter := ⟨previous, previousEq, previousReal, parentShorter⟩
            currentReal := startReal }
      · intro w observed
        have wEq : w = oAtom := Option.some.inj (observed.symm.trans oObserved)
        rw [wEq]
        exact AcyclicCutBranchAutomorphism.cutBranch_mem_self
          input.moleculeGraph incomingEdge
  | tail _path step ih =>
      obtain ⟨edge, childReal⟩ := step
      exact input.realCutReachableState_step acyclic enough start previous sameRootStart
        parentShorter previousReal pObserved _ _ ih.1 ih.2 edge childReal

/-- **Backward lifting along a simple physical chain on the real slice.**  Every adjacent chain of
fresh atoms is realized by real executable child steps.  The produced child is real by the reverse
direction of `localizedRerootChildren?_realChild_exists_iff_adjacent`; this is why the chain
hypotheses alone (without `SimpleBonded`) suffice, and why the reachability relation had to be
restricted to real children: the raw executable children also contain duplicate copies that the
real existential deliberately ignores. -/
theorem realChildReachable_of_simple_chain
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (rest : List input.Atom) :
    ∀ (cursor : input.LocalizedRerootCursor carrierFuel)
      (previous : input.LocalizedCIPOccurrence carrierFuel)
      (current z : input.Atom),
      cursor.previous? = some previous →
      cursor.occurrence.1.root = previous.1.root →
      cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom →
      previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom →
      cursor.occurrence.1.node.current? = some current →
      previous.1.node.current? = some z →
      (current :: rest).Nodup →
      (current :: rest).IsChain (fun a b => input.moleculeGraph.Adj a b) →
      z ∉ current :: rest →
      ∃ target : input.LocalizedRerootCursor carrierFuel,
        input.RealChildReachable cursor target ∧
          target.occurrence.1.node.current? = (current :: rest).getLast? := by
  induction rest with
  | nil =>
      intro cursor previous current z _previousEq _sameRoot _cursorReal _previousReal
        currentObserved _zObserved _nodup _chain _zAvoid
      exact ⟨cursor, Relation.ReflTransGen.refl, by simpa using currentObserved⟩
  | cons next tail inductionHypothesis =>
      intro cursor previous current z previousEq sameRoot cursorReal previousReal
        currentObserved zObserved nodup chain zAvoid
      have nodupTail : (next :: tail).Nodup := (List.nodup_cons.mp nodup).2
      have currentNotTail : current ∉ next :: tail := (List.nodup_cons.mp nodup).1
      have nextNeZ : next ≠ z := by
        intro nextEq
        exact zAvoid (by
          rw [nextEq]
          exact List.mem_cons_of_mem current List.mem_cons_self)
      have adjacent : input.moleculeGraph.Adj current next := chain.rel_head
      have localIff :=
        input.localizedRerootChildren?_realChild_exists_iff_adjacent (acyclic := acyclic)
          (enough := enough) (cursor := cursor) (previous := previous) previousEq sameRoot.symm
          (input.carrierOccurrence_realPath_of_provenance_real cursor.occurrence cursorReal)
          (input.carrierOccurrence_realPath_of_provenance_real previous previousReal)
          currentObserved zObserved (input.executableLocalizedRerootChildren cursor)
          (input.localizedRerootChildren?_eq_some_executable cursor)
      obtain ⟨child, childPresent, childReal, childCurrent⟩ :=
        (localIff next).mpr ⟨adjacent, nextNeZ⟩
      have childPrevious : child.previous? = some cursor.occurrence :=
        input.executableLocalizedRerootChildren_previous cursor child childPresent
      have childRoot : child.occurrence.1.root = cursor.occurrence.1.root :=
        input.localizedRerootChildren_root_eq cursor child
          (input.executableLocalizedRerootChildren cursor)
          (input.executableLocalizedRerootChildren_declarative cursor) childPresent
      obtain ⟨target, reachable, targetObserved⟩ :=
        inductionHypothesis child cursor.occurrence next current childPrevious childRoot
          childReal cursorReal childCurrent currentObserved nodupTail chain.tail currentNotTail
      refine ⟨target, ?_, ?_⟩
      · have single : input.RealChildReachable cursor child :=
          Relation.ReflTransGen.tail Relation.ReflTransGen.refl
            ⟨childPresent, childReal⟩
        exact single.trans reachable
      · rw [targetObserved]
        rfl

/-- **Restricted real-slice cut equivalence at arbitrary bond order.**  From a real source cursor
whose genuine incoming coordinate is also real and whose cut is a physical edge `pAtom - oAtom`,
an atom `w` is the current atom of some cursor reachable through real executable child steps (the
zero-step path included) if and only if `w` lies in the physical cut branch of `oAtom` after
deleting `pAtom`.

This is the real-position slice of the accepted single-bond
`actualChildReachable_current_iff_cutBranch`.  It deliberately does **not** claim blanket physical
fidelity: `localizedRerootChildren?_multipleBondCopy_survives` shows that the full child list also
contains multiple-bond duplicate copies whose current atom is the deleted incoming atom, so those
copies are outside this equivalence. -/
theorem realChildReachable_current_iff_cutBranch
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : start.previous? = some previous)
    (sameRootStart : start.occurrence.1.root = previous.1.root)
    (validStart : input.LocalizedRerootCursorValid start)
    (parentShorter : previous.1.address.length < start.occurrence.1.address.length)
    (startReal : input.RealPathNode start.occurrence.1.root start.occurrence.1.node)
    (previousReal : input.RealPathNode previous.1.root previous.1.node)
    {oAtom pAtom : input.Atom}
    (oObserved : start.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (w : input.Atom) :
    (∃ target : input.LocalizedRerootCursor carrierFuel,
      input.RealChildReachable start target ∧
        target.occurrence.1.node.current? = some w) ↔
      w ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom := by
  constructor
  · rintro ⟨target, reachable, observed⟩
    exact (input.realChildReachable_state_and_mem_cutBranch acyclic enough
      start previous previousEq sameRootStart validStart parentShorter
      (input.realPathNode_provenance startReal)
      (input.realPathNode_provenance previousReal)
      oObserved pObserved incomingEdge target reachable).2 w observed
  · intro branchMem
    obtain ⟨walk, avoids⟩ := branchMem
    let path : input.moleculeGraph.underlyingSimpleGraph.Path oAtom w := walk.toPath
    let simpleWalk : input.moleculeGraph.underlyingSimpleGraph.Walk oAtom w := path.1
    have simple : simpleWalk.IsPath := path.2
    have simpleAvoid : pAtom ∉ simpleWalk.support :=
      fun present => avoids (SimpleGraph.Walk.support_toPath_subset walk present)
    let rest := simpleWalk.support.tail
    have supportCons : simpleWalk.support = oAtom :: rest := by
      simpa [rest] using SimpleGraph.Walk.support_eq_cons simpleWalk
    have nodup : (oAtom :: rest).Nodup := by
      simpa [supportCons] using simple.support_nodup
    have chain : (oAtom :: rest).IsChain
        (fun a b => input.moleculeGraph.Adj a b) := by
      simpa [supportCons] using SimpleGraph.Walk.isChain_adj_support simpleWalk
    have avoidCons : pAtom ∉ oAtom :: rest := by
      simpa [supportCons] using simpleAvoid
    have lastEq : (oAtom :: rest).getLast? = some w := by
      rw [← supportCons]
      rw [List.getLast?_eq_getLast_of_ne_nil
        (SimpleGraph.Walk.support_ne_nil simpleWalk)]
      exact congrArg some (SimpleGraph.Walk.getLast_support simpleWalk)
    obtain ⟨target, reachable, targetObserved⟩ :=
      input.realChildReachable_of_simple_chain acyclic enough rest
        start previous oAtom pAtom previousEq sameRootStart
        (input.realPathNode_provenance startReal)
        (input.realPathNode_provenance previousReal)
        oObserved pObserved nodup chain avoidCons
    exact ⟨target, reachable, by rw [targetObserved, lastEq]⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realPathNode_child_of_mem_executableOfficialCIPChildren
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realPathNode_of_declarativeSubtree_real
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.carrierOccurrence_realPath_of_provenance_real
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realPathNode_history_nodup
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realCarrierOccurrence_address_length_le_atomCount
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.multipleBondRealCarrierOccurrence_remaining_pos
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realCarrierOccurrence_depth_eq_address_length
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realOccurrence_current_injective_at_fixedRoot
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realOccurrence_address_eq_of_current_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realChildFrame_of_adjacent_notParent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realChildFrame_slot_eq_copySlot
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realParentFrame_adjacent_and_current
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.intendedChildFrame_current_adjacent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootChildren?_realChild_exists_iff_adjacent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootChildren?_realChild_unique
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootChildren?_child_current_adjacent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootChildren?_multipleBondCopy_survives
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootChildren?_realChild_correspondence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.simpleOccurrencePath_address_eq_of_node_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootChildren?_realChild_exists_iff_adjacent_of_simplePaths
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RealChildReachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RealCutReachableState
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realCutReachableState_step
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realChildReachable_state_and_mem_cutBranch
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realChildReachable_of_simple_chain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realChildReachable_current_iff_cutBranch
