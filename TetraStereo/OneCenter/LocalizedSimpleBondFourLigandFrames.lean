import TetraStereo.OneCenter.LocalizedAcyclicFourLigandFrameCompleteness
import TetraStereo.OneCenter.LocalizedCarrierRealCenterActiveSimple
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fintype.Card
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# Four-ligand frames on cyclic single-bond inputs

`LocalizedAcyclicFourLigandFrameCompleteness` builds an actual four-ligand frame from
`localizedRerootChildren?` at `previous? = none`, then reads a detected-ligand permutation.
Its neighborhood bijection uses `MoleculeGraph.Acyclic` twice: fixed-root current-atom
injectivity, and the claim that a neighbor already on the history cannot occur.

On a cyclic graph those two moves come apart.

* A real carrier occurrence still has `OfficialCIPNode.ActiveSimple`: real provenance and a
  duplicate-free stored history. `declarativeLocalizedOccurrence_activeSimple_of_provenance_real`
  reads that from the carrier derivation. A simple path may sit inside a graph that also has
  cycles; `history.Nodup` remains the real-occurrence fact.
* A zero-copy step whose atom is already on that history is a terminal
  `OfficialCIPNodeProvenance.ringDuplicate`, with `current?` still equal to the duplicated atom.
  The immediate parent atom is already on the history, and the uncut frame represents it by the
  active-simple parent occurrence, not by a second ring-duplicate child.
* Sibling current atoms are separated by the raw executable copy `(next, 0)` and
  `physical_executableOfficialCIPChild_slot_unique`. The argument never calls
  `localizedCIPOccurrence_current_injective_at_fixedRoot`.

The retained hypotheses are a certified input, `MoleculeGraph.SimpleBonded`, carrier fuel at
least the atom count, the target carrier occurrence, and `RealTetrahedralCenterNode` (equivalently
`localizedOccurrenceDescriptorCenter? = some center`). `MoleculeGraph.Acyclic` is not a hypothesis.
The resulting `localizedOccurrenceFourLigandFrame?` success and the detected-ligand permutation
apply at every such occurrence, including a center reached along a carrier path that meets a ring.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

variable (input : CertifiedLocalizedCIPInput)

/-! ## Real histories stay duplicate-free, so fuel reaches the next child -/

/-- Every carrier occurrence, real or duplicate, stores one history atom per address step.
The relation is the official `extend` step from `OfficialCIPNode.root`. A ring-duplicate step
prepends the repeated atom and still lengthens the history by one. -/
theorem carrierOccurrence_history_length_eq_address_succ
    {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    occurrence.1.node.history.length = occurrence.1.address.length + 1 := by
  have derived :=
    (input.mem_localizedOccurrences_iff carrierFuel occurrence.1).mp occurrence.2
  have rooted := input.declarativeLocalizedOccurrence_as_rootSubtree derived
  exact input.declarativeLocalizedOccurrenceSubtree_history_length rooted
    (by simp [OfficialCIPNode.root])

/-- A real carrier occurrence at fuel at least the atom count has a positive remaining depth.
Duplicate-freedom of the real history bounds its length by the atom count, and the address is one
shorter than that history. The same bound is available on a cyclic graph: only the real
provenance is used. -/
theorem realCarrierOccurrence_remaining_pos
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (real : occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    0 < occurrence.1.remaining := by
  have active :=
    input.localizedCIPOccurrence_activeSimple_of_provenance_real occurrence real
  have historyLength :=
    input.carrierOccurrence_history_length_eq_address_succ occurrence
  have cardLe := active.2.length_le_card
  simp only [Fintype.card_fin] at cardLe
  have addressBound : occurrence.1.address.length + 1 ≤
      input.certified.input.molecule.atomCount := by
    rw [← historyLength]
    exact cardLe
  have grade := input.localizedCIPOccurrence_depthGrade occurrence
  omega

/-! ## Simple-bond child copies are exactly the zero-copies -/

/-- Under `SimpleBonded`, every raw executable child copy is the zero-copy of a positive edge,
and it is not the stored parent zero-copy. Positive copy indices are the multiple-bond branch;
bond order one removes them. -/
theorem simpleBond_childCopy_eq_zero
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (node : OfficialCIPNode input.Atom)
    {next : input.Atom} {copyIndex : Nat}
    (present : (next, copyIndex) ∈ input.executableOfficialChildCopies node) :
    copyIndex = 0 ∧
      (∃ current, node.current? = some current ∧ input.moleculeGraph.Adj current next) ∧
      node.parent? ≠ some next := by
  unfold executableOfficialChildCopies at present
  cases currentObserved : node.current? with
  | none =>
      simp [currentObserved] at present
  | some current =>
      cases parentObserved : node.parent? with
      | none =>
          have neighborPresent : (next, copyIndex) ∈
              input.executableOfficialNeighborCopies current := by
            simpa [currentObserved, parentObserved] using present
          obtain ⟨adjacent, bound⟩ :=
            (input.mem_executableOfficialNeighborCopies_iff current next copyIndex).mp
              neighborPresent
          have bondOne := singleBonded current next adjacent
          have copyZero : copyIndex = 0 := by
            rw [bondOne] at bound
            omega
          refine ⟨copyZero, ⟨current, rfl, adjacent⟩, ?_⟩
          intro parentEq
          cases parentEq
      | some parent =>
          have filtered : (next, copyIndex) ∈
              (input.executableOfficialNeighborCopies current).filter
                (fun copy => !(copy.1 == parent && copy.2 == 0)) := by
            simpa [currentObserved, parentObserved] using present
          rw [List.mem_filter] at filtered
          obtain ⟨neighborPresent, allowed⟩ := filtered
          obtain ⟨adjacent, bound⟩ :=
            (input.mem_executableOfficialNeighborCopies_iff current next copyIndex).mp
              neighborPresent
          have bondOne := singleBonded current next adjacent
          have copyZero : copyIndex = 0 := by
            rw [bondOne] at bound
            omega
          refine ⟨copyZero, ⟨current, rfl, adjacent⟩, ?_⟩
          intro parentEq
          have nextEq : next = parent := (Option.some.inj parentEq).symm
          have blocked : (next == parent && copyIndex == 0) = true := by
            simp [nextEq, copyZero]
          simp [blocked] at allowed

/-- A positive non-parent neighbor is the raw zero-copy child of a real node, and the carrier
stores that child at the raw-copy slot. The child may be a ring duplicate: `extend` records
`current? = some w` in either provenance. -/
theorem realCenter_outwardChildFrame_of_notParent
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {oAtom w : input.Atom}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (oObserved : target.1.node.current? = some oAtom)
    (adjacent : input.moleculeGraph.Adj oAtom w)
    (notParent : target.1.node.parent? ≠ some w)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    ∃ (childFrame : input.LocalizedCIPOccurrenceFrame) (slot : Nat),
      childFrame.address = target.1.address ++ [slot] ∧
      childFrame.root = target.1.root ∧
      childFrame.node.current? = some w ∧
      childFrame.node = target.1.node.extend w 0 ∧
      childFrame ∈ input.localizedOccurrences carrierFuel ∧
      childFrame ∈ input.localizedCarrierOutwardChildFrames
        (fuel := carrierFuel) target.1 := by
  have nonduplicate : target.1.node.isDuplicateLeaf = false :=
    input.isDuplicateLeaf_eq_false_of_provenance_real target.1.node real
  have copyPresent : (w, 0) ∈ input.executableOfficialChildCopies target.1.node :=
    input.mem_executableOfficialChildCopies_of_adjacent target.1.node oAtom w 0
      oObserved adjacent adjacent (Or.inr notParent)
  let slot := input.executableOfficialChildCopySlot target.1.node w 0
  have atSlot : (target.1.node.extend w 0, slot) ∈
      (input.executableOfficialCIPChildren target.1.node).zipIdx :=
    input.executableOfficialChildCopySlot_mem target.1.node w 0 nonduplicate copyPresent
  have positive := input.realCarrierOccurrence_remaining_pos enough target real
  let childFrame : input.LocalizedCIPOccurrenceFrame :=
    { root := target.1.root
      address := target.1.address ++ [slot]
      node := target.1.node.extend w 0
      remaining := target.1.remaining - 1 }
  have childDerived : input.DeclarativeLocalizedOccurrence carrierFuel childFrame :=
    DeclarativeLocalizedOccurrence.immediateChild input
      ((input.mem_localizedOccurrences_iff carrierFuel target.1).mp target.2)
      positive atSlot
  have childPresent : childFrame ∈ input.localizedOccurrences carrierFuel :=
    (input.mem_localizedOccurrences_iff carrierFuel childFrame).mpr childDerived
  have outwardPresent : childFrame ∈
      input.localizedCarrierOutwardChildFrames (fuel := carrierFuel) target.1 := by
    rw [localizedCarrierOutwardChildFrames, List.mem_filter]
    refine ⟨childPresent, ?_⟩
    simp [childFrame]
  exact ⟨childFrame, slot, rfl, rfl, by simp [childFrame], rfl, childPresent, outwardPresent⟩

/-- An outward carrier frame of a real node is the zero-copy `extend` of one non-parent neighbor.
`SimpleBonded` forces the raw copy index to be zero, so the frame's current atom determines the
copy. -/
theorem simpleBond_outwardFrame_extend_zero
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {carrierFuel : Nat}
    {oAtom : input.Atom}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (oObserved : target.1.node.current? = some oAtom)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (frame : input.LocalizedCIPOccurrenceFrame)
    (outward : frame ∈ input.localizedCarrierOutwardChildFrames
      (fuel := carrierFuel) target.1) :
    ∃ w slot,
      frame.node = target.1.node.extend w 0 ∧
      frame.node.current? = some w ∧
      frame.root = target.1.root ∧
      frame.address = target.1.address ++ [slot] ∧
      (target.1.node.extend w 0, slot) ∈
        (input.executableOfficialCIPChildren target.1.node).zipIdx ∧
      target.1.node.parent? ≠ some w ∧
      input.moleculeGraph.Adj oAtom w := by
  rw [localizedCarrierOutwardChildFrames, List.mem_filter] at outward
  obtain ⟨framePresent, raw⟩ := outward
  simp only [Bool.and_eq_true, beq_iff_eq] at raw
  obtain ⟨⟨rootEq, lengthEq⟩, dropEq⟩ := raw
  have nonempty : frame.address ≠ [] := by
    intro empty
    have zeroLength : frame.address.length = 0 := by simp [empty]
    omega
  let slot := frame.address.getLast nonempty
  have addressEq : frame.address = target.1.address ++ [slot] := by
    calc frame.address
        = frame.address.dropLast ++ [frame.address.getLast nonempty] :=
          (List.dropLast_append_getLast (l := frame.address) nonempty).symm
      _ = target.1.address ++ [slot] := by rw [dropEq]
  obtain ⟨childNode, childAtSlot, frameEq⟩ :=
    input.declarativeLocalizedOccurrence_immediate_child
      ((input.mem_localizedOccurrences_iff carrierFuel target.1).mp target.2)
      ((input.mem_localizedOccurrences_iff carrierFuel frame).mp framePresent)
      rootEq slot addressEq
  have nonduplicate : target.1.node.isDuplicateLeaf = false :=
    input.isDuplicateLeaf_eq_false_of_provenance_real target.1.node real
  have childrenEq : input.executableOfficialCIPChildren target.1.node =
      (input.executableOfficialChildCopies target.1.node).map
        (fun copy => target.1.node.extend copy.1 copy.2) := by
    rw [executableOfficialCIPChildren, if_neg (by simpa using nonduplicate)]
  have childAtMapped : (childNode, slot) ∈
      ((input.executableOfficialChildCopies target.1.node).map
        (fun copy => target.1.node.extend copy.1 copy.2)).zipIdx := by
    simpa [childrenEq] using childAtSlot
  have indexed := List.mk_mem_zipIdx_iff_getElem?.mp childAtMapped
  rw [List.getElem?_map] at indexed
  cases copyObserved :
      (input.executableOfficialChildCopies target.1.node)[slot]? with
  | none =>
      simp [copyObserved] at indexed
  | some copy =>
      simp [copyObserved] at indexed
      have copyPresent := List.mem_of_getElem? copyObserved
      rcases copy with ⟨next, copyIndex⟩
      have nodeIdentity : childNode = target.1.node.extend next copyIndex := by
        simpa using indexed.symm
      obtain ⟨copyZero, ⟨current, currentEq, adjacent⟩, notParent⟩ :=
        input.simpleBond_childCopy_eq_zero singleBonded target.1.node copyPresent
      have currentMatch : current = oAtom :=
        Option.some.inj (currentEq.symm.trans oObserved)
      subst copyZero
      subst currentMatch
      refine ⟨next, slot, ?_, ?_, rootEq, addressEq, ?_, notParent, adjacent⟩
      · simp [frameEq, nodeIdentity]
      · simp [frameEq, nodeIdentity, OfficialCIPNode.extend_current?]
      · simpa [nodeIdentity] using childAtSlot

/-- The stored parent of a non-root real occurrence is an active-simple carrier neighbor.
Its current atom lies on the target history and is the target's `parent?`. The uncut zipper
represents that atom by this parent frame. -/
theorem realCenter_parent_current
    {carrierFuel : Nat}
    {oAtom : input.Atom}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (oObserved : target.1.node.current? = some oAtom)
    (nonroot : target.1.address ≠ []) :
    ∃ (certificate : input.LocalizedParentFrameHistory target) (parentAtom : input.Atom),
      certificate.parent.1.node.current? = some parentAtom ∧
      target.1.node.parent? = some parentAtom ∧
      parentAtom ∈ target.1.node.history ∧
      input.moleculeGraph.Adj oAtom parentAtom ∧
      certificate.parent.1.node.ActiveSimple ∧
      certificate.parent.1 ∈ input.localizedRerootNeighborFrames
        (fuel := carrierFuel) target.1 := by
  obtain ⟨certificate⟩ := input.exists_localizedParentFrameHistory target nonroot
  obtain ⟨current, parentAtom, _tail, currentEq, parentCurrentEq, historyEq, _parentHistory⟩ :=
    certificate.history_shape input
  have currentMatch : current = oAtom :=
    Option.some.inj (currentEq.symm.trans oObserved)
  subst currentMatch
  have parentObserved : target.1.node.parent? = some parentAtom := by
    simp [OfficialCIPNode.parent?, historyEq]
  have visited : parentAtom ∈ target.1.node.history := by
    simp [historyEq]
  obtain ⟨parentCurrent, parentFrameCurrent, adjacent⟩ :=
    input.parentFrame_current_adjacent oObserved nonroot certificate
  have parentMatch : parentAtom = parentCurrent :=
    Option.some.inj (parentCurrentEq.symm.trans parentFrameCurrent)
  subst parentMatch
  exact ⟨certificate, parentAtom, parentCurrentEq, parentObserved, visited, adjacent,
    certificate.parent_active, certificate.parent_mem_neighborFrames input⟩

/-- At a real node the uncut reroot expansion is exactly the carrier neighborhood, and every
emitted cursor records the target as its incoming coordinate. -/
theorem simpleBond_realCenter_childFrames
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (children : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRerootChildren?
      ({ occurrence := target, previous? := none } :
        input.LocalizedRerootCursor carrierFuel) = some children) :
    children.map (fun child => child.occurrence.1) =
        input.localizedRerootNeighborFrames (fuel := carrierFuel) target.1 ∧
      ∀ child ∈ children, child.previous? = some target := by
  have derived := input.localizedRerootChildren?_sound
    ({ occurrence := target, previous? := none } :
      input.LocalizedRerootCursor carrierFuel) children computed
  have notDuplicate :=
    input.isDuplicateLeaf_eq_false_of_provenance_real target.1.node real
  refine ⟨?_, derived.2⟩
  have mapped := derived.1
  unfold intendedLocalizedRerootChildFrames at mapped
  rw [if_neg (by simpa using notDuplicate)] at mapped
  simpa using mapped

/-! ## Immediate children and neighbor atoms -/

/-- Every atom carried by an uncut child of a real center is a physical neighbor, and every
physical neighbor is carried by some uncut child. The parent atom is included. A neighbor already
on the history is included as well. -/
theorem simpleBond_realCenter_rerootChildren_current_iff_adjacent
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (meaning : input.RealTetrahedralCenterNode target.1.node center)
    (children : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRerootChildren?
      ({ occurrence := target, previous? := none } :
        input.LocalizedRerootCursor carrierFuel) = some children) :
    ∀ w, (∃ child ∈ children, child.occurrence.1.node.current? = some w) ↔
      input.moleculeGraph.Adj center.1 w := by
  have oObserved : target.1.node.current? = some center.1 := meaning.2
  have real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom := meaning.1
  have frames := input.simpleBond_realCenter_childFrames target real children computed
  intro w
  constructor
  · rintro ⟨child, childPresent, childCurrent⟩
    have framePresent : child.occurrence.1 ∈
        input.localizedRerootNeighborFrames (fuel := carrierFuel) target.1 := by
      rw [← frames.1]
      exact List.mem_map.mpr ⟨child, childPresent, rfl⟩
    rw [localizedRerootNeighborFrames, List.mem_append] at framePresent
    rcases framePresent with parentPresent | outwardPresent
    · have nonroot : target.1.address ≠ [] := by
        rw [localizedCarrierParentFrames, List.mem_filter] at parentPresent
        obtain ⟨_, raw⟩ := parentPresent
        simp only [Bool.and_eq_true, beq_iff_eq] at raw
        obtain ⟨⟨_, lengthEq⟩, _⟩ := raw
        intro empty
        rw [empty] at lengthEq
        simp at lengthEq
      obtain ⟨certificate, parentAtom, parentCurrent, _parentObserved, _visited, adjacent,
          _active, _member⟩ :=
        input.realCenter_parent_current target oObserved nonroot
      have singleton := certificate.carrierParentFrames_eq_singleton input
      have frameEq : child.occurrence.1 = certificate.parent.1 := by
        have member : child.occurrence.1 ∈ [certificate.parent.1] := by
          simpa [singleton] using parentPresent
        simpa using member
      have onParent : certificate.parent.1.node.current? = some w := by
        simpa [frameEq] using childCurrent
      have wEq : w = parentAtom :=
        Option.some.inj (onParent.symm.trans parentCurrent)
      simpa [wEq] using adjacent
    · obtain ⟨next, _slot, _nodeEq, currentEq, _rootEq, _addressEq, _atSlot, _notParent,
          adjacent⟩ :=
        input.simpleBond_outwardFrame_extend_zero singleBonded target oObserved real
          child.occurrence.1 outwardPresent
      have onChild : child.occurrence.1.node.current? = some next := currentEq
      have wEq : w = next := Option.some.inj (childCurrent.symm.trans onChild)
      simpa [wEq] using adjacent
  · intro adjacent
    by_cases parentCase : target.1.node.parent? = some w
    · have nonroot : target.1.address ≠ [] := by
        intro empty
        have targetDerived :=
          (input.mem_localizedOccurrences_iff carrierFuel target.1).mp target.2
        have rootShape :=
          input.declarativeLocalizedOccurrence_eq_root_of_address_nil targetDerived empty
        have parentNone : target.1.node.parent? = none := by
          rw [rootShape]
          simp [OfficialCIPNode.root, OfficialCIPNode.parent?]
        rw [parentNone] at parentCase
        simp at parentCase
      obtain ⟨certificate, parentAtom, parentCurrent, parentObserved, _visited, _adjacent,
          _active, parentNeighbor⟩ :=
        input.realCenter_parent_current target oObserved nonroot
      have parentEq : parentAtom = w := by
        have same : some parentAtom = some w := parentObserved.symm.trans parentCase
        exact Option.some.inj same
      have member : certificate.parent.1 ∈
          children.map (fun child => child.occurrence.1) := by
        rw [frames.1]
        simpa [parentEq] using parentNeighbor
      rw [List.mem_map] at member
      obtain ⟨child, childPresent, frameEq⟩ := member
      refine ⟨child, childPresent, ?_⟩
      simpa [frameEq, parentEq] using parentCurrent
    · obtain ⟨childFrame, _slot, _addressEq, _rootEq, frameCurrent, _nodeEq, _present,
          outwardPresent⟩ :=
        input.realCenter_outwardChildFrame_of_notParent enough target oObserved adjacent
          parentCase real
      have neighborPresent : childFrame ∈
          input.localizedRerootNeighborFrames (fuel := carrierFuel) target.1 :=
        List.mem_append_right _ outwardPresent
      have member : childFrame ∈ children.map (fun child => child.occurrence.1) := by
        rw [frames.1]
        exact neighborPresent
      rw [List.mem_map] at member
      obtain ⟨child, childPresent, frameEq⟩ := member
      exact ⟨child, childPresent, by simpa [frameEq] using frameCurrent⟩

/-- Sibling cursors of one real center have distinct current atoms. Equal current atoms determine
the same raw zero-copy, hence the same carrier address. A ring-duplicate child may repeat an
ancestor atom; it does not repeat a sibling. The parent atom occurs once, as the parent frame. -/
theorem simpleBond_realCenter_rerootChildren_current_injective
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (meaning : input.RealTetrahedralCenterNode target.1.node center)
    (children : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRerootChildren?
      ({ occurrence := target, previous? := none } :
        input.LocalizedRerootCursor carrierFuel) = some children) :
    ∀ left ∈ children, ∀ right ∈ children,
      left.occurrence.1.node.current? = right.occurrence.1.node.current? →
        left = right := by
  have oObserved : target.1.node.current? = some center.1 := meaning.2
  have real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom := meaning.1
  have frames := input.simpleBond_realCenter_childFrames target real children computed
  intro left leftPresent right rightPresent sameCurrent
  have leftFrame : left.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel) target.1 := by
    rw [← frames.1]
    exact List.mem_map.mpr ⟨left, leftPresent, rfl⟩
  have rightFrame : right.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel) target.1 := by
    rw [← frames.1]
    exact List.mem_map.mpr ⟨right, rightPresent, rfl⟩
  have previousEq : left.previous? = right.previous? :=
    (frames.2 left leftPresent).trans (frames.2 right rightPresent).symm
  rw [localizedRerootNeighborFrames, List.mem_append] at leftFrame rightFrame
  rcases leftFrame with leftParent | leftOutward
  · rcases rightFrame with rightParent | rightOutward
    · have nonroot : target.1.address ≠ [] := by
        rw [localizedCarrierParentFrames, List.mem_filter] at leftParent
        obtain ⟨_, raw⟩ := leftParent
        simp only [Bool.and_eq_true, beq_iff_eq] at raw
        obtain ⟨⟨_, lengthEq⟩, _⟩ := raw
        intro empty
        rw [empty] at lengthEq
        simp at lengthEq
      obtain ⟨certificate, _parentAtom, _parentCurrent, _parentObserved, _visited, _adjacent,
          _active, _member⟩ :=
        input.realCenter_parent_current target oObserved nonroot
      have singleton := certificate.carrierParentFrames_eq_singleton input
      have leftEq : left.occurrence.1 = certificate.parent.1 := by
        have member : left.occurrence.1 ∈ [certificate.parent.1] := by
          simpa [singleton] using leftParent
        simpa using member
      have rightEq : right.occurrence.1 = certificate.parent.1 := by
        have member : right.occurrence.1 ∈ [certificate.parent.1] := by
          simpa [singleton] using rightParent
        simpa using member
      have occurrenceEq : left.occurrence = right.occurrence :=
        Subtype.ext (leftEq.trans rightEq.symm)
      exact LocalizedRerootCursor.ext input occurrenceEq previousEq
    · obtain ⟨w, leftCurrent⟩ := input.localizedRerootCursor_current_exists left
      have rightCurrent : right.occurrence.1.node.current? = some w := by
        rw [← sameCurrent, leftCurrent]
      have nonroot : target.1.address ≠ [] := by
        rw [localizedCarrierParentFrames, List.mem_filter] at leftParent
        obtain ⟨_, raw⟩ := leftParent
        simp only [Bool.and_eq_true, beq_iff_eq] at raw
        obtain ⟨⟨_, lengthEq⟩, _⟩ := raw
        intro empty
        rw [empty] at lengthEq
        simp at lengthEq
      obtain ⟨certificate, parentAtom, parentCurrent, parentObserved, _visited, _adjacent,
          _active, _member⟩ :=
        input.realCenter_parent_current target oObserved nonroot
      have singleton := certificate.carrierParentFrames_eq_singleton input
      have leftEq : left.occurrence.1 = certificate.parent.1 := by
        have member : left.occurrence.1 ∈ [certificate.parent.1] := by
          simpa [singleton] using leftParent
        simpa using member
      have leftOnParent : certificate.parent.1.node.current? = some w := by
        simpa [leftEq] using leftCurrent
      have wEq : w = parentAtom :=
        Option.some.inj (leftOnParent.symm.trans parentCurrent)
      obtain ⟨next, _slot, _nodeEq, currentEq, _rootEq, _addressEq, _atSlot, notParent,
          _adjacent⟩ :=
        input.simpleBond_outwardFrame_extend_zero singleBonded target oObserved real
          right.occurrence.1 rightOutward
      have nextEq : next = w := Option.some.inj (currentEq.symm.trans rightCurrent)
      have parentSome : target.1.node.parent? = some next := by
        simpa [wEq, nextEq] using parentObserved
      exact absurd parentSome notParent
  · rcases rightFrame with rightParent | rightOutward
    · obtain ⟨w, rightCurrent⟩ := input.localizedRerootCursor_current_exists right
      have leftCurrent : left.occurrence.1.node.current? = some w := by
        rw [sameCurrent, rightCurrent]
      have nonroot : target.1.address ≠ [] := by
        rw [localizedCarrierParentFrames, List.mem_filter] at rightParent
        obtain ⟨_, raw⟩ := rightParent
        simp only [Bool.and_eq_true, beq_iff_eq] at raw
        obtain ⟨⟨_, lengthEq⟩, _⟩ := raw
        intro empty
        rw [empty] at lengthEq
        simp at lengthEq
      obtain ⟨certificate, parentAtom, parentCurrent, parentObserved, _visited, _adjacent,
          _active, _member⟩ :=
        input.realCenter_parent_current target oObserved nonroot
      have singleton := certificate.carrierParentFrames_eq_singleton input
      have rightEq : right.occurrence.1 = certificate.parent.1 := by
        have member : right.occurrence.1 ∈ [certificate.parent.1] := by
          simpa [singleton] using rightParent
        simpa using member
      have rightOnParent : certificate.parent.1.node.current? = some w := by
        simpa [rightEq] using rightCurrent
      have wEq : w = parentAtom :=
        Option.some.inj (rightOnParent.symm.trans parentCurrent)
      obtain ⟨next, _slot, _nodeEq, currentEq, _rootEq, _addressEq, _atSlot, notParent,
          _adjacent⟩ :=
        input.simpleBond_outwardFrame_extend_zero singleBonded target oObserved real
          left.occurrence.1 leftOutward
      have nextEq : next = w := Option.some.inj (currentEq.symm.trans leftCurrent)
      have parentSome : target.1.node.parent? = some next := by
        simpa [wEq, nextEq] using parentObserved
      exact absurd parentSome notParent
    · obtain ⟨leftAtom, leftSlot, leftNodeEq, leftCurrentEq, leftRootEq, leftAddressEq,
          leftAtSlot, _leftNotParent, _leftAdjacent⟩ :=
        input.simpleBond_outwardFrame_extend_zero singleBonded target oObserved real
          left.occurrence.1 leftOutward
      obtain ⟨rightAtom, rightSlot, rightNodeEq, rightCurrentEq, rightRootEq, rightAddressEq,
          rightAtSlot, _rightNotParent, _rightAdjacent⟩ :=
        input.simpleBond_outwardFrame_extend_zero singleBonded target oObserved real
          right.occurrence.1 rightOutward
      have atomEq : leftAtom = rightAtom := by
        have leftSome : left.occurrence.1.node.current? = some leftAtom := leftCurrentEq
        have rightSome : right.occurrence.1.node.current? = some rightAtom := rightCurrentEq
        exact Option.some.inj (leftSome.symm.trans (sameCurrent.trans rightSome))
      subst atomEq
      have physical : (target.1.node.extend leftAtom 0).provenance =
            OfficialCIPNodeProvenance.realAtom ∨
          ∃ distance, (target.1.node.extend leftAtom 0).provenance =
            OfficialCIPNodeProvenance.ringDuplicate distance := by
        rw [OfficialCIPNode.extend_provenance]
        by_cases visited : leftAtom ∈ target.1.node.history
        · exact Or.inr ⟨target.1.node.duplicateRootDistance leftAtom,
            OfficialCIPNode.childProvenance_ring_duplicate target.1.node leftAtom visited⟩
        · exact Or.inl
            (OfficialCIPNode.childProvenance_real target.1.node leftAtom visited)
      have slotEq := input.physical_executableOfficialCIPChild_slot_unique
        target.1.node (target.1.node.extend leftAtom 0) leftSlot rightSlot
        leftAtSlot rightAtSlot physical
      have addressEq : left.occurrence.1.address = right.occurrence.1.address := by
        rw [leftAddressEq, rightAddressEq, slotEq]
      have rootEq : left.occurrence.1.root = right.occurrence.1.root :=
        leftRootEq.trans rightRootEq.symm
      have frameEq := input.declarativeLocalizedOccurrence_functional_at_root_address
        ((input.mem_localizedOccurrences_iff carrierFuel left.occurrence.1).mp
          left.occurrence.2)
        ((input.mem_localizedOccurrences_iff carrierFuel right.occurrence.1).mp
          right.occurrence.2)
        rootEq addressEq
      exact LocalizedRerootCursor.ext input (Subtype.ext frameEq) previousEq

/-- **Immediate actual children biject with the physical neighbors.**  The uncut expansion at a
real detected center is in explicit bijection with `Neighbor center.1`, reading each child's
`current?`. The parent atom is one neighbor, carried by the parent frame. Every other neighbor,
including an atom already on the history, is carried by its zero-copy outward child. -/
theorem simpleBond_realCenter_rerootChildren_neighborEquiv
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (meaning : input.RealTetrahedralCenterNode target.1.node center) :
    ∃ (children : List (input.LocalizedRerootCursor carrierFuel))
      (ligand : {child // child ∈ children} ≃ input.moleculeGraph.Neighbor center.1),
      input.localizedRerootChildren?
        ({ occurrence := target, previous? := none } :
          input.LocalizedRerootCursor carrierFuel) = some children ∧
        (∀ child, child.1.occurrence.1.node.current? = some (ligand child).1) := by
  classical
  let rootCursor : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := target, previous? := none }
  obtain ⟨children, computed⟩ := input.exists_localizedRerootChildren rootCursor
  have correspondence :=
    input.simpleBond_realCenter_rerootChildren_current_iff_adjacent singleBonded enough
      target center meaning children computed
  have injective :=
    input.simpleBond_realCenter_rerootChildren_current_injective singleBonded target center
      meaning children computed
  let atomOf : {child // child ∈ children} → input.Atom :=
    fun child => Classical.choose (input.localizedRerootCursor_current_exists child.1)
  have atomOf_spec : ∀ child : {child // child ∈ children},
      child.1.occurrence.1.node.current? = some (atomOf child) :=
    fun child => Classical.choose_spec (input.localizedRerootCursor_current_exists child.1)
  have adjOf : ∀ child : {child // child ∈ children},
      input.moleculeGraph.Adj center.1 (atomOf child) :=
    fun child => (correspondence (atomOf child)).mp ⟨child.1, child.2, atomOf_spec child⟩
  let toNeighbor : {child // child ∈ children} → input.moleculeGraph.Neighbor center.1 :=
    fun child => ⟨atomOf child, adjOf child⟩
  have toNeighbor_injective : Function.Injective toNeighbor := by
    intro left right equal
    have sameAtom : atomOf left = atomOf right := congrArg Subtype.val equal
    have sameCurrent : left.1.occurrence.1.node.current? =
        right.1.occurrence.1.node.current? := by
      rw [atomOf_spec left, atomOf_spec right, sameAtom]
    exact Subtype.ext (injective left.1 left.2 right.1 right.2 sameCurrent)
  have toNeighbor_surjective : Function.Surjective toNeighbor := by
    intro neighbor
    obtain ⟨child, present, current⟩ := (correspondence neighbor.1).mpr neighbor.2
    refine ⟨⟨child, present⟩, ?_⟩
    apply Subtype.ext
    exact Option.some.inj ((atomOf_spec ⟨child, present⟩).symm.trans current)
  exact ⟨children, Equiv.ofBijective toNeighbor ⟨toNeighbor_injective, toNeighbor_surjective⟩,
    computed, fun child => atomOf_spec child⟩

/-- Each uncut child is either the active-simple parent frame or one outward zero-copy.
An outward atom already on the history is a terminal ring duplicate. An outward fresh atom is
`realAtom`. `SimpleBonded` excludes a multiple-bond copy. -/
theorem simpleBond_realCenter_immediateChild_classified
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (meaning : input.RealTetrahedralCenterNode target.1.node center)
    (children : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRerootChildren?
      ({ occurrence := target, previous? := none } :
        input.LocalizedRerootCursor carrierFuel) = some children)
    (child : input.LocalizedRerootCursor carrierFuel)
    (present : child ∈ children) :
    ∃ w, child.occurrence.1.node.current? = some w ∧
      input.moleculeGraph.Adj center.1 w ∧
      ((∃ certificate : input.LocalizedParentFrameHistory target,
          child.occurrence = certificate.parent ∧
          certificate.parent.1.node.ActiveSimple ∧
          target.1.node.parent? = some w ∧
          w ∈ target.1.node.history) ∨
        (child.occurrence.1.node = target.1.node.extend w 0 ∧
          target.1.node.parent? ≠ some w ∧
          (w ∈ target.1.node.history →
            child.occurrence.1.node.provenance =
              OfficialCIPNodeProvenance.ringDuplicate
                (target.1.node.duplicateRootDistance w) ∧
            child.occurrence.1.node.isDuplicateLeaf = true ∧
            input.executableOfficialCIPChildren child.occurrence.1.node = []) ∧
          (w ∉ target.1.node.history →
            child.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom))) := by
  have oObserved : target.1.node.current? = some center.1 := meaning.2
  have real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom := meaning.1
  have frames := input.simpleBond_realCenter_childFrames target real children computed
  have framePresent : child.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel) target.1 := by
    rw [← frames.1]
    exact List.mem_map.mpr ⟨child, present, rfl⟩
  rw [localizedRerootNeighborFrames, List.mem_append] at framePresent
  rcases framePresent with parentPresent | outwardPresent
  · have nonroot : target.1.address ≠ [] := by
      rw [localizedCarrierParentFrames, List.mem_filter] at parentPresent
      obtain ⟨_, raw⟩ := parentPresent
      simp only [Bool.and_eq_true, beq_iff_eq] at raw
      obtain ⟨⟨_, lengthEq⟩, _⟩ := raw
      intro empty
      rw [empty] at lengthEq
      simp at lengthEq
    obtain ⟨certificate, parentAtom, parentCurrent, parentObserved, visited, adjacent, active,
        _member⟩ :=
      input.realCenter_parent_current target oObserved nonroot
    have singleton := certificate.carrierParentFrames_eq_singleton input
    have frameEq : child.occurrence.1 = certificate.parent.1 := by
      have member : child.occurrence.1 ∈ [certificate.parent.1] := by
        simpa [singleton] using parentPresent
      simpa using member
    have occurrenceEq : child.occurrence = certificate.parent := Subtype.ext frameEq
    refine ⟨parentAtom, ?_, adjacent, Or.inl ?_⟩
    · simpa [frameEq] using parentCurrent
    · exact ⟨certificate, occurrenceEq, active, parentObserved, visited⟩
  · obtain ⟨w, _slot, nodeEq, currentEq, _rootEq, _addressEq, _atSlot, notParent, adjacent⟩ :=
      input.simpleBond_outwardFrame_extend_zero singleBonded target oObserved real
        child.occurrence.1 outwardPresent
    refine ⟨w, currentEq, adjacent, Or.inr ⟨nodeEq, notParent, ?_, ?_⟩⟩
    · intro visited
      have provenance : child.occurrence.1.node.provenance =
          OfficialCIPNodeProvenance.ringDuplicate
            (target.1.node.duplicateRootDistance w) := by
        rw [nodeEq]
        exact input.legitimateOccurrence_ring_provenance visited
      have leaf : child.occurrence.1.node.isDuplicateLeaf = true := by
        rw [OfficialCIPNode.isDuplicateLeaf, provenance]
        rfl
      have terminal : input.executableOfficialCIPChildren child.occurrence.1.node = [] := by
        simp [executableOfficialCIPChildren, leaf]
      exact ⟨provenance, leaf, terminal⟩
    · intro fresh
      rw [nodeEq, OfficialCIPNode.extend_provenance]
      exact OfficialCIPNode.childProvenance_real target.1.node w fresh

/-- On a non-root real center, the parent atom is carried by exactly one uncut child: the
active-simple parent occurrence. That child keeps real provenance and a duplicate-free history.
The expansion does not also emit a ring-duplicate child for the same parent atom. -/
theorem simpleBond_realCenter_parent_handled
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (meaning : input.RealTetrahedralCenterNode target.1.node center)
    (nonroot : target.1.address ≠ []) :
    ∃ (children : List (input.LocalizedRerootCursor carrierFuel))
      (child : input.LocalizedRerootCursor carrierFuel)
      (parentAtom : input.Atom)
      (certificate : input.LocalizedParentFrameHistory target),
      input.localizedRerootChildren?
        ({ occurrence := target, previous? := none } :
          input.LocalizedRerootCursor carrierFuel) = some children ∧
      child ∈ children ∧
      child.occurrence = certificate.parent ∧
      child.occurrence.1.node.current? = some parentAtom ∧
      target.1.node.parent? = some parentAtom ∧
      parentAtom ∈ target.1.node.history ∧
      input.moleculeGraph.Adj center.1 parentAtom ∧
      certificate.parent.1.node.ActiveSimple ∧
      (∀ other ∈ children, other.occurrence.1.node.current? = some parentAtom →
        other = child) := by
  have oObserved : target.1.node.current? = some center.1 := meaning.2
  have real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom := meaning.1
  let rootCursor : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := target, previous? := none }
  obtain ⟨children, computed⟩ := input.exists_localizedRerootChildren rootCursor
  have frames := input.simpleBond_realCenter_childFrames target real children computed
  obtain ⟨certificate, parentAtom, parentCurrent, parentObserved, visited, adjacent, active,
      parentNeighbor⟩ :=
    input.realCenter_parent_current target oObserved nonroot
  have member : certificate.parent.1 ∈ children.map (fun child => child.occurrence.1) := by
    rw [frames.1]
    exact parentNeighbor
  rw [List.mem_map] at member
  obtain ⟨child, childPresent, frameEq⟩ := member
  have occurrenceEq : child.occurrence = certificate.parent := Subtype.ext frameEq
  have injective :=
    input.simpleBond_realCenter_rerootChildren_current_injective singleBonded target center
      meaning children computed
  refine ⟨children, child, parentAtom, certificate, computed, childPresent, occurrenceEq, ?_,
    parentObserved, visited, adjacent, active, ?_⟩
  · simpa [frameEq] using parentCurrent
  · intro other otherPresent otherCurrent
    have childCurrent : child.occurrence.1.node.current? = some parentAtom := by
      simpa [frameEq] using parentCurrent
    exact injective other otherPresent child childPresent (otherCurrent.trans childCurrent.symm)

/-- A neighbor that already lies on the real history, and is not the stored parent, is emitted as
a terminal ring-duplicate child. `current?` remains that atom, and the executable child list of
the duplicate is empty. -/
theorem simpleBond_realCenter_visitedNeighbor_terminalRingDuplicate
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (meaning : input.RealTetrahedralCenterNode target.1.node center)
    {w : input.Atom}
    (adjacent : input.moleculeGraph.Adj center.1 w)
    (visited : w ∈ target.1.node.history)
    (notParent : target.1.node.parent? ≠ some w) :
    ∃ (children : List (input.LocalizedRerootCursor carrierFuel))
      (child : input.LocalizedRerootCursor carrierFuel),
      input.localizedRerootChildren?
        ({ occurrence := target, previous? := none } :
          input.LocalizedRerootCursor carrierFuel) = some children ∧
      child ∈ children ∧
      child.occurrence.1.node.current? = some w ∧
      child.occurrence.1.node = target.1.node.extend w 0 ∧
      child.occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.ringDuplicate (target.1.node.duplicateRootDistance w) ∧
      child.occurrence.1.node.isDuplicateLeaf = true ∧
      input.executableOfficialCIPChildren child.occurrence.1.node = [] := by
  have oObserved : target.1.node.current? = some center.1 := meaning.2
  have real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom := meaning.1
  let rootCursor : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := target, previous? := none }
  obtain ⟨children, computed⟩ := input.exists_localizedRerootChildren rootCursor
  have frames := input.simpleBond_realCenter_childFrames target real children computed
  obtain ⟨childFrame, _slot, _addressEq, _rootEq, _frameCurrent, nodeEq, _carrier, outward⟩ :=
    input.realCenter_outwardChildFrame_of_notParent enough target oObserved adjacent
      notParent real
  have neighborPresent : childFrame ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel) target.1 :=
    List.mem_append_right _ outward
  have member : childFrame ∈ children.map (fun child => child.occurrence.1) := by
    rw [frames.1]
    exact neighborPresent
  rw [List.mem_map] at member
  obtain ⟨child, childPresent, frameEq⟩ := member
  have nodeOnChild : child.occurrence.1.node = target.1.node.extend w 0 := by
    simpa [frameEq] using nodeEq
  have provenance : child.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.ringDuplicate (target.1.node.duplicateRootDistance w) := by
    rw [nodeOnChild]
    exact input.legitimateOccurrence_ring_provenance visited
  have leaf : child.occurrence.1.node.isDuplicateLeaf = true := by
    rw [OfficialCIPNode.isDuplicateLeaf, provenance]
    rfl
  have terminal : input.executableOfficialCIPChildren child.occurrence.1.node = [] := by
    simp [executableOfficialCIPChildren, leaf]
  refine ⟨children, child, computed, childPresent, ?_, nodeOnChild, provenance, leaf, terminal⟩
  · simp [nodeOnChild, OfficialCIPNode.extend_current?]

/-- The uncut child count equals the physical degree. The count is the cardinality of the
neighbor bijection. -/
theorem simpleBond_realCenter_rerootChildren_length_eq_neighbor_card
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (meaning : input.RealTetrahedralCenterNode target.1.node center)
    (children : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRerootChildren?
      ({ occurrence := target, previous? := none } :
        input.LocalizedRerootCursor carrierFuel) = some children) :
    children.length = Fintype.card (input.moleculeGraph.Neighbor center.1) := by
  classical
  obtain ⟨built, ligand, builtComputed, _spec⟩ :=
    input.simpleBond_realCenter_rerootChildren_neighborEquiv singleBonded enough target center
      meaning
  have childrenEq : children = built :=
    Option.some.inj (computed.symm.trans builtComputed)
  rw [childrenEq]
  have sound := input.localizedRerootChildren?_sound
    ({ occurrence := target, previous? := none } :
      input.LocalizedRerootCursor carrierFuel) built builtComputed
  have nodup := input.localizedRerootChildren_nodup
    ({ occurrence := target, previous? := none } :
      input.LocalizedRerootCursor carrierFuel) built sound
  have cardEq := Fintype.card_congr ((List.Nodup.getEquiv built nodup).trans ligand)
  simpa [Fintype.card_fin] using cardEq

/-! ## Actual four-ligand frame and detected ligand permutation -/

/-- **Actual four-ligand frame at every real detected center.**  For a certified single-bond
input, at any carrier fuel at least the atom count, an occurrence recognized as a real tetrahedral
center has

`input.localizedOccurrenceFourLigandFrame? target = some frame`,

and the four slots are bijective with the physical neighbors through each cursor's `current?`.
The occurrence may lie at any carrier address, including an address whose history meets a ring. -/
theorem exists_simpleBond_localizedOccurrenceFourLigandFrame_and_neighborEquiv
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (meaning : input.RealTetrahedralCenterNode target.1.node center) :
    ∃ (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
      (ligand : Fin 4 ≃ input.moleculeGraph.Neighbor center.1),
      input.localizedOccurrenceFourLigandFrame? target = some frame ∧
        (∀ i, (frame.cursorAt i).occurrence.1.node.current? = some (ligand i).1) := by
  classical
  let rootCursor : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := target, previous? := none }
  obtain ⟨children, ligandSub, computed, ligandSub_spec⟩ :=
    input.simpleBond_realCenter_rerootChildren_neighborEquiv singleBonded enough target center
      meaning
  have sound := input.localizedRerootChildren?_sound rootCursor children computed
  have nodup := input.localizedRerootChildren_nodup rootCursor children sound
  have lengthEq : children.length = 4 := by
    have degree := input.simpleBond_realCenter_rerootChildren_length_eq_neighbor_card
      singleBonded enough target center meaning children computed
    have tetrahedral : input.moleculeGraph.IsTetrahedralCenter center.1 :=
      (input.moleculeGraph.mem_tetrahedralCenterSet center.1).mp center.2
    rw [degree]
    exact tetrahedral
  let frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel :=
    { cursors := children, length_eq := lengthEq }
  have frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame := by
    rw [input.localizedOccurrenceFourLigandFrame?_eq_some_iff]
    exact ⟨sound, lengthEq⟩
  let indexEquiv : Fin 4 ≃ {child // child ∈ children} :=
    (finCongr lengthEq.symm).trans (List.Nodup.getEquiv children nodup)
  let ligand : Fin 4 ≃ input.moleculeGraph.Neighbor center.1 := indexEquiv.trans ligandSub
  refine ⟨frame, ligand, frameComputed, fun i => ?_⟩
  exact ligandSub_spec (indexEquiv i)

/-- Frame existence from `RealTetrahedralCenterNode`. -/
theorem exists_simpleBond_localizedOccurrenceFourLigandFrame_of_realCenter
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (meaning : input.RealTetrahedralCenterNode target.1.node center) :
    ∃ frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel,
      input.localizedOccurrenceFourLigandFrame? target = some frame := by
  obtain ⟨frame, _ligand, computed, _spec⟩ :=
    input.exists_simpleBond_localizedOccurrenceFourLigandFrame_and_neighborEquiv
      singleBonded enough target center meaning
  exact ⟨frame, computed⟩

/-- Frame existence from the executable recognizer `localizedOccurrenceDescriptorCenter?`. -/
theorem exists_simpleBond_localizedOccurrenceFourLigandFrame_of_recognition
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (recognized : input.localizedOccurrenceDescriptorCenter? target = some center) :
    ∃ frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel,
      input.localizedOccurrenceFourLigandFrame? target = some frame :=
  input.exists_simpleBond_localizedOccurrenceFourLigandFrame_of_realCenter singleBonded enough
    target center
    ((input.localizedOccurrenceDescriptorCenter?_eq_some_iff target center).mp recognized)

/-- **Detected-ligand permutation.**  The four frame slots are a permutation of
`detectedMultiCenterMolecule.ligandAtomAt` at the recognized center. The permutation is the
composite of the child/neighbor bijection with the inverse of the detected ligand enumeration. -/
theorem exists_simpleBond_localizedOccurrenceFourLigandFrame_and_ligandPermutation_detected
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (meaning : input.RealTetrahedralCenterNode target.1.node center) :
    ∃ (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
      (alpha : Equiv.Perm (Fin 4)),
      input.localizedOccurrenceFourLigandFrame? target = some frame ∧
        ∀ i, (frame.cursorAt i).occurrence.1.node.current? =
          some (input.detectedMultiCenterMolecule.ligandAtomAt
            ⟨center.1, center.2⟩ (alpha i)) := by
  classical
  let detectedCenter : input.detectedMultiCenterMolecule.Center := ⟨center.1, center.2⟩
  obtain ⟨frame, ligand, frameComputed, ligandSpec⟩ :=
    input.exists_simpleBond_localizedOccurrenceFourLigandFrame_and_neighborEquiv
      singleBonded enough target center meaning
  let alpha : Equiv.Perm (Fin 4) :=
    ligand.trans (input.physicalLigandEquiv input.detectedMultiCenterMolecule rfl detectedCenter).symm
  refine ⟨frame, alpha, frameComputed, fun i => ?_⟩
  have key : input.physicalLigandEquiv input.detectedMultiCenterMolecule rfl detectedCenter
      (alpha i) = ligand i := by
    unfold alpha
    simp only [Equiv.trans_apply]
    exact (input.physicalLigandEquiv input.detectedMultiCenterMolecule rfl
      detectedCenter).apply_symm_apply (ligand i)
  calc (frame.cursorAt i).occurrence.1.node.current?
      = some (ligand i).1 := ligandSpec i
    _ = some (input.physicalLigandEquiv input.detectedMultiCenterMolecule rfl
          detectedCenter (alpha i)).1 := by rw [← key]
    _ = some (input.detectedMultiCenterMolecule.ligandAtomAt detectedCenter (alpha i)) := by
          rw [input.physicalLigandEquiv_apply_coe]

/-- Detected-ligand permutation from `localizedOccurrenceDescriptorCenter? = some center`. -/
theorem exists_simpleBond_localizedOccurrenceFourLigandFrame_and_ligandPermutation_of_recognition
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (recognized : input.localizedOccurrenceDescriptorCenter? target = some center) :
    ∃ (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
      (alpha : Equiv.Perm (Fin 4)),
      input.localizedOccurrenceFourLigandFrame? target = some frame ∧
        ∀ i, (frame.cursorAt i).occurrence.1.node.current? =
          some (input.detectedMultiCenterMolecule.ligandAtomAt
            ⟨center.1, center.2⟩ (alpha i)) :=
  input.exists_simpleBond_localizedOccurrenceFourLigandFrame_and_ligandPermutation_detected
    singleBonded enough target center
    ((input.localizedOccurrenceDescriptorCenter?_eq_some_iff target center).mp recognized)

/-- Classification of every cursor of a successful simple-bond four-ligand frame. A frame slot
whose atom lies on the history and is not the parent is a terminal ring duplicate; the parent
slot is the active-simple parent occurrence. -/
theorem simpleBond_fourLigandFrame_cursor_classified
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (meaning : input.RealTetrahedralCenterNode target.1.node center)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (child : input.LocalizedRerootCursor carrierFuel)
    (present : child ∈ frame.cursors) :
    ∃ w, child.occurrence.1.node.current? = some w ∧
      input.moleculeGraph.Adj center.1 w ∧
      ((∃ certificate : input.LocalizedParentFrameHistory target,
          child.occurrence = certificate.parent ∧
          certificate.parent.1.node.ActiveSimple ∧
          target.1.node.parent? = some w ∧
          w ∈ target.1.node.history) ∨
        (child.occurrence.1.node = target.1.node.extend w 0 ∧
          target.1.node.parent? ≠ some w ∧
          (w ∈ target.1.node.history →
            child.occurrence.1.node.provenance =
              OfficialCIPNodeProvenance.ringDuplicate
                (target.1.node.duplicateRootDistance w) ∧
            child.occurrence.1.node.isDuplicateLeaf = true ∧
            input.executableOfficialCIPChildren child.occurrence.1.node = []) ∧
          (w ∉ target.1.node.history →
            child.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom))) := by
  have derived :=
    (input.localizedOccurrenceFourLigandFrame?_eq_some_iff target frame).mp computed
  have childrenComputed : input.localizedRerootChildren?
      ({ occurrence := target, previous? := none } :
        input.LocalizedRerootCursor carrierFuel) = some frame.cursors :=
    (input.localizedRerootChildren?_eq_some_iff _ frame.cursors).mpr derived.1
  exact input.simpleBond_realCenter_immediateChild_classified singleBonded target center meaning
    frame.cursors childrenComputed child present

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.carrierOccurrence_history_length_eq_address_succ
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realCarrierOccurrence_remaining_pos
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.simpleBond_childCopy_eq_zero
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realCenter_outwardChildFrame_of_notParent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.simpleBond_outwardFrame_extend_zero
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realCenter_parent_current
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.simpleBond_realCenter_childFrames
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.simpleBond_realCenter_rerootChildren_current_iff_adjacent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.simpleBond_realCenter_rerootChildren_current_injective
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.simpleBond_realCenter_rerootChildren_neighborEquiv
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.simpleBond_realCenter_immediateChild_classified
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.simpleBond_realCenter_parent_handled
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.simpleBond_realCenter_visitedNeighbor_terminalRingDuplicate
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.simpleBond_realCenter_rerootChildren_length_eq_neighbor_card
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_simpleBond_localizedOccurrenceFourLigandFrame_and_neighborEquiv
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_simpleBond_localizedOccurrenceFourLigandFrame_of_realCenter
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_simpleBond_localizedOccurrenceFourLigandFrame_of_recognition
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_simpleBond_localizedOccurrenceFourLigandFrame_and_ligandPermutation_detected
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_simpleBond_localizedOccurrenceFourLigandFrame_and_ligandPermutation_of_recognition
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.simpleBond_fourLigandFrame_cursor_classified
