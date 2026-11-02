import TetraStereo.OneCenter.AcyclicCutBranchAutomorphism
import TetraStereo.OneCenter.LocalizedAcyclicCarrierInjectivity
import TetraStereo.OneCenter.LocalizedParentFrameHistory
import TetraStereo.OneCenter.LocalizedOutwardRerootDependencySupport
import TetraStereo.KernelOnly

set_option autoImplicit false

















































namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

variable (input : CertifiedLocalizedCIPInput)

/-! ## Carrier occurrences at any sufficient fuel -/

/-- Every occurrence of the shared carrier at any fuel occupies at most `atomCount` sibling
slots.  The proof uses the exact history/address grading and the duplicate-freedom of the stored
real physical history; no carrier sufficiency hypothesis is needed for this bound. -/
theorem carrierOccurrence_address_length_le_atomCount
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    occurrence.1.address.length ≤ input.certified.input.molecule.atomCount := by
  have derived := (input.mem_localizedOccurrences_iff
    carrierFuel occurrence.1).mp occurrence.2
  have rooted := input.declarativeLocalizedOccurrence_as_rootSubtree derived
  have historyLength :
      occurrence.1.node.history.length = occurrence.1.address.length + 1 :=
    input.declarativeLocalizedOccurrenceSubtree_history_length rooted
      (by simp [OfficialCIPNode.root])
  have nodup := input.carrierOccurrence_history_nodup singleBonded acyclic occurrence
  have cardLe := nodup.length_le_card
  simp only [Fintype.card_fin] at cardLe
  omega

/-- Every occurrence of the shared carrier at a fuel at least `atomCount` still has strictly
positive remaining expansion depth.  The address occupies at most `atomCount` slots while the
depth grade is `carrierFuel + 1`, so this is exactly where the fuel bound is used. -/
theorem carrierOccurrence_remaining_pos
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    0 < occurrence.1.remaining := by
  have grade := input.declarativeLocalizedOccurrence_depthGrade
    ((input.mem_localizedOccurrences_iff carrierFuel occurrence.1).mp occurrence.2)
  have bound :=
    input.carrierOccurrence_address_length_le_atomCount singleBonded acyclic occurrence
  omega

/-- **Fuel-general positive occurrence witness.**  Every simple physical walk from a root atom at
the original center is represented by an actual carrier occurrence at **any** fuel at least
`atomCount`, with the exact terminal atom, real provenance, the atom-count address bound, the
stored remaining depth `carrierFuel + 1 - address.length`, and strictly positive stored remaining
depth.

This is the fuel-lifting form of `carrierOccurrence_exists_of_simple_walk`: the witness is built
from the underlying `SimpleOccurrencePath` through
`legitimateOccurrence_mem_localizedOccurrences_of_fuel`, not from the exact-`atomCount` carrier
constructor, so it applies verbatim to the universal reference carrier at `atomCount + 1`. -/
theorem carrierOccurrence_exists_of_simple_walk_of_fuel
    {root target : input.Atom}
    (walk : input.moleculeGraph.underlyingSimpleGraph.Walk root target)
    (simple : walk.IsPath)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel) :
    ∃ (occurrence : input.LocalizedCIPOccurrence carrierFuel)
      (node : OfficialCIPNode input.Atom) (address : List Nat),
      occurrence.1.root = root ∧
      occurrence.1.address = address ∧
      occurrence.1.node = node ∧
      occurrence.1.remaining = carrierFuel + 1 - address.length ∧
      occurrence.1.node.current? = some target ∧
      occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
      occurrence.1.address.length ≤ input.certified.input.molecule.atomCount ∧
      0 < occurrence.1.remaining := by
  obtain ⟨node, address, path, observed⟩ :=
    input.simpleOccurrencePath_of_simple_walk walk simple
  let legitimate : LegitimateOccurrence input root node address :=
    LegitimateOccurrence.simple path
  have lengthBound := input.legitimateOccurrence_address_length_le_atomCount legitimate
  have fuelBound : address.length ≤ carrierFuel := le_trans lengthBound enough
  let frame : input.LocalizedCIPOccurrenceFrame :=
    { root := root
      address := address
      node := node
      remaining := carrierFuel + 1 - address.length }
  have present : frame ∈ input.localizedOccurrences carrierFuel := by
    simpa [frame] using input.legitimateOccurrence_mem_localizedOccurrences_of_fuel
      (fuel := carrierFuel) legitimate fuelBound
  let occurrence : input.LocalizedCIPOccurrence carrierFuel := ⟨frame, present⟩
  refine ⟨occurrence, node, address, rfl, rfl, rfl, rfl, ?_, ?_, lengthBound, ?_⟩
  · simpa [occurrence, frame] using observed
  · simpa [occurrence, frame] using input.simpleOccurrencePath_provenance path
  · have remainingEq : occurrence.1.remaining = carrierFuel + 1 - address.length := rfl
    omega

/-! ## Physical adjacency of the two carrier neighbor classes -/

/-- **Strict outward carrier neighbor is a physical neighbor.**  If a carrier frame `frame` sits
at address `target.address ++ [slot]` inside the shared carrier, then its current atom is
physically adjacent to the target's current atom.  The proof inverts the actual derivation step
with `declarativeLocalizedOccurrence_immediate_child` and reads the adjacency from the executable
official child enumeration. -/
theorem outwardChildFrame_current_adjacent
    {carrierFuel : Nat}
    {oAtom w : input.Atom}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    (oObserved : target.1.node.current? = some oAtom)
    (frame : input.LocalizedCIPOccurrenceFrame)
    (neighbor : frame ∈ input.localizedRerootNeighborFrames
      (fuel := carrierFuel) target.1)
    (slot : Nat)
    (addressEq : frame.address = target.1.address ++ [slot])
    (frameCurrent : frame.node.current? = some w) :
    input.moleculeGraph.Adj oAtom w := by
  have characterized :=
    (input.mem_localizedRerootNeighborFrames_iff target.1 frame).mp neighbor
  obtain ⟨framePresent, sameRoot, _classified⟩ := characterized
  obtain ⟨childNode, childAtSlot, frameEq⟩ :=
    input.declarativeLocalizedOccurrence_immediate_child
      ((input.mem_localizedOccurrences_iff
        carrierFuel target.1).mp target.2)
      ((input.mem_localizedOccurrences_iff
        carrierFuel frame).mp framePresent)
      sameRoot slot addressEq
  have childObserved : childNode.current? = some w := by
    have observed := frameCurrent
    rw [frameEq] at observed
    exact observed
  exact input.adj_of_mem_executableOfficialCIPChildren
    target.1.node childNode oAtom w oObserved childObserved
    (List.fst_mem_of_mem_zipIdx childAtSlot)

/-- **Shorter-address carrier neighbor is a physical neighbor.**  The actual parent frame of a
non-root carrier occurrence is physically adjacent to it.  The proof inverts the target's
derivation step from the parent frame and reads the adjacency from the executable official child
enumeration, so the parent atom is not identified by any assumed history agreement. -/
theorem parentFrame_current_adjacent
    {carrierFuel : Nat}
    {oAtom : input.Atom}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    (oObserved : target.1.node.current? = some oAtom)
    (nonroot : target.1.address ≠ [])
    (certificate : input.LocalizedParentFrameHistory target) :
    ∃ parentCurrent,
      certificate.parent.1.node.current? = some parentCurrent ∧
        input.moleculeGraph.Adj oAtom parentCurrent := by
  have sameRoot : target.1.root = certificate.parent.1.root :=
    certificate.parent_root.symm
  let slot := target.1.address.getLast nonroot
  have addressEq : target.1.address = certificate.parent.1.address ++ [slot] := by
    rw [certificate.parent_address]
    exact (List.dropLast_append_getLast (l := target.1.address) nonroot).symm
  obtain ⟨childNode, childAtSlot, frameEq⟩ :=
    input.declarativeLocalizedOccurrence_immediate_child
      ((input.mem_localizedOccurrences_iff
        carrierFuel certificate.parent.1).mp certificate.parent.2)
      ((input.mem_localizedOccurrences_iff
        carrierFuel target.1).mp target.2)
      sameRoot slot addressEq
  obtain ⟨parentCurrent, parentObserved⟩ := Option.isSome_iff_exists.mp
    (input.declarativeLocalizedOccurrence_node_current_isSome
      ((input.mem_localizedOccurrences_iff
        carrierFuel certificate.parent.1).mp certificate.parent.2))
  have childObserved : childNode.current? = some oAtom := by
    have observed := oObserved
    rw [frameEq] at observed
    exact observed
  have adjacent := input.adj_of_mem_executableOfficialCIPChildren
    certificate.parent.1.node childNode parentCurrent oAtom parentObserved childObserved
    (List.fst_mem_of_mem_zipIdx childAtSlot)
  exact ⟨parentCurrent, parentObserved, (input.moleculeGraph.adj_symm).mp adjacent⟩

/-! ## Realizing a physical neighbor as an actual carrier child frame -/

/-- **Physical neighbor that is not the stored parent is an executable outward child.**  Given a
real carrier occurrence at a sufficient fuel, a positive-bond neighbor `w` that is not its stored
parent, we build the exact executable zero-copy child frame at the executable raw-copy slot of
`(w, 0)`.  The frame is an actual carrier occurrence and an actual outward carrier child. -/
theorem carrierChildFrame_of_adjacent_notParent
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
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
  have sourceDerived :=
    (input.mem_localizedOccurrences_iff carrierFuel target.1).mp target.2
  have positive := input.carrierOccurrence_remaining_pos singleBonded acyclic enough target
  let childFrame : input.LocalizedCIPOccurrenceFrame :=
    { root := target.1.root
      address := target.1.address ++ [slot]
      node := target.1.node.extend w 0
      remaining := target.1.remaining - 1 }
  have childDerived : input.DeclarativeLocalizedOccurrence carrierFuel childFrame :=
    DeclarativeLocalizedOccurrence.immediateChild input sourceDerived positive atSlot
  have childPresent : childFrame ∈ input.localizedOccurrences carrierFuel :=
    (input.mem_localizedOccurrences_iff carrierFuel childFrame).mpr childDerived
  have outwardPresent : childFrame ∈
      input.localizedCarrierOutwardChildFrames (fuel := carrierFuel) target.1 := by
    rw [localizedCarrierOutwardChildFrames, List.mem_filter]
    refine ⟨childPresent, ?_⟩
    simp [childFrame]
  exact ⟨childFrame, slot, rfl, rfl, by simp [childFrame], rfl, childPresent, outwardPresent⟩

/-! ## Structural invariants of the actual child list -/

/-- Every child of an actual expansion records the source occurrence as its incoming cut. -/
theorem localizedRerootChildren?_previous_eq
    {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (children : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRerootChildren? cursor = some children) :
    ∀ child ∈ children, child.previous? = some cursor.occurrence :=
  (input.localizedRerootChildren?_sound cursor children computed).2

/-- Every child of an actual expansion keeps the source original root atom. -/
theorem localizedRerootChildren?_root_eq
    {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (children : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRerootChildren? cursor = some children)
    (child : input.LocalizedRerootCursor carrierFuel)
    (present : child ∈ children) :
    child.occurrence.1.root = cursor.occurrence.1.root :=
  input.localizedRerootChildren_root_eq cursor child children
    (input.localizedRerootChildren?_sound cursor children computed) present




theorem localizedRerootChildren?_current_injective
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (children : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRerootChildren? cursor = some children) :
    ∀ left ∈ children, ∀ right ∈ children,
      left.occurrence.1.node.current? = right.occurrence.1.node.current? →
        left = right := by
  intro left leftPresent right rightPresent sameCurrent
  have derived := input.localizedRerootChildren?_sound cursor children computed
  have leftRoot := input.localizedRerootChildren_root_eq cursor left children derived leftPresent
  have rightRoot :=
    input.localizedRerootChildren_root_eq cursor right children derived rightPresent
  have occurrenceEq := input.localizedCIPOccurrence_current_injective_at_fixedRoot
    singleBonded acyclic left.occurrence right.occurrence
    (leftRoot.trans rightRoot.symm) sameCurrent
  have leftPrevious := derived.2 left leftPresent
  have rightPrevious := derived.2 right rightPresent
  exact LocalizedRerootCursor.ext input occurrenceEq
    (leftPrevious.trans rightPrevious.symm)

/-! ## The central correspondence, incoming-coordinate case -/













theorem localizedRerootChildren?_current_iff_adjacent_of_previous
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous)
    (sameRoot : cursor.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : cursor.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (children : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRerootChildren? cursor = some children) :
    ∀ w, (∃ child ∈ children, child.occurrence.1.node.current? = some w) ↔
      input.moleculeGraph.Adj oAtom w ∧ w ≠ pAtom := by
  have derived := input.localizedRerootChildren?_sound cursor children computed
  have previousDerived :=
    (input.mem_localizedOccurrences_iff carrierFuel previous.1).mp previous.2
  intro w
  constructor
  · -- Forward: every emitted child's current atom is a physical neighbor, and never the
    -- incoming atom (the incoming coordinate is cut).
    rintro ⟨child, childPresent, childCurrent⟩
    have intended : child.occurrence.1 ∈
        input.intendedLocalizedRerootChildFrames cursor := by
      rw [← derived.1]
      exact List.mem_map.mpr ⟨child, childPresent, rfl⟩
    have neighbor := input.mem_localizedRerootNeighborFrames_of_mem_intended
      cursor child.occurrence.1 intended
    have characterized :=
      (input.mem_localizedRerootNeighborFrames_iff
        cursor.occurrence.1 child.occurrence.1).mp neighbor
    obtain ⟨framePresent, sameFrameRoot, classified⟩ := characterized
    have childNotPrevious : child.occurrence.1.address ≠ previous.1.address :=
      input.address_ne_previous_of_mem_intended cursor previous previousEq
        child.occurrence.1 intended
    have currentNe : w ≠ pAtom := by
      intro wEq
      have occurrenceEq := input.localizedCIPOccurrence_current_injective_at_fixedRoot
        singleBonded acyclic child.occurrence previous
        (sameFrameRoot.trans sameRoot) (by rw [childCurrent, pObserved, wEq])
      have addressEq : child.occurrence.1.address = previous.1.address :=
        congrArg (fun occurrence => occurrence.1.address) occurrenceEq
      exact childNotPrevious addressEq
    have physical : input.moleculeGraph.Adj oAtom w := by
      rcases classified with parentCase | childCase
      · -- Shorter-address neighbor: the actual parent frame, physically adjacent.
        have parentCase' := parentCase
        have nonroot : cursor.occurrence.1.address ≠ [] := by
          intro empty
          rw [empty] at parentCase'
          simp at parentCase'
        obtain ⟨certificate⟩ :=
          input.exists_localizedParentFrameHistory cursor.occurrence nonroot
        have frameEq : child.occurrence.1 = certificate.parent.1 :=
          input.declarativeLocalizedOccurrence_functional_at_root_address
            ((input.mem_localizedOccurrences_iff carrierFuel child.occurrence.1).mp
              framePresent)
            ((input.mem_localizedOccurrences_iff carrierFuel certificate.parent.1).mp
              certificate.parent.2)
            (sameFrameRoot.trans certificate.parent_root.symm)
            (parentCase'.2.trans certificate.parent_address.symm)
        obtain ⟨parentCurrent, parentCurrentObserved, parentAdjacent⟩ :=
          input.parentFrame_current_adjacent oObserved nonroot certificate
        have childCurrent' : certificate.parent.1.node.current? = some w := by
          rw [frameEq] at childCurrent
          exact childCurrent
        have wEq : w = parentCurrent :=
          Option.some.inj (childCurrent'.symm.trans parentCurrentObserved)
        rw [wEq]
        exact parentAdjacent
      · -- Strict outward neighbor: the actual executable child of the occurrence.
        have childCase' := childCase
        have nonempty : child.occurrence.1.address ≠ [] := by
          intro empty
          rw [empty] at childCase'
          simp at childCase'
        refine input.outwardChildFrame_current_adjacent oObserved
          child.occurrence.1 neighbor
          (child.occurrence.1.address.getLast nonempty) ?_ childCurrent
        calc child.occurrence.1.address
            = child.occurrence.1.address.dropLast ++
                [child.occurrence.1.address.getLast nonempty] :=
              (List.dropLast_append_getLast
                (l := child.occurrence.1.address) nonempty).symm
          _ = cursor.occurrence.1.address ++
                [child.occurrence.1.address.getLast nonempty] := by
              rw [← childCase'.2]
    exact ⟨physical, currentNe⟩
  · -- Reverse: every parent-deleted physical neighbor is realized by an actual child frame.
    rintro ⟨adjacent, wNeP⟩
    have notDuplicate :=
      input.carrierOccurrence_not_duplicateLeaf singleBonded acyclic cursor.occurrence
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
          (certificate.parent_root.trans sameRoot) sameAddress
        have currentSame :
            certificate.parent.1.node.current? = previous.1.node.current? :=
          congrArg (fun frame => frame.node.current?) frameEq
        rw [certificateCurrent, pObserved] at currentSame
        exact wNeP (Option.some.inj currentSame)
      have intended : certificate.parent.1 ∈
          input.intendedLocalizedRerootChildFrames cursor := by
        unfold intendedLocalizedRerootChildFrames
        rw [if_neg (by simpa using notDuplicate)]
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
      exact ⟨childCursor, childPresent, by rw [childOccurrenceEq]; exact certificateCurrent⟩
    · -- The neighbor is not the stored parent: realize the actual executable zero-copy child.
      have notParent : cursor.occurrence.1.node.parent? ≠ some w := sameParent
      have real :=
        input.carrierOccurrence_provenance_real singleBonded acyclic cursor.occurrence
      obtain ⟨childFrame, slot, addressEq, rootEq, frameCurrent, _nodeEq, childPresent,
        outwardPresent⟩ :=
        input.carrierChildFrame_of_adjacent_notParent singleBonded acyclic enough
          cursor.occurrence oObserved adjacent notParent real
      have childDerived :=
        (input.mem_localizedOccurrences_iff carrierFuel childFrame).mp childPresent
      have neighborPresent : childFrame ∈
          input.localizedRerootNeighborFrames (fuel := carrierFuel)
            cursor.occurrence.1 :=
        List.mem_append_right _ outwardPresent
      have addressNe : childFrame.address ≠ previous.1.address := by
        intro sameAddress
        have frameEq := input.declarativeLocalizedOccurrence_functional_at_root_address
          childDerived previousDerived (rootEq.trans sameRoot) sameAddress
        have currentSame : childFrame.node.current? = previous.1.node.current? :=
          congrArg (fun frame => frame.node.current?) frameEq
        rw [frameCurrent, pObserved] at currentSame
        exact wNeP (Option.some.inj currentSame)
      have intended : childFrame ∈
          input.intendedLocalizedRerootChildFrames cursor := by
        unfold intendedLocalizedRerootChildFrames
        rw [if_neg (by simpa using notDuplicate)]
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
        exact frameCurrent⟩

/-! ## The central correspondence, root-cursor case -/

/-- **Root cursor: actual reroot children realize exactly the physical neighborhood.**  With no
incoming coordinate (`previous? = none`) the cut removes nothing, and the child current atoms are
exactly the physical neighbors of the root cursor's current atom. -/
theorem localizedRerootChildren?_current_iff_adjacent_root
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (rootCursor : cursor.previous? = none)
    {oAtom : input.Atom}
    (oObserved : cursor.occurrence.1.node.current? = some oAtom)
    (children : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRerootChildren? cursor = some children) :
    ∀ w, (∃ child ∈ children, child.occurrence.1.node.current? = some w) ↔
      input.moleculeGraph.Adj oAtom w := by
  have derived := input.localizedRerootChildren?_sound cursor children computed
  have notDuplicate :=
    input.carrierOccurrence_not_duplicateLeaf singleBonded acyclic cursor.occurrence
  intro w
  constructor
  · rintro ⟨child, childPresent, childCurrent⟩
    have intended : child.occurrence.1 ∈
        input.intendedLocalizedRerootChildFrames cursor := by
      rw [← derived.1]
      exact List.mem_map.mpr ⟨child, childPresent, rfl⟩
    have neighbor := input.mem_localizedRerootNeighborFrames_of_mem_intended
      cursor child.occurrence.1 intended
    have characterized :=
      (input.mem_localizedRerootNeighborFrames_iff
        cursor.occurrence.1 child.occurrence.1).mp neighbor
    obtain ⟨framePresent, sameFrameRoot, classified⟩ := characterized
    rcases classified with parentCase | childCase
    · have parentCase' := parentCase
      have nonroot : cursor.occurrence.1.address ≠ [] := by
        intro empty
        rw [empty] at parentCase'
        simp at parentCase'
      obtain ⟨certificate⟩ :=
        input.exists_localizedParentFrameHistory cursor.occurrence nonroot
      obtain ⟨parentCurrent, parentCurrentObserved, parentAdjacent⟩ :=
        input.parentFrame_current_adjacent oObserved nonroot certificate
      have frameEq : child.occurrence.1 = certificate.parent.1 :=
        input.declarativeLocalizedOccurrence_functional_at_root_address
          ((input.mem_localizedOccurrences_iff carrierFuel child.occurrence.1).mp
            framePresent)
          ((input.mem_localizedOccurrences_iff carrierFuel certificate.parent.1).mp
            certificate.parent.2)
          (sameFrameRoot.trans certificate.parent_root.symm)
          (parentCase'.2.trans certificate.parent_address.symm)
      have childCurrent' : certificate.parent.1.node.current? = some w := by
        rw [frameEq] at childCurrent
        exact childCurrent
      have wEq : w = parentCurrent :=
        Option.some.inj (childCurrent'.symm.trans parentCurrentObserved)
      rw [wEq]
      exact parentAdjacent
    · have childCase' := childCase
      have nonempty : child.occurrence.1.address ≠ [] := by
        intro empty
        rw [empty] at childCase'
        simp at childCase'
      refine input.outwardChildFrame_current_adjacent oObserved
        child.occurrence.1 neighbor
        (child.occurrence.1.address.getLast nonempty) ?_ childCurrent
      calc child.occurrence.1.address
          = child.occurrence.1.address.dropLast ++
              [child.occurrence.1.address.getLast nonempty] :=
            (List.dropLast_append_getLast
              (l := child.occurrence.1.address) nonempty).symm
        _ = cursor.occurrence.1.address ++
              [child.occurrence.1.address.getLast nonempty] := by
            rw [← childCase'.2]
  · rintro adjacent
    by_cases sameParent : cursor.occurrence.1.node.parent? = some w
    · have nonroot : cursor.occurrence.1.address ≠ [] := by
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
      have intended : certificate.parent.1 ∈
          input.intendedLocalizedRerootChildFrames cursor := by
        unfold intendedLocalizedRerootChildFrames
        rw [if_neg (by simpa using notDuplicate)]
        rw [rootCursor]
        exact certificate.parent_mem_neighborFrames input
      have member : certificate.parent.1 ∈
          children.map (fun child => child.occurrence.1) := by
        rw [derived.1]
        exact intended
      rw [List.mem_map] at member
      obtain ⟨childCursor, childPresent, childOccurrenceEq⟩ := member
      exact ⟨childCursor, childPresent, by
        rw [childOccurrenceEq]
        exact certificateCurrent⟩
    · have notParent : cursor.occurrence.1.node.parent? ≠ some w := sameParent
      have real :=
        input.carrierOccurrence_provenance_real singleBonded acyclic cursor.occurrence
      obtain ⟨childFrame, _slot, _addressEq, _rootEq, frameCurrent, _nodeEq,
        childPresent, outwardPresent⟩ :=
        input.carrierChildFrame_of_adjacent_notParent singleBonded acyclic enough
          cursor.occurrence oObserved adjacent notParent real
      have neighborPresent : childFrame ∈
          input.localizedRerootNeighborFrames (fuel := carrierFuel)
            cursor.occurrence.1 :=
        List.mem_append_right _ outwardPresent
      have intended : childFrame ∈
          input.intendedLocalizedRerootChildFrames cursor := by
        unfold intendedLocalizedRerootChildFrames
        rw [if_neg (by simpa using notDuplicate)]
        rw [rootCursor]
        exact neighborPresent
      have member : childFrame ∈ children.map (fun child => child.occurrence.1) := by
        rw [derived.1]
        exact intended
      rw [List.mem_map] at member
      obtain ⟨childCursor, childPresent', childOccurrenceEq⟩ := member
      exact ⟨childCursor, childPresent', by
        rw [childOccurrenceEq]
        exact frameCurrent⟩

/-! ## Bundled cursor invariants -/

/-- **Bundled actual child invariants.**  An actual expansion records the source occurrence as
the incoming cut on every child, preserves the original carrier root on every child, and has
injective physical current-atom projection. -/
theorem localizedRerootChildren?_previous_root_injective
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (children : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRerootChildren? cursor = some children) :
    (∀ child ∈ children, child.previous? = some cursor.occurrence) ∧
      (∀ child ∈ children, child.occurrence.1.root = cursor.occurrence.1.root) ∧
      (∀ left ∈ children, ∀ right ∈ children,
        left.occurrence.1.node.current? = right.occurrence.1.node.current? →
          left = right) :=
  ⟨input.localizedRerootChildren?_previous_eq cursor children computed,
    fun child present =>
      input.localizedRerootChildren?_root_eq cursor children computed child present,
    input.localizedRerootChildren?_current_injective singleBonded acyclic
      cursor children computed⟩

/-! ## Iterated actual directed-cut correspondence

The local correspondence above is iterated along the actual executable child lists, preserving the
original-root coordinates throughout.  Reachability is the plain reflexive-transitive closure of
`E`, so the zero-step path is included.  No synthetic re-rooted graph is introduced: every step is
an actual `executableLocalizedRerootChildren` member.
-/

/-- Reachability through the actual executable child lists, with the zero-step path included. -/
def ActualChildReachable (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (start target : input.LocalizedRerootCursor carrierFuel) : Prop :=
  Relation.ReflTransGen (E input) start target

/-- Geometric state of an actual cursor reached from a start cursor whose incoming coordinate is
the genuine address parent.  The incoming cut is strictly shorter, every executable step is
therefore strictly outward, and the address length grows monotonically away from the start. -/
structure ActualCutReachableState (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (start cursor : input.LocalizedRerootCursor carrierFuel) : Prop where
  valid : input.LocalizedRerootCursorValid cursor
  root : cursor.occurrence.1.root = start.occurrence.1.root
  atLeast : start.occurrence.1.address.length ≤ cursor.occurrence.1.address.length
  strictlyDeeper : cursor ≠ start →
    start.occurrence.1.address.length < cursor.occurrence.1.address.length
  incomingShorter : ∃ previous, cursor.previous? = some previous ∧
    previous.1.address.length < cursor.occurrence.1.address.length








theorem actualCutReachableState_step
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (sameRootStart : start.occurrence.1.root = previous.1.root)
    (parentShorter : previous.1.address.length < start.occurrence.1.address.length)
    {oAtom pAtom : input.Atom}
    (pObserved : previous.1.node.current? = some pAtom)
    (b c : input.LocalizedRerootCursor carrierFuel)
    (stateB : ActualCutReachableState input start b)
    (branchB : ∀ w, b.occurrence.1.node.current? = some w →
      w ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom)
    (step : E input b c) :
    ActualCutReachableState input start c ∧
      ∀ w, c.occurrence.1.node.current? = some w →
        w ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom := by
  obtain ⟨previousB, previousEqB, previousShorterB⟩ := stateB.incomingShorter
  obtain ⟨_dropLast, childLength, childRoot, childPrevious, childValid⟩ :=
    input.outward_edge b c stateB.valid previousB previousEqB previousShorterB step
  have stateC : ActualCutReachableState input start c :=
    { valid := childValid
      root := childRoot.trans stateB.root
      atLeast := by
        rw [childLength]
        exact Nat.le_trans stateB.atLeast (Nat.le_succ _)
      strictlyDeeper := by
        intro _notStart
        rw [childLength]
        exact Nat.lt_of_le_of_lt stateB.atLeast (Nat.lt_succ_self _)
      incomingShorter := ⟨b.occurrence, childPrevious, by
        rw [childLength]
        exact Nat.lt_succ_self _⟩ }
  refine ⟨stateC, ?_⟩
  intro w observed
  -- The local neighbor theorem at the source cursor `b`, using its actual validity.
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
    input.localizedRerootChildren?_current_iff_adjacent_of_previous
      singleBonded acyclic enough b previousB previousEqB sameRootB
      xObserved zObserved (input.executableLocalizedRerootChildren b)
      (input.localizedRerootChildren?_eq_some_executable b)
  obtain ⟨adjacent, _notZ⟩ :=
    (localIff w).mp ⟨c, step, observed⟩
  have xBranch : x ∈ AcyclicCutBranchAutomorphism.CutBranch
      input.moleculeGraph pAtom oAtom :=
    branchB x xObserved
  have wNeRoot : w ≠ pAtom := by
    intro wEq
    have occurrenceEq : c.occurrence = previous :=
      input.localizedCIPOccurrence_current_injective_at_fixedRoot
        singleBonded acyclic c.occurrence previous
        (stateC.root.trans sameRootStart)
        (by rw [observed, pObserved, wEq])
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

/-- **Forward direction: every actually reachable current atom lies in the parent-deleted
physical branch.**  The state invariant and the branch membership are proved together by
induction over the actual child-list closure. -/
theorem actualReachable_state_and_mem_cutBranch
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : start.previous? = some previous)
    (sameRootStart : start.occurrence.1.root = previous.1.root)
    (validStart : input.LocalizedRerootCursorValid start)
    (parentShorter : previous.1.address.length < start.occurrence.1.address.length)
    {oAtom pAtom : input.Atom}
    (oObserved : start.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (target : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) start target) :
    ActualCutReachableState input start target ∧
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
            incomingShorter := ⟨previous, previousEq, parentShorter⟩ }
      · intro w observed
        have wEq : w = oAtom := Option.some.inj (observed.symm.trans oObserved)
        rw [wEq]
        exact AcyclicCutBranchAutomorphism.cutBranch_mem_self
          input.moleculeGraph incomingEdge
  | tail _path step ih =>
      exact input.actualCutReachableState_step (singleBonded := singleBonded)
        (acyclic := acyclic) (enough := enough) (start := start)
        (previous := previous) (sameRootStart := sameRootStart)
        (parentShorter := parentShorter) (pObserved := pObserved)
        (stateB := ih.1) (branchB := ih.2) (step := step)

/-! ## Completeness along a simple physical path -/

/-- **Backward lifting along a simple physical chain.**  Starting from any actual cursor with a
recorded incoming coordinate, every adjacent chain of fresh atoms is realized by actual executable
child steps.  The only atom excluded at each step is the recorded incoming atom, and the chain
being duplicate-free is exactly what guarantees that the next atom is not that incoming atom.

This is the source-coverage engine: it does not assume neighbor bisection, child totality or frame
agreement, and every produced step is a genuine `executableLocalizedRerootChildren` member. -/
theorem actualReachable_of_simple_chain
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (rest : List input.Atom) :
    ∀ (cursor : input.LocalizedRerootCursor carrierFuel)
      (previous : input.LocalizedCIPOccurrence carrierFuel)
      (current z : input.Atom),
      cursor.previous? = some previous →
      cursor.occurrence.1.root = previous.1.root →
      cursor.occurrence.1.node.current? = some current →
      previous.1.node.current? = some z →
      (current :: rest).Nodup →
      (current :: rest).IsChain (fun a b => input.moleculeGraph.Adj a b) →
      z ∉ current :: rest →
      ∃ target : input.LocalizedRerootCursor carrierFuel,
        Relation.ReflTransGen (E input) cursor target ∧
          target.occurrence.1.node.current? =
            (current :: rest).getLast? := by
  induction rest with
  | nil =>
      intro cursor previous current z previousEq sameRoot currentObserved zObserved
        nodup chain zAvoid
      refine ⟨cursor, Relation.ReflTransGen.refl, ?_⟩
      simpa using currentObserved
  | cons next tail inductionHypothesis =>
      intro cursor previous current z previousEq sameRoot currentObserved zObserved
        nodup chain zAvoid
      have nodupTail : (next :: tail).Nodup := (List.nodup_cons.mp nodup).2
      have currentNotTail : current ∉ next :: tail := (List.nodup_cons.mp nodup).1
      have nextNeZ : next ≠ z := by
        intro nextEq
        apply zAvoid
        rw [nextEq]
        exact List.mem_cons_of_mem current List.mem_cons_self
      have adjacent : input.moleculeGraph.Adj current next := chain.rel_head
      have localIff :=
        input.localizedRerootChildren?_current_iff_adjacent_of_previous
          singleBonded acyclic enough cursor previous previousEq sameRoot
          currentObserved zObserved (input.executableLocalizedRerootChildren cursor)
          (input.localizedRerootChildren?_eq_some_executable cursor)
      obtain ⟨child, childPresent, childCurrent⟩ :=
        (localIff next).mpr ⟨adjacent, nextNeZ⟩
      have childPrevious : child.previous? = some cursor.occurrence :=
        input.executableLocalizedRerootChildren_previous cursor child childPresent
      have childRoot : child.occurrence.1.root = cursor.occurrence.1.root :=
        input.localizedRerootChildren_root_eq cursor child
          (input.executableLocalizedRerootChildren cursor)
          (input.executableLocalizedRerootChildren_declarative cursor) childPresent
      obtain ⟨target, reachable, targetObserved⟩ :=
        inductionHypothesis child cursor.occurrence next current childPrevious childRoot
          childCurrent currentObserved nodupTail chain.tail currentNotTail
      refine ⟨target, ?_, ?_⟩
      · exact (Relation.ReflTransGen.tail Relation.ReflTransGen.refl
          childPresent).trans reachable
      · rw [targetObserved]
        rfl

/-! ## The iterated directed-cut correspondence -/

/-- **Reachable current atoms are exactly the parent-deleted physical branch.**  From an actual
cursor `start` whose incoming coordinate `previous` is the genuine address parent, whose cut is a
valid physical edge `pAtom - oAtom`, and with the original-root coordinates preserved throughout:

> an atom `w` occurs as the current atom of some cursor reachable from `start` through the actual
> executable child lists (the zero-step path included) if and only if `w` lies in the physical cut
> branch of `oAtom` after deleting `pAtom`.

The forward direction uses the iterated local neighbor theorem and the strictly-outward state
invariant; the reverse direction lifts a simple physical path avoiding `pAtom` through the actual
child lists.  No synthetic re-rooted graph, desired neighbor bisection, child totality, frame
agreement or physical cut bijection is assumed. -/
theorem actualChildReachable_current_iff_cutBranch
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : start.previous? = some previous)
    (sameRootStart : start.occurrence.1.root = previous.1.root)
    (validStart : input.LocalizedRerootCursorValid start)
    (parentShorter : previous.1.address.length < start.occurrence.1.address.length)
    {oAtom pAtom : input.Atom}
    (oObserved : start.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (w : input.Atom) :
    (∃ target : input.LocalizedRerootCursor carrierFuel,
      input.ActualChildReachable start target ∧
        target.occurrence.1.node.current? = some w) ↔
      w ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom := by
  constructor
  · rintro ⟨target, reachable, observed⟩
    exact (input.actualReachable_state_and_mem_cutBranch singleBonded acyclic enough
      start previous previousEq sameRootStart validStart parentShorter
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
      input.actualReachable_of_simple_chain singleBonded acyclic enough rest
        start previous oAtom pAtom previousEq sameRootStart oObserved pObserved
        nodup chain avoidCons
    exact ⟨target, reachable, by rw [targetObserved, lastEq]⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.carrierOccurrence_address_length_le_atomCount
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.carrierOccurrence_remaining_pos
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.carrierOccurrence_exists_of_simple_walk_of_fuel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outwardChildFrame_current_adjacent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.parentFrame_current_adjacent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.carrierChildFrame_of_adjacent_notParent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootChildren?_previous_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootChildren?_root_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootChildren?_current_injective
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootChildren?_current_iff_adjacent_of_previous
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootChildren?_current_iff_adjacent_root
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootChildren?_previous_root_injective
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualCutReachableState_step
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualReachable_state_and_mem_cutBranch
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualReachable_of_simple_chain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualChildReachable_current_iff_cutBranch
