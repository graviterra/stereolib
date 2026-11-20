import TetraStereo.OneCenter.LocalizedMarkedRetainedIndependentOperations
import TetraStereo.OneCenter.LocalizedSimpleBondFourLigandFrames
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# Degree counts and the unrestricted report identification

`LocalizedSimpleBondFourLigandFrames` proves that the uncut reroot children of a real centre
occurrence biject with its physical neighbours. Those proofs use the centre only through its atom
and real provenance; their statements are typed by `TetrahedralCenter`. The first section states
the same bijection for an arbitrary real atom occurrence (proofs adapted verbatim).

Consequences:

* `exec_length_lt_degree`: a valid cursor with an incoming coordinate has strictly fewer
  executable children than its atom has neighbours (the incoming carrier neighbour is cut).
* `frame_none_of_degree_ne_four`: a real occurrence of an atom without four neighbours has no
  certified four-ligand frame, so both the experimental and the independent operations refuse
  at three-coordinate (lone-pair) occurrences.
* `facts_eq_independent_general`, `descriptor_eq_independent_general`,
  `assign_eq_independent_general`: on every intake-agreeing admitted localized single-bond input,
  every generated fact, every recursive descriptor and the whole report of the experimental
  evaluator equal those of the comparator-free independent operations. No degree or branching
  premise remains; three-coordinate branching atoms are allowed.

Lone-pair stereocentres are refused by both records; treating them is outside this evaluator.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedRetainedReachDegree

open CertifiedLocalizedCIPInput DeclarativeCIP MoleculeGraph
open LocalizedMarkedOperationEvaluator LocalizedMarkedRetainedIndependentOperations
open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedOperations
open LocalizedMarkedRetainedPromotedOperations
open LocalizedMarkedCarrierLookup LocalizedMarkedReachableConfigurations
open LocalizedMarkedReachedFrameNeighbors LocalizedMarkedCertifiedTerminalRefusal
open LocalizedMarkedDetectedSnapshotSupport
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms?)

variable (input : CertifiedLocalizedCIPInput)

abbrev RawNode := RawMolecule.CanonicalBranchNode

/-- A real occurrence node of a given atom. -/
def RealAtomNode (node : OfficialCIPNode input.Atom) (atom : input.Atom) : Prop :=
  node.provenance = OfficialCIPNodeProvenance.realAtom ∧ node.current? = some atom

/-! ## Uncut children of an arbitrary real atom occurrence -/

theorem rerootChildren_current_iff_adjacent
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.Atom)
    (meaning : RealAtomNode input target.1.node center)
    (children : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRerootChildren?
      ({ occurrence := target, previous? := none } :
        input.LocalizedRerootCursor carrierFuel) = some children) :
    ∀ w, (∃ child ∈ children, child.occurrence.1.node.current? = some w) ↔
      input.moleculeGraph.Adj center w := by
  have oObserved : target.1.node.current? = some center := meaning.2
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

theorem rerootChildren_current_injective
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.Atom)
    (meaning : RealAtomNode input target.1.node center)
    (children : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRerootChildren?
      ({ occurrence := target, previous? := none } :
        input.LocalizedRerootCursor carrierFuel) = some children) :
    ∀ left ∈ children, ∀ right ∈ children,
      left.occurrence.1.node.current? = right.occurrence.1.node.current? →
        left = right := by
  have oObserved : target.1.node.current? = some center := meaning.2
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

/-- The uncut children of a real occurrence are as many as its atom's neighbours. -/
theorem rootChildren_length_eq_degree
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.Atom)
    (meaning : RealAtomNode input target.1.node center) :
    (input.executableLocalizedRerootChildren
      ({ occurrence := target, previous? := none } :
        input.LocalizedRerootCursor carrierFuel)).length =
      (input.moleculeGraph.neighborFinset center).card := by
  classical
  let rootCursor : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := target, previous? := none }
  let children := input.executableLocalizedRerootChildren rootCursor
  have computed : input.localizedRerootChildren? rootCursor = some children :=
    input.localizedRerootChildren?_eq_some_executable rootCursor
  have correspondence := rerootChildren_current_iff_adjacent input singleBonded enough target
    center meaning children computed
  have injective := rerootChildren_current_injective input singleBonded target center meaning
    children computed
  have nodup := input.localizedRerootChildren_nodup rootCursor children
    (input.localizedRerootChildren?_sound rootCursor children computed)
  let atomOf : {child // child ∈ children} → input.Atom :=
    fun child => Classical.choose (input.localizedRerootCursor_current_exists child.1)
  have atomOf_spec : ∀ child : {child // child ∈ children},
      child.1.occurrence.1.node.current? = some (atomOf child) :=
    fun child => Classical.choose_spec (input.localizedRerootCursor_current_exists child.1)
  let toNeighbor : {child // child ∈ children} → input.moleculeGraph.Neighbor center :=
    fun child => ⟨atomOf child,
      (correspondence (atomOf child)).mp ⟨child.1, child.2, atomOf_spec child⟩⟩
  have bijective : Function.Bijective toNeighbor := by
    constructor
    · intro left right equal
      have sameAtom : atomOf left = atomOf right := congrArg Subtype.val equal
      have sameCurrent : left.1.occurrence.1.node.current? =
          right.1.occurrence.1.node.current? := by
        rw [atomOf_spec left, atomOf_spec right, sameAtom]
      exact Subtype.ext (injective left.1 left.2 right.1 right.2 sameCurrent)
    · intro neighbor
      obtain ⟨child, present, current⟩ := (correspondence neighbor.1).mpr neighbor.2
      refine ⟨⟨child, present⟩, ?_⟩
      apply Subtype.ext
      exact Option.some.inj ((atomOf_spec ⟨child, present⟩).symm.trans current)
  have cardEq := Fintype.card_congr
    ((List.Nodup.getEquiv children nodup).trans (Equiv.ofBijective toNeighbor bijective))
  rw [Fintype.card_fin] at cardEq
  rw [cardEq, Fintype.card_subtype]
  rfl

/-! ## Cursors with an incoming coordinate -/

/-- The incoming carrier neighbour is cut: strictly fewer children than neighbours. -/
theorem exec_length_lt_degree
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous)
    (center : input.Atom)
    (meaning : RealAtomNode input cursor.occurrence.1.node center) :
    (input.executableLocalizedRerootChildren cursor).length <
      (input.moleculeGraph.neighborFinset center).card := by
  have derived := input.executableLocalizedRerootChildren_declarative cursor
  have lengthIntended : (input.executableLocalizedRerootChildren cursor).length =
      (input.intendedLocalizedRerootChildFrames cursor).length := by
    rw [← derived.1, List.length_map]
  have notDuplicate :=
    input.isDuplicateLeaf_eq_false_of_provenance_real cursor.occurrence.1.node meaning.1
  have intendedEq : input.intendedLocalizedRerootChildFrames cursor =
      (input.localizedRerootNeighborFrames (fuel := carrierFuel) cursor.occurrence.1).filter
        fun frame => frame.address != previous.1.address := by
    unfold intendedLocalizedRerootChildFrames
    rw [if_neg (by simpa using notDuplicate), previousEq]
  have previousNeighbor : previous.1 ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel) cursor.occurrence.1 := by
    unfold LocalizedRerootCursorValid at valid
    rw [previousEq] at valid
    exact input.mem_localizedRerootNeighborFrames_symm previous cursor.occurrence.1 valid
  have rootLength := rootChildren_length_eq_degree input singleBonded enough cursor.occurrence
    center meaning
  have rootFrames := input.simpleBond_realCenter_childFrames cursor.occurrence meaning.1
    _ (input.localizedRerootChildren?_eq_some_executable
      ({ occurrence := cursor.occurrence, previous? := none } :
        input.LocalizedRerootCursor carrierFuel))
  have neighborLength : (input.localizedRerootNeighborFrames (fuel := carrierFuel)
      cursor.occurrence.1).length = (input.moleculeGraph.neighborFinset center).card := by
    rw [← rootFrames.1, List.length_map, rootLength]
  rw [lengthIntended, intendedEq, ← neighborLength]
  apply List.length_filter_lt_length_iff_exists.mpr
  exact ⟨previous.1, previousNeighbor, by simp⟩

/-! ## Three-coordinate occurrences refuse in both operation records -/

theorem frame_none_of_degree_ne_four (singleBonded : input.moleculeGraph.SimpleBonded)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (center : input.Atom) (meaning : RealAtomNode input target.1.node center)
    (notFour : (input.moleculeGraph.neighborFinset center).card ≠ 4) :
    input.localizedNoDoubleFourLigandFrameExec? target = none := by
  have length := rootChildren_length_eq_degree input singleBonded (Nat.le_succ _) target center
    meaning
  unfold localizedNoDoubleFourLigandFrameExec?
  rw [executableLocalizedRerootChildren?_eq_some]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [dif_neg (by omega)]

/-! ## The report identification without the three-coordinate premise -/

section Report

open RawLocalizedChildNodeTransport LocalizedMarkedConfigurationTransport

variable (single : input.moleculeGraph.SimpleBonded) (fallback : CompleteLigandRule5Key)
  (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)

include agreement admissible supported in
/-- The certified degree of a looked-up atom is its raw degree. -/
theorem lookup_degree (node : RawNode) (valid : node.atom < mol.atomCount)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (found : lookup? input node = some target) :
    ∃ current, target.1.node.current? = some current ∧
      (input.moleculeGraph.neighborFinset current).card =
        (mol.canonicalIncidentNeighbors node.atom).length := by
  have corresponds := lookup?_sound input node target found
  obtain ⟨current, currentEq⟩ := NodeCorresponds.exists_current corresponds
  have currentVal : current.val = node.atom := by
    have mapped := corresponds.current
    rw [currentEq] at mapped
    exact Option.some.inj mapped
  have currentIndex : current = localizedIndexOf mol input agreement ⟨node.atom, valid⟩ :=
    Fin.ext currentVal
  have permutation := canonicalIncidentNeighbors_perm_sortedNeighborAtoms mol input agreement
    admissible.1.1 admissible.1.2 supported ⟨node.atom, valid⟩
  have length := permutation.length_eq
  refine ⟨current, currentEq, ?_⟩
  rw [currentIndex]
  simpa [sortedNeighborAtoms] using length.symm

include agreement admissible supported in
/-- **Agreement at every reached framed occurrence**, three-coordinate frames included: those
have no certified four-ligand frame, so both records refuse. -/
theorem agreeAt_general
    (node : RawNode) (reached : Reached mol node) (atoms : List Nat)
    (frame : frameAtoms? mol node = some atoms) :
    AgreeAt (operations input mol) (independentOperations input single fallback mol) node := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have rawSingle := raw_single mol input agreement wellFormed unique supported single
  have rawReal := LocalizedMarkedGeneratedSnapshotSupport.real_of_frame mol node atoms frame
  have valid := reached_atom_valid mol wellFormed node reached
  rcases frame_atoms_perm_neighbors mol wellFormed rawSingle node reached atoms frame with
    ⟨four, _⟩ | ⟨three, _⟩
  · have detected : ∀ target, lookup? input node = some target → RealDetected input target :=
      fun target found => ⟨lookup?_real input node target found rawReal,
        carrier_detected_of_raw_degree mol input agreement wellFormed unique supported rawSingle
          target node valid (lookup?_sound input node target found) four⟩
    exact ⟨fun state => ordinary_eq_independent input single mol state node detected,
      fun state mark => marked_shape_eq_independent input single fallback mol state
        node mark detected⟩
  · have noFrame : ∀ target, lookup? input node = some target →
        input.localizedNoDoubleFourLigandFrameExec? target = none := by
      intro target found
      obtain ⟨current, currentEq, degree⟩ := lookup_degree input mol agreement admissible
        supported node valid target found
      exact frame_none_of_degree_ne_four input single target current
        ⟨lookup?_real input node target found rawReal, currentEq⟩ (by omega)
    refine ⟨fun state => ?_, fun state mark => ?_⟩
    · change LocalizedMarkedRetainedOperations.ordinary input mol state node =
        independentOrdinary input single mol state node
      unfold LocalizedMarkedRetainedOperations.ordinary independentOrdinary
      cases found : lookup? input node with
      | none => rfl
      | some target =>
          simp only [Option.bind_eq_bind, Option.bind_some, frame, noFrame target found,
            Option.bind_none]
    · change (marked? input mol state node mark).map shape =
        (independentMarked input single fallback mol state node mark).map shape
      unfold marked? markedWithLayout? independentMarked
      by_cases bound : mark < input.certified.input.molecule.atomCount
      · rw [dif_pos bound, dif_pos bound]
        cases found : lookup? input node with
        | none => rfl
        | some target =>
            simp only [Option.bind_eq_bind, Option.bind_some, frame, noFrame target found,
              Option.bind_none]
      · rw [dif_neg bound, dif_neg bound]

include agreement admissible supported in
/-- **Generated facts at every depth, geometry, state and inherited context**, on every
intake-agreeing admitted localized single-bond input: arbitrary branching atoms (including
three-coordinate nitrogen), rings and ring duplicates. -/
theorem facts_eq_independent_general :
    ∀ depth geom state ctx node, Reached mol node →
      facts mol (operations input mol) depth geom state ctx node =
        facts mol (independentOperations input single fallback mol) depth geom state ctx node :=
  facts_congr mol _ _ (agreeAt_general input single fallback mol agreement admissible supported)

include agreement admissible supported in
/-- Every recursive auxiliary descriptor, including inherited contexts. -/
theorem descriptor_eq_independent_general (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : RawNode) (reached : Reached mol node) :
    descriptor? mol (operations input mol) depth geom state ctx node =
      descriptor? mol (independentOperations input single fallback mol) depth geom state ctx node :=
  descriptor_congr mol _ _ (agreeAt_general input single fallback mol agreement admissible
    supported) depth geom state ctx node reached

include agreement admissible supported in
/-- **The whole detected-centre report** of the experimental evaluator is the report of the
independent operations, on the same domain. -/
theorem assign_eq_independent_general (geom : Geometry) :
    assign mol (operations input mol) geom =
      assign mol (independentOperations input single fallback mol) geom :=
  assign_congr mol _ _ (agreeAt_general input single fallback mol agreement admissible supported)
    geom

end Report

end TetraStereo.OneCenter.LocalizedMarkedRetainedReachDegree

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedReachDegree.rerootChildren_current_iff_adjacent
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedReachDegree.rerootChildren_current_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedReachDegree.rootChildren_length_eq_degree
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedReachDegree.exec_length_lt_degree
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedReachDegree.frame_none_of_degree_ne_four
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedReachDegree.lookup_degree
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedReachDegree.agreeAt_general
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedReachDegree.facts_eq_independent_general
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedReachDegree.descriptor_eq_independent_general
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedReachDegree.assign_eq_independent_general
