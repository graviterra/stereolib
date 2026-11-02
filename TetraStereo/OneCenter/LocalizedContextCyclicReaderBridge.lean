import TetraStereo.OneCenter.LocalizedContextMolecularReader
import TetraStereo.OneCenter.LocalizedRuleMajorOwnMolecularEvidence
import TetraStereo.OneCenter.LocalizedOccurrenceCarrierCoverage
import TetraStereo.OneCenter.LocalizedCarrierRealCenterActiveSimple
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 2048
set_option linter.unnecessarySimpa false

/-!
# Simple-bonded reader bridge, including ring-duplicate leaves

`LocalizedContextMolecularReader` and `LocalizedRuleMajorOwnMolecularEvidence` identify the
molecular reader with the context walk and with the generated reference state only after assuming
`Acyclic`. That hypothesis is used to pretend every carrier occurrence is a real simple path.
On a ring it is false: a zero-copy step back to an atom already on the branch is a
`ringDuplicate` leaf.

Under `SimpleBonded` alone, every carrier occurrence is still a `LegitimateOccurrence`, and the
only duplicate kind is that one ring step. Copy index zero is forced by bond order one, so the
multiple-bond arm is empty. Real provenance is exactly the `SimpleOccurrencePath` branch. The
molecular unit is the stored root plus `history.reverse.tail`. Accepted path uniqueness
(`simpleOccurrencePath_address_unique`) identifies those units. The current atom does not: two
simple branches may end at the same atom.

The generated descriptor map and `molecularReader` are the revised evaluator's own
`referenceState`. No desired map is assumed. A non-real cursor, including a ring-duplicate leaf
whose occurrence reading is `unavailable`, contributes `LocalizedAuxiliaryLabel` `none`. Real
cursors still read `readContext` along the actual `rerootWalk`, and one executable reroot step
covers the backward pop, a fresh append, and a ring append. This file does not identify retained
path length with physical shortest distance, and it does not retune `R`/`S`/`r`/`s` or reference
counts.
-/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

open DeclarativeCIP

variable (input : CertifiedLocalizedCIPInput)

private theorem history_eq_of_reverse_tail_eq
    {left right : List input.Atom} {root : input.Atom}
    (leftLast : left.getLast? = some root) (rightLast : right.getLast? = some root)
    (tailEq : left.reverse.tail = right.reverse.tail) :
    left = right := by
  have leftNe : left ≠ [] := by
    intro empty
    simp [empty] at leftLast
  have rightNe : right ≠ [] := by
    intro empty
    simp [empty] at rightLast
  have leftHead : left.reverse.head? = some root := by
    have reverseLast : left.reverse.head? = left.getLast? := by
      simpa using (List.getLast?_reverse (l := left.reverse)).symm
    exact reverseLast.trans leftLast
  have rightHead : right.reverse.head? = some root := by
    have reverseLast : right.reverse.head? = right.getLast? := by
      simpa using (List.getLast?_reverse (l := right.reverse)).symm
    exact reverseLast.trans rightLast
  have leftCons : left.reverse = root :: left.reverse.tail := by
    cases reverseEq : left.reverse with
    | nil =>
        exact absurd (by simpa using congrArg List.reverse reverseEq) leftNe
    | cons head tail =>
        have headEq : head = root := by
          have headSome : left.reverse.head? = some head := by simp [reverseEq]
          exact Option.some.inj (headSome.symm.trans leftHead)
        rw [headEq]
        rfl
  have rightCons : right.reverse = root :: right.reverse.tail := by
    cases reverseEq : right.reverse with
    | nil =>
        exact absurd (by simpa using congrArg List.reverse reverseEq) rightNe
    | cons head tail =>
        have headEq : head = root := by
          have headSome : right.reverse.head? = some head := by simp [reverseEq]
          exact Option.some.inj (headSome.symm.trans rightHead)
        rw [headEq]
        rfl
  have reverseEq : left.reverse = right.reverse := by
    rw [leftCons, rightCons, tailEq]
  simpa using congrArg List.reverse reverseEq

private theorem simpleOccurrencePath_node_eq_of_history_eq
    {root : input.Atom} {leftNode rightNode : OfficialCIPNode input.Atom}
    {leftAddress rightAddress : List Nat}
    (left : SimpleOccurrencePath input root leftNode leftAddress)
    (right : SimpleOccurrencePath input root rightNode rightAddress)
    (historyEq : leftNode.history = rightNode.history) :
    leftNode = rightNode := by
  obtain ⟨leftCurrent, _, leftCurrentEq, leftHead, leftProv, _, _, _⟩ :=
    input.simpleOccurrencePath_realPathNode left
  obtain ⟨rightCurrent, _, rightCurrentEq, rightHead, rightProv, _, _, _⟩ :=
    input.simpleOccurrencePath_realPathNode right
  have currentEq : leftCurrent = rightCurrent := by
    have heads : some leftCurrent = some rightCurrent := by
      rw [← leftHead, historyEq, rightHead]
    exact Option.some.inj heads
  cases leftNode with
  | mk leftCurrent? leftHistory leftProvenance =>
      cases rightNode with
      | mk rightCurrent? rightHistory rightProvenance =>
          have leftSome : leftCurrent? = some leftCurrent := leftCurrentEq
          have rightSome : rightCurrent? = some rightCurrent := rightCurrentEq
          subst currentEq
          subst historyEq
          subst leftSome
          subst rightSome
          subst leftProv
          subst rightProv
          rfl

/-- A duplicate leaf has no executable child, so a derivation rooted there is the leaf frame. -/
private theorem declarativeLocalizedOccurrenceSubtree_eq_of_duplicateLeaf
    {root : input.Atom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode input.Atom} {occurrence : input.LocalizedCIPOccurrenceFrame}
    (duplicate : node.isDuplicateLeaf = true)
    (derived : input.DeclarativeLocalizedOccurrenceSubtree root path fuel node occurrence) :
    occurrence = { root := root, address := path, node := node, remaining := fuel } := by
  cases derived with
  | subtreeRoot => rfl
  | subtreeDescendant childAtSlot _descendant =>
      have childPresent := List.fst_mem_of_mem_zipIdx childAtSlot
      have empty : input.executableOfficialCIPChildren node = [] := by
        simp [executableOfficialCIPChildren, duplicate]
      rw [empty] at childPresent
      cases childPresent

/-- The zip index of `extend next 0` is the raw zero-copy slot. Equal extended nodes cannot hide
a positive copy: `childProvenance` sends every positive index to `multipleBondDuplicate`. -/
private theorem executableChildCopySlot_eq_zipIdx
    (node : OfficialCIPNode input.Atom) (next : input.Atom) (slot : Nat)
    (nonduplicate : node.isDuplicateLeaf = false)
    (childAtSlot :
      (node.extend next 0, slot) ∈ (input.executableOfficialCIPChildren node).zipIdx) :
    slot = input.executableOfficialChildCopySlot node next 0 := by
  have atIndex : (input.executableOfficialCIPChildren node)[slot]? =
      some (node.extend next 0) :=
    (List.mk_mem_zipIdx_iff_getElem?).mp childAtSlot
  unfold executableOfficialCIPChildren at atIndex
  rw [if_neg (by simpa using nonduplicate)] at atIndex
  rw [List.getElem?_map] at atIndex
  cases rawObserved : (input.executableOfficialChildCopies node)[slot]? with
  | none => simp [rawObserved] at atIndex
  | some raw =>
      obtain ⟨rawNext, rawIndex⟩ := raw
      have nodeEq : node.extend rawNext rawIndex = node.extend next 0 := by
        apply Option.some.inj
        simpa [rawObserved, Option.map_some] using atIndex
      have nextEq : rawNext = next := by
        have currents := congrArg OfficialCIPNode.current? nodeEq
        simpa only [OfficialCIPNode.extend_current?, Option.some.injEq] using currents
      have indexZero : rawIndex = 0 := by
        have provenances := congrArg OfficialCIPNode.provenance nodeEq
        rw [OfficialCIPNode.extend_provenance, OfficialCIPNode.extend_provenance] at provenances
        by_cases zero : rawIndex = 0
        · exact zero
        · rw [nextEq] at provenances
          rw [OfficialCIPNode.childProvenance_copy_pos node next zero] at provenances
          by_cases seen : next ∈ node.history
          · rw [OfficialCIPNode.childProvenance_ring_duplicate node next seen] at provenances
            exact OfficialCIPNodeProvenance.noConfusion provenances
          · rw [OfficialCIPNode.childProvenance_real node next seen] at provenances
            exact OfficialCIPNodeProvenance.noConfusion provenances
      have rawEq : (input.executableOfficialChildCopies node)[slot]? = some (next, 0) := by
        rw [rawObserved, nextEq, indexZero]
      obtain ⟨bound, elemEq⟩ := List.getElem?_eq_some_iff.mp rawEq
      have idx := List.Nodup.idxOf_getElem (input.executableOfficialChildCopies_nodup node)
        slot bound
      rw [elemEq] at idx
      simpa only [executableOfficialChildCopySlot] using idx.symm

/-- Every bounded derivation below a simple path is a simple path or one terminal ring step.
`SimpleBonded` forces the executable copy index to zero, so a positive multiple-bond copy cannot
appear. A ring step is a leaf: its derivation cannot continue. -/
private theorem declarativeLocalizedOccurrenceSubtree_legitimate
    (singleBonded : input.moleculeGraph.SimpleBonded) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat} {fuel : Nat}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (path : SimpleOccurrencePath input root node address)
    (derived : input.DeclarativeLocalizedOccurrenceSubtree root address fuel node occurrence) :
    LegitimateOccurrence input root occurrence.node occurrence.address := by
  induction derived with
  | subtreeRoot _address _fuel _node =>
      exact LegitimateOccurrence.simple path
  | @subtreeDescendant address fuel node child slot occurrence childAtSlot below ih =>
      obtain ⟨current, _, currentObserved, _, _, _, _, _⟩ :=
        input.simpleOccurrencePath_realPathNode path
      have childPresent := List.fst_mem_of_mem_zipIdx childAtSlot
      have nonduplicate : node.isDuplicateLeaf = false :=
        input.isDuplicateLeaf_eq_false_of_provenance_real node
          (input.simpleOccurrencePath_provenance path)
      unfold executableOfficialCIPChildren at childPresent
      rw [if_neg (by simpa using nonduplicate), List.mem_map] at childPresent
      obtain ⟨copy, copyPresent, childIdentity⟩ := childPresent
      obtain ⟨next, copyIndex⟩ := copy
      change node.extend next copyIndex = child at childIdentity
      obtain ⟨adjacent, bound⟩ :=
        input.mem_executableOfficialChildCopies_adjacent_bound node current next copyIndex
          currentObserved copyPresent
      have oneBond := singleBonded current next adjacent
      have copyZero : copyIndex = 0 := by
        have boundOne : copyIndex < 1 := by simpa [oneBond] using bound
        omega
      subst copyIndex
      have notParent : node.parent? ≠ some next := by
        intro parentSome
        cases parentObserved : node.parent? with
        | none =>
            rw [parentObserved] at parentSome
            simp at parentSome
        | some parent =>
            have parentEq : parent = next :=
              Option.some.inj (by simpa [parentObserved] using parentSome)
            exact input.not_parent_of_zero_mem_executableOfficialChildCopies node next parent
              copyPresent parentObserved parentEq.symm
      have childEq : child = node.extend next 0 := childIdentity.symm
      have slotEq : slot = input.executableOfficialChildCopySlot node next 0 :=
        input.executableChildCopySlot_eq_zipIdx node next slot nonduplicate
          (by
            have rewritten : (node.extend next 0, slot) ∈
                (input.executableOfficialCIPChildren node).zipIdx := by
              rw [← childEq]
              exact childAtSlot
            exact rewritten)
      by_cases seen : next ∈ node.history
      · have childProv : child.provenance =
            OfficialCIPNodeProvenance.ringDuplicate (node.duplicateRootDistance next) := by
          rw [childEq]
          exact input.legitimateOccurrence_ring_provenance seen
        have childDuplicate : child.isDuplicateLeaf = true :=
          input.isDuplicateLeaf_eq_true_of_ring_provenance child childProv
        have occurrenceEq :=
          input.declarativeLocalizedOccurrenceSubtree_eq_of_duplicateLeaf childDuplicate below
        have ringLegit : LegitimateOccurrence input root (node.extend next 0)
            (address ++ [input.executableOfficialChildCopySlot node next 0]) :=
          LegitimateOccurrence.ring path currentObserved adjacent notParent seen
        rw [occurrenceEq, childEq, slotEq]
        exact ringLegit
      · have stepPath : SimpleOccurrencePath input root child (address ++ [slot]) := by
          have stepped : SimpleOccurrencePath input root (node.extend next 0)
              (address ++ [input.executableOfficialChildCopySlot node next 0]) :=
            SimpleOccurrencePath.step path currentObserved adjacent notParent seen
          rw [← childEq, ← slotEq] at stepped
          exact stepped
        exact ih stepPath

/-- **Carrier classification at copy index zero.**  Every finite carrier occurrence of a
single-bond molecule is a simple path or one terminal ring-duplicate step. -/
theorem carrierOccurrence_legitimate
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    LegitimateOccurrence input occurrence.1.root occurrence.1.node occurrence.1.address := by
  have derived := (input.mem_localizedOccurrences_iff fuel occurrence.1).mp occurrence.2
  exact input.declarativeLocalizedOccurrenceSubtree_legitimate singleBonded
    (SimpleOccurrencePath.root (root := occurrence.1.root))
    (input.declarativeLocalizedOccurrence_as_rootSubtree derived)

/-- The same classification, projected to provenance. Multiple-bond duplicates do not occur. -/
theorem carrierOccurrence_provenance_simple_or_ring
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∨
      ∃ distance, occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.ringDuplicate distance := by
  have legit := input.carrierOccurrence_legitimate singleBonded occurrence
  revert legit
  generalize occurrence.1.node = node
  generalize occurrence.1.address = address
  intro legit
  cases legit with
  | simple path =>
      exact Or.inl (input.simpleOccurrencePath_provenance path)
  | @ring parent _address _current next _path _observed _adjacent _notParent seen =>
      exact Or.inr ⟨parent.duplicateRootDistance next,
        input.legitimateOccurrence_ring_provenance seen⟩
  | @multiple _parent _address current next copyIndex _path _observed adjacent bound positive =>
      have oneBond := singleBonded current next adjacent
      have copyLt : copyIndex < 1 := by simpa [oneBond] using bound
      exact False.elim (by omega)

/-- **Real provenance is the simple-path branch.**  A ring leaf is `ringDuplicate`, so a carrier
occurrence whose provenance is `realAtom` is the `SimpleOccurrencePath` carried by the copy-zero
classification, not merely an `ActiveSimple` history. -/
theorem simpleOccurrencePath_of_carrier_real
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (real : occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    SimpleOccurrencePath input occurrence.1.root occurrence.1.node occurrence.1.address := by
  have legit := input.carrierOccurrence_legitimate singleBonded occurrence
  revert real
  revert legit
  generalize occurrence.1.node = node
  generalize occurrence.1.address = address
  intro legit
  induction legit with
  | simple path =>
      intro _
      exact path
  | @ring _parent _address _current _next _path _observed _adjacent _notParent seen =>
      intro real
      rw [input.legitimateOccurrence_ring_provenance seen] at real
      cases real
  | @multiple _parent _address _current _next _copyIndex _path _observed _adjacent _bound
      positive =>
      intro real
      rw [input.legitimateOccurrence_multiple_provenance positive] at real
      cases real

/-- Every legitimate history, simple or duplicate, still ends at the path root. The ring atom is
prepended; it does not replace the stored root. -/
theorem legitimateOccurrence_history_getLast
    {root : input.Atom} {node : OfficialCIPNode input.Atom} {address : List Nat}
    (occ : LegitimateOccurrence input root node address) :
    node.history.getLast? = some root := by
  cases occ with
  | simple path =>
      exact input.realPathNode_history_getLast (input.simpleOccurrencePath_realPathNode path)
  | @ring parent _address _current _next path _observed _adjacent _notParent _seen =>
      have parentLast :=
        input.realPathNode_history_getLast (input.simpleOccurrencePath_realPathNode path)
      rw [OfficialCIPNode.extend_history, List.getLast?_cons, parentLast]
      rfl
  | @multiple parent _address _current _next _copyIndex path _observed _adjacent _bound _positive =>
      have parentLast :=
        input.realPathNode_history_getLast (input.simpleOccurrencePath_realPathNode path)
      rw [OfficialCIPNode.extend_history, List.getLast?_cons, parentLast]
      rfl

/-- Carrier form of the root endpoint. It holds for ring-duplicate leaves as well as real nodes. -/
theorem carrierOccurrence_history_getLast_eq_root
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    occurrence.1.node.history.getLast? = some occurrence.1.root :=
  input.legitimateOccurrence_history_getLast
    (input.carrierOccurrence_legitimate singleBonded occurrence)

/-- `RealPathNode` records real-atom provenance. A ring or other non-real node is not one. -/
theorem not_realPathNode_of_not_realAtom
    {root : input.Atom} {node : OfficialCIPNode input.Atom}
    (notReal : node.provenance ≠ OfficialCIPNodeProvenance.realAtom) :
    ¬ input.RealPathNode root node := by
  intro real
  obtain ⟨_, _, _, _, provenance, _, _, _⟩ := real
  exact notReal provenance

private theorem legitimateOccurrence_address_eq_of_history_eq
    (singleBonded : input.moleculeGraph.SimpleBonded) {root : input.Atom}
    {leftNode rightNode : OfficialCIPNode input.Atom}
    {leftAddress rightAddress : List Nat}
    (left : LegitimateOccurrence input root leftNode leftAddress)
    (right : LegitimateOccurrence input root rightNode rightAddress)
    (historyEq : leftNode.history = rightNode.history) :
    leftAddress = rightAddress := by
  cases left with
  | simple leftPath =>
      cases right with
      | simple rightPath =>
          exact input.simpleOccurrencePath_address_unique leftPath rightPath
            (input.simpleOccurrencePath_node_eq_of_history_eq leftPath rightPath historyEq)
      | @ring parent _parentAddress _current next _path _observed _adjacent _notParent seen =>
          have nodup := input.simpleOccurrencePath_history_nodup leftPath
          have repeated : ¬ (parent.extend next 0).history.Nodup := by
            rw [OfficialCIPNode.extend_history]
            intro nodupCons
            exact (List.nodup_cons.mp nodupCons).1 seen
          exact False.elim (repeated (historyEq ▸ nodup))
      | @multiple _parent _address current next copyIndex _path _observed adjacent bound positive =>
          have oneBond := singleBonded current next adjacent
          have copyLt : copyIndex < 1 := by simpa [oneBond] using bound
          omega
  | @ring leftParent _leftAddress _leftCurrent leftNext leftPath _observed _adjacent _notParent
      leftSeen =>
      cases right with
      | simple rightPath =>
          have nodup := input.simpleOccurrencePath_history_nodup rightPath
          have repeated : ¬ (leftParent.extend leftNext 0).history.Nodup := by
            rw [OfficialCIPNode.extend_history]
            intro nodupCons
            exact (List.nodup_cons.mp nodupCons).1 leftSeen
          exact False.elim (repeated (historyEq.symm ▸ nodup))
      | @ring rightParent _rightAddress _rightCurrent rightNext rightPath _observed _adjacent
          _notParent _rightSeen =>
          have consEq : leftNext :: leftParent.history = rightNext :: rightParent.history := by
            simpa [OfficialCIPNode.extend_history] using historyEq
          have nextEq : leftNext = rightNext := (List.cons.inj consEq).1
          have parentHistoryEq : leftParent.history = rightParent.history :=
            (List.cons.inj consEq).2
          have parentNodeEq := input.simpleOccurrencePath_node_eq_of_history_eq leftPath rightPath
            parentHistoryEq
          have parentAddressEq := input.simpleOccurrencePath_address_unique leftPath rightPath
            parentNodeEq
          have slotEq : input.executableOfficialChildCopySlot leftParent leftNext 0 =
              input.executableOfficialChildCopySlot rightParent rightNext 0 := by
            rw [parentNodeEq, nextEq]
          rw [parentAddressEq, slotEq]
      | @multiple _parent _address current next copyIndex _path _observed adjacent bound positive =>
          have oneBond := singleBonded current next adjacent
          have copyLt : copyIndex < 1 := by simpa [oneBond] using bound
          omega
  | @multiple _parent _address current next copyIndex _path _observed adjacent bound positive =>
      have oneBond := singleBonded current next adjacent
      have copyLt : copyIndex < 1 := by simpa [oneBond] using bound
      omega

/-- **Occurrence units identify carrier occurrences by root and history.**  Equal
`molecularFrameUnit` values give the same root and the same `history.reverse.tail`. Every
simple-bonded history ends at that root, so the histories agree. `simpleOccurrencePath_address_unique`
then gives the same address on the real branch, and the one zero-copy ring slot gives it on a
duplicate leaf. A repeated ring history is not a simple history, so a ring leaf is never chosen in
place of the real visit. The current atom is not the key: this argument never calls
`localizedCIPOccurrence_current_injective_at_fixedRoot`. -/
theorem molecularFrameUnit_injective_on_simpleBonded_carrier
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (left right : input.LocalizedCIPOccurrence fuel)
    (unitEq : input.molecularFrameUnit left.1 = input.molecularFrameUnit right.1) :
    left = right := by
  have rootEq : left.1.root = right.1.root := congrArg OccurrenceUnit.root unitEq
  have tailEq : left.1.node.history.reverse.tail = right.1.node.history.reverse.tail :=
    congrArg OccurrenceUnit.path unitEq
  have leftLast := input.carrierOccurrence_history_getLast_eq_root singleBonded left
  have rightLast := input.carrierOccurrence_history_getLast_eq_root singleBonded right
  rw [← rootEq] at rightLast
  have historyEq : left.1.node.history = right.1.node.history :=
    input.history_eq_of_reverse_tail_eq leftLast rightLast tailEq
  have leftLegit := input.carrierOccurrence_legitimate singleBonded left
  have rightLegit := input.carrierOccurrence_legitimate singleBonded right
  rw [← rootEq] at rightLegit
  have addressEq : left.1.address = right.1.address :=
    input.legitimateOccurrence_address_eq_of_history_eq singleBonded leftLegit rightLegit historyEq
  have leftDerived := (input.mem_localizedOccurrences_iff fuel left.1).mp left.2
  have rightDerived := (input.mem_localizedOccurrences_iff fuel right.1).mp right.2
  exact Subtype.ext (input.declarativeLocalizedOccurrence_functional_at_root_address
    leftDerived rightDerived rootEq addressEq)

private theorem molecularFrameUnit_path_eq_append_of_history_cons
    {atom : input.Atom} {frame parent : input.LocalizedCIPOccurrenceFrame}
    (historyEq : frame.node.history = atom :: parent.node.history)
    (parentLast : parent.node.history.getLast? = some parent.root) :
    frame.node.history.reverse.tail = parent.node.history.reverse.tail ++ [atom] := by
  have reverseNe : parent.node.history.reverse ≠ [] := by
    intro empty
    have historyEmpty : parent.node.history = [] := by
      simpa using congrArg List.reverse empty
    simp [historyEmpty] at parentLast
  rw [historyEq, List.reverse_cons]
  exact List.tail_append_singleton_of_ne_nil reverseNe

private theorem incomingAtom?_append_singleton
    {root atom : input.Atom} (path : List input.Atom) :
    incomingAtom? root (path ++ [atom]) = some (OccurrenceUnit.atom ⟨root, path⟩) := by
  have lastEq : path.getLast? = path.reverse.head? := by
    simpa using (List.getLast?_reverse (l := path.reverse))
  cases reverseEq : path.reverse with
  | nil =>
      have pathEq : path = [] := by
        simpa using congrArg List.reverse reverseEq
      subst path
      simp [incomingAtom?, OccurrenceUnit.atom]
  | cons first rest =>
      simp [incomingAtom?, List.reverse_append, reverseEq, lastEq, OccurrenceUnit.atom]

/-- **One executable reroot step, without acyclicity.**  The source of an executable child is not
a duplicate leaf. Its history still ends at the stored root. The address-shortening neighbor is
the backward pop. An outward child, whether a fresh simple step or a ring-duplicate leaf, appends:
the repeated atom is not the stored parent, so `incomingAtom?` does not select it. The ring child
need not be a `RealPathNode`. -/
theorem molecularFrameUnit_executableChild_rerootStep_of_simpleBonded
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (source child : input.LocalizedRerootCursor fuel) {next : input.Atom}
    (nextObserved : child.occurrence.1.node.current? = some next)
    (present : child ∈ input.executableLocalizedRerootChildren source) :
    (input.molecularFrameUnit child.occurrence.1).root =
        (input.molecularFrameUnit source.occurrence.1).root ∧
      (input.molecularFrameUnit child.occurrence.1).path =
        rerootStep (input.molecularFrameUnit source.occurrence.1).root
          (input.molecularFrameUnit source.occurrence.1).path next := by
  let sourceFrame := source.occurrence.1
  let childFrame := child.occurrence.1
  have sourceDerived : input.DeclarativeLocalizedOccurrence fuel sourceFrame :=
    (input.mem_localizedOccurrences_iff fuel sourceFrame).mp source.occurrence.2
  have childDerived : input.DeclarativeLocalizedOccurrence fuel childFrame :=
    (input.mem_localizedOccurrences_iff fuel childFrame).mp child.occurrence.2
  have childIntended : childFrame ∈ input.intendedLocalizedRerootChildFrames source := by
    rw [← input.executableLocalizedRerootChildren_map source]
    exact List.mem_map.mpr ⟨child, present, rfl⟩
  have sourceNonDuplicate : sourceFrame.node.isDuplicateLeaf = false := by
    by_cases duplicate : source.occurrence.1.node.isDuplicateLeaf = true
    · have childPresent := childIntended
      unfold intendedLocalizedRerootChildFrames at childPresent
      rw [if_pos duplicate] at childPresent
      cases childPresent
    · exact (Bool.not_eq_true _).mp duplicate
  have sourceLast : sourceFrame.node.history.getLast? = some sourceFrame.root :=
    input.carrierOccurrence_history_getLast_eq_root singleBonded source.occurrence
  have childNeighbor : childFrame ∈
      input.localizedRerootNeighborFrames (fuel := fuel) sourceFrame := by
    simp [intendedLocalizedRerootChildFrames] at childIntended
    rcases childIntended with ⟨_notDuplicate, childInNeighbors⟩
    cases previousEq : source.previous? with
    | none => simpa [previousEq] using childInNeighbors
    | some previous =>
        have filtered : childFrame ∈
            (input.localizedRerootNeighborFrames (fuel := fuel) sourceFrame).filter
              (fun frame => frame.address != previous.1.address) := by
          simpa [previousEq] using childInNeighbors
        exact (List.mem_filter.mp filtered).1
  have neighborShape :=
    (input.mem_localizedRerootNeighborFrames_iff (fuel := fuel) sourceFrame childFrame).mp
      childNeighbor
  have rootEq : childFrame.root = sourceFrame.root := neighborShape.2.1
  have addressCases :
      (childFrame.address.length + 1 = sourceFrame.address.length ∧
        childFrame.address = sourceFrame.address.dropLast) ∨
      (sourceFrame.address.length + 1 = childFrame.address.length ∧
        sourceFrame.address = childFrame.address.dropLast) :=
    neighborShape.2.2
  constructor
  · exact rootEq
  · rcases addressCases with ⟨_lengthEq, childAddressEq⟩ | ⟨_lengthEq, sourceAddressEq⟩
    · have sourceNonroot : sourceFrame.address ≠ [] := by
        intro empty
        rw [empty] at _lengthEq
        simp at _lengthEq
      obtain ⟨certificate⟩ :=
        input.exists_localizedParentFrameHistory source.occurrence sourceNonroot
      have certificateDerived :
          input.DeclarativeLocalizedOccurrence fuel certificate.parent.1 :=
        (input.mem_localizedOccurrences_iff fuel certificate.parent.1).mp certificate.parent.2
      have frameEq : childFrame = certificate.parent.1 :=
        input.declarativeLocalizedOccurrence_functional_at_root_address childDerived
          certificateDerived (rootEq.trans certificate.parent_root.symm)
          (childAddressEq.trans certificate.parent_address.symm)
      have parentLast : certificate.parent.1.node.history.getLast? =
          some certificate.parent.1.root :=
        input.carrierOccurrence_history_getLast_eq_root singleBonded certificate.parent
      have sourcePathEq :
          (input.molecularFrameUnit sourceFrame).path =
            (input.molecularFrameUnit certificate.parent.1).path ++ [certificate.current] :=
        molecularFrameUnit_path_eq_append_of_history_cons input certificate.history_eq parentLast
      have childHead : childFrame.node.history.head? = some next := by
        have currentHead :=
          input.declarativeLocalizedOccurrence_node_history_head_eq_current childDerived
        rw [nextObserved] at currentHead
        exact currentHead
      have childLast : childFrame.node.history.getLast? = some childFrame.root :=
        input.carrierOccurrence_history_getLast_eq_root singleBonded child.occurrence
      have childAtom : (input.molecularFrameUnit childFrame).atom = next :=
        input.molecularFrameUnit_atom_eq_current childFrame childHead childLast
      have parentAtom : (input.molecularFrameUnit certificate.parent.1).atom = next := by
        rw [frameEq] at childAtom
        exact childAtom
      have incoming :
          incomingAtom? (input.molecularFrameUnit sourceFrame).root
            (input.molecularFrameUnit sourceFrame).path = some next := by
        rw [sourcePathEq]
        have atomEq :
            OccurrenceUnit.atom ⟨(input.molecularFrameUnit sourceFrame).root,
              (input.molecularFrameUnit certificate.parent.1).path⟩ = next := by
          change OccurrenceUnit.atom
            ⟨certificate.parent.1.root,
              (input.molecularFrameUnit certificate.parent.1).path⟩ = next at parentAtom
          simpa [OccurrenceUnit.atom, certificate.parent_root] using parentAtom
        rw [incomingAtom?_append_singleton]
        exact congrArg some atomEq
      have incoming' : incomingAtom? (input.molecularFrameUnit sourceFrame).root
          ((input.molecularFrameUnit certificate.parent.1).path ++ [certificate.current]) =
            some next := by
        simpa [sourcePathEq] using incoming
      have childPathEq :
          (input.molecularFrameUnit childFrame).path =
            (input.molecularFrameUnit certificate.parent.1).path := by
        simpa [frameEq]
      have stepEq : rerootStep (input.molecularFrameUnit sourceFrame).root
          ((input.molecularFrameUnit certificate.parent.1).path ++ [certificate.current]) next =
            (input.molecularFrameUnit certificate.parent.1).path := by
        simp [rerootStep, incoming']
      calc
        (input.molecularFrameUnit childFrame).path =
            (input.molecularFrameUnit certificate.parent.1).path := childPathEq
        _ = rerootStep (input.molecularFrameUnit sourceFrame).root
              ((input.molecularFrameUnit certificate.parent.1).path ++
                [certificate.current]) next := stepEq.symm
        _ = rerootStep (input.molecularFrameUnit sourceFrame).root
              (input.molecularFrameUnit sourceFrame).path next := by
          rw [← sourcePathEq]
    · have childNonempty : childFrame.address ≠ [] := by
        intro empty
        rw [empty] at _lengthEq
        simp at _lengthEq
      let slot := childFrame.address.getLast childNonempty
      have childAddressEq' : childFrame.address = sourceFrame.address ++ [slot] := by
        rw [sourceAddressEq]
        exact (List.dropLast_append_getLast (l := childFrame.address) childNonempty).symm
      obtain ⟨childNode, childAtSlot, childFrameEq⟩ :=
        input.declarativeLocalizedOccurrence_immediate_child sourceDerived childDerived
          rootEq slot childAddressEq'
      have childNodeCurrent : childNode.current? = some next := by
        have currentEq := nextObserved
        change childFrame.node.current? = some next at currentEq
        rw [childFrameEq] at currentEq
        exact currentEq
      have childNodePresent : childNode ∈ input.executableOfficialCIPChildren sourceFrame.node :=
        List.fst_mem_of_mem_zipIdx childAtSlot
      unfold executableOfficialCIPChildren at childNodePresent
      rw [if_neg (by simpa [OfficialCIPNode.isDuplicateLeaf] using sourceNonDuplicate),
        List.mem_map] at childNodePresent
      rcases childNodePresent with ⟨⟨copyAtom, copyIndex⟩, copyPresent, childIdentity⟩
      have currentObserved : sourceFrame.node.current?.isSome = true :=
        input.declarativeLocalizedOccurrence_node_current_isSome sourceDerived
      obtain ⟨sourceCurrent, sourceCurrentObserved⟩ :=
        Option.isSome_iff_exists.mp currentObserved
      have adjacentBound := input.mem_executableOfficialChildCopies_adjacent_bound
        sourceFrame.node sourceCurrent copyAtom copyIndex sourceCurrentObserved copyPresent
      have oneBond := singleBonded sourceCurrent copyAtom adjacentBound.1
      have copyZero : copyIndex = 0 := by
        have copyBound : copyIndex < 1 := by simpa [oneBond] using adjacentBound.2
        omega
      have copyAtomEq : copyAtom = next := by
        rw [← childIdentity] at childNodeCurrent
        simp at childNodeCurrent
        exact childNodeCurrent
      have childNodeEq : childNode = sourceFrame.node.extend next 0 := by
        calc
          childNode = sourceFrame.node.extend copyAtom copyIndex := childIdentity.symm
          _ = sourceFrame.node.extend next 0 := by rw [copyAtomEq, copyZero]
      have childHistoryEq : childFrame.node.history = next :: sourceFrame.node.history := by
        rw [childFrameEq, childNodeEq, OfficialCIPNode.extend_history]
      have childPathEq :
          (input.molecularFrameUnit childFrame).path =
            (input.molecularFrameUnit sourceFrame).path ++ [next] :=
        molecularFrameUnit_path_eq_append_of_history_cons input childHistoryEq sourceLast
      have sourceParentIncoming :
          incomingAtom? (input.molecularFrameUnit sourceFrame).root
            (input.molecularFrameUnit sourceFrame).path ≠ some next := by
        by_cases sourceNonroot : sourceFrame.address = []
        · have pathLength :=
            input.molecularFrameUnit_path_length_eq_address_length source.occurrence
          have pathLengthZero : (input.molecularFrameUnit sourceFrame).path.length = 0 := by
            calc
              (input.molecularFrameUnit sourceFrame).path.length = sourceFrame.address.length :=
                pathLength
              _ = 0 := by simp [sourceNonroot]
          have sourcePathEmpty : (input.molecularFrameUnit sourceFrame).path = [] := by
            cases path : (input.molecularFrameUnit sourceFrame).path with
            | nil => rfl
            | cons head tail => simp [path] at pathLengthZero
          simp [sourcePathEmpty, incomingAtom?]
        · obtain ⟨certificate⟩ :=
            input.exists_localizedParentFrameHistory source.occurrence sourceNonroot
          have parentLast : certificate.parent.1.node.history.getLast? =
              some certificate.parent.1.root :=
            input.carrierOccurrence_history_getLast_eq_root singleBonded certificate.parent
          have sourcePathEq :
              (input.molecularFrameUnit sourceFrame).path =
                (input.molecularFrameUnit certificate.parent.1).path ++
                  [certificate.current] :=
            molecularFrameUnit_path_eq_append_of_history_cons input certificate.history_eq
              parentLast
          have parentHead : certificate.parent.1.node.history.head? =
              certificate.parent.1.node.current? :=
            input.declarativeLocalizedOccurrence_node_history_head_eq_current
              ((input.mem_localizedOccurrences_iff fuel certificate.parent.1).mp
                certificate.parent.2)
          have parentCurrentSome := input.declarativeLocalizedOccurrence_node_current_isSome
            ((input.mem_localizedOccurrences_iff fuel certificate.parent.1).mp
              certificate.parent.2)
          obtain ⟨parentCurrent, parentCurrentObserved⟩ :=
            Option.isSome_iff_exists.mp parentCurrentSome
          have parentHead' : certificate.parent.1.node.history.head? = some parentCurrent := by
            rw [parentCurrentObserved] at parentHead
            exact parentHead
          have parentAtom : (input.molecularFrameUnit certificate.parent.1).atom =
              parentCurrent :=
            input.molecularFrameUnit_atom_eq_current certificate.parent.1 parentHead' parentLast
          have incoming :
              incomingAtom? (input.molecularFrameUnit sourceFrame).root
                (input.molecularFrameUnit sourceFrame).path = some parentCurrent := by
            rw [sourcePathEq, incomingAtom?_append_singleton]
            have atomEq :
                OccurrenceUnit.atom ⟨(input.molecularFrameUnit sourceFrame).root,
                  (input.molecularFrameUnit certificate.parent.1).path⟩ = parentCurrent := by
              change OccurrenceUnit.atom
                ⟨certificate.parent.1.root,
                  (input.molecularFrameUnit certificate.parent.1).path⟩ = parentCurrent
                at parentAtom
              simpa [OccurrenceUnit.atom, certificate.parent_root] using parentAtom
            exact congrArg some atomEq
          have sourceParent : sourceFrame.node.parent? = some parentCurrent := by
            cases parentHistory : certificate.parent.1.node.history with
            | nil => simp [parentHistory] at parentLast
            | cons first rest =>
                have firstEq : first = parentCurrent := by
                  simpa [parentHistory] using parentHead'
                subst first
                have sourceHistory : sourceFrame.node.history =
                    certificate.current :: parentCurrent :: rest := by
                  calc
                    sourceFrame.node.history =
                        certificate.current :: certificate.parent.1.node.history :=
                      certificate.history_eq
                    _ = certificate.current :: parentCurrent :: rest := by
                      rw [parentHistory]
                unfold OfficialCIPNode.parent?
                rw [sourceHistory]
          have copyNotParent := input.not_parent_of_zero_mem_executableOfficialChildCopies
            sourceFrame.node copyAtom parentCurrent (by simpa [copyZero] using copyPresent)
              sourceParent
          have nextNeParent : next ≠ parentCurrent := by
            intro equal
            apply copyNotParent
            simpa [copyAtomEq] using equal
          intro equal
          rw [incoming] at equal
          exact nextNeParent (Option.some.inj equal).symm
      have stepEq : rerootStep (input.molecularFrameUnit sourceFrame).root
          (input.molecularFrameUnit sourceFrame).path next =
            (input.molecularFrameUnit sourceFrame).path ++ [next] := by
        simp [rerootStep, sourceParentIncoming]
      simpa [sourceFrame, childFrame] using childPathEq.trans stepEq.symm

/-- Pointwise context correspondence for an arbitrary target and cursor. Real provenance reads
`readContext` at the supplied walk. Every other provenance, including a ring duplicate whose
reading is `unavailable`, returns that reading's localized label, which is `none`. Acyclicity is
not used. The only alignment premise is the cursor's own molecular unit. -/
theorem molecularReader_eq_contextLabel_of_actual_walk
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (cursor : input.LocalizedRerootCursor fuel)
    (unit : DetectedOccurrence input.moleculeGraph) (steps : List input.Atom)
    (targetUnit : input.molecularFrameUnit target.1 = unit.1)
    (cursorUnit : input.molecularFrameUnit cursor.occurrence.1 =
      ⟨unit.1.root, rerootWalk unit.1.root unit.1.path steps⟩) :
    input.molecularReader descriptorMap target cursor =
      if cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom then
        (readContext input.moleculeGraph descriptorMap unit steps).toLocalizedLabel
      else
        OccurrenceReading.unavailable.toLocalizedLabel := by
  by_cases real : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom
  · rw [if_pos real]
    have targetDepth := input.molecularFrameUnit_path_length_eq_address_length target
    have cursorDepth := input.molecularFrameUnit_path_length_eq_address_length cursor.occurrence
    have targetDepth' : target.1.address.length = unit.1.path.length := by
      calc
        target.1.address.length = (input.molecularFrameUnit target.1).path.length :=
          targetDepth.symm
        _ = unit.1.path.length := by
          simpa using congrArg (fun u : OccurrenceUnit input.Atom => u.path.length) targetUnit
    have cursorRoot : cursor.occurrence.1.root = unit.1.root := by
      have rootProjection := congrArg OccurrenceUnit.root cursorUnit
      simpa using rootProjection
    exact input.molecularReader_eq_readContext_of_walk descriptorMap target cursor unit steps
      targetUnit targetDepth' cursorRoot cursorUnit (by
        calc
          cursor.occurrence.1.address.length =
              (input.molecularFrameUnit cursor.occurrence.1).path.length := cursorDepth.symm
          _ = (rerootWalk unit.1.root unit.1.path steps).length := by
            simpa using congrArg (fun u : OccurrenceUnit input.Atom => u.path.length) cursorUnit)
      real
  · rw [if_neg real, input.molecularReader_eq_none_of_not_real descriptorMap target cursor real]
    simp [OccurrenceReading.toLocalizedLabel]

/-- The same correspondence after one executable child step. Backward pop, fresh append, and ring
append are all `rerootStep`; only the real results consult `readContext`. -/
theorem molecularReader_eq_contextLabel_of_executableChild
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (source child : input.LocalizedRerootCursor fuel) {next : input.Atom}
    (nextObserved : child.occurrence.1.node.current? = some next)
    (present : child ∈ input.executableLocalizedRerootChildren source)
    (unit : DetectedOccurrence input.moleculeGraph) (steps : List input.Atom)
    (targetUnit : input.molecularFrameUnit target.1 = unit.1)
    (sourceUnit : input.molecularFrameUnit source.occurrence.1 =
      ⟨unit.1.root, rerootWalk unit.1.root unit.1.path steps⟩) :
    input.molecularReader descriptorMap target child =
      if child.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom then
        (readContext input.moleculeGraph descriptorMap unit (steps ++ [next])).toLocalizedLabel
      else
        OccurrenceReading.unavailable.toLocalizedLabel := by
  have step := input.molecularFrameUnit_executableChild_rerootStep_of_simpleBonded singleBonded
    source child nextObserved present
  have sourceRoot : (input.molecularFrameUnit source.occurrence.1).root = unit.1.root := by
    rw [sourceUnit]
  have sourcePath : (input.molecularFrameUnit source.occurrence.1).path =
      rerootWalk unit.1.root unit.1.path steps := by
    rw [sourceUnit]
  have childRoot : (input.molecularFrameUnit child.occurrence.1).root = unit.1.root :=
    step.1.trans sourceRoot
  have childPath : (input.molecularFrameUnit child.occurrence.1).path =
      rerootWalk unit.1.root unit.1.path (steps ++ [next]) := by
    calc
      (input.molecularFrameUnit child.occurrence.1).path =
          rerootStep (input.molecularFrameUnit source.occurrence.1).root
            (input.molecularFrameUnit source.occurrence.1).path next := step.2
      _ = rerootStep unit.1.root (rerootWalk unit.1.root unit.1.path steps) next := by
          rw [sourceRoot, sourcePath]
      _ = rerootWalk unit.1.root unit.1.path (steps ++ [next]) := by
          rw [rerootWalk_append unit.1.root unit.1.path steps [next]]
          simp [rerootWalk]
  have childUnit : input.molecularFrameUnit child.occurrence.1 =
      ⟨unit.1.root, rerootWalk unit.1.root unit.1.path (steps ++ [next])⟩ := by
    have eta : input.molecularFrameUnit child.occurrence.1 =
        ⟨(input.molecularFrameUnit child.occurrence.1).root,
          (input.molecularFrameUnit child.occurrence.1).path⟩ := rfl
    rw [eta, childRoot, childPath]
  exact input.molecularReader_eq_contextLabel_of_actual_walk descriptorMap target child unit
    (steps ++ [next]) targetUnit childUnit

end CertifiedLocalizedCIPInput

namespace LocalizedRuleMajorReference
open DeclarativeCIP CertifiedLocalizedCIPInput
noncomputable section
open scoped Classical

/-- On a single-bond carrier, `Classical.choose` returns the unique occurrence of a unit. The
uniqueness theorem ranges over ring leaves as well as real nodes, because the choice itself does. -/
theorem actualReferenceOccurrenceOf_eq_some_iff_of_simpleBonded
    (input : Input) (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (unit : OccurrenceUnit input.certified.Atom) (occurrence : Occurrence input) :
    actualReferenceOccurrenceOf input unit = some occurrence ↔
      input.certified.molecularFrameUnit occurrence.1 = unit := by
  constructor
  · intro chosen
    unfold actualReferenceOccurrenceOf at chosen
    split at chosen
    · rename_i present
      have chosenEq : Classical.choose present = occurrence := Option.some.inj chosen
      rw [← chosenEq]
      exact Classical.choose_spec present
    · simp at chosen
  · intro unitEq
    have present : ∃ occurrence : Occurrence input,
        input.certified.molecularFrameUnit occurrence.1 = unit := ⟨occurrence, unitEq⟩
    have chosenEq : Classical.choose present = occurrence :=
      input.certified.molecularFrameUnit_injective_on_simpleBonded_carrier singleBonded
        (Classical.choose present) occurrence
        (by rw [Classical.choose_spec present, unitEq])
    unfold actualReferenceOccurrenceOf
    rw [dif_pos present, chosenEq]

/-- A non-real carrier occurrence has no tetrahedral descriptor source, so the generated
reference state at that occurrence is `none`. -/
theorem referenceState_none_of_not_real (input : Input) (occurrence : Occurrence input)
    (notReal : occurrence.1.node.provenance ≠ OfficialCIPNodeProvenance.realAtom) :
    referenceState input occurrence = none := by
  rw [← reference_fixed input occurrence]
  apply input.certified.ruleMajorDescriptor?_eq_none_of_no_center occurrence
    (input.certified.localizedDependencyView (referenceState input) occurrence)
  unfold localizedOccurrenceDescriptorCenter? realTetrahedralCenterAtNode?
  rw [if_neg notReal]

private theorem referenceState_eq_none_of_real_not_detected (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) (occurrence : Occurrence input)
    (real : occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (notDetected : ¬ IsDetectedCenter input.certified.moleculeGraph
      (input.certified.molecularFrameUnit occurrence.1).atom) :
    referenceState input occurrence = none := by
  have path := input.certified.simpleOccurrencePath_of_carrier_real singleBonded occurrence real
  obtain ⟨current, _, currentObserved, head, _, _, _, _⟩ :=
    input.certified.simpleOccurrencePath_realPathNode path
  have last := input.certified.realPathNode_history_getLast
    (input.certified.simpleOccurrencePath_realPathNode path)
  have frameAtom : (input.certified.molecularFrameUnit occurrence.1).atom = current :=
    input.certified.molecularFrameUnit_atom_eq_current occurrence.1 head last
  have notCenter : current ∉ input.certified.tetrahedralCenterSet := by
    intro present
    apply notDetected
    rw [frameAtom]
    exact (input.certified.moleculeGraph.isTetrahedralCenter_iff_neighborFinset_card current).mp
      ((input.certified.moleculeGraph.mem_tetrahedralCenterSet current).mp present)
  rw [← reference_fixed input occurrence]
  apply input.certified.ruleMajorDescriptor?_eq_none_of_no_center occurrence
    (input.certified.localizedDependencyView (referenceState input) occurrence)
  unfold localizedOccurrenceDescriptorCenter? realTetrahedralCenterAtNode?
  rw [if_pos real]
  simp only [currentObserved, tetrahedralCenterAt?, dif_neg notCenter]

/-- Exact readback of the generated map. The occurrence may be any carrier node of the unit; the
single-bond identification supplies it without `Acyclic`. -/
theorem descriptorMap_readback_of_simpleBonded (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (unit : DetectedOccurrence input.certified.moleculeGraph) (occurrence : Occurrence input)
    (unitEq : input.certified.molecularFrameUnit occurrence.1 = unit.1) :
    (descriptorMap input unit).bind Descriptor.toLocalizedLabel = referenceState input occurrence := by
  have chosen :=
    (actualReferenceOccurrenceOf_eq_some_iff_of_simpleBonded input singleBonded unit.1
      occurrence).2 unitEq
  unfold descriptorMap
  rw [chosen]
  exact option_map_localizedAuxiliaryDescriptor_bind _

/-- **The molecular reader is the generated reader** at every target and every queried cursor of a
single-bond molecule. Real detected cursors read `referenceState` through `descriptorMap`. Real
non-centers and non-real cursors, including ring-duplicate leaves, are `none` on both sides.
No acyclicity, availability, or externally supplied map agreement is assumed. -/
theorem molecularReader_eq_generatedReader_of_simpleBonded (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : input.certified.LocalizedCIPOccurrence (carrierFuel input)) :
    input.certified.molecularReader (descriptorMap input) target =
      input.certified.localizedDependencyLabel target
        (input.certified.localizedDependencyView (referenceState input) target) := by
  funext cursor
  unfold CertifiedLocalizedCIPInput.molecularReader
  by_cases dependency : input.certified.LocalizedDepthDependency cursor.occurrence target
  · unfold CertifiedLocalizedCIPInput.localizedDependencyLabel
    simp only [CertifiedLocalizedCIPInput.molecularView,
      CertifiedLocalizedCIPInput.localizedDependencyView, dif_pos dependency]
    by_cases real : cursor.occurrence.1.node.provenance = .realAtom
    · rw [if_pos real]
      by_cases detected : IsDetectedCenter input.certified.moleculeGraph
          (input.certified.molecularFrameUnit cursor.occurrence.1).atom
      · rw [dif_pos detected]
        exact descriptorMap_readback_of_simpleBonded input singleBonded
          ⟨input.certified.molecularFrameUnit cursor.occurrence.1, detected⟩ cursor.occurrence rfl
      · rw [dif_neg detected]
        exact (referenceState_eq_none_of_real_not_detected input singleBonded cursor.occurrence
          real detected).symm
    · rw [if_neg real]
      exact (referenceState_none_of_not_real input cursor.occurrence real).symm
  · unfold CertifiedLocalizedCIPInput.localizedDependencyLabel
    simp only [dif_neg dependency]

theorem molecularView_eq_generatedView_of_simpleBonded (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) (target : Occurrence input) :
    input.certified.molecularView (descriptorMap input) target =
      input.certified.localizedDependencyView (referenceState input) target := by
  funext source dependency
  have observed := congrFun
    (molecularReader_eq_generatedReader_of_simpleBonded input singleBonded target)
    (⟨source, none⟩ : input.certified.LocalizedRerootCursor (carrierFuel input))
  simpa only [molecularReader, localizedDependencyLabel, dif_pos dependency] using observed

end
end LocalizedRuleMajorReference
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.carrierOccurrence_legitimate
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.carrierOccurrence_provenance_simple_or_ring
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.simpleOccurrencePath_of_carrier_real
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.legitimateOccurrence_history_getLast
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.carrierOccurrence_history_getLast_eq_root
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.not_realPathNode_of_not_realAtom
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.molecularFrameUnit_injective_on_simpleBonded_carrier
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.molecularFrameUnit_executableChild_rerootStep_of_simpleBonded
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.molecularReader_eq_contextLabel_of_actual_walk
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.molecularReader_eq_contextLabel_of_executableChild
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.actualReferenceOccurrenceOf_eq_some_iff_of_simpleBonded
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState_none_of_not_real
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.descriptorMap_readback_of_simpleBonded
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.molecularReader_eq_generatedReader_of_simpleBonded
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.molecularView_eq_generatedView_of_simpleBonded
