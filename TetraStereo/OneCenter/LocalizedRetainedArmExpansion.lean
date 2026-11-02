import TetraStereo.OneCenter.DeclarativeCIPRetainedOccurrenceCarrier
import TetraStereo.OneCenter.DeclarativeCIPRetainedCutArm
import TetraStereo.OneCenter.LocalizedContextBranchStages
import TetraStereo.OneCenter.LocalizedContextCyclicReaderBridge
import TetraStereo.OneCenter.LocalizedOccurrenceCarrierCoverage
import TetraStereo.OneCenter.LocalizedRerootFuelCompleteness
import TetraStereo.OneCenter.LocalizedRealizedTreeCutEmbedding
import TetraStereo.OneCenter.LocalizedRealizedTreeCutEquivalence
import TetraStereo.OneCenter.LocalizedActualMolecularEvidenceRefinement
import TetraStereo.OneCenter.LocalizedRetainedContextObservationReadback
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

/-!
# Actual context arms and the predecessor-cut carrier

`cutRetainedArm` keeps the focus component of the retained carrier after the incoming
predecessor's reroot-subtree is deleted. `retainedArm` is the uncut full reroot and is not the
target graph. The actual arm is the rule-major expansion of an executable child. That cursor
keeps `previous? = some` of the target occurrence; the expansion filters that predecessor and
the cursor is not rebuilt.

A ring-duplicate child is proved to be the one-node cut from its actual carrier parent.
For a real child, this module identifies the actual incoming anchor. Fuel at least the atom
count places every simple path and one terminal ring step in the carrier. Correspondence
between a real arm and the whole kept component remains a downstream obligation. These
foundation results assume neither acyclicity, a fresh-root expansion, nor a supplied isomorphism.
-/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

open DeclarativeCIP
open DeclarativeCIP.RetainedOccurrenceCarrier
open DeclarativeCIP.RetainedCutArm
open LocalizedCumulativeDecoratedTree
open TetraStereo.OneCenter.Rule4aTableBridge

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput)

private theorem firstIndexOf?_eq_some_idxOf {α : Type} [DecidableEq α]
    (atom : α) (path : List α) (present : atom ∈ path) :
    firstIndexOf? atom path = some (path.idxOf atom) := by
  induction path with
  | nil =>
      simp at present
  | cons head tail ih =>
      by_cases headEq : head = atom
      · subst headEq
        rw [firstIndexOf?_cons_self, List.idxOf_cons_eq _ rfl]
      · have tailPresent : atom ∈ tail := by
          rcases List.mem_cons.mp present with rfl | hmem
          · exact absurd rfl headEq
          · exact hmem
        have tailEq := ih tailPresent
        rw [firstIndexOf?, if_neg headEq, tailEq, List.idxOf_cons_ne _ headEq]
        simp

private theorem duplicateRootDistance_eq_idxOf
    (node : OfficialCIPNode input.Atom) (atom : input.Atom)
    (present : atom ∈ node.history.reverse) :
    node.duplicateRootDistance atom = node.history.reverse.idxOf atom := by
  unfold OfficialCIPNode.duplicateRootDistance
  rw [firstIndexOf?_eq_some_idxOf atom node.history.reverse present]
  simp

private theorem parent?_eq_reverse_penultimate
    (node : OfficialCIPNode input.Atom) :
    node.parent? = node.history.reverse.dropLast.getLast? := by
  cases historyEq : node.history with
  | nil => simp [OfficialCIPNode.parent?, historyEq]
  | cons atom rest =>
      cases rest with
      | nil => simp [OfficialCIPNode.parent?, historyEq]
      | cons previous more =>
          simp [OfficialCIPNode.parent?, historyEq, List.reverse_cons]

private theorem carrierHistory_ne_nil
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    occurrence.1.node.history ≠ [] := by
  intro empty
  have last := input.carrierOccurrence_history_getLast_eq_root singleBonded occurrence
  simp [empty] at last

/-- Carrier node read off a simple-bonded occurrence. Real nodes use the reversed history.
Ring nodes split off the closure atom and keep the simple prefix. -/
def occurrenceCarrierNode
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) : CarrierNode input.Atom :=
  if occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom then
    .real occurrence.1.node.history.reverse
  else
    .ring occurrence.1.node.history.tail.reverse
      (occurrence.1.node.history.head (input.carrierHistory_ne_nil singleBonded occurrence))

private theorem simpleHistory_reverse_simpleFrom
    {root : input.Atom} {node : OfficialCIPNode input.Atom} {address : List Nat}
    (path : SimpleOccurrencePath input root node address) :
    SimpleFrom input.moleculeGraph root node.history.reverse ∧
      node.current? = node.history.reverse.getLast? := by
  induction path with
  | root =>
      simp [OfficialCIPNode.root, SimpleFrom.root_path]
  | @step parent address current next parentPath currentObserved adjacent notParent fresh ih =>
      obtain ⟨parentSimple, parentCurrent⟩ := ih
      have reverseStep : (parent.extend next 0).history.reverse =
          parent.history.reverse ++ [next] := by
        simp [OfficialCIPNode.extend_history, List.reverse_cons]
      have freshReverse : next ∉ parent.history.reverse := by
        intro member
        exact fresh ((List.mem_reverse.mp member))
      have lastParent : parent.history.reverse.getLast? = some current := by
        rw [← parentCurrent, currentObserved]
      have extended : SimpleFrom input.moleculeGraph root
          (parent.history.reverse ++ [next]) :=
        (SimpleFrom.append_iff parentSimple).2
          ⟨⟨current, lastParent, adjacent⟩, freshReverse⟩
      refine ⟨by simpa [reverseStep] using extended, ?_⟩
      simp [OfficialCIPNode.extend_current?, OfficialCIPNode.extend_history, List.reverse_cons]

private theorem simpleFrom_exists_path_aux
    {root : input.Atom} (n : Nat) :
    ∀ {path : List input.Atom}, path.length = n →
      SimpleFrom input.moleculeGraph root path →
      ∃ node address, SimpleOccurrencePath input root node address ∧
        node.history.reverse = path ∧ node.current? = path.getLast? := by
  induction n with
  | zero =>
      intro path hlen simple
      exact (SimpleFrom.ne_nil simple (List.length_eq_zero_iff.mp hlen)).elim
  | succ n ih =>
      intro path hlen simple
      cases path with
      | nil =>
          simp at hlen
      | cons head tail =>
          cases tail with
          | nil =>
              have headRoot : head = root := ChainFrom.singleton simple.1
              exact ⟨OfficialCIPNode.root root, [], SimpleOccurrencePath.root, by
                simp [OfficialCIPNode.root, headRoot]⟩
          | cons second rest =>
              have long : 1 < (head :: second :: rest).length := by simp
              have prefixSimple := SimpleFrom.dropLast simple long
              have prefixLen : (head :: second :: rest).dropLast.length = n := by
                simpa [List.length_dropLast] using hlen
              obtain ⟨parent, address, parentPath, parentReverse, parentCurrent⟩ :=
                ih prefixLen prefixSimple
              have prefixNe : (head :: second :: rest).dropLast ≠ [] := by
                simp
              let next := (head :: second :: rest).getLast (by simp)
              have split : head :: second :: rest =
                  (head :: second :: rest).dropLast ++ [next] :=
                (List.dropLast_append_getLast (by simp)).symm
              obtain ⟨current, _prefixChain, currentLast, adjacent⟩ :=
                ChainFrom.snoc_inv (split ▸ simple.1) prefixNe
              have currentObserved : parent.current? = some current := by
                rw [parentCurrent, currentLast]
              have fresh : next ∉ (head :: second :: rest).dropLast := by
                intro member
                have nodupAppend : ((head :: second :: rest).dropLast ++ [next]).Nodup :=
                  split ▸ simple.2
                have nodupSwap : List.Nodup (next :: (head :: second :: rest).dropLast) := by
                  simpa [List.singleton_append] using
                    (List.nodup_append_comm.mp nodupAppend)
                exact (List.nodup_cons.mp nodupSwap).1 member
              have freshHistory : next ∉ parent.history := by
                intro member
                exact fresh (parentReverse ▸ List.mem_reverse.mpr member)
              have notParent : parent.parent? ≠ some next := by
                intro parentSome
                cases historyEq : parent.history with
                | nil =>
                    simp [OfficialCIPNode.parent?, historyEq] at parentSome
                | cons atom more =>
                    cases more with
                    | nil =>
                        simp [OfficialCIPNode.parent?, historyEq] at parentSome
                    | cons previous extra =>
                        simp [OfficialCIPNode.parent?, historyEq] at parentSome
                        exact freshHistory (by simp [historyEq, parentSome])
              have stepped : SimpleOccurrencePath input root (parent.extend next 0)
                  (address ++ [input.executableOfficialChildCopySlot parent next 0]) :=
                SimpleOccurrencePath.step parentPath currentObserved adjacent notParent
                  freshHistory
              refine ⟨parent.extend next 0,
                address ++ [input.executableOfficialChildCopySlot parent next 0], stepped, ?_, ?_⟩
              · rw [OfficialCIPNode.extend_history, List.reverse_cons, parentReverse, ← split]
              · rw [OfficialCIPNode.extend_current?, split,
                  List.getLast?_append_of_ne_nil _ (by simp)]
                simp

private theorem simpleFrom_exists_path
    {root : input.Atom} {path : List input.Atom}
    (simple : SimpleFrom input.moleculeGraph root path) :
    ∃ node address, SimpleOccurrencePath input root node address ∧
      node.history.reverse = path ∧ node.current? = path.getLast? :=
  input.simpleFrom_exists_path_aux path.length rfl simple

/-- Every simple outer path is an occurrence at every fuel at least the atom count. -/
theorem exists_occurrence_of_simpleFrom
    {root : input.Atom} {path : List input.Atom}
    (simple : SimpleFrom input.moleculeGraph root path) {fuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ fuel) :
    ∃ occurrence : input.LocalizedCIPOccurrence fuel,
      occurrence.1.root = root ∧
        occurrence.1.node.history.reverse = path ∧
        occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  obtain ⟨node, address, pathNode, reverseEq, _current⟩ :=
    input.simpleFrom_exists_path simple
  have legit : LegitimateOccurrence input root node address :=
    LegitimateOccurrence.simple pathNode
  have addressBound : address.length ≤ fuel := by
    have addressAtoms := input.legitimateOccurrence_address_length_le_atomCount legit
    omega
  let frame : input.LocalizedCIPOccurrenceFrame :=
    { root := root
      address := address
      node := node
      remaining := fuel + 1 - address.length }
  refine ⟨⟨frame,
      input.legitimateOccurrence_mem_localizedOccurrences_of_fuel legit addressBound⟩,
    rfl, reverseEq, input.simpleOccurrencePath_provenance pathNode⟩

private theorem ringFrom_exists_legitimate
    (_singleBonded : input.moleculeGraph.SimpleBonded)
    {root : input.Atom} {path : List input.Atom} {atom : input.Atom}
    (ring : CarrierNode.Valid input.moleculeGraph root (.ring path atom)) :
    ∃ parent address,
      SimpleOccurrencePath input root parent address ∧
        parent.history.reverse = path ∧
        parent.current? = path.getLast? ∧
        LegitimateOccurrence input root (parent.extend atom 0)
          (address ++ [input.executableOfficialChildCopySlot parent atom 0]) := by
  obtain ⟨parent, address, parentPath, reverseEq, currentEq⟩ :=
    input.simpleFrom_exists_path ring.1
  obtain ⟨⟨current, currentLast, adjacent⟩, member, notPenultimate⟩ := ring.2
  have currentObserved : parent.current? = some current := by
    rw [currentEq, currentLast]
  have visited : atom ∈ parent.history :=
    List.mem_reverse.mp (reverseEq.symm ▸ member)
  have histRev : parent.history = path.reverse := by
    simpa [List.reverse_reverse] using congrArg List.reverse reverseEq
  have notParent : parent.parent? ≠ some atom := by
    intro parentSome
    have pathNe : path ≠ [] := SimpleFrom.ne_nil ring.1
    have split : path = path.dropLast ++ [current] := by
      have lastEq : path.getLast pathNe = current := by
        apply Option.some_inj.mp
        rw [← List.getLast?_eq_some_getLast (l := path) pathNe, currentLast]
      simpa [lastEq] using (List.dropLast_append_getLast pathNe).symm
    have histShape : parent.history = current :: path.dropLast.reverse := by
      rw [histRev, split]
      simp [List.reverse_append]
    cases dropRev : path.dropLast.reverse with
    | nil =>
        simp [OfficialCIPNode.parent?, histShape, dropRev] at parentSome
    | cons second tail =>
        have secondEq : parent.parent? = some second := by
          simp [OfficialCIPNode.parent?, histShape, dropRev]
        have atomSecond : atom = second :=
          Option.some_inj.mp (parentSome.symm.trans secondEq)
        have penultimate : path.dropLast.getLast? = some atom := by
          rw [atomSecond]
          have headReverse : path.dropLast.getLast? = path.dropLast.reverse.head? := by
            conv_lhs => rw [← List.reverse_reverse (as := path.dropLast)]
            exact List.getLast?_reverse (l := path.dropLast.reverse)
          simpa [dropRev] using headReverse
        exact notPenultimate penultimate
  exact ⟨parent, address, parentPath, reverseEq, currentEq,
    LegitimateOccurrence.ring parentPath currentObserved adjacent notParent visited⟩

/-- Every terminal ring closure is an occurrence at every fuel at least the atom count. -/
theorem exists_occurrence_of_ring
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {root : input.Atom} {path : List input.Atom} {atom : input.Atom}
    (ring : CarrierNode.Valid input.moleculeGraph root (.ring path atom)) {fuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ fuel) :
    ∃ occurrence : input.LocalizedCIPOccurrence fuel,
      occurrence.1.root = root ∧
        occurrence.1.node.history = atom :: path.reverse ∧
        occurrence.1.node.provenance =
          OfficialCIPNodeProvenance.ringDuplicate (path.idxOf atom) := by
  obtain ⟨parent, address, parentPath, reverseEq, currentEq, legit⟩ :=
    input.ringFrom_exists_legitimate singleBonded ring
  have addressBound : (address ++
      [input.executableOfficialChildCopySlot parent atom 0]).length ≤ fuel := by
    have addressAtoms := input.legitimateOccurrence_address_length_le_atomCount legit
    omega
  have historyEq : (parent.extend atom 0).history = atom :: path.reverse := by
    rw [OfficialCIPNode.extend_history]
    congr 1
    simpa [List.reverse_reverse] using congrArg List.reverse reverseEq
  have distanceEq : parent.duplicateRootDistance atom = path.idxOf atom := by
    have present : atom ∈ parent.history.reverse := by
      rw [reverseEq]
      exact ring.2.2.1
    simpa [reverseEq] using input.duplicateRootDistance_eq_idxOf parent atom present
  have provenanceEq : (parent.extend atom 0).provenance =
      OfficialCIPNodeProvenance.ringDuplicate (path.idxOf atom) := by
    have visited : atom ∈ parent.history := by
      rw [← List.mem_reverse, reverseEq]
      exact ring.2.2.1
    rw [OfficialCIPNode.extend_provenance, OfficialCIPNode.childProvenance, distanceEq]
    simp [visited]
  let frame : input.LocalizedCIPOccurrenceFrame :=
    { root := root
      address := address ++ [input.executableOfficialChildCopySlot parent atom 0]
      node := parent.extend atom 0
      remaining := fuel + 1 - (address ++
        [input.executableOfficialChildCopySlot parent atom 0]).length }
  refine ⟨⟨frame,
      input.legitimateOccurrence_mem_localizedOccurrences_of_fuel legit addressBound⟩,
    rfl, historyEq, provenanceEq⟩

/-- A carrier ring duplicate is one `extend` of its simple prefix. -/
private theorem exists_carrier_ring_step
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) {distance : Nat}
    (ring : occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.ringDuplicate distance) :
    ∃ (parent : OfficialCIPNode input.Atom) (address : List Nat) (current next : input.Atom)
      (_parentPath : SimpleOccurrencePath input occurrence.1.root parent address),
      occurrence.1.node = parent.extend next 0 ∧
        parent.current? = some current ∧
        input.moleculeGraph.Adj current next ∧
        parent.parent? ≠ some next ∧
        next ∈ parent.history := by
  have legit := input.carrierOccurrence_legitimate singleBonded occurrence
  revert ring legit
  generalize hnode : occurrence.1.node = node
  generalize haddress : occurrence.1.address = address
  intro ring legit
  cases legit with
  | simple pathNode =>
      rw [input.simpleOccurrencePath_provenance pathNode] at ring
      cases ring
  | @ring parent prefixAddress current next parentPath currentObserved adjacent notParent seen =>
      exact ⟨parent, prefixAddress, current, next, parentPath, rfl, currentObserved, adjacent,
        notParent, seen⟩
  | @multiple parent prefixAddress current next copyIndex _parentPath _observed adjacent bound
      positive =>
      have oneBond := singleBonded current next adjacent
      have copyZero : copyIndex = 0 := by
        have boundLt := bound
        simp [oneBond] at boundLt
        exact boundLt
      exact False.elim (positive copyZero)

/-- The history-derived carrier node of a simple-bonded occurrence is valid, and its outer root
is the occurrence root. -/
theorem occurrenceCarrierNode_valid
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    CarrierNode.Valid input.moleculeGraph occurrence.1.root
      (input.occurrenceCarrierNode singleBonded occurrence) := by
  cases hprov : occurrence.1.node.provenance with
  | realAtom =>
      have pathNode := input.simpleOccurrencePath_of_carrier_real singleBonded occurrence hprov
      obtain ⟨simple, _⟩ := input.simpleHistory_reverse_simpleFrom pathNode
      simpa [occurrenceCarrierNode, hprov] using simple
  | ringDuplicate distance =>
      obtain ⟨parent, _address, current, next, parentPath, nodeEq, currentObserved, adjacent,
          notParent, seen⟩ :=
        input.exists_carrier_ring_step singleBonded occurrence hprov
      obtain ⟨prefixSimple, parentCurrent⟩ := input.simpleHistory_reverse_simpleFrom parentPath
      have historyEq : occurrence.1.node.history = next :: parent.history := by
        simp [nodeEq]
      have closure : RingClosure input.moleculeGraph parent.history.reverse next := by
        refine ⟨⟨current, ?_, adjacent⟩, List.mem_reverse.mpr seen, ?_⟩
        · rw [← parentCurrent, currentObserved]
        · rw [← input.parent?_eq_reverse_penultimate parent]
          exact notParent
      have validRing : CarrierNode.Valid input.moleculeGraph occurrence.1.root
          (.ring parent.history.reverse next) := ⟨prefixSimple, closure⟩
      have carrierEq : input.occurrenceCarrierNode singleBonded occurrence =
          .ring parent.history.reverse next := by
        rw [occurrenceCarrierNode]
        have notReal : occurrence.1.node.provenance ≠ OfficialCIPNodeProvenance.realAtom := by
          rw [hprov]
          intro bad
          cases bad
        rw [if_neg notReal]
        simp [historyEq]
      exact carrierEq.symm ▸ validRing
  | multipleBondDuplicate distance =>
      have split := input.carrierOccurrence_provenance_simple_or_ring singleBonded occurrence
      simp [hprov] at split
  | placeholder kind distance =>
      have split := input.carrierOccurrence_provenance_simple_or_ring singleBonded occurrence
      simp [hprov] at split

theorem occurrenceCarrierNode_label
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    CarrierNode.label (input.occurrenceCarrierNode singleBonded occurrence) =
      occurrence.1.node.toDeclarativeLabel := by
  cases hprov : occurrence.1.node.provenance with
  | realAtom =>
      have derived := (input.mem_localizedOccurrences_iff fuel occurrence.1).mp occurrence.2
      have headEq := input.declarativeLocalizedOccurrence_node_history_head_eq_current derived
      have lastEq : occurrence.1.node.history.reverse.getLast? =
          occurrence.1.node.history.head? :=
        List.getLast?_reverse (l := occurrence.1.node.history)
      simp [occurrenceCarrierNode, hprov, OfficialCIPNode.toDeclarativeLabel,
        OfficialCIPNodeProvenance.toDeclarative, CarrierNode.label, lastEq, headEq]
  | ringDuplicate distance =>
      obtain ⟨parent, _address, _current, next, _parentPath, nodeEq, _currentObserved, _adjacent,
          _notParent, seen⟩ :=
        input.exists_carrier_ring_step singleBonded occurrence hprov
      have historyEq : occurrence.1.node.history = next :: parent.history := by
        simp [nodeEq]
      have distanceEq : parent.duplicateRootDistance next =
          parent.history.reverse.idxOf next :=
        input.duplicateRootDistance_eq_idxOf parent next (List.mem_reverse.mpr seen)
      have prov : occurrence.1.node.provenance =
          OfficialCIPNodeProvenance.ringDuplicate (parent.history.reverse.idxOf next) := by
        rw [nodeEq, OfficialCIPNode.extend_provenance, OfficialCIPNode.childProvenance, distanceEq]
        simp [seen]
      have currentEq : occurrence.1.node.current? = some next := by
        simp [nodeEq]
      have carrierEq : input.occurrenceCarrierNode singleBonded occurrence =
          .ring parent.history.reverse next := by
        rw [occurrenceCarrierNode]
        have notReal : occurrence.1.node.provenance ≠ OfficialCIPNodeProvenance.realAtom := by
          rw [hprov]
          intro bad
          cases bad
        rw [if_neg notReal]
        simp [historyEq]
      simp [carrierEq, CarrierNode.label, OfficialCIPNode.toDeclarativeLabel,
        OfficialCIPNodeProvenance.toDeclarative, currentEq, prov]
  | multipleBondDuplicate distance =>
      have split := input.carrierOccurrence_provenance_simple_or_ring singleBonded occurrence
      simp [hprov] at split
  | placeholder kind distance =>
      have split := input.carrierOccurrence_provenance_simple_or_ring singleBonded occurrence
      simp [hprov] at split

theorem occurrenceCarrierNode_readback
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    occurrenceReadback occurrence.1.root
        (input.occurrenceCarrierNode singleBonded occurrence) =
      input.molecularFrameUnit occurrence.1 := by
  have fullEq : CarrierNode.fullAtoms
      (input.occurrenceCarrierNode singleBonded occurrence) =
      occurrence.1.node.history.reverse := by
    cases hprov : occurrence.1.node.provenance with
    | realAtom =>
        simp [occurrenceCarrierNode, hprov, CarrierNode.fullAtoms]
    | ringDuplicate distance =>
        obtain ⟨parent, _address, _current, next, _parentPath, nodeEq, _observed, _adjacent,
            _notParent, _seen⟩ :=
          input.exists_carrier_ring_step singleBonded occurrence hprov
        have historyEq : occurrence.1.node.history = next :: parent.history := by
          simp [nodeEq]
        have carrierEq : input.occurrenceCarrierNode singleBonded occurrence =
            .ring parent.history.reverse next := by
          rw [occurrenceCarrierNode]
          have notReal : occurrence.1.node.provenance ≠ OfficialCIPNodeProvenance.realAtom := by
            rw [hprov]
            intro bad
            cases bad
          rw [if_neg notReal]
          simp [historyEq]
        simp [carrierEq, CarrierNode.fullAtoms, historyEq, List.reverse_cons]
    | multipleBondDuplicate distance =>
        have split := input.carrierOccurrence_provenance_simple_or_ring singleBonded occurrence
        simp [hprov] at split
    | placeholder kind distance =>
        have split := input.carrierOccurrence_provenance_simple_or_ring singleBonded occurrence
        simp [hprov] at split
  have valid := input.occurrenceCarrierNode_valid singleBonded occurrence
  have read := occurrenceReadback_eq_history_reverse_tail valid
  calc
    occurrenceReadback occurrence.1.root
        (input.occurrenceCarrierNode singleBonded occurrence) =
        (⟨occurrence.1.root, (CarrierNode.fullAtoms
          (input.occurrenceCarrierNode singleBonded occurrence)).reverse.reverse.tail⟩ :
          OccurrenceUnit input.Atom) := read.symm
    _ = ⟨occurrence.1.root, occurrence.1.node.history.reverse.tail⟩ := by
      simp [fullEq, List.reverse_reverse]
    _ = input.molecularFrameUnit occurrence.1 := rfl

private theorem leaf_hierarchy_eq_nil
    (node : OfficialCIPNode input.Atom) {address : List Nat}
    (present : address ∈ (OfficialCIPSourceTree.node node []).hierarchyAddresses) :
    address = [] := by
  simp [OfficialCIPSourceTree.hierarchyAddresses, OfficialCIPSourceTree.occurrences,
    OfficialCIPSourceTree.forestOccurrences, List.inits] at present
  exact present

/-- A ring-duplicate executable child is the one-node predecessor cut.
`previous?` stays `some` of the target, and that target is the carrier parent. -/
theorem ringExecutableChild_retainedContextArmFaithful
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor fuel → Option LocalizedAuxiliaryLabel}
    (target cursor : input.LocalizedRerootCursor fuel)
    (childMem : cursor ∈ input.executableLocalizedRerootChildren target)
    (arm : input.RuleMajorContextArm fuel stage read cursor)
    {distance : Nat}
    (ring : cursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.ringDuplicate distance) :
    cursor.previous? = some target.occurrence ∧
    ∃ (path : List input.Atom) (atom : input.Atom)
      (ringValid : CarrierNode.Valid input.moleculeGraph cursor.occurrence.1.root
        (.ring path atom)),
      input.occurrenceCarrierNode singleBonded cursor.occurrence = .ring path atom ∧
      input.occurrenceCarrierNode singleBonded target.occurrence = .real path ∧
      RetainedContextArmFaithful input.moleculeGraph cursor.occurrence.1.root
        ⟨.ring path atom, ringValid⟩ (some ⟨.real path, ringValid.1⟩) CutAnchor.ringParent
        (ruleMajorTreeGraph arm.tree) := by
  have previousEq := input.executableLocalizedRerootChildren_previous target cursor childMem
  have targetReal :=
    input.retainedExecutableParent_realAtom singleBonded target cursor childMem
  have duplicate : cursor.occurrence.1.node.isDuplicateLeaf = true :=
    input.isDuplicateLeaf_eq_true_of_ring_provenance cursor.occurrence.1.node ring
  have intended : cursor.occurrence.1 ∈ input.intendedLocalizedRerootChildFrames target := by
    rw [← input.executableLocalizedRerootChildren_map target]
    exact List.mem_map.mpr ⟨cursor, childMem, rfl⟩
  have neighbor := input.mem_localizedRerootNeighborFrames_of_mem_intended target
    cursor.occurrence.1 intended
  have split := (input.mem_localizedRerootNeighborFrames_iff (fuel := fuel)
    target.occurrence.1 cursor.occurrence.1).mp neighbor
  rcases split.2 with ⟨rootEq, shorter | longer⟩
  · exfalso
    have targetNonempty : target.occurrence.1.address ≠ [] := by
      intro empty
      simp [empty] at shorter
    let slot := target.occurrence.1.address.getLast targetNonempty
    have addressEq : target.occurrence.1.address =
        cursor.occurrence.1.address ++ [slot] := by
      simpa [slot, shorter.2] using
        (List.dropLast_append_getLast targetNonempty).symm
    have cursorDerived :=
      (input.mem_localizedOccurrences_iff fuel cursor.occurrence.1).mp cursor.occurrence.2
    have targetDerived :=
      (input.mem_localizedOccurrences_iff fuel target.occurrence.1).mp target.occurrence.2
    obtain ⟨_childNode, childAt, _frameEq⟩ :=
      input.declarativeLocalizedOccurrence_immediate_child cursorDerived targetDerived
        rootEq.symm slot addressEq
    have presentNode := List.fst_mem_of_mem_zipIdx childAt
    unfold executableOfficialCIPChildren at presentNode
    rw [if_pos duplicate] at presentNode
    simp at presentNode
  · have cursorNonempty : cursor.occurrence.1.address ≠ [] := by
      intro empty
      simp [empty] at longer
    obtain ⟨certificate⟩ :=
      input.exists_localizedParentFrameHistory cursor.occurrence cursorNonempty
    have targetDerived :=
      (input.mem_localizedOccurrences_iff fuel target.occurrence.1).mp target.occurrence.2
    have parentDerived :=
      (input.mem_localizedOccurrences_iff fuel certificate.parent.1).mp certificate.parent.2
    have frameEq : target.occurrence.1 = certificate.parent.1 :=
      input.declarativeLocalizedOccurrence_functional_at_root_address targetDerived parentDerived
        (rootEq.symm.trans certificate.parent_root.symm)
        (longer.2.trans certificate.parent_address.symm)
    have historyEq : cursor.occurrence.1.node.history =
        certificate.current :: certificate.parent.1.node.history := certificate.history_eq
    have frameNode : target.occurrence.1.node = certificate.parent.1.node := by
      rw [frameEq]
    have targetNodeEq : input.occurrenceCarrierNode singleBonded target.occurrence =
        .real certificate.parent.1.node.history.reverse := by
      rw [occurrenceCarrierNode, if_pos targetReal]
      simp [frameNode]
    have cursorNodeEq : input.occurrenceCarrierNode singleBonded cursor.occurrence =
        .ring certificate.parent.1.node.history.reverse certificate.current := by
      rw [occurrenceCarrierNode]
      have notReal : cursor.occurrence.1.node.provenance ≠
          OfficialCIPNodeProvenance.realAtom := by
        rw [ring]
        intro bad
        cases bad
      rw [if_neg notReal]
      simp [historyEq]
    have ringValid : CarrierNode.Valid input.moleculeGraph cursor.occurrence.1.root
        (.ring certificate.parent.1.node.history.reverse certificate.current) :=
      cursorNodeEq ▸ input.occurrenceCarrierNode_valid singleBonded cursor.occurrence
    have carrierLabel := input.occurrenceCarrierNode_label singleBonded cursor.occurrence
    have carrierLabel' : CarrierNode.label
        (.ring certificate.parent.1.node.history.reverse certificate.current) =
        cursor.occurrence.1.node.toDeclarativeLabel := by
      rw [← cursorNodeEq]
      exact carrierLabel
    have executableNil : input.executableLocalizedRerootChildren cursor = [] := by
      simp [executableLocalizedRerootChildren, intendedLocalizedRerootChildFrames, duplicate]
    have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace arm.trace
    revert realizes
    generalize htree : arm.tree = tree
    intro realizes
    cases realizes with
    | mk source children sorted childrenComputed sourcePerm _childrenRealize =>
        have sourceEq : source = cursor := by
          have raw : (localizedRootTree input source (read source) sorted).source = cursor := by
            rw [← htree]
            exact arm.sourceEq
          unfold localizedRootTree at raw
          exact raw
        have childrenNil : children = [] := by
          have computed : input.localizedRerootChildren? cursor = some children := by
            rw [← sourceEq]
            exact childrenComputed
          have exec := input.localizedRerootChildren?_eq_some_executable cursor
          have same : some children = some (input.executableLocalizedRerootChildren cursor) :=
            computed.symm.trans exec
          rw [executableNil] at same
          exact Option.some_inj.mp same
        have sortedNil : sorted = [] := by
          have mapNil : sorted.map (fun child => child.source) = [] :=
            List.perm_nil.mp (childrenNil ▸ sourcePerm)
          cases sorted with
          | nil => rfl
          | cons child more => simp at mapNil
        let built := localizedRootTree input source (read source) sorted
        have sourceTree : toOfficialSourceTree
            (localizedRootTree input source (read source) sorted) =
            OfficialCIPSourceTree.node cursor.occurrence.1.node [] := by
          rw [sourceEq, sortedNil]
          simp [toOfficialSourceTree_localizedRootTree, toOfficialSourceTreeList_nil]
        let graph := ruleMajorTreeGraph built
        have onlyAddress : ∀ address : List Nat,
            address ∈ (toOfficialSourceTree built).hierarchyAddresses → address = [] := by
          intro address present
          rw [sourceTree] at present
          exact leaf_hierarchy_eq_nil input cursor.occurrence.1.node present
        let rootNode : graph.Node := ⟨[], (toOfficialSourceTree built).nil_mem_hierarchyAddresses⟩
        have onlyNode : ∀ node : graph.Node, node = rootNode := by
          intro node
          apply Subtype.ext
          exact onlyAddress node.1 node.2
        have labelEq : graph.label rootNode = cursor.occurrence.1.node.toDeclarativeLabel := by
          have reduced : graph.label rootNode =
              (toOfficialSourceTree built).source.toDeclarativeLabel := by
            change (toOfficialSourceTree built).declarativeLabel rootNode = _
            simp [OfficialCIPSourceTree.declarativeLabel, OfficialCIPSourceTree.sourceAtAddress?,
              OfficialCIPSourceTree.subtreeAt?, rootNode, OfficialCIPSourceTree.source]
          rw [reduced]
          have sourceNode : (toOfficialSourceTree built).source =
              cursor.occurrence.1.node := by
            rw [show toOfficialSourceTree built =
                toOfficialSourceTree (localizedRootTree input source (read source) sorted) from rfl,
              sourceTree]
            rfl
          rw [sourceNode]
        have noChild : ∀ parent node : graph.Node, ¬ graph.child parent node := by
          intro parent node hedge
          have parentNil : parent.1 = [] := onlyAddress parent.1 parent.2
          have nodeNil : node.1 = [] := onlyAddress node.1 node.2
          rcases hedge with ⟨slot, extendEq⟩
          simp [parentNil, nodeNil] at extendEq
        have faithful : RetainedContextArmFaithful input.moleculeGraph
            cursor.occurrence.1.root
            ⟨.ring certificate.parent.1.node.history.reverse certificate.current, ringValid⟩
            (some ⟨.real certificate.parent.1.node.history.reverse, ringValid.1⟩)
            CutAnchor.ringParent graph := by
          refine ⟨{
            toEquiv := {
              toFun := fun _ => rootNode
              invFun := fun _ => ⟨⟩
              left_inv := fun _ => rfl
              right_inv := fun node => (onlyNode node).symm
            }
            map_root := by
              apply Subtype.ext
              rfl
            map_child := by
              intro parent node
              constructor
              · intro hedge
                exact hedge.elim
              · intro hedge
                exact (noChild _ _ hedge).elim
            map_label := by
              intro node
              cases node
              simp [cutRetainedArm, ringTerminalArm]
              exact carrierLabel'.trans labelEq.symm
            map_depth := by
              intro node
              cases node
              simp [cutRetainedArm, ringTerminalArm]
              change (0 : Nat) = rootNode.1.length
              rfl
          }⟩
        exact ⟨previousEq, certificate.parent.1.node.history.reverse, certificate.current,
          ringValid, cursorNodeEq, targetNodeEq, faithful⟩

/-- The target occurrence is one reroot-child of a real executable focus.
The focus keeps its actual `previous?`; the target is that incoming predecessor. -/
theorem realExecutableChild_incomingArmChild
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (target cursor : input.LocalizedRerootCursor fuel)
    (childMem : cursor ∈ input.executableLocalizedRerootChildren target)
    (real : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    ∃ (path : List input.Atom)
      (hpath : SimpleFrom input.moleculeGraph cursor.occurrence.1.root path)
      (inc : Nodes input.moleculeGraph cursor.occurrence.1.root),
      input.occurrenceCarrierNode singleBonded cursor.occurrence = .real path ∧
        input.occurrenceCarrierNode singleBonded target.occurrence = inc.1 ∧
        armChild path ⟨.real path, hpath⟩ inc := by
  have targetReal :=
    input.retainedExecutableParent_realAtom singleBonded target cursor childMem
  have cursorCarrier : input.occurrenceCarrierNode singleBonded cursor.occurrence =
      .real cursor.occurrence.1.node.history.reverse := by
    rw [occurrenceCarrierNode, if_pos real]
  have hpath : SimpleFrom input.moleculeGraph cursor.occurrence.1.root
      cursor.occurrence.1.node.history.reverse := by
    have valid := input.occurrenceCarrierNode_valid singleBonded cursor.occurrence
    simpa [cursorCarrier] using valid
  have intended : cursor.occurrence.1 ∈ input.intendedLocalizedRerootChildFrames target := by
    rw [← input.executableLocalizedRerootChildren_map target]
    exact List.mem_map.mpr ⟨cursor, childMem, rfl⟩
  have neighbor := input.mem_localizedRerootNeighborFrames_of_mem_intended target
    cursor.occurrence.1 intended
  have split := (input.mem_localizedRerootNeighborFrames_iff (fuel := fuel)
    target.occurrence.1 cursor.occurrence.1).mp neighbor
  rcases split.2 with ⟨rootEq, shorter | longer⟩
  · have cursorNonempty : target.occurrence.1.address ≠ [] := by
      intro empty
      simp [empty] at shorter
    let slot := target.occurrence.1.address.getLast cursorNonempty
    have addressEq : target.occurrence.1.address =
        cursor.occurrence.1.address ++ [slot] := by
      simpa [slot, shorter.2] using (List.dropLast_append_getLast cursorNonempty).symm
    obtain ⟨certificate⟩ :=
      input.exists_localizedParentFrameHistory target.occurrence cursorNonempty
    have cursorDerived :=
      (input.mem_localizedOccurrences_iff fuel cursor.occurrence.1).mp cursor.occurrence.2
    have parentDerived :=
      (input.mem_localizedOccurrences_iff fuel certificate.parent.1).mp certificate.parent.2
    have frameEq : cursor.occurrence.1 = certificate.parent.1 :=
      input.declarativeLocalizedOccurrence_functional_at_root_address cursorDerived parentDerived
        (rootEq.trans certificate.parent_root.symm)
        (shorter.2.trans certificate.parent_address.symm)
    have historyEq : target.occurrence.1.node.history =
        certificate.current :: cursor.occurrence.1.node.history := by
      simpa [frameEq] using certificate.history_eq
    have pathEq : cursor.occurrence.1.node.history.reverse ++ [certificate.current] =
        target.occurrence.1.node.history.reverse := by
      simp [historyEq, List.reverse_cons]
    have targetCarrier : input.occurrenceCarrierNode singleBonded target.occurrence =
        .real target.occurrence.1.node.history.reverse := by
      rw [occurrenceCarrierNode, if_pos targetReal]
    have targetAtCursor : CarrierNode.Valid input.moleculeGraph cursor.occurrence.1.root
        (.real (cursor.occurrence.1.node.history.reverse ++ [certificate.current])) := by
      have extended : SimpleFrom input.moleculeGraph cursor.occurrence.1.root
          (cursor.occurrence.1.node.history.reverse ++ [certificate.current]) := by
        rw [pathEq]
        have validTarget := input.occurrenceCarrierNode_valid singleBonded target.occurrence
        have transported : CarrierNode.Valid input.moleculeGraph cursor.occurrence.1.root
            (input.occurrenceCarrierNode singleBonded target.occurrence) := by
          simpa [rootEq] using validTarget
        simpa [targetCarrier] using transported
      simpa using extended
    let inc : Nodes input.moleculeGraph cursor.occurrence.1.root :=
      ⟨.real (cursor.occurrence.1.node.history.reverse ++ [certificate.current]), targetAtCursor⟩
    have childRel : CarrierNode.Child (.real cursor.occurrence.1.node.history.reverse) inc.1 := by
      dsimp [inc]
      exact ⟨certificate.current, rfl⟩
    have incomingEq : input.occurrenceCarrierNode singleBonded target.occurrence = inc.1 := by
      rw [targetCarrier]
      dsimp [inc]
      exact congrArg CarrierNode.real pathEq.symm
    exact ⟨cursor.occurrence.1.node.history.reverse, hpath, inc, cursorCarrier, incomingEq,
      (armChild_focus_iff hpath inc).2 (Or.inl childRel)⟩
  · have cursorNonempty : cursor.occurrence.1.address ≠ [] := by
      intro empty
      simp [empty] at longer
    obtain ⟨certificate⟩ :=
      input.exists_localizedParentFrameHistory cursor.occurrence cursorNonempty
    have targetDerived :=
      (input.mem_localizedOccurrences_iff fuel target.occurrence.1).mp target.occurrence.2
    have parentDerived :=
      (input.mem_localizedOccurrences_iff fuel certificate.parent.1).mp certificate.parent.2
    have frameEq : target.occurrence.1 = certificate.parent.1 :=
      input.declarativeLocalizedOccurrence_functional_at_root_address targetDerived parentDerived
        (rootEq.symm.trans certificate.parent_root.symm)
        (longer.2.trans certificate.parent_address.symm)
    have historyEq : cursor.occurrence.1.node.history =
        certificate.current :: target.occurrence.1.node.history := by
      simpa [frameEq] using certificate.history_eq
    have targetCarrier : input.occurrenceCarrierNode singleBonded target.occurrence =
        .real target.occurrence.1.node.history.reverse := by
      rw [occurrenceCarrierNode, if_pos targetReal]
    have pathShape : cursor.occurrence.1.node.history.reverse =
        target.occurrence.1.node.history.reverse ++ [certificate.current] := by
      simp [historyEq, List.reverse_cons]
    have hlen : 1 < cursor.occurrence.1.node.history.reverse.length := by
      rw [pathShape, List.length_append]
      have nonempty := input.carrierHistory_ne_nil singleBonded target.occurrence
      have pos : 0 < target.occurrence.1.node.history.length :=
        List.length_pos_of_ne_nil nonempty
      simp
      omega
    have dropEq : cursor.occurrence.1.node.history.reverse.dropLast =
        target.occurrence.1.node.history.reverse := by
      simp [pathShape]
    have incValid : CarrierNode.Valid input.moleculeGraph cursor.occurrence.1.root
        (.real cursor.occurrence.1.node.history.reverse.dropLast) :=
      SimpleFrom.dropLast hpath hlen
    let inc : Nodes input.moleculeGraph cursor.occurrence.1.root :=
      ⟨.real cursor.occurrence.1.node.history.reverse.dropLast, incValid⟩
    have incomingEq : input.occurrenceCarrierNode singleBonded target.occurrence = inc.1 := by
      rw [targetCarrier]
      dsimp [inc]
      exact congrArg CarrierNode.real dropEq.symm
    exact ⟨cursor.occurrence.1.node.history.reverse, hpath, inc, cursorCarrier, incomingEq,
      (armChild_focus_iff hpath inc).2 (Or.inr ⟨hlen, by dsimp [inc]⟩)⟩

/-- Equal carrier nodes at one outer root are the same occurrence frame.
The carrier readback is `molecularFrameUnit`, and that unit is injective on the
simple-bonded carrier. -/
theorem occurrenceFrame_eq_of_carrierNode
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    {left right : input.LocalizedCIPOccurrence fuel}
    (sameRoot : left.1.root = right.1.root)
    (sameCarrier : input.occurrenceCarrierNode singleBonded left =
      input.occurrenceCarrierNode singleBonded right) :
    left.1 = right.1 := by
  have unitEq : input.molecularFrameUnit left.1 = input.molecularFrameUnit right.1 := by
    calc
      input.molecularFrameUnit left.1 =
          occurrenceReadback left.1.root
            (input.occurrenceCarrierNode singleBonded left) :=
        (input.occurrenceCarrierNode_readback singleBonded left).symm
      _ = occurrenceReadback right.1.root
            (input.occurrenceCarrierNode singleBonded right) := by
          rw [sameRoot, sameCarrier]
      _ = input.molecularFrameUnit right.1 :=
        input.occurrenceCarrierNode_readback singleBonded right
  exact congrArg Subtype.val
    (input.molecularFrameUnit_injective_on_simpleBonded_carrier singleBonded left right unitEq)


end
end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_occurrence_of_simpleFrom
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_occurrence_of_ring
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.occurrenceCarrierNode_valid
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.occurrenceCarrierNode_label
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.occurrenceCarrierNode_readback
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.occurrenceFrame_eq_of_carrierNode
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ringExecutableChild_retainedContextArmFaithful
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realExecutableChild_incomingArmChild
