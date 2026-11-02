import TetraStereo.OneCenter.LocalizedActualOutwardRule1bEquivalence
import TetraStereo.OneCenter.LocalizedOccurrenceFixedPoint
import TetraStereo.OneCenter.LocalizedRetainedConstitutionalTreeReadback
import TetraStereo.OneCenter.LocalizedRetainedDigraphSphereCorrespondence
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

/-! # Actual cyclic outward provenance separation

This module is the strictness companion to `LocalizedActualOutwardRule1bEquivalence`.  It
records the exact local algebraic fact consumed by the actual comparator: at a common outward
sphere, a real node has that sphere's Rule 1b distance, while a ring duplicate has the strictly
earlier root-first ancestor index.  The ancestor index is recovered from the official history,
not supplied as a numerical assumption.  The consumer-facing actual frame theorem is developed
from the actual reroot child constructors below.
-/

namespace TetraStereo.OneCenter
namespace LocalizedCyclicOutwardProvenanceSeparation

open OfficialCIPNode OfficialCIPNodeProvenance
open CertifiedLocalizedCIPInput
open OutwardRule1bObserverEquivalence


/-- Actual siblings' source nodes are real or ring duplicates and have their shared stored depth.
The carrier's finite address membership supplies the depth grading; `SimpleBonded` eliminates
multiple-bond provenance through the established carrier classification. -/
theorem actualPair_provenance_and_depth
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {fuel : Nat}
    (pair : LocalizedActualOutwardRule1bEquivalence.ActualOutwardSiblingPair input fuel) :
    ∃ n, pair.left.occurrence.1.node.depth = n ∧
      pair.right.occurrence.1.node.depth = n ∧
      (pair.left.occurrence.1.node.provenance = realAtom ∨
        ∃ j, pair.left.occurrence.1.node.provenance = ringDuplicate j) ∧
      (pair.right.occurrence.1.node.provenance = realAtom ∨
        ∃ j, pair.right.occurrence.1.node.provenance = ringDuplicate j) := by
  let leftFrame := pair.left.occurrence.1
  let rightFrame := pair.right.occurrence.1
  have leftDerived := (input.mem_localizedOccurrences_iff fuel leftFrame).mp
    pair.left.occurrence.2
  have rightDerived := (input.mem_localizedOccurrences_iff fuel rightFrame).mp
    pair.right.occurrence.2
  have leftRanked := carrierOccurrence_ranked_depth input leftDerived
  have rightRanked := carrierOccurrence_ranked_depth input rightDerived
  have leftAddressLength : leftFrame.address.length =
      pair.target.occurrence.1.address.length + 1 := by
    rw [pair.leftAddress]
    simp
  have rightAddressLength : rightFrame.address.length =
      pair.target.occurrence.1.address.length + 1 := by
    rw [pair.rightAddress]
    simp
  have sameDepth : leftFrame.node.depth = rightFrame.node.depth := by
    rw [leftRanked.2, rightRanked.2, leftAddressLength, rightAddressLength]
  have leftKind := input.carrierOccurrence_provenance_simple_or_ring singleBonded pair.left.occurrence
  have rightKind := input.carrierOccurrence_provenance_simple_or_ring singleBonded pair.right.occurrence
  exact ⟨leftFrame.node.depth, rfl, sameDepth.symm.trans rfl, leftKind, rightKind⟩


private theorem append_singleton_inj_left {α : Type*}
    {left right : List α} {x y : α}
    (equal : left ++ [x] = right ++ [y]) : left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail => simp at equal
  | cons head tail ih =>
      cases right with
      | nil => simp at equal
      | cons other rest =>
          simp only [List.cons_append] at equal
          injection equal with headEq tailEq
          subst other
          exact congrArg (List.cons head) (ih tailEq)

/-- A ring carrier occurrence at a one-slot extension is the actual zero-copy official ring
child of its immediate carrier parent. The parent is recovered by source-root/address
functionality, and `SimpleBonded` supplies the actual executable copy equation. -/
private theorem ringFrame_officialChild
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ fuel)
    (parent : input.LocalizedCIPOccurrence fuel)
    (childRoot : input.Atom) (childAddress : List Nat)
    (childNode : OfficialCIPNode input.Atom)
    (sameRoot : childRoot = parent.1.root)
    (oneSlot : ∃ slot, childAddress = parent.1.address ++ [slot])
    {j : Nat} (ring : childNode.provenance = ringDuplicate j)
    (legitimate : LegitimateOccurrence input childRoot childNode childAddress) :
    ∃ atom slot, childNode = parent.1.node.extend atom 0 ∧
      atom ∈ parent.1.node.history ∧
      childNode ∈ input.executableOfficialCIPChildren parent.1.node ∧
      childAddress = parent.1.address ++ [slot] ∧
      slot = input.executableOfficialChildCopySlot parent.1.node atom 0 := by
  cases legitimate with
  | @simple node address path =>
      have childReal := input.simpleOccurrencePath_provenance path
      rw [childReal] at ring
      cases ring
  | @ring prefixNode prefixAddress current next path currentObserved adjacent notParent visited =>
      rcases oneSlot with ⟨slot, actualAddress⟩
      have addressEq : prefixAddress ++
          [input.executableOfficialChildCopySlot prefixNode next 0] =
            parent.1.address ++ [slot] := by
        calc
          prefixAddress ++ [input.executableOfficialChildCopySlot prefixNode next 0] =
              prefixAddress ++
                [input.executableOfficialChildCopySlot prefixNode next 0] := rfl
          _ = parent.1.address ++ [slot] := actualAddress
      have parentAddress : prefixAddress = parent.1.address :=
        append_singleton_inj_left addressEq
      have prefixLength : prefixAddress.length ≤ fuel := by
        have countBound := input.legitimateOccurrence_address_length_le_atomCount
          (LegitimateOccurrence.simple path)
        exact Nat.le_trans countBound enough
      have prefixMember := input.legitimateOccurrence_mem_localizedOccurrences_of_fuel
        (LegitimateOccurrence.simple path) prefixLength
      let prefixFrame : input.LocalizedCIPOccurrenceFrame := {
        root := childRoot
        address := prefixAddress
        node := prefixNode
        remaining := fuel + 1 - prefixAddress.length
      }
      have targetDerived := (input.mem_localizedOccurrences_iff fuel parent.1).mp parent.2
      have prefixDerived := (input.mem_localizedOccurrences_iff fuel prefixFrame).mp (by
        simpa [prefixFrame] using prefixMember)
      have nodeEq : prefixNode = parent.1.node := by
        have frameEq := input.declarativeLocalizedOccurrence_functional_at_root_address
          prefixDerived targetDerived sameRoot parentAddress
        exact congrArg LocalizedCIPOccurrenceFrame.node frameEq
      subst prefixNode
      have currentObserved' : parent.1.node.current? = some current := by
        simpa using currentObserved
      have nonduplicate : parent.1.node.isDuplicateLeaf = false :=
        input.isDuplicateLeaf_eq_false_of_provenance_real parent.1.node
          (input.simpleOccurrencePath_provenance path)
      have officialMember := input.mem_executableOfficialCIPChildren_of_adjacent
        parent.1.node current next 0 nonduplicate currentObserved' adjacent adjacent
        (Or.inr notParent)
      have slotEq : slot = input.executableOfficialChildCopySlot parent.1.node next 0 := by
        have suffixEq := congrArg List.getLast? addressEq
        have decoded : some (input.executableOfficialChildCopySlot parent.1.node next 0) =
            some slot := by
          simpa using suffixEq
        exact (Option.some.inj decoded).symm
      exact ⟨next, slot, rfl, visited, officialMember, actualAddress, slotEq⟩
  | @multiple prefixNode prefixAddress current next copyIndex path currentObserved adjacent bound positive =>
      have oneBond := singleBonded current next adjacent
      have copyLt : copyIndex < 1 := by simpa [oneBond] using bound
      omega

private theorem actualRingChild_official
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ fuel)
    (parent child : input.LocalizedCIPOccurrence fuel)
    (sameRoot : child.1.root = parent.1.root)
    (oneSlot : ∃ slot, child.1.address = parent.1.address ++ [slot])
    {j : Nat} (ring : child.1.node.provenance = ringDuplicate j) :
    ∃ atom slot, child.1.node = parent.1.node.extend atom 0 ∧
      atom ∈ parent.1.node.history ∧
      child.1.node ∈ input.executableOfficialCIPChildren parent.1.node ∧
      child.1.address = parent.1.address ++ [slot] ∧
      slot = input.executableOfficialChildCopySlot parent.1.node atom 0 := by
  exact ringFrame_officialChild input singleBonded enough parent child.1.root child.1.address
    child.1.node sameRoot oneSlot ring
    (input.carrierOccurrence_legitimate singleBonded child)

/-- A ring duplicate's stored Rule 1b distance is strictly earlier than its sphere. -/
theorem ringDistance_lt_outwardDepth {V : Type*} [DecidableEq V]
    (node : OfficialCIPNode V) (ranked : OutwardRanked node)
    {j : Nat} (ring : node.provenance = ringDuplicate j) :
    node.rule1bRootDistance < node.depth := by
  rcases ranked.classified with real | ⟨ancestor, classification, earlier⟩
  · rw [real] at ring
    cases ring
  · rcases classification with isRing | isMultiple
    · have same : j = ancestor := by rw [ring] at isRing; injection isRing
      subst ancestor
      simpa [rule1bRootDistance, ring] using earlier
    · rw [ring] at isMultiple
      cases isMultiple

/-- At a shared outward depth, real and ring provenance force distinct Rule 1b observations.
The actual source child equation establishes the supplied provenance cases in the sibling
corollaries; this lemma contains no assumed ancestor ordering. -/
theorem real_ring_distance_ne {V : Type*} [DecidableEq V]
    (left right : OfficialCIPNode V) (depth : Nat)
    (rightRanked : OutwardRanked right)
    (leftDepth : left.depth = depth) (rightDepth : right.depth = depth)
    (leftReal : left.provenance = realAtom)
    {j : Nat} (rightRing : right.provenance = ringDuplicate j) :
    left.rule1bRootDistance ≠ right.rule1bRootDistance := by
  have leftValue : left.rule1bRootDistance = depth := by
    simp [rule1bRootDistance, leftReal, leftDepth]
  have rightEarlier := ringDistance_lt_outwardDepth right rightRanked rightRing
  intro tie
  have earlierAtDepth : right.rule1bRootDistance < depth := by
    simpa [rightDepth] using rightEarlier
  rw [← leftValue, tie] at earlierAtDepth
  exact Nat.lt_irrefl _ earlierAtDepth

/-- Two ring observations at one depth differ whenever their actual repeated ancestors differ.
`duplicateRootDistance_eq_firstIndex` recovers the ancestor address from each stored official
history; the sibling frame theorem discharges distinctness using the distinct physical atoms. -/
theorem ring_ring_distance_ne_of_distinct_indices {V : Type*} [DecidableEq V]
    (left right : OfficialCIPNode V)
    {jLeft jRight : Nat}
    (leftRing : left.provenance = ringDuplicate jLeft)
    (rightRing : right.provenance = ringDuplicate jRight)
    (indicesNe : jLeft ≠ jRight) :
    left.rule1bRootDistance ≠ right.rule1bRootDistance := by
  have leftValue : left.rule1bRootDistance = jLeft := by
    simp [rule1bRootDistance, leftRing]
  have rightValue : right.rule1bRootDistance = jRight := by
    simp [rule1bRootDistance, rightRing]
  intro equal
  apply indicesNe
  rw [← leftValue, equal, rightValue]

/-- At actual outward siblings' common depth, a real/ring pair has distinct root distances.
Both provenance classes and the common depth are derived from the actual carrier pair. -/
theorem actualPair_real_ring_rootDistances_ne
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {fuel : Nat}
    (pair : LocalizedActualOutwardRule1bEquivalence.ActualOutwardSiblingPair input fuel)
    (leftReal : pair.left.occurrence.1.node.provenance = realAtom)
    {j : Nat} (rightRing : pair.right.occurrence.1.node.provenance = ringDuplicate j) :
    pair.left.occurrence.1.node.rule1bRootDistance ≠
      pair.right.occurrence.1.node.rule1bRootDistance := by
  obtain ⟨n, leftDepth, rightDepth, _, _⟩ :=
    actualPair_provenance_and_depth input singleBonded pair
  have rightRanked := carrierOccurrence_ranked_depth input
    ((input.mem_localizedOccurrences_iff fuel pair.right.occurrence.1).mp
      pair.right.occurrence.2)
  exact LocalizedCyclicOutwardProvenanceSeparation.real_ring_distance_ne pair.left.occurrence.1.node pair.right.occurrence.1.node n
    rightRanked.1 leftDepth rightDepth leftReal rightRing



/-- A successful observer-parametrized official build keeps its root source cell in the first
sphere, independently of how later sibling layers are sorted. -/
private theorem officialBuild_rootSourceCell
    {V : Type*} [Fintype V] [DecidableEq V]
    (observe : OfficialCIPNode V → Nat) (m : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
    ∀ fuel node key,
      MoleculeGraph.buildOfficialRuleMajorKeyWith observe m children fuel node = some key →
        key.sourceNodes.head? = some [([], node)] := by
  intro fuel
  induction fuel with
  | zero =>
      intro node key built
      simp [MoleculeGraph.buildOfficialRuleMajorKeyWith] at built
      subst key
      simp [MoleculeGraph.officialRuleMajorRootKeyWith]
  | succ fuel ih =>
      intro node key built
      unfold MoleculeGraph.buildOfficialRuleMajorKeyWith at built
      dsimp only at built
      by_cases terminal : (children node).isEmpty = true
      · simp [terminal] at built
        subst key
        simp [MoleculeGraph.officialRuleMajorRootKeyWith]
      · simp only [if_neg terminal] at built
        cases childBuild : (children node).mapM
            (MoleculeGraph.buildOfficialRuleMajorKeyWith observe m children fuel) with
        | none => simp [childBuild] at built
        | some childKeys =>
          cases sortedBuild : OfficialRuleMajorKey.sort? childKeys with
          | none => simp [childBuild, sortedBuild] at built
          | some sorted =>
            simp [childBuild, sortedBuild] at built
            subst key
            simp [OfficialRuleMajorKey.assemble,
              MoleculeGraph.officialRuleMajorRootKeyWith]




/-- Distinct ring children of one official parent have distinct root-first ancestor indices.
The ancestor at each index is decoded by the official first-index lookup. If the indices matched,
the lookup gives the same neighbor atom, and the two zero-copy extensions would be the same node. -/
theorem distinctOfficialRingChildren_have_distinct_indices
    (input : CertifiedLocalizedCIPInput)
    {parent left right : OfficialCIPNode input.Atom} {jLeft jRight : Nat}
    (parentRanked : OutwardRanked parent)
    (leftPresent : left ∈ input.executableOfficialCIPChildren parent)
    (rightPresent : right ∈ input.executableOfficialCIPChildren parent)
    (leftRing : left.provenance = ringDuplicate jLeft)
    (rightRing : right.provenance = ringDuplicate jRight)
    (childrenNe : left ≠ right) : jLeft ≠ jRight := by
  obtain ⟨_, atomLeft, leftEq, leftMem, leftDistance, leftIndex⟩ :=
    executable_ring_child_ancestor input parentRanked leftPresent leftRing
  obtain ⟨_, atomRight, rightEq, rightMem, rightDistance, rightIndex⟩ :=
    executable_ring_child_ancestor input parentRanked rightPresent rightRing
  intro indicesEq
  have leftLookup : firstIndexOf? atomLeft parent.history.reverse = some jLeft := leftIndex
  have rightLookup : firstIndexOf? atomRight parent.history.reverse = some jRight := rightIndex
  rw [← indicesEq] at rightLookup
  have leftAt : parent.history.reverse[jLeft]? = some atomLeft := by
    let decoded := duplicateRootDistance_eq_firstIndex parent atomLeft leftMem
    have indexEq : decoded.choose = jLeft := by
      exact (decoded.choose_spec.2.1).symm.trans leftDistance
    have getAt := decoded.choose_spec.2.2.2
    simpa [indexEq] using getAt
  have rightAt : parent.history.reverse[jLeft]? = some atomRight := by
    let decoded := duplicateRootDistance_eq_firstIndex parent atomRight rightMem
    have indexEq : decoded.choose = jLeft := by
      calc
        decoded.choose = jRight := (decoded.choose_spec.2.1).symm.trans rightDistance
        _ = jLeft := indicesEq.symm
    have getAt := decoded.choose_spec.2.2.2
    simpa [indexEq] using getAt
  have atomsEq : atomLeft = atomRight := Option.some.inj (leftAt.symm.trans rightAt)
  apply childrenNe
  rw [leftEq, rightEq, atomsEq]



/-- Distinct actual ring siblings of one target have distinct duplicate ancestor indices. The
ring classification of each child is expanded into its actual simple-path parent plus one
zero-copy neighbor step; target root/address functionality identifies both path prefixes with
the same target. The distinct address slots then force distinct neighbor atoms and hence distinct
first indices in the common parent history. -/
theorem actualPair_ringAncestorIndices_ne
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (pair : LocalizedActualOutwardRule1bEquivalence.ActualOutwardSiblingPair input
      (input.certified.input.molecule.atomCount + 1))
    (childrenDistinct : pair.left ≠ pair.right)
    {jLeft jRight : Nat}
    (leftRing : pair.left.occurrence.1.node.provenance = ringDuplicate jLeft)
    (rightRing : pair.right.occurrence.1.node.provenance = ringDuplicate jRight) :
    jLeft ≠ jRight := by
  have enough : input.certified.input.molecule.atomCount ≤
      input.certified.input.molecule.atomCount + 1 := Nat.le_succ _
  obtain ⟨atomLeft, slotLeftActual, leftNodeEq, leftAtomMem, leftOfficial,
    leftAddress, leftSlotEq⟩ := actualRingChild_official input singleBonded enough
      pair.target.occurrence pair.left.occurrence pair.leftRoot
      ⟨pair.leftSlot, pair.leftAddress⟩ leftRing
  obtain ⟨atomRight, slotRightActual, rightNodeEq, rightAtomMem, rightOfficial,
    rightAddress, rightSlotEq⟩ := actualRingChild_official input singleBonded enough
      pair.target.occurrence pair.right.occurrence pair.rightRoot
      ⟨pair.rightSlot, pair.rightAddress⟩ rightRing
  have slotsNe : pair.leftSlot ≠ pair.rightSlot := by
    intro slotsEq
    have addressEq : pair.left.occurrence.1.address = pair.right.occurrence.1.address := by
      calc
        pair.left.occurrence.1.address = pair.target.occurrence.1.address ++ [pair.leftSlot] :=
          pair.leftAddress
        _ = pair.target.occurrence.1.address ++ [pair.rightSlot] := by rw [slotsEq]
        _ = pair.right.occurrence.1.address := pair.rightAddress.symm
    have leftDerived := (input.mem_localizedOccurrences_iff
      (input.certified.input.molecule.atomCount + 1) pair.left.occurrence.1).mp
      pair.left.occurrence.2
    have rightDerived := (input.mem_localizedOccurrences_iff
      (input.certified.input.molecule.atomCount + 1) pair.right.occurrence.1).mp
      pair.right.occurrence.2
    have rootEq := pair.leftRoot.trans pair.rightRoot.symm
    have frameEq := input.declarativeLocalizedOccurrence_functional_at_root_address
      leftDerived rightDerived rootEq addressEq
    have occurrenceEq : pair.left.occurrence = pair.right.occurrence :=
      Subtype.ext frameEq
    have cursorEq := LocalizedRerootCursor.ext input occurrenceEq
      (pair.leftPrevious.trans pair.rightPrevious.symm)
    exact childrenDistinct cursorEq
  have leftSlotDecode : pair.leftSlot = slotLeftActual := by
    have sameAddress := pair.leftAddress.symm.trans leftAddress
    exact Option.some.inj (by simpa using congrArg List.getLast? sameAddress)
  have rightSlotDecode : pair.rightSlot = slotRightActual := by
    have sameAddress := pair.rightAddress.symm.trans rightAddress
    exact Option.some.inj (by simpa using congrArg List.getLast? sameAddress)
  have actualSlotsNe : slotLeftActual ≠ slotRightActual := by
    intro same
    apply slotsNe
    calc
      pair.leftSlot = slotLeftActual := leftSlotDecode
      _ = slotRightActual := same
      _ = pair.rightSlot := rightSlotDecode.symm
  have atomsNe : atomLeft ≠ atomRight := by
    intro atomsEq
    apply actualSlotsNe
    rw [atomsEq] at leftSlotEq
    exact leftSlotEq.trans rightSlotEq.symm
  exact distinctOfficialRingChildren_have_distinct_indices input
    (carrierOccurrence_ranked_depth input
      ((input.mem_localizedOccurrences_iff
        (input.certified.input.molecule.atomCount + 1) pair.target.occurrence.1).mp
        pair.target.occurrence.2)).1
    leftOfficial rightOfficial leftRing rightRing (by
      intro nodesEq
      apply atomsNe
      have childCurrent := congrArg OfficialCIPNode.current? nodesEq
      have h1 : some atomLeft = some atomRight := by
        simpa [leftNodeEq, rightNodeEq] using childCurrent
      exact Option.some.inj h1)


/-- Source alignment exposes the root Rule 1b cell as the first singleton source sphere. -/
theorem aligned_root_observation
    {V : Type*} [Fintype V] [DecidableEq V]
    (observe : OfficialCIPNode V → Nat) (m : MoleculeGraph V)
    (key : OfficialRuleMajorKey V) (node : OfficialCIPNode V)
    (aligned : OfficialRuleMajorKey.SourceAlignedWith observe m key)
    (rootCell : key.sourceNodes.head? = some [([], node)]) :
    key.rule1b.head? = some [([], observe node)] := by
  rcases aligned with ⟨_, rule1b, _⟩
  rw [rule1b]
  simp [OfficialRuleMajorKey.mapSourceLayers, OfficialRuleMajorKey.mapObservation, rootCell]

/-- Equal constitutional keys force equal chosen Rule 1b root observations whenever their source
roots are retained and aligned. -/
theorem compare_ne_eq_of_root_observations_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (observe : OfficialCIPNode V → Nat) (m : MoleculeGraph V)
    (left right : OfficialRuleMajorKey V)
    (leftNode rightNode : OfficialCIPNode V)
    (leftAligned : OfficialRuleMajorKey.SourceAlignedWith observe m left)
    (rightAligned : OfficialRuleMajorKey.SourceAlignedWith observe m right)
    (leftRoot : left.sourceNodes.head? = some [([], leftNode)])
    (rightRoot : right.sourceNodes.head? = some [([], rightNode)])
    (observationsNe : observe leftNode ≠ observe rightNode) :
    OfficialRuleMajorKey.compare left right ≠ Ordering.eq := by
  intro equal
  have columns := (CertifiedLocalizedCIPInput.officialRuleMajorKey_compare_eq_iff left right).mp equal
  have leftCell := aligned_root_observation observe m left leftNode leftAligned leftRoot
  have rightCell := aligned_root_observation observe m right rightNode rightAligned rightRoot
  apply observationsNe
  have sameHeads : left.rule1b.head? = right.rule1b.head? :=
    congrArg List.head? columns.2.1
  rw [leftCell, rightCell] at sameHeads
  have cellsEq : ([([], observe leftNode)] : List (OfficialSparseEntry Nat)) =
      [([], observe rightNode)] := Option.some.inj sameHeads
  have pairEq : ([], observe leftNode) = ([], observe rightNode) :=
    (List.cons.inj cellsEq).1
  exact congrArg Prod.snd pairEq



/-- The actual revised constitutional keys cannot tie when one actual sibling is real and the
other is a ring duplicate.  Successful revised and official builds are supplied by the accepted
actual outward bridge; root source cells and hybrid root observations are then recovered from
those builds. -/
theorem actualPair_revised_compare_ne_eq_of_real_ring
    (input : CertifiedLocalizedCIPInput)
    {read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    (pair : LocalizedActualOutwardRule1bEquivalence.ActualOutwardSiblingPair input
      (input.certified.input.molecule.atomCount + 1))
    (leftReal : pair.left.occurrence.1.node.provenance = realAtom)
    {j : Nat} (rightRing : pair.right.occurrence.1.node.provenance = ringDuplicate j) :
    ∃ keyLeft keyRight,
      input.buildRuleMajorCumulativeWithRead? .rule4a read
        (2 * (input.certified.input.molecule.atomCount + 1 + 1)) pair.left = some keyLeft ∧
      input.buildRuleMajorCumulativeWithRead? .rule4a read
        (2 * (input.certified.input.molecule.atomCount + 1 + 1)) pair.right = some keyRight ∧
      OfficialRuleMajorKey.compare keyLeft.constitutional keyRight.constitutional ≠
        Ordering.eq := by
  obtain ⟨n, fuel, keyLeft, keyRight, actualLeft, actualRight, hybridLeft, hybridRight,
    leftDepth, rightDepth, fuelEq, keyLeftBuilt, keyRightBuilt, actualLeftBuilt,
    actualRightBuilt, hybridLeftBuilt, hybridRightBuilt, leftTwin, rightTwin,
    leftObservable, rightObservable, comparison⟩ :=
    LocalizedActualOutwardRule1bEquivalence.actual_siblings_revised_compare_eq_hybrid
      input .rule4a read pair
  have rightRanked : OutwardRanked pair.right.occurrence.1.node := by
    have derived := (input.mem_localizedOccurrences_iff
      (input.certified.input.molecule.atomCount + 1) pair.right.occurrence.1).mp
      pair.right.occurrence.2
    exact (carrierOccurrence_ranked_depth input derived).1
  have rightEarlier := ringDistance_lt_outwardDepth
    pair.right.occurrence.1.node rightRanked rightRing
  let sentinel : Nat := input.certified.input.molecule.atomCount + 2
  have leftRootActual := officialBuild_rootSourceCell rule1bRootDistance
    input.moleculeGraph input.executableOfficialCIPChildren fuel
    pair.left.occurrence.1.node actualLeft (by
      rw [← MoleculeGraph.buildOfficialRuleMajorKey_eq_rule1bRootDistance
        input.moleculeGraph input.executableOfficialCIPChildren fuel pair.left.occurrence.1.node]
      exact actualLeftBuilt)
  have rightRootActual := officialBuild_rootSourceCell rule1bRootDistance
    input.moleculeGraph input.executableOfficialCIPChildren fuel
    pair.right.occurrence.1.node actualRight (by
      rw [← MoleculeGraph.buildOfficialRuleMajorKey_eq_rule1bRootDistance
        input.moleculeGraph input.executableOfficialCIPChildren fuel pair.right.occurrence.1.node]
      exact actualRightBuilt)
  have leftRootHybrid : hybridLeft.sourceNodes.head? = some [([], pair.left.occurrence.1.node)] := by
    rw [← leftTwin.sources]
    exact leftRootActual
  have rightRootHybrid : hybridRight.sourceNodes.head? = some [([], pair.right.occurrence.1.node)] := by
    rw [← rightTwin.sources]
    exact rightRootActual
  have rightDepthEq : pair.right.occurrence.1.node.depth = n := rightDepth
  have rightJlt : j < n := by
    simpa [rule1bRootDistance, rightRing, rightDepth] using rightEarlier
  have sentinelGt : n < sentinel := by omega
  have hybridNe : OfficialRuleMajorKey.compare hybridLeft hybridRight ≠ Ordering.eq :=
    compare_ne_eq_of_root_observations_ne (hybridDuplicatePriority sentinel)
      input.moleculeGraph hybridLeft hybridRight
      pair.left.occurrence.1.node pair.right.occurrence.1.node
      leftTwin.alignHybrid rightTwin.alignHybrid leftRootHybrid rightRootHybrid (by
        rw [hybridDuplicatePriority_real sentinel _ leftReal,
          hybridDuplicatePriority_ring sentinel _ j rightRing]
        omega)
  refine ⟨keyLeft, keyRight, keyLeftBuilt, keyRightBuilt, ?_⟩
  intro tie
  have tieHybrid : OfficialRuleMajorKey.compare hybridLeft hybridRight = Ordering.eq :=
    comparison.symm.trans tie
  exact hybridNe tieHybrid



/-- The same actual strictness result with the real and ring siblings in the opposite order. -/
theorem actualPair_revised_compare_ne_eq_of_ring_real
    (input : CertifiedLocalizedCIPInput)
    {read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    (pair : LocalizedActualOutwardRule1bEquivalence.ActualOutwardSiblingPair input
      (input.certified.input.molecule.atomCount + 1))
    {j : Nat} (leftRing : pair.left.occurrence.1.node.provenance = ringDuplicate j)
    (rightReal : pair.right.occurrence.1.node.provenance = realAtom) :
    ∃ keyLeft keyRight,
      input.buildRuleMajorCumulativeWithRead? .rule4a read
        (2 * (input.certified.input.molecule.atomCount + 1 + 1)) pair.left = some keyLeft ∧
      input.buildRuleMajorCumulativeWithRead? .rule4a read
        (2 * (input.certified.input.molecule.atomCount + 1 + 1)) pair.right = some keyRight ∧
      OfficialRuleMajorKey.compare keyLeft.constitutional keyRight.constitutional ≠
        Ordering.eq := by
  let swapped : LocalizedActualOutwardRule1bEquivalence.ActualOutwardSiblingPair input
      (input.certified.input.molecule.atomCount + 1) := {
    target := pair.target
    left := pair.right
    right := pair.left
    leftPrevious := pair.rightPrevious
    rightPrevious := pair.leftPrevious
    leftRoot := pair.rightRoot
    rightRoot := pair.leftRoot
    leftSlot := pair.rightSlot
    rightSlot := pair.leftSlot
    leftAddress := pair.rightAddress
    rightAddress := pair.leftAddress
  }
  obtain ⟨rightKey, leftKey, rightBuilt, leftBuilt, reverseNe⟩ :=
    actualPair_revised_compare_ne_eq_of_real_ring input swapped rightReal leftRing
  refine ⟨leftKey, rightKey, leftBuilt, rightBuilt, ?_⟩
  intro tie
  apply reverseNe
  have columns := (CertifiedLocalizedCIPInput.officialRuleMajorKey_compare_eq_iff
    leftKey.constitutional rightKey.constitutional).mp tie
  exact (CertifiedLocalizedCIPInput.officialRuleMajorKey_compare_eq_iff
    rightKey.constitutional leftKey.constitutional).mpr
      ⟨columns.1.symm, columns.2.1.symm, columns.2.2.symm⟩

/-- Two distinct actual ring-duplicate children of the same outward target have distinct
constitutional priorities in the revised Rule 4a builder.  The duplicate indices are recovered
from the actual zero-copy child extensions and the parent's root-first history lookup; they are
not hypotheses about the comparator. -/
theorem actualPair_revised_compare_ne_eq_of_distinct_ring
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    (pair : LocalizedActualOutwardRule1bEquivalence.ActualOutwardSiblingPair input
      (input.certified.input.molecule.atomCount + 1))
    (childrenDistinct : pair.left ≠ pair.right)
    {jLeft jRight : Nat}
    (leftRing : pair.left.occurrence.1.node.provenance = ringDuplicate jLeft)
    (rightRing : pair.right.occurrence.1.node.provenance = ringDuplicate jRight) :
    ∃ keyLeft keyRight,
      input.buildRuleMajorCumulativeWithRead? .rule4a read
        (2 * (input.certified.input.molecule.atomCount + 1 + 1)) pair.left = some keyLeft ∧
      input.buildRuleMajorCumulativeWithRead? .rule4a read
        (2 * (input.certified.input.molecule.atomCount + 1 + 1)) pair.right = some keyRight ∧
      OfficialRuleMajorKey.compare keyLeft.constitutional keyRight.constitutional ≠
        Ordering.eq := by
  obtain ⟨n, fuel, keyLeft, keyRight, actualLeft, actualRight, hybridLeft, hybridRight,
    leftDepth, rightDepth, fuelEq, keyLeftBuilt, keyRightBuilt, actualLeftBuilt,
    actualRightBuilt, hybridLeftBuilt, hybridRightBuilt, leftTwin, rightTwin,
    leftObservable, rightObservable, comparison⟩ :=
    LocalizedActualOutwardRule1bEquivalence.actual_siblings_revised_compare_eq_hybrid
      input .rule4a read pair
  have indicesNe := actualPair_ringAncestorIndices_ne input singleBonded pair
    childrenDistinct leftRing rightRing
  let sentinel := input.certified.input.molecule.atomCount + 2
  have leftRootActual := officialBuild_rootSourceCell rule1bRootDistance
    input.moleculeGraph input.executableOfficialCIPChildren fuel
    pair.left.occurrence.1.node actualLeft (by
      rw [← MoleculeGraph.buildOfficialRuleMajorKey_eq_rule1bRootDistance
        input.moleculeGraph input.executableOfficialCIPChildren fuel pair.left.occurrence.1.node]
      exact actualLeftBuilt)
  have rightRootActual := officialBuild_rootSourceCell rule1bRootDistance
    input.moleculeGraph input.executableOfficialCIPChildren fuel
    pair.right.occurrence.1.node actualRight (by
      rw [← MoleculeGraph.buildOfficialRuleMajorKey_eq_rule1bRootDistance
        input.moleculeGraph input.executableOfficialCIPChildren fuel pair.right.occurrence.1.node]
      exact actualRightBuilt)
  have leftRootHybrid : hybridLeft.sourceNodes.head? =
      some [([], pair.left.occurrence.1.node)] := by
    rw [← leftTwin.sources]
    exact leftRootActual
  have rightRootHybrid : hybridRight.sourceNodes.head? =
      some [([], pair.right.occurrence.1.node)] := by
    rw [← rightTwin.sources]
    exact rightRootActual
  have hybridNe : OfficialRuleMajorKey.compare hybridLeft hybridRight ≠ Ordering.eq :=
    compare_ne_eq_of_root_observations_ne (hybridDuplicatePriority sentinel)
      input.moleculeGraph hybridLeft hybridRight
      pair.left.occurrence.1.node pair.right.occurrence.1.node
      leftTwin.alignHybrid rightTwin.alignHybrid
      leftRootHybrid rightRootHybrid (by
        rw [hybridDuplicatePriority_ring sentinel _ jLeft leftRing,
          hybridDuplicatePriority_ring sentinel _ jRight rightRing]
        exact fun h => indicesNe h)
  refine ⟨keyLeft, keyRight, keyLeftBuilt, keyRightBuilt, ?_⟩
  intro tie
  have tieHybrid : OfficialRuleMajorKey.compare hybridLeft hybridRight = Ordering.eq :=
    comparison.symm.trans tie
  exact hybridNe tieHybrid


end LocalizedCyclicOutwardProvenanceSeparation
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicOutwardProvenanceSeparation.ringDistance_lt_outwardDepth
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicOutwardProvenanceSeparation.real_ring_distance_ne
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicOutwardProvenanceSeparation.ring_ring_distance_ne_of_distinct_indices
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicOutwardProvenanceSeparation.actualPair_provenance_and_depth
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicOutwardProvenanceSeparation.actualPair_real_ring_rootDistances_ne

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicOutwardProvenanceSeparation.aligned_root_observation
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicOutwardProvenanceSeparation.compare_ne_eq_of_root_observations_ne

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicOutwardProvenanceSeparation.actualPair_revised_compare_ne_eq_of_real_ring

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicOutwardProvenanceSeparation.actualPair_revised_compare_ne_eq_of_ring_real

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicOutwardProvenanceSeparation.distinctOfficialRingChildren_have_distinct_indices

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicOutwardProvenanceSeparation.actualPair_ringAncestorIndices_ne

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicOutwardProvenanceSeparation.actualPair_revised_compare_ne_eq_of_distinct_ring
