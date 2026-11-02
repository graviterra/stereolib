import TetraStereo.OneCenter.LocalizedRecursiveDescriptorKey
import TetraStereo.OneCenter.DeclarativeCIPGlobalFixedPoint
import TetraStereo.OneCenter.LocalizedAxialChainPerception

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Finite occurrence-local carrier for localized CIP dependencies

A molecular atom is not an adequate coordinate for auxiliary CIP descriptors.  The same atom
can occur below different final stereocenters, in different ligand slots, or with different
rerooting histories.  This module therefore enumerates proof-relevant occurrences carrying:

* the final stereogenic-unit root atom whose comparison is being evaluated;
* the complete root-relative sibling address;
* the provenance-bearing official digraph node, including its history; and
* the remaining certified expansion depth.

The enumeration is characterized by an independent inductive relation.  At the established
finite-molecule default bound, every ligand root is already proved complete by
`executableOfficialExpansionCompleteWithin_default`.  The strict dependency relation permits
only a deeper address below the same final root.  Its well-foundedness is a kernel proof over the
finite, exactly enumerated carrier; it is not an assumed scheduler order.

This file intentionally does not yet assign auxiliary descriptors.  It establishes the chemical
coordinates and well-founded dependency boundary on which the Rule-4c evaluator must operate.
-/

namespace CertifiedLocalizedCIPInput

/-- Runtime neighbor-copy enumeration has no duplicate `(atom, copy-index)` pair. -/
theorem executableOfficialNeighborCopies_nodup
    (input : CertifiedLocalizedCIPInput) (current : input.Atom) :
    (input.executableOfficialNeighborCopies current).Nodup := by
  unfold executableOfficialNeighborCopies
  rw [List.nodup_flatMap]
  constructor
  · intro neighbor _neighborPresent
    exact List.Nodup.map (by
      intro left right equality
      exact Prod.mk.inj equality |>.2) List.nodup_range
  · have neighborsNodup :=
      Finset.sort_nodup (input.moleculeGraph.neighborFinset current) (· ≤ ·)
    rw [List.nodup_iff_pairwise_ne] at neighborsNodup
    apply neighborsNodup.imp
    intro left right different
    rw [Function.onFun, List.disjoint_left]
    intro pair leftPresent rightPresent
    rw [List.mem_map] at leftPresent rightPresent
    rcases leftPresent with ⟨leftIndex, _leftIndexPresent, leftIdentity⟩
    rcases rightPresent with ⟨rightIndex, _rightIndexPresent, rightIdentity⟩
    subst pair
    exact different (Prod.mk.inj rightIdentity |>.1.symm)

/-- Removing the zero-copy parent preserves uniqueness of executable child-copy coordinates. -/
theorem executableOfficialChildCopies_nodup
    (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) :
    (input.executableOfficialChildCopies node).Nodup := by
  unfold executableOfficialChildCopies
  cases currentObserved : node.current? with
  | none => exact List.nodup_nil
  | some current =>
      cases parentObserved : node.parent? with
      | none => exact input.executableOfficialNeighborCopies_nodup current
      | some parent => exact
          (input.executableOfficialNeighborCopies_nodup current).filter _

/-- One occurrence-local coordinate in a bounded official molecular expansion. -/
structure LocalizedCIPOccurrenceFrame (input : CertifiedLocalizedCIPInput) where
  root : input.Atom
  address : List Nat
  node : OfficialCIPNode input.Atom
  remaining : Nat
  deriving DecidableEq, Repr

@[ext] theorem LocalizedCIPOccurrenceFrame.ext
    (input : CertifiedLocalizedCIPInput)
    {left right : input.LocalizedCIPOccurrenceFrame}
    (root : left.root = right.root)
    (address : left.address = right.address)
    (node : left.node = right.node)
    (remaining : left.remaining = right.remaining) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Depth-first executable enumeration of one bounded provenance subtree.  `path` is already
the address of `node`; child indices are appended only after the executable child enumeration
has fixed their sibling slots. -/
def localizedOccurrenceSubtree (input : CertifiedLocalizedCIPInput)
    (root : input.Atom) :
    Nat → List Nat → OfficialCIPNode input.Atom →
      List input.LocalizedCIPOccurrenceFrame
  | 0, path, node =>
      [{ root := root, address := path, node := node, remaining := 0 }]
  | fuel + 1, path, node =>
      { root := root, address := path, node := node, remaining := fuel + 1 } ::
        (input.executableOfficialCIPChildren node).zipIdx.flatMap fun child =>
          input.localizedOccurrenceSubtree root fuel
            (path ++ [child.2]) child.1

/-- Independent bounded-reachability relation for one occurrence subtree. -/
inductive DeclarativeLocalizedOccurrenceSubtree
    (input : CertifiedLocalizedCIPInput)
    (root : input.Atom) :
    List Nat → Nat → OfficialCIPNode input.Atom →
      input.LocalizedCIPOccurrenceFrame → Prop
  | subtreeRoot (path fuel node) :
      DeclarativeLocalizedOccurrenceSubtree input root path fuel node
        { root := root, address := path, node := node, remaining := fuel }
  | subtreeDescendant {path fuel node child slot occurrence}
      (childAtSlot : (child, slot) ∈
        (input.executableOfficialCIPChildren node).zipIdx)
      (descendant : DeclarativeLocalizedOccurrenceSubtree input root
        (path ++ [slot]) fuel child occurrence) :
      DeclarativeLocalizedOccurrenceSubtree input root path (fuel + 1) node occurrence

/-- The executable subtree contains exactly the independently derivable bounded occurrences. -/
theorem mem_localizedOccurrenceSubtree_iff
    (input : CertifiedLocalizedCIPInput)
    (root : input.Atom) :
    ∀ fuel path node occurrence,
      occurrence ∈ input.localizedOccurrenceSubtree root fuel path node ↔
        input.DeclarativeLocalizedOccurrenceSubtree root path fuel node occurrence
  | 0, path, node, occurrence => by
      constructor
      · intro present
        simp [localizedOccurrenceSubtree] at present
        subst occurrence
        exact DeclarativeLocalizedOccurrenceSubtree.subtreeRoot path 0 node
      · intro derived
        cases derived with
        | subtreeRoot => simp [localizedOccurrenceSubtree]
  | fuel + 1, path, node, occurrence => by
      constructor
      · intro present
        rw [localizedOccurrenceSubtree, List.mem_cons] at present
        rcases present with here | below
        · subst occurrence
          exact DeclarativeLocalizedOccurrenceSubtree.subtreeRoot path (fuel + 1) node
        · rw [List.mem_flatMap] at below
          rcases below with ⟨child, childPresent, descendantPresent⟩
          exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant childPresent
            ((input.mem_localizedOccurrenceSubtree_iff root fuel
              (path ++ [child.2]) child.1 occurrence).mp descendantPresent)
      · intro derived
        cases derived with
        | subtreeRoot => simp [localizedOccurrenceSubtree]
        | @subtreeDescendant _ _ _ child slot occurrence childPresent descendant =>
            rw [localizedOccurrenceSubtree, List.mem_cons]
            apply Or.inr
            rw [List.mem_flatMap]
            exact ⟨(child, slot), childPresent,
              (input.mem_localizedOccurrenceSubtree_iff root fuel
                (path ++ [slot]) child occurrence).mpr descendant⟩

/-- Every derivable subtree occurrence has the exact address/remaining-depth grading imposed by
its bounded root. -/
theorem declarativeLocalizedOccurrenceSubtree_depthGrade
    (input : CertifiedLocalizedCIPInput)
    {root : input.Atom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode input.Atom}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrenceSubtree root path fuel node occurrence) :
    occurrence.address.length + occurrence.remaining = path.length + fuel := by
  induction derived with
  | subtreeRoot => rfl
  | subtreeDescendant _childAtSlot _descendant inductionHypothesis =>
      simp only [List.length_append, List.length_singleton] at inductionHypothesis ⊢
      omega

/-- Every declarative subtree occurrence retains the address of its subtree root as a prefix. -/
theorem declarativeLocalizedOccurrenceSubtree_addressPrefix
    (input : CertifiedLocalizedCIPInput)
    {root : input.Atom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode input.Atom}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrenceSubtree
      root path fuel node occurrence) :
    path <+: occurrence.address := by
  induction derived with
  | subtreeRoot => exact ⟨[], by simp⟩
  | @subtreeDescendant path fuel node child slot occurrence
      childAtSlot descendant inductionHypothesis =>
      exact (List.prefix_append path [slot]).trans inductionHypothesis

/-- A derivation whose address has not moved below its subtree path is exactly the subtree root
frame; no descendant constructor can collapse an appended sibling slot. -/
theorem declarativeLocalizedOccurrenceSubtree_eq_root_of_address_eq
    (input : CertifiedLocalizedCIPInput)
    {root : input.Atom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode input.Atom}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrenceSubtree
      root path fuel node occurrence)
    (address : occurrence.address = path) :
    occurrence =
      { root := root, address := path, node := node, remaining := fuel } := by
  cases derived with
  | subtreeRoot => rfl
  | @subtreeDescendant _ _ _ child slot descendant childAtSlot below =>
      have addressPrefix :=
        input.declarativeLocalizedOccurrenceSubtree_addressPrefix below
      have lengthBound := addressPrefix.length_le
      rw [address] at lengthBound
      simp at lengthBound

/-- A bounded official subtree is functional at root-relative addresses.  In particular, two
derivations from the same official root cannot attach different provenance-bearing nodes or
remaining depths to the same sibling address. -/
theorem declarativeLocalizedOccurrenceSubtree_functional_at_address
    (input : CertifiedLocalizedCIPInput)
    {root : input.Atom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode input.Atom}
    {left right : input.LocalizedCIPOccurrenceFrame}
    (leftDerived : input.DeclarativeLocalizedOccurrenceSubtree
      root path fuel node left)
    (rightDerived : input.DeclarativeLocalizedOccurrenceSubtree
      root path fuel node right)
    (sameAddress : left.address = right.address) :
    left = right := by
  induction leftDerived generalizing right with
  | subtreeRoot =>
      exact input.declarativeLocalizedOccurrenceSubtree_eq_root_of_address_eq
        rightDerived (by simpa using sameAddress.symm) |>.symm
  | @subtreeDescendant path fuel node leftChild leftSlot left
      leftChildAtSlot leftBelow inductionHypothesis =>
      cases rightDerived with
      | subtreeRoot =>
          have addressPrefix :=
            input.declarativeLocalizedOccurrenceSubtree_addressPrefix leftBelow
          have lengthBound := addressPrefix.length_le
          rw [sameAddress] at lengthBound
          simp at lengthBound
      | @subtreeDescendant _ _ _ rightChild rightSlot right
          rightChildAtSlot rightBelow =>
          have leftPrefix :=
            input.declarativeLocalizedOccurrenceSubtree_addressPrefix leftBelow
          have rightPrefix :=
            input.declarativeLocalizedOccurrenceSubtree_addressPrefix rightBelow
          rw [sameAddress] at leftPrefix
          have prefixIdentity : path ++ [leftSlot] = path ++ [rightSlot] := by
            rw [List.prefix_iff_eq_take] at leftPrefix rightPrefix
            calc
              path ++ [leftSlot] =
                  (right.address.take (path ++ [leftSlot]).length) := leftPrefix
              _ = right.address.take (path ++ [rightSlot]).length := by simp
              _ = path ++ [rightSlot] := rightPrefix.symm
          have slotIdentity : leftSlot = rightSlot := by
            simpa using prefixIdentity
          subst rightSlot
          have leftIndexed := List.mem_zipIdx leftChildAtSlot
          have rightIndexed := List.mem_zipIdx rightChildAtSlot
          have childIdentity : leftChild = rightChild := by
            simpa using leftIndexed.2.2.trans rightIndexed.2.2.symm
          subst rightChild
          exact inductionHypothesis rightBelow sameAddress

/-- Every subtree derivation retains the selected official root atom. -/
theorem declarativeLocalizedOccurrenceSubtree_root_eq
    (input : CertifiedLocalizedCIPInput)
    {root : input.Atom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode input.Atom}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrenceSubtree
      root path fuel node occurrence) :
    occurrence.root = root := by
  induction derived with
  | subtreeRoot => rfl
  | subtreeDescendant _ _ inductionHypothesis => exact inductionHypothesis

/-- If two occurrences lie in the same official subtree and the second address is exactly one
sibling slot below the first, then its node is exactly the executable official child at that slot.
This is the local edge-recovery counterpart of address functionality. -/
theorem declarativeLocalizedOccurrenceSubtree_immediate_child
    (input : CertifiedLocalizedCIPInput)
    {root : input.Atom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode input.Atom}
    {source childOccurrence : input.LocalizedCIPOccurrenceFrame}
    (sourceDerived : input.DeclarativeLocalizedOccurrenceSubtree
      root path fuel node source)
    (childDerived : input.DeclarativeLocalizedOccurrenceSubtree
      root path fuel node childOccurrence)
    (slot : Nat)
    (childAddress : childOccurrence.address = source.address ++ [slot]) :
    ∃ child,
      (child, slot) ∈ (input.executableOfficialCIPChildren source.node).zipIdx ∧
      childOccurrence =
        { root := source.root
          address := source.address ++ [slot]
          node := child
          remaining := source.remaining - 1 } := by
  induction sourceDerived generalizing childOccurrence with
  | subtreeRoot =>
      cases childDerived with
      | subtreeRoot => simp at childAddress
      | @subtreeDescendant _ childFuel _ child childSlot childOccurrence
          childAtSlot below =>
          have belowPrefix :=
            input.declarativeLocalizedOccurrenceSubtree_addressPrefix below
          rw [childAddress] at belowPrefix
          have prefixIdentity := belowPrefix.eq_of_length (by simp)
          have slotIdentity : childSlot = slot := by simpa using prefixIdentity
          subst childSlot
          have childIdentity :=
            input.declarativeLocalizedOccurrenceSubtree_eq_root_of_address_eq
              below (by simpa using childAddress)
          exact ⟨child, childAtSlot, by simpa using childIdentity⟩
  | @subtreeDescendant path fuel node sourceChild sourceSlot source
      sourceAtSlot sourceBelow inductionHypothesis =>
      cases childDerived with
      | subtreeRoot =>
          have sourcePrefix :=
            input.declarativeLocalizedOccurrenceSubtree_addressPrefix sourceBelow
          have lengthBound := sourcePrefix.length_le
          change path = source.address ++ [slot] at childAddress
          rw [childAddress] at lengthBound
          simp at lengthBound
      | @subtreeDescendant _ _ _ candidateChild candidateSlot childOccurrence
          candidateAtSlot candidateBelow =>
          have sourcePrefix :=
            input.declarativeLocalizedOccurrenceSubtree_addressPrefix sourceBelow
          have sourcePrefixChild : path ++ [sourceSlot] <+:
              childOccurrence.address := by
            apply sourcePrefix.trans
            rw [childAddress]
            exact List.prefix_append _ _
          have candidatePrefix :=
            input.declarativeLocalizedOccurrenceSubtree_addressPrefix candidateBelow
          have topPrefixIdentity :
              path ++ [sourceSlot] = path ++ [candidateSlot] := by
            rw [List.prefix_iff_eq_take] at sourcePrefixChild candidatePrefix
            calc
              path ++ [sourceSlot] =
                  childOccurrence.address.take (path ++ [sourceSlot]).length :=
                sourcePrefixChild
              _ = childOccurrence.address.take
                  (path ++ [candidateSlot]).length := by simp
              _ = path ++ [candidateSlot] := candidatePrefix.symm
          have topSlotIdentity : sourceSlot = candidateSlot := by
            simpa using topPrefixIdentity
          subst candidateSlot
          have sourceIndexed := List.mem_zipIdx sourceAtSlot
          have candidateIndexed := List.mem_zipIdx candidateAtSlot
          have topChildIdentity : sourceChild = candidateChild := by
            simpa using sourceIndexed.2.2.trans candidateIndexed.2.2.symm
          subst candidateChild
          exact inductionHypothesis candidateBelow childAddress

/-- If a derived occurrence still has positive depth, every executable child at that coordinate
is itself derivable in the same bounded official subtree. -/
theorem DeclarativeLocalizedOccurrenceSubtree.immediateChild
    (input : CertifiedLocalizedCIPInput)
    {root : input.Atom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode input.Atom}
    {source : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrenceSubtree
      root path fuel node source)
    (positive : 0 < source.remaining)
    {child : OfficialCIPNode input.Atom} {slot : Nat}
    (childAtSlot : (child, slot) ∈
      (input.executableOfficialCIPChildren source.node).zipIdx) :
    input.DeclarativeLocalizedOccurrenceSubtree root path fuel node
      { root := source.root
        address := source.address ++ [slot]
        node := child
        remaining := source.remaining - 1 } := by
  induction derived with
  | subtreeRoot path subtreeFuel subtreeNode =>
      cases subtreeFuel with
      | zero => simp at positive
      | succ childFuel =>
          exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant childAtSlot
            (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
              (path ++ [slot]) childFuel child)
  | subtreeDescendant parentAtSlot descendant inductionHypothesis =>
      exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant parentAtSlot
        (inductionHypothesis positive childAtSlot)

/-- Bounded occurrence family below one final center.  This is the complete official occurrence
subtree rooted at the final center, not merely the four zero-copy real ligand subtrees.  In
particular, multiple-bond duplicate copies created directly at the final center remain available
to later rerooting.  The empty address denotes the final center itself. -/
def localizedOccurrencesAtCenter (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (center : input.TetrahedralCenter) :
    List input.LocalizedCIPOccurrenceFrame :=
  input.localizedOccurrenceSubtree center (fuel + 1) []
    (OfficialCIPNode.root center.1)

/-- Independent exact reachability relation for the complete final-center occurrence subtree. -/
def DeclarativeLocalizedOccurrenceAtCenter
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (center : input.TetrahedralCenter) :
    input.LocalizedCIPOccurrenceFrame → Prop :=
  input.DeclarativeLocalizedOccurrenceSubtree center.1 [] (fuel + 1)
    (OfficialCIPNode.root center.1)

/-- The executable one-center family is extensionally exact. -/
theorem mem_localizedOccurrencesAtCenter_iff
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (center : input.TetrahedralCenter)
    (occurrence : input.LocalizedCIPOccurrenceFrame) :
    occurrence ∈ input.localizedOccurrencesAtCenter fuel center ↔
      input.DeclarativeLocalizedOccurrenceAtCenter fuel center occurrence := by
  exact input.mem_localizedOccurrenceSubtree_iff center.1 (fuel + 1) []
    (OfficialCIPNode.root center.1) occurrence

/-- Every one-center occurrence lies on the common grading hyperplane
`address.length + remaining = fuel + 1`. -/
theorem declarativeLocalizedOccurrenceAtCenter_depthGrade
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {center : input.TetrahedralCenter}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrenceAtCenter fuel center occurrence) :
    occurrence.address.length + occurrence.remaining = fuel + 1 := by
  simpa using input.declarativeLocalizedOccurrenceSubtree_depthGrade derived

/-! ## Molecule-wide axial roots -/

/-- One canonical open even-cumulene chain perceived from the complete molecule graph. -/
abbrev LocalizedEvenAxialChain (input : CertifiedLocalizedCIPInput) :=
  { axis : input.LocalizedEvenAxialChainFrame //
    axis ∈ input.localizedEvenAxialChains }

/-- Complete official occurrence subtree rooted at the canonical terminal of one perceived open
even cumulene axis. -/
def localizedOccurrencesAtEvenAxialChain
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChainFrame) :
    List input.LocalizedCIPOccurrenceFrame :=
  input.localizedOccurrenceSubtree axis.root.terminal (fuel + 1) []
    (OfficialCIPNode.root axis.root.terminal)

/-- Independent exact occurrence meaning below a molecule-wide canonical even-axis root. -/
def DeclarativeLocalizedOccurrenceAtEvenAxialChain
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChainFrame) :
    input.LocalizedCIPOccurrenceFrame → Prop :=
  input.DeclarativeLocalizedOccurrenceSubtree axis.root.terminal [] (fuel + 1)
    (OfficialCIPNode.root axis.root.terminal)

/-- The real zero-copy child entering a perceived axis from its canonical terminal root. -/
def localizedEvenAxialFirstChildNode
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChainFrame) : OfficialCIPNode input.Atom :=
  (OfficialCIPNode.root axis.root.terminal).extend axis.root.firstAxis 0

/-- Any positive non-parent edge leaving a real official node occurs as its zero-copy executable
child. This is the reusable carrier-embedding fact for molecular paths. -/
theorem extend_zero_mem_executableOfficialCIPChildren_of_real
    (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) (current next : input.Atom)
    (real : node.provenance = OfficialCIPNodeProvenance.realAtom)
    (currentObserved : node.current? = some current)
    (adjacent : input.moleculeGraph.Adj current next)
    (notParent : node.parent? ≠ some next) :
    node.extend next 0 ∈ input.executableOfficialCIPChildren node := by
  have copyPresent : (next, 0) ∈ input.executableOfficialNeighborCopies current := by
    unfold executableOfficialNeighborCopies
    rw [List.mem_flatMap]
    refine ⟨next, (Finset.mem_sort (r := (· ≤ ·))).mpr
      ((input.moleculeGraph.mem_neighborFinset current next).mpr adjacent), ?_⟩
    rw [List.mem_map]
    exact ⟨0, by simpa [MoleculeGraph.Adj] using adjacent, rfl⟩
  have nonduplicate : node.isDuplicateLeaf = false := by
    simp [OfficialCIPNode.isDuplicateLeaf, real]
  unfold executableOfficialCIPChildren
  rw [if_neg (by simpa using nonduplicate)]
  unfold executableOfficialChildCopies
  rw [currentObserved]
  cases parentObserved : node.parent? with
  | none =>
      simp only
      exact List.mem_map.mpr ⟨(next, 0), copyPresent, rfl⟩
  | some parent =>
      simp only
      apply List.mem_map.mpr
      refine ⟨(next, 0), List.mem_filter.mpr ⟨copyPresent, ?_⟩, rfl⟩
      have nextNeParent : next ≠ parent := by
        intro same
        subst next
        exact notParent parentObserved
      simp [nextNeParent]

/-- Any executable child whose provenance denotes a physical atom position is necessarily the
zero copy of a non-parent graph edge. Positive copy indices are exclusively multiple-bond
bookkeeping duplicates. -/
theorem eq_extend_zero_and_not_parent_of_mem_executableOfficialCIPChildren
    (input : CertifiedLocalizedCIPInput)
    (node child : OfficialCIPNode input.Atom)
    (present : child ∈ input.executableOfficialCIPChildren node)
    (physical : child.provenance = OfficialCIPNodeProvenance.realAtom ∨
      ∃ distance, child.provenance =
        OfficialCIPNodeProvenance.ringDuplicate distance) :
    ∃ next,
      child = node.extend next 0 ∧
      node.parent? ≠ some next := by
  unfold executableOfficialCIPChildren at present
  split at present
  · simp at present
  · rw [List.mem_map] at present
    rcases present with ⟨copy, copyPresent, childIdentity⟩
    rcases copy with ⟨next, copyIndex⟩
    subst child
    have copyZero : copyIndex = 0 := by
      by_contra nonzero
      have duplicate := OfficialCIPNode.childProvenance_copy_pos
        node next nonzero
      rcases physical with real | ring
      · simp [OfficialCIPNode.extend_provenance, duplicate] at real
      · rcases ring with ⟨distance, ring⟩
        simp [OfficialCIPNode.extend_provenance, duplicate] at ring
    subst copyIndex
    refine ⟨next, rfl, ?_⟩
    unfold executableOfficialChildCopies at copyPresent
    cases parentObserved : node.parent? with
    | none => simp
    | some parent =>
        intro equality
        have nextEqParent : next = parent := Option.some.inj equality |>.symm
        subst next
        cases currentObserved : node.current? <;>
          simp [parentObserved, currentObserved] at copyPresent

/-- A physical zero-copy child has a unique sibling slot even though positive multiple-bond
copies may be structurally equal to one another. -/
theorem physical_executableOfficialCIPChild_slot_unique
    (input : CertifiedLocalizedCIPInput)
    (node child : OfficialCIPNode input.Atom)
    (firstSlot secondSlot : Nat)
    (firstAtSlot : (child, firstSlot) ∈
      (input.executableOfficialCIPChildren node).zipIdx)
    (secondAtSlot : (child, secondSlot) ∈
      (input.executableOfficialCIPChildren node).zipIdx)
    (physical : child.provenance = OfficialCIPNodeProvenance.realAtom ∨
      ∃ distance, child.provenance =
        OfficialCIPNodeProvenance.ringDuplicate distance) :
    firstSlot = secondSlot := by
  by_cases duplicate : node.isDuplicateLeaf = true
  · simp [executableOfficialCIPChildren, duplicate] at firstAtSlot
  · let copies := input.executableOfficialChildCopies node
    have firstIndexed := List.mem_zipIdx firstAtSlot
    have secondIndexed := List.mem_zipIdx secondAtSlot
    simp only [Nat.zero_le, zero_add, true_and] at firstIndexed secondIndexed
    have firstBound : firstSlot < copies.length := by
      simpa [copies, executableOfficialCIPChildren, duplicate] using firstIndexed.1
    have secondBound : secondSlot < copies.length := by
      simpa [copies, executableOfficialCIPChildren, duplicate] using secondIndexed.1
    let firstCopy := copies[firstSlot]
    let secondCopy := copies[secondSlot]
    have firstNode : child = node.extend firstCopy.1 firstCopy.2 := by
      simpa [copies, firstCopy, executableOfficialCIPChildren, duplicate] using
        firstIndexed.2
    have secondNode : child = node.extend secondCopy.1 secondCopy.2 := by
      simpa [copies, secondCopy, executableOfficialCIPChildren, duplicate] using
        secondIndexed.2
    have firstZero : firstCopy.2 = 0 := by
      by_contra nonzero
      have duplicateProvenance := OfficialCIPNode.childProvenance_copy_pos
        node firstCopy.1 nonzero
      rcases physical with real | ring
      · rw [firstNode, OfficialCIPNode.extend_provenance,
          duplicateProvenance] at real
        exact OfficialCIPNodeProvenance.noConfusion real
      · rcases ring with ⟨distance, ring⟩
        rw [firstNode, OfficialCIPNode.extend_provenance,
          duplicateProvenance] at ring
        exact OfficialCIPNodeProvenance.noConfusion ring
    have secondZero : secondCopy.2 = 0 := by
      by_contra nonzero
      have duplicateProvenance := OfficialCIPNode.childProvenance_copy_pos
        node secondCopy.1 nonzero
      rcases physical with real | ring
      · rw [secondNode, OfficialCIPNode.extend_provenance,
          duplicateProvenance] at real
        exact OfficialCIPNodeProvenance.noConfusion real
      · rcases ring with ⟨distance, ring⟩
        rw [secondNode, OfficialCIPNode.extend_provenance,
          duplicateProvenance] at ring
        exact OfficialCIPNodeProvenance.noConfusion ring
    have atomIdentity : firstCopy.1 = secondCopy.1 := by
      have nodeIdentity := firstNode.symm.trans secondNode
      have currentIdentity := congrArg OfficialCIPNode.current? nodeIdentity
      simpa using currentIdentity
    have copyIdentity : firstCopy = secondCopy := by
      apply Prod.ext
      · exact atomIdentity
      · exact firstZero.trans secondZero.symm
    have copiesNodup : copies.Nodup := by
      exact input.executableOfficialChildCopies_nodup node
    have firstIndex := List.Nodup.idxOf_getElem copiesNodup firstSlot firstBound
    have secondIndex := List.Nodup.idxOf_getElem copiesNodup secondSlot secondBound
    have elementIdentity : copies[firstSlot] = copies[secondSlot] := by
      simpa [firstCopy, secondCopy] using copyIdentity
    rw [elementIdentity] at firstIndex
    exact firstIndex.symm.trans secondIndex

/-- Exact graph perception guarantees that the first physical axis atom is an executable official
CIP child of the terminal root. -/
theorem localizedEvenAxialFirstChildNode_mem
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChainFrame)
    (axisValid : input.DeclarativeLocalizedEvenAxialChainFrame axis) :
    input.localizedEvenAxialFirstChildNode axis ∈
      input.executableOfficialCIPChildren
        (OfficialCIPNode.root axis.root.terminal) := by
  have doubleBond := axisValid.1.1.1
  unfold localizedEvenAxialFirstChildNode executableOfficialCIPChildren
    executableOfficialChildCopies executableOfficialNeighborCopies
  simp only [OfficialCIPNode.root, OfficialCIPNode.isDuplicateLeaf,
    OfficialCIPNodeProvenance.isDuplicateLeaf_realAtom, Bool.false_eq_true,
    ↓reduceIte, OfficialCIPNode.parent?, List.mem_map, List.mem_flatMap]
  refine ⟨(axis.root.firstAxis, 0), ?_, rfl⟩
  refine ⟨axis.root.firstAxis, ?_, ?_⟩
  · exact (Finset.mem_sort (r := (· ≤ ·))).mpr
      ((input.moleculeGraph.mem_neighborFinset
        axis.root.terminal axis.root.firstAxis).mpr (by
          simp [MoleculeGraph.Adj, doubleBond]))
  · simp [doubleBond]

/-- The first physical axis child has a canonical sibling slot in the executable root list. -/
theorem exists_localizedEvenAxialFirstChildSlot
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChainFrame)
    (axisValid : input.DeclarativeLocalizedEvenAxialChainFrame axis) :
    ∃ slot, (input.localizedEvenAxialFirstChildNode axis, slot) ∈
      (input.executableOfficialCIPChildren
        (OfficialCIPNode.root axis.root.terminal)).zipIdx := by
  have childPresent := input.localizedEvenAxialFirstChildNode_mem axis axisValid
  rw [List.mem_iff_getElem] at childPresent
  rcases childPresent with ⟨slot, slotValid, childAtSlot⟩
  refine ⟨slot, (List.mem_iff_getElem).mpr ⟨slot, ?_, ?_⟩⟩
  · simpa using slotValid
  · simp [childAtSlot]

theorem mem_localizedOccurrencesAtEvenAxialChain_iff
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChainFrame)
    (occurrence : input.LocalizedCIPOccurrenceFrame) :
    occurrence ∈ input.localizedOccurrencesAtEvenAxialChain fuel axis ↔
      input.DeclarativeLocalizedOccurrenceAtEvenAxialChain fuel axis occurrence := by
  exact input.mem_localizedOccurrenceSubtree_iff axis.root.terminal (fuel + 1) []
    (OfficialCIPNode.root axis.root.terminal) occurrence

theorem declarativeLocalizedOccurrenceAtEvenAxialChain_depthGrade
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {axis : input.LocalizedEvenAxialChainFrame}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrenceAtEvenAxialChain
      fuel axis occurrence) :
    occurrence.address.length + occurrence.remaining = fuel + 1 := by
  simpa using input.declarativeLocalizedOccurrenceSubtree_depthGrade derived

/-- Complete official occurrence subtree rooted at an arbitrary molecular atom.  Enumerating
these roots for every atom avoids assuming a stereogenic family before molecule-wide perception:
ordinary double bonds, cyclic double bonds, axes, planes, and centers all receive the same finite
official-CIP carrier. -/
def localizedOccurrencesAtAtom
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (atom : input.Atom) :
    List input.LocalizedCIPOccurrenceFrame :=
  input.localizedOccurrenceSubtree atom (fuel + 1) []
    (OfficialCIPNode.root atom)

/-- Independent exact meaning of an occurrence below one arbitrary molecular-atom root. -/
def DeclarativeLocalizedOccurrenceAtAtom
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (atom : input.Atom) :
    input.LocalizedCIPOccurrenceFrame → Prop :=
  input.DeclarativeLocalizedOccurrenceSubtree atom [] (fuel + 1)
    (OfficialCIPNode.root atom)

/-- The arbitrary-atom occurrence enumeration is extensionally exact. -/
theorem mem_localizedOccurrencesAtAtom_iff
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (atom : input.Atom)
    (occurrence : input.LocalizedCIPOccurrenceFrame) :
    occurrence ∈ input.localizedOccurrencesAtAtom fuel atom ↔
      input.DeclarativeLocalizedOccurrenceAtAtom fuel atom occurrence := by
  exact input.mem_localizedOccurrenceSubtree_iff atom (fuel + 1) []
    (OfficialCIPNode.root atom) occurrence

/-- Complete bounded occurrence family rooted at every atom of the finite molecule.  The earlier
tetrahedral-center and open-even-axis enumerations are retained above as useful specialized views,
but are no longer the completeness boundary of the shared scheduler carrier. -/
def localizedOccurrences (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    List input.LocalizedCIPOccurrenceFrame :=
  (List.finRange input.certified.input.molecule.atomCount).flatMap
    (input.localizedOccurrencesAtAtom fuel) |>.dedup

/-- The shared finite carrier contains no duplicate occurrence coordinates, even when two
stereogenic-family root enumerations happen to generate the same underlying subtree frame. -/
theorem localizedOccurrences_nodup
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    (input.localizedOccurrences fuel).Nodup := by
  exact List.nodup_dedup _

/-- Independent molecule-wide bounded occurrence relation.  Its stored root is itself the exact
atom-rooted official subtree from which the coordinate must be derivable. -/
def DeclarativeLocalizedOccurrence
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (occurrence : input.LocalizedCIPOccurrenceFrame) : Prop :=
  input.DeclarativeLocalizedOccurrenceAtAtom fuel occurrence.root occurrence

/-- Molecule-wide executable occurrence enumeration is extensionally exact. -/
theorem mem_localizedOccurrences_iff
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (occurrence : input.LocalizedCIPOccurrenceFrame) :
    occurrence ∈ input.localizedOccurrences fuel ↔
      input.DeclarativeLocalizedOccurrence fuel occurrence := by
  rw [localizedOccurrences, List.mem_dedup, List.mem_flatMap]
  constructor
  · rintro ⟨atom, _atomPresent, occurrencePresent⟩
    have derived := (input.mem_localizedOccurrencesAtAtom_iff
      fuel atom occurrence).mp occurrencePresent
    have rootIdentity :=
      input.declarativeLocalizedOccurrenceSubtree_root_eq derived
    simpa [DeclarativeLocalizedOccurrence,
      DeclarativeLocalizedOccurrenceAtAtom, rootIdentity] using derived
  · intro derived
    exact ⟨occurrence.root, by simp,
      (input.mem_localizedOccurrencesAtAtom_iff fuel occurrence.root occurrence).mpr
        derived⟩

/-- Every molecule-wide occurrence, regardless of which stereogenic-family enumeration supplied
it, is a derivation from the same official subtree rooted at its stored root atom. -/
theorem declarativeLocalizedOccurrence_as_rootSubtree
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrence fuel occurrence) :
    input.DeclarativeLocalizedOccurrenceSubtree occurrence.root [] (fuel + 1)
      (OfficialCIPNode.root occurrence.root) occurrence := by
  exact derived

/-- In the deduplicated molecule-wide carrier, root plus sibling address is a complete coordinate:
family overlap cannot introduce a second node or remaining depth at the same coordinate. -/
theorem declarativeLocalizedOccurrence_functional_at_root_address
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {left right : input.LocalizedCIPOccurrenceFrame}
    (leftDerived : input.DeclarativeLocalizedOccurrence fuel left)
    (rightDerived : input.DeclarativeLocalizedOccurrence fuel right)
    (sameRoot : left.root = right.root)
    (sameAddress : left.address = right.address) :
    left = right := by
  have leftRooted :=
    input.declarativeLocalizedOccurrence_as_rootSubtree leftDerived
  have rightRooted :=
    input.declarativeLocalizedOccurrence_as_rootSubtree rightDerived
  have rightRootedAtLeft :
      input.DeclarativeLocalizedOccurrenceSubtree left.root [] (fuel + 1)
        (OfficialCIPNode.root left.root) right := by
    simpa [sameRoot] using rightRooted
  exact input.declarativeLocalizedOccurrenceSubtree_functional_at_address
    leftRooted rightRootedAtLeft sameAddress

/-- Molecule-wide version of immediate official child recovery.  It remains valid when the two
coordinates entered the deduplicated carrier through different stereogenic-family enumerations. -/
theorem declarativeLocalizedOccurrence_immediate_child
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {source childOccurrence : input.LocalizedCIPOccurrenceFrame}
    (sourceDerived : input.DeclarativeLocalizedOccurrence fuel source)
    (childDerived : input.DeclarativeLocalizedOccurrence fuel childOccurrence)
    (sameRoot : childOccurrence.root = source.root)
    (slot : Nat)
    (childAddress : childOccurrence.address = source.address ++ [slot]) :
    ∃ child,
      (child, slot) ∈ (input.executableOfficialCIPChildren source.node).zipIdx ∧
      childOccurrence =
        { root := source.root
          address := source.address ++ [slot]
          node := child
          remaining := source.remaining - 1 } := by
  have sourceRooted :=
    input.declarativeLocalizedOccurrence_as_rootSubtree sourceDerived
  have childRooted :=
    input.declarativeLocalizedOccurrence_as_rootSubtree childDerived
  have childRootedAtSource :
      input.DeclarativeLocalizedOccurrenceSubtree source.root [] (fuel + 1)
        (OfficialCIPNode.root source.root) childOccurrence := by
    simpa [sameRoot] using childRooted
  exact input.declarativeLocalizedOccurrenceSubtree_immediate_child
    sourceRooted childRootedAtSource slot childAddress

/-- Every executable child below a positive-depth molecule-wide occurrence belongs to the same
finite shared carrier family. -/
theorem DeclarativeLocalizedOccurrence.immediateChild
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {source : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrence fuel source)
    (positive : 0 < source.remaining)
    {child : OfficialCIPNode input.Atom} {slot : Nat}
    (childAtSlot : (child, slot) ∈
      (input.executableOfficialCIPChildren source.node).zipIdx) :
    input.DeclarativeLocalizedOccurrence fuel
      { root := source.root
        address := source.address ++ [slot]
        node := child
        remaining := source.remaining - 1 } := by
  exact DeclarativeLocalizedOccurrenceSubtree.immediateChild
    input derived positive childAtSlot

/-- The common address/remaining-depth grading holds molecule-wide. -/
theorem declarativeLocalizedOccurrence_depthGrade
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
  (derived : input.DeclarativeLocalizedOccurrence fuel occurrence) :
    occurrence.address.length + occurrence.remaining = fuel + 1 := by
  simpa using input.declarativeLocalizedOccurrenceSubtree_depthGrade derived

/-- An occurrence at the empty address is uniquely the official root frame for its stored root. -/
theorem declarativeLocalizedOccurrence_eq_root_of_address_nil
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrence fuel occurrence)
    (address : occurrence.address = []) :
    occurrence =
      { root := occurrence.root
        address := []
        node := OfficialCIPNode.root occurrence.root
        remaining := fuel + 1 } := by
  exact input.declarativeLocalizedOccurrenceSubtree_eq_root_of_address_eq
    derived address

/-- Finite proof-relevant occurrence carrier at a selected molecular expansion bound. -/
abbrev LocalizedCIPOccurrence (input : CertifiedLocalizedCIPInput) (fuel : Nat) :=
  { occurrence : input.LocalizedCIPOccurrenceFrame //
    occurrence ∈ input.localizedOccurrences fuel }

/-- Canonical sibling index of the real zero-copy child entering a perceived even axis. -/
noncomputable def localizedEvenAxialFirstChildSlot
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain) : Nat :=
  Classical.choose (input.exists_localizedEvenAxialFirstChildSlot axis.1
    ((input.mem_localizedEvenAxialChains_iff axis.1).mp axis.2))

/-- The selected first-axis slot is backed by the executable official child enumeration. -/
theorem localizedEvenAxialFirstChildSlot_mem
    (input : CertifiedLocalizedCIPInput)
    (axis : input.LocalizedEvenAxialChain) :
    (input.localizedEvenAxialFirstChildNode axis.1,
        input.localizedEvenAxialFirstChildSlot axis) ∈
      (input.executableOfficialCIPChildren
        (OfficialCIPNode.root axis.1.root.terminal)).zipIdx :=
  Classical.choose_spec (input.exists_localizedEvenAxialFirstChildSlot axis.1
    ((input.mem_localizedEvenAxialChains_iff axis.1).mp axis.2))

noncomputable instance localizedCIPOccurrenceFintype
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    Fintype (input.LocalizedCIPOccurrence fuel) := by
  classical
  exact Fintype.ofList (input.localizedOccurrences fuel).attach
    (by intro occurrence; simp)

/-! ## Family-neutral molecular roots and canonical double-bond children -/

/-- Any exact terminal root of a maximal open consecutive-double-bond chain, independent of the
later odd/even parity classification. -/
abbrev LocalizedAxialRoot (input : CertifiedLocalizedCIPInput) :=
  { root : input.LocalizedAxialRootCandidate //
    root ∈ input.localizedAxialRootCandidates }

/-- Distinguished official root occurrence for an arbitrary atom of the molecule. -/
noncomputable def localizedAtomRootOccurrence
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (atom : input.Atom) :
    input.LocalizedCIPOccurrence fuel := by
  classical
  refine ⟨
    { root := atom
      address := []
      node := OfficialCIPNode.root atom
      remaining := fuel + 1 }, ?_⟩
  apply (input.mem_localizedOccurrences_iff fuel _).mpr
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [] (fuel + 1)
    (OfficialCIPNode.root atom)

@[simp] theorem localizedAtomRootOccurrence_root
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (atom : input.Atom) :
    (input.localizedAtomRootOccurrence fuel atom).1.root = atom := rfl

@[simp] theorem localizedAtomRootOccurrence_address
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (atom : input.Atom) :
    (input.localizedAtomRootOccurrence fuel atom).1.address = [] := rfl

@[simp] theorem localizedAtomRootOccurrence_node
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (atom : input.Atom) :
    (input.localizedAtomRootOccurrence fuel atom).1.node =
      OfficialCIPNode.root atom := rfl

@[simp] theorem localizedAtomRootOccurrence_remaining
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (atom : input.Atom) :
    (input.localizedAtomRootOccurrence fuel atom).1.remaining = fuel + 1 := rfl

/-- Real zero-copy child entering a maximal open consecutive-double-bond chain from one exact
terminal root. -/
def localizedAxialRootFirstChildNode
    (input : CertifiedLocalizedCIPInput)
    (root : input.LocalizedAxialRoot) : OfficialCIPNode input.Atom :=
  (OfficialCIPNode.root root.1.terminal).extend root.1.firstAxis 0

theorem localizedAxialRootFirstChildNode_mem
    (input : CertifiedLocalizedCIPInput)
    (root : input.LocalizedAxialRoot) :
    input.localizedAxialRootFirstChildNode root ∈
      input.executableOfficialCIPChildren (OfficialCIPNode.root root.1.terminal) := by
  have rootValid := (input.mem_localizedAxialRootCandidates_iff root.1).mp root.2
  apply input.extend_zero_mem_executableOfficialCIPChildren_of_real
    (OfficialCIPNode.root root.1.terminal) root.1.terminal root.1.firstAxis
  · rfl
  · rfl
  · simp [MoleculeGraph.Adj, rootValid.1]
  · simp [OfficialCIPNode.root, OfficialCIPNode.parent?]

theorem exists_localizedAxialRootFirstChildSlot
    (input : CertifiedLocalizedCIPInput)
    (root : input.LocalizedAxialRoot) :
    ∃ slot, (input.localizedAxialRootFirstChildNode root, slot) ∈
      (input.executableOfficialCIPChildren
        (OfficialCIPNode.root root.1.terminal)).zipIdx := by
  have childPresent := input.localizedAxialRootFirstChildNode_mem root
  rw [List.mem_iff_getElem] at childPresent
  rcases childPresent with ⟨slot, slotValid, childAtSlot⟩
  exact ⟨slot, (List.mem_iff_getElem).mpr
    ⟨slot, by simpa using slotValid, by simp [childAtSlot]⟩⟩

noncomputable def localizedAxialRootFirstChildSlot
    (input : CertifiedLocalizedCIPInput)
    (root : input.LocalizedAxialRoot) : Nat :=
  Classical.choose (input.exists_localizedAxialRootFirstChildSlot root)

theorem localizedAxialRootFirstChildSlot_mem
    (input : CertifiedLocalizedCIPInput)
    (root : input.LocalizedAxialRoot) :
    (input.localizedAxialRootFirstChildNode root,
        input.localizedAxialRootFirstChildSlot root) ∈
      (input.executableOfficialCIPChildren
        (OfficialCIPNode.root root.1.terminal)).zipIdx :=
  Classical.choose_spec (input.exists_localizedAxialRootFirstChildSlot root)

/-- Distinguished root occurrence of an arbitrary perceived maximal open double-bond chain. -/
noncomputable def localizedAxialRootOccurrence
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (root : input.LocalizedAxialRoot) : input.LocalizedCIPOccurrence fuel :=
  input.localizedAtomRootOccurrence fuel root.1.terminal

/-- Distinguished first-child occurrence entering an arbitrary perceived maximal open chain. -/
noncomputable def localizedAxialRootFirstChildOccurrence
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (root : input.LocalizedAxialRoot) : input.LocalizedCIPOccurrence fuel := by
  classical
  let slot := input.localizedAxialRootFirstChildSlot root
  let child := input.localizedAxialRootFirstChildNode root
  refine ⟨
    { root := root.1.terminal
      address := [slot]
      node := child
      remaining := fuel }, ?_⟩
  apply (input.mem_localizedOccurrences_iff fuel _).mpr
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input.localizedAxialRootFirstChildSlot_mem root)
    (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [slot] fuel child)

@[simp] theorem localizedAxialRootOccurrence_root
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (root : input.LocalizedAxialRoot) :
    (input.localizedAxialRootOccurrence fuel root).1.root = root.1.terminal := rfl

@[simp] theorem localizedAxialRootOccurrence_address
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (root : input.LocalizedAxialRoot) :
    (input.localizedAxialRootOccurrence fuel root).1.address = [] := rfl

@[simp] theorem localizedAxialRootFirstChildOccurrence_root
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (root : input.LocalizedAxialRoot) :
    (input.localizedAxialRootFirstChildOccurrence fuel root).1.root =
      root.1.terminal := rfl

@[simp] theorem localizedAxialRootFirstChildOccurrence_address
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (root : input.LocalizedAxialRoot) :
    (input.localizedAxialRootFirstChildOccurrence fuel root).1.address =
      [input.localizedAxialRootFirstChildSlot root] := rfl

theorem localizedAxialRootFirstChildOccurrence_physical
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (root : input.LocalizedAxialRoot) :
    (input.localizedAxialRootFirstChildOccurrence fuel root).1.node.provenance =
        OfficialCIPNodeProvenance.realAtom ∧
      (input.localizedAxialRootFirstChildOccurrence fuel root).1.node.current? =
        some root.1.firstAxis ∧
      (input.localizedAxialRootFirstChildOccurrence fuel root).1.node.parent? =
        some root.1.terminal ∧
      input.moleculeGraph.bond root.1.terminal root.1.firstAxis = 2 := by
  have rootValid := (input.mem_localizedAxialRootCandidates_iff root.1).mp root.2
  have doubleBond := rootValid.1
  have distinct : root.1.firstAxis ≠ root.1.terminal := by
    intro equal
    rw [equal] at doubleBond
    simp [input.moleculeGraph.bond_self] at doubleBond
  refine ⟨?_, ?_, ?_, doubleBond⟩
  · simp [localizedAxialRootFirstChildOccurrence,
      localizedAxialRootFirstChildNode, OfficialCIPNode.extend,
      OfficialCIPNode.childProvenance, OfficialCIPNode.root, distinct]
  · rfl
  · rfl

/-- Every undirected physical order-two bond exactly once, oriented by strict atom order. -/
noncomputable def localizedCanonicalDoubleBondPairs
    (input : CertifiedLocalizedCIPInput) : List (input.Atom × input.Atom) := by
  classical
  exact (List.finRange input.certified.input.molecule.atomCount).flatMap fun left =>
    (List.finRange input.certified.input.molecule.atomCount).filterMap fun right =>
      if left < right ∧ input.moleculeGraph.bond left right = 2 then
        some (left, right)
      else none

@[simp] theorem mem_localizedCanonicalDoubleBondPairs_iff
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom) :
    (left, right) ∈ input.localizedCanonicalDoubleBondPairs ↔
      left < right ∧ input.moleculeGraph.bond left right = 2 := by
  classical
  simp [localizedCanonicalDoubleBondPairs]

/-- Canonically oriented molecule-wide physical double-bond carrier. -/
abbrev LocalizedCanonicalDoubleBond (input : CertifiedLocalizedCIPInput) :=
  { pair : input.Atom × input.Atom //
    pair ∈ input.localizedCanonicalDoubleBondPairs }

/-- Real zero-copy child entering a canonical double bond from its lower-ordered endpoint root. -/
def localizedCanonicalDoubleBondFirstChildNode
    (input : CertifiedLocalizedCIPInput)
    (bond : input.LocalizedCanonicalDoubleBond) : OfficialCIPNode input.Atom :=
  (OfficialCIPNode.root bond.1.1).extend bond.1.2 0

/-- The canonical physical double-bond child is executable from its atom root. -/
theorem localizedCanonicalDoubleBondFirstChildNode_mem
    (input : CertifiedLocalizedCIPInput)
    (bond : input.LocalizedCanonicalDoubleBond) :
    input.localizedCanonicalDoubleBondFirstChildNode bond ∈
      input.executableOfficialCIPChildren (OfficialCIPNode.root bond.1.1) := by
  have bondFacts :=
    (input.mem_localizedCanonicalDoubleBondPairs_iff bond.1.1 bond.1.2).mp bond.2
  apply input.extend_zero_mem_executableOfficialCIPChildren_of_real
    (OfficialCIPNode.root bond.1.1) bond.1.1 bond.1.2
  · rfl
  · rfl
  · simp [MoleculeGraph.Adj, bondFacts.2]
  · simp [OfficialCIPNode.root, OfficialCIPNode.parent?]

/-- The real double-bond child has a concrete sibling slot in the official root expansion. -/
theorem exists_localizedCanonicalDoubleBondFirstChildSlot
    (input : CertifiedLocalizedCIPInput)
    (bond : input.LocalizedCanonicalDoubleBond) :
    ∃ slot, (input.localizedCanonicalDoubleBondFirstChildNode bond, slot) ∈
      (input.executableOfficialCIPChildren
        (OfficialCIPNode.root bond.1.1)).zipIdx := by
  have childPresent := input.localizedCanonicalDoubleBondFirstChildNode_mem bond
  rw [List.mem_iff_getElem] at childPresent
  rcases childPresent with ⟨slot, slotValid, childAtSlot⟩
  refine ⟨slot, (List.mem_iff_getElem).mpr ⟨slot, ?_, ?_⟩⟩
  · simpa using slotValid
  · simp [childAtSlot]

/-- Selected official sibling slot of a canonical physical double-bond child. -/
noncomputable def localizedCanonicalDoubleBondFirstChildSlot
    (input : CertifiedLocalizedCIPInput)
    (bond : input.LocalizedCanonicalDoubleBond) : Nat :=
  Classical.choose (input.exists_localizedCanonicalDoubleBondFirstChildSlot bond)

/-- The selected double-bond slot retains its executable-child certificate. -/
theorem localizedCanonicalDoubleBondFirstChildSlot_mem
    (input : CertifiedLocalizedCIPInput)
    (bond : input.LocalizedCanonicalDoubleBond) :
    (input.localizedCanonicalDoubleBondFirstChildNode bond,
        input.localizedCanonicalDoubleBondFirstChildSlot bond) ∈
      (input.executableOfficialCIPChildren
        (OfficialCIPNode.root bond.1.1)).zipIdx :=
  Classical.choose_spec (input.exists_localizedCanonicalDoubleBondFirstChildSlot bond)

/-- Distinguished real child occurrence representing one canonical physical double bond. -/
noncomputable def localizedCanonicalDoubleBondFirstChildOccurrence
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond) :
    input.LocalizedCIPOccurrence fuel := by
  classical
  let slot := input.localizedCanonicalDoubleBondFirstChildSlot bond
  let child := input.localizedCanonicalDoubleBondFirstChildNode bond
  refine ⟨
    { root := bond.1.1
      address := [slot]
      node := child
      remaining := fuel }, ?_⟩
  apply (input.mem_localizedOccurrences_iff fuel _).mpr
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input.localizedCanonicalDoubleBondFirstChildSlot_mem bond)
    (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [slot] fuel child)

@[simp] theorem localizedCanonicalDoubleBondFirstChildOccurrence_root
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond) :
    (input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond).1.root =
      bond.1.1 := rfl

@[simp] theorem localizedCanonicalDoubleBondFirstChildOccurrence_address
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond) :
    (input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond).1.address =
      [input.localizedCanonicalDoubleBondFirstChildSlot bond] := rfl

@[simp] theorem localizedCanonicalDoubleBondFirstChildOccurrence_node
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond) :
    (input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond).1.node =
      input.localizedCanonicalDoubleBondFirstChildNode bond := rfl

/-- The distinguished child coordinate is exactly the physical order-two edge stored by the
canonical double-bond carrier. -/
theorem localizedCanonicalDoubleBondFirstChildOccurrence_physical
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (bond : input.LocalizedCanonicalDoubleBond) :
    (input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond).1.node.provenance =
        OfficialCIPNodeProvenance.realAtom ∧
      (input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond).1.node.current? =
        some bond.1.2 ∧
      (input.localizedCanonicalDoubleBondFirstChildOccurrence fuel bond).1.node.parent? =
        some bond.1.1 ∧
      input.moleculeGraph.bond bond.1.1 bond.1.2 = 2 := by
  have bondFacts :=
    (input.mem_localizedCanonicalDoubleBondPairs_iff bond.1.1 bond.1.2).mp bond.2
  have distinct : bond.1.2 ≠ bond.1.1 := ne_of_gt bondFacts.1
  refine ⟨?_, ?_, ?_, bondFacts.2⟩
  · simp [localizedCanonicalDoubleBondFirstChildNode, OfficialCIPNode.extend,
      OfficialCIPNode.childProvenance, OfficialCIPNode.root, distinct]
  · rfl
  · rfl

/-- Every member of the executable finite carrier satisfies the exact common depth grading. -/
theorem localizedCIPOccurrence_depthGrade
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    occurrence.1.address.length + occurrence.1.remaining = fuel + 1 := by
  apply input.declarativeLocalizedOccurrence_depthGrade
  exact (input.mem_localizedOccurrences_iff fuel occurrence.1).mp occurrence.2

/-- Distinguished terminal-root occurrence for one canonical open even-cumulene axis. -/
noncomputable def localizedEvenAxialRootOccurrence
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) : input.LocalizedCIPOccurrence fuel := by
  classical
  refine ⟨
    { root := axis.1.root.terminal
      address := []
      node := OfficialCIPNode.root axis.1.root.terminal
      remaining := fuel + 1 }, ?_⟩
  apply (input.mem_localizedOccurrences_iff fuel _).mpr
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [] (fuel + 1)
    (OfficialCIPNode.root axis.1.root.terminal)

/-- Distinguished real zero-copy first child entering a canonical open even-cumulene axis. -/
noncomputable def localizedEvenAxialFirstChildOccurrence
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) : input.LocalizedCIPOccurrence fuel := by
  classical
  let slot := input.localizedEvenAxialFirstChildSlot axis
  let child := input.localizedEvenAxialFirstChildNode axis.1
  refine ⟨
    { root := axis.1.root.terminal
      address := [slot]
      node := child
      remaining := fuel }, ?_⟩
  apply (input.mem_localizedOccurrences_iff fuel _).mpr
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input.localizedEvenAxialFirstChildSlot_mem axis)
    (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [slot] fuel child)

@[simp] theorem localizedEvenAxialRootOccurrence_root
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) :
    (input.localizedEvenAxialRootOccurrence fuel axis).1.root =
      axis.1.root.terminal := rfl

@[simp] theorem localizedEvenAxialRootOccurrence_address
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) :
    (input.localizedEvenAxialRootOccurrence fuel axis).1.address = [] := rfl

@[simp] theorem localizedEvenAxialRootOccurrence_node
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) :
    (input.localizedEvenAxialRootOccurrence fuel axis).1.node =
      OfficialCIPNode.root axis.1.root.terminal := rfl

@[simp] theorem localizedEvenAxialRootOccurrence_remaining
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) :
    (input.localizedEvenAxialRootOccurrence fuel axis).1.remaining =
      fuel + 1 := rfl

@[simp] theorem localizedEvenAxialFirstChildOccurrence_root
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) :
    (input.localizedEvenAxialFirstChildOccurrence fuel axis).1.root =
      axis.1.root.terminal := rfl

@[simp] theorem localizedEvenAxialFirstChildOccurrence_address
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) :
    (input.localizedEvenAxialFirstChildOccurrence fuel axis).1.address =
      [input.localizedEvenAxialFirstChildSlot axis] := rfl

@[simp] theorem localizedEvenAxialFirstChildOccurrence_node
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) :
    (input.localizedEvenAxialFirstChildOccurrence fuel axis).1.node =
      input.localizedEvenAxialFirstChildNode axis.1 := rfl

/-- The selected first-axis coordinate is exactly the real physical order-two edge perceived in
the molecular graph. -/
theorem localizedEvenAxialFirstChildOccurrence_physical
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) :
    (input.localizedEvenAxialFirstChildOccurrence fuel axis).1.node.provenance =
        OfficialCIPNodeProvenance.realAtom ∧
      (input.localizedEvenAxialFirstChildOccurrence fuel axis).1.node.current? =
        some axis.1.root.firstAxis ∧
      (input.localizedEvenAxialFirstChildOccurrence fuel axis).1.node.parent? =
        some axis.1.root.terminal ∧
      input.moleculeGraph.bond axis.1.root.terminal axis.1.root.firstAxis = 2 := by
  have axisValid := (input.mem_localizedEvenAxialChains_iff axis.1).mp axis.2
  have doubleBond := axisValid.1.1.1
  have distinct : axis.1.root.firstAxis ≠ axis.1.root.terminal := by
    intro equal
    rw [equal] at doubleBond
    simp [input.moleculeGraph.bond_self] at doubleBond
  refine ⟨?_, ?_, ?_, doubleBond⟩
  · simp [localizedEvenAxialFirstChildNode, OfficialCIPNode.extend,
      OfficialCIPNode.childProvenance, OfficialCIPNode.root, distinct]
  · rfl
  · rfl

/-- The distinguished final occurrence is present for every detected center. -/
noncomputable def localizedFinalOccurrence
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (center : input.TetrahedralCenter) : input.LocalizedCIPOccurrence fuel := by
  classical
  refine ⟨
    { root := center.1
      address := []
      node := OfficialCIPNode.root center.1
      remaining := fuel + 1 }, ?_⟩
  apply (input.mem_localizedOccurrences_iff fuel _).mpr
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [] (fuel + 1)
    (OfficialCIPNode.root center.1)

/-- Dependency permitted for localized auxiliary evaluation: the source must be a strictly
deeper occurrence under the same final-center root. -/
def LocalizedDepthDependency
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (source target : input.LocalizedCIPOccurrence fuel) : Prop :=
  source.1.root = target.1.root ∧
    target.1.address.length < source.1.address.length

/-- The first-axis occurrence is a legal strict dependency of its terminal-root target. -/
theorem localizedEvenAxialFirstChildOccurrence_dependency
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (axis : input.LocalizedEvenAxialChain) :
    input.LocalizedDepthDependency
      (input.localizedEvenAxialFirstChildOccurrence fuel axis)
      (input.localizedEvenAxialRootOccurrence fuel axis) := by
  constructor
  · simp
  · simp

instance localizedDepthDependencyDecidable
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (source target : input.LocalizedCIPOccurrence fuel) :
    Decidable (input.LocalizedDepthDependency source target) := by
  unfold LocalizedDepthDependency
  infer_instance

/-- Strict root-relative depth dependency is transitive. -/
theorem localizedDepthDependency_trans
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {first second third : input.LocalizedCIPOccurrence fuel}
    (firstSecond : input.LocalizedDepthDependency first second)
    (secondThird : input.LocalizedDepthDependency second third) :
    input.LocalizedDepthDependency first third :=
  ⟨firstSecond.1.trans secondThird.1,
    Nat.lt_trans secondThird.2 firstSecond.2⟩

/-- Strict root-relative depth dependency is irreflexive. -/
theorem localizedDepthDependency_irrefl
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    ¬ input.LocalizedDepthDependency occurrence occurrence := by
  intro dependency
  exact (Nat.lt_irrefl _ dependency.2).elim

/-- A permitted source has strictly less remaining expansion depth than its target.  This is the
causal measure used by the fixed-point construction. -/
theorem localizedDepthDependency_remaining_lt
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {source target : input.LocalizedCIPOccurrence fuel}
    (dependency : input.LocalizedDepthDependency source target) :
    source.1.remaining < target.1.remaining := by
  rcases dependency with ⟨_sameRoot, deeper⟩
  have sourceGrade := input.localizedCIPOccurrence_depthGrade source
  have targetGrade := input.localizedCIPOccurrence_depthGrade target
  omega

/-- Exact depth grading makes deeper-source dependency well founded. -/
theorem localizedDepthDependency_wellFounded
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    WellFounded (@input.LocalizedDepthDependency fuel) := by
  refine Subrelation.wf ?_
    (InvImage.wf (fun occurrence : input.LocalizedCIPOccurrence fuel =>
      occurrence.1.remaining) (Nat.lt_wfRel).2)
  intro source target dependency
  exact input.localizedDepthDependency_remaining_lt dependency

/-- Every default-bound ligand root represented by the carrier is a complete official expansion,
not a fuel-truncated prefix. -/
theorem localizedOccurrenceDefaultLigandRoot_complete
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    MoleculeGraph.OfficialExpansionCompleteWithin
      input.executableOfficialCIPChildren
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center index)) :=
  input.executableOfficialExpansionCompleteWithin_default center index

/-- Occurrence-local recognition retains the exact provenance frame.  In particular, duplicate
nodes never become descriptor sources and two rerootings of one atom remain distinct inputs. -/
def localizedOccurrenceDescriptorCenter?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    Option input.TetrahedralCenter :=
  input.realTetrahedralCenterAtNode? occurrence.1.node

/-- Successful descriptor-source recognition is exactly the existing proof-facing real-center
predicate at this occurrence's provenance-bearing node. -/
theorem localizedOccurrenceDescriptorCenter?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (center : input.TetrahedralCenter) :
    input.localizedOccurrenceDescriptorCenter? occurrence = some center ↔
      input.RealTetrahedralCenterNode occurrence.1.node center :=
  input.realTetrahedralCenterAtNode?_eq_some_iff occurrence.1.node center

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
