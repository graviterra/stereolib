import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceFixedPoint

set_option autoImplicit false

/-!
# Naturality of the source-canonical occurrence carrier

Constitutional atom automorphisms transport official CIP nodes, child membership, declarative
subtrees, and finite carrier membership.  Child slots are reconstructed rather than assumed
fixed: source-index enumeration may renumber them under a non-monotone atom permutation.
-/

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-- Transport an official CIP node through a permutation of physical source atoms. -/
def mapAromaticCanonicalOfficialCIPNode
    {source : AuthoritativeChemicalInput}
    (permutation : Equiv.Perm source.AromaticCanonicalAtom)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    OfficialCIPNode source.AromaticCanonicalAtom :=
  { current? := node.current?.map permutation
    history := node.history.map permutation
    provenance := node.provenance }

/-- Exact constitution automorphism of the finite source-canonical chemical graph. -/
def AromaticCanonicalConstitutionAutomorphism
    (source : AuthoritativeChemicalInput)
    (permutation : Equiv.Perm source.AromaticCanonicalAtom) : Prop :=
  (∀ atom,
      source.molecule.atoms.get (permutation atom) =
        source.molecule.atoms.get atom) ∧
    (∀ left right,
      source.molecule.aromaticCanonicalBondOrder left.val right.val =
        source.molecule.aromaticCanonicalBondOrder
          (permutation left).val (permutation right).val) ∧
    (∀ left right,
      source.molecule.aromaticPairEdges.contains
          (semanticEdgeKey left.val right.val) =
        source.molecule.aromaticPairEdges.contains
          (semanticEdgeKey (permutation left).val (permutation right).val))

/-- Mapping physical atoms is an equivalence on official CIP nodes. -/
def aromaticCanonicalOfficialCIPNodePermutation
    {source : AuthoritativeChemicalInput}
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom) :
    Equiv.Perm (OfficialCIPNode source.AromaticCanonicalAtom) where
  toFun := mapAromaticCanonicalOfficialCIPNode atomPermutation
  invFun := mapAromaticCanonicalOfficialCIPNode atomPermutation.symm
  left_inv := by
    intro node
    cases node
    simp [mapAromaticCanonicalOfficialCIPNode]
  right_inv := by
    intro node
    cases node
    simp [mapAromaticCanonicalOfficialCIPNode]

theorem firstIndexOf?_map_equiv
    {V : Type*} [DecidableEq V] (permutation : Equiv.Perm V)
    (target : V) : ∀ values : List V,
    firstIndexOf? (permutation target) (values.map permutation) =
      firstIndexOf? target values
  | [] => rfl
  | value :: values => by
      by_cases equal : value = target
      · subst value
        simp [firstIndexOf?]
      · have mappedDifferent : permutation value ≠ permutation target :=
          fun mappedEqual => equal (permutation.injective mappedEqual)
        simp [firstIndexOf?, equal, mappedDifferent,
          firstIndexOf?_map_equiv permutation target values]

theorem mapAromaticCanonicalOfficialCIPNode_extend
    {source : AuthoritativeChemicalInput}
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (node : OfficialCIPNode source.AromaticCanonicalAtom)
    (next : source.AromaticCanonicalAtom) (copyIndex : Nat) :
    mapAromaticCanonicalOfficialCIPNode atomPermutation
        (node.extend next copyIndex) =
      (mapAromaticCanonicalOfficialCIPNode atomPermutation node).extend
        (atomPermutation next) copyIndex := by
  cases node with
  | mk current history provenance =>
      have mappedIndex :
          firstIndexOf? (atomPermutation next)
              (history.map atomPermutation).reverse =
            firstIndexOf? next history.reverse := by
        simpa using firstIndexOf?_map_equiv atomPermutation next history.reverse
      simp [mapAromaticCanonicalOfficialCIPNode, OfficialCIPNode.extend,
        OfficialCIPNode.childProvenance, OfficialCIPNode.duplicateRootDistance,
        OfficialCIPNode.depth, mappedIndex,
        atomPermutation.injective.eq_iff]

theorem mem_aromaticCanonicalOrdinaryNeighborCopiesAt_iff
    (molecule : SemanticMolecule) (size : Nat) (atom : Fin size)
    (copy : Fin size × Nat) :
    copy ∈ molecule.aromaticCanonicalOrdinaryNeighborCopiesAt size atom ↔
      copy.2 < molecule.aromaticCanonicalBondOrder atom.val copy.1.val := by
  rcases copy with ⟨neighbor, copyIndex⟩
  simp [SemanticMolecule.aromaticCanonicalOrdinaryNeighborCopiesAt]

theorem aromaticCanonicalOrdinaryNeighborCopiesAt_mem_map_iff
    (source : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (constitution : source.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (atom neighbor : source.AromaticCanonicalAtom) (copyIndex : Nat) :
    (atomPermutation neighbor, copyIndex) ∈
        source.molecule.aromaticCanonicalOrdinaryNeighborCopiesAt
          source.molecule.atomCount (atomPermutation atom) ↔
      (neighbor, copyIndex) ∈
        source.molecule.aromaticCanonicalOrdinaryNeighborCopiesAt
          source.molecule.atomCount atom := by
  rw [mem_aromaticCanonicalOrdinaryNeighborCopiesAt_iff,
    mem_aromaticCanonicalOrdinaryNeighborCopiesAt_iff]
  rw [← constitution.2.1 atom neighbor]

theorem mapAromaticCanonicalOfficialCIPNode_parent?
    {source : AuthoritativeChemicalInput}
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    (mapAromaticCanonicalOfficialCIPNode atomPermutation node).parent? =
      node.parent?.map atomPermutation := by
  cases node with
  | mk current history provenance =>
      cases history with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil => rfl
          | cons parent rest => rfl

theorem aromaticCanonicalChildCopiesAt_mem_map_iff
    (source : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (constitution : source.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (node : OfficialCIPNode source.AromaticCanonicalAtom)
    (neighbor : source.AromaticCanonicalAtom) (copyIndex : Nat) :
    (atomPermutation neighbor, copyIndex) ∈
        source.molecule.aromaticCanonicalChildCopiesAt
          source.molecule.atomCount
          (mapAromaticCanonicalOfficialCIPNode atomPermutation node) ↔
      (neighbor, copyIndex) ∈
        source.molecule.aromaticCanonicalChildCopiesAt
          source.molecule.atomCount node := by
  unfold SemanticMolecule.aromaticCanonicalChildCopiesAt
  rw [mapAromaticCanonicalOfficialCIPNode_parent?]
  cases current : node.current? with
  | none => simp [mapAromaticCanonicalOfficialCIPNode, current]
  | some atom =>
      simp only [mapAromaticCanonicalOfficialCIPNode, current, Option.map_some]
      cases parent : node.parent? with
      | none =>
          simp only [Option.map_none]
          exact aromaticCanonicalOrdinaryNeighborCopiesAt_mem_map_iff
            source atomPermutation constitution atom neighbor copyIndex
      | some previous =>
          simp only [Option.map_some, List.mem_filter]
          rw [aromaticCanonicalOrdinaryNeighborCopiesAt_mem_map_iff
            source atomPermutation constitution atom neighbor copyIndex]
          simp [atomPermutation.injective.eq_iff]

theorem aromaticCanonicalMancudeRepresentativeAt?_eq_none_of_no_edges
    (molecule : SemanticMolecule) (size : Nat)
    (noEdges : molecule.aromaticPairEdges = []) (atom : Fin size) :
    molecule.aromaticCanonicalMancudeRepresentativeAt? size atom = none := by
  simp [SemanticMolecule.aromaticCanonicalMancudeRepresentativeAt?, noEdges]

@[simp] theorem mapAromaticCanonicalOfficialCIPNode_isDuplicateLeaf
    {source : AuthoritativeChemicalInput}
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    (mapAromaticCanonicalOfficialCIPNode atomPermutation node).isDuplicateLeaf =
      node.isDuplicateLeaf := by
  rfl

theorem aromaticCanonicalOfficialCIPChildrenAt_mem_map_iff_of_no_edges
    (source : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (constitution : source.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (noEdges : source.molecule.aromaticPairEdges = [])
    (node child : OfficialCIPNode source.AromaticCanonicalAtom) :
    mapAromaticCanonicalOfficialCIPNode atomPermutation child ∈
        source.molecule.aromaticCanonicalOfficialCIPChildrenAt
          source.molecule.atomCount
          (mapAromaticCanonicalOfficialCIPNode atomPermutation node) ↔
      child ∈ source.molecule.aromaticCanonicalOfficialCIPChildrenAt
        source.molecule.atomCount node := by
  by_cases duplicate : node.isDuplicateLeaf = true
  · have mappedDuplicate :
        (mapAromaticCanonicalOfficialCIPNode atomPermutation node).isDuplicateLeaf = true := by
      simpa using duplicate
    rw [source.molecule.aromaticCanonicalOfficialCIPChildrenAt_of_duplicateLeaf
      source.molecule.atomCount duplicate]
    rw [source.molecule.aromaticCanonicalOfficialCIPChildrenAt_of_duplicateLeaf
      source.molecule.atomCount mappedDuplicate]
    simp only [List.not_mem_nil]
  · have mappedDuplicate :
        (mapAromaticCanonicalOfficialCIPNode atomPermutation node).isDuplicateLeaf ≠ true := by
      simpa using duplicate
    rw [SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt,
      SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt,
      if_neg duplicate, if_neg mappedDuplicate]
    have noRepresentative (atom : source.AromaticCanonicalAtom) :
        source.molecule.aromaticCanonicalMancudeRepresentativeAt?
          source.molecule.atomCount atom = none :=
      aromaticCanonicalMancudeRepresentativeAt?_eq_none_of_no_edges
        source.molecule source.molecule.atomCount noEdges atom
    cases current : node.current? with
    | none =>
      have mappedCurrent :
          (mapAromaticCanonicalOfficialCIPNode atomPermutation node).current? = none := by
        simp [mapAromaticCanonicalOfficialCIPNode, current]
      simp [SemanticMolecule.aromaticCanonicalChildCopiesAt, current, mappedCurrent]
    | some atom =>
      have mappedCurrent :
          (mapAromaticCanonicalOfficialCIPNode atomPermutation node).current? =
            some (atomPermutation atom) := by
        simp [mapAromaticCanonicalOfficialCIPNode, current]
      rw [mappedCurrent]
      dsimp only
      rw [noRepresentative atom, noRepresentative (atomPermutation atom)]
      simp only [List.append_nil, List.mem_map]
      constructor
      · rintro ⟨copy, copyPresent, mappedChildEq⟩
        rcases copy with ⟨neighbor, copyIndex⟩
        let originalNeighbor := atomPermutation.symm neighbor
        have mappedCopyPresent :
            (atomPermutation originalNeighbor, copyIndex) ∈
              source.molecule.aromaticCanonicalChildCopiesAt
                source.molecule.atomCount
                (mapAromaticCanonicalOfficialCIPNode atomPermutation node) := by
          simpa [originalNeighbor] using copyPresent
        have originalCopyPresent :=
          (aromaticCanonicalChildCopiesAt_mem_map_iff source atomPermutation
            constitution node originalNeighbor copyIndex).mp mappedCopyPresent
        refine ⟨(originalNeighbor, copyIndex), originalCopyPresent, ?_⟩
        apply (aromaticCanonicalOfficialCIPNodePermutation atomPermutation).injective
        calc
          mapAromaticCanonicalOfficialCIPNode atomPermutation
              (node.extend originalNeighbor copyIndex) =
              (mapAromaticCanonicalOfficialCIPNode atomPermutation node).extend
                (atomPermutation originalNeighbor) copyIndex :=
            mapAromaticCanonicalOfficialCIPNode_extend atomPermutation node
              originalNeighbor copyIndex
          _ = mapAromaticCanonicalOfficialCIPNode atomPermutation child := by
            simpa [originalNeighbor] using mappedChildEq
      · rintro ⟨copy, copyPresent, rfl⟩
        rcases copy with ⟨neighbor, copyIndex⟩
        refine ⟨(atomPermutation neighbor, copyIndex), ?_, ?_⟩
        · exact (aromaticCanonicalChildCopiesAt_mem_map_iff source atomPermutation
            constitution node neighbor copyIndex).mpr copyPresent
        · exact (mapAromaticCanonicalOfficialCIPNode_extend atomPermutation node
            neighbor copyIndex).symm

theorem exists_mem_zipIdx_of_mem
    {V : Type*} {value : V} {values : List V} (present : value ∈ values) :
    ∃ slot, (value, slot) ∈ values.zipIdx := by
  rw [List.mem_iff_getElem] at present
  rcases present with ⟨slot, slotBound, valueAtSlot⟩
  refine ⟨slot, ?_⟩
  have zippedBound : slot < values.zipIdx.length := by
    simpa using slotBound
  have zippedPresent : values.zipIdx[slot] ∈ values.zipIdx :=
    List.getElem_mem zippedBound
  rw [List.getElem_zipIdx] at zippedPresent
  simpa [valueAtSlot] using zippedPresent

/-- Atom naturality preserves child existence but permits source-index slot renumbering. -/
theorem exists_mapped_aromaticCanonicalOfficialCIPChild_slot_of_no_edges
    (source : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (constitution : source.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (noEdges : source.molecule.aromaticPairEdges = [])
    (node child : OfficialCIPNode source.AromaticCanonicalAtom) (slot : Nat)
    (childAtSlot : (child, slot) ∈
      (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
        source.molecule.atomCount node).zipIdx) :
    ∃ mappedSlot,
      (mapAromaticCanonicalOfficialCIPNode atomPermutation child, mappedSlot) ∈
        (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
          source.molecule.atomCount
          (mapAromaticCanonicalOfficialCIPNode atomPermutation node)).zipIdx := by
  have childPresent := List.fst_mem_of_mem_zipIdx childAtSlot
  have mappedChildPresent :=
    (aromaticCanonicalOfficialCIPChildrenAt_mem_map_iff_of_no_edges
      source atomPermutation constitution noEdges node child).mpr childPresent
  exact exists_mem_zipIdx_of_mem mappedChildPresent

/-- Declarative reachability is natural under a constitutional atom automorphism.  The address
is rebuilt one child at a time while length, root, node, and remaining depth are preserved. -/
theorem exists_mapped_declarativeAromaticCanonicalOccurrenceSubtree_of_no_edges
    (source : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (constitution : source.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (noEdges : source.molecule.aromaticPairEdges = [])
    (root : source.AromaticCanonicalAtom)
    {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode source.AromaticCanonicalAtom}
    {occurrence : source.AromaticCanonicalOccurrenceFrame}
    (derived : source.DeclarativeAromaticCanonicalOccurrenceSubtree
      root path fuel node occurrence) :
    ∀ mappedPath, mappedPath.length = path.length →
      ∃ mappedAddress,
        mappedAddress.length = occurrence.address.length ∧
        source.DeclarativeAromaticCanonicalOccurrenceSubtree
          (atomPermutation root) mappedPath fuel
          (mapAromaticCanonicalOfficialCIPNode atomPermutation node)
          { root := atomPermutation occurrence.root
            address := mappedAddress
            node := mapAromaticCanonicalOfficialCIPNode atomPermutation occurrence.node
            remaining := occurrence.remaining } := by
  induction derived with
  | subtreeRoot path fuel node =>
      intro mappedPath mappedPathLength
      exact ⟨mappedPath, mappedPathLength,
        DeclarativeAromaticCanonicalOccurrenceSubtree.subtreeRoot
          mappedPath fuel (mapAromaticCanonicalOfficialCIPNode atomPermutation node)⟩
  | @subtreeDescendant path fuel node child slot occurrence childAtSlot descendant
      inductionHypothesis =>
      intro mappedPath mappedPathLength
      obtain ⟨mappedSlot, mappedChildAtSlot⟩ :=
        exists_mapped_aromaticCanonicalOfficialCIPChild_slot_of_no_edges
          source atomPermutation constitution noEdges node child slot childAtSlot
      have mappedDescendantPathLength :
          (mappedPath ++ [mappedSlot]).length = (path ++ [slot]).length := by
        simp [mappedPathLength]
      obtain ⟨mappedAddress, mappedAddressLength, mappedDescendant⟩ :=
        inductionHypothesis (mappedPath ++ [mappedSlot]) mappedDescendantPathLength
      exact ⟨mappedAddress, mappedAddressLength,
        DeclarativeAromaticCanonicalOccurrenceSubtree.subtreeDescendant
          mappedChildAtSlot mappedDescendant⟩

/-- Carrier closure follows from independent reachability without evaluating the finite carrier. -/
theorem exists_mapped_aromaticCanonicalOccurrence_of_no_edges
    (source : AuthoritativeChemicalInput) (fuel : Nat)
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (constitution : source.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (noEdges : source.molecule.aromaticPairEdges = [])
    (occurrence : source.AromaticCanonicalOccurrence fuel) :
    ∃ mappedOccurrence : source.AromaticCanonicalOccurrence fuel,
      mappedOccurrence.1.root = atomPermutation occurrence.1.root ∧
      mappedOccurrence.1.address.length = occurrence.1.address.length ∧
      mappedOccurrence.1.node =
        mapAromaticCanonicalOfficialCIPNode atomPermutation occurrence.1.node ∧
      mappedOccurrence.1.remaining = occurrence.1.remaining := by
  have derived := (source.mem_aromaticCanonicalOccurrences_iff
    fuel occurrence.1).mp occurrence.2
  change source.DeclarativeAromaticCanonicalOccurrenceSubtree
    occurrence.1.root [] (fuel + 1) (OfficialCIPNode.root occurrence.1.root)
      occurrence.1 at derived
  obtain ⟨mappedAddress, mappedAddressLength, mappedDerived⟩ :=
    exists_mapped_declarativeAromaticCanonicalOccurrenceSubtree_of_no_edges
      source atomPermutation constitution noEdges occurrence.1.root derived [] rfl
  let mappedFrame : source.AromaticCanonicalOccurrenceFrame :=
    { root := atomPermutation occurrence.1.root
      address := mappedAddress
      node := mapAromaticCanonicalOfficialCIPNode atomPermutation occurrence.1.node
      remaining := occurrence.1.remaining }
  have mappedPresent : mappedFrame ∈ source.aromaticCanonicalOccurrences fuel := by
    rw [source.mem_aromaticCanonicalOccurrences_iff]
    change source.DeclarativeAromaticCanonicalOccurrenceSubtree
      mappedFrame.root [] (fuel + 1) (OfficialCIPNode.root mappedFrame.root) mappedFrame
    simpa [mappedFrame, mapAromaticCanonicalOfficialCIPNode,
      OfficialCIPNode.root] using mappedDerived
  exact ⟨⟨mappedFrame, mappedPresent⟩, rfl, mappedAddressLength, rfl, rfl⟩

/-! ## Canonical child slots -/

theorem aromaticCanonicalOrdinaryNeighborCopiesAt_nodup
    (molecule : SemanticMolecule) (size : Nat) (atom : Fin size) :
    (molecule.aromaticCanonicalOrdinaryNeighborCopiesAt size atom).Nodup := by
  rw [SemanticMolecule.aromaticCanonicalOrdinaryNeighborCopiesAt, List.nodup_flatMap]
  constructor
  · intro neighbor _
    apply List.Nodup.map
    · intro left right equal
      exact congrArg Prod.snd equal
    · exact List.nodup_range
  · exact (List.nodup_finRange size).imp fun {left right} different => by
      rw [Function.onFun, List.disjoint_left]
      intro copy leftPresent rightPresent
      rcases List.mem_map.mp leftPresent with ⟨leftIndex, _, leftEq⟩
      rcases List.mem_map.mp rightPresent with ⟨rightIndex, _, rightEq⟩
      apply different
      exact (congrArg Prod.fst leftEq).trans (congrArg Prod.fst rightEq).symm

theorem aromaticCanonicalChildCopiesAt_nodup
    (molecule : SemanticMolecule) (size : Nat)
    (node : OfficialCIPNode (Fin size)) :
    (molecule.aromaticCanonicalChildCopiesAt size node).Nodup := by
  unfold SemanticMolecule.aromaticCanonicalChildCopiesAt
  cases node.current? with
  | none => exact List.nodup_nil
  | some current =>
      cases node.parent? with
      | none => exact aromaticCanonicalOrdinaryNeighborCopiesAt_nodup molecule size current
      | some parent =>
          exact (aromaticCanonicalOrdinaryNeighborCopiesAt_nodup molecule size current).filter _

theorem aromaticCanonicalChildCopiesAt_copyIndex_eq_zero_of_single
    (molecule : SemanticMolecule) (size : Nat)
    (single : ∀ left right : Fin size,
      molecule.aromaticCanonicalBondOrder left.val right.val ≤ 1)
    (node : OfficialCIPNode (Fin size)) (copy : Fin size × Nat)
    (present : copy ∈ molecule.aromaticCanonicalChildCopiesAt size node) :
    copy.2 = 0 := by
  unfold SemanticMolecule.aromaticCanonicalChildCopiesAt at present
  cases current : node.current? with
  | none => simp [current] at present
  | some atom =>
      rw [current] at present
      cases parent : node.parent? with
      | none =>
          rw [parent] at present
          have below := (mem_aromaticCanonicalOrdinaryNeighborCopiesAt_iff
            molecule size atom copy).mp present
          have atMostOne := single atom copy.1
          omega
      | some previous =>
          rw [parent] at present
          have ordinaryPresent :
              copy ∈ molecule.aromaticCanonicalOrdinaryNeighborCopiesAt size atom :=
            (List.mem_filter.mp present).1
          have below := (mem_aromaticCanonicalOrdinaryNeighborCopiesAt_iff
            molecule size atom copy).mp ordinaryPresent
          have atMostOne := single atom copy.1
          omega

theorem aromaticCanonicalChildCopiesAt_map_extend_nodup_of_single
    (molecule : SemanticMolecule) (size : Nat)
    (single : ∀ left right : Fin size,
      molecule.aromaticCanonicalBondOrder left.val right.val ≤ 1)
    (node : OfficialCIPNode (Fin size)) :
    ((molecule.aromaticCanonicalChildCopiesAt size node).map fun copy =>
      node.extend copy.1 copy.2).Nodup := by
  apply List.Nodup.map_on
  · intro left leftPresent right rightPresent extendedEqual
    have leftZero :=
      aromaticCanonicalChildCopiesAt_copyIndex_eq_zero_of_single
        molecule size single node left leftPresent
    have rightZero :=
      aromaticCanonicalChildCopiesAt_copyIndex_eq_zero_of_single
        molecule size single node right rightPresent
    have neighborsEqual : left.1 = right.1 := by
      have currentEqual := congrArg OfficialCIPNode.current? extendedEqual
      simpa [OfficialCIPNode.extend] using currentEqual
    exact Prod.ext neighborsEqual (leftZero.trans rightZero.symm)
  · exact aromaticCanonicalChildCopiesAt_nodup molecule size node

theorem aromaticCanonicalOfficialCIPChildrenAt_nodup_of_no_edges_of_single
    (molecule : SemanticMolecule) (size : Nat)
    (noEdges : molecule.aromaticPairEdges = [])
    (single : ∀ left right : Fin size,
      molecule.aromaticCanonicalBondOrder left.val right.val ≤ 1)
    (node : OfficialCIPNode (Fin size)) :
    (molecule.aromaticCanonicalOfficialCIPChildrenAt size node).Nodup := by
  by_cases duplicate : node.isDuplicateLeaf = true
  · rw [molecule.aromaticCanonicalOfficialCIPChildrenAt_of_duplicateLeaf size duplicate]
    exact List.nodup_nil
  · rw [SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt, if_neg duplicate]
    have noRepresentative (atom : Fin size) :
        molecule.aromaticCanonicalMancudeRepresentativeAt? size atom = none :=
      aromaticCanonicalMancudeRepresentativeAt?_eq_none_of_no_edges
        molecule size noEdges atom
    cases current : node.current? with
    | none =>
        dsimp only
        rw [List.append_nil]
        change ((molecule.aromaticCanonicalChildCopiesAt size node).map fun copy =>
          node.extend copy.1 copy.2).Nodup
        exact aromaticCanonicalChildCopiesAt_map_extend_nodup_of_single
          molecule size single node
    | some atom =>
        dsimp only
        rw [noRepresentative atom, List.append_nil]
        exact aromaticCanonicalChildCopiesAt_map_extend_nodup_of_single
          molecule size single node

theorem zipIdx_slot_unique_of_nodup
    {V : Type*} {values : List V} (nodup : values.Nodup)
    {value : V} {firstSlot secondSlot : Nat}
    (firstPresent : (value, firstSlot) ∈ values.zipIdx)
    (secondPresent : (value, secondSlot) ∈ values.zipIdx) :
    firstSlot = secondSlot := by
  have firstValue := List.fst_eq_of_mem_zipIdx firstPresent
  have secondValue := List.fst_eq_of_mem_zipIdx secondPresent
  exact nodup.getElem_inj_iff.mp (firstValue.symm.trans secondValue)

theorem existsUnique_mapped_aromaticCanonicalOfficialCIPChild_slot_of_no_edges_of_nodup
    (source : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (constitution : source.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (noEdges : source.molecule.aromaticPairEdges = [])
    (childrenNodup : ∀ candidate,
      (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
        source.molecule.atomCount candidate).Nodup)
    (node child : OfficialCIPNode source.AromaticCanonicalAtom) (slot : Nat)
    (childAtSlot : (child, slot) ∈
      (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
        source.molecule.atomCount node).zipIdx) :
    ∃! mappedSlot,
      (mapAromaticCanonicalOfficialCIPNode atomPermutation child, mappedSlot) ∈
        (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
          source.molecule.atomCount
          (mapAromaticCanonicalOfficialCIPNode atomPermutation node)).zipIdx := by
  obtain ⟨mappedSlot, mappedPresent⟩ :=
    exists_mapped_aromaticCanonicalOfficialCIPChild_slot_of_no_edges
      source atomPermutation constitution noEdges node child slot childAtSlot
  refine ⟨mappedSlot, mappedPresent, ?_⟩
  intro candidateSlot candidatePresent
  exact zipIdx_slot_unique_of_nodup
    (childrenNodup (mapAromaticCanonicalOfficialCIPNode atomPermutation node))
      candidatePresent mappedPresent

noncomputable def canonicalMappedAromaticCanonicalOfficialCIPChildSlot
    (source : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (constitution : source.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (noEdges : source.molecule.aromaticPairEdges = [])
    (childrenNodup : ∀ candidate,
      (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
        source.molecule.atomCount candidate).Nodup)
    (node child : OfficialCIPNode source.AromaticCanonicalAtom) (slot : Nat)
    (childAtSlot : (child, slot) ∈
      (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
        source.molecule.atomCount node).zipIdx) : Nat :=
  Classical.choose <|
    existsUnique_mapped_aromaticCanonicalOfficialCIPChild_slot_of_no_edges_of_nodup
      source atomPermutation constitution noEdges childrenNodup
        node child slot childAtSlot

theorem canonicalMappedAromaticCanonicalOfficialCIPChildSlot_mem
    (source : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (constitution : source.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (noEdges : source.molecule.aromaticPairEdges = [])
    (childrenNodup : ∀ candidate,
      (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
        source.molecule.atomCount candidate).Nodup)
    (node child : OfficialCIPNode source.AromaticCanonicalAtom) (slot : Nat)
    (childAtSlot : (child, slot) ∈
      (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
        source.molecule.atomCount node).zipIdx) :
    (mapAromaticCanonicalOfficialCIPNode atomPermutation child,
      canonicalMappedAromaticCanonicalOfficialCIPChildSlot source atomPermutation
        constitution noEdges childrenNodup node child slot childAtSlot) ∈
      (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
        source.molecule.atomCount
        (mapAromaticCanonicalOfficialCIPNode atomPermutation node)).zipIdx :=
  (Classical.choose_spec <|
    existsUnique_mapped_aromaticCanonicalOfficialCIPChild_slot_of_no_edges_of_nodup
      source atomPermutation constitution noEdges childrenNodup
        node child slot childAtSlot).1

theorem mapAromaticCanonicalOfficialCIPNode_involutive
    {source : AuthoritativeChemicalInput}
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (involutive : Function.Involutive atomPermutation)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    mapAromaticCanonicalOfficialCIPNode atomPermutation
      (mapAromaticCanonicalOfficialCIPNode atomPermutation node) = node := by
  cases node
  simp [mapAromaticCanonicalOfficialCIPNode, involutive]

theorem canonicalMappedAromaticCanonicalOfficialCIPChildSlot_involutive
    (source : AuthoritativeChemicalInput)
    (atomPermutation : Equiv.Perm source.AromaticCanonicalAtom)
    (constitution : source.AromaticCanonicalConstitutionAutomorphism atomPermutation)
    (involutive : Function.Involutive atomPermutation)
    (noEdges : source.molecule.aromaticPairEdges = [])
    (childrenNodup : ∀ candidate,
      (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
        source.molecule.atomCount candidate).Nodup)
    (node child : OfficialCIPNode source.AromaticCanonicalAtom) (slot : Nat)
    (childAtSlot : (child, slot) ∈
      (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
        source.molecule.atomCount node).zipIdx) :
    let firstSlot :=
      canonicalMappedAromaticCanonicalOfficialCIPChildSlot source atomPermutation
        constitution noEdges childrenNodup node child slot childAtSlot
    let firstAtSlot :=
      canonicalMappedAromaticCanonicalOfficialCIPChildSlot_mem source atomPermutation
        constitution noEdges childrenNodup node child slot childAtSlot
    canonicalMappedAromaticCanonicalOfficialCIPChildSlot source atomPermutation
      constitution noEdges childrenNodup
      (mapAromaticCanonicalOfficialCIPNode atomPermutation node)
      (mapAromaticCanonicalOfficialCIPNode atomPermutation child) firstSlot firstAtSlot = slot := by
  dsimp only
  let firstSlot :=
    canonicalMappedAromaticCanonicalOfficialCIPChildSlot source atomPermutation
      constitution noEdges childrenNodup node child slot childAtSlot
  have firstAtSlot :=
    canonicalMappedAromaticCanonicalOfficialCIPChildSlot_mem source atomPermutation
      constitution noEdges childrenNodup node child slot childAtSlot
  have secondAtSlot :=
    canonicalMappedAromaticCanonicalOfficialCIPChildSlot_mem source atomPermutation
      constitution noEdges childrenNodup
      (mapAromaticCanonicalOfficialCIPNode atomPermutation node)
      (mapAromaticCanonicalOfficialCIPNode atomPermutation child) firstSlot firstAtSlot
  have secondAtSlot' :
      (child,
        canonicalMappedAromaticCanonicalOfficialCIPChildSlot source atomPermutation
          constitution noEdges childrenNodup
          (mapAromaticCanonicalOfficialCIPNode atomPermutation node)
          (mapAromaticCanonicalOfficialCIPNode atomPermutation child) firstSlot firstAtSlot) ∈
        (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
          source.molecule.atomCount node).zipIdx := by
    simpa [mapAromaticCanonicalOfficialCIPNode_involutive atomPermutation involutive] using
      secondAtSlot
  exact zipIdx_slot_unique_of_nodup (childrenNodup node) secondAtSlot' childAtSlot

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
