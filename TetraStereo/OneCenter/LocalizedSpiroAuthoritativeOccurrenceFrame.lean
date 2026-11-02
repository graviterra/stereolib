import TetraStereo.OneCenter.LocalizedTetrahedralSpiroIncidenceCompleteness
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeMoleculeCanonicalReadinessCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace SemanticMolecule

/-- The direct localized-CIP admission domain contains no still-aromatic interaction. -/
theorem aromaticPairEdges_eq_nil_of_localizedCovalentPairsOnly
    (molecule : SemanticMolecule)
    (localized : molecule.LocalizedCovalentPairsOnly) :
    molecule.aromaticPairEdges = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro edge present
  rw [aromaticPairEdges, List.mem_filterMap] at present
  obtain ⟨interaction, interactionPresent, observed⟩ := present
  rcases localized interaction interactionPresent with
    ⟨left, right, order, participants, kind, positive⟩
  simp [aromaticPairEdge?, participants, kind] at observed

/-- Hence source-canonical bond multiplicity is literal localized bond multiplicity on this
domain. -/
theorem aromaticCanonicalBondOrder_eq_localizedBondOrder_of_localizedCovalentPairsOnly
    (molecule : SemanticMolecule)
    (localized : molecule.LocalizedCovalentPairsOnly)
    (left right : Nat) :
    molecule.aromaticCanonicalBondOrder left right =
      molecule.localizedBondOrder left right := by
  rw [aromaticCanonicalBondOrder,
    molecule.aromaticPairEdges_eq_nil_of_localizedCovalentPairsOnly localized]
  simp

end SemanticMolecule

namespace CertifiedLocalizedCIPInput

/-- Every source-canonical adjacent atom occurs as the real zero-copy child of the authoritative
root occurrence. -/
theorem root_extend_zero_mem_aromaticCanonicalOfficialCIPChildrenAt_of_adjacent
    (input : CertifiedLocalizedCIPInput) (center branch : input.Atom)
    (adjacent : input.certified.input.AromaticCanonicalAdjacent center branch) :
    (OfficialCIPNode.root center).extend branch 0 ∈
      input.certified.input.molecule.aromaticCanonicalOfficialCIPChildrenAt
        input.certified.input.molecule.atomCount (OfficialCIPNode.root center) := by
  let source := input.certified.input
  have graphAdjacent : input.moleculeGraph.Adj center branch :=
    (input.moleculeGraph_adj_iff_aromaticCanonicalAdjacent center branch).mpr adjacent
  have positive : 0 < source.molecule.localizedBondOrder center.val branch.val := by
    exact graphAdjacent
  have bondOrder :=
    source.molecule.aromaticCanonicalBondOrder_eq_localizedBondOrder_of_localizedCovalentPairsOnly
      input.graphReady.2.2.2.1 center.val branch.val
  have ordinaryPresent :
      (branch, 0) ∈ source.molecule.aromaticCanonicalOrdinaryNeighborCopiesAt
        source.molecule.atomCount center := by
    rw [SemanticMolecule.aromaticCanonicalOrdinaryNeighborCopiesAt,
      List.mem_flatMap]
    refine ⟨branch, by simp, ?_⟩
    rw [List.mem_map]
    exact ⟨0, by simp [bondOrder, positive], rfl⟩
  have childCopyPresent :
      (branch, 0) ∈ source.molecule.aromaticCanonicalChildCopiesAt
        source.molecule.atomCount (OfficialCIPNode.root center) := by
    simpa [SemanticMolecule.aromaticCanonicalChildCopiesAt,
      OfficialCIPNode.root, OfficialCIPNode.current?, OfficialCIPNode.parent?] using
        ordinaryPresent
  have notLeaf : ¬(OfficialCIPNode.root center).isDuplicateLeaf = true := by
    simp [OfficialCIPNode.root, OfficialCIPNode.isDuplicateLeaf]
  unfold SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt
  rw [if_neg notLeaf]
  apply List.mem_append.mpr
  apply Or.inl
  rw [List.mem_map]
  exact ⟨(branch, 0), childCopyPresent, rfl⟩

/-- Canonical slot of the real zero-copy child for one source-canonical neighbor. -/
noncomputable def authoritativeRootBranchChildIndex
    (input : CertifiedLocalizedCIPInput) (center branch : input.Atom)
    (adjacent : input.certified.input.AromaticCanonicalAdjacent center branch) :
    Fin (input.certified.input.molecule.aromaticCanonicalOfficialCIPChildrenAt
      input.certified.input.molecule.atomCount (OfficialCIPNode.root center)).length :=
  Classical.choose <| List.mem_iff_get.mp
    (input.root_extend_zero_mem_aromaticCanonicalOfficialCIPChildrenAt_of_adjacent
      center branch adjacent)

theorem authoritativeRootBranchChildIndex_get
    (input : CertifiedLocalizedCIPInput) (center branch : input.Atom)
    (adjacent : input.certified.input.AromaticCanonicalAdjacent center branch) :
    (input.certified.input.molecule.aromaticCanonicalOfficialCIPChildrenAt
      input.certified.input.molecule.atomCount (OfficialCIPNode.root center)).get
        (input.authoritativeRootBranchChildIndex center branch adjacent) =
      (OfficialCIPNode.root center).extend branch 0 :=
  Classical.choose_spec <| List.mem_iff_get.mp
    (input.root_extend_zero_mem_aromaticCanonicalOfficialCIPChildrenAt_of_adjacent
      center branch adjacent)

/-- The exact depth-one source occurrence coordinate selected by a real branch. -/
noncomputable def authoritativeRootBranchOccurrenceFrame
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (center branch : input.Atom)
    (adjacent : input.certified.input.AromaticCanonicalAdjacent center branch) :
    input.certified.input.AromaticCanonicalOccurrenceFrame :=
  { root := center
    address := [input.authoritativeRootBranchChildIndex center branch adjacent]
    node := (OfficialCIPNode.root center).extend branch 0
    remaining := fuel }

/-- The selected depth-one coordinate belongs to the complete bounded authoritative occurrence
carrier for every carrier fuel. -/
theorem authoritativeRootBranchOccurrenceFrame_mem
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (center branch : input.Atom)
    (adjacent : input.certified.input.AromaticCanonicalAdjacent center branch) :
    input.authoritativeRootBranchOccurrenceFrame fuel center branch adjacent ∈
      input.certified.input.aromaticCanonicalOccurrences fuel := by
  let source := input.certified.input
  let children := source.molecule.aromaticCanonicalOfficialCIPChildrenAt
    source.molecule.atomCount (OfficialCIPNode.root center)
  let index := input.authoritativeRootBranchChildIndex center branch adjacent
  have childAtIndex : children.get index =
      (OfficialCIPNode.root center).extend branch 0 := by
    exact input.authoritativeRootBranchChildIndex_get center branch adjacent
  change Fin children.length at index
  have indexed :
      ((OfficialCIPNode.root center).extend branch 0, index.val) ∈ children.zipIdx := by
    apply List.mem_iff_get.mpr
    let zippedIndex : Fin children.zipIdx.length :=
      ⟨index.val, by simp⟩
    refine ⟨zippedIndex, ?_⟩
    change children.zipIdx[index.val] =
      ((OfficialCIPNode.root center).extend branch 0, index.val)
    rw [List.getElem_zipIdx]
    simpa using congrArg (fun child => (child, index.val)) childAtIndex
  apply (source.mem_aromaticCanonicalOccurrences_iff fuel _).mpr
  change source.DeclarativeAromaticCanonicalOccurrenceSubtree center [] (fuel + 1)
    (OfficialCIPNode.root center)
      (input.authoritativeRootBranchOccurrenceFrame fuel center branch adjacent)
  apply AuthoritativeChemicalInput.DeclarativeAromaticCanonicalOccurrenceSubtree.subtreeDescendant
    indexed
  exact AuthoritativeChemicalInput.DeclarativeAromaticCanonicalOccurrenceSubtree.subtreeRoot
    [index.val] fuel ((OfficialCIPNode.root center).extend branch 0)

/-- A real authoritative occurrence cursor rooted at a perceived tetrahedral center and entering
one specified branch. -/
noncomputable def authoritativeRootBranchCursor
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter)
    (branch : input.Atom)
    (adjacent : input.certified.input.AromaticCanonicalAdjacent center.1 branch) :
    input.certified.input.AromaticCanonicalRerootCursor fuel :=
  { occurrence :=
      ⟨input.authoritativeRootBranchOccurrenceFrame fuel center.1 branch adjacent,
        input.authoritativeRootBranchOccurrenceFrame_mem fuel center.1 branch adjacent⟩
    previous? := some (input.certified.input.aromaticCanonicalFinalOccurrence fuel center) }

@[simp] theorem authoritativeRootBranchCursor_current
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter)
    (branch : input.Atom)
    (adjacent : input.certified.input.AromaticCanonicalAdjacent center.1 branch) :
    (input.authoritativeRootBranchCursor fuel center branch adjacent).occurrence.1.node.current? =
      some branch := by
  simp [authoritativeRootBranchCursor, authoritativeRootBranchOccurrenceFrame]

@[simp] theorem authoritativeRootBranchCursor_provenance
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter)
    (branch : input.Atom)
    (adjacent : input.certified.input.AromaticCanonicalAdjacent center.1 branch) :
    (input.authoritativeRootBranchCursor fuel center branch adjacent).occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom := by
  have different : branch ≠ center.1 := adjacent.1.symm
  simp [authoritativeRootBranchCursor, authoritativeRootBranchOccurrenceFrame,
    OfficialCIPNode.root, OfficialCIPNode.childProvenance, different]

@[simp] theorem authoritativeRootBranchCursor_previous
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter)
    (branch : input.Atom)
    (adjacent : input.certified.input.AromaticCanonicalAdjacent center.1 branch) :
    (input.authoritativeRootBranchCursor fuel center branch adjacent).previous? =
      some (input.certified.input.aromaticCanonicalFinalOccurrence fuel center) := by
  rfl

/-- The constructed branch cursor is literally a member of the production first-occurrence
ligand frame, rather than merely an occurrence somewhere in the global carrier. -/
theorem authoritativeRootBranchCursor_mem_rerootChildren
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter)
    (branch : input.Atom)
    (adjacent : input.certified.input.AromaticCanonicalAdjacent center.1 branch) :
    input.authoritativeRootBranchCursor fuel center branch adjacent ∈
      input.certified.input.aromaticCanonicalRerootChildren
        { occurrence := input.certified.input.aromaticCanonicalFinalOccurrence fuel center
          previous? := none } := by
  let source := input.certified.input
  let target : source.AromaticCanonicalRerootCursor fuel :=
    { occurrence := source.aromaticCanonicalFinalOccurrence fuel center
      previous? := none }
  let frame := input.authoritativeRootBranchOccurrenceFrame fuel center.1 branch adjacent
  have frameGlobal : frame ∈ source.aromaticCanonicalOccurrences fuel := by
    exact input.authoritativeRootBranchOccurrenceFrame_mem fuel center.1 branch adjacent
  have frameIntended : frame ∈ source.intendedAromaticCanonicalRerootChildFrames target := by
    unfold AuthoritativeChemicalInput.intendedAromaticCanonicalRerootChildFrames
    simp only [target]
    rw [if_neg (by simp [AuthoritativeChemicalInput.aromaticCanonicalFinalOccurrence,
      OfficialCIPNode.root, OfficialCIPNode.isDuplicateLeaf])]
    rw [AuthoritativeChemicalInput.aromaticCanonicalRerootNeighborFrames, List.mem_append]
    apply Or.inr
    rw [AuthoritativeChemicalInput.aromaticCanonicalCarrierOutwardChildFrames,
      List.mem_filter]
    refine ⟨frameGlobal, ?_⟩
    simp [frame, authoritativeRootBranchOccurrenceFrame,
      AuthoritativeChemicalInput.aromaticCanonicalFinalOccurrence]
  have exactChildren := source.aromaticCanonicalRerootChildren_sound target
  have mappedPresent : frame ∈
      (source.aromaticCanonicalRerootChildren target).map
        (fun child => child.occurrence.1) := by
    rw [exactChildren.1]
    exact frameIntended
  obtain ⟨child, childPresent, childFrame⟩ := List.mem_map.mp mappedPresent
  have childPrevious := exactChildren.2 child childPresent
  have childEq : child = input.authoritativeRootBranchCursor fuel center branch adjacent := by
    apply AuthoritativeChemicalInput.AromaticCanonicalRerootCursor.ext
    · exact Subtype.ext childFrame
    · simpa [target] using childPrevious
  rwa [← childEq]

/-- Every branch start in the exact tetrahedral spiro incidence has a production authoritative
real occurrence cursor in the center's root ligand frame. -/
theorem DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter.exists_authoritative_cursor_of_ring_branch
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (first second : Finset input.Atom)
    (sourceEq : input.localizedCycleNeighbors first center ∪
        input.localizedCycleNeighbors second center =
      input.certified.input.aromaticCanonicalNeighborFinset center)
    (branch : input.Atom)
    (present : branch ∈ input.localizedCycleNeighbors first center ∪
      input.localizedCycleNeighbors second center) :
    ∃ cursor,
      cursor ∈ input.certified.input.aromaticCanonicalRerootChildren
          { occurrence := input.certified.input.aromaticCanonicalFinalOccurrence fuel
              (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged)
            previous? := none } ∧
        cursor.occurrence.1.node.current? = some branch ∧
        cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  have sourcePresent :
      branch ∈ input.certified.input.aromaticCanonicalNeighborFinset center := by
    rw [← sourceEq]
    exact present
  have adjacent :=
    (input.certified.input.mem_aromaticCanonicalNeighborFinset_iff center branch).mp
      sourcePresent
  let sourceCenter :=
    input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged
  let cursor := input.authoritativeRootBranchCursor fuel sourceCenter branch adjacent
  exact ⟨cursor,
    input.authoritativeRootBranchCursor_mem_rerootChildren fuel sourceCenter branch adjacent,
    input.authoritativeRootBranchCursor_current fuel sourceCenter branch adjacent,
    input.authoritativeRootBranchCursor_provenance fuel sourceCenter branch adjacent⟩

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
