import TetraStereo.OneCenter.LocalizedSpiroAuthoritativeComparatorIntegration
import TetraStereo.OneCenter.AuthoritativeSemanticMancudePublicTetrahedralAnalysis

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Exact incidence bridge for connectivity-only tetrahedral spiro centers

The simple-spiro topology theorem supplies four distinct ring branch starts, but topology alone
cannot exclude additional acyclic neighbours at the same atom.  This module states that genuine
chemical boundary explicitly: the connectivity-only tetrahedral route additionally requires a
permitted center element and graph degree four.  Under exactly those conditions, the four ring
branches are proved to be the complete source-canonical tetrahedral ligand frame.

The bridge does not assume that the localized graph and source-normalized graph agree.  It derives
their equality from `LocalizedCIPGraphReady`: every admitted interaction is already a localized
covalent pair, so no aromatic interaction can contribute a different constitutional edge.
-/

namespace SemanticInteraction

/-- On the direct localized-CIP domain an interaction contributes the same constitutional key to
the ordinary localized graph and to aromatic-safe source normalization. -/
theorem aromaticNormalizedPairKey?_eq_localizedCovalentRecord?_map_fst_of_isLocalizedCovalentPair
    (interaction : SemanticInteraction)
    (localized : interaction.IsLocalizedCovalentPair) :
    SemanticMolecule.aromaticNormalizedPairKey? interaction =
      interaction.localizedCovalentRecord?.map Prod.fst := by
  rcases localized with ⟨left, right, order, participants, kind, positive⟩
  simp [SemanticMolecule.aromaticNormalizedPairKey?,
    SemanticMolecule.aromaticPairEdge?, localizedCovalentRecord?, participants, kind, positive]

end SemanticInteraction

namespace SemanticMolecule

private theorem map_filterMap_option_map_spiro
    {α β γ : Type} (items : List α) (select : α → Option β) (mapValue : β → γ) :
    (items.filterMap select).map mapValue =
      items.filterMap (fun item => (select item).map mapValue) := by
  induction items with
  | nil => rfl
  | cons item items inductionHypothesis =>
      cases observed : select item <;> simp [observed, inductionHypothesis]

/-- A graph-ready semantic molecule has exactly the same constitutional pair keys before and
after aromatic-safe source normalization.  This is a theorem of the admission predicate, not a
representation-alignment assumption. -/
theorem aromaticNormalizedPairKeys_eq_localizedCovalentKeys_of_localizedCovalentPairsOnly
    (molecule : SemanticMolecule)
    (localized : molecule.LocalizedCovalentPairsOnly) :
    molecule.aromaticNormalizedPairKeys = molecule.localizedCovalentKeys := by
  rw [localizedCovalentKeys, localizedCovalentRecords,
    map_filterMap_option_map_spiro]
  unfold aromaticNormalizedPairKeys
  apply List.filterMap_congr
  intro interaction present
  exact
    interaction.aromaticNormalizedPairKey?_eq_localizedCovalentRecord?_map_fst_of_isLocalizedCovalentPair
      (localized interaction present)

end SemanticMolecule

namespace CertifiedLocalizedCIPInput

/-- Exact adjacency alignment between the direct localized graph and the source-canonical
aromatic-safe constitutional relation. -/
theorem moleculeGraph_adj_iff_aromaticCanonicalAdjacent
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom) :
    input.moleculeGraph.Adj left right ↔
      input.certified.input.AromaticCanonicalAdjacent left right := by
  let source := input.certified.input
  change source.molecule.toLocalizedMoleculeGraph.Adj left right ↔
    source.AromaticCanonicalAdjacent left right
  rw [source.molecule.toLocalizedMoleculeGraph_adj_iff_localizedCovalentKey
    input.graphReady]
  have keysEqual :=
    source.molecule.aromaticNormalizedPairKeys_eq_localizedCovalentKeys_of_localizedCovalentPairsOnly
      input.graphReady.2.2.2.1
  unfold AuthoritativeChemicalInput.AromaticCanonicalAdjacent
  rw [keysEqual]

/-- Consequently, graph neighbors and the source-canonical tetrahedral neighbor set are
extensionally identical on every certified localized input. -/
theorem neighborFinset_eq_aromaticCanonicalNeighborFinset
    (input : CertifiedLocalizedCIPInput) (center : input.Atom) :
    input.moleculeGraph.neighborFinset center =
      input.certified.input.aromaticCanonicalNeighborFinset center := by
  classical
  ext neighbor
  rw [MoleculeGraph.mem_neighborFinset,
    input.certified.input.mem_aromaticCanonicalNeighborFinset_iff]
  exact input.moleculeGraph_adj_iff_aromaticCanonicalAdjacent center neighbor

/-- Exact independent applicability boundary for the ordinary tetrahedral spiro route.  The
simple two-ring carrier is retained, the center element must lie in the explicit connectivity-only
tetrahedral domain, and no fifth graph neighbor may be present. -/
def DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center) : Prop :=
  input.DeclarativeLocalizedSpiroCenter center carrier ∧
    input.certified.input.ConnectivityOnlyTetrahedralCenterAtom center ∧
      (input.moleculeGraph.neighborFinset center).card = 4

/-- Exact constructor of the source-canonical tetrahedral-center subtype from the molecule-level
spiro incidence judgment. -/
noncomputable def aromaticCanonicalTetrahedralCenterOfLocalizedSpiro
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier) :
    input.certified.input.AromaticCanonicalTetrahedralCenter := by
  refine ⟨center,
    (input.certified.input.mem_aromaticCanonicalTetrahedralCenterSet_iff center).mpr
      ⟨judged.2.1, ?_⟩⟩
  rw [← input.neighborFinset_eq_aromaticCanonicalNeighborFinset center]
  exact judged.2.2

/-- A cycle-neighbor set is always contained in the ambient molecular neighbor set. -/
theorem localizedCycleNeighbors_subset_neighborFinset
    (input : CertifiedLocalizedCIPInput) (ring : Finset input.Atom)
    (center : input.Atom) :
    input.localizedCycleNeighbors ring center ⊆
      input.moleculeGraph.neighborFinset center := by
  intro neighbor present
  apply (input.moleculeGraph.mem_neighborFinset center neighbor).mpr
  exact (input.mem_localizedCycleNeighbors_iff ring center neighbor).mp present |>.2

/-- The four ring branch starts are not merely four distinct atoms: on the tetrahedral route they
are exactly all graph neighbors and exactly all source-canonical neighbors. -/
theorem DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter.exists_exact_ring_branch_neighbors
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier) :
    ∃ first second,
      first ≠ second ∧
        carrier.rings = {first, second} ∧
          input.localizedCycleNeighbors first center ∪
              input.localizedCycleNeighbors second center =
            input.moleculeGraph.neighborFinset center ∧
          input.localizedCycleNeighbors first center ∪
              input.localizedCycleNeighbors second center =
            input.certified.input.aromaticCanonicalNeighborFinset center := by
  obtain ⟨first, second, different, ringsEq, branchCard⟩ :=
    judged.1.four_ring_branch_starts input center carrier
  have subset :
      input.localizedCycleNeighbors first center ∪
          input.localizedCycleNeighbors second center ⊆
        input.moleculeGraph.neighborFinset center := by
    intro neighbor present
    rw [Finset.mem_union] at present
    rcases present with firstPresent | secondPresent
    · exact input.localizedCycleNeighbors_subset_neighborFinset first center firstPresent
    · exact input.localizedCycleNeighbors_subset_neighborFinset second center secondPresent
  have reverseCard :
      (input.moleculeGraph.neighborFinset center).card ≤
        (input.localizedCycleNeighbors first center ∪
          input.localizedCycleNeighbors second center).card := by
    rw [judged.2.2, branchCard]
  have graphEq :
      input.localizedCycleNeighbors first center ∪
          input.localizedCycleNeighbors second center =
        input.moleculeGraph.neighborFinset center :=
    Finset.eq_of_subset_of_card_le subset reverseCard
  refine ⟨first, second, different, ringsEq, graphEq, ?_⟩
  rw [graphEq, input.neighborFinset_eq_aromaticCanonicalNeighborFinset center]

/-- Exact branch-to-canonical-frame correspondence.  Every ring branch start occurs at one of the
four source-canonical ligand positions, and every such position is one of the ring branch starts. -/
theorem DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter.exists_ring_pair_canonical_ligands_exact
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier) :
    ∃ first second,
      first ≠ second ∧
        carrier.rings = {first, second} ∧
          ∀ atom,
            atom ∈ input.localizedCycleNeighbors first center ∪
                input.localizedCycleNeighbors second center ↔
              ∃ index : Fin 4,
                input.certified.input.aromaticCanonicalLigandAtom
                    (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro
                      center carrier judged) index = atom := by
  obtain ⟨first, second, different, ringsEq, _graphEq, sourceEq⟩ :=
    judged.exists_exact_ring_branch_neighbors input center carrier
  refine ⟨first, second, different, ringsEq, ?_⟩
  intro atom
  constructor
  · intro branch
    have sourcePresent :
        atom ∈ input.certified.input.aromaticCanonicalNeighborFinset center := by
      rw [← sourceEq]
      exact branch
    have adjacent :=
      (input.certified.input.mem_aromaticCanonicalNeighborFinset_iff center atom).mp
        sourcePresent
    exact input.certified.input.exists_aromaticCanonicalLigandAtom_eq_of_adjacent
      (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged)
      atom adjacent
  · rintro ⟨index, atomEq⟩
    have adjacent := input.certified.input.aromaticCanonicalLigandAtom_adjacent
      (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged) index
    have sourcePresent :
        input.certified.input.aromaticCanonicalLigandAtom
            (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged) index ∈
          input.certified.input.aromaticCanonicalNeighborFinset center :=
      (input.certified.input.mem_aromaticCanonicalNeighborFinset_iff center _).mpr adjacent
    rw [← sourceEq, atomEq] at sourcePresent
    exact sourcePresent

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
