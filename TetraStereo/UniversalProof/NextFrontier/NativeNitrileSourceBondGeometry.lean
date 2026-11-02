import TetraStereo.UniversalProof.NextFrontier.NativeNitrileSourceFrames
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileCanonicalChildren

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.PositiveHydrogenBondTransportProofs.PositiveHydrogenBondTransport

/-- The independent semantic converter retains every actual single and triple record, with
its exact multiplicity and unordered endpoint key. -/
theorem source_localized_records (parity : TetrahedralInputParity) (n : Nat) :
    (nitrileSource parity n).molecule.localizedCovalentRecords =
      (expanded parity n).bonds.map (fun bond => (bond.edgeKey, bond.kind.order)) := by
  have interactions := (expanded parity n).toSemanticMolecule?_interactions
    (nitrileSource parity n).molecule (expanded_source_annotation_agreement parity n).1
  rw [SemanticMolecule.localizedCovalentRecords, interactions, List.filterMap_map]
  calc
    _ = (expanded parity n).bonds.filterMap
        (fun bond => some (bond.edgeKey, bond.kind.order)) := by
      apply List.filterMap_congr
      intro bond retained
      rcases expanded_bond_kinds parity n bond retained with single | triple
      · simp [RawBond.toSemanticInteraction, SemanticInteraction.localizedCovalentRecord?,
          single, RawBond.edgeKey, semanticEdgeKey, ParsedBondKind.order]
      · simp [RawBond.toSemanticInteraction, SemanticInteraction.localizedCovalentRecord?,
          triple, RawBond.edgeKey, semanticEdgeKey, ParsedBondKind.order]
    _ = _ := by simp

theorem source_localized_keys_unique (parity : TetrahedralInputParity) (n : Nat) :
    (nitrileSource parity n).molecule.LocalizedCovalentRecordsUnique := by
  unfold SemanticMolecule.LocalizedCovalentRecordsUnique SemanticMolecule.localizedCovalentKeys
  rw [source_localized_records, List.map_map]
  exact (expanded_admissible parity n).2

theorem source_no_aromatic_edges (parity : TetrahedralInputParity) (n : Nat) :
    (nitrileSource parity n).molecule.aromaticPairEdges = [] := by
  unfold SemanticMolecule.aromaticPairEdges
  rw [(expanded parity n).toSemanticMolecule?_interactions
    (nitrileSource parity n).molecule (expanded_source_annotation_agreement parity n).1]
  apply List.filterMap_eq_nil_iff.mpr
  intro interaction retained
  obtain ⟨bond, member, rfl⟩ := List.mem_map.mp retained
  rcases expanded_bond_kinds parity n bond member with single | triple
  · simp [RawBond.toSemanticInteraction, SemanticMolecule.aromaticPairEdge?, single]
  · simp [RawBond.toSemanticInteraction, SemanticMolecule.aromaticPairEdge?, triple]

theorem source_canonical_order_eq_localized (parity : TetrahedralInputParity) (n left right : Nat) :
    (nitrileSource parity n).molecule.aromaticCanonicalBondOrder left right =
      (nitrileSource parity n).molecule.localizedBondOrder left right := by
  simp only [SemanticMolecule.aromaticCanonicalBondOrder, source_no_aromatic_edges,
    List.contains_nil, Bool.false_eq_true, ↓reduceIte]

theorem source_no_virtual_duplicate (parity : TetrahedralInputParity) (n : Nat)
    (atom : (nitrileSource parity n).AromaticCanonicalAtom) :
    (nitrileSource parity n).molecule.aromaticCanonicalMancudeRepresentativeAt?
      (nitrileSource parity n).molecule.atomCount atom = none := by
  simp [SemanticMolecule.aromaticCanonicalMancudeRepresentativeAt?, source_no_aromatic_edges]

private theorem source_record_order (parity : TetrahedralInputParity) (n : Nat)
    (bond : RawBond) (retained : bond ∈ (expanded parity n).bonds) :
    (nitrileSource parity n).molecule.localizedBondOrder bond.source bond.target = bond.kind.order := by
  unfold SemanticMolecule.localizedBondOrder
  rw [if_neg ((expanded_admissible parity n).1 bond retained).2.2]
  apply SemanticMolecule.localizedBondOrderAtKey_eq_of_mem_unique
  · exact source_localized_keys_unique parity n
  · rw [source_localized_records]
    exact List.mem_map.mpr ⟨bond, retained, rfl⟩

private theorem nitrile_incident_record_cases (parity : TetrahedralInputParity) (n : Nat)
    (bond : RawBond) (retained : bond ∈ (expanded parity n).bonds)
    (incident : bond.source = 2 ∨ bond.target = 2) :
    bond = ⟨0, 2, .single⟩ ∨ bond = ⟨2, 3, .triple⟩ := by
  have inventory := expanded_nitrile_incident_records parity n
  change ((expanded parity n).bonds.filter
    (fun item => item.source == 2 || item.target == 2)).Perm _ at inventory
  have member := inventory.mem_iff.mp (List.mem_filter.mpr
    ⟨retained, by simpa only [Bool.or_eq_true, beq_iff_eq] using incident⟩)
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using member

/-- Exact converted multiplicities at the nitrile carbon, including the genuine triple edge. -/
theorem source_nitrile_bond_order (parity : TetrahedralInputParity) (n neighbor : Nat) :
    (nitrileSource parity n).molecule.aromaticCanonicalBondOrder 2 neighbor =
      if neighbor = 0 then 1 else if neighbor = 3 then 3 else 0 := by
  rw [source_canonical_order_eq_localized]
  by_cases zero : neighbor = 0
  · subst neighbor
    simp only [↓reduceIte]
    rw [SemanticMolecule.localizedBondOrder_comm]
    exact source_record_order parity n ⟨0, 2, .single⟩
      (withExplicitHydrogens_retains_original_bonds (raw parity n) _ (by simp [raw, prefixBonds]))
  · rw [if_neg zero]
    by_cases nitrogen : neighbor = 3
    · subst neighbor
      simp only [↓reduceIte]
      exact source_record_order parity n ⟨2, 3, .triple⟩
        (withExplicitHydrogens_retains_original_bonds (raw parity n) _ (raw_triple_present parity n))
    · rw [if_neg nitrogen]
      apply SemanticMolecule.localizedBondOrder_eq_zero_of_no_record
      intro present
      rw [SemanticMolecule.localizedCovalentKeys, source_localized_records, List.map_map] at present
      obtain ⟨bond, retained, equal⟩ := List.mem_map.mp present
      have key : semanticEdgeKey 2 neighbor = semanticEdgeKey bond.source bond.target := equal.symm
      have ends := (wedge_semanticEdgeKey_eq_iff 2 neighbor bond.source bond.target).mp key
      have incident : bond.source = 2 ∨ bond.target = 2 :=
        ends.elim (fun pair => Or.inl pair.1.symm) (fun pair => Or.inr pair.1.symm)
      rcases nitrile_incident_record_cases parity n bond retained incident with rfl | rfl
      · simp only at ends
        rcases ends with ⟨bad, _⟩ | ⟨_, same⟩
        · omega
        · exact zero same
      · simp only at ends
        rcases ends with ⟨_, same⟩ | ⟨bad, _⟩
        · exact nitrogen same
        · omega

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
