import TetraStereo.UniversalProof.NativeRawRecordBounds
import TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
import TetraStereo.OneCenter.AuthoritativeSingleWedgeSourcePrimitives

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeSourceSingleIncidenceProofs.LocalSourceRule3AllCarrierRecovery

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery

/-- Independent actual incidence data; no neighbor-degree or returned-key conclusion occurs. -/
structure SingleIncidentDomain (raw : RawMolecule) (center : Nat) : Prop where
  wellFormed : raw.WellFormed
  incidentKinds : ∀ bond ∈ raw.bonds,
    bond.source = center ∨ bond.target = center → bond.kind = .single

namespace Incidence

section Converted
variable (raw : RawMolecule) (source : AuthoritativeChemicalInput)
variable (converted : raw.toSemanticMolecule? = some source.molecule)
variable (center : source.AromaticCanonicalAtom)
variable (domain : SingleIncidentDomain raw center.val)
include converted domain

theorem converted_neighbor_bound (neighbor : Nat)
    (member : neighbor ∈ recordNeighbors raw center.val) :
    neighbor < source.molecule.atomCount ∧ neighbor ≠ center.val := by
  have facts := recordNeighbor_bounds domain.wellFormed member
  refine ⟨?_, facts.2⟩
  simpa only [raw.toSemanticMolecule?_atomCount source.molecule converted] using facts.1

/-- Every actual converted center incidence has a single binary record and a real raw endpoint. -/
theorem converted_center_incidents (interaction : SemanticInteraction)
    (member : interaction ∈ source.molecule.interactions)
    (incident : center.val ∈ interaction.participants) :
    ∃ neighbor ∈ recordNeighbors raw center.val,
      (interaction.participants = [center.val, neighbor] ∨
        interaction.participants = [neighbor, center.val]) ∧ interaction.kind = .covalent 1 := by
  rw [raw.toSemanticMolecule?_interactions source.molecule converted] at member
  obtain ⟨bond, retained, rfl⟩ := List.mem_map.mp member
  change center.val ∈ [bond.source, bond.target] at incident
  have ends : bond.source = center.val ∨ bond.target = center.val := by
    simpa [eq_comm] using incident
  have kind := domain.incidentKinds bond retained ends
  rcases ends with first | second
  · refine ⟨bond.target, List.mem_filterMap.mpr ⟨bond, retained, ?_⟩, ?_, ?_⟩
    · simp [recordNeighbor?, first]
    · exact Or.inl (by change [bond.source, bond.target] = _; rw [first])
    · simp only [RawBond.toSemanticInteraction, kind]
  · refine ⟨bond.source, List.mem_filterMap.mpr ⟨bond, retained, ?_⟩, ?_, ?_⟩
    · have different : bond.source ≠ center.val := by
        intro same
        exact (domain.wellFormed bond retained).2.2 (same.trans second.symm)
      simp [recordNeighbor?, different, second]
    · exact Or.inr (by change [bond.source, bond.target] = _; rw [second])
    · simp only [RawBond.toSemanticInteraction, kind]

theorem converted_neighbor_record (neighbor : Nat)
    (member : neighbor ∈ recordNeighbors raw center.val) :
    (semanticEdgeKey center.val neighbor, 1) ∈ source.molecule.localizedCovalentRecords := by
  obtain ⟨bond, retained, observed⟩ := List.mem_filterMap.mp member
  unfold recordNeighbor? at observed
  have endpoints : (bond.source = center.val ∧ bond.target = neighbor) ∨
      (bond.target = center.val ∧ bond.source = neighbor) := by
    split at observed
    · exact Or.inl ⟨by simpa using ‹(bond.source == center.val) = true›,
        Option.some.inj observed⟩
    · split at observed
      · exact Or.inr ⟨by simpa using ‹(bond.target == center.val) = true›,
          Option.some.inj observed⟩
      · cases observed
  have incident : bond.source = center.val ∨ bond.target = center.val :=
    endpoints.elim (fun facts => Or.inl facts.1) (fun facts => Or.inr facts.1)
  have kind := domain.incidentKinds bond retained incident
  apply List.mem_filterMap.mpr
  refine ⟨bond.toSemanticInteraction, ?_, ?_⟩
  · rw [raw.toSemanticMolecule?_interactions source.molecule converted]
    exact List.mem_map.mpr ⟨bond, retained, rfl⟩
  · rcases endpoints with first | second
    · simp [RawBond.toSemanticInteraction, SemanticInteraction.localizedCovalentRecord?,
        kind, first.1, first.2]
    · simp [RawBond.toSemanticInteraction, SemanticInteraction.localizedCovalentRecord?,
        kind, second.1, second.2, semanticEdgeKey_comm]

theorem converted_matching_record (neighbor order : Nat)
    (member : (semanticEdgeKey center.val neighbor, order) ∈
      source.molecule.localizedCovalentRecords) :
    order = 1 ∧ neighbor ∈ recordNeighbors raw center.val := by
  obtain ⟨interaction, retained, recorded⟩ := List.mem_filterMap.mp member
  obtain ⟨first, second, participants, kind, key⟩ :=
    wedge_localized_record_endpoints interaction _ order recorded
  have aligned := (wedge_semanticEdgeKey_eq_iff center.val neighbor first second).mp key
  have incident : center.val ∈ interaction.participants := by
    rcases aligned with aligned | reversed
    · simp [participants, aligned.1.symm]
    · rw [participants]
      exact List.mem_cons_of_mem first (List.mem_singleton.mpr reversed.1)
  obtain ⟨endpoint, present, ends, single⟩ :=
    converted_center_incidents raw source converted center domain interaction retained incident
  have one : order = 1 := by simpa [kind] using single
  refine ⟨one, ?_⟩
  rcases ends with ends | ends
  · have equal : first = center.val ∧ second = endpoint := by simpa [participants] using ends
    have neighborEq : neighbor = endpoint := by rcases aligned with _ | _ <;> omega
    simpa [neighborEq] using present
  · have equal : first = endpoint ∧ second = center.val := by simpa [participants] using ends
    have neighborEq : neighbor = endpoint := by rcases aligned with _ | _ <;> omega
    simpa [neighborEq] using present

theorem converted_localized_keys_iff (neighbor : Nat) :
    semanticEdgeKey center.val neighbor ∈ source.molecule.localizedCovalentKeys ↔
      neighbor ∈ recordNeighbors raw center.val := by
  constructor
  · intro member
    obtain ⟨⟨key, order⟩, retained, equal⟩ := List.mem_map.mp member
    dsimp at equal
    subst key
    exact (converted_matching_record raw source converted center domain neighbor order retained).2
  · intro member
    exact List.mem_map.mpr ⟨(semanticEdgeKey center.val neighbor, 1),
      converted_neighbor_record raw source converted center domain neighbor member, rfl⟩

omit converted domain in
private theorem lookup_single (records : List ((Nat × Nat) × Nat)) (key : Nat × Nat)
    (single : ∀ record ∈ records, record.1 = key → record.2 = 1) :
    SemanticMolecule.localizedBondOrderAtKey records key =
      if key ∈ records.map Prod.fst then 1 else 0 := by
  induction records with
  | nil => simp [SemanticMolecule.localizedBondOrderAtKey]
  | cons record records inductionHypothesis =>
      by_cases same : record.1 = key
      · simp [SemanticMolecule.localizedBondOrderAtKey, same,
          single record (by simp) same]
      · have tailSingle : ∀ item ∈ records, item.1 = key → item.2 = 1 := by
          intro item retained matched
          exact single item (List.mem_cons_of_mem _ retained) matched
        rw [SemanticMolecule.localizedBondOrderAtKey, if_neg same,
          inductionHypothesis tailSingle]
        simp only [List.map_cons, List.mem_cons, Ne.symm same, false_or]

theorem converted_localized_bond_order (neighbor : Nat) :
    source.molecule.localizedBondOrder center.val neighbor =
      if neighbor ∈ recordNeighbors raw center.val then 1 else 0 := by
  by_cases same : center.val = neighbor
  · have absent : neighbor ∉ recordNeighbors raw center.val := by
      intro member
      exact (converted_neighbor_bound raw source converted center domain neighbor member).2 same.symm
    simp only [SemanticMolecule.localizedBondOrder, if_pos same, if_neg absent]
  · unfold SemanticMolecule.localizedBondOrder
    rw [if_neg same, lookup_single]
    · change (if semanticEdgeKey center.val neighbor ∈ source.molecule.localizedCovalentKeys
        then 1 else 0) = _
      simp only [converted_localized_keys_iff raw source converted center domain neighbor]
    · rintro ⟨key, order⟩ retained matched
      dsimp at matched ⊢
      subst key
      exact (converted_matching_record raw source converted center domain neighbor order retained).1

theorem converted_no_incident_aromatic (neighbor : Nat) :
    semanticEdgeKey center.val neighbor ∉ source.molecule.aromaticPairEdges := by
  intro member
  obtain ⟨interaction, retained, observed⟩ := List.mem_filterMap.mp member
  rw [raw.toSemanticMolecule?_interactions source.molecule converted] at retained
  obtain ⟨bond, rawMember, rfl⟩ := List.mem_map.mp retained
  have endpoints : semanticEdgeKey bond.source bond.target = semanticEdgeKey center.val neighbor := by
    cases kind : bond.kind <;>
      simp [RawBond.toSemanticInteraction, SemanticMolecule.aromaticPairEdge?, kind] at observed
    simpa only [semanticEdgeKey_comm] using observed
  have incident : bond.source = center.val ∨ bond.target = center.val := by
    rcases (wedge_semanticEdgeKey_eq_iff bond.source bond.target center.val neighbor).mp endpoints
      with first | second
    · exact Or.inl first.1
    · exact Or.inr second.2
  have single := domain.incidentKinds bond rawMember incident
  simp [RawBond.toSemanticInteraction, SemanticMolecule.aromaticPairEdge?, single] at observed

theorem converted_canonical_bond_order (neighbor : Nat) :
    source.molecule.aromaticCanonicalBondOrder center.val neighbor =
      if neighbor ∈ recordNeighbors raw center.val then 1 else 0 := by
  have absent := converted_no_incident_aromatic raw source converted center domain neighbor
  have absentReverse : semanticEdgeKey neighbor center.val ∉ source.molecule.aromaticPairEdges := by
    rw [semanticEdgeKey_comm]
    exact absent
  simpa [SemanticMolecule.aromaticCanonicalBondOrder, absent, absentReverse] using
    converted_localized_bond_order raw source converted center domain neighbor

theorem converted_no_mancude_representative :
    source.molecule.aromaticCanonicalMancudeRepresentativeAt? source.molecule.atomCount center = none := by
  apply List.find?_eq_none.mpr
  intro neighbor _
  simpa using converted_no_incident_aromatic raw source converted center domain neighbor.val

theorem converted_ordinary_copies :
    source.molecule.aromaticCanonicalOrdinaryNeighborCopiesAt source.molecule.atomCount center =
      ((List.finRange source.molecule.atomCount).filter
        (fun neighbor => decide (neighbor.val ∈ recordNeighbors raw center.val))).map
        (fun neighbor => (neighbor, 0)) := by
  unfold SemanticMolecule.aromaticCanonicalOrdinaryNeighborCopiesAt
  have allLists (neighbors : List (Fin source.molecule.atomCount)) :
      (neighbors.flatMap fun neighbor =>
        (List.range (source.molecule.aromaticCanonicalBondOrder center.val neighbor.val)).map
          fun copyIndex => (neighbor, copyIndex)) =
      (neighbors.filter (fun neighbor => decide
        (neighbor.val ∈ recordNeighbors raw center.val))).map (fun neighbor => (neighbor, 0)) := by
    induction neighbors with
    | nil => simp
    | cons neighbor neighbors inductionHypothesis =>
        rw [List.flatMap_cons, List.filter_cons,
          converted_canonical_bond_order raw source converted center domain neighbor.val]
        by_cases present : neighbor.val ∈ recordNeighbors raw center.val <;>
          simp [present, inductionHypothesis]
  exact allLists _


end Converted
end Incidence

end TetraStereo.UniversalProof.NativeSourceSingleIncidenceProofs.LocalSourceRule3AllCarrierRecovery
