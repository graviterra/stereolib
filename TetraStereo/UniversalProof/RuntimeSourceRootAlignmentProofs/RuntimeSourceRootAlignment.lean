import TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
import TetraStereo.UniversalProof.HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery
import TetraStereo.OneCenter.AuthoritativeSingleWedgeSourceOccurrenceCompleteness

set_option autoImplicit false

namespace TetraStereo.UniversalProof.RuntimeSourceRootAlignmentProofs.RuntimeSourceRootAlignment

open TetraStereo.OneCenter TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery

/-!
General SAME-source raw-to-canonical root transport. The domain states raw bond facts, not a
desired root order or alignment: actual leaf neighbors have distinct atomic numbers and every
actual center-incident bond record is single. The last condition is stronger than numerical
bond-order one, which by itself also allows aromatic records and virtual canonical roots.

Successful conversion derives the source graph facts below. Actual final carrier children may
be reordered; only a permutation is concluded. No drawing/wedge is invented. Unrelated source
double/aromatic bonds remain unrestricted. This unit does not establish runtime/formal sorted
priority equality, parser parity/output correspondence, public-runner completeness or adoption.
Those retain TECHNICAL_PROOF_REQUIRED, HUMAN_REVIEW_REQUIRED and EXTERNAL_EVIDENCE_REQUIRED.
-/

structure SingleLeafDomain (raw : RawMolecule) (center : Nat) : Prop where
  leaf : LeafNeighborDomain raw center
  incidentKinds : ∀ bond ∈ raw.bonds,
    bond.source = center ∨ bond.target = center → bond.kind = .single

section Converted

variable (raw : RawMolecule) (source : AuthoritativeChemicalInput)
variable (converted : raw.toSemanticMolecule? = some source.molecule)
variable (center : source.AromaticCanonicalAtom)
variable (domain : SingleLeafDomain raw center.val)

include converted domain

theorem converted_neighbor_bound (neighbor : Nat)
    (member : neighbor ∈ recordNeighbors raw center.val) :
    neighbor < source.molecule.atomCount ∧ neighbor ≠ center.val := by
  have facts := recordNeighbor_bounds domain.leaf.wellFormed member
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
        exact (domain.leaf.wellFormed bond retained).2.2 (same.trans second.symm)
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

/-- Official enumeration uses source atom indices, not raw bond record order. -/
theorem converted_official_children :
    source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount
        (OfficialCIPNode.root center) =
      ((List.finRange source.molecule.atomCount).filter
        (fun neighbor => decide (neighbor.val ∈ recordNeighbors raw center.val))).map
        (fun neighbor => (OfficialCIPNode.root center).extend neighbor 0) := by
  simp [SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt,
    OfficialCIPNode.root, OfficialCIPNode.isDuplicateLeaf,
    SemanticMolecule.aromaticCanonicalChildCopiesAt, OfficialCIPNode.parent?,
    converted_no_mancude_representative raw source converted center domain,
    converted_ordinary_copies raw source converted center domain, List.map_map]

theorem converted_official_root_ids :
    officialRootIDs source center =
      ((List.finRange source.molecule.atomCount).filter
        (fun neighbor => decide (neighbor.val ∈ recordNeighbors raw center.val))).map
        (fun neighbor => some neighbor.val) := by
  unfold officialRootIDs
  rw [converted_official_children raw source converted center domain]
  simp only [List.map_map]
  apply List.map_congr_left
  intro neighbor _
  rfl

theorem converted_official_root_ids_perm :
    (officialRootIDs source center).Perm ((recordNeighbors raw center.val).map some) := by
  rw [converted_official_root_ids raw source converted center domain]
  apply List.perm_of_nodup_nodup_toFinset_eq
  · apply List.Nodup.map
    · intro left right equal
      exact Fin.ext (Option.some.inj equal)
    · exact (List.nodup_finRange _).filter _
  · exact domain.leaf.neighbors_nodup.map (Option.some_injective Nat)
  · apply Finset.ext
    intro atomID
    cases atomID with
    | none => simp
    | some neighbor =>
        have bounded (present : neighbor ∈ recordNeighbors raw center.val) :
            neighbor < source.molecule.atomCount :=
          (converted_neighbor_bound raw source converted center domain neighbor present).1
        simp only [List.mem_toFinset, List.mem_map, List.mem_filter,
          List.mem_finRange, true_and, decide_eq_true_eq, Option.some.injEq]
        constructor
        · rintro ⟨atom, present, rfl⟩
          exact ⟨atom.val, present, rfl⟩
        · rintro ⟨value, present, equality⟩
          subst value
          exact ⟨⟨neighbor, bounded present⟩, present, rfl⟩

end Converted

theorem raw_neighbor_iff_positive (raw : RawMolecule) (center neighbor : Nat)
    (domain : SingleLeafDomain raw center) :
    neighbor ∈ recordNeighbors raw center ↔ 0 < raw.bondOrder center neighbor := by
  constructor
  · intro member
    rw [domain.leaf.single member]
    exact Nat.zero_lt_one
  · intro positive
    have different : center ≠ neighbor := by
      intro equal
      subst neighbor
      have impossible : 0 < (0 : Nat) := by simpa only [raw.bondOrder_self] using positive
      exact (Nat.lt_irrefl 0) impossible
    obtain ⟨bond, retained, connects⟩ := (raw.bondOrder_pos_iff_exists_bond different).mp positive
    apply List.mem_filterMap.mpr
    refine ⟨bond, retained, ?_⟩
    simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at connects
    rcases connects with ⟨first, second⟩ | ⟨first, second⟩
    · simp [recordNeighbor?, first, second]
    · simp [recordNeighbor?, first, second, Ne.symm different]

theorem written_neighbors_perm_records (raw : RawMolecule) (center : Nat)
    (domain : SingleLeafDomain raw center) (written : raw.WrittenNeighborExact) :
    (raw.writtenNeighbors center).Perm (recordNeighbors raw center) := by
  have clauses := RawMolecule.WrittenNeighborExact.at raw written ⟨center, domain.leaf.centerBound⟩
  apply List.perm_of_nodup_nodup_toFinset_eq clauses.1 domain.leaf.neighbors_nodup
  apply Finset.ext
  intro neighbor
  simp only [List.mem_toFinset]
  rw [TetraStereo.UniversalProof.HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery.source_writtenNeighbors_mem_iff
    raw domain.leaf.wellFormed written center domain.leaf.centerBound neighbor,
    raw_neighbor_iff_positive raw center neighbor domain]

theorem generated_runtime_ids_eq (raw : RawMolecule) (center : Nat)
    (domain : SingleLeafDomain raw center) :
    (generatedRuntimeRoots raw center).map (fun cursor => some cursor.node.atom) =
      (recordNeighbors raw center).map some := by
  rw [generatedRuntimeRoots_eq raw center domain.leaf]
  simp only [List.map_map]
  rfl

theorem converted_final_root_ids_perm (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SingleLeafDomain raw center.1.val) :
    (finalOccurrenceRootIDs source fuel center).Perm ((recordNeighbors raw center.1.val).map some) :=
  (finalOccurrenceRootIDs_perm_officialRootIDs source fuel center).trans
    (converted_official_root_ids_perm raw source converted center.1 domain)

/-- Both sides are actual production root generators over the SAME converted input. -/
theorem actual_runtime_source_ids_perm (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SingleLeafDomain raw center.1.val) :
    (finalOccurrenceRootIDs source fuel center).Perm
      ((generatedRuntimeRoots raw center.1.val).map (fun cursor => some cursor.node.atom)) := by
  rw [generated_runtime_ids_eq raw center.1.val domain]
  exact converted_final_root_ids_perm raw source converted fuel center domain

theorem actual_returned_four_roots (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SingleLeafDomain raw center.1.val)
    (four : (recordNeighbors raw center.1.val).length = 4) :
    source.aromaticCanonicalOccurrenceLigandFrame?
      (source.aromaticCanonicalFinalOccurrence fuel center) =
        some (finalOccurrenceRoots source fuel center) ∧
      (finalOccurrenceRoots source fuel center).length = 4 := by
  refine ⟨finalOccurrenceRoots_are_returned source fuel center, ?_⟩
  have count := (converted_final_root_ids_perm raw source converted fuel center domain).length_eq
  simpa only [finalOccurrenceRootIDs, List.length_map, four] using count

/-- A returned canonical root has the SAME real endpoint and center-edge history. -/
theorem converted_final_cursor_real_root (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SingleLeafDomain raw center.1.val)
    (cursor : source.AromaticCanonicalRerootCursor fuel)
    (present : cursor ∈ finalOccurrenceRoots source fuel center) :
    ∃ neighbor : source.AromaticCanonicalAtom, neighbor.val ∈ recordNeighbors raw center.1.val ∧
      cursor.occurrence.1.node = OfficialCIPNode.rootFromEdge center.1 neighbor := by
  have nodesPerm := (finalOccurrenceRoots_frames_perm source fuel center).map (fun frame => frame.node)
  have officialNodes : (aromaticCanonicalFinalDirectChildFrames source fuel center).map
      (fun frame => frame.node) = source.molecule.aromaticCanonicalOfficialCIPChildrenAt
        source.molecule.atomCount (OfficialCIPNode.root center.1) := by
    unfold aromaticCanonicalFinalDirectChildFrames
    rw [List.map_map]
    change (source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount
      (OfficialCIPNode.root center.1)).zipIdx.map Prod.fst = _
    exact List.zipIdx_map_fst 0 _
  have inActual : cursor.occurrence.1.node ∈
      ((finalOccurrenceRoots source fuel center).map (fun child => child.occurrence.1)).map
        (fun frame => frame.node) := by
    simp only [List.mem_map]
    exact ⟨cursor.occurrence.1, ⟨cursor, present, rfl⟩, rfl⟩
  have inOfficial := nodesPerm.mem_iff.mp inActual
  rw [officialNodes, converted_official_children raw source converted center.1 domain] at inOfficial
  obtain ⟨neighbor, retained, nodeEq⟩ := List.mem_map.mp inOfficial
  have endpointPresent : neighbor.val ∈ recordNeighbors raw center.1.val :=
    of_decide_eq_true (List.mem_filter.mp retained).2
  have neighborDifferent : neighbor ≠ center.1 := by
    intro same
    exact (converted_neighbor_bound raw source converted center.1 domain neighbor.val endpointPresent).2
      (congrArg Fin.val same)
  refine ⟨neighbor, endpointPresent, nodeEq.symm.trans ?_⟩
  simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance,
    OfficialCIPNode.root, OfficialCIPNode.rootFromEdge, neighborDifferent]

/-- Actual finite matching is derived from physical count and raw written-neighbor exactness. -/
theorem converted_written_alignment_exists (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SingleLeafDomain raw center.1.val)
    (written : raw.WrittenNeighborExact) (four : (recordNeighbors raw center.1.val).length = 4) :
    ∃ positions, findSlotAlignment? (raw.writtenNeighbors center.1.val)
      (finalOccurrenceRootIDs source fuel center) = some positions := by
  have writtenPerm : (raw.writtenNeighbors center.1.val).Perm (recordNeighbors raw center.1.val) := by
    exact written_neighbors_perm_records raw center.1.val domain written
  apply findSlotAlignment?_exists_of_perm
  · exact writtenPerm.length_eq.trans four
  · exact writtenPerm.nodup_iff.mpr domain.leaf.neighbors_nodup
  · exact (converted_final_root_ids_perm raw source converted fuel center domain).trans
      (writtenPerm.map some).symm

namespace InlineHydrogen

abbrev expanded : RawMolecule :=
  TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery.InlineHydrogenWitness.expanded

/-- Actual public raw conversion, with its own copied annotation diagram and no spatial input. -/
def source : AuthoritativeChemicalInput :=
  expanded.toAuthoritativeChemicalInput?.getD { molecule := { atoms := [], interactions := [] } }

def centerAtom : source.AromaticCanonicalAtom := ⟨0, by decide +kernel⟩

theorem actual_conversion : expanded.toSemanticMolecule? = some source.molecule := by
  decide +kernel

theorem actual_domain : SingleLeafDomain expanded centerAtom.val := by
  refine ⟨TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery.InlineHydrogenWitness.independent_domain,
    ?_⟩
  intro bond retained _
  change bond ∈ [⟨0, 4, .single⟩, ⟨0, 1, .single⟩, ⟨0, 2, .single⟩, ⟨0, 3, .single⟩] at retained
  simp at retained
  rcases retained with rfl | rfl | rfl | rfl <;> rfl

theorem actual_runtime_record_order : recordNeighbors expanded centerAtom.val = [4, 1, 2, 3] :=
  TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery.InlineHydrogenWitness.source_neighbor_records

theorem actual_official_order : officialRootIDs source centerAtom = [some 1, some 2, some 3, some 4] := by
  rw [converted_official_root_ids expanded source actual_conversion centerAtom actual_domain]
  decide +kernel

/-- The positive-demand inline H has a genuinely nonidentity written-to-official permutation. -/
theorem actual_nonidentity_alignment :
    findSlotAlignment? (expanded.writtenNeighbors centerAtom.val) (officialRootIDs source centerAtom) =
      some [1, 2, 3, 0] := by
  rw [actual_official_order]
  decide +kernel

theorem actual_alignment_meaning : ExactSlotAlignment (expanded.writtenNeighbors centerAtom.val)
    (officialRootIDs source centerAtom) [1, 2, 3, 0] :=
  findSlotAlignment?_sound _ _ _ actual_nonidentity_alignment

theorem identity_alignment_false : ¬ ExactSlotAlignment (expanded.writtenNeighbors centerAtom.val)
    (officialRootIDs source centerAtom) (List.range 4) := by
  intro assumed
  have wrong := assumed.2.2.2
  rw [actual_official_order] at wrong
  change [some 4, some 1, some 2, some 3] = [some 1, some 2, some 3, some 4] at wrong
  cases wrong

end InlineHydrogen

end TetraStereo.UniversalProof.RuntimeSourceRootAlignmentProofs.RuntimeSourceRootAlignment
