import TetraStereo.OneCenter.AuthoritativeSingleWedgeSourcePrimitives
import TetraStereo.OneCenter.AuthoritativeSingleWedgeOccurrenceAlignment
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceNaturality
import Mathlib.Data.Finset.Dedup

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput
namespace SingleWedgeSource

/-!
# Drawing-source completeness for actual production occurrence alignment

The source extractor admits exactly four distinct depicted neighbours, requires a semantic
single bond for each, and forbids every other semantic centre incidence. Those source facts
alone determine the canonical root children. Aromatic and multiply bonded chemistry away from
the centre is unrestricted. No atom-ID permutation or successful alignment is supplied by a
caller. The production occurrence carrier remains the existing noncomputable finite carrier.
-/

/-- Every extracted endpoint is a genuine, distinct, bounded single-bond neighbour. -/
theorem sourceFrame_endpoint_facts (source : AuthoritativeChemicalInput)
    (center : Nat) (frame : Frame) (bound : SourceFrame source center frame) :
    ∀ neighbor ∈ frame.endpoints,
      neighbor < source.molecule.atomCount ∧ neighbor ≠ center ∧
        singleNeighbor? source center neighbor = true := by
  rcases bound with ⟨diagram, positions, _, _, admitted, rfl⟩
  intro neighbor present
  rcases List.mem_map.mp present with ⟨bond, incident, rfl⟩
  have retained := (List.mem_filter.mp incident).1
  have atomBounds : bond.source < source.molecule.atomCount ∧
      bond.target < source.molecule.atomCount ∧ bond.source ≠ bond.target :=
    of_decide_eq_true (List.all_eq_true.mp admitted.2.2.2.1 bond retained)
  have distinct : endpoint center bond ≠ center ∧ bond.scope = .absolute :=
    of_decide_eq_true (List.all_eq_true.mp admitted.2.2.2.2.2.2.2.1 bond incident)
  refine ⟨?_, distinct.1, ?_⟩
  · unfold endpoint
    split
    · exact atomBounds.2.1
    · exact atomBounds.1
  · exact List.all_eq_true.mp admitted.2.2.2.2.2.2.2.2.2.2.2.2.1 bond incident

/-- All matching centre records have order one and name a drawn endpoint. Duplicate semantic
records, if allowed by the source structure, cannot introduce a different bond order. -/
theorem sourceFrame_matching_record (source : AuthoritativeChemicalInput)
    (center : Fin source.molecule.atomCount) (frame : Frame)
    (bound : SourceFrame source center.val frame) (neighbor order : Nat)
    (present : (semanticEdgeKey center.val neighbor, order) ∈
      source.molecule.localizedCovalentRecords) :
    order = 1 ∧ neighbor ∈ frame.endpoints := by
  rcases List.mem_filterMap.mp present with ⟨interaction, retained, recorded⟩
  rcases wedge_localized_record_endpoints interaction _ order recorded with
    ⟨first, second, participants, kind, key⟩
  have aligned := (wedge_semanticEdgeKey_eq_iff center.val neighbor first second).mp key
  have incident : center.val ∈ interaction.participants := by
    rcases aligned with aligned | reversed
    · simp [participants, aligned.1.symm]
    · rw [participants]
      exact List.mem_cons_of_mem first (List.mem_singleton.mpr reversed.1)
  have sourceFacts := extracted_semantic_incidents_are_binary_single source center frame
    ((extract?_eq_some_iff source center frame).mpr bound)
  rcases sourceFacts.2 interaction retained incident with
    ⟨a, b, actualParticipants, actualKind, endpoints⟩
  have orderEq : order = 1 := by simpa [kind] using actualKind
  have ab : a = first ∧ b = second := by simpa [participants] using actualParticipants.symm
  refine ⟨orderEq, ?_⟩
  rcases endpoints with endpoints | endpoints
  · have neighborEq : neighbor = b := by
      rcases aligned with aligned | reversed <;> omega
    simpa [neighborEq] using endpoints.2
  · have neighborEq : neighbor = a := by
      rcases aligned with aligned | reversed <;> omega
    simpa [neighborEq] using endpoints.2

/-- Every depicted neighbour contributes an actual positive localized record. -/
theorem sourceFrame_single_record (source : AuthoritativeChemicalInput)
    (center : Nat) (frame : Frame) (bound : SourceFrame source center frame)
    (neighbor : Nat) (present : neighbor ∈ frame.endpoints) :
    (semanticEdgeKey center neighbor, 1) ∈ source.molecule.localizedCovalentRecords := by
  have single := (sourceFrame_endpoint_facts source center frame bound neighbor present).2.2
  rcases List.any_eq_true.mp single with ⟨interaction, retained, accepted⟩
  have pair : interaction.kind = .covalent 1 ∧
      (interaction.participants = [center, neighbor] ∨
        interaction.participants = [neighbor, center]) := of_decide_eq_true accepted
  apply List.mem_filterMap.mpr
  refine ⟨interaction, retained, ?_⟩
  rcases pair.2 with written | reversed
  · simp [SemanticInteraction.localizedCovalentRecord?, written, pair.1]
  · simp [SemanticInteraction.localizedCovalentRecord?, reversed, pair.1,
      semanticEdgeKey_comm]

theorem sourceFrame_localized_keys_iff (source : AuthoritativeChemicalInput)
    (center : Fin source.molecule.atomCount) (frame : Frame)
    (bound : SourceFrame source center.val frame) (neighbor : Nat) :
    semanticEdgeKey center.val neighbor ∈ source.molecule.localizedCovalentKeys ↔
      neighbor ∈ frame.endpoints := by
  constructor
  · intro present
    rcases List.mem_map.mp present with ⟨⟨key, order⟩, retained, keyEq⟩
    dsimp at keyEq
    subst key
    exact (sourceFrame_matching_record source center frame bound neighbor order retained).2
  · intro present
    exact List.mem_map.mpr ⟨(semanticEdgeKey center.val neighbor, 1),
      sourceFrame_single_record source center.val frame bound neighbor present, rfl⟩

private theorem wedge_lookup_single_records (records : List ((Nat × Nat) × Nat))
    (key : Nat × Nat)
    (single : ∀ record ∈ records, record.1 = key → record.2 = 1) :
    SemanticMolecule.localizedBondOrderAtKey records key =
      if key ∈ records.map Prod.fst then 1 else 0 := by
  induction records with
  | nil => simp [SemanticMolecule.localizedBondOrderAtKey]
  | cons record records inductionHypothesis =>
      by_cases same : record.1 = key
      · simp [SemanticMolecule.localizedBondOrderAtKey, same,
          single record (by simp) same]
      · have tailSingle : ∀ record ∈ records, record.1 = key → record.2 = 1 := by
          intro item retained matched
          exact single item (List.mem_cons_of_mem _ retained) matched
        rw [SemanticMolecule.localizedBondOrderAtKey, if_neg same,
          inductionHypothesis tailSingle]
        simp only [List.map_cons, List.mem_cons, Ne.symm same, false_or]

/-- Canonical source adjacency at the admitted centre is exactly the drawn neighbour set. -/
theorem sourceFrame_localized_bond_order (source : AuthoritativeChemicalInput)
    (center : Fin source.molecule.atomCount) (frame : Frame)
    (bound : SourceFrame source center.val frame) (neighbor : Nat) :
    source.molecule.localizedBondOrder center.val neighbor =
      if neighbor ∈ frame.endpoints then 1 else 0 := by
  by_cases same : center.val = neighbor
  · have absent : neighbor ∉ frame.endpoints := by
      intro present
      exact (sourceFrame_endpoint_facts source center.val frame bound neighbor present).2.1
        same.symm
    simp [SemanticMolecule.localizedBondOrder, same, absent]
  · unfold SemanticMolecule.localizedBondOrder
    rw [if_neg same, wedge_lookup_single_records]
    · change (if semanticEdgeKey center.val neighbor ∈
        source.molecule.localizedCovalentKeys then 1 else 0) =
        if neighbor ∈ frame.endpoints then 1 else 0
      simp only [sourceFrame_localized_keys_iff source center frame bound neighbor]
    · intro record retained matched
      rcases record with ⟨key, order⟩
      dsimp at matched ⊢
      subst key
      exact (sourceFrame_matching_record source center frame bound neighbor order retained).1

private theorem wedge_aromatic_record_endpoints (interaction : SemanticInteraction)
    (key : Nat × Nat)
    (recorded : SemanticMolecule.aromaticPairEdge? interaction = some key) :
    ∃ first second, interaction.participants = [first, second] ∧
      interaction.kind = .aromatic ∧ key = semanticEdgeKey first second := by
  rcases interaction with ⟨participants, kind⟩
  rcases participants with _ | ⟨first, participants⟩
  · simp [SemanticMolecule.aromaticPairEdge?] at recorded
  rcases participants with _ | ⟨second, participants⟩
  · simp [SemanticMolecule.aromaticPairEdge?] at recorded
  rcases participants with _ | ⟨third, rest⟩
  · cases kind <;> simp [SemanticMolecule.aromaticPairEdge?] at recorded
    exact ⟨first, second, rfl, rfl, recorded.symm⟩
  · simp [SemanticMolecule.aromaticPairEdge?] at recorded

/-- Aromatic bonds anywhere else in the source are allowed; none can be incident here. -/
theorem sourceFrame_no_incident_aromatic (source : AuthoritativeChemicalInput)
    (center : Fin source.molecule.atomCount) (frame : Frame)
    (bound : SourceFrame source center.val frame) (neighbor : Nat) :
    semanticEdgeKey center.val neighbor ∉ source.molecule.aromaticPairEdges := by
  intro present
  rcases List.mem_filterMap.mp present with ⟨interaction, retained, recorded⟩
  rcases wedge_aromatic_record_endpoints interaction _ recorded with
    ⟨first, second, participants, kind, key⟩
  have aligned := (wedge_semanticEdgeKey_eq_iff center.val neighbor first second).mp key
  have incident : center.val ∈ interaction.participants := by
    rcases aligned with aligned | reversed
    · simp [participants, aligned.1.symm]
    · rw [participants]
      exact List.mem_cons_of_mem first (List.mem_singleton.mpr reversed.1)
  rcases (extracted_semantic_incidents_are_binary_single source center frame
    ((extract?_eq_some_iff source center frame).mpr bound)).2 interaction retained incident with
    ⟨_, _, _, single, _⟩
  simp [kind] at single

theorem sourceFrame_canonical_bond_order (source : AuthoritativeChemicalInput)
    (center : Fin source.molecule.atomCount) (frame : Frame)
    (bound : SourceFrame source center.val frame) (neighbor : Nat) :
    source.molecule.aromaticCanonicalBondOrder center.val neighbor =
      if neighbor ∈ frame.endpoints then 1 else 0 := by
  have absent := sourceFrame_no_incident_aromatic source center frame bound neighbor
  have absentReverse : semanticEdgeKey neighbor center.val ∉
      source.molecule.aromaticPairEdges := by
    rw [semanticEdgeKey_comm]
    exact absent
  simpa [SemanticMolecule.aromaticCanonicalBondOrder, absent, absentReverse] using
    sourceFrame_localized_bond_order source center frame bound neighbor

theorem sourceFrame_no_mancude_representative (source : AuthoritativeChemicalInput)
    (center : Fin source.molecule.atomCount) (frame : Frame)
    (bound : SourceFrame source center.val frame) :
    source.molecule.aromaticCanonicalMancudeRepresentativeAt?
      source.molecule.atomCount center = none := by
  apply List.find?_eq_none.mpr
  intro neighbor _
  simpa using sourceFrame_no_incident_aromatic source center frame bound neighbor.val

/-- The precise ordinary copy list consists solely of real zero-copy drawn neighbours. -/
theorem sourceFrame_ordinary_copies (source : AuthoritativeChemicalInput)
    (center : Fin source.molecule.atomCount) (frame : Frame)
    (bound : SourceFrame source center.val frame) :
    source.molecule.aromaticCanonicalOrdinaryNeighborCopiesAt
        source.molecule.atomCount center =
      ((List.finRange source.molecule.atomCount).filter
        (fun neighbor => decide (neighbor.val ∈ frame.endpoints))).map
        (fun neighbor => (neighbor, 0)) := by
  unfold SemanticMolecule.aromaticCanonicalOrdinaryNeighborCopiesAt
  have allLists (neighbors : List (Fin source.molecule.atomCount)) :
      (neighbors.flatMap fun neighbor =>
        (List.range (source.molecule.aromaticCanonicalBondOrder center.val neighbor.val)).map
          fun copyIndex => (neighbor, copyIndex)) =
      (neighbors.filter (fun neighbor => decide (neighbor.val ∈ frame.endpoints))).map
        (fun neighbor => (neighbor, 0)) := by
    induction neighbors with
    | nil => simp
    | cons neighbor neighbors inductionHypothesis =>
        rw [List.flatMap_cons, List.filter_cons]
        rw [sourceFrame_canonical_bond_order source center frame bound neighbor.val]
        by_cases present : neighbor.val ∈ frame.endpoints <;>
          simp [present, inductionHypothesis]
  exact allLists _

/-- Exact official children, prior to the independently proved carrier permutation. -/
theorem sourceFrame_official_children (source : AuthoritativeChemicalInput)
    (center : Fin source.molecule.atomCount) (frame : Frame)
    (bound : SourceFrame source center.val frame) :
    source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount
        (OfficialCIPNode.root center) =
      ((List.finRange source.molecule.atomCount).filter
        (fun neighbor => decide (neighbor.val ∈ frame.endpoints))).map
        (fun neighbor => (OfficialCIPNode.root center).extend neighbor 0) := by
  simp [SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt,
    OfficialCIPNode.root, OfficialCIPNode.isDuplicateLeaf,
    SemanticMolecule.aromaticCanonicalChildCopiesAt, OfficialCIPNode.parent?,
    sourceFrame_no_mancude_representative source center frame bound,
    sourceFrame_ordinary_copies source center frame bound, List.map_map]

/-- Exact root IDs are the source-index enumeration of the four drawn endpoint IDs. -/
theorem sourceFrame_official_root_ids (source : AuthoritativeChemicalInput)
    (center : Fin source.molecule.atomCount) (frame : Frame)
    (bound : SourceFrame source center.val frame) :
    officialRootIDs source center =
      ((List.finRange source.molecule.atomCount).filter
        (fun neighbor => decide (neighbor.val ∈ frame.endpoints))).map
        (fun neighbor => some neighbor.val) := by
  unfold officialRootIDs
  rw [sourceFrame_official_children source center frame bound]
  simp only [List.map_map]
  apply List.map_congr_left
  intro neighbor _
  rfl

/-- The source facts derive the actual official ID permutation, without guessing an order. -/
theorem sourceFrame_official_root_ids_perm (source : AuthoritativeChemicalInput)
    (center : Fin source.molecule.atomCount) (frame : Frame)
    (bound : SourceFrame source center.val frame) :
    (officialRootIDs source center).Perm (frame.endpoints.map some) := by
  rw [sourceFrame_official_root_ids source center frame bound]
  apply List.perm_of_nodup_nodup_toFinset_eq
  · apply List.Nodup.map
    · intro left right equal
      exact Fin.ext (Option.some.inj equal)
    · exact (List.nodup_finRange _).filter _
  · exact (sourceFrame_endpoints_exactly_four_distinct source center.val frame bound).2.map
      (Option.some_injective Nat)
  · apply Finset.ext
    intro atomID
    cases atomID with
    | none => simp
    | some neighbor =>
        have bounded (present : neighbor ∈ frame.endpoints) :
            neighbor < source.molecule.atomCount :=
          (sourceFrame_endpoint_facts source center.val frame bound neighbor present).1
        simp only [List.mem_toFinset, List.mem_map, List.mem_filter,
          List.mem_finRange, true_and, decide_eq_true_eq, Option.some.injEq]
        constructor
        · rintro ⟨atom, present, rfl⟩
          exact ⟨atom.val, present, rfl⟩
        · rintro ⟨value, present, equality⟩
          subst value
          exact ⟨⟨neighbor, bounded present⟩, present, rfl⟩

/-- Root-ID matching is now a theorem of source recognition for arbitrary fuel and source. -/
theorem sourceFrame_final_root_ids_perm (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (frame : Frame)
    (bound : SourceFrame source center.1.val frame) :
    (finalOccurrenceRootIDs source fuel center).Perm (frame.endpoints.map some) :=
  (finalOccurrenceRootIDs_perm_officialRootIDs source fuel center).trans
    (sourceFrame_official_root_ids_perm source center.1 frame bound)

theorem sourceFrame_occurrence_admitted (source : AuthoritativeChemicalInput) (fuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (frame : Frame)
    (bound : SourceFrame source center.1.val frame) :
    SourceOccurrenceAdmitted source fuel center :=
  ⟨frame, bound, sourceFrame_final_root_ids_perm source fuel center frame bound⟩

/-- Completeness of the actual alignment adapter from the source drawing alone. -/
theorem occurrenceAlignment?_exists_of_sourceFrame (source : AuthoritativeChemicalInput)
    (fuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) (frame : Frame)
    (bound : SourceFrame source center.1.val frame) :
    ∃ aligned, occurrenceAlignment? source fuel center = some aligned :=
  (occurrenceAlignment?_exists_iff_admitted source fuel center).mpr
    (sourceFrame_occurrence_admitted source fuel center frame bound)

/-- The actual production-order parity exists from the admitted drawing alone. -/
theorem occurrenceParity?_exists_of_sourceFrame (source : AuthoritativeChemicalInput)
    (fuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) (frame : Frame)
    (bound : SourceFrame source center.1.val frame) :
    ∃ parity, occurrenceParity? source fuel center = some parity :=
  (occurrenceParity?_exists_iff_admitted source fuel center).mpr
    (sourceFrame_occurrence_admitted source fuel center frame bound)

/-- The former root-ID hypothesis is redundant throughout the admitted drawing domain. -/
theorem sourceOccurrenceAdmitted_iff_sourceFrame (source : AuthoritativeChemicalInput)
    (fuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) :
    SourceOccurrenceAdmitted source fuel center ↔
      ∃ frame, SourceFrame source center.1.val frame := by
  constructor
  · rintro ⟨frame, bound, _⟩
    exact ⟨frame, bound⟩
  · rintro ⟨frame, bound⟩
    exact sourceFrame_occurrence_admitted source fuel center frame bound

theorem occurrenceAlignment?_exists_iff_sourceFrame (source : AuthoritativeChemicalInput)
    (fuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) :
    (∃ aligned, occurrenceAlignment? source fuel center = some aligned) ↔
      ∃ frame, SourceFrame source center.1.val frame :=
  (occurrenceAlignment?_exists_iff_admitted source fuel center).trans
    (sourceOccurrenceAdmitted_iff_sourceFrame source fuel center)

theorem occurrenceParity?_exists_iff_sourceFrame (source : AuthoritativeChemicalInput)
    (fuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) :
    (∃ parity, occurrenceParity? source fuel center = some parity) ↔
      ∃ frame, SourceFrame source center.1.val frame :=
  (occurrenceParity?_exists_iff_admitted source fuel center).trans
    (sourceOccurrenceAdmitted_iff_sourceFrame source fuel center)

end SingleWedgeSource
end AuthoritativeChemicalInput
end TetraStereo.OneCenter
