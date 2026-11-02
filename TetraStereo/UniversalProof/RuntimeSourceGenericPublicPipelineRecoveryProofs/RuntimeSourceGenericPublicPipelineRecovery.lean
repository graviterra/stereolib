import TetraStereo.UniversalProof.RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.RuntimeSourceGenericPublicPipelineRecoveryProofs.RuntimeSourceGenericPublicPipelineRecovery

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.RuntimeSourceRootAlignmentProofs.RuntimeSourceRootAlignment
open TetraStereo.UniversalProof.RuntimeOccurrenceFactRecoveryProofs.RuntimeOccurrenceFactRecovery
open TetraStereo.UniversalProof.RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge



















/-- Actual nonloop record incidence, without graph-comparison or key assumptions. -/
theorem record_neighbor_eq_some_iff (center atom : Nat) (different : atom ≠ center) (bond : RawBond) :
    recordNeighbor? center bond = some atom ↔
      (bond.source = center ∧ bond.target = atom) ∨ (bond.target = center ∧ bond.source = atom) := by
  by_cases atSource : bond.source = center
  · simp [recordNeighbor?, atSource]
    intro _ impossible
    exact False.elim (different impossible.symm)
  · by_cases atTarget : bond.target = center
    · simp [recordNeighbor?, atSource, atTarget]
    · simp [recordNeighbor?, atSource, atTarget]

/-- The same actual bond record denotes both orientations of an edge. -/
theorem record_neighbor_symmetric (center atom : Nat) (different : atom ≠ center) (bond : RawBond) :
    recordNeighbor? center bond = some atom ↔ recordNeighbor? atom bond = some center := by
  rw [record_neighbor_eq_some_iff center atom different bond,
    record_neighbor_eq_some_iff atom center different.symm bond]
  constructor
  · rintro (⟨first, second⟩ | ⟨first, second⟩)
    · exact Or.inr ⟨second, first⟩
    · exact Or.inl ⟨second, first⟩
  · rintro (⟨first, second⟩ | ⟨first, second⟩)
    · exact Or.inr ⟨second, first⟩
    · exact Or.inl ⟨second, first⟩

/-- Edge-record counts are symmetric BEFORE the production incident-neighbor deduplication. -/
theorem record_neighbor_count_symmetric (raw : RawMolecule) (center atom : Nat) (different : atom ≠ center) :
    (recordNeighbors raw center).count atom = (recordNeighbors raw atom).count center := by
  unfold recordNeighbors
  rw [List.count_filterMap, List.count_filterMap]
  apply List.countP_congr
  intro bond _
  simpa only [beq_iff_eq] using record_neighbor_symmetric center atom different bond

private theorem mem_eraseDups_iff (atom : Nat) (values : List Nat) :
    atom ∈ values.eraseDups ↔ atom ∈ values := by
  cases values with
  | nil => simp
  | cons head tail =>
      rw [List.eraseDups_cons]
      by_cases same : atom = head
      · subst head
        simp
      · have filtered := mem_eraseDups_iff atom (tail.filter fun next => !next == head)
        simpa [same] using filtered
termination_by values.length
decreasing_by
  have filtered := List.length_filter_le (fun next => !next == head) tail
  simpa using Nat.lt_succ_of_le filtered

theorem incident_neighbor_mem_iff (raw : RawMolecule) (center atom : Nat) :
    atom ∈ raw.incidentAtoms center ↔ atom ∈ recordNeighbors raw center := by
  change atom ∈ (recordNeighbors raw center).eraseDups ↔ _
  exact mem_eraseDups_iff atom (recordNeighbors raw center)

/-- Real reverse incidence is derived from the retained source bond, not guessed root ancestry. -/
theorem reverse_record_neighbor_mem (raw : RawMolecule) (center atom : Nat)
    (domain : LeafNeighborDomain raw center) (member : atom ∈ recordNeighbors raw center) :
    center ∈ recordNeighbors raw atom := by
  obtain ⟨bond, retained, observed⟩ := List.mem_filterMap.mp member
  have different := (recordNeighbor_bounds domain.wellFormed member).2
  exact List.mem_filterMap.mpr ⟨bond, retained, (record_neighbor_symmetric center atom different bond).mp observed⟩

private theorem equal_of_mem_degree_one {atoms : List Nat} (degree : atoms.length ≤ 1)
    {first second : Nat} (firstMember : first ∈ atoms) (secondMember : second ∈ atoms) : first = second := by
  cases atoms with
  | nil => simp at firstMember
  | cons head tail =>
      cases tail with
      | nil =>
          simp only [List.mem_singleton] at firstMember secondMember
          exact firstMember.trans secondMember.symm
      | cons next rest =>
          simp only [List.length_cons] at degree
          omega

/-- Physical degree-one and exact duplicate-free central incidence derive the FULL leaf record row.
No actual canonical-child or collector outcome is included in the graph premise. -/
theorem actual_leaf_record_row (raw : RawMolecule) (center atom : Nat)
    (domain : LeafNeighborDomain raw center) (member : atom ∈ recordNeighbors raw center) :
    recordNeighbors raw atom = [center] := by
  have different := (recordNeighbor_bounds domain.wellFormed member).2
  have reverse := reverse_record_neighbor_mem raw center atom domain member
  have centerIncident := (incident_neighbor_mem_iff raw atom center).mpr reverse
  have allCenter : ∀ other ∈ recordNeighbors raw atom, center = other := by
    intro other retained
    exact equal_of_mem_degree_one (domain.leaf member) centerIncident
      ((incident_neighbor_mem_iff raw atom other).mpr retained)
  have forwardCount : (recordNeighbors raw center).count atom = 1 :=
    List.count_eq_one_of_mem domain.neighbors_nodup member
  have reverseCount : (recordNeighbors raw atom).count center = 1 :=
    (record_neighbor_count_symmetric raw center atom different).symm.trans forwardCount
  have countLength : (recordNeighbors raw atom).count center = (recordNeighbors raw atom).length :=
    List.count_eq_length.mpr allCenter
  have recovered := (List.replicate_count_eq_of_count_eq_length countLength).symm
  rw [reverseCount] at recovered
  simpa only [List.replicate_succ, List.replicate_zero] using recovered

private theorem unit_copy_records (raw : RawMolecule) (node : RawMolecule.CanonicalBranchNode)
    (bonds : List RawBond)
    (single : ∀ bond ∈ bonds, ∀ atom, recordNeighbor? node.atom bond = some atom →
      raw.canonicalBondOrder node atom = 1) :
    (bonds.flatMap fun bond =>
      match recordNeighbor? node.atom bond with
      | none => []
      | some atom => (List.range (raw.canonicalBondOrder node atom)).map (fun copy => (atom, copy))) =
      (bonds.filterMap (recordNeighbor? node.atom)).map (fun atom => (atom, 0)) := by
  induction bonds with
  | nil => rfl
  | cons bond bonds inductionHypothesis =>
      have tailSingle : ∀ selected ∈ bonds, ∀ atom, recordNeighbor? node.atom selected = some atom →
          raw.canonicalBondOrder node atom = 1 := by
        intro selected retained atom observed
        exact single selected (List.mem_cons_of_mem bond retained) atom observed
      simp only [List.flatMap_cons, List.filterMap_cons]
      cases observed : recordNeighbor? node.atom bond with
      | none => simpa only [List.nil_append] using inductionHypothesis tailSingle
      | some atom =>
          have order := single bond List.mem_cons_self atom observed
          simp only [order, List.range_succ, List.range_zero, List.nil_append,
            List.map_cons, List.map_nil, List.cons_append]
          rw [inductionHypothesis tailSingle]

/-- The actual leaf expansion has exactly one parent copy, and removes that copy. -/
theorem actual_leaf_child_copies_empty (raw : RawMolecule) (center atom : Nat)
    (domain : LeafNeighborDomain raw center) (member : atom ∈ recordNeighbors raw center) :
    raw.canonicalChildCopies (canonicalRoot center atom) = [] := by
  have row := actual_leaf_record_row raw center atom domain member
  have copies := unit_copy_records raw (canonicalRoot center atom) raw.bonds (by
    intro bond retained next observed
    have inRow : next ∈ recordNeighbors raw atom := List.mem_filterMap.mpr ⟨bond, retained, observed⟩
    rw [row] at inRow
    have equal : next = center := List.mem_singleton.mp inRow
    subst next
    have reverseOrder : raw.bondOrder atom center = 1 :=
      (raw.bondOrder_symm atom center).trans (domain.single member)
    simp [canonicalBondOrder, canonicalRoot, reverseOrder])
  change (raw.bonds.flatMap fun bond =>
    match recordNeighbor? atom bond with
    | none => []
    | some next => (List.range (raw.canonicalBondOrder (canonicalRoot center atom) next)).map
        (fun copy => (next, copy))) =
      (recordNeighbors raw atom).map (fun next => (next, 0)) at copies
  unfold canonicalChildCopies
  change eraseCanonicalParentCopy center
    (raw.bonds.flatMap fun bond =>
      match recordNeighbor? atom bond with
      | none => []
      | some next => (List.range (raw.canonicalBondOrder (canonicalRoot center atom) next)).map
          (fun copy => (next, copy))) = []
  rw [copies]
  rw [row]
  simp [eraseCanonicalParentCopy]

theorem actual_leaf_children_empty (raw : RawMolecule) (center atom : Nat)
    (domain : LeafNeighborDomain raw center) (member : atom ∈ recordNeighbors raw center) :
    raw.canonicalChildren (canonicalRoot center atom) = [] := by
  simp [canonicalChildren, actual_leaf_child_copies_empty raw center atom domain member]

theorem actual_leaf_frontier_empty (raw : RawMolecule) (center : Nat)
    (domain : LeafNeighborDomain raw center) :
    ((recordNeighbors raw center).map (canonicalRoot center)).flatMap raw.canonicalChildren = [] := by
  rw [List.flatMap_map]
  apply List.flatMap_eq_nil_iff.mpr
  intro atom member
  exact actual_leaf_children_empty raw center atom domain member

/-- The actual complete two-level canonical tree, with actual bond-record order retained. -/
def actualTree (raw : RawMolecule) (center : Nat) : List RawMolecule.CanonicalBranchNode :=
  canonicalCenterRoot center :: (recordNeighbors raw center).map (canonicalRoot center)

/-- GENERAL collector success from independent graph facts. There is NO supplied tree equation. -/
theorem actual_collected_tree (raw : RawMolecule) (center : Nat)
    (domain : LeafNeighborDomain raw center) (extraFuel : Nat) :
    collectCanonicalTreeAuthoritative raw (extraFuel + 2) [canonicalCenterRoot center] =
      some (actualTree raw center) := by
  simp only [collectCanonicalTreeAuthoritative, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, canonicalChildren_centerRoot_eq raw center domain]
  have leafCollected : collectCanonicalTreeAuthoritative raw (extraFuel + 1)
      ((recordNeighbors raw center).map (canonicalRoot center)) =
        some ((recordNeighbors raw center).map (canonicalRoot center)) := by
    cases frontier : ((recordNeighbors raw center).map (canonicalRoot center)) with
    | nil => rfl
    | cons first remaining =>
        have frontierEmpty := actual_leaf_frontier_empty raw center domain
        rw [frontier] at frontierEmpty
        change (do
          let tail ← collectCanonicalTreeAuthoritative raw extraFuel
            ((first :: remaining).flatMap raw.canonicalChildren)
          some ((first :: remaining) ++ tail)) = some (first :: remaining)
        rw [frontierEmpty, collected_empty]
        simp
  rw [leafCollected]
  rfl

/-- GENERAL internally derived whole auxiliary state from independent raw annotation intake. -/
theorem actual_auxiliary_state (raw : RawMolecule) (center : Nat)
    (domain : LeafNeighborDomain raw center) (only : OnlyCenterTagged raw center) (extraFuel : Nat) :
    buildOccurrenceAuxStateFullyAuthoritative? raw (extraFuel + 2) center = some [] :=
  auxiliary_state_empty_of_actual_tree raw (extraFuel + 2) center only (actualTree raw center)
    (actual_collected_tree raw center domain extraFuel)

/-- GENERAL actual public occurrence API success; no supplied tree, state, successful callback,
positions, sorted order or descriptor occurs in its premises. The input tag is the real atom. -/
theorem actual_public_fact_exists (raw : RawMolecule) (center : Nat)
    (domain : SingleLeafDomain raw center) (written : raw.WrittenNeighborExact)
    (four : (recordNeighbors raw center).length = 4) (only : OnlyCenterTagged raw center)
    (spec : AtomSpec) (atomObserved : raw.atomAt? center = some spec)
    (parity : TetrahedralInputParity) (parityObserved : spec.tetrahedral? = some parity)
    (extraFuel : Nat) :
    ∃ positions, tetrahedralOccurrenceFact? raw (extraFuel + 2) center =
      some (recoveredPublicFact center positions (RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven positions))) :=
  public_fact_exists_of_actual_tree raw (extraFuel + 2) center domain written four only
    (actualTree raw center) (actual_collected_tree raw center domain.leaf extraFuel)
    spec atomObserved parity parityObserved

/-- GENERAL SAME-source public pipeline / actual parser agreement, with independent parser meaning.
The public occurrence API computes its own actual auxiliary state; there is no expected output
or collected-tree premise. The formal NoDouble backend restriction is retained explicitly. -/
theorem actual_public_formal_alignment (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement raw source) (written : raw.WrittenNeighborExact)
    (carrierFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SingleLeafDomain raw center.1.val) (four : (recordNeighbors raw center.1.val).length = 4)
    (only : OnlyCenterTagged raw center.1.val) (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    (spec : AtomSpec) (atomObserved : raw.atomAt? center.1.val = some spec)
    (parity : TetrahedralInputParity) (parityObserved : spec.tetrahedral? = some parity)
    (view : source.AromaticCanonicalDependencyView (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (extraFuel : Nat) :
    ∃ positions descriptor,
      tetrahedralOccurrenceFact? raw (extraFuel + 2) center.1.val =
        some (recoveredPublicFact center.1.val positions descriptor) ∧
      constitutionParserRichDescriptor? raw source agreement written
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view (2 * (carrierFuel + 1)) =
          some (.chiral descriptor) ∧
      ConstitutionParserRichDescriptorMeaning raw source agreement written
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view (2 * (carrierFuel + 1))
          (.chiral descriptor) ∧
      descriptor = RawMolecule.descriptorOfParity parity (RawMolecule.permutationIsEven positions) := by
  obtain ⟨positions, descriptor, localComputed, parserComputed, parserMeaning, formula⟩ :=
    actual_runtime_fact_formal_alignment raw source agreement written carrierFuel center domain four
      noDouble spec atomObserved parity parityObserved view [] (extraFuel + 2)
  refine ⟨positions, descriptor, ?_, parserComputed, parserMeaning, formula⟩
  exact public_fact_of_actual_local_fact raw (extraFuel + 2) center.1.val only (actualTree raw center.1.val)
    (actual_collected_tree raw center.1.val domain.leaf extraFuel) positions descriptor localComputed

/-- The independent graph domain is inhabited by the actual checked CF input; this uses the
general collector proof rather than a literal tree evaluation. -/
theorem actual_CF_collected_tree (extraFuel : Nat) :
    collectCanonicalTreeAuthoritative RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery.ClosedCF.raw (extraFuel + 2) [canonicalCenterRoot 0] =
      some (actualTree RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery.ClosedCF.raw 0) :=
  actual_collected_tree RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery.ClosedCF.raw 0
    RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment.ClosedCF.actual_domain.leaf extraFuel

/-- A genuine actual CF auxiliary environment, derived using the general graph theorem. -/
theorem actual_CF_auxiliary_state (extraFuel : Nat) :
    buildOccurrenceAuxStateFullyAuthoritative? RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery.ClosedCF.raw (extraFuel + 2) 0 = some [] :=
  actual_auxiliary_state RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery.ClosedCF.raw 0
    RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment.ClosedCF.actual_domain.leaf
    RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery.ClosedCF.actual_only_center_tagged extraFuel

end TetraStereo.UniversalProof.RuntimeSourceGenericPublicPipelineRecoveryProofs.RuntimeSourceGenericPublicPipelineRecovery
