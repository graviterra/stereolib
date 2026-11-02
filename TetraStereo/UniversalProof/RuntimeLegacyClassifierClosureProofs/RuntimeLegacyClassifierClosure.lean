import TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery
import Mathlib.Data.List.GetD

set_option autoImplicit false

namespace TetraStereo.UniversalProof.RuntimeLegacyClassifierClosureProofs.RuntimeLegacyClassifierClosure

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.RuntimeSourceRootAlignmentProofs.RuntimeSourceRootAlignment
open TetraStereo.UniversalProof.NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
















/-- Sorting-library law: off-diagonal callback agreement is enough; the sort never compares a
fresh candidate with the same-ranked element under independent distinct-rank intake. -/
theorem insertDescBy_strict_rank {alpha : Type*} (candidateUniverse : List alpha)
    (rank : alpha → Nat) (before : alpha → alpha → Bool)
    (correct : ∀ a ∈ candidateUniverse, ∀ b ∈ candidateUniverse, rank a ≠ rank b →
      before a b = decide (rank b < rank a)) (candidate : alpha) (candidateIn : candidate ∈ candidateUniverse) :
    ∀ existing : List alpha, (∀ a ∈ existing, a ∈ candidateUniverse) →
      rank candidate ∉ existing.map rank →
      existing.Pairwise (fun a b => rank b < rank a) →
      (insertDescBy before candidate existing).Pairwise (fun a b => rank b < rank a) := by
  intro existing
  induction existing with
  | nil => intro _ _ _; simp only [insertDescBy, List.pairwise_singleton]
  | cons head tail inductionHypothesis =>
      intro members fresh sorted
      have headIn := members head List.mem_cons_self
      have tailMembers : ∀ a ∈ tail, a ∈ candidateUniverse :=
        fun a member => members a (List.mem_cons_of_mem head member)
      have different : rank candidate ≠ rank head := by
        intro same
        exact fresh (List.mem_map.mpr ⟨head, List.mem_cons_self, same.symm⟩)
      have tailFresh : rank candidate ∉ tail.map rank := by
        intro member
        exact fresh (List.mem_cons_of_mem (rank head) member)
      have headBefore := (List.pairwise_cons.mp sorted).1
      have tailSorted := (List.pairwise_cons.mp sorted).2
      rcases Nat.lt_or_gt_of_ne different with lower | higher
      · have compared : before candidate head = false := by
          rw [correct candidate candidateIn head headIn different]
          exact decide_eq_false (by omega)
        simp only [insertDescBy, compared, Bool.false_eq_true, ite_false]
        apply List.pairwise_cons.mpr
        refine ⟨?_, inductionHypothesis tailMembers tailFresh tailSorted⟩
        intro other member
        have original := (insertDescBy_perm before candidate tail).mem_iff.mp member
        rcases List.mem_cons.mp original with same | inTail
        · simpa only [same] using lower
        · exact headBefore other inTail
      · have compared : before candidate head = true := by
          rw [correct candidate candidateIn head headIn different]
          exact decide_eq_true higher
        simp only [insertDescBy, compared, ite_true]
        apply List.pairwise_cons.mpr
        refine ⟨?_, sorted⟩
        intro other member
        rcases List.mem_cons.mp member with same | inTail
        · simpa only [same] using higher
        · exact lt_trans (headBefore other inTail) higher

theorem sortDescBy_strict_rank {alpha : Type*} (candidateUniverse : List alpha)
    (rank : alpha → Nat) (before : alpha → alpha → Bool)
    (correct : ∀ a ∈ candidateUniverse, ∀ b ∈ candidateUniverse, rank a ≠ rank b →
      before a b = decide (rank b < rank a)) :
    ∀ values : List alpha, (∀ a ∈ values, a ∈ candidateUniverse) → (values.map rank).Nodup →
      (sortDescBy before values).Pairwise (fun a b => rank b < rank a) := by
  intro values
  induction values with
  | nil => intro _ _; exact List.Pairwise.nil
  | cons head tail inductionHypothesis =>
      intro members distinct
      have clauses : rank head ∉ tail.map rank ∧ (tail.map rank).Nodup := by
        simpa only [List.map_cons, List.nodup_cons] using distinct
      have tailMembers : ∀ a ∈ tail, a ∈ candidateUniverse :=
        fun a member => members a (List.mem_cons_of_mem head member)
      have sortedPerm := sortDescBy_perm before tail
      change (insertDescBy before head (sortDescBy before tail)).Pairwise _
      apply insertDescBy_strict_rank candidateUniverse rank before correct head (members head List.mem_cons_self)
      · intro a member
        exact tailMembers a (sortedPerm.mem_iff.mp member)
      · intro member
        exact clauses.1 ((sortedPerm.map rank).mem_iff.mp member)
      · exact inductionHypothesis tailMembers clauses.2

theorem position_projection_range (values : List Nat) :
    (List.range values.length).map (fun position => values.getD position 0) = values := by
  apply List.ext_getElem (by simp only [List.length_map, List.length_range])
  intro index _ bound
  simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem values 0 bound]

/-- ACTUAL legacy written-position order, used unchanged by the production ranker. -/
def legacyPositions (raw : RawMolecule) (fuel center : Nat) (branches : List Nat) : List Nat :=
  sortDescBy (fun a b =>
    raw.compareBranches fuel center (branches.getD a 0) (branches.getD b 0) != Ordering.lt)
    (List.range branches.length)

theorem legacy_positions_perm (raw : RawMolecule) (fuel center : Nat) (branches : List Nat) :
    (legacyPositions raw fuel center branches).Perm (List.range branches.length) :=
  sortDescBy_perm _ _

theorem actual_legacy_before (raw : RawMolecule) (fuel center left right : Nat)
    (different : raw.atomZAt left ≠ raw.atomZAt right) :
    (raw.compareBranches fuel center left right != Ordering.lt) =
      decide (raw.atomZAt right < raw.atomZAt left) := by
  unfold compareBranches
  rw [actual_legacy_strict_branch raw fuel center left right different]
  rcases Nat.lt_or_gt_of_ne different with lower | higher
  · rw [Nat.compare_eq_lt.mpr lower]
    change false = decide (raw.atomZAt right < raw.atomZAt left)
    exact (decide_eq_false (by omega)).symm
  · rw [Nat.compare_eq_gt.mpr higher]
    change true = decide (raw.atomZAt right < raw.atomZAt left)
    exact (decide_eq_true higher).symm

theorem legacy_positions_strict (raw : RawMolecule) (fuel center : Nat) (branches : List Nat)
    (distinct : (branches.map raw.atomZAt).Nodup) :
    (legacyPositions raw fuel center branches).Pairwise
      (fun a b => raw.atomZAt (branches.getD b 0) < raw.atomZAt (branches.getD a 0)) := by
  apply sortDescBy_strict_rank (List.range branches.length)
    (fun position => raw.atomZAt (branches.getD position 0)) _
  · intro a _ b _ different
    exact actual_legacy_before raw fuel center _ _ different
  · intro _ member; exact member
  · have same : (List.range branches.length).map
        (fun position => raw.atomZAt (branches.getD position 0)) = branches.map raw.atomZAt := by
      simpa only [List.map_map] using
        congrArg (List.map raw.atomZAt) (position_projection_range branches)
    exact same.symm ▸ distinct

/-- Every actual adjacent check passes: no sorted-position or callback success is supplied. -/
theorem actual_legacy_adjacent_checks (raw : RawMolecule) (fuel center : Nat) (branches : List Nat)
    (distinct : (branches.map raw.atomZAt).Nodup) :
    (List.range ((legacyPositions raw fuel center branches).length - 1)).all (fun index =>
      match (legacyPositions raw fuel center branches)[index]?,
          (legacyPositions raw fuel center branches)[index + 1]? with
      | some left, some right => raw.compareBranches? fuel center
          (branches.getD left 0) (branches.getD right 0) == some Ordering.gt
      | _, _ => false) = true := by
  apply List.all_eq_true.mpr
  intro index member
  have beforeEnd := List.mem_range.mp member
  have leftBound : index < (legacyPositions raw fuel center branches).length := by omega
  have rightBound : index + 1 < (legacyPositions raw fuel center branches).length := by omega
  have higher := (List.pairwise_iff_getElem.mp (legacy_positions_strict raw fuel center branches distinct))
    index (index + 1) leftBound rightBound (by omega)
  have different : raw.atomZAt (branches.getD (legacyPositions raw fuel center branches)[index] 0) ≠
      raw.atomZAt (branches.getD (legacyPositions raw fuel center branches)[index + 1] 0) := by omega
  simp only [getElem?_pos (legacyPositions raw fuel center branches) index leftBound,
    getElem?_pos (legacyPositions raw fuel center branches) (index + 1) rightBound,
    actual_legacy_strict_branch raw fuel center _ _ different, Nat.compare_eq_gt.mpr higher,
    beq_self_eq_true]

theorem actual_legacy_rank (raw : RawMolecule) (fuel center : Nat) (branches : List Nat)
    (distinct : (branches.map raw.atomZAt).Nodup) :
    raw.rankBranchPositions? fuel center branches = some (legacyPositions raw fuel center branches) := by
  change (if (List.range ((legacyPositions raw fuel center branches).length - 1)).all (fun index =>
      match (legacyPositions raw fuel center branches)[index]?,
          (legacyPositions raw fuel center branches)[index + 1]? with
      | some left, some right => raw.compareBranches? fuel center
          (branches.getD left 0) (branches.getD right 0) == some Ordering.gt
      | _, _ => false) then some (legacyPositions raw fuel center branches) else none) = _
  simp only [actual_legacy_adjacent_checks raw fuel center branches distinct, ite_true]

/-- Independent raw observation class for the HIGHER legacy consumer. It requires no leaf,
acyclicity, global NoDouble, generated frame, source output or caller-specified priority order. -/
structure LegacyAtomicIntake (raw : RawMolecule) (center : Nat) (spec : AtomSpec)
    (parity : TetrahedralInputParity) : Prop where
  observed : raw.atomAt? center = some spec
  tagged : spec.tetrahedral? = some parity
  supported : centreElementSupported spec.element = true
  four : (raw.writtenNeighbors center).length = 4
  distinct : ((raw.writtenNeighbors center).map raw.atomZAt).Nodup

theorem actual_legacy_outcome (raw : RawMolecule) (center fuel : Nat) (spec : AtomSpec)
    (parity : TetrahedralInputParity) (intake : LegacyAtomicIntake raw center spec parity) :
    raw.tetrahedralOutcome fuel center = .tetrahedral
      (descriptorOfParity parity (permutationIsEven
        (legacyPositions raw fuel center (raw.writtenNeighbors center)))) := by
  have ligands := AuthoritativeCIPRule6Scheduler.ligandsWithLonePair_eq_writtenNeighbors_of_length_four
    raw center intake.four
  simp [tetrahedralOutcome, intake.observed, intake.tagged, intake.supported, ligands, intake.four,
    actual_legacy_rank raw fuel center (raw.writtenNeighbors center) intake.distinct]

theorem actual_expanded_classifier (raw : RawMolecule) (center : Nat) (spec : AtomSpec)
    (parity : TetrahedralInputParity) (intake : LegacyAtomicIntake raw center spec parity)
    (known : raw.rule2MassesKnown? = true) :
    expandedTetrahedralDescriptorAt? raw center = some
      (descriptorOfParity parity (permutationIsEven
        (legacyPositions raw (analysisFuel raw) center (raw.writtenNeighbors center)))) := by
  simp [expandedTetrahedralDescriptorAt?, known,
    actual_legacy_outcome raw center (analysisFuel raw) spec parity intake]

theorem original_normalized_legacy_intake (raw : RawMolecule) (center : Nat)
    (intake : NormalizedLeafIntake raw center) (four : (recordNeighbors raw center).length = 4)
    (spec : AtomSpec) (observed : raw.atomAt? center = some spec)
    (parity : TetrahedralInputParity) (tagged : spec.tetrahedral? = some parity)
    (supported : centreElementSupported spec.element = true) :
    LegacyAtomicIntake (parsedInput raw) center (materializedAtomSpec spec) parity := by
  have writtenFour := actual_written_four raw center intake.domain intake.writtenExact four
  have writtenPerm := written_neighbors_perm_records raw center intake.domain intake.writtenExact
  refine ⟨?_, tagged, supported, ?_, ?_⟩
  · rw [actual_parsed_atom_lookup raw center intake, observed]; rfl
  · rw [actual_parsed_written_order raw center intake center intake.domain.leaf.centerBound]
    exact writtenFour
  · rw [actual_parsed_written_order raw center intake center intake.domain.leaf.centerBound]
    have atomicNumbers : (parsedInput raw).atomZAt = raw.atomZAt := by
      funext index
      exact actual_parsed_atomic_number raw center intake index
    simpa only [atomicNumbers] using
      (writtenPerm.map raw.atomZAt).nodup_iff.mpr intake.domain.leaf.distinctRanks

/-- GENERAL actual HIGHER parsed classifier result on ORIGINAL independent normalized-leaf intake.
The returned label is computed from its own actual sorted written positions, not supplied. -/
theorem actual_parsed_classifier (raw : RawMolecule) (center : Nat)
    (intake : NormalizedLeafIntake raw center) (four : (recordNeighbors raw center).length = 4)
    (spec : AtomSpec) (observed : raw.atomAt? center = some spec)
    (parity : TetrahedralInputParity) (tagged : spec.tetrahedral? = some parity)
    (supported : centreElementSupported spec.element = true) (known : raw.rule2MassesKnown? = true) :
    parsedTetrahedralDescriptorAt? raw center = some
      (descriptorOfParity parity (permutationIsEven
        (legacyPositions (parsedInput raw) (analysisFuel (parsedInput raw)) center
          ((parsedInput raw).writtenNeighbors center)))) := by
  rw [parsed_classifier_input]
  exact actual_expanded_classifier (parsedInput raw) center (materializedAtomSpec spec) parity
    (original_normalized_legacy_intake raw center intake four spec observed parity tagged supported)
    (actual_parsed_mass_guard raw known)

theorem legacy_sorted_atom_ids_perm (raw : RawMolecule) (fuel center : Nat) (branches : List Nat) :
    ((legacyPositions raw fuel center branches).map (fun position => branches.getD position 0)).Perm branches := by
  have permutation := (legacy_positions_perm raw fuel center branches).map
    (fun position => branches.getD position 0)
  rw [position_projection_range] at permutation
  exact permutation

theorem written_positions_roundtrip (written : List Nat) (distinct : written.Nodup) :
    ∀ positions : List Nat, (∀ position ∈ positions, position < written.length) →
      (positions.map (fun position => written.getD position 0)).mapM (writtenSlot? written) =
        some positions := by
  intro positions
  induction positions with
  | nil => intro _; rfl
  | cons position tail inductionHypothesis =>
      intro bounds
      have bound := bounds position List.mem_cons_self
      have observed : written[position]? = some (written.getD position 0) := by
        rw [getElem?_pos written position bound, List.getD_eq_getElem written 0 bound]
      have slot := writtenSlot?_eq_some written distinct position (written.getD position 0) observed
      simp only [List.map_cons, List.mapM_cons, slot,
        inductionHypothesis (fun other member => bounds other (List.mem_cons_of_mem position member))]
      rfl

/-- The two ACTUAL sorters return the same written positions. The legacy consumer's own sort
and authoritative runtime's own generated roots are independently derived, then aligned by
strict atom-ID permutation uniqueness. The arbitrary physical-H slot order is retained. -/
theorem actual_runtime_positions_legacy (raw : RawMolecule) (center : Nat)
    (domain : SingleLeafDomain raw center) (written : raw.WrittenNeighborExact)
    (four : (recordNeighbors raw center).length = 4) (state : OccurrenceAuxState)
    (runtimeFuel legacyFuel : Nat) (result : List CanonicalRerootCursor × Nat)
    (computed : sortOccurrencesTrackedAuthoritative? raw state runtimeFuel
      (generatedRuntimeRoots raw center) = some result) :
    runtimePriorityPositions? raw center result.1 =
      some (legacyPositions raw legacyFuel center (raw.writtenNeighbors center)) := by
  obtain ⟨actual, actualComputed, permutation, strict, _⟩ :=
    generated_runtime_sort raw center runtimeFuel domain.leaf state
  have sameResult : result = actual := Option.some.inj (computed.symm.trans actualComputed)
  subst result
  have writtenPerm := written_neighbors_perm_records raw center domain written
  have writtenNodup := writtenPerm.nodup_iff.mpr domain.leaf.neighbors_nodup
  have distinct := (writtenPerm.map raw.atomZAt).nodup_iff.mpr domain.leaf.distinctRanks
  have runtimeIDsPerm : (actual.1.map (fun cursor => cursor.node.atom)).Perm (recordNeighbors raw center) := by
    have mapped := permutation.map (fun cursor => cursor.node.atom)
    rw [generatedRuntimeRoots_eq raw center domain.leaf] at mapped
    simpa only [List.map_map, Function.comp_def, canonicalRoot, List.map_id'] using mapped
  have runtimeStrict : (actual.1.map (fun cursor => cursor.node.atom)).Pairwise
      (fun a b => raw.atomZAt b < raw.atomZAt a) := List.pairwise_map.mpr strict
  have legacyStrict : ((legacyPositions raw legacyFuel center (raw.writtenNeighbors center)).map
      (fun position => (raw.writtenNeighbors center).getD position 0)).Pairwise
        (fun a b => raw.atomZAt b < raw.atomZAt a) :=
    List.pairwise_map.mpr (legacy_positions_strict raw legacyFuel center _ distinct)
  have idsEqual := RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment.atom_id_order_unique raw _ _
    runtimeStrict legacyStrict
    (runtimeIDsPerm.trans (legacy_sorted_atom_ids_perm raw legacyFuel center _ |>.trans writtenPerm).symm)
  have ligands := AuthoritativeCIPRule6Scheduler.ligandsWithLonePair_eq_writtenNeighbors_of_length_four
    raw center (actual_written_four raw center domain written four)
  unfold runtimePriorityPositions?
  rw [ligands]
  change actual.1.mapM ((writtenSlot? (raw.writtenNeighbors center)) ∘ (fun cursor => cursor.node.atom)) = _
  rw [← List.mapM_map, idsEqual]
  apply written_positions_roundtrip _ writtenNodup
  intro position member
  exact List.mem_range.mp ((legacy_positions_perm raw legacyFuel center _).mem_iff.mp member)

/-- Genuine expanded-input HIGHER classifier / SAME-source parser equality, with the parser's
OWN independent meaning. No source-global NoDouble hypothesis or caller parity result appears. -/
theorem actual_higher_source_alignment (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement raw source) (written : raw.WrittenNeighborExact)
    (carrierFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SingleLeafDomain raw center.1.val) (four : (recordNeighbors raw center.1.val).length = 4)
    (spec : AtomSpec) (observed : raw.atomAt? center.1.val = some spec)
    (parity : TetrahedralInputParity) (tagged : spec.tetrahedral? = some parity)
    (supported : centreElementSupported spec.element = true) (known : raw.rule2MassesKnown? = true)
    (view : source.AromaticCanonicalDependencyView (source.aromaticCanonicalFinalOccurrence carrierFuel center)) :
    ∃ descriptor,
      expandedTetrahedralDescriptorAt? raw center.1.val = some descriptor ∧
      constitutionParserRichDescriptor? raw source agreement written
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view (2 * (carrierFuel + 1)) =
          some (.chiral descriptor) ∧
      ConstitutionParserRichDescriptorMeaning raw source agreement written
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view (2 * (carrierFuel + 1))
          (.chiral descriptor) := by
  obtain ⟨result, positions, descriptor, _, runtimeComputed, positionsComputed, formula,
      parserComputed, meaning, _⟩ :=
    NativeSourceSingleIncidenceProofs.LocalSourceRule3AllCarrierRecovery.actual_local_descriptor_transport raw source
      agreement written carrierFuel center domain four spec observed parity tagged view [] 0
  have equalPositions := Option.some.inj (positionsComputed.symm.trans
    (actual_runtime_positions_legacy raw center.1.val domain written four [] 0 (analysisFuel raw)
      result runtimeComputed))
  have legacyIntake : LegacyAtomicIntake raw center.1.val spec parity :=
    ⟨observed, tagged, supported, actual_written_four raw center.1.val domain written four,
      (written_neighbors_perm_records raw center.1.val domain written |>.map raw.atomZAt).nodup_iff.mpr
        domain.leaf.distinctRanks⟩
  refine ⟨descriptor, ?_, parserComputed, meaning⟩
  rw [formula, equalPositions]
  exact actual_expanded_classifier raw center.1.val spec parity legacyIntake known

/-- GENERAL HIGHER parsed input and OWN materialized-source parser now emit the same descriptor.
Source agreement refers to the actual parsedInput, not an original-input nominal source cast. -/
theorem actual_parsed_source_alignment (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : RawAnnotationAgreement (parsedInput raw) source) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (intake : NormalizedLeafIntake raw center.1.val)
    (four : (recordNeighbors raw center.1.val).length = 4)
    (spec : AtomSpec) (observed : raw.atomAt? center.1.val = some spec)
    (parity : TetrahedralInputParity) (tagged : spec.tetrahedral? = some parity)
    (supported : centreElementSupported spec.element = true) (known : raw.rule2MassesKnown? = true)
    (view : source.AromaticCanonicalDependencyView (source.aromaticCanonicalFinalOccurrence carrierFuel center)) :
    ∃ descriptor,
      parsedTetrahedralDescriptorAt? raw center.1.val = some descriptor ∧
      constitutionParserRichDescriptor? (parsedInput raw) source agreement
        (actual_parsed_written_exact raw center.1.val intake)
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view (2 * (carrierFuel + 1)) =
          some (.chiral descriptor) ∧
      ConstitutionParserRichDescriptorMeaning (parsedInput raw) source agreement
        (actual_parsed_written_exact raw center.1.val intake)
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view (2 * (carrierFuel + 1))
          (.chiral descriptor) := by
  rw [parsed_classifier_input]
  apply actual_higher_source_alignment (parsedInput raw) source agreement
    (actual_parsed_written_exact raw center.1.val intake) carrierFuel center
    (actual_parsed_domain raw center.1.val intake)
    (by simpa only [actual_parsed_neighbors raw center.1.val intake] using four)
    (materializedAtomSpec spec) (by
      rw [actual_parsed_atom_lookup raw center.1.val intake, observed]; rfl)
    parity tagged supported (actual_parsed_mass_guard raw known) view

namespace PositiveHydrogen

open PositiveHydrogenPublicPipelineRecoveryProofs.PositiveHydrogenPublicPipelineRecovery

/-- This real positive-H input is separately admitted on its actual expanded graph. -/
theorem actual_legacy_intake : LegacyAtomicIntake expanded 0 expandedCenterSpec .clockwise := by
  refine ⟨actual_materialized_center, actual_center_parity, ?_, ?_, ?_⟩
  · decide +kernel
  · rw [actual_written_hydrogen_first]; rfl
  · have perm := written_neighbors_perm_records expanded 0 actual_expanded_domain actual_written_exact
    exact (perm.map expanded.atomZAt).nodup_iff.mpr actual_expanded_domain.leaf.distinctRanks


theorem actual_legacy_positions :
    legacyPositions expanded (analysisFuel expanded) 0 (expanded.writtenNeighbors 0) = [3, 2, 1, 0] := by
  decide +kernel

theorem actual_legacy_R : parsedTetrahedralDescriptorAt? original 0 = some RS.R := by
  have known : expanded.rule2MassesKnown? = true := by decide +kernel
  simpa only [parsed_classifier_input, actual_positive_hydrogen_input, actual_legacy_positions] using
    actual_expanded_classifier expanded 0 expandedCenterSpec .clockwise actual_legacy_intake known

/-- The SAME physical-H parsed classifier and OWN expanded-source parser agree at every carrier.
The closed R is derived from real legacy written positions, not a requested output premise. -/
theorem actual_same_source_R (carrierFuel : Nat)
    (view : source.AromaticCanonicalDependencyView (source.aromaticCanonicalFinalOccurrence carrierFuel center)) :
    parsedTetrahedralDescriptorAt? original 0 = some RS.R ∧
      constitutionParserRichDescriptor? expanded source actual_annotation_agreement actual_written_exact
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view (2 * (carrierFuel + 1)) =
          some (.chiral RS.R) ∧
      ConstitutionParserRichDescriptorMeaning expanded source actual_annotation_agreement actual_written_exact
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view (2 * (carrierFuel + 1))
          (.chiral RS.R) := by
  obtain ⟨descriptor, computed, parserComputed, meaning⟩ :=
    actual_higher_source_alignment expanded source actual_annotation_agreement actual_written_exact
      carrierFuel center actual_expanded_domain actual_four_roots expandedCenterSpec actual_materialized_center
      .clockwise actual_center_parity (by decide +kernel) (by decide +kernel) view
  have known : expanded.rule2MassesKnown? = true := by decide +kernel
  have classifierR : expandedTetrahedralDescriptorAt? expanded 0 = some RS.R := by
    simpa only [actual_legacy_positions] using
      actual_expanded_classifier expanded 0 expandedCenterSpec .clockwise actual_legacy_intake known
  have equal := Option.some.inj (computed.symm.trans classifierR)
  subst descriptor
  exact ⟨actual_legacy_R, parserComputed, meaning⟩

end PositiveHydrogen

namespace ClosedCF

abbrev raw : RawMolecule := RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery.ClosedCF.raw

theorem actual_legacy_positions :
    legacyPositions (parsedInput raw) (analysisFuel (parsedInput raw)) 0
      ((parsedInput raw).writtenNeighbors 0) = [3, 2, 1, 0] := by
  decide +kernel

/-- The actual CF result follows from GENERAL original-domain classifier closure. -/
theorem actual_parsed_R : parsedTetrahedralDescriptorAt? raw 0 = some RS.R := by
  have computed := actual_parsed_classifier raw 0 actual_CF_intake (by decide +kernel)
    ({ AtomSpec.aliphatic .C with tetrahedral? := some .clockwise } : AtomSpec)
    (by decide +kernel) .clockwise rfl (by decide +kernel) (by decide +kernel)
  simpa only [actual_legacy_positions] using computed

end ClosedCF

end TetraStereo.UniversalProof.RuntimeLegacyClassifierClosureProofs.RuntimeLegacyClassifierClosure
