import TetraStereo.UniversalProof.NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment
import TetraStereo.UniversalProof.NextFrontier.FramedAtomicDispatch

set_option autoImplicit false

namespace TetraStereo.UniversalProof.RuntimeOccurrenceFactRecoveryProofs.RuntimeOccurrenceFactRecovery

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.RuntimeSourceRootAlignmentProofs.RuntimeSourceRootAlignment
open TetraStereo.UniversalProof.NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge













/-- Strict actual generated neighbors have an actual composed runtime gt decision, with no pseudo
history. The cycle condition is derived from the physical leaf graph domain. -/
theorem actual_generated_strict_decision (raw : RawMolecule) (center : Nat)
    (domain : LeafNeighborDomain raw center) (state : OccurrenceAuxState) (fuel : Nat)
    (left right : CanonicalRerootCursor)
    (leftMember : left ∈ generatedRuntimeRoots raw center)
    (rightMember : right ∈ generatedRuntimeRoots raw center)
    (higher : AtomicDesc raw left right) :
    compareOccurrenceBranchesComplete? raw state fuel left right =
      some { ordering := Ordering.gt, pseudo := false } := by
  have leftDomain := generated_root_realOutsideCycle raw center fuel domain left leftMember
  have rightDomain := generated_root_realOutsideCycle raw center fuel domain right rightMember
  have different : raw.atomZAt left.node.atom ≠ raw.atomZAt right.node.atom := by
    intro equal
    exact (Nat.ne_of_lt higher) equal.symm
  have computed := compareOccurrenceBranchesComplete?_eq_of_rule1a raw state fuel left right
    leftDomain.1 rightDomain.1 different (Or.inl leftDomain.2.2)
  simpa only [Nat.compare_eq_gt.mpr higher] using computed

/-- The actual recursive adjacent checker succeeds on every strictly ordered list of actual
returned roots. Both the no-tie refusal check and pseudo filter are derived from its decisions. -/
theorem actual_adjacent_decisions (raw : RawMolecule) (center : Nat)
    (domain : LeafNeighborDomain raw center) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) :
    (∀ cursor ∈ roots, cursor ∈ generatedRuntimeRoots raw center) →
    roots.Pairwise (AtomicDesc raw) →
    ∃ decisions,
      compareOccurrenceAdjacentPairsAuthoritative? raw state fuel roots = some decisions ∧
      decisions.all (fun decision => decision.ordering != Ordering.eq) = true ∧
      decisions.filter (fun decision => decision.pseudo) = [] ∧
      decisions.length = roots.length - 1 := by
  induction roots with
  | nil => intro _ _; exact ⟨[], rfl, rfl, rfl, rfl⟩
  | cons left remaining inductionHypothesis =>
      intro members sorted
      cases remaining with
      | nil => exact ⟨[], rfl, rfl, rfl, rfl⟩
      | cons right tail =>
          have rightMembers : ∀ cursor ∈ right :: tail, cursor ∈ generatedRuntimeRoots raw center := by
            intro cursor member
            exact members cursor (List.mem_cons.mpr (Or.inr member))
          have rightSorted := (List.pairwise_cons.mp sorted).2
          obtain ⟨decisions, computed, strict, pseudo, length⟩ :=
            inductionHypothesis rightMembers rightSorted
          have higher := (List.pairwise_cons.mp sorted).1 right List.mem_cons_self
          have comparison := actual_generated_strict_decision raw center domain state fuel left right
            (members left List.mem_cons_self) (rightMembers right List.mem_cons_self) higher
          refine ⟨{ ordering := Ordering.gt, pseudo := false } :: decisions, ?_, ?_, ?_, ?_⟩
          · simp [compareOccurrenceAdjacentPairsAuthoritative?, comparison, computed]
          · simpa using strict
          · simpa using pseudo
          · simpa only [List.length_cons, Nat.add_sub_cancel] using congrArg Nat.succ length

/-- The ACTUAL runtime sorter supplies the membership and strictness used above. The computed
result is only an intermediate binding; its sort/order properties are independently recovered. -/
theorem actual_sorted_adjacent_decisions (raw : RawMolecule) (center : Nat)
    (domain : LeafNeighborDomain raw center) (state : OccurrenceAuxState) (fuel : Nat)
    (result : List CanonicalRerootCursor × Nat)
    (computed : sortOccurrencesTrackedAuthoritative? raw state fuel
      (generatedRuntimeRoots raw center) = some result) :
    ∃ decisions,
      compareOccurrenceAdjacentPairsAuthoritative? raw state fuel result.1 = some decisions ∧
      decisions.all (fun decision => decision.ordering != Ordering.eq) = true ∧
      decisions.filter (fun decision => decision.pseudo) = [] ∧
      decisions.length = result.1.length - 1 := by
  obtain ⟨actual, observed, permutation, sorted, _⟩ :=
    generated_runtime_sort raw center fuel domain state
  have equal : actual = result := Option.some.inj (observed.symm.trans computed)
  subst actual
  exact actual_adjacent_decisions raw center domain state fuel result.1
    (fun cursor member => permutation.mem_iff.mp member) sorted

/-- Exact fields of a local runtime fact after genuine source position/parity recovery. -/
def recoveredFact (center : Nat) (positions : List Nat) (descriptor : RS) : OccurrenceAuxFact where
  key := canonicalOccurrenceKey (canonicalCenterRoot center)
  atom := center
  descriptor := descriptor
  uppercase := true
  priorityPositions := positions

theorem recoveredFact_key (center : Nat) (positions : List Nat) (descriptor : RS) :
    (recoveredFact center positions descriptor).key = canonicalOccurrenceKey (canonicalCenterRoot center) := rfl

theorem recoveredFact_atom (center : Nat) (positions : List Nat) (descriptor : RS) :
    (recoveredFact center positions descriptor).atom = center := rfl

theorem recoveredFact_uppercase (center : Nat) (positions : List Nat) (descriptor : RS) :
    (recoveredFact center positions descriptor).uppercase = true := rfl

/-- Historical backend binding, preserving the original primitive premises and fact formula.
The public dispatch helper below adds independently derived atomic-frame evidence. -/
theorem legacy_actual_fact_of_program_bindings (raw : RawMolecule) (center fuel : Nat)
    (state : OccurrenceAuxState) (spec : AtomSpec) (parity : TetrahedralInputParity)
    (atomObserved : raw.atomAt? center = some spec)
    (parityObserved : spec.tetrahedral? = some parity)
    (result : List CanonicalRerootCursor × Nat) (positions : List Nat) (decisions : List OccurrenceComparison)
    (descriptor : RS)
    (frameComputed : occurrenceLigandFrame? raw (canonicalCenterRoot center) =
      some (generatedRuntimeRoots raw center))
    (sortComputed : sortOccurrencesTrackedAuthoritative? raw state fuel
      (generatedRuntimeRoots raw center) = some result)
    (positionsComputed : runtimePriorityPositions? raw center result.1 = some positions)
    (decisionsComputed : compareOccurrenceAdjacentPairsAuthoritative? raw state fuel result.1 = some decisions)
    (strict : decisions.all (fun decision => decision.ordering != Ordering.eq) = true)
    (pseudo : decisions.filter (fun decision => decision.pseudo) = [])
    (descriptorFormula : descriptor = RawMolecule.descriptorOfParity parity
      (RawMolecule.permutationIsEven positions)) :
    legacyOccurrenceFactAuthoritative? raw fuel state (canonicalCenterRoot center) =
      some (recoveredFact center positions descriptor) := by
  unfold legacyOccurrenceFactAuthoritative?
  change (do
    let actualSpec ← raw.atomAt? center
    let actualParity ← actualSpec.tetrahedral?
    let roots ← occurrenceLigandFrame? raw (canonicalCenterRoot center)
    let sorted ← sortOccurrencesTrackedAuthoritative? raw state fuel roots
    let actualPositions ← runtimePriorityPositions? raw center sorted.1
    let actualDecisions ← compareOccurrenceAdjacentPairsAuthoritative? raw state fuel sorted.1
    if !(actualDecisions.all fun decision => decision.ordering != Ordering.eq) then none else
      let pseudoPairCount := (actualDecisions.filter fun decision => decision.pseudo).length
      some {
        key := canonicalOccurrenceKey (canonicalCenterRoot center)
        atom := center
        descriptor := RawMolecule.descriptorOfParity actualParity
          (RawMolecule.permutationIsEven actualPositions)
        uppercase := pseudoPairCount % 2 == 0
        priorityPositions := actualPositions }) = some (recoveredFact center positions descriptor)
  simp [atomObserved, parityObserved, frameComputed, sortComputed, positionsComputed,
    decisionsComputed, pseudo, descriptorFormula, recoveredFact]
  simpa using strict

/-- Public dispatch-aware atomic-frame binding helper. Unlike its historical counterpart,
this requires independent real observations and distinct first-Z ranks of the actual generated
frame. The final graph-domain theorems derive these two inputs. -/
theorem actual_fact_of_program_bindings (raw : RawMolecule) (center fuel : Nat)
    (state : OccurrenceAuxState) (spec : AtomSpec) (parity : TetrahedralInputParity)
    (atomObserved : raw.atomAt? center = some spec)
    (parityObserved : spec.tetrahedral? = some parity)
    (result : List CanonicalRerootCursor × Nat) (positions : List Nat) (decisions : List OccurrenceComparison)
    (descriptor : RS)
    (frameComputed : occurrenceLigandFrame? raw (canonicalCenterRoot center) =
      some (generatedRuntimeRoots raw center))
    (sortComputed : sortOccurrencesTrackedAuthoritative? raw state fuel
      (generatedRuntimeRoots raw center) = some result)
    (positionsComputed : runtimePriorityPositions? raw center result.1 = some positions)
    (decisionsComputed : compareOccurrenceAdjacentPairsAuthoritative? raw state fuel result.1 = some decisions)
    (strict : decisions.all (fun decision => decision.ordering != Ordering.eq) = true)
    (pseudo : decisions.filter (fun decision => decision.pseudo) = [])
    (descriptorFormula : descriptor = RawMolecule.descriptorOfParity parity
      (RawMolecule.permutationIsEven positions))
    (observed : ∀ cursor ∈ generatedRuntimeRoots raw center,
      NonleafAtomicRuntimeComparisonRecoveryProofs.NonleafAtomicRuntimeComparisonRecovery.ObservedReal raw cursor)
    (distinct : ((generatedRuntimeRoots raw center).map
      (fun cursor => raw.atomZAt cursor.node.atom)).Nodup) :
    occurrenceFactAuthoritative? raw fuel state (canonicalCenterRoot center) =
      some (recoveredFact center positions descriptor) := by
  rw [FramedAtomicDispatch.authoritative_fact_eq_legacy raw center fuel state
    (canonicalCenterRoot center) .root (generatedRuntimeRoots raw center) rfl
    frameComputed observed distinct]
  exact legacy_actual_fact_of_program_bindings raw center fuel state spec parity atomObserved
    parityObserved result positions decisions descriptor frameComputed sortComputed positionsComputed
    decisionsComputed strict pseudo descriptorFormula

private theorem leaf_roots_observed (raw : RawMolecule) (center : Nat)
    (domain : LeafNeighborDomain raw center) :
    ∀ cursor ∈ generatedRuntimeRoots raw center,
      NonleafAtomicRuntimeComparisonRecoveryProofs.NonleafAtomicRuntimeComparisonRecovery.ObservedReal raw cursor := by
  intro cursor member
  have meaning := generated_root_meaning raw center domain cursor member
  have provenance := (generated_root_realOutsideCycle raw center 0 domain cursor member).1
  obtain ⟨spec, lookup, _⟩ := meaning.2.2.2
  exact ⟨provenance, spec, lookup⟩

private theorem leaf_roots_distinct (raw : RawMolecule) (center : Nat)
    (domain : LeafNeighborDomain raw center) :
    ((generatedRuntimeRoots raw center).map (fun cursor => raw.atomZAt cursor.node.atom)).Nodup := by
  rw [List.nodup_map_iff_inj_on (generated_roots_nodup raw center domain)]
  intro left leftMember right rightMember equal
  exact generated_roots_rank_injective raw center domain left right leftMember rightMember equal

/-- An actual generated root has a genuine unique written-neighbor position. -/
theorem generated_written_slot_exists (raw : RawMolecule) (center : Nat)
    (domain : SingleLeafDomain raw center) (written : raw.WrittenNeighborExact)
    (cursor : CanonicalRerootCursor) (member : cursor ∈ generatedRuntimeRoots raw center) :
    ∃ position, writtenSlot? (raw.writtenNeighbors center) cursor.node.atom = some position := by
  have permutation := written_neighbors_perm_records raw center domain written
  have distinct := permutation.nodup_iff.mpr domain.leaf.neighbors_nodup
  rw [generatedRuntimeRoots_eq raw center domain.leaf] at member
  obtain ⟨atom, inRecords, rfl⟩ := List.mem_map.mp member
  have inWritten := permutation.mem_iff.mpr inRecords
  obtain ⟨position, observed⟩ := List.mem_iff_getElem?.mp inWritten
  exact ⟨position, writtenSlot?_eq_some _ distinct position atom observed⟩

/-- Runtime lookup is total on actual generated roots from independent written-frame exactness.
No source/formal-sort result is needed for this runtime-only law. -/
theorem actual_runtime_positions_exists (raw : RawMolecule) (center : Nat)
    (domain : SingleLeafDomain raw center) (written : raw.WrittenNeighborExact)
    (four : (recordNeighbors raw center).length = 4) (roots : List CanonicalRerootCursor) :
    (∀ cursor ∈ roots, cursor ∈ generatedRuntimeRoots raw center) →
    ∃ positions, runtimePriorityPositions? raw center roots = some positions := by
  have writtenFour := actual_written_four raw center domain written four
  have ligands := AuthoritativeCIPRule6Scheduler.ligandsWithLonePair_eq_writtenNeighbors_of_length_four
    raw center writtenFour
  unfold runtimePriorityPositions?
  rw [ligands]
  change (∀ cursor ∈ roots, cursor ∈ generatedRuntimeRoots raw center) →
    ∃ positions, roots.mapM (fun cursor => writtenSlot? (raw.writtenNeighbors center) cursor.node.atom) = some positions
  induction roots with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons cursor tail inductionHypothesis =>
      intro members
      obtain ⟨position, observed⟩ := generated_written_slot_exists raw center domain written cursor
        (members cursor List.mem_cons_self)
      obtain ⟨positions, tailComputed⟩ := inductionHypothesis
        (fun other member => members other (List.mem_cons.mpr (Or.inr member)))
      exact ⟨position :: positions, by simp [List.mapM_cons, observed, tailComputed]⟩

/-- A GENERAL runtime-only local fact exists directly from the graph, actual tag and written frame.
It needs no formal source, NoDouble backend premise, supplied sort success or supplied positions. -/
theorem actual_runtime_fact_exists (raw : RawMolecule) (center : Nat)
    (domain : SingleLeafDomain raw center) (written : raw.WrittenNeighborExact)
    (four : (recordNeighbors raw center).length = 4)
    (spec : AtomSpec) (atomObserved : raw.atomAt? center = some spec)
    (parity : TetrahedralInputParity) (parityObserved : spec.tetrahedral? = some parity)
    (state : OccurrenceAuxState) (fuel : Nat) :
    ∃ positions,
      occurrenceFactAuthoritative? raw fuel state (canonicalCenterRoot center) =
        some (recoveredFact center positions (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven positions))) := by
  obtain ⟨result, computed, permutation, _, _⟩ :=
    generated_runtime_sort raw center fuel domain.leaf state
  obtain ⟨positions, positionsComputed⟩ := actual_runtime_positions_exists raw center domain written four result.1
    (fun cursor member => permutation.mem_iff.mp member)
  obtain ⟨decisions, decisionsComputed, strict, pseudo, _⟩ :=
    actual_sorted_adjacent_decisions raw center domain.leaf state fuel result computed
  exact ⟨positions, actual_fact_of_program_bindings raw center fuel state spec parity atomObserved
    parityObserved result positions decisions _ (actual_runtime_frame raw center domain written four)
    computed positionsComputed decisionsComputed strict pseudo rfl
    (leaf_roots_observed raw center domain.leaf) (leaf_roots_distinct raw center domain.leaf)⟩

/-- GENERAL local runtime fact / SAME-source parser descriptor agreement. Input parity comes from
the actual raw atom record. Every frame, sort, lookup and no-tie/pseudo refusal result is derived. -/
theorem actual_runtime_fact_formal_alignment (raw : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : RawAnnotationAgreement raw source)
    (written : raw.WrittenNeighborExact) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (domain : SingleLeafDomain raw center.1.val)
    (four : (recordNeighbors raw center.1.val).length = 4)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    (spec : AtomSpec) (atomObserved : raw.atomAt? center.1.val = some spec)
    (parity : TetrahedralInputParity) (parityObserved : spec.tetrahedral? = some parity)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center))
    (state : OccurrenceAuxState) (runtimeFuel : Nat) :
    ∃ positions descriptor,
      occurrenceFactAuthoritative? raw runtimeFuel state (canonicalCenterRoot center.1.val) =
        some (recoveredFact center.1.val positions descriptor) ∧
      constitutionParserRichDescriptor? raw source agreement written
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
        (2 * (carrierFuel + 1)) = some (.chiral descriptor) ∧
      ConstitutionParserRichDescriptorMeaning raw source agreement written
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view
        (2 * (carrierFuel + 1)) (.chiral descriptor) ∧
      descriptor = RawMolecule.descriptorOfParity parity (RawMolecule.permutationIsEven positions) := by
  obtain ⟨result, positions, descriptor, frameComputed, sortComputed, positionsComputed,
    descriptorFormula, parserComputed, parserMeaning, _⟩ :=
    actual_runtime_formal_descriptor_transport raw source agreement written carrierFuel center
      domain four noDouble spec atomObserved parity parityObserved view state runtimeFuel
  obtain ⟨decisions, decisionsComputed, strict, pseudo, _⟩ :=
    actual_sorted_adjacent_decisions raw center.1.val domain.leaf state runtimeFuel result sortComputed
  refine ⟨positions, descriptor, ?_, parserComputed, parserMeaning, descriptorFormula⟩
  exact actual_fact_of_program_bindings raw center.1.val runtimeFuel state spec parity atomObserved
    parityObserved result positions decisions descriptor frameComputed sortComputed positionsComputed
    decisionsComputed strict pseudo descriptorFormula
    (leaf_roots_observed raw center.1.val domain.leaf)
    (leaf_roots_distinct raw center.1.val domain.leaf)

namespace ClosedCF

abbrev raw : RawMolecule := NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.ClosedCF.raw
abbrev source : AuthoritativeChemicalInput := NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.ClosedCF.source
abbrev center : source.AromaticCanonicalTetrahedralCenter := NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.ClosedCF.center

/-- A genuine closed local runtime fact and actual source parser emission, for ANY view/state/fuel.
No full discovery/public-wrapper claim is made by this local fact. -/
theorem actual_runtime_fact_alignment
    (view : source.AromaticCanonicalDependencyView (source.aromaticCanonicalFinalOccurrence 0 center))
    (state : OccurrenceAuxState) (runtimeFuel : Nat) :
    ∃ positions descriptor,
      occurrenceFactAuthoritative? raw runtimeFuel state (canonicalCenterRoot center.1.val) =
        some (recoveredFact center.1.val positions descriptor) ∧
      constitutionParserRichDescriptor? raw source
        NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.ClosedCF.actual_annotation_agreement
        NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.ClosedCF.actual_written_exact
        (source.aromaticCanonicalFinalOccurrence 0 center) view 2 = some (.chiral descriptor) ∧
      ConstitutionParserRichDescriptorMeaning raw source
        NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.ClosedCF.actual_annotation_agreement
        NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.ClosedCF.actual_written_exact
        (source.aromaticCanonicalFinalOccurrence 0 center) view 2 (.chiral descriptor) ∧
      descriptor = RawMolecule.descriptorOfParity TetrahedralInputParity.clockwise
        (RawMolecule.permutationIsEven positions) :=
  actual_runtime_fact_formal_alignment raw source
    NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.ClosedCF.actual_annotation_agreement
    NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.ClosedCF.actual_written_exact 0 center
    RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment.ClosedCF.actual_domain
    RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment.ClosedCF.actual_four
    RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment.ClosedCF.actual_noDouble
    { AtomSpec.aliphatic .C with tetrahedral? := some TetrahedralInputParity.clockwise }
    NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.ClosedCF.actual_input_parity
    TetrahedralInputParity.clockwise (by rfl) view state runtimeFuel

end ClosedCF

end TetraStereo.UniversalProof.RuntimeOccurrenceFactRecoveryProofs.RuntimeOccurrenceFactRecovery
