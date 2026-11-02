import TetraStereo.UniversalProof.NonleafSourceParserAlignmentProofs.NonleafSourceParserAlignment
import TetraStereo.UniversalProof.RuntimePositiveHydrogenDomainRecoveryProofs.RuntimePositiveHydrogenDomainRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NonleafPositiveHydrogenPipelineRecoveryProofs.NonleafPositiveHydrogenPipelineRecovery

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment
open TetraStereo.UniversalProof.RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery
open TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery
open TetraStereo.UniversalProof.RuntimeLegacyClassifierClosureProofs.RuntimeLegacyClassifierClosure
open TetraStereo.UniversalProof.RuntimePositiveHydrogenDomainRecoveryProofs.RuntimePositiveHydrogenDomainRecovery
open TetraStereo.UniversalProof.NonleafSourceParserAlignmentProofs.NonleafSourceParserAlignment
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge















structure PositiveAtomicIntake (raw : RawMolecule) (center : Nat) : Prop where
  domain : SourceAtomicDomain raw center
  unique : raw.BondRecordsUnique
  written : raw.WrittenNeighborExact
  demand : OneHydrogenDemand raw center
  three : (recordNeighbors raw center).length = 3
  heavy : ∀ atom ∈ recordNeighbors raw center, 1 < raw.atomZAt atom

theorem actual_original_atom (raw : RawMolecule) (center index : Nat)
    (intake : PositiveAtomicIntake raw center) (spec : AtomSpec)
    (observed : raw.atomAt? index = some spec) :
    raw.withExplicitHydrogens.atomAt? index = some (materializedAtomSpec spec) :=
  PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.withExplicitHydrogens_originalAtom raw
    intake.domain.atomic.wellFormed index spec observed

theorem actual_fresh_hydrogen (raw : RawMolecule) (center : Nat)
    (intake : PositiveAtomicIntake raw center) :
    raw.withExplicitHydrogens.atomAt? raw.atomCount = some (AtomSpec.aliphatic .H) :=
  PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.withExplicitHydrogens_boundary_hydrogen raw
    intake.domain.atomic.wellFormed ⟨center, intake.demand.centerBound, by rw [intake.demand.one]; omega⟩

theorem actual_original_rank (raw : RawMolecule) (center index : Nat)
    (intake : PositiveAtomicIntake raw center) (bound : index < raw.atomCount) :
    raw.withExplicitHydrogens.atomZAt index = raw.atomZAt index := by
  obtain ⟨spec, observed⟩ := listGet?_exists_of_lt raw.atoms index bound
  have looked : raw.atomAt? index = some spec := observed
  rw [atomZAt, actual_original_atom raw center index intake spec looked, atomZAt, looked]
  rfl

theorem actual_fresh_rank (raw : RawMolecule) (center : Nat)
    (intake : PositiveAtomicIntake raw center) :
    raw.withExplicitHydrogens.atomZAt raw.atomCount = 1 := by
  rw [atomZAt, actual_fresh_hydrogen raw center intake]
  rfl

/-- Genuine generated center row up to the splice's physical record order. -/
theorem actual_center_records (raw : RawMolecule) (center : Nat)
    (demand : OneHydrogenDemand raw center) :
    (recordNeighbors raw.withExplicitHydrogens center).Perm
      (recordNeighbors raw center ++ [raw.atomCount]) := by
  have projected := (actual_bond_permutation raw center demand).filterMap (recordNeighbor? center)
  simpa [recordNeighbors, List.filterMap_append, recordNeighbor?, generatedBond] using projected

private theorem original_fresh_row_empty (raw : RawMolecule) (well : raw.WellFormed) :
    recordNeighbors raw raw.atomCount = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro bond member
  have endpoints := well bond member
  change bond.source < raw.atomCount ∧ bond.target < raw.atomCount ∧ bond.source ≠ bond.target at endpoints
  have sourceDifferent : bond.source ≠ raw.atomCount := by omega
  have targetDifferent : bond.target ≠ raw.atomCount := by omega
  simp [recordNeighbor?, sourceDifferent, targetDifferent]

theorem actual_fresh_leaf_row (raw : RawMolecule) (center : Nat)
    (intake : PositiveAtomicIntake raw center) :
    recordNeighbors raw.withExplicitHydrogens raw.atomCount = [center] := by
  have different : center ≠ raw.atomCount := by have := intake.demand.centerBound; omega
  have projected := (actual_bond_permutation raw center intake.demand).filterMap
    (recordNeighbor? raw.atomCount)
  rw [List.filterMap_append] at projected
  change (recordNeighbors raw.withExplicitHydrogens raw.atomCount).Perm
    (recordNeighbors raw raw.atomCount ++ [generatedBond raw center].filterMap
      (recordNeighbor? raw.atomCount)) at projected
  rw [original_fresh_row_empty raw intake.domain.atomic.wellFormed] at projected
  have singleton : (recordNeighbors raw.withExplicitHydrogens raw.atomCount).Perm [center] := by
    simpa [recordNeighbor?, generatedBond, different] using projected
  exact singleton.eq_singleton

theorem actual_four (raw : RawMolecule) (center : Nat) (intake : PositiveAtomicIntake raw center) :
    (recordNeighbors raw.withExplicitHydrogens center).length = 4 := by
  rw [(actual_center_records raw center intake.demand).length_eq,
    List.length_append, intake.three]
  rfl

/-- Old ranks are unchanged and the newly generated hydrogen contributes exactly rank 1. -/
theorem actual_rank_permutation (raw : RawMolecule) (center : Nat)
    (intake : PositiveAtomicIntake raw center) :
    ((recordNeighbors raw.withExplicitHydrogens center).map raw.withExplicitHydrogens.atomZAt).Perm
      ((recordNeighbors raw center).map raw.atomZAt ++ [1]) := by
  have permutation := (actual_center_records raw center intake.demand).map raw.withExplicitHydrogens.atomZAt
  have mapped : (recordNeighbors raw center).map raw.withExplicitHydrogens.atomZAt =
      (recordNeighbors raw center).map raw.atomZAt := by
    apply List.map_congr_left
    intro atom member
    exact actual_original_rank raw center atom intake
      (recordNeighbor_bounds intake.domain.atomic.wellFormed member).1
  simpa only [List.map_append, List.map_cons, List.map_nil, mapped,
    actual_fresh_rank raw center intake] using permutation

theorem actual_distinct_ranks (raw : RawMolecule) (center : Nat)
    (intake : PositiveAtomicIntake raw center) :
    ((recordNeighbors raw.withExplicitHydrogens center).map raw.withExplicitHydrogens.atomZAt).Nodup := by
  apply (actual_rank_permutation raw center intake).nodup_iff.mpr
  apply List.nodup_append.mpr
  refine ⟨intake.domain.atomic.distinctRanks, by simp, ?_⟩
  intro rank member other singleton equal
  obtain ⟨atom, retained, rfl⟩ := List.mem_map.mp member
  have one : other = 1 := List.mem_singleton.mp singleton
  have higher := intake.heavy atom retained
  omega

private theorem record_incidence {center atom : Nat} {bond : RawBond}
    (observed : recordNeighbor? center bond = some atom) :
    bond.source = center ∨ bond.target = center := by
  unfold recordNeighbor? at observed
  split at observed
  · rename_i same; exact Or.inl (beq_iff_eq.mp same)
  · split at observed
    · rename_i same; exact Or.inr (beq_iff_eq.mp same)
    · contradiction

private theorem record_connects {center atom : Nat} {bond : RawBond}
    (observed : recordNeighbor? center bond = some atom) : bond.connects center atom = true := by
  unfold recordNeighbor? at observed
  split at observed
  · rename_i same
    have endpoint : bond.target = atom := Option.some.inj observed
    simp [RawBond.connects, beq_iff_eq.mp same, endpoint]
  · split at observed
    · rename_i same
      have endpoint : bond.source = atom := Option.some.inj observed
      simp [RawBond.connects, beq_iff_eq.mp same, endpoint]
    · contradiction

theorem actual_incident_kinds (raw : RawMolecule) (center : Nat)
    (intake : PositiveAtomicIntake raw center) (bond : RawBond)
    (member : bond ∈ raw.withExplicitHydrogens.bonds)
    (incident : bond.source = center ∨ bond.target = center) : bond.kind = .single := by
  have retained := (actual_bond_permutation raw center intake.demand).mem_iff.mp member
  rcases List.mem_append.mp retained with old | fresh
  · exact intake.domain.incidentKinds bond old incident
  · have equal : bond = generatedBond raw center := List.mem_singleton.mp fresh
    subst bond
    rfl

/-- Derived nonleaf output domain of the ACTUAL expansion; no supplied post-domain. -/
theorem actual_expanded_domain (raw : RawMolecule) (center : Nat)
    (intake : PositiveAtomicIntake raw center) : SourceAtomicDomain raw.withExplicitHydrogens center := by
  have admitted : raw.StereochemicalAdmissible :=
    ⟨⟨intake.domain.atomic.wellFormed, intake.unique⟩, intake.written⟩
  have output := withExplicitHydrogens_preserves_admissible raw admitted
  refine ⟨⟨output.1, ?_, ?_, actual_distinct_ranks raw center intake⟩,
    actual_incident_kinds raw center intake⟩
  · rw [actual_atom_count raw center intake.demand]
    have := intake.demand.centerBound
    omega
  · intro atom member
    obtain ⟨bond, retained, observed⟩ := List.mem_filterMap.mp member
    have kind := actual_incident_kinds raw center intake bond retained (record_incidence observed)
    rw [bondOrder_eq_kind_of_mem_connects raw.withExplicitHydrogens output.1 output.2 retained
      (record_connects observed), kind]
    rfl

theorem actual_written_exact (raw : RawMolecule) : raw.withExplicitHydrogens.WrittenNeighborExact :=
  withExplicitHydrogens_writtenNeighborExact raw

/-- REAL center written order: H is inserted using the original preceding-atom test. -/
theorem actual_written_center (raw : RawMolecule) (center : Nat)
    (intake : PositiveAtomicIntake raw center) :
    raw.withExplicitHydrogens.writtenNeighbors center =
      insertHydrogenInOrder (raw.writtenNeighbors center)
        (HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery.materializationHasPreceding raw center)
        [raw.atomCount] := by
  rw [HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery.withExplicitHydrogens_writtenNeighbors
    raw intake.domain.atomic.wellFormed intake.written center intake.demand.centerBound]
  have base : HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery.hydrogenExpansionBase raw center =
      raw.atomCount := by
    have before := actual_prefix raw center intake.demand center (by have := intake.demand.centerBound; omega)
    simp only [Nat.lt_irrefl, if_false] at before
    have length := HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery.expansionPrefix_atomListLength raw center
    rw [before] at length
    have initialLength : (initialHydrogenExpansionState raw).1.length = raw.atomCount := by
      simp only [initialHydrogenExpansionState, List.length_map, atomCount]
    rw [initialLength] at length
    have sumZero : ((List.range center).map raw.hydrogenCountAt).sum = 0 := by
      omega
    exact congrArg (raw.atomCount + ·) sumZero |>.trans (Nat.add_zero _)
  simp [HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery.materializedWrittenRow,
    HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery.materializedHydrogenIds, intake.demand.one, base]

/-- The new H carries no tetrahedral tag; only original annotated records can select discovery. -/
theorem actual_only_center_tagged (raw : RawMolecule) (center : Nat)
    (intake : PositiveAtomicIntake raw center) (only : OnlyCenterTagged raw center) :
    OnlyCenterTagged raw.withExplicitHydrogens center := by
  intro index spec observed tagged
  by_cases old : index.val < raw.atomCount
  · obtain ⟨original, looked⟩ := listGet?_exists_of_lt raw.atoms index.val old
    have originalAt : raw.atomAt? index.val = some original := looked
    have equal := Option.some.inj
      ((actual_original_atom raw center index.val intake original originalAt).symm.trans observed)
    subst spec
    exact only ⟨index.val, old⟩ original originalAt tagged
  · have last : index.val = raw.atomCount := by
      have upper := index.isLt
      have size := actual_atom_count raw center intake.demand
      omega
    have equal := Option.some.inj ((actual_fresh_hydrogen raw center intake).symm.trans (by simpa [last] using observed))
    subst spec
    cases tagged

/-- The ACTUAL expanded graph demands no further hydrogen. Fresh H starts with an implicit-count
record; its zero demand follows from its REAL incident valence one, not a fabricated inline field. -/
theorem actual_expanded_zero_demand (raw : RawMolecule) (center : Nat)
    (intake : PositiveAtomicIntake raw center) :
    ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.ZeroHydrogenDemand raw.withExplicitHydrogens := by
  intro index bound
  by_cases old : index < raw.atomCount
  · obtain ⟨spec, observed⟩ := listGet?_exists_of_lt raw.atoms index old
    have looked : raw.atomAt? index = some spec := observed
    unfold hydrogenCountAt
    rw [actual_original_atom raw center index intake spec looked]
    rfl
  · have last : index = raw.atomCount := by
      rw [actual_atom_count raw center intake.demand] at bound
      omega
    subst index
    have valence := (PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.withExplicitHydrogens_freshAtom raw
      intake.domain.atomic.wellFormed raw.atomCount (AtomSpec.aliphatic .H) (Nat.le_refl _)
      (actual_fresh_hydrogen raw center intake)).2
    unfold hydrogenCountAt
    rw [actual_fresh_hydrogen raw center intake]
    change (match (defaultValences (AtomSpec.aliphatic .H)).find?
        (fun v => raw.withExplicitHydrogens.incidentBondOrderSum raw.atomCount ≤ v) with
      | some v => v - raw.withExplicitHydrogens.incidentBondOrderSum raw.atomCount
      | none => 0) = 0
    rw [valence]
    rfl

/-- Bond normalization preserves the independent nonleaf original-record domain. -/
theorem normalized_source_domain (raw : RawMolecule) (center : Nat)
    (domain : SourceAtomicDomain raw center) : SourceAtomicDomain raw.normalizeUnspecifiedBonds center := by
  refine ⟨⟨normalizeUnspecifiedBonds_wellFormed raw domain.atomic.wellFormed,
    domain.atomic.centerBound, ?_, ?_⟩, ?_⟩
  · intro atom member
    rw [normalized_record_neighbors] at member
    rw [normalizeUnspecifiedBonds_bondOrder]
    exact domain.atomic.single atom member
  · simpa only [normalized_record_neighbors, normalized_atomic_number] using domain.atomic.distinctRanks
  · intro bond member incident
    obtain ⟨original, retained, rfl⟩ := List.mem_map.mp member
    have originalIncident : original.source = center ∨ original.target = center := by
      simpa only [normalizeUnspecifiedBond_source, normalizeUnspecifiedBond_target] using incident
    have kind := domain.incidentKinds original retained originalIncident
    simp only [normalizeUnspecifiedBond, kind]

theorem normalized_intake (raw : RawMolecule) (center : Nat)
    (intake : PositiveAtomicIntake raw center) : PositiveAtomicIntake raw.normalizeUnspecifiedBonds center := by
  refine ⟨normalized_source_domain raw center intake.domain,
    normalizeUnspecifiedBonds_bondRecordsUnique raw intake.unique,
    normalizeUnspecifiedBonds_writtenNeighborExact raw intake.written, ?_, ?_, ?_⟩
  · refine ⟨intake.demand.centerBound, ?_, ?_⟩
    · rw [normalized_hydrogen_demand]; exact intake.demand.one
    · intro index bound different
      rw [normalized_hydrogen_demand]
      exact intake.demand.other index bound different
  · rw [normalized_record_neighbors]; exact intake.three
  · intro atom member
    rw [normalized_atomic_number]
    exact intake.heavy atom (by simpa only [normalized_record_neighbors] using member)

theorem actual_parsed_domain (raw : RawMolecule) (center : Nat)
    (intake : PositiveAtomicIntake raw center) : SourceAtomicDomain (parsedInput raw) center :=
  actual_expanded_domain raw.normalizeUnspecifiedBonds center (normalized_intake raw center intake)

theorem actual_parsed_four (raw : RawMolecule) (center : Nat)
    (intake : PositiveAtomicIntake raw center) : (recordNeighbors (parsedInput raw) center).length = 4 :=
  actual_four raw.normalizeUnspecifiedBonds center (normalized_intake raw center intake)

theorem actual_parsed_zero_demand (raw : RawMolecule) (center : Nat)
    (intake : PositiveAtomicIntake raw center) :
    ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.ZeroHydrogenDemand (parsedInput raw) :=
  actual_expanded_zero_demand raw.normalizeUnspecifiedBonds center (normalized_intake raw center intake)

theorem actual_parsed_only_center_tagged (raw : RawMolecule) (center : Nat)
    (intake : PositiveAtomicIntake raw center) (only : OnlyCenterTagged raw center) :
    OnlyCenterTagged (parsedInput raw) center :=
  actual_only_center_tagged raw.normalizeUnspecifiedBonds center
    (normalized_intake raw center intake) only

/-- The ACTUAL normalized/materialized public occurrence API succeeds at a derived finite fuel,
including cyclic and nonleaf original branches. No expanded-domain/tree success is supplied. -/
theorem actual_parsed_public_occurrence (raw : RawMolecule) (center : Nat)
    (intake : PositiveAtomicIntake raw center) (only : OnlyCenterTagged raw center)
    (spec : AtomSpec) (observed : raw.atomAt? center = some spec)
    (parity : TetrahedralInputParity) (tagged : spec.tetrahedral? = some parity) (extraFuel : Nat) :
    ∃ positions, tetrahedralOccurrenceFact? (parsedInput raw)
      ((parsedInput raw).atomCount + 1 + extraFuel) center =
      some (recoveredPublicFact center positions
        (RawMolecule.descriptorOfParity parity (RawMolecule.permutationIsEven positions))) :=
  NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.actual_public_fact (parsedInput raw) center _
    (actual_parsed_domain raw center intake).atomic
    (withExplicitHydrogens_writtenNeighborExact raw.normalizeUnspecifiedBonds)
    (actual_parsed_four raw center intake) (actual_parsed_only_center_tagged raw center intake only)
    (materializedAtomSpec spec)
    (actual_positive_or_zero_atom_transport raw intake.domain.atomic.wellFormed center spec observed)
    parity tagged (by omega)

theorem actual_parsed_legacy_intake (raw : RawMolecule) (center : Nat)
    (intake : PositiveAtomicIntake raw center) (spec : AtomSpec)
    (observed : raw.atomAt? center = some spec) (parity : TetrahedralInputParity)
    (tagged : spec.tetrahedral? = some parity) (supported : centreElementSupported spec.element = true) :
    LegacyAtomicIntake (parsedInput raw) center (materializedAtomSpec spec) parity := by
  have domain := actual_parsed_domain raw center intake
  have written : (parsedInput raw).WrittenNeighborExact :=
    withExplicitHydrogens_writtenNeighborExact raw.normalizeUnspecifiedBonds
  have permutation := NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.actual_written_permutation
    (parsedInput raw) center domain.atomic written
  refine ⟨actual_positive_or_zero_atom_transport raw intake.domain.atomic.wellFormed center spec observed,
    tagged, supported, permutation.length_eq.trans (actual_parsed_four raw center intake), ?_⟩
  exact (permutation.map (parsedInput raw).atomZAt).nodup_iff.mpr domain.atomic.distinctRanks

/-- The REAL higher legacy classifier consumes its own internally derived expanded intake.
Distinct first-Z priority is sufficient; no physical leaf/cycle-free condition is required. -/
theorem actual_parsed_classifier (raw : RawMolecule) (center : Nat)
    (intake : PositiveAtomicIntake raw center) (spec : AtomSpec)
    (observed : raw.atomAt? center = some spec) (parity : TetrahedralInputParity)
    (tagged : spec.tetrahedral? = some parity) (supported : centreElementSupported spec.element = true)
    (known : raw.rule2MassesKnown? = true) :
    parsedTetrahedralDescriptorAt? raw center = some
      (descriptorOfParity parity (permutationIsEven
        (legacyPositions (parsedInput raw) (analysisFuel (parsedInput raw)) center
          ((parsedInput raw).writtenNeighbors center)))) := by
  rw [parsed_classifier_input]
  exact actual_expanded_classifier (parsedInput raw) center (materializedAtomSpec spec) parity
    (actual_parsed_legacy_intake raw center intake spec observed parity tagged supported)
    (actual_parsed_mass_guard raw known)

/-- Original positive-H preprocessing constructs the domain needed by the SAME actual parsed
source's independent formal meaning. Actual source admission and NoDouble remain explicit. -/
theorem actual_parsed_public_source_alignment (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (carrierFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (intake : PositiveAtomicIntake raw center.1.val)
    (agreement : RawAnnotationAgreement (parsedInput raw) source)
    (noDouble : source.NoAromaticCanonicalOrdinaryDoubleBond)
    (only : OnlyCenterTagged raw center.1.val)
    (spec : AtomSpec) (observed : raw.atomAt? center.1.val = some spec)
    (parity : TetrahedralInputParity) (tagged : spec.tetrahedral? = some parity)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence carrierFuel center)) (extraFuel : Nat) :
    ∃ positions descriptor,
      tetrahedralOccurrenceFact? (parsedInput raw) ((parsedInput raw).atomCount + 1 + extraFuel)
        center.1.val = some (recoveredPublicFact center.1.val positions descriptor) ∧
      constitutionParserRichDescriptor? (parsedInput raw) source agreement
        (withExplicitHydrogens_writtenNeighborExact raw.normalizeUnspecifiedBonds)
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view (2 * (carrierFuel + 1)) =
          some (.chiral descriptor) ∧
      ConstitutionParserRichDescriptorMeaning (parsedInput raw) source agreement
        (withExplicitHydrogens_writtenNeighborExact raw.normalizeUnspecifiedBonds)
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view (2 * (carrierFuel + 1))
          (.chiral descriptor) ∧
      descriptor = descriptorOfParity parity (permutationIsEven positions) :=
  NonleafSourceParserAlignmentProofs.NonleafSourceParserAlignment.actual_public_formal_alignment (parsedInput raw) source
    agreement (withExplicitHydrogens_writtenNeighborExact raw.normalizeUnspecifiedBonds)
    carrierFuel center (actual_parsed_domain raw center.1.val intake)
    (actual_parsed_four raw center.1.val intake) noDouble
    (actual_parsed_only_center_tagged raw center.1.val intake only) (materializedAtomSpec spec)
    (actual_positive_or_zero_atom_transport raw intake.domain.atomic.wellFormed center.1.val spec observed)
    parity tagged view _ (by omega)

/-- Intermediate actual-sort binding. It is used only after constructing that actual sort from
original graph records; no leaf/cycle-free assumption enters parity transport. -/
theorem actual_runtime_positions_legacy (raw : RawMolecule) (center : Nat)
    (domain : SourceAtomicDomain raw center) (written : raw.WrittenNeighborExact)
    (four : (recordNeighbors raw center).length = 4) (state : OccurrenceAuxState)
    (runtimeFuel legacyFuel : Nat) (result : List CanonicalRerootCursor × Nat)
    (computed : sortOccurrencesTrackedAuthoritative? raw state runtimeFuel
      (generatedRuntimeRoots raw center) = some result) :
    runtimePriorityPositions? raw center result.1 =
      some (legacyPositions raw legacyFuel center (raw.writtenNeighbors center)) := by
  obtain ⟨actual, actualComputed, permutation, strict, _⟩ :=
    NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.actual_generated_sort raw center domain.atomic state runtimeFuel
  have sameResult : result = actual := Option.some.inj (computed.symm.trans actualComputed)
  subst result
  have writtenPerm := NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.actual_written_permutation raw center domain.atomic written
  have writtenNodup := writtenPerm.nodup_iff.mpr domain.atomic.neighbors_nodup
  have distinct := (writtenPerm.map raw.atomZAt).nodup_iff.mpr domain.atomic.distinctRanks
  have runtimeIDsPerm : (actual.1.map (fun cursor => cursor.node.atom)).Perm (recordNeighbors raw center) := by
    have mapped := permutation.map (fun cursor => cursor.node.atom)
    rw [NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.generatedRuntimeRoots_eq raw center domain.atomic] at mapped
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
    raw center (writtenPerm.length_eq.trans four)
  unfold runtimePriorityPositions?
  rw [ligands]
  change actual.1.mapM ((writtenSlot? (raw.writtenNeighbors center)) ∘ (fun cursor => cursor.node.atom)) = _
  rw [← List.mapM_map, idsEqual]
  apply written_positions_roundtrip _ writtenNodup
  intro position member
  exact List.mem_range.mp ((legacy_positions_perm raw legacyFuel center _).mem_iff.mp member)


/-- PUBLIC occurrence construction after real positive-H preprocessing has exactly the actual
legacy classifier's computed positions and parity. This is not a surrogate descriptor consumer. -/
theorem actual_parsed_public_legacy_positions (raw : RawMolecule) (center : Nat)
    (intake : PositiveAtomicIntake raw center) (only : OnlyCenterTagged raw center)
    (spec : AtomSpec) (observed : raw.atomAt? center = some spec)
    (parity : TetrahedralInputParity) (tagged : spec.tetrahedral? = some parity) (extraFuel : Nat) :
    tetrahedralOccurrenceFact? (parsedInput raw) ((parsedInput raw).atomCount + 1 + extraFuel) center =
      some (recoveredPublicFact center
        (legacyPositions (parsedInput raw) (analysisFuel (parsedInput raw)) center
          ((parsedInput raw).writtenNeighbors center))
        (descriptorOfParity parity (permutationIsEven
          (legacyPositions (parsedInput raw) (analysisFuel (parsedInput raw)) center
            ((parsedInput raw).writtenNeighbors center))))) := by
  let parsed := parsedInput raw
  let fuel := parsed.atomCount + 1 + extraFuel
  have domain := actual_parsed_domain raw center intake
  have written := withExplicitHydrogens_writtenNeighborExact raw.normalizeUnspecifiedBonds
  have four := actual_parsed_four raw center intake
  obtain ⟨result, computed, permutation, sorted, _⟩ :=
    NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.actual_generated_sort parsed center domain.atomic [] fuel
  have positionsComputed := actual_runtime_positions_legacy parsed center domain written four [] fuel
    (analysisFuel parsed) result computed
  obtain ⟨decisions, decisionsComputed, strict, pseudo, _⟩ :=
    NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.actual_observed_adjacent parsed [] fuel result.1
      (fun cursor member => NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.actual_root_observed
        parsed center domain.atomic cursor (permutation.mem_iff.mp member)) sorted
  have localComputed := RuntimeOccurrenceFactRecoveryProofs.RuntimeOccurrenceFactRecovery.actual_fact_of_program_bindings
    parsed center fuel [] (materializedAtomSpec spec) parity
    (actual_positive_or_zero_atom_transport raw intake.domain.atomic.wellFormed center spec observed)
    tagged result _ decisions _
    (NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.actual_four_frame parsed center domain.atomic written four)
    computed positionsComputed decisionsComputed strict pseudo rfl
    (NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.actual_root_observed parsed center domain.atomic)
    (NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery.actual_root_distinct_ranks parsed center domain.atomic)
  exact public_fact_of_actual_local_fact parsed fuel center
    (actual_parsed_only_center_tagged raw center intake only)
    (FiniteCanonicalCollectorRecoveryProofs.FiniteCanonicalCollectorRecovery.prefixTree parsed center 0 fuel)
    (FiniteCanonicalCollectorRecoveryProofs.FiniteCanonicalCollectorRecovery.actual_collector_complete parsed center fuel
      domain.atomic.wellFormed domain.atomic.centerBound (by dsimp [fuel]; omega)) _ _ localComputed

namespace CyclicPositive

def centerSpec : AtomSpec :=
  { AtomSpec.aliphatic .C with explicitHydrogens? := some 1, tetrahedral? := some .clockwise }

def raw : RawMolecule :=
  { atoms := [centerSpec,
      { AtomSpec.aliphatic .C with explicitHydrogens? := some 0 },
      { AtomSpec.aliphatic .C with explicitHydrogens? := some 0 },
      { AtomSpec.aliphatic .C with explicitHydrogens? := some 0 },
      { AtomSpec.aliphatic .F with explicitHydrogens? := some 0 },
      { AtomSpec.aliphatic .Br with explicitHydrogens? := some 0 }]
    bonds := [⟨0, 1, .single⟩, ⟨0, 4, .single⟩, ⟨0, 5, .single⟩,
      ⟨1, 2, .single⟩, ⟨2, 3, .single⟩, ⟨3, 1, .single⟩]
    neighborOrder := [[1, 4, 5], [0, 2, 3], [1, 3], [2, 1], [0], [0]] }

theorem actual_admissible : raw.StereochemicalAdmissible := by
  apply (stereochemicalAdmissible?_eq_true_iff raw).mp
  decide +kernel

theorem actual_original_domain : SourceAtomicDomain raw 0 := by
  refine ⟨⟨actual_admissible.1.1, by decide +kernel, ?_, by decide +kernel⟩, ?_⟩
  · intro atom member
    change atom ∈ [1, 4, 5] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide +kernel
  · intro bond member _
    change bond ∈ [⟨0, 1, .single⟩, ⟨0, 4, .single⟩, ⟨0, 5, .single⟩,
      ⟨1, 2, .single⟩, ⟨2, 3, .single⟩, ⟨3, 1, .single⟩] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem actual_intake : PositiveAtomicIntake raw 0 := by
  refine ⟨actual_original_domain, actual_admissible.1.2, actual_admissible.2,
    ⟨by decide +kernel, by decide +kernel, ?_⟩, by decide +kernel, ?_⟩
  · intro index bound different
    change index < 6 at bound
    interval_cases index
    · contradiction
    all_goals decide +kernel
  · intro atom member
    change atom ∈ [1, 4, 5] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide +kernel

theorem actual_only_center : OnlyCenterTagged raw 0 := by
  intro index spec observed tagged
  change Fin 6 at index
  fin_cases index <;> simp [raw, atomAt?, listGet?] at observed
  all_goals subst spec
  all_goals simp_all [AtomSpec.aliphatic, centerSpec]

theorem actual_cycle_nonleaf : raw.atomLiesInCycle 5 1 = true ∧
    (raw.incidentAtoms 1).length = 3 := by decide +kernel

theorem actual_one_fresh_H : raw.withExplicitHydrogens.atomCount = 7 ∧
    raw.withExplicitHydrogens.atomAt? 6 = some (AtomSpec.aliphatic .H) :=
  ⟨actual_atom_count raw 0 actual_intake.demand, actual_fresh_hydrogen raw 0 actual_intake⟩

theorem actual_written_H_first : raw.withExplicitHydrogens.writtenNeighbors 0 = [6, 1, 4, 5] := by
  rw [actual_written_center raw 0 actual_intake]
  rfl

theorem actual_expanded_nonleaf_domain : SourceAtomicDomain raw.withExplicitHydrogens 0 ∧
    (recordNeighbors raw.withExplicitHydrogens 0).length = 4 ∧
    raw.withExplicitHydrogens.atomLiesInCycle 5 1 = true ∧
    (raw.withExplicitHydrogens.incidentAtoms 1).length = 3 :=
  ⟨actual_expanded_domain raw 0 actual_intake, actual_four raw 0 actual_intake,
    by decide +kernel, by decide +kernel⟩

theorem actual_parsed_written_H_first : (parsedInput raw).writtenNeighbors 0 = [6, 1, 4, 5] := by
  have normalized : raw.normalizeUnspecifiedBonds = raw := by decide +kernel
  change raw.normalizeUnspecifiedBonds.withExplicitHydrogens.writtenNeighbors 0 = _
  rw [normalized]
  exact actual_written_H_first

theorem actual_legacy_positions : legacyPositions (parsedInput raw) (analysisFuel (parsedInput raw))
    0 ((parsedInput raw).writtenNeighbors 0) = [3, 2, 1, 0] := by decide +kernel

/-- The actual positive-H original cyclic input reaches the REAL higher classifier R. -/
theorem actual_higher_R : parsedTetrahedralDescriptorAt? raw 0 = some .R := by
  have computed := actual_parsed_classifier raw 0 actual_intake centerSpec rfl .clockwise rfl
    (by decide +kernel) (by decide +kernel)
  simpa only [actual_legacy_positions] using computed

/-- The actual public occurrence API also emits R with the actual H-first written positions. -/
theorem actual_public_R (extraFuel : Nat) :
    tetrahedralOccurrenceFact? (parsedInput raw) ((parsedInput raw).atomCount + 1 + extraFuel) 0 =
      some (recoveredPublicFact 0 [3, 2, 1, 0] .R) := by
  have computed := actual_parsed_public_legacy_positions raw 0 actual_intake actual_only_center
    centerSpec rfl .clockwise rfl extraFuel
  simpa only [actual_legacy_positions] using computed

end CyclicPositive

end TetraStereo.UniversalProof.NonleafPositiveHydrogenPipelineRecoveryProofs.NonleafPositiveHydrogenPipelineRecovery
