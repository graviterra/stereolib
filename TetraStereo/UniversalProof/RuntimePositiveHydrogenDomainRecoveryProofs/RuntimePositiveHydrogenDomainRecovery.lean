import TetraStereo.UniversalProof.RuntimeLegacyClassifierClosureProofs.RuntimeLegacyClassifierClosure
import TetraStereo.UniversalProof.ReviewedPositiveHydrogenAtomTransportClosureProofs.ReviewedPositiveHydrogenAtomTransportClosure
import TetraStereo.UniversalProof.ReviewedPositiveHydrogenBondTransportClosureProofs.ReviewedPositiveHydrogenBondTransportClosure

set_option autoImplicit false

namespace TetraStereo.UniversalProof.RuntimePositiveHydrogenDomainRecoveryProofs.RuntimePositiveHydrogenDomainRecovery

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.RuntimeSourceRootAlignmentProofs.RuntimeSourceRootAlignment
open TetraStereo.UniversalProof.RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery
open TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery
open TetraStereo.UniversalProof.RuntimeLegacyClassifierClosureProofs.RuntimeLegacyClassifierClosure
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
















/-- Original-record demand, with no expansion equation as a premise. -/
structure OneHydrogenDemand (raw : RawMolecule) (center : Nat) : Prop where
  centerBound : center < raw.atomCount
  one : raw.hydrogenCountAt center = 1
  other : ∀ index, index < raw.atomCount → index ≠ center → raw.hydrogenCountAt index = 0

/-- Three original physical leaves; the fresh ordinary H has a distinct atomic rank. -/
structure PositiveLeafIntake (raw : RawMolecule) (center : Nat) : Prop where
  domain : SingleLeafDomain raw center
  unique : raw.BondRecordsUnique
  written : raw.WrittenNeighborExact
  demand : OneHydrogenDemand raw center
  three : (recordNeighbors raw center).length = 3
  heavy : ∀ atom ∈ recordNeighbors raw center, 1 < raw.atomZAt atom

def generatedBond (raw : RawMolecule) (center : Nat) : RawBond :=
  { source := center, target := raw.atomCount, kind := .single }

/-- Actual range-prefix accumulator, before or after the unique demanding original index. -/
theorem actual_prefix (raw : RawMolecule) (center : Nat) (demand : OneHydrogenDemand raw center)
    (n : Nat) (bound : n ≤ raw.atomCount) :
    HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery.expansionPrefix raw n =
      if center < n then withExplicitHydrogensStep raw (initialHydrogenExpansionState raw) center
      else initialHydrogenExpansionState raw := by
  induction n with
  | zero => simp [HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery.expansionPrefix]
  | succ n inductionHypothesis =>
      have previous := inductionHypothesis (by omega)
      rw [HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery.expansionPrefix_succ, previous]
      by_cases atCenter : n = center
      · subst n
        simp only [Nat.lt_irrefl, if_false, Nat.lt_succ_self, if_true]
      · have zero := demand.other n (by omega) atCenter
        rw [ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.zero_demand_step_identity raw _ n zero]
        have same : (center < n + 1) ↔ center < n := by omega
        simp only [same]

/-- The full ACTUAL accumulator is one production step, regardless of the center's original index. -/
theorem actual_fold (raw : RawMolecule) (center : Nat) (demand : OneHydrogenDemand raw center) :
    ReviewedPositiveHydrogenBondTransportClosureProofs.ReviewedPositiveHydrogenBondTransportClosure.expansionResult raw =
      withExplicitHydrogensStep raw (initialHydrogenExpansionState raw) center := by
  have computed := actual_prefix raw center demand raw.atomCount (Nat.le_refl _)
  simpa only [demand.centerBound, if_true,
    HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery.expansionPrefix,
    ReviewedPositiveHydrogenBondTransportClosureProofs.ReviewedPositiveHydrogenBondTransportClosure.expansionResult] using computed

theorem actual_atom_count (raw : RawMolecule) (center : Nat) (demand : OneHydrogenDemand raw center) :
    raw.withExplicitHydrogens.atomCount = raw.atomCount + 1 := by
  rw [PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.withExplicitHydrogens_atomCount_eq_fold]
  change (ReviewedPositiveHydrogenBondTransportClosureProofs.ReviewedPositiveHydrogenBondTransportClosure.expansionResult raw).toRawMolecule.atomCount =
    raw.atomCount + 1
  rw [actual_fold raw center demand,
    ReviewedPositiveHydrogenBondTransportClosureProofs.ReviewedPositiveHydrogenBondTransportClosure.withExplicitHydrogensStep_atomCount]
  simp only [initialHydrogenExpansionState, List.length_map, atomCount, demand.one]

/-- Actual splice position may vary; the identical old records and one fresh record are preserved. -/
theorem actual_bond_permutation (raw : RawMolecule) (center : Nat)
    (demand : OneHydrogenDemand raw center) :
    raw.withExplicitHydrogens.bonds.Perm (raw.bonds ++ [generatedBond raw center]) := by
  rw [ReviewedPositiveHydrogenBondTransportClosureProofs.ReviewedPositiveHydrogenBondTransportClosure.withExplicitHydrogens_bonds_eq_fold,
    actual_fold raw center demand]
  have permutation :=
    ReviewedPositiveHydrogenBondTransportClosureProofs.ReviewedPositiveHydrogenBondTransportClosure.withExplicitHydrogensStep_bonds_perm
      raw (initialHydrogenExpansionState raw) center
  simpa [initialHydrogenExpansionState, HydrogenExpansionState.toRawMolecule, demand.one,
    ReviewedPositiveHydrogenBondTransportClosureProofs.ReviewedPositiveHydrogenBondTransportClosure.freshHydrogenBonds,
    ReviewedPositiveHydrogenBondTransportClosureProofs.ReviewedPositiveHydrogenBondTransportClosure.freshHydrogenIds,
    generatedBond, atomCount] using permutation

theorem actual_original_atom (raw : RawMolecule) (center index : Nat)
    (intake : PositiveLeafIntake raw center) (spec : AtomSpec)
    (observed : raw.atomAt? index = some spec) :
    raw.withExplicitHydrogens.atomAt? index = some (materializedAtomSpec spec) :=
  PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.withExplicitHydrogens_originalAtom raw
    intake.domain.leaf.wellFormed index spec observed

theorem actual_fresh_hydrogen (raw : RawMolecule) (center : Nat)
    (intake : PositiveLeafIntake raw center) :
    raw.withExplicitHydrogens.atomAt? raw.atomCount = some (AtomSpec.aliphatic .H) :=
  PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.withExplicitHydrogens_boundary_hydrogen raw
    intake.domain.leaf.wellFormed ⟨center, intake.demand.centerBound, by rw [intake.demand.one]; omega⟩

theorem actual_original_rank (raw : RawMolecule) (center index : Nat)
    (intake : PositiveLeafIntake raw center) (bound : index < raw.atomCount) :
    raw.withExplicitHydrogens.atomZAt index = raw.atomZAt index := by
  obtain ⟨spec, observed⟩ := listGet?_exists_of_lt raw.atoms index bound
  have looked : raw.atomAt? index = some spec := observed
  rw [atomZAt, actual_original_atom raw center index intake spec looked, atomZAt, looked]
  rfl

theorem actual_fresh_rank (raw : RawMolecule) (center : Nat)
    (intake : PositiveLeafIntake raw center) :
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
    (intake : PositiveLeafIntake raw center) :
    recordNeighbors raw.withExplicitHydrogens raw.atomCount = [center] := by
  have different : center ≠ raw.atomCount := by have := intake.demand.centerBound; omega
  have projected := (actual_bond_permutation raw center intake.demand).filterMap
    (recordNeighbor? raw.atomCount)
  rw [List.filterMap_append] at projected
  change (recordNeighbors raw.withExplicitHydrogens raw.atomCount).Perm
    (recordNeighbors raw raw.atomCount ++ [generatedBond raw center].filterMap
      (recordNeighbor? raw.atomCount)) at projected
  rw [original_fresh_row_empty raw intake.domain.leaf.wellFormed] at projected
  have singleton : (recordNeighbors raw.withExplicitHydrogens raw.atomCount).Perm [center] := by
    simpa [recordNeighbor?, generatedBond, different] using projected
  exact singleton.eq_singleton

theorem actual_old_leaf_row (raw : RawMolecule) (center atom : Nat)
    (intake : PositiveLeafIntake raw center) (member : atom ∈ recordNeighbors raw center) :
    recordNeighbors raw.withExplicitHydrogens atom = [center] := by
  have bounds := recordNeighbor_bounds intake.domain.leaf.wellFormed member
  have notFresh : raw.atomCount ≠ atom := by omega
  have notCenter : center ≠ atom := bounds.2.symm
  have row := RuntimeSourceGenericPublicPipelineRecoveryProofs.RuntimeSourceGenericPublicPipelineRecovery.actual_leaf_record_row
    raw center atom intake.domain.leaf member
  have projected := (actual_bond_permutation raw center intake.demand).filterMap (recordNeighbor? atom)
  rw [List.filterMap_append] at projected
  change (recordNeighbors raw.withExplicitHydrogens atom).Perm
    (recordNeighbors raw atom ++ [generatedBond raw center].filterMap (recordNeighbor? atom)) at projected
  rw [row] at projected
  have singleton : (recordNeighbors raw.withExplicitHydrogens atom).Perm [center] := by
    simpa [recordNeighbor?, generatedBond, notFresh, notCenter] using projected
  exact singleton.eq_singleton

theorem actual_four (raw : RawMolecule) (center : Nat) (intake : PositiveLeafIntake raw center) :
    (recordNeighbors raw.withExplicitHydrogens center).length = 4 := by
  rw [(actual_center_records raw center intake.demand).length_eq,
    List.length_append, intake.three]
  rfl

/-- Old ranks are unchanged and the newly generated hydrogen contributes exactly rank 1. -/
theorem actual_rank_permutation (raw : RawMolecule) (center : Nat)
    (intake : PositiveLeafIntake raw center) :
    ((recordNeighbors raw.withExplicitHydrogens center).map raw.withExplicitHydrogens.atomZAt).Perm
      ((recordNeighbors raw center).map raw.atomZAt ++ [1]) := by
  have permutation := (actual_center_records raw center intake.demand).map raw.withExplicitHydrogens.atomZAt
  have mapped : (recordNeighbors raw center).map raw.withExplicitHydrogens.atomZAt =
      (recordNeighbors raw center).map raw.atomZAt := by
    apply List.map_congr_left
    intro atom member
    exact actual_original_rank raw center atom intake
      (recordNeighbor_bounds intake.domain.leaf.wellFormed member).1
  simpa only [List.map_append, List.map_cons, List.map_nil, mapped,
    actual_fresh_rank raw center intake] using permutation

theorem actual_distinct_ranks (raw : RawMolecule) (center : Nat)
    (intake : PositiveLeafIntake raw center) :
    ((recordNeighbors raw.withExplicitHydrogens center).map raw.withExplicitHydrogens.atomZAt).Nodup := by
  apply (actual_rank_permutation raw center intake).nodup_iff.mpr
  apply List.nodup_append.mpr
  refine ⟨intake.domain.leaf.distinctRanks, by simp, ?_⟩
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
    (intake : PositiveLeafIntake raw center) (bond : RawBond)
    (member : bond ∈ raw.withExplicitHydrogens.bonds)
    (incident : bond.source = center ∨ bond.target = center) : bond.kind = .single := by
  have retained := (actual_bond_permutation raw center intake.demand).mem_iff.mp member
  rcases List.mem_append.mp retained with old | fresh
  · exact intake.domain.incidentKinds bond old incident
  · have equal : bond = generatedBond raw center := List.mem_singleton.mp fresh
    subst bond
    rfl

/-- The actual returned graph enters the checked single-leaf comparator domain, without a supplied
post-domain, root list, sort or desired descriptor. -/
theorem actual_expanded_domain (raw : RawMolecule) (center : Nat)
    (intake : PositiveLeafIntake raw center) : SingleLeafDomain raw.withExplicitHydrogens center := by
  have admitted : raw.StereochemicalAdmissible :=
    ⟨⟨intake.domain.leaf.wellFormed, intake.unique⟩, intake.written⟩
  have output := withExplicitHydrogens_preserves_admissible raw admitted
  refine ⟨⟨output.1, ?_, ?_, ?_, actual_distinct_ranks raw center intake⟩,
    actual_incident_kinds raw center intake⟩
  · rw [actual_atom_count raw center intake.demand]
    have := intake.demand.centerBound
    omega
  · apply List.all_eq_true.mpr
    intro atom member
    obtain ⟨bond, retained, observed⟩ := List.mem_filterMap.mp member
    have kind := actual_incident_kinds raw center intake bond retained (record_incidence observed)
    exact decide_eq_true (by
      rw [bondOrder_eq_kind_of_mem_connects raw.withExplicitHydrogens output.1 output.2 retained
        (record_connects observed), kind]
      rfl)
  · apply List.all_eq_true.mpr
    intro atom member
    have original := (actual_center_records raw center intake.demand).mem_iff.mp member
    have row : recordNeighbors raw.withExplicitHydrogens atom = [center] := by
      rcases List.mem_append.mp original with old | fresh
      · exact actual_old_leaf_row raw center atom intake old
      · have same : atom = raw.atomCount := List.mem_singleton.mp fresh
        subst atom
        exact actual_fresh_leaf_row raw center intake
    exact decide_eq_true (by
      change (recordNeighbors raw.withExplicitHydrogens atom).eraseDups.length ≤ 1
      rw [row]
      exact Nat.le_refl 1)

theorem actual_written_exact (raw : RawMolecule) : raw.withExplicitHydrogens.WrittenNeighborExact :=
  withExplicitHydrogens_writtenNeighborExact raw

/-- REAL center written order: H is inserted using the original preceding-atom test. -/
theorem actual_written_center (raw : RawMolecule) (center : Nat)
    (intake : PositiveLeafIntake raw center) :
    raw.withExplicitHydrogens.writtenNeighbors center =
      insertHydrogenInOrder (raw.writtenNeighbors center)
        (HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery.materializationHasPreceding raw center)
        [raw.atomCount] := by
  rw [HydrogenWrittenNeighborRecoveryProofs.HydrogenWrittenNeighborRecovery.withExplicitHydrogens_writtenNeighbors
    raw intake.domain.leaf.wellFormed intake.written center intake.demand.centerBound]
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
    (intake : PositiveLeafIntake raw center) (only : OnlyCenterTagged raw center) :
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
    (intake : PositiveLeafIntake raw center) :
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
      intake.domain.leaf.wellFormed raw.atomCount (AtomSpec.aliphatic .H) (Nat.le_refl _)
      (actual_fresh_hydrogen raw center intake)).2
    unfold hydrogenCountAt
    rw [actual_fresh_hydrogen raw center intake]
    change (match (defaultValences (AtomSpec.aliphatic .H)).find?
        (fun v => raw.withExplicitHydrogens.incidentBondOrderSum raw.atomCount ≤ v) with
      | some v => v - raw.withExplicitHydrogens.incidentBondOrderSum raw.atomCount
      | none => 0) = 0
    rw [valence]
    rfl


theorem normalized_intake (raw : RawMolecule) (center : Nat)
    (intake : PositiveLeafIntake raw center) : PositiveLeafIntake raw.normalizeUnspecifiedBonds center := by
  refine ⟨normalized_single_leaf raw center intake.domain,
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
    (intake : PositiveLeafIntake raw center) : SingleLeafDomain (parsedInput raw) center :=
  actual_expanded_domain raw.normalizeUnspecifiedBonds center (normalized_intake raw center intake)

theorem actual_parsed_four (raw : RawMolecule) (center : Nat)
    (intake : PositiveLeafIntake raw center) : (recordNeighbors (parsedInput raw) center).length = 4 :=
  actual_four raw.normalizeUnspecifiedBonds center (normalized_intake raw center intake)

theorem actual_parsed_zero_demand (raw : RawMolecule) (center : Nat)
    (intake : PositiveLeafIntake raw center) :
    ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.ZeroHydrogenDemand (parsedInput raw) :=
  actual_expanded_zero_demand raw.normalizeUnspecifiedBonds center (normalized_intake raw center intake)

theorem actual_parsed_only_center_tagged (raw : RawMolecule) (center : Nat)
    (intake : PositiveLeafIntake raw center) (only : OnlyCenterTagged raw center) :
    OnlyCenterTagged (parsedInput raw) center :=
  actual_only_center_tagged raw.normalizeUnspecifiedBonds center
    (normalized_intake raw center intake) only

/-- Actual PUBLIC occurrence consumer after original-input positive-demand preprocessing. Its
collector, empty auxiliary environment, strict comparisons and written parity are derived internally. -/
theorem actual_parsed_public_occurrence (raw : RawMolecule) (center : Nat)
    (intake : PositiveLeafIntake raw center) (only : OnlyCenterTagged raw center)
    (spec : AtomSpec) (observed : raw.atomAt? center = some spec)
    (parity : TetrahedralInputParity) (tagged : spec.tetrahedral? = some parity) (extraFuel : Nat) :
    ∃ positions, tetrahedralOccurrenceFact? (parsedInput raw) (extraFuel + 2) center =
      some (recoveredPublicFact center positions
        (RawMolecule.descriptorOfParity parity (RawMolecule.permutationIsEven positions))) :=
  RuntimeSourceGenericPublicPipelineRecoveryProofs.RuntimeSourceGenericPublicPipelineRecovery.actual_public_fact_exists (parsedInput raw) center
    (actual_parsed_domain raw center intake)
    (withExplicitHydrogens_writtenNeighborExact raw.normalizeUnspecifiedBonds)
    (actual_parsed_four raw center intake) (actual_parsed_only_center_tagged raw center intake only)
    (materializedAtomSpec spec)
    (actual_positive_or_zero_atom_transport raw intake.domain.leaf.wellFormed center spec observed)
    parity tagged extraFuel

/-- The ACTUAL positive-demand parsed input satisfies the existing legacy classifier's independent
tagged/supported/four-written/distinct-rank intake, without supplying a sort or desired positions. -/
theorem actual_parsed_legacy_intake (raw : RawMolecule) (center : Nat)
    (intake : PositiveLeafIntake raw center) (spec : AtomSpec)
    (observed : raw.atomAt? center = some spec) (parity : TetrahedralInputParity)
    (tagged : spec.tetrahedral? = some parity) (supported : centreElementSupported spec.element = true) :
    LegacyAtomicIntake (parsedInput raw) center (materializedAtomSpec spec) parity := by
  have domain := actual_parsed_domain raw center intake
  have written : (parsedInput raw).WrittenNeighborExact :=
    withExplicitHydrogens_writtenNeighborExact raw.normalizeUnspecifiedBonds
  refine ⟨actual_positive_or_zero_atom_transport raw intake.domain.leaf.wellFormed center spec observed,
    tagged, supported, NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment.actual_written_four
      (parsedInput raw) center domain written
      (actual_parsed_four raw center intake), ?_⟩
  exact (written_neighbors_perm_records (parsedInput raw) center domain written
    |>.map (parsedInput raw).atomZAt).nodup_iff.mpr domain.leaf.distinctRanks

/-- Genuine GENERAL higher public parsed classifier result from ORIGINAL one-H intake. The label
is its own computed written-slot parity, not an expected descriptor premise or a new consumer. -/
theorem actual_parsed_classifier (raw : RawMolecule) (center : Nat)
    (intake : PositiveLeafIntake raw center) (spec : AtomSpec)
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

/-- Actual HIGHER classifier result and OWN source meaning after positive-demand preprocessing.
Source admission/perception are explicitly separate from the derived expansion domain. No result,
sort, parity alignment, auxiliary state or desired label is supplied. -/
theorem actual_parsed_source_alignment (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (carrierFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (intake : PositiveLeafIntake raw center.1.val)
    (agreement : RawAnnotationAgreement (parsedInput raw) source)
    (spec : AtomSpec) (observed : raw.atomAt? center.1.val = some spec)
    (parity : TetrahedralInputParity) (tagged : spec.tetrahedral? = some parity)
    (supported : centreElementSupported spec.element = true) (known : raw.rule2MassesKnown? = true)
    (view : source.AromaticCanonicalDependencyView (source.aromaticCanonicalFinalOccurrence carrierFuel center)) :
    ∃ descriptor,
      parsedTetrahedralDescriptorAt? raw center.1.val = some descriptor ∧
      constitutionParserRichDescriptor? (parsedInput raw) source agreement
        (withExplicitHydrogens_writtenNeighborExact raw.normalizeUnspecifiedBonds)
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view (2 * (carrierFuel + 1)) =
          some (.chiral descriptor) ∧
      ConstitutionParserRichDescriptorMeaning (parsedInput raw) source agreement
        (withExplicitHydrogens_writtenNeighborExact raw.normalizeUnspecifiedBonds)
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) view (2 * (carrierFuel + 1))
          (.chiral descriptor) := by
  rw [parsed_classifier_input]
  exact actual_higher_source_alignment (parsedInput raw) source agreement
    (withExplicitHydrogens_writtenNeighborExact raw.normalizeUnspecifiedBonds) carrierFuel center
    (actual_parsed_domain raw center.1.val intake) (actual_parsed_four raw center.1.val intake)
    (materializedAtomSpec spec)
    (actual_positive_or_zero_atom_transport raw intake.domain.leaf.wellFormed center.1.val spec observed)
    parity tagged supported (actual_parsed_mass_guard raw known) view

namespace ClosedPositive

/-- Independently specified input `[C@@H](F)(Cl)Br`, before H expansion. -/
abbrev raw : RawMolecule := PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.bracketCarbonHalide

theorem actual_original_domain : SingleLeafDomain raw 0 := by
  refine ⟨⟨PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.bracketCarbonHalide_wellFormed,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, ?_⟩
  intro bond member _
  change bond ∈ [⟨0, 1, .single⟩, ⟨0, 2, .single⟩, ⟨0, 3, .single⟩] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

theorem actual_intake : PositiveLeafIntake raw 0 := by
  refine ⟨actual_original_domain, by unfold BondRecordsUnique; decide +kernel, ?_, ?_, by decide +kernel, ?_⟩
  · apply (writtenNeighborExact?_eq_true_iff raw).mp
    decide +kernel
  · refine ⟨by decide +kernel,
      PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.bracketCarbonHalide_centerHydrogens, ?_⟩
    intro index bound different
    change index < 4 at bound
    interval_cases index
    · contradiction
    all_goals decide +kernel
  · intro atom member
    change atom ∈ [1, 2, 3] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide +kernel

theorem actual_written_hydrogen_first : raw.withExplicitHydrogens.writtenNeighbors 0 = [4, 1, 2, 3] := by
  rw [actual_written_center raw 0 actual_intake]
  rfl

/-- Nonvacuity of the GENERAL derived post-domain; no expanded-domain fact was supplied. -/
theorem actual_four_distinct_leaf_transport :
    SingleLeafDomain raw.withExplicitHydrogens 0 ∧
      (recordNeighbors raw.withExplicitHydrogens 0).length = 4 ∧
      ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.ZeroHydrogenDemand raw.withExplicitHydrogens :=
  ⟨actual_expanded_domain raw 0 actual_intake, actual_four raw 0 actual_intake,
    actual_expanded_zero_demand raw 0 actual_intake⟩

/-- The GENERAL positive-demand theorem derives the actual higher classifier; only its finite
returned parity expression is evaluated to identify R on this real nonidentity written frame. -/
theorem actual_higher_classifier_R : parsedTetrahedralDescriptorAt? raw 0 = some RS.R := by
  calc
    parsedTetrahedralDescriptorAt? raw 0 = some
      (descriptorOfParity .clockwise (permutationIsEven
        (legacyPositions (parsedInput raw) (analysisFuel (parsedInput raw)) 0
          ((parsedInput raw).writtenNeighbors 0)))) :=
      actual_parsed_classifier raw 0 actual_intake
        PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.bracketCenterSpec
        PositiveHydrogenAtomTransportProofs.PositiveHydrogenAtomTransport.bracketCarbonHalide_centerSpec_lookup
        .clockwise rfl (by decide +kernel) (by decide +kernel)
    _ = some RS.R := by decide +kernel

end ClosedPositive

end TetraStereo.UniversalProof.RuntimePositiveHydrogenDomainRecoveryProofs.RuntimePositiveHydrogenDomainRecovery
