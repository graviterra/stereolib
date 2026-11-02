import TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupport
import TetraStereo.UniversalProof.RuntimeLegacyClassifierClosureProofs.RuntimeLegacyClassifierClosure
import TetraStereo.UniversalProof.NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery
import TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofsLibrary.GeneratedPendantOccurrenceRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.FirstZSeedDiscoveryRecoveryProofs.FirstZSeedDiscoveryRecovery

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity
open TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery
open TetraStereo.UniversalProof.RuntimeLegacyClassifierClosureProofs.RuntimeLegacyClassifierClosure
open TetraStereo.UniversalProof.NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery














/-- Independent physical first-Z intake for every actual input annotation. -/
structure FirstZTagDomain (raw : RawMolecule) : Prop where
  written : raw.WrittenNeighborExact
  zero : ZeroHydrogenDemand raw
  tagged : ∀ index spec parity, raw.atomAt? index = some spec →
    spec.tetrahedral? = some parity →
    AtomicCenterDomain raw index ∧ (recordNeighbors raw index).length = 4 ∧
      centreElementSupported spec.element = true
  nonempty : ∃ index spec parity, raw.atomAt? index = some spec ∧
    spec.tetrahedral? = some parity

/-- The intended pendant family discharges every rank/four-center condition using physical
records. The additional element condition is an atom-record condition, not a label premise. -/
theorem domain_of_pendant_records (raw : RawMolecule) (well : raw.WellFormed)
    (written : raw.WrittenNeighborExact) (zero : ZeroHydrogenDemand raw)
    (sites : ∀ index spec parity, raw.atomAt? index = some spec →
      spec.tetrahedral? = some parity →
      Nonempty (NativeInitialSeedRuntimeSupportProofsLibrary.GeneratedPendantOccurrenceRecovery.PendantSite raw index) ∧
        spec.element = .C)
    (nonempty : ∃ index spec parity, raw.atomAt? index = some spec ∧
      spec.tetrahedral? = some parity) : FirstZTagDomain raw := by
  refine ⟨written, zero, ?_, nonempty⟩
  intro index spec parity observed tagged
  obtain ⟨⟨site⟩, carbon⟩ := sites index spec parity observed tagged
  refine ⟨NativeInitialSeedRuntimeSupportProofsLibrary.GeneratedPendantOccurrenceRecovery.PendantSite.atomic_domain raw well index site,
    NativeInitialSeedRuntimeSupportProofsLibrary.GeneratedPendantOccurrenceRecovery.PendantSite.four raw index site, ?_⟩
  rw [carbon]
  rfl

-- materialized is re-exported from NativeInitialSeedRuntimeSupport.


def seedDescriptor (result : ChemistryNormalizationResult) (fuel index : Nat)
    (parity : TetrahedralInputParity) : RS :=
  descriptorOfParity parity (permutationIsEven
    (legacyPositions (materialized result) fuel index
      ((materialized result).writtenNeighbors index)))

/-- Priority metadata remains the actual Rule-3-aware production computation. -/
def seedFact (result : ChemistryNormalizationResult) (fuel index : Nat)
    (parity : TetrahedralInputParity) : RawDescriptorFact :=
  { atom := index, descriptor := seedDescriptor result fuel index parity,
    uppercase := true, evidenceSize := 0,
    priorityPositions := (rankBranchPositionsThroughRule3? result (materialized result) fuel
      index ((materialized result).ligandsWithLonePair index)).getD [] }

/-- A factored spelling of the actual initial-state filterMap entry, not a new assigner. -/
def seedEntry (result : ChemistryNormalizationResult) (fuel index : Nat) :
    Option RawDescriptorFact :=
  match tetrahedralOutcomeThroughRule3 result (materialized result) fuel index with
  | .tetrahedral descriptor =>
      some ({ atom := index, descriptor := descriptor, uppercase := true, evidenceSize := 0, priorityPositions := (rankBranchPositionsThroughRule3? result (materialized result) fuel index ((materialized result).ligandsWithLonePair index)).getD [] } : RawDescriptorFact)
  | _ => none

theorem initial_eq_entries (result : ChemistryNormalizationResult) (fuel : Nat) :
    initialRawDescriptorState result (materialized result) fuel =
      (List.range result.parsed.atomCount).filterMap (seedEntry result fuel) := rfl

theorem actual_materialized_legacy_intake (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (index : Nat) (spec : AtomSpec)
    (parity : TetrahedralInputParity) (observed : result.parsed.atomAt? index = some spec)
    (tagged : spec.tetrahedral? = some parity) :
    LegacyAtomicIntake (materialized result) index (materializedAtomSpec spec) parity := by
  obtain ⟨physical, four, supported⟩ := domain.tagged index spec parity observed tagged
  have exactRecord := zero_demand_expansion_exact_record result.parsed domain.zero domain.written
  have writtenPerm := actual_written_permutation result.parsed index physical domain.written
  have writtenFour : (result.parsed.writtenNeighbors index).length = 4 := by
    rw [writtenPerm.length_eq, four]
  refine ⟨?_, tagged, supported, ?_, ?_⟩
  · rw [materialized, exactRecord, materialized_atom_lookup, observed]; rfl
  · rw [materialized, exactRecord,
      materialized_record_written_order result.parsed index physical.centerBound]
    exact writtenFour
  · rw [materialized, exactRecord,
      materialized_record_written_order result.parsed index physical.centerBound]
    have atomicNumbers : (materializedWrittenRecord result.parsed).atomZAt = result.parsed.atomZAt := by
      funext neighbor
      exact materialized_atomic_number result.parsed neighbor
    rw [atomicNumbers]
    exact (writtenPerm.map result.parsed.atomZAt).nodup_iff.mpr physical.distinctRanks

theorem actual_seed_entry (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (fuel index : Nat) (spec : AtomSpec)
    (parity : TetrahedralInputParity) (observed : result.parsed.atomAt? index = some spec)
    (tagged : spec.tetrahedral? = some parity) :
    seedEntry result fuel index = some (seedFact result fuel index parity) := by
  have intake := actual_materialized_legacy_intake result domain index spec parity observed tagged
  have outcome := actual_legacy_outcome (materialized result) index fuel
    (materializedAtomSpec spec) parity intake
  simp only [seedEntry, tetrahedralOutcomeThroughRule3, outcome]
  rfl

theorem seed_entry_fields (result : ChemistryNormalizationResult) (fuel index : Nat)
    (fact : RawDescriptorFact) (computed : seedEntry result fuel index = some fact) :
    fact.atom = index ∧ fact.evidenceSize = 0 ∧ fact.uppercase = true := by
  unfold seedEntry at computed
  cases outcome : tetrahedralOutcomeThroughRule3 result (materialized result) fuel index <;>
    simp_all
  all_goals
    subst fact
    exact ⟨rfl, rfl, rfl⟩

private theorem find_filterMap_entry (entry : Nat → Option RawDescriptorFact)
    (key : ∀ index fact, entry index = some fact → fact.atom = index)
    (indices : List Nat) (index : Nat) (fact : RawDescriptorFact)
    (computed : entry index = some fact) (member : index ∈ indices) :
    (indices.filterMap entry).find? (fun candidate => candidate.atom == index) = some fact := by
  induction indices with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons first rest ih =>
      by_cases same : first = index
      · subst first
        simp [computed, key index fact computed]
      · have retained : index ∈ rest := (List.mem_cons.mp member).resolve_left (Ne.symm same)
        cases firstComputed : entry first with
        | none => simpa [List.filterMap_cons, firstComputed] using ih retained
        | some candidate =>
            have atom := key first candidate firstComputed
            simpa [List.filterMap_cons, firstComputed, atom, same] using ih retained

theorem actual_seed_lookup (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (fuel index : Nat) (spec : AtomSpec)
    (parity : TetrahedralInputParity) (observed : result.parsed.atomAt? index = some spec)
    (tagged : spec.tetrahedral? = some parity) :
    (initialRawDescriptorState result (materialized result) fuel).factAt? index =
      some (seedFact result fuel index parity) := by
  have physical := (domain.tagged index spec parity observed tagged).1
  rw [initial_eq_entries]
  exact find_filterMap_entry (seedEntry result fuel)
    (fun i fact computed => (seed_entry_fields result fuel i fact computed).1)
    (List.range result.parsed.atomCount) index (seedFact result fuel index parity)
    (actual_seed_entry result domain fuel index spec parity observed tagged)
    (List.mem_range.mpr physical.centerBound)

theorem initial_fact_fields (result : ChemistryNormalizationResult) (fuel : Nat)
    (fact : RawDescriptorFact)
    (member : fact ∈ initialRawDescriptorState result (materialized result) fuel) :
    fact.evidenceSize = 0 ∧ fact.uppercase = true := by
  rw [initial_eq_entries] at member
  obtain ⟨index, _, computed⟩ := List.mem_filterMap.mp member
  exact (seed_entry_fields result fuel index fact computed).2

/-- Every actual center update freezes a derived seed, or rejects an actual untagged atom
before compiling any occurrence tree. No local callback completeness premise is used. -/
theorem actual_update_fixed (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (maxEvidence fuel index : Nat) :
    updateRawDescriptorAt result (materialized result) maxEvidence fuel
      (initialRawDescriptorState result (materialized result) fuel) index =
        initialRawDescriptorState result (materialized result) fuel := by
  let initial := initialRawDescriptorState result (materialized result) fuel
  cases found : initial.factAt? index with
  | some fact =>
      dsimp only [initial] at found
      have member : fact ∈ initial := List.mem_of_find?_eq_some found
      have zero := (initial_fact_fields result fuel fact member).1
      simp [updateRawDescriptorAt, found, zero]
  | none =>
      dsimp only [initial] at found
      cases observed : result.parsed.atomAt? index with
      | none => simp [updateRawDescriptorAt, found, tetrahedralFactFromState?, observed]
      | some spec =>
          cases tagged : spec.tetrahedral? with
          | none =>
              simp [updateRawDescriptorAt, found, tetrahedralFactFromState?, observed, tagged]
          | some parity =>
              have lookup := actual_seed_lookup result domain fuel index spec parity observed tagged
              rw [found] at lookup
              contradiction

theorem actual_schedule_fixed (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (maxEvidence fuel : Nat) (schedule : List Nat) :
    runRawDescriptorDiscoverySchedule result (materialized result) maxEvidence fuel schedule
      (initialRawDescriptorState result (materialized result) fuel) =
        initialRawDescriptorState result (materialized result) fuel := by
  unfold runRawDescriptorDiscoverySchedule
  induction schedule with
  | nil => rfl
  | cons index rest ih =>
      rw [List.foldl_cons, actual_update_fixed result domain maxEvidence fuel index]
      exact ih

theorem actual_pass_fixed (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (maxEvidence fuel : Nat) :
    runRawDescriptorDiscoveryPass result (materialized result) maxEvidence fuel
      (initialRawDescriptorState result (materialized result) fuel) =
        initialRawDescriptorState result (materialized result) fuel :=
  actual_schedule_fixed result domain maxEvidence fuel _

theorem actual_stabilized (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (maxEvidence fuel remaining : Nat) :
    stabilizedRawDescriptorState? result (materialized result) maxEvidence fuel (remaining + 1)
      (initialRawDescriptorState result (materialized result) fuel) =
        some (initialRawDescriptorState result (materialized result) fuel) := by
  simp [stabilizedRawDescriptorState?, discoverRawDescriptorsFromCertified,
    actual_pass_fixed result domain maxEvidence fuel]

theorem actual_unresolved_nil (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (fuel : Nat) :
    (rawAnnotatedCenters result).filter (fun index =>
      ((initialRawDescriptorState result (materialized result) fuel).factAt? index).isNone) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro index member
  obtain ⟨_, taggedIndex⟩ := List.mem_filter.mp member
  cases observed : result.parsed.atomAt? index with
  | none => simp [observed] at taggedIndex
  | some spec =>
      cases tagged : spec.tetrahedral? with
      | none => simp [observed, tagged] at taggedIndex
      | some parity =>
          rw [actual_seed_lookup result domain fuel index spec parity observed tagged]
          simp

theorem actual_auxiliary_solver_fixed (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (maxEvidence fuel : Nat) :
    solveAuxiliaryDescriptorDependencies result (materialized result) maxEvidence fuel
      (initialRawDescriptorState result (materialized result) fuel) =
        initialRawDescriptorState result (materialized result) fuel := by
  simp [solveAuxiliaryDescriptorDependencies, actual_unresolved_nil result domain fuel,
    auxiliarySimultaneousDescriptorState]

theorem actual_exact_solver_fixed (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (maxEvidence fuel : Nat) :
    solveExactAuxiliaryDescriptorDependencies result (materialized result) maxEvidence fuel
      (initialRawDescriptorState result (materialized result) fuel) =
        initialRawDescriptorState result (materialized result) fuel := by
  simp [solveExactAuxiliaryDescriptorDependencies, actual_unresolved_nil result domain fuel]

theorem actual_finish_fixed (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (fuel : Nat) :
    finishRawDescriptorSource result (materialized result) fuel
      (initialRawDescriptorState result (materialized result) fuel) =
        initialRawDescriptorState result (materialized result) fuel := by
  unfold finishRawDescriptorSource
  simp only [actual_unresolved_nil result domain fuel]
  split
  · rfl
  · exact actual_exact_solver_fixed result domain 100 fuel

theorem actual_constructive_source (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (fuel : Nat) :
    constructiveRawDescriptorSourceValue result (materialized result) fuel
      (initialRawDescriptorState result (materialized result) fuel) =
        initialRawDescriptorState result (materialized result) fuel := by
  simp [constructiveRawDescriptorSourceValue, actual_stabilized result domain,
    actual_auxiliary_solver_fixed result domain, retainLastStableRawDescriptorState,
    actual_finish_fixed result domain fuel]

theorem actual_initial_nonempty (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (fuel : Nat) :
    (initialRawDescriptorState result (materialized result) fuel).isEmpty = false := by
  obtain ⟨index, spec, parity, observed, tagged⟩ := domain.nonempty
  have found := actual_seed_lookup result domain fuel index spec parity observed tagged
  have member := List.mem_of_find?_eq_some found
  cases initial : initialRawDescriptorState result (materialized result) fuel with
  | nil => rw [initial] at member; exact False.elim (List.not_mem_nil member)
  | cons first rest => rfl

theorem actual_source_selected (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (fuel : Nat) :
    discoverRawDescriptorSource result (materialized result) fuel =
      initialRawDescriptorState result (materialized result) fuel := by
  unfold discoverRawDescriptorSource certifiedRawDescriptorSource
  simp only [actual_initial_nonempty result domain fuel, Bool.false_eq_true, ↓reduceIte]
  change constructiveRawDescriptorSourceValue result (materialized result) fuel
    (initialRawDescriptorState result (materialized result) fuel) = _
  exact actual_constructive_source result domain fuel

theorem actual_rule6_normalization_neutral (result : ChemistryNormalizationResult)
    (fuel : Nat) :
    normalizeTwoCyclicRule6AnchorCarrier (materialized result) fuel
      (initialRawDescriptorState result (materialized result) fuel) =
        initialRawDescriptorState result (materialized result) fuel := by
  unfold normalizeTwoCyclicRule6AnchorCarrier
  have mapped := List.map_congr_left
    (l := initialRawDescriptorState result (materialized result) fuel) (g := id)
    (f := fun fact => match exactTwoCyclicAnchorCarrierWitness? (materialized result)
      (initialRawDescriptorState result (materialized result) fuel) fuel fact.atom fact with
      | some true => { fact with descriptor := RS.swap fact.descriptor }
      | _ => fact) (by
      intro fact member
      have uppercase := (initial_fact_fields result fuel fact member).2
      simp [exactTwoCyclicAnchorCarrierWitness?, uppercase])
  simpa only [List.map_id] using mapped

/-- Actual whole descriptor discovery, not an invented parallel state or a supplied result. -/
theorem actual_discovery_is_initial (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (fuel : Nat) :
    discoverRawDescriptors result (materialized result) fuel =
      initialRawDescriptorState result (materialized result) fuel := by
  rw [discoverRawDescriptors, actual_source_selected result domain fuel]
  exact actual_rule6_normalization_neutral result fuel

/-- Every actual observed input tag is emitted in the actual whole discovered state with its
derived parity descriptor; the fact retains the actual Rule-3-aware priority metadata. -/
theorem actual_discovered_tag (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (fuel index : Nat) (spec : AtomSpec)
    (parity : TetrahedralInputParity) (observed : result.parsed.atomAt? index = some spec)
    (tagged : spec.tetrahedral? = some parity) :
    (discoverRawDescriptors result (materialized result) fuel).factAt? index =
      some (seedFact result fuel index parity) := by
  rw [actual_discovery_is_initial result domain fuel]
  exact actual_seed_lookup result domain fuel index spec parity observed tagged

theorem actual_seed_none_of_absent (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (fuel index : Nat)
    (absent : result.parsed.atomAt? index = none) : seedEntry result fuel index = none := by
  have lookup : (materialized result).atomAt? index = none := by
    rw [materialized, zero_demand_expansion_exact_record result.parsed domain.zero domain.written,
      materialized_atom_lookup, absent]
    rfl
  simp [seedEntry, tetrahedralOutcomeThroughRule3, tetrahedralOutcome, lookup]

theorem actual_seed_none_of_untagged (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (fuel index : Nat) (spec : AtomSpec)
    (observed : result.parsed.atomAt? index = some spec) (untagged : spec.tetrahedral? = none) :
    seedEntry result fuel index = none := by
  have lookup : (materialized result).atomAt? index = some (materializedAtomSpec spec) := by
    rw [materialized, zero_demand_expansion_exact_record result.parsed domain.zero domain.written,
      materialized_atom_lookup, observed]
    rfl
  simp [seedEntry, tetrahedralOutcomeThroughRule3, tetrahedralOutcome, lookup, untagged]

/-- The actual discovered list has precisely the actual tagged input indices, in parser order.
This statement does not assert that all untagged source candidate centers are nonstereogenic. -/
theorem actual_discovered_atoms (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (fuel : Nat) :
    (discoverRawDescriptors result (materialized result) fuel).map RawDescriptorFact.atom =
      rawAnnotatedCenters result := by
  rw [actual_discovery_is_initial result domain fuel, initial_eq_entries]
  unfold rawAnnotatedCenters
  generalize List.range result.parsed.atomCount = indices
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      cases observed : result.parsed.atomAt? index with
      | none => simp [actual_seed_none_of_absent result domain fuel index observed,
          observed, ih]
      | some spec =>
          cases tagged : spec.tetrahedral? with
          | none => simp [actual_seed_none_of_untagged result domain fuel index spec observed tagged,
              observed, tagged, ih]
          | some parity => simp [actual_seed_entry result domain fuel index spec parity observed tagged,
              observed, tagged, seedFact, ih]

end TetraStereo.UniversalProof.FirstZSeedDiscoveryRecoveryProofs.FirstZSeedDiscoveryRecovery
