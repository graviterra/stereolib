import TetraStereo.UniversalProof.NextFrontier.NativeNitrileInitialSeed

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileSeedDiscovery

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
open TetraStereo.UniversalProof.NextFrontier.NativeNitrileInitialSeed

private theorem seed_covers_observed_tag (n : Nat) (parity : TetrahedralInputParity)
    (index : Nat) (spec : AtomSpec) (tag : TetrahedralInputParity)
    (observed : (nitrileResult n parity).parsed.atomAt? index = some spec)
    (tagged : spec.tetrahedral? = some tag) :
    ∃ fact, (nitrileInitial n parity).factAt? index = some fact := by
  rw [nitrileResult, raw_normalized_parsed] at observed
  have bounded := listGet?_eq_some_implies_lt (raw parity n).atoms index spec observed
  have atRoot := raw_only_center_tagged parity n ⟨index, bounded⟩ spec observed
    (by rw [tagged]; rfl)
  change index = 0 at atRoot
  rw [atRoot]
  exact ⟨seedFact parity, actual_initial_seed_lookup n parity⟩

private theorem initial_fact_fields (n : Nat) (parity : TetrahedralInputParity)
    (fact : RawDescriptorFact) (member : fact ∈ nitrileInitial n parity) :
    fact.evidenceSize = 0 ∧ fact.uppercase = true := by
  rw [initial_eq_entries] at member
  obtain ⟨index, _, computed⟩ := List.mem_filterMap.mp member
  exact (seed_entry_fields n parity index fact computed).2

/-- Every actual update either freezes its derived seed or sees no parsed annotation. -/
theorem actual_update_fixed (n : Nat) (parity : TetrahedralInputParity)
    (maxEvidence index : Nat) :
    updateRawDescriptorAt (nitrileResult n parity) (expanded parity n) maxEvidence (nitrileFuel n parity)
      (nitrileInitial n parity) index = nitrileInitial n parity := by
  cases found : (nitrileInitial n parity).factAt? index with
  | some fact =>
      have member : fact ∈ nitrileInitial n parity := List.mem_of_find?_eq_some found
      have zero := (initial_fact_fields n parity fact member).1
      simp [updateRawDescriptorAt, found, zero]
  | none =>
      cases observed : (nitrileResult n parity).parsed.atomAt? index with
      | none => simp [updateRawDescriptorAt, found, tetrahedralFactFromState?, observed]
      | some spec =>
          cases tagged : spec.tetrahedral? with
          | none => simp [updateRawDescriptorAt, found, tetrahedralFactFromState?, observed, tagged]
          | some tag =>
              obtain ⟨fact, lookup⟩ := seed_covers_observed_tag n parity index spec tag observed tagged
              rw [found] at lookup
              contradiction

/-- Any natural max-evidence bound and any schedule, with no supplied state. -/
theorem actual_schedule_fixed (n : Nat) (parity : TetrahedralInputParity) (maxEvidence : Nat)
    (schedule : List Nat) :
    runRawDescriptorDiscoverySchedule (nitrileResult n parity) (expanded parity n) maxEvidence
      (nitrileFuel n parity) schedule (nitrileInitial n parity) = nitrileInitial n parity := by
  unfold runRawDescriptorDiscoverySchedule
  induction schedule with
  | nil => rfl
  | cons index rest ih =>
      rw [List.foldl_cons, actual_update_fixed n parity maxEvidence index]
      exact ih

theorem actual_pass_fixed (n : Nat) (parity : TetrahedralInputParity) (maxEvidence : Nat) :
    runRawDescriptorDiscoveryPass (nitrileResult n parity) (expanded parity n) maxEvidence
      (nitrileFuel n parity) (nitrileInitial n parity) = nitrileInitial n parity :=
  actual_schedule_fixed n parity maxEvidence _

/-- A single pass already stabilizes. The positive bound is on schedule budget, not first-Z depth. -/
theorem actual_stabilized (n : Nat) (parity : TetrahedralInputParity) (maxEvidence remaining : Nat) :
    stabilizedRawDescriptorState? (nitrileResult n parity) (expanded parity n) maxEvidence (nitrileFuel n parity)
      (remaining + 1) (nitrileInitial n parity) = some (nitrileInitial n parity) := by
  simp [stabilizedRawDescriptorState?, discoverRawDescriptorsFromCertified,
    actual_pass_fixed n parity maxEvidence]

theorem actual_unresolved_nil (n : Nat) (parity : TetrahedralInputParity) :
    (rawAnnotatedCenters (nitrileResult n parity)).filter (fun index =>
      ((nitrileInitial n parity).factAt? index).isNone) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro index member
  obtain ⟨_, taggedIndex⟩ := List.mem_filter.mp member
  cases observed : (nitrileResult n parity).parsed.atomAt? index with
  | none => simp [observed] at taggedIndex
  | some spec =>
      cases tagged : spec.tetrahedral? with
      | none => simp [observed, tagged] at taggedIndex
      | some tag =>
          obtain ⟨fact, found⟩ := seed_covers_observed_tag n parity index spec tag observed tagged
          rw [found]
          simp

theorem actual_auxiliary_fixed (n : Nat) (parity : TetrahedralInputParity) (maxEvidence : Nat) :
    solveAuxiliaryDescriptorDependencies (nitrileResult n parity) (expanded parity n) maxEvidence
      (nitrileFuel n parity) (nitrileInitial n parity) = nitrileInitial n parity := by
  simp [solveAuxiliaryDescriptorDependencies, actual_unresolved_nil n parity,
    auxiliarySimultaneousDescriptorState]

theorem actual_exact_auxiliary_fixed (n : Nat) (parity : TetrahedralInputParity) (maxEvidence : Nat) :
    solveExactAuxiliaryDescriptorDependencies (nitrileResult n parity) (expanded parity n) maxEvidence
      (nitrileFuel n parity) (nitrileInitial n parity) = nitrileInitial n parity := by
  simp [solveExactAuxiliaryDescriptorDependencies, actual_unresolved_nil n parity]

theorem actual_finish_fixed (n : Nat) (parity : TetrahedralInputParity) :
    finishRawDescriptorSource (nitrileResult n parity) (expanded parity n) (nitrileFuel n parity)
      (nitrileInitial n parity) = nitrileInitial n parity := by
  unfold finishRawDescriptorSource
  simp only [actual_unresolved_nil n parity]
  split
  · rfl
  · exact actual_exact_auxiliary_fixed n parity 100

theorem actual_constructive_fixed (n : Nat) (parity : TetrahedralInputParity) :
    constructiveRawDescriptorSourceValue (nitrileResult n parity) (expanded parity n) (nitrileFuel n parity)
      (nitrileInitial n parity) = nitrileInitial n parity := by
  simp [constructiveRawDescriptorSourceValue, actual_stabilized n parity,
    actual_auxiliary_fixed n parity, retainLastStableRawDescriptorState, actual_finish_fixed n parity]

private theorem actual_initial_nonempty (n : Nat) (parity : TetrahedralInputParity)  :
    (nitrileInitial n parity).isEmpty = false := by
  have found := actual_initial_seed_lookup n parity
  have member := List.mem_of_find?_eq_some found
  cases initial : nitrileInitial n parity with
  | nil => rw [initial] at member; exact False.elim (List.not_mem_nil member)
  | cons first rest => rfl

theorem actual_source_selected (n : Nat) (parity : TetrahedralInputParity)  :
    discoverRawDescriptorSource (nitrileResult n parity) (expanded parity n) (nitrileFuel n parity) = nitrileInitial n parity := by
  have initialNonempty : (initialRawDescriptorState (nitrileResult n parity) (expanded parity n)
      (nitrileFuel n parity)).isEmpty = false := actual_initial_nonempty n parity
  unfold discoverRawDescriptorSource certifiedRawDescriptorSource
  simp only [initialNonempty, Bool.false_eq_true, ↓reduceIte]
  change constructiveRawDescriptorSourceValue (nitrileResult n parity) (expanded parity n)
    (nitrileFuel n parity) (nitrileInitial n parity) = _
  exact actual_constructive_fixed n parity

theorem actual_rule6_neutral (n : Nat) (parity : TetrahedralInputParity) :
    normalizeTwoCyclicRule6AnchorCarrier (expanded parity n) (nitrileFuel n parity) (nitrileInitial n parity) =
      nitrileInitial n parity := by
  unfold normalizeTwoCyclicRule6AnchorCarrier
  have mapped := List.map_congr_left (l := nitrileInitial n parity) (g := id)
    (f := fun fact => match exactTwoCyclicAnchorCarrierWitness? (expanded parity n)
      (nitrileInitial n parity) (nitrileFuel n parity) fact.atom fact with
      | some true => { fact with descriptor := RS.swap fact.descriptor }
      | _ => fact) (by
        intro fact member
        have uppercase := (initial_fact_fields n parity fact member).2
        simp [exactTwoCyclicAnchorCarrierWitness?, uppercase])
  simpa only [List.map_id] using mapped

/-- Whole production discovery at actual analysisFuel equals its internally computed seed state. -/
theorem actual_discovery_is_initial (n : Nat) (parity : TetrahedralInputParity)  :
    discoverRawDescriptors (nitrileResult n parity) (expanded parity n) (nitrileFuel n parity) = nitrileInitial n parity := by
  rw [discoverRawDescriptors, actual_source_selected n parity]
  exact actual_rule6_neutral n parity

/-- Actual final discovered fact: parity-derived descriptor and priority [1,2,3,0]. -/
theorem actual_discovered_tag (n : Nat) (parity : TetrahedralInputParity)  :
    (discoverRawDescriptors (nitrileResult n parity) (expanded parity n) (nitrileFuel n parity)).factAt? 0 =
      some (seedFact parity) := by
  rw [actual_discovery_is_initial n parity]
  exact actual_initial_seed_lookup n parity

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileSeedDiscovery
