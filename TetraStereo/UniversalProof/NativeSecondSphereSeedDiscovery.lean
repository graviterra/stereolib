import TetraStereo.UniversalProof.SecondSphereInitialSeedBridge

set_option autoImplicit false

namespace TetraStereo.UniversalProof.SecondSphereFamilyTrackedRanking

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
open TetraStereo.UniversalProof.SecondSphereFamilyValenceInstantiation
open TetraStereo.UniversalProof.SecondSphereFamilyPhysicalInstantiation





def familyResult (ps : List TetrahedralInputParity) : ChemistryNormalizationResult :=
  normalizeRawMolecule (familyRaw ps)

def familyFuel (ps : List TetrahedralInputParity) : Nat := analysisFuel (familyRaw ps)

def familyInitial (ps : List TetrahedralInputParity) : RawDescriptorState :=
  initialRawDescriptorState (familyResult ps) (familyRaw ps) (familyFuel ps)

private theorem actual_seed_lookup (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyInitial ps).factAt? (tagIndex i.val) =
      some (SecondSphereInitialSeedBridge.seedFact ps i) := by
  have found := SecondSphereInitialSeedBridge.actual_initial_seed_lookup ps i
  rw [familyRaw_normalized_parsed,
    SecondSphereInitialSeedBridge.actual_materialized_identity] at found
  have index : SecondSphereInitialSeedBridge.roleIndex i.val 5 = tagIndex i.val := by
    unfold SecondSphereInitialSeedBridge.roleIndex tagIndex
    omega
  rw [index] at found
  simpa only [familyInitial, familyResult, familyFuel] using found

private theorem seed_covers_observed_tag (ps : List TetrahedralInputParity)
    (index : Nat) (spec : AtomSpec) (parity : TetrahedralInputParity)
    (observed : (familyRaw ps).atomAt? index = some spec)
    (tagged : spec.tetrahedral? = some parity) :
    ∃ fact, (familyInitial ps).factAt? index = some fact := by
  have actual : observedTag (familyRaw ps) index = some parity := by
    simp only [observedTag, observed, Option.bind_some, tagged]
  obtain ⟨i, position, _⟩ := (familyRaw_observedTag_iff ps index parity).mp actual
  rw [position]
  exact ⟨_, actual_seed_lookup ps i⟩

private theorem initial_fact_fields (ps : List TetrahedralInputParity) (fact : RawDescriptorFact)
    (member : fact ∈ familyInitial ps) : fact.evidenceSize = 0 ∧ fact.uppercase = true := by
  change fact ∈ (List.range (familyResult ps).parsed.atomCount).filterMap
    (SecondSphereInitialSeedBridge.seedEntry ps) at member
  obtain ⟨index, _, computed⟩ := List.mem_filterMap.mp member
  unfold SecondSphereInitialSeedBridge.seedEntry at computed
  cases outcome : tetrahedralOutcomeThroughRule3 (normalizeRawMolecule (familyRaw ps))
    (familyRaw ps) (analysisFuel (familyRaw ps)) index <;> simp_all
  subst fact
  exact ⟨rfl, rfl⟩

/-- Each actual center update freezes its derived seed or rejects an untagged atom. -/
theorem actual_update_fixed (ps : List TetrahedralInputParity) (maxEvidence index : Nat) :
    updateRawDescriptorAt (familyResult ps) (familyRaw ps) maxEvidence (familyFuel ps)
      (familyInitial ps) index = familyInitial ps := by
  cases found : (familyInitial ps).factAt? index with
  | some fact =>
      have member : fact ∈ familyInitial ps := List.mem_of_find?_eq_some found
      have zero := (initial_fact_fields ps fact member).1
      simp [updateRawDescriptorAt, found, zero]
  | none =>
      cases observed : (familyRaw ps).atomAt? index with
      | none =>
          have parsed : (familyResult ps).parsed.atomAt? index = none := by
            simpa only [familyResult, familyRaw_normalized_parsed] using observed
          simp [updateRawDescriptorAt, found, tetrahedralFactFromState?, parsed]
      | some spec =>
          cases tagged : spec.tetrahedral? with
          | none =>
              have parsed : (familyResult ps).parsed.atomAt? index = some spec := by
                simpa only [familyResult, familyRaw_normalized_parsed] using observed
              simp [updateRawDescriptorAt, found, tetrahedralFactFromState?, parsed, tagged]
          | some parity =>
              obtain ⟨fact, lookup⟩ := seed_covers_observed_tag ps index spec parity observed tagged
              rw [found] at lookup
              contradiction

/-- Any natural max-evidence bound and any schedule, with no supplied state. -/
theorem actual_schedule_fixed (ps : List TetrahedralInputParity) (maxEvidence : Nat)
    (schedule : List Nat) :
    runRawDescriptorDiscoverySchedule (familyResult ps) (familyRaw ps) maxEvidence
      (familyFuel ps) schedule (familyInitial ps) = familyInitial ps := by
  unfold runRawDescriptorDiscoverySchedule
  induction schedule with
  | nil => rfl
  | cons index rest ih =>
      rw [List.foldl_cons, actual_update_fixed ps maxEvidence index]
      exact ih

theorem actual_pass_fixed (ps : List TetrahedralInputParity) (maxEvidence : Nat) :
    runRawDescriptorDiscoveryPass (familyResult ps) (familyRaw ps) maxEvidence
      (familyFuel ps) (familyInitial ps) = familyInitial ps :=
  actual_schedule_fixed ps maxEvidence _

/-- A single pass already stabilizes. The positive bound is on schedule budget, not first-Z depth. -/
theorem actual_stabilized (ps : List TetrahedralInputParity) (maxEvidence remaining : Nat) :
    stabilizedRawDescriptorState? (familyResult ps) (familyRaw ps) maxEvidence (familyFuel ps)
      (remaining + 1) (familyInitial ps) = some (familyInitial ps) := by
  simp [stabilizedRawDescriptorState?, discoverRawDescriptorsFromCertified,
    actual_pass_fixed ps maxEvidence]

theorem actual_unresolved_nil (ps : List TetrahedralInputParity) :
    (rawAnnotatedCenters (familyResult ps)).filter (fun index =>
      ((familyInitial ps).factAt? index).isNone) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro index member
  obtain ⟨_, taggedIndex⟩ := List.mem_filter.mp member
  have parsed : (familyResult ps).parsed = familyRaw ps := familyRaw_normalized_parsed ps
  rw [parsed] at taggedIndex
  cases observed : (familyRaw ps).atomAt? index with
  | none => simp [observed] at taggedIndex
  | some spec =>
      cases tagged : spec.tetrahedral? with
      | none => simp [observed, tagged] at taggedIndex
      | some parity =>
          obtain ⟨fact, found⟩ := seed_covers_observed_tag ps index spec parity observed tagged
          rw [found]
          simp

theorem actual_auxiliary_fixed (ps : List TetrahedralInputParity) (maxEvidence : Nat) :
    solveAuxiliaryDescriptorDependencies (familyResult ps) (familyRaw ps) maxEvidence
      (familyFuel ps) (familyInitial ps) = familyInitial ps := by
  simp [solveAuxiliaryDescriptorDependencies, actual_unresolved_nil ps,
    auxiliarySimultaneousDescriptorState]

theorem actual_exact_auxiliary_fixed (ps : List TetrahedralInputParity) (maxEvidence : Nat) :
    solveExactAuxiliaryDescriptorDependencies (familyResult ps) (familyRaw ps) maxEvidence
      (familyFuel ps) (familyInitial ps) = familyInitial ps := by
  simp [solveExactAuxiliaryDescriptorDependencies, actual_unresolved_nil ps]

theorem actual_finish_fixed (ps : List TetrahedralInputParity) :
    finishRawDescriptorSource (familyResult ps) (familyRaw ps) (familyFuel ps)
      (familyInitial ps) = familyInitial ps := by
  unfold finishRawDescriptorSource
  simp only [actual_unresolved_nil ps]
  split
  · rfl
  · exact actual_exact_auxiliary_fixed ps 100

theorem actual_constructive_fixed (ps : List TetrahedralInputParity) :
    constructiveRawDescriptorSourceValue (familyResult ps) (familyRaw ps) (familyFuel ps)
      (familyInitial ps) = familyInitial ps := by
  simp [constructiveRawDescriptorSourceValue, actual_stabilized ps,
    actual_auxiliary_fixed ps, retainLastStableRawDescriptorState, actual_finish_fixed ps]

private theorem actual_initial_nonempty (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyInitial ps).isEmpty = false := by
  have found := actual_seed_lookup ps i
  have member := List.mem_of_find?_eq_some found
  cases initial : familyInitial ps with
  | nil => rw [initial] at member; exact False.elim (List.not_mem_nil member)
  | cons first rest => rfl

theorem actual_source_selected (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    discoverRawDescriptorSource (familyResult ps) (familyRaw ps) (familyFuel ps) = familyInitial ps := by
  have initialNonempty : (initialRawDescriptorState (familyResult ps) (familyRaw ps)
      (familyFuel ps)).isEmpty = false := actual_initial_nonempty ps i
  unfold discoverRawDescriptorSource certifiedRawDescriptorSource
  simp only [initialNonempty, Bool.false_eq_true, ↓reduceIte]
  change constructiveRawDescriptorSourceValue (familyResult ps) (familyRaw ps)
    (familyFuel ps) (familyInitial ps) = _
  exact actual_constructive_fixed ps

theorem actual_rule6_neutral (ps : List TetrahedralInputParity) :
    normalizeTwoCyclicRule6AnchorCarrier (familyRaw ps) (familyFuel ps) (familyInitial ps) =
      familyInitial ps := by
  unfold normalizeTwoCyclicRule6AnchorCarrier
  have mapped := List.map_congr_left (l := familyInitial ps) (g := id)
    (f := fun fact => match exactTwoCyclicAnchorCarrierWitness? (familyRaw ps)
      (familyInitial ps) (familyFuel ps) fact.atom fact with
      | some true => { fact with descriptor := RS.swap fact.descriptor }
      | _ => fact) (by
        intro fact member
        have uppercase := (initial_fact_fields ps fact member).2
        simp [exactTwoCyclicAnchorCarrierWitness?, uppercase])
  simpa only [List.map_id] using mapped

/-- Whole production discovery at actual analysisFuel equals its internally computed seed state. -/
theorem actual_discovery_is_initial (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    discoverRawDescriptors (familyResult ps) (familyRaw ps) (familyFuel ps) = familyInitial ps := by
  rw [discoverRawDescriptors, actual_source_selected ps i]
  exact actual_rule6_neutral ps

/-- Actual final discovered fact: parity-derived descriptor and priority [2,0,3,1]. -/
theorem actual_discovered_tag (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (discoverRawDescriptors (familyResult ps) (familyRaw ps) (familyFuel ps)).factAt? (tagIndex i.val) =
      some (SecondSphereInitialSeedBridge.seedFact ps i) := by
  rw [actual_discovery_is_initial ps i]
  exact actual_seed_lookup ps i

end TetraStereo.UniversalProof.SecondSphereFamilyTrackedRanking
