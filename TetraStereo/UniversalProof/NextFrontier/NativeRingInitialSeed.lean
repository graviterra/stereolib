import TetraStereo.UniversalProof.NextFrontier.NativeRingInitialComparison

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingInitialSeed

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRingDomain
open TetraStereo.UniversalProof.GeneralRingPhysicalAdmission
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.NativeRingRuntimeAtoms
open TetraStereo.UniversalProof.NativeRingInitialComparison

def ringResult (n : Nat) (parity : TetrahedralInputParity) : ChemistryNormalizationResult :=
  normalizeRawMolecule (ringRaw n parity)

def ringFuel (n : Nat) (parity : TetrahedralInputParity) : Nat := analysisFuel (expanded n parity)

theorem strict_comparison_of_z (n : Nat) (parity : TetrahedralInputParity)
    (left right leftZ rightZ : Nat)
    (observedLeft : (expanded n parity).atomZAt left = leftZ)
    (observedRight : (expanded n parity).atomZAt right = rightZ)
    (different : leftZ ≠ rightZ) :
    (expanded n parity).compareBranches? (ringFuel n parity) 0 left right =
      some (compare leftZ rightZ) := by
  rw [NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery.actual_legacy_strict_branch
    _ _ _ _ _ (by rwa [observedLeft, observedRight]), observedLeft, observedRight]

/-- Both production position consumers use the corrected first-atom written frame. The
normalization result in the Rule-3 consumer is arbitrary because every comparison is strict. -/
theorem actual_rank_positions (n : Nat) (parity : TetrahedralInputParity)
    (result : ChemistryNormalizationResult) :
    (expanded n parity).rankBranchPositions? (ringFuel n parity) 0
      ((expanded n parity).writtenNeighbors 0) = some [1, 2, 3, 0] ∧
    rankBranchPositionsThroughRule3? result (expanded n parity) (ringFuel n parity) 0
      ((expanded n parity).writtenNeighbors 0) = some [1, 2, 3, 0] := by
  have hZ := expanded_hydrogen_z n parity (n + 5) (by omega) (by omega)
  have fZ := expanded_fluorine_z n parity
  have lZ := expanded_left_z n parity
  have rZ := expanded_chain_z n parity n (by omega)
  have hf := strict_comparison_of_z n parity (n + 5) 1 1 9 hZ fZ (by decide)
  have hl := strict_comparison_of_z n parity (n + 5) 2 1 6 hZ lZ (by decide)
  have hr := strict_comparison_of_z n parity (n + 5) (n + 4) 1 6 hZ rZ (by decide)
  have fl := strict_comparison_of_z n parity 1 2 9 6 fZ lZ (by decide)
  have rh := strict_comparison_of_z n parity (n + 4) (n + 5) 6 1 rZ hZ (by decide)
  change _ = some Ordering.lt at hf
  change _ = some Ordering.lt at hl
  change _ = some Ordering.lt at hr
  change _ = some Ordering.gt at fl
  change _ = some Ordering.gt at rh
  have lr := (actual_compareBranches_both n parity).1
  change (expanded n parity).compareBranches? (ringFuel n parity) 0 2 (n + 4) = some .gt at lr
  have qhf := SecondSphereInitialSeedBridge.rule3_of_strict result _ _ 0 _ _ .lt hf (by decide)
  have qhl := SecondSphereInitialSeedBridge.rule3_of_strict result _ _ 0 _ _ .lt hl (by decide)
  have qhr := SecondSphereInitialSeedBridge.rule3_of_strict result _ _ 0 _ _ .lt hr (by decide)
  have qfl := SecondSphereInitialSeedBridge.rule3_of_strict result _ _ 0 _ _ .gt fl (by decide)
  have qrh := SecondSphereInitialSeedBridge.rule3_of_strict result _ _ 0 _ _ .gt rh (by decide)
  have qlr := SecondSphereInitialSeedBridge.rule3_of_strict result _ _ 0 _ _ .gt lr (by decide)
  rw [expanded_root_written_row]
  constructor
  · simp [rankBranchPositions?, compareBranches, sortDescBy, insertDescBy, List.range_succ,
      hf, hl, hr, fl, rh, lr]
  · simp [rankBranchPositionsThroughRule3?, sortDescBy, insertDescBy, List.range_succ,
      qhf, qhl, qhr, qfl, qrh, qlr]

theorem actual_root_ligands (n : Nat) (parity : TetrahedralInputParity) :
    (expanded n parity).ligandsWithLonePair 0 = (expanded n parity).writtenNeighbors 0 :=
  AuthoritativeCIPRule6Scheduler.ligandsWithLonePair_eq_writtenNeighbors_of_length_four
    _ _ (by rw [expanded_root_written_row]; rfl)

theorem priority_odd : permutationIsEven [1, 2, 3, 0] = false := by decide +kernel

theorem actual_legacy_outcome (n : Nat) (parity : TetrahedralInputParity) :
    (expanded n parity).tetrahedralOutcome (ringFuel n parity) 0 =
      .tetrahedral (descriptorOfParity parity false) := by
  have atom := expanded_original_atom n parity 0 _ (ringRaw_atomAt_zero n parity)
  have rank := (actual_rank_positions n parity (ringResult n parity)).1
  have ligands := actual_root_ligands n parity
  have four : ((expanded n parity).writtenNeighbors 0).length = 4 := by
    rw [expanded_root_written_row]
    rfl
  simp [tetrahedralOutcome, atom, materializedAtomSpec, taggedCarbon, carbon,
    ligands, rank, four, priority_odd, centreElementSupported, AtomSpec.aliphatic]

theorem actual_rule3_outcome (n : Nat) (parity : TetrahedralInputParity) :
    tetrahedralOutcomeThroughRule3 (ringResult n parity) (expanded n parity)
      (ringFuel n parity) 0 = .tetrahedral (descriptorOfParity parity false) := by
  simp only [tetrahedralOutcomeThroughRule3, actual_legacy_outcome]

def seedFact (parity : TetrahedralInputParity) : RawDescriptorFact :=
  { atom := 0, descriptor := descriptorOfParity parity false, uppercase := true,
    evidenceSize := 0, priorityPositions := [1, 2, 3, 0] }

def seedEntry (n : Nat) (parity : TetrahedralInputParity) (index : Nat) :
    Option RawDescriptorFact :=
  match tetrahedralOutcomeThroughRule3 (ringResult n parity) (expanded n parity)
      (ringFuel n parity) index with
  | .tetrahedral descriptor =>
      let positions := (rankBranchPositionsThroughRule3? (ringResult n parity)
        (expanded n parity) (ringFuel n parity) index
        ((expanded n parity).ligandsWithLonePair index)).getD []
      some ({ atom := index, descriptor := descriptor, uppercase := true, evidenceSize := 0,
              priorityPositions := positions } : RawDescriptorFact)
  | _ => none

theorem actual_seed_entry (n : Nat) (parity : TetrahedralInputParity) :
    seedEntry n parity 0 = some (seedFact parity) := by
  simp only [seedEntry, actual_rule3_outcome, actual_root_ligands,
    (actual_rank_positions n parity (ringResult n parity)).2, Option.getD_some]
  rfl

theorem seed_entry_fields (n : Nat) (parity : TetrahedralInputParity) (index : Nat)
    (fact : RawDescriptorFact) (computed : seedEntry n parity index = some fact) :
    fact.atom = index ∧ fact.evidenceSize = 0 ∧ fact.uppercase = true := by
  unfold seedEntry at computed
  cases outcome : tetrahedralOutcomeThroughRule3 (ringResult n parity) (expanded n parity)
    (ringFuel n parity) index <;> simp_all
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

def ringInitial (n : Nat) (parity : TetrahedralInputParity) : RawDescriptorState :=
  initialRawDescriptorState (ringResult n parity) (expanded n parity) (ringFuel n parity)

theorem initial_eq_entries (n : Nat) (parity : TetrahedralInputParity) :
    ringInitial n parity =
      (List.range (ringResult n parity).parsed.atomCount).filterMap (seedEntry n parity) := rfl

/-- Actual initial seed lookup at the atom introduced first by the parser, for every ring size
and either input parity. The priority and evidence fields are computed by production. -/
theorem actual_initial_seed_lookup (n : Nat) (parity : TetrahedralInputParity) :
    (ringInitial n parity).factAt? 0 = some (seedFact parity) := by
  change ((List.range (ringResult n parity).parsed.atomCount).filterMap
    (seedEntry n parity)).find? (fun candidate => candidate.atom == 0) = _
  apply find_filterMap_entry (seedEntry n parity)
    (fun index fact computed => (seed_entry_fields n parity index fact computed).1)
    _ 0 _ (actual_seed_entry n parity)
  rw [ringResult, ringRaw_normalized_parsed, atom_count]
  exact List.mem_range.mpr (by omega)

theorem actual_normalized_materialization (n : Nat) (parity : TetrahedralInputParity) :
    (ringResult n parity).parsed.withExplicitHydrogens = expanded n parity := by
  rw [ringResult, ringRaw_normalized_parsed]
  rfl

end TetraStereo.UniversalProof.NativeRingInitialSeed
