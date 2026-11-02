import TetraStereo.UniversalProof.NextFrontier.NativeNitrileInitialComparison
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileCertifiedIntake
import TetraStereo.UniversalProof.SecondSphereInitialSeedBridge

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileInitialSeed

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

def nitrileResult (n : Nat) (parity : TetrahedralInputParity) : ChemistryNormalizationResult :=
  normalizeRawMolecule (raw parity n)

def nitrileFuel (n : Nat) (parity : TetrahedralInputParity) : Nat := analysisFuel (expanded parity n)

theorem strict_comparison_of_z (n : Nat) (parity : TetrahedralInputParity)
    (left right leftZ rightZ : Nat)
    (observedLeft : (expanded parity n).atomZAt left = leftZ)
    (observedRight : (expanded parity n).atomZAt right = rightZ)
    (different : leftZ ≠ rightZ) :
    (expanded parity n).compareBranches? (nitrileFuel n parity) 0 left right =
      some (compare leftZ rightZ) := by
  rw [NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery.actual_legacy_strict_branch
    _ _ _ _ _ (by rwa [observedLeft, observedRight]), observedLeft, observedRight]

/-- Both production position consumers use the corrected first-atom written frame. The
normalization result in the Rule-3 consumer is arbitrary because every comparison is strict. -/
theorem actual_rank_positions (n : Nat) (parity : TetrahedralInputParity)
    (result : ChemistryNormalizationResult) :
    (expanded parity n).rankBranchPositions? (nitrileFuel n parity) 0
      ((expanded parity n).writtenNeighbors 0) = some [1, 2, 3, 0] ∧
    rankBranchPositionsThroughRule3? result (expanded parity n) (nitrileFuel n parity) 0
      ((expanded parity n).writtenNeighbors 0) = some [1, 2, 3, 0] := by
  rcases expanded_local_atomic_numbers parity n with ⟨_, fZ, lZ, _, rZ, _, _, hZ, _⟩
  have hf := strict_comparison_of_z n parity (n + 7) 1 1 9 hZ fZ (by decide)
  have hl := strict_comparison_of_z n parity (n + 7) 2 1 6 hZ lZ (by decide)
  have hr := strict_comparison_of_z n parity (n + 7) 4 1 6 hZ rZ (by decide)
  have fl := strict_comparison_of_z n parity 1 2 9 6 fZ lZ (by decide)
  have rh := strict_comparison_of_z n parity 4 (n + 7) 6 1 rZ hZ (by decide)
  change _ = some Ordering.lt at hf
  change _ = some Ordering.lt at hl
  change _ = some Ordering.lt at hr
  change _ = some Ordering.gt at fl
  change _ = some Ordering.gt at rh
  have lr := (actual_initial_compareBranches_both parity n).1
  change (expanded parity n).compareBranches? (nitrileFuel n parity) 0 2 4 = some .gt at lr
  have qhf := SecondSphereInitialSeedBridge.rule3_of_strict result _ _ 0 _ _ .lt hf (by decide)
  have qhl := SecondSphereInitialSeedBridge.rule3_of_strict result _ _ 0 _ _ .lt hl (by decide)
  have qhr := SecondSphereInitialSeedBridge.rule3_of_strict result _ _ 0 _ _ .lt hr (by decide)
  have qfl := SecondSphereInitialSeedBridge.rule3_of_strict result _ _ 0 _ _ .gt fl (by decide)
  have qrh := SecondSphereInitialSeedBridge.rule3_of_strict result _ _ 0 _ _ .gt rh (by decide)
  have qlr := SecondSphereInitialSeedBridge.rule3_of_strict result _ _ 0 _ _ .gt lr (by decide)
  rw [expanded_center_row]
  constructor
  · simp [rankBranchPositions?, compareBranches, sortDescBy, insertDescBy, List.range_succ,
      hf, hl, hr, fl, rh, lr]
  · simp [rankBranchPositionsThroughRule3?, sortDescBy, insertDescBy, List.range_succ,
      qhf, qhl, qhr, qfl, qrh, qlr]

theorem actual_root_ligands (n : Nat) (parity : TetrahedralInputParity) :
    (expanded parity n).ligandsWithLonePair 0 = (expanded parity n).writtenNeighbors 0 :=
  AuthoritativeCIPRule6Scheduler.ligandsWithLonePair_eq_writtenNeighbors_of_length_four
    _ _ (by rw [expanded_center_row]; rfl)

theorem priority_odd : permutationIsEven [1, 2, 3, 0] = false := by decide +kernel

theorem actual_legacy_outcome (n : Nat) (parity : TetrahedralInputParity) :
    (expanded parity n).tetrahedralOutcome (nitrileFuel n parity) 0 =
      .tetrahedral (descriptorOfParity parity false) := by
  have atom := expanded_original_atom parity n 0 _ (raw_center parity n)
  have rank := (actual_rank_positions n parity (nitrileResult n parity)).1
  have ligands := actual_root_ligands n parity
  have four : ((expanded parity n).writtenNeighbors 0).length = 4 := by
    rw [expanded_center_row]
    rfl
  simp [tetrahedralOutcome, atom, materializedAtomSpec, centerSpec, bracket,
    ligands, rank, four, priority_odd, centreElementSupported]

theorem actual_rule3_outcome (n : Nat) (parity : TetrahedralInputParity) :
    tetrahedralOutcomeThroughRule3 (nitrileResult n parity) (expanded parity n)
      (nitrileFuel n parity) 0 = .tetrahedral (descriptorOfParity parity false) := by
  simp only [tetrahedralOutcomeThroughRule3, actual_legacy_outcome]

def seedFact (parity : TetrahedralInputParity) : RawDescriptorFact :=
  { atom := 0, descriptor := descriptorOfParity parity false, uppercase := true,
    evidenceSize := 0, priorityPositions := [1, 2, 3, 0] }

def seedEntry (n : Nat) (parity : TetrahedralInputParity) (index : Nat) :
    Option RawDescriptorFact :=
  match tetrahedralOutcomeThroughRule3 (nitrileResult n parity) (expanded parity n)
      (nitrileFuel n parity) index with
  | .tetrahedral descriptor =>
      let positions := (rankBranchPositionsThroughRule3? (nitrileResult n parity)
        (expanded parity n) (nitrileFuel n parity) index
        ((expanded parity n).ligandsWithLonePair index)).getD []
      some ({ atom := index, descriptor := descriptor, uppercase := true, evidenceSize := 0,
              priorityPositions := positions } : RawDescriptorFact)
  | _ => none

theorem actual_seed_entry (n : Nat) (parity : TetrahedralInputParity) :
    seedEntry n parity 0 = some (seedFact parity) := by
  simp only [seedEntry, actual_rule3_outcome, actual_root_ligands,
    (actual_rank_positions n parity (nitrileResult n parity)).2, Option.getD_some]
  rfl

theorem seed_entry_fields (n : Nat) (parity : TetrahedralInputParity) (index : Nat)
    (fact : RawDescriptorFact) (computed : seedEntry n parity index = some fact) :
    fact.atom = index ∧ fact.evidenceSize = 0 ∧ fact.uppercase = true := by
  unfold seedEntry at computed
  cases outcome : tetrahedralOutcomeThroughRule3 (nitrileResult n parity) (expanded parity n)
    (nitrileFuel n parity) index <;> simp_all
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

def nitrileInitial (n : Nat) (parity : TetrahedralInputParity) : RawDescriptorState :=
  initialRawDescriptorState (nitrileResult n parity) (expanded parity n) (nitrileFuel n parity)

theorem initial_eq_entries (n : Nat) (parity : TetrahedralInputParity) :
    nitrileInitial n parity =
      (List.range (nitrileResult n parity).parsed.atomCount).filterMap (seedEntry n parity) := rfl

/-- Actual initial seed lookup at the atom introduced first by the parser, for every chain length
and either input parity. The priority and evidence fields are computed by production. -/
theorem actual_initial_seed_lookup (n : Nat) (parity : TetrahedralInputParity) :
    (nitrileInitial n parity).factAt? 0 = some (seedFact parity) := by
  change ((List.range (nitrileResult n parity).parsed.atomCount).filterMap
    (seedEntry n parity)).find? (fun candidate => candidate.atom == 0) = _
  apply find_filterMap_entry (seedEntry n parity)
    (fun index fact computed => (seed_entry_fields n parity index fact computed).1)
    _ 0 _ (actual_seed_entry n parity)
  rw [nitrileResult, raw_normalized_parsed, raw_atomCount]
  exact List.mem_range.mpr (by omega)

theorem actual_normalized_materialization (n : Nat) (parity : TetrahedralInputParity) :
    (nitrileResult n parity).parsed.withExplicitHydrogens = expanded parity n := by
  rw [nitrileResult, raw_normalized_parsed]
  rfl

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileInitialSeed
