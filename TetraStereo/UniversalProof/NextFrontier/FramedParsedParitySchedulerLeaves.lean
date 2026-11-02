import TetraStereo.UniversalProof.NextFrontier.FramedParsedParityScheduler
import TetraStereo.UniversalProof.NextFrontier.FramedParsedParitySchedulerCenter

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-! Off-tree candidate. Only the eight center guard leaves reduce an expensive assignment call.
Pass/fixed-point assembly is symbolic; full metadata and insertion order are retained. Observed
candidates are pinned in Root's parsed-parity-scheduler-observation-01 BUILD.log, not assumed true. -/
namespace TetraStereo.UniversalProof.FramedParsedParitySchedulerLeaves

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.FramedParsedParityFamily
open TetraStereo.UniversalProof.FramedParsedParitySeed
open TetraStereo.UniversalProof.FramedParsedParityScheduler
open TetraStereo.UniversalProof.FramedParsedParitySchedulerCenter

def stateD (center left right : TetrahedralInputParity) : RawDescriptorState :=
  expectedSeed left right ++ (centralCandidate center left right).toList

def remainingSchedule : List Nat := [2,3,4,5,6,7,8,9,10]

theorem parsedRaw_actual (center left right : TetrahedralInputParity) :
    familyMol? center left right = some (parsedRaw center left right) := by
  cases found : familyMol? center left right with
  | none =>
      have shape := family_structural center left right
      rw [found] at shape
      contradiction
  | some raw => simp only [parsedRaw, found, Option.getD_some]

theorem actual_initial (center left right : TetrahedralInputParity) :
    initialRawDescriptorState (actualResult center left right) (actualMol center left right)
      (actualFuel center left right) = expectedSeed left right := by
  have observed := actualInitial_eq_expected center left right
  unfold actualInitial? at observed
  rw [parsedRaw_actual] at observed
  change some (initialRawDescriptorState (actualResult center left right)
    (actualMol center left right) (actualFuel center left right)) = _ at observed
  exact Option.some.inj observed

/-- Cheap parser/normalization population leaf; no descriptor discovery is reduced. -/
theorem actual_atomCount (center left right : TetrahedralInputParity) :
    (actualResult center left right).parsed.atomCount = 11 := by
  cases center <;> cases left <;> cases right <;> decide +kernel

/-- Cheap metadata/annotation guards for the tail of the real increasing-index schedule. -/
theorem remaining_guards (center left right : TetrahedralInputParity) :
    remainingSchedule.all
      (updateNoopGuard (actualResult center left right) (stateD center left right)) = true := by
  cases center <;> cases left <;> cases right <;> decide +kernel

theorem index_zero_seed_guard (center left right : TetrahedralInputParity) :
    updateNoopGuard (actualResult center left right) (expectedSeed left right) 0 = true := by
  cases center <;> cases left <;> cases right <;> decide +kernel

theorem index_zero_stateD_guard (center left right : TetrahedralInputParity) :
    updateNoopGuard (actualResult center left right) (stateD center left right) 0 = true := by
  cases center <;> cases left <;> cases right <;> decide +kernel

theorem stateD_center_lookup (center left right : TetrahedralInputParity) :
    (stateD center left right).factAt? 1 = centralCandidate center left right := by
  cases center <;> cases left <;> cases right <;> decide +kernel

theorem stateD_remove_center (center left right : TetrahedralInputParity) :
    (stateD center left right).filter (fun fact => fact.atom != 1) = expectedSeed left right := by
  cases center <;> cases left <;> cases right <;> decide +kernel

theorem candidate_metadata (center left right : TetrahedralInputParity) (fact : RawDescriptorFact)
    (observed : centralCandidate center left right = some fact) :
    fact.atom = 1 ∧ fact.evidenceSize = 2 := by
  unfold centralCandidate at observed
  cases found : expectedFact? center left right with
  | none =>
      simp only [found, Option.map_none] at observed
      cases observed
  | some occurrence =>
      have equal : ({ atom := 1, descriptor := occurrence.descriptor, uppercase := occurrence.uppercase, evidenceSize := 2, decisiveRule? := none, descriptorDependentPairs := 2, priorityPositions := occurrence.priorityPositions } : RawDescriptorFact) = fact := by
        simpa only [found, Option.map_some, Option.some.injEq] using observed
      subst fact
      exact ⟨rfl, rfl⟩

/-- Appending an actual absent central candidate retains the full candidate state. -/
theorem insert_central_candidate (center left right : TetrahedralInputParity)
    (fact : RawDescriptorFact) (observed : centralCandidate center left right = some fact) :
    (expectedSeed left right).insertIfAbsent fact = stateD center left right := by
  have atom := (candidate_metadata center left right fact observed).1
  have absent := (expectedSeed_shape left right).2
  unfold RawDescriptorState.insertIfAbsent stateD
  rw [atom, absent, observed]
  all_goals rfl

theorem update_seed_center (center left right : TetrahedralInputParity) :
    updateRawDescriptorAt (actualResult center left right) (actualMol center left right) 100
      (actualFuel center left right) (expectedSeed left right) 1 = stateD center left right := by
  have absent := (expectedSeed_shape left right).2
  unfold updateRawDescriptorAt
  rw [absent, central_update_fact]
  cases candidate : centralCandidate center left right with
  | none => simp only [stateD, candidate, Option.toList_none, List.append_nil]
  | some fact => exact insert_central_candidate center left right fact candidate

theorem update_stateD_center (center left right : TetrahedralInputParity) :
    updateRawDescriptorAt (actualResult center left right) (actualMol center left right) 100
      (actualFuel center left right) (stateD center left right) 1 = stateD center left right := by
  unfold updateRawDescriptorAt
  rw [stateD_center_lookup]
  cases candidate : centralCandidate center left right with
  | none =>
      dsimp only []
      have same : stateD center left right = expectedSeed left right := by
        simp only [stateD, candidate, Option.toList_none, List.append_nil]
      rw [same, central_update_fact, candidate]
  | some fact =>
      dsimp only []
      have evidence := (candidate_metadata center left right fact candidate).2
      rw [evidence]
      change (match tetrahedralFactFromState? (actualResult center left right)
        (actualMol center left right)
        ((stateD center left right).filter fun known => known.atom != 1) 100
        (actualFuel center left right) 1 with
        | some newFact => RawDescriptorState.insertIfAbsent
            ((stateD center left right).filter fun known => known.atom != 1) newFact
        | none => (stateD center left right).filter fun known => known.atom != 1) = _
      rw [stateD_remove_center, central_update_fact, candidate]
      exact insert_central_candidate center left right fact candidate

theorem pass_seed_eq_stateD (center left right : TetrahedralInputParity) :
    runRawDescriptorDiscoveryPass (actualResult center left right) (actualMol center left right)
      100 (actualFuel center left right) (expectedSeed left right) = stateD center left right := by
  rw [discoveryPass_eq_schedule, actual_atomCount]
  have scheduleEq : List.range 11 = [0,1] ++ remainingSchedule := by decide
  rw [scheduleEq, discoverySchedule_append]
  have prefixRun : runRawDescriptorDiscoverySchedule (actualResult center left right)
      (actualMol center left right) 100 (actualFuel center left right) [0,1]
      (expectedSeed left right) = stateD center left right := by
    simp only [runRawDescriptorDiscoverySchedule, List.foldl_cons, List.foldl_nil]
    rw [updateRawDescriptorAt_of_noop_guard _ _ _ _ _ _ (index_zero_seed_guard center left right)]
    exact update_seed_center center left right
  rw [prefixRun]
  exact discoverySchedule_noop_of_guards _ _ _ _ _ _ (remaining_guards center left right)

theorem pass_stateD_eq_stateD (center left right : TetrahedralInputParity) :
    runRawDescriptorDiscoveryPass (actualResult center left right) (actualMol center left right)
      100 (actualFuel center left right) (stateD center left right) = stateD center left right := by
  rw [discoveryPass_eq_schedule, actual_atomCount]
  have scheduleEq : List.range 11 = [0,1] ++ remainingSchedule := by decide
  rw [scheduleEq, discoverySchedule_append]
  have prefixRun : runRawDescriptorDiscoverySchedule (actualResult center left right)
      (actualMol center left right) 100 (actualFuel center left right) [0,1]
      (stateD center left right) = stateD center left right := by
    simp only [runRawDescriptorDiscoverySchedule, List.foldl_cons, List.foldl_nil]
    rw [updateRawDescriptorAt_of_noop_guard _ _ _ _ _ _ (index_zero_stateD_guard center left right)]
    exact update_stateD_center center left right
  rw [prefixRun]
  exact discoverySchedule_noop_of_guards _ _ _ _ _ _ (remaining_guards center left right)

/-- Actual budget is twelve; this is symbolic assembly from the center leaves, not whole-run
finite reduction. Both the seed and D stabilize to the complete metadata state D. -/
theorem stabilized_from_seed (center left right : TetrahedralInputParity) :
    stabilizedRawDescriptorState? (actualResult center left right) (actualMol center left right) 100
      (actualFuel center left right) ((actualResult center left right).parsed.atomCount + 1)
      (expectedSeed left right) = some (stateD center left right) := by
  have fixed : runRawDescriptorDiscoveryPass (actualResult center left right)
      (actualMol center left right) 100 (actualFuel center left right)
      (runRawDescriptorDiscoveryPass (actualResult center left right) (actualMol center left right)
        100 (actualFuel center left right) (expectedSeed left right)) =
      runRawDescriptorDiscoveryPass (actualResult center left right) (actualMol center left right)
        100 (actualFuel center left right) (expectedSeed left right) := by
    exact (congrArg (fun state => runRawDescriptorDiscoveryPass (actualResult center left right)
      (actualMol center left right) 100 (actualFuel center left right) state)
      (pass_seed_eq_stateD center left right)).trans
        ((pass_stateD_eq_stateD center left right).trans
          (pass_seed_eq_stateD center left right).symm)
  have selfEq : (runRawDescriptorDiscoveryPass (actualResult center left right)
      (actualMol center left right) 100 (actualFuel center left right) (expectedSeed left right) ==
      runRawDescriptorDiscoveryPass (actualResult center left right) (actualMol center left right)
        100 (actualFuel center left right) (expectedSeed left right)) = true := by
    simp only [beq_self_eq_true]
  have accepted := stabilizedRawDescriptorState?_two_step (actualResult center left right)
    (actualMol center left right) 100 (actualFuel center left right)
    ((actualResult center left right).parsed.atomCount + 1) (expectedSeed left right)
    (by rw [actual_atomCount]; decide) fixed selfEq
  exact accepted.trans (congrArg some (pass_seed_eq_stateD center left right))

/-- D itself is accepted by the actual twelve-pass budget, with identical full metadata. -/
theorem stabilized_from_stateD (center left right : TetrahedralInputParity) :
    stabilizedRawDescriptorState? (actualResult center left right) (actualMol center left right) 100
      (actualFuel center left right) ((actualResult center left right).parsed.atomCount + 1)
      (stateD center left right) = some (stateD center left right) := by
  have fixed := pass_stateD_eq_stateD center left right
  have twice : runRawDescriptorDiscoveryPass (actualResult center left right)
      (actualMol center left right) 100 (actualFuel center left right)
      (runRawDescriptorDiscoveryPass (actualResult center left right) (actualMol center left right)
        100 (actualFuel center left right) (stateD center left right)) =
      runRawDescriptorDiscoveryPass (actualResult center left right) (actualMol center left right)
        100 (actualFuel center left right) (stateD center left right) := by
    exact congrArg (fun state => runRawDescriptorDiscoveryPass (actualResult center left right)
      (actualMol center left right) 100 (actualFuel center left right) state) fixed
  have selfEq : (runRawDescriptorDiscoveryPass (actualResult center left right)
      (actualMol center left right) 100 (actualFuel center left right) (stateD center left right) ==
      runRawDescriptorDiscoveryPass (actualResult center left right) (actualMol center left right)
        100 (actualFuel center left right) (stateD center left right)) = true := by
    simp only [beq_self_eq_true]
  have accepted := stabilizedRawDescriptorState?_two_step (actualResult center left right)
    (actualMol center left right) 100 (actualFuel center left right)
    ((actualResult center left right).parsed.atomCount + 1) (stateD center left right)
    (by rw [actual_atomCount]; decide) twice selfEq
  exact accepted.trans (congrArg some fixed)

/-- Public initial seed is the accepted independent seed, not a caller-supplied final state. -/
theorem stabilized_from_actual_initial (center left right : TetrahedralInputParity) :
    stabilizedRawDescriptorState? (actualResult center left right) (actualMol center left right) 100
      (actualFuel center left right) ((actualResult center left right).parsed.atomCount + 1)
      (initialRawDescriptorState (actualResult center left right) (actualMol center left right)
        (actualFuel center left right)) = some (stateD center left right) := by
  rw [actual_initial]
  exact stabilized_from_seed center left right

end TetraStereo.UniversalProof.FramedParsedParitySchedulerLeaves
