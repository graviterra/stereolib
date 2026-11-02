import TetraStereo.UniversalProof.NextFrontier.FramedParsedParitySeed
import TetraStereo.UniversalProof.NextFrontier.FramedParsedParityFamily
import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
















































namespace TetraStereo.UniversalProof.FramedParsedParityScheduler

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.FramedParsedParityFamily
open TetraStereo.UniversalProof.FramedParsedParitySeed

/-- The production discovery evidence budget used by the maintained auxiliary solver. -/
def discoveryEvidenceSize : ℕ := 100

/-- The actual normalization result of the member string. -/
def schedulerResult? (center leftArm rightArm : TetrahedralInputParity) :
    Option ChemistryNormalizationResult :=
  (familyMol? center leftArm rightArm).map normalizeRawMolecule

/-- The actual expanded molecule discovery runs on (explicit hydrogens materialized). -/
def schedulerMol? (center leftArm rightArm : TetrahedralInputParity) : Option RawMolecule :=
  (schedulerResult? center leftArm rightArm).map (fun result => result.parsed.withExplicitHydrogens)

/-- The actual public discovery input; it is definitionally the accepted seed input. -/
def schedulerSeed? (center leftArm rightArm : TetrahedralInputParity) : Option RawDescriptorState :=
  actualInitial? center leftArm rightArm

/-- One actual left-to-right descriptor-discovery pass from the seed. -/
def schedulerPass? (center leftArm rightArm : TetrahedralInputParity) : Option RawDescriptorState :=
  match schedulerResult? center leftArm rightArm, schedulerMol? center leftArm rightArm,
        schedulerSeed? center leftArm rightArm with
  | some result, some mol, some seed =>
      some (runRawDescriptorDiscoveryPass result mol discoveryEvidenceSize (analysisFuel mol) seed)
  | _, _, _ => none

/-- The actual-budget stabilization gate from the seed (`remaining = atomCount + 1 = 12`). -/
def schedulerFixed? (center leftArm rightArm : TetrahedralInputParity) : Option RawDescriptorState :=
  match schedulerResult? center leftArm rightArm, schedulerMol? center leftArm rightArm,
        schedulerSeed? center leftArm rightArm with
  | some result, some mol, some seed =>
      stabilizedRawDescriptorState? result mol discoveryEvidenceSize (analysisFuel mol)
        (result.parsed.atomCount + 1) seed
  | _, _, _ => none

/-! ## Seed bridge (uses the accepted independent seed, no recomputation) -/

/-- The actual public discovery input equals the independent two-fact seed for all eight members. -/
theorem schedulerSeed_eq_expected (center leftArm rightArm : TetrahedralInputParity) :
    schedulerSeed? center leftArm rightArm = some (expectedSeed leftArm rightArm) := by
  unfold schedulerSeed?
  exact actualInitial_eq_expected center leftArm rightArm

/-- The chosen central written parity cannot change the two independent arm seeds. -/
theorem schedulerSeed_center_independent (first second leftArm rightArm : TetrahedralInputParity) :
    schedulerSeed? first leftArm rightArm = schedulerSeed? second leftArm rightArm := by
  rw [schedulerSeed_eq_expected, schedulerSeed_eq_expected]

/-! ## General structural scheduler primitives -/

/-- Schedule composition: splitting a schedule concatenates the corresponding updates in order. -/
theorem discoverySchedule_append (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) (first second : List ℕ) (state : RawDescriptorState) :
    runRawDescriptorDiscoverySchedule result mol maxEvidenceSize fuel (first ++ second) state =
      runRawDescriptorDiscoverySchedule result mol maxEvidenceSize fuel second
        (runRawDescriptorDiscoverySchedule result mol maxEvidenceSize fuel first state) := by
  simp only [runRawDescriptorDiscoverySchedule]
  exact List.foldl_append

/-- The maintained pass is definitionally its canonical increasing-index schedule. -/
theorem discoveryPass_eq_schedule (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) (state : RawDescriptorState) :
    runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel state =
      runRawDescriptorDiscoverySchedule result mol maxEvidenceSize fuel
        (List.range result.parsed.atomCount) state := rfl

/-- One maintained center update is a no-op on an already-known `evidenceSize = 0` seed fact:
the Rule-1–3 finality contract freezes the two independent arm seeds. -/
theorem updateRawDescriptorAt_frozen (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) (current : RawDescriptorState) (idx : ℕ)
    (existing : RawDescriptorFact) (lookup : current.factAt? idx = some existing)
    (seed : existing.evidenceSize = 0) :
    updateRawDescriptorAt result mol maxEvidenceSize fuel current idx = current := by
  unfold updateRawDescriptorAt
  rw [lookup]
  simp [seed]

/-- A whole schedule whose every visited atom already carries a frozen seed fact is a literal
no-op: order and every field are preserved. -/
theorem discoverySchedule_frozen_noop (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel : ℕ) (schedule : List ℕ) :
    ∀ state : RawDescriptorState,
      (∀ idx ∈ schedule, ∃ existing,
        state.factAt? idx = some existing ∧ existing.evidenceSize = 0) →
      runRawDescriptorDiscoverySchedule result mol maxEvidenceSize fuel schedule state = state := by
  induction schedule with
  | nil => intro state _; rfl
  | cons idx rest ih =>
      intro state frozen
      have hidx := frozen idx (by simp)
      have hrest : ∀ j ∈ rest, ∃ existing,
          state.factAt? j = some existing ∧ existing.evidenceSize = 0 :=
        fun j hj => frozen j (by simp [hj])
      simp only [runRawDescriptorDiscoverySchedule]
      rw [List.foldl_cons,
        updateRawDescriptorAt_frozen result mol maxEvidenceSize fuel state idx
          hidx.choose hidx.choose_spec.1 hidx.choose_spec.2]
      simpa only [runRawDescriptorDiscoverySchedule] using ih state hrest

/-- The stabilization gate returns exactly the run state whenever the run reports stabilization. -/
theorem stabilizedRawDescriptorState?_some_of_stabilized
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel remaining : ℕ) (state : RawDescriptorState)
    (stabilized :
      (discoverRawDescriptorsFromCertified result mol maxEvidenceSize fuel remaining state).stabilized =
        true) :
    stabilizedRawDescriptorState? result mol maxEvidenceSize fuel remaining state =
      some (discoverRawDescriptorsFromCertified result mol maxEvidenceSize fuel remaining state).state := by
  dsimp only [stabilizedRawDescriptorState?]
  rw [stabilized]
  rfl

/-- Cheap update admission: a stored constitutional seed is frozen; an absent untagged
parsed index cannot acquire a tetrahedral fact. No expensive descriptor comparison is performed. -/
def updateNoopGuard (result : ChemistryNormalizationResult) (state : RawDescriptorState)
    (idx : ℕ) : Bool :=
  match state.factAt? idx with
  | some existing => existing.evidenceSize == 0
  | none => (result.parsed.atomAt? idx).all fun spec => spec.tetrahedral?.isNone

theorem updateRawDescriptorAt_of_noop_guard (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (maxEvidenceSize fuel : ℕ) (state : RawDescriptorState) (idx : ℕ)
    (guard : updateNoopGuard result state idx = true) :
    updateRawDescriptorAt result mol maxEvidenceSize fuel state idx = state := by
  cases lookup : state.factAt? idx with
  | some existing =>
      have frozen : existing.evidenceSize = 0 := by
        have observed : (existing.evidenceSize == 0) = true := by
          simpa only [updateNoopGuard, lookup] using guard
        exact beq_iff_eq.mp observed
      exact updateRawDescriptorAt_frozen result mol maxEvidenceSize fuel state idx existing
        lookup frozen
  | none =>
      have untagged : (result.parsed.atomAt? idx).all
          (fun spec => spec.tetrahedral?.isNone) = true := by
        simpa only [updateNoopGuard, lookup] using guard
      have absent : tetrahedralFactFromState? result mol state maxEvidenceSize fuel idx = none := by
        cases atomObserved : result.parsed.atomAt? idx with
        | none => simp only [tetrahedralFactFromState?, atomObserved]
        | some spec =>
            rw [atomObserved] at untagged
            change spec.tetrahedral?.isNone = true at untagged
            simp [tetrahedralFactFromState?, atomObserved, untagged]
      simp only [updateRawDescriptorAt, lookup, absent]

theorem discoverySchedule_noop_of_guards (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (maxEvidenceSize fuel : ℕ) (schedule : List ℕ)
    (state : RawDescriptorState)
    (guards : schedule.all (updateNoopGuard result state) = true) :
    runRawDescriptorDiscoverySchedule result mol maxEvidenceSize fuel schedule state = state := by
  revert guards
  induction schedule with
  | nil => intro _; rfl
  | cons idx rest ih =>
      intro guards
      have checks : updateNoopGuard result state idx = true ∧
          rest.all (updateNoopGuard result state) = true := by
        simpa only [List.all_cons, Bool.and_eq_true] using guards
      change rest.foldl (updateRawDescriptorAt result mol maxEvidenceSize fuel)
        (updateRawDescriptorAt result mol maxEvidenceSize fuel state idx) = state
      rw [updateRawDescriptorAt_of_noop_guard result mol maxEvidenceSize fuel state idx checks.1]
      exact ih checks.2

/-! ## General exact seed-to-fixed two-step equations -/

/-- Two actual pass observations identify the FULL accepted run, including list order and every
fact metadata field. No desired final state is a premise. The first-pass state is the maintained
pass itself; equality of its next pass is a primitive fixed-point observation. -/
theorem discoverFromCertified_two_step_run
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel remaining : ℕ) (seed : RawDescriptorState)
    (budget : 2 ≤ remaining)
    (fixed : runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel
        (runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel seed) =
      runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel seed)
    (selfEq : (runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel seed ==
        runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel seed) = true) :
    discoverRawDescriptorsFromCertified result mol maxEvidenceSize fuel remaining seed =
      { state := runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel seed,
        stabilized := true } := by
  cases remaining with
  | zero => omega
  | succ n =>
      cases n with
      | zero => omega
      | succ m =>
          change (if runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel seed == seed then
            { state := seed, stabilized := true }
            else discoverRawDescriptorsFromCertified result mol maxEvidenceSize fuel (m + 1)
              (runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel seed)) = _
          split
          · rename_i stopped
            have same : runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel seed = seed :=
              beq_iff_eq.mp stopped
            exact congrArg (fun state : RawDescriptorState =>
              ({ state := state, stabilized := true } : RawDescriptorDiscoveryRun)) same.symm
          · change (if runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel
                (runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel seed) ==
                runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel seed then
              { state := runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel seed,
                stabilized := true }
              else discoverRawDescriptorsFromCertified result mol maxEvidenceSize fuel m
                (runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel
                  (runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel seed))) = _
            rw [fixed, selfEq]
            rfl

/-- Compatibility theorem: the accepted exact two-step run has its stabilization bit set. -/
theorem discoverFromCertified_two_step_stabilizes
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel remaining : ℕ) (seed : RawDescriptorState)
    (budget : 2 ≤ remaining)
    (fixed : runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel
        (runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel seed) =
      runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel seed)
    (selfEq : (runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel seed ==
        runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel seed) = true) :
    (discoverRawDescriptorsFromCertified result mol maxEvidenceSize fuel remaining seed).stabilized =
      true := by
  have run := discoverFromCertified_two_step_run result mol maxEvidenceSize fuel remaining seed
    budget fixed selfEq
  exact congrArg RawDescriptorDiscoveryRun.stabilized run

/-- The actual-budget Option gate returns the full first-pass state under the same primitives. -/
theorem stabilizedRawDescriptorState?_two_step
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (maxEvidenceSize fuel remaining : ℕ) (seed : RawDescriptorState)
    (budget : 2 ≤ remaining)
    (fixed : runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel
        (runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel seed) =
      runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel seed)
    (selfEq : (runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel seed ==
        runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel seed) = true) :
    stabilizedRawDescriptorState? result mol maxEvidenceSize fuel remaining seed =
      some (runRawDescriptorDiscoveryPass result mol maxEvidenceSize fuel seed) := by
  have run := discoverFromCertified_two_step_run result mol maxEvidenceSize fuel remaining seed
    budget fixed selfEq
  dsimp only [stabilizedRawDescriptorState?]
  rw [run]
  rfl

/-! Actual family observations and bounded computation leaves are separate modules, so this
structural helper can be gated without executing those leaves. -/

#check schedulerSeed_eq_expected
#check discoverySchedule_append
#check updateRawDescriptorAt_frozen
#check discoverySchedule_frozen_noop
#check stabilizedRawDescriptorState?_some_of_stabilized
#check discoverFromCertified_two_step_stabilizes

end TetraStereo.UniversalProof.FramedParsedParityScheduler
