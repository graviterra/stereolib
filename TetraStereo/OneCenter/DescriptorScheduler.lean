import TetraStereo.OneCenter.DescriptorDiscovery

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {m : MultiCenterMolecule V} {cfg : m.Configuration}

namespace Rule5DiscoveryTask

variable (task : Rule5DiscoveryTask m cfg)

theorem resolveFromState?_eq_of_rs_eq {state₁ state₂ : DescriptorDiscoveryState m cfg}
    (h : state₁.rs = state₂.rs) :
    task.resolveFromState? state₁ = task.resolveFromState? state₂ := by
  simp [Rule5DiscoveryTask.resolveFromState?, h]

end Rule5DiscoveryTask

namespace DescriptorDiscoveryState

@[simp] theorem applyRule5Task_rs (state : DescriptorDiscoveryState m cfg)
    (task : Rule5DiscoveryTask m cfg) :
    (state.applyRule5Task task).rs = state.rs := by
  cases h : task.resolveFromState? state with
  | none => simp [applyRule5Task, h]
  | some result => simp [applyRule5Task, h]

theorem applyRule5Task_pseudo_of_center_ne (state : DescriptorDiscoveryState m cfg)
    (task : Rule5DiscoveryTask m cfg) {center : m.Center} (hcenter : center ≠ task.center) :
    (state.applyRule5Task task).pseudo center = state.pseudo center := by
  cases h : task.resolveFromState? state with
  | none => simp [applyRule5Task, h]
  | some result => simp [applyRule5Task, h, assignPseudo_pseudo_of_ne, hcenter]

/-- Assignments at distinct centers commute exactly. -/
theorem assignPseudo_commute_of_center_ne (state : DescriptorDiscoveryState m cfg)
    {left right : m.Center} (leftDescriptor rightDescriptor : PseudoRS)
    (hne : left ≠ right) :
    (state.assignPseudo left leftDescriptor).assignPseudo right rightDescriptor =
      (state.assignPseudo right rightDescriptor).assignPseudo left leftDescriptor := by
  cases state with
  | mk rs pseudo =>
      simp only [assignPseudo]
      congr
      funext center
      by_cases hleft : center = left
      · subst center
        simp [hne]
      · by_cases hright : center = right
        · subst center
          simp [hleft]
        · simp [hleft, hright]

theorem runRule5Tasks_rs (state : DescriptorDiscoveryState m cfg)
    (tasks : List (Rule5DiscoveryTask m cfg)) :
    (state.runRule5Tasks tasks).rs = state.rs := by
  induction tasks generalizing state with
  | nil => rfl
  | cons task tasks ih =>
      change ((state.applyRule5Task task).runRule5Tasks tasks).rs = state.rs
      rw [ih, DescriptorDiscoveryState.applyRule5Task_rs]

theorem applyRule5Task_resolveFromState?_eq (state : DescriptorDiscoveryState m cfg)
    (applied task : Rule5DiscoveryTask m cfg) :
    task.resolveFromState? (state.applyRule5Task applied) = task.resolveFromState? state := by
  exact task.resolveFromState?_eq_of_rs_eq (DescriptorDiscoveryState.applyRule5Task_rs state applied)



theorem applyRule5Task_commute_of_center_ne (state : DescriptorDiscoveryState m cfg)
    (left right : Rule5DiscoveryTask m cfg) (hne : left.center ≠ right.center) :
    (state.applyRule5Task left).applyRule5Task right =
      (state.applyRule5Task right).applyRule5Task left := by
  have rightResolution :=
    DescriptorDiscoveryState.applyRule5Task_resolveFromState?_eq state left right
  have leftResolution :=
    DescriptorDiscoveryState.applyRule5Task_resolveFromState?_eq state right left
  cases hleft : left.resolveFromState? state with
  | none =>
      simp only [DescriptorDiscoveryState.applyRule5Task, hleft] at leftResolution ⊢
      simp only [leftResolution]
  | some leftResult =>
      cases hright : right.resolveFromState? state with
      | none =>
          simp only [DescriptorDiscoveryState.applyRule5Task, hleft, hright] at rightResolution ⊢
          simp only [rightResolution]
      | some rightResult =>
          simp only [DescriptorDiscoveryState.applyRule5Task, hleft, hright] at rightResolution
          simp only [DescriptorDiscoveryState.applyRule5Task, hleft, hright] at leftResolution
          simp only [DescriptorDiscoveryState.applyRule5Task, hleft, hright]
          simp only [rightResolution, leftResolution]
          exact DescriptorDiscoveryState.assignPseudo_commute_of_center_ne
            state leftResult.descriptor rightResult.descriptor hne

theorem runRule5Tasks_resolveFromState?_eq (state : DescriptorDiscoveryState m cfg)
    (tasks : List (Rule5DiscoveryTask m cfg)) (task : Rule5DiscoveryTask m cfg) :
    task.resolveFromState? (state.runRule5Tasks tasks) = task.resolveFromState? state := by
  exact task.resolveFromState?_eq_of_rs_eq (DescriptorDiscoveryState.runRule5Tasks_rs state tasks)




theorem runRule5Tasks_eq_of_perm_of_targetsNodup
    (state : DescriptorDiscoveryState m cfg)
    {left right : List (Rule5DiscoveryTask m cfg)}
    (permutation : left.Perm right)
    (targetsNodup : (left.map fun task => task.center).Nodup) :
    state.runRule5Tasks left = state.runRule5Tasks right := by
  induction permutation generalizing state with
  | nil => rfl
  | @cons task left right permutation inductionHypothesis =>
      simp only [runRule5Tasks, List.foldl_cons]
      apply inductionHypothesis
      exact targetsNodup.tail
  | @swap first second rest =>
      simp only [List.map_cons, List.nodup_cons] at targetsNodup
      have reverseCentersNe : second.center ≠ first.center := by
        intro equal
        apply targetsNodup.1
        simp [equal]
      have centersNe : first.center ≠ second.center := by
        exact Ne.symm reverseCentersNe
      simp only [runRule5Tasks, List.foldl_cons]
      rw [DescriptorDiscoveryState.applyRule5Task_commute_of_center_ne
        state first second centersNe]
  | @trans first middle last firstMiddle middleLast firstMiddleIH middleLastIH =>
      have middleNodup : (middle.map fun task => task.center).Nodup := by
        exact (firstMiddle.map fun task => task.center).nodup targetsNodup
      exact (firstMiddleIH state targetsNodup).trans (middleLastIH state middleNodup)

theorem runRule5Tasks_pseudo_of_forall_center_ne (state : DescriptorDiscoveryState m cfg)
    (tasks : List (Rule5DiscoveryTask m cfg)) (center : m.Center)
    (hcenter : ∀ task, task ∈ tasks → center ≠ task.center) :
    (state.runRule5Tasks tasks).pseudo center = state.pseudo center := by
  induction tasks generalizing state with
  | nil => rfl
  | cons task tasks ih =>
      have htask : center ≠ task.center := hcenter task (by simp)
      have htail : ∀ task', task' ∈ tasks → center ≠ task'.center := by
        intro task' hmem
        exact hcenter task' (by simp [hmem])
      change ((state.applyRule5Task task).runRule5Tasks tasks).pseudo center =
        state.pseudo center
      rw [ih (state.applyRule5Task task) htail]
      exact DescriptorDiscoveryState.applyRule5Task_pseudo_of_center_ne state task htask


def Rule5TargetsNodup (tasks : List (Rule5DiscoveryTask m cfg)) : Prop :=
  (tasks.map fun task => task.center).Nodup

theorem runRule5Tasks_fixedPoint_of_targetsNodup
    (state : DescriptorDiscoveryState m cfg) (tasks : List (Rule5DiscoveryTask m cfg))
    (hnodup : Rule5TargetsNodup tasks) :
    (state.runRule5Tasks tasks).FixedPointForRule5Tasks tasks := by
  induction tasks generalizing state with
  | nil =>
      intro task hmem
      simp at hmem
  | cons hd tasks ih =>
      intro query hmem
      dsimp [Rule5TargetsNodup] at hnodup
      simp at hnodup
      rcases hnodup with ⟨hnotMemHead, hnodupTail⟩
      simp at hmem
      rcases hmem with rfl | hquery
      · intro result hresolveFinal
        have hresolveState : query.resolveFromState? state = some result := by
          have hrun := DescriptorDiscoveryState.runRule5Tasks_resolveFromState?_eq
            (state.applyRule5Task query) tasks query
          have happly := DescriptorDiscoveryState.applyRule5Task_resolveFromState?_eq
            state query query
          change query.resolveFromState? ((state.applyRule5Task query).runRule5Tasks tasks) =
            some result at hresolveFinal
          rw [hrun] at hresolveFinal
          rw [happly] at hresolveFinal
          exact hresolveFinal
        have hassigned :
            (state.applyRule5Task query).pseudo query.center = some result.descriptor :=
          DescriptorDiscoveryState.applyRule5Task_pseudo_eq_some_of_resolveFromState?_eq_some
            (state := state) (task := query) (result := result) hresolveState
        have hnoLater : ∀ later, later ∈ tasks → query.center ≠ later.center := by
          intro later hlater heq
          exact hnotMemHead later hlater heq.symm
        have hpreserve := DescriptorDiscoveryState.runRule5Tasks_pseudo_of_forall_center_ne
          (state.applyRule5Task query) tasks query.center hnoLater
        change ((state.applyRule5Task query).runRule5Tasks tasks).pseudo query.center =
          some result.descriptor
        rw [hpreserve, hassigned]
      · exact ih (state.applyRule5Task hd) hnodupTail query hquery


theorem applyRule5Task_eq_of_stable
    (state : DescriptorDiscoveryState m cfg) (task : Rule5DiscoveryTask m cfg)
    (stable : state.StableForRule5Task task) :
    state.applyRule5Task task = state := by
  cases resolved : task.resolveFromState? state with
  | none => simp [DescriptorDiscoveryState.applyRule5Task, resolved]
  | some result =>
      have known := stable result resolved
      simp only [DescriptorDiscoveryState.applyRule5Task, resolved]
      cases state with
      | mk rs pseudo =>
          simp only [DescriptorDiscoveryState.assignPseudo] at known ⊢
          congr
          funext center
          by_cases self : center = task.center
          · subst center
            simpa using known.symm
          · simp [self]



theorem runRule5Tasks_eq_of_fixedPoint
    (state : DescriptorDiscoveryState m cfg) (tasks : List (Rule5DiscoveryTask m cfg))
    (fixed : state.FixedPointForRule5Tasks tasks) :
    state.runRule5Tasks tasks = state := by
  induction tasks with
  | nil => rfl
  | cons task tasks inductionHypothesis =>
      have taskStable : state.StableForRule5Task task := fixed task (by simp)
      have taskUnchanged : state.applyRule5Task task = state :=
        DescriptorDiscoveryState.applyRule5Task_eq_of_stable state task taskStable
      change (state.applyRule5Task task).runRule5Tasks tasks = state
      rw [taskUnchanged]
      apply inductionHypothesis
      intro later member
      exact fixed later (by simp [member])



theorem runRule5Tasks_idempotent_of_targetsNodup
    (state : DescriptorDiscoveryState m cfg) (tasks : List (Rule5DiscoveryTask m cfg))
    (hnodup : Rule5TargetsNodup tasks) :
    (state.runRule5Tasks tasks).runRule5Tasks tasks = state.runRule5Tasks tasks := by
  exact DescriptorDiscoveryState.runRule5Tasks_eq_of_fixedPoint
    (state.runRule5Tasks tasks) tasks
    (DescriptorDiscoveryState.runRule5Tasks_fixedPoint_of_targetsNodup state tasks hnodup)

end DescriptorDiscoveryState

/-- A reusable descriptor-discovery schedule: start from safe descriptor-CIP `R/S` seeds, then run
all listed descriptor-dependent Rule-5 tasks. -/
structure Rule5DiscoverySchedule (m : MultiCenterMolecule V) (cfg : m.Configuration) where
  tasks : List (Rule5DiscoveryTask m cfg)

namespace Rule5DiscoverySchedule

/-- The safe initial state for a schedule: only descriptor-CIP-resolved centers receive `R/S`. -/
def initialState (_schedule : Rule5DiscoverySchedule m cfg) : DescriptorDiscoveryState m cfg :=
  DescriptorDiscoveryState.seedResolvedDescriptorRS? m cfg

/-- Run the schedule once from a supplied state. -/
def runOnceFrom (schedule : Rule5DiscoverySchedule m cfg)
    (state : DescriptorDiscoveryState m cfg) : DescriptorDiscoveryState m cfg :=
  state.runRule5Tasks schedule.tasks

/-- Run the schedule once from safe descriptor-CIP seeds. -/
def runOnce (schedule : Rule5DiscoverySchedule m cfg) : DescriptorDiscoveryState m cfg :=
  schedule.runOnceFrom schedule.initialState

/-- Iterate the schedule for a fixed fuel count.  For current Rule-5 tasks one pass is enough when
target centers are unique, but this fuelled runner is useful for later descriptor layers. -/
def run (schedule : Rule5DiscoverySchedule m cfg) : ℕ → DescriptorDiscoveryState m cfg
  | 0 => schedule.initialState
  | n + 1 => schedule.runOnceFrom (schedule.run n)


def singleton (task : Rule5DiscoveryTask m cfg) : Rule5DiscoverySchedule m cfg where
  tasks := [task]

@[simp] theorem singleton_tasks (task : Rule5DiscoveryTask m cfg) :
    (singleton task).tasks = [task] :=
  rfl

variable (schedule : Rule5DiscoverySchedule m cfg)

@[simp] theorem run_zero : schedule.run 0 = schedule.initialState :=
  rfl

@[simp] theorem run_succ (n : ℕ) :
    schedule.run (n + 1) = schedule.runOnceFrom (schedule.run n) :=
  rfl

@[simp] theorem run_one : schedule.run 1 = schedule.runOnce := by
  rfl

/-- A schedule has no duplicate target centers. -/
def TargetsNodup : Prop :=
  DescriptorDiscoveryState.Rule5TargetsNodup schedule.tasks


theorem task_ready_initial_of_resolved_sources (task : Rule5DiscoveryTask m cfg)
    (hleft : m.ResolvedCIPDescriptorAt task.leftSource)
    (hright : m.ResolvedCIPDescriptorAt task.rightSource) :
    task.Ready schedule.initialState := by
  simpa [initialState] using
    Rule5DiscoveryTask.ready_seedResolvedDescriptorRS?_of_resolved_sources
      (task := task) hleft hright




theorem task_resolve_initial_of_resolved_sources (task : Rule5DiscoveryTask m cfg)
    (hleft : m.ResolvedCIPDescriptorAt task.leftSource)
    (hright : m.ResolvedCIPDescriptorAt task.rightSource)
    (hne : m.cipConfigurationRSDescriptor cfg task.leftSource ≠
      m.cipConfigurationRSDescriptor cfg task.rightSource) :
    task.resolveFromState? schedule.initialState =
      some
        (task.resolve
          (m.cipConfigurationRSDescriptor cfg task.leftSource)
          (m.cipConfigurationRSDescriptor cfg task.rightSource)) := by
  simpa [initialState] using
    Rule5DiscoveryTask.resolveFromState?_seedResolvedDescriptorRS?_eq_some
      (task := task) hleft hright hne





theorem task_resolveFromState?_isSome_iff_resolved_sources_ne
    (task : Rule5DiscoveryTask m cfg) :
    (task.resolveFromState? schedule.initialState).isSome ↔
      m.ResolvedCIPDescriptorAt task.leftSource ∧
        m.ResolvedCIPDescriptorAt task.rightSource ∧
          m.cipConfigurationRSDescriptor cfg task.leftSource ≠
            m.cipConfigurationRSDescriptor cfg task.rightSource := by
  constructor
  · intro hsome
    have happlicable : task.Applicable schedule.initialState :=
      (Rule5DiscoveryTask.resolveFromState?_isSome_iff_applicable task
        schedule.initialState).1 hsome
    unfold Rule5DiscoveryTask.Applicable at happlicable
    rcases happlicable with ⟨leftDescriptor, rightDescriptor, hleft, hright, hne⟩
    have hleftResolved : m.ResolvedCIPDescriptorAt task.leftSource := by
      by_contra hresolved
      have hnone :=
        DescriptorDiscoveryState.seedResolvedDescriptorRS?_rs_eq_none_of_not_resolved
          (m := m) (cfg := cfg) (c := task.leftSource) hresolved
      have hnone' : schedule.initialState.rs task.leftSource = none := by
        simpa [initialState] using hnone
      rw [hleft] at hnone'
      cases hnone'
    have hrightResolved : m.ResolvedCIPDescriptorAt task.rightSource := by
      by_contra hresolved
      have hnone :=
        DescriptorDiscoveryState.seedResolvedDescriptorRS?_rs_eq_none_of_not_resolved
          (m := m) (cfg := cfg) (c := task.rightSource) hresolved
      have hnone' : schedule.initialState.rs task.rightSource = none := by
        simpa [initialState] using hnone
      rw [hright] at hnone'
      cases hnone'
    have hleftSome : schedule.initialState.rs task.leftSource =
        some (m.cipConfigurationRSDescriptor cfg task.leftSource) := by
      simpa [initialState] using
        DescriptorDiscoveryState.seedResolvedDescriptorRS?_rs_eq_some_of_resolved
          (m := m) (cfg := cfg) (c := task.leftSource) hleftResolved
    have hrightSome : schedule.initialState.rs task.rightSource =
        some (m.cipConfigurationRSDescriptor cfg task.rightSource) := by
      simpa [initialState] using
        DescriptorDiscoveryState.seedResolvedDescriptorRS?_rs_eq_some_of_resolved
          (m := m) (cfg := cfg) (c := task.rightSource) hrightResolved
    have hleft_eq : leftDescriptor =
        m.cipConfigurationRSDescriptor cfg task.leftSource := by
      have hsome : some leftDescriptor =
          some (m.cipConfigurationRSDescriptor cfg task.leftSource) :=
        hleft.symm.trans hleftSome
      simpa using hsome
    have hright_eq : rightDescriptor =
        m.cipConfigurationRSDescriptor cfg task.rightSource := by
      have hsome : some rightDescriptor =
          some (m.cipConfigurationRSDescriptor cfg task.rightSource) :=
        hright.symm.trans hrightSome
      simpa using hsome
    refine ⟨hleftResolved, hrightResolved, ?_⟩
    intro heq
    exact hne (hleft_eq.trans (heq.trans hright_eq.symm))
  · rintro ⟨hleftResolved, hrightResolved, hne⟩
    apply (Rule5DiscoveryTask.resolveFromState?_isSome_iff_applicable task
      schedule.initialState).2
    unfold Rule5DiscoveryTask.Applicable
    have hleftSome : schedule.initialState.rs task.leftSource =
        some (m.cipConfigurationRSDescriptor cfg task.leftSource) := by
      simpa [initialState] using
        DescriptorDiscoveryState.seedResolvedDescriptorRS?_rs_eq_some_of_resolved
          (m := m) (cfg := cfg) (c := task.leftSource) hleftResolved
    have hrightSome : schedule.initialState.rs task.rightSource =
        some (m.cipConfigurationRSDescriptor cfg task.rightSource) := by
      simpa [initialState] using
        DescriptorDiscoveryState.seedResolvedDescriptorRS?_rs_eq_some_of_resolved
          (m := m) (cfg := cfg) (c := task.rightSource) hrightResolved
    exact ⟨m.cipConfigurationRSDescriptor cfg task.leftSource,
      m.cipConfigurationRSDescriptor cfg task.rightSource, hleftSome, hrightSome, hne⟩

/-- A one-pass run of a target-distinct schedule is a fixed point for that schedule. -/
theorem runOnce_fixedPoint_of_targetsNodup (hnodup : schedule.TargetsNodup) :
    schedule.runOnce.FixedPointForRule5Tasks schedule.tasks := by
  simpa [runOnce, runOnceFrom, TargetsNodup] using
    DescriptorDiscoveryState.runRule5Tasks_fixedPoint_of_targetsNodup
      (state := schedule.initialState) (tasks := schedule.tasks) hnodup

/-- Executable fixed-point form of the target-distinct one-pass theorem. -/
theorem runOnceFrom_runOnce_eq_of_targetsNodup
    (state : DescriptorDiscoveryState m cfg) (hnodup : schedule.TargetsNodup) :
    schedule.runOnceFrom (schedule.runOnceFrom state) = schedule.runOnceFrom state := by
  exact DescriptorDiscoveryState.runRule5Tasks_idempotent_of_targetsNodup
    state schedule.tasks hnodup

/-- Two target-distinct schedules containing the same Rule-5 tasks produce exactly the same state,
independently of their traversal order. -/
theorem runOnce_eq_of_tasks_perm
    (first second : Rule5DiscoverySchedule m cfg)
    (permutation : first.tasks.Perm second.tasks)
    (targetsNodup : first.TargetsNodup) :
    first.runOnce = second.runOnce := by
  exact DescriptorDiscoveryState.runRule5Tasks_eq_of_perm_of_targetsNodup
    first.initialState permutation targetsNodup

/-- In particular, the safe-seed result produced by `runOnce` is unchanged by another pass. -/
theorem runOnceFrom_runOnce_eq_of_targetsNodup_safe
    (hnodup : schedule.TargetsNodup) :
    schedule.runOnceFrom schedule.runOnce = schedule.runOnce := by
  exact schedule.runOnceFrom_runOnce_eq_of_targetsNodup schedule.initialState hnodup

/-- **Schedule saturation (one-pass totality).**  On a target-distinct schedule the fuelled runner
reaches its fixed point after at most one pass, for every positive fuel.  Consequently schedule
saturation needs no larger caller-supplied fuel bound: fuel `1`, `2`, `3`, … all denote the
same saturated state.  Fuel `0` has no such guarantee, since the safe seed need not be stable;
that is why the statement is guarded by `0 < n`. -/
theorem run_eq_runOnce_of_targetsNodup (hnodup : schedule.TargetsNodup) :
    ∀ n, 0 < n → schedule.run n = schedule.runOnce := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (Nat.lt_irrefl 0)
  | succ n inductionHypothesis =>
      intro _
      cases n with
      | zero => exact schedule.run_one
      | succ m =>
          have step :
              schedule.run (Nat.succ (Nat.succ m)) =
                schedule.runOnceFrom (schedule.run (Nat.succ m)) := rfl
          rw [step, inductionHypothesis (Nat.succ_pos m)]
          exact schedule.runOnceFrom_runOnce_eq_of_targetsNodup_safe hnodup

/-- **Fixed point at every positive fuel.**  On a target-distinct schedule the saturated state is a
literal fixed point of the schedule for any positive fuel, so the scheduler's terminal state is
independent of positive fuel under the target-distinctness hypothesis. -/
theorem run_fixedPoint_of_targetsNodup (hnodup : schedule.TargetsNodup) {n : ℕ} (hn : 0 < n) :
    (schedule.run n).FixedPointForRule5Tasks schedule.tasks := by
  rw [schedule.run_eq_runOnce_of_targetsNodup hnodup n hn]
  exact schedule.runOnce_fixedPoint_of_targetsNodup hnodup



theorem run_pseudo_eq_runOnce_pseudo_of_targetsNodup
    (hnodup : schedule.TargetsNodup) {n : ℕ} (hn : 0 < n) (center : m.Center) :
    (schedule.run n).pseudo center = schedule.runOnce.pseudo center := by
  rw [schedule.run_eq_runOnce_of_targetsNodup hnodup n hn]



theorem singleton_runOnce_pseudo_eq_some_of_resolve_initial
    (task : Rule5DiscoveryTask m cfg) (result : Rule5DiscoveryTask.Result task)
    (hresolve : task.resolveFromState? (singleton task).initialState = some result) :
    ((singleton task).runOnce).pseudo task.center = some result.descriptor := by
  have h := DescriptorDiscoveryState.applyRule5Task_pseudo_eq_some_of_resolveFromState?_eq_some
    (state := (singleton task).initialState) (task := task) (result := result) hresolve
  simpa [runOnce, runOnceFrom, singleton, DescriptorDiscoveryState.runRule5Tasks_singleton] using h

/-- A proof object for a successful scheduled Rule-5 resolution from safe descriptor-CIP seeds. -/
structure SafeTaskResolution (schedule : Rule5DiscoverySchedule m cfg) where
  task : Rule5DiscoveryTask m cfg
  task_mem : task ∈ schedule.tasks
  result : Rule5DiscoveryTask.Result task
  resolved_from_initial : task.resolveFromState? schedule.initialState = some result

/-- Every certified safe resolution was produced by the guarded resolver, hence its two source
descriptors are genuinely distinct.  This is a consequence of the actual success criterion, not an
extra assumption: equal seeded sources would have made the resolver return `none`. -/
theorem safeTaskResolution_result_descriptors_ne
    (resolution : SafeTaskResolution schedule) :
    resolution.result.leftDescriptor ≠ resolution.result.rightDescriptor :=
  Rule5DiscoveryTask.resolveFromState?_some_leftDescriptor_ne_rightDescriptor
    resolution.task schedule.initialState resolution.result resolution.resolved_from_initial

/-- In a target-distinct schedule, any certified safe resolution is present after one pass. -/
theorem runOnce_pseudo_eq_some_of_safeTaskResolution_of_targetsNodup
    (resolution : SafeTaskResolution schedule) (hnodup : schedule.TargetsNodup) :
    schedule.runOnce.pseudo resolution.task.center = some resolution.result.descriptor := by
  have hfixed := schedule.runOnce_fixedPoint_of_targetsNodup hnodup
  have hresolveFinal :
      resolution.task.resolveFromState? schedule.runOnce = some resolution.result := by
    rw [runOnce, runOnceFrom]
    rw [DescriptorDiscoveryState.runRule5Tasks_resolveFromState?_eq]
    exact resolution.resolved_from_initial
  exact hfixed resolution.task resolution.task_mem resolution.result hresolveFinal

/-- Construct a scheduled safe resolution from source resolvedness, provided the resolved source
descriptors are distinct.  Without the distinctness proof the guarded resolver is not known to
fire: readiness alone is dependency availability, not applicability. -/
def safeTaskResolutionOfResolvedSources (schedule : Rule5DiscoverySchedule m cfg)
    {task : Rule5DiscoveryTask m cfg} (htask : task ∈ schedule.tasks)
    (hleft : m.ResolvedCIPDescriptorAt task.leftSource)
    (hright : m.ResolvedCIPDescriptorAt task.rightSource)
    (hne : m.cipConfigurationRSDescriptor cfg task.leftSource ≠
      m.cipConfigurationRSDescriptor cfg task.rightSource) :
    SafeTaskResolution schedule where
  task := task
  task_mem := htask
  result := task.resolve
    (m.cipConfigurationRSDescriptor cfg task.leftSource)
    (m.cipConfigurationRSDescriptor cfg task.rightSource)
  resolved_from_initial :=
    task_resolve_initial_of_resolved_sources schedule task hleft hright hne

end Rule5DiscoverySchedule

end
end OneCenter
end TetraStereo
