import TetraStereo.OneCenter.DescriptorTaskExtraction













set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {m : MultiCenterMolecule V} {cfg : m.Configuration}

/-! ## Missing readiness is a literal no-op -/

namespace Rule5DiscoveryTask




theorem resolveFromState?_eq_none_of_left_source_none
    (task : Rule5DiscoveryTask m cfg) (state : DescriptorDiscoveryState m cfg)
    (h : state.rs task.leftSource = none) :
    task.resolveFromState? state = none := by
  unfold Rule5DiscoveryTask.resolveFromState?
  rw [h]

end Rule5DiscoveryTask

namespace DescriptorDiscoveryState


theorem applyRule5Task_eq_self_of_resolveFromState?_eq_none
    (state : DescriptorDiscoveryState m cfg) (task : Rule5DiscoveryTask m cfg)
    (h : task.resolveFromState? state = none) :
    state.applyRule5Task task = state := by
  cases resolved : task.resolveFromState? state with
  | none => simp [DescriptorDiscoveryState.applyRule5Task, resolved]
  | some result => exact absurd h (by simp [resolved])


theorem applyRule5Task_eq_self_of_left_source_none
    (state : DescriptorDiscoveryState m cfg) (task : Rule5DiscoveryTask m cfg)
    (h : state.rs task.leftSource = none) :
    state.applyRule5Task task = state :=
  applyRule5Task_eq_self_of_resolveFromState?_eq_none state task
    (Rule5DiscoveryTask.resolveFromState?_eq_none_of_left_source_none task state h)



theorem runRule5Tasks_eq_self_of_all_left_source_none
    (state : DescriptorDiscoveryState m cfg) (tasks : List (Rule5DiscoveryTask m cfg))
    (h : ∀ task, task ∈ tasks → state.rs task.leftSource = none) :
    state.runRule5Tasks tasks = state := by
  induction tasks generalizing state with
  | nil => rfl
  | cons task tasks inductionHypothesis =>
      change ((state.applyRule5Task task).runRule5Tasks tasks) = state
      rw [applyRule5Task_eq_self_of_left_source_none state task (h task (by simp))]
      exact inductionHypothesis state (fun later hlater => h later (by simp [hlater]))

end DescriptorDiscoveryState

namespace Rule5TaskSelector

variable (selector : Rule5TaskSelector m cfg)

/-- **Extracted schedule saturation.**  At every positive fuel the extracted schedule's fuelled run
equals its one-pass run. -/
theorem extracted_run_eq_runOnce {n : ℕ} (hn : 0 < n) :
    selector.schedule.run n = selector.schedule.runOnce :=
  selector.schedule.run_eq_runOnce_of_targetsNodup
    selector.schedule_targetsNodup n hn



theorem extracted_run_fixedPoint {n : ℕ} (hn : 0 < n) :
    (selector.schedule.run n).FixedPointForRule5Tasks selector.schedule.tasks :=
  selector.schedule.run_fixedPoint_of_targetsNodup
    selector.schedule_targetsNodup hn

/-! ## The `R/S` seed is immutable -/

/-- Rule-5 tasks write only pseudo descriptors, so the fuelled run preserves the initial `R/S`
seed at every fuel (including `0`). -/
theorem extracted_schedule_run_rs (n : ℕ) :
    (selector.schedule.run n).rs = selector.schedule.initialState.rs := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      change ((selector.schedule.run n).runRule5Tasks selector.schedule.tasks).rs =
        selector.schedule.initialState.rs
      rw [DescriptorDiscoveryState.runRule5Tasks_rs]
      exact inductionHypothesis

/-! ## Conditional refusal: unresolved `R/S` seeds stay unresolved -/




theorem extracted_runOnce_pseudo_eq_none_of_left_source_unresolved
    (h : ∀ task, task ∈ selector.tasks → ¬ m.ResolvedCIPDescriptorAt task.leftSource)
    (center : m.Center) :
    selector.schedule.runOnce.pseudo center = none := by
  have hnone : ∀ task, task ∈ selector.schedule.tasks →
      selector.schedule.initialState.rs task.leftSource = none := by
    intro task hmem
    classical
    exact DescriptorDiscoveryState.seedResolvedDescriptorRS?_rs_eq_none_of_not_resolved
      m cfg task.leftSource (h task hmem)
  have hfix := DescriptorDiscoveryState.runRule5Tasks_eq_self_of_all_left_source_none
    (state := selector.schedule.initialState) (tasks := selector.schedule.tasks) hnone
  change (selector.schedule.initialState.runRule5Tasks selector.schedule.tasks).pseudo center = none
  rw [hfix]
  rfl

/-- Fuelled form of the regression: at every positive fuel the unresolved seed still yields an
empty pseudo slot. -/
theorem extracted_run_pseudo_eq_none_of_left_source_unresolved
    (h : ∀ task, task ∈ selector.tasks → ¬ m.ResolvedCIPDescriptorAt task.leftSource)
    {n : ℕ} (hn : 0 < n) (center : m.Center) :
    (selector.schedule.run n).pseudo center = none := by
  rw [extracted_run_eq_runOnce selector hn]
  exact extracted_runOnce_pseudo_eq_none_of_left_source_unresolved selector h center

end Rule5TaskSelector

end

end OneCenter
end TetraStereo
