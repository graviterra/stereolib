import TetraStereo.OneCenter.DescriptorScheduler

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {m : MultiCenterMolecule V} {cfg : m.Configuration}



structure Rule5TaskSpec (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (center : m.Center) where
  leftLigand : Fin 4
  rightLigand : Fin 4
  leftSource : m.Center
  rightSource : m.Center
  keyTie :
    cipTraceOutcome
      (CIPRuleEngine.compareKeyTrace
        (m.cipKeyDescriptorAt center leftLigand)
        (m.cipKeyDescriptorAt center rightLigand)) = Ordering.eq

namespace Rule5TaskSpec

def toTask {center : m.Center} (spec : Rule5TaskSpec m cfg center) :
    Rule5DiscoveryTask m cfg where
  center := center
  leftLigand := spec.leftLigand
  rightLigand := spec.rightLigand
  leftSource := spec.leftSource
  rightSource := spec.rightSource
  keyTie := spec.keyTie

@[simp] theorem toTask_center {center : m.Center} (spec : Rule5TaskSpec m cfg center) :
    spec.toTask.center = center :=
  rfl

end Rule5TaskSpec




structure Rule5TaskSelector (m : MultiCenterMolecule V) (cfg : m.Configuration) where
  spec? : (center : m.Center) → Option (Rule5TaskSpec m cfg center)

namespace Rule5TaskSelector

variable (selector : Rule5TaskSelector m cfg)

/-- The canonical center enumeration used by extracted schedules. -/
def centerList (m : MultiCenterMolecule V) : List m.Center :=
  (Finset.univ : Finset m.Center).toList


def task? (center : m.Center) : Option (Rule5DiscoveryTask m cfg) :=
  (selector.spec? center).map fun spec => spec.toTask


def taskCenter? (center : m.Center) : Option m.Center :=
  (selector.spec? center).map fun _ => center

/-- Extract all selected Rule-5 tasks. -/
def tasks : List (Rule5DiscoveryTask m cfg) :=
  (centerList m).filterMap selector.task?

/-- The schedule induced by extracted Rule-5 tasks. -/
def schedule : Rule5DiscoverySchedule m cfg where
  tasks := selector.tasks

private theorem task?_center_eq {center : m.Center} {task : Rule5DiscoveryTask m cfg}
    (h : task ∈ selector.task? center) : task.center = center := by
  unfold task? at h
  cases hspec : selector.spec? center with
  | none => simp [hspec] at h
  | some spec =>
      simp [hspec] at h
      subst task
      rfl

private theorem map_center_filterMap_task?_eq_filterMap_taskCenter? (centers : List m.Center) :
    (centers.filterMap selector.task?).map (fun task => task.center) =
      centers.filterMap selector.taskCenter? := by
  induction centers with
  | nil => simp
  | cons center centers ih =>
      unfold task? taskCenter?
      cases hspec : selector.spec? center with
      | none => simpa [task?, taskCenter?, hspec] using ih
      | some spec => simpa [task?, taskCenter?, hspec] using congrArg (fun xs => center :: xs) ih

private theorem taskCenter?_mem_eq {center center' : m.Center}
    (h : center' ∈ selector.taskCenter? center) : center' = center := by
  unfold taskCenter? at h
  cases hspec : selector.spec? center with
  | none => simp [hspec] at h
  | some spec =>
      simp [hspec] at h
      exact h.symm

theorem tasks_targetsNodup : DescriptorDiscoveryState.Rule5TargetsNodup selector.tasks := by
  dsimp [DescriptorDiscoveryState.Rule5TargetsNodup, tasks]
  rw [selector.map_center_filterMap_task?_eq_filterMap_taskCenter?]
  apply (Finset.univ : Finset m.Center).nodup_toList.filterMap
  intro center center' output h h'
  exact (selector.taskCenter?_mem_eq h).symm.trans (selector.taskCenter?_mem_eq h')

theorem schedule_targetsNodup : selector.schedule.TargetsNodup := by
  simpa [schedule, Rule5DiscoverySchedule.TargetsNodup] using selector.tasks_targetsNodup

theorem schedule_runOnce_fixedPoint :
    selector.schedule.runOnce.FixedPointForRule5Tasks selector.schedule.tasks := by
  exact selector.schedule.runOnce_fixedPoint_of_targetsNodup selector.schedule_targetsNodup






def safeResolutionAtOfResolvedSources {center : m.Center} (spec : Rule5TaskSpec m cfg center)
    (hspec : selector.spec? center = some spec)
    (hleft : m.ResolvedCIPDescriptorAt spec.leftSource)
    (hright : m.ResolvedCIPDescriptorAt spec.rightSource)
    (hne : m.cipConfigurationRSDescriptor cfg spec.leftSource ≠
      m.cipConfigurationRSDescriptor cfg spec.rightSource) :
    Rule5DiscoverySchedule.SafeTaskResolution selector.schedule := by
  refine Rule5DiscoverySchedule.safeTaskResolutionOfResolvedSources selector.schedule
    (task := spec.toTask) ?_ hleft hright hne
  dsimp [schedule, tasks, task?]
  refine List.mem_filterMap.2 ⟨center, by simp [Rule5TaskSelector.centerList], ?_⟩
  simp [Rule5TaskSelector.task?, hspec]

/-- Extracted safe resolutions are written to the scheduled state after one pass. -/
theorem schedule_runOnce_pseudo_eq_some_of_safeResolution
    (resolution : Rule5DiscoverySchedule.SafeTaskResolution selector.schedule) :
    selector.schedule.runOnce.pseudo resolution.task.center = some resolution.result.descriptor :=
  selector.schedule.runOnce_pseudo_eq_some_of_safeTaskResolution_of_targetsNodup
    resolution selector.schedule_targetsNodup

end Rule5TaskSelector

end
end OneCenter
end TetraStereo
