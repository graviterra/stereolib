import TetraStereo.OneCenter.CIPRules

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section


















variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The global information accumulated by descriptor discovery.  Ordinary `R/S` descriptors and
lowercase pseudoasymmetric descriptors are tracked separately because a center can have a local
configuration sign while also being pseudoasymmetric as a descriptor-dependent CIP center. -/
structure DescriptorDiscoveryState (m : MultiCenterMolecule V) (cfg : m.Configuration) where
  rs : m.Center → Option RS
  pseudo : m.Center → Option PseudoRS

namespace DescriptorDiscoveryState

variable {m : MultiCenterMolecule V} {cfg : m.Configuration}

/-- Seed discovery with the current multi-center `R/S` pattern and no lowercase descriptors. -/
def seedConfigurationRS (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    DescriptorDiscoveryState m cfg where
  rs := fun c => some (m.configurationRS cfg c)
  pseudo := fun _ => none

/-- Seed discovery from the descriptor-facing CIP `R/S` pipeline.  A center receives an `R/S`
seed only when its descriptor-facing local CIP priorities are resolved; unresolved centers remain
`none` and can be filled by later descriptor-dependent tasks. -/
def seedResolvedDescriptorRS? (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    DescriptorDiscoveryState m cfg where
  rs := by
    classical
    exact fun c =>
      if h : m.ResolvedCIPDescriptorAt c then
        some (m.cipConfigurationRSDescriptor cfg c)
      else
        none
  pseudo := fun _ => none

theorem seedResolvedDescriptorRS?_rs_eq_some_of_resolved
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center)
    (h : m.ResolvedCIPDescriptorAt c) :
    (seedResolvedDescriptorRS? m cfg).rs c = some (m.cipConfigurationRSDescriptor cfg c) := by
  classical
  simp [seedResolvedDescriptorRS?, h]

theorem seedResolvedDescriptorRS?_rs_eq_none_of_not_resolved
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center)
    (h : ¬ m.ResolvedCIPDescriptorAt c) :
    (seedResolvedDescriptorRS? m cfg).rs c = none := by
  classical
  simp [seedResolvedDescriptorRS?, h]

/-- Assign a lowercase pseudoasymmetric descriptor at one center. -/
def assignPseudo (state : DescriptorDiscoveryState m cfg) (center : m.Center)
    (descriptor : PseudoRS) : DescriptorDiscoveryState m cfg where
  rs := state.rs
  pseudo := fun c => if c = center then some descriptor else state.pseudo c

@[simp] theorem assignPseudo_rs (state : DescriptorDiscoveryState m cfg) (center : m.Center)
    (descriptor : PseudoRS) :
    (state.assignPseudo center descriptor).rs = state.rs :=
  rfl

@[simp] theorem assignPseudo_pseudo_self (state : DescriptorDiscoveryState m cfg)
    (center : m.Center) (descriptor : PseudoRS) :
    (state.assignPseudo center descriptor).pseudo center = some descriptor := by
  simp [assignPseudo]

theorem assignPseudo_pseudo_of_ne (state : DescriptorDiscoveryState m cfg)
    {center other : m.Center} (descriptor : PseudoRS) (h : other ≠ center) :
    (state.assignPseudo center descriptor).pseudo other = state.pseudo other := by
  simp [assignPseudo, h]

end DescriptorDiscoveryState



structure Rule5DiscoveryTask (m : MultiCenterMolecule V) (cfg : m.Configuration) where
  center : m.Center
  leftLigand : Fin 4
  rightLigand : Fin 4
  leftSource : m.Center
  rightSource : m.Center
  keyTie :
    cipTraceOutcome
      (CIPRuleEngine.compareKeyTrace
        (m.cipKeyDescriptorAt center leftLigand)
        (m.cipKeyDescriptorAt center rightLigand)) = Ordering.eq

namespace Rule5DiscoveryTask

variable {m : MultiCenterMolecule V} {cfg : m.Configuration}


def dependencies (task : Rule5DiscoveryTask m cfg) : List m.Center :=
  [task.leftSource, task.rightSource]




def Ready (task : Rule5DiscoveryTask m cfg) (state : DescriptorDiscoveryState m cfg) : Prop :=
  (∃ descriptor, state.rs task.leftSource = some descriptor) ∧
    (∃ descriptor, state.rs task.rightSource = some descriptor)

/-- Applicability is dependency availability together with a genuine enantiomorphic-pair-shaped
input: both source `R/S` descriptors are present and **distinct**.  Equal `R,R` or `S,S` sources
are not an enantiomorphic pair and must not be coerced into a lowercase descriptor. -/
def Applicable (task : Rule5DiscoveryTask m cfg) (state : DescriptorDiscoveryState m cfg) : Prop :=
  ∃ leftDescriptor rightDescriptor : RS,
    state.rs task.leftSource = some leftDescriptor ∧
      state.rs task.rightSource = some rightDescriptor ∧
      leftDescriptor ≠ rightDescriptor

/-- Readiness plus pointwise distinctness of any two available source descriptors gives
applicability. -/
theorem applicable_of_ready_of_descriptor_ne
    (task : Rule5DiscoveryTask m cfg) (state : DescriptorDiscoveryState m cfg)
    (hready : task.Ready state)
    (hne : ∀ leftDescriptor rightDescriptor : RS,
      state.rs task.leftSource = some leftDescriptor →
        state.rs task.rightSource = some rightDescriptor →
          leftDescriptor ≠ rightDescriptor) :
    task.Applicable state := by
  rcases hready with ⟨⟨leftDescriptor, hleft⟩, ⟨rightDescriptor, hright⟩⟩
  unfold Rule5DiscoveryTask.Applicable
  exact ⟨leftDescriptor, rightDescriptor, hleft, hright,
    hne leftDescriptor rightDescriptor hleft hright⟩


structure Result (task : Rule5DiscoveryTask m cfg) where
  leftDescriptor : RS
  rightDescriptor : RS
  engine : CIPRuleEngine.Rule5PseudoDescriptorEngineResult
  descriptor : PseudoRS
  descriptor_eq : descriptor = engine.descriptor
  sound :
    descriptor =
      pseudoDescriptor (m.configurationSign cfg task.center) leftDescriptor rightDescriptor


def resolve (task : Rule5DiscoveryTask m cfg) (leftDescriptor rightDescriptor : RS) :
    Result task :=
  let engine :=
    m.rule5PseudoDescriptorEngineAt cfg task.center task.leftLigand task.rightLigand
      leftDescriptor rightDescriptor
  { leftDescriptor := leftDescriptor
    rightDescriptor := rightDescriptor
    engine := engine
    descriptor := engine.descriptor
    descriptor_eq := rfl
    sound := by
      exact
        CIPRuleEngine.rule5PseudoDescriptorEngineFromKeys_descriptor_eq_pseudoDescriptor_of_key_eq
          (m.configurationSign cfg task.center) leftDescriptor rightDescriptor task.keyTie }




def resolveFromState? (task : Rule5DiscoveryTask m cfg)
    (state : DescriptorDiscoveryState m cfg) : Option (Result task) :=
  match state.rs task.leftSource, state.rs task.rightSource with
  | some leftDescriptor, some rightDescriptor =>
      if leftDescriptor = rightDescriptor then none
      else some (task.resolve leftDescriptor rightDescriptor)
  | _, _ => none

/-- Distinct available source descriptors resolve to exactly the legacy `resolve` value.  This is
the compatibility statement: on the previously accepted distinct-`R/S` inputs the result is
unchanged. -/
theorem resolveFromState?_eq_some_of_rs_sources_ne
    (task : Rule5DiscoveryTask m cfg) (state : DescriptorDiscoveryState m cfg)
    {leftDescriptor rightDescriptor : RS}
    (hleft : state.rs task.leftSource = some leftDescriptor)
    (hright : state.rs task.rightSource = some rightDescriptor)
    (hne : leftDescriptor ≠ rightDescriptor) :
    task.resolveFromState? state = some (task.resolve leftDescriptor rightDescriptor) := by
  simp [resolveFromState?, hleft, hright, hne]

/-- Equal available source descriptors are refused. -/
theorem resolveFromState?_eq_none_of_rs_sources_eq
    (task : Rule5DiscoveryTask m cfg) (state : DescriptorDiscoveryState m cfg)
    {descriptor : RS}
    (hleft : state.rs task.leftSource = some descriptor)
    (hright : state.rs task.rightSource = some descriptor) :
    task.resolveFromState? state = none := by
  simp [resolveFromState?, hleft, hright]

/-- Missing right source remains a no-op: readiness is a prerequisite of applicability.
(The corresponding left-source statement is already provided downstream by
`UniversalProof/ExtractedScheduleSaturationProofs/ExtractedScheduleSaturation.lean`; it is not redeclared here.) -/
theorem resolveFromState?_eq_none_of_right_source_none
    (task : Rule5DiscoveryTask m cfg) (state : DescriptorDiscoveryState m cfg)
    (h : state.rs task.rightSource = none) :
    task.resolveFromState? state = none := by
  simp [resolveFromState?, h]

/-- Exact success criterion for the guarded resolver: a resolution exists exactly when both source
descriptors are available and distinct. -/
theorem resolveFromState?_isSome_iff_applicable
    (task : Rule5DiscoveryTask m cfg) (state : DescriptorDiscoveryState m cfg) :
    (task.resolveFromState? state).isSome ↔ task.Applicable state := by
  constructor
  · intro hsome
    unfold Rule5DiscoveryTask.resolveFromState? at hsome
    cases hleft : state.rs task.leftSource with
    | none =>
        exfalso
        simp [hleft] at hsome
    | some leftDescriptor =>
        cases hright : state.rs task.rightSource with
        | none =>
            exfalso
            simp [hleft, hright] at hsome
        | some rightDescriptor =>
            unfold Rule5DiscoveryTask.Applicable
            refine ⟨leftDescriptor, rightDescriptor, hleft, hright, ?_⟩
            by_cases heq : leftDescriptor = rightDescriptor
            · exfalso
              simp [hleft, hright, if_pos heq] at hsome
            · exact heq
  · intro happlicable
    unfold Rule5DiscoveryTask.Applicable at happlicable
    rcases happlicable with ⟨leftDescriptor, rightDescriptor, hleft, hright, hne⟩
    rw [Rule5DiscoveryTask.resolveFromState?_eq_some_of_rs_sources_ne
      task state hleft hright hne]
    rfl

/-- Every successful resolution really used distinct source descriptors.  This is the guarded
resolver's soundness condition: the zero-sign/equal-source coercion is unreachable. -/
theorem resolveFromState?_some_leftDescriptor_ne_rightDescriptor
    (task : Rule5DiscoveryTask m cfg) (state : DescriptorDiscoveryState m cfg)
    (result : Result task)
    (h : task.resolveFromState? state = some result) :
    result.leftDescriptor ≠ result.rightDescriptor := by
  intro heq
  unfold Rule5DiscoveryTask.resolveFromState? at h
  cases hleft : state.rs task.leftSource with
  | none => simp [hleft] at h
  | some leftDescriptor =>
      cases hright : state.rs task.rightSource with
      | none => simp [hleft, hright] at h
      | some rightDescriptor =>
          by_cases hold : leftDescriptor = rightDescriptor
          · exfalso
            simp [hleft, hright, if_pos hold] at h
          · have hsomeEq :
                some result = some (task.resolve leftDescriptor rightDescriptor) := by
              simpa [hleft, hright, if_neg hold] using h.symm
            have hresolve : result = task.resolve leftDescriptor rightDescriptor :=
              Option.some.inj hsomeEq
            have hleftField : result.leftDescriptor = leftDescriptor := by
              rw [hresolve]
              rfl
            have hrightField : result.rightDescriptor = rightDescriptor := by
              rw [hresolve]
              rfl
            exact hold (hleftField.symm.trans (heq.trans hrightField))



theorem resolveFromState?_isSome_of_ready
    (task : Rule5DiscoveryTask m cfg) (state : DescriptorDiscoveryState m cfg)
    (hready : task.Ready state)
    (hne : ∀ leftDescriptor rightDescriptor : RS,
      state.rs task.leftSource = some leftDescriptor →
        state.rs task.rightSource = some rightDescriptor →
          leftDescriptor ≠ rightDescriptor) :
    (task.resolveFromState? state).isSome := by
  have happlicable : task.Applicable state :=
    task.applicable_of_ready_of_descriptor_ne state hready hne
  exact (task.resolveFromState?_isSome_iff_applicable state).2 happlicable

theorem ready_seedResolvedDescriptorRS?_of_resolved_sources
    (task : Rule5DiscoveryTask m cfg)
    (hleft : m.ResolvedCIPDescriptorAt task.leftSource)
    (hright : m.ResolvedCIPDescriptorAt task.rightSource) :
    task.Ready (DescriptorDiscoveryState.seedResolvedDescriptorRS? m cfg) := by
  constructor
  · exact ⟨m.cipConfigurationRSDescriptor cfg task.leftSource,
      DescriptorDiscoveryState.seedResolvedDescriptorRS?_rs_eq_some_of_resolved
        m cfg task.leftSource hleft⟩
  · exact ⟨m.cipConfigurationRSDescriptor cfg task.rightSource,
      DescriptorDiscoveryState.seedResolvedDescriptorRS?_rs_eq_some_of_resolved
        m cfg task.rightSource hright⟩

/-- On descriptor-CIP-resolved sources, the guarded resolver still returns the legacy result when
the two resolved descriptors are distinct.  The distinctness premise is genuinely necessary after
the guard: `R,R` and `S,S` are refused. -/
theorem resolveFromState?_seedResolvedDescriptorRS?_eq_some
    (task : Rule5DiscoveryTask m cfg)
    (hleft : m.ResolvedCIPDescriptorAt task.leftSource)
    (hright : m.ResolvedCIPDescriptorAt task.rightSource)
    (hne : m.cipConfigurationRSDescriptor cfg task.leftSource ≠
      m.cipConfigurationRSDescriptor cfg task.rightSource) :
    task.resolveFromState? (DescriptorDiscoveryState.seedResolvedDescriptorRS? m cfg) =
      some
        (task.resolve
          (m.cipConfigurationRSDescriptor cfg task.leftSource)
          (m.cipConfigurationRSDescriptor cfg task.rightSource)) := by
  classical
  simp [resolveFromState?, DescriptorDiscoveryState.seedResolvedDescriptorRS?,
    hleft, hright, hne]

/-- On descriptor-CIP-resolved sources with equal descriptors, the guarded resolver refuses. -/
theorem resolveFromState?_seedResolvedDescriptorRS?_eq_none_of_eq
    (task : Rule5DiscoveryTask m cfg)
    (hleft : m.ResolvedCIPDescriptorAt task.leftSource)
    (hright : m.ResolvedCIPDescriptorAt task.rightSource)
    (heq : m.cipConfigurationRSDescriptor cfg task.leftSource =
      m.cipConfigurationRSDescriptor cfg task.rightSource) :
    task.resolveFromState? (DescriptorDiscoveryState.seedResolvedDescriptorRS? m cfg) = none := by
  classical
  simp [resolveFromState?, DescriptorDiscoveryState.seedResolvedDescriptorRS?,
    hleft, hright, heq]

end Rule5DiscoveryTask

namespace DescriptorDiscoveryState

variable {m : MultiCenterMolecule V} {cfg : m.Configuration}



def applyRule5Task (state : DescriptorDiscoveryState m cfg)
    (task : Rule5DiscoveryTask m cfg) : DescriptorDiscoveryState m cfg :=
  match task.resolveFromState? state with
  | none => state
  | some result => state.assignPseudo task.center result.descriptor

/-- Run a list of Rule-5 tasks once from left to right. -/
def runRule5Tasks (state : DescriptorDiscoveryState m cfg)
    (tasks : List (Rule5DiscoveryTask m cfg)) : DescriptorDiscoveryState m cfg :=
  tasks.foldl (fun current task => current.applyRule5Task task) state


def StableForRule5Task (state : DescriptorDiscoveryState m cfg)
    (task : Rule5DiscoveryTask m cfg) : Prop :=
  ∀ result, task.resolveFromState? state = some result →
    state.pseudo task.center = some result.descriptor


def FixedPointForRule5Tasks (state : DescriptorDiscoveryState m cfg)
    (tasks : List (Rule5DiscoveryTask m cfg)) : Prop :=
  ∀ task, task ∈ tasks → state.StableForRule5Task task

theorem applyRule5Task_pseudo_eq_some_of_resolveFromState?_eq_some
    (state : DescriptorDiscoveryState m cfg) (task : Rule5DiscoveryTask m cfg)
    (result : Rule5DiscoveryTask.Result task)
    (h : task.resolveFromState? state = some result) :
    (state.applyRule5Task task).pseudo task.center = some result.descriptor := by
  simp [applyRule5Task, h]

theorem runRule5Tasks_singleton (state : DescriptorDiscoveryState m cfg)
    (task : Rule5DiscoveryTask m cfg) :
    state.runRule5Tasks [task] = state.applyRule5Task task := by
  rfl

end DescriptorDiscoveryState

/-- A compact certificate that a global descriptor-discovery state has produced a lowercase
pseudoasymmetric descriptor from discovered `R/S` dependencies and that the molecular configuration
is achiral by symmetry. -/
structure Rule5GlobalDiscoveryCertificate (m : MultiCenterMolecule V)
    (cfg : m.Configuration) where
  initial : DescriptorDiscoveryState m cfg
  task : Rule5DiscoveryTask m cfg
  result : Rule5DiscoveryTask.Result task
  resolved_from_initial : task.resolveFromState? initial = some result
  finalState : DescriptorDiscoveryState m cfg
  finalState_eq : finalState = initial.applyRule5Task task
  final_pseudo : finalState.pseudo task.center = some result.descriptor
  achiral : m.AchiralConfigurationBySymmetry cfg

end
end OneCenter
end TetraStereo
