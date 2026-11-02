import TetraStereo.OneCenter.OfficialCIPEngine
import TetraStereo.OneCenter.OfficialContextPerception
import TetraStereo.OneCenter.DescriptorScheduler

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
  General official descriptor environment.

  The first descriptor scheduler was intentionally narrow: it solved tetrahedral `R/S` dependencies
  for Rule-5 pseudoasymmetric tasks.  This module lifts that shape to the official-rule level.  An
  environment can hold Rule 3, 4a, 4b, 4c, and 5 facts for arbitrary stereochemical units; tasks can
  depend on any such facts; schedules can be iterated to a fixed point.

  The legacy discovery-to-environment bridge shares one class projection with official branch
  perception: lowercase pseudoasymmetry is preferred over the local uppercase `R/S` seed.  A center
  can simultaneously carry an `R/S` seed (needed by Rule 5) and a pseudoasymmetric descriptor (the
  Rule 4a class), and those are not in conflict: the class is pseudoasymmetric while the uppercase
  descriptor remains available to Rule 5.
-/

/-- The official descriptor slots that can feed Rule 3/4/5 context comparison. -/
inductive OfficialDescriptorSlot where
  | rule3Geometry
  | rule4aKind
  | rule4bPair
  | rule4cDescriptor
  | rule5Descriptor
  deriving DecidableEq, Repr

/-- A typed official descriptor fact, packaged with its slot. -/
inductive OfficialDescriptorValue where
  | rule3Geometry (geometry : OfficialRule3Geometry)
  | rule4aKind (kind : OfficialStereogenicUnitKind)
  | rule4bPair (pair : OfficialDescriptorPairKind)
  | rule4cDescriptor (descriptor : OfficialPseudoasymmetricDescriptor)
  | rule5Descriptor (descriptor : OfficialRule5Descriptor)
  deriving DecidableEq, Repr

namespace OfficialDescriptorValue

/-- The slot populated by a descriptor value. -/
def slot : OfficialDescriptorValue → OfficialDescriptorSlot
  | rule3Geometry _ => OfficialDescriptorSlot.rule3Geometry
  | rule4aKind _ => OfficialDescriptorSlot.rule4aKind
  | rule4bPair _ => OfficialDescriptorSlot.rule4bPair
  | rule4cDescriptor _ => OfficialDescriptorSlot.rule4cDescriptor
  | rule5Descriptor _ => OfficialDescriptorSlot.rule5Descriptor

/-- Convert a single descriptor value into an official ligand context containing only that fact. -/
def toOfficialLigandRuleContext : OfficialDescriptorValue →
    CIPRuleEngine.OfficialLigandRuleContext
  | rule3Geometry geometry => CIPRuleEngine.OfficialLigandRuleContext.ofRule3Geometry geometry
  | rule4aKind kind => CIPRuleEngine.OfficialLigandRuleContext.ofRule4aKind kind
  | rule4bPair pair => CIPRuleEngine.OfficialLigandRuleContext.ofRule4bPair pair
  | rule4cDescriptor descriptor =>
      CIPRuleEngine.OfficialLigandRuleContext.ofRule4cDescriptor descriptor
  | rule5Descriptor descriptor =>
      CIPRuleEngine.OfficialLigandRuleContext.ofRule5Descriptor descriptor

@[simp] theorem slot_rule5Descriptor (descriptor : OfficialRule5Descriptor) :
    (rule5Descriptor descriptor).slot = OfficialDescriptorSlot.rule5Descriptor :=
  rfl

@[simp] theorem slot_rule4cDescriptor (descriptor : OfficialPseudoasymmetricDescriptor) :
    (rule4cDescriptor descriptor).slot = OfficialDescriptorSlot.rule4cDescriptor :=
  rfl

end OfficialDescriptorValue

/-- A dependency on one official descriptor slot at one stereochemical unit. -/
structure OfficialDescriptorRequirement (Unit : Type*) where
  unit : Unit
  slot : OfficialDescriptorSlot
  deriving DecidableEq, Repr

/-- A global environment of official descriptor facts.  The unit type may be molecule centers,
alkenes, axes, helices, ligand branches, or any future stereogenic-unit index type. -/
structure OfficialDescriptorEnvironment (Unit : Type*) where
  rule3Geometry : Unit → Option OfficialRule3Geometry := fun _ => none
  rule4aKind : Unit → Option OfficialStereogenicUnitKind := fun _ => none
  rule4bPair : Unit → Option OfficialDescriptorPairKind := fun _ => none
  rule4cDescriptor : Unit → Option OfficialPseudoasymmetricDescriptor := fun _ => none
  rule5Descriptor : Unit → Option OfficialRule5Descriptor := fun _ => none

namespace OfficialDescriptorEnvironment

variable {Unit : Type*}

/-- Empty official descriptor environment. -/
def empty : OfficialDescriptorEnvironment Unit := {}

/-- Lookup a descriptor value by unit and slot. -/
def value? (env : OfficialDescriptorEnvironment Unit) (unit : Unit) :
    OfficialDescriptorSlot → Option OfficialDescriptorValue
  | OfficialDescriptorSlot.rule3Geometry =>
      (env.rule3Geometry unit).map OfficialDescriptorValue.rule3Geometry
  | OfficialDescriptorSlot.rule4aKind =>
      (env.rule4aKind unit).map OfficialDescriptorValue.rule4aKind
  | OfficialDescriptorSlot.rule4bPair =>
      (env.rule4bPair unit).map OfficialDescriptorValue.rule4bPair
  | OfficialDescriptorSlot.rule4cDescriptor =>
      (env.rule4cDescriptor unit).map OfficialDescriptorValue.rule4cDescriptor
  | OfficialDescriptorSlot.rule5Descriptor =>
      (env.rule5Descriptor unit).map OfficialDescriptorValue.rule5Descriptor

/-- A requirement is satisfied when the requested unit/slot has a fact. -/
def Satisfies (env : OfficialDescriptorEnvironment Unit)
    (requirement : OfficialDescriptorRequirement Unit) : Prop :=
  ∃ value, env.value? requirement.unit requirement.slot = some value

/-- A list of requirements is ready when every requested fact is present. -/
def Ready (env : OfficialDescriptorEnvironment Unit)
    (requirements : List (OfficialDescriptorRequirement Unit)) : Prop :=
  ∀ requirement, requirement ∈ requirements → env.Satisfies requirement

/-- Executable readiness check for a list of requirements. -/
def requirementsReady (env : OfficialDescriptorEnvironment Unit)
    (requirements : List (OfficialDescriptorRequirement Unit)) : Bool :=
  requirements.all fun requirement =>
    (env.value? requirement.unit requirement.slot).isSome

/-- Assign one official descriptor value to one unit. -/
def assign [DecidableEq Unit] (env : OfficialDescriptorEnvironment Unit)
    (unit : Unit) (value : OfficialDescriptorValue) :
    OfficialDescriptorEnvironment Unit where
  rule3Geometry := fun query =>
    match value with
    | OfficialDescriptorValue.rule3Geometry geometry =>
        if query = unit then some geometry else env.rule3Geometry query
    | _ => env.rule3Geometry query
  rule4aKind := fun query =>
    match value with
    | OfficialDescriptorValue.rule4aKind kind =>
        if query = unit then some kind else env.rule4aKind query
    | _ => env.rule4aKind query
  rule4bPair := fun query =>
    match value with
    | OfficialDescriptorValue.rule4bPair pair =>
        if query = unit then some pair else env.rule4bPair query
    | _ => env.rule4bPair query
  rule4cDescriptor := fun query =>
    match value with
    | OfficialDescriptorValue.rule4cDescriptor descriptor =>
        if query = unit then some descriptor else env.rule4cDescriptor query
    | _ => env.rule4cDescriptor query
  rule5Descriptor := fun query =>
    match value with
    | OfficialDescriptorValue.rule5Descriptor descriptor =>
        if query = unit then some descriptor else env.rule5Descriptor query
    | _ => env.rule5Descriptor query

@[simp] theorem value?_assign_self [DecidableEq Unit]
    (env : OfficialDescriptorEnvironment Unit) (unit : Unit)
    (value : OfficialDescriptorValue) :
    (env.assign unit value).value? unit value.slot = some value := by
  cases value <;> simp [assign, value?, OfficialDescriptorValue.slot]

theorem value?_assign_of_ne [DecidableEq Unit]
    (env : OfficialDescriptorEnvironment Unit) {target query : Unit}
    (value : OfficialDescriptorValue) (slot : OfficialDescriptorSlot) (h : query ≠ target) :
    (env.assign target value).value? query slot = env.value? query slot := by
  cases value <;> cases slot <;> simp [assign, value?, h]

/-- Convert all facts for one unit to an official ligand rule context. -/
def toOfficialLigandRuleContext (env : OfficialDescriptorEnvironment Unit) (unit : Unit) :
    CIPRuleEngine.OfficialLigandRuleContext where
  rule3Geometry? := env.rule3Geometry unit
  rule4aKind? := env.rule4aKind unit
  rule4bPair? := env.rule4bPair unit
  rule4cDescriptor? := env.rule4cDescriptor unit
  rule5Descriptor? := env.rule5Descriptor unit

/-- Build an environment from already perceived ligand evidence. -/
def fromPerceivedEvidence (evidence : Unit → PerceivedLigandEvidence) :
    OfficialDescriptorEnvironment Unit where
  rule3Geometry := fun unit => (evidence unit).rule3Geometry?
  rule4aKind := fun unit => (evidence unit).rule4aKind?
  rule4bPair := fun unit => (evidence unit).rule4bPair?
  rule4cDescriptor := fun unit => (evidence unit).rule4cDescriptor?
  rule5Descriptor := fun unit => (evidence unit).rule5Descriptor?

@[simp] theorem fromPerceivedEvidence_context
    (evidence : Unit → PerceivedLigandEvidence) (unit : Unit) :
    (fromPerceivedEvidence evidence).toOfficialLigandRuleContext unit =
      (evidence unit).toOfficialLigandRuleContext :=
  rfl

end OfficialDescriptorEnvironment



structure OfficialDescriptorTask (Unit : Type*) where
  target : Unit
  requirements : List (OfficialDescriptorRequirement Unit)
  resolve? : OfficialDescriptorEnvironment Unit → Option OfficialDescriptorValue

namespace OfficialDescriptorTask

variable {Unit : Type*}


def Ready (task : OfficialDescriptorTask Unit)
    (env : OfficialDescriptorEnvironment Unit) : Prop :=
  env.Ready task.requirements


def Safe (task : OfficialDescriptorTask Unit) : Prop :=
  ∀ env value, task.resolve? env = some value → task.Ready env


def apply [DecidableEq Unit] (task : OfficialDescriptorTask Unit)
    (env : OfficialDescriptorEnvironment Unit) : OfficialDescriptorEnvironment Unit :=
  match task.resolve? env with
  | none => env
  | some value => env.assign task.target value


def StableFor (task : OfficialDescriptorTask Unit)
    (env : OfficialDescriptorEnvironment Unit) : Prop :=
  ∀ value, task.resolve? env = some value →
    env.value? task.target value.slot = some value

theorem apply_value?_eq_some_of_resolve?_eq_some [DecidableEq Unit]
    (task : OfficialDescriptorTask Unit) (env : OfficialDescriptorEnvironment Unit)
    (value : OfficialDescriptorValue) (h : task.resolve? env = some value) :
    (task.apply env).value? task.target value.slot = some value := by
  simp [apply, h]

end OfficialDescriptorTask

namespace OfficialDescriptorEnvironment

variable {Unit : Type*} [DecidableEq Unit]


def FixedPointForTasks (env : OfficialDescriptorEnvironment Unit)
    (tasks : List (OfficialDescriptorTask Unit)) : Prop :=
  ∀ task, task ∈ tasks → task.StableFor env

/-- Run a list of descriptor tasks once, left to right. -/
def runTasks (env : OfficialDescriptorEnvironment Unit)
    (tasks : List (OfficialDescriptorTask Unit)) : OfficialDescriptorEnvironment Unit :=
  tasks.foldl (fun current task => task.apply current) env

@[simp] theorem runTasks_nil (env : OfficialDescriptorEnvironment Unit) :
    env.runTasks [] = env :=
  rfl

@[simp] theorem runTasks_singleton (env : OfficialDescriptorEnvironment Unit)
    (task : OfficialDescriptorTask Unit) :
    env.runTasks [task] = task.apply env :=
  rfl

end OfficialDescriptorEnvironment

/-- A fuelled official descriptor schedule.  Cyclic dependencies are handled by iterating the
schedule and then requiring/proving a fixed point. -/
structure OfficialDescriptorSchedule (Unit : Type*) where
  tasks : List (OfficialDescriptorTask Unit)

namespace OfficialDescriptorSchedule

variable {Unit : Type*} [DecidableEq Unit]

/-- Run a schedule once from a supplied environment. -/
def runOnceFrom (schedule : OfficialDescriptorSchedule Unit)
    (env : OfficialDescriptorEnvironment Unit) : OfficialDescriptorEnvironment Unit :=
  env.runTasks schedule.tasks

/-- Iterate a schedule with finite fuel. -/
def runFrom (schedule : OfficialDescriptorSchedule Unit)
    (initial : OfficialDescriptorEnvironment Unit) : ℕ → OfficialDescriptorEnvironment Unit
  | 0 => initial
  | fuel + 1 => schedule.runOnceFrom (schedule.runFrom initial fuel)

/-- A schedule-level fixed point: another pass makes no changes. -/
def FixedPoint (schedule : OfficialDescriptorSchedule Unit)
    (env : OfficialDescriptorEnvironment Unit) : Prop :=
  schedule.runOnceFrom env = env

@[simp] theorem runFrom_zero (schedule : OfficialDescriptorSchedule Unit)
    (initial : OfficialDescriptorEnvironment Unit) :
    schedule.runFrom initial 0 = initial :=
  rfl

@[simp] theorem runFrom_succ (schedule : OfficialDescriptorSchedule Unit)
    (initial : OfficialDescriptorEnvironment Unit) (fuel : ℕ) :
    schedule.runFrom initial (fuel + 1) =
      schedule.runOnceFrom (schedule.runFrom initial fuel) :=
  rfl

/-- If two consecutive schedule iterations are equal, the earlier state is a fixed point. -/
theorem fixedPoint_of_runFrom_stabilizes (schedule : OfficialDescriptorSchedule Unit)
    (initial : OfficialDescriptorEnvironment Unit) {fuel : ℕ}
    (h : schedule.runFrom initial (fuel + 1) = schedule.runFrom initial fuel) :
    schedule.FixedPoint (schedule.runFrom initial fuel) := by
  simpa [FixedPoint] using h

/-- Once a fixed point is reached, one more schedule pass leaves the environment unchanged. -/
theorem runOnceFrom_eq_of_fixedPoint (schedule : OfficialDescriptorSchedule Unit)
    {env : OfficialDescriptorEnvironment Unit} (h : schedule.FixedPoint env) :
    schedule.runOnceFrom env = env :=
  h

end OfficialDescriptorSchedule

namespace OfficialRule5Descriptor

/-- Recover the current tetrahedral `R/S` descriptor from an official Rule-5 value when possible. -/
def toRS? : OfficialRule5Descriptor → Option RS
  | ⟨OfficialRule5DescriptorKind.tetrahedralCenter, false, OfficialDescriptorSense.senior⟩ =>
      some RS.R
  | ⟨OfficialRule5DescriptorKind.tetrahedralCenter, false, OfficialDescriptorSense.junior⟩ =>
      some RS.S
  | _ => none

@[simp] theorem toRS?_ofRS (descriptor : RS) :
    (ofRS descriptor).toRS? = some descriptor := by
  cases descriptor <;> rfl

end OfficialRule5Descriptor

namespace DescriptorDiscoveryState

variable {m : MultiCenterMolecule V} {cfg : m.Configuration}

/-- Shared Rule 4a class projection for a discovery state.  Lowercase pseudoasymmetry takes
precedence over the local uppercase `R/S` seed: a pseudoasymmetric descriptor establishes the
stereogenic-unit class, while the `R/S` seed continues to be tracked separately for Rule 5. -/
def rule4aKindAt? (state : DescriptorDiscoveryState m cfg) (center : m.Center) :
    Option OfficialStereogenicUnitKind :=
  Option.first
    ((state.pseudo center).map fun _ => OfficialStereogenicUnitKind.pseudoasymmetric)
    ((state.rs center).map fun _ => OfficialStereogenicUnitKind.chiral)

@[simp] theorem rule4aKindAt?_eq_some_of_pseudo_eq_some
    (state : DescriptorDiscoveryState m cfg) {center : m.Center} {descriptor : PseudoRS}
    (h : state.pseudo center = some descriptor) :
    state.rule4aKindAt? center = some OfficialStereogenicUnitKind.pseudoasymmetric := by
  simp [rule4aKindAt?, h]

@[simp] theorem rule4aKindAt?_eq_some_chiral_of_pseudo_eq_none_rs_eq_some
    (state : DescriptorDiscoveryState m cfg) {center : m.Center} {descriptor : RS}
    (hpseudo : state.pseudo center = none) (hrs : state.rs center = some descriptor) :
    state.rule4aKindAt? center = some OfficialStereogenicUnitKind.chiral := by
  simp [rule4aKindAt?, hpseudo, hrs]

@[simp] theorem rule4aKindAt?_eq_none_of_pseudo_eq_none_rs_eq_none
    (state : DescriptorDiscoveryState m cfg) {center : m.Center}
    (hpseudo : state.pseudo center = none) (hrs : state.rs center = none) :
    state.rule4aKindAt? center = none := by
  simp [rule4aKindAt?, hpseudo, hrs]

/-- Embed the legacy tetrahedral descriptor-discovery state into the general official descriptor
environment.  `R/S` facts become Rule 5 facts; lowercase pseudo facts become Rule 4c facts; the
Rule 4a class comes from the shared projection, which prefers pseudoasymmetry over the `R/S` seed. -/
def toOfficialDescriptorEnvironment (state : DescriptorDiscoveryState m cfg) :
    OfficialDescriptorEnvironment m.Center where
  rule3Geometry := fun _ => none
  rule4aKind := state.rule4aKindAt?
  rule4bPair := fun _ => none
  rule4cDescriptor := fun center =>
    (state.pseudo center).map OfficialPseudoasymmetricDescriptor.ofPseudoRS
  rule5Descriptor := fun center => (state.rs center).map OfficialRule5Descriptor.ofRS

@[simp] theorem toOfficialDescriptorEnvironment_rule4aKind_eq_rule4aKindAt?
    (state : DescriptorDiscoveryState m cfg) (center : m.Center) :
    (state.toOfficialDescriptorEnvironment).rule4aKind center =
      state.rule4aKindAt? center :=
  rfl

/-- Rule 4a classification from a pseudoasymmetric descriptor, independent of the local `R/S`
seed.  This is the corrected bridge: it does not consult `state.rs` at all. -/
@[simp] theorem toOfficialDescriptorEnvironment_rule4aKind_eq_some_of_pseudo_eq_some
    (state : DescriptorDiscoveryState m cfg) {center : m.Center} {descriptor : PseudoRS}
    (h : state.pseudo center = some descriptor) :
    (state.toOfficialDescriptorEnvironment).rule4aKind center =
      some OfficialStereogenicUnitKind.pseudoasymmetric := by
  simp [toOfficialDescriptorEnvironment, rule4aKindAt?, h]

/-- With no pseudoasymmetric descriptor, an available `R/S` seed classifies as chiral. -/
@[simp] theorem toOfficialDescriptorEnvironment_rule4aKind_eq_some_chiral_of_pseudo_eq_none
    (state : DescriptorDiscoveryState m cfg) {center : m.Center} {descriptor : RS}
    (hpseudo : state.pseudo center = none) (hrs : state.rs center = some descriptor) :
    (state.toOfficialDescriptorEnvironment).rule4aKind center =
      some OfficialStereogenicUnitKind.chiral := by
  simp [toOfficialDescriptorEnvironment, rule4aKindAt?, hpseudo, hrs]

@[simp] theorem toOfficialDescriptorEnvironment_rule5_of_rs_eq_some
    (state : DescriptorDiscoveryState m cfg) {center : m.Center} {descriptor : RS}
    (h : state.rs center = some descriptor) :
    (state.toOfficialDescriptorEnvironment).rule5Descriptor center =
      some (OfficialRule5Descriptor.ofRS descriptor) := by
  simp [toOfficialDescriptorEnvironment, h]

@[simp] theorem toOfficialDescriptorEnvironment_rule4c_of_pseudo_eq_some
    (state : DescriptorDiscoveryState m cfg) {center : m.Center} {descriptor : PseudoRS}
    (h : state.pseudo center = some descriptor) :
    (state.toOfficialDescriptorEnvironment).rule4cDescriptor center =
      some (OfficialPseudoasymmetricDescriptor.ofPseudoRS descriptor) := by
  simp [toOfficialDescriptorEnvironment, h]

end DescriptorDiscoveryState

namespace Rule5DiscoveryTask

variable {m : MultiCenterMolecule V} {cfg : m.Configuration}





def toOfficialDescriptorTask (task : Rule5DiscoveryTask m cfg) :
    OfficialDescriptorTask m.Center where
  target := task.center
  requirements :=
    [ { unit := task.leftSource, slot := OfficialDescriptorSlot.rule5Descriptor }
    , { unit := task.rightSource, slot := OfficialDescriptorSlot.rule5Descriptor }
    ]
  resolve? := fun env =>
    match (env.rule5Descriptor task.leftSource).bind OfficialRule5Descriptor.toRS?,
        (env.rule5Descriptor task.rightSource).bind OfficialRule5Descriptor.toRS? with
    | some leftDescriptor, some rightDescriptor =>
        if leftDescriptor = rightDescriptor then none
        else
          some
            (OfficialDescriptorValue.rule4cDescriptor
              (OfficialPseudoasymmetricDescriptor.ofPseudoRS
                (pseudoDescriptor (m.configurationSign cfg task.center)
                  leftDescriptor rightDescriptor)))
    | _, _ => none

/-- Distinct available source descriptors retain the legacy official computation. -/
theorem toOfficialDescriptorTask_resolve?_eq_some_of_rs_sources_ne
    (task : Rule5DiscoveryTask m cfg) (state : DescriptorDiscoveryState m cfg)
    {leftDescriptor rightDescriptor : RS}
    (hleft : state.rs task.leftSource = some leftDescriptor)
    (hright : state.rs task.rightSource = some rightDescriptor)
    (hne : leftDescriptor ≠ rightDescriptor) :
    task.toOfficialDescriptorTask.resolve? state.toOfficialDescriptorEnvironment =
      some
        (OfficialDescriptorValue.rule4cDescriptor
          (OfficialPseudoasymmetricDescriptor.ofPseudoRS
            (pseudoDescriptor (m.configurationSign cfg task.center)
              leftDescriptor rightDescriptor))) := by
  simp [toOfficialDescriptorTask, DescriptorDiscoveryState.toOfficialDescriptorEnvironment,
    hleft, hright, hne]

/-- Historical name for the official resolution theorem, retained with the now-necessary
distinct-source premise.  The premise is not implied by readiness. -/
theorem toOfficialDescriptorTask_resolve?_eq_some_of_rs_sources
    (task : Rule5DiscoveryTask m cfg) (state : DescriptorDiscoveryState m cfg)
    {leftDescriptor rightDescriptor : RS}
    (hleft : state.rs task.leftSource = some leftDescriptor)
    (hright : state.rs task.rightSource = some rightDescriptor)
    (hne : leftDescriptor ≠ rightDescriptor) :
    task.toOfficialDescriptorTask.resolve? state.toOfficialDescriptorEnvironment =
      some
        (OfficialDescriptorValue.rule4cDescriptor
          (OfficialPseudoasymmetricDescriptor.ofPseudoRS
            (pseudoDescriptor (m.configurationSign cfg task.center)
              leftDescriptor rightDescriptor))) :=
  toOfficialDescriptorTask_resolve?_eq_some_of_rs_sources_ne task state hleft hright hne

/-- Equal available source descriptors are refused by the actual official adapter. -/
theorem toOfficialDescriptorTask_resolve?_eq_none_of_rs_sources_eq
    (task : Rule5DiscoveryTask m cfg) (state : DescriptorDiscoveryState m cfg)
    {descriptor : RS}
    (hleft : state.rs task.leftSource = some descriptor)
    (hright : state.rs task.rightSource = some descriptor) :
    task.toOfficialDescriptorTask.resolve? state.toOfficialDescriptorEnvironment = none := by
  simp [toOfficialDescriptorTask, DescriptorDiscoveryState.toOfficialDescriptorEnvironment,
    hleft, hright]

theorem toOfficialDescriptorTask_resolve?_eq_none_of_left_source_none
    (task : Rule5DiscoveryTask m cfg) (state : DescriptorDiscoveryState m cfg)
    (h : state.rs task.leftSource = none) :
    task.toOfficialDescriptorTask.resolve? state.toOfficialDescriptorEnvironment = none := by
  simp [toOfficialDescriptorTask, DescriptorDiscoveryState.toOfficialDescriptorEnvironment, h]

theorem toOfficialDescriptorTask_resolve?_eq_none_of_right_source_none
    (task : Rule5DiscoveryTask m cfg) (state : DescriptorDiscoveryState m cfg)
    (h : state.rs task.rightSource = none) :
    task.toOfficialDescriptorTask.resolve? state.toOfficialDescriptorEnvironment = none := by
  simp [toOfficialDescriptorTask, DescriptorDiscoveryState.toOfficialDescriptorEnvironment, h]

end Rule5DiscoveryTask

end
end OneCenter
end TetraStereo
