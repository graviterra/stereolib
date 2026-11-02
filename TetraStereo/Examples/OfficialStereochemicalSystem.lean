import TetraStereo.OneCenter.OfficialStereochemicalSystem

set_option autoImplicit false

namespace TetraStereo
namespace Examples
namespace OfficialStereochemicalSystem

open OneCenter

/-- Tiny stereochemical-unit universe for exercising the system-level detector layer. -/
inductive DemoUnit where
  | leftBranch
  | rightBranch
  | dependentUnit
  deriving DecidableEq, Repr, Fintype

open DemoUnit

def leftRule5Requirement : OfficialDescriptorRequirement DemoUnit where
  unit := leftBranch
  slot := OfficialDescriptorSlot.rule5Descriptor

def rightRule5Requirement : OfficialDescriptorRequirement DemoUnit where
  unit := rightBranch
  slot := OfficialDescriptorSlot.rule5Descriptor

def demoInitialEnvironment : OfficialDescriptorEnvironment DemoUnit :=
  ((OfficialDescriptorEnvironment.empty.assign leftBranch
    (OfficialDescriptorValue.rule5Descriptor OfficialRule5Descriptor.descriptorR)).assign
      rightBranch
      (OfficialDescriptorValue.rule5Descriptor OfficialRule5Descriptor.descriptorS))


def demoRule4cTask : OfficialDescriptorTask DemoUnit where
  target := dependentUnit
  requirements := [leftRule5Requirement, rightRule5Requirement]
  resolve? := fun env =>
    match (env.rule5Descriptor leftBranch).bind OfficialRule5Descriptor.toRS?,
        (env.rule5Descriptor rightBranch).bind OfficialRule5Descriptor.toRS? with
    | some RS.R, some RS.S =>
        some (OfficialDescriptorValue.rule4cDescriptor OfficialPseudoasymmetricDescriptor.r)
    | _, _ => none

def demoOutput : OfficialDetectorOutput DemoUnit where
  initialEnvironment := demoInitialEnvironment
  schedule := { tasks := [demoRule4cTask] }

def emptyOutput : OfficialDetectorOutput DemoUnit where
  initialEnvironment := OfficialDescriptorEnvironment.empty
  schedule := { tasks := [demoRule4cTask] }

example :
    (demoOutput.finalEnvironment 1).value? dependentUnit
        OfficialDescriptorSlot.rule4cDescriptor =
      some (OfficialDescriptorValue.rule4cDescriptor OfficialPseudoasymmetricDescriptor.r) := by
  have hresolve :
      demoRule4cTask.resolve? demoInitialEnvironment =
        some (OfficialDescriptorValue.rule4cDescriptor OfficialPseudoasymmetricDescriptor.r) := by
    simp [demoRule4cTask, demoInitialEnvironment, OfficialDescriptorEnvironment.assign,
      OfficialRule5Descriptor.toRS?, OfficialRule5Descriptor.descriptorR,
      OfficialRule5Descriptor.descriptorS]
  have happly :=
    demoRule4cTask.apply_value?_eq_some_of_resolve?_eq_some demoInitialEnvironment
      (OfficialDescriptorValue.rule4cDescriptor OfficialPseudoasymmetricDescriptor.r) hresolve
  simpa [demoOutput, OfficialDetectorOutput.finalEnvironment,
    OfficialDescriptorSchedule.runFrom, OfficialDescriptorSchedule.runOnceFrom,
    OfficialDescriptorEnvironment.runTasks_singleton] using happly

example :
    demoRule4cTask.safeResolve? OfficialDescriptorEnvironment.empty = none := by
  simp [OfficialDescriptorTask.safeResolve?, demoRule4cTask, leftRule5Requirement,
    rightRule5Requirement, OfficialDescriptorEnvironment.requirementsReady,
    OfficialDescriptorEnvironment.empty, OfficialDescriptorEnvironment.value?]

example :
    emptyOutput.safeDescriptorValue? 0 [leftRule5Requirement] dependentUnit
        OfficialDescriptorSlot.rule4cDescriptor =
      none := by
  have hnotReady :
      (emptyOutput.finalEnvironment 0).requirementsReady [leftRule5Requirement] = false := by
    simp [emptyOutput, OfficialDetectorOutput.finalEnvironment, leftRule5Requirement,
      OfficialDescriptorEnvironment.requirementsReady, OfficialDescriptorEnvironment.empty,
      OfficialDescriptorEnvironment.value?]
  exact
    emptyOutput.safeDescriptorValue?_eq_none_of_requirementsReady_eq_false 0
      [leftRule5Requirement] dependentUnit OfficialDescriptorSlot.rule4cDescriptor hnotReady

example
    (h : demoOutput.finalEnvironment 2 = demoOutput.finalEnvironment 1) :
    demoOutput.FixedAt 1 := by
  exact demoOutput.fixedAt_of_finalEnvironment_stabilizes h

example
    {V Unit : Type*} [Fintype V] [DecidableEq V] [DecidableEq Unit]
    (m : OneCenter.MultiCenterMolecule V) (output : OfficialDetectorOutput Unit)
    (ligandUnit : m.Center → Fin 4 → Unit) {fuel : ℕ} (h : output.FixedAt fuel) :
    m.officialSystemContextFromDetector output ligandUnit (fuel + 1) =
      m.officialSystemContextFromDetector output ligandUnit fuel := by
  exact m.officialSystemContextFromDetector_succ_eq_of_fixedAt output ligandUnit h

example
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenter.MultiCenterMolecule V) (center : m.Center) :
    (m.tetrahedralCenterRegistry).kind center =
      OfficialStereochemicalUnitKind.tetrahedralCenter := by
  simp

end OfficialStereochemicalSystem
end Examples
end TetraStereo
