import TetraStereo.OneCenter.OfficialDescriptorEnvironment

set_option autoImplicit false

namespace TetraStereo
namespace Examples
namespace OfficialDescriptorEnvironment

open OneCenter

/-- Tiny stereochemical-unit universe used to exercise the general descriptor environment. -/
inductive DemoUnit where
  | leftSource
  | rightSource
  | middleTarget
  deriving DecidableEq, Repr, Fintype

open DemoUnit

def initialEnv : OneCenter.OfficialDescriptorEnvironment DemoUnit :=
  ((OneCenter.OfficialDescriptorEnvironment.empty.assign leftSource
    (OfficialDescriptorValue.rule5Descriptor OfficialRule5Descriptor.descriptorR)).assign
      rightSource
      (OfficialDescriptorValue.rule5Descriptor OfficialRule5Descriptor.descriptorS))

def pseudoRequirementLeft : OfficialDescriptorRequirement DemoUnit where
  unit := leftSource
  slot := OfficialDescriptorSlot.rule5Descriptor

def pseudoRequirementRight : OfficialDescriptorRequirement DemoUnit where
  unit := rightSource
  slot := OfficialDescriptorSlot.rule5Descriptor



def pseudoTask : OfficialDescriptorTask DemoUnit where
  target := middleTarget
  requirements := [pseudoRequirementLeft, pseudoRequirementRight]
  resolve? := fun env =>
    match (env.rule5Descriptor leftSource).bind OfficialRule5Descriptor.toRS?,
        (env.rule5Descriptor rightSource).bind OfficialRule5Descriptor.toRS? with
    | some RS.R, some RS.S =>
        some (OfficialDescriptorValue.rule4cDescriptor OfficialPseudoasymmetricDescriptor.r)
    | _, _ => none

def pseudoSchedule : OfficialDescriptorSchedule DemoUnit where
  tasks := [pseudoTask]

example :
    pseudoTask.resolve? initialEnv =
      some (OfficialDescriptorValue.rule4cDescriptor OfficialPseudoasymmetricDescriptor.r) := by
  simp [pseudoTask, initialEnv, OneCenter.OfficialDescriptorEnvironment.assign,
    OfficialRule5Descriptor.toRS?, OfficialRule5Descriptor.descriptorR,
    OfficialRule5Descriptor.descriptorS]

example :
    (pseudoSchedule.runFrom initialEnv 1).value? middleTarget
        OfficialDescriptorSlot.rule4cDescriptor =
      some (OfficialDescriptorValue.rule4cDescriptor OfficialPseudoasymmetricDescriptor.r) := by
  have hresolve :
      pseudoTask.resolve? initialEnv =
        some (OfficialDescriptorValue.rule4cDescriptor OfficialPseudoasymmetricDescriptor.r) := by
    simp [pseudoTask, initialEnv, OneCenter.OfficialDescriptorEnvironment.assign,
      OfficialRule5Descriptor.toRS?, OfficialRule5Descriptor.descriptorR,
      OfficialRule5Descriptor.descriptorS]
  have happly :=
    pseudoTask.apply_value?_eq_some_of_resolve?_eq_some initialEnv
      (OfficialDescriptorValue.rule4cDescriptor OfficialPseudoasymmetricDescriptor.r) hresolve
  simpa [pseudoSchedule, OfficialDescriptorSchedule.runFrom,
    OfficialDescriptorSchedule.runOnceFrom, OfficialDescriptorEnvironment.runTasks_singleton] using
    happly

example
    (h : pseudoSchedule.runFrom initialEnv 2 = pseudoSchedule.runFrom initialEnv 1) :
    pseudoSchedule.FixedPoint (pseudoSchedule.runFrom initialEnv 1) := by
  exact pseudoSchedule.fixedPoint_of_runFrom_stabilizes initialEnv h

/-- Perceived descriptor-pair evidence can be lifted directly into the general environment and then
viewed as an official ligand context. -/
example :
    (OneCenter.OfficialDescriptorEnvironment.fromPerceivedEvidence
      (fun _ : DemoUnit =>
        PerceivedLigandEvidence.ofDescriptorPair
          (PerceivedDescriptor.tetrahedral RS.R)
          (PerceivedDescriptor.helical HelicalDescriptor.M))).toOfficialLigandRuleContext
        leftSource =
      (PerceivedLigandEvidence.ofDescriptorPair
        (PerceivedDescriptor.tetrahedral RS.R)
        (PerceivedDescriptor.helical HelicalDescriptor.M)).toOfficialLigandRuleContext := by
  rfl

end OfficialDescriptorEnvironment
end Examples
end TetraStereo
