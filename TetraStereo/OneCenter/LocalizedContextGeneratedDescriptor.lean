import TetraStereo.OneCenter.LocalizedContextFrameCompilation
import TetraStereo.OneCenter.LocalizedContextFullComparison
import TetraStereo.OneCenter.LocalizedContextActualReadingShape
import TetraStereo.OneCenter.LocalizedContextIndependentExpansion
import TetraStereo.OneCenter.LocalizedContextDescriptorExecution
import TetraStereo.OneCenter.DeclarativeCIPContextualDescriptor
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! End-to-end generated descriptor meaning at arbitrary detected carrier occurrences.
All actual four-arm builds, reference populations, reading orders, complete comparisons, tracked
counts and geometry execution are derived. The independent judgment uses the retained molecular
context and the certified input's atom coordinates, including missing-coordinate refusal. -/

namespace TetraStereo.OneCenter.LocalizedRuleMajorReference
open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
noncomputable section

namespace ContextFrameCompilation
variable {input : Input} {target : Occurrence input}
  {unit : DetectedOccurrence input.certified.moleculeGraph}
  {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}
  (frames : ContextFrameCompilation input target unit targetUnit)

def graphs : Fin 4 → RootedDigraph input.certified.Atom :=
  fun slot => ruleMajorTreeGraph (frames.stages slot).a.tree

def keys : Fin 4 → CompleteLigandRule5Key :=
  contextualFrameKeysAt input.certified.moleculeGraph (descriptorMap input) unit
    frames.graphs frames.W frames.D

def ligandAtoms : Fin 4 → input.certified.Atom :=
  fun slot => input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
    (frames.detectedLigandPermutation slot)

def coordinates : Fin 4 → Option CartesianPoint3 :=
  fun slot => input.certified.spatialPointAt? (frames.ligandAtoms slot)

theorem cursor_coordinates (slot : Fin 4) :
    input.certified.localizedRerootCursorSpatialPoint? (frames.frame.cursorAt slot) =
      frames.coordinates slot := by
  unfold localizedRerootCursorSpatialPoint?
  rw [frames.ligandAt]
  rfl

theorem graphs_faithful
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic) (slot : Fin 4) :
    RootedDigraph.FaithfulExactExpansion input.certified.moleculeGraph
      unit.1.atom (frames.ligandAtoms slot) (frames.graphs slot) := by
  have current := ((input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff
    target frames.center).mp frames.centerComputed).2
  rw [frames.centerEq] at current
  exact ruleMajorContextArm_faithfulExactExpansion_of_actualChild input.certified singleBonded acyclic
    ⟨target, none⟩ (frames.frame.cursorAt slot) (frames.childAt slot)
    (frames.stages slot).a current (frames.ligandAt slot)

theorem keys_eq_of_faithful
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (other : Fin 4 → RootedDigraph input.certified.Atom)
    (faithful : ∀ slot, RootedDigraph.FaithfulExactExpansion input.certified.moleculeGraph
      unit.1.atom (frames.ligandAtoms slot) (other slot)) :
    frames.keys = contextualFrameKeysAt input.certified.moleculeGraph (descriptorMap input)
      unit other frames.W frames.D := by
  have current := ((input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff
    target frames.center).mp frames.centerComputed).2
  rw [frames.centerEq] at current
  funext slot
  exact generatedContextArm_contextualCompleteLigandRule5KeyAt_eq_of_faithful input
    singleBonded acyclic ⟨target, none⟩ (frames.frame.cursorAt slot) (frames.childAt slot)
    (frames.stages slot).a unit current (frames.ligandAt slot) (other slot) (faithful slot)
    frames.W frames.D

def executionData
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic) :
    input.certified.ContextDescriptorExecutionData target (contextOccurrenceView input target) where
  center := frames.center
  centerComputed := frames.centerComputed
  frame := frames.frame
  frameComputed := frames.frameComputed
  compounds := frames.compounds
  keys := frames.keys
  callbackEq := frames.callbackEq
  fullOrdering := by
    intro left right
    exact generatedContextCompound_full_compare input singleBonded acyclic ⟨target, none⟩
      unit targetUnit (frames.frame.cursorAt left) (frames.frame.cursorAt right)
      (frames.childAt left) (frames.childAt right) (frames.stages left) (frames.stages right)
      (frames.widthBound left) (frames.depthBound left)
      (frames.widthBound right) (frames.depthBound right)
      (frames.compoundBuilt left) (frames.compoundBuilt right)
  priorComparison := by
    intro left right
    exact generatedContextCompound_prior_compare input singleBonded acyclic ⟨target, none⟩
      unit targetUnit (frames.frame.cursorAt left) (frames.frame.cursorAt right)
      (frames.childAt left) (frames.childAt right) (frames.stages left) (frames.stages right)
      (frames.widthBound left) (frames.depthBound left)
      (frames.widthBound right) (frames.depthBound right)
      (frames.compoundBuilt left) (frames.compoundBuilt right)
  shaped := by
    intro slot
    obtain ⟨compound, built, shaped⟩ :=
      exists_generatedContextCompound_rule5ReadingShape input singleBonded acyclic
        ⟨target, none⟩ unit targetUnit (frames.frame.cursorAt slot) (frames.childAt slot)
    have equal : frames.compounds slot = compound :=
      Option.some.inj ((frames.compoundBuilt slot).symm.trans built)
    rwa [equal]

theorem exec_some_iff_contextualJudgment
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (descriptor : LocalizedAuxiliaryLabel) :
    input.certified.ruleMajorDescriptorExec? target (contextOccurrenceView input target) =
        some descriptor ↔
      ContextualDescriptorJudgmentAt input.certified.moleculeGraph (descriptorMap input) unit
        frames.graphs frames.W frames.D frames.coordinates descriptor := by
  have result := (frames.executionData singleBonded acyclic).exec_some_iff_completeRootJudgment
    descriptor
  change _ ↔ ∃ points, (∀ slot,
    input.certified.localizedRerootCursorSpatialPoint? (frames.frame.cursorAt slot) =
      some (points slot)) ∧ CompleteRootDescriptorJudgment frames.keys points descriptor at result
  simpa only [frames.cursor_coordinates, ContextualDescriptorJudgmentAt, keys] using result

theorem exec_none_iff_no_contextualJudgment
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic) :
    input.certified.ruleMajorDescriptorExec? target (contextOccurrenceView input target) = none ↔
      ¬ ∃ descriptor,
        ContextualDescriptorJudgmentAt input.certified.moleculeGraph (descriptorMap input) unit
          frames.graphs frames.W frames.D frames.coordinates descriptor := by
  have result := (frames.executionData singleBonded acyclic).exec_none_iff_no_completeRootJudgment
  change _ ↔ ¬ ∃ descriptor, ∃ points, (∀ slot,
    input.certified.localizedRerootCursorSpatialPoint? (frames.frame.cursorAt slot) =
      some (points slot)) ∧ CompleteRootDescriptorJudgment frames.keys points descriptor at result
  simpa only [frames.cursor_coordinates, ContextualDescriptorJudgmentAt, keys] using result

theorem referenceState_some_iff_contextualJudgment
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (descriptor : LocalizedAuxiliaryLabel) :
    referenceState input target = some descriptor ↔
      ContextualDescriptorJudgmentAt input.certified.moleculeGraph (descriptorMap input) unit
        frames.graphs frames.W frames.D frames.coordinates descriptor := by
  rw [← reference_fixed input target, ← input.certified.ruleMajorDescriptorExec?_eq]
  exact frames.exec_some_iff_contextualJudgment singleBonded acyclic descriptor

theorem referenceState_none_iff_no_contextualJudgment
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic) :
    referenceState input target = none ↔
      ¬ ∃ descriptor,
        ContextualDescriptorJudgmentAt input.certified.moleculeGraph (descriptorMap input) unit
          frames.graphs frames.W frames.D frames.coordinates descriptor := by
  rw [← reference_fixed input target, ← input.certified.ruleMajorDescriptorExec?_eq]
  exact frames.exec_none_iff_no_contextualJudgment singleBonded acyclic

theorem referenceState_outcome
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic) :
    ContextualOutcomeAt input.certified.moleculeGraph (descriptorMap input) unit
      frames.graphs frames.W frames.D frames.coordinates (referenceState input target) := by
  cases result : referenceState input target with
  | none => exact (frames.referenceState_none_iff_no_contextualJudgment singleBonded acyclic).mp result
  | some descriptor =>
      exact (frames.referenceState_some_iff_contextualJudgment singleBonded acyclic descriptor).mp result

theorem referenceState_lowercase_iff
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    {descriptor : LocalizedAuxiliaryLabel}
    (returned : referenceState input target = some descriptor) :
    descriptor.IsLowercase ↔ completeRule5PairCount frames.keys = 1 := by
  exact contextualDescriptorJudgmentAt_lowercase_iff
    ((frames.referenceState_some_iff_contextualJudgment singleBonded acyclic descriptor).mp returned)

/-- The generated result has the same independent meaning on every faithful exact expansion of
each actual physical ligand. No runtime tree or builder equations are hypotheses on `other`. -/
theorem referenceState_some_iff_faithfulJudgment
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (other : Fin 4 → RootedDigraph input.certified.Atom)
    (faithful : ∀ slot, RootedDigraph.FaithfulExactExpansion input.certified.moleculeGraph
      unit.1.atom (frames.ligandAtoms slot) (other slot))
    (descriptor : LocalizedAuxiliaryLabel) :
    referenceState input target = some descriptor ↔
      ContextualDescriptorJudgmentAt input.certified.moleculeGraph (descriptorMap input) unit
        other frames.W frames.D frames.coordinates descriptor := by
  rw [frames.referenceState_some_iff_contextualJudgment singleBonded acyclic]
  unfold ContextualDescriptorJudgmentAt
  change (∃ points, (∀ slot, frames.coordinates slot = some (points slot)) ∧
    CompleteRootDescriptorJudgment frames.keys points descriptor) ↔ _
  rw [frames.keys_eq_of_faithful singleBonded acyclic other faithful]

theorem referenceState_none_iff_no_faithfulJudgment
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (other : Fin 4 → RootedDigraph input.certified.Atom)
    (faithful : ∀ slot, RootedDigraph.FaithfulExactExpansion input.certified.moleculeGraph
      unit.1.atom (frames.ligandAtoms slot) (other slot)) :
    referenceState input target = none ↔
      ¬ ∃ descriptor,
        ContextualDescriptorJudgmentAt input.certified.moleculeGraph (descriptorMap input) unit
          other frames.W frames.D frames.coordinates descriptor := by
  rw [frames.referenceState_none_iff_no_contextualJudgment singleBonded acyclic]
  unfold ContextualDescriptorJudgmentAt
  change (¬ ∃ descriptor, ∃ points, (∀ slot, frames.coordinates slot = some (points slot)) ∧
    CompleteRootDescriptorJudgment frames.keys points descriptor) ↔ _
  rw [frames.keys_eq_of_faithful singleBonded acyclic other faithful]

end ContextFrameCompilation

/-- This construction derives the entire comparison and geometry interface at an arbitrary
detected occurrence; its path need not be empty. -/
def generatedContextFrameCompilation
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : Occurrence input)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1) :
    ContextFrameCompilation input target unit targetUnit :=
  Classical.choice (exists_contextFrameCompilation input singleBonded acyclic target unit targetUnit)

/-- Every generated detected auxiliary occurrence satisfies the independent retained-context
outcome, including exact refusal when no strict-priority geometric descriptor exists. -/
theorem every_detected_auxiliary_occurrence_contextual_outcome
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : Occurrence input)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1) :
    let frames := generatedContextFrameCompilation input singleBonded acyclic target unit targetUnit
    ContextualOutcomeAt input.certified.moleculeGraph (descriptorMap input) unit
      frames.graphs frames.W frames.D frames.coordinates (referenceState input target) := by
  exact ContextFrameCompilation.referenceState_outcome
    (generatedContextFrameCompilation input singleBonded acyclic target unit targetUnit)
    singleBonded acyclic

end
end TetraStereo.OneCenter.LocalizedRuleMajorReference

assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.cursor_coordinates
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.graphs_faithful
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.keys_eq_of_faithful
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.executionData
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.exec_some_iff_contextualJudgment
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.exec_none_iff_no_contextualJudgment
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.referenceState_some_iff_contextualJudgment
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.referenceState_none_iff_no_contextualJudgment
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.referenceState_outcome
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.referenceState_lowercase_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.referenceState_some_iff_faithfulJudgment
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.referenceState_none_iff_no_faithfulJudgment
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.every_detected_auxiliary_occurrence_contextual_outcome
