import TetraStereo.OneCenter.DeclarativeCIPRetainedContextDescriptor
import TetraStereo.OneCenter.LocalizedContextActualReadingShape
import TetraStereo.OneCenter.LocalizedContextDescriptorExecution
import TetraStereo.OneCenter.LocalizedCyclicContextFrameCompilation
import TetraStereo.OneCenter.LocalizedRetainedContextRule5Comparison
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! Own reference state at a real detected carrier occurrence, read on the actual compiled arm
graphs.

The four arm graphs are `ruleMajorTreeGraph` of the compiled Rule-4a stages. Their retained
keys, prior order, and through-Rule-5 order are derived from
`retainedGeneratedCompound_prior_compare` and `retainedGeneratedCompound_throughRule5`. The
common windows, compounds, and stage bounds are fields of the compiled frame. No comparator
strictness, reference selection, reader agreement, sorting success, or chosen letter is assumed.
Missing coordinates and unresolved full-key ties remain ordinary refusals.

These graphs are the actual stage graphs. This module does not transport the judgment along an
independent faithful cut arm; that replacement belongs to `LocalizedRetainedArmExpansion`. An
auxiliary target keeps its stored carrier root and address, the outer context. A final-report
center is read at `localizedFinalOccurrenceExecutable`, whose root is that center.
-/

namespace TetraStereo.OneCenter.LocalizedRuleMajorReference
open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
noncomputable section
open scoped Classical

namespace ContextFrameCompilation

variable {input : Input}
  {target : Occurrence input}
  {unit : DetectedOccurrence input.certified.moleculeGraph}
  {targetUnit : input.certified.molecularFrameUnit target.1 = unit.1}
  (frames : ContextFrameCompilation input target unit targetUnit)

/-- Actual Rule-4a stage graph of one compiled ligand. This is not a cut-arm transport. -/
def actualArmGraphs : Fin 4 → RootedDigraph input.certified.Atom :=
  fun slot => ruleMajorTreeGraph (frames.stages slot).a.tree

theorem actualArmGraphs_eq_stage (slot : Fin 4) :
    frames.actualArmGraphs slot = ruleMajorTreeGraph (frames.stages slot).a.tree := rfl

/-- Retained complete Rule-5 keys of those actual stage graphs, at the compiled window. -/
def retainedKeys : Fin 4 → CompleteLigandRule5Key :=
  retainedContextualFrameKeysAt input.certified.moleculeGraph (descriptorMap input) unit
    frames.actualArmGraphs frames.W frames.D

theorem retainedKeys_eq_stage (slot : Fin 4) :
    frames.retainedKeys slot =
      retainedCompleteLigandRule5KeyAt input.certified.moleculeGraph (descriptorMap input) unit
        (ruleMajorTreeGraph (frames.stages slot).a.tree) frames.W frames.D := rfl

def actualLigandAtoms : Fin 4 → input.certified.Atom :=
  fun slot => input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
    (frames.detectedLigandPermutation slot)

/-- Certified spatial table at the frame's detected ligand atoms. Absent positions stay `none`. -/
def actualCoordinates : Fin 4 → Option CartesianPoint3 :=
  fun slot => input.certified.spatialPointAt? (frames.actualLigandAtoms slot)

theorem actualCoordinates_eq_source :
    frames.actualCoordinates =
      retainedContextualSourceCoordinates input.certified frames.actualLigandAtoms := rfl

theorem actualCursor_coordinates (slot : Fin 4) :
    input.certified.localizedRerootCursorSpatialPoint? (frames.frame.cursorAt slot) =
      frames.actualCoordinates slot := by
  unfold localizedRerootCursorSpatialPoint? actualCoordinates actualLigandAtoms
  rw [frames.ligandAt]
  rfl

/-- Through-Rule-5 order of the compiled compounds is the retained key order. The equality is
the actual-stage theorem, not a premise. -/
theorem retainedActual_fullOrdering
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) (left right : Fin 4) :
    (input.certified.compareLocalizedRerootCompoundThroughRule5
      (frames.compounds left) (frames.compounds right)).ordering =
      compare (frames.retainedKeys left) (frames.retainedKeys right) := by
  have agreement :=
    RetainedContextRule5Comparison.retainedGeneratedCompound_throughRule5 input singleBonded
      ⟨target, none⟩ unit targetUnit
      (frames.frame.cursorAt left) (frames.frame.cursorAt right)
      (frames.childAt left) (frames.childAt right)
      (frames.stages left) (frames.stages right)
      (frames.widthBound left) (frames.depthBound left)
      (frames.widthBound right) (frames.depthBound right)
      (frames.compoundBuilt left) (frames.compoundBuilt right)
  simpa [retainedKeys, actualArmGraphs, retainedContextualFrameKeysAt] using agreement.1

/-- Prior order of the compiled compounds is the retained prior-key order. -/
theorem retainedActual_priorComparison
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) (left right : Fin 4) :
    input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (frames.compounds left).prior (frames.compounds right).prior =
      compare (ofLex (frames.retainedKeys left)).1 (ofLex (frames.retainedKeys right)).1 := by
  have agreement :=
    RetainedContextCompoundComparison.retainedGeneratedCompound_prior_compare input singleBonded
      ⟨target, none⟩ unit targetUnit
      (frames.frame.cursorAt left) (frames.frame.cursorAt right)
      (frames.childAt left) (frames.childAt right)
      (frames.stages left) (frames.stages right)
      (frames.widthBound left) (frames.depthBound left)
      (frames.widthBound right) (frames.depthBound right)
      (frames.compoundBuilt left) (frames.compoundBuilt right)
  simpa [retainedKeys, actualArmGraphs, retainedContextualFrameKeysAt,
    retainedCompleteLigandRule5KeyAt_prior] using agreement

/-- Every compiled compound has a legal reading shape: no reference, one reference, or both.
The shape is read back from the stages; it is not a selected population. -/
theorem retainedActual_readingShape (index : Fin 4) :
    input.certified.RuleMajorReadingShape (frames.compounds index) := by
  let view := contextOccurrenceView input target
  let read := fun source => input.certified.localizedDependencyLabel target view source
  have uniformBuilt :
      input.certified.buildRuleMajorCompoundRule45KeyWith?
        (fun stage position =>
          input.certified.buildRuleMajorCumulativeWithRead? stage read
            (2 * (carrierFuel input + 1)) position)
        (frames.frame.cursorAt index) = some (frames.compounds index) := by
    rw [← input.certified.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
    rw [← input.certified.buildActualRuleMajorCompoundRule45KeyExec?_eq]
    exact frames.compoundBuilt index
  exact input.certified.contextStages_compound_rule5ReadingShape
    (frames.stages index) uniformBuilt

/-- Execution algebra at the compiled frame. Keys and both comparisons are the derived retained
orders. -/
def retainedExecutionData
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) :
    input.certified.ContextDescriptorExecutionData target
      (contextOccurrenceView input target) where
  center := frames.center
  centerComputed := frames.centerComputed
  frame := frames.frame
  frameComputed := frames.frameComputed
  compounds := frames.compounds
  keys := frames.retainedKeys
  callbackEq := frames.callbackEq
  fullOrdering := frames.retainedActual_fullOrdering singleBonded
  priorComparison := frames.retainedActual_priorComparison singleBonded
  shaped := frames.retainedActual_readingShape

/-- Execution returns a letter exactly when the actual cursors have coordinates and those
coordinates satisfy the independent retained judgment on the actual stage graphs. No coordinate
or nondegeneracy hypothesis is used. This is not a faithful cut-arm statement. -/
theorem exec_some_iff_retainedJudgment
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (descriptor : LocalizedAuxiliaryLabel) :
    input.certified.ruleMajorDescriptorExec? target (contextOccurrenceView input target) =
        some descriptor ↔
      RetainedContextualDescriptorJudgmentAt input.certified.moleculeGraph (descriptorMap input)
        unit frames.actualArmGraphs frames.W frames.D frames.actualCoordinates descriptor := by
  have result :=
    (frames.retainedExecutionData singleBonded).exec_some_iff_completeRootJudgment descriptor
  change _ ↔ ∃ points, (∀ slot,
    input.certified.localizedRerootCursorSpatialPoint? (frames.frame.cursorAt slot) =
      some (points slot)) ∧ CompleteRootDescriptorJudgment frames.retainedKeys points descriptor
    at result
  simpa only [frames.actualCursor_coordinates, RetainedContextualDescriptorJudgmentAt,
    retainedKeys] using result

theorem exec_none_iff_no_retainedJudgment
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) :
    input.certified.ruleMajorDescriptorExec? target (contextOccurrenceView input target) = none ↔
      ¬ ∃ descriptor,
        RetainedContextualDescriptorJudgmentAt input.certified.moleculeGraph (descriptorMap input)
          unit frames.actualArmGraphs frames.W frames.D frames.actualCoordinates descriptor := by
  have result :=
    (frames.retainedExecutionData singleBonded).exec_none_iff_no_completeRootJudgment
  change _ ↔ ¬ ∃ descriptor, ∃ points, (∀ slot,
    input.certified.localizedRerootCursorSpatialPoint? (frames.frame.cursorAt slot) =
      some (points slot)) ∧ CompleteRootDescriptorJudgment frames.retainedKeys points descriptor
    at result
  simpa only [frames.actualCursor_coordinates, RetainedContextualDescriptorJudgmentAt,
    retainedKeys] using result

/-- The own reference state at this carrier target, including a nonroot auxiliary, agrees with
the retained judgment on the actual stage graphs. The target root and address stay as stored. -/
theorem referenceState_some_iff_retainedJudgment
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (descriptor : LocalizedAuxiliaryLabel) :
    referenceState input target = some descriptor ↔
      RetainedContextualDescriptorJudgmentAt input.certified.moleculeGraph (descriptorMap input)
        unit frames.actualArmGraphs frames.W frames.D frames.actualCoordinates descriptor := by
  rw [← reference_fixed input target, ← input.certified.ruleMajorDescriptorExec?_eq]
  exact frames.exec_some_iff_retainedJudgment singleBonded descriptor

theorem referenceState_none_iff_no_retainedJudgment
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) :
    referenceState input target = none ↔
      ¬ ∃ descriptor,
        RetainedContextualDescriptorJudgmentAt input.certified.moleculeGraph (descriptorMap input)
          unit frames.actualArmGraphs frames.W frames.D frames.actualCoordinates descriptor := by
  rw [← reference_fixed input target, ← input.certified.ruleMajorDescriptorExec?_eq]
  exact frames.exec_none_iff_no_retainedJudgment singleBonded

theorem referenceState_retainedOutcome
    (singleBonded : input.certified.moleculeGraph.SimpleBonded) :
    RetainedContextualOutcomeAt input.certified.moleculeGraph (descriptorMap input) unit
      frames.actualArmGraphs frames.W frames.D frames.actualCoordinates
      (referenceState input target) := by
  cases result : referenceState input target with
  | none =>
      exact (frames.referenceState_none_iff_no_retainedJudgment singleBonded).mp result
  | some descriptor =>
      exact (frames.referenceState_some_iff_retainedJudgment singleBonded descriptor).mp result

/-- Lowercase means one independent retained prior tie. This count is `completeRule5PairCount`;
it is not a physical enantiomorphic-pair relation on the arm graphs. -/
theorem referenceState_lowercase_iff
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    {descriptor : LocalizedAuxiliaryLabel}
    (returned : referenceState input target = some descriptor) :
    descriptor.IsLowercase ↔ completeRule5PairCount frames.retainedKeys = 1 := by
  exact retainedContextualDescriptorJudgmentAt_lowercase_iff
    ((frames.referenceState_some_iff_retainedJudgment singleBonded descriptor).mp returned)

/-- An assigned letter is the geometric reading of the independent descending retained-key order
at the actual coordinates. `R` and `S` are that raw orientation; `r` and `s` are the same reading
after the retained prior-pair count. -/
theorem referenceState_eq_descending_geometric_reading
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    {descriptor : LocalizedAuxiliaryLabel}
    (returned : referenceState input target = some descriptor) :
    ∃ (points : Fin 4 → CartesianPoint3) (order : List (Fin 4)) (raw : RS),
      (∀ slot, frames.actualCoordinates slot = some (points slot)) ∧
      order.Perm (List.finRange 4) ∧
      order.Pairwise (fun left right => frames.retainedKeys right < frames.retainedKeys left) ∧
      RationalTetrahedralDescriptor (order.map points) raw ∧
      descriptor = classifyTetrahedralRSPseudo raw
        (completeRule5PairCount frames.retainedKeys) := by
  have judgment :=
    (frames.referenceState_some_iff_retainedJudgment singleBonded descriptor).mp returned
  obtain ⟨points, available, complete⟩ := judgment
  obtain ⟨order, raw, permutation, sorted, rational, descriptorEq⟩ := complete
  exact ⟨points, order, raw, available, permutation, sorted, rational, descriptorEq⟩

end ContextFrameCompilation

/-- On a simple-bonded input, the own state at a real detected carrier occurrence — root or
nonroot — is the retained judgment of its compiled actual arm graphs. Acyclicity is not used.
Independent cut-arm transport is not claimed. -/
theorem referenceState_some_iff_retainedJudgment_of_real
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    (descriptor : LocalizedAuxiliaryLabel) :
    let frames := cyclicContextFrameCompilation input singleBonded target real unit targetUnit
    referenceState input target = some descriptor ↔
      RetainedContextualDescriptorJudgmentAt input.certified.moleculeGraph (descriptorMap input)
        unit frames.actualArmGraphs frames.W frames.D frames.actualCoordinates descriptor :=
  (cyclicContextFrameCompilation input singleBonded target real unit targetUnit).referenceState_some_iff_retainedJudgment singleBonded descriptor

theorem referenceState_none_iff_no_retainedJudgment_of_real
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1) :
    let frames := cyclicContextFrameCompilation input singleBonded target real unit targetUnit
    referenceState input target = none ↔
      ¬ ∃ descriptor,
        RetainedContextualDescriptorJudgmentAt input.certified.moleculeGraph (descriptorMap input)
          unit frames.actualArmGraphs frames.W frames.D frames.actualCoordinates descriptor :=
  (cyclicContextFrameCompilation input singleBonded target real unit targetUnit).referenceState_none_iff_no_retainedJudgment singleBonded

theorem referenceState_retainedOutcome_of_real
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1) :
    let frames := cyclicContextFrameCompilation input singleBonded target real unit targetUnit
    RetainedContextualOutcomeAt input.certified.moleculeGraph (descriptorMap input) unit
      frames.actualArmGraphs frames.W frames.D frames.actualCoordinates
      (referenceState input target) :=
  (cyclicContextFrameCompilation input singleBonded target real unit targetUnit).referenceState_retainedOutcome singleBonded

theorem referenceState_lowercase_iff_of_real
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    {descriptor : LocalizedAuxiliaryLabel}
    (returned : referenceState input target = some descriptor) :
    let frames := cyclicContextFrameCompilation input singleBonded target real unit targetUnit
    descriptor.IsLowercase ↔ completeRule5PairCount frames.retainedKeys = 1 :=
  (cyclicContextFrameCompilation input singleBonded target real unit targetUnit).referenceState_lowercase_iff singleBonded returned

theorem referenceState_eq_descending_geometric_reading_of_real
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : Occurrence input)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    {descriptor : LocalizedAuxiliaryLabel}
    (returned : referenceState input target = some descriptor) :
    let frames := cyclicContextFrameCompilation input singleBonded target real unit targetUnit
    ∃ (points : Fin 4 → CartesianPoint3) (order : List (Fin 4)) (raw : RS),
      (∀ slot, frames.actualCoordinates slot = some (points slot)) ∧
      order.Perm (List.finRange 4) ∧
      order.Pairwise (fun left right => frames.retainedKeys right < frames.retainedKeys left) ∧
      RationalTetrahedralDescriptor (order.map points) raw ∧
      descriptor = classifyTetrahedralRSPseudo raw
        (completeRule5PairCount frames.retainedKeys) :=
  (cyclicContextFrameCompilation input singleBonded target real unit targetUnit).referenceState_eq_descending_geometric_reading singleBonded returned

/-! Final-report centers are their own root occurrences. Auxiliary judgments above keep the
target's outer carrier context and are not substituted for this root. -/

theorem tetrahedralCenter_isDetected
    (input : CertifiedLocalizedCIPInput) (center : input.TetrahedralCenter) :
    IsDetectedCenter input.moleculeGraph center.1 :=
  (input.moleculeGraph.isTetrahedralCenter_iff_neighborFinset_card center.1).mp
    ((input.moleculeGraph.mem_tetrahedralCenterSet center.1).mp center.2)

def finalCenterUnit (input : Input) (center : input.certified.TetrahedralCenter) :
    DetectedOccurrence input.certified.moleculeGraph :=
  ⟨⟨center.1, []⟩, tetrahedralCenter_isDetected input.certified center⟩

theorem finalOccurrence_provenance_real
    (input : Input) (center : input.certified.TetrahedralCenter) :
    (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center).1.node.provenance =
      OfficialCIPNodeProvenance.realAtom := by
  simp [localizedFinalOccurrenceExecutable, localizedFinalRootFrame, OfficialCIPNode.root]

theorem finalOccurrence_molecularFrameUnit
    (input : Input) (center : input.certified.TetrahedralCenter) :
    input.certified.molecularFrameUnit
        (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center).1 =
      (finalCenterUnit input center).1 := by
  unfold finalCenterUnit molecularFrameUnit
  simp [localizedFinalOccurrenceExecutable, localizedFinalRootFrame, OfficialCIPNode.root]

/-- The final report reads each center at `localizedFinalOccurrenceExecutable`, whose root is
that center. -/
theorem analyze_uses_own_final_root (input : Input) :
    (analyze input = input.certified.canonicalTetrahedralCenters.map fun center =>
      (center.val.val, referenceState input
        (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center))) ∧
    ∀ center, (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center).1.root =
      center.val :=
  ⟨analyze_eq_referenceReport input, fun center =>
    input.certified.localizedFinalOccurrenceExecutable_root (carrierFuel input) center⟩

/-- The report state of one center is the retained judgment of the compilation at that center's
own final root, not at an auxiliary outer context. -/
theorem referenceState_at_final_occurrence_some_iff_retainedJudgment
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (center : input.certified.TetrahedralCenter)
    (descriptor : LocalizedAuxiliaryLabel) :
    let target := input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center
    let unit := finalCenterUnit input center
    let frames := cyclicContextFrameCompilation input singleBonded target
      (finalOccurrence_provenance_real input center)
      unit (finalOccurrence_molecularFrameUnit input center)
    referenceState input target = some descriptor ↔
      RetainedContextualDescriptorJudgmentAt input.certified.moleculeGraph (descriptorMap input)
        unit frames.actualArmGraphs frames.W frames.D frames.actualCoordinates descriptor :=
  referenceState_some_iff_retainedJudgment_of_real input singleBonded
    (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)
    (finalOccurrence_provenance_real input center)
    (finalCenterUnit input center)
    (finalOccurrence_molecularFrameUnit input center) descriptor

end
end TetraStereo.OneCenter.LocalizedRuleMajorReference

assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.actualArmGraphs
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.actualArmGraphs_eq_stage
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.retainedKeys
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.retainedKeys_eq_stage
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.actualLigandAtoms
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.actualCoordinates
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.actualCoordinates_eq_source
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.actualCursor_coordinates
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.retainedActual_fullOrdering
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.retainedActual_priorComparison
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.retainedActual_readingShape
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.retainedExecutionData
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.exec_some_iff_retainedJudgment
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.exec_none_iff_no_retainedJudgment
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.referenceState_some_iff_retainedJudgment
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.referenceState_none_iff_no_retainedJudgment
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.referenceState_retainedOutcome
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.referenceState_lowercase_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ContextFrameCompilation.referenceState_eq_descending_geometric_reading
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState_some_iff_retainedJudgment_of_real
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState_none_iff_no_retainedJudgment_of_real
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState_retainedOutcome_of_real
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState_lowercase_iff_of_real
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState_eq_descending_geometric_reading_of_real
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.tetrahedralCenter_isDetected
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.finalCenterUnit
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.finalOccurrence_provenance_real
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.finalOccurrence_molecularFrameUnit
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.analyze_uses_own_final_root
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.referenceState_at_final_occurrence_some_iff_retainedJudgment
