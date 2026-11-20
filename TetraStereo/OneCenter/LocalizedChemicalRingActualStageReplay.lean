import TetraStereo.OneCenter.LocalizedChemicalRingStageReplay
import TetraStereo.OneCenter.LocalizedChemicalRingActualReferenceMatch
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! Actual retained comparison ties force matching rebuilt observations at every cumulative
stage. The actual occurrence frame supplies validity, so successful rebuilds are derived at
the runtime's own budget. No reader alignment, reference selection, stage-key equality or
successful rebuild is an input to the actual endpoint. -/

namespace TetraStereo.OneCenter.LocalizedChemicalRingActualStageReplay

open CertifiedLocalizedCIPInput DeclarativeCIP LocalizedCumulativeDecoratedTree
open LocalizedChemicalRingDecodedRelation LocalizedChemicalRingStageReplay
open LocalizedChemicalRingActualComparisonLabelMatch LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedPromotedRanking LocalizedMarkedRetainedCanonicalFrame
open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedPromotedKey LocalizedMarkedRetainedCanonicalMarker

noncomputable section
variable {input : CertifiedLocalizedCIPInput}

theorem frame_tie_stage_rebuilds
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : RetainedExecutionFrame descriptorMap target)
    (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (single : input.moleculeGraph.SimpleBonded) (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.1 = unit.1) (left right : Fin 4)
    (tie : frame.retainedKeys unit left = frame.retainedKeys unit right)
    (stage : LocalizedCumulativeRule45Stage) :
    ∃ keyL keyR,
      input.buildRuleMajorCumulativeWithRead? stage (input.molecularReader descriptorMap target)
        (2 * (retainedCarrierFuel input + 1)) (frame.frame.cursorAt left) = some keyL ∧
      input.buildRuleMajorCumulativeWithRead? stage (input.molecularReader descriptorMap target)
        (2 * (retainedCarrierFuel input + 1)) (frame.frame.cursorAt right) = some keyR ∧
      input.localizedRerootCumulativeRule45Observable keyL =
        input.localizedRerootCumulativeRule45Observable keyR := by
  have valid (slot : Fin 4) := input.localizedRerootChild_valid _ _ _
    (input.executableLocalizedRerootChildren_declarative ⟨target, none⟩) (frame.childAt slot)
  obtain ⟨keyL, builtL⟩ := input.exists_buildRuleMajorCumulativeWithRead_at_twice stage
    (input.molecularReader descriptorMap target) _ (valid left)
  obtain ⟨keyR, builtR⟩ := input.exists_buildRuleMajorCumulativeWithRead_at_twice stage
    (input.molecularReader descriptorMap target) _ (valid right)
  obtain ⟨treeL, treeR, sourceL, sourceR, realL, realR, same, _⟩ :=
    frame_tie_same_label_trees descriptorMap target frame tetrahedral single unit targetUnit left right tie
  have related := shapePositionCursorRelation_sources (shape_eq_of_observation_eq treeL treeR same)
    (sourceL.trans (frame.stages left).a.sourceEq) (sourceR.trans (frame.stages right).a.sourceEq)
  exact ⟨keyL, keyR, builtL, builtR, replay_of_observations same _ _ realL realR
    stage _ _ _ related keyL keyR builtL builtR⟩

/-- Derived success and table matching for all actual cumulative stages, from an actual refined
comparison tie on a finite simple-bonded input. Rings and arbitrary raw auxiliary states remain. -/
theorem actual_refined_tie_stage_rebuilds
    (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
    (state : OccurrenceAuxState) (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.moleculeGraph) (targetUnit : input.molecularFrameUnit target.1 = unit.1)
    (reference : input.Atom) (W D : Nat) (left right : Fin 4)
    (tie : refinedKey input single state target real unit targetUnit reference W D left =
      refinedKey input single state target real unit targetUnit reference W D right)
    (stage : LocalizedCumulativeRule45Stage) :
    ∃ keyL keyR,
      input.buildRuleMajorCumulativeWithRead? stage (rawStateReader input state target)
        (2 * (retainedCarrierFuel input + 1))
        ((frames input single state target real unit targetUnit).frame.cursorAt left) = some keyL ∧
      input.buildRuleMajorCumulativeWithRead? stage (rawStateReader input state target)
        (2 * (retainedCarrierFuel input + 1))
        ((frames input single state target real unit targetUnit).frame.cursorAt right) = some keyR ∧
      input.localizedRerootCumulativeRule45Observable keyL =
        input.localizedRerootCumulativeRule45Observable keyR := by
  simp only [rawStateReader_eq_molecularReader]
  exact frame_tie_stage_rebuilds (rawStateDescriptorMap input state) target
    (frames input single state target real unit targetUnit) (rawStateDescriptorMap_tetrahedral input state)
    single unit targetUnit left right (congrArg (fun value : RefinedKey => (ofLex value).1) tie) stage

end
end TetraStereo.OneCenter.LocalizedChemicalRingActualStageReplay

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualStageReplay.frame_tie_stage_rebuilds
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualStageReplay.actual_refined_tie_stage_rebuilds
