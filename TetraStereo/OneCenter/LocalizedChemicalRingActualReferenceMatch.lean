import TetraStereo.OneCenter.LocalizedChemicalRingDecodedRelation
import TetraStereo.OneCenter.LocalizedChemicalRingActualComparisonLabelMatch
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Reference matching derived from actual complete comparison keys

The same actual full comparison tie that decodes the common-R reading trees also determines
their actual Rule-4b reference selection. Empty, singleton and two-reference selections are all
included. This is an occurrence-level result; it does not identify the decoded correspondence
with promoted marker addresses or assert a physical molecular symmetry.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingActualReferenceMatch

open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree
open LocalizedCyclicMatchedReadingDecode LocalizedChemicalRingActualFullLabelMatch
open LocalizedChemicalRingDecodedRelation LocalizedChemicalRingActualComparisonLabelMatch
open DeclarativeCIP LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedPromotedKey
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedStateReader
open LocalizedChemicalRingPromotedColorReadback LocalizedMarkedRetainedCanonicalMarker
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedPromotedRanking

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-- A complete tie derives equal reference populations' selections. No selection, matched-reader
or chosen-reference premise is supplied. -/
theorem full_tie_references
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuel : Nat) (x y : input.LocalizedRerootCursor carrierFuel)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (builtL : input.buildRuleMajorCompoundRule45KeyWith?
      (fun stage => input.buildRuleMajorCumulativeWithRead? stage
        (input.localizedDependencyLabel target view) fuel) x = some left)
    (builtR : input.buildRuleMajorCompoundRule45KeyWith?
      (fun stage => input.buildRuleMajorCumulativeWithRead? stage
        (input.localizedDependencyLabel target view) fuel) y = some right)
    (tie : (input.compareLocalizedRerootCompoundThroughRule5 left right).ordering = .eq) :
    localizedRule4bReferencesFromRankedLabels left.prior.rule4aKey.rankedLabels =
      localizedRule4bReferencesFromRankedLabels right.prior.rule4aKey.rankedLabels := by
  obtain ⟨treeL, treeR, sourceL, sourceR, realL, realR, same⟩ :=
    full_tie_same_observations _ _ _ _ _ _ _ _ builtL builtR tie
  exact references_eq_of_observations target view realL realR same fuel x y
    (shapePositionCursorRelation_sources (shape_eq_of_observation_eq treeL treeR same) sourceL sourceR)
    _ _ (compound_components _ _ builtL).1 (compound_components _ _ builtR).1

noncomputable section

theorem frame_tie_references
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : RetainedExecutionFrame descriptorMap target)
    (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (single : input.moleculeGraph.SimpleBonded) (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.1 = unit.1) (left right : Fin 4)
    (tie : frame.retainedKeys unit left = frame.retainedKeys unit right) :
    localizedRule4bReferencesFromRankedLabels (frame.compounds left).prior.rule4aKey.rankedLabels =
      localizedRule4bReferencesFromRankedLabels (frame.compounds right).prior.rule4aKey.rankedLabels := by
  have full := frame.fullOrdering tetrahedral single unit targetUnit left right
  rw [tie, (completeLigandRule5Key_compare_eq_iff _ _).mpr rfl] at full
  exact full_tie_references target (input.molecularView descriptorMap target) _ _ _ _ _
    (frame_uniform_built descriptorMap target frame left)
    (frame_uniform_built descriptorMap target frame right) full

/-- Actual generated-state comparisons are included by allowing an arbitrary raw auxiliary state.
All stage builds and selected lists are the ones produced by the actual retained frame. -/
theorem actual_refined_tie_references
    (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
    (state : OccurrenceAuxState) (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.moleculeGraph) (targetUnit : input.molecularFrameUnit target.1 = unit.1)
    (reference : input.Atom) (W D : Nat) (left right : Fin 4)
    (tie : refinedKey input single state target real unit targetUnit reference W D left =
      refinedKey input single state target real unit targetUnit reference W D right) :
    localizedRule4bReferencesFromRankedLabels
        ((frames input single state target real unit targetUnit).compounds left).prior.rule4aKey.rankedLabels =
      localizedRule4bReferencesFromRankedLabels
        ((frames input single state target real unit targetUnit).compounds right).prior.rule4aKey.rankedLabels := by
  exact frame_tie_references (rawStateDescriptorMap input state) target
    (frames input single state target real unit targetUnit) (rawStateDescriptorMap_tetrahedral input state)
    single unit targetUnit left right (congrArg (fun value : RefinedKey => (ofLex value).1) tie)

end
end TetraStereo.OneCenter.LocalizedChemicalRingActualReferenceMatch

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualReferenceMatch.full_tie_references
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualReferenceMatch.frame_tie_references
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualReferenceMatch.actual_refined_tie_references
