import TetraStereo.OneCenter.LocalizedContextAbsoluteRule5Readback
import TetraStereo.OneCenter.LocalizedContextCrossBranchReadingComparison
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! At a complete prior tie, the actual appended Rule-5 bits compare exactly as independent
absolute streams. Both selected senses and either common sense are allowed. -/

namespace TetraStereo.OneCenter.DeclarativeCIP
noncomputable section
universe u

theorem contextualRule5Reading_iso {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) {left right : RootedDigraph Atom}
    (iso : RootedDigraph.Iso left right) (W D : Nat)
    (reference : Option DescriptorSense) (common : DescriptorSense) :
    contextualCompleteRule5ReadingAt molecule descriptorMap unit right W D reference common =
      contextualCompleteRule5ReadingAt molecule descriptorMap unit left W D reference common := by
  cases reference with
  | none =>
      simp only [contextualCompleteRule5ReadingAt]
      rw [contextualCompleteReadingAt_iso molecule descriptorMap unit iso W D none]
  | some own =>
      exact congrArg (fun key : CompleteReadingKey =>
        mapObservationKey (absoluteRule5Label own common) (ofLex key).1)
        (contextualCompleteReadingAt_iso molecule descriptorMap unit iso W D (some own))

end
end TetraStereo.OneCenter.DeclarativeCIP

namespace TetraStereo.OneCenter.Rule5ObservationBridge
open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree DeclarativeCIP
open Rule4aTableBridge Rule4cObservationBridge OfficialSparseCanonicalVectorComparison
noncomputable section

variable (input : LocalizedRuleMajorReference.Input)
  (singleBonded : input.certified.moleculeGraph.SimpleBonded)
  (acyclic : input.certified.moleculeGraph.Acyclic)
  (target : input.certified.LocalizedRerootCursor
    (input.certified.certified.input.molecule.atomCount + 1))
  (unit : DetectedOccurrence input.certified.moleculeGraph)
  (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
  (cursorL cursorR : input.certified.LocalizedRerootCursor
    (input.certified.certified.input.molecule.atomCount + 1))
  (childL : cursorL ∈ input.certified.executableLocalizedRerootChildren target)
  (childR : cursorR ∈ input.certified.executableLocalizedRerootChildren target)
  (leftStages : input.certified.RuleMajorContextStages
    (input.certified.certified.input.molecule.atomCount + 1)
    (input.certified.localizedDependencyLabel target.occurrence
      (input.certified.localizedDependencyView
        (LocalizedRuleMajorReference.referenceState input) target.occurrence)) cursorL)
  (rightStages : input.certified.RuleMajorContextStages
    (input.certified.certified.input.molecule.atomCount + 1)
    (input.certified.localizedDependencyLabel target.occurrence
      (input.certified.localizedDependencyView
        (LocalizedRuleMajorReference.referenceState input) target.occurrence)) cursorR)
  (isoL : RuleMajorContextStageGraphIsoBundle leftStages)
  (isoR : RuleMajorContextStageGraphIsoBundle rightStages)

include singleBonded acyclic targetUnit childL childR isoL isoR

theorem contextCrossBranch_selected_rule5_compare
    (leftReference rightReference common : RS) {W D : Nat}
    (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
    (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D)
    (aTie : input.certified.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq)
    (cTie : OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      (leftStages.c leftReference).key.descriptor (rightStages.c rightReference).key.descriptor = .eq) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (input.certified.rule5LiftKey (common == leftReference) (leftStages.c leftReference).key).descriptor
        (input.certified.rule5LiftKey (common == rightReference) (rightStages.c rightReference).key).descriptor =
      compare
        (contextualCompleteRule5ReadingAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph leftStages.a.tree) W D
          (some (senseOf leftReference)) (senseOf common))
        (contextualCompleteRule5ReadingAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph rightStages.a.tree) W D
          (some (senseOf rightReference)) (senseOf common)) := by
  have cEq := (compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff _ _).mp cTie
  rw [compare_lifts_eq_bits _ _ _ _ cEq]
  have ties := contextCrossBranch_ties leftStages rightStages leftReference rightReference aTie
  have repL := generatedContext_selectedRule5_represents input singleBonded acyclic
    target unit targetUnit cursorL childL leftStages leftReference common
    ((leftStages.b_width_le leftReference).trans leftWidth)
    ((leftStages.b_depth_le leftReference).trans leftDepth)
  have repR := generatedContext_selectedRule5_represents input singleBonded acyclic
    target unit targetUnit cursorR childR rightStages rightReference common
    ((rightStages.b_width_le rightReference).trans rightWidth)
    ((rightStages.b_depth_le rightReference).trans rightDepth)
  rw [contextualRule5Reading_iso input.certified.moleculeGraph
    (LocalizedRuleMajorReference.descriptorMap input) unit (isoL.b leftReference)] at repL
  rw [contextualRule5Reading_iso input.certified.moleculeGraph
    (LocalizedRuleMajorReference.descriptorMap input) unit (isoR.b rightReference)] at repR
  have shapedL := mapObservationKey_wellShaped
    (absoluteRule5Label (senseOf leftReference) (senseOf common))
    (ordinaryKeyWithObservations_stereo_wellShaped (ruleMajorTreeGraph leftStages.a.tree)
      (contextualNodeObservation input.certified.moleculeGraph (ruleMajorTreeGraph leftStages.a.tree)
        unit.1.root)
      (readingEvidence input.certified.moleculeGraph (LocalizedRuleMajorReference.descriptorMap input)
        unit (ruleMajorTreeGraph leftStages.a.tree) (senseOf leftReference)) W D
      .rule4bLikeUnlikeDescriptorPairs (ruleMajorTreeGraph leftStages.a.tree).root)
  have shapedR := mapObservationKey_wellShaped
    (absoluteRule5Label (senseOf rightReference) (senseOf common))
    (ordinaryKeyWithObservations_stereo_wellShaped (ruleMajorTreeGraph rightStages.a.tree)
      (contextualNodeObservation input.certified.moleculeGraph (ruleMajorTreeGraph rightStages.a.tree)
        unit.1.root)
      (readingEvidence input.certified.moleculeGraph (LocalizedRuleMajorReference.descriptorMap input)
        unit (ruleMajorTreeGraph rightStages.a.tree) (senseOf rightReference)) W D
      .rule4bLikeUnlikeDescriptorPairs (ruleMajorTreeGraph rightStages.a.tree).root)
  exact compare_of_pathFirstDifference shapedL shapedR repL repR
    (fun outcome => bitTable_pathFirstDifference_iff
      (LocalizedRuleMajorSortTrace.fullMatch_of_trace (leftStages.c leftReference).trace).tableMatch
      (LocalizedRuleMajorSortTrace.fullMatch_of_trace (rightStages.c rightReference).trace).tableMatch
      (LocalizedRuleMajorSortTrace.realizes_of_trace (leftStages.c leftReference).trace)
      (LocalizedRuleMajorSortTrace.realizes_of_trace (rightStages.c rightReference).trace)
      common (contextCompareNatLayers_eq_of_tie ties.cRule1a) outcome)

end
end TetraStereo.OneCenter.Rule5ObservationBridge

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualRule5Reading_iso
assert_kernel_only TetraStereo.OneCenter.Rule5ObservationBridge.contextCrossBranch_selected_rule5_compare
