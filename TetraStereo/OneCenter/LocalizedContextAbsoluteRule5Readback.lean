import TetraStereo.OneCenter.LocalizedContextBranchStages
import TetraStereo.OneCenter.LocalizedContextRule4bCanonicalBridge
import TetraStereo.OneCenter.DeclarativeCIPContextualRule5Order
import TetraStereo.OneCenter.LocalizedRuleMajorRule5Observation
import TetraStereo.OneCenter.LocalizedRuleMajorCompleteReadingPrefix
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Absolute Rule-5 stream readback at arbitrary auxiliary targets. The separate Rule-4b
and Rule-4c builds retain their earlier columns even when their sibling orders differ.
The independent absolute stream therefore represents the actual appended Rule-5 bits. -/

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages
open Rule4aTableBridge
noncomputable section

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
  {cursor : input.LocalizedRerootCursor carrierFuel}
  (stages : input.RuleMajorContextStages carrierFuel read cursor)

theorem b_encoded4b_eq_c (reference : RS) (path : List Nat) :
    encoded4b (stages.b reference).key path = encoded4b (stages.c reference).key path := by
  have preserved := input.buildRuleMajorCumulativeWithRead_rule4b_rule4c_prefix reference
    read _ cursor _ _ (stages.b reference).built (stages.c reference).built
  have rule1a : (stages.b reference).key.constitutional.rule1a =
      (stages.c reference).key.constitutional.rule1a :=
    congrArg RuleMajorPrefixObservable.rule1a preserved
  have columns := input.ruleMajorPrefix_two_scalars preserved
  unfold encoded4b
  rw [rule1a, columns.1, columns.2]

theorem c_rule1a_eq_a (reference : RS) :
    (stages.c reference).key.constitutional.rule1a = stages.a.key.constitutional.rule1a := by
  have ab := input.buildRuleMajorCumulativeWithRead_rule4a_rule4b_prefix reference
    read _ cursor _ _ stages.a.built (stages.b reference).built
  have bc := input.buildRuleMajorCumulativeWithRead_rule4b_rule4c_prefix reference
    read _ cursor _ _ (stages.b reference).built (stages.c reference).built
  have abRule : stages.a.key.constitutional.rule1a =
      (stages.b reference).key.constitutional.rule1a :=
    congrArg RuleMajorPrefixObservable.rule1a ab
  have bcRule : (stages.b reference).key.constitutional.rule1a =
      (stages.c reference).key.constitutional.rule1a :=
    congrArg RuleMajorPrefixObservable.rule1a bc
  exact (abRule.trans bcRule).symm

end
end TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages

namespace TetraStereo.OneCenter.Rule5ObservationBridge
open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree DeclarativeCIP Rule4aTableBridge
noncomputable section

/-- The generated reader's independent absolute stream represents the appended bit on the
actual Rule-4c key. No selected-reference, upper-case-only, or fresh-root assumption is used.
This theorem reads the independent stream on the actual Rule-4b graph; faithful expansion
transport can move it to the common ligand graph. -/
theorem generatedContext_selectedRule5_represents
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (cursor : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (rootChild : cursor ∈ input.certified.executableLocalizedRerootChildren target)
    (stages : input.certified.RuleMajorContextStages
      (input.certified.certified.input.molecule.atomCount + 1)
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) cursor)
    (reference common : RS) {W D : Nat}
    (width : (ruleMajorTreeGraph (stages.b reference).tree).width ≤ W)
    (depth : (ruleMajorTreeGraph (stages.b reference).tree).height ≤ D) :
    ∀ path, Certificate.CanonicalSphereKey.pathObservationOf W D
      (contextualCompleteRule5ReadingAt input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit
        (ruleMajorTreeGraph (stages.b reference).tree) W D
        (some (senseOf reference)) (senseOf common)) path =
      bitObservable (common == reference) (stages.c reference).key path := by
  have trace := (stages.b reference).trace
  have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace trace
  have child : (stages.b reference).tree.source ∈
      input.certified.executableLocalizedRerootChildren target := by
    simpa only [(stages.b reference).sourceEq] using rootChild
  have hyp := ruleMajorGeneratedContextTreeRankReadback input singleBonded acyclic
    target unit targetUnit (stages.b reference).tree realizes child
  have rootEq := contextTree_outerRoot_eq_unitRoot singleBonded acyclic
    target unit targetUnit (stages.b reference).tree child
  have observations : ∀ rule node actual,
      (stages.b reference).tree.decoratedSubtreeAt? node.1 = some actual →
      contextualNodeObservation input.certified.moleculeGraph
        (ruleMajorTreeGraph (stages.b reference).tree) unit.1.root rule node =
          priorityValue rule (armObservation rule actual) := by
    intro rule node actual lookup
    rw [← rootEq]
    exact contextualTree_nodeObservation singleBonded acyclic
      (stages.b reference).tree realizes rule node actual lookup
  have hsingle : ∀ atom other, input.certified.moleculeGraph.bond atom other ≤ 1 := by
    intro atom other
    rcases Nat.eq_zero_or_pos (input.certified.moleculeGraph.bond atom other) with zero | positive
    · rw [zero]; exact Nat.zero_le 1
    · exact le_of_eq (singleBonded atom other positive)
  have mask := rule4abOnly_readingEvidence_of_single input.certified.moleculeGraph
    (LocalizedRuleMajorReference.descriptorMap input) unit
    (ruleMajorTreeGraph (stages.b reference).tree) hsingle (senseOf reference)
  have represented := (contextTree_node_bridge4b (stages.b reference).tree _
    observations hyp mask width depth (ruleMajorTreeGraph (stages.b reference).tree).root
    (stages.b reference).tree (stages.b reference).key trace (by
      change (stages.b reference).tree.decoratedSubtreeAt? [] = some (stages.b reference).tree
      rw [decoratedSubtreeAt?])).2.2
  intro path
  change Certificate.CanonicalSphereKey.pathObservationOf W D
    (mapObservationKey (absoluteRule5Label (senseOf reference) (senseOf common))
      (observedRule4bComponent (ruleMajorTreeGraph (stages.b reference).tree)
        (contextualNodeObservation input.certified.moleculeGraph
          (ruleMajorTreeGraph (stages.b reference).tree) unit.1.root)
        (readingEvidence input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph (stages.b reference).tree) (senseOf reference))
        W D (ruleMajorTreeGraph (stages.b reference).tree).root)) path = _
  rw [pathObservationOf_mapObservationKey, represented path,
    stages.b_encoded4b_eq_c reference path]
  exact absolute_encoded4b
    (LocalizedRuleMajorSortTrace.fullMatch_of_trace (stages.c reference).trace).tableMatch
    common path

end
end TetraStereo.OneCenter.Rule5ObservationBridge

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages.b_encoded4b_eq_c
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages.c_rule1a_eq_a
assert_kernel_only TetraStereo.OneCenter.Rule5ObservationBridge.generatedContext_selectedRule5_represents
