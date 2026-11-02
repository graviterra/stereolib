import TetraStereo.OneCenter.LocalizedContextCompoundPriorComparison
import TetraStereo.OneCenter.LocalizedContextRule5ListComparison
import TetraStereo.OneCenter.DeclarativeCIPContextualRule5Order
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! For actual generated compounds at arbitrary auxiliary targets, the complete ordering through
Rule 5 agrees with the independent contextual complete-ligand key. The Rule-5 comparison is used
only after deriving a tie in the full prior key. -/

namespace TetraStereo.OneCenter.Rule4aTableBridge
open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree DeclarativeCIP
noncomputable section

/-- Actual complete compound comparison agrees with the full independent contextual key. Both
actual compounds are successful executions at executable children of the same target, with
their fixed context stages and a shared width/depth bound. Reference selection, stage readbacks,
sorting, and the prior tie that gates Rule 5 are derived from these executions. -/
theorem generatedContextCompound_full_compare
    (input : LocalizedRuleMajorReference.Input)
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
    {W D : Nat} (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
    (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D)
    {left right : input.certified.LocalizedRerootCompoundRule45Key}
    (builtL : input.certified.buildActualRuleMajorCompoundRule45KeyExec? target.occurrence
      (input.certified.localizedDependencyView
        (LocalizedRuleMajorReference.referenceState input) target.occurrence)
      (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1)) cursorL = some left)
    (builtR : input.certified.buildActualRuleMajorCompoundRule45KeyExec? target.occurrence
      (input.certified.localizedDependencyView
        (LocalizedRuleMajorReference.referenceState input) target.occurrence)
      (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1)) cursorR = some right) :
    (input.certified.compareLocalizedRerootCompoundThroughRule5 left right).ordering =
      compare
        (contextualCompleteLigandRule5KeyAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph leftStages.a.tree) W D)
        (contextualCompleteLigandRule5KeyAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph rightStages.a.tree) W D) := by
  let graphL := ruleMajorTreeGraph leftStages.a.tree
  let graphR := ruleMajorTreeGraph rightStages.a.tree
  let descriptorMap := LocalizedRuleMajorReference.descriptorMap input
  have priorAgreement := generatedContextCompound_prior_compare input singleBonded acyclic
    target unit targetUnit cursorL cursorR childL childR leftStages rightStages
    leftWidth leftDepth rightWidth rightDepth builtL builtR
  have actualThen :
      (input.certified.compareLocalizedRerootCompoundThroughRule5 left right).ordering =
        (input.certified.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior).then
          (input.certified.compareLocalizedRerootCompoundRule5Readings .R
            left.rule5Readings right.rule5Readings) := by
    rw [input.certified.compareLocalizedRerootCompoundThroughRule5_ordering]
    rfl
  have independentThen :
      compare (contextualCompleteLigandRule5KeyAt input.certified.moleculeGraph
        descriptorMap unit graphL W D)
        (contextualCompleteLigandRule5KeyAt input.certified.moleculeGraph
          descriptorMap unit graphR W D) =
        (compare (contextualCompleteLigandPriorKeyAt input.certified.moleculeGraph
          descriptorMap unit graphL W D)
          (contextualCompleteLigandPriorKeyAt input.certified.moleculeGraph
            descriptorMap unit graphR W D)).then
          (compare (contextualCompleteRule5ReadingsAt input.certified.moleculeGraph
            descriptorMap unit graphL W D .senior)
            (contextualCompleteRule5ReadingsAt input.certified.moleculeGraph
              descriptorMap unit graphR W D .senior)) := rfl
  rw [actualThen, independentThen, ← priorAgreement]
  apply then_congr
  intro priorTie
  have actualPriorTie :
      input.certified.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior = .eq :=
    priorAgreement.symm ▸ priorTie
  exact generatedContextCompound_rule5Readings_compare input singleBonded acyclic
    target unit targetUnit cursorL cursorR childL childR leftStages rightStages
    leftWidth leftDepth rightWidth rightDepth builtL builtR actualPriorTie .R

end
end TetraStereo.OneCenter.Rule4aTableBridge

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.generatedContextCompound_full_compare
