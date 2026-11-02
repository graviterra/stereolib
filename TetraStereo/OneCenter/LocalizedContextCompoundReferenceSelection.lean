import TetraStereo.OneCenter.LocalizedContextReferenceSelectionBridge
import TetraStereo.OneCenter.LocalizedRuleMajorCompoundReadback
import TetraStereo.OneCenter.LocalizedRuleMajorReferenceSelection
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual compound execution and independent reference selection at arbitrary auxiliary targets.
Both construction success and selection are derived from the input and generated state. -/

namespace TetraStereo.OneCenter.ContextReferenceBridge
open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree DeclarativeCIP Rule4aTableBridge
noncomputable section

/-- The compound key used by the executable descriptor evaluator selects exactly the independent
contextual reference population. The target's path, the comparison depth, and the number of
eligible centres are unrestricted on the finite acyclic single-bond domain. -/
theorem exists_generatedContextCompound_references_eq_selection
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (cursor : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (rootChild : cursor ∈ input.certified.executableLocalizedRerootChildren target) :
    ∃ (tree : LocalizedCumulativeDecoratedTree input.certified
        (input.certified.certified.input.molecule.atomCount + 1))
      (compound : input.certified.LocalizedRerootCompoundRule45Key),
      tree.source = cursor ∧
      input.certified.buildActualRuleMajorCompoundRule45KeyExec? target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)
        (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1)) cursor = some compound ∧
      compound.prior.references =
        toReferenceList (contextualReferenceSelection input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit (ruleMajorTreeGraph tree)) := by
  let view := input.certified.localizedDependencyView
    (LocalizedRuleMajorReference.referenceState input) target.occurrence
  let read := input.certified.localizedDependencyLabel target.occurrence view
  have valid := input.certified.localizedRerootChild_valid target cursor _
    (input.certified.executableLocalizedRerootChildren_declarative target) rootChild
  obtain ⟨tree, key, source, built, trace⟩ :=
    exists_ruleMajorTrace_at_twice input.certified .rule4a read cursor valid
  obtain ⟨compound, compoundBuilt⟩ :=
    input.certified.exists_buildActualRuleMajorCompoundRule45Key_at_twice
      target.occurrence view cursor valid
  have uniformBuilt := compoundBuilt
  rw [input.certified.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor] at uniformBuilt
  have references := input.certified.buildRuleMajorCompoundRule45KeyWith?_references_eq
    (fun stage position => input.certified.buildRuleMajorCumulativeWithRead? stage read
      (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1)) position)
    cursor uniformBuilt key built
  refine ⟨tree, compound, source, ?_, ?_⟩
  · rw [input.certified.buildActualRuleMajorCompoundRule45KeyExec?_eq]
    exact compoundBuilt
  · exact references.trans (generatedContextTree_references_eq_selection input singleBonded acyclic
      target unit targetUnit tree trace (by simpa only [source] using rootChild))

end
end TetraStereo.OneCenter.ContextReferenceBridge
assert_kernel_only TetraStereo.OneCenter.ContextReferenceBridge.exists_generatedContextCompound_references_eq_selection
