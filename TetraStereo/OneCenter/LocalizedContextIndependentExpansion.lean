import TetraStereo.OneCenter.LocalizedContextBranchStages
import TetraStereo.OneCenter.LocalizedContextIncomingEdge
import TetraStereo.OneCenter.LocalizedContextSourceFaithfulness
import TetraStereo.OneCenter.DeclarativeCIPContextualRule5Order
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual context arms are faithful exact expansions of the physical incoming edge. Their
independent complete key therefore agrees with that of any faithful expansion of the same edge. -/

namespace TetraStereo.OneCenter.Rule4aTableBridge
open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree DeclarativeCIP
noncomputable section

/-- An arm at an actual executable context child is a faithful exact expansion of its incoming
physical edge. The stage and label reader are arbitrary; all cursor predecessor, root, validity,
and adjacency facts are recovered from executable child membership. -/
theorem ruleMajorContextArm_faithfulExactExpansion_of_actualChild
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (target cursor : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (cursorChild : cursor ∈ input.executableLocalizedRerootChildren target)
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.RuleMajorContextArm (input.certified.input.molecule.atomCount + 1)
      stage read cursor)
    {targetAtom ligandAtom : input.Atom}
    (targetCurrent : target.occurrence.1.node.current? = some targetAtom)
    (cursorCurrent : cursor.occurrence.1.node.current? = some ligandAtom) :
    RootedDigraph.FaithfulExactExpansion input.moleculeGraph targetAtom ligandAtom
      (ruleMajorTreeGraph arm.tree) := by
  obtain ⟨targetAtom', ligandAtom', targetObserved, ligandObserved, previousEq, sameRoot,
    valid, incomingEdge⟩ := input.executableLocalizedRerootChild_incomingData
      singleBonded acyclic target cursor cursorChild
  have targetAtomEq : targetAtom' = targetAtom :=
    Option.some.inj (targetObserved.symm.trans targetCurrent)
  have ligandAtomEq : ligandAtom' = ligandAtom :=
    Option.some.inj (ligandObserved.symm.trans cursorCurrent)
  subst targetAtom'
  subst ligandAtom'
  have previousEqArm : arm.tree.source.previous? = some target.occurrence := by
    rw [arm.sourceEq]
    exact previousEq
  have validArm : input.LocalizedRerootCursorValid arm.tree.source := by
    rw [arm.sourceEq]
    exact valid
  have sameRootArm : arm.tree.source.occurrence.1.root = target.occurrence.1.root := by
    rw [arm.sourceEq]
    exact sameRoot
  have currentArm : arm.tree.source.occurrence.1.node.current? = some ligandAtom := by
    rw [arm.sourceEq]
    exact cursorCurrent
  exact ruleMajorTreeGraph_faithfulExactExpansion singleBonded acyclic (by omega)
    (LocalizedRuleMajorSortTrace.realizes_of_trace arm.trace) target.occurrence previousEqArm
    validArm sameRootArm currentArm targetCurrent incomingEdge

/-- The complete contextual Rule-5 key of an actual child arm is unchanged when its rooted graph
is replaced by any faithful exact expansion of the same incoming physical edge. The contextual
unit and descriptor map are held fixed, while no outward-only source-tree condition is needed. -/
theorem generatedContextArm_contextualCompleteLigandRule5KeyAt_eq_of_faithful
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target cursor : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (cursorChild : cursor ∈ input.certified.executableLocalizedRerootChildren target)
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    (arm : input.certified.RuleMajorContextArm
      (input.certified.certified.input.molecule.atomCount + 1) stage read cursor)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    {targetAtom ligandAtom : input.certified.Atom}
    (targetCurrent : target.occurrence.1.node.current? = some targetAtom)
    (cursorCurrent : cursor.occurrence.1.node.current? = some ligandAtom)
    (other : RootedDigraph input.certified.Atom)
    (otherFaithful : RootedDigraph.FaithfulExactExpansion input.certified.moleculeGraph
      targetAtom ligandAtom other)
    (W D : Nat) :
    contextualCompleteLigandRule5KeyAt input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit
        (ruleMajorTreeGraph arm.tree) W D =
      contextualCompleteLigandRule5KeyAt input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit other W D := by
  have actualFaithful := ruleMajorContextArm_faithfulExactExpansion_of_actualChild
    input.certified singleBonded acyclic target cursor cursorChild arm targetCurrent cursorCurrent
  obtain ⟨iso⟩ := RootedDigraph.faithfulExactExpansion_unique_up_to_iso
    input.certified.moleculeGraph targetAtom ligandAtom (ruleMajorTreeGraph arm.tree) other
    actualFaithful otherFaithful
  exact (contextualCompleteLigandRule5KeyAt_iso input.certified.moleculeGraph
    (LocalizedRuleMajorReference.descriptorMap input) unit iso W D).symm

end
end TetraStereo.OneCenter.Rule4aTableBridge

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorContextArm_faithfulExactExpansion_of_actualChild
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.generatedContextArm_contextualCompleteLigandRule5KeyAt_eq_of_faithful
