import TetraStereo.OneCenter.DeclarativeCIPContextualConstitutional
import TetraStereo.OneCenter.LocalizedRuleMajorCanonicalBridge
import TetraStereo.OneCenter.LocalizedOuterDigraphPhysicalObservations
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual constitutional observations in every realized rerooting context. The Rule-1b
observation uses the retained outer-root physical distance, following the existing explicit
auxiliary profile. No fresh-root equality, desired comparator outcome, rigidity assumption,
or successful molecular descriptor is assumed. -/

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree DeclarativeCIP
noncomputable section
open scoped Classical

/-- At every node of an arbitrary actual realized tree, the independent contextual observation
equals the actual constitutional observation. This includes parent-facing auxiliary arms. -/
theorem contextualTree_nodeObservation
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {read : input.LocalizedRerootCursor fuel → Option LocalizedAuxiliaryLabel}
    (tree : LocalizedCumulativeDecoratedTree input fuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (rule : ConstitutionalRule) (node : (ruleMajorTreeGraph tree).Node)
    (actual : LocalizedCumulativeDecoratedTree input fuel)
    (lookup : tree.decoratedSubtreeAt? node.1 = some actual) :
    contextualNodeObservation input.moleculeGraph (ruleMajorTreeGraph tree)
        tree.source.occurrence.1.root rule node =
      priorityValue rule (armObservation rule actual) := by
  have erasedLookup : (toOfficialSourceTree tree).subtreeAt? node.1 =
      some (toOfficialSourceTree actual) := by
    rw [toOfficialSourceTree_subtreeAt? tree node.1, lookup]
    rfl
  have labelEq : (ruleMajorTreeGraph tree).label node =
      actual.source.occurrence.1.node.toDeclarativeLabel := by
    change (toOfficialSourceTree tree).declarativeLabel node = _
    rw [(toOfficialSourceTree tree).declarativeLabel_eq_of_subtreeAt?
      (toOfficialSourceTree actual) node erasedLookup]
    rw [toOfficialSourceTree_source]
  have shape : actual = localizedRootTree input actual.source (read actual.source)
      actual.children :=
    realizes_of_decoratedSubtreeAt? tree realizes node.1 actual lookup
  have observedShape : armObservation rule actual =
      armSourceObservation input rule actual.source := by
    rw [shape]
    cases rule <;> rfl
  rw [observedShape]
  have real := input.carrierOccurrence_provenance_real singleBonded acyclic
    actual.source.occurrence
  obtain ⟨atom, _path, current, _head, _provenance, _simple, _support, _penultimate⟩ :=
    input.carrierOccurrence_realPath singleBonded acyclic actual.source.occurrence
  have retainedRoot : actual.source.occurrence.1.root = tree.source.occurrence.1.root :=
    TetraStereo.OneCenter.subtreeAt?_source_occurrence_root_eq realizes
      (by rwa [← decoratedSubtreeAt?_eq_subtreeAt?])
  cases rule with
  | rule1aAtomicNumber =>
      simpa [contextualNodeObservation, contextualRuleValue, nodeObservation, ruleValue, labelEq,
        armSourceObservation] using
        congrArg (priorityValue ConstitutionalRule.rule1aAtomicNumber)
          (MoleculeGraph.officialNodeAtomLabel_first_eq_nodeAtomicNumber
            input.moleculeGraph actual.source.occurrence.1.node).symm
  | rule1bDuplicateNodeProximity =>
      have distance := carrierOccurrence_rule1bRootDistance_eq_physical_dist
        singleBonded acyclic actual.source.occurrence current
      rw [retainedRoot] at distance
      simp [contextualNodeObservation, contextualRuleValue, labelEq, OfficialCIPNode.toDeclarativeLabel, real,
        OfficialCIPNodeProvenance.toDeclarative, current, armSourceObservation,
        priorityValue, distance]
  | rule2AtomicMass =>
      simpa [contextualNodeObservation, contextualRuleValue, nodeObservation, ruleValue, labelEq,
        armSourceObservation] using
        congrArg (priorityValue ConstitutionalRule.rule2AtomicMass)
          (MoleculeGraph.officialNodeAtomLabel_second_eq_nodeAtomicMass
            input.moleculeGraph actual.source.occurrence.1.node).symm

/-- On an original-root arm, contextual observations specialize to the already accepted
constitutional observations. This is derived from the actual tree, not a supplied distance law. -/
theorem ruleMajorRootArm_contextualObservation_eq
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (arm : input.RuleMajorRootArm center index stage read)
    (rule : ConstitutionalRule) (node : (ruleMajorArmGraph arm).Node) :
    contextualNodeObservation input.moleculeGraph (ruleMajorArmGraph arm)
        arm.tree.source.occurrence.1.root rule node =
      nodeObservation input.moleculeGraph (ruleMajorArmGraph arm) rule node := by
  obtain ⟨actual, lookup, _⟩ := ruleMajorRootArm_decoratedSubtree_of_node arm node
  exact (contextualTree_nodeObservation singleBonded acyclic arm.tree arm.realizes
    rule node actual lookup).trans
      (ruleMajorRootArm_nodeObservation arm rule node actual lookup).symm

/-- The contextual constitutional key preserves every established original-root key, at every
node and every comparison window. Auxiliary contexts are covered by the contextual construction
without asserting this fresh-root specialization there. -/
theorem ruleMajorRootArm_contextualRuleKey_eq
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (arm : input.RuleMajorRootArm center index stage read) (W D : Nat)
    (node : (ruleMajorArmGraph arm).Node) :
    contextualRuleKey input.moleculeGraph (ruleMajorArmGraph arm)
        arm.tree.source.occurrence.1.root W D node =
      ruleKey input.moleculeGraph (ruleMajorArmGraph arm) W D node := by
  unfold contextualRuleKey
  exact (ruleKeyWithObservations_congr (ruleMajorArmGraph arm) W D _ _
    (ruleMajorRootArm_contextualObservation_eq singleBonded acyclic arm) node).trans
      (ruleKeyWithObservations_eq_ruleKey (ruleMajorArmGraph arm) input.moleculeGraph W D node)

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextualTree_nodeObservation
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_contextualObservation_eq
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_contextualRuleKey_eq
