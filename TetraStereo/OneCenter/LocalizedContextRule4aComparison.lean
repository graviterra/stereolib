import TetraStereo.OneCenter.LocalizedContextRule4aCanonicalBridge
import TetraStereo.OneCenter.LocalizedContextConstitutionalComparison
import TetraStereo.OneCenter.DeclarativeCIPContextualRule5Order
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Cross-arm Rule-4a comparison at arbitrary retained-root contexts. The recursive actual
sort trace supplies the representations; no comparison agreement or strictness is assumed. -/

namespace TetraStereo.OneCenter.Rule4aTableBridge
open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree DeclarativeCIP
noncomputable section

theorem contextTrees_rule4a_compare
    {input : CertifiedLocalizedCIPInput} {carrierFuel fuelLeft fuelRight : Nat}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (leftTrace : LocalizedRuleMajorSortTrace input .rule4a read fuelLeft left leftKey)
    (rightTrace : LocalizedRuleMajorSortTrace input .rule4a read fuelRight right rightKey)
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {leftUnit rightUnit : DetectedOccurrence input.moleculeGraph}
    (leftReadback : ContextTreeRankReadback left descriptorMap leftUnit)
    (rightReadback : ContextTreeRankReadback right descriptorMap rightUnit)
    {W D : Nat} (leftWidth : (ruleMajorTreeGraph left).width ≤ W)
    (rightWidth : (ruleMajorTreeGraph right).width ≤ W)
    (leftHeight : (ruleMajorTreeGraph left).height ≤ D)
    (rightHeight : (ruleMajorTreeGraph right).height ≤ D) :
    input.compareLocalizedRerootCumulativeRule45Keys leftKey rightKey =
      compare
        (observedPairKey (ruleMajorTreeGraph left)
          (contextualNodeObservation input.moleculeGraph (ruleMajorTreeGraph left)
            left.source.occurrence.1.root)
          (rankEvidence input.moleculeGraph descriptorMap leftUnit (ruleMajorTreeGraph left))
          W D (ruleMajorTreeGraph left).root)
        (observedPairKey (ruleMajorTreeGraph right)
          (contextualNodeObservation input.moleculeGraph (ruleMajorTreeGraph right)
            right.source.occurrence.1.root)
          (rankEvidence input.moleculeGraph descriptorMap rightUnit (ruleMajorTreeGraph right))
          W D (ruleMajorTreeGraph right).root) := by
  have realizesL := LocalizedRuleMajorSortTrace.realizes_of_trace leftTrace
  have realizesR := LocalizedRuleMajorSortTrace.realizes_of_trace rightTrace
  have repL := (contextTree_node_bridge4a left _
    (contextualTree_nodeObservation singleBonded acyclic left realizesL)
    leftReadback leftWidth leftHeight (ruleMajorTreeGraph left).root left leftKey leftTrace
    (by change left.decoratedSubtreeAt? [] = some left; rw [decoratedSubtreeAt?])).2
  have repR := (contextTree_node_bridge4a right _
    (contextualTree_nodeObservation singleBonded acyclic right realizesR)
    rightReadback rightWidth rightHeight (ruleMajorTreeGraph right).root right rightKey rightTrace
    (by change right.decoratedSubtreeAt? [] = some right; rw [decoratedSubtreeAt?])).2
  have constitution := contextualTrees_compare_eq_compare_key singleBonded acyclic
    left right leftTrace rightTrace leftWidth rightWidth leftHeight rightHeight
  change (OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional).then
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        leftKey.descriptor rightKey.descriptor) =
    (compare
      (contextualRuleKey input.moleculeGraph (ruleMajorTreeGraph left)
        left.source.occurrence.1.root W D (ruleMajorTreeGraph left).root)
      (contextualRuleKey input.moleculeGraph (ruleMajorTreeGraph right)
        right.source.occurrence.1.root W D (ruleMajorTreeGraph right).root)).then _
  rw [constitution]
  cases h : compare
      (contextualRuleKey input.moleculeGraph (ruleMajorTreeGraph left)
        left.source.occurrence.1.root W D (ruleMajorTreeGraph left).root)
      (contextualRuleKey input.moleculeGraph (ruleMajorTreeGraph right)
        right.source.occurrence.1.root W D (ruleMajorTreeGraph right).root) with
  | lt => rfl
  | gt => rfl
  | eq =>
      simp only [Ordering.eq_then]
      have tied := constitution.trans h
      simp only [OfficialRuleMajorKey.compare, compareLex, Ordering.byKey,
        Ordering.then_eq_eq] at tied
      exact compare_descriptor_eq_compare_key
        (LocalizedRuleMajorSortTrace.fullMatch_of_trace leftTrace).tableMatch
        (LocalizedRuleMajorSortTrace.fullMatch_of_trace rightTrace).tableMatch
        realizesL realizesR tied.1
        (ordinaryKeyWithObservations_stereo_wellShaped (ruleMajorTreeGraph left) _ _ W D
          .rule4aStereogenicUnitKind (ruleMajorTreeGraph left).root)
        (ordinaryKeyWithObservations_stereo_wellShaped (ruleMajorTreeGraph right) _ _ W D
          .rule4aStereogenicUnitKind (ruleMajorTreeGraph right).root) repL repR

/-- At an arbitrary actual target, the generated reader discharges both arms' readback
premises. The independent prefix uses the target unit's retained outer-root distances. -/
theorem generatedContextTrees_rule4a_compare
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (left right : LocalizedCumulativeDecoratedTree input.certified
      (input.certified.certified.input.molecule.atomCount + 1))
    {fuelLeft fuelRight : Nat}
    {leftKey rightKey : input.certified.LocalizedRerootCumulativeRule45Key}
    (leftTrace : LocalizedRuleMajorSortTrace input.certified .rule4a
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence))
      fuelLeft left leftKey)
    (rightTrace : LocalizedRuleMajorSortTrace input.certified .rule4a
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence))
      fuelRight right rightKey)
    (leftChild : left.source ∈ input.certified.executableLocalizedRerootChildren target)
    (rightChild : right.source ∈ input.certified.executableLocalizedRerootChildren target)
    {W D : Nat} (leftWidth : (ruleMajorTreeGraph left).width ≤ W)
    (rightWidth : (ruleMajorTreeGraph right).width ≤ W)
    (leftHeight : (ruleMajorTreeGraph left).height ≤ D)
    (rightHeight : (ruleMajorTreeGraph right).height ≤ D) :
    input.certified.compareLocalizedRerootCumulativeRule45Keys leftKey rightKey =
      compare
        (contextualMolecularRankPairAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit (ruleMajorTreeGraph left) W D)
        (contextualMolecularRankPairAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit (ruleMajorTreeGraph right) W D) := by
  have readL := ruleMajorGeneratedContextTreeRankReadback input singleBonded acyclic
    target unit targetUnit left (LocalizedRuleMajorSortTrace.realizes_of_trace leftTrace) leftChild
  have readR := ruleMajorGeneratedContextTreeRankReadback input singleBonded acyclic
    target unit targetUnit right (LocalizedRuleMajorSortTrace.realizes_of_trace rightTrace) rightChild
  have rootL := contextTree_outerRoot_eq_unitRoot singleBonded acyclic
    target unit targetUnit left leftChild
  have rootR := contextTree_outerRoot_eq_unitRoot singleBonded acyclic
    target unit targetUnit right rightChild
  simpa only [rootL, rootR, contextualMolecularRankPairAt] using
    contextTrees_rule4a_compare singleBonded acyclic left right leftTrace rightTrace readL readR
      leftWidth rightWidth leftHeight rightHeight

end
end TetraStereo.OneCenter.Rule4aTableBridge

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextTrees_rule4a_compare
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.generatedContextTrees_rule4a_compare
