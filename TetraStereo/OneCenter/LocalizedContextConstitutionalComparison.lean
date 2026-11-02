import TetraStereo.OneCenter.LocalizedRuleMajorObservedCanonicalBridge
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Constitutional comparator correctness in arbitrary retained-root rerooting contexts.
The independent keys use molecular observations, including distance from the original outer
root. The actual recursive trace supplies ordering and table representation; these properties
are derived rather than assumed. This module does not claim the later stereo rules are closed. -/

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree DeclarativeCIP
open OfficialSparseCanonicalVectorComparison
noncomputable section
open scoped Classical

/-- Representation in any common comparison layout large enough for this actual tree. -/
theorem contextualTree_root_represents_layout
    {input : CertifiedLocalizedCIPInput} {carrierFuel fuel : Nat}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input stage read fuel tree key)
    {W D : Nat} (hW : (ruleMajorTreeGraph tree).width ≤ W)
    (hD : (ruleMajorTreeGraph tree).height ≤ D) :
    Represents W D
      (contextualRuleKey input.moleculeGraph (ruleMajorTreeGraph tree)
        tree.source.occurrence.1.root W D (ruleMajorTreeGraph tree).root)
      key.constitutional :=
  (observedTree_node_bridge tree _
    (contextualTree_nodeObservation singleBonded acyclic tree
      (LocalizedRuleMajorSortTrace.realizes_of_trace trace)) hW hD
    (ruleMajorTreeGraph tree).root tree key trace (by
      change tree.decoratedSubtreeAt? [] = some tree
      rw [decoratedSubtreeAt?])).2

/-- The executed constitutional comparison is exactly the independent contextual key comparison.
This covers arbitrary actual arms, including arms facing the retained outer root. -/
theorem contextualTrees_compare_eq_compare_key
    {input : CertifiedLocalizedCIPInput} {carrierFuel fuelLeft fuelRight : Nat}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {stageLeft stageRight : LocalizedCumulativeRule45Stage}
    {readLeft readRight : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (leftTrace : LocalizedRuleMajorSortTrace input stageLeft readLeft fuelLeft left leftKey)
    (rightTrace : LocalizedRuleMajorSortTrace input stageRight readRight fuelRight right rightKey)
    {W D : Nat} (leftWidth : (ruleMajorTreeGraph left).width ≤ W)
    (rightWidth : (ruleMajorTreeGraph right).width ≤ W)
    (leftHeight : (ruleMajorTreeGraph left).height ≤ D)
    (rightHeight : (ruleMajorTreeGraph right).height ≤ D) :
    OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional =
      compare
        (contextualRuleKey input.moleculeGraph (ruleMajorTreeGraph left)
          left.source.occurrence.1.root W D (ruleMajorTreeGraph left).root)
        (contextualRuleKey input.moleculeGraph (ruleMajorTreeGraph right)
          right.source.occurrence.1.root W D (ruleMajorTreeGraph right).root) := by
  exact compare_eq_compare_vector
    (wellFormedRuleMajorKey_of_tableMatch
      (LocalizedRuleMajorSortTrace.fullMatch_of_trace leftTrace).tableMatch
      (LocalizedRuleMajorSortTrace.realizes_of_trace leftTrace))
    (wellFormedRuleMajorKey_of_tableMatch
      (LocalizedRuleMajorSortTrace.fullMatch_of_trace rightTrace).tableMatch
      (LocalizedRuleMajorSortTrace.realizes_of_trace rightTrace))
    (ruleKeyWithObservations_vectorWellShaped (ruleMajorTreeGraph left) _ W D _)
    (ruleKeyWithObservations_vectorWellShaped (ruleMajorTreeGraph right) _ W D _)
    (contextualTree_root_represents_layout singleBonded acyclic left leftTrace leftWidth leftHeight)
    (contextualTree_root_represents_layout singleBonded acyclic right rightTrace rightWidth rightHeight)

/-- Every valid actual cursor builds successfully and yields a canonical contextual addressing
and a represented independent key. No successful build or comparison premise is supplied. -/
theorem exists_contextualKey_at_valid_cursor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      tree.source = cursor ∧
        input.buildRuleMajorCumulativeWithRead? stage read (2 * (carrierFuel + 1)) cursor = some key ∧
        Dense (toOfficialSourceTree tree).declarativeAddressing ∧
        KeySorted
          (contextualRuleKey input.moleculeGraph (ruleMajorTreeGraph tree)
            cursor.occurrence.1.root (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height)
          (toOfficialSourceTree tree).declarativeAddressing ∧
        Represents (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
          (contextualRuleKey input.moleculeGraph (ruleMajorTreeGraph tree)
            cursor.occurrence.1.root (ruleMajorTreeGraph tree).width
            (ruleMajorTreeGraph tree).height (ruleMajorTreeGraph tree).root)
          key.constitutional := by
  obtain ⟨tree, key, source, built, trace⟩ :=
    exists_ruleMajorTrace_at_twice input stage read cursor valid
  have observations := contextualTree_nodeObservation singleBonded acyclic tree
    (LocalizedRuleMajorSortTrace.realizes_of_trace trace)
  have canonical := observedTree_canonicalAddressing tree _ observations trace
  have represents := contextualTree_root_represents singleBonded acyclic tree trace
  refine ⟨tree, key, source, built, canonical.1, ?_, ?_⟩
  · simpa only [contextualRuleKey, source] using canonical.2
  · simpa only [source] using represents

/-- At the adequate molecular budget the same successful actual tree covers exactly the
independent incoming-cut molecular inventory. This rules out proving comparison correctness
merely for a truncated occurrence expansion. -/
theorem exists_contextualKey_fullInventory
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      tree.source = cursor ∧
        input.buildRuleMajorCumulativeWithRead? stage read (2 * (carrierFuel + 1)) cursor = some key ∧
        PhysicalFullCutTree input.moleculeGraph
          (cursor.previous?.bind (fun previous => previous.1.node.current?))
          (nodeAtom singleBonded acyclic tree)
          (physicalErasure singleBonded acyclic tree) ∧
        Dense (toOfficialSourceTree tree).declarativeAddressing ∧
        KeySorted
          (contextualRuleKey input.moleculeGraph (ruleMajorTreeGraph tree)
            cursor.occurrence.1.root (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height)
          (toOfficialSourceTree tree).declarativeAddressing ∧
        Represents (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
          (contextualRuleKey input.moleculeGraph (ruleMajorTreeGraph tree)
            cursor.occurrence.1.root (ruleMajorTreeGraph tree).width
            (ruleMajorTreeGraph tree).height (ruleMajorTreeGraph tree).root)
          key.constitutional := by
  obtain ⟨tree, key, source, built, trace⟩ :=
    exists_ruleMajorTrace_at_twice input stage read cursor valid
  have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace trace
  have canonical := observedTree_canonicalAddressing tree _
    (contextualTree_nodeObservation singleBonded acyclic tree realizes) trace
  have represents := contextualTree_root_represents singleBonded acyclic tree trace
  refine ⟨tree, key, source, built, ?_, canonical.1, ?_, ?_⟩
  · exact physicalErasure_full enough singleBonded acyclic realizes
      (by simpa only [source] using valid) _ (by rw [source]) _ rfl
  · simpa only [contextualRuleKey, source] using canonical.2
  · simpa only [source] using represents

/-- End-to-end constitutional comparison at two arbitrary valid rerooting cursors. Both actual
build equations and the common comparison window are constructed, not supplied by the caller. -/
theorem exists_contextualComparison_at_valid_cursors
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (leftValid : input.LocalizedRerootCursorValid leftCursor)
    (rightValid : input.LocalizedRerootCursorValid rightCursor) :
    ∃ (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
      (leftKey rightKey : input.LocalizedRerootCumulativeRule45Key),
      left.source = leftCursor ∧ right.source = rightCursor ∧
      input.buildRuleMajorCumulativeWithRead? stage read (2 * (carrierFuel + 1)) leftCursor =
        some leftKey ∧
      input.buildRuleMajorCumulativeWithRead? stage read (2 * (carrierFuel + 1)) rightCursor =
        some rightKey ∧
      let W := max (ruleMajorTreeGraph left).width (ruleMajorTreeGraph right).width
      let D := max (ruleMajorTreeGraph left).height (ruleMajorTreeGraph right).height
      OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional =
        compare
          (contextualRuleKey input.moleculeGraph (ruleMajorTreeGraph left)
            leftCursor.occurrence.1.root W D (ruleMajorTreeGraph left).root)
          (contextualRuleKey input.moleculeGraph (ruleMajorTreeGraph right)
            rightCursor.occurrence.1.root W D (ruleMajorTreeGraph right).root) := by
  obtain ⟨left, leftKey, leftSource, leftBuilt, leftTrace⟩ :=
    exists_ruleMajorTrace_at_twice input stage read leftCursor leftValid
  obtain ⟨right, rightKey, rightSource, rightBuilt, rightTrace⟩ :=
    exists_ruleMajorTrace_at_twice input stage read rightCursor rightValid
  refine ⟨left, right, leftKey, rightKey, leftSource, rightSource, leftBuilt, rightBuilt, ?_⟩
  simpa only [leftSource, rightSource] using
    contextualTrees_compare_eq_compare_key singleBonded acyclic left right leftTrace rightTrace
      (Nat.le_max_left _ _) (Nat.le_max_right _ _) (Nat.le_max_left _ _) (Nat.le_max_right _ _)

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextualTree_root_represents_layout
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextualTrees_compare_eq_compare_key
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.exists_contextualKey_at_valid_cursor
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.exists_contextualKey_fullInventory
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.exists_contextualComparison_at_valid_cursors
