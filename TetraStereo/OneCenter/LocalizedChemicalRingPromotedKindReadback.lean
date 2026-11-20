import TetraStereo.OneCenter.LocalizedChemicalRingPromotedStereoReadback
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Actual promoted ties preserve stereogenic kind at matching addresses

The full ordinary comparison refines Rule 4a at every recursive child. Its Rule-4a prefix is
identified with the exact subtree build, not only with the constitutional projection. Thus the
promoted addressings already constructed from actual ties also sort the independent Rule-4a
keys. Equal actual complete keys then give equal kind observations at those same addresses.

This is a derived part of label matching. It does not yet distinguish R from S, or r from s,
and it does not assert that all occurrences are mapped by one molecular automorphism.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingPromotedKindReadback

open CertifiedLocalizedCIPInput DeclarativeCIP RootedDigraph Rule4aTableBridge
open LocalizedCumulativeDecoratedTree LocalizedMarkedRetainedCanonicalFrame
open LocalizedMarkedRetainedCanonicalMarker LocalizedMarkedRetainedSubtreeContext
open LocalizedMarkedRetainedPromotedKey LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking
open LocalizedChemicalRingPromotedConstitutionReadback LocalizedChemicalRingPromotedStereoReadback
open RetainedContextStereoReadback RetainedRule4aCanonicalBridge

noncomputable section
open scoped Classical

variable {input : CertifiedLocalizedCIPInput}
  (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (unit : OccurrenceUnit input.Atom) (targetUnit : input.molecularFrameUnit target.1 = unit)
  (fallback : CompleteLigandRule5Key)
  {fuel : Nat} {tree : LocalizedCumulativeDecoratedTree input (retainedCarrierFuel input)}
  {treeKey : input.LocalizedRerootCumulativeRule45Key}
  (trace : LocalizedRuleMajorSortTrace input .rule4a
    (input.localizedDependencyLabel target (input.molecularView descriptorMap target)) fuel tree treeKey)
  (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
  (single : input.moleculeGraph.SimpleBonded)
  (rootChild : tree.source ∈ input.executableLocalizedRerootChildren ⟨target, none⟩)
  (W D : Nat) (width : (ruleMajorTreeGraph tree).width ≤ W)
  (height : (ruleMajorTreeGraph tree).height ≤ D)

include trace tetrahedral single rootChild targetUnit width height in
theorem deepPrior_refines_rule4a (parent left right : (ruleMajorTreeGraph tree).Node)
    (edgeL : (ruleMajorTreeGraph tree).child parent left)
    (edgeR : (ruleMajorTreeGraph tree).child parent right)
    (ordered : deepPrior descriptorMap target fallback tree right ≤
      deepPrior descriptorMap target fallback tree left) :
    observedPairKey (ruleMajorTreeGraph tree) (observe tree)
        (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D right ≤
      observedPairKey (ruleMajorTreeGraph tree) (observe tree)
        (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D left := by
  have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace trace
  have hyp := retainedContextTreeRankReadback_of_molecularReader descriptorMap tetrahedral single
    ⟨target, none⟩ unit targetUnit tree realizes rootChild
  have childL := child_edge tree realizes edgeL
  have childR := child_edge tree realizes edgeR
  have validL := input.localizedRerootChild_valid _ _ _
    (input.executableLocalizedRerootChildren_declarative (nodeSource input tree parent)) childL
  have validR := input.localizedRerootChild_valid _ _ _
    (input.executableLocalizedRerootChildren_declarative (nodeSource input tree parent)) childR
  obtain ⟨compoundL, builtL⟩ := ordinaryKey?_exists input target (input.molecularView descriptorMap target)
    (nodeSource input tree left) validL
  obtain ⟨compoundR, builtR⟩ := ordinaryKey?_exists input target (input.molecularView descriptorMap target)
    (nodeSource input tree right) validR
  have comparePrior := deepPrior_agreement descriptorMap target fallback tree realizes tetrahedral
    single rootChild parent left right edgeL edgeR compoundL compoundR builtL builtR
  have fullOrdered : (input.compareLocalizedRerootCompoundThroughRule5 compoundL compoundR).ordering ≠ .lt := by
    rw [comparePrior]
    exact fun h => not_lt_of_ge ordered (compare_lt_iff_lt.mp h)
  have prior := rule4a_ne_lt_of_full_ne_lt compoundL compoundR fullOrdered
  obtain ⟨subL, lookupL⟩ := exists_local_subtree tree left
  obtain ⟨subR, lookupR⟩ := exists_local_subtree tree right
  have decL : tree.decoratedSubtreeAt? left.1 = some subL := by
    rwa [decoratedSubtreeAt?_eq_subtreeAt?]
  have decR : tree.decoratedSubtreeAt? right.1 = some subR := by
    rwa [decoratedSubtreeAt?_eq_subtreeAt?]
  obtain ⟨fuelL, keyL, traceL⟩ := ruleMajorTrace_of_subtree input .rule4a _ trace left.1 subL decL
  obtain ⟨fuelR, keyR, traceR⟩ := ruleMajorTrace_of_subtree input .rule4a _ trace right.1 subR decR
  rw [nodeSource_of_lookup input tree lookupL] at builtL
  rw [nodeSource_of_lookup input tree lookupR] at builtR
  have sameL := subtree_rule4a_eq_ordinary target (input.molecularView descriptorMap target) traceL compoundL builtL
  have sameR := subtree_rule4a_eq_ordinary target (input.molecularView descriptorMap target) traceR compoundR builtR
  rw [← sameL, ← sameR] at prior
  have matchL := (LocalizedRuleMajorSortTrace.fullMatch_of_trace traceL).tableMatch
  have matchR := (LocalizedRuleMajorSortTrace.fullMatch_of_trace traceR).tableMatch
  rw [compareRule4aOld_eq_ruleMajor_one matchL matchR] at prior
  exact observedPairKey_le_of_ruleMajor_compare_ne_lt (observe tree)
    (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
    matchL matchR (LocalizedRuleMajorSortTrace.realizes_of_trace traceL)
    (LocalizedRuleMajorSortTrace.realizes_of_trace traceR)
    (observedTree_node_bridge tree (observe tree) (observe_of_lookup tree) width height left subL keyL traceL decL).2
    (observedTree_node_bridge tree (observe tree) (observe_of_lookup tree) width height right subR keyR traceR decR).2
    (retainedContextTree_node_bridge4a tree (observe tree) (observe_of_lookup tree) hyp
      width height left subL keyL traceL decL).2
    (retainedContextTree_node_bridge4a tree (observe tree) (observe_of_lookup tree) hyp
      width height right subR keyR traceR decR).2 prior

include trace tetrahedral single rootChild targetUnit width height in
theorem promoted_rule4a_sorted (reference : input.Atom) (markerW markerD : Nat)
    {addressing : (ruleMajorTreeGraph tree).Addressing}
    (canonical : PromotedCanonical.CanonicalAddressing (ruleMajorTreeGraph tree)
      (deepPrior descriptorMap target fallback tree) (referenceMark input reference tree)
      markerW markerD addressing) :
    KeySorted (ordinaryKeyWithObservations (ruleMajorTreeGraph tree) (observe tree)
      (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D) addressing := by
  have sorted := PromotedCanonical.canonicalAddressing_prior_sorted _ _ _ _ _ canonical
  have only4a := rule4aOnly_retainedRankEvidence_of_simpleBonded input.moleculeGraph descriptorMap
    unit (ruleMajorTreeGraph tree) single
  intro parent left right slotL slotR addressL addressR slots
  have paired := deepPrior_refines_rule4a descriptorMap target unit targetUnit fallback trace
    tetrahedral single rootChild W D width height parent left right
    ((addressing.child_iff parent left).mpr ⟨slotL, addressL⟩)
    ((addressing.child_iff parent right).mpr ⟨slotR, addressR⟩)
    (sorted parent left right slotL slotR addressL addressR slots)
  exact le_of_not_gt fun less => (not_lt_of_ge paired)
    ((observedOrdinaryKey_lt_iff_pairKey (ruleMajorTreeGraph tree) (observe tree)
      _ only4a W D left right).mp less)

section Frame

theorem frame_rule4a_component_eq
    (frame : RetainedExecutionFrame descriptorMap target)
    (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (single : input.moleculeGraph.SimpleBonded) (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.1 = unit.1) (left right : Fin 4)
    (W D : Nat)
    (widthL : (ruleMajorTreeGraph (frame.stages left).a.tree).width ≤ W)
    (heightL : (ruleMajorTreeGraph (frame.stages left).a.tree).height ≤ D)
    (widthR : (ruleMajorTreeGraph (frame.stages right).a.tree).width ≤ W)
    (heightR : (ruleMajorTreeGraph (frame.stages right).a.tree).height ≤ D)
    (tie : frame.retainedKeys unit left = frame.retainedKeys unit right) :
    observedRule4aComponent (ruleMajorTreeGraph (frame.stages left).a.tree)
        (observe (frame.stages left).a.tree)
        (retainedRankEvidence input.moleculeGraph descriptorMap unit.1
          (ruleMajorTreeGraph (frame.stages left).a.tree)) W D
        (ruleMajorTreeGraph (frame.stages left).a.tree).root =
      observedRule4aComponent (ruleMajorTreeGraph (frame.stages right).a.tree)
        (observe (frame.stages right).a.tree)
        (retainedRankEvidence input.moleculeGraph descriptorMap unit.1
          (ruleMajorTreeGraph (frame.stages right).a.tree)) W D
        (ruleMajorTreeGraph (frame.stages right).a.tree).root := by
  have full := frame.fullOrdering tetrahedral single unit targetUnit left right
  rw [tie, (completeLigandRule5Key_compare_eq_iff _ _).mpr rfl] at full
  have prior := rule4a_eq_of_full_eq (frame.compounds left) (frame.compounds right) full
  have same (slot : Fin 4) : (frame.stages slot).a.key = (frame.compounds slot).prior.rule4aKey := by
    apply subtree_rule4a_eq_ordinary target (input.molecularView descriptorMap target) (frame.stages slot).a.trace
    rw [(frame.stages slot).a.sourceEq]
    exact frame.compoundBuilt slot
  rw [← same left, ← same right] at prior
  have hyp (slot : Fin 4) : RetainedContextTreeRankReadback (frame.stages slot).a.tree descriptorMap unit.1 :=
    retainedContextTreeRankReadback_of_molecularReader descriptorMap tetrahedral single ⟨target, none⟩
      unit.1 targetUnit _ (LocalizedRuleMajorSortTrace.realizes_of_trace (frame.stages slot).a.trace)
      (by rw [(frame.stages slot).a.sourceEq]; exact frame.childAt slot)
  have comparison := retainedContextTrees_rule4a_compare
    (frame.stages left).a.tree (frame.stages right).a.tree (frame.stages left).a.trace
    (frame.stages right).a.trace (observe (frame.stages left).a.tree)
    (observe (frame.stages right).a.tree) (observe_of_lookup _) (observe_of_lookup _)
    (hyp left) (hyp right) widthL widthR heightL heightR
  rw [comparison] at prior
  exact congrArg (fun key => (ofLex key).2) ((pairKeyCompare_eq_eq_iff _ _).mp prior)

end Frame
end
end TetraStereo.OneCenter.LocalizedChemicalRingPromotedKindReadback

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedKindReadback.deepPrior_refines_rule4a
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedKindReadback.promoted_rule4a_sorted
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedKindReadback.frame_rule4a_component_eq
