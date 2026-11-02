import TetraStereo.OneCenter.LocalizedRuleMajorRule4cActualRefinement
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The actual recursively sorted Rule-4c keys implement the complete independent
constitutional/4a/4b/4c order, with no rigidity, reference-count or no-lowercase hypothesis.
This is the cumulative-stage comparison, not yet the compound alternative-list comparison. -/

namespace TetraStereo.OneCenter.Rule4aTableBridge
open LocalizedCumulativeDecoratedTree CertifiedLocalizedCIPInput DeclarativeCIP
open Rule4cObservationBridge
noncomputable section

theorem ruleMajor_actual_rule4c_pair_compare
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
    {leftIndex rightIndex : Fin 4} {leftReference rightReference : RS}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
    (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic)
    (left : input.RuleMajorRootArm center leftIndex (.rule4c leftReference)
      (input.molecularReader descriptorMap target))
    (right : input.RuleMajorRootArm center rightIndex (.rule4c rightReference)
      (input.molecularReader descriptorMap target))
    {W D : Nat}
    (leftWidth : (ruleMajorArmGraph left).width ≤ W)
    (leftDepth : (ruleMajorArmGraph left).height ≤ D)
    (rightWidth : (ruleMajorArmGraph right).width ≤ W)
    (rightDepth : (ruleMajorArmGraph right).height ≤ D) :
    input.compareRuleMajorCumulativeDescriptor 3 left.key right.key =
      compare
        (rule4abcKey input.moleculeGraph (ruleMajorArmGraph left)
          (readingEvidence4c input.moleculeGraph descriptorMap (input.topUnit center)
            (ruleMajorArmGraph left) (senseOf leftReference)) W D (ruleMajorArmGraph left).root)
        (rule4abcKey input.moleculeGraph (ruleMajorArmGraph right)
          (readingEvidence4c input.moleculeGraph descriptorMap (input.topUnit center)
            (ruleMajorArmGraph right) (senseOf rightReference)) W D (ruleMajorArmGraph right).root) := by
  have readL := ruleMajorReadback4c_of_treeLike descriptorMap tetrahedral target targetRoot
    targetAddress singleBonded acyclic left
  have readR := ruleMajorReadback4c_of_treeLike descriptorMap tetrahedral target targetRoot
    targetAddress singleBonded acyclic right
  have repL := ruleMajorRootArm_node_bridge4c left readL leftWidth leftDepth
    (ruleMajorArmGraph left).root left.tree left.key left.trace rfl
  have repR := ruleMajorRootArm_node_bridge4c right readR rightWidth rightDepth
    (ruleMajorArmGraph right).root right.tree right.key right.trace rfl
  have comparison := compareRuleMajor_rule4c_eq_then left.tableMatch right.tableMatch
    (LocalizedRuleMajorSortTrace.fullMatch_of_trace left.trace).labelMatch
    (LocalizedRuleMajorSortTrace.fullMatch_of_trace right.trace).labelMatch
    left.realizes right.realizes
    (ruleMajorRootArm_node_bridge left leftWidth leftDepth
      (ruleMajorArmGraph left).root left.tree left.key left.trace rfl).2
    (ruleMajorRootArm_node_bridge right rightWidth rightDepth
      (ruleMajorArmGraph right).root right.tree right.key right.trace rfl).2
    (ordinaryKey_stereo_wellShaped input.moleculeGraph (ruleMajorArmGraph left) _ W D
      .rule4aStereogenicUnitKind (ruleMajorArmGraph left).root)
    (ordinaryKey_stereo_wellShaped input.moleculeGraph (ruleMajorArmGraph right) _ W D
      .rule4aStereogenicUnitKind (ruleMajorArmGraph right).root)
    (ordinaryKey_stereo_wellShaped input.moleculeGraph (ruleMajorArmGraph left) _ W D
      .rule4bLikeUnlikeDescriptorPairs (ruleMajorArmGraph left).root)
    (ordinaryKey_stereo_wellShaped input.moleculeGraph (ruleMajorArmGraph right) _ W D
      .rule4bLikeUnlikeDescriptorPairs (ruleMajorArmGraph right).root)
    (ordinaryKey_stereo_wellShaped input.moleculeGraph (ruleMajorArmGraph left) _ W D
      .rule4cPseudoasymmetricDescriptor (ruleMajorArmGraph left).root)
    (ordinaryKey_stereo_wellShaped input.moleculeGraph (ruleMajorArmGraph right) _ W D
      .rule4cPseudoasymmetricDescriptor (ruleMajorArmGraph right).root)
    repL.2.1 repR.2.1 repL.2.2.1 repR.2.2.1 repL.2.2.2 repR.2.2.2
  rw [Ordering.then_assoc, Ordering.then_assoc] at comparison
  exact comparison

end
end TetraStereo.OneCenter.Rule4aTableBridge

namespace TetraStereo.OneCenter.LocalizedRuleMajorReference
open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
noncomputable section

/-- Two executable stages of the evaluator's own generated state succeed and compare by
the independent complete key. No map, successful build, sortedness or comparison is supplied.
The common layout is any finite bound on these actual expansions, not a fixed depth bound. -/
theorem generated_rule4c_pair_comparison (input : Input)
    (center : input.certified.TetrahedralCenter) (leftIndex rightIndex : Fin 4)
    (leftReference rightReference : RS)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic) :
    let target := ActualReaderPhysicalBranchInverse.topTarget input center
    let reader := input.certified.localizedDependencyLabel target
      (input.certified.localizedDependencyView (referenceState input) target)
    ∃ (left : input.certified.RuleMajorRootArm center leftIndex (.rule4c leftReference) reader)
      (right : input.certified.RuleMajorRootArm center rightIndex (.rule4c rightReference) reader),
      input.certified.buildRuleMajorCumulativeWithReadExec? (.rule4c leftReference) reader
          (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
          (input.certified.localizedLigandRootCursor center leftIndex) = some left.key ∧
      input.certified.buildRuleMajorCumulativeWithReadExec? (.rule4c rightReference) reader
          (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
          (input.certified.localizedLigandRootCursor center rightIndex) = some right.key ∧
      ∀ W D : Nat, (ruleMajorArmGraph left).width ≤ W →
        (ruleMajorArmGraph left).height ≤ D → (ruleMajorArmGraph right).width ≤ W →
        (ruleMajorArmGraph right).height ≤ D →
        input.certified.compareRuleMajorCumulativeDescriptor 3 left.key right.key =
          compare
            (rule4abcKey input.certified.moleculeGraph (ruleMajorArmGraph left)
              (readingEvidence4c input.certified.moleculeGraph (descriptorMap input)
                (input.certified.topUnit center) (ruleMajorArmGraph left) (senseOf leftReference))
              W D (ruleMajorArmGraph left).root)
            (rule4abcKey input.certified.moleculeGraph (ruleMajorArmGraph right)
              (readingEvidence4c input.certified.moleculeGraph (descriptorMap input)
                (input.certified.topUnit center) (ruleMajorArmGraph right) (senseOf rightReference))
              W D (ruleMajorArmGraph right).root) := by
  dsimp only
  rw [← molecularReader_eq_generatedReader input singleBonded acyclic]
  obtain ⟨left⟩ := input.certified.exists_ruleMajorRootArm center leftIndex (.rule4c leftReference)
    (input.certified.molecularReader (descriptorMap input)
      (ActualReaderPhysicalBranchInverse.topTarget input center))
  obtain ⟨right⟩ := input.certified.exists_ruleMajorRootArm center rightIndex (.rule4c rightReference)
    (input.certified.molecularReader (descriptorMap input)
      (ActualReaderPhysicalBranchInverse.topTarget input center))
  refine ⟨left, right, ?_, ?_, ?_⟩
  · rw [input.certified.buildRuleMajorCumulativeWithReadExec_eq]
    exact left.built
  · rw [input.certified.buildRuleMajorCumulativeWithReadExec_eq]
    exact right.built
  · intro W D widthL depthL widthR depthR
    exact ruleMajor_actual_rule4c_pair_compare (descriptorMap input)
      (descriptorMap_tetrahedral input) (ActualReaderPhysicalBranchInverse.topTarget input center)
      (ActualReaderPhysicalBranchInverse.topTarget_root input center)
      (ActualReaderPhysicalBranchInverse.topTarget_address input center)
      singleBonded acyclic left right widthL depthL widthR depthR

end
end TetraStereo.OneCenter.LocalizedRuleMajorReference

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajor_actual_rule4c_pair_compare
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.generated_rule4c_pair_comparison
