import TetraStereo.OneCenter.LocalizedRuleMajorRule4cActualRefinement
import TetraStereo.OneCenter.LocalizedRuleMajorNoReference4cActualRefinement
import TetraStereo.OneCenter.LocalizedRuleMajorActualEvidenceRefinement
import TetraStereo.OneCenter.DeclarativeCIPCompleteReadingProjection
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Scalar comparisons of actual molecular reading stages, expressed on arbitrary faithful
expansions. Earlier-column ties are explicit here: the compound assembly discharges them using
cross-stage prefix preservation. Lowercase auxiliary labels remain visible throughout. -/

namespace TetraStereo.OneCenter.Rule4aTableBridge
open LocalizedCumulativeDecoratedTree CertifiedLocalizedCIPInput DeclarativeCIP
open Rule4cObservationBridge
noncomputable section

variable {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
  {leftIndex rightIndex : Fin 4} {leftReference rightReference : RS}
  (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
  (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
  (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
  (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic)

include tetrahedral targetRoot targetAddress singleBonded acyclic

theorem actual_ruleMajor_scalar4b_compare
    (left : input.RuleMajorRootArm center leftIndex (.rule4b leftReference)
      (input.molecularReader descriptorMap target))
    (right : input.RuleMajorRootArm center rightIndex (.rule4b rightReference)
      (input.molecularReader descriptorMap target))
    (graphL graphR : RootedDigraph input.Atom)
    (faithfulL : graphL.FaithfulExactExpansion input.moleculeGraph center.1
      (input.canonicalLigandAtom center leftIndex))
    (faithfulR : graphR.FaithfulExactExpansion input.moleculeGraph center.1
      (input.canonicalLigandAtom center rightIndex))
    {W D : Nat} (widthL : (ruleMajorArmGraph left).width ≤ W)
    (depthL : (ruleMajorArmGraph left).height ≤ D)
    (widthR : (ruleMajorArmGraph right).width ≤ W)
    (depthR : (ruleMajorArmGraph right).height ≤ D)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left.key.constitutional.rule1a right.key.constitutional.rule1a = .eq)
    (tied4a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4a left.key) (scalar4a right.key) = .eq) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4b left.key) (scalar4b right.key) =
      compare
        (readingAt input.moleculeGraph descriptorMap (input.topUnit center) graphL W D
          (senseOf leftReference))
        (readingAt input.moleculeGraph descriptorMap (input.topUnit center) graphR W D
          (senseOf rightReference)) := by
  exact compare_of_pathFirstDifference
    (ordinaryKey_stereo_wellShaped input.moleculeGraph graphL _ W D
      .rule4bLikeUnlikeDescriptorPairs graphL.root)
    (ordinaryKey_stereo_wellShaped input.moleculeGraph graphR _ W D
      .rule4bLikeUnlikeDescriptorPairs graphR.root)
    (ruleMajor_reading_represents_every_faithful descriptorMap tetrahedral target targetRoot
      targetAddress singleBonded acyclic left graphL faithfulL widthL depthL)
    (ruleMajor_reading_represents_every_faithful descriptorMap tetrahedral target targetRoot
      targetAddress singleBonded acyclic right graphR faithfulR widthR depthR)
    (fun outcome => rule4b_pathFirstDifference_iff left.tableMatch right.tableMatch
      left.realizes right.realizes tied tied4a outcome)

theorem actual_ruleMajor_scalar4c_compare
    (left : input.RuleMajorRootArm center leftIndex (.rule4c leftReference)
      (input.molecularReader descriptorMap target))
    (right : input.RuleMajorRootArm center rightIndex (.rule4c rightReference)
      (input.molecularReader descriptorMap target))
    (graphL graphR : RootedDigraph input.Atom)
    (faithfulL : graphL.FaithfulExactExpansion input.moleculeGraph center.1
      (input.canonicalLigandAtom center leftIndex))
    (faithfulR : graphR.FaithfulExactExpansion input.moleculeGraph center.1
      (input.canonicalLigandAtom center rightIndex))
    {W D : Nat} (widthL : (ruleMajorArmGraph left).width ≤ W)
    (depthL : (ruleMajorArmGraph left).height ≤ D)
    (widthR : (ruleMajorArmGraph right).width ≤ W)
    (depthR : (ruleMajorArmGraph right).height ≤ D)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left.key.constitutional.rule1a right.key.constitutional.rule1a = .eq)
    (tied4a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4a left.key) (scalar4a right.key) = .eq) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4c left.key) (scalar4c right.key) =
      compare
        (ofLex (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          graphL W D (some (senseOf leftReference)))).2
        (ofLex (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          graphR W D (some (senseOf rightReference)))).2 := by
  exact compare_of_pathFirstDifference
    (ordinaryKey_stereo_wellShaped input.moleculeGraph graphL _ W D
      .rule4cPseudoasymmetricDescriptor graphL.root)
    (ordinaryKey_stereo_wellShaped input.moleculeGraph graphR _ W D
      .rule4cPseudoasymmetricDescriptor graphR.root)
    (ruleMajor_reading4c_represents_every_faithful descriptorMap tetrahedral target targetRoot
      targetAddress singleBonded acyclic left graphL faithfulL widthL depthL)
    (ruleMajor_reading4c_represents_every_faithful descriptorMap tetrahedral target targetRoot
      targetAddress singleBonded acyclic right graphR faithfulR widthR depthR)
    (fun outcome => rule4c_pathFirstDifference_iff left.tableMatch right.tableMatch
      (LocalizedRuleMajorSortTrace.fullMatch_of_trace left.trace).labelMatch
      (LocalizedRuleMajorSortTrace.fullMatch_of_trace right.trace).labelMatch
      left.realizes right.realizes tied tied4a outcome)

theorem actual_ruleMajor_noReference4c_compare
    (left : input.RuleMajorRootArm center leftIndex .rule4cNoReference
      (input.molecularReader descriptorMap target))
    (right : input.RuleMajorRootArm center rightIndex .rule4cNoReference
      (input.molecularReader descriptorMap target))
    (graphL graphR : RootedDigraph input.Atom)
    (faithfulL : graphL.FaithfulExactExpansion input.moleculeGraph center.1
      (input.canonicalLigandAtom center leftIndex))
    (faithfulR : graphR.FaithfulExactExpansion input.moleculeGraph center.1
      (input.canonicalLigandAtom center rightIndex))
    {W D : Nat} (widthL : (ruleMajorArmGraph left).width ≤ W)
    (depthL : (ruleMajorArmGraph left).height ≤ D)
    (widthR : (ruleMajorArmGraph right).width ≤ W)
    (depthR : (ruleMajorArmGraph right).height ≤ D)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left.key.constitutional.rule1a right.key.constitutional.rule1a = .eq)
    (tied4a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4a left.key) (scalar4a right.key) = .eq) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4b left.key) (scalar4b right.key) =
      compare
        (ofLex (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          graphL W D none)).2
        (ofLex (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          graphR W D none)).2 := by
  exact compare_of_pathFirstDifference
    (ordinaryKey_stereo_wellShaped input.moleculeGraph graphL _ W D
      .rule4cPseudoasymmetricDescriptor graphL.root)
    (ordinaryKey_stereo_wellShaped input.moleculeGraph graphR _ W D
      .rule4cPseudoasymmetricDescriptor graphR.root)
    (ruleMajor_noReference4c_represents_every_faithful descriptorMap tetrahedral target targetRoot
      targetAddress singleBonded acyclic left graphL faithfulL widthL depthL)
    (ruleMajor_noReference4c_represents_every_faithful descriptorMap tetrahedral target targetRoot
      targetAddress singleBonded acyclic right graphR faithfulR widthR depthR)
    (fun outcome => noReference4c_pathFirstDifference_iff left.tableMatch right.tableMatch
      (LocalizedRuleMajorSortTrace.fullMatch_of_trace left.trace).labelMatch
      (LocalizedRuleMajorSortTrace.fullMatch_of_trace right.trace).labelMatch
      left.realizes right.realizes tied tied4a outcome)

end
end TetraStereo.OneCenter.Rule4aTableBridge

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.actual_ruleMajor_scalar4b_compare
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.actual_ruleMajor_scalar4c_compare
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.actual_ruleMajor_noReference4c_compare
