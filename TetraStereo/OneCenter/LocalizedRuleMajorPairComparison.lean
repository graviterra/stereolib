import TetraStereo.OneCenter.LocalizedRuleMajorActualEvidenceRefinement
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Comparison of actual rule-major arm keys against the independent constitutional,
Rule-4a and Rule-4b keys. Both arms may contain lowercase auxiliary descriptors. The
common finite layout is a proof parameter bounding the two actual expansions, not a
fixed depth restriction. -/

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge
open LocalizedCumulativeDecoratedTree CertifiedLocalizedCIPInput DeclarativeCIP
open OfficialSparseCanonicalVectorComparison
noncomputable section
open scoped Classical

/-- The generic column transfer permits two different faithful expansion graphs. -/
theorem compareRuleMajor_across_graphs
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {tree₁ tree₂ : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key₁ key₂ : input.LocalizedRerootCumulativeRule45Key} {ρ₁ ρ₂ : RS}
    {read₁ read₂ : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (match₁ : LocalizedCumulativeTreeTableMatch (.rule4b ρ₁) tree₁ key₁)
    (match₂ : LocalizedCumulativeTreeTableMatch (.rule4b ρ₂) tree₂ key₂)
    (realizes₁ : LocalizedCumulativeTreeRealizes input read₁ tree₁)
    (realizes₂ : LocalizedCumulativeTreeRealizes input read₂ tree₂)
    {W D : Nat} {graph₁ graph₂ : RootedDigraph input.Atom} {child₁ : graph₁.Node} {child₂ : graph₂.Node}
    (repC₁ : Represents W D (ruleKey input.moleculeGraph graph₁ W D child₁) key₁.constitutional)
    (repC₂ : Represents W D (ruleKey input.moleculeGraph graph₂ W D child₂) key₂.constitutional)
    {K4a₁ K4a₂ K4b₁ K4b₂ : Certificate.CanonicalSphereKey.Key DeclarativeCIP.StereoLabel}
    (shaped4a₁ : Certificate.CanonicalSphereKey.WellShaped W D K4a₁)
    (shaped4a₂ : Certificate.CanonicalSphereKey.WellShaped W D K4a₂)
    (shaped4b₁ : Certificate.CanonicalSphereKey.WellShaped W D K4b₁)
    (shaped4b₂ : Certificate.CanonicalSphereKey.WellShaped W D K4b₂)
    (rep4a₁ : Represents4a W D K4a₁ key₁) (rep4a₂ : Represents4a W D K4a₂ key₂)
    (rep4b₁ : Represents4b W D K4b₁ key₁) (rep4b₂ : Represents4b W D K4b₂ key₂) :
    compareRuleMajorCumulativeDescriptor input 2 key₁ key₂ =
      (compare (ruleKey input.moleculeGraph graph₁ W D child₁)
          (ruleKey input.moleculeGraph graph₂ W D child₂)).then
        ((compare K4a₁ K4a₂).then (compare K4b₁ K4b₂)) := by
  have wf₁ := wellFormedRuleMajorKey_of_tableMatch match₁ realizes₁
  have wf₂ := wellFormedRuleMajorKey_of_tableMatch match₂ realizes₂
  have hconst : OfficialRuleMajorKey.compare key₁.constitutional key₂.constitutional =
      compare (ruleKey input.moleculeGraph graph₁ W D child₁)
        (ruleKey input.moleculeGraph graph₂ W D child₂) :=
    compare_eq_compare_vector wf₁ wf₂
      (ruleKey_vectorWellShaped input.moleculeGraph graph₁ W D child₁)
      (ruleKey_vectorWellShaped input.moleculeGraph graph₂ W D child₂) repC₁ repC₂
  rw [compareRuleMajor_two, hconst]
  rcases hc : compare (ruleKey input.moleculeGraph graph₁ W D child₁)
      (ruleKey input.moleculeGraph graph₂ W D child₂) with _ | _ | _
  · rfl
  · simp only [Ordering.then]
    have tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        key₁.constitutional.rule1a key₂.constitutional.rule1a = Ordering.eq := by
      have h : OfficialRuleMajorKey.compare key₁.constitutional key₂.constitutional = Ordering.eq := by
        rw [hconst, hc]
      unfold OfficialRuleMajorKey.compare at h
      exact (compareLex_eq_eq.1 h).1
    have h4a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4a key₁) (scalar4a key₂) = compare K4a₁ K4a₂ :=
      compare_of_pathFirstDifference shaped4a₁ shaped4a₂ rep4a₁ rep4a₂
        (fun outcome => rule4a_pathFirstDifference_iff_rule4b match₁ match₂ realizes₁ realizes₂ tied
          outcome)
    rw [h4a]
    rcases h4 : compare K4a₁ K4a₂ with _ | _ | _
    · rfl
    · exact compare_of_pathFirstDifference shaped4b₁ shaped4b₂ rep4b₁ rep4b₂
        (fun outcome => rule4b_pathFirstDifference_iff match₁ match₂ realizes₁ realizes₂ tied
          (h4a.trans h4) outcome)
    · rfl
  · rfl


/-- Two actual arms compare as their independent whole-rule keys, with all readback and
recursive sorting obligations derived from the molecular input and descriptor map. -/
theorem ruleMajor_actual_pair_compare
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
    {leftIndex rightIndex : Fin 4} {leftReference rightReference : RS}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
    (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic)
    (left : input.RuleMajorRootArm center leftIndex (.rule4b leftReference)
      (input.molecularReader descriptorMap target))
    (right : input.RuleMajorRootArm center rightIndex (.rule4b rightReference)
      (input.molecularReader descriptorMap target))
    {W D : Nat}
    (leftWidth : (ruleMajorArmGraph left).width ≤ W)
    (leftDepth : (ruleMajorArmGraph left).height ≤ D)
    (rightWidth : (ruleMajorArmGraph right).width ≤ W)
    (rightDepth : (ruleMajorArmGraph right).height ≤ D) :
    input.compareRuleMajorCumulativeDescriptor 2 left.key right.key =
      (compare
        (ruleKey input.moleculeGraph (ruleMajorArmGraph left) W D (ruleMajorArmGraph left).root)
        (ruleKey input.moleculeGraph (ruleMajorArmGraph right) W D (ruleMajorArmGraph right).root)).then
      ((compare
        (rule4aComponent input.moleculeGraph (ruleMajorArmGraph left)
          (readingEvidence input.moleculeGraph descriptorMap (input.topUnit center)
            (ruleMajorArmGraph left) (senseOf leftReference)) W D (ruleMajorArmGraph left).root)
        (rule4aComponent input.moleculeGraph (ruleMajorArmGraph right)
          (readingEvidence input.moleculeGraph descriptorMap (input.topUnit center)
            (ruleMajorArmGraph right) (senseOf rightReference)) W D (ruleMajorArmGraph right).root)).then
       (compare
        (rule4bComponent input.moleculeGraph (ruleMajorArmGraph left)
          (readingEvidence input.moleculeGraph descriptorMap (input.topUnit center)
            (ruleMajorArmGraph left) (senseOf leftReference)) W D (ruleMajorArmGraph left).root)
        (rule4bComponent input.moleculeGraph (ruleMajorArmGraph right)
          (readingEvidence input.moleculeGraph descriptorMap (input.topUnit center)
            (ruleMajorArmGraph right) (senseOf rightReference)) W D (ruleMajorArmGraph right).root))) := by
  have readL := ruleMajorReadback4b_of_treeLike descriptorMap tetrahedral target targetRoot
    targetAddress singleBonded acyclic left
  have readR := ruleMajorReadback4b_of_treeLike descriptorMap tetrahedral target targetRoot
    targetAddress singleBonded acyclic right
  have repL := ruleMajorRootArm_node_bridge4b left readL leftWidth leftDepth
    (ruleMajorArmGraph left).root left.tree left.key left.trace rfl
  have repR := ruleMajorRootArm_node_bridge4b right readR rightWidth rightDepth
    (ruleMajorArmGraph right).root right.tree right.key right.trace rfl
  exact compareRuleMajor_across_graphs left.tableMatch right.tableMatch left.realizes right.realizes
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
    repL.2.1 repR.2.1 repL.2.2 repR.2.2

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.compareRuleMajor_across_graphs
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajor_actual_pair_compare
