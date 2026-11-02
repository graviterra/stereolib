import TetraStereo.OneCenter.LocalizedRuleMajorActualRule5ListComparison
import TetraStereo.OneCenter.LocalizedRuleMajorActualCompoundComparison
import TetraStereo.OneCenter.DeclarativeCIPCompleteRule5Order
import TetraStereo.OneCenter.LocalizedGuardedRule5Projection
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Complete actual ligand comparison against independent molecular priority through Rule 5.
The comparison's reference-sensitivity flag is characterized by the independent common-R/S
reading lists. Physical enantiomorphism and the final centre's geometry remain separate notions. -/

namespace TetraStereo.OneCenter.Rule4aTableBridge
open CertifiedLocalizedCIPInput DeclarativeCIP
noncomputable section

private theorem referenceSensitivity_iff (commonR commonS : Ordering) :
    (match commonR with
      | .lt => commonS != .lt
      | .gt => commonS != .gt
      | .eq => false) = true ↔ commonR ≠ .eq ∧ commonR ≠ commonS := by
  cases commonR <;> cases commonS <;> decide

variable {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
  {leftIndex rightIndex : Fin 4}
  (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
  (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
  (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
  (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic)
  (leftStages : input.RuleMajorBranchStages center leftIndex descriptorMap target)
  (rightStages : input.RuleMajorBranchStages center rightIndex descriptorMap target)
  {W D : Nat} (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
  (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D)
  {left right : input.LocalizedRerootCompoundRule45Key}
  (builtL : input.buildActualRuleMajorCompoundRule45Key? target
    (input.molecularView descriptorMap target)
    (2 * (input.certified.input.molecule.atomCount + 1 + 1))
    (input.localizedLigandRootCursor center leftIndex) = some left)
  (builtR : input.buildActualRuleMajorCompoundRule45Key? target
    (input.molecularView descriptorMap target)
    (2 * (input.certified.input.molecule.atomCount + 1 + 1))
    (input.localizedLigandRootCursor center rightIndex) = some right)

include tetrahedral targetRoot targetAddress singleBonded acyclic leftWidth leftDepth
  rightWidth rightDepth builtL builtR

theorem actual_ruleMajor_full_ordering :
    (input.compareLocalizedRerootCompoundThroughRule5 left right).ordering =
      compare
        (completeLigandRule5KeyAt input.moleculeGraph descriptorMap (input.topUnit center)
          leftStages.graph W D)
        (completeLigandRule5KeyAt input.moleculeGraph descriptorMap (input.topUnit center)
          rightStages.graph W D) := by
  have priorCompare := actual_ruleMajor_compound_prior_compare descriptorMap tetrahedral
    target targetRoot targetAddress singleBonded acyclic leftStages rightStages
    leftWidth leftDepth rightWidth rightDepth builtL builtR
  rw [input.compareLocalizedRerootCompoundThroughRule5_ordering]
  change (input.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior).then
    (input.compareLocalizedRerootCompoundRule5Readings .R left.rule5Readings right.rule5Readings) =
    (compare
      (completeLigandPriorKeyAt input.moleculeGraph descriptorMap (input.topUnit center) leftStages.graph W D)
      (completeLigandPriorKeyAt input.moleculeGraph descriptorMap (input.topUnit center) rightStages.graph W D)).then
    (compare
      (completeRule5ReadingsAt input.moleculeGraph descriptorMap (input.topUnit center) leftStages.graph W D .senior)
      (completeRule5ReadingsAt input.moleculeGraph descriptorMap (input.topUnit center) rightStages.graph W D .senior))
  rw [← priorCompare]
  apply then_congr
  intro priorTie
  exact input.actual_ruleMajor_compound_rule5Readings_compare descriptorMap tetrahedral
    target targetRoot targetAddress singleBonded acyclic leftStages rightStages
    leftWidth leftDepth rightWidth rightDepth .R builtL builtR priorTie

theorem actual_ruleMajor_pseudo_iff_referenceSensitive :
    (input.compareLocalizedRerootCompoundThroughRule5 left right).pseudo = true ↔
      ReferenceSensitiveRule5PairAt input.moleculeGraph descriptorMap (input.topUnit center)
        leftStages.graph rightStages.graph W D := by
  have priorCompare := actual_ruleMajor_compound_prior_compare descriptorMap tetrahedral
    target targetRoot targetAddress singleBonded acyclic leftStages rightStages
    leftWidth leftDepth rightWidth rightDepth builtL builtR
  by_cases priorTie : input.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior = .eq
  · have independentTie := (completeLigandPriorKey_compare_eq_iff _ _).mp
      (priorCompare.symm.trans priorTie)
    have commonR := input.actual_ruleMajor_compound_rule5Readings_compare descriptorMap tetrahedral
      target targetRoot targetAddress singleBonded acyclic leftStages rightStages
      leftWidth leftDepth rightWidth rightDepth .R builtL builtR priorTie
    have commonS := input.actual_ruleMajor_compound_rule5Readings_compare descriptorMap tetrahedral
      target targetRoot targetAddress singleBonded acyclic leftStages rightStages
      leftWidth leftDepth rightWidth rightDepth .S builtL builtR priorTie
    rw [input.compareLocalizedRerootCompoundThroughRule5_pseudo_eq_commonS left right priorTie,
      commonR, commonS]
    unfold ReferenceSensitiveRule5PairAt
    simp only [independentTie, true_and, ne_eq, senseOf]
    rw [← listKey_compare_eq_iff]
    exact referenceSensitivity_iff _ _
  · have independentNe : completeLigandPriorKeyAt input.moleculeGraph descriptorMap
        (input.topUnit center) leftStages.graph W D ≠
      completeLigandPriorKeyAt input.moleculeGraph descriptorMap
        (input.topUnit center) rightStages.graph W D := by
      intro equal
      exact priorTie (priorCompare.trans ((completeLigandPriorKey_compare_eq_iff _ _).mpr equal))
    simp [compareLocalizedRerootCompoundThroughRule5, priorTie,
      ReferenceSensitiveRule5PairAt, independentNe]

end
end TetraStereo.OneCenter.Rule4aTableBridge

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.actual_ruleMajor_full_ordering
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.actual_ruleMajor_pseudo_iff_referenceSensitive
