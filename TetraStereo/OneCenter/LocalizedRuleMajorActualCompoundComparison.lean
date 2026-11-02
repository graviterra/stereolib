import TetraStereo.OneCenter.LocalizedRuleMajorCompoundIndependentReadings
import TetraStereo.OneCenter.LocalizedRuleMajorCrossBranchReadingComparison
import TetraStereo.OneCenter.LocalizedRuleMajorCompoundComparisonAlgebra
import TetraStereo.OneCenter.LocalizedRuleMajorRule4aPairComparison
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual whole-rule compound comparison against an independently defined molecular key.
All reference populations, complete alternatives and their ordering are derived from successful
builders. Empty-reference branches retain their Rule-4c observations. The theorem is through
Rule 4c; it does not assert a Rule-5 decision or physical descriptor correctness. -/

namespace TetraStereo.OneCenter.DeclarativeCIP
noncomputable section
universe u

abbrev CompleteLigandPriorKey := Lex (MolecularRankPair × CompletePriorSignature)

def completeLigandPriorKeyAt {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom) (W D : Nat) :
    CompleteLigandPriorKey :=
  toLex (molecularRankPairAt molecule descriptorMap unit graph W D,
    completePriorSignatureAt molecule descriptorMap unit graph W D)

theorem completeLigandPriorKeyAt_eq_of_faithful
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (externalParent ligand : Atom)
    {left right : RootedDigraph Atom}
    (faithfulL : left.FaithfulExactExpansion molecule externalParent ligand)
    (faithfulR : right.FaithfulExactExpansion molecule externalParent ligand) (W D : Nat) :
    completeLigandPriorKeyAt molecule descriptorMap unit left W D =
      completeLigandPriorKeyAt molecule descriptorMap unit right W D := by
  unfold completeLigandPriorKeyAt
  rw [molecularRankPairAt_eq_of_faithful molecule descriptorMap unit externalParent ligand
    faithfulL faithfulR W D,
    completePriorSignatureAt_eq_of_faithful molecule descriptorMap unit externalParent ligand
      faithfulL faithfulR W D]

theorem ReferenceSelection.empty_iff_of_countPriority_eq {left right : ReferenceSelection}
    (counts : left.countPriority = right.countPriority) : left = .empty ↔ right = .empty := by
  cases left <;> cases right <;> simp_all [ReferenceSelection.countPriority]

end
end TetraStereo.OneCenter.DeclarativeCIP

namespace TetraStereo.OneCenter.Rule4aTableBridge
open CertifiedLocalizedCIPInput DeclarativeCIP
noncomputable section

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

include tetrahedral targetRoot targetAddress singleBonded acyclic
  leftWidth leftDepth rightWidth rightDepth

private theorem reading_comparisons
    (dataL : RuleMajorCompoundReadbackData leftStages left W D)
    (dataR : RuleMajorCompoundReadbackData rightStages right W D)
    (aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq)
    (countTie : left.prior.referenceCountPriority = right.prior.referenceCountPriority)
    (l : input.LocalizedRerootRule4bcReading) (hl : l ∈ left.prior.readings)
    (r : input.LocalizedRerootRule4bcReading) (hr : r ∈ right.prior.readings) :
    let observedL := completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
      leftStages.graph W D (l.reference?.map senseOf)
    let observedR := completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
      rightStages.graph W D (r.reference?.map senseOf)
    input.compareLocalizedRerootRule4bcReadingsByRule4b l r =
        compare (ofLex observedL).1 (ofLex observedR).1 ∧
      (input.compareLocalizedRerootRule4bcReadingsByRule4b l r = .eq →
        OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
          l.rule4cKey.descriptor r.rule4cKey.descriptor =
            compare (ofLex observedL).2 (ofLex observedR).2) := by
  dsimp only
  have emptyIff := ReferenceSelection.empty_iff_of_countPriority_eq
    (dataL.count.symm.trans (countTie.trans dataR.count))
  have lp := dataL.readingStages l hl
  have rp := dataR.readingStages r hr
  cases hL : l.reference? with
  | none =>
      have rightNone := (dataR.readingEmpty r hr).mpr
        (emptyIff.mp ((dataL.readingEmpty l hl).mp hL))
      rw [hL] at lp
      rw [rightNone] at rp
      simp only [rightNone, Option.map_none]
      constructor
      · change OfficialRuleMajorKey.compareSparseLayers _ _ _ = compare ([] :
          Certificate.CanonicalSphereKey.Key StereoLabel) []
        dsimp only
        rw [lp.1, rp.1]
        exact (Ordering.then_eq_eq.mp aTie).2
      · intro _
        rw [lp.2, rp.2]
        exact crossBranch_noReference_completeReading_compare descriptorMap tetrahedral
          target targetRoot targetAddress singleBonded acyclic leftStages rightStages
          aTie leftWidth leftDepth rightWidth rightDepth
  | some refL =>
      cases hR : r.reference? with
      | none =>
          have leftNone := (dataL.readingEmpty l hl).mpr
            (emptyIff.mpr ((dataR.readingEmpty r hr).mp hR))
          simp [hL] at leftNone
      | some refR =>
          rw [hL] at lp
          rw [hR] at rp
          simp only [Option.map_some]
          constructor
          · change OfficialRuleMajorKey.compareSparseLayers _ _ _ = _
            dsimp only
            rw [lp.1, rp.1]
            exact crossBranch_selectedB_completeReading_compare descriptorMap tetrahedral
              target targetRoot targetAddress singleBonded acyclic leftStages rightStages
              refL refR aTie leftWidth leftDepth rightWidth rightDepth
          · intro bTie
            change OfficialRuleMajorKey.compareSparseLayers _
              l.rule4bKey.descriptor r.rule4bKey.descriptor = .eq at bTie
            rw [lp.1, rp.1] at bTie
            rw [lp.2, rp.2]
            exact crossBranch_selectedC_completeReading_compare descriptorMap tetrahedral
              target targetRoot targetAddress singleBonded acyclic leftStages rightStages
              refL refR aTie bTie leftWidth leftDepth rightWidth rightDepth

private theorem compound_after4a_compare
    (dataL : RuleMajorCompoundReadbackData leftStages left W D)
    (dataR : RuleMajorCompoundReadbackData rightStages right W D)
    (aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq) :
    input.compareLocalizedRerootCompoundRule4bcAfterRule4a left.prior right.prior =
      compare (completePriorSignatureAt input.moleculeGraph descriptorMap
        (input.topUnit center) leftStages.graph W D)
        (completePriorSignatureAt input.moleculeGraph descriptorMap
          (input.topUnit center) rightStages.graph W D) := by
  rw [← compare_unmaskedCompletePriorSignature_eq]
  change (compare left.prior.referenceCountPriority right.prior.referenceCountPriority).then _ =
    (compare
      (referenceSelection input.moleculeGraph descriptorMap (input.topUnit center) leftStages.graph).countPriority
      (referenceSelection input.moleculeGraph descriptorMap (input.topUnit center) rightStages.graph).countPriority).then _
  rw [← dataL.count, ← dataR.count]
  apply then_congr
  intro countTie
  have countEq := compare_eq_iff_eq.mp countTie
  let observeL := fun reading : input.LocalizedRerootRule4bcReading =>
    completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
      leftStages.graph W D (reading.reference?.map senseOf)
  let observeR := fun reading : input.LocalizedRerootRule4bcReading =>
    completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
      rightStages.graph W D (reading.reference?.map senseOf)
  have agrees := reading_comparisons descriptorMap tetrahedral target targetRoot targetAddress
    singleBonded acyclic leftStages rightStages leftWidth leftDepth rightWidth rightDepth
    dataL dataR aTie countEq
  have lists := compareLex_then_map_eq
    input.compareLocalizedRerootRule4bcReadingsByRule4b
    (fun l r => OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      l.rule4cKey.descriptor r.rule4cKey.descriptor)
    compare compare (fun l => (ofLex (observeL l)).1) (fun r => (ofLex (observeR r)).1)
    (fun l => (ofLex (observeL l)).2) (fun r => (ofLex (observeR r)).2)
    left.prior.readings right.prior.readings
    (fun l hl r hr => (agrees l hl r hr).1)
    (fun l hl r hr => (agrees l hl r hr).2)
  have fstL := congrArg (List.map (fun key : CompleteReadingKey => (ofLex key).1)) dataL.observations
  have fstR := congrArg (List.map (fun key : CompleteReadingKey => (ofLex key).1)) dataR.observations
  have sndL := congrArg (List.map (fun key : CompleteReadingKey => (ofLex key).2)) dataL.observations
  have sndR := congrArg (List.map (fun key : CompleteReadingKey => (ofLex key).2)) dataR.observations
  simp only [List.map_map, Function.comp_def] at fstL fstR sndL sndR
  dsimp only [observeL, observeR] at lists
  rw [fstL, fstR, sndL, sndR] at lists
  exact lists

/-- Every successful actual compound pair agrees with the independently defined molecular
order through Rule 4c. The construction derives reference selection, sorting and all internal
earlier-rule ties, and retains arbitrary tetrahedral labels and comparison depth. -/
theorem actual_ruleMajor_compound_prior_compare
    (builtL : input.buildActualRuleMajorCompoundRule45Key? target
      (input.molecularView descriptorMap target)
      (2 * (input.certified.input.molecule.atomCount + 1 + 1))
      (input.localizedLigandRootCursor center leftIndex) = some left)
    (builtR : input.buildActualRuleMajorCompoundRule45Key? target
      (input.molecularView descriptorMap target)
      (2 * (input.certified.input.molecule.atomCount + 1 + 1))
      (input.localizedLigandRootCursor center rightIndex) = some right) :
    input.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior =
      compare (completeLigandPriorKeyAt input.moleculeGraph descriptorMap
        (input.topUnit center) leftStages.graph W D)
        (completeLigandPriorKeyAt input.moleculeGraph descriptorMap
          (input.topUnit center) rightStages.graph W D) := by
  have dataL := input.buildActualRuleMajorCompoundRule45Key?_independentReadback descriptorMap
    tetrahedral target targetRoot targetAddress singleBonded acyclic leftStages leftWidth leftDepth builtL
  have dataR := input.buildActualRuleMajorCompoundRule45Key?_independentReadback descriptorMap
    tetrahedral target targetRoot targetAddress singleBonded acyclic rightStages rightWidth rightDepth builtR
  have initialCompare := ruleMajor_rule4a_pair_compare ⟨input⟩ descriptorMap tetrahedral target
    targetRoot targetAddress singleBonded acyclic leftStages.a rightStages.a
    (leftStages.a_width_le.trans leftWidth) (leftStages.a_depth_le.trans leftDepth)
    (rightStages.a_width_le.trans rightWidth) (rightStages.a_depth_le.trans rightDepth)
  change (input.compareLocalizedRerootCumulativeRule45Keys left.prior.rule4aKey
    right.prior.rule4aKey).then
      (input.compareLocalizedRerootCompoundRule4bcAfterRule4a left.prior right.prior) =
    (compare
      (molecularRankPairAt input.moleculeGraph descriptorMap (input.topUnit center) leftStages.graph W D)
      (molecularRankPairAt input.moleculeGraph descriptorMap (input.topUnit center) rightStages.graph W D)).then _
  rw [dataL.aKey, dataR.aKey, ← initialCompare]
  exact then_congr (fun tied => compound_after4a_compare descriptorMap tetrahedral target
    targetRoot targetAddress singleBonded acyclic leftStages rightStages leftWidth leftDepth
    rightWidth rightDepth dataL dataR tied)

end
end TetraStereo.OneCenter.Rule4aTableBridge

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completeLigandPriorKeyAt_eq_of_faithful
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ReferenceSelection.empty_iff_of_countPriority_eq
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.actual_ruleMajor_compound_prior_compare
