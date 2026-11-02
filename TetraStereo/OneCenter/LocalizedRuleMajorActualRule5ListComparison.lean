import TetraStereo.OneCenter.DeclarativeCIPCompleteRule5Signature
import TetraStereo.OneCenter.LocalizedRuleMajorCompoundRule5Readback
import TetraStereo.OneCenter.LocalizedRuleMajorTaggedReadingOrder
import TetraStereo.OneCenter.LocalizedRuleMajorNoReferenceCompleteComparison
import TetraStereo.OneCenter.LocalizedRuleMajorAbsoluteRule5Comparison
import TetraStereo.OneCenter.LocalizedRuleMajorCompoundComparisonAlgebra
import TetraStereo.OneCenter.LocalizedRuleMajorActualCompoundComparison
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual ranked Rule-5 reading lists compared with the independent absolute Rule-5 signature.
Successful builds provide every alternative and preserve the empty-reference Rule-4c reading. -/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput
open DeclarativeCIP Rule4aTableBridge Rule5ObservationBridge
open LocalizedCumulativeDecoratedTree
noncomputable section
open scoped Classical

private theorem completeListTie_of_rule4b_rule4c_ties
    {input : CertifiedLocalizedCIPInput}
    (left right : List input.LocalizedRerootRule4bcReading)
    (rule4bTie : input.compareLocalizedRerootCompoundRule4bReadings left right = .eq)
    (rule4cTie : input.compareLocalizedRerootCompoundRule4cReadings left right = .eq) :
    List.compareLex input.compareRule4bcReadingsComplete left right = .eq := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons y ys =>
          change List.compareLex input.compareLocalizedRerootRule4bcReadingsByRule4b [] (y :: ys) = .eq at rule4bTie
          have impossible := List.compareLex_nil_left_eq_eq.mp rule4bTie
          cases impossible
  | cons x xs ih =>
      cases right with
      | nil =>
          change List.compareLex input.compareLocalizedRerootRule4bcReadingsByRule4b (x :: xs) [] = .eq at rule4bTie
          have impossible := List.compareLex_nil_right_eq_eq.mp rule4bTie
          cases impossible
      | cons y ys =>
          simp only [compareLocalizedRerootCompoundRule4bReadings,
            compareLocalizedRerootCompoundRule4cReadings,
            List.compareLex_cons_cons, Ordering.then_eq_eq] at rule4bTie rule4cTie
          have cHead : OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
              x.rule4cKey.descriptor y.rule4cKey.descriptor = .eq := by
            simpa [Ordering.byKey] using rule4cTie.1
          have head : input.compareRule4bcReadingsComplete x y = .eq := by
            unfold compareRule4bcReadingsComplete
            rw [localizedCompareLex_eq_right_of_eq rule4bTie.1]
            exact cHead
          rw [List.compareLex_cons_cons, head, Ordering.eq_then]
          exact ih ys rule4bTie.2 rule4cTie.2

private theorem commonReading_descriptor
    {input : CertifiedLocalizedCIPInput} (common : RS)
    (reading : input.LocalizedRerootRule4bcReading) :
    input.localizedRerootRule5Descriptor common
      (input.ruleMajorExpectedRule5Reading reading) =
        (input.rule5LiftKey
          (match reading.reference? with
            | none => false
            | some own => common == own) reading.rule4cKey).descriptor := by
  cases common <;> cases ref : reading.reference? with
  | none => simp [ruleMajorExpectedRule5Reading, localizedRerootRule5Descriptor, ref]
  | some own => cases own <;>
      simp [ruleMajorExpectedRule5Reading, localizedRerootRule5Descriptor, ref]

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
  leftWidth leftDepth rightWidth rightDepth leftStages rightStages

private theorem actualRule5Pair_compare
    (common : RS)
    (leftData : RuleMajorCompoundReadbackData leftStages left W D)
    (rightData : RuleMajorCompoundReadbackData rightStages right W D)
    (aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq)
    (countEq : left.prior.referenceCountPriority = right.prior.referenceCountPriority)
    (x : input.LocalizedRerootRule4bcReading) (hx : x ∈ left.prior.readings)
    (y : input.LocalizedRerootRule4bcReading) (hy : y ∈ right.prior.readings)
    (priorEq : input.compareRule4bcReadingsComplete x y = .eq) :
    Ordering.byKey
        (fun reading => input.localizedRerootRule5Descriptor common
          (input.ruleMajorExpectedRule5Reading reading))
        (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority)
        x y =
      compare
        (absoluteRule5ReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          leftStages.graph W D (x.reference?.map senseOf) (senseOf common))
        (absoluteRule5ReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          rightStages.graph W D (y.reference?.map senseOf) (senseOf common)) := by
  have countValues :
      (referenceSelection input.moleculeGraph descriptorMap (input.topUnit center)
        leftStages.graph).countPriority =
      (referenceSelection input.moleculeGraph descriptorMap (input.topUnit center)
        rightStages.graph).countPriority := by
    rw [← leftData.count, ← rightData.count]
    exact countEq
  have emptyIff := ReferenceSelection.empty_iff_of_countPriority_eq countValues
  have stagesL := leftData.readingStages x hx
  have stagesR := rightData.readingStages y hy
  have priorParts :
      input.compareLocalizedRerootRule4bcReadingsByRule4b x y = .eq ∧
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        x.rule4cKey.descriptor y.rule4cKey.descriptor = .eq := by
    unfold compareRule4bcReadingsComplete at priorEq
    cases hB : input.compareLocalizedRerootRule4bcReadingsByRule4b x y with
    | lt => simp [compareLex, hB] at priorEq
    | gt => simp [compareLex, hB] at priorEq
    | eq =>
        simp [compareLex, hB] at priorEq
        exact ⟨rfl, by simpa [Ordering.byKey, compareLex, hB] using priorEq⟩
  have cmpActual :
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (input.localizedRerootRule5Descriptor common
          (input.ruleMajorExpectedRule5Reading x))
        (input.localizedRerootRule5Descriptor common
          (input.ruleMajorExpectedRule5Reading y)) =
      compare
        (absoluteRule5ReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          leftStages.graph W D (x.reference?.map senseOf) (senseOf common))
        (absoluteRule5ReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          rightStages.graph W D (y.reference?.map senseOf) (senseOf common)) := by
    cases hxRef : x.reference? with
    | none =>
        have leftEmpty := (leftData.readingEmpty x hx).mp hxRef
        have rightEmpty := emptyIff.mp leftEmpty
        have hyRef : y.reference? = none := (rightData.readingEmpty y hy).mpr rightEmpty
        simp [hxRef] at stagesL
        simp [hyRef] at stagesR
        have noRefKeys := stagesL.2
        have noRefKeysR := stagesR.2
        have cTie : OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
            leftStages.noReference.key.descriptor rightStages.noReference.key.descriptor = .eq := by
          simpa [noRefKeys, noRefKeysR] using priorParts.2
        have descEq : leftStages.noReference.key.descriptor = rightStages.noReference.key.descriptor :=
          (compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff _ _).mp cTie
        have actualEq : OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
            (input.rule5LiftKey false leftStages.noReference.key).descriptor
            (input.rule5LiftKey false rightStages.noReference.key).descriptor = .eq := by
          rw [compare_lifts_eq_bits false false leftStages.noReference.key
            rightStages.noReference.key descEq]
          have bitEq : bitTable false leftStages.noReference.key =
              bitTable false rightStages.noReference.key := by
            simp [Rule5ObservationBridge.bitTable, descEq]
          rw [bitEq]
          exact CompilerProjectionFidelity.compareSparseLayers_self
            OfficialRuleMajorKey.compareNat CompilerProjectionFidelity.compareNat_self _
        have independentEq :
            (ofLex (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
              leftStages.graph W D none)).2 =
            (ofLex (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
              rightStages.graph W D none)).2 := by
          have actualCompare := crossBranch_noReference_completeReading_compare
            descriptorMap tetrahedral target targetRoot targetAddress singleBonded acyclic
            leftStages rightStages aTie leftWidth leftDepth rightWidth rightDepth
          have cTie := by simpa only [noRefKeys, noRefKeysR] using priorParts.2
          have cmpRead := actualCompare.symm.trans cTie
          have secondEq :
              (ofLex (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
                leftStages.graph W D none)).2 =
              (ofLex (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
                rightStages.graph W D none)).2 := by
            exact (key_compare_eq_iff _ _).mp cmpRead
          exact secondEq
        have absEq :
            absoluteRule5ReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
              leftStages.graph W D none (senseOf common) =
            absoluteRule5ReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
              rightStages.graph W D none (senseOf common) := by
          simp only [absoluteRule5ReadingAt]
          rw [independentEq]
        rw [commonReading_descriptor common x, commonReading_descriptor common y,
          stagesL.2, stagesR.2, hxRef, hyRef]
        simp only [Option.map_none]
        have rhsEq : compare
            (absoluteRule5ReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
              leftStages.graph W D none (senseOf common))
            (absoluteRule5ReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
              rightStages.graph W D none (senseOf common)) = .eq := by
          rw [absEq]
          exact Std.ReflCmp.compare_self
        exact actualEq.trans rhsEq.symm
    | some ownL =>
        have rightNotEmpty :
            (referenceSelection input.moleculeGraph descriptorMap (input.topUnit center)
              rightStages.graph) ≠ .empty := by
          intro hEmpty
          have leftEmpty := emptyIff.mpr hEmpty
          have leftReadingEmpty := (leftData.readingEmpty x hx).mpr leftEmpty
          simp [hxRef] at leftReadingEmpty
        cases hyRef : y.reference? with
        | none =>
            have rightEmpty := (rightData.readingEmpty y hy).mp hyRef
            exact (rightNotEmpty rightEmpty).elim
        | some ownR =>
            simp [hxRef] at stagesL
            simp [hyRef] at stagesR
            have cTie : OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
                (leftStages.c ownL).key.descriptor (rightStages.c ownR).key.descriptor = .eq := by
              simpa [stagesL.2, stagesR.2] using priorParts.2
            rw [commonReading_descriptor common x, commonReading_descriptor common y,
              stagesL.2, stagesR.2, hxRef, hyRef]
            simp only [Option.map_some]
            exact crossBranch_selected_rule5_compare descriptorMap tetrahedral target targetRoot
              targetAddress singleBonded acyclic leftStages rightStages ownL ownR common
              leftWidth leftDepth rightWidth rightDepth aTie cTie
  simpa only [Ordering.byKey] using cmpActual

/-- For successful actual compound builds whose complete Rules-4b/4c prior ties, comparing the
full common-R or common-S Rule-5 list is exactly comparing the independent absolute Rule-5
readings in each branch's complete-reading order. -/
theorem actual_ruleMajor_compound_rule5Readings_compare
    (common : RS)
    {left right : input.LocalizedRerootCompoundRule45Key}
    (builtL : input.buildActualRuleMajorCompoundRule45Key? target
      (input.molecularView descriptorMap target)
      (2 * (input.certified.input.molecule.atomCount + 1 + 1))
      (input.localizedLigandRootCursor center leftIndex) = some left)
    (builtR : input.buildActualRuleMajorCompoundRule45Key? target
      (input.molecularView descriptorMap target)
      (2 * (input.certified.input.molecule.atomCount + 1 + 1))
      (input.localizedLigandRootCursor center rightIndex) = some right)
    (priorTie : input.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior = .eq) :
    input.compareLocalizedRerootCompoundRule5Readings common left.rule5Readings right.rule5Readings =
      compare
        (completeRule5ReadingsAt input.moleculeGraph descriptorMap (input.topUnit center)
          leftStages.graph W D (senseOf common))
        (completeRule5ReadingsAt input.moleculeGraph descriptorMap (input.topUnit center)
          rightStages.graph W D (senseOf common)) := by
  have tieFacts := (input.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff
    left.prior right.prior).mp priorTie
  have aTie := tieFacts.1
  have countTie : left.prior.referenceCountPriority = right.prior.referenceCountPriority :=
    compare_eq_iff_eq.mp tieFacts.2.1
  have listTie := completeListTie_of_rule4b_rule4c_ties left.prior.readings right.prior.readings
    tieFacts.2.2.1 tieFacts.2.2.2
  have leftData := input.buildActualRuleMajorCompoundRule45Key?_independentReadback
    descriptorMap tetrahedral target targetRoot targetAddress singleBonded acyclic leftStages
    leftWidth leftDepth builtL
  have rightData := input.buildActualRuleMajorCompoundRule45Key?_independentReadback
    descriptorMap tetrahedral target targetRoot targetAddress singleBonded acyclic rightStages
    rightWidth rightDepth builtR
  have stageATie : input.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq := by
    rw [← leftData.aKey, ← rightData.aKey]
    exact aTie
  have leftReadback := input.buildActualRuleMajorCompoundRule45Key?_rule5Readings_eq_map
    descriptorMap tetrahedral target targetRoot targetAddress singleBonded acyclic leftStages
    leftWidth leftDepth builtL
  have rightReadback := input.buildActualRuleMajorCompoundRule45Key?_rule5Readings_eq_map
    descriptorMap tetrahedral target targetRoot targetAddress singleBonded acyclic rightStages
    rightWidth rightDepth builtR
  have tagsL := input.buildActualRuleMajorCompoundRule45Key?_taggedAlternativeReferences
    descriptorMap tetrahedral target targetRoot targetAddress singleBonded acyclic leftStages
    leftWidth leftDepth builtL
  have tagsR := input.buildActualRuleMajorCompoundRule45Key?_taggedAlternativeReferences
    descriptorMap tetrahedral target targetRoot targetAddress singleBonded acyclic rightStages
    rightWidth rightDepth builtR
  rw [leftReadback, rightReadback]
  unfold compareLocalizedRerootCompoundRule5Readings
  simp only [completeRule5ReadingsAt]
  rw [← tagsL, ← tagsR]
  let expectedCmp := Ordering.byKey (fun reading => input.localizedRerootRule5Descriptor common
      (input.ruleMajorExpectedRule5Reading reading))
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority)
  let mappedCmp := Ordering.byKey (input.localizedRerootRule5Descriptor common)
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority)
  have mappedExpected :
      List.compareLex mappedCmp
          (left.prior.readings.map input.ruleMajorExpectedRule5Reading)
          (right.prior.readings.map input.ruleMajorExpectedRule5Reading) =
        List.compareLex expectedCmp left.prior.readings right.prior.readings := by
    exact Rule4aTableBridge.compareLex_map_rel expectedCmp mappedCmp
      input.ruleMajorExpectedRule5Reading (by intro x y; rfl) _ _
  have tiedMap := compareLex_map_eq_of_prior_tie
    input.compareRule4bcReadingsComplete expectedCmp compare
    (fun reading => absoluteRule5ReadingAt input.moleculeGraph descriptorMap
      (input.topUnit center) leftStages.graph W D (reading.reference?.map senseOf)
      (senseOf common))
    (fun reading => absoluteRule5ReadingAt input.moleculeGraph descriptorMap
      (input.topUnit center) rightStages.graph W D (reading.reference?.map senseOf)
      (senseOf common))
    left.prior.readings right.prior.readings
    (fun x hx y hy priorEq => actualRule5Pair_compare descriptorMap tetrahedral target
      targetRoot targetAddress singleBonded acyclic leftStages rightStages leftWidth leftDepth
      rightWidth rightDepth common leftData rightData stageATie countTie x hx y hy priorEq)
    listTie
  calc
    _ = List.compareLex expectedCmp left.prior.readings right.prior.readings := mappedExpected
    _ = List.compareLex compare
        (left.prior.readings.map fun reading => absoluteRule5ReadingAt
          input.moleculeGraph descriptorMap (input.topUnit center) leftStages.graph W D
          (reading.reference?.map senseOf) (senseOf common))
        (right.prior.readings.map fun reading => absoluteRule5ReadingAt
          input.moleculeGraph descriptorMap (input.topUnit center) rightStages.graph W D
          (reading.reference?.map senseOf) (senseOf common)) := tiedMap
    _ = _ := by simp only [List.compare_eq_compareLex, List.map_map, Function.comp_def]

end
end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actual_ruleMajor_compound_rule5Readings_compare
