import TetraStereo.OneCenter.LocalizedRuleMajorRule5Observation
import TetraStereo.OneCenter.LocalizedRuleMajorBranchStages
import TetraStereo.OneCenter.LocalizedRuleMajorActualCompleteReadingComparison
import TetraStereo.OneCenter.LocalizedRuleMajorCompleteReadingPrefix
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput.RuleMajorBranchStages
open Rule4aTableBridge
noncomputable section

variable {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
  {descriptorMap : DeclarativeCIP.DescriptorMap (DeclarativeCIP.DetectedOccurrence input.moleculeGraph)}
  {target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1)}
  (stages : input.RuleMajorBranchStages center index descriptorMap target)

theorem b_encoded4b_eq_c (reference : RS) (path : List Nat) :
    encoded4b (stages.b reference).key path = encoded4b (stages.c reference).key path := by
  have preserved := input.buildRuleMajorCumulativeWithRead_rule4b_rule4c_prefix reference
    (input.molecularReader descriptorMap target) _ _ _ _
    (stages.b reference).built (stages.c reference).built
  have rule1a : (stages.b reference).key.constitutional.rule1a =
      (stages.c reference).key.constitutional.rule1a :=
    congrArg RuleMajorPrefixObservable.rule1a preserved
  have columns := input.ruleMajorPrefix_two_scalars preserved
  unfold encoded4b
  rw [rule1a, columns.1, columns.2]

theorem c_rule1a_eq_a (reference : RS) :
    (stages.c reference).key.constitutional.rule1a = stages.a.key.constitutional.rule1a := by
  have ab := input.buildRuleMajorCumulativeWithRead_rule4a_rule4b_prefix reference
    (input.molecularReader descriptorMap target) _ _ _ _ stages.a.built (stages.b reference).built
  have bc := input.buildRuleMajorCumulativeWithRead_rule4b_rule4c_prefix reference
    (input.molecularReader descriptorMap target) _ _ _ _
    (stages.b reference).built (stages.c reference).built
  have abRule : stages.a.key.constitutional.rule1a =
      (stages.b reference).key.constitutional.rule1a := congrArg RuleMajorPrefixObservable.rule1a ab
  have bcRule : (stages.b reference).key.constitutional.rule1a =
      (stages.c reference).key.constitutional.rule1a := congrArg RuleMajorPrefixObservable.rule1a bc
  exact (abRule.trans bcRule).symm

end
end CertifiedLocalizedCIPInput.RuleMajorBranchStages

namespace Rule5ObservationBridge
open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree DeclarativeCIP
open Rule4aTableBridge Rule4cObservationBridge OfficialSparseCanonicalVectorComparison
open SparsePhysicalFirstDifference SparseSupportAlignment
noncomputable section

variable {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
  {index leftIndex rightIndex : Fin 4}
  (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
  (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
  (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
  (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic)

include tetrahedral targetRoot targetAddress singleBonded acyclic

/-- The independently decoded absolute reading represents the actual appended Rule-5 column
on the separately rebuilt Rule-4c arm. Its B observation is transported by the proved prefix. -/
theorem selectedRule5_represents
    (stages : input.RuleMajorBranchStages center index descriptorMap target)
    (reference common : RS) {W D : Nat}
    (width : stages.widthBound ≤ W) (depth : stages.depthBound ≤ D) :
    ∀ path, Certificate.CanonicalSphereKey.pathObservationOf W D
      (absoluteRule5ReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
        stages.graph W D (some (senseOf reference)) (senseOf common)) path =
      bitObservable (common == reference) (stages.c reference).key path := by
  have represented := ruleMajor_reading_represents_every_faithful descriptorMap tetrahedral
    target targetRoot targetAddress singleBonded acyclic (stages.b reference) stages.graph
    stages.a.faithful ((stages.b_width_le reference).trans width)
    ((stages.b_depth_le reference).trans depth)
  intro path
  simp only [absoluteRule5ReadingAt, pathObservationOf_mapObservationKey]
  rw [represented path, stages.b_encoded4b_eq_c reference path]
  exact absolute_encoded4b (stages.c reference).tableMatch common path

/-- At a complete prior-table tie, two selected readings compare by their independently
decoded absolute descriptor stream. Selected references may differ; lowercase data remains. -/
theorem crossBranch_selected_rule5_compare
    (leftStages : input.RuleMajorBranchStages center leftIndex descriptorMap target)
    (rightStages : input.RuleMajorBranchStages center rightIndex descriptorMap target)
    (leftReference rightReference common : RS) {W D : Nat}
    (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
    (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D)
    (aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq)
    (cTie : OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      (leftStages.c leftReference).key.descriptor (rightStages.c rightReference).key.descriptor = .eq) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (input.rule5LiftKey (common == leftReference) (leftStages.c leftReference).key).descriptor
        (input.rule5LiftKey (common == rightReference) (rightStages.c rightReference).key).descriptor =
      compare
        (absoluteRule5ReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          leftStages.graph W D (some (senseOf leftReference)) (senseOf common))
        (absoluteRule5ReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          rightStages.graph W D (some (senseOf rightReference)) (senseOf common)) := by
  have cEq := (compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff _ _).mp cTie
  rw [compare_lifts_eq_bits _ _ _ _ cEq]
  have aObservable := (input.compareLocalizedRerootCumulativeRule45Keys_eq_iff_observable_eq
    leftStages.a.key rightStages.a.key).mp aTie
  have aRule1a := congrArg LocalizedCumulativeRule45Observable.rule1a aObservable
  have rule1aEq : (leftStages.c leftReference).key.constitutional.rule1a =
      (rightStages.c rightReference).key.constitutional.rule1a := by
    rw [leftStages.c_rule1a_eq_a leftReference, rightStages.c_rule1a_eq_a rightReference]
    exact aRule1a
  have rule1aTie := (compareSparseLayers_compareNat_eq_iff _ _).mpr rule1aEq
  have shapedL := mapObservationKey_wellShaped (absoluteRule5Label (senseOf leftReference) (senseOf common))
    (ordinaryKey_stereo_wellShaped input.moleculeGraph leftStages.graph
      (readingEvidence input.moleculeGraph descriptorMap (input.topUnit center)
        leftStages.graph (senseOf leftReference)) W D
      .rule4bLikeUnlikeDescriptorPairs leftStages.graph.root)
  have shapedR := mapObservationKey_wellShaped (absoluteRule5Label (senseOf rightReference) (senseOf common))
    (ordinaryKey_stereo_wellShaped input.moleculeGraph rightStages.graph
      (readingEvidence input.moleculeGraph descriptorMap (input.topUnit center)
        rightStages.graph (senseOf rightReference)) W D
      .rule4bLikeUnlikeDescriptorPairs rightStages.graph.root)
  exact compare_of_pathFirstDifference shapedL shapedR
    (selectedRule5_represents descriptorMap tetrahedral target targetRoot targetAddress
      singleBonded acyclic leftStages leftReference common leftWidth leftDepth)
    (selectedRule5_represents descriptorMap tetrahedral target targetRoot targetAddress
      singleBonded acyclic rightStages rightReference common rightWidth rightDepth)
    (fun outcome => bitTable_pathFirstDifference_iff
      (leftStages.c leftReference).tableMatch (rightStages.c rightReference).tableMatch
      (leftStages.c leftReference).realizes (rightStages.c rightReference).realizes
      common rule1aTie outcome)

end
end Rule5ObservationBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorBranchStages.b_encoded4b_eq_c
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorBranchStages.c_rule1a_eq_a
assert_kernel_only TetraStereo.OneCenter.Rule5ObservationBridge.selectedRule5_represents
assert_kernel_only TetraStereo.OneCenter.Rule5ObservationBridge.crossBranch_selected_rule5_compare
