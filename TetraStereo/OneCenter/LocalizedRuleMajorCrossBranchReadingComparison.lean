import TetraStereo.OneCenter.LocalizedRuleMajorBranchStages
import TetraStereo.OneCenter.LocalizedRuleMajorActualCompleteReadingComparison
import TetraStereo.OneCenter.LocalizedRuleMajorNoReferenceCompleteComparison
import TetraStereo.OneCenter.LocalizedRuleMajorCompleteReadingPrefix
import TetraStereo.OneCenter.LocalizedRuleMajorCompleteReadingOrder
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual stage comparisons across ligand branches. A tie of the original Rule-4a key, together
with the proved successful-builder prefix relations, derives all earlier-column ties needed by
the Rule-4b, Rule-4c, and no-reference molecular-reading bridges. -/

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree DeclarativeCIP
open Rule4cObservationBridge OfficialSparseCanonicalVectorComparison
noncomputable section

private structure CrossBranchTies {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {leftIndex rightIndex : Fin 4}
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1)}
    (leftStages : input.RuleMajorBranchStages center leftIndex descriptorMap target)
    (rightStages : input.RuleMajorBranchStages center rightIndex descriptorMap target)
    (leftReference rightReference : RS) where
  bRule1a : (leftStages.b leftReference).key.constitutional.rule1a =
    (rightStages.b rightReference).key.constitutional.rule1a
  bScalar4a : scalar4a (leftStages.b leftReference).key = scalar4a (rightStages.b rightReference).key
  cRule1a : (leftStages.c leftReference).key.constitutional.rule1a =
    (rightStages.c rightReference).key.constitutional.rule1a
  cScalar4a : scalar4a (leftStages.c leftReference).key = scalar4a (rightStages.c rightReference).key
  bToCScalar4bLeft : scalar4b (leftStages.b leftReference).key =
    scalar4b (leftStages.c leftReference).key
  bToCScalar4bRight : scalar4b (rightStages.b rightReference).key =
    scalar4b (rightStages.c rightReference).key
  noReferenceRule1a : leftStages.noReference.key.constitutional.rule1a =
    rightStages.noReference.key.constitutional.rule1a
  noReferenceScalar4a : scalar4a leftStages.noReference.key = scalar4a rightStages.noReference.key

private theorem crossBranch_ties {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {leftIndex rightIndex : Fin 4}
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1)}
    (leftStages : input.RuleMajorBranchStages center leftIndex descriptorMap target)
    (rightStages : input.RuleMajorBranchStages center rightIndex descriptorMap target)
    (leftReference rightReference : RS)
    (aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq) :
    CrossBranchTies leftStages rightStages leftReference rightReference := by
  let read := input.molecularReader descriptorMap target
  let fuel := 2 * (input.certified.input.molecule.atomCount + 1 + 1)
  let cursorL := input.localizedLigandRootCursor center leftIndex
  let cursorR := input.localizedLigandRootCursor center rightIndex
  have observableEq :=
    (input.compareLocalizedRerootCumulativeRule45Keys_eq_iff_observable_eq
      leftStages.a.key rightStages.a.key).mp aTie
  have aRule1a : leftStages.a.key.constitutional.rule1a =
      rightStages.a.key.constitutional.rule1a := by
    have h := congrArg LocalizedCumulativeRule45Observable.rule1a observableEq
    simpa only [localizedRerootCumulativeRule45Observable] using h
  have aDescriptor : leftStages.a.key.descriptor = rightStages.a.key.descriptor := by
    have h := congrArg LocalizedCumulativeRule45Observable.descriptor observableEq
    simpa only [localizedRerootCumulativeRule45Observable] using h
  have aScalar4a : scalar4a leftStages.a.key = scalar4a rightStages.a.key := by
    unfold scalar4a
    rw [aDescriptor]
  have abL := input.buildRuleMajorCumulativeWithRead_rule4a_rule4b_prefix
    leftReference read fuel cursorL leftStages.a.key (leftStages.b leftReference).key
    leftStages.a.built (leftStages.b leftReference).built
  have abR := input.buildRuleMajorCumulativeWithRead_rule4a_rule4b_prefix
    rightReference read fuel cursorR rightStages.a.key (rightStages.b rightReference).key
    rightStages.a.built (rightStages.b rightReference).built
  have abL1 : leftStages.a.key.constitutional.rule1a =
      (leftStages.b leftReference).key.constitutional.rule1a := by
    exact congrArg RuleMajorPrefixObservable.rule1a abL
  have abR1 : rightStages.a.key.constitutional.rule1a =
      (rightStages.b rightReference).key.constitutional.rule1a := by
    exact congrArg RuleMajorPrefixObservable.rule1a abR
  have abL4a := input.ruleMajorPrefix_one_scalar4a abL
  have abR4a := input.ruleMajorPrefix_one_scalar4a abR
  have bcL := input.buildRuleMajorCumulativeWithRead_rule4b_rule4c_prefix
    leftReference read fuel cursorL (leftStages.b leftReference).key (leftStages.c leftReference).key
    (leftStages.b leftReference).built (leftStages.c leftReference).built
  have bcR := input.buildRuleMajorCumulativeWithRead_rule4b_rule4c_prefix
    rightReference read fuel cursorR (rightStages.b rightReference).key (rightStages.c rightReference).key
    (rightStages.b rightReference).built (rightStages.c rightReference).built
  have bcL1 : (leftStages.b leftReference).key.constitutional.rule1a =
      (leftStages.c leftReference).key.constitutional.rule1a :=
    congrArg RuleMajorPrefixObservable.rule1a bcL
  have bcR1 : (rightStages.b rightReference).key.constitutional.rule1a =
      (rightStages.c rightReference).key.constitutional.rule1a :=
    congrArg RuleMajorPrefixObservable.rule1a bcR
  have bcLScalars := input.ruleMajorPrefix_two_scalars bcL
  have bcRScalars := input.ruleMajorPrefix_two_scalars bcR
  have anL := input.buildRuleMajorCumulativeWithRead_rule4a_rule4cNoReference_prefix
    read fuel cursorL leftStages.a.key leftStages.noReference.key
    leftStages.a.built leftStages.noReference.built
  have anR := input.buildRuleMajorCumulativeWithRead_rule4a_rule4cNoReference_prefix
    read fuel cursorR rightStages.a.key rightStages.noReference.key
    rightStages.a.built rightStages.noReference.built
  have anL1 : leftStages.a.key.constitutional.rule1a =
      leftStages.noReference.key.constitutional.rule1a :=
    congrArg RuleMajorPrefixObservable.rule1a anL
  have anR1 : rightStages.a.key.constitutional.rule1a =
      rightStages.noReference.key.constitutional.rule1a :=
    congrArg RuleMajorPrefixObservable.rule1a anR
  have anL4a := input.ruleMajorPrefix_one_scalar4a anL
  have anR4a := input.ruleMajorPrefix_one_scalar4a anR
  exact {
    bRule1a := abL1.symm.trans (aRule1a.trans abR1)
    bScalar4a := abL4a.symm.trans (aScalar4a.trans abR4a)
    cRule1a := bcL1.symm.trans
      ((abL1.symm.trans (aRule1a.trans abR1)).trans bcR1)
    cScalar4a := bcLScalars.1.symm.trans
      ((abL4a.symm.trans (aScalar4a.trans abR4a)).trans bcRScalars.1)
    bToCScalar4bLeft := bcLScalars.2
    bToCScalar4bRight := bcRScalars.2
    noReferenceRule1a := anL1.symm.trans (aRule1a.trans anR1)
    noReferenceScalar4a := anL4a.symm.trans (aScalar4a.trans anR4a)
  }

private theorem compareNatLayers_eq_of_tie {left right : List (List (OfficialSparseEntry Nat))}
    (tie : left = right) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat left right = .eq := by
  rw [tie]
  exact CompilerProjectionFidelity.compareSparseLayers_self OfficialRuleMajorKey.compareNat
    CompilerProjectionFidelity.compareNat_self _

private theorem graph_faithful_of_a {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {index : Fin 4}
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1)}
    (stages : input.RuleMajorBranchStages center index descriptorMap target) :
    stages.graph.FaithfulExactExpansion input.moleculeGraph center.1
      (input.canonicalLigandAtom center index) := stages.a.faithful

variable {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
  {leftIndex rightIndex : Fin 4}
  (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
  (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
  (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
  (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic)
  (leftStages : input.RuleMajorBranchStages center leftIndex descriptorMap target)
  (rightStages : input.RuleMajorBranchStages center rightIndex descriptorMap target)

include tetrahedral targetRoot targetAddress singleBonded acyclic leftStages rightStages

/-- Across actual branches, the selected Rule-4b descriptor comparator is the independent
first field of the complete molecular reading. The only premise is the actual `.rule4a` key tie. -/
theorem crossBranch_selectedB_completeReading_compare (leftReference rightReference : RS)
    (aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq)
    {W D : Nat} (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
    (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (leftStages.b leftReference).key.descriptor (rightStages.b rightReference).key.descriptor =
      compare
        (ofLex (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          leftStages.graph W D (some (senseOf leftReference))).1)
        (ofLex (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          rightStages.graph W D (some (senseOf rightReference))).1) := by
  let ties := crossBranch_ties leftStages rightStages leftReference rightReference aTie
  have tied1a := compareNatLayers_eq_of_tie ties.bRule1a
  have tied4a := compareNatLayers_eq_of_tie ties.bScalar4a
  have readCompare := actual_ruleMajor_scalar4b_compare descriptorMap tetrahedral target
    targetRoot targetAddress singleBonded acyclic
    (leftStages.b leftReference) (rightStages.b rightReference) leftStages.graph rightStages.graph
    (graph_faithful_of_a leftStages) (graph_faithful_of_a rightStages)
    (le_trans (leftStages.b_width_le leftReference) leftWidth)
    (le_trans (leftStages.b_depth_le leftReference) leftDepth)
    (le_trans (rightStages.b_width_le rightReference) rightWidth)
    (le_trans (rightStages.b_depth_le rightReference) rightDepth) tied1a tied4a
  rw [compare_descriptor_eq_scalar4b_of_scalar4a_eq
    (leftStages.b leftReference).tableMatch (rightStages.b rightReference).tableMatch ties.bScalar4a]
  simpa [DeclarativeCIP.completeReadingAt] using readCompare

/-- Across actual branches, the selected Rule-4c comparator is the independent second field
when the corresponding selected Rule-4b descriptor comparison ties. -/
theorem crossBranch_selectedC_completeReading_compare (leftReference rightReference : RS)
    (aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq)
    (selectedBTie : OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      (leftStages.b leftReference).key.descriptor (rightStages.b rightReference).key.descriptor = .eq)
    {W D : Nat} (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
    (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (leftStages.c leftReference).key.descriptor (rightStages.c rightReference).key.descriptor =
      compare
        (ofLex (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          leftStages.graph W D (some (senseOf leftReference))).2)
        (ofLex (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          rightStages.graph W D (some (senseOf rightReference))).2) := by
  let ties := crossBranch_ties leftStages rightStages leftReference rightReference aTie
  have scalarBTie : scalar4b (leftStages.b leftReference).key =
      scalar4b (rightStages.b rightReference).key := by
    have cmpEq := (compare_descriptor_eq_scalar4b_of_scalar4a_eq
      (leftStages.b leftReference).tableMatch (rightStages.b rightReference).tableMatch ties.bScalar4a).symm
    rw [selectedBTie] at cmpEq
    exact (compareSparseLayers_compareNat_eq_iff _ _).mp cmpEq
  have scalarCTie : scalar4b (leftStages.c leftReference).key =
      scalar4b (rightStages.c rightReference).key :=
    ties.bToCScalar4bLeft.symm.trans (scalarBTie.trans ties.bToCScalar4bRight)
  have readCompare := actual_ruleMajor_scalar4c_compare descriptorMap tetrahedral target
    targetRoot targetAddress singleBonded acyclic
    (leftStages.c leftReference) (rightStages.c rightReference) leftStages.graph rightStages.graph
    (graph_faithful_of_a leftStages) (graph_faithful_of_a rightStages)
    (le_trans (leftStages.c_width_le leftReference) leftWidth)
    (le_trans (leftStages.c_depth_le leftReference) leftDepth)
    (le_trans (rightStages.c_width_le rightReference) rightWidth)
    (le_trans (rightStages.c_depth_le rightReference) rightDepth)
    (compareNatLayers_eq_of_tie ties.cRule1a) (compareNatLayers_eq_of_tie ties.cScalar4a)
  rw [compare_descriptor_eq_scalar4c_of_prior_columns_eq
    (leftStages.c leftReference).tableMatch (rightStages.c rightReference).tableMatch
    ties.cScalar4a scalarCTie]
  exact readCompare

/-- Across actual branches, the no-reference Rule-4c descriptor comparison is the independent
second field even when lowercase `r/s` annotations occur. -/
theorem crossBranch_noReference_completeReading_compare
    (aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq)
    {W D : Nat} (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
    (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        leftStages.noReference.key.descriptor rightStages.noReference.key.descriptor =
      compare
        (ofLex (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          leftStages.graph W D none)).2
        (ofLex (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          rightStages.graph W D none)).2 := by
  let ties := crossBranch_ties leftStages rightStages .R .R aTie
  exact actual_ruleMajor_noReference_completeReading_compare descriptorMap tetrahedral target
    targetRoot targetAddress singleBonded acyclic leftStages.noReference rightStages.noReference
    leftStages.graph rightStages.graph (graph_faithful_of_a leftStages)
    (graph_faithful_of_a rightStages)
    (le_trans leftStages.noReference_width_le leftWidth)
    (le_trans leftStages.noReference_depth_le leftDepth)
    (le_trans rightStages.noReference_width_le rightWidth)
    (le_trans rightStages.noReference_depth_le rightDepth)
    (compareNatLayers_eq_of_tie ties.noReferenceRule1a)
    (compareNatLayers_eq_of_tie ties.noReferenceScalar4a)

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.crossBranch_selectedB_completeReading_compare
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.crossBranch_selectedC_completeReading_compare
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.crossBranch_noReference_completeReading_compare
