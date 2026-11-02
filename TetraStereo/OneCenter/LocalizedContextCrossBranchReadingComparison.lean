import TetraStereo.OneCenter.LocalizedContextBranchStages
import TetraStereo.OneCenter.LocalizedContextCompleteReadingOrder
import TetraStereo.OneCenter.LocalizedRuleMajorCompleteReadingPrefix
import TetraStereo.OneCenter.LocalizedRuleMajorCompleteReadingOrder
import TetraStereo.OneCenter.LocalizedRuleMajorNoReferenceCompleteComparison
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual prefix preservation and independent reading comparisons across two contextual stage
families. Earlier-column agreements follow from the actual stage-4a comparison; the selected
Rule-4b and Rule-4c comparisons and the genuine no-reference Rule-4c comparison then agree with
their independent observations on the original stage-4a graphs. The two arms may use different
reference senses, and no-reference observations retain their genuine pseudoasymmetric component. -/

namespace TetraStereo.OneCenter.Rule4aTableBridge
open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree DeclarativeCIP
open Rule4cObservationBridge OfficialSparseCanonicalVectorComparison
noncomputable section

structure ContextCrossBranchTies {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {cursorL cursorR : input.LocalizedRerootCursor carrierFuel}
    (leftStages : input.RuleMajorContextStages carrierFuel read cursorL)
    (rightStages : input.RuleMajorContextStages carrierFuel read cursorR)
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

theorem contextCrossBranch_ties {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {cursorL cursorR : input.LocalizedRerootCursor carrierFuel}
    (leftStages : input.RuleMajorContextStages carrierFuel read cursorL)
    (rightStages : input.RuleMajorContextStages carrierFuel read cursorR)
    (leftReference rightReference : RS)
    (aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq) :
    ContextCrossBranchTies leftStages rightStages leftReference rightReference := by
  let fuel := 2 * (carrierFuel + 1)
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

theorem contextCompareNatLayers_eq_of_tie {left right : List (List (OfficialSparseEntry Nat))}
    (tie : left = right) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat left right = .eq := by
  rw [tie]
  exact CompilerProjectionFidelity.compareSparseLayers_self OfficialRuleMajorKey.compareNat
    CompilerProjectionFidelity.compareNat_self _

section ReadingComparisons

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
  {cursorL cursorR : input.LocalizedRerootCursor carrierFuel}
  (singleBonded : input.moleculeGraph.SimpleBonded)
  (leftStages : input.RuleMajorContextStages carrierFuel read cursorL)
  (rightStages : input.RuleMajorContextStages carrierFuel read cursorR)
  (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (unit : DetectedOccurrence input.moleculeGraph)
  (readL : RuleMajorContextReadingReadbacks leftStages descriptorMap unit)
  (readR : RuleMajorContextReadingReadbacks rightStages descriptorMap unit)
  (isoL : RuleMajorContextStageGraphIsoBundle leftStages)
  (isoR : RuleMajorContextStageGraphIsoBundle rightStages)

include singleBonded readL readR isoL isoR

theorem contextCrossBranch_selectedB_compare (leftReference rightReference : RS)
    (aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq)
    {W D : Nat} (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
    (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (leftStages.b leftReference).key.descriptor (rightStages.b rightReference).key.descriptor =
      compare
        (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph leftStages.a.tree) W D (some (senseOf leftReference)))).1
        (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph rightStages.a.tree) W D (some (senseOf rightReference)))).1 := by
  let ties := contextCrossBranch_ties leftStages rightStages leftReference rightReference aTie
  have scalar := contextTrees_ruleMajor_scalar4b_compare singleBonded
    (leftStages.b leftReference).tree (rightStages.b rightReference).tree
    (leftStages.b leftReference).trace (rightStages.b rightReference).trace
    (readL.bReadback leftReference) (readR.bReadback rightReference)
    (readL.bObservations leftReference) (readR.bObservations rightReference)
    ((leftStages.b_width_le leftReference).trans leftWidth)
    ((leftStages.b_depth_le leftReference).trans leftDepth)
    ((rightStages.b_width_le rightReference).trans rightWidth)
    ((rightStages.b_depth_le rightReference).trans rightDepth)
    (contextCompareNatLayers_eq_of_tie ties.bRule1a)
    (contextCompareNatLayers_eq_of_tie ties.bScalar4a)
  change _ = compare
    (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph (leftStages.b leftReference).tree) W D
      (some (senseOf leftReference)))).1
    (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph (rightStages.b rightReference).tree) W D
      (some (senseOf rightReference)))).1 at scalar
  rw [contextualCompleteReadingAt_iso input.moleculeGraph descriptorMap unit
      (isoL.b leftReference), contextualCompleteReadingAt_iso input.moleculeGraph descriptorMap unit
      (isoR.b rightReference)] at scalar
  rw [compare_descriptor_eq_scalar4b_of_scalar4a_eq
    (LocalizedRuleMajorSortTrace.fullMatch_of_trace (leftStages.b leftReference).trace).tableMatch
    (LocalizedRuleMajorSortTrace.fullMatch_of_trace (rightStages.b rightReference).trace).tableMatch
    ties.bScalar4a]
  exact scalar

theorem contextCrossBranch_selectedC_compare (leftReference rightReference : RS)
    (aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq)
    (bTie : OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      (leftStages.b leftReference).key.descriptor (rightStages.b rightReference).key.descriptor = .eq)
    {W D : Nat} (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
    (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (leftStages.c leftReference).key.descriptor (rightStages.c rightReference).key.descriptor =
      compare
        (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph leftStages.a.tree) W D (some (senseOf leftReference)))).2
        (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph rightStages.a.tree) W D (some (senseOf rightReference)))).2 := by
  let ties := contextCrossBranch_ties leftStages rightStages leftReference rightReference aTie
  have scalarBTie : scalar4b (leftStages.b leftReference).key =
      scalar4b (rightStages.b rightReference).key := by
    have cmpEq := (compare_descriptor_eq_scalar4b_of_scalar4a_eq
      (LocalizedRuleMajorSortTrace.fullMatch_of_trace (leftStages.b leftReference).trace).tableMatch
      (LocalizedRuleMajorSortTrace.fullMatch_of_trace (rightStages.b rightReference).trace).tableMatch
      ties.bScalar4a).symm
    rw [bTie] at cmpEq
    exact (compareSparseLayers_compareNat_eq_iff _ _).mp cmpEq
  have scalarCTie := ties.bToCScalar4bLeft.symm.trans (scalarBTie.trans ties.bToCScalar4bRight)
  have scalar := contextTrees_ruleMajor_scalar4c_compare singleBonded
    (leftStages.c leftReference).tree (rightStages.c rightReference).tree
    (leftStages.c leftReference).trace (rightStages.c rightReference).trace
    (readL.cReadback leftReference) (readR.cReadback rightReference)
    (readL.cObservations leftReference) (readR.cObservations rightReference)
    ((leftStages.c_width_le leftReference).trans leftWidth)
    ((leftStages.c_depth_le leftReference).trans leftDepth)
    ((rightStages.c_width_le rightReference).trans rightWidth)
    ((rightStages.c_depth_le rightReference).trans rightDepth)
    (contextCompareNatLayers_eq_of_tie ties.cRule1a)
    (contextCompareNatLayers_eq_of_tie ties.cScalar4a)
  change _ = compare
    (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph (leftStages.c leftReference).tree) W D
      (some (senseOf leftReference)))).2
    (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph (rightStages.c rightReference).tree) W D
      (some (senseOf rightReference)))).2 at scalar
  rw [contextualCompleteReadingAt_iso input.moleculeGraph descriptorMap unit
      (isoL.c leftReference), contextualCompleteReadingAt_iso input.moleculeGraph descriptorMap unit
      (isoR.c rightReference)] at scalar
  rw [compare_descriptor_eq_scalar4c_of_prior_columns_eq
    (LocalizedRuleMajorSortTrace.fullMatch_of_trace (leftStages.c leftReference).trace).tableMatch
    (LocalizedRuleMajorSortTrace.fullMatch_of_trace (rightStages.c rightReference).trace).tableMatch
    ties.cScalar4a scalarCTie]
  exact scalar

theorem contextCrossBranch_noReference_compare
    (aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq)
    {W D : Nat} (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
    (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        leftStages.noReference.key.descriptor rightStages.noReference.key.descriptor =
      compare
        (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph leftStages.a.tree) W D none)).2
        (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph rightStages.a.tree) W D none)).2 := by
  let ties := contextCrossBranch_ties leftStages rightStages .R .R aTie
  have scalar := contextTrees_ruleMajor_noReference4c_compare singleBonded
    leftStages.noReference.tree rightStages.noReference.tree
    leftStages.noReference.trace rightStages.noReference.trace
    readL.noReferenceReadback readR.noReferenceReadback
    readL.noReferenceObservations readR.noReferenceObservations
    (leftStages.noReference_width_le.trans leftWidth)
    (leftStages.noReference_depth_le.trans leftDepth)
    (rightStages.noReference_width_le.trans rightWidth)
    (rightStages.noReference_depth_le.trans rightDepth)
    (contextCompareNatLayers_eq_of_tie ties.noReferenceRule1a)
    (contextCompareNatLayers_eq_of_tie ties.noReferenceScalar4a)
  change _ = compare
    (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph leftStages.noReference.tree) W D none)).2
    (ofLex (contextualCompleteReadingAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph rightStages.noReference.tree) W D none)).2 at scalar
  rw [contextualCompleteReadingAt_iso input.moleculeGraph descriptorMap unit isoL.noReference,
    contextualCompleteReadingAt_iso input.moleculeGraph descriptorMap unit isoR.noReference] at scalar
  rw [compare_descriptor_eq_scalar4b_of_prior_scalar4a_eq
    (LocalizedRuleMajorSortTrace.fullMatch_of_trace leftStages.noReference.trace).tableMatch
    (LocalizedRuleMajorSortTrace.fullMatch_of_trace rightStages.noReference.trace).tableMatch
    ties.noReferenceScalar4a]
  exact scalar

end ReadingComparisons
end
end TetraStereo.OneCenter.Rule4aTableBridge

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextCrossBranch_ties
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextCompareNatLayers_eq_of_tie
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextCrossBranch_selectedB_compare
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextCrossBranch_selectedC_compare
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextCrossBranch_noReference_compare
