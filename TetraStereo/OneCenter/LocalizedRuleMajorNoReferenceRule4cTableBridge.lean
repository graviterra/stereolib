import TetraStereo.OneCenter.LocalizedRuleMajorRule4cTableBridge
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Comparison of actual no-reference Rule-4c stage tables. Empty uppercase reference
selection does not imply absence of lowercase labels. The two-column stage compares the whole
kind table before the complete pseudoasymmetric observation, including both r and s. -/

namespace TetraStereo.OneCenter.Rule4cObservationBridge
open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree
open Rule4aTableBridge DeclarativeCIP OfficialSparseCanonicalVectorComparison
noncomputable section
open scoped Classical

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
  {key : input.LocalizedRerootCumulativeRule45Key} {stage : LocalizedCumulativeRule45Stage}

theorem scalar4a_eq_table_anyStage (matched : LocalizedCumulativeTreeTableMatch stage tree key) :
    scalar4a key = table prio4a tree := by
  unfold scalar4a
  rw [← matched.2.2.2, tables_descriptor, table_map]
  cases stage <;> rfl

theorem rule4bTableView_matches_anyStage (reference : RS)
    (matched : LocalizedCumulativeTreeTableMatch stage tree key) :
    LocalizedCumulativeTreeTableMatch (.rule4b reference) tree
      (rule4bTableView reference tree key) :=
  ⟨matched.1, matched.2.1, matched.2.2.1, rfl⟩

theorem scalar4a_rule4bTableView_anyStage (reference : RS)
    (matched : LocalizedCumulativeTreeTableMatch stage tree key) :
    scalar4a (rule4bTableView reference tree key) = scalar4a key := by
  rw [scalar4a_eq_table_rule4b (rule4bTableView_matches_anyStage reference matched),
    scalar4a_eq_table_anyStage matched]

theorem encoded4a_rule4bTableView_anyStage (reference : RS)
    (matched : LocalizedCumulativeTreeTableMatch stage tree key) (path : List Nat) :
    encoded4a (rule4bTableView reference tree key) path = encoded4a key path := by
  unfold encoded4a
  rw [scalar4a_rule4bTableView_anyStage reference matched]
  rfl

theorem rule4a_pathFirstDifference_iff_anyStage
    {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    {stageL stageR : LocalizedCumulativeRule45Stage}
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (matchL : LocalizedCumulativeTreeTableMatch stageL treeL keyL)
    (matchR : LocalizedCumulativeTreeTableMatch stageR treeR keyR)
    (realizesL : LocalizedCumulativeTreeRealizes input readL treeL)
    (realizesR : LocalizedCumulativeTreeRealizes input readR treeR)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      keyL.constitutional.rule1a keyR.constitutional.rule1a = .eq) (outcome : Ordering) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4a keyL) (scalar4a keyR) = outcome ↔
      PathFirstDifferenceOf (encoded4a keyL) (encoded4a keyR) outcome := by
  have result := rule4a_pathFirstDifference_iff_rule4b
    (rule4bTableView_matches_anyStage .R matchL) (rule4bTableView_matches_anyStage .R matchR)
    realizesL realizesR tied outcome
  have encL : encoded4a (rule4bTableView .R treeL keyL) = encoded4a keyL :=
    funext (encoded4a_rule4bTableView_anyStage .R matchL)
  have encR : encoded4a (rule4bTableView .R treeR keyR) = encoded4a keyR :=
    funext (encoded4a_rule4bTableView_anyStage .R matchR)
  rw [scalar4a_rule4bTableView_anyStage .R matchL,
    scalar4a_rule4bTableView_anyStage .R matchR, encL, encR] at result
  exact result

/-- In the no-reference stage, the second column is Rule 4c, not Rule 4b. -/
theorem scalar4b_noReference_eq_rule4cTable
    (matched : LocalizedCumulativeTreeTableMatch .rule4cNoReference tree key) :
    scalar4b key = table (fun node => localizedRule4cPriority node.label) tree := by
  unfold scalar4b
  rw [← matched.2.2.2, tables_descriptor, table_map]
  rfl

theorem compareNoReferenceScalar4c_eq_pseudoValueOfLabels
    {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    (matchL : LocalizedCumulativeTreeTableMatch .rule4cNoReference treeL keyL)
    (matchR : LocalizedCumulativeTreeTableMatch .rule4cNoReference treeR keyR)
    (labelsL : LocalizedCumulativeTreeLabelMatch treeL keyL)
    (labelsR : LocalizedCumulativeTreeLabelMatch treeR keyR)
    (priorTie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4a keyL) (scalar4a keyR) = .eq) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4b keyL) (scalar4b keyR) =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (mapLabelTable pseudoValueOfLabel keyL.labels)
        (mapLabelTable pseudoValueOfLabel keyR.labels) := by
  have kindEq := (compareSparseLayers_compareNat_eq_iff _ _).1 priorTie
  have kindL : mapLabelTable localizedRule4aPriority keyL.labels = scalar4a keyL := by
    rw [← labelsL, mapLabelTable_labelTable, scalar4a_eq_table_anyStage matchL]
    rfl
  have kindR : mapLabelTable localizedRule4aPriority keyR.labels = scalar4a keyR := by
    rw [← labelsR, mapLabelTable_labelTable, scalar4a_eq_table_anyStage matchR]
    rfl
  have runtimeL : mapLabelTable localizedRule4cPriority keyL.labels = scalar4b keyL := by
    rw [← labelsL, mapLabelTable_labelTable, scalar4b_noReference_eq_rule4cTable matchL]
  have runtimeR : mapLabelTable localizedRule4cPriority keyR.labels = scalar4b keyR := by
    rw [← labelsR, mapLabelTable_labelTable, scalar4b_noReference_eq_rule4cTable matchR]
  rw [← runtimeL, ← runtimeR]
  apply compareRule4cTables_eq_pseudoValueTables_of_kindTables_eq
  rw [kindL, kindR, kindEq]

theorem noReference4c_pathFirstDifference_iff
    {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (matchL : LocalizedCumulativeTreeTableMatch .rule4cNoReference treeL keyL)
    (matchR : LocalizedCumulativeTreeTableMatch .rule4cNoReference treeR keyR)
    (labelsL : LocalizedCumulativeTreeLabelMatch treeL keyL)
    (labelsR : LocalizedCumulativeTreeLabelMatch treeR keyR)
    (realizesL : LocalizedCumulativeTreeRealizes input readL treeL)
    (realizesR : LocalizedCumulativeTreeRealizes input readR treeR)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      keyL.constitutional.rule1a keyR.constitutional.rule1a = .eq)
    (tied4a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4a keyL) (scalar4a keyR) = .eq) (outcome : Ordering) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4b keyL) (scalar4b keyR) = outcome ↔
      PathFirstDifferenceOf (encodedPseudo4c keyL) (encodedPseudo4c keyR) outcome := by
  rw [compareNoReferenceScalar4c_eq_pseudoValueOfLabels matchL matchR labelsL labelsR tied4a]
  exact pseudoTable_pathFirstDifference_iff matchL matchR labelsL labelsR realizesL realizesR tied outcome

theorem compareRuleMajor_noReference4c_eq_then
    {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (matchL : LocalizedCumulativeTreeTableMatch .rule4cNoReference treeL keyL)
    (matchR : LocalizedCumulativeTreeTableMatch .rule4cNoReference treeR keyR)
    (labelsL : LocalizedCumulativeTreeLabelMatch treeL keyL)
    (labelsR : LocalizedCumulativeTreeLabelMatch treeR keyR)
    (realizesL : LocalizedCumulativeTreeRealizes input readL treeL)
    (realizesR : LocalizedCumulativeTreeRealizes input readR treeR)
    {W D : Nat} {graphL graphR : RootedDigraph input.Atom}
    {nodeL : graphL.Node} {nodeR : graphR.Node}
    (repCL : Represents W D (ruleKey input.moleculeGraph graphL W D nodeL) keyL.constitutional)
    (repCR : Represents W D (ruleKey input.moleculeGraph graphR W D nodeR) keyR.constitutional)
    {KaL KaR KcL KcR : Certificate.CanonicalSphereKey.Key StereoLabel}
    (shapeAL : Certificate.CanonicalSphereKey.WellShaped W D KaL)
    (shapeAR : Certificate.CanonicalSphereKey.WellShaped W D KaR)
    (shapeCL : Certificate.CanonicalSphereKey.WellShaped W D KcL)
    (shapeCR : Certificate.CanonicalSphereKey.WellShaped W D KcR)
    (repAL : Represents4a W D KaL keyL) (repAR : Represents4a W D KaR keyR)
    (rep4cL : Represents4c W D KcL keyL) (rep4cR : Represents4c W D KcR keyR) :
    input.compareRuleMajorCumulativeDescriptor 2 keyL keyR =
      (compare (ruleKey input.moleculeGraph graphL W D nodeL)
        (ruleKey input.moleculeGraph graphR W D nodeR)).then
        ((compare KaL KaR).then (compare KcL KcR)) := by
  have wfL := wellFormedRuleMajorKey_of_tableMatch matchL realizesL
  have wfR := wellFormedRuleMajorKey_of_tableMatch matchR realizesR
  have constitution : OfficialRuleMajorKey.compare keyL.constitutional keyR.constitutional =
      compare (ruleKey input.moleculeGraph graphL W D nodeL)
        (ruleKey input.moleculeGraph graphR W D nodeR) :=
    compare_eq_compare_vector wfL wfR
      (ruleKey_vectorWellShaped input.moleculeGraph graphL W D nodeL)
      (ruleKey_vectorWellShaped input.moleculeGraph graphR W D nodeR) repCL repCR
  rw [compareRuleMajor_two, constitution]
  cases hc : compare (ruleKey input.moleculeGraph graphL W D nodeL)
      (ruleKey input.moleculeGraph graphR W D nodeR) with
  | lt => rfl
  | gt => rfl
  | eq =>
      simp only [Ordering.then]
      have tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          keyL.constitutional.rule1a keyR.constitutional.rule1a = .eq := by
        have h := constitution.trans hc
        unfold OfficialRuleMajorKey.compare at h
        exact (compareLex_eq_eq.1 h).1
      have earlier : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          (scalar4a keyL) (scalar4a keyR) = compare KaL KaR :=
        compare_of_pathFirstDifference shapeAL shapeAR repAL repAR
          (rule4a_pathFirstDifference_iff_anyStage matchL matchR realizesL realizesR tied)
      rw [earlier]
      cases ha : compare KaL KaR with
      | lt => rfl
      | gt => rfl
      | eq =>
          exact compare_of_pathFirstDifference shapeCL shapeCR rep4cL rep4cR
            (noReference4c_pathFirstDifference_iff matchL matchR labelsL labelsR
              realizesL realizesR tied (earlier.trans ha))

theorem rule4acKey_le_of_compare_ne_lt
    {graph : RootedDigraph input.Atom} (evidence : StereochemicalEvidence graph)
    {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (matchL : LocalizedCumulativeTreeTableMatch .rule4cNoReference treeL keyL)
    (matchR : LocalizedCumulativeTreeTableMatch .rule4cNoReference treeR keyR)
    (labelsL : LocalizedCumulativeTreeLabelMatch treeL keyL)
    (labelsR : LocalizedCumulativeTreeLabelMatch treeR keyR)
    (realizesL : LocalizedCumulativeTreeRealizes input readL treeL)
    (realizesR : LocalizedCumulativeTreeRealizes input readR treeR)
    {W D : Nat} {nodeL nodeR : graph.Node}
    (repCL : Represents W D (ruleKey input.moleculeGraph graph W D nodeL) keyL.constitutional)
    (repCR : Represents W D (ruleKey input.moleculeGraph graph W D nodeR) keyR.constitutional)
    (repAL : Represents4a W D (rule4aComponent input.moleculeGraph graph evidence W D nodeL) keyL)
    (repAR : Represents4a W D (rule4aComponent input.moleculeGraph graph evidence W D nodeR) keyR)
    (rep4cL : Represents4c W D (rule4cComponent input.moleculeGraph graph evidence W D nodeL) keyL)
    (rep4cR : Represents4c W D (rule4cComponent input.moleculeGraph graph evidence W D nodeR) keyR)
    (descending : input.compareRuleMajorCumulativeDescriptor 2 keyL keyR ≠ .lt) :
    rule4acKey input.moleculeGraph graph evidence W D nodeR ≤
      rule4acKey input.moleculeGraph graph evidence W D nodeL := by
  rw [compareRuleMajor_noReference4c_eq_then matchL matchR labelsL labelsR realizesL realizesR
    repCL repCR
    (ordinaryKey_stereo_wellShaped input.moleculeGraph graph evidence W D _ nodeL)
    (ordinaryKey_stereo_wellShaped input.moleculeGraph graph evidence W D _ nodeR)
    (ordinaryKey_stereo_wellShaped input.moleculeGraph graph evidence W D _ nodeL)
    (ordinaryKey_stereo_wellShaped input.moleculeGraph graph evidence W D _ nodeR)
    repAL repAR rep4cL rep4cR] at descending
  exact lex_le_of_then_ne_lt _ _ _ vectorCompare_eq_iff Rule4aTableBridge.vectorCompare_gt_iff
    stereoKeyCompare_eq_iff stereoKeyCompare_gt_iff stereoKeyCompare_eq_iff
    stereoKeyCompare_gt_iff descending

end
end TetraStereo.OneCenter.Rule4cObservationBridge

assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.scalar4a_eq_table_anyStage
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.rule4bTableView_matches_anyStage
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.scalar4a_rule4bTableView_anyStage
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.encoded4a_rule4bTableView_anyStage
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.rule4a_pathFirstDifference_iff_anyStage
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.scalar4b_noReference_eq_rule4cTable
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.compareNoReferenceScalar4c_eq_pseudoValueOfLabels
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.noReference4c_pathFirstDifference_iff
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.compareRuleMajor_noReference4c_eq_then
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.rule4acKey_le_of_compare_ne_lt
