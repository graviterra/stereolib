import TetraStereo.OneCenter.LocalizedRuleMajorRule4cPriorTie
import TetraStereo.OneCenter.LocalizedRuleMajorPairComparison
import TetraStereo.OneCenter.DeclarativeCIPRule4cKeyProjection
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Complete Rule-4c observation comparison, including lowercase auxiliary descriptors.
The independent encoding is read from the exact label table, not equated numerically with the
runtime's differently numbered Rule-4c column. Their orders agree after the derived earlier
Rule-4a tie. Earlier columns are transferred through a table-only Rule-4b view of the same tree;
that view does not assert that a different stage builder chose this sibling order. -/

namespace TetraStereo.OneCenter.Rule4cObservationBridge
open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree
open Rule4aTableBridge DeclarativeCIP OfficialSparseCanonicalVectorComparison
open SparsePhysicalFirstDifference SparseSupportAlignment
noncomputable section
open scoped Classical

def encodedPseudo4c {input : CertifiedLocalizedCIPInput}
    (key : input.LocalizedRerootCumulativeRule45Key) (path : List Nat) : WithBot StereoLabel :=
  if HasAddress key.constitutional.rule1a path then
    (((code (tableValue (mapLabelTable pseudoValueOfLabel key.labels) path) : StereoCode) :
      StereoLabel) : WithBot StereoLabel)
  else ⊥

def Represents4c (W D : Nat) (K : Certificate.CanonicalSphereKey.Key StereoLabel)
    {input : CertifiedLocalizedCIPInput} (key : input.LocalizedRerootCumulativeRule45Key) : Prop :=
  ∀ path, Certificate.CanonicalSphereKey.pathObservationOf W D K path = encodedPseudo4c key path

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
  {key : input.LocalizedRerootCumulativeRule45Key} {stage : LocalizedCumulativeRule45Stage}

theorem pseudoTable_eq_table (labels : LocalizedCumulativeTreeLabelMatch tree key) :
    mapLabelTable pseudoValueOfLabel key.labels =
      table (fun node => pseudoValueOfLabel node.label) tree := by
  rw [← labels, mapLabelTable_labelTable]

theorem pseudoTable_rows (matched : LocalizedCumulativeTreeTableMatch stage tree key)
    (labels : LocalizedCumulativeTreeLabelMatch tree key) :
    SameAddressRows (mapLabelTable pseudoValueOfLabel key.labels) key.constitutional.rule1a := by
  rw [pseudoTable_eq_table labels, ← matched.1, tables_rule1a]
  exact LocalizedActualTableAddressOrder.SameAddressRows_table_observations _ _ tree

theorem pseudoTable_wellFormed (labels : LocalizedCumulativeTreeLabelMatch tree key) :
    SparseTableWellFormed (mapLabelTable pseudoValueOfLabel key.labels) := by
  rw [pseudoTable_eq_table labels]
  exact LocalizedActualTableAddressOrder.table_wellFormed _ tree

theorem pseudoTable_pathFirstDifference_iff
    {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    {stageL stageR : LocalizedCumulativeRule45Stage}
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (matchL : LocalizedCumulativeTreeTableMatch stageL treeL keyL)
    (matchR : LocalizedCumulativeTreeTableMatch stageR treeR keyR)
    (labelsL : LocalizedCumulativeTreeLabelMatch treeL keyL)
    (labelsR : LocalizedCumulativeTreeLabelMatch treeR keyR)
    (realizesL : LocalizedCumulativeTreeRealizes input readL treeL)
    (realizesR : LocalizedCumulativeTreeRealizes input readR treeR)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      keyL.constitutional.rule1a keyR.constitutional.rule1a = .eq) (outcome : Ordering) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (mapLabelTable pseudoValueOfLabel keyL.labels)
        (mapLabelTable pseudoValueOfLabel keyR.labels) = outcome ↔
      PathFirstDifferenceOf (encodedPseudo4c keyL) (encodedPseudo4c keyR) outcome := by
  have wfL := wellFormedRuleMajorKey_of_tableMatch matchL realizesL
  have wfR := wellFormedRuleMajorKey_of_tableMatch matchR realizesR
  have support : ∀ path, HasAddress keyL.constitutional.rule1a path ↔
      HasAddress keyR.constitutional.rule1a path := sameSupport_of_compareSparseLayers_eq
    wfL.wellFormed1a wfR.wellFormed1a wfL.positive1a wfR.positive1a tied
  have pointwise : ∀ path, compare (encodedPseudo4c keyL path) (encodedPseudo4c keyR path) =
      OfficialRuleMajorKey.compareNat
        (tableValue (mapLabelTable pseudoValueOfLabel keyL.labels) path)
        (tableValue (mapLabelTable pseudoValueOfLabel keyR.labels) path) := by
    intro path
    unfold encodedPseudo4c OfficialRuleMajorKey.compareNat
    by_cases present : HasAddress keyL.constitutional.rule1a path
    · have presentR : HasAddress keyR.constitutional.rule1a path := (support path).1 present
      rw [if_pos present, if_pos presentR]
      rcases lt_trichotomy
          (tableValue (mapLabelTable pseudoValueOfLabel keyL.labels) path)
          (tableValue (mapLabelTable pseudoValueOfLabel keyR.labels) path) with h | h | h
      · rw [compare_lt_iff_lt.2 h, compare_lt_iff_lt.2]
        exact WithBot.coe_lt_coe.2 (WithBot.coe_lt_coe.2 (code_lt_iff.2 h))
      · rw [h, compare_eq_iff_eq.2 rfl, compare_eq_iff_eq.2 rfl]
      · rw [compare_gt_iff_gt.2 h, compare_gt_iff_gt.2]
        exact WithBot.coe_lt_coe.2 (WithBot.coe_lt_coe.2 (code_lt_iff.2 h))
    · have absentR : ¬ HasAddress keyR.constitutional.rule1a path :=
        fun h => present ((support path).2 h)
      rw [if_neg present, if_neg absentR, compare_eq_iff_eq.2 rfl]
      have absentL : ¬ HasAddress (mapLabelTable pseudoValueOfLabel keyL.labels) path :=
        fun h => present ((hasAddress_iff_of_sameAddressRows (pseudoTable_rows matchL labelsL) path).1 h)
      have absentR' : ¬ HasAddress (mapLabelTable pseudoValueOfLabel keyR.labels) path :=
        fun h => absentR ((hasAddress_iff_of_sameAddressRows (pseudoTable_rows matchR labelsR) path).1 h)
      rw [tableValue_eq_zero_of_not_hasAddress absentL,
        tableValue_eq_zero_of_not_hasAddress absentR', compare_eq_iff_eq.2 rfl]
  exact (later_compareSparseLayers_eq_firstDifference OfficialRuleMajorKey.compareNat rfl
      wfL.wellFormed1a wfR.wellFormed1a wfL.positive1a wfR.positive1a tied
      (pseudoTable_rows matchL labelsL) (pseudoTable_rows matchR labelsR)
      (pseudoTable_wellFormed labelsL) (pseudoTable_wellFormed labelsR) outcome).trans
    ((FirstDifferenceOutcome.congr (fun position result => by rw [pointwise position]) outcome).trans
      (firstDifferenceOutcome_iff_pathFirstDifferenceOf _ _ outcome))

theorem rule4c_pathFirstDifference_iff
    {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key} {ρL ρR : RS}
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (matchL : LocalizedCumulativeTreeTableMatch (.rule4c ρL) treeL keyL)
    (matchR : LocalizedCumulativeTreeTableMatch (.rule4c ρR) treeR keyR)
    (labelsL : LocalizedCumulativeTreeLabelMatch treeL keyL)
    (labelsR : LocalizedCumulativeTreeLabelMatch treeR keyR)
    (realizesL : LocalizedCumulativeTreeRealizes input readL treeL)
    (realizesR : LocalizedCumulativeTreeRealizes input readR treeR)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      keyL.constitutional.rule1a keyR.constitutional.rule1a = .eq)
    (tied4a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4a keyL) (scalar4a keyR) = .eq) (outcome : Ordering) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4c keyL) (scalar4c keyR) = outcome ↔
      PathFirstDifferenceOf (encodedPseudo4c keyL) (encodedPseudo4c keyR) outcome := by
  rw [compareScalar4c_eq_pseudoValueOfLabels_of_rule4a_tie matchL matchR labelsL labelsR tied4a]
  exact pseudoTable_pathFirstDifference_iff matchL matchR labelsL labelsR realizesL realizesR tied outcome

/-! This projection changes only the observed stage on a fixed tree. It is not a different
stage execution or a sort-trace conversion. -/

def rule4bTableView (reference : RS)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key) : input.LocalizedRerootCumulativeRule45Key :=
  { key with descriptor := (tree.tables (.rule4b reference)).descriptor }

theorem rule4bTableView_matches {reference : RS}
    (matched : LocalizedCumulativeTreeTableMatch (.rule4c reference) tree key) :
    LocalizedCumulativeTreeTableMatch (.rule4b reference) tree
      (rule4bTableView reference tree key) :=
  ⟨matched.1, matched.2.1, matched.2.2.1, rfl⟩

theorem scalar4b_rule4c_eq_table {reference : RS}
    (matched : LocalizedCumulativeTreeTableMatch (.rule4c reference) tree key) :
    scalar4b key = table (bit4b reference) tree := by
  unfold scalar4b
  rw [← matched.2.2.2, tables_descriptor, table_map]
  rfl

theorem scalar4a_rule4bTableView {reference : RS}
    (matched : LocalizedCumulativeTreeTableMatch (.rule4c reference) tree key) :
    scalar4a (rule4bTableView reference tree key) = scalar4a key := by
  rw [scalar4a_eq_table_rule4b (rule4bTableView_matches matched), scalar4a_rule4c_eq_table matched]
  rfl

theorem scalar4b_rule4bTableView {reference : RS}
    (matched : LocalizedCumulativeTreeTableMatch (.rule4c reference) tree key) :
    scalar4b (rule4bTableView reference tree key) = scalar4b key := by
  rw [scalar4b_eq_table (rule4bTableView_matches matched), scalar4b_rule4c_eq_table matched]

theorem encoded4a_rule4bTableView {reference : RS}
    (matched : LocalizedCumulativeTreeTableMatch (.rule4c reference) tree key) (path : List Nat) :
    encoded4a (rule4bTableView reference tree key) path = encoded4a key path := by
  unfold encoded4a
  rw [scalar4a_rule4bTableView matched]
  rfl

theorem encoded4b_rule4bTableView {reference : RS}
    (matched : LocalizedCumulativeTreeTableMatch (.rule4c reference) tree key) (path : List Nat) :
    encoded4b (rule4bTableView reference tree key) path = encoded4b key path := by
  unfold encoded4b
  rw [scalar4a_rule4bTableView matched, scalar4b_rule4bTableView matched]
  rfl

private theorem compareLex_three (a b c : Ordering) :
    List.compareLex compare [a, b, c] [Ordering.eq, Ordering.eq, Ordering.eq] =
      (a.then b).then c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem compareRuleMajor_three (left right : input.LocalizedRerootCumulativeRule45Key) :
    input.compareRuleMajorCumulativeDescriptor 3 left right =
      (input.compareRuleMajorCumulativeDescriptor 2 left right).then
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          (scalar4c left) (scalar4c right)) := by
  rw [compareRuleMajor_two]
  unfold compareRuleMajorCumulativeDescriptor
  simp only [compareLex, Ordering.byKey]
  rw [show List.range 3 = [0, 1, 2] from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [compareLex_three]
  simp only [projectCumulative_zero, projectCumulative_one]
  cases OfficialRuleMajorKey.compare left.constitutional right.constitutional <;> rfl

theorem compareRuleMajor_rule4c_prefix_eq_then
    {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key} {ρL ρR : RS}
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (matchL : LocalizedCumulativeTreeTableMatch (.rule4c ρL) treeL keyL)
    (matchR : LocalizedCumulativeTreeTableMatch (.rule4c ρR) treeR keyR)
    (realizesL : LocalizedCumulativeTreeRealizes input readL treeL)
    (realizesR : LocalizedCumulativeTreeRealizes input readR treeR)
    {W D : Nat} {graphL graphR : RootedDigraph input.Atom}
    {nodeL : graphL.Node} {nodeR : graphR.Node}
    (repCL : Represents W D (ruleKey input.moleculeGraph graphL W D nodeL) keyL.constitutional)
    (repCR : Represents W D (ruleKey input.moleculeGraph graphR W D nodeR) keyR.constitutional)
    {KaL KaR KbL KbR : Certificate.CanonicalSphereKey.Key StereoLabel}
    (shapeAL : Certificate.CanonicalSphereKey.WellShaped W D KaL)
    (shapeAR : Certificate.CanonicalSphereKey.WellShaped W D KaR)
    (shapeBL : Certificate.CanonicalSphereKey.WellShaped W D KbL)
    (shapeBR : Certificate.CanonicalSphereKey.WellShaped W D KbR)
    (repAL : Represents4a W D KaL keyL) (repAR : Represents4a W D KaR keyR)
    (repBL : Represents4b W D KbL keyL) (repBR : Represents4b W D KbR keyR) :
    input.compareRuleMajorCumulativeDescriptor 2 keyL keyR =
      (compare (ruleKey input.moleculeGraph graphL W D nodeL)
        (ruleKey input.moleculeGraph graphR W D nodeR)).then
        ((compare KaL KaR).then (compare KbL KbR)) := by
  have result := compareRuleMajor_across_graphs
    (rule4bTableView_matches matchL) (rule4bTableView_matches matchR) realizesL realizesR
    repCL repCR shapeAL shapeAR shapeBL shapeBR
    (show Represents4a W D KaL (rule4bTableView ρL treeL keyL) from
      fun path => (repAL path).trans (encoded4a_rule4bTableView matchL path).symm)
    (show Represents4a W D KaR (rule4bTableView ρR treeR keyR) from
      fun path => (repAR path).trans (encoded4a_rule4bTableView matchR path).symm)
    (show Represents4b W D KbL (rule4bTableView ρL treeL keyL) from
      fun path => (repBL path).trans (encoded4b_rule4bTableView matchL path).symm)
    (show Represents4b W D KbR (rule4bTableView ρR treeR keyR) from
      fun path => (repBR path).trans (encoded4b_rule4bTableView matchR path).symm)
  rw [compareRuleMajor_two] at result ⊢
  rw [scalar4a_rule4bTableView matchL, scalar4a_rule4bTableView matchR,
    scalar4b_rule4bTableView matchL, scalar4b_rule4bTableView matchR] at result
  exact result

theorem compareRuleMajor_rule4c_eq_then
    {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key} {ρL ρR : RS}
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (matchL : LocalizedCumulativeTreeTableMatch (.rule4c ρL) treeL keyL)
    (matchR : LocalizedCumulativeTreeTableMatch (.rule4c ρR) treeR keyR)
    (labelsL : LocalizedCumulativeTreeLabelMatch treeL keyL)
    (labelsR : LocalizedCumulativeTreeLabelMatch treeR keyR)
    (realizesL : LocalizedCumulativeTreeRealizes input readL treeL)
    (realizesR : LocalizedCumulativeTreeRealizes input readR treeR)
    {W D : Nat} {graphL graphR : RootedDigraph input.Atom}
    {nodeL : graphL.Node} {nodeR : graphR.Node}
    (repCL : Represents W D (ruleKey input.moleculeGraph graphL W D nodeL) keyL.constitutional)
    (repCR : Represents W D (ruleKey input.moleculeGraph graphR W D nodeR) keyR.constitutional)
    {KaL KaR KbL KbR KcL KcR : Certificate.CanonicalSphereKey.Key StereoLabel}
    (shapeAL : Certificate.CanonicalSphereKey.WellShaped W D KaL)
    (shapeAR : Certificate.CanonicalSphereKey.WellShaped W D KaR)
    (shapeBL : Certificate.CanonicalSphereKey.WellShaped W D KbL)
    (shapeBR : Certificate.CanonicalSphereKey.WellShaped W D KbR)
    (shapeCL : Certificate.CanonicalSphereKey.WellShaped W D KcL)
    (shapeCR : Certificate.CanonicalSphereKey.WellShaped W D KcR)
    (repAL : Represents4a W D KaL keyL) (repAR : Represents4a W D KaR keyR)
    (repBL : Represents4b W D KbL keyL) (repBR : Represents4b W D KbR keyR)
    (rep4cL : Represents4c W D KcL keyL) (rep4cR : Represents4c W D KcR keyR) :
    input.compareRuleMajorCumulativeDescriptor 3 keyL keyR =
      ((compare (ruleKey input.moleculeGraph graphL W D nodeL)
        (ruleKey input.moleculeGraph graphR W D nodeR)).then
        ((compare KaL KaR).then (compare KbL KbR))).then (compare KcL KcR) := by
  have priorComparison := compareRuleMajor_rule4c_prefix_eq_then matchL matchR realizesL realizesR
    repCL repCR shapeAL shapeAR shapeBL shapeBR repAL repAR repBL repBR
  rw [compareRuleMajor_three, ← priorComparison]
  cases h : input.compareRuleMajorCumulativeDescriptor 2 keyL keyR with
  | lt => rfl
  | gt => rfl
  | eq =>
      simp only [Ordering.then]
      rw [compareRuleMajor_two, Ordering.then_eq_eq, Ordering.then_eq_eq] at h
      have tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          keyL.constitutional.rule1a keyR.constitutional.rule1a = .eq := by
        have constitution := h.1
        unfold OfficialRuleMajorKey.compare at constitution
        exact (compareLex_eq_eq.1 constitution).1
      exact compare_of_pathFirstDifference shapeCL shapeCR rep4cL rep4cR
        (fun outcome => rule4c_pathFirstDifference_iff matchL matchR labelsL labelsR
          realizesL realizesR tied h.2.1 outcome)

theorem rule4abcKey_le_of_compare_ne_lt
    {graph : RootedDigraph input.Atom} (evidence : StereochemicalEvidence graph)
    {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key} {ρL ρR : RS}
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (matchL : LocalizedCumulativeTreeTableMatch (.rule4c ρL) treeL keyL)
    (matchR : LocalizedCumulativeTreeTableMatch (.rule4c ρR) treeR keyR)
    (labelsL : LocalizedCumulativeTreeLabelMatch treeL keyL)
    (labelsR : LocalizedCumulativeTreeLabelMatch treeR keyR)
    (realizesL : LocalizedCumulativeTreeRealizes input readL treeL)
    (realizesR : LocalizedCumulativeTreeRealizes input readR treeR)
    {W D : Nat} {nodeL nodeR : graph.Node}
    (repCL : Represents W D (ruleKey input.moleculeGraph graph W D nodeL) keyL.constitutional)
    (repCR : Represents W D (ruleKey input.moleculeGraph graph W D nodeR) keyR.constitutional)
    (repAL : Represents4a W D (rule4aComponent input.moleculeGraph graph evidence W D nodeL) keyL)
    (repAR : Represents4a W D (rule4aComponent input.moleculeGraph graph evidence W D nodeR) keyR)
    (repBL : Represents4b W D (rule4bComponent input.moleculeGraph graph evidence W D nodeL) keyL)
    (repBR : Represents4b W D (rule4bComponent input.moleculeGraph graph evidence W D nodeR) keyR)
    (rep4cL : Represents4c W D (rule4cComponent input.moleculeGraph graph evidence W D nodeL) keyL)
    (rep4cR : Represents4c W D (rule4cComponent input.moleculeGraph graph evidence W D nodeR) keyR)
    (descending : input.compareRuleMajorCumulativeDescriptor 3 keyL keyR ≠ .lt) :
    rule4abcKey input.moleculeGraph graph evidence W D nodeR ≤
      rule4abcKey input.moleculeGraph graph evidence W D nodeL := by
  rw [compareRuleMajor_rule4c_eq_then matchL matchR labelsL labelsR realizesL realizesR
    repCL repCR
    (ordinaryKey_stereo_wellShaped input.moleculeGraph graph evidence W D _ nodeL)
    (ordinaryKey_stereo_wellShaped input.moleculeGraph graph evidence W D _ nodeR)
    (ordinaryKey_stereo_wellShaped input.moleculeGraph graph evidence W D _ nodeL)
    (ordinaryKey_stereo_wellShaped input.moleculeGraph graph evidence W D _ nodeR)
    (ordinaryKey_stereo_wellShaped input.moleculeGraph graph evidence W D _ nodeL)
    (ordinaryKey_stereo_wellShaped input.moleculeGraph graph evidence W D _ nodeR)
    repAL repAR repBL repBR rep4cL rep4cR] at descending
  unfold rule4abcKey
  cases h : compare (ruleKey input.moleculeGraph graph W D nodeL)
      (ruleKey input.moleculeGraph graph W D nodeR) with
  | lt => simp [h] at descending
  | gt =>
      apply le_of_lt
      rw [Prod.Lex.lt_iff]
      exact Or.inl ((Rule4aTableBridge.vectorCompare_gt_iff _ _).1 h)
  | eq =>
      have equal := (vectorCompare_eq_iff _ _).1 h
      refine Prod.Lex.le_iff.2 (Or.inr ⟨equal.symm, ?_⟩)
      rw [h] at descending
      change ((compare (rule4aComponent input.moleculeGraph graph evidence W D nodeL)
          (rule4aComponent input.moleculeGraph graph evidence W D nodeR)).then
        (compare (rule4bComponent input.moleculeGraph graph evidence W D nodeL)
          (rule4bComponent input.moleculeGraph graph evidence W D nodeR))).then
        (compare (rule4cComponent input.moleculeGraph graph evidence W D nodeL)
          (rule4cComponent input.moleculeGraph graph evidence W D nodeR)) ≠ .lt at descending
      rw [Ordering.then_assoc] at descending
      exact lex_le_of_then_ne_lt _ _ _ stereoKeyCompare_eq_iff stereoKeyCompare_gt_iff
        stereoKeyCompare_eq_iff stereoKeyCompare_gt_iff stereoKeyCompare_eq_iff
        stereoKeyCompare_gt_iff descending

end
end TetraStereo.OneCenter.Rule4cObservationBridge

assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.pseudoTable_eq_table
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.pseudoTable_rows
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.pseudoTable_wellFormed
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.pseudoTable_pathFirstDifference_iff
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.rule4c_pathFirstDifference_iff
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.rule4bTableView_matches
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.scalar4b_rule4c_eq_table
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.scalar4a_rule4bTableView
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.scalar4b_rule4bTableView
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.encoded4a_rule4bTableView
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.encoded4b_rule4bTableView
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.compareRuleMajor_three
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.compareRuleMajor_rule4c_prefix_eq_then
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.compareRuleMajor_rule4c_eq_then
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.rule4abcKey_le_of_compare_ne_lt
