import TetraStereo.OneCenter.DeclarativeCIPAbsoluteRule5Reading
import TetraStereo.OneCenter.LocalizedRuleMajorRule5Relabel
import TetraStereo.OneCenter.LocalizedRuleMajorRule4cTableBridge
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Rule-5 comparison with independently selected reference senses. Equal complete prior tables
leave only the appended absolute seniority bits. The argument allows every tetrahedral label,
including r/s, and does not assert monotonicity of the selected-sense decoder. -/

namespace TetraStereo.OneCenter.Rule5ObservationBridge
open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree DeclarativeCIP
open Rule4aTableBridge Rule4cObservationBridge OfficialSparseCanonicalVectorComparison
open SparsePhysicalFirstDifference SparseSupportAlignment
noncomputable section
open scoped Classical

def bitTable {input : CertifiedLocalizedCIPInput} (same : Bool)
    (key : input.LocalizedRerootCumulativeRule45Key) : List (List (OfficialSparseEntry Nat)) :=
  key.descriptor.map (List.map (sparseEntryMap (rule5Bit same)))

def bitObservable {input : CertifiedLocalizedCIPInput} (same : Bool)
    (key : input.LocalizedRerootCumulativeRule45Key) (path : List Nat) : WithBot StereoLabel :=
  if HasAddress key.constitutional.rule1a path then
    (((code (tableValue (bitTable same key) path) : StereoCode) : StereoLabel) : WithBot StereoLabel)
  else ⊥

private theorem compare_append_shared (priorValues : List Nat) (left right : Nat) :
    compareLocalizedCumulativeRule45Priority (priorValues ++ [left]) (priorValues ++ [right]) =
      OfficialRuleMajorKey.compareNat left right := by
  induction priorValues with
  | nil =>
      simp [compareLocalizedCumulativeRule45Priority, List.compareLex_cons_cons,
        List.compareLex_nil_nil]
  | cons head tail ih =>
      simpa only [List.cons_append, compareLocalizedCumulativeRule45Priority,
        List.compareLex_cons_cons, CompilerProjectionFidelity.compareNat_self,
        Ordering.eq_then] using ih

private theorem compare_liftEntry (sameL sameR : Bool) (entry : OfficialSparseEntry (List Nat)) :
    OfficialRuleMajorKey.compareSparseEntry compareLocalizedCumulativeRule45Priority
        (entry.1, rule5Lift sameL entry.2) (entry.1, rule5Lift sameR entry.2) =
      OfficialRuleMajorKey.compareSparseEntry OfficialRuleMajorKey.compareNat
        (entry.1, rule5Bit sameL entry.2) (entry.1, rule5Bit sameR entry.2) := by
  unfold OfficialRuleMajorKey.compareSparseEntry
  simp only [compareLex, Ordering.byKey]
  rw [rule5Lift, rule5Lift, compare_append_shared]

private theorem compare_liftLayer (sameL sameR : Bool) :
    ∀ layer : List (OfficialSparseEntry (List Nat)),
      OfficialRuleMajorKey.compareSparseLayer compareLocalizedCumulativeRule45Priority
          (rule5LiftLayer sameL layer) (rule5LiftLayer sameR layer) =
        OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareNat
          (layer.map (sparseEntryMap (rule5Bit sameL)))
          (layer.map (sparseEntryMap (rule5Bit sameR)))
  | [] => rfl
  | entry :: tail => by
      simp only [rule5LiftLayer, List.map_cons, OfficialRuleMajorKey.compareSparseLayer,
        List.compareLex_cons_cons]
      rw [← OfficialRuleMajorKey.compareSparseLayer, ← OfficialRuleMajorKey.compareSparseLayer,
        ← rule5LiftLayer, ← rule5LiftLayer, compare_liftLayer sameL sameR tail]
      rw [compare_liftEntry]
      rfl

/-- The lifts may use opposite conventions: the shared prefix still drops out exactly. -/
theorem compare_lifts_eq_bits {input : CertifiedLocalizedCIPInput}
    (sameL sameR : Bool) (left right : input.LocalizedRerootCumulativeRule45Key)
    (prior : left.descriptor = right.descriptor) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (input.rule5LiftKey sameL left).descriptor (input.rule5LiftKey sameR right).descriptor =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (bitTable sameL left) (bitTable sameR right) := by
  unfold rule5LiftKey bitTable
  rw [prior]
  induction right.descriptor with
  | nil => rfl
  | cons layer tail ih =>
      simp only [List.map_cons, OfficialRuleMajorKey.compareSparseLayers,
        List.compareLex_cons_cons]
      rw [compare_liftLayer]
      exact congrArg _ ih

theorem rule5Bit_priority (own common : RS) (label : Option LocalizedAuxiliaryLabel) :
    rule5Bit (common == own) (localizedCumulativeRule45Priority (.rule4c own) label) =
      localizedRule5Priority common label := by
  cases label with
  | none => cases own <;> cases common <;> rfl
  | some label =>
      cases label with
      | chiral label => cases own <;> cases common <;> cases label <;> rfl
      | pseudoasymmetric label => cases own <;> cases common <;> cases label <;> rfl

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
  {key : input.LocalizedRerootCumulativeRule45Key} {own : RS}

theorem bitTable_eq_table (matched : LocalizedCumulativeTreeTableMatch (.rule4c own) tree key)
    (common : RS) :
    bitTable (common == own) key = table (fun node => localizedRule5Priority common node.label) tree := by
  unfold bitTable
  rw [← matched.2.2.2, tables_descriptor, table_map]
  congr 1
  funext node
  exact rule5Bit_priority own common node.label

theorem bitTable_rows (matched : LocalizedCumulativeTreeTableMatch (.rule4c own) tree key)
    (common : RS) : SameAddressRows (bitTable (common == own) key) key.constitutional.rule1a := by
  rw [bitTable_eq_table matched common, ← matched.1, tables_rule1a]
  exact LocalizedActualTableAddressOrder.SameAddressRows_table_observations _ _ tree

theorem bitTable_wellFormed (matched : LocalizedCumulativeTreeTableMatch (.rule4c own) tree key)
    (common : RS) : SparseTableWellFormed (bitTable (common == own) key) := by
  rw [bitTable_eq_table matched common]
  exact LocalizedActualTableAddressOrder.table_wellFormed _ tree

theorem absolute_encoded4b (matched : LocalizedCumulativeTreeTableMatch (.rule4c own) tree key)
    (common : RS) (path : List Nat) :
    WithBot.map (absoluteRule5Label (senseOf own) (senseOf common)) (encoded4b key path) =
      bitObservable (common == own) key path := by
  unfold encoded4b bitObservable
  by_cases present : HasAddress key.constitutional.rule1a path
  · rw [if_pos present, if_pos present]
    rw [scalar4a_rule4c_eq_table matched, scalar4b_rule4c_eq_table matched,
      bitTable_eq_table matched common]
    rw [tableValue_table_eq_observeAt, tableValue_table_eq_observeAt,
      tableValue_table_eq_observeAt]
    unfold observeAt
    cases observed : tree.decoratedSubtreeAt? path with
    | none =>
        simp [absoluteRule5Label, absoluteRule5Bit_nonchiral]
    | some node =>
        cases hLabel : node.label with
        | none => simp [localizedRule4aPriority,
            localizedRule5Priority, absoluteRule5Label, absoluteRule5Bit_nonchiral, hLabel]
        | some value =>
            cases value with
            | chiral descriptor =>
                cases own <;> cases common <;> cases descriptor <;>
                  simp [bit4b, localizedRule4aPriority, localizedRule4bPriority,
                    localizedRule5Priority, absoluteRule5Label, absoluteRule5Bit, seniorityOf,
                    likeObservation, unlikeObservation, encodeReadings, code, senseOf,
                    DescriptorSense.mirror, hLabel]
            | pseudoasymmetric descriptor =>
                cases descriptor <;>
                  simp [localizedRule4aPriority,
                    localizedRule5Priority, absoluteRule5Label, absoluteRule5Bit_nonchiral, hLabel]
  · rw [if_neg present, if_neg present, WithBot.map_bot]

theorem bitTable_pathFirstDifference_iff
    {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key} {ownL ownR : RS}
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (matchL : LocalizedCumulativeTreeTableMatch (.rule4c ownL) treeL keyL)
    (matchR : LocalizedCumulativeTreeTableMatch (.rule4c ownR) treeR keyR)
    (realizesL : LocalizedCumulativeTreeRealizes input readL treeL)
    (realizesR : LocalizedCumulativeTreeRealizes input readR treeR)
    (common : RS)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      keyL.constitutional.rule1a keyR.constitutional.rule1a = .eq) (outcome : Ordering) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (bitTable (common == ownL) keyL) (bitTable (common == ownR) keyR) = outcome ↔
      PathFirstDifferenceOf (bitObservable (common == ownL) keyL)
        (bitObservable (common == ownR) keyR) outcome := by
  have wfL := wellFormedRuleMajorKey_of_tableMatch matchL realizesL
  have wfR := wellFormedRuleMajorKey_of_tableMatch matchR realizesR
  have support : ∀ path, HasAddress keyL.constitutional.rule1a path ↔
      HasAddress keyR.constitutional.rule1a path := sameSupport_of_compareSparseLayers_eq
    wfL.wellFormed1a wfR.wellFormed1a wfL.positive1a wfR.positive1a tied
  have pointwise : ∀ path,
      compare (bitObservable (common == ownL) keyL path) (bitObservable (common == ownR) keyR path) =
        OfficialRuleMajorKey.compareNat (tableValue (bitTable (common == ownL) keyL) path)
          (tableValue (bitTable (common == ownR) keyR) path) := by
    intro path
    unfold bitObservable OfficialRuleMajorKey.compareNat
    by_cases present : HasAddress keyL.constitutional.rule1a path
    · rw [if_pos present, if_pos ((support path).1 present)]
      rcases lt_trichotomy (tableValue (bitTable (common == ownL) keyL) path)
          (tableValue (bitTable (common == ownR) keyR) path) with h | h | h
      · rw [compare_lt_iff_lt.2 h, compare_lt_iff_lt.2]
        exact WithBot.coe_lt_coe.2 (WithBot.coe_lt_coe.2 (code_lt_iff.2 h))
      · rw [h, compare_eq_iff_eq.2 rfl, compare_eq_iff_eq.2 rfl]
      · rw [compare_gt_iff_gt.2 h, compare_gt_iff_gt.2]
        exact WithBot.coe_lt_coe.2 (WithBot.coe_lt_coe.2 (code_lt_iff.2 h))
    · have absentR : ¬ HasAddress keyR.constitutional.rule1a path :=
        fun h => present ((support path).2 h)
      rw [if_neg present, if_neg absentR, compare_eq_iff_eq.2 rfl]
      have absentL : ¬ HasAddress (bitTable (common == ownL) keyL) path :=
        fun h => present ((hasAddress_iff_of_sameAddressRows (bitTable_rows matchL common) path).1 h)
      have absentR' : ¬ HasAddress (bitTable (common == ownR) keyR) path :=
        fun h => absentR ((hasAddress_iff_of_sameAddressRows (bitTable_rows matchR common) path).1 h)
      rw [tableValue_eq_zero_of_not_hasAddress absentL,
        tableValue_eq_zero_of_not_hasAddress absentR', compare_eq_iff_eq.2 rfl]
  exact (later_compareSparseLayers_eq_firstDifference OfficialRuleMajorKey.compareNat rfl
    wfL.wellFormed1a wfR.wellFormed1a wfL.positive1a wfR.positive1a tied
    (bitTable_rows matchL common) (bitTable_rows matchR common)
    (bitTable_wellFormed matchL common) (bitTable_wellFormed matchR common) outcome).trans
      ((FirstDifferenceOutcome.congr (fun position result => by rw [pointwise position]) outcome).trans
        (firstDifferenceOutcome_iff_pathFirstDifferenceOf _ _ outcome))

end
end TetraStereo.OneCenter.Rule5ObservationBridge

assert_kernel_only TetraStereo.OneCenter.Rule5ObservationBridge.compare_lifts_eq_bits
assert_kernel_only TetraStereo.OneCenter.Rule5ObservationBridge.rule5Bit_priority
assert_kernel_only TetraStereo.OneCenter.Rule5ObservationBridge.absolute_encoded4b
assert_kernel_only TetraStereo.OneCenter.Rule5ObservationBridge.bitTable_pathFirstDifference_iff
