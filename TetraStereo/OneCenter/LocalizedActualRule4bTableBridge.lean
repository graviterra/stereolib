import TetraStereo.OneCenter.LocalizedActualRule4aTableBridge
import TetraStereo.OneCenter.LocalizedActualSiblingSortRefinement
import TetraStereo.KernelOnly

set_option autoImplicit false




















namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

noncomputable section
open scoped Classical
open LocalizedCumulativeDecoratedTree
open CertifiedLocalizedCIPInput
open OfficialSparseCanonicalVectorComparison
open DeclarativeCIP

/-! ## The two scalar columns of a stage-`.rule4b ρ` key -/

/-- The Rule-4b like/unlike bit of a decorated node against `ρ`. -/
def bit4b {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} (ρ : RS)
    (node : LocalizedCumulativeDecoratedTree input carrierFuel) : Nat :=
  localizedRule4bPriority ρ node.label

/-- Scalar projection of the second cumulative component (`0` if absent). -/
def scalar4b {input : CertifiedLocalizedCIPInput} (key : input.LocalizedRerootCumulativeRule45Key) :
    List (List (OfficialSparseEntry Nat)) :=
  key.descriptor.map (List.map (sparseEntryMap fun v => v.getD 1 0))

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
  {key : input.LocalizedRerootCumulativeRule45Key} {ρ : RS}

theorem scalar4a_eq_table_rule4b (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) tree key) :
    scalar4a key = table prio4a tree := by
  unfold scalar4a
  rw [← tableMatch.2.2.2, tables_descriptor, table_map]
  rfl

theorem scalar4b_eq_table (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) tree key) :
    scalar4b key = table (bit4b ρ) tree := by
  unfold scalar4b
  rw [← tableMatch.2.2.2, tables_descriptor, table_map]
  rfl

theorem scalar4a_wellFormed_rule4b
    (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) tree key) :
    SparsePhysicalFirstDifference.SparseTableWellFormed (scalar4a key) := by
  rw [scalar4a_eq_table_rule4b tableMatch]
  exact LocalizedActualTableAddressOrder.table_wellFormed prio4a tree

theorem scalar4a_rows_rule4b (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) tree key) :
    SparseSupportAlignment.SameAddressRows (scalar4a key) key.constitutional.rule1a := by
  rw [scalar4a_eq_table_rule4b tableMatch, ← tableMatch.1, tables_rule1a]
  exact LocalizedActualTableAddressOrder.SameAddressRows_table_observations prio4a
    (fun node => node.atomicNumber) tree

theorem scalar4b_wellFormed (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) tree key) :
    SparsePhysicalFirstDifference.SparseTableWellFormed (scalar4b key) := by
  rw [scalar4b_eq_table tableMatch]
  exact LocalizedActualTableAddressOrder.table_wellFormed (bit4b ρ) tree

theorem scalar4b_rows (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) tree key) :
    SparseSupportAlignment.SameAddressRows (scalar4b key) key.constitutional.rule1a := by
  rw [scalar4b_eq_table tableMatch, ← tableMatch.1, tables_rule1a]
  exact LocalizedActualTableAddressOrder.SameAddressRows_table_observations (bit4b ρ)
    (fun node => node.atomicNumber) tree

/-- A node whose Rule-4a kind is not chiral has Rule-4b bit `0`. -/
theorem bit4b_eq_zero_of_prio4a_ne_two (node : LocalizedCumulativeDecoratedTree input carrierFuel)
    (h : prio4a node ≠ 2) : bit4b ρ node = 0 := by
  unfold prio4a bit4b localizedRule4aPriority at *
  rcases hl : node.label with _ | ⟨_ | _⟩ <;> rw [hl] at h <;>
    simp [localizedRule4bPriority] at h ⊢

theorem scalar4b_eq_zero_of_scalar4a_ne_two
    (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) tree key) (path : List Nat)
    (h : SparsePhysicalFirstDifference.tableValue (scalar4a key) path ≠ 2) :
    SparsePhysicalFirstDifference.tableValue (scalar4b key) path = 0 := by
  rw [scalar4b_eq_table tableMatch, tableValue_table_eq_observeAt]
  rw [scalar4a_eq_table_rule4b tableMatch, tableValue_table_eq_observeAt] at h
  unfold observeAt at h ⊢
  revert h
  cases tree.decoratedSubtreeAt? path with
  | none => intro _; rfl
  | some node => intro h; exact bit4b_eq_zero_of_prio4a_ne_two node h

/-! ## The rule-major comparator at width two -/

/-- `projectCumulative 0` is the Rule-4a scalar table. -/
theorem projectCumulative_zero (layers : List (List (OfficialSparseEntry (List Nat)))) :
    projectCumulative 0 layers = layers.map (List.map (sparseEntryMap fun v => v.headD 0)) := by
  unfold projectCumulative sparseEntryMap
  congr 1
  funext layer
  congr 1
  funext entry
  cases entry.2 <;> rfl

theorem projectCumulative_one (layers : List (List (OfficialSparseEntry (List Nat)))) :
    projectCumulative 1 layers = layers.map (List.map (sparseEntryMap fun v => v.getD 1 0)) := rfl

private theorem compareLex_two (c0 c1 : Ordering) :
    List.compareLex compare [c0, c1] [Ordering.eq, Ordering.eq] = c0.then c1 := by
  cases c0 <;> cases c1 <;> rfl

theorem compareRuleMajor_two (left right : input.LocalizedRerootCumulativeRule45Key) :
    compareRuleMajorCumulativeDescriptor input 2 left right =
      (OfficialRuleMajorKey.compare left.constitutional right.constitutional).then
        ((OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
            (scalar4a left) (scalar4a right)).then
          (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
            (scalar4b left) (scalar4b right))) := by
  unfold compareRuleMajorCumulativeDescriptor
  simp only [compareLex, Ordering.byKey]
  congr 1
  rw [show List.range 2 = [0, 1] from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [compareLex_two]
  simp only [projectCumulative_zero]
  rfl

/-! ## Encoded Rule-4b observations -/

/-- Encoded Rule-4b observation of a stage-`.rule4b ρ` key at an address: the code of the
like/unlike bit at chiral addresses of the Rule-1a support, `⊥` elsewhere. -/
def encoded4b {input : CertifiedLocalizedCIPInput} (key : input.LocalizedRerootCumulativeRule45Key)
    (path : List Nat) : WithBot DeclarativeCIP.StereoLabel :=
  if SparseSupportAlignment.HasAddress key.constitutional.rule1a path then
    ((if SparsePhysicalFirstDifference.tableValue (scalar4a key) path = 2 then
      ((code (SparsePhysicalFirstDifference.tableValue (scalar4b key) path) :
        DeclarativeCIP.StereoCode) : DeclarativeCIP.StereoLabel)
      else (⊥ : DeclarativeCIP.StereoLabel)) : WithBot DeclarativeCIP.StereoLabel)
  else ⊥

variable {tree₁ tree₂ : LocalizedCumulativeDecoratedTree input carrierFuel}
  {key₁ key₂ : input.LocalizedRerootCumulativeRule45Key} {ρ₁ ρ₂ : RS}

/-- Pointwise: with aligned supports and equal Rule-4a values, the encoded Rule-4b observations
compare as the bits. -/
theorem compare_encoded4b
    (match₁ : LocalizedCumulativeTreeTableMatch (.rule4b ρ₁) tree₁ key₁)
    (match₂ : LocalizedCumulativeTreeTableMatch (.rule4b ρ₂) tree₂ key₂)
    (support : ∀ path, SparseSupportAlignment.HasAddress key₁.constitutional.rule1a path ↔
      SparseSupportAlignment.HasAddress key₂.constitutional.rule1a path)
    (col0 : ∀ path, SparsePhysicalFirstDifference.tableValue (scalar4a key₁) path =
      SparsePhysicalFirstDifference.tableValue (scalar4a key₂) path)
    (path : List Nat) :
    compare (encoded4b key₁ path) (encoded4b key₂ path) =
      OfficialRuleMajorKey.compareNat
        (SparsePhysicalFirstDifference.tableValue (scalar4b key₁) path)
        (SparsePhysicalFirstDifference.tableValue (scalar4b key₂) path) := by
  unfold encoded4b OfficialRuleMajorKey.compareNat
  by_cases present : SparseSupportAlignment.HasAddress key₁.constitutional.rule1a path
  · have present₂ := (support path).1 present
    rw [if_pos present, if_pos present₂, ← col0 path]
    by_cases chiral : SparsePhysicalFirstDifference.tableValue (scalar4a key₁) path = 2
    · rw [if_pos chiral, if_pos chiral]
      rcases lt_trichotomy (SparsePhysicalFirstDifference.tableValue (scalar4b key₁) path)
          (SparsePhysicalFirstDifference.tableValue (scalar4b key₂) path) with h | h | h
      · rw [compare_lt_iff_lt.2 h, compare_lt_iff_lt.2]
        exact WithBot.coe_lt_coe.2 (WithBot.coe_lt_coe.2 (code_lt_iff.2 h))
      · rw [h, compare_eq_iff_eq.2 rfl, compare_eq_iff_eq.2 rfl]
      · rw [compare_gt_iff_gt.2 h, compare_gt_iff_gt.2]
        exact WithBot.coe_lt_coe.2 (WithBot.coe_lt_coe.2 (code_lt_iff.2 h))
    · rw [if_neg chiral, if_neg chiral, compare_eq_iff_eq.2 rfl,
        scalar4b_eq_zero_of_scalar4a_ne_two match₁ path chiral,
        scalar4b_eq_zero_of_scalar4a_ne_two match₂ path (by rw [← col0 path]; exact chiral),
        compare_eq_iff_eq.2 rfl]
  · have absent₂ : ¬ SparseSupportAlignment.HasAddress key₂.constitutional.rule1a path :=
      fun h => present ((support path).2 h)
    rw [if_neg present, if_neg absent₂, compare_eq_iff_eq.2 rfl]
    have abs₁ : ¬ SparseSupportAlignment.HasAddress (scalar4b key₁) path :=
      fun h => present ((hasAddress_iff_of_sameAddressRows (scalar4b_rows match₁) path).mp h)
    have abs₂ : ¬ SparseSupportAlignment.HasAddress (scalar4b key₂) path :=
      fun h => absent₂ ((hasAddress_iff_of_sameAddressRows (scalar4b_rows match₂) path).mp h)
    rw [tableValue_eq_zero_of_not_hasAddress abs₁, tableValue_eq_zero_of_not_hasAddress abs₂,
      compare_eq_iff_eq.2 rfl]

/-- A Rule-4a column tie is a pointwise equality of Rule-4a values. -/
theorem scalar4a_pointwise_of_tie
    {read₁ read₂ : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (match₁ : LocalizedCumulativeTreeTableMatch (.rule4b ρ₁) tree₁ key₁)
    (match₂ : LocalizedCumulativeTreeTableMatch (.rule4b ρ₂) tree₂ key₂)
    (realizes₁ : LocalizedCumulativeTreeRealizes input read₁ tree₁)
    (realizes₂ : LocalizedCumulativeTreeRealizes input read₂ tree₂)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      key₁.constitutional.rule1a key₂.constitutional.rule1a = Ordering.eq)
    (tied4a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4a key₁) (scalar4a key₂) = Ordering.eq) :
    ∀ path, SparsePhysicalFirstDifference.tableValue (scalar4a key₁) path =
      SparsePhysicalFirstDifference.tableValue (scalar4a key₂) path := by
  have wf₁ := wellFormedRuleMajorKey_of_tableMatch match₁ realizes₁
  have wf₂ := wellFormedRuleMajorKey_of_tableMatch match₂ realizes₂
  have h := (later_compareSparseLayers_eq_firstDifference OfficialRuleMajorKey.compareNat rfl
    wf₁.wellFormed1a wf₂.wellFormed1a wf₁.positive1a wf₂.positive1a tied
    (scalar4a_rows_rule4b match₁) (scalar4a_rows_rule4b match₂)
    (scalar4a_wellFormed_rule4b match₁) (scalar4a_wellFormed_rule4b match₂) Ordering.eq).1 tied4a
  intro path
  exact (CompilerProjectionFidelity.compareNat_eq_eq_iff _ _).1 (h path)

/-- **The executed Rule-4b column, after Rule-1a and Rule-4a ties, is the path-level first
difference of the encoded Rule-4b observations.** -/
theorem rule4b_pathFirstDifference_iff
    {read₁ read₂ : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (match₁ : LocalizedCumulativeTreeTableMatch (.rule4b ρ₁) tree₁ key₁)
    (match₂ : LocalizedCumulativeTreeTableMatch (.rule4b ρ₂) tree₂ key₂)
    (realizes₁ : LocalizedCumulativeTreeRealizes input read₁ tree₁)
    (realizes₂ : LocalizedCumulativeTreeRealizes input read₂ tree₂)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      key₁.constitutional.rule1a key₂.constitutional.rule1a = Ordering.eq)
    (tied4a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4a key₁) (scalar4a key₂) = Ordering.eq)
    (outcome : Ordering) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4b key₁) (scalar4b key₂) = outcome ↔
      PathFirstDifferenceOf (encoded4b key₁) (encoded4b key₂) outcome := by
  have wf₁ := wellFormedRuleMajorKey_of_tableMatch match₁ realizes₁
  have wf₂ := wellFormedRuleMajorKey_of_tableMatch match₂ realizes₂
  have support : ∀ path, SparseSupportAlignment.HasAddress key₁.constitutional.rule1a path ↔
      SparseSupportAlignment.HasAddress key₂.constitutional.rule1a path :=
    SparsePhysicalFirstDifference.sameSupport_of_compareSparseLayers_eq
      wf₁.wellFormed1a wf₂.wellFormed1a wf₁.positive1a wf₂.positive1a tied
  have col0 := scalar4a_pointwise_of_tie match₁ match₂ realizes₁ realizes₂ tied tied4a
  exact (later_compareSparseLayers_eq_firstDifference OfficialRuleMajorKey.compareNat rfl
      wf₁.wellFormed1a wf₂.wellFormed1a wf₁.positive1a wf₂.positive1a tied
      (scalar4b_rows match₁) (scalar4b_rows match₂)
      (scalar4b_wellFormed match₁) (scalar4b_wellFormed match₂) outcome).trans
    ((DeclarativeCIP.FirstDifferenceOutcome.congr (fun position result =>
      by rw [compare_encoded4b match₁ match₂ support col0 position]) outcome).trans
      (firstDifferenceOutcome_iff_pathFirstDifferenceOf _ _ outcome))

/-- The Rule-4a column of a stage-`.rule4b ρ` key, after a Rule-1a tie, is likewise the first
difference of `encoded4a` (the stage-`.rule4a` lemma transported to the stage-`.rule4b ρ`
match). -/
theorem rule4a_pathFirstDifference_iff_rule4b
    {read₁ read₂ : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (match₁ : LocalizedCumulativeTreeTableMatch (.rule4b ρ₁) tree₁ key₁)
    (match₂ : LocalizedCumulativeTreeTableMatch (.rule4b ρ₂) tree₂ key₂)
    (realizes₁ : LocalizedCumulativeTreeRealizes input read₁ tree₁)
    (realizes₂ : LocalizedCumulativeTreeRealizes input read₂ tree₂)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      key₁.constitutional.rule1a key₂.constitutional.rule1a = Ordering.eq)
    (outcome : Ordering) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4a key₁) (scalar4a key₂) = outcome ↔
      PathFirstDifferenceOf (encoded4a key₁) (encoded4a key₂) outcome := by
  have wf₁ := wellFormedRuleMajorKey_of_tableMatch match₁ realizes₁
  have wf₂ := wellFormedRuleMajorKey_of_tableMatch match₂ realizes₂
  have support : ∀ path, SparseSupportAlignment.HasAddress key₁.constitutional.rule1a path ↔
      SparseSupportAlignment.HasAddress key₂.constitutional.rule1a path :=
    SparsePhysicalFirstDifference.sameSupport_of_compareSparseLayers_eq
      wf₁.wellFormed1a wf₂.wellFormed1a wf₁.positive1a wf₂.positive1a tied
  have pointwise : ∀ path, compare (encoded4a key₁ path) (encoded4a key₂ path) =
      OfficialRuleMajorKey.compareNat
        (SparsePhysicalFirstDifference.tableValue (scalar4a key₁) path)
        (SparsePhysicalFirstDifference.tableValue (scalar4a key₂) path) := by
    intro path
    unfold encoded4a OfficialRuleMajorKey.compareNat
    by_cases present : SparseSupportAlignment.HasAddress key₁.constitutional.rule1a path
    · have present₂ := (support path).1 present
      rw [if_pos present, if_pos present₂]
      rcases lt_trichotomy (SparsePhysicalFirstDifference.tableValue (scalar4a key₁) path)
          (SparsePhysicalFirstDifference.tableValue (scalar4a key₂) path) with h | h | h
      · rw [compare_lt_iff_lt.2 h, compare_lt_iff_lt.2]
        exact WithBot.coe_lt_coe.2 (WithBot.coe_lt_coe.2 (code_lt_iff.2 h))
      · rw [h, compare_eq_iff_eq.2 rfl, compare_eq_iff_eq.2 rfl]
      · rw [compare_gt_iff_gt.2 h, compare_gt_iff_gt.2]
        exact WithBot.coe_lt_coe.2 (WithBot.coe_lt_coe.2 (code_lt_iff.2 h))
    · have absent₂ : ¬ SparseSupportAlignment.HasAddress key₂.constitutional.rule1a path :=
        fun h => present ((support path).2 h)
      rw [if_neg present, if_neg absent₂, compare_eq_iff_eq.2 rfl]
      have abs₁ : ¬ SparseSupportAlignment.HasAddress (scalar4a key₁) path :=
        fun h => present ((hasAddress_iff_of_sameAddressRows (scalar4a_rows_rule4b match₁) path).mp h)
      have abs₂ : ¬ SparseSupportAlignment.HasAddress (scalar4a key₂) path :=
        fun h => absent₂ ((hasAddress_iff_of_sameAddressRows (scalar4a_rows_rule4b match₂) path).mp h)
      rw [tableValue_eq_zero_of_not_hasAddress abs₁, tableValue_eq_zero_of_not_hasAddress abs₂,
        compare_eq_iff_eq.2 rfl]
  exact (later_compareSparseLayers_eq_firstDifference OfficialRuleMajorKey.compareNat rfl
      wf₁.wellFormed1a wf₂.wellFormed1a wf₁.positive1a wf₂.positive1a tied
      (scalar4a_rows_rule4b match₁) (scalar4a_rows_rule4b match₂)
      (scalar4a_wellFormed_rule4b match₁) (scalar4a_wellFormed_rule4b match₂) outcome).trans
    ((DeclarativeCIP.FirstDifferenceOutcome.congr (fun position result =>
      by rw [pointwise position]) outcome).trans
      (firstDifferenceOutcome_iff_pathFirstDifferenceOf _ _ outcome))

/-! ## The cumulative sort is rule-major when the Rule-4a tables agree -/

private theorem compareSparseLayer_pair_of_fst_eq :
    ∀ (l m : List (OfficialSparseEntry (Nat × Nat))),
      l.map (sparseEntryMap Prod.fst) = m.map (sparseEntryMap Prod.fst) →
        OfficialRuleMajorKey.compareSparseLayer compareLocalizedCumulativeRule45Priority
            (l.map (sparseEntryMap fun p => [p.1, p.2])) (m.map (sparseEntryMap fun p => [p.1, p.2])) =
          OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareNat
            (l.map (sparseEntryMap Prod.snd)) (m.map (sparseEntryMap Prod.snd))
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | e :: l, f :: m, h => by
      simp only [List.map_cons, List.cons.injEq, sparseEntryMap, Prod.mk.injEq] at h
      obtain ⟨⟨haddr, hfst⟩, hrest⟩ := h
      simp only [List.map_cons, OfficialRuleMajorKey.compareSparseLayer, List.compareLex_cons_cons]
      rw [← OfficialRuleMajorKey.compareSparseLayer,
        ← OfficialRuleMajorKey.compareSparseLayer,
        compareSparseLayer_pair_of_fst_eq l m (by
          simpa only [List.map_cons, sparseEntryMap] using hrest)]
      congr 1
      unfold OfficialRuleMajorKey.compareSparseEntry sparseEntryMap
      simp only [compareLex, Ordering.byKey, haddr, hfst]
      congr 1
      unfold compareLocalizedCumulativeRule45Priority
      simp only [List.compareLex_cons_cons, List.compareLex_nil_nil, CompilerProjectionFidelity.compareNat_self]
      cases OfficialRuleMajorKey.compareNat e.2.2 f.2.2 <;> rfl

private theorem compareSparseLayers_pair_of_fst_eq :
    ∀ (L M : List (List (OfficialSparseEntry (Nat × Nat)))),
      L.map (List.map (sparseEntryMap Prod.fst)) = M.map (List.map (sparseEntryMap Prod.fst)) →
        OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
            (L.map (List.map (sparseEntryMap fun p => [p.1, p.2])))
            (M.map (List.map (sparseEntryMap fun p => [p.1, p.2]))) =
          OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
            (L.map (List.map (sparseEntryMap Prod.snd))) (M.map (List.map (sparseEntryMap Prod.snd)))
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | l :: L, m :: M, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.map_cons, OfficialRuleMajorKey.compareSparseLayers, List.compareLex_cons_cons]
      rw [← OfficialRuleMajorKey.compareSparseLayers, ← OfficialRuleMajorKey.compareSparseLayers,
        compareSparseLayers_pair_of_fst_eq L M h.2, compareSparseLayer_pair_of_fst_eq l m h.1]

/-- The stage-`.rule4b ρ` descriptor is the pair table in singleton-vector form. -/
theorem descriptor_eq_map_pair (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) tree key) :
    key.descriptor = (table (fun node => (prio4a node, bit4b ρ node)) tree).map
      (List.map (sparseEntryMap fun p => [p.1, p.2])) := by
  rw [← tableMatch.2.2.2, tables_descriptor, table_map]
  rfl

theorem scalar4a_eq_map_fst (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) tree key) :
    scalar4a key = (table (fun node => (prio4a node, bit4b ρ node)) tree).map
      (List.map (sparseEntryMap Prod.fst)) := by
  rw [scalar4a_eq_table_rule4b tableMatch, table_map]

theorem scalar4b_eq_map_snd (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) tree key) :
    scalar4b key = (table (fun node => (prio4a node, bit4b ρ node)) tree).map
      (List.map (sparseEntryMap Prod.snd)) := by
  rw [scalar4b_eq_table tableMatch, table_map]

/-- **Equal Rule-4a tables make the cumulative descriptor comparison the Rule-4b column
comparison.** -/
theorem compare_descriptor_eq_scalar4b_of_scalar4a_eq
    (match₁ : LocalizedCumulativeTreeTableMatch (.rule4b ρ₁) tree₁ key₁)
    (match₂ : LocalizedCumulativeTreeTableMatch (.rule4b ρ₂) tree₂ key₂)
    (h4a : scalar4a key₁ = scalar4a key₂) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        key₁.descriptor key₂.descriptor =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4b key₁) (scalar4b key₂) := by
  rw [descriptor_eq_map_pair match₁, descriptor_eq_map_pair match₂, scalar4b_eq_map_snd match₁,
    scalar4b_eq_map_snd match₂]
  apply compareSparseLayers_pair_of_fst_eq
  rw [← scalar4a_eq_map_fst match₁, ← scalar4a_eq_map_fst match₂, h4a]

/-- **The actual comparator is rule-major** on two stage-`.rule4b` keys whose Rule-4a tables agree
whenever their constitutional keys tie. -/
theorem compare_eq_ruleMajor_of_scalar4a
    (match₁ : LocalizedCumulativeTreeTableMatch (.rule4b ρ₁) tree₁ key₁)
    (match₂ : LocalizedCumulativeTreeTableMatch (.rule4b ρ₂) tree₂ key₂)
    (h4a : OfficialRuleMajorKey.compare key₁.constitutional key₂.constitutional = Ordering.eq →
      scalar4a key₁ = scalar4a key₂) :
    input.compareLocalizedRerootCumulativeRule45Keys key₁ key₂ =
      compareRuleMajorCumulativeDescriptor input 2 key₁ key₂ := by
  rw [compareRuleMajor_two]
  unfold compareLocalizedRerootCumulativeRule45Keys
  simp only [compareLex, Ordering.byKey]
  rcases hc : OfficialRuleMajorKey.compare key₁.constitutional key₂.constitutional with _ | _ | _
  · rfl
  · simp only [Ordering.then]
    have heq := h4a hc
    rw [compare_descriptor_eq_scalar4b_of_scalar4a_eq match₁ match₂ heq, heq]
    have hself : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4a key₂) (scalar4a key₂) = Ordering.eq :=
      CompilerProjectionFidelity.compareSparseLayers_self OfficialRuleMajorKey.compareNat
        CompilerProjectionFidelity.compareNat_self _
    rw [hself]
  · rfl

/-! ## Representation and the rule-major comparison -/

/-- A sphere key represents an actual key's Rule-4b column pointwise. -/
def Represents4b (W D : Nat) (key4b : Certificate.CanonicalSphereKey.Key DeclarativeCIP.StereoLabel)
    {input : CertifiedLocalizedCIPInput} (key : input.LocalizedRerootCumulativeRule45Key) : Prop :=
  ∀ path, Certificate.CanonicalSphereKey.pathObservationOf W D key4b path = encoded4b key path

/-- A scalar column comparison that is the first difference of two represented sphere keys is
their `compare`. -/
theorem compare_of_pathFirstDifference {W D : Nat}
    {K₁ K₂ : Certificate.CanonicalSphereKey.Key DeclarativeCIP.StereoLabel}
    (shaped₁ : Certificate.CanonicalSphereKey.WellShaped W D K₁)
    (shaped₂ : Certificate.CanonicalSphereKey.WellShaped W D K₂)
    {enc₁ enc₂ : List Nat → WithBot DeclarativeCIP.StereoLabel}
    (rep₁ : ∀ path, Certificate.CanonicalSphereKey.pathObservationOf W D K₁ path = enc₁ path)
    (rep₂ : ∀ path, Certificate.CanonicalSphereKey.pathObservationOf W D K₂ path = enc₂ path)
    {c : Ordering} (iff : ∀ outcome, c = outcome ↔ PathFirstDifferenceOf enc₁ enc₂ outcome) :
    c = compare K₁ K₂ := by
  cases h : c with
  | lt =>
      obtain ⟨path, decisive, earlierTied⟩ := (iff Ordering.lt).1 h
      symm
      rw [stereoKeyCompare_lt_iff]
      refine (Certificate.CanonicalSphereKey.key_lt_iff_pathObservation shaped₁ shaped₂).2
        ⟨path, ?_, ?_⟩
      · rw [rep₁ path, rep₂ path]; exact decisive
      · intro earlier before
        rw [rep₁ earlier, rep₂ earlier]; exact earlierTied earlier before
  | gt =>
      obtain ⟨path, decisive, earlierTied⟩ := (iff Ordering.gt).1 h
      symm
      rw [stereoKeyCompare_gt_iff]
      refine (Certificate.CanonicalSphereKey.key_lt_iff_pathObservation shaped₂ shaped₁).2
        ⟨path, ?_, ?_⟩
      · rw [rep₁ path, rep₂ path]; exact decisive
      · intro earlier before
        rw [rep₁ earlier, rep₂ earlier]; exact (earlierTied earlier before).symm
  | eq =>
      symm
      rw [stereoKeyCompare_eq_iff]
      refine (Certificate.CanonicalSphereKey.key_eq_iff_pathObservation shaped₁ shaped₂).2 ?_
      intro path
      rw [rep₁ path, rep₂ path]
      exact (iff Ordering.eq).1 h path

/-- **The rule-major comparison of two stage-`.rule4b ρ` keys is the lexicographic comparison of
their constitutional, Rule-4a and Rule-4b sphere keys.** -/
theorem compareRuleMajor_eq_then
    {read₁ read₂ : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (match₁ : LocalizedCumulativeTreeTableMatch (.rule4b ρ₁) tree₁ key₁)
    (match₂ : LocalizedCumulativeTreeTableMatch (.rule4b ρ₂) tree₂ key₂)
    (realizes₁ : LocalizedCumulativeTreeRealizes input read₁ tree₁)
    (realizes₂ : LocalizedCumulativeTreeRealizes input read₂ tree₂)
    {W D : Nat} {graph : RootedDigraph input.Atom} {child₁ child₂ : graph.Node}
    (repC₁ : Represents W D (ruleKey input.moleculeGraph graph W D child₁) key₁.constitutional)
    (repC₂ : Represents W D (ruleKey input.moleculeGraph graph W D child₂) key₂.constitutional)
    {K4a₁ K4a₂ K4b₁ K4b₂ : Certificate.CanonicalSphereKey.Key DeclarativeCIP.StereoLabel}
    (shaped4a₁ : Certificate.CanonicalSphereKey.WellShaped W D K4a₁)
    (shaped4a₂ : Certificate.CanonicalSphereKey.WellShaped W D K4a₂)
    (shaped4b₁ : Certificate.CanonicalSphereKey.WellShaped W D K4b₁)
    (shaped4b₂ : Certificate.CanonicalSphereKey.WellShaped W D K4b₂)
    (rep4a₁ : Represents4a W D K4a₁ key₁) (rep4a₂ : Represents4a W D K4a₂ key₂)
    (rep4b₁ : Represents4b W D K4b₁ key₁) (rep4b₂ : Represents4b W D K4b₂ key₂) :
    compareRuleMajorCumulativeDescriptor input 2 key₁ key₂ =
      (compare (ruleKey input.moleculeGraph graph W D child₁)
          (ruleKey input.moleculeGraph graph W D child₂)).then
        ((compare K4a₁ K4a₂).then (compare K4b₁ K4b₂)) := by
  have wf₁ := wellFormedRuleMajorKey_of_tableMatch match₁ realizes₁
  have wf₂ := wellFormedRuleMajorKey_of_tableMatch match₂ realizes₂
  have hconst : OfficialRuleMajorKey.compare key₁.constitutional key₂.constitutional =
      compare (ruleKey input.moleculeGraph graph W D child₁)
        (ruleKey input.moleculeGraph graph W D child₂) :=
    compare_eq_compare_vector wf₁ wf₂
      (ruleKey_vectorWellShaped input.moleculeGraph graph W D child₁)
      (ruleKey_vectorWellShaped input.moleculeGraph graph W D child₂) repC₁ repC₂
  rw [compareRuleMajor_two, hconst]
  rcases hc : compare (ruleKey input.moleculeGraph graph W D child₁)
      (ruleKey input.moleculeGraph graph W D child₂) with _ | _ | _
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

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.rule4b_pathFirstDifference_iff
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.compareRuleMajor_eq_then
