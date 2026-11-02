import TetraStereo.OneCenter.LocalizedActualRule4bTableBridge
import TetraStereo.OneCenter.LocalizedChiralStageExtension
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

/-! ## Seniority arithmetic -/

/-- The descriptor named by a Rule-4b like/unlike bit under the own reference `ρ`. -/
def descriptorOfBit (ρ : RS) (like : Nat) : RS := if like = 1 then ρ else RS.swap ρ

/-- The Rule-5 common-`R` seniority bit appended to a `[kind, like]` observation whose like bit is
read under the convention `τ`: `1` at a chiral centre whose named descriptor is `R`. -/
def seniority (τ : RS) (kind like : Nat) : Nat :=
  if kind = 2 then (if descriptorOfBit τ like = RS.R then 1 else 0) else 0

theorem swap_swap (ρ : RS) : RS.swap (RS.swap ρ) = ρ := by cases ρ <;> rfl

theorem swap_eq_R_iff (d : RS) : RS.swap d = RS.R ↔ d = RS.S := by cases d <;> decide


theorem extendToRule5_getD_three (τ : RS) (kind like : Nat) :
    (extendLocalizedRule4bPriorityToRule5 τ .R [kind, like]).getD 3 0 = seniority τ kind like := by
  unfold extendLocalizedRule4bPriorityToRule5 seniority descriptorOfBit
  by_cases hk : kind = 2
  · subst hk
    by_cases hl : like = 1
    · subst hl
      cases τ <;> simp
    · cases τ <;> simp [hl, RS.swap]
  · simp [hk]


theorem extendToRule5_two (τ : RS) (kind like : Nat) :
    extendLocalizedRule4bPriorityToRule5 τ .R [kind, like] = [kind, like, 0, seniority τ kind like] := by
  rw [← extendToRule5_getD_three τ kind like]
  unfold extendLocalizedRule4bPriorityToRule5
  rfl

theorem descriptorOfBit_swap (ρ : RS) (like : Nat) :
    descriptorOfBit (RS.swap ρ) like = RS.swap (descriptorOfBit ρ like) := by
  unfold descriptorOfBit
  split_ifs
  · rfl
  · rw [swap_swap]

/-- The two conventions agree exactly off the chiral support. -/
theorem seniority_eq_iff (ρ : RS) (kind like : Nat) :
    seniority ρ kind like = seniority (RS.swap ρ) kind like ↔ kind ≠ 2 := by
  unfold seniority
  by_cases hk : kind = 2
  · simp only [hk, if_true, descriptorOfBit_swap, swap_eq_R_iff, ne_eq, not_true_eq_false,
      iff_false]
    cases descriptorOfBit ρ like <;> simp
  · simp [hk]

/-- On the chiral support the own convention is senior exactly when the named descriptor is `R`. -/
theorem seniority_swap_lt_iff (ρ : RS) (kind like : Nat) :
    seniority (RS.swap ρ) kind like < seniority ρ kind like ↔
      kind = 2 ∧ descriptorOfBit ρ like = RS.R := by
  unfold seniority
  by_cases hk : kind = 2
  · simp only [hk, if_true, descriptorOfBit_swap, swap_eq_R_iff, true_and]
    cases descriptorOfBit ρ like <;> simp
  · simp [hk]

/-- For a genuine bit, the named descriptor is `R` exactly when the bit is the like code of `R`. -/
theorem descriptorOfBit_eq_R_iff (ρ : RS) {like : Nat} (hlike : like ≤ 1) :
    descriptorOfBit ρ like = RS.R ↔ like = (if ρ = RS.R then 1 else 0) := by
  unfold descriptorOfBit
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hlike with rfl | rfl <;> cases ρ <;> simp [RS.swap]

theorem localizedRule4bPriority_le_one (ρ : RS) :
    ∀ label : Option LocalizedAuxiliaryLabel, localizedRule4bPriority ρ label ≤ 1
  | none => Nat.zero_le _
  | some (.pseudoasymmetric _) => Nat.zero_le _
  | some (.chiral _) => by
      simp only [localizedRule4bPriority]
      split_ifs <;> omega

/-! ## The fourth scalar column -/

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-- The Rule-5 common-`R` seniority of a decorated node: its Rule-4a kind and own-reference
(`ρ`) like bit, read under the convention `τ`. -/
def seniorityAt (ρ τ : RS) (node : LocalizedCumulativeDecoratedTree input carrierFuel) : Nat :=
  seniority τ (prio4a node) (bit4b ρ node)

/-- Scalar projection of the fourth cumulative component (`0` if absent). -/
def scalar5 (key : input.LocalizedRerootCumulativeRule45Key) :
    List (List (OfficialSparseEntry Nat)) :=
  key.descriptor.map (List.map (sparseEntryMap fun v => v.getD 3 0))

variable {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
  {key : input.LocalizedRerootCumulativeRule45Key} {ρ : RS}

theorem scalar5_extend_eq_table
    (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) tree key) (τ : RS) :
    scalar5 (input.extendLocalizedRerootCumulativeRule45Key
        (extendLocalizedRule4bPriorityToRule5 τ .R) key) =
      table (seniorityAt ρ τ) tree := by
  unfold scalar5
  rw [extendLocalizedRerootCumulativeRule45Key_descriptor, ← tableMatch.2.2.2, tables_descriptor]
  unfold extendLocalizedPriorityLayers extendLocalizedPriorityLayer
  rw [List.map_map]
  have step : (List.map (sparseEntryMap fun v : List Nat => v.getD 3 0) ∘
      List.map (extendLocalizedPriorityEntry (extendLocalizedRule4bPriorityToRule5 τ .R))) =
      List.map (sparseEntryMap fun v =>
        (extendLocalizedRule4bPriorityToRule5 τ .R v).getD 3 0) := by
    funext layer
    simp only [Function.comp_apply, List.map_map]
    rfl
  rw [step, table_map]
  congr 1
  funext node
  exact extendToRule5_getD_three τ (prio4a node) (bit4b ρ node)

theorem scalar5_rows (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) tree key)
    (τ : RS) :
    SparseSupportAlignment.SameAddressRows
      (scalar5 (input.extendLocalizedRerootCumulativeRule45Key
        (extendLocalizedRule4bPriorityToRule5 τ .R) key))
      key.constitutional.rule1a := by
  rw [scalar5_extend_eq_table tableMatch τ, ← tableMatch.1, tables_rule1a]
  exact LocalizedActualTableAddressOrder.SameAddressRows_table_observations (seniorityAt ρ τ)
    (fun node => node.atomicNumber) tree

theorem scalar5_wellFormed (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) tree key)
    (τ : RS) :
    SparsePhysicalFirstDifference.SparseTableWellFormed
      (scalar5 (input.extendLocalizedRerootCumulativeRule45Key
        (extendLocalizedRule4bPriorityToRule5 τ .R) key)) := by
  rw [scalar5_extend_eq_table tableMatch τ]
  exact LocalizedActualTableAddressOrder.table_wellFormed (seniorityAt ρ τ) tree

/-- The fourth column at an address is the seniority of the Rule-4a kind and Rule-4b bit there. -/
theorem tableValue_scalar5 (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) tree key)
    (τ : RS) (path : List Nat) :
    SparsePhysicalFirstDifference.tableValue
        (scalar5 (input.extendLocalizedRerootCumulativeRule45Key
          (extendLocalizedRule4bPriorityToRule5 τ .R) key)) path =
      seniority τ (SparsePhysicalFirstDifference.tableValue (scalar4a key) path)
        (SparsePhysicalFirstDifference.tableValue (scalar4b key) path) := by
  rw [scalar5_extend_eq_table tableMatch τ, scalar4a_eq_table_rule4b tableMatch,
    scalar4b_eq_table tableMatch, tableValue_table_eq_observeAt, tableValue_table_eq_observeAt,
    tableValue_table_eq_observeAt]
  unfold observeAt
  cases tree.decoratedSubtreeAt? path with
  | none => simp [seniority]
  | some node => rfl

/-- The Rule-4b column is a genuine bit everywhere. -/
theorem tableValue_scalar4b_le_one
    (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) tree key) (path : List Nat) :
    SparsePhysicalFirstDifference.tableValue (scalar4b key) path ≤ 1 := by
  rw [scalar4b_eq_table tableMatch, tableValue_table_eq_observeAt]
  unfold observeAt
  cases tree.decoratedSubtreeAt? path with
  | none => exact Nat.zero_le _
  | some node => exact localizedRule4bPriority_le_one ρ node.label

/-! ## The descriptor comparison of two extensions is the fourth-column comparison -/

private theorem compareLex_quad (k l a b : Nat) :
    List.compareLex OfficialRuleMajorKey.compareNat [k, l, 0, a] [k, l, 0, b] =
      OfficialRuleMajorKey.compareNat a b := by
  simp only [List.compareLex_cons_cons, List.compareLex_nil_nil,
    CompilerProjectionFidelity.compareNat_self]
  cases OfficialRuleMajorKey.compareNat a b <;> rfl

private theorem compareSparseEntry_extend5 (τ₁ τ₂ : RS) (addr : List Nat) (k l : Nat) :
    OfficialRuleMajorKey.compareSparseEntry compareLocalizedCumulativeRule45Priority
        (extendLocalizedPriorityEntry (extendLocalizedRule4bPriorityToRule5 τ₁ .R) (addr, [k, l]))
        (extendLocalizedPriorityEntry (extendLocalizedRule4bPriorityToRule5 τ₂ .R) (addr, [k, l])) =
      OfficialRuleMajorKey.compareSparseEntry OfficialRuleMajorKey.compareNat
        (sparseEntryMap (fun v : List Nat => v.getD 3 0)
          (extendLocalizedPriorityEntry (extendLocalizedRule4bPriorityToRule5 τ₁ .R) (addr, [k, l])))
        (sparseEntryMap (fun v : List Nat => v.getD 3 0)
          (extendLocalizedPriorityEntry (extendLocalizedRule4bPriorityToRule5 τ₂ .R)
            (addr, [k, l]))) := by
  unfold extendLocalizedPriorityEntry sparseEntryMap
  simp only [extendToRule5_two]
  unfold OfficialRuleMajorKey.compareSparseEntry
  simp only [compareLex, Ordering.byKey, Function.flip_def,
    CompilerProjectionFidelity.list_compareLex_self _ CompilerProjectionFidelity.compareNat_self addr,
    Ordering.eq_then]
  unfold compareLocalizedCumulativeRule45Priority
  rw [compareLex_quad]
  rfl

private theorem compareSparseLayer_map_congr {α β : Type*}
    (cmp₁ : α → α → Ordering) (cmp₂ : β → β → Ordering)
    (F G : OfficialSparseEntry (List Nat) → OfficialSparseEntry α)
    (H K : OfficialSparseEntry (List Nat) → OfficialSparseEntry β) :
    ∀ layer : List (OfficialSparseEntry (List Nat)),
      (∀ e ∈ layer, OfficialRuleMajorKey.compareSparseEntry cmp₁ (F e) (G e) =
        OfficialRuleMajorKey.compareSparseEntry cmp₂ (H e) (K e)) →
      OfficialRuleMajorKey.compareSparseLayer cmp₁ (layer.map F) (layer.map G) =
        OfficialRuleMajorKey.compareSparseLayer cmp₂ (layer.map H) (layer.map K)
  | [], _ => rfl
  | e :: layer, h => by
      simp only [List.map_cons, OfficialRuleMajorKey.compareSparseLayer, List.compareLex_cons_cons]
      rw [← OfficialRuleMajorKey.compareSparseLayer, ← OfficialRuleMajorKey.compareSparseLayer,
        compareSparseLayer_map_congr cmp₁ cmp₂ F G H K layer
          (fun e' he' => h e' (List.mem_cons_of_mem _ he')),
        h e List.mem_cons_self]

private theorem compareSparseLayers_map_congr {α β : Type*}
    (cmp₁ : α → α → Ordering) (cmp₂ : β → β → Ordering)
    (F G : OfficialSparseEntry (List Nat) → OfficialSparseEntry α)
    (H K : OfficialSparseEntry (List Nat) → OfficialSparseEntry β) :
    ∀ T : List (List (OfficialSparseEntry (List Nat))),
      (∀ layer ∈ T, ∀ e ∈ layer, OfficialRuleMajorKey.compareSparseEntry cmp₁ (F e) (G e) =
        OfficialRuleMajorKey.compareSparseEntry cmp₂ (H e) (K e)) →
      OfficialRuleMajorKey.compareSparseLayers cmp₁ (T.map (List.map F)) (T.map (List.map G)) =
        OfficialRuleMajorKey.compareSparseLayers cmp₂ (T.map (List.map H)) (T.map (List.map K))
  | [], _ => rfl
  | layer :: T, h => by
      simp only [List.map_cons, OfficialRuleMajorKey.compareSparseLayers, List.compareLex_cons_cons]
      rw [← OfficialRuleMajorKey.compareSparseLayers, ← OfficialRuleMajorKey.compareSparseLayers,
        compareSparseLayers_map_congr cmp₁ cmp₂ F G H K T
          (fun layer' hl' => h layer' (List.mem_cons_of_mem _ hl')),
        compareSparseLayer_map_congr cmp₁ cmp₂ F G H K layer (h layer List.mem_cons_self)]

/-- **Two Rule-5 extensions of one Rule-4b table compare by their fourth columns.** -/
theorem compare_extend5_eq_scalar5 {T : List (List (OfficialSparseEntry (List Nat)))}
    (image : LocalizedStageDescriptorImage (.rule4b ρ) LocalizedNoPseudoLabel T) (τ₁ τ₂ : RS) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (extendLocalizedPriorityLayers (extendLocalizedRule4bPriorityToRule5 τ₁ .R) T)
        (extendLocalizedPriorityLayers (extendLocalizedRule4bPriorityToRule5 τ₂ .R) T) =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        ((extendLocalizedPriorityLayers (extendLocalizedRule4bPriorityToRule5 τ₁ .R) T).map
          (List.map (sparseEntryMap fun v : List Nat => v.getD 3 0)))
        ((extendLocalizedPriorityLayers (extendLocalizedRule4bPriorityToRule5 τ₂ .R) T).map
          (List.map (sparseEntryMap fun v : List Nat => v.getD 3 0))) := by
  unfold extendLocalizedPriorityLayers extendLocalizedPriorityLayer
  rw [List.map_map, List.map_map]
  have fold : ∀ (ext : List Nat → List Nat),
      (List.map (sparseEntryMap fun v : List Nat => v.getD 3 0) ∘
        List.map (extendLocalizedPriorityEntry ext)) =
      List.map ((sparseEntryMap fun v : List Nat => v.getD 3 0) ∘
        extendLocalizedPriorityEntry ext) := by
    intro ext
    funext layer
    simp only [Function.comp_apply, List.map_map]
  rw [fold, fold]
  apply compareSparseLayers_map_congr
  intro layer hl e he
  obtain ⟨label, _, hv⟩ := image layer hl e he
  obtain ⟨addr, v⟩ := e
  simp only at hv
  subst hv
  exact compareSparseEntry_extend5 τ₁ τ₂ addr _ _

/-- Key form of the fourth-column reduction. -/
theorem compare_extendKey5_eq_scalar5
    (image : LocalizedStageDescriptorImage (.rule4b ρ) LocalizedNoPseudoLabel key.descriptor)
    (τ₁ τ₂ : RS) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (input.extendLocalizedRerootCumulativeRule45Key
          (extendLocalizedRule4bPriorityToRule5 τ₁ .R) key).descriptor
        (input.extendLocalizedRerootCumulativeRule45Key
          (extendLocalizedRule4bPriorityToRule5 τ₂ .R) key).descriptor =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar5 (input.extendLocalizedRerootCumulativeRule45Key
          (extendLocalizedRule4bPriorityToRule5 τ₁ .R) key))
        (scalar5 (input.extendLocalizedRerootCumulativeRule45Key
          (extendLocalizedRule4bPriorityToRule5 τ₂ .R) key)) := by
  unfold scalar5
  rw [extendLocalizedRerootCumulativeRule45Key_descriptor,
    extendLocalizedRerootCumulativeRule45Key_descriptor]
  exact compare_extend5_eq_scalar5 image τ₁ τ₂

/-! ## The path first difference of the seniority functions -/

/-- **The common-`R` comparison of two extensions of one Rule-4b key is the path first difference
of their seniority functions.** -/
theorem compare_extend5_iff_pathFirstDifference
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) tree key)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (image : LocalizedStageDescriptorImage (.rule4b ρ) LocalizedNoPseudoLabel key.descriptor)
    (τ₁ τ₂ : RS) (outcome : Ordering) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (input.extendLocalizedRerootCumulativeRule45Key
          (extendLocalizedRule4bPriorityToRule5 τ₁ .R) key).descriptor
        (input.extendLocalizedRerootCumulativeRule45Key
          (extendLocalizedRule4bPriorityToRule5 τ₂ .R) key).descriptor = outcome ↔
      PathFirstDifferenceOf
        (fun path => seniority τ₁ (SparsePhysicalFirstDifference.tableValue (scalar4a key) path)
          (SparsePhysicalFirstDifference.tableValue (scalar4b key) path))
        (fun path => seniority τ₂ (SparsePhysicalFirstDifference.tableValue (scalar4a key) path)
          (SparsePhysicalFirstDifference.tableValue (scalar4b key) path)) outcome := by
  have wf := wellFormedRuleMajorKey_of_tableMatch tableMatch realizes
  rw [compare_extendKey5_eq_scalar5 image τ₁ τ₂]
  refine (later_compareSparseLayers_eq_firstDifference OfficialRuleMajorKey.compareNat rfl
    wf.wellFormed1a wf.wellFormed1a wf.positive1a wf.positive1a
    (CompilerProjectionFidelity.compareSparseLayers_self _
      CompilerProjectionFidelity.compareNat_self _)
    (scalar5_rows tableMatch τ₁) (scalar5_rows tableMatch τ₂)
    (scalar5_wellFormed tableMatch τ₁) (scalar5_wellFormed tableMatch τ₂) outcome).trans ?_
  refine (DeclarativeCIP.FirstDifferenceOutcome.congr (fun position result => ?_) outcome).trans
    (firstDifferenceOutcome_iff_pathFirstDifferenceOf _ _ outcome)
  rw [tableValue_scalar5 tableMatch τ₁ position, tableValue_scalar5 tableMatch τ₂ position]
  exact Iff.rfl

/-- **The own convention is senior exactly when the first chiral address carries `R`.** -/
theorem compare_extend5_gt_iff
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) tree key)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (image : LocalizedStageDescriptorImage (.rule4b ρ) LocalizedNoPseudoLabel key.descriptor) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (input.extendLocalizedRerootCumulativeRule45Key
          (extendLocalizedRule4bPriorityToRule5 ρ .R) key).descriptor
        (input.extendLocalizedRerootCumulativeRule45Key
          (extendLocalizedRule4bPriorityToRule5 (RS.swap ρ) .R) key).descriptor = .gt ↔
      ∃ path, SparsePhysicalFirstDifference.tableValue (scalar4a key) path = 2 ∧
        descriptorOfBit ρ (SparsePhysicalFirstDifference.tableValue (scalar4b key) path) = RS.R ∧
        ∀ earlier, Certificate.CanonicalSphereKey.AddressBefore earlier path →
          SparsePhysicalFirstDifference.tableValue (scalar4a key) earlier ≠ 2 := by
  rw [compare_extend5_iff_pathFirstDifference tableMatch realizes image ρ (RS.swap ρ) .gt]
  show (∃ path,
      seniority (RS.swap ρ) (SparsePhysicalFirstDifference.tableValue (scalar4a key) path)
          (SparsePhysicalFirstDifference.tableValue (scalar4b key) path) <
        seniority ρ (SparsePhysicalFirstDifference.tableValue (scalar4a key) path)
          (SparsePhysicalFirstDifference.tableValue (scalar4b key) path) ∧
      ∀ earlier, Certificate.CanonicalSphereKey.AddressBefore earlier path →
        seniority ρ (SparsePhysicalFirstDifference.tableValue (scalar4a key) earlier)
            (SparsePhysicalFirstDifference.tableValue (scalar4b key) earlier) =
          seniority (RS.swap ρ) (SparsePhysicalFirstDifference.tableValue (scalar4a key) earlier)
            (SparsePhysicalFirstDifference.tableValue (scalar4b key) earlier)) ↔ _
  simp only [seniority_swap_lt_iff, seniority_eq_iff, and_assoc]

/-! ## Readback through the represented Rule-4b column -/

/-- The encoded Rule-4b observation is a chiral code exactly at a chiral address, and the code is
the like bit there. -/
theorem encoded4b_eq_code_iff
    (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) tree key) (path : List Nat)
    (b : Nat) :
    encoded4b key path =
        (((code b : DeclarativeCIP.StereoCode) : DeclarativeCIP.StereoLabel) :
          WithBot DeclarativeCIP.StereoLabel) ↔
      SparsePhysicalFirstDifference.tableValue (scalar4a key) path = 2 ∧
        SparsePhysicalFirstDifference.tableValue (scalar4b key) path = b := by
  unfold encoded4b
  by_cases present : SparseSupportAlignment.HasAddress key.constitutional.rule1a path
  · rw [if_pos present]
    by_cases chiral : SparsePhysicalFirstDifference.tableValue (scalar4a key) path = 2
    · rw [if_pos chiral]
      simp only [chiral, true_and]
      constructor
      · intro h
        exact code_injective (WithBot.coe_inj.1 (WithBot.coe_inj.1 h))
      · intro h
        rw [h]
    · rw [if_neg chiral]
      simp only [chiral, false_and, iff_false]
      intro h
      exact WithBot.bot_ne_coe (WithBot.coe_inj.1 h)
  · rw [if_neg present]
    have absent : SparsePhysicalFirstDifference.tableValue (scalar4a key) path = 0 := by
      apply tableValue_eq_zero_of_not_hasAddress
      intro h
      exact present ((hasAddress_iff_of_sameAddressRows (scalar4a_rows_rule4b tableMatch) path).1 h)
    simp only [absent]
    constructor
    · intro h
      exact absurd h WithBot.bot_ne_coe
    · intro h
      omega

theorem encoded4b_not_code_iff
    (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) tree key) (path : List Nat) :
    (∀ b : Nat, encoded4b key path ≠
        (((code b : DeclarativeCIP.StereoCode) : DeclarativeCIP.StereoLabel) :
          WithBot DeclarativeCIP.StereoLabel)) ↔
      SparsePhysicalFirstDifference.tableValue (scalar4a key) path ≠ 2 := by
  constructor
  · intro h hk
    exact h (SparsePhysicalFirstDifference.tableValue (scalar4b key) path)
      ((encoded4b_eq_code_iff tableMatch path _).2 ⟨hk, rfl⟩)
  · intro hk b h
    exact hk ((encoded4b_eq_code_iff tableMatch path b).1 h).1

/-- **Independent readback of the decision.**  With the Rule-4b column represented by a sphere key
`K` (C1), the own convention is senior exactly when `K`, at its first chiral address in the
sphere-major order, carries the like code of `R`. -/
theorem compare_extend5_gt_iff_represented
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) tree key)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (image : LocalizedStageDescriptorImage (.rule4b ρ) LocalizedNoPseudoLabel key.descriptor)
    {W D : Nat} {K : Certificate.CanonicalSphereKey.Key DeclarativeCIP.StereoLabel}
    (rep : Represents4b W D K key) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (input.extendLocalizedRerootCumulativeRule45Key
          (extendLocalizedRule4bPriorityToRule5 ρ .R) key).descriptor
        (input.extendLocalizedRerootCumulativeRule45Key
          (extendLocalizedRule4bPriorityToRule5 (RS.swap ρ) .R) key).descriptor = .gt ↔
      ∃ path,
        Certificate.CanonicalSphereKey.pathObservationOf W D K path =
          (((code (if ρ = RS.R then 1 else 0) : DeclarativeCIP.StereoCode) :
            DeclarativeCIP.StereoLabel) : WithBot DeclarativeCIP.StereoLabel) ∧
        ∀ earlier, Certificate.CanonicalSphereKey.AddressBefore earlier path →
          ∀ b : Nat, Certificate.CanonicalSphereKey.pathObservationOf W D K earlier ≠
            (((code b : DeclarativeCIP.StereoCode) : DeclarativeCIP.StereoLabel) :
              WithBot DeclarativeCIP.StereoLabel) := by
  rw [compare_extend5_gt_iff tableMatch realizes image]
  constructor
  · rintro ⟨path, hk, hd, hbefore⟩
    refine ⟨path, ?_, ?_⟩
    · rw [rep path, encoded4b_eq_code_iff tableMatch]
      exact ⟨hk, (descriptorOfBit_eq_R_iff ρ (tableValue_scalar4b_le_one tableMatch path)).1 hd⟩
    · intro earlier hb
      rw [rep earlier, encoded4b_not_code_iff tableMatch]
      exact hbefore earlier hb
  · rintro ⟨path, hcode, hbefore⟩
    rw [rep path, encoded4b_eq_code_iff tableMatch] at hcode
    refine ⟨path, hcode.1,
      (descriptorOfBit_eq_R_iff ρ (tableValue_scalar4b_le_one tableMatch path)).2 hcode.2, ?_⟩
    intro earlier hb
    refine (encoded4b_not_code_iff tableMatch earlier).1 ?_
    intro b
    rw [← rep earlier]
    exact hbefore earlier hb b

end

end Rule4aTableBridge
end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.extendToRule5_getD_three
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.compare_extendKey5_eq_scalar5
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.compare_extend5_iff_pathFirstDifference
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.compare_extend5_gt_iff
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.compare_extend5_gt_iff_represented
