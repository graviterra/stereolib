import TetraStereo.OneCenter.LocalizedActualCanonicalConstitutionalRefinement
import TetraStereo.OneCenter.DeclarativeCIPStereoPathObservation
import TetraStereo.OneCenter.DeclarativeCIPMolecularEvidence
import TetraStereo.KernelOnly

set_option autoImplicit false


























namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

noncomputable section
open scoped Classical

open LocalizedCumulativeDecoratedTree
open CertifiedLocalizedCIPInput
open OfficialSparseCanonicalVectorComparison

/-! ## Entry payload maps commute with addressed-table compilation -/

/-- Apply a function to the payload of an addressed sparse entry. -/
def sparseEntryMap {α β : Type*} (project : α → β) (entry : OfficialSparseEntry α) :
    OfficialSparseEntry β :=
  (entry.1, project entry.2)

theorem sparseEntryMap_comp {α β γ : Type*} (f : α → β) (g : β → γ) (entry : OfficialSparseEntry α) :
    sparseEntryMap g (sparseEntryMap f entry) = sparseEntryMap (g ∘ f) entry := rfl

theorem sparseEntryMap_id {α : Type*} (entry : OfficialSparseEntry α) :
    sparseEntryMap id entry = entry := rfl

theorem prefixLayer_sparseEntryMap {α β : Type*} (project : α → β) (slot : Nat)
    (layer : List (OfficialSparseEntry α)) :
    (OfficialRuleMajorKey.prefixLayer slot layer).map (sparseEntryMap project) =
      OfficialRuleMajorKey.prefixLayer slot (layer.map (sparseEntryMap project)) := by
  induction layer with
  | nil => rfl
  | cons entry rest ih =>
      simp only [OfficialRuleMajorKey.prefixLayer, List.map_cons, sparseEntryMap] at ih ⊢
      rw [ih]

theorem mergePairs_sparseEntryMap {α β γ : Type*} (project : α → β) (pairs : List (γ × Nat))
    (block : γ → List (OfficialSparseEntry α)) :
    (SparseAddress.mergePairs pairs block).map (sparseEntryMap project) =
      SparseAddress.mergePairs pairs (fun value => (block value).map (sparseEntryMap project)) := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih =>
      show (OfficialRuleMajorKey.prefixLayer pair.2 (block pair.1) ++
          SparseAddress.mergePairs rest block).map (sparseEntryMap project) =
        OfficialRuleMajorKey.prefixLayer pair.2 ((block pair.1).map (sparseEntryMap project)) ++
          SparseAddress.mergePairs rest (fun value => (block value).map (sparseEntryMap project))
      rw [List.map_append, prefixLayer_sparseEntryMap, ih]

theorem getD_map_sparseEntryMap {α β : Type*} (project : α → β)
    (layers : List (List (OfficialSparseEntry α))) (depth : Nat) :
    (layers.map (List.map (sparseEntryMap project))).getD depth [] =
      (layers.getD depth []).map (sparseEntryMap project) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases layers[depth]? with
  | none => rfl
  | some layer => rfl

theorem localizedTreeChildLayerCount_sparseEntryMap {α β : Type*} (project : α → β)
    (tables : List (List (List (OfficialSparseEntry α)))) :
    localizedTreeChildLayerCount (tables.map (List.map (List.map (sparseEntryMap project)))) =
      localizedTreeChildLayerCount tables := by
  simp only [localizedTreeChildLayerCount, List.foldl_map, List.length_map]

theorem mergeLocalizedTreeChildTables_sparseEntryMap {α β : Type*} (project : α → β)
    (tables : List (List (List (OfficialSparseEntry α)))) :
    (mergeLocalizedTreeChildTables tables).map (List.map (sparseEntryMap project)) =
      mergeLocalizedTreeChildTables (tables.map (List.map (List.map (sparseEntryMap project)))) := by
  unfold mergeLocalizedTreeChildTables
  rw [mergePairTable_zipIdx_map_gen]
  rw [localizedTreeChildLayerCount_sparseEntryMap]
  simp only [SparseAddress.mergePairTable, List.map_map]
  apply List.map_congr_left
  intro depth _
  rw [Function.comp_apply, mergePairs_sparseEntryMap]
  congr 1
  funext value
  exact (getD_map_sparseEntryMap project value depth).symm

/-- **Payload maps commute with table compilation.** -/
theorem table_map {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} {α β : Type*}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → α) (project : α → β) :
    ∀ tree : LocalizedCumulativeDecoratedTree input carrierFuel,
      (table observe tree).map (List.map (sparseEntryMap project)) =
        table (fun node => project (observe node)) tree := by
  have main : ∀ n : Nat, ∀ tree : LocalizedCumulativeDecoratedTree input carrierFuel,
      LocalizedCumulativeDecoratedTree.height tree ≤ n →
      (table observe tree).map (List.map (sparseEntryMap project)) =
        table (fun node => project (observe node)) tree := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro k ih tree bound
    rw [table_eq_root_merge, table_eq_root_merge, List.map_append]
    congr 1
    rw [mergeLocalizedTreeChildTables_sparseEntryMap, List.map_map]
    congr 1
    apply List.map_congr_left
    intro child present
    have smaller := height_lt_height_of_mem tree present
    exact ih (LocalizedCumulativeDecoratedTree.height child) (by omega) child le_rfl
  intro tree
  exact main _ tree le_rfl

/-! ## Lexicographic comparison through entry maps -/

theorem compareLex_map_rel {α β : Type*} (cmpα : α → α → Ordering) (cmpβ : β → β → Ordering)
    (f : α → β) (respects : ∀ a b, cmpβ (f a) (f b) = cmpα a b) :
    ∀ xs ys : List α, List.compareLex cmpβ (xs.map f) (ys.map f) = List.compareLex cmpα xs ys
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
      simp only [List.map_cons, List.compareLex_cons_cons, respects, compareLex_map_rel cmpα cmpβ f respects xs ys]

/-- Singleton cumulative vectors compare as their scalar. -/
theorem compareCumulative_singleton (a b : Nat) :
    compareLocalizedCumulativeRule45Priority [a] [b] = OfficialRuleMajorKey.compareNat a b := by
  unfold compareLocalizedCumulativeRule45Priority
  simp only [List.compareLex_cons_cons, List.compareLex_nil_nil]
  cases OfficialRuleMajorKey.compareNat a b <;> rfl

/-- The actual cumulative-vector comparison of two singleton-vector tables is the scalar
`compareNat` comparison of their scalar tables. -/
theorem compareSparseLayers_map_single (T U : List (List (OfficialSparseEntry Nat))) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (T.map (List.map (sparseEntryMap fun p => [p])))
        (U.map (List.map (sparseEntryMap fun p => [p]))) =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat T U := by
  unfold OfficialRuleMajorKey.compareSparseLayers
  apply compareLex_map_rel
  intro l m
  unfold OfficialRuleMajorKey.compareSparseLayer
  apply compareLex_map_rel
  intro e f
  unfold OfficialRuleMajorKey.compareSparseEntry sparseEntryMap
  simp only [compareLex, Ordering.byKey, compareCumulative_singleton]

/-! ## The scalar Rule-4a table of a stage-`.rule4a` key -/

/-- The Rule-4a priority of a decorated node. -/
def prio4a {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (node : LocalizedCumulativeDecoratedTree input carrierFuel) : Nat :=
  localizedRule4aPriority node.label

/-- The stage-`.rule4a` descriptor table of a table-matched key is the singleton-vector image of
the scalar Rule-4a priority table. -/
theorem descriptor_eq_map_single {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (tableMatch : LocalizedCumulativeTreeTableMatch .rule4a tree key) :
    key.descriptor = (table prio4a tree).map (List.map (sparseEntryMap fun p => [p])) := by
  rw [← tableMatch.2.2.2, tables_descriptor, table_map]
  rfl

/-- Scalar projection of a cumulative descriptor table (first component, `0` if absent). -/
def scalar4a {input : CertifiedLocalizedCIPInput} (key : input.LocalizedRerootCumulativeRule45Key) :
    List (List (OfficialSparseEntry Nat)) :=
  key.descriptor.map (List.map (sparseEntryMap fun v => v.headD 0))

theorem scalar4a_eq_table {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (tableMatch : LocalizedCumulativeTreeTableMatch .rule4a tree key) :
    scalar4a key = table prio4a tree := by
  unfold scalar4a
  rw [descriptor_eq_map_single tableMatch, List.map_map]
  apply List.map_id''
  intro layer
  rw [Function.comp_apply, List.map_map]
  apply List.map_id''
  intro entry
  rfl

theorem scalar4a_wellFormed {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (tableMatch : LocalizedCumulativeTreeTableMatch .rule4a tree key) :
    SparsePhysicalFirstDifference.SparseTableWellFormed (scalar4a key) := by
  rw [scalar4a_eq_table tableMatch]
  exact LocalizedActualTableAddressOrder.table_wellFormed prio4a tree

theorem scalar4a_rows {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (tableMatch : LocalizedCumulativeTreeTableMatch .rule4a tree key) :
    SparseSupportAlignment.SameAddressRows (scalar4a key) key.constitutional.rule1a := by
  rw [scalar4a_eq_table tableMatch, ← tableMatch.1, tables_rule1a]
  exact LocalizedActualTableAddressOrder.SameAddressRows_table_observations prio4a
    (fun node => node.atomicNumber) tree

/-- The actual descriptor comparison of two stage-`.rule4a` keys is the scalar comparison of their
scalar tables. -/
theorem compare_descriptor_eq_scalar {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {tree₁ tree₂ : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key₁ key₂ : input.LocalizedRerootCumulativeRule45Key}
    (match₁ : LocalizedCumulativeTreeTableMatch .rule4a tree₁ key₁)
    (match₂ : LocalizedCumulativeTreeTableMatch .rule4a tree₂ key₂) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        key₁.descriptor key₂.descriptor =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4a key₁) (scalar4a key₂) := by
  rw [descriptor_eq_map_single match₁, descriptor_eq_map_single match₂,
    scalar4a_eq_table match₁, scalar4a_eq_table match₂]
  exact compareSparseLayers_map_single _ _

/-! ## Encoded Rule-4a observations -/

/-- The singleton stereo code carrying one priority at the empty relative address: the value
`stereoValue .rule4aStereogenicUnitKind` assigns to a present node of kind priority `p`. -/
def code (p : Nat) : DeclarativeCIP.StereoCode :=
  [[toLex (OrderDual.toDual ([] : List Nat), p)]]

theorem code_eq_encode (kind : DeclarativeCIP.StereogenicUnitKind) :
    DeclarativeCIP.encodeHierarchy DeclarativeCIP.StereogenicUnitKind.priority
      (DeclarativeCIP.singleEntry kind) = code kind.priority := rfl

theorem code_lt_iff {a b : Nat} : code a < code b ↔ a < b := by
  unfold code
  rw [List.cons_lt_cons_iff, List.cons_lt_cons_iff]
  constructor
  · rintro (h | ⟨_, h⟩)
    · rcases h with h | ⟨_, h⟩
      · rcases Prod.Lex.lt_iff.1 h with h | ⟨_, h⟩
        · exact absurd h (lt_irrefl _)
        · exact h
      · exact absurd h (List.not_lt_nil _)
    · exact absurd h (List.not_lt_nil _)
  · intro h
    exact Or.inl (Or.inl (Prod.Lex.lt_iff.2 (Or.inr ⟨rfl, h⟩)))

theorem code_injective {a b : Nat} (h : code a = code b) : a = b := by
  unfold code at h
  simp at h
  exact h

/-- Encoded Rule-4a observation of an actual key at an address: `⊥` off the Rule-1a support,
otherwise the present stereo label carrying the scalar Rule-4a priority. -/
def encoded4a {input : CertifiedLocalizedCIPInput} (key : input.LocalizedRerootCumulativeRule45Key)
    (path : List Nat) : WithBot DeclarativeCIP.StereoLabel :=
  if SparseSupportAlignment.HasAddress key.constitutional.rule1a path then
    (((code (SparsePhysicalFirstDifference.tableValue (scalar4a key) path) :
      DeclarativeCIP.StereoCode) : DeclarativeCIP.StereoLabel) : WithBot DeclarativeCIP.StereoLabel)
  else ⊥

/-! ## Path-level first differences for an arbitrary linear order -/

/-- Path-level first difference under the canonical shortlex address order. -/
def PathFirstDifferenceOf {α : Type*} [LinearOrder α] (left right : List Nat → α) :
    Ordering → Prop
  | Ordering.eq => ∀ path, left path = right path
  | Ordering.lt =>
      ∃ path, left path < right path ∧
        ∀ earlier, Certificate.CanonicalSphereKey.AddressBefore earlier path →
          left earlier = right earlier
  | Ordering.gt =>
      ∃ path, right path < left path ∧
        ∀ earlier, Certificate.CanonicalSphereKey.AddressBefore earlier path →
          left earlier = right earlier

theorem firstDifferenceOutcome_iff_pathFirstDifferenceOf {α : Type*} [LinearOrder α]
    (left right : List Nat → α) (outcome : Ordering) :
    DeclarativeCIP.FirstDifferenceOutcome
        (fun path result => compare (left path) (right path) = result) outcome ↔
      PathFirstDifferenceOf left right outcome := by
  cases outcome with
  | eq =>
      change (∀ path, compare (left path) (right path) = Ordering.eq) ↔
        (∀ path, left path = right path)
      exact forall_congr' fun path => compare_eq_iff_eq
  | lt =>
      change (∃ path, compare (left path) (right path) = Ordering.lt ∧
          ∀ earlier, DeclarativeCIP.HierarchyAddressBefore earlier path →
            compare (left earlier) (right earlier) = Ordering.eq) ↔
        (∃ path, left path < right path ∧
          ∀ earlier, Certificate.CanonicalSphereKey.AddressBefore earlier path →
            left earlier = right earlier)
      constructor
      · rintro ⟨path, decided, earlierTied⟩
        exact ⟨path, compare_lt_iff_lt.1 decided, fun earlier before => compare_eq_iff_eq.1
          (earlierTied earlier ((addressBefore_iff_hierarchyAddressBefore earlier path).mp before))⟩
      · rintro ⟨path, decided, earlierTied⟩
        exact ⟨path, compare_lt_iff_lt.2 decided, fun earlier before => compare_eq_iff_eq.2
          (earlierTied earlier ((addressBefore_iff_hierarchyAddressBefore earlier path).mpr before))⟩
  | gt =>
      change (∃ path, compare (left path) (right path) = Ordering.gt ∧
          ∀ earlier, DeclarativeCIP.HierarchyAddressBefore earlier path →
            compare (left earlier) (right earlier) = Ordering.eq) ↔
        (∃ path, right path < left path ∧
          ∀ earlier, Certificate.CanonicalSphereKey.AddressBefore earlier path →
            left earlier = right earlier)
      constructor
      · rintro ⟨path, decided, earlierTied⟩
        exact ⟨path, compare_gt_iff_gt.1 decided, fun earlier before => compare_eq_iff_eq.1
          (earlierTied earlier ((addressBefore_iff_hierarchyAddressBefore earlier path).mp before))⟩
      · rintro ⟨path, decided, earlierTied⟩
        exact ⟨path, compare_gt_iff_gt.2 decided, fun earlier before => compare_eq_iff_eq.2
          (earlierTied earlier ((addressBefore_iff_hierarchyAddressBefore earlier path).mpr before))⟩

/-! ## The Rule-4a column after a Rule-1a tie -/

/-- Pointwise: on a shared support the encoded observations compare as the scalar values; off it
both are `⊥` and both scalars are `0`. -/
theorem compare_encoded4a {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {tree₁ tree₂ : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key₁ key₂ : input.LocalizedRerootCumulativeRule45Key}
    (match₁ : LocalizedCumulativeTreeTableMatch .rule4a tree₁ key₁)
    (match₂ : LocalizedCumulativeTreeTableMatch .rule4a tree₂ key₂)
    (support : ∀ path, SparseSupportAlignment.HasAddress key₁.constitutional.rule1a path ↔
      SparseSupportAlignment.HasAddress key₂.constitutional.rule1a path)
    (path : List Nat) :
    compare (encoded4a key₁ path) (encoded4a key₂ path) =
      OfficialRuleMajorKey.compareNat
        (SparsePhysicalFirstDifference.tableValue (scalar4a key₁) path)
        (SparsePhysicalFirstDifference.tableValue (scalar4a key₂) path) := by
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
      fun h => present ((hasAddress_iff_of_sameAddressRows (scalar4a_rows match₁) path).mp h)
    have abs₂ : ¬ SparseSupportAlignment.HasAddress (scalar4a key₂) path :=
      fun h => absent₂ ((hasAddress_iff_of_sameAddressRows (scalar4a_rows match₂) path).mp h)
    rw [tableValue_eq_zero_of_not_hasAddress abs₁, tableValue_eq_zero_of_not_hasAddress abs₂,
      compare_eq_iff_eq.2 rfl]

/-- **The executed Rule-4a column, after a Rule-1a tie, is the path-level first difference of the
encoded Rule-4a observations.** -/
theorem rule4a_pathFirstDifference_iff {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree₁ tree₂ : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key₁ key₂ : input.LocalizedRerootCumulativeRule45Key}
    (match₁ : LocalizedCumulativeTreeTableMatch .rule4a tree₁ key₁)
    (match₂ : LocalizedCumulativeTreeTableMatch .rule4a tree₂ key₂)
    (realizes₁ : LocalizedCumulativeTreeRealizes input read tree₁)
    (realizes₂ : LocalizedCumulativeTreeRealizes input read tree₂)
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
  exact (later_compareSparseLayers_eq_firstDifference OfficialRuleMajorKey.compareNat rfl
      wf₁.wellFormed1a wf₂.wellFormed1a wf₁.positive1a wf₂.positive1a tied
      (scalar4a_rows match₁) (scalar4a_rows match₂)
      (scalar4a_wellFormed match₁) (scalar4a_wellFormed match₂) outcome).trans
    ((DeclarativeCIP.FirstDifferenceOutcome.congr (fun position result =>
      by rw [compare_encoded4a match₁ match₂ support position]) outcome).trans
      (firstDifferenceOutcome_iff_pathFirstDifferenceOf _ _ outcome))

/-! ## Representation by a Rule-4a sphere key -/

/-! ### Core `compare` on stereo keys is the lexicographic order -/

theorem stereoLabelCompare_eq_iff (left right : WithBot DeclarativeCIP.StereoLabel) :
    compare left right = Ordering.eq ↔ left = right := compare_eq_iff_eq
theorem stereoLabelCompare_lt_iff (left right : WithBot DeclarativeCIP.StereoLabel) :
    compare left right = Ordering.lt ↔ left < right := compare_lt_iff_lt
theorem stereoLabelCompare_gt_iff (left right : WithBot DeclarativeCIP.StereoLabel) :
    compare left right = Ordering.gt ↔ right < left := compare_gt_iff_gt

theorem stereoLevelCompare_eq_iff
    (left right : Certificate.CanonicalSphereKey.Level DeclarativeCIP.StereoLabel) :
    compare left right = Ordering.eq ↔ left = right :=
  (listCompareLex_iff_lex (cmp := compare) (fun a b => stereoLabelCompare_eq_iff a b)
    (fun a b => stereoLabelCompare_lt_iff a b) (fun a b => stereoLabelCompare_gt_iff a b)
    left right).2.2
theorem stereoLevelCompare_lt_iff
    (left right : Certificate.CanonicalSphereKey.Level DeclarativeCIP.StereoLabel) :
    compare left right = Ordering.lt ↔ left < right :=
  (listCompareLex_iff_lex (cmp := compare) (fun a b => stereoLabelCompare_eq_iff a b)
    (fun a b => stereoLabelCompare_lt_iff a b) (fun a b => stereoLabelCompare_gt_iff a b)
    left right).1
theorem stereoLevelCompare_gt_iff
    (left right : Certificate.CanonicalSphereKey.Level DeclarativeCIP.StereoLabel) :
    compare left right = Ordering.gt ↔ right < left :=
  (listCompareLex_iff_lex (cmp := compare) (fun a b => stereoLabelCompare_eq_iff a b)
    (fun a b => stereoLabelCompare_lt_iff a b) (fun a b => stereoLabelCompare_gt_iff a b)
    left right).2.1

theorem stereoKeyCompare_eq_iff
    (left right : Certificate.CanonicalSphereKey.Key DeclarativeCIP.StereoLabel) :
    compare left right = Ordering.eq ↔ left = right :=
  (listCompareLex_iff_lex (cmp := compare) (fun a b => stereoLevelCompare_eq_iff a b)
    (fun a b => stereoLevelCompare_lt_iff a b) (fun a b => stereoLevelCompare_gt_iff a b)
    left right).2.2
theorem stereoKeyCompare_lt_iff
    (left right : Certificate.CanonicalSphereKey.Key DeclarativeCIP.StereoLabel) :
    compare left right = Ordering.lt ↔ left < right :=
  (listCompareLex_iff_lex (cmp := compare) (fun a b => stereoLevelCompare_eq_iff a b)
    (fun a b => stereoLevelCompare_lt_iff a b) (fun a b => stereoLevelCompare_gt_iff a b)
    left right).1
theorem stereoKeyCompare_gt_iff
    (left right : Certificate.CanonicalSphereKey.Key DeclarativeCIP.StereoLabel) :
    compare left right = Ordering.gt ↔ right < left :=
  (listCompareLex_iff_lex (cmp := compare) (fun a b => stereoLevelCompare_eq_iff a b)
    (fun a b => stereoLevelCompare_lt_iff a b) (fun a b => stereoLevelCompare_gt_iff a b)
    left right).2.1

/-- A sphere key over stereo labels represents an actual key's Rule-4a column pointwise. -/
def Represents4a (W D : Nat) (key4a : Certificate.CanonicalSphereKey.Key DeclarativeCIP.StereoLabel)
    {input : CertifiedLocalizedCIPInput} (key : input.LocalizedRerootCumulativeRule45Key) : Prop :=
  ∀ path, Certificate.CanonicalSphereKey.pathObservationOf W D key4a path = encoded4a key path

/-- **The actual Rule-4a descriptor comparison is the sphere-key comparison** of any two
well-shaped representing keys, after a Rule-1a tie. -/
theorem compare_descriptor_eq_compare_key {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree₁ tree₂ : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key₁ key₂ : input.LocalizedRerootCumulativeRule45Key}
    (match₁ : LocalizedCumulativeTreeTableMatch .rule4a tree₁ key₁)
    (match₂ : LocalizedCumulativeTreeTableMatch .rule4a tree₂ key₂)
    (realizes₁ : LocalizedCumulativeTreeRealizes input read tree₁)
    (realizes₂ : LocalizedCumulativeTreeRealizes input read tree₂)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      key₁.constitutional.rule1a key₂.constitutional.rule1a = Ordering.eq)
    {W D : Nat} {K₁ K₂ : Certificate.CanonicalSphereKey.Key DeclarativeCIP.StereoLabel}
    (shaped₁ : Certificate.CanonicalSphereKey.WellShaped W D K₁)
    (shaped₂ : Certificate.CanonicalSphereKey.WellShaped W D K₂)
    (rep₁ : Represents4a W D K₁ key₁) (rep₂ : Represents4a W D K₂ key₂) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        key₁.descriptor key₂.descriptor = compare K₁ K₂ := by
  rw [compare_descriptor_eq_scalar match₁ match₂]
  cases h : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4a key₁) (scalar4a key₂) with
  | lt =>
      obtain ⟨path, decisive, earlierTied⟩ :=
        (rule4a_pathFirstDifference_iff match₁ match₂ realizes₁ realizes₂ tied Ordering.lt).1 h
      symm
      rw [stereoKeyCompare_lt_iff]
      refine (Certificate.CanonicalSphereKey.key_lt_iff_pathObservation shaped₁ shaped₂).2
        ⟨path, ?_, ?_⟩
      · rw [rep₁ path, rep₂ path]; exact decisive
      · intro earlier before
        rw [rep₁ earlier, rep₂ earlier]; exact earlierTied earlier before
  | gt =>
      obtain ⟨path, decisive, earlierTied⟩ :=
        (rule4a_pathFirstDifference_iff match₁ match₂ realizes₁ realizes₂ tied Ordering.gt).1 h
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
      exact (rule4a_pathFirstDifference_iff match₁ match₂ realizes₁ realizes₂ tied Ordering.eq).1
        h path

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.table_map
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.compareSparseLayers_map_single
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.compare_descriptor_eq_scalar
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.code_lt_iff
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.rule4a_pathFirstDifference_iff
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.compare_descriptor_eq_compare_key
