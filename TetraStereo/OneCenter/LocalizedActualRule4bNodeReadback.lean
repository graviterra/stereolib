import TetraStereo.OneCenter.LocalizedActualRule4bTableBridge
import TetraStereo.OneCenter.LocalizedActualRule4aNodeReadback
import TetraStereo.OneCenter.DeclarativeCIPReadingKeyProjection
import TetraStereo.OneCenter.LocalizedActualReferenceSelectionBridge
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Node readback of a stage-`.rule4b ρ` key

The stage-`.rule4b ρ` analogue of `LocalizedActualRule4aNodeReadback`: the encoded Rule-4a and
Rule-4b observations of a table-matched realized key at the empty address and one sphere further
out, the independent Rule-4b label of the molecular reading under `readingEvidence (senseOf ρ)`,
and the triple-key order of two siblings whose actual comparison is not `lt`.
-/

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open LocalizedCumulativeDecoratedTree
open CertifiedLocalizedCIPInput
open CertifiedLocalizedCIPInput.OriginalRootArm
open OfficialSparseCanonicalVectorComparison
open DeclarativeCIP

noncomputable section
open scoped Classical

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
  {dsub : LocalizedCumulativeDecoratedTree input carrierFuel}
  {key : input.LocalizedRerootCumulativeRule45Key} {ρ : RS}

/-! ## Encoded observations at the node and one sphere out -/

theorem encoded4a_nil_rule4b (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) dsub key)
    (realizes : LocalizedCumulativeTreeRealizes input read dsub) :
    encoded4a key [] = (((code (prio4a dsub) : StereoCode) : StereoLabel) : WithBot StereoLabel) := by
  unfold encoded4a
  have hpresent : SparseSupportAlignment.HasAddress key.constitutional.rule1a [] := by
    have viaTable : SparseSupportAlignment.HasAddress
        (table (fun node => node.atomicNumber) dsub) [] :=
      (hasAddress_atomicNumber_table_iff_subtree realizes []).2 ⟨dsub, rfl⟩
    simpa [← tableMatch.1, tables_rule1a] using viaTable
  rw [if_pos hpresent, scalar4a_eq_table_rule4b tableMatch, tableValue_table_eq_observeAt prio4a dsub []]
  rfl

theorem encoded4b_nil (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) dsub key)
    (realizes : LocalizedCumulativeTreeRealizes input read dsub) :
    encoded4b key [] =
      ((if prio4a dsub = 2 then ((code (bit4b ρ dsub) : StereoCode) : StereoLabel)
        else (⊥ : StereoLabel)) : WithBot StereoLabel) := by
  unfold encoded4b
  have hpresent : SparseSupportAlignment.HasAddress key.constitutional.rule1a [] := by
    have viaTable : SparseSupportAlignment.HasAddress
        (table (fun node => node.atomicNumber) dsub) [] :=
      (hasAddress_atomicNumber_table_iff_subtree realizes []).2 ⟨dsub, rfl⟩
    simpa [← tableMatch.1, tables_rule1a] using viaTable
  rw [if_pos hpresent, scalar4a_eq_table_rule4b tableMatch, scalar4b_eq_table tableMatch,
    tableValue_table_eq_observeAt prio4a dsub [], tableValue_table_eq_observeAt (bit4b ρ) dsub []]
  rfl

/-- The shared `cons` step of both encodings: on the Rule-1a support of `digit :: path` the
child at slot `digit` is present and matched; off it, the child's address is off its own support. -/
private theorem cons_support (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) dsub key)
    (realizes : LocalizedCumulativeTreeRealizes input read dsub)
    {sortedKeys : List input.LocalizedRerootCumulativeRule45Key}
    (paired : List.Forall₂ (fun childKey childTree =>
        LocalizedCumulativeTreeTableMatch (.rule4b ρ) childTree childKey ∧
          LocalizedCumulativeTreeRealizes input read childTree) sortedKeys dsub.children)
    (digit : Nat) (path : List Nat) :
    (SparseSupportAlignment.HasAddress key.constitutional.rule1a (digit :: path) →
      ∃ (hd : digit < dsub.children.length) (hk : digit < sortedKeys.length),
        SparseSupportAlignment.HasAddress (sortedKeys[digit]'hk).constitutional.rule1a path ∧
        LocalizedCumulativeTreeTableMatch (.rule4b ρ) (dsub.children[digit]'hd) (sortedKeys[digit]'hk) ∧
        LocalizedCumulativeTreeRealizes input read (dsub.children[digit]'hd) ∧
        dsub.decoratedSubtreeAt? (digit :: path) = (dsub.children[digit]'hd).decoratedSubtreeAt? path) ∧
    (¬ SparseSupportAlignment.HasAddress key.constitutional.rule1a (digit :: path) →
      ∀ (hk : digit < sortedKeys.length),
        ¬ SparseSupportAlignment.HasAddress (sortedKeys[digit]'hk).constitutional.rule1a path) := by
  have keysLength : sortedKeys.length = dsub.children.length := List.Forall₂.length_eq paired
  constructor
  · intro hpresent
    have guardTable : SparseSupportAlignment.HasAddress
        (table (fun node => node.atomicNumber) dsub) (digit :: path) := by
      simpa [← tableMatch.1, tables_rule1a] using hpresent
    obtain ⟨subtree, subtreeLookup⟩ :=
      (hasAddress_atomicNumber_table_iff_subtree realizes (digit :: path)).1 guardTable
    obtain ⟨child, subtree', childGet, childPath⟩ :=
      (decoratedSubtreeAt?_cons_some dsub digit path).1 ⟨subtree, subtreeLookup⟩
    have hd : digit < dsub.children.length := (List.getElem?_eq_some_iff.1 childGet).1
    have hk : digit < sortedKeys.length := by omega
    have childIs : child = dsub.children[digit]'hd :=
      (Option.some.inj ((List.getElem?_eq_getElem hd).symm.trans childGet)).symm
    have slotPaired := List.Forall₂.get (i := digit) paired hk hd
    simp only [List.get_eq_getElem] at slotPaired
    have childSubtree : (dsub.children[digit]'hd).decoratedSubtreeAt? path = some subtree' := by
      simpa [childIs] using childPath
    refine ⟨hd, hk, ?_, slotPaired.1, slotPaired.2, ?_⟩
    · have viaChildTable : SparseSupportAlignment.HasAddress
          (table (fun node => node.atomicNumber) (dsub.children[digit]'hd)) path :=
        (hasAddress_atomicNumber_table_iff_subtree slotPaired.2 path).2 ⟨subtree', childSubtree⟩
      have h1 := slotPaired.1.1
      rw [tables_rule1a] at h1
      rw [← h1]
      exact viaChildTable
    · rw [decoratedSubtreeAt?, childGet, childIs]
  · intro hpresent hk childGuard
    apply hpresent
    have hd : digit < dsub.children.length := by omega
    have slotPaired := List.Forall₂.get (i := digit) paired hk hd
    simp only [List.get_eq_getElem] at slotPaired
    have viaChildTable : SparseSupportAlignment.HasAddress
        (table (fun node => node.atomicNumber) (dsub.children[digit]'hd)) path := by
      have h1 := slotPaired.1.1
      rw [tables_rule1a] at h1
      rw [h1]
      exact childGuard
    obtain ⟨subtree', childPath⟩ :=
      (hasAddress_atomicNumber_table_iff_subtree slotPaired.2 path).1 viaChildTable
    have lookup : ∃ subtree, dsub.decoratedSubtreeAt? (digit :: path) = some subtree :=
      (decoratedSubtreeAt?_cons_some dsub digit path).2
        ⟨_, subtree', List.getElem?_eq_getElem hd, childPath⟩
    have viaTable := (hasAddress_atomicNumber_table_iff_subtree realizes (digit :: path)).2 lookup
    simpa [← tableMatch.1, tables_rule1a] using viaTable

theorem encoded4a_cons_of_key_rule4b (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) dsub key)
    (realizes : LocalizedCumulativeTreeRealizes input read dsub)
    {sortedKeys : List input.LocalizedRerootCumulativeRule45Key}
    (paired : List.Forall₂ (fun childKey childTree =>
        LocalizedCumulativeTreeTableMatch (.rule4b ρ) childTree childKey ∧
          LocalizedCumulativeTreeRealizes input read childTree) sortedKeys dsub.children)
    (digit : Nat) (path : List Nat) :
    encoded4a key (digit :: path) =
      ((sortedKeys[digit]?).map fun childKey => encoded4a childKey path).getD ⊥ := by
  obtain ⟨present, absent⟩ := cons_support tableMatch realizes paired digit path
  unfold encoded4a
  by_cases hpresent : SparseSupportAlignment.HasAddress key.constitutional.rule1a (digit :: path)
  · obtain ⟨hd, hk, childGuard, matchC, realizesC, lookupEq⟩ := present hpresent
    rw [if_pos hpresent, List.getElem?_eq_getElem hk]
    simp only [Option.map_some, Option.getD_some]
    rw [if_pos childGuard]
    congr 3
    rw [scalar4a_eq_table_rule4b tableMatch, scalar4a_eq_table_rule4b matchC,
      tableValue_table_eq_observeAt, tableValue_table_eq_observeAt]
    unfold observeAt
    rw [lookupEq]
  · rw [if_neg hpresent]
    cases keysGet : sortedKeys[digit]? with
    | none => rfl
    | some childKey =>
        simp only [Option.map_some, Option.getD_some]
        have hk : digit < sortedKeys.length := (List.getElem?_eq_some_iff.1 keysGet).1
        have childKeyIs : childKey = sortedKeys[digit]'hk :=
          Option.some.inj (keysGet.symm.trans (List.getElem?_eq_getElem hk))
        rw [childKeyIs, if_neg (absent hpresent hk)]

theorem encoded4b_cons_of_key (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) dsub key)
    (realizes : LocalizedCumulativeTreeRealizes input read dsub)
    {sortedKeys : List input.LocalizedRerootCumulativeRule45Key}
    (paired : List.Forall₂ (fun childKey childTree =>
        LocalizedCumulativeTreeTableMatch (.rule4b ρ) childTree childKey ∧
          LocalizedCumulativeTreeRealizes input read childTree) sortedKeys dsub.children)
    (digit : Nat) (path : List Nat) :
    encoded4b key (digit :: path) =
      ((sortedKeys[digit]?).map fun childKey => encoded4b childKey path).getD ⊥ := by
  obtain ⟨present, absent⟩ := cons_support tableMatch realizes paired digit path
  unfold encoded4b
  by_cases hpresent : SparseSupportAlignment.HasAddress key.constitutional.rule1a (digit :: path)
  · obtain ⟨hd, hk, childGuard, matchC, realizesC, lookupEq⟩ := present hpresent
    rw [if_pos hpresent, List.getElem?_eq_getElem hk]
    simp only [Option.map_some, Option.getD_some]
    rw [if_pos childGuard]
    have h4a : SparsePhysicalFirstDifference.tableValue (scalar4a key) (digit :: path) =
        SparsePhysicalFirstDifference.tableValue (scalar4a (sortedKeys[digit]'hk)) path := by
      rw [scalar4a_eq_table_rule4b tableMatch, scalar4a_eq_table_rule4b matchC,
        tableValue_table_eq_observeAt, tableValue_table_eq_observeAt]
      unfold observeAt
      rw [lookupEq]
    have h4b : SparsePhysicalFirstDifference.tableValue (scalar4b key) (digit :: path) =
        SparsePhysicalFirstDifference.tableValue (scalar4b (sortedKeys[digit]'hk)) path := by
      rw [scalar4b_eq_table tableMatch, scalar4b_eq_table matchC,
        tableValue_table_eq_observeAt, tableValue_table_eq_observeAt]
      unfold observeAt
      rw [lookupEq]
    rw [h4a, h4b]
  · rw [if_neg hpresent]
    cases keysGet : sortedKeys[digit]? with
    | none => rfl
    | some childKey =>
        simp only [Option.map_some, Option.getD_some]
        have hk : digit < sortedKeys.length := (List.getElem?_eq_some_iff.1 keysGet).1
        have childKeyIs : childKey = sortedKeys[digit]'hk :=
          Option.some.inj (keysGet.symm.trans (List.getElem?_eq_getElem hk))
        rw [childKeyIs, if_neg (absent hpresent hk)]

/-! ## The independent Rule-4b label of a molecular reading -/

variable (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (unit : DetectedOccurrence input.moleculeGraph) (graph : RootedDigraph input.Atom)

/-- The Rule-4a label is the same under the reading evidence and the rank evidence. -/
theorem stereoLabel_readingEvidence_rule4a (reference : DescriptorSense) (node : graph.Node) :
    stereoLabel graph (readingEvidence input.moleculeGraph descriptorMap unit graph reference)
        .rule4aStereogenicUnitKind node =
      stereoLabel graph (rankEvidence input.moleculeGraph descriptorMap unit graph)
        .rule4aStereogenicUnitKind node := rfl

/-- The Rule-4b label: the like/unlike code at eligible nodes, `⊥` elsewhere. -/
theorem stereoLabel_readingEvidence_rule4b (reference : DescriptorSense) (node : graph.Node) :
    stereoLabel graph (readingEvidence input.moleculeGraph descriptorMap unit graph reference)
        .rule4bLikeUnlikeDescriptorPairs node =
      match eligibleSense input.moleculeGraph descriptorMap unit graph node with
      | some observed => ((code (DescriptorPairKind.ofSenses reference observed).priority :
          StereoCode) : StereoLabel)
      | none => ⊥ := by
  unfold stereoLabel stereoValue readingEvidence
  cases eligibleSense input.moleculeGraph descriptorMap unit graph node <;> rfl

/-- The runtime Rule-4b bit of a tetrahedral reading is the like/unlike priority of its sense
against `senseOf ρ`; non-eligible readings have bit `0`. -/
theorem rule4bPriority_toLocalizedLabel (reading : OccurrenceReading) (htetra : reading.IsTetrahedral)
    (ρ : RS) :
    localizedRule4bPriority ρ reading.toLocalizedLabel =
      match readingSense reading with
      | some observed => (DescriptorPairKind.ofSenses (senseOf ρ) observed).priority
      | none => 0 := by
  cases reading with
  | descriptor value =>
      cases value <;> cases ρ <;>
        simp [OccurrenceReading.toLocalizedLabel, Descriptor.toLocalizedLabel, readingSense,
          Descriptor.chiralSense, senseOf, DescriptorPairKind.ofSenses, DescriptorPairKind.priority,
          localizedRule4bPriority, OccurrenceReading.IsTetrahedral, Descriptor.IsTetrahedral] at htetra ⊢
  | outsideInventory => cases ρ <;> rfl
  | unassigned => cases ρ <;> rfl
  | unavailable => cases ρ <;> rfl

/-- A tetrahedral reading is eligible exactly when its Rule-4a kind priority is `2`. -/
theorem kindPriority_eq_two_iff (reading : OccurrenceReading) (htetra : reading.IsTetrahedral) :
    localizedRule4aPriority reading.toLocalizedLabel = 2 ↔ (readingSense reading).isSome := by
  cases reading with
  | descriptor value =>
      cases value <;>
        simp [OccurrenceReading.toLocalizedLabel, Descriptor.toLocalizedLabel, readingSense,
          Descriptor.chiralSense, localizedRule4aPriority, OccurrenceReading.IsTetrahedral,
          Descriptor.IsTetrahedral] at htetra ⊢
  | outsideInventory => simp [OccurrenceReading.toLocalizedLabel, readingSense, localizedRule4aPriority]
  | unassigned => simp [OccurrenceReading.toLocalizedLabel, readingSense, localizedRule4aPriority]
  | unavailable => simp [OccurrenceReading.toLocalizedLabel, readingSense, localizedRule4aPriority]

/-- The independent Rule-4b observation at the empty path equals the encoded actual observation. -/
theorem stereoNodePathObservation_nil_eq_encoded4b (W D : Nat) (node : graph.Node)
    (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) dsub key)
    (realizes : LocalizedCumulativeTreeRealizes input read dsub)
    (hlabel : dsub.label =
      (occurrenceReading input.moleculeGraph descriptorMap unit graph node).toLocalizedLabel)
    (htetra : (occurrenceReading input.moleculeGraph descriptorMap unit graph node).IsTetrahedral) :
    stereoNodePathObservation input.moleculeGraph graph
        (readingEvidence input.moleculeGraph descriptorMap unit graph (senseOf ρ)) W D
        .rule4bLikeUnlikeDescriptorPairs node [] = encoded4b key [] := by
  rw [stereoNodePathObservation_nil, encoded4b_nil tableMatch realizes,
    stereoLabel_readingEvidence_rule4b]
  have hsense : eligibleSense input.moleculeGraph descriptorMap unit graph node =
      readingSense (occurrenceReading input.moleculeGraph descriptorMap unit graph node) := rfl
  rw [hsense]
  unfold prio4a bit4b
  rw [hlabel, rule4bPriority_toLocalizedLabel _ htetra]
  by_cases h2 : localizedRule4aPriority
      (occurrenceReading input.moleculeGraph descriptorMap unit graph node).toLocalizedLabel = 2
  · rw [if_pos h2]
    have hsome := (kindPriority_eq_two_iff _ htetra).1 h2
    cases hs : readingSense (occurrenceReading input.moleculeGraph descriptorMap unit graph node) with
    | none => rw [hs] at hsome; simp at hsome
    | some observed => rfl
  · rw [if_neg h2]
    have hnone : readingSense (occurrenceReading input.moleculeGraph descriptorMap unit graph node) =
        none := by
      cases hs : readingSense (occurrenceReading input.moleculeGraph descriptorMap unit graph node) with
      | none => rfl
      | some observed =>
          exfalso
          exact h2 ((kindPriority_eq_two_iff _ htetra).2 (by rw [hs]; rfl))
    rw [hnone]

/-- The independent Rule-4a observation at the empty path equals the encoded actual observation
(stage-`.rule4b ρ` key, reading evidence). -/
theorem stereoNodePathObservation_nil_eq_encoded4a_rule4b (W D : Nat) (node : graph.Node)
    (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4b ρ) dsub key)
    (realizes : LocalizedCumulativeTreeRealizes input read dsub)
    (hlabel : dsub.label =
      (occurrenceReading input.moleculeGraph descriptorMap unit graph node).toLocalizedLabel)
    (htetra : (occurrenceReading input.moleculeGraph descriptorMap unit graph node).IsTetrahedral)
    (havail : occurrenceReading input.moleculeGraph descriptorMap unit graph node ≠ .unavailable)
    (reference : DescriptorSense) :
    stereoNodePathObservation input.moleculeGraph graph
        (readingEvidence input.moleculeGraph descriptorMap unit graph reference) W D
        .rule4aStereogenicUnitKind node [] = encoded4a key [] := by
  rw [stereoNodePathObservation_nil, encoded4a_nil_rule4b tableMatch realizes,
    stereoLabel_readingEvidence_rule4a, stereoLabel_rankEvidence_rule4a descriptorMap unit graph node
    havail, prio4a_eq_kindPriority dsub _ hlabel htetra]

/-! ## Sibling order from the actual comparison -/

/-- A lexicographic `then`-chain of three comparators that is not `lt` yields the reversed
lexicographic `≤` on the triple, for any comparators characterised by `eq` and `gt`. -/
theorem lex_le_of_then_ne_lt {α β γ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ]
    (cmpα : α → α → Ordering) (cmpβ : β → β → Ordering) (cmpγ : γ → γ → Ordering)
    (eqα : ∀ x y, cmpα x y = Ordering.eq ↔ x = y) (gtα : ∀ x y, cmpα x y = Ordering.gt ↔ y < x)
    (eqβ : ∀ x y, cmpβ x y = Ordering.eq ↔ x = y) (gtβ : ∀ x y, cmpβ x y = Ordering.gt ↔ y < x)
    (eqγ : ∀ x y, cmpγ x y = Ordering.eq ↔ x = y) (gtγ : ∀ x y, cmpγ x y = Ordering.gt ↔ y < x)
    {a a' : α} {b b' : β} {c c' : γ}
    (h : (cmpα a a').then ((cmpβ b b').then (cmpγ c c')) ≠ Ordering.lt) :
    (toLex (a', toLex (b', c')) : Lex (α × Lex (β × γ))) ≤ toLex (a, toLex (b, c)) := by
  rcases ha : cmpα a a' with _ | _ | _
  · rw [ha] at h; exact absurd rfl h
  · have hae : a = a' := (eqα a a').1 ha
    subst hae
    rw [ha] at h
    simp only [Ordering.then] at h
    rcases hb : cmpβ b b' with _ | _ | _
    · rw [hb] at h; exact absurd rfl h
    · have hbe : b = b' := (eqβ b b').1 hb
      subst hbe
      rw [hb] at h
      simp only at h
      have hc : c' ≤ c := by
        rcases hcc : cmpγ c c' with _ | _ | _
        · rw [hcc] at h; exact absurd rfl h
        · exact ((eqγ c c').1 hcc).symm.le
        · exact ((gtγ c c').1 hcc).le
      exact Prod.Lex.le_iff.2 (Or.inr ⟨rfl, Prod.Lex.le_iff.2 (Or.inr ⟨rfl, hc⟩)⟩)
    · exact Prod.Lex.le_iff.2 (Or.inr ⟨rfl, (Prod.Lex.lt_iff.2 (Or.inl ((gtβ b b').1 hb))).le⟩)
  · exact (Prod.Lex.lt_iff.2 (Or.inl ((gtα a a').1 ha))).le

theorem vectorCompare_gt_iff (left right : List (Certificate.CanonicalSphereKey.Key ℤ)) :
    compare left right = Ordering.gt ↔ right < left :=
  (listCompareLex_iff_lex (cmp := compare) (fun a b => keyCompare_eq_iff a b)
    (fun a b => keyCompare_lt_iff a b) (fun a b => keyCompare_gt_iff a b) left right).2.1




theorem tripleKey_le_of_compare_ne_lt (evidence : StereochemicalEvidence graph)
    {treeI treeJ : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyI keyJ : input.LocalizedRerootCumulativeRule45Key}
    (matchI : LocalizedCumulativeTreeTableMatch (.rule4b ρ) treeI keyI)
    (matchJ : LocalizedCumulativeTreeTableMatch (.rule4b ρ) treeJ keyJ)
    (realizesI : LocalizedCumulativeTreeRealizes input read treeI)
    (realizesJ : LocalizedCumulativeTreeRealizes input read treeJ)
    {W D : Nat} {childI childJ : graph.Node}
    (repI : Represents W D (ruleKey input.moleculeGraph graph W D childI) keyI.constitutional)
    (repJ : Represents W D (ruleKey input.moleculeGraph graph W D childJ) keyJ.constitutional)
    (rep4aI : Represents4a W D (rule4aComponent input.moleculeGraph graph evidence W D childI) keyI)
    (rep4aJ : Represents4a W D (rule4aComponent input.moleculeGraph graph evidence W D childJ) keyJ)
    (rep4bI : Represents4b W D (rule4bComponent input.moleculeGraph graph evidence W D childI) keyI)
    (rep4bJ : Represents4b W D (rule4bComponent input.moleculeGraph graph evidence W D childJ) keyJ)
    (h4a : OfficialRuleMajorKey.compare keyI.constitutional keyJ.constitutional = Ordering.eq →
      scalar4a keyI = scalar4a keyJ)
    (hne : input.compareLocalizedRerootCumulativeRule45Keys keyI keyJ ≠ Ordering.lt) :
    tripleKey input.moleculeGraph graph evidence W D childJ ≤
      tripleKey input.moleculeGraph graph evidence W D childI := by
  rw [compare_eq_ruleMajor_of_scalar4a matchI matchJ h4a,
    compareRuleMajor_eq_then matchI matchJ realizesI realizesJ repI repJ
      (ordinaryKey_stereo_wellShaped input.moleculeGraph graph evidence W D _ childI)
      (ordinaryKey_stereo_wellShaped input.moleculeGraph graph evidence W D _ childJ)
      (ordinaryKey_stereo_wellShaped input.moleculeGraph graph evidence W D _ childI)
      (ordinaryKey_stereo_wellShaped input.moleculeGraph graph evidence W D _ childJ)
      rep4aI rep4aJ rep4bI rep4bJ] at hne
  exact lex_le_of_then_ne_lt _ _ _ vectorCompare_eq_iff vectorCompare_gt_iff stereoKeyCompare_eq_iff
    stereoKeyCompare_gt_iff stereoKeyCompare_eq_iff stereoKeyCompare_gt_iff hne

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.encoded4b_cons_of_key
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.stereoNodePathObservation_nil_eq_encoded4b
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.tripleKey_le_of_compare_ne_lt
