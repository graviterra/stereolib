import TetraStereo.OneCenter.LocalizedRuleMajorStagePrefix
import TetraStereo.OneCenter.LocalizedRuleMajorRule4cTableBridge
import TetraStereo.OneCenter.LocalizedActualRule4bTableBridge
import TetraStereo.OneCenter.LocalizedActualRule4aTableBridge
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Complete actual Rule-4b/4c comparison reduces to whole scalar columns. -/

namespace TetraStereo.OneCenter
namespace Rule4cObservationBridge
open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree
open Rule4aTableBridge
open OfficialSparseCanonicalVectorComparison
noncomputable section

private theorem mapPair_eq_of_component_maps {α β γ : Type*} (f : α → β) (g : α → γ) :
    ∀ left right : List α, left.map f = right.map f → left.map g = right.map g →
      left.map (fun value => (f value, g value)) =
        right.map (fun value => (f value, g value))
  | [], [], _, _ => rfl
  | [], _ :: _, hf, _ => by simp at hf
  | _ :: _, [], hf, _ => by simp at hf
  | x :: xs, y :: ys, hf, hg => by
      simp only [List.map_cons, List.cons.injEq] at hf hg
      rcases hf with ⟨hfx, hft⟩
      rcases hg with ⟨hgx, hgt⟩
      simp [hfx, hgx, mapPair_eq_of_component_maps f g xs ys hft hgt]

private theorem mapPairTable_eq_of_component_tables {α β γ : Type*}
    (f : α → β) (g : α → γ) :
    ∀ left right : List (List α),
      left.map (List.map f) = right.map (List.map f) →
      left.map (List.map g) = right.map (List.map g) →
      left.map (List.map fun value => (f value, g value)) =
        right.map (List.map fun value => (f value, g value))
  | [], [], _, _ => rfl
  | [], _ :: _, hf, _ => by simp at hf
  | _ :: _, [], hf, _ => by simp at hf
  | leftLayer :: leftLayers, rightLayer :: rightLayers, hf, hg => by
      simp only [List.map_cons, List.cons.injEq] at hf hg
      rcases hf with ⟨hfl, hft⟩
      rcases hg with ⟨hgl, hgt⟩
      simp [mapPair_eq_of_component_maps f g leftLayer rightLayer hfl hgl,
        mapPairTable_eq_of_component_tables f g leftLayers rightLayers hft hgt]

private abbrev Rule4cTriple := (Nat × Nat) × Nat

private def rule4cTripleVector (value : Rule4cTriple) : List Nat :=
  [value.1.1, value.1.2, value.2]

private theorem compareSparseLayer_rule4cTriple_of_firstTwo_eq :
    ∀ (left right : List (OfficialSparseEntry Rule4cTriple)),
      left.map (sparseEntryMap Prod.fst) = right.map (sparseEntryMap Prod.fst) →
      OfficialRuleMajorKey.compareSparseLayer compareLocalizedCumulativeRule45Priority
          (left.map (sparseEntryMap rule4cTripleVector))
          (right.map (sparseEntryMap rule4cTripleVector)) =
        OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareNat
          (left.map (sparseEntryMap Prod.snd))
          (right.map (sparseEntryMap Prod.snd))
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | leftEntry :: leftTail, rightEntry :: rightTail, h => by
      have hcons : sparseEntryMap Prod.fst leftEntry = sparseEntryMap Prod.fst rightEntry ∧
          leftTail.map (sparseEntryMap Prod.fst) = rightTail.map (sparseEntryMap Prod.fst) :=
        List.cons.inj (by simpa only [List.map_cons] using h)
      have entryComponents : (leftEntry.1, leftEntry.2.1) =
          (rightEntry.1, rightEntry.2.1) := by
        simpa [sparseEntryMap] using hcons.1
      obtain ⟨addressEq, pairEq⟩ := Prod.mk.inj entryComponents
      obtain ⟨firstEq, secondEq⟩ := Prod.mk.inj pairEq
      simp only [List.map_cons, OfficialRuleMajorKey.compareSparseLayer,
        List.compareLex_cons_cons]
      rw [← OfficialRuleMajorKey.compareSparseLayer, ← OfficialRuleMajorKey.compareSparseLayer,
        compareSparseLayer_rule4cTriple_of_firstTwo_eq leftTail rightTail hcons.2]
      congr 1
      unfold OfficialRuleMajorKey.compareSparseEntry sparseEntryMap
      simp only [compareLex, Ordering.byKey, addressEq]
      congr 1
      unfold compareLocalizedCumulativeRule45Priority
      unfold rule4cTripleVector
      rw [firstEq, secondEq]
      simp only [List.compareLex_cons_cons, List.compareLex_nil_nil,
        CompilerProjectionFidelity.compareNat_self]
      cases OfficialRuleMajorKey.compareNat leftEntry.2.2 rightEntry.2.2 <;> rfl

private theorem compareSparseLayers_rule4cTriple_of_firstTwo_eq :
    ∀ (left right : List (List (OfficialSparseEntry Rule4cTriple))),
      left.map (List.map (sparseEntryMap Prod.fst)) =
          right.map (List.map (sparseEntryMap Prod.fst)) →
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
          (left.map (List.map (sparseEntryMap rule4cTripleVector)))
          (right.map (List.map (sparseEntryMap rule4cTripleVector))) =
        OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          (left.map (List.map (sparseEntryMap Prod.snd)))
          (right.map (List.map (sparseEntryMap Prod.snd)))
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | leftLayer :: leftTail, rightLayer :: rightTail, h => by
      have hcons := List.cons.inj (by simpa only [List.map_cons] using h)
      have tailEq := compareSparseLayers_rule4cTriple_of_firstTwo_eq leftTail rightTail hcons.2
      have layerEq := compareSparseLayer_rule4cTriple_of_firstTwo_eq leftLayer rightLayer hcons.1
      simp only [List.map_cons, OfficialRuleMajorKey.compareSparseLayers,
        List.compareLex_cons_cons]
      rw [← OfficialRuleMajorKey.compareSparseLayers, ← OfficialRuleMajorKey.compareSparseLayers,
        tailEq, layerEq]

/-- With the actual Rule-4a/4b table tied, the node-major three-column Rule-4c descriptor
comparison is exactly its whole Rule-4c column comparison. -/
theorem compare_descriptor_eq_scalar4c_of_prior_columns_eq
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key} {ρL ρR : RS}
    (matchL : LocalizedCumulativeTreeTableMatch (.rule4c ρL) treeL keyL)
    (matchR : LocalizedCumulativeTreeTableMatch (.rule4c ρR) treeR keyR)
    (firstColumnTie : scalar4a keyL = scalar4a keyR)
    (secondColumnTie : scalar4b keyL = scalar4b keyR) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        keyL.descriptor keyR.descriptor =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4c keyL) (scalar4c keyR) := by
  let tripleL (node : LocalizedCumulativeDecoratedTree input carrierFuel) : Rule4cTriple :=
    ((prio4a node, bit4b ρL node), localizedRule4cPriority node.label)
  let tripleR (node : LocalizedCumulativeDecoratedTree input carrierFuel) : Rule4cTriple :=
    ((prio4a node, bit4b ρR node), localizedRule4cPriority node.label)
  have descL : keyL.descriptor =
      (table tripleL treeL).map (List.map (sparseEntryMap rule4cTripleVector)) := by
    rw [← matchL.2.2.2, tables_descriptor, table_map]
    rfl
  have descR : keyR.descriptor =
      (table tripleR treeR).map (List.map (sparseEntryMap rule4cTripleVector)) := by
    rw [← matchR.2.2.2, tables_descriptor, table_map]
    rfl
  have firstL : scalar4a keyL =
      (table tripleL treeL).map
        (List.map (sparseEntryMap fun value : Rule4cTriple => value.1.1)) := by
    rw [scalar4a_rule4c_eq_table matchL]
    simpa [tripleL, prio4a, bit4b] using
      (table_map tripleL (fun value => value.1.1) treeL).symm
  have firstR : scalar4a keyR =
      (table tripleR treeR).map
        (List.map (sparseEntryMap fun value : Rule4cTriple => value.1.1)) := by
    rw [scalar4a_rule4c_eq_table matchR]
    simpa [tripleR, prio4a, bit4b] using
      (table_map tripleR (fun value => value.1.1) treeR).symm
  have secondL : scalar4b keyL =
      (table tripleL treeL).map
        (List.map (sparseEntryMap fun value : Rule4cTriple => value.1.2)) := by
    rw [scalar4b_rule4c_eq_table matchL]
    simpa [tripleL, prio4a, bit4b] using
      (table_map tripleL (fun value => value.1.2) treeL).symm
  have secondR : scalar4b keyR =
      (table tripleR treeR).map
        (List.map (sparseEntryMap fun value : Rule4cTriple => value.1.2)) := by
    rw [scalar4b_rule4c_eq_table matchR]
    simpa [tripleR, prio4a, bit4b] using
      (table_map tripleR (fun value => value.1.2) treeR).symm
  have firstProjectionTie :
      (table tripleL treeL).map
        (List.map (sparseEntryMap fun value : Rule4cTriple => value.1.1)) =
      (table tripleR treeR).map
        (List.map (sparseEntryMap fun value : Rule4cTriple => value.1.1)) :=
    firstL.symm.trans (firstColumnTie.trans firstR)
  have secondProjectionTie :
      (table tripleL treeL).map
        (List.map (sparseEntryMap fun value : Rule4cTriple => value.1.2)) =
      (table tripleR treeR).map
        (List.map (sparseEntryMap fun value : Rule4cTriple => value.1.2)) :=
    secondL.symm.trans (secondColumnTie.trans secondR)
  have projectionTie :
      (table tripleL treeL).map (List.map (sparseEntryMap Prod.fst)) =
        (table tripleR treeR).map (List.map (sparseEntryMap Prod.fst)) := by
    have paired := mapPairTable_eq_of_component_tables
      (fun entry : OfficialSparseEntry Rule4cTriple =>
        sparseEntryMap (fun value : Rule4cTriple => value.1.1) entry)
      (fun entry => sparseEntryMap (fun value : Rule4cTriple => value.1.2) entry)
      (table tripleL treeL) (table tripleR treeR) firstProjectionTie secondProjectionTie
    have converted := congrArg
      (fun layers => layers.map (List.map fun pair => (pair.1.1, (pair.1.2, pair.2.2)))) paired
    simpa [List.map_map, Function.comp_def, sparseEntryMap] using converted
  rw [descL, descR]
  have columns := compareSparseLayers_rule4cTriple_of_firstTwo_eq
    (table tripleL treeL) (table tripleR treeR) projectionTie
  rw [columns]
  rw [scalar4c_eq_table matchL, scalar4c_eq_table matchR,
    ← table_map tripleL Prod.snd, ← table_map tripleR Prod.snd]

end
end Rule4cObservationBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.compare_descriptor_eq_scalar4c_of_prior_columns_eq
