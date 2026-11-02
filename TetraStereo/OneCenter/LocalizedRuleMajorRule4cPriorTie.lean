import TetraStereo.OneCenter.LocalizedRuleMajorRule4cObservation
import TetraStereo.OneCenter.LocalizedCumulativeKeyObservableOrder
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Derive the Rule-4c encoding connection from an actual earlier Rule-4a column tie.
No pointwise kind correspondence, absence of lowercase labels, or desired Rule-4c
comparison is assumed. Equal kind/address tables align the two lists directly. -/

namespace TetraStereo.OneCenter
namespace Rule4cObservationBridge

open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree Rule4aTableBridge
noncomputable section

private theorem compare_maps_eq_on_fiber {α κ β γ : Type*}
    (classify : α → κ) (f : α → β) (g : α → γ)
    (cmpF : β → β → Ordering) (cmpG : γ → γ → Ordering)
    (law : ∀ a b, classify a = classify b → cmpF (f a) (f b) = cmpG (g a) (g b)) :
    ∀ left right : List α, left.map classify = right.map classify →
      List.compareLex cmpF (left.map f) (right.map f) =
        List.compareLex cmpG (left.map g) (right.map g) := by
  intro left
  induction left with
  | nil =>
      intro right same
      cases right with
      | nil => rfl
      | cons b bs => simp at same
  | cons a as ih =>
      intro right same
      cases right with
      | nil => simp at same
      | cons b bs =>
          have heads : classify a = classify b ∧ as.map classify = bs.map classify :=
            List.cons.inj (by simpa only [List.map_cons] using same)
          simp only [List.map_cons, List.compareLex_cons_cons]
          rw [law a b heads.1, ih bs heads.2]

/-- Equality of the earlier kind/address tables is sufficient for the complete Rule-4c
comparison; no independent pointwise fiber premise is needed. -/
theorem compareRule4cTables_eq_pseudoValueTables_of_kindTables_eq
    (left right : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))))
    (kinds : mapLabelTable localizedRule4aPriority left =
      mapLabelTable localizedRule4aPriority right) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (mapLabelTable localizedRule4cPriority left)
        (mapLabelTable localizedRule4cPriority right) =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (mapLabelTable pseudoValueOfLabel left)
        (mapLabelTable pseudoValueOfLabel right) := by
  apply compare_maps_eq_on_fiber
    (List.map (sparseEntryMap localizedRule4aPriority))
    (List.map (sparseEntryMap localizedRule4cPriority))
    (List.map (sparseEntryMap pseudoValueOfLabel))
    (OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareNat)
    (OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareNat) ?_
    left right kinds
  intro layerL layerR same
  apply compare_maps_eq_on_fiber
    (sparseEntryMap localizedRule4aPriority)
    (sparseEntryMap localizedRule4cPriority)
    (sparseEntryMap pseudoValueOfLabel)
    (OfficialRuleMajorKey.compareSparseEntry OfficialRuleMajorKey.compareNat)
    (OfficialRuleMajorKey.compareSparseEntry OfficialRuleMajorKey.compareNat) ?_
    layerL layerR same
  intro a b entryEq
  have addressEq : a.1 = b.1 :=
    congrArg (fun entry : OfficialSparseEntry Nat => entry.1) entryEq
  have kindEq : localizedRule4aPriority a.2 = localizedRule4aPriority b.2 :=
    congrArg (fun entry : OfficialSparseEntry Nat => entry.2) entryEq
  rw [SparsePhysicalFirstDifference.compareSparseEntry_eq_of_address_eq
      OfficialRuleMajorKey.compareNat addressEq,
    SparsePhysicalFirstDifference.compareSparseEntry_eq_of_address_eq
      OfficialRuleMajorKey.compareNat addressEq]
  exact compareRule4cPriority_eq_pseudoValueOfLabel a.2 b.2 kindEq

theorem mapLabelTable_labelTable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (observe : Option LocalizedAuxiliaryLabel → Nat)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    mapLabelTable observe tree.labelTable = table (fun node => observe node.label) tree := by
  unfold mapLabelTable
  rw [labelTable_eq_table]
  exact table_map (fun node => node.label) observe tree

theorem scalar4a_rule4c_eq_table {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key} {ρ : RS}
    (matched : LocalizedCumulativeTreeTableMatch (.rule4c ρ) tree key) :
    scalar4a key = table (fun node => localizedRule4aPriority node.label) tree := by
  unfold scalar4a
  rw [← matched.2.2.2, tables_descriptor, table_map]
  rfl

/-- Actual stage-4c keys: a tie of the preceding Rule-4a columns derives the complete
runtime-versus-independent Rule-4c comparison, including r/s auxiliary descriptors. -/
theorem compareScalar4c_eq_pseudoValueOfLabels_of_rule4a_tie
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key} {ρL ρR : RS}
    (matchL : LocalizedCumulativeTreeTableMatch (.rule4c ρL) treeL keyL)
    (matchR : LocalizedCumulativeTreeTableMatch (.rule4c ρR) treeR keyR)
    (labelsL : LocalizedCumulativeTreeLabelMatch treeL keyL)
    (labelsR : LocalizedCumulativeTreeLabelMatch treeR keyR)
    (priorTie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4a keyL) (scalar4a keyR) = .eq) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4c keyL) (scalar4c keyR) =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (mapLabelTable pseudoValueOfLabel keyL.labels)
        (mapLabelTable pseudoValueOfLabel keyR.labels) := by
  have kindEq := (compareSparseLayers_compareNat_eq_iff _ _).1 priorTie
  have kindL : mapLabelTable localizedRule4aPriority keyL.labels = scalar4a keyL := by
    rw [← labelsL, mapLabelTable_labelTable, scalar4a_rule4c_eq_table matchL]
  have kindR : mapLabelTable localizedRule4aPriority keyR.labels = scalar4a keyR := by
    rw [← labelsR, mapLabelTable_labelTable, scalar4a_rule4c_eq_table matchR]
  have runtimeL : mapLabelTable localizedRule4cPriority keyL.labels = scalar4c keyL := by
    rw [← labelsL, mapLabelTable_labelTable, scalar4c_eq_table matchL]
  have runtimeR : mapLabelTable localizedRule4cPriority keyR.labels = scalar4c keyR := by
    rw [← labelsR, mapLabelTable_labelTable, scalar4c_eq_table matchR]
  rw [← runtimeL, ← runtimeR]
  apply compareRule4cTables_eq_pseudoValueTables_of_kindTables_eq
  rw [kindL, kindR, kindEq]

end
end Rule4cObservationBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.compareRule4cTables_eq_pseudoValueTables_of_kindTables_eq
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.mapLabelTable_labelTable
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.scalar4a_rule4c_eq_table
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.compareScalar4c_eq_pseudoValueOfLabels_of_rule4a_tie
