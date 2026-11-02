import TetraStereo.OneCenter.LocalizedActualRule4bTableBridge
import TetraStereo.OneCenter.LocalizedActualRule4bPhysicalComparison
import TetraStereo.OneCenter.LocalizedActualMolecularEvidenceRefinement
import TetraStereo.OneCenter.DeclarativeCIPFirstDifferenceSchedule
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Rule 4c scalar and addressed-table observation bridge

The runtime Rule-4c priority is the two-level code `r ↦ 1`, `s ↦ 0`; the independent molecular
reading uses `r ↦ 2`, `s ↦ 1`, with `0` for readings that carry no pseudoasymmetric descriptor.
They are not equal as numbers.  On the Rule-4a pseudoasymmetric fiber they induce the same order.

This module exposes that scalar law and lifts it through the complete addressed sparse hierarchy.
The table theorem takes only a pointwise Rule-4a fiber condition at equal addresses.  It does not
assume that pseudoasymmetric labels are absent, nor does it assume the requested whole-table
comparison.  Exact label-table matches let a caller apply it to an actual stage-`.rule4c ρ` key.
-/

namespace TetraStereo.OneCenter
namespace Rule4cObservationBridge

open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree
open OfficialSparseCanonicalVectorComparison
open SparsePhysicalFirstDifference
open SparseSupportAlignment
open DeclarativeCIP
open Rule4aTableBridge

noncomputable section
open scoped Classical

/-! ## The two scalar encodings -/

/-- Independent Rule-4c value associated with a localized node label:
`0 = absent`, `1 = s`, `2 = r`. -/
def pseudoValueOfLabel : Option LocalizedAuxiliaryLabel → Nat
  | some (.pseudoasymmetric .r) => 2
  | some (.pseudoasymmetric .s) => 1
  | none | some (.chiral _) => 0

/-- The exact support of independent pseudoasymmetric values is the Rule-4a pseudo kind. -/
theorem pseudoValueOfLabel_ne_zero_iff_rule4aPseudo (label : Option LocalizedAuxiliaryLabel) :
    pseudoValueOfLabel label ≠ 0 ↔ localizedRule4aPriority label = 1 := by
  cases label with
  | none => simp [pseudoValueOfLabel, localizedRule4aPriority]
  | some label => cases label with
      | chiral descriptor => simp [pseudoValueOfLabel, localizedRule4aPriority]
      | pseudoasymmetric descriptor => cases descriptor <;>
          simp [pseudoValueOfLabel, localizedRule4aPriority]

/-- On the Rule-4a fiber, the runtime Rule-4c code and the independent pseudo-value have the
same pairwise ordering.  In particular this covers both `r` and `s`. -/
theorem compareRule4cPriority_eq_pseudoValueOfLabel
    (left right : Option LocalizedAuxiliaryLabel)
    (kindEq : localizedRule4aPriority left = localizedRule4aPriority right) :
    OfficialRuleMajorKey.compareNat (localizedRule4cPriority left)
        (localizedRule4cPriority right) =
      OfficialRuleMajorKey.compareNat (pseudoValueOfLabel left) (pseudoValueOfLabel right) := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some right => cases right with
          | chiral descriptor => simp [localizedRule4aPriority] at kindEq
          | pseudoasymmetric descriptor => simp [localizedRule4aPriority] at kindEq
  | some left =>
      cases left with
      | chiral descriptor =>
          cases right with
          | none => simp [localizedRule4aPriority] at kindEq
          | some right => cases right with
              | chiral other => rfl
              | pseudoasymmetric other => simp [localizedRule4aPriority] at kindEq
      | pseudoasymmetric descriptor =>
          cases right with
          | none => simp [localizedRule4aPriority] at kindEq
          | some right => cases right with
              | chiral other => simp [localizedRule4aPriority] at kindEq
              | pseudoasymmetric other =>
                  cases descriptor <;> cases other <;> decide

/-- The label encoding is exactly the independent reading's pseudo-value whenever the reading
is tetrahedral and its localized-label readback is exact. -/
theorem pseudoValue_eq_pseudoValueOfLabel (reading : OccurrenceReading)
    (label : Option LocalizedAuxiliaryLabel)
    (readback : reading.toLocalizedLabel = label) :
    reading.pseudoValue = pseudoValueOfLabel label := by
  cases reading with
  | descriptor value =>
      rw [← readback]
      cases value <;> rfl
  | outsideInventory => rw [← readback]; rfl
  | unassigned => rw [← readback]; rfl
  | unavailable => rw [← readback]; rfl

/-- Reading-level form of the Rule-4a fiber law, reusing the existing scalar refinement theorem. -/
theorem compareRule4cPriority_eq_pseudoValue (left right : OccurrenceReading)
    (leftTetrahedral : left.IsTetrahedral) (rightTetrahedral : right.IsTetrahedral)
    (kindEq : left.kindPriority = right.kindPriority) :
    OfficialRuleMajorKey.compareNat
        (localizedRule4cPriority left.toLocalizedLabel)
        (localizedRule4cPriority right.toLocalizedLabel) =
      OfficialRuleMajorKey.compareNat left.pseudoValue right.pseudoValue := by
  simpa [OfficialRuleMajorKey.compareNat] using
    rule4cOrder_eq_runtime left right leftTetrahedral rightTetrahedral kindEq

/-! ## Actual scalar table projection at stage `.rule4c ρ` -/

/-- Scalar projection of the third cumulative component (the Rule-4c component). -/
def scalar4c {input : CertifiedLocalizedCIPInput}
    (key : input.LocalizedRerootCumulativeRule45Key) :
    List (List (OfficialSparseEntry Nat)) :=
  key.descriptor.map (List.map (sparseEntryMap fun values => values.getD 2 0))

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
  {key : input.LocalizedRerootCumulativeRule45Key} {ρ : RS}

/-- A matched stage-`.rule4c ρ` key projects to the tree's runtime Rule-4c observation table. -/
theorem scalar4c_eq_table
    (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4c ρ) tree key) :
    scalar4c key = table (fun node => localizedRule4cPriority node.label) tree := by
  unfold scalar4c
  rw [← tableMatch.2.2.2, tables_descriptor, table_map]
  rfl

/-- The scalar Rule-4c projection is structurally well formed. -/
theorem scalar4c_wellFormed
    (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4c ρ) tree key) :
    SparsePhysicalFirstDifference.SparseTableWellFormed (scalar4c key) := by
  rw [scalar4c_eq_table tableMatch]
  exact LocalizedActualTableAddressOrder.table_wellFormed
    (fun node => localizedRule4cPriority node.label) tree

/-- The scalar Rule-4c projection has exactly the Rule-1a table's address rows. -/
theorem scalar4c_rows
    (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4c ρ) tree key) :
    SparseSupportAlignment.SameAddressRows (scalar4c key) key.constitutional.rule1a := by
  rw [scalar4c_eq_table tableMatch, ← tableMatch.1, tables_rule1a]
  exact LocalizedActualTableAddressOrder.SameAddressRows_table_observations
    (fun node => localizedRule4cPriority node.label) (fun node => node.atomicNumber) tree

/-! ## Whole addressed hierarchy extension -/

/-- Map an exact localized-label table to one scalar observation table. -/
def mapLabelTable (observe : Option LocalizedAuxiliaryLabel → Nat)
    (labels : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    List (List (OfficialSparseEntry Nat)) :=
  labels.map (List.map (sparseEntryMap observe))

private theorem compareSparseLayer_rule4c_eq_pseudo
    (left right : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))
    (fiber : ∀ e₁, e₁ ∈ left → ∀ e₂, e₂ ∈ right → e₁.1 = e₂.1 →
      localizedRule4aPriority e₁.2 = localizedRule4aPriority e₂.2) :
    OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareNat
        (left.map (sparseEntryMap localizedRule4cPriority))
        (right.map (sparseEntryMap localizedRule4cPriority)) =
      OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareNat
        (left.map (sparseEntryMap pseudoValueOfLabel))
        (right.map (sparseEntryMap pseudoValueOfLabel)) := by
  let rawCompare := fun e₁ e₂ =>
      OfficialRuleMajorKey.compareSparseEntry OfficialRuleMajorKey.compareNat
        (sparseEntryMap localizedRule4cPriority e₁)
        (sparseEntryMap localizedRule4cPriority e₂)
  have runtimeMap :
      List.compareLex rawCompare left right =
        OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareNat
          (left.map (sparseEntryMap localizedRule4cPriority))
          (right.map (sparseEntryMap localizedRule4cPriority)) := by
    unfold OfficialRuleMajorKey.compareSparseLayer
    exact (compareLex_map_eq rawCompare
      (OfficialRuleMajorKey.compareSparseEntry OfficialRuleMajorKey.compareNat)
      (sparseEntryMap localizedRule4cPriority) (sparseEntryMap localizedRule4cPriority)
      left right (by intro e₁ _ e₂ _; rfl))
  have pseudoMap :
      List.compareLex rawCompare left right =
        OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareNat
          (left.map (sparseEntryMap pseudoValueOfLabel))
          (right.map (sparseEntryMap pseudoValueOfLabel)) := by
    unfold OfficialRuleMajorKey.compareSparseLayer
    apply compareLex_map_eq rawCompare
      (OfficialRuleMajorKey.compareSparseEntry OfficialRuleMajorKey.compareNat)
      (sparseEntryMap pseudoValueOfLabel) (sparseEntryMap pseudoValueOfLabel) left right
    intro e₁ h₁ e₂ h₂
    change OfficialRuleMajorKey.compareSparseEntry OfficialRuleMajorKey.compareNat
        (sparseEntryMap localizedRule4cPriority e₁)
        (sparseEntryMap localizedRule4cPriority e₂) =
      OfficialRuleMajorKey.compareSparseEntry OfficialRuleMajorKey.compareNat
        (sparseEntryMap pseudoValueOfLabel e₁)
        (sparseEntryMap pseudoValueOfLabel e₂)
    cases addressOrder : SparsePhysicalFirstDifference.AddressCompare e₁.1 e₂.1 with
    | lt =>
        rw [SparsePhysicalFirstDifference.compareSparseEntry_gt_of_address_lt
              OfficialRuleMajorKey.compareNat addressOrder,
            SparsePhysicalFirstDifference.compareSparseEntry_gt_of_address_lt
              OfficialRuleMajorKey.compareNat addressOrder]
    | eq =>
        have addressEq := SparsePhysicalFirstDifference.AddressCompare_eq_iff.mp addressOrder
        rw [SparsePhysicalFirstDifference.compareSparseEntry_eq_of_address_eq
              OfficialRuleMajorKey.compareNat addressEq,
            SparsePhysicalFirstDifference.compareSparseEntry_eq_of_address_eq
              OfficialRuleMajorKey.compareNat addressEq]
        exact compareRule4cPriority_eq_pseudoValueOfLabel e₁.2 e₂.2
          (fiber e₁ h₁ e₂ h₂ addressEq)
    | gt =>
        rw [SparsePhysicalFirstDifference.compareSparseEntry_lt_of_address_gt
              OfficialRuleMajorKey.compareNat addressOrder,
            SparsePhysicalFirstDifference.compareSparseEntry_lt_of_address_gt
              OfficialRuleMajorKey.compareNat addressOrder]
  unfold OfficialRuleMajorKey.compareSparseLayer at runtimeMap pseudoMap ⊢
  rw [← runtimeMap, pseudoMap]

/-- **Rule-4c table order bridge.**  If the Rule-4a kind agrees at each address present on both
sides, the entire addressed Rule-4c hierarchy compares exactly as the independent pseudo-value
hierarchy.  Rows, layer lengths, and address comparisons are retained verbatim from the label
tables, so unequal addresses are decided identically before the scalar Rule-4c law is consulted. -/
theorem compareRule4cTables_eq_pseudoValueTables_of_rule4aFiber
    (left right : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))))
    (fiber : ∀ e₁, e₁ ∈ left.flatten → ∀ e₂, e₂ ∈ right.flatten → e₁.1 = e₂.1 →
      localizedRule4aPriority e₁.2 = localizedRule4aPriority e₂.2) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (mapLabelTable localizedRule4cPriority left)
        (mapLabelTable localizedRule4cPriority right) =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (mapLabelTable pseudoValueOfLabel left)
        (mapLabelTable pseudoValueOfLabel right) := by
  unfold OfficialRuleMajorKey.compareSparseLayers mapLabelTable
  let runtimeLayer :
      List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)) →
        List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)) → Ordering := fun l r =>
    OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareNat
      (l.map (sparseEntryMap localizedRule4cPriority))
      (r.map (sparseEntryMap localizedRule4cPriority))
  have runtimeMap :
      List.compareLex runtimeLayer left right =
        List.compareLex (OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareNat)
          (left.map (List.map (sparseEntryMap localizedRule4cPriority)))
          (right.map (List.map (sparseEntryMap localizedRule4cPriority))) := by
    exact (compareLex_map_eq runtimeLayer
      (OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareNat)
      (fun layer => layer.map (sparseEntryMap localizedRule4cPriority))
      (fun layer => layer.map (sparseEntryMap localizedRule4cPriority)) left right
      (by intro l _ r _; rfl))
  have pseudoMap :
      List.compareLex runtimeLayer left right =
        List.compareLex (OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareNat)
          (left.map (List.map (sparseEntryMap pseudoValueOfLabel)))
          (right.map (List.map (sparseEntryMap pseudoValueOfLabel))) := by
    apply compareLex_map_eq runtimeLayer
      (OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareNat)
      (fun layer => layer.map (sparseEntryMap pseudoValueOfLabel))
      (fun layer => layer.map (sparseEntryMap pseudoValueOfLabel)) left right
    intro l hl r hr
    apply compareSparseLayer_rule4c_eq_pseudo l r
    intro e₁ h₁ e₂ h₂ sameAddress
    exact fiber e₁ (List.mem_flatten.mpr ⟨l, hl, h₁⟩)
      e₂ (List.mem_flatten.mpr ⟨r, hr, h₂⟩) sameAddress
  exact runtimeMap.symm.trans pseudoMap

/-- Actual-key corollary: under exact actual label-table matches, the third scalar column of two
stage-`.rule4c` keys has the same whole hierarchy order as the independent pseudo-value
projection of those exact readback labels. -/
theorem compareScalar4c_eq_pseudoValueOfLabels
    {tree₁ tree₂ : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key₁ key₂ : input.LocalizedRerootCumulativeRule45Key} {ρ₁ ρ₂ : RS}
    (match₁ : LocalizedCumulativeTreeTableMatch (.rule4c ρ₁) tree₁ key₁)
    (match₂ : LocalizedCumulativeTreeTableMatch (.rule4c ρ₂) tree₂ key₂)
    (labels₁ : LocalizedCumulativeTreeLabelMatch tree₁ key₁)
    (labels₂ : LocalizedCumulativeTreeLabelMatch tree₂ key₂)
    (fiber : ∀ e₁, e₁ ∈ tree₁.labelTable.flatten →
      ∀ e₂, e₂ ∈ tree₂.labelTable.flatten → e₁.1 = e₂.1 →
        localizedRule4aPriority e₁.2 = localizedRule4aPriority e₂.2) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4c key₁) (scalar4c key₂) =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (mapLabelTable pseudoValueOfLabel key₁.labels)
        (mapLabelTable pseudoValueOfLabel key₂.labels) := by
  have runtime₁ : scalar4c key₁ = mapLabelTable localizedRule4cPriority key₁.labels := by
    rw [scalar4c_eq_table match₁, ← labels₁]
    rw [labelTable_eq_table]
    exact (table_map (fun node => node.label)
      localizedRule4cPriority tree₁).symm
  have runtime₂ : scalar4c key₂ = mapLabelTable localizedRule4cPriority key₂.labels := by
    rw [scalar4c_eq_table match₂, ← labels₂]
    rw [labelTable_eq_table]
    exact (table_map (fun node => node.label)
      localizedRule4cPriority tree₂).symm
  rw [runtime₁, runtime₂]
  exact compareRule4cTables_eq_pseudoValueTables_of_rule4aFiber
    key₁.labels key₂.labels (by
      intro e₁ h₁ e₂ h₂ sameAddress
      apply fiber e₁ _ e₂ _ sameAddress
      · have h₁' := h₁
        rw [← labels₁] at h₁'
        exact h₁'
      · have h₂' := h₂
        rw [← labels₂] at h₂'
        exact h₂')

end
end Rule4cObservationBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.pseudoValueOfLabel_ne_zero_iff_rule4aPseudo
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.compareRule4cPriority_eq_pseudoValueOfLabel
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.pseudoValue_eq_pseudoValueOfLabel
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.scalar4c_eq_table
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.scalar4c_wellFormed
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.scalar4c_rows
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.compareRule4cTables_eq_pseudoValueTables_of_rule4aFiber
assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.compareScalar4c_eq_pseudoValueOfLabels
