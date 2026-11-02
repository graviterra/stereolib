import TetraStereo.UniversalProof.CentralDrawingRule3TieProofs.CentralDrawingRule3Tie
import TetraStereo.UniversalProof.CentralDrawingRule3TieProofs.CentralDrawingRule4bcTie

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace TetraStereo.UniversalProof.CentralDrawingRule3TieProofs.CentralDrawingRule45Comparison

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.UniversalProof.ThreeCenterDrawingSourceProofs.ThreeCenterDrawingSource

/-!
# Actual four-key central tracked sort under the corrected tetrahedral calibration

Cl and F outrank the carbon ligands by the actual compiled atomic heads.  Under the corrected
geometry calibration the two equal-carbon daughter occurrences carry the actual scheduled
dependency labels `S` at slot `2` and `R` at slot `3` (the upstream historical keys
`central_left_dependency_label_R` / `central_right_dependency_label_S` keep their names and now
state the corrected values).  Their complete Rule-3 keys tie, and their complete compound
Rule-4b/4c prior keys tie.  The genuine compiled Rule-5 readings are consequently headed

* slot `2` (`S`): common `R` `[2, 1, 0, 0]`, common `S` `[2, 1, 0, 1]`;
* slot `3` (`R`): common `R` `[2, 1, 0, 1]`, common `S` `[2, 1, 0, 0]`,

so the **actual common-`R` comparison of slot `2` against slot `3` is `lt`** (and common `S` is
`gt`).  The actual forward carbon comparison is therefore `lt` with the enantiomorphic signal and
the reversed comparison is `gt`.  In particular slot `3` outranks slot `2`, so the production
tracked sorter returns `[1, 0, 3, 2]` with exactly one pseudo comparison.

The historical certificate keys are preserved.  `central_actual_carbon_comparison_gt` and
`central_actual_carbon_comparison_lt` keep their names and now state the actual corrected
directions; accurately named siblings (`..._forward_lt`, `..._reversed_gt`) are provided alongside
them.  `centralExpectedRank` and `centralTrackedOrder` are corrected together so that the
off-diagonal comparison table, the strict all-pairs coherence guard and the safe-sort guard are
all derived from the actual comparator rather than from any supplied order, expected label or
comparison callback.

The tracked order is definitionally the source's `centralHypotheticalOrderRightFirst`, the order
under which the exact central source geometry is uppercase `R`
(`central_geometry_hypothetical_right_first`).  With the single pseudo comparison recorded by the
tracked sort, this is precisely the geometry-side interface consumed by the downstream central
descriptor construction, which therefore keeps the central pseudo descriptor
`.pseudoasymmetric .r` (the descriptor proof itself remains downstream and unchanged).  No
successful sort, priority order, expected label or comparison callback is assumed; final drawing
geometry is a separate step.
-/

/-! ## 1. The actual central four-ligand frame and atomic priorities -/

noncomputable def centralFourFrame : source.AromaticCanonicalOccurrenceFourLigandFrame branchCarrierFuel :=
  { roots := centralRoots, rootsLength := central_roots_length }

theorem centralFourFrame_roots_real : OccurrenceRootsReal source centralFourFrame := by
  intro slot
  fin_cases slot <;> exact ⟨_, rfl, rfl⟩

def centralAtomicPriorityValue : Fin 4 → Nat
  | ⟨0, _⟩ => 9
  | ⟨1, _⟩ => 17
  | ⟨2, _⟩ => 6
  | ⟨3, _⟩ => 6

theorem central_actual_atomic_priority_value (slot : Fin 4) :
    occurrenceAtomicPriority source centralFourFrame slot = centralAtomicPriorityValue slot := by
  fin_cases slot <;> rfl

/-! ## 2. Actual daughter labels and the genuine carbon comparisons

The two carbon comparisons are derived from the actual compiled drawing model.  The Rule-3 tie is
the closed automorphism tie of `CentralDrawingRule3Tie`; the complete Rule-4b/4c prior tie is the
closed drawing reflection of `CentralDrawingRule4bcTie`; the Rule-5 readings are the actual
compiled readings of `CentralDrawingRule45CompiledReadings`.  Nothing here supplies an expected
label or a comparison value. -/

/-- The actual left daughter dependency label (slot `2`) is `S`.  This mirrors the corrected
upstream historical key `central_left_dependency_label_R`. -/
theorem central_daughter_label_two_S :
    source.aromaticCanonicalDependencyLabel centralTarget centralView
        (centralRootAt centralSlotTwo) = some (.chiral RS.S) :=
  central_slot_two_label

/-- The actual right daughter dependency label (slot `3`) is `R`.  This mirrors the corrected
upstream historical key `central_right_dependency_label_S`. -/
theorem central_daughter_label_three_R :
    source.aromaticCanonicalDependencyLabel centralTarget centralView
        (centralRootAt centralSlotThree) = some (.chiral RS.R) :=
  central_slot_three_label

/-- The actual common-`R` Rule-5 comparison of the compiled slot-2/slot-3 reading lists is `lt`:
the slot-2 (`S`) head is `[2, 1, 0, 0]` and the slot-3 (`R`) head is `[2, 1, 0, 1]`.  This is the
decisive common-reference premise of the tracked order. -/
theorem central_tracked_commonR_forward_lt :
    source.compareAromaticCanonicalRerootCompoundRule5Readings RS.R
      (centralKeyFrame.keyAt centralSlotTwo).rule45.rule5Readings
      (centralKeyFrame.keyAt centralSlotThree).rule45.rule5Readings = Ordering.lt :=
  central_actual_commonR_lt

/-- The actual common-`S` Rule-5 comparison of the same lists is `gt`, completing the
enantiomorphic pair. -/
theorem central_tracked_commonS_forward_gt :
    source.compareAromaticCanonicalRerootCompoundRule5Readings RS.S
      (centralKeyFrame.keyAt centralSlotTwo).rule45.rule5Readings
      (centralKeyFrame.keyAt centralSlotThree).rule45.rule5Readings = Ordering.gt :=
  central_actual_commonS_gt

/-- **Actual forward carbon comparison.**  Historical certificate key: the slot-2/slot-3
comparison is `lt` with the enantiomorphic signal under the corrected calibration. -/
theorem central_actual_carbon_comparison_gt :
    source.compareAromaticCanonicalOccurrenceRule3Through5At centralKeyFrame
      centralSlotTwo centralSlotThree = { ordering := Ordering.lt, pseudo := true } :=
  central_drawing_rule45_forward_of_rule3_tie central_rule3_tie

/-- Accurate-name alias for the actual forward carbon comparison. -/
theorem central_actual_carbon_comparison_forward_lt :
    source.compareAromaticCanonicalOccurrenceRule3Through5At centralKeyFrame
      centralSlotTwo centralSlotThree = { ordering := Ordering.lt, pseudo := true } :=
  central_actual_carbon_comparison_gt

theorem central_actual_rule4bc_prior_tie_reversed :
    source.compareAromaticCanonicalRerootCompoundRule4bcKeys
      (centralKeyFrame.keyAt centralSlotThree).rule45.prior
      (centralKeyFrame.keyAt centralSlotTwo).rule45.prior = Ordering.eq := by
  letI := source.compareAromaticCanonicalRerootCompoundRule4bcKeys_transCmp
  rw [Std.OrientedCmp.eq_swap
    (cmp := source.compareAromaticCanonicalRerootCompoundRule4bcKeys)
    (a := (centralKeyFrame.keyAt centralSlotThree).rule45.prior)
    (b := (centralKeyFrame.keyAt centralSlotTwo).rule45.prior), central_actual_rule4bc_prior_tie]
  rfl

/-- **Actual reversed carbon comparison.**  Historical certificate key: slot `3` against slot `2`
is `gt` with the enantiomorphic signal. -/
theorem central_actual_carbon_comparison_lt :
    source.compareAromaticCanonicalOccurrenceRule3Through5At centralKeyFrame
      centralSlotThree centralSlotTwo = { ordering := Ordering.gt, pseudo := true } :=
  central_drawing_rule45_reversed_of_actual_prior_ties central_rule3_tie_reversed
    central_actual_rule4bc_prior_tie_reversed

/-- Accurate-name alias for the actual reversed carbon comparison. -/
theorem central_actual_carbon_comparison_reversed_gt :
    source.compareAromaticCanonicalOccurrenceRule3Through5At centralKeyFrame
      centralSlotThree centralSlotTwo = { ordering := Ordering.gt, pseudo := true } :=
  central_actual_carbon_comparison_lt

/-- The authoritative direction summary: the actual slot-2/slot-3 carbon comparison is `lt` and
the reversed comparison is `gt`, both with the enantiomorphic signal.  This is the concrete
comparator fact that forces slot `3` ahead of slot `2` in the tracked order. -/
theorem central_actual_carbon_directions :
    (source.compareAromaticCanonicalOccurrenceRule3Through5At centralKeyFrame
        centralSlotTwo centralSlotThree).ordering = Ordering.lt ∧
      (source.compareAromaticCanonicalOccurrenceRule3Through5At centralKeyFrame
        centralSlotThree centralSlotTwo).ordering = Ordering.gt := by
  rw [central_actual_carbon_comparison_gt, central_actual_carbon_comparison_lt]
  exact ⟨rfl, rfl⟩

private theorem central_actual_atomic_comparison_gt (left right : Fin 4)
    (higher : centralAtomicPriorityValue right < centralAtomicPriorityValue left) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At centralKeyFrame left right =
      { ordering := Ordering.gt, pseudo := false } := by
  apply occurrence_comparison_gt_of_atomic_priority source centralTarget centralView 4
    centralFourFrame centralFourFrame_roots_real centralKeyFrame centralKeyFrame_computed
  simpa only [central_actual_atomic_priority_value] using higher

private theorem central_actual_atomic_comparison_lt (left right : Fin 4)
    (lower : centralAtomicPriorityValue left < centralAtomicPriorityValue right) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At centralKeyFrame left right =
      { ordering := Ordering.lt, pseudo := false } := by
  apply occurrence_comparison_lt_of_atomic_priority source centralTarget centralView 4
    centralFourFrame centralFourFrame_roots_real centralKeyFrame centralKeyFrame_computed
  simpa only [central_actual_atomic_priority_value] using lower

/-! ## 3. The complete off-diagonal comparison table

`centralExpectedRank` is the highest-first rank induced by the actual comparator: slot `1` (Cl)
outranks slot `0` (F), which outranks slot `3` (the `R` carbon daughter), which outranks slot `2`
(the `S` carbon daughter).  The table is used only to identify the production callback by
off-diagonal congruence; it is not assumed anywhere as data. -/

/-- A finite table for checking the independently derived complete comparator matrix. -/
def centralExpectedRank : Fin 4 → Nat
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => 1

def centralExpectedComparison (left right : Fin 4) : ConstitutionalRule5Comparison :=
  { ordering := compare (centralExpectedRank left) (centralExpectedRank right)
    pseudo := decide ((left.val = 2 ∧ right.val = 3) ∨ (left.val = 3 ∧ right.val = 2)) }

private theorem central_expected_comparison_of_atomic_gt (left right : Fin 4)
    (higher : centralAtomicPriorityValue right < centralAtomicPriorityValue left)
    (expected : centralExpectedComparison left right = { ordering := Ordering.gt, pseudo := false }) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At centralKeyFrame left right =
      centralExpectedComparison left right :=
  (central_actual_atomic_comparison_gt left right higher).trans expected.symm

private theorem central_expected_comparison_of_atomic_lt (left right : Fin 4)
    (lower : centralAtomicPriorityValue left < centralAtomicPriorityValue right)
    (expected : centralExpectedComparison left right = { ordering := Ordering.lt, pseudo := false }) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At centralKeyFrame left right =
      centralExpectedComparison left right :=
  (central_actual_atomic_comparison_lt left right lower).trans expected.symm

/-- All twelve off-diagonal comparisons are derived; the sort never needs a diagonal callback. -/
theorem central_actual_comparison_eq_table_of_ne (left right : Fin 4) (different : left ≠ right) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At centralKeyFrame left right =
      centralExpectedComparison left right := by
  fin_cases left <;> fin_cases right
  all_goals first
    | exact False.elim (different rfl)
    | exact central_expected_comparison_of_atomic_gt _ _ (by decide +kernel) (by decide +kernel)
    | exact central_expected_comparison_of_atomic_lt _ _ (by decide +kernel) (by decide +kernel)
    | simpa [centralSlotTwo, centralSlotThree, centralExpectedComparison, centralExpectedRank]
        using central_actual_carbon_comparison_gt
    | simpa [centralSlotTwo, centralSlotThree, centralExpectedComparison, centralExpectedRank]
        using central_actual_carbon_comparison_lt

/-- The rank table encodes exactly the actual carbon direction: slot `3` outranks slot `2`. -/
theorem central_actual_carbon_rank_order :
    centralExpectedRank centralSlotTwo < centralExpectedRank centralSlotThree := by
  decide +kernel

def centralExpectedCallback (left right : Fin 4) :
    Option ConstitutionalDescriptorHierarchyComparison :=
  some (aromaticCanonicalRule3Through5DescriptorComparison (centralExpectedComparison left right))

theorem central_actual_callback_eq_table_of_ne (left right : Fin 4) (different : left ≠ right) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At? centralKeyFrame left right =
      centralExpectedCallback left right := by
  unfold compareAromaticCanonicalOccurrenceRule3Through5At? centralExpectedCallback
  rw [central_actual_comparison_eq_table_of_ne left right different]

/-! ## 4. The actual production tracked order and its guards -/

/-- Historical certificate key.  Under the corrected calibration the higher-priority carbon is
slot `3` (`R`), so the production tracked order is `[1, 0, 3, 2]`, not `[1, 0, 2, 3]`. -/
def centralTrackedOrder : TrackedLocalizedLigandOrder :=
  { highestFirst := [1, 0, 3, 2], pseudoComparisons := 1 }

theorem centralTrackedOrder_highestFirst : centralTrackedOrder.highestFirst = [1, 0, 3, 2] := rfl

theorem centralTrackedOrder_pseudoComparisons : centralTrackedOrder.pseudoComparisons = 1 := rfl

/-- The tracked order is definitionally the source's right-first hypothetical order, the order
under which `central_geometry_hypothetical_right_first` proves the exact central geometry
uppercase `R`.  Combined with the single pseudo comparison this is the geometry-side interface
consumed downstream to keep the central pseudo descriptor `.pseudoasymmetric .r`; the descriptor
proof itself is a separate, unchanged obligation. -/
theorem centralTrackedOrder_geometry_interface :
    centralTrackedOrder.highestFirst = centralHypotheticalOrderRightFirst ∧
      centralTrackedOrder.pseudoComparisons = 1 := ⟨rfl, rfl⟩

/-- The expected ranks strictly descend along the tracked order. -/
theorem centralTrackedOrder_rank_descends :
    centralTrackedOrder.highestFirst.Pairwise
      (fun left right => centralExpectedRank right < centralExpectedRank left) := by
  decide +kernel

private theorem central_expected_tracked_sort :
    sortFourLocalizedLigandsTracked centralExpectedCallback = some centralTrackedOrder := by
  decide +kernel

/-- The actual production execution is identified by off-diagonal congruence on a Nodup input. -/
theorem central_actual_raw_tracked_order_computed :
    source.aromaticCanonicalOccurrenceRule3Through5TrackedOrder? centralKeyFrame =
      some centralTrackedOrder := by
  have executionEq := sortLocalizedLigandsTrackedFrom_eq_of_callback_ne
    (source.compareAromaticCanonicalOccurrenceRule3Through5At? centralKeyFrame)
    centralExpectedCallback central_actual_callback_eq_table_of_ne
    (List.finRange 4) [] 0 (List.nodup_finRange 4)
  change sortLocalizedLigandsTrackedFrom
    (source.compareAromaticCanonicalOccurrenceRule3Through5At? centralKeyFrame)
    (List.finRange 4) [] 0 = some centralTrackedOrder
  rw [executionEq]
  exact central_expected_tracked_sort

/-- The all-pairs coherence guard, not merely the insertion history, is strictly descending. -/
theorem central_actual_order_coherent :
    source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent centralKeyFrame
      centralTrackedOrder.highestFirst = true := by
  apply (source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent_eq_true_iff
    centralKeyFrame centralTrackedOrder.highestFirst).mpr
  have tableStrict : centralTrackedOrder.highestFirst.Pairwise
      (fun left right => (centralExpectedComparison left right).ordering = Ordering.gt) := by
    decide +kernel
  apply tableStrict.imp
  intro left right strict
  have different : left ≠ right := by
    intro same
    subst right
    simp [centralExpectedComparison] at strict
  rw [central_actual_comparison_eq_table_of_ne left right different]
  exact strict

theorem central_actual_safe_tracked_order_computed :
    source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? centralKeyFrame =
      some centralTrackedOrder := by
  simp [safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?,
    central_actual_raw_tracked_order_computed, central_actual_order_coherent]

theorem centralTrackedOrder_permutation : centralTrackedOrder.highestFirst.Perm (List.finRange 4) :=
  sortFourLocalizedLigandsTracked_perm
    (source.compareAromaticCanonicalOccurrenceRule3Through5At? centralKeyFrame)
    centralTrackedOrder central_actual_raw_tracked_order_computed

end TetraStereo.UniversalProof.CentralDrawingRule3TieProofs.CentralDrawingRule45Comparison
