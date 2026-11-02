import TetraStereo.OneCenter.LocalizedShortCircuitDescriptor
import TetraStereo.OneCenter.TrackedLocalizedLigandSortCompleteness

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- A strict Rule3 ranking fixes the full comparison, independently of all later-rule keys. -/
theorem fullComparison_eq_strictRank_of_rule3
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (priority : Fin 4 → Nat) (injective : Function.Injective priority)
    (ranked : ∀ left right, left ≠ right →
      input.compareLocalizedRerootRecursiveRule3SpatialKeys
        (frame.keyAt left).rule3 (frame.keyAt right).rule3 = compare (priority left) (priority right)) :
    ∀ left right, left ≠ right →
      input.compareLocalizedOccurrenceRule3Through5At? frame left right =
        strictRankComparison priority left right := by
  intro left right different
  have distinct : priority left ≠ priority right := fun equal => different (injective equal)
  rcases Nat.lt_or_gt_of_ne distinct with lower | higher
  · have compared := Nat.compare_eq_lt.mpr lower
    simp [compareLocalizedOccurrenceRule3Through5At?, compareLocalizedOccurrenceRule3Through5At,
      ranked left right different, strictRankComparison, compared]
  · have compared := Nat.compare_eq_gt.mpr higher
    simp [compareLocalizedOccurrenceRule3Through5At?, compareLocalizedOccurrenceRule3Through5At,
      ranked left right different, strictRankComparison, compared]

/-- Strict Rule3 ranks construct the production tracked order and pass its all-pairs guard.
The independently supplied rank order fixes the geometry order; no sort success is assumed. -/
theorem trackedOrder_total_of_strictRule3
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel)
    (priority : Fin 4 → Nat) (injective : Function.Injective priority)
    (ranked : ∀ left right, left ≠ right →
      input.compareLocalizedRerootRecursiveRule3SpatialKeys
        (frame.keyAt left).rule3 (frame.keyAt right).rule3 = compare (priority left) (priority right))
    (order : List (Fin 4)) (permutation : order.Perm (List.finRange 4))
    (descending : order.Pairwise (fun left right => priority right < priority left)) :
    input.localizedNoDoubleTrackedOrderExec? frame =
      some { highestFirst := order, pseudoComparisons := 0 } := by
  have callback := input.fullComparison_eq_strictRank_of_rule3 frame priority injective ranked
  obtain ⟨tracked, computed, perm, sorted, history⟩ :=
    sortFourLocalizedLigandsTracked_total_of_strictRank_callback_ne
      priority injective (input.compareLocalizedOccurrenceRule3Through5At? frame) callback
  have orderEqual : tracked.highestFirst = order := by
    apply List.Perm.eq_of_pairwise (fun _ _ _ _ h h' => False.elim (by omega))
      sorted descending (perm.trans permutation.symm)
  have coherent : input.localizedOccurrenceRule3Through5OrderCoherent frame tracked.highestFirst = true := by
    apply (input.localizedOccurrenceRule3Through5OrderCoherent_eq_true_iff frame _).mpr
    apply sorted.imp
    intro left right lower
    have different : left ≠ right := by intro equal; subst right; omega
    have compared := callback left right different
    have ordering := congrArg (fun result => result.map fun record => record.ordering) compared
    simpa [compareLocalizedOccurrenceRule3Through5At?, strictRankComparison,
      Nat.compare_eq_gt.mpr lower] using ordering
  have trackedEqual : tracked = { highestFirst := order, pseudoComparisons := 0 } := by
    cases tracked
    simp_all
  have coherentOrder : input.localizedOccurrenceRule3Through5OrderCoherent frame order = true := by
    simpa only [orderEqual] using coherent
  rw [localizedNoDoubleTrackedOrderExec?_eq_safeLocalizedOccurrenceRule3Through5TrackedOrder?]
  simp [safeLocalizedOccurrenceRule3Through5TrackedOrder?,
    localizedOccurrenceRule3Through5TrackedOrder?, computed, trackedEqual, coherentOrder]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
