import TetraStereo.OneCenter.LocalizedShortCircuitStrictOrder

set_option autoImplicit false
namespace TetraStereo.OneCenter
open CertifiedLocalizedCIPInput

/-- Strict rank agreement suffices for insertion. Actual Rule5 flags remain unrestricted and
their observed count is retained by the original production operation. -/
theorem insertLocalizedLigandTracked_total_of_strictOrdering
    (priority : Fin 4 → Nat) (injective : Function.Injective priority)
    (compareAt : Fin 4 → Fin 4 → Option ConstitutionalDescriptorHierarchyComparison)
    (ranked : ∀ left right, left ≠ right → ∃ comparison,
      compareAt left right = some comparison ∧
      comparison.ordering = compare (priority left) (priority right))
    (candidate : Fin 4) :
    ∀ existing : List (Fin 4), candidate ∉ existing →
      existing.Pairwise (fun left right => priority left < priority right) →
      ∃ result, insertLocalizedLigandTracked compareAt candidate existing = some result ∧
        result.lowestFirst.Perm (candidate :: existing) ∧
        result.lowestFirst.Pairwise (fun left right => priority left < priority right) := by
  intro existing
  induction existing with
  | nil =>
      intro _ _
      exact ⟨⟨[candidate], 0⟩, rfl, List.Perm.refl _, by simp⟩
  | cons low remaining ih =>
      intro fresh increasing
      have different : low ≠ candidate := by
        intro same
        exact fresh (by simp [same])
      have distinct : priority low ≠ priority candidate := fun equal => different (injective equal)
      obtain ⟨comparison, comparisonComputed, comparisonOrder⟩ := ranked low candidate different
      let observed := if comparison.pseudo then 1 else 0
      have tailIncreasing := (List.pairwise_cons.mp increasing).2
      have lowBefore := (List.pairwise_cons.mp increasing).1
      rcases Nat.lt_or_gt_of_ne distinct with lower | higher
      · have compared := comparisonOrder.trans (Nat.compare_eq_lt.mpr lower)
        have freshTail : candidate ∉ remaining := by
          intro member
          exact fresh (List.mem_cons_of_mem low member)
        obtain ⟨deeper, computed, perm, sorted⟩ := ih freshTail tailIncreasing
        refine ⟨⟨low :: deeper.lowestFirst, observed + deeper.pseudoComparisons⟩, ?_, ?_, ?_⟩
        · simp [insertLocalizedLigandTracked, comparisonComputed, compared, computed, observed]
        · exact (List.Perm.cons low perm).trans (List.Perm.swap _ _ _)
        · apply List.pairwise_cons.mpr
          refine ⟨?_, sorted⟩
          intro other member
          rcases List.mem_cons.mp (perm.mem_iff.mp member) with same | inTail
          · simpa [same] using lower
          · exact lowBefore other inTail
      · have compared := comparisonOrder.trans (Nat.compare_eq_gt.mpr higher)
        refine ⟨⟨candidate :: low :: remaining, observed⟩, ?_, List.Perm.refl _, ?_⟩
        · simp [insertLocalizedLigandTracked, comparisonComputed, compared, observed]
        · apply List.pairwise_cons.mpr
          refine ⟨?_, increasing⟩
          intro other member
          rcases List.mem_cons.mp member with same | inTail
          · simpa [same] using higher
          · exact lt_trans higher (lowBefore other inTail)

/-- Sorting distinct slots is total for any flags attached to the strict rank comparisons. -/
theorem sortLocalizedLigandsTrackedFrom_total_of_strictOrdering
    (priority : Fin 4 → Nat) (injective : Function.Injective priority)
    (compareAt : Fin 4 → Fin 4 → Option ConstitutionalDescriptorHierarchyComparison)
    (ranked : ∀ left right, left ≠ right → ∃ comparison,
      compareAt left right = some comparison ∧
      comparison.ordering = compare (priority left) (priority right)) :
    ∀ candidates lowestFirst : List (Fin 4), ∀ history : Nat,
      (lowestFirst ++ candidates).Nodup →
      lowestFirst.Pairwise (fun left right => priority left < priority right) →
      ∃ result, sortLocalizedLigandsTrackedFrom compareAt candidates lowestFirst history = some result ∧
        result.highestFirst.Perm (lowestFirst ++ candidates) ∧
        result.highestFirst.Pairwise (fun left right => priority right < priority left) := by
  intro candidates
  induction candidates with
  | nil =>
      intro lowestFirst history _ increasing
      refine ⟨⟨lowestFirst.reverse, history⟩, rfl, ?_, ?_⟩
      · simpa only [List.append_nil] using List.reverse_perm lowestFirst
      · exact List.pairwise_reverse.mpr increasing
  | cons candidate candidates ih =>
      intro lowestFirst history distinct increasing
      have fresh : candidate ∉ lowestFirst := by
        intro member
        exact (List.nodup_append.mp distinct).2.2 candidate member candidate (by simp) rfl
      obtain ⟨inserted, computed, perm, sorted⟩ :=
        insertLocalizedLigandTracked_total_of_strictOrdering priority injective compareAt ranked
          candidate lowestFirst fresh increasing
      have moved : (candidate :: lowestFirst ++ candidates).Perm
          (lowestFirst ++ candidate :: candidates) := List.perm_middle.symm
      have preserved : (inserted.lowestFirst ++ candidates).Perm
          (lowestFirst ++ candidate :: candidates) := (perm.append_right candidates).trans moved
      have nextDistinct := preserved.symm.nodup distinct
      obtain ⟨result, sortedComputed, outputPerm, outputSorted⟩ :=
        ih inserted.lowestFirst (history + inserted.pseudoComparisons) nextDistinct sorted
      refine ⟨result, ?_, outputPerm.trans preserved, outputSorted⟩
      simp [sortLocalizedLigandsTrackedFrom, computed, sortedComputed]

/-- No diagonal callback hypothesis, pseudo-flag restriction or assumed sort result is needed. -/
theorem sortFourLocalizedLigandsTracked_total_of_strictOrdering
    (priority : Fin 4 → Nat) (injective : Function.Injective priority)
    (compareAt : Fin 4 → Fin 4 → Option ConstitutionalDescriptorHierarchyComparison)
    (ranked : ∀ left right, left ≠ right → ∃ comparison,
      compareAt left right = some comparison ∧
      comparison.ordering = compare (priority left) (priority right)) :
    ∃ result, sortFourLocalizedLigandsTracked compareAt = some result ∧
      result.highestFirst.Perm (List.finRange 4) ∧
      result.highestFirst.Pairwise (fun left right => priority right < priority left) := by
  simpa [sortFourLocalizedLigandsTracked, sortLocalizedLigandsTracked] using
    sortLocalizedLigandsTrackedFrom_total_of_strictOrdering priority injective compareAt ranked
      (List.finRange 4) [] 0 (List.nodup_finRange 4) (by simp)

namespace CertifiedLocalizedCIPInput

/-- Complete Rule3-through-5 ordering constructs the production sort and passes the all-pairs
guard. Unlike the strict-Rule3 specialization, this allows decisive enantiomorphic comparisons. -/
theorem trackedOrder_total_of_strictOrdering
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame fuel)
    (priority : Fin 4 → Nat) (injective : Function.Injective priority)
    (ranked : ∀ left right, left ≠ right →
      (input.compareLocalizedOccurrenceRule3Through5At frame left right).ordering =
        compare (priority left) (priority right)) :
    ∃ tracked, input.localizedNoDoubleTrackedOrderExec? frame = some tracked ∧
      tracked.highestFirst.Perm (List.finRange 4) ∧
      tracked.highestFirst.Pairwise (fun left right => priority right < priority left) := by
  obtain ⟨tracked, computed, perm, sorted⟩ :=
    sortFourLocalizedLigandsTracked_total_of_strictOrdering priority injective
      (input.compareLocalizedOccurrenceRule3Through5At? frame)
      (fun left right different =>
        ⟨input.compareLocalizedOccurrenceRule3Through5At frame left right, rfl,
          ranked left right different⟩)
  have coherent : input.localizedOccurrenceRule3Through5OrderCoherent frame tracked.highestFirst = true := by
    apply (input.localizedOccurrenceRule3Through5OrderCoherent_eq_true_iff frame _).mpr
    apply sorted.imp
    intro left right lower
    have different : left ≠ right := by intro same; subst right; omega
    exact (ranked left right different).trans (Nat.compare_eq_gt.mpr lower)
  refine ⟨tracked, ?_, perm, sorted⟩
  rw [localizedNoDoubleTrackedOrderExec?_eq_safeLocalizedOccurrenceRule3Through5TrackedOrder?]
  simp [safeLocalizedOccurrenceRule3Through5TrackedOrder?,
    localizedOccurrenceRule3Through5TrackedOrder?, computed, coherent]

/-- An independent descending permutation fixes the spatial order while preserving the actual
executed pseudo-comparison count for the descriptor classifier. -/
theorem trackedOrder_total_at_ranked_order
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame fuel)
    (priority : Fin 4 → Nat) (injective : Function.Injective priority)
    (ranked : ∀ left right, left ≠ right →
      (input.compareLocalizedOccurrenceRule3Through5At frame left right).ordering =
        compare (priority left) (priority right))
    (order : List (Fin 4)) (permutation : order.Perm (List.finRange 4))
    (descending : order.Pairwise (fun left right => priority right < priority left)) :
    ∃ count, input.localizedNoDoubleTrackedOrderExec? frame =
      some { highestFirst := order, pseudoComparisons := count } := by
  obtain ⟨tracked, computed, perm, sorted⟩ :=
    input.trackedOrder_total_of_strictOrdering frame priority injective ranked
  have orderEqual : tracked.highestFirst = order := by
    apply List.Perm.eq_of_pairwise (fun _ _ _ _ h h' => False.elim (by omega))
      sorted descending (perm.trans permutation.symm)
  refine ⟨tracked.pseudoComparisons, ?_⟩
  rw [computed]
  congr 1
  cases tracked
  simp_all

end CertifiedLocalizedCIPInput

namespace TrackedOrderingRegression

def flaggedComparison (secondFlag : Bool) (left right : Fin 4) :
    Option ConstitutionalDescriptorHierarchyComparison :=
  if left = right then none else some
    { ordering := compare (TrackedStrictRankRegression.scatteredPriority left)
        (TrackedStrictRankRegression.scatteredPriority right)
      pseudo := (left == 0 && right == 1) || (secondFlag && left == 1 && right == 2) }

theorem one_observed_flag : sortFourLocalizedLigandsTracked (flaggedComparison false) =
    some { highestFirst := [2, 0, 3, 1], pseudoComparisons := 1 } := rfl

theorem two_observed_flags : sortFourLocalizedLigandsTracked (flaggedComparison true) =
    some { highestFirst := [2, 0, 3, 1], pseudoComparisons := 2 } := rfl

end TrackedOrderingRegression
end TetraStereo.OneCenter
