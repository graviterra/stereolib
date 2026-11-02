import TetraStereo.OneCenter.LocalizedRuleMajorActualFrameComparison
import TetraStereo.OneCenter.TrackedLocalizedLigandSortOrderingCompleteness
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Exact success and refusal of the actual four-ligand safe sort. Distinctness is tested on
independent complete molecular keys; comparison success, ordering laws, and the all-pairs
guard are derived. The tracked pseudo count is retained without a physical interpretation. -/

namespace TetraStereo.OneCenter.LocalizedRuleMajorReference
open CertifiedLocalizedCIPInput DeclarativeCIP
noncomputable section
open scoped Classical

namespace GeneratedRuleMajorFrameComparisonData

variable {input : Input} {center : input.certified.TetrahedralCenter}
  (frames : GeneratedRuleMajorFrameComparisonData input center)

def actualCallback : Fin 4 → Fin 4 → Option ConstitutionalDescriptorHierarchyComparison :=
  input.certified.compareRuleMajorOccurrenceExecAt? (generatedTarget input center)
    (input.certified.localizedDependencyView (referenceState input)
      (generatedTarget input center)) frames.frame

def slotRank (slot : Fin 4) : Nat := frames.data.rank (frames.ligandToSlot.symm slot)

theorem safeOrder_exists (distinct : Function.Injective frames.data.fullKey) :
    ∃ tracked, safeTrackedOrderOrderedExecOf frames.actualCallback = some tracked ∧
      tracked.highestFirst.Perm (List.finRange 4) ∧
      tracked.highestFirst.Pairwise (fun left right =>
        frames.data.fullKey (frames.ligandToSlot.symm right) <
          frames.data.fullKey (frames.ligandToSlot.symm left)) := by
  have rankInjective : Function.Injective frames.slotRank := by
    intro left right equal
    apply frames.ligandToSlot.symm.injective
    apply distinct
    exact (frames.data.rank_eq_iff_fullKey_eq _ _).mp equal
  have ranked : ∀ left right : Fin 4, left ≠ right → ∃ result,
      frames.actualCallback left right = some result ∧
      result.ordering = compare (frames.slotRank left) (frames.slotRank right) := by
    intro left right _
    obtain ⟨result, computed, _, ordering, _⟩ := frames.callback_success left right
    exact ⟨result, computed, ordering⟩
  obtain ⟨tracked, computed, permutation, sorted⟩ :=
    sortFourLocalizedLigandsTracked_total_of_strictOrdering
      frames.slotRank rankInjective frames.actualCallback ranked
  have coherent : orderCoherentOf frames.actualCallback tracked.highestFirst = true := by
    apply (orderCoherentOf_eq_true_iff _ _).mpr
    apply sorted.imp
    intro left right higher
    have different : left ≠ right := by intro equal; subst right; omega
    obtain ⟨result, comparison, ordering⟩ := ranked left right different
    exact ⟨result, comparison, ordering.trans (Nat.compare_eq_gt.mpr higher)⟩
  refine ⟨tracked, ?_, permutation, ?_⟩
  · rw [safeTrackedOrderOrderedExecOf_eq]
    simp [safeTrackedOrderOf, computed, coherent]
  · exact sorted.imp fun higher => (frames.data.rank_lt_iff_fullKey_lt _ _).mp higher

theorem safeOrder_eq_none_of_not_injective
    (notDistinct : ¬ Function.Injective frames.data.fullKey) :
    safeTrackedOrderOrderedExecOf frames.actualCallback = none := by
  have witnesses : ∃ left right, frames.data.fullKey left = frames.data.fullKey right ∧
      left ≠ right := by
    by_contra absent
    apply notDistinct
    intro left right equal
    by_contra different
    exact absent ⟨left, right, equal, different⟩
  obtain ⟨left, right, equal, different⟩ := witnesses
  have slotsDifferent : frames.ligandToSlot left ≠ frames.ligandToSlot right :=
    fun same => different (frames.ligandToSlot.injective same)
  have tied : ∀ a b, frames.data.fullKey a = frames.data.fullKey b →
      ∃ result, frames.actualCallback (frames.ligandToSlot a) (frames.ligandToSlot b) =
        some result ∧ result.ordering = .eq := by
    intro a b keyEq
    obtain ⟨result, computed, ordering, _, _⟩ :=
      frames.callback_success (frames.ligandToSlot a) (frames.ligandToSlot b)
    refine ⟨result, computed, ?_⟩
    apply ordering.trans
    apply (completeLigandRule5Key_compare_eq_iff _ _).mpr
    simpa only [Equiv.symm_apply_apply] using keyEq
  rw [safeTrackedOrderOrderedExecOf_eq]
  exact safeTrackedOrderOf_eq_none_of_tie frames.actualCallback slotsDifferent
    (tied left right equal) (tied right left equal.symm)

/-- Exact success criterion for the executable safe sort, with no assumptions about flags. -/
theorem safeOrder_success_iff :
    (∃ tracked, safeTrackedOrderOrderedExecOf frames.actualCallback = some tracked) ↔
      Function.Injective frames.data.fullKey := by
  constructor
  · rintro ⟨tracked, computed⟩
    by_contra notDistinct
    rw [frames.safeOrder_eq_none_of_not_injective notDistinct] at computed
    cases computed
  · intro distinct
    obtain ⟨tracked, computed, _, _⟩ := frames.safeOrder_exists distinct
    exact ⟨tracked, computed⟩

end GeneratedRuleMajorFrameComparisonData
end
end TetraStereo.OneCenter.LocalizedRuleMajorReference

assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFrameComparisonData.safeOrder_exists
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFrameComparisonData.safeOrder_eq_none_of_not_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFrameComparisonData.safeOrder_success_iff
