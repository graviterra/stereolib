import TetraStereo.OneCenter.TrackedLocalizedLigandSortOrderingCompleteness
import TetraStereo.OneCenter.LocalizedTerminalLigandTieRefusal

set_option autoImplicit false
namespace TetraStereo.OneCenter

/-- A finite comparator supplies its own natural-number priority by counting smaller elements. -/
def comparisonRank {α : Type*} [Fintype α] (cmp : α → α → Ordering) (a : α) : Nat :=
  (Finset.univ.filter fun b => cmp b a = .lt).card

theorem comparisonRank_lt {α : Type*} [Fintype α]
    (cmp : α → α → Ordering) [Std.TransCmp cmp] {a b : α}
    (less : cmp a b = .lt) : comparisonRank cmp a < comparisonRank cmp b := by
  have subset : (Finset.univ.filter fun x => cmp x a = .lt) ⊆
      (Finset.univ.filter fun x => cmp x b = .lt) := by
    intro x member
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member ⊢
    exact Std.TransCmp.lt_trans member less
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset subset).mpr
  refine ⟨a, ?_, ?_⟩
  · simp [less]
  · simp [Std.ReflCmp.compare_self (cmp := cmp)]

/-- Separation plus the existing comparator laws identify all computed ranks exactly. -/
theorem comparisonRank_ordering {α : Type*} [Fintype α]
    (cmp : α → α → Ordering) [Std.TransCmp cmp]
    (separated : ∀ a b, a ≠ b → cmp a b ≠ .eq) (a b : α) :
    cmp a b = compare (comparisonRank cmp a) (comparisonRank cmp b) := by
  cases compared : cmp a b with
  | lt => exact (Nat.compare_eq_lt.mpr (comparisonRank_lt cmp compared)).symm
  | gt => exact (Nat.compare_eq_gt.mpr
      (comparisonRank_lt cmp (Std.OrientedCmp.lt_of_gt compared))).symm
  | eq =>
      have same : a = b := by
        by_contra different
        exact separated a b different compared
      subst b
      simp

theorem comparisonRank_injective {α : Type*} [Fintype α]
    (cmp : α → α → Ordering) [Std.TransCmp cmp]
    (separated : ∀ a b, a ≠ b → cmp a b ≠ .eq) : Function.Injective (comparisonRank cmp) := by
  intro a b equal
  have compared : cmp a b = .eq := by
    simpa [equal] using comparisonRank_ordering cmp separated a b
  by_contra different
  exact separated a b different compared

namespace CertifiedLocalizedCIPInput

def fullComparisonRank (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame fuel) : Fin 4 → Nat :=
  comparisonRank fun a b => (input.compareLocalizedOccurrenceRule3Through5At frame a b).ordering

def FullComparisonSeparated (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame fuel) : Prop :=
  ∀ a b : Fin 4, a ≠ b → (input.compareLocalizedOccurrenceRule3Through5At frame a b).ordering ≠ .eq

instance fullComparisonSeparatedDecidable (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame fuel) :
    Decidable (input.FullComparisonSeparated frame) := by
  unfold FullComparisonSeparated
  infer_instance

theorem fullComparisonRank_constructed (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame fuel)
    (separated : input.FullComparisonSeparated frame) :
    Function.Injective (input.fullComparisonRank frame) ∧
      ∀ a b, (input.compareLocalizedOccurrenceRule3Through5At frame a b).ordering =
        compare (input.fullComparisonRank frame a) (input.fullComparisonRank frame b) := by
  let cmp := fun a b => (input.compareLocalizedOccurrenceRule3Through5At frame a b).ordering
  letI : Std.TransCmp cmp := input.compareLocalizedOccurrenceRule3Through5At_transCmp frame
  exact ⟨comparisonRank_injective cmp separated, comparisonRank_ordering cmp separated⟩

/-- The finite twelve-pair non-tie condition constructs a successful production order, including
the actual Rule5 history. No ranking function or successful sorting result is supplied. -/
theorem trackedOrder_total_of_separated (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame fuel)
    (separated : input.FullComparisonSeparated frame) :
    ∃ tracked, input.localizedNoDoubleTrackedOrderExec? frame = some tracked ∧
      tracked.highestFirst.Perm (List.finRange 4) ∧
      tracked.highestFirst.Pairwise (fun a b =>
        input.fullComparisonRank frame b < input.fullComparisonRank frame a) := by
  obtain ⟨injective, ranked⟩ := input.fullComparisonRank_constructed frame separated
  exact input.trackedOrder_total_of_strictOrdering frame (input.fullComparisonRank frame)
    injective (fun a b _ => ranked a b)

/-- A complete tied pair rules out the strict production order. -/
theorem trackedOrder_none_of_not_separated (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame fuel)
    (notSeparated : ¬ input.FullComparisonSeparated frame) :
    input.localizedNoDoubleTrackedOrderExec? frame = none := by
  unfold FullComparisonSeparated at notSeparated
  push_neg at notSeparated
  obtain ⟨left, right, different, tied⟩ := notSeparated
  have forward : input.compareLocalizedOccurrenceRule3Through5Keys
      (frame.keyAt left) (frame.keyAt right) = .eq := by
    rw [← input.compareLocalizedOccurrenceRule3Through5At_ordering frame left right]
    exact tied
  letI := input.compareLocalizedOccurrenceRule3Through5Keys_transCmp
  exact TerminalTie.trackedOrder_none_of_tie input frame left right different forward
    (Std.OrientedCmp.eq_symm forward)

/-- Exact complete success/refusal boundary for every already compiled full key frame. -/
theorem trackedOrder_isSome_iff_separated (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame fuel) :
    (input.localizedNoDoubleTrackedOrderExec? frame).isSome = true ↔
      input.FullComparisonSeparated frame := by
  constructor
  · intro computed
    by_contra notSeparated
    rw [input.trackedOrder_none_of_not_separated frame notSeparated] at computed
    cases computed
  · intro separated
    obtain ⟨tracked, computed, _, _⟩ := input.trackedOrder_total_of_separated frame separated
    simp [computed]

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
