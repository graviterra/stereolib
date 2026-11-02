import TetraStereo.OneCenter.LocalizedPseudoasymmetricClassification

set_option autoImplicit false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput

/-!
Strict natural-number priorities make the actual tracked insertion sort total. These results
concern the supplied comparison callback. Chemical admission and identification of a production
callback with these priorities are separate obligations.
-/

/-- A strict atomic-priority callback has no enantiomorphic comparison history. -/
def strictRankComparison (priority : Fin 4 → ℕ) (left right : Fin 4) :
    Option ConstitutionalDescriptorHierarchyComparison :=
  some { ordering := compare (priority left) (priority right), pseudo := false }

/-- Inserting a fresh ligand into an increasing list succeeds, preserves all members, and
preserves strict ordering. No successful-execution hypothesis is supplied. -/
theorem insertLocalizedLigandTracked_strictRank_total
    (priority : Fin 4 → ℕ) (injective : Function.Injective priority)
    (candidate : Fin 4) :
    ∀ existing : List (Fin 4), candidate ∉ existing →
      existing.Pairwise (fun left right => priority left < priority right) →
      ∃ result, insertLocalizedLigandTracked (strictRankComparison priority)
          candidate existing = some result ∧
        result.lowestFirst.Perm (candidate :: existing) ∧
        result.lowestFirst.Pairwise (fun left right => priority left < priority right) ∧
        result.pseudoComparisons = 0 := by
  intro existing
  induction existing with
  | nil =>
      intro _ _
      exact ⟨⟨[candidate], 0⟩, rfl, List.Perm.refl _, by simp, rfl⟩
  | cons low remaining ih =>
      intro fresh increasing
      have different : priority low ≠ priority candidate := by
        intro equal
        have same := injective equal
        exact fresh (by simp [same])
      have tailIncreasing := (List.pairwise_cons.mp increasing).2
      have lowBefore := (List.pairwise_cons.mp increasing).1
      rcases Nat.lt_or_gt_of_ne different with lower | higher
      · have compared : compare (priority low) (priority candidate) = Ordering.lt :=
          Nat.compare_eq_lt.mpr lower
        have freshTail : candidate ∉ remaining := by
          intro member
          exact fresh (List.mem_cons_of_mem low member)
        obtain ⟨deeper, computed, perm, sorted, zero⟩ := ih freshTail tailIncreasing
        refine ⟨⟨low :: deeper.lowestFirst, 0⟩, ?_, ?_, ?_, rfl⟩
        · simp [insertLocalizedLigandTracked, strictRankComparison, compared,
            computed, zero]
        · exact (List.Perm.cons low perm).trans (List.Perm.swap _ _ _)
        · apply List.pairwise_cons.mpr
          refine ⟨?_, sorted⟩
          intro other member
          have membership := perm.mem_iff.mp member
          rcases List.mem_cons.mp membership with same | inTail
          · simpa [same] using lower
          · exact lowBefore other inTail
      · have compared : compare (priority low) (priority candidate) = Ordering.gt :=
          Nat.compare_eq_gt.mpr higher
        refine ⟨⟨candidate :: low :: remaining, 0⟩, ?_, List.Perm.refl _, ?_, rfl⟩
        · simp [insertLocalizedLigandTracked, strictRankComparison, compared]
        · apply List.pairwise_cons.mpr
          refine ⟨?_, increasing⟩
          intro other member
          rcases List.mem_cons.mp member with same | inTail
          · simpa [same] using higher
          · exact lt_trans higher (lowBefore other inTail)

/-- The actual recursive sorter terminates successfully on distinct ligand positions. Its
output is strictly decreasing in the independent rank, and the accumulated history is unchanged.
-/
theorem sortLocalizedLigandsTrackedFrom_strictRank_total
    (priority : Fin 4 → ℕ) (injective : Function.Injective priority) :
    ∀ candidates lowestFirst : List (Fin 4), ∀ pseudoComparisons : ℕ,
      (lowestFirst ++ candidates).Nodup →
      lowestFirst.Pairwise (fun left right => priority left < priority right) →
      ∃ result,
        sortLocalizedLigandsTrackedFrom (strictRankComparison priority)
            candidates lowestFirst pseudoComparisons = some result ∧
        result.highestFirst.Perm (lowestFirst ++ candidates) ∧
        result.highestFirst.Pairwise (fun left right => priority right < priority left) ∧
        result.pseudoComparisons = pseudoComparisons := by
  intro candidates
  induction candidates with
  | nil =>
      intro lowestFirst history _ increasing
      refine ⟨⟨lowestFirst.reverse, history⟩, rfl, ?_, ?_, rfl⟩
      · simp only [List.append_nil]
        exact List.reverse_perm lowestFirst
      · exact List.pairwise_reverse.mpr increasing
  | cons candidate candidates ih =>
      intro lowestFirst history distinct increasing
      have fresh : candidate ∉ lowestFirst := by
        intro member
        exact (List.nodup_append.mp distinct).2.2 candidate member candidate
          (by simp) rfl
      obtain ⟨inserted, computed, perm, sorted, zero⟩ :=
        insertLocalizedLigandTracked_strictRank_total priority injective candidate
          lowestFirst fresh increasing
      have moved : (candidate :: lowestFirst ++ candidates).Perm
          (lowestFirst ++ candidate :: candidates) := List.perm_middle.symm
      have preserved : (inserted.lowestFirst ++ candidates).Perm
          (lowestFirst ++ candidate :: candidates) :=
        (perm.append_right candidates).trans moved
      have nextDistinct := preserved.symm.nodup distinct
      obtain ⟨result, sortedComputed, outputPerm, outputSorted, historyExact⟩ :=
        ih inserted.lowestFirst history nextDistinct sorted
      refine ⟨result, ?_, outputPerm.trans preserved, outputSorted, historyExact⟩
      simp [sortLocalizedLigandsTrackedFrom, computed, zero, sortedComputed]

/-- Four distinct priorities suffice for successful production sorting, exact preservation of
the four canonical slots, all-pairs strict descending order, and zero pseudo comparisons. -/
theorem sortFourLocalizedLigandsTracked_strictRank_total
    (priority : Fin 4 → ℕ) (injective : Function.Injective priority) :
    ∃ result,
      sortFourLocalizedLigandsTracked (strictRankComparison priority) = some result ∧
      result.highestFirst.Perm (List.finRange 4) ∧
      result.highestFirst.Pairwise (fun left right => priority right < priority left) ∧
      result.pseudoComparisons = 0 := by
  simpa [sortFourLocalizedLigandsTracked, sortLocalizedLigandsTracked] using
    sortLocalizedLigandsTrackedFrom_strictRank_total priority injective
      (List.finRange 4) [] 0 (List.nodup_finRange 4) (by simp)

/-- Identification with a real comparison callback transports the totality theorem. -/
theorem sortFourLocalizedLigandsTracked_total_of_strictRank_callback
    (priority : Fin 4 → ℕ) (injective : Function.Injective priority)
    (compareAt : Fin 4 → Fin 4 → Option ConstitutionalDescriptorHierarchyComparison)
    (compared : ∀ left right, compareAt left right = strictRankComparison priority left right) :
    ∃ result,
      sortFourLocalizedLigandsTracked compareAt = some result ∧
      result.highestFirst.Perm (List.finRange 4) ∧
      result.highestFirst.Pairwise (fun left right => priority right < priority left) ∧
      result.pseudoComparisons = 0 := by
  have equality : compareAt = strictRankComparison priority := funext fun left =>
    funext fun right => compared left right
  rw [equality]
  exact sortFourLocalizedLigandsTracked_strictRank_total priority injective

/-- Inserting a fresh candidate never compares a slot with itself, so callback equality away
from the diagonal suffices to identify the actual execution, including failure. -/
theorem insertLocalizedLigandTracked_eq_of_callback_ne
    (compareAt compareOther :
      Fin 4 → Fin 4 → Option ConstitutionalDescriptorHierarchyComparison)
    (compared : ∀ left right, left ≠ right → compareAt left right = compareOther left right)
    (candidate : Fin 4) :
    ∀ existing : List (Fin 4), candidate ∉ existing →
      insertLocalizedLigandTracked compareAt candidate existing =
        insertLocalizedLigandTracked compareOther candidate existing := by
  intro existing
  induction existing with
  | nil => intro _; rfl
  | cons low remaining ih =>
      intro fresh
      have different : low ≠ candidate := by
        intro same
        exact fresh (by simp [same])
      have freshTail : candidate ∉ remaining := by
        intro member
        exact fresh (List.mem_cons_of_mem low member)
      simp only [insertLocalizedLigandTracked, compared low candidate different, ih freshTail]



theorem sortLocalizedLigandsTrackedFrom_eq_of_callback_ne
    (compareAt compareOther :
      Fin 4 → Fin 4 → Option ConstitutionalDescriptorHierarchyComparison)
    (compared : ∀ left right, left ≠ right → compareAt left right = compareOther left right) :
    ∀ candidates lowestFirst : List (Fin 4), ∀ history : ℕ,
      (lowestFirst ++ candidates).Nodup →
      sortLocalizedLigandsTrackedFrom compareAt candidates lowestFirst history =
        sortLocalizedLigandsTrackedFrom compareOther candidates lowestFirst history := by
  intro candidates
  induction candidates with
  | nil => intro _ _ _; rfl
  | cons candidate candidates ih =>
      intro lowestFirst history distinct
      have fresh : candidate ∉ lowestFirst := by
        intro member
        exact (List.nodup_append.mp distinct).2.2 candidate member candidate
          (by simp) rfl
      have insertionEqual := insertLocalizedLigandTracked_eq_of_callback_ne
        compareAt compareOther compared candidate lowestFirst fresh
      cases computed : insertLocalizedLigandTracked compareOther candidate lowestFirst with
      | none => simp [sortLocalizedLigandsTrackedFrom, insertionEqual, computed]
      | some inserted =>
          have perm := (insertLocalizedLigandTracked_sound compareOther candidate
            lowestFirst inserted computed).perm
          have moved : (candidate :: lowestFirst ++ candidates).Perm
              (lowestFirst ++ candidate :: candidates) := List.perm_middle.symm
          have preserved : (inserted.lowestFirst ++ candidates).Perm
              (lowestFirst ++ candidate :: candidates) :=
            (perm.append_right candidates).trans moved
          have nextDistinct := preserved.symm.nodup distinct
          simp only [sortLocalizedLigandsTrackedFrom, insertionEqual, computed]
          exact ih inserted.lowestFirst (history + inserted.pseudoComparisons) nextDistinct

/-- A production callback need only agree with strict atomic ranks on distinct slots. Its
diagonal may fail or take another rule branch without affecting this successful sort. -/
theorem sortFourLocalizedLigandsTracked_total_of_strictRank_callback_ne
    (priority : Fin 4 → ℕ) (injective : Function.Injective priority)
    (compareAt : Fin 4 → Fin 4 → Option ConstitutionalDescriptorHierarchyComparison)
    (compared : ∀ left right, left ≠ right →
      compareAt left right = strictRankComparison priority left right) :
    ∃ result,
      sortFourLocalizedLigandsTracked compareAt = some result ∧
      result.highestFirst.Perm (List.finRange 4) ∧
      result.highestFirst.Pairwise (fun left right => priority right < priority left) ∧
      result.pseudoComparisons = 0 := by
  have executionEqual := sortLocalizedLigandsTrackedFrom_eq_of_callback_ne
    compareAt (strictRankComparison priority) compared (List.finRange 4) [] 0
      (List.nodup_finRange 4)
  change ∃ result,
    sortLocalizedLigandsTrackedFrom compareAt (List.finRange 4) [] 0 = some result ∧ _
  rw [executionEqual]
  exact sortFourLocalizedLigandsTracked_strictRank_total priority injective

namespace TrackedStrictRankRegression

def scatteredPriority (slot : Fin 4) : ℕ :=
  match slot.val with
  | 0 => 17
  | 1 => 2
  | 2 => 31
  | _ => 9

def relabeledPriority (slot : Fin 4) : ℕ :=
  match slot.val with
  | 0 => 9
  | 1 => 31
  | 2 => 2
  | _ => 17

theorem scatteredPriority_injective : Function.Injective scatteredPriority := by
  decide

theorem relabeledPriority_injective : Function.Injective relabeledPriority := by
  decide

/-- The largest rank is not the first or last canonical slot. -/
theorem scatteredPriority_actual_order :
    sortFourLocalizedLigandsTracked (strictRankComparison scatteredPriority) =
      some { highestFirst := [2, 0, 3, 1], pseudoComparisons := 0 } := by
  rfl

/-- Relabeling the rank assignment changes the actual output order. -/
theorem relabeledPriority_actual_order :
    sortFourLocalizedLigandsTracked (strictRankComparison relabeledPriority) =
      some { highestFirst := [1, 3, 0, 2], pseudoComparisons := 0 } := by
  rfl

def scatteredNoDiagonal (left right : Fin 4) :
    Option ConstitutionalDescriptorHierarchyComparison :=
  if left = right then none else strictRankComparison scatteredPriority left right

/-- A callback that explicitly refuses every diagonal still sorts the four distinct slots. -/
theorem diagonal_refusal_does_not_block_actual_sort :
    sortFourLocalizedLigandsTracked scatteredNoDiagonal =
      some { highestFirst := [2, 0, 3, 1], pseudoComparisons := 0 } := by
  rfl

/-- A tie is refused by the actual insertion operation. -/
theorem tied_insertion_refused :
    insertLocalizedLigandTracked (strictRankComparison (fun _ => 6)) 1 [0] = none := by
  rfl

/-- Four tied ranks cannot manufacture an arbitrary successful canonical order. -/
theorem tied_four_slot_sort_refused :
    sortFourLocalizedLigandsTracked (strictRankComparison (fun _ => 6)) = none := by
  rfl

end TrackedStrictRankRegression

end TetraStereo.OneCenter
