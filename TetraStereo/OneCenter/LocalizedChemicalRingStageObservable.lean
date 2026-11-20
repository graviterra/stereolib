import TetraStereo.OneCenter.LocalizedChemicalRingDecodedRelation
import TetraStereo.OneCenter.LocalizedRuleMajorStagePrefix
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! The complete fixed-width rule-major columns recover the comparison-visible cumulative
observable. Consequently sorting permuted child observations gives the same observed order.
Source identities and raw ranked-label order are deliberately not part of this result. -/

namespace TetraStereo.OneCenter.LocalizedChemicalRingStageObservable

open CertifiedLocalizedCIPInput OfficialRuleMajorKey

private theorem lists_eq_of_coordinate_maps {α β : Type*} (width : Nat) (positive : 0 < width)
    (coordinate : Nat → α → β) : ∀ (left right : List α),
    (∀ i, i < width → left.map (coordinate i) = right.map (coordinate i)) →
    (∀ a ∈ left, ∀ b ∈ right, (∀ i, i < width → coordinate i a = coordinate i b) → a = b) →
    left = right
  | [], [], _, _ => rfl
  | [], _ :: _, same, _ => by simpa using same 0 positive
  | _ :: _, [], same, _ => by simpa using same 0 positive
  | a :: left, b :: right, same, injective => by
      have head := injective a (by simp) b (by simp) (fun i hi => (List.cons.inj (same i hi)).1)
      have tail := lists_eq_of_coordinate_maps width positive coordinate left right
        (fun i hi => (List.cons.inj (same i hi)).2)
        (fun x hx y hy => injective x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem b hy))
      rw [head, tail]

def Shaped (width : Nat) (table : List (List (OfficialSparseEntry (List Nat)))) : Prop :=
  ∀ row ∈ table, ∀ entry ∈ row, entry.2.length = width

theorem descriptor_eq_of_columns (width : Nat) (positive : 0 < width)
    (left right : List (List (OfficialSparseEntry (List Nat))))
    (shapeL : Shaped width left) (shapeR : Shaped width right)
    (same : ∀ i, i < width → projectCumulative i left = projectCumulative i right) : left = right := by
  apply lists_eq_of_coordinate_maps
    (α := List (OfficialSparseEntry (List Nat))) (β := List (OfficialSparseEntry Nat)) width positive
    (fun i (row : List (OfficialSparseEntry (List Nat))) =>
      row.map (fun (entry : OfficialSparseEntry (List Nat)) => (entry.1, entry.2.getD i 0)))
    left right same
  intro rowL memL rowR memR rowSame
  apply lists_eq_of_coordinate_maps width positive
    (fun i (entry : OfficialSparseEntry (List Nat)) => (entry.1, entry.2.getD i 0)) rowL rowR rowSame
  intro entryL inL entryR inR entries
  apply Prod.ext
  · exact congrArg (fun entry : OfficialSparseEntry Nat => entry.1) (entries 0 positive)
  · apply List.ext_getElem ((shapeL rowL memL entryL inL).trans (shapeR rowR memR entryR inR).symm)
    intro i hi hj
    have bound : i < width := by simpa [shapeL rowL memL entryL inL] using hi
    have observed := congrArg Prod.snd (entries i bound)
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hj, Option.getD_some] using observed

variable {input : CertifiedLocalizedCIPInput}

theorem observable_eq_of_prefix (width : Nat) (positive : 0 < width)
    (left right : input.LocalizedRerootCumulativeRule45Key)
    (shapeL : Shaped width left.descriptor) (shapeR : Shaped width right.descriptor)
    (same : input.ruleMajorPrefixObservable width left = input.ruleMajorPrefixObservable width right) :
    input.localizedRerootCumulativeRule45Observable left =
      input.localizedRerootCumulativeRule45Observable right := by
  have columns := congrArg RuleMajorPrefixObservable.columns same
  have descriptor := descriptor_eq_of_columns width positive left.descriptor right.descriptor shapeL shapeR
    (fun i hi => by
      have h := congrArg (fun xs => xs[i]?) columns
      simpa [ruleMajorPrefixObservable, ruleMajorCumulativeColumns, List.getElem?_map, hi] using h)
  simp only [localizedRerootCumulativeRule45Observable, LocalizedCumulativeRule45Observable.mk.injEq]
  exact ⟨(congrArg RuleMajorPrefixObservable.rule1a same),
    (congrArg RuleMajorPrefixObservable.rule1b same),
    (congrArg RuleMajorPrefixObservable.rule2 same), descriptor⟩

private def prefixOfObservable (width : Nat) (obs : LocalizedCumulativeRule45Observable) :
    RuleMajorPrefixObservable input.Atom where
  rule1a := obs.rule1a
  rule1b := obs.rule1b
  rule2 := obs.rule2
  columns := (List.range width).map (fun i => projectCumulative i obs.descriptor)

private theorem map_eq_of_map_eq {α β γ : Type*} (f : α → β) (g : α → γ) :
    ∀ (left right : List α), left.map g = right.map g →
      (∀ a ∈ left, ∀ b ∈ right, g a = g b → f a = f b) → left.map f = right.map f
  | [], [], _, _ => rfl
  | [], _ :: _, same, _ => by cases same
  | _ :: _, [], same, _ => by cases same
  | a :: left, b :: right, same, compatible => by
      have pair := List.cons.inj same
      simp only [List.map_cons]
      rw [compatible a (by simp) b (by simp) pair.1,
        map_eq_of_map_eq f g left right pair.2
          (fun x hx y hy => compatible x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem b hy))]

/-- The current whole-rule sort is invariant on comparison-visible observables under a
permutation of well-shaped child observations. Exact child records need not be equal. -/
theorem sorted_observables_eq (width : Nat) (positive : 0 < width)
    (left right : List input.LocalizedRerootCumulativeRule45Key)
    (shapeL : ∀ key ∈ left, Shaped width key.descriptor)
    (shapeR : ∀ key ∈ right, Shaped width key.descriptor)
    (perm : (left.map input.localizedRerootCumulativeRule45Observable).Perm
      (right.map input.localizedRerootCumulativeRule45Observable)) :
    ((sortKeysBy (input.compareRuleMajorCumulativeDescriptor width) left).map
      input.localizedRerootCumulativeRule45Observable) =
    ((sortKeysBy (input.compareRuleMajorCumulativeDescriptor width) right).map
      input.localizedRerootCumulativeRule45Observable) := by
  have prefixPerm : (left.map (input.ruleMajorPrefixObservable width)).Perm
      (right.map (input.ruleMajorPrefixObservable width)) := by
    simpa only [List.map_map] using perm.map (prefixOfObservable (input := input) width)
  have sortedPrefix := ruleMajorPrefixObservable_sorted_perm_unique _ _
    ((input.ruleMajorPrefixObservable_sort_perm width left).trans
      (prefixPerm.trans (input.ruleMajorPrefixObservable_sort_perm width right).symm))
    (input.ruleMajorPrefixObservable_sort_pairwise width left)
    (input.ruleMajorPrefixObservable_sort_pairwise width right)
  apply map_eq_of_map_eq input.localizedRerootCumulativeRule45Observable
    (input.ruleMajorPrefixObservable width) _ _ sortedPrefix
  intro a ha b hb same
  exact observable_eq_of_prefix width positive a b
    (shapeL a ((input.sortKeysBy_ruleMajorCumulative_perm width left).mem_iff.mp ha))
    (shapeR b ((input.sortKeysBy_ruleMajorCumulative_perm width right).mem_iff.mp hb)) same

end TetraStereo.OneCenter.LocalizedChemicalRingStageObservable

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStageObservable.descriptor_eq_of_columns
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStageObservable.observable_eq_of_prefix
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingStageObservable.sorted_observables_eq
