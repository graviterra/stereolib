import TetraStereo.OneCenter.DeclarativeCIPCompleteReadingSignature
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Adding the complete Rule-4c reading only refines ties between Rule-4b alternatives.
The count and Rule-4b part of the extended independent signature is exactly the previously
proved molecular ligand signature, including its empty-reference case. -/

namespace TetraStereo.OneCenter.DeclarativeCIP
noncomputable section
open scoped Classical
universe u

private theorem completeReading_fst_monotone :
    Monotone (fun key : CompleteReadingKey => (ofLex key).1) := by
  intro left right le
  rcases lt_or_eq_of_le le with lt | eq
  · rw [← toLex_ofLex left, ← toLex_ofLex right, Prod.Lex.lt_iff] at lt
    rcases lt with lt | ⟨eq, _⟩
    · exact lt.le
    · exact eq.le
  · exact (congrArg (fun key : CompleteReadingKey => (ofLex key).1) eq).le

private theorem completeReading_fst_max (left right : CompleteReadingKey) :
    (ofLex (max left right)).1 = max (ofLex left).1 (ofLex right).1 := by
  rcases le_total left right with le | le
  · rw [max_eq_right le, max_eq_right (completeReading_fst_monotone le)]
  · rw [max_eq_left le, max_eq_left (completeReading_fst_monotone le)]

private theorem completeReading_fst_min (left right : CompleteReadingKey) :
    (ofLex (min left right)).1 = min (ofLex left).1 (ofLex right).1 := by
  rcases le_total left right with le | le
  · rw [min_eq_left le, min_eq_left (completeReading_fst_monotone le)]
  · rw [min_eq_right le, min_eq_right (completeReading_fst_monotone le)]

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

theorem completeReading_compare_eq_then (left right : CompleteReadingKey) :
    compare left right =
      (compare (ofLex left).1 (ofLex right).1).then
        (compare (ofLex left).2 (ofLex right).2) := rfl

theorem completeReading_compare_eq_iff (left right : CompleteReadingKey) :
    compare left right = .eq ↔ left = right := by
  rw [completeReading_compare_eq_then, Ordering.then_eq_eq,
    key_compare_eq_iff, key_compare_eq_iff]
  constructor
  · rintro ⟨first, second⟩
    exact congrArg toLex (Prod.ext first second)
  · intro equal
    subst right
    exact ⟨rfl, rfl⟩

theorem completeReading_compare_lt_iff (left right : CompleteReadingKey) :
    compare left right = .lt ↔ left < right := by
  rw [completeReading_compare_eq_then, ← toLex_ofLex left, ← toLex_ofLex right, Prod.Lex.lt_iff]
  simp only [ofLex_toLex]
  cases h : compare (ofLex left).1 (ofLex right).1 with
  | lt => simp [Ordering.then, (key_compare_lt_iff _ _).1 h]
  | eq =>
      have equal := (key_compare_eq_iff _ _).1 h
      simp [Ordering.then, equal, key_compare_lt_iff]
  | gt =>
      have notLt : ¬ (ofLex left).1 < (ofLex right).1 := by
        intro strict
        have := (key_compare_lt_iff _ _).2 strict
        rw [h] at this
        contradiction
      have notEq : (ofLex left).1 ≠ (ofLex right).1 := by
        intro equal
        have := (key_compare_eq_iff _ _).2 equal
        rw [h] at this
        contradiction
      simp [Ordering.then, notLt, notEq]

/-- Runtime-style two-way sorting agrees with the independent maximum/minimum order. -/
theorem completeReading_descendingPair (left right : CompleteReadingKey) :
    (if compare left right = .lt then [right, left] else [left, right]) =
      [max left right, min left right] := by
  split_ifs with h
  · have strict := (completeReading_compare_lt_iff _ _).1 h
    rw [max_eq_right strict.le, min_eq_left strict.le]
  · have le : right ≤ left := le_of_not_gt (fun strict => h
        ((completeReading_compare_lt_iff _ _).2 strict))
    rw [max_eq_left le, min_eq_right le]

theorem completePriorSignatureAt_rule4b (W D : ℕ) :
    ((ofLex (completePriorSignatureAt molecule descriptorMap unit graph W D)).1,
      (ofLex (ofLex (completePriorSignatureAt molecule descriptorMap unit graph W D)).2).1) =
      ligandSignatureAt molecule descriptorMap unit graph W D := by
  unfold completePriorSignatureAt completeReadingsAt ligandSignatureAt
  cases referenceSelection molecule descriptorMap unit graph with
  | empty => rfl
  | one sense => rfl
  | both =>
      simp only [ReferenceSelection.countPriority, ofLex_toLex, reduceCtorEq,
        if_false, List.map_cons, List.map_nil]
      rw [completeReading_fst_max, completeReading_fst_min, descendingPair_eq_max_min]
      rfl

end
end TetraStereo.OneCenter.DeclarativeCIP

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completePriorSignatureAt_rule4b
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completeReading_compare_eq_then
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completeReading_compare_eq_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completeReading_compare_lt_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completeReading_descendingPair
