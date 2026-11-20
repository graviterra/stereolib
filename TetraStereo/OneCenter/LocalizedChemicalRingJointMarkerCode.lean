import Mathlib.Data.List.Basic
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
A joint marker observation for an ordered list of retained atoms.

An occurrence names at most one atom, so its entire membership vector can be encoded by
the first position of that atom in the list, plus one. Zero means unmarked or absent.
Repeated marks are allowed. One observation on one common addressing suffices to recover
every marked atom; separately canonicalized single-marker addressings are unnecessary.

These are encoding facts, not a proof that a runtime key constructs a common addressing,
nor a chemical justification of the order among distinct marker codes.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerCode

universe u v
variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

def code (marks : List α) (atom : α) : Nat :=
  if atom ∈ marks then marks.idxOf atom + 1 else 0

def observation (marks : List α) : Option α → Nat
  | none => 0
  | some atom => code marks atom

theorem code_eq_zero_iff (marks : List α) (atom : α) :
    code marks atom = 0 ↔ atom ∉ marks := by
  simp [code]

/-- No nodup premise: duplicate entries still designate the same atom. -/
theorem eq_of_code_eq {marks : List α} {first second : α}
    (member : first ∈ marks) (same : code marks first = code marks second) :
    first = second := by
  by_cases secondMember : second ∈ marks
  · apply (List.idxOf_inj member).mp
    simpa [code, member, secondMember] using same
  · simp [code, member, secondMember] at same

theorem observation_eq_mark_iff (marks : List α) (mark : α)
    (member : mark ∈ marks) (atom : Option α) :
    observation marks atom = code marks mark ↔ atom = some mark := by
  cases atom with
  | none => simp [observation, code, member]
  | some atom =>
      constructor
      · intro same
        exact congrArg some (eq_of_code_eq member same.symm).symm
      · intro same
        cases same
        rfl

private theorem idxOf_map_injective (f : α → β) (injective : Function.Injective f)
    (marks : List α) (atom : α) :
    (marks.map f).idxOf (f atom) = marks.idxOf atom := by
  induction marks with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.idxOf_cons, cond_eq_ite, beq_iff_eq,
        injective.eq_iff, ih]

/-- Relabel marks and the occurrence together; the joint color is unchanged. -/
theorem code_map (f : α → β) (injective : Function.Injective f)
    (marks : List α) (atom : α) :
    code (marks.map f) (f atom) = code marks atom := by
  have member : f atom ∈ marks.map f ↔ atom ∈ marks := by
    simp [List.mem_map, injective.eq_iff]
  simp only [code, member, idxOf_map_injective f injective]

theorem observation_map (f : α → β) (injective : Function.Injective f)
    (marks : List α) (atom : Option α) :
    observation (marks.map f) (atom.map f) = observation marks atom := by
  cases atom with
  | none => rfl
  | some atom => exact code_map f injective marks atom

theorem code_singleton (mark atom : α) :
    code [mark] atom = if atom = mark then 1 else 0 := by
  by_cases same : atom = mark
  · subst atom
    simp [code]
  · simp [code, same]

/-- Exactly the old reference-membership bit, including absent occurrences. -/
theorem observation_singleton (mark : α) (atom : Option α) :
    observation [mark] atom = if atom = some mark then 1 else 0 := by
  cases atom with
  | none => simp [observation]
  | some atom => simp [observation, code_singleton]

/-- A single map preserving the joint observation fixes all retained marks. -/
theorem fixes_marks (marks : List α) (f : α → α)
    (preserved : ∀ mark ∈ marks, code marks (f mark) = code marks mark) :
    ∀ mark ∈ marks, f mark = mark := by
  intro mark member
  exact (eq_of_code_eq member (preserved mark member).symm).symm

assert_kernel_only code_eq_zero_iff
assert_kernel_only eq_of_code_eq
assert_kernel_only observation_eq_mark_iff
assert_kernel_only code_map
assert_kernel_only observation_map
assert_kernel_only code_singleton
assert_kernel_only observation_singleton
assert_kernel_only fixes_marks

end TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerCode
