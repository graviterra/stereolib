import Mathlib.Data.List.Permutation
import Mathlib.Tactic.Linarith

/-!
# Structurally recursive, exact-order list permutations

The recursion in mathlib's `List.permutationsAux` uses a well-founded pair
recursor. This alternative uses structural recursion on a natural-number fuel.
The public wrapper always supplies sufficient fuel, and the equality theorem
preserves the entire output list, including order and multiplicity.

This is a proposed computation bridge, not an external chemistry approval.
-/

namespace TetraStereo.OneCenter.KernelPermutationEnumeration

/-- A natural-valued ranking for both calls in `List.permutationsAux`. -/
def kernelPermutationMeasure {α : Type*} (ts is : List α) : Nat :=
  (ts.length + is.length) ^ 2 + ts.length

theorem kernelPermutationMeasure_pour {α : Type*} (t : α) (ts is : List α) :
    kernelPermutationMeasure ts (t :: is) <
      kernelPermutationMeasure (t :: ts) is := by
  simp only [kernelPermutationMeasure, List.length_cons]
  have h : ts.length + (is.length + 1) = ts.length + 1 + is.length := by omega
  rw [h]
  omega

theorem kernelPermutationMeasure_restart {α : Type*} (t : α) (ts is : List α) :
    kernelPermutationMeasure is [] <
      kernelPermutationMeasure (t :: ts) is := by
  simp only [kernelPermutationMeasure, List.length_cons, List.length_nil, Nat.add_zero]
  nlinarith [Nat.zero_le (ts.length * is.length), Nat.zero_le (ts.length ^ 2)]

/-- The original enumeration algorithm with structural recursion on fuel.
The fallback at zero is unreachable from `kernelPermutations`, as proved below. -/
def kernelPermutationsAux {α : Type*} : Nat → List α → List α → List (List α)
  | 0, _, _ => []
  | _ + 1, [], _ => []
  | fuel + 1, t :: ts, is =>
      List.foldr (fun y r => (List.permutationsAux2 t ts r y id).2)
        (kernelPermutationsAux fuel ts (t :: is))
        (is :: kernelPermutationsAux fuel is [])

/-- Sufficient structural fuel reproduces mathlib's enumeration exactly. -/
theorem kernelPermutationsAux_eq {α : Type*} (fuel : Nat) (ts is : List α)
    (h : kernelPermutationMeasure ts is < fuel) :
    kernelPermutationsAux fuel ts is = List.permutationsAux ts is := by
  induction fuel generalizing ts is with
  | zero => omega
  | succ fuel ih =>
      cases ts with
      | nil => simp only [kernelPermutationsAux, List.permutationsAux_nil]
      | cons t ts =>
          have hpour : kernelPermutationMeasure ts (t :: is) < fuel := by
            have := kernelPermutationMeasure_pour t ts is
            omega
          have hrestart : kernelPermutationMeasure is [] < fuel := by
            have := kernelPermutationMeasure_restart t ts is
            omega
          rw [kernelPermutationsAux, List.permutationsAux_cons, List.permutations,
            ih ts (t :: is) hpour, ih is [] hrestart]

/-- Exact-order permutations, computed with a proved sufficient structural budget. -/
def kernelPermutations {α : Type*} (l : List α) : List (List α) :=
  l :: kernelPermutationsAux (kernelPermutationMeasure l [] + 1) l []

/-- The public bridge is unconditional for every element type and every list. -/
theorem kernelPermutations_eq_permutations {α : Type*} (l : List α) :
    kernelPermutations l = List.permutations l := by
  unfold kernelPermutations List.permutations
  rw [kernelPermutationsAux_eq _ _ _ (Nat.lt_succ_self _)]

theorem mem_kernelPermutations {α : Type*} {s t : List α} :
    s ∈ kernelPermutations t ↔ s.Perm t := by
  rw [kernelPermutations_eq_permutations, List.mem_permutations]

/-- Closed structural computation of the four-ligand search-space cardinality. -/
theorem kernelPermutations_range_four_length :
    (kernelPermutations (List.range 4)).length = 24 := by
  decide +kernel

/-- Transfer the closed computation to the original public enumeration. -/
theorem permutations_range_four_length_via_kernel :
    (List.permutations (List.range 4)).length = 24 := by
  rw [← kernelPermutations_eq_permutations]
  exact kernelPermutations_range_four_length

end TetraStereo.OneCenter.KernelPermutationEnumeration
