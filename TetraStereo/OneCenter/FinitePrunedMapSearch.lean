import TetraStereo.OneCenter.FinitePhysicalBranchTransport
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.FinitePrunedMapSearch

section Engine

variable {V : Type*} [DecidableEq V]

/-- One shared function-update DFS. A source assignment is checked by `prefixCheck` before
recursing, so incompatible prefixes are pruned before they are expanded. The complete-map
predicate is supplied by the caller. -/
def searchAux (prefixCheck : (V → V) → List V → Bool)
    (leafCheck : (V → V) → Bool) (targets : List V) :
    List V → List V → (V → V) → Bool
  | [], _seen, f => leafCheck f
  | x :: xs, seen, f =>
      targets.any fun y =>
        prefixCheck (Function.update f x y) (x :: seen) &&
        searchAux prefixCheck leafCheck targets xs (x :: seen) (Function.update f x y)

/-- Logical trace of a successful run of the generic prefix-pruned engine. -/
def SearchTrace (prefixCheck : (V → V) → List V → Bool) (targets : List V) :
    List V → List V → (V → V) → (V → V) → Prop
  | [], _seen, f, result => result = f
  | x :: xs, seen, f, result =>
      ∃ y, y ∈ targets ∧ prefixCheck (Function.update f x y) (x :: seen) = true ∧
        SearchTrace prefixCheck targets xs (x :: seen) (Function.update f x y) result

theorem searchAux_eq_true_iff_trace (prefixCheck : (V → V) → List V → Bool)
    (leafCheck : (V → V) → Bool) (targets sources seen : List V) (f : V → V) :
    searchAux prefixCheck leafCheck targets sources seen f = true ↔
      ∃ result, SearchTrace prefixCheck targets sources seen f result ∧ leafCheck result = true := by
  induction sources generalizing seen f with
  | nil => simp [searchAux, SearchTrace]
  | cons x xs ih =>
      simp only [searchAux, List.any_eq_true, Bool.and_eq_true]
      constructor
      · rintro ⟨y, hy, hp, hr⟩
        obtain ⟨result, ht, hl⟩ :=
          (ih (seen := x :: seen) (f := Function.update f x y)).mp hr
        exact ⟨result, ⟨y, hy, hp, ht⟩, hl⟩
      · rintro ⟨result, ⟨y, hy, hp, ht⟩, hl⟩
        exact ⟨y, hy, hp, (ih (seen := x :: seen)
          (f := Function.update f x y)).mpr ⟨result, ht, hl⟩⟩

theorem searchAux_sound (prefixCheck : (V → V) → List V → Bool)
    (leafCheck : (V → V) → Bool) (targets sources seen : List V) (f : V → V)
    (h : searchAux prefixCheck leafCheck targets sources seen f = true) :
    ∃ result, SearchTrace prefixCheck targets sources seen f result ∧ leafCheck result = true :=
  (searchAux_eq_true_iff_trace prefixCheck leafCheck targets sources seen f).mp h

/-- Guided completeness: if a full target function passes the leaf check and every prefix of its
updates passes the gate, the DFS finds that same function. -/
theorem searchAux_true_of_target (prefixCheck : (V → V) → List V → Bool)
    (leafCheck : (V → V) → Bool) (targets sources seen : List V) (f E : V → V)
    (leafValid : leafCheck E = true) (sourcesNodup : sources.Nodup)
    (sourcesFresh : ∀ v ∈ sources, v ∉ seen)
    (sourcesCovered : ∀ v, v ∈ sources ∨ v ∈ seen)
    (targetsCovered : ∀ v, v ∈ targets)
    (agreement : ∀ v ∈ seen, f v = E v)
    (prefixValid : ∀ (f : V → V) (seen : List V),
      (∀ v ∈ seen, f v = E v) → ∀ x, x ∉ seen →
        prefixCheck (Function.update f x (E x)) (x :: seen) = true) :
    searchAux prefixCheck leafCheck targets sources seen f = true := by
  induction sources generalizing seen f with
  | nil =>
      have allSeen : ∀ v, v ∈ seen := by
        intro v
        rcases sourcesCovered v with h | h
        · simp at h
        · exact h
      have heq : f = E := funext fun v => agreement v (allSeen v)
      simp only [searchAux, heq, leafValid]
  | cons x xs ih =>
      have hxFresh : x ∉ seen := sourcesFresh x (by simp)
      let f' := Function.update f x (E x)
      have agreement' : ∀ v ∈ x :: seen, f' v = E v := by
        intro v hv
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · simp [f', Function.update_self]
        · have hne : x ≠ v := by
            intro h
            subst x
            exact hxFresh hv
          change Function.update f x (E x) v = E v
          rw [Function.update_of_ne hne.symm]
          exact agreement v hv
      have hprefix : prefixCheck f' (x :: seen) = true :=
        prefixValid f seen agreement x hxFresh
      have coverage' : ∀ v, v ∈ xs ∨ v ∈ x :: seen := by
        intro v
        rcases sourcesCovered v with hsrc | hseen
        · simp only [List.mem_cons] at hsrc
          rcases hsrc with rfl | hsrc
          · exact Or.inr (by simp)
          · exact Or.inl hsrc
        · exact Or.inr (by simp [hseen])
      have fresh' : ∀ v ∈ xs, v ∉ x :: seen := by
        intro v hv hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with h | h
        · exact (List.nodup_cons.mp sourcesNodup).1 (h ▸ hv)
        · exact sourcesFresh v (by simp [hv]) h
      have rest := ih (seen := x :: seen) (f := f')
        (List.nodup_cons.mp sourcesNodup).2 fresh' coverage' agreement'
      apply (List.any_eq_true).2
      refine ⟨E x, targetsCovered (E x), ?_⟩
      simpa [f'] using And.intro hprefix rest

end Engine

end TetraStereo.OneCenter.FinitePrunedMapSearch

assert_kernel_only TetraStereo.OneCenter.FinitePrunedMapSearch.searchAux_eq_true_iff_trace
assert_kernel_only TetraStereo.OneCenter.FinitePrunedMapSearch.searchAux_sound
assert_kernel_only TetraStereo.OneCenter.FinitePrunedMapSearch.searchAux_true_of_target
