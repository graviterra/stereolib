import TetraStereo.OneCenter.LocalizedMarkedOperationEvaluator

set_option autoImplicit false

/-! Exact point caching for diagnostic reuse. Only the theorem's computed entries are certified;
arbitrary supplied cache values are not claimed correct. No comparison or reference rule changes. -/

namespace TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantCache

open LocalizedMarkedOperationEvaluator (Operations Node)

def withPointCache (ops : Operations) (state : OccurrenceAuxState) (node : Node) (mark : Nat)
    (ordinary : Option (List Nat × List (Option Ordering)))
    (marked : Option Rule6TrackedRanking) : Operations where
  ordinary := fun s n => if s = state ∧ n = node then ordinary else ops.ordinary s n
  marked := fun s n r => if s = state ∧ n = node ∧ r = mark then marked else ops.marked s n r

/-- Cached values are the actual callback computations; no output agreement is assumed. -/
theorem computed_cache_eq (ops : Operations) (state : OccurrenceAuxState) (node : Node)
    (mark : Nat) :
    withPointCache ops state node mark (ops.ordinary state node) (ops.marked state node mark) =
      ops := by
  cases ops with
  | mk ordinary marked =>
      unfold withPointCache
      congr 1
      · funext s n
        split_ifs with h
        · rcases h with ⟨rfl, rfl⟩
          rfl
        · rfl
      · funext s n r
        split_ifs with h
        · rcases h with ⟨rfl, rfl, rfl⟩
          rfl
        · rfl

end TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantCache

assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantCache.computed_cache_eq
