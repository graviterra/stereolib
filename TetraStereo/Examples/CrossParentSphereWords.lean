import TetraStereo.Examples.AntipodalCyclohexaneWords

/-! Recover a native full-path word by counting likes within each occupied
sphere when the molecular path priorities place every like before every unlike.
The graph expansion keeps occurrences from all parents and their multiplicities. -/
set_option autoImplicit false
namespace TetraStereo.Examples.CrossParentSphereWords
open Engine OneCenter
open RingFullPathPairs (FullTrace)
open private block_paths from TetraStereo.Examples.DecalinLigandOrder
open private flatMap_perm from TetraStereo.Engine.RingFullPathPairs

def sortedBits (bs : List Bool) := List.replicate (bs.count true) true ++ List.replicate (bs.count false) false

private theorem sorted_perm (bs : List Bool) : (sortedBits bs).Perm bs := by
  apply List.perm_iff_count.mpr
  intro b
  cases b <;> simp [sortedBits,List.count_replicate]

private theorem sorted_desc (bs : List Bool) : (sortedBits bs).Pairwise (· ≥ ·) := by
  simp [sortedBits,List.pairwise_append]

def word? {α : Type} (kids : α → List α) (emit : α → Option Bool) : Nat → List α → Option (List Bool)
  | 0, row => if row.isEmpty then some [] else none
  | n+1, row => (word? kids emit n (row.flatMap kids)).map (sortedBits (row.filterMap emit) ++ ·)

private theorem empty {α : Type} (kids : α → List α) (emit : α → Option Bool) (n : Nat) :
    word? kids emit n [] = some [] := by induction n <;> simp_all [word?,sortedBits]

/-- A certificate on the projected graph suffices for every legal ordering of the full trace.
Dominance is required only for a false/true pair of emitting visits in the same sphere. -/
theorem trace_word {α β κ : Type} [LinearOrder κ] {E : α → List α → Prop}
    {key : α → κ} {proj : α → β} {kids : β → List β} {D : Nat → α → Prop}
    (step : ∀ depth x, D depth x → ∀ ys, E x ys → (ys.map proj).Perm (kids (proj x)) ∧ ∀ y ∈ ys, D (depth+1) y)
    (emit : β → Option Bool) (strong : ∀ depth x y, D depth x → D depth y → emit (proj x) = some false →
      emit (proj y) = some true → key x < key y)
    {xs out : List α} (trace : FullTrace key E xs out) (depth : Nat) (inside : ∀ x ∈ xs, D depth x)
    (desc : (xs.map key).Pairwise (· ≥ ·)) :
    ∀ n row word, (xs.map proj).Perm row → word? kids emit n row = some word →
      out.filterMap (fun x => emit (proj x)) = word ∧ ∀ x ∈ out, ∃ n, D n x := by
  induction trace generalizing depth with
  | stop =>
    intro n row word perm ok
    obtain rfl := perm.symm.eq_nil
    rw [empty] at ok
    exact ⟨Option.some.inj ok,by simp⟩
  | @sphere b row blocks next later expanded sorted _ ih =>
    intro n actual word roots ok
    cases n with
    | zero =>
      cases actual with
      | nil => have := roots.eq_nil; contradiction
      | cons => simp [word?] at ok
    | succ n =>
      obtain ⟨paths,sub⟩ := block_paths expanded inside (step depth)
      have nextPaths := ((sorted.perm.map proj).trans paths).trans (flatMap_perm kids roots)
      obtain ⟨rest,hr,hend⟩ := Option.map_eq_some_iff.mp ok
      obtain ⟨suffix,valid⟩ := ih (depth+1) (fun x hx => sub x (sorted.perm.mem_iff.mp hx)) sorted.descending n _ _ nextPaths hr
      have order : ((b::row).filterMap (fun x => emit (proj x))).Pairwise (· ≥ ·) := by
        apply List.pairwise_filterMap.mpr
        apply (List.pairwise_map.mp desc).imp_of_mem
        intro a c ha hc ge u hu v hv
        cases u <;> cases v <;> first | decide | exact (not_lt_of_ge ge (strong depth a c (inside a ha) (inside c hc) hu hv)).elim
      have perm := roots.filterMap emit
      rw [List.filterMap_map] at perm
      have head := List.Perm.eq_of_pairwise (fun _ _ _ _ ab ba => le_antisymm ba ab)
        order (sorted_desc (actual.filterMap emit)) (perm.trans (sorted_perm _).symm)
      refine ⟨?_,fun x hx => (List.mem_append.mp hx).elim (fun h => ⟨depth,inside x h⟩) (valid x)⟩
      rw [List.filterMap_append,head,suffix,hend]

end TetraStereo.Examples.CrossParentSphereWords
assert_kernel_only TetraStereo.Examples.CrossParentSphereWords.trace_word
