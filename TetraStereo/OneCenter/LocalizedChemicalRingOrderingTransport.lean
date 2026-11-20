import TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking
import TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Transport of finite priority orders

The hypotheses below concern keys and input populations, not a sorted result or callback
covariance. Stable ordering inside a tie is deliberately not identified. Sorted key columns,
and therefore adjacent comparison flags, agree even when entries tie. The entry lists agree
after transport when the keys separate the input entries.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingOrderingTransport

open LocalizedMarkedRetainedOrdinaryRanking
open LocalizedGenericMarkedRecalculation (strict consistent tiedPositions eligibleOf atomsAt)

section Order

variable {α β K : Type} [LinearOrder K]

omit [LinearOrder K] in
theorem adjacentBy_map (cmp : K → K → Ordering) (key : α → K) :
    ∀ xs : List α,
      adjacentBy (fun a b => some (cmp a b)) (xs.map key) =
        adjacentBy (fun a b => some (cmp (key a) (key b))) xs
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
      simp only [List.map_cons, adjacentBy]
      exact congrArg (List.cons (some (cmp (key a) (key b))))
        (adjacentBy_map cmp key (b :: rest))

/-- Sorting commutes with mapping to the key column, including ties. -/
theorem sorted_keys (key : α → K) (xs : List α) :
    (keyOrder key xs).map key = keyOrder id (xs.map key) := by
  exact List.map_insertionSort (fun a b => key b ≤ key a) (fun a b : K => b ≤ a)
    key xs (fun _ _ _ _ => Iff.rfl)

/-- Two populations with the same multiset of keys have identical sorted key columns. -/
theorem sorted_keys_eq (left : α → K) (right : β → K) (xs : List α) (ys : List β)
    (keys : (ys.map right).Perm (xs.map left)) :
    (keyOrder right ys).map right = (keyOrder left xs).map left := by
  rw [sorted_keys, sorted_keys]
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => le_antisymm hba hab)
    (keyOrder_pairwise id (ys.map right)) (keyOrder_pairwise id (xs.map left))
    ((keyOrder_perm id (ys.map right)).trans
      (keys.trans (keyOrder_perm id (xs.map left)).symm))

/-- Adjacent decisions are transported without preserving the order of tied entries. -/
theorem adjacent_sorted_eq (cmp : K → K → Ordering)
    (left : α → K) (right : β → K) (xs : List α) (ys : List β)
    (keys : (ys.map right).Perm (xs.map left)) :
    adjacentBy (fun a b => some (cmp (right a) (right b))) (keyOrder right ys) =
      adjacentBy (fun a b => some (cmp (left a) (left b))) (keyOrder left xs) := by
  rw [← adjacentBy_map cmp right, ← adjacentBy_map cmp left,
    sorted_keys_eq left right xs ys keys]

theorem adjacent_flags_eq (cmp : K → K → Ordering)
    (left : α → K) (right : β → K) (xs : List α) (ys : List β)
    (keys : (ys.map right).Perm (xs.map left)) :
    consistent (adjacentBy (fun a b => some (cmp (right a) (right b))) (keyOrder right ys)) =
        consistent (adjacentBy (fun a b => some (cmp (left a) (left b))) (keyOrder left xs)) ∧
      strict (adjacentBy (fun a b => some (cmp (right a) (right b))) (keyOrder right ys)) =
        strict (adjacentBy (fun a b => some (cmp (left a) (left b))) (keyOrder left xs)) := by
  rw [adjacent_sorted_eq cmp left right xs ys keys]
  exact ⟨rfl, rfl⟩

omit [LinearOrder K] in
/-- Transported keys suffice to transport the complete key population. -/
theorem mapped_keys_perm (f : α → β) (left : α → K) (right : β → K)
    (xs : List α) (ys : List β) (population : ys.Perm (xs.map f))
    (preserved : ∀ a ∈ xs, right (f a) = left a) :
    (ys.map right).Perm (xs.map left) := by
  have eq : (xs.map f).map right = xs.map left := by
    rw [List.map_map]
    exact List.map_congr_left preserved
  exact (population.map right).trans (List.Perm.of_eq eq)

/-- Stable sort transport when the input keys distinguish entries. The distinctness
condition is derived from a strict adjacent column by `strict_keys_injective`. -/
theorem keyOrder_transport_of_injective (f : α → β) (left : α → K) (right : β → K)
    (xs : List α) (ys : List β) (population : ys.Perm (xs.map f))
    (preserved : ∀ a ∈ xs, right (f a) = left a)
    (separate : ∀ a ∈ xs, ∀ b ∈ xs, left a = left b → a = b) :
    keyOrder right ys = (keyOrder left xs).map f := by
  have memImage : ∀ b ∈ ys, ∃ a ∈ xs, f a = b := by
    intro b hb
    exact List.mem_map.mp (population.mem_iff.mp hb)
  have rightSeparate : ∀ a ∈ ys, ∀ b ∈ ys, right a = right b → a = b := by
    intro a ha b hb eq
    obtain ⟨a', ha', rfl⟩ := memImage a ha
    obtain ⟨b', hb', rfl⟩ := memImage b hb
    rw [preserved a' ha', preserved b' hb'] at eq
    exact congrArg f (separate a' ha' b' hb' eq)
  have sortedPerm : (keyOrder right ys).Perm ((keyOrder left xs).map f) :=
    (keyOrder_perm right ys).trans
      (population.trans ((keyOrder_perm left xs).map f).symm)
  apply List.Perm.eq_of_pairwise
    (fun a b ha hb hab hba => rightSeparate a
      ((keyOrder_perm right ys).mem_iff.mp ha) b
      ((keyOrder_perm right ys).mem_iff.mp (sortedPerm.mem_iff.mpr hb))
      (le_antisymm hba hab))
    (keyOrder_pairwise right ys)
  · rw [List.pairwise_map]
    exact (keyOrder_pairwise left xs).imp_of_mem fun {a b} ha hb h => by
      rw [preserved a ((keyOrder_perm left xs).mem_iff.mp ha),
        preserved b ((keyOrder_perm left xs).mem_iff.mp hb)]
      exact h
  · exact sortedPerm

theorem strict_keys_injective (cmp : K → K → Ordering)
    (lt_iff : ∀ a b, cmp a b = Ordering.lt ↔ a < b)
    (eq_iff : ∀ a b, cmp a b = Ordering.eq ↔ a = b)
    (key : α → K) (xs : List α) (nodup : xs.Nodup)
    (isStrict : strict (adjacentBy (fun a b => some (cmp (key a) (key b)))
      (keyOrder key xs)) = true) :
    ∀ a ∈ xs, ∀ b ∈ xs, key a = key b → a = b := by
  apply (keyOrder_chain_iff_injective key xs nodup).mp
  apply (adjacentBy_key_all_gt_iff cmp lt_iff eq_iff key _).mp
  simpa [strict, List.all_eq_true] using isStrict

theorem keyOrder_transport_of_strict (cmp : K → K → Ordering)
    (lt_iff : ∀ a b, cmp a b = Ordering.lt ↔ a < b)
    (eq_iff : ∀ a b, cmp a b = Ordering.eq ↔ a = b)
    (f : α → β) (left : α → K) (right : β → K)
    (xs : List α) (ys : List β) (nodup : xs.Nodup)
    (population : ys.Perm (xs.map f)) (preserved : ∀ a ∈ xs, right (f a) = left a)
    (isStrict : strict (adjacentBy (fun a b => some (cmp (left a) (left b)))
      (keyOrder left xs)) = true) :
    keyOrder right ys = (keyOrder left xs).map f :=
  keyOrder_transport_of_injective f left right xs ys population preserved
    (strict_keys_injective cmp lt_iff eq_iff left xs nodup isStrict)

end Order

/-- The same tied-run selector as `tiedPositions`, before choosing a representation of slots. -/
def tiedEntries {α : Type} : Bool → List α → List (Option Ordering) → List α
  | _, [], _ => []
  | prev, [p], _ => if prev then [p] else []
  | prev, p :: q :: rest, [] =>
      (if prev then [p] else []) ++ tiedEntries false (q :: rest) []
  | prev, p :: q :: rest, d :: ds =>
      let tie := d == some Ordering.eq
      (if prev || tie then [p] else []) ++ tiedEntries tie (q :: rest) ds

theorem tiedEntries_map {α β : Type} (f : α → β) :
    ∀ prev (xs : List α) ds,
      tiedEntries prev (xs.map f) ds = (tiedEntries prev xs ds).map f
  | _, [], _ => rfl
  | prev, [_], _ => by cases prev <;> rfl
  | prev, a :: b :: rest, [] => by
      simp only [List.map_cons, tiedEntries, List.map_append]
      exact congrArg₂ List.append (by cases prev <;> rfl)
        (tiedEntries_map f false (b :: rest) [])
  | prev, a :: b :: rest, d :: ds => by
      simp only [List.map_cons, tiedEntries, List.map_append]
      exact congrArg₂ List.append (by cases prev || d == some Ordering.eq <;> rfl)
        (tiedEntries_map f (d == some Ordering.eq) (b :: rest) ds)

theorem tiedEntries_nat : ∀ prev (xs : List Nat) ds,
    tiedEntries prev xs ds = tiedPositions prev xs ds
  | _, [], _ => rfl
  | _, [_], _ => rfl
  | prev, a :: b :: rest, [] => by
      simp only [tiedEntries, tiedPositions, tiedEntries_nat false (b :: rest) []]
  | prev, a :: b :: rest, d :: ds => by
      simp only [tiedEntries, tiedPositions, tiedEntries_nat (d == some Ordering.eq) (b :: rest) ds]

theorem tiedEntries_sublist {α : Type} : ∀ prev (xs : List α) ds,
    List.Sublist (tiedEntries prev xs ds) xs
  | _, [], _ => List.Sublist.refl _
  | prev, [a], _ => by cases prev <;> simp [tiedEntries]
  | prev, a :: b :: rest, [] => by
      have ih := tiedEntries_sublist false (b :: rest) []
      cases prev <;> simp only [tiedEntries, Bool.false_eq_true, ↓reduceIte,
        List.nil_append, List.singleton_append]
      · exact ih.cons _
      · exact ih.cons₂ _
  | prev, a :: b :: rest, d :: ds => by
      have ih := tiedEntries_sublist (d == some Ordering.eq) (b :: rest) ds
      simp only [tiedEntries]
      cases prev || d == some Ordering.eq <;> simp only [Bool.false_eq_true, ↓reduceIte,
        List.nil_append, List.singleton_append]
      · exact ih.cons _
      · exact ih.cons₂ _

section Ties

variable {α K : Type} [LinearOrder K]
  (cmp : K → K → Ordering) (eq_iff : ∀ a b, cmp a b = Ordering.eq ↔ a = b)
  (key : α → K)

include eq_iff

/-- A selected entry is in a nontrivial equal-key class, or in the run continued by `prev`.
This characterizes the actual adjacency selector rather than replacing it by another algorithm. -/
theorem tiedEntries_mem_cons : ∀ (rest : List α) (first a : α) (prev : Bool),
    (first :: rest).Nodup → (first :: rest).Pairwise (fun x y => key y ≤ key x) →
    (a ∈ tiedEntries prev (first :: rest)
      (adjacentBy (fun x y => some (cmp (key x) (key y))) (first :: rest)) ↔
      a ∈ first :: rest ∧ ((prev = true ∧ key a = key first) ∨
        ∃ b ∈ first :: rest, b ≠ a ∧ key b = key a)) := by
  classical
  intro rest
  induction rest with
  | nil =>
      intro first a prev _ _
      cases prev <;> simp only [tiedEntries, Bool.false_eq_true, ↓reduceIte,
        List.not_mem_nil, List.mem_singleton, false_and, false_or, true_and]
      all_goals aesop
  | cons second rest ih =>
      intro first a prev nodup sorted
      have nd := List.nodup_cons.mp nodup
      have so := List.pairwise_cons.mp sorted
      have tailMem := ih second a ((some (cmp (key first) (key second))) == some Ordering.eq)
        nd.2 so.2
      have tie : ((some (cmp (key first) (key second))) == some Ordering.eq) =
          decide (key first = key second) := by
        apply Bool.eq_iff_iff.mpr
        simpa only [beq_iff_eq, Option.some.injEq, decide_eq_true_eq] using
          eq_iff (key first) (key second)
      have gap : key first ≠ key second → ∀ x ∈ second :: rest, key x ≠ key first := by
        intro different x member equal
        have upper : key x ≤ key second := by
          rcases List.mem_cons.mp member with rfl | member
          · exact le_rfl
          · exact (List.pairwise_cons.mp so.2).1 x member
        have lower := so.1 second List.mem_cons_self
        rw [equal] at upper
        exact different (le_antisymm upper lower)
      have distinct : first ≠ second := fun h => nd.1 (h.symm ▸ List.mem_cons_self)
      simp only [adjacentBy, tiedEntries, List.mem_append]
      rw [tailMem, tie]
      by_cases equal : key first = key second
      · have ht : decide (key first = key second) = true := by simp [equal]
        simp only [ht, Bool.or_true, ↓reduceIte, List.mem_singleton,
          true_and]
        constructor
        · rintro (rfl | ⟨member, continued | ⟨b, hb, different, same⟩⟩)
          · exact ⟨List.mem_cons_self, Or.inr ⟨second, by simp, distinct.symm, equal.symm⟩⟩
          · exact ⟨List.mem_cons_of_mem _ member,
              Or.inr ⟨first, List.mem_cons_self,
                fun h => nd.1 (h.symm ▸ member), equal.trans continued.symm⟩⟩
          · exact ⟨List.mem_cons_of_mem _ member,
              Or.inr ⟨b, List.mem_cons_of_mem _ hb, different, same⟩⟩
        · rintro ⟨member, reason⟩
          rcases List.mem_cons.mp member with rfl | member
          · exact Or.inl rfl
          · refine Or.inr ⟨member, ?_⟩
            rcases reason with ⟨_, same⟩ | ⟨b, hb, different, same⟩
            · exact Or.inl (same.trans equal)
            · rcases List.mem_cons.mp hb with rfl | hb
              · exact Or.inl (same.symm.trans equal)
              · exact Or.inr ⟨b, hb, different, same⟩
      · have gap := gap equal
        simp only [equal, decide_false, Bool.or_false, Bool.false_eq_true, false_and, false_or]
        have noOther : ¬ ∃ b ∈ first :: second :: rest, b ≠ first ∧ key b = key first := by
          rintro ⟨b, hb, different, same⟩
          rcases List.mem_cons.mp hb with hb | hb
          · exact different hb
          · exact gap b hb same
        by_cases ha : a = first
        · subst a
          rw [iff_false_intro noOther, iff_false_intro nd.1]
          cases prev <;> simp
        · by_cases member : a ∈ second :: rest
          · have differentKey := gap a member
            have dup : (∃ b ∈ first :: second :: rest, b ≠ a ∧ key b = key a) ↔
                (∃ b ∈ second :: rest, b ≠ a ∧ key b = key a) := by
              constructor
              · rintro ⟨b, hb, different, same⟩
                rcases List.mem_cons.mp hb with hb | hb
                · subst b
                  exact False.elim (differentKey same.symm)
                · exact ⟨b, hb, different, same⟩
              · rintro ⟨b, hb, different, same⟩
                exact ⟨b, List.mem_cons_of_mem _ hb, different, same⟩
            rw [dup]
            cases prev <;> simp [ha, member, differentKey]
          · cases prev <;> simp [ha, member]

/-- Exactly those entries whose key is shared by another entry are eligible. -/
theorem tiedEntries_mem (xs : List α) (nodup : xs.Nodup)
    (sorted : xs.Pairwise (fun x y => key y ≤ key x)) (a : α) :
    a ∈ tiedEntries false xs (adjacentBy (fun x y => some (cmp (key x) (key y))) xs) ↔
      a ∈ xs ∧ ∃ b ∈ xs, b ≠ a ∧ key b = key a := by
  cases xs with
  | nil => simp [tiedEntries]
  | cons first rest =>
      simpa using tiedEntries_mem_cons cmp eq_iff key rest first a false nodup sorted

/-- The actual sorted selector detects a duplicate key in the original population. -/
theorem tied_sorted_mem (xs : List α) (nodup : xs.Nodup) (a : α) :
    a ∈ tiedEntries false (keyOrder key xs)
      (adjacentBy (fun x y => some (cmp (key x) (key y))) (keyOrder key xs)) ↔
      a ∈ xs ∧ ∃ b ∈ xs, b ≠ a ∧ key b = key a := by
  rw [tiedEntries_mem cmp eq_iff key _ ((keyOrder_perm key xs).nodup_iff.mpr nodup)
    (keyOrder_pairwise key xs)]
  simp only [(keyOrder_perm key xs).mem_iff]

variable {β : Type}

/-- All tied reference entries transport, regardless of how a stable sort orders ties. -/
theorem tied_sorted_transport (f : α → β) (injective : Function.Injective f)
    (left : α → K) (right : β → K) (xs : List α) (ys : List β)
    (nodup : xs.Nodup) (population : ys.Perm (xs.map f))
    (preserved : ∀ a ∈ xs, right (f a) = left a) :
    (tiedEntries false (keyOrder right ys)
      (adjacentBy (fun a b => some (cmp (right a) (right b))) (keyOrder right ys))).Perm
      ((tiedEntries false (keyOrder left xs)
        (adjacentBy (fun a b => some (cmp (left a) (left b))) (keyOrder left xs))).map f) := by
  have ynodup : ys.Nodup := population.nodup_iff.mpr (nodup.map injective)
  have leftNodup := ((keyOrder_perm left xs).nodup_iff.mpr nodup).sublist
    (tiedEntries_sublist false (keyOrder left xs)
      (adjacentBy (fun a b => some (cmp (left a) (left b))) (keyOrder left xs)))
  have rightNodup := ((keyOrder_perm right ys).nodup_iff.mpr ynodup).sublist
    (tiedEntries_sublist false (keyOrder right ys)
      (adjacentBy (fun a b => some (cmp (right a) (right b))) (keyOrder right ys)))
  apply (List.perm_ext_iff_of_nodup rightNodup (leftNodup.map injective)).mpr
  intro y
  rw [tied_sorted_mem cmp eq_iff right ys ynodup, List.mem_map]
  constructor
  · rintro ⟨member, b, other, different, same⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (population.mem_iff.mp member)
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (population.mem_iff.mp other)
    refine ⟨a, (tied_sorted_mem cmp eq_iff left xs nodup a).mpr ?_, rfl⟩
    refine ⟨ha, c, hc, fun eq => different (congrArg f eq), ?_⟩
    simpa only [preserved a ha, preserved c hc] using same
  · rintro ⟨a, selected, rfl⟩
    obtain ⟨ha, c, hc, different, same⟩ :=
      (tied_sorted_mem cmp eq_iff left xs nodup a).mp selected
    refine ⟨population.mem_iff.mpr (List.mem_map_of_mem ha), f c,
      population.mem_iff.mpr (List.mem_map_of_mem hc), fun eq => different (injective eq), ?_⟩
    rw [preserved a ha, preserved c hc]
    exact same

end Ties

/-- Slot representation is independent of tied-run selection. This is the bridge to the
actual `eligibleOf` atom readback, including its handling of out-of-range positions. -/
theorem eligibleOf_tiedEntries {α : Type} (atoms : List Nat) (index : α → Nat)
    (order : List α) (adjacent : List (Option Ordering)) :
    eligibleOf atoms (order.map index) adjacent =
      (tiedEntries false order adjacent).filterMap (fun a => atoms[index a]?) := by
  unfold eligibleOf atomsAt
  rw [← tiedEntries_nat, tiedEntries_map, List.filterMap_map]
  rfl

end TetraStereo.OneCenter.LocalizedChemicalRingOrderingTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrderingTransport.sorted_keys_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrderingTransport.adjacent_flags_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrderingTransport.keyOrder_transport_of_strict
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrderingTransport.tiedEntries_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrderingTransport.tiedEntries_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrderingTransport.tied_sorted_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrderingTransport.eligibleOf_tiedEntries
