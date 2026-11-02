/-
Copyright (c) 2026 TetraStereo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


import Mathlib.Data.List.Sort

set_option autoImplicit false

/-!
# Finite ranked orders

This module provides the generic, chemistry-free combinatorial core of an ordered dependency
argument: a computable ordering of a finite carrier list by a rank function, together with the
proofs that make the order usable in certificates.

`rankedOrder rank carrier` is `List.mergeSort` of `carrier` with the comparison
`fun a b => decide (rank a ≤ rank b)`.  The rank is an arbitrary `β` with a `LinearOrder`
instance, so all results below are generic; no chemical identifiers or structures occur.

The main results are:

* `rankedOrder_perm`, `length_rankedOrder`, `mem_rankedOrder`, `nodup_rankedOrder`:
  the ranked order is a permutation of the carrier and preserves lengths, membership and
  `Nodup`.
* `pairwise_rankedOrder`: the ranked order is sorted, i.e. it is `Pairwise` for
  `fun a b => rank a ≤ rank b`.
* `idxOf_lt_idxOf_of_rank_lt`: if `a` and `b` are carrier members with `rank a < rank b`, then
  `a` occurs strictly before `b` in the ranked order (index comparison, under `DecidableEq`).
  It is an instance of the reusable list lemma `idxOf_lt_idxOf_of_pairwise`, which needs only
  `[BEq α] [LawfulBEq α]` and a reflexive relation `r`: in an `r`-sorted list, an element that
  may not follow another one occurs strictly earlier.
* `mem_prefix_of_rank_lt`: the "earlier dependency" theorem.  If the ranked order decomposes as
  `pre ++ b :: suffix`, then every carrier member `a` with `rank a < rank b` lies in
  `pre`.  Hence such an `a` is a *strictly earlier* entry of the certificate list, not merely
  a carrier member; `mem_prefix_of_dependency` phrases the same for an abstract dependency
  relation whose edges strictly increase the rank.

Everything is proved from `List.mergeSort_perm` and `List.pairwise_mergeSort` (Lean core, exposed
by `Mathlib.Data.List.Sort`).  Every proof is fully elaborated; nothing is assumed.
-/

namespace TetraStereo.Certificate.FiniteRankedOrder

universe u v

variable {α : Type u} {β : Type v}

/-! ### The computable ranked order -/

/-- The ranked order of a finite carrier: merge-sort `carrier` by the rank `rank`, with ties
broken by merge-sort stability (equal ranks keep their relative carrier order). -/
def rankedOrder [LinearOrder β] (rank : α → β) (carrier : List α) : List α :=
  carrier.mergeSort (fun a b => decide (rank a ≤ rank b))

variable [LinearOrder β]

/-- The ranked order is a permutation of the carrier. -/
theorem rankedOrder_perm (rank : α → β) (carrier : List α) :
    List.Perm (rankedOrder rank carrier) carrier := by
  simpa only [rankedOrder] using
    List.mergeSort_perm carrier (fun a b => decide (rank a ≤ rank b))

/-- The ranked order has the same length as the carrier. -/
theorem length_rankedOrder (rank : α → β) (carrier : List α) :
    (rankedOrder rank carrier).length = carrier.length := by
  simpa only [rankedOrder] using
    List.length_mergeSort (le := fun a b => decide (rank a ≤ rank b)) carrier

/-- Membership is unchanged by ranking: the ranked order lists exactly the carrier members. -/
theorem mem_rankedOrder (rank : α → β) (carrier : List α) {a : α} :
    a ∈ rankedOrder rank carrier ↔ a ∈ carrier := by
  simpa only [rankedOrder] using
    List.mem_mergeSort (le := fun a b => decide (rank a ≤ rank b)) (a := a) (l := carrier)

/-- Ranking preserves `Nodup`. -/
theorem nodup_rankedOrder (rank : α → β) (carrier : List α) (h : carrier.Nodup) :
    (rankedOrder rank carrier).Nodup :=
  (rankedOrder_perm rank carrier).symm.nodup h

/-- The ranked order is sorted, in the boolean comparison form used to build it. -/
theorem pairwise_rankedOrder_decide (rank : α → β) (carrier : List α) :
    (rankedOrder rank carrier).Pairwise (fun a b => decide (rank a ≤ rank b) = true) := by
  have h := List.pairwise_mergeSort (le := fun a b => decide (rank a ≤ rank b))
    (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at hab hbc ⊢
      exact le_trans hab hbc)
    (fun a b => by
      simp only [Bool.or_eq_true_iff, decide_eq_true_eq]
      exact le_total (rank a) (rank b))
    carrier
  simpa only [rankedOrder] using h

/-- The ranked order is sorted by rank: every entry is ranked below every later entry. -/
theorem pairwise_rankedOrder (rank : α → β) (carrier : List α) :
    (rankedOrder rank carrier).Pairwise (fun a b => rank a ≤ rank b) :=
  List.Pairwise.imp (fun {_ _} h => of_decide_eq_true h) (pairwise_rankedOrder_decide rank carrier)

/-! ### Earlier occurrences of dependencies -/

/-- Reusable combinatorial core of the "earlier dependency" argument.

In a list `l` that is sorted for a reflexive relation `r`, if `a` and `b` are entries of `l` and
`b` may not follow `a` (`¬ r b a`), then `a` occurs strictly before `b`: its `idxOf` index is
smaller.  The hypothesis `hr : ∀ x, r x x` is what rules out the case `a = b`. -/
theorem idxOf_lt_idxOf_of_pairwise [BEq α] [LawfulBEq α] {r : α → α → Prop} (hr : ∀ x, r x x) :
    ∀ {l : List α}, l.Pairwise r → ∀ {a b : α}, a ∈ l → b ∈ l → ¬ r b a → l.idxOf a < l.idxOf b := by
  intro l
  induction l with
  | nil =>
    intro _ a b ha _ _
    exact absurd ha (by simp)
  | cons x t ih =>
    intro hp a b ha hb hba
    by_cases hax : a = x
    · -- `a` is the head, so its index is `0`; `b` cannot be the head as well.
      rw [hax] at hba
      rw [hax]
      rw [List.idxOf_cons_self]
      have hbx : b ≠ x := by
        intro h
        rw [h] at hba
        exact hba (hr x)
      rw [List.idxOf_cons_ne t (Ne.symm hbx)]
      exact Nat.succ_pos _
    · have ha_t : a ∈ t := by
        rcases List.mem_cons.mp ha with h | h
        · exact absurd h hax
        · exact h
      rw [List.idxOf_cons_ne t (Ne.symm hax)]
      by_cases hbx : b = x
      · -- `b` is the head while `a` is in the tail, which sortedness forbids.
        rw [hbx] at hba
        exact absurd (List.rel_of_pairwise_cons hp ha_t) hba
      · have hb_t : b ∈ t := by
          rcases List.mem_cons.mp hb with h | h
          · exact absurd h hbx
          · exact h
        rw [List.idxOf_cons_ne t (Ne.symm hbx)]
        exact Nat.succ_lt_succ (ih (List.Pairwise.of_cons hp) ha_t hb_t hba)

/-- Main reusable form: in the ranked order of `carrier`, a carrier member of strictly smaller
rank occurs strictly earlier.  (`List.idxOf` is Mathlib's `BEq`-based position function; with
`[DecidableEq α]` the `BEq` and `LawfulBEq` instances are those induced by `=`, so the statement
reads "the position of `a` is below the position of `b`".) -/
theorem idxOf_lt_idxOf_of_rank_lt [DecidableEq α] (rank : α → β) {carrier : List α} {a b : α}
    (ha : a ∈ carrier) (hb : b ∈ carrier) (hab : rank a < rank b) :
    (rankedOrder rank carrier).idxOf a < (rankedOrder rank carrier).idxOf b :=
  idxOf_lt_idxOf_of_pairwise (r := fun x y => rank x ≤ rank y) (fun x => le_refl (rank x))
    (pairwise_rankedOrder rank carrier)
    ((mem_rankedOrder rank carrier).mpr ha) ((mem_rankedOrder rank carrier).mpr hb)
    (not_le_of_gt hab)

/-- The same statement with the hypotheses `List.idxOf` actually needs, for reuse with an
explicit `BEq` instance other than the one induced by `DecidableEq`. -/
theorem idxOf_lt_idxOf_of_rank_lt' [BEq α] [LawfulBEq α] (rank : α → β) {carrier : List α}
    {a b : α} (ha : a ∈ carrier) (hb : b ∈ carrier) (hab : rank a < rank b) :
    (rankedOrder rank carrier).idxOf a < (rankedOrder rank carrier).idxOf b :=
  idxOf_lt_idxOf_of_pairwise (r := fun x y => rank x ≤ rank y) (fun x => le_refl (rank x))
    (pairwise_rankedOrder rank carrier)
    ((mem_rankedOrder rank carrier).mpr ha) ((mem_rankedOrder rank carrier).mpr hb)
    (not_le_of_gt hab)

/-- Splitting a sorted list at an entry: everything before `b` is related to `b`, and `b` is
related to everything after it. -/
theorem pairwise_append_cons {r : α → α → Prop} {l p s : List α} {b : α} (hp : l.Pairwise r)
    (hl : l = p ++ b :: s) : (∀ x ∈ p, r x b) ∧ (∀ x ∈ s, r b x) := by
  rw [hl] at hp
  rw [List.pairwise_append] at hp
  exact ⟨fun x hx => hp.2.2 x hx b List.mem_cons_self,
    fun x hx => List.rel_of_pairwise_cons hp.2.1 hx⟩

/-- The earlier-dependency theorem.

If the ranked order of `carrier` decomposes as `pre ++ b :: suffix`, then any carrier member
`a` with `rank a < rank b` occurs in `pre`, i.e. strictly before `b`.  In particular a
dependency edge from `a` to `b` that strictly decreases rank is recorded at an *earlier* position
of the certificate list. -/
theorem mem_prefix_of_rank_lt (rank : α → β) {carrier pre suffix : List α} {a b : α}
    (hsplit : rankedOrder rank carrier = pre ++ b :: suffix) (ha : a ∈ carrier)
    (hab : rank a < rank b) : a ∈ pre := by
  have hmem : a ∈ pre ++ b :: suffix := by
    rw [← hsplit]
    exact (mem_rankedOrder rank carrier).mpr ha
  rcases List.mem_append.mp hmem with h | h
  · exact h
  · rcases List.mem_cons.mp h with h_eq | h_suf
    · rw [h_eq] at hab
      exact absurd hab (lt_irrefl (rank b))
    · obtain ⟨-, h2⟩ := pairwise_append_cons (pairwise_rankedOrder rank carrier) hsplit
      exact absurd (h2 a h_suf) (not_le_of_gt hab)

/-- `mem_prefix_of_rank_lt` for an abstract dependency relation whose edges strictly increase
the rank.  This is the generic form of "a dependency of `b` is listed strictly before `b`". -/
theorem mem_prefix_of_dependency (rank : α → β) {dep : α → α → Prop}
    (hdep : ∀ a b, dep a b → rank a < rank b) {carrier pre suffix : List α} {a b : α}
    (hsplit : rankedOrder rank carrier = pre ++ b :: suffix) (ha : a ∈ carrier) (hd : dep a b) :
    a ∈ pre :=
  mem_prefix_of_rank_lt rank hsplit ha (hdep a b hd)

end TetraStereo.Certificate.FiniteRankedOrder
