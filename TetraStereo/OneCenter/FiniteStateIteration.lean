import TetraStereo.OneCenter.RankedOccurrenceIteration
import TetraStereo.Certificate.Dependency

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace FiniteStateIteration

open TetraStereo.OneCenter.DeclarativeCIP

universe u v

/-!
# Tabulated finite-state iteration over a finite carrier

`RankedIteration.iterate` represents a state as an arbitrary function `O → Option L`.  Reading points of `iterate rawStep seed n` can repeatedly recompute earlier states.
On a finite carrier, tabulating each round avoids that repeated evaluation.

Given a carrier list `carrier : List O` that enumerates every element of `O`, this module stores a
round as a *fact list* `List (O × Option L)`:

* the seed round tabulates `seed` over the carrier;
* every later round reads the previous fact list **once** into the lookup state
  `Certificate.Dependency.lookup previous` and re-evaluates every carrier element against that
  single state.

The fact list keeps exactly the carrier keys, in order (`map_fst_tabulatedFacts`), so looking the
list up really is the tabulated state, and each round evaluates `rawStep` once per carrier entry. Association-list lookup remains linear
in the carrier length for each dependency query.

The main theorem `lookupState_tabulatedFacts` proves that when the carrier is complete the
tabulated lookup state *is* the functional iterate, by list-lookup exactness plus ordinary `Nat`
induction.  No per-round solution, fixed point, or system-level hypothesis is assumed anywhere: the
only hypothesis is carrier completeness.  `Nodup`, `Fintype`, decidability of `Option L` and any
occurrence system are not needed.
-/

/-- A fact list pairs a carrier element with its currently tabulated optional outcome.  This is the
same product as `TetraStereo.Certificate.Dependency.Fact`, whose `lookup` is used below, so
tabulations interoperate with the dependency certificate checker without conversion. -/
abbrev Fact (O : Type u) (L : Type v) := O × Option L

variable {O : Type u} {L : Type v}

/-- One tabulation round.  The previous fact list is read into a state **once**, and every carrier
element is then re-evaluated against that single state. -/
def round [DecidableEq O] (carrier : List O)
    (rawStep : (O → Option L) → O → Option L) (previous : List (Fact O L)) : List (Fact O L) :=
  let state := Certificate.Dependency.lookup previous
  carrier.map (fun o => (o, rawStep state o))

/-- Tabulated iteration: `n` rounds from the seed tabulation, by plain `Nat` recursion. -/
def tabulatedFacts [DecidableEq O] (carrier : List O)
    (rawStep : (O → Option L) → O → Option L) (seed : O → Option L) :
    Nat → List (Fact O L)
  | 0 => carrier.map (fun o => (o, seed o))
  | n + 1 => round carrier rawStep (tabulatedFacts carrier rawStep seed n)

/-- The initial fact list tabulates the seed state over the carrier. -/
@[simp] theorem tabulatedFacts_zero [DecidableEq O] (carrier : List O)
    (rawStep : (O → Option L) → O → Option L) (seed : O → Option L) :
    tabulatedFacts carrier rawStep seed 0 = carrier.map (fun o => (o, seed o)) := rfl

/-- Round `n + 1` is one `round` applied to round `n`; the recursion is not nested. -/
@[simp] theorem tabulatedFacts_succ [DecidableEq O] (carrier : List O)
    (rawStep : (O → Option L) → O → Option L) (seed : O → Option L) (n : Nat) :
    tabulatedFacts carrier rawStep seed (n + 1) =
      round carrier rawStep (tabulatedFacts carrier rawStep seed n) := rfl

/-- The lookup state read off a fact list.  It is the dependency-certificate lookup, so a
tabulated round is directly usable as checker state. -/
abbrev lookupState [DecidableEq O] (facts : List (Fact O L)) : O → Option L :=
  Certificate.Dependency.lookup facts

/-- Exact tabulation, list form: looking a tabulated carrier up at a listed element returns that
element's tabulated outcome. -/
theorem lookup_map_self [DecidableEq O] (f : O → Option L) (o : O) :
    ∀ {l : List O}, o ∈ l →
      Certificate.Dependency.lookup (l.map (fun x => (x, f x))) o = f o
  | [], member => absurd member (by simp)
  | a :: rest, member => by
      by_cases heq : a = o
      · subst heq
        simp [Certificate.Dependency.lookup]
      · have member' : o ∈ rest := by
          rcases List.mem_cons.mp member with h | h
          · exact absurd h.symm heq
          · exact h
        simp only [List.map_cons, Certificate.Dependency.lookup, if_neg heq]
        exact lookup_map_self f o member'

/-- The state read off a round is the previous lookup state fed once through `rawStep`. -/
theorem lookup_round [DecidableEq O] (carrier : List O)
    (rawStep : (O → Option L) → O → Option L) (previous : List (Fact O L)) (o : O)
    (member : o ∈ carrier) :
    Certificate.Dependency.lookup (round carrier rawStep previous) o =
      rawStep (Certificate.Dependency.lookup previous) o := by
  dsimp only [round]
  exact lookup_map_self (rawStep (Certificate.Dependency.lookup previous)) o member

/-- One tabulation round, state form: the tabulated state advances by exactly one raw step. -/
theorem lookupState_succ [DecidableEq O] (carrier : List O)
    (complete : ∀ o : O, o ∈ carrier)
    (rawStep : (O → Option L) → O → Option L) (seed : O → Option L) (n : Nat) :
    lookupState (tabulatedFacts carrier rawStep seed (n + 1)) =
      rawStep (lookupState (tabulatedFacts carrier rawStep seed n)) := by
  funext o
  rw [tabulatedFacts_succ]
  exact lookup_round carrier rawStep _ o (complete o)

/-- **Main theorem.**  For a complete carrier, the state tabulated by `n` rounds is exactly the
`n`-fold functional iterate, pointwise on the whole carrier.  The proof is `Nat` induction whose
step only needs `lookup_round` and the induction hypothesis as a *function* equality; it assumes
nothing about the round being a solution of anything. -/
theorem lookupState_tabulatedFacts [DecidableEq O] (carrier : List O)
    (complete : ∀ o : O, o ∈ carrier)
    (rawStep : (O → Option L) → O → Option L) (seed : O → Option L) (n : Nat) :
    lookupState (tabulatedFacts carrier rawStep seed n) =
      RankedIteration.iterate rawStep seed n := by
  induction n with
  | zero =>
      funext o
      exact lookup_map_self seed o (complete o)
  | succ n ih =>
      funext o
      rw [lookupState_succ carrier complete rawStep seed n, ih]
      rfl

/-- Pointwise form of the main theorem. -/
theorem lookup_tabulatedFacts [DecidableEq O] (carrier : List O)
    (complete : ∀ o : O, o ∈ carrier)
    (rawStep : (O → Option L) → O → Option L) (seed : O → Option L) (n : Nat) (o : O) :
    Certificate.Dependency.lookup (tabulatedFacts carrier rawStep seed n) o =
      RankedIteration.iterate rawStep seed n o :=
  congrFun (lookupState_tabulatedFacts carrier complete rawStep seed n) o

/-- Reading the keys of a tabulation of `f` over `l` returns `l` unchanged. -/
theorem map_fst_tabulate (f : O → Option L) (l : List O) :
    (l.map (fun x => (x, f x))).map Prod.fst = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      show Prod.fst (a, f a) :: (t.map (fun x => (x, f x))).map Prod.fst = a :: t
      rw [ih]

/-- The keys of a fact list are always exactly the carrier, in order: tabulation is faithful and
never drops, duplicates or reorders carrier elements. -/
theorem map_fst_tabulatedFacts [DecidableEq O] (carrier : List O)
    (rawStep : (O → Option L) → O → Option L) (seed : O → Option L) (n : Nat) :
    (tabulatedFacts carrier rawStep seed n).map Prod.fst = carrier := by
  induction n with
  | zero =>
      rw [tabulatedFacts_zero]
      exact map_fst_tabulate seed carrier
  | succ n ih =>
      rw [tabulatedFacts_succ]
      dsimp only [round]
      exact map_fst_tabulate
        (fun o => rawStep (Certificate.Dependency.lookup (tabulatedFacts carrier rawStep seed n)) o)
        carrier

/-- Every round has one fact per carrier element. -/
theorem length_tabulatedFacts [DecidableEq O] (carrier : List O)
    (rawStep : (O → Option L) → O → Option L) (seed : O → Option L) (n : Nat) :
    (tabulatedFacts carrier rawStep seed n).length = carrier.length := by
  have h := congrArg List.length (map_fst_tabulatedFacts carrier rawStep seed n)
  simpa only [List.length_map] using h

/-! ## A computable witness

The carrier below is spelled out by hand only to show that `tabulatedFacts` and its lookup really
reduce in the kernel and that the iterations propagate.  Production callers supply their own
complete carrier. -/

/-- Propagate a single positive label from `0` along `1`, `2`, … -/
def toyStep (state : Nat → Option Bool) : Nat → Option Bool
  | 0 => some true
  | n + 1 => state n

/-- After three tabulated rounds the label has propagated to element `2`. -/
theorem toy_tabulated_three_two :
    Certificate.Dependency.lookup (tabulatedFacts [0, 1, 2] toyStep (fun _ => none) 3) 2 =
      some true := by
  decide

end FiniteStateIteration
end OneCenter
end TetraStereo
