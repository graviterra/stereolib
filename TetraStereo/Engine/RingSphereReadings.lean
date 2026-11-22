import TetraStereo.Engine.RingNestedActivePair
import Mathlib.Data.List.Permutation

set_option autoImplicit false

namespace TetraStereo.Engine.RingSphereReadings
open OneCenter RingNestedActivePair

/-- A projected word retains every observed entry at its original distance.
Different rule stages and ligands may choose their orders independently. -/
def Word {α : Type} (rows : List (List α)) (word : List α) :=
  ∃ actual, List.Forall₂ List.Perm rows actual ∧ actual.flatten = word

private def variants {α : Type} [DecidableEq α] (row : List α) : List (List α) :=
  match row with
  | [] => [[]]
  | x :: xs => if xs.all (· == x) then [row] else row.permutations.dedup

private theorem mem_variants {α : Type} [DecidableEq α] {row ys : List α} :
    ys ∈ variants row ↔ row.Perm ys := by
  cases row with
  | nil => simp [variants]
  | cons x xs =>
    by_cases same : xs.all (· == x) = true
    · simp only [variants, same, if_true, List.mem_singleton]
      constructor
      · rintro rfl; exact .refl _
      · intro p
        have all : ∀ y ∈ x :: xs, y = x := by
          intro y hy
          rcases List.mem_cons.mp hy with rfl | h
          · rfl
          · exact beq_iff_eq.mp (List.all_eq_true.mp same y h)
        exact (List.eq_replicate_iff.mpr ⟨p.length_eq.symm,fun y hy => all y (p.mem_iff.mpr hy)⟩).trans
          (List.eq_replicate_iff.mpr ⟨rfl,all⟩).symm
    · simp only [variants,if_neg same,List.mem_dedup,List.mem_permutations]
      exact ⟨List.Perm.symm,List.Perm.symm⟩

private def words {α : Type} [DecidableEq α] : List (List α) → List (List α)
  | [] => [[]]
  | row :: rows =>
    let tail := words rows
    (variants row).flatMap fun head => tail.map (head ++ ·)

private theorem mem_words {α : Type} [DecidableEq α] {rows : List (List α)} {word} :
    word ∈ words rows ↔ Word rows word := by
  induction rows generalizing word with
  | nil =>
    constructor
    · intro h; obtain rfl : word = [] := List.mem_singleton.mp h; exact ⟨[],.nil,rfl⟩
    · rintro ⟨_,h,rfl⟩; cases h; exact List.mem_singleton_self _
  | cons x xs ih =>
    simp only [words,List.mem_flatMap,List.mem_map,mem_variants,ih]
    constructor
    · rintro ⟨y,p,_,⟨ys,ps,rfl⟩,rfl⟩; exact ⟨y :: ys,.cons p ps,rfl⟩
    · rintro ⟨ys,h,rfl⟩
      cases h with
      | cons p ps => exact ⟨_,p,_,⟨_,ps,rfl⟩,rfl⟩

theorem canonical {α : Type} (rows : List (List α)) : Word rows rows.flatten := by
  refine ⟨rows,?_,rfl⟩
  induction rows with
  | nil => exact .nil
  | cons _ _ h => exact .cons (.refl _) h

/-- Consensus checks the actual signed score, so opposite seed scores of
magnitude two cannot be silently replaced by a strict score of magnitude one. -/
def across? {α : Type} [DecidableEq α] (f : List α → List α → Option Int)
    (a b : List (List α)) : Option Int := do
  let k ← f a.flatten b.flatten
  if (words a).all (fun x => (words b).all fun y => f x y == some k) then return k else none

theorem across_iff {α : Type} [DecidableEq α] {f : List α → List α → Option Int}
    {a b k} : across? f a b = some k ↔
    ∀ x y, Word a x → Word b y → f x y = some k := by
  constructor
  · intro h
    unfold across? at h
    obtain ⟨v,_,out⟩ := Option.bind_eq_some_iff.mp h
    split at out <;> try contradiction
    next allowed =>
      obtain rfl := Option.some.inj out
      intro x y hx hy
      exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp allowed x (mem_words.mpr hx)) y (mem_words.mpr hy))
  · intro h
    have all : (words a).all (fun x => (words b).all fun y => f x y == some k) = true :=
      List.all_eq_true.mpr fun x hx => List.all_eq_true.mpr fun y hy =>
        beq_iff_eq.mpr (h x y (mem_words.mp hx) (mem_words.mp hy))
    simp only [across?,h _ _ (canonical a) (canonical b),Option.bind_eq_bind,Option.bind_some,all,if_true]; rfl

abbrev Profile := List (List Visit)

def unitRows (p : Profile) (rev : Bool) := p.map (List.map fun v => unit (v.label rev))
def lowerRows (p : Profile) (rev : Bool) := p.map (List.map fun v => lower (v.label rev))
def upperRows (p : Profile) (rev : Bool) :=
  let label (v : Visit) := upper (v.label rev)
  match p with
  | [] => []
  | top :: tail => top.map label :: tail.map fun (row : List Visit) => (row.filter fun (v : Visit) => 0 < v.children).map label

theorem upper_flatten (p : Profile) (rev : Bool) :
    (upperRows p rev).flatten = (descriptors p).map (fun v => upper (v.label rev)) := by
  cases p <;> simp [upperRows,descriptors,List.flatMap_def,List.map_flatten,List.map_map,Function.comp_def]

/-- At the first occupied distance every possible local reference has the
same hand. Distinct hands at greater distance are allowed. -/
def oneReference : List (List (Option RS)) → Bool
  | [] => true
  | row :: rows => match row.filterMap id with
    | [] => oneReference rows
    | h :: hs => hs.all (· == h)

def ord (x y : List Nat) : Option Int := some (lowerScore x y)

/-- Constitution has already tied. Advance to descriptor rules only on a
universal unit equality and in the single-local-reference branch of Rule 4b. -/
def score? (a b : Profile) (rev : Bool) : Option Int := do
  guard (across? ord (unitRows a rev) (unitRows b rev) == some 0)
  let x := upperRows a rev
  let y := upperRows b rev
  guard (oneReference x && oneReference y)
  let first ← across? RingSeededPairs.localSign? x y
  if first ≠ 0 then return first
  let low ← across? ord (lowerRows a rev) (lowerRows b rev)
  if low ≠ 0 then return low
  let plus ← across? (RingSeededPairs.listSign? .R) x y
  let minus ← across? (RingSeededPairs.listSign? .S) x y
  return CentresRing.PairList.combine plus minus

/-- The source stages, each evaluated with freshly chosen traversal words. -/
def stages? (u v : List Nat) (x y : List (Option RS)) (l r : List Nat)
    (xr yr xs ys : List (Option RS)) : Option Int := do
  let firstUnit := lowerScore u v
  if firstUnit ≠ 0 then return firstUnit
  let first ← RingSeededPairs.localSign? x y
  if first ≠ 0 then return first
  let low := lowerScore l r
  if low ≠ 0 then return low
  let plus ← RingSeededPairs.listSign? .R xr yr
  let minus ← RingSeededPairs.listSign? .S xs ys
  return CentresRing.PairList.combine plus minus

theorem independent {a b rev k} (hit : score? a b rev = some k)
    {u v x y l r xr yr xs ys}
    (hu : Word (unitRows a rev) u) (hv : Word (unitRows b rev) v)
    (hx : Word (upperRows a rev) x) (hy : Word (upperRows b rev) y)
    (hl : Word (lowerRows a rev) l) (hr : Word (lowerRows b rev) r)
    (hxr : Word (upperRows a rev) xr) (hyr : Word (upperRows b rev) yr)
    (hxs : Word (upperRows a rev) xs) (hys : Word (upperRows b rev) ys) :
    stages? u v x y l r xr yr xs ys = some k := by
  by_cases unitTie : across? ord (unitRows a rev) (unitRows b rev) = some 0
  · have units := Option.some.inj (across_iff.mp unitTie _ _ hu hv)
    by_cases allowed : (oneReference (upperRows a rev) && oneReference (upperRows b rev)) = true
    · simp only [score?,unitTie,beq_self_eq_true,allowed,guard_true,pure_bind] at hit
      obtain ⟨first,hfirst,more⟩ := Option.bind_eq_some_iff.mp hit
      have f := across_iff.mp hfirst _ _ hx hy
      by_cases strict : first ≠ 0
      · simpa [stages?,units,f,strict] using more
      · obtain rfl := not_ne_iff.mp strict
        simp only [ne_eq,not_true_eq_false,if_false] at more
        obtain ⟨low,hlow,more⟩ := Option.bind_eq_some_iff.mp more
        have loweq := Option.some.inj (across_iff.mp hlow _ _ hl hr)
        by_cases decisive : low ≠ 0
        · simpa [stages?,units,f,loweq,decisive] using more
        · obtain rfl := not_ne_iff.mp decisive
          simp only [not_true_eq_false,if_false] at more
          obtain ⟨plus,hp,more⟩ := Option.bind_eq_some_iff.mp more
          obtain ⟨minus,hm,out⟩ := Option.bind_eq_some_iff.mp more
          simpa [stages?,units,f,loweq,across_iff.mp hp _ _ hxr hyr,across_iff.mp hm _ _ hxs hys] using out
    · simp [score?,unitTie,allowed] at hit
  · simp [score?,unitTie] at hit

end TetraStereo.Engine.RingSphereReadings

assert_kernel_only TetraStereo.Engine.RingSphereReadings.across_iff
assert_kernel_only TetraStereo.Engine.RingSphereReadings.independent
