import TetraStereo.Engine.CentresRingPairList
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.Engine.RingSeededPairs
open OneCenter
open CentresRing.PairList (combine)

/-- At one distance the individual nonterminal visits have no fixed order. A present
entry is an uppercase tetrahedral publication; absence here is a checked observation. -/
abbrev Spheres := List (List (Option RS))

def Visits (s : Spheres) (walk : List (Option RS)) : Prop :=
  ∃ levels : Spheres, List.Forall₂ List.Perm levels s ∧ walk = levels.flatten

/-- Homogeneity within a distance makes the entire publication stream independent of all
sibling priorities, including those modified by a reference hand. -/
def uniform : List (Option RS) → Bool
  | [] => true
  | x :: xs => xs.all (· == x)

private theorem unique_level {xs ys : List (Option RS)} (perm : ys.Perm xs)
    (same : uniform xs = true) : ys = xs := by
  cases xs with
  | nil => exact perm.eq_nil
  | cons x xs =>
    have all : ∀ y ∈ x :: xs, y = x := by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | tail
      · rfl
      · exact beq_iff_eq.mp (List.all_eq_true.mp same y tail)
    have right := List.eq_replicate_iff.mpr ⟨rfl,all⟩
    have left := List.eq_replicate_iff.mpr ⟨perm.length_eq,fun y hy => all y (perm.mem_iff.mp hy)⟩
    exact left.trans right.symm

theorem walk_exact {s : Spheres} (uniforms : s.all uniform = true) {walk}
    (visited : Visits s walk) : walk = s.flatten := by
  obtain ⟨levels,ordered,rfl⟩ := visited
  suffices levels = s by rw [this]
  induction ordered with
  | nil => rfl
  | cons perm tail ih =>
    rw [List.all_cons,Bool.and_eq_true] at uniforms
    obtain ⟨first,rest⟩ := uniforms
    rw [unique_level perm first,ih rest]

/-- `comparePairs` compares normalized observations in lockstep, including unlabeled nodes.
The first mismatch of like/unlike status decides. Exhausting either queue returns a tie. -/
def compareBits : List Bool → List Bool → Int
  | a::as,b::bs => if a = b then compareBits as bs else if a then 1 else -1
  | _,_ => 0

def like (s : RS) (v : Option RS) : Bool := v == some s

/-- PairList.compareTo checks equal lengths of the *accepted* descriptor lists.
The seeded head is the same within one comparison. -/
def listSign? (s : RS) (a b : List (Option RS)) : Option Int :=
  let x := a.filterMap id
  let y := b.filterMap id
  if x.length = y.length then some (compareBits (x.map (· == s)) (y.map (· == s))) else none

/-- On a homogeneous first occupied sphere, every priority grouping has the same reference.
In the single-reference branch Rule 4b uses its own seed on each ligand. -/
def localSign? (a b : List (Option RS)) : Option Int := do
  match a.findSome? id,b.findSome? id with
  | none,none => return 0
  | some x,some y => return compareBits (a.map (like x)) (b.map (like y))
  | _,_ => none

/-- A root comparison first applies the per-ligand Rule 4b seeds, then, after a tie,
the two independent Rule5New fixed seeds. All present publications here are uppercase,
so Rule 4c contributes equality. -/
structure Decision where
  rule4b : Int
  rule5 : Option Int
  deriving Repr, DecidableEq

def fromVisits? (a b ar br as' bs' : List (Option RS)) : Option Decision := do
  let first ← localSign? a b
  if first ≠ 0 then return ⟨first,none⟩
  let plus ← listSign? .R ar br
  let minus ← listSign? .S as' bs'
  return ⟨0,some (combine plus minus)⟩

def evaluate? (a b : Spheres) : Option Decision := do
  guard (a.all uniform && b.all uniform)
  let x := a.flatten
  let y := b.flatten
  fromVisits? x y x y x y

/-- Six independently ordered traversals (two per-ligand Rule 4b traversals and four
Rule 5 seeded traversals) give the emitted result, even if none uses the input enumeration. -/
theorem independent {a b : Spheres} {out : Decision} (computed : evaluate? a b = some out)
    {x y xr yr xs ys} (ax : Visits a x) (by' : Visits b y) (ar : Visits a xr) (br : Visits b yr)
    (as' : Visits a xs) (bs' : Visits b ys) : fromVisits? x y xr yr xs ys = some out := by
  by_cases ag : a.all uniform = true
  · by_cases bg : b.all uniform = true
    · rw [walk_exact ag ax,walk_exact bg by',walk_exact ag ar,walk_exact bg br,walk_exact ag as',walk_exact bg bs']
      simpa [evaluate?,ag,bg] using computed
    · simp [evaluate?,bg] at computed
  · simp [evaluate?,ag] at computed

/-- Reversing both truth words reverses the first difference, including a tie. -/
theorem complement (a b : List Bool) :
    compareBits (a.map (!·)) (b.map (!·)) = -compareBits a b := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih =>
    cases b with
    | nil => rfl
    | cons y ys => cases x <;> cases y <;> simp [compareBits,ih]

private theorem seed_complement (x : RS) : (x == RS.S) = !(x == RS.R) := by cases x <;> rfl

theorem two_seed_sign (a b : List (Option RS)) :
    listSign? .S a b = (listSign? .R a b).map (-·) := by
  dsimp only [listSign?]
  split
  · simp only [Option.map_some]
    apply congrArg some
    rw [← complement]
    simp only [List.map_map,Function.comp_def,seed_complement]
  · rfl

end TetraStereo.Engine.RingSeededPairs

assert_kernel_only TetraStereo.Engine.RingSeededPairs.independent
assert_kernel_only TetraStereo.Engine.RingSeededPairs.two_seed_sign
