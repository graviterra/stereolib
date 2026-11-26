import TetraStereo.Examples.FigureEightArmOrbits

/-! A closed ligand comparison for the VS262 arm topology. A branch code specifies the
hand of its proximal carbon and the two distal hands. For a mixed distal pair, it also
specifies the intervening pseudoasymmetric hand. All eight branch types occur.
This model is specific to the topology and treats the trivalent nitrogen as unoriented. -/
namespace TetraStereo.Examples.FigureEightArmPriority
open FigureEightArmOrbits

private def mixed (a : Fin 8) : Bool := decide (2 ≤ a.val % 4)
private def lowerR (a : Fin 8) : Bool := a.val % 4 == 2
private def proximalR (a : Fin 8) : Bool := decide (4 ≤ a.val)

-- Lower codes 0 and 1 are SS and RR. Codes 2 and 3 are mixed with r and s.
private def distalR (a : Fin 8) : List Bool :=
  if mixed a then [true, false] else [a.val % 4 == 1, a.val % 4 == 1]

/-- A later pass ranks on the complete earlier priorities before its reference bit.
The final bit of each Nat records like/unlike. Sorting these codes gives the
ordered observations without retaining arbitrary identities of tied siblings. -/
private def pathRank (a : Fin 8) (seed useLower : Bool) : Nat :=
  4 * (mixed a).toNat + 2 * (useLower && lowerR a).toNat + (proximalR a == seed).toNat

private def insertRank (n : Nat) : List Nat → List Nat
  | [] => [n]
  | a :: rest => if n ≥ a then n :: a :: rest else a :: insertRank n rest

def reading (a b : Fin 8) (seed useLower : Bool) : Nat :=
  let branches := [a,b]
  let proximal := branches.map (fun v => pathRank v seed useLower)
  let distal := branches.flatMap fun v =>
    (distalR v).map (fun h => 2 * pathRank v seed useLower + (h == seed).toNat)
  ((proximal.foldr insertRank []) ++ (distal.foldr insertRank [])).foldl
    (fun score code => 2 * score + code % 2) 0

/-- Positional encoding of the four pass results. The two readings have six bits
each, and the lower-case pass counts at most two r centers. -/
def priority (a b : Fin 8) : Nat :=
  let units := (mixed a).toNat + (mixed b).toNat
  let best := max (reading a b false false) (reading a b true false)
  let lower := (lowerR a).toNat + (lowerR b).toNat
  ((units * 64 + best) * 3 + lower) * 64 + reading a b true true

def types : List (Fin 8 × Fin 8) :=
  (List.finRange 8).flatMap fun a =>
    ((List.finRange 8).filter (fun b => decide (a ≤ b))).map (a, ·)

private def table := types.map fun t => (priority t.1 t.2,t)
private def recover (n : Nat) := (table.lookup n)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
private theorem recover_sorted : ∀ a b : Fin 8, a ≤ b → recover (priority a b) = some (a,b) := by
  decide +kernel

private theorem ordered (a : Arm) : (orbit a).1 ≤ (orbit a).2 :=
  (min_le_left _ _).trans (le_max_left _ _)

def armPriority (a : Arm) := priority (orbit a).1 (orbit a).2

/-- A tie after all four passes is equivalent to an actual sequence of exchanges
of equivalent ligand positions in the raw eight-sign arms. -/
theorem tie_iff_exchange (a b : Arm) : armPriority a = armPriority b ↔ PhysicalSwap a b := by
  rw [← orbit_eq_iff]
  constructor
  · intro h
    have h' := congrArg recover h
    unfold armPriority at h'
    rw [recover_sorted _ _ (ordered a), recover_sorted _ _ (ordered b)] at h'
    exact Option.some.inj h'
  · intro h
    simp only [armPriority, h]

assert_kernel_only tie_iff_exchange
end TetraStereo.Examples.FigureEightArmPriority
