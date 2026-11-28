import TetraStereo.Engine.RingEqualPathHandCounts

/-! Comparison of two four-donor nitrogen arms of the 41-atom cross-parent fixture. -/
set_option autoImplicit false
namespace TetraStereo.Examples.CrossParentRootOrder
open OneCenter Engine
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingNestedActivePair (Reader)
open RingFullPathEligibility (Key)
open RingFullPathTrialReadings (trialKey)
attribute [local instance] lexOrd

def donor (left : Bool) (j : Fin 4) : Fin 8 :=
  ⟨if left then j.val else 4+j.val, by cases left <;> simp <;> omega⟩

def donors (hands : Fin 8 → RS) (left : Bool) : List RS :=
  (List.finRange 4).map fun j => hands (donor left j)

def rCount (hands : Fin 8 → RS) (left rev : Bool) :=
  let nr := (donors hands left).count .R
  if rev then 4-nr else nr

def countWord (hands : Fin 8 → RS) (left rev : Bool) (seed : RS) : List Bool :=
  let nr := rCount hands left rev
  let yes := if seed = .R then nr else 4-nr
  List.replicate yes true ++ List.replicate (4-yes) false

theorem bound (hands : Fin 8 → RS) (left rev : Bool) : rCount hands left rev ≤ 4 := by
  have h : (donors hands left).count .R ≤ 4 := by
    simpa [donors] using (List.count_le_length (l := donors hands left) (a := RS.R))
  cases rev <;> simp [rCount]; omega

def majority (n : Nat) := max n (4-n)

def compareCounts (a b : Nat) : Ordering :=
  (compare (majority a) (majority b)).then (compare a b)

def order (hands : Fin 8 → RS) (rev : Bool) :=
  compareCounts (rCount hands true rev) (rCount hands false rev)

/-- The two higher ranks are sulfur and oxygen. At nitrogen, only a strict
winning arm receives 1; equal populations leave both arms at 0. -/
def rank (hands : Fin 8 → RS) (rev : Bool) (n : Nat) : Nat :=
  if n = 40 then 3 else if n = 39 then 2 else if n = 1 then
    (order hands rev == .gt).toNat else (order hands rev == .lt).toNat

theorem compare_nitrogens (hands : Fin 8 → RS) (rev : Bool) :
    compare (rank hands rev 1) (rank hands rev 2) = order hands rev := by
  cases h : order hands rev <;> simp [rank,h] <;> decide

theorem fields {i : Input} {r : Reader i} {q : Arm i} {k : Key} (h : Fin 8 → RS) (left rev : Bool)
    (got : RingFullPathEligibility.key? i r rev q = some k)
    (fourB : ∀ seed, RingFullPathPairs.stageWords i r rev [] seed q = some (countWord h left rev seed))
    (five : RingFullPathPairs.stageWords i r rev [.lowercase] .R q = some (countWord h left rev .R)) :
    k.bestFourB = max (countWord h left rev .R) (countWord h left rev .S) ∧
    k.fixedR = countWord h left rev .R := by
  unfold RingFullPathEligibility.key? at got
  simp only [RingFullPathPairs.pairs?,RingFullPathRule5.word?,fourB,five] at got
  cases u : RingRetainedStereoRefinement.priority i r rev [] q <;>
    cases l : RingRetainedStereoRefinement.priority i r rev [.lowercase] q <;> simp [u,l] at got
  subst k
  exact ⟨rfl,rfl⟩

private def bits (n : Nat) := List.replicate n true ++ List.replicate (4-n) false

private theorem ranked_counts : ∀ a b : Fin 5,
    compare (max (bits a.val) (bits (4-a.val))) (max (bits b.val) (bits (4-b.val))) =
      compare (majority a.val) (majority b.val) ∧
    compare (bits a.val) (bits b.val) = compare a.val b.val := by decide +kernel

theorem arm_order (h : Fin 8 → RS) (rev : Bool) (x y : Key)
    (prior : x.throughFourA = y.throughFourA) (lower : x.fourC = y.fourC)
    (left : x.bestFourB = max (countWord h true rev .R) (countWord h true rev .S) ∧ x.fixedR = countWord h true rev .R)
    (right : y.bestFourB = max (countWord h false rev .R) (countWord h false rev .S) ∧ y.fixedR = countWord h false rev .R) :
    compare (trialKey x []) (trialKey y []) = compare (rank h rev 1) (rank h rev 2) := by
  have ha := bound h true rev
  have hb := bound h false rev
  obtain ⟨best,fixed⟩ := ranked_counts ⟨rCount h true rev,by omega⟩ ⟨rCount h false rev,by omega⟩
  simp only [trialKey,prior,lower,left.1,left.2,right.1,right.2,List.compare_cons_cons,
    RingBinaryPairScore.compare_bits,Std.ReflOrd.compare_self,Ordering.eq_then,Ordering.then_eq,
    compare_nitrogens]
  change (compare (max (bits _) (bits _)) (max (bits _) (bits _))).then (compare (bits _) (bits _)) = _
  simp only [if_true,reduceCtorEq,if_false]
  rw [best,fixed]
  rfl

theorem order_cases (h : Fin 8 → RS) :
    let a := rCount h true false
    let b := rCount h false false
    (order h false = .eq ↔ a = b) ∧
    (if majority a = majority b then order h true = (order h false).swap
     else order h true = order h false) := by
  have small (a b : Fin 5) :
      (compareCounts a b = .eq ↔ a = b) ∧
      (if majority a = majority b then compareCounts (4-a.val) (4-b.val) = (compareCounts a b).swap
       else compareCounts (4-a.val) (4-b.val) = compareCounts a b) := by
    fin_cases a <;> fin_cases b <;> decide +kernel
  have a := bound h true false
  have b := bound h false false
  simpa [Fin.ext_iff,order,rCount] using small ⟨rCount h true false,by omega⟩ ⟨rCount h false false,by omega⟩

end TetraStereo.Examples.CrossParentRootOrder
assert_kernel_only TetraStereo.Examples.CrossParentRootOrder.arm_order
assert_kernel_only TetraStereo.Examples.CrossParentRootOrder.order_cases
