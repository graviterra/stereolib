import TetraStereo.Engine.RingPromotionBalance

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.ReferenceFrame
open OneCenter LocalizedChemicalRingPromotionAggregation

/-- A permutation of the unexamined candidates can pair each true reading with its
opposite. This certificate only requires covariance under transport, without choosing
or computing any individual hand in that subset. Fixed points must have a tied reading. -/
theorem zero_of_opposite_transport {A : Type} (remaining : List A) (read : A → Option RS)
    (move : A → A) (onto : (remaining.map move).Perm remaining)
    (opposite : ∀ a ∈ remaining, read (move a) = (read a).map RS.swap) :
    readingBalance (remaining.map read) = 0 := by
  have transported : (remaining.map move).map read = (remaining.map read).map (Option.map RS.swap) := by
    simp only [List.map_map]
    exact List.map_congr_left (fun a h => opposite a h)
  have e := readingBalance_perm (onto.map read)
  rw [transported,readingBalance_swap] at e
  omega

/-- The unpaired remainder determines the exact signed promotion result, including its
case and refusal, for a complete molecular population admitting the indicated transport. -/
theorem Population.signed_of_transport {m g p} (s : Population m g p)
    (known remaining : List (Trial s.frame)) (partition : s.trials.Perm (known ++ remaining))
    (move : Trial s.frame → Trial s.frame) (onto : (remaining.map move).Perm remaining)
    (opposite : ∀ a ∈ remaining, (move a).hand? false = (a.hand? false).map RS.swap) :
    s.signedDescriptor = (survivingHand (readingBalance (known.map (fun a => a.hand? false)))).map
      fun hand => if s.frame.reversals % 2 = 0 then .chiral hand else .pseudoasymmetric (pseudoRSOfRS hand) := by
  have cancel := zero_of_opposite_transport remaining (fun a => a.hand? false) move onto opposite
  have balance := readingBalance_perm (partition.map (fun a => a.hand? false))
  rw [List.map_append] at balance
  have add (a b : List (Option RS)) : readingBalance (a ++ b) = readingBalance a + readingBalance b := by
    simp [readingBalance]
  rw [add,cancel,add_zero] at balance
  rw [s.signedDescriptor_eq]
  simp only [Population.hands,balance]

/-- With no symmetry witness, every unresolved trial contributes at most one in either
direction. A sufficient margin certifies a strict answer for every completion. -/
theorem balance_bounds (xs : List (Option RS)) :
    -(xs.length : Int) ≤ readingBalance xs ∧ readingBalance xs ≤ (xs.length : Int) := by
  induction xs with
  | nil => simp [readingBalance]
  | cons x xs ih =>
    have term : -(1 : Int) ≤ readingScore x ∧ readingScore x ≤ 1 := by
      cases x with
      | none => decide
      | some s => cases s <;> decide
    change _ ≤ readingScore x + readingBalance xs ∧ readingScore x + readingBalance xs ≤ _
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    omega

/-- Sharp positive and negative margins when unseen choices are independent and may be
either strict hand or a proved tie. The necessity proof supplies explicit extreme fills. -/
theorem all_completions {known : Int} {n : Nat} :
    ((∀ xs : List (Option RS), xs.length = n → 0 < known + readingBalance xs) ↔ (n : Int) < known) ∧
    ((∀ xs : List (Option RS), xs.length = n → known + readingBalance xs < 0) ↔ known < -(n : Int)) := by
  have neg (k : Nat) : readingBalance (List.replicate k (some .S)) = -(k : Int) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.replicate_succ]
      change (-1 : Int) + readingBalance _ = _
      rw [ih]
      omega
  have pos (k : Nat) : readingBalance (List.replicate k (some .R)) = (k : Int) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.replicate_succ]
      change (1 : Int) + readingBalance _ = _
      rw [ih]
      omega
  constructor <;> constructor
  · intro h
    have worst := h _ (List.length_replicate (a := some RS.S) (n := n))
    rw [neg] at worst
    omega
  · intro h xs len
    have bound := balance_bounds xs
    omega
  · intro h
    have worst := h _ (List.length_replicate (a := some RS.R) (n := n))
    rw [pos] at worst
    omega
  · intro h xs len
    have bound := balance_bounds xs
    omega

end TetraStereo.Engine.RingChemicalPriority.ReferenceFrame

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.zero_of_opposite_transport
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Population.signed_of_transport
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.all_completions
