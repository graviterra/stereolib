import Mathlib.Tactic.DeriveEncodable
import Mathlib.Data.Nat.Basic
import TetraStereo.KernelOnly
import Lean.Elab.Tactic.Omega

/-!
# Exact orbit keys for finite rooted oriented branches

The parent edge at a tetrahedral node is fixed. Its three displayed children may
be exchanged, with each transposition reversing the displayed orientation.
Ordinary binary nodes have unordered children. Labels are arbitrary natural
numbers (e.g. independently encoded atom/bond records), not CIP priorities.

The constructive key recursively normalizes each subtree and selects the least
serialization of the two or six explicitly legal local displays. The theorem
has arbitrary finite depth, no CIP descriptor claim, and no cyclic-closure claim.
-/
namespace TetraStereo.Engine.OrientedBranchOrbit

inductive Tree where
  | leaf : Nat → Tree
  | unary : Nat → Tree → Tree
  | ordinary : Nat → Tree → Tree → Tree
  | tetra : Nat → Bool → Tree → Tree → Tree → Tree
  deriving Encodable

/-- Legal relabellings, defined independently of all keys and encodings.
The two adjacent exchanges generate all permutations of the three children. -/
inductive Legal : Tree → Tree → Prop where
  | refl (t) : Legal t t
  | symm {t u} : Legal t u → Legal u t
  | trans {t u v} : Legal t u → Legal u v → Legal t v
  | unary {a b} (label) : Legal a b → Legal (.unary label a) (.unary label b)
  | ordinary {a b c d} (label) : Legal a c → Legal b d →
      Legal (.ordinary label a b) (.ordinary label c d)
  | tetra {a b c d e f} (label hand) : Legal a d → Legal b e → Legal c f →
      Legal (.tetra label hand a b c) (.tetra label hand d e f)
  | ordinarySwap (label a b) : Legal (.ordinary label a b) (.ordinary label b a)
  | swap12 (label hand a b c) :
      Legal (.tetra label hand a b c) (.tetra label (!hand) b a c)
  | swap23 (label hand a b c) :
      Legal (.tetra label hand a b c) (.tetra label (!hand) a c b)

/-- Select the lesser serialization; ties are equal trees. -/
def pick (a b : Tree) : Tree :=
  if Encodable.encode a ≤ Encodable.encode b then a else b

theorem pick_eq (a b : Tree) : pick a b = a ∨ pick a b = b := by
  unfold pick
  split <;> simp

theorem encode_pick (a b : Tree) :
    Encodable.encode (pick a b) = min (Encodable.encode a) (Encodable.encode b) := by
  unfold pick
  split <;> simp_all [Nat.min_def]

theorem pick_comm (a b : Tree) : pick a b = pick b a := by
  apply Encodable.encode_injective
  simp only [encode_pick, Nat.min_comm]

theorem pick_assoc (a b c : Tree) : pick (pick a b) c = pick a (pick b c) := by
  apply Encodable.encode_injective
  simp only [encode_pick, Nat.min_assoc]

theorem pick_idem (a : Tree) : pick a a = a := by simp [pick]

/-- Six legal signed displays. Minimum serialization chooses a deterministic
child order and transports orientation by the parity of the permutation. -/
def localTetra (n : Nat) (s : Bool) (a b c : Tree) : Tree :=
  pick (.tetra n s a b c)
    (pick (.tetra n s b c a)
      (pick (.tetra n s c a b)
        (pick (.tetra n (!s) b a c)
          (pick (.tetra n (!s) a c b) (.tetra n (!s) c b a)))))

/-- Ordinary unordered node canonicalization. -/
def localOrdinary (n : Nat) (a b : Tree) : Tree :=
  pick (.ordinary n a b) (.ordinary n b a)

theorem localOrdinary_swap (n a b) : localOrdinary n a b = localOrdinary n b a :=
  pick_comm _ _

theorem localTetra_swap12 (n s a b c) :
    localTetra n s a b c = localTetra n (!s) b a c := by
  apply Encodable.encode_injective
  simp only [localTetra, Bool.not_not, encode_pick]
  omega

theorem localTetra_swap23 (n s a b c) :
    localTetra n s a b c = localTetra n (!s) a c b := by
  apply Encodable.encode_injective
  simp only [localTetra, Bool.not_not, encode_pick]
  omega

/-- Constructive bottom-up canonical form, with bounded local work at every node. -/
def canonical : Tree → Tree
  | .leaf n => .leaf n
  | .unary n a => .unary n (canonical a)
  | .ordinary n a b => localOrdinary n (canonical a) (canonical b)
  | .tetra n s a b c => localTetra n s (canonical a) (canonical b) (canonical c)

def key (t : Tree) : Nat := Encodable.encode (canonical t)

private theorem legal_pick {t a b : Tree} (ha : Legal t a) (hb : Legal t b) :
    Legal t (pick a b) := by
  rcases pick_eq a b with h | h
  · rw [h]
    exact ha
  · rw [h]
    exact hb

/-- An exchange of the first and third child is three adjacent exchanges. -/
theorem swap13 (label hand a b c) :
    Legal (.tetra label hand a b c) (.tetra label (!hand) c b a) := by
  have h := Legal.trans (Legal.swap12 label hand a b c)
    (Legal.trans (Legal.swap23 label (!hand) b a c)
      (Legal.swap12 label (!(!hand)) b c a))
  simpa using h

private theorem legal_localTetra (n s a b c) :
    Legal (.tetra n s a b c) (localTetra n s a b c) := by
  unfold localTetra
  apply legal_pick (Legal.refl _)
  · apply legal_pick
    · simpa using Legal.trans (Legal.swap12 n s a b c) (Legal.swap23 n (!s) b a c)
    · apply legal_pick
      · simpa using Legal.trans (Legal.swap23 n s a b c) (Legal.swap12 n (!s) a c b)
      · exact legal_pick (Legal.swap12 n s a b c)
          (legal_pick (Legal.swap23 n s a b c) (swap13 n s a b c))

theorem legal_canonical (t : Tree) : Legal t (canonical t) := by
  induction t with
  | leaf n => exact Legal.refl _
  | unary n a ha => exact Legal.unary n ha
  | ordinary n a b ha hb =>
    exact Legal.trans (Legal.ordinary n ha hb)
      (legal_pick (Legal.refl _) (Legal.ordinarySwap n _ _))
  | tetra n s a b c ha hb hc =>
    exact Legal.trans (Legal.tetra n s ha hb hc) (legal_localTetra n s _ _ _)

/-- Every generator preserves the recursively computed normal form. -/
theorem canonical_eq_of_legal {t u : Tree} (h : Legal t u) :
    canonical t = canonical u := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | unary n _ ih => simp only [canonical, ih]
  | ordinary n _ _ ih₁ ih₂ => simp only [canonical, ih₁, ih₂]
  | tetra n s _ _ _ ih₁ ih₂ ih₃ => simp only [canonical, ih₁, ih₂, ih₃]
  | ordinarySwap n a b => exact localOrdinary_swap _ _ _
  | swap12 n s a b c => exact localTetra_swap12 _ _ _ _ _
  | swap23 n s a b c => exact localTetra_swap23 _ _ _ _ _

theorem canonical_eq_iff_legal (t u : Tree) : canonical t = canonical u ↔ Legal t u := by
  constructor
  · intro h
    apply Legal.trans (legal_canonical t)
    rw [h]
    exact Legal.symm (legal_canonical u)
  · exact canonical_eq_of_legal

theorem key_eq_iff_legal (t u : Tree) : key t = key u ↔ Legal t u := by
  unfold key
  rw [Encodable.encode_injective.eq_iff, canonical_eq_iff_legal]

theorem canonical_idempotent (t : Tree) : canonical (canonical t) = canonical t :=
  (canonical_eq_of_legal (legal_canonical t)).symm

/-- Two legally equal children erase orientation through a genuine odd exchange. -/
theorem equal_children_erase_hand (label hand) {a b : Tree} (c : Tree)
    (hab : Legal a b) :
    Legal (.tetra label hand a b c) (.tetra label (!hand) a b c) := by
  exact Legal.trans (Legal.swap12 label hand a b c)
    (Legal.tetra label (!hand) (Legal.symm hab) hab (Legal.refl c))

theorem equal_children_key_erase_hand (label hand) {a b : Tree} (c : Tree)
    (hab : key a = key b) :
    key (.tetra label hand a b c) = key (.tetra label (!hand) a b c) :=
  (key_eq_iff_legal _ _).mpr
    (equal_children_erase_hand label hand c ((key_eq_iff_legal _ _).mp hab))

/-- The other adjacent pair also erases orientation by an actual exchange. -/
theorem equal_children23_erase_hand (label hand) (a : Tree) {b c : Tree}
    (hbc : Legal b c) :
    Legal (.tetra label hand a b c) (.tetra label (!hand) a b c) :=
  Legal.trans (Legal.swap23 label hand a b c)
    (Legal.tetra label (!hand) (Legal.refl a) (Legal.symm hbc) hbc)

/-- The nonadjacent equal pair uses the three-exchange odd permutation. -/
theorem equal_children13_erase_hand (label hand) {a c : Tree} (b : Tree)
    (hac : Legal a c) :
    Legal (.tetra label hand a b c) (.tetra label (!hand) a b c) :=
  Legal.trans (swap13 label hand a b c)
    (Legal.tetra label (!hand) (Legal.symm hac) (Legal.refl b) hac)

assert_kernel_only key_eq_iff_legal
assert_kernel_only equal_children_erase_hand
assert_kernel_only canonical_idempotent

end TetraStereo.Engine.OrientedBranchOrbit
