import TetraStereo.OneCenter.DeclarativeCIPOrdinaryCanonicalAddressing
import TetraStereo.OneCenter.DeclarativeCIPCarrier

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section

open scoped Classical

universe u

/-!
# Independent order laws and total preorder for the eight ordinary rules

For `StereochemicalProblemData` with the ordinary canonical addressing family, every ordinary rule
outcome (Rules 1a, 1b, 2, 3, 4a, 4b, 4c, 5) is a first-difference comparison of one observation
field per ligand, read through one chosen faithful expansion and ordinary canonical addressing
(`ordinary_ruleOutcome_lex`).  The first-difference laws then supply
`OrdinaryRuleOutcomeOrderLaws`, and the existing assembly theorem concludes that ordinary
declarative priority is a total preorder (`withOrdinaryCanonicalAddressing_ordinaryPriority`).

Premises: admissible expansions are faithful and exist; the supplied evidence satisfies the
specification's `evidence_invariant`.  Rule 6 is outside this result.  Generating the semantic
evidence from a molecule, and relating the production runtime to these outcomes, remain separate.
-/

open RootedDigraph

/-- Rules 3--5 hierarchy outcomes are first-difference comparisons of encoded fields. -/
theorem stereochemicalHierarchyOutcome_iff_lexOutcome {Atom : Type u}
    (rule : StereochemicalRule) {left right : RootedDigraph Atom}
    (leftAddressing : left.Addressing) (leftEvidence : StereochemicalEvidence left)
    (rightAddressing : right.Addressing) (rightEvidence : StereochemicalEvidence right)
    (outcome : Ordering) :
    StereochemicalHierarchyOutcome rule left leftAddressing leftEvidence right rightAddressing
        rightEvidence outcome ↔
      LexOutcome (fun position => stereoValue rule (addressEvidence leftAddressing leftEvidence position))
        (fun position => stereoValue rule (addressEvidence rightAddressing rightEvidence position))
        outcome := by
  apply FirstDifferenceOutcome.congr
  intro position outcome
  rw [stereochemicalOutcomeAt_iff, orderedKeyOutcome_iff_compare]

/-! ## Order-embedding codes into lexicographic lists of naturals -/

/-- A strictly order-preserving injective code into `List ℕ`. -/
structure LexCode (β : Type*) [LinearOrder β] where
  code : β → List ℕ
  lt_iff : ∀ a b, code a < code b ↔ a < b
  injective : Function.Injective code

/-- A nonempty, prefix-free order-embedding code, suitable for concatenation. -/
structure PrefixCode (β : Type*) [LinearOrder β] extends LexCode β where
  ne_nil : ∀ b, code b ≠ []
  prefix_free : ∀ a b, code a <+: code b → a = b

theorem LexCode.orderedKeyOutcome_iff {β : Type*} [LinearOrder β] (c : LexCode β) (a b : β)
    (outcome : Ordering) :
    OrderedKeyOutcome (c.code a) (c.code b) outcome ↔ OrderedKeyOutcome a b outcome := by
  rcases lt_trichotomy a b with h | h | h
  · rw [orderedKeyOutcome_of_lt h, orderedKeyOutcome_of_lt ((c.lt_iff a b).2 h)]
  · rw [orderedKeyOutcome_of_eq h, orderedKeyOutcome_of_eq (by rw [h])]
  · rw [orderedKeyOutcome_of_gt h, orderedKeyOutcome_of_gt ((c.lt_iff b a).2 h)]

theorem List.append_lt_append_left_iff {x s t : List ℕ} : x ++ s < x ++ t ↔ s < t := by
  induction x with
  | nil => rfl
  | cons a x ih =>
      constructor
      · intro h
        cases h with
        | cons h => exact ih.1 h
        | rel h => exact absurd h (lt_irrefl _)
      · intro h
        exact List.Lex.cons (ih.2 h)

theorem List.append_lt_append_of_not_prefix {x y s t : List ℕ} (hxy : ¬ x <+: y)
    (hyx : ¬ y <+: x) : x ++ s < y ++ t ↔ x < y := by
  induction x generalizing y with
  | nil => exact absurd (List.nil_prefix) hxy
  | cons a x ih =>
      cases y with
      | nil => exact absurd (List.nil_prefix) hyx
      | cons b y =>
          rcases lt_trichotomy a b with hab | rfl | hab
          · exact ⟨fun _ => List.Lex.rel hab, fun _ => List.Lex.rel hab⟩
          · have hxy' : ¬ x <+: y := fun h => hxy (List.prefix_cons_inj _ |>.2 h)
            have hyx' : ¬ y <+: x := fun h => hyx (List.prefix_cons_inj _ |>.2 h)
            constructor
            · intro h
              cases h with
              | cons h => exact List.Lex.cons ((ih hxy' hyx').1 h)
              | rel h => exact absurd h (lt_irrefl _)
            · intro h
              cases h with
              | cons h => exact List.Lex.cons ((ih hxy' hyx').2 h)
              | rel h => exact absurd h (lt_irrefl _)
          · constructor
            · intro h
              cases h with
              | cons h => exact absurd hab (lt_irrefl _)
              | rel h => exact absurd (lt_trans h hab) (lt_irrefl _)
            · intro h
              cases h with
              | cons h => exact absurd hab (lt_irrefl _)
              | rel h => exact absurd (lt_trans h hab) (lt_irrefl _)

theorem PrefixCode.append_lt_iff {β : Type*} [LinearOrder β] (c : PrefixCode β) (a b : β)
    (s t : List ℕ) :
    c.code a ++ s < c.code b ++ t ↔ a < b ∨ (a = b ∧ s < t) := by
  by_cases hab : a = b
  · subst hab
    rw [List.append_lt_append_left_iff]
    exact ⟨fun h => Or.inr ⟨rfl, h⟩, fun h => h.elim (fun h => absurd h (lt_irrefl _))
      (fun h => h.2)⟩
  · have hxy : ¬ c.code a <+: c.code b := fun h => hab (c.prefix_free a b h)
    have hyx : ¬ c.code b <+: c.code a := fun h => hab (c.prefix_free b a h).symm
    rw [List.append_lt_append_of_not_prefix hxy hyx, c.lt_iff]
    exact ⟨Or.inl, fun h => h.elim id (fun h => absurd h.1 hab)⟩

theorem PrefixCode.append_prefix {β : Type*} [LinearOrder β] (c : PrefixCode β) {a b : β}
    {s t : List ℕ} (h : c.code a ++ s <+: c.code b ++ t) : a = b ∧ s <+: t := by
  have hpre : c.code a <+: c.code b ∨ c.code b <+: c.code a := by
    obtain ⟨r, hr⟩ := h
    rw [List.append_assoc] at hr
    rcases List.append_eq_append_iff.1 hr with ⟨m, hm, _⟩ | ⟨m, hm, _⟩
    · exact Or.inl ⟨m, hm.symm⟩
    · exact Or.inr ⟨m, hm.symm⟩
  have hab : a = b := hpre.elim (c.prefix_free a b) (fun h => (c.prefix_free b a h).symm)
  subst hab
  exact ⟨rfl, (List.prefix_append_right_inj _).1 h⟩

/-- The single-token code of a natural number. -/
def natCode : PrefixCode ℕ where
  code n := [n]
  lt_iff a b := List.lex_singleton_iff a b
  injective a b h := by simpa using h
  ne_nil _ := by simp
  prefix_free a b h := by
    have := h.eq_of_length (by simp)
    simpa using this

/-- Lists of prefix-coded values: shifted element codes, then the terminator `0`. -/
def listCodeAux {β : Type*} [LinearOrder β] (c : PrefixCode β) : List β → List ℕ
  | [] => [0]
  | b :: bs => (c.code b).map Nat.succ ++ listCodeAux c bs

theorem shifted_head_pos {β : Type*} [LinearOrder β] (c : PrefixCode β) (b : β) :
    ∃ head rest, (c.code b).map Nat.succ = (head + 1) :: rest := by
  obtain ⟨head, rest, h⟩ := List.exists_cons_of_ne_nil (c.ne_nil b)
  exact ⟨head, rest.map Nat.succ, by rw [h]; rfl⟩

theorem List.map_succ_lt_iff : ∀ {l m : List ℕ}, l.map Nat.succ < m.map Nat.succ ↔ l < m
  | [], [] => by simp
  | [], _ :: _ => ⟨fun _ => List.nil_lt_cons _ _, fun _ => List.nil_lt_cons _ _⟩
  | _ :: _, [] => ⟨fun h => absurd h (List.not_lt_nil _), fun h => absurd h (List.not_lt_nil _)⟩
  | a :: l, b :: m => by
      simp only [List.map_cons]
      constructor
      · intro h
        cases h with
        | cons h => exact List.Lex.cons (List.map_succ_lt_iff.1 h)
        | rel h => exact List.Lex.rel (Nat.succ_lt_succ_iff.1 h)
      · intro h
        cases h with
        | cons h => exact List.Lex.cons (List.map_succ_lt_iff.2 h)
        | rel h => exact List.Lex.rel (Nat.succ_lt_succ h)

theorem List.map_succ_prefix_iff : ∀ {l m : List ℕ}, l.map Nat.succ <+: m.map Nat.succ ↔ l <+: m
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l, b :: m => by
      simp only [List.map_cons, List.cons_prefix_cons, Nat.succ.injEq]
      rw [List.map_succ_prefix_iff]

/-- The shifted code is still a prefix code. -/
def PrefixCode.shift {β : Type*} [LinearOrder β] (c : PrefixCode β) : PrefixCode β where
  code b := (c.code b).map Nat.succ
  lt_iff a b := by rw [← c.lt_iff]; exact List.map_succ_lt_iff
  injective a b h := c.injective (List.map_injective_iff.2 Nat.succ_injective h)
  ne_nil b := by simpa using c.ne_nil b
  prefix_free a b h := c.prefix_free a b (List.map_succ_prefix_iff.1 h)

theorem PrefixCode.shift_head {β : Type*} [LinearOrder β] (c : PrefixCode β) (b : β) :
    ∃ head rest, c.shift.code b = (head + 1) :: rest := by
  obtain ⟨head, rest, h⟩ := List.exists_cons_of_ne_nil (c.ne_nil b)
  exact ⟨head, rest.map Nat.succ, by show (c.code b).map Nat.succ = _; rw [h]; rfl⟩

theorem prefix_of_eq {l m : List ℕ} (h : l = m) : l <+: m := by
  rw [h]

theorem lex_cons_iff' {a b : ℕ} {l m : List ℕ} :
    a :: l < b :: m ↔ a < b ∨ (a = b ∧ l < m) := by
  constructor
  · intro h
    cases h with
    | cons h => exact Or.inr ⟨rfl, h⟩
    | rel h => exact Or.inl h
  · rintro (h | ⟨rfl, h⟩)
    · exact List.Lex.rel h
    · exact List.Lex.cons h

theorem list_cons_lt_cons_iff {β : Type*} [LinearOrder β] {a b : β} {l m : List β} :
    a :: l < b :: m ↔ a < b ∨ (a = b ∧ l < m) := by
  constructor
  · intro h
    cases h with
    | cons h => exact Or.inr ⟨rfl, h⟩
    | rel h => exact Or.inl h
  · rintro (h | ⟨rfl, h⟩)
    · exact List.Lex.rel h
    · exact List.Lex.cons h

/-- Code of a list: shifted element codes followed by the terminator `0`. -/
def listCodeAux' {β : Type*} [LinearOrder β] (c : PrefixCode β) : List β → List ℕ
  | [] => [0]
  | b :: bs => c.shift.code b ++ listCodeAux' c bs

theorem listCodeAux'_cons_head {β : Type*} [LinearOrder β] (c : PrefixCode β) (b : β)
    (bs : List β) : ∃ head rest, listCodeAux' c (b :: bs) = (head + 1) :: rest := by
  obtain ⟨head, rest, h⟩ := c.shift_head b
  exact ⟨head, rest ++ listCodeAux' c bs, by simp [listCodeAux', h]⟩

def listCode {β : Type*} [LinearOrder β] (c : PrefixCode β) : PrefixCode (List β) where
  code := listCodeAux' c
  lt_iff := by
    intro l m
    induction l generalizing m with
    | nil =>
        cases m with
        | nil => exact ⟨fun h => absurd h (lt_irrefl _), fun h => absurd h (lt_irrefl _)⟩
        | cons b bs =>
            obtain ⟨head, rest, h⟩ := listCodeAux'_cons_head c b bs
            refine ⟨fun _ => List.nil_lt_cons _ _, fun _ => ?_⟩
            show [0] < listCodeAux' c (b :: bs)
            rw [h]
            exact List.Lex.rel (Nat.succ_pos _)
    | cons a as ih =>
        cases m with
        | nil =>
            obtain ⟨head, rest, h⟩ := listCodeAux'_cons_head c a as
            refine ⟨fun hlt => ?_, fun hlt => absurd hlt (List.not_lt_nil _)⟩
            change listCodeAux' c (a :: as) < [0] at hlt
            rw [h] at hlt
            rcases lex_cons_iff'.1 hlt with hlt | ⟨heq, _⟩
            · omega
            · omega
        | cons b bs =>
            show c.shift.code a ++ listCodeAux' c as < c.shift.code b ++ listCodeAux' c bs ↔ _
            rw [c.shift.append_lt_iff, list_cons_lt_cons_iff, ih bs]
  injective := by
    intro l m h
    induction l generalizing m with
    | nil =>
        cases m with
        | nil => rfl
        | cons b bs =>
            obtain ⟨head, rest, hb⟩ := listCodeAux'_cons_head c b bs
            change [0] = listCodeAux' c (b :: bs) at h
            rw [hb] at h
            simp at h
    | cons a as ih =>
        cases m with
        | nil =>
            obtain ⟨head, rest, ha⟩ := listCodeAux'_cons_head c a as
            change listCodeAux' c (a :: as) = [0] at h
            rw [ha] at h
            simp at h
        | cons b bs =>
            change c.shift.code a ++ listCodeAux' c as = c.shift.code b ++ listCodeAux' c bs at h
            obtain ⟨hab, _⟩ := c.shift.append_prefix (prefix_of_eq h)
            subst hab
            have := List.append_cancel_left h
            rw [ih this]
  ne_nil l := by cases l <;> simp [listCodeAux', (PrefixCode.shift _).ne_nil]
  prefix_free := by
    intro l m h
    induction l generalizing m with
    | nil =>
        cases m with
        | nil => rfl
        | cons b bs =>
            obtain ⟨head, rest, hb⟩ := listCodeAux'_cons_head c b bs
            change [0] <+: listCodeAux' c (b :: bs) at h
            rw [hb] at h
            simp at h
    | cons a as ih =>
        cases m with
        | nil =>
            obtain ⟨head, rest, ha⟩ := listCodeAux'_cons_head c a as
            change listCodeAux' c (a :: as) <+: [0] at h
            rw [ha] at h
            have := h.length_le
            have hlen := (List.prefix_cons_iff.1 h)
            simp at hlen
        | cons b bs =>
            change c.shift.code a ++ listCodeAux' c as <+: c.shift.code b ++ listCodeAux' c bs at h
            obtain ⟨hab, hpre⟩ := c.shift.append_prefix h
            subst hab
            rw [ih bs hpre]

/-- Code of a lexicographic pair: concatenated component codes. -/
def pairCode {β γ : Type*} [LinearOrder β] [LinearOrder γ] (c₁ : PrefixCode β)
    (c₂ : PrefixCode γ) : PrefixCode (β ×ₗ γ) where
  code x := c₁.code (ofLex x).1 ++ c₂.code (ofLex x).2
  lt_iff x y := by
    rw [c₁.append_lt_iff, c₂.lt_iff, Prod.Lex.lt_iff]
  injective x y h := by
    have h' : c₁.code (ofLex x).1 ++ c₂.code (ofLex x).2 =
        c₁.code (ofLex y).1 ++ c₂.code (ofLex y).2 := h
    obtain ⟨h₁, _⟩ := c₁.append_prefix (prefix_of_eq h')
    rw [h₁] at h'
    have h₂ := c₂.injective (List.append_cancel_left h')
    have e : ofLex x = ofLex y := Prod.ext h₁ h₂
    simpa using congrArg toLex e
  ne_nil x := by simp [c₁.ne_nil]
  prefix_free x y h := by
    obtain ⟨h₁, hpre⟩ := c₁.append_prefix h
    have h₂ := c₂.prefix_free _ _ hpre
    have e : ofLex x = ofLex y := Prod.ext h₁ h₂
    simpa using congrArg toLex e

/-- The order-reversing unary digit code `0^x 1`. -/
def digitCode (x : ℕ) : List ℕ := List.replicate x 0 ++ [1]

theorem digitCode_succ (x : ℕ) : digitCode (x + 1) = 0 :: digitCode x := rfl

theorem digitCode_lt_iff : ∀ x y, digitCode x < digitCode y ↔ y < x
  | 0, 0 => ⟨fun h => absurd h (lt_irrefl _), fun h => absurd h (Nat.not_lt_zero _)⟩
  | 0, y + 1 => by
      rw [digitCode_succ]
      exact ⟨fun h => by rcases lex_cons_iff'.1 h with h | ⟨h, _⟩ <;> omega,
        fun h => absurd h (Nat.not_lt_zero _)⟩
  | x + 1, 0 => by
      rw [digitCode_succ]
      exact ⟨fun _ => Nat.succ_pos _, fun _ => List.Lex.rel (by decide)⟩
  | x + 1, y + 1 => by
      rw [digitCode_succ, digitCode_succ, lex_cons_iff', digitCode_lt_iff x y]
      omega

theorem digitCode_prefix : ∀ {x y}, digitCode x <+: digitCode y → x = y
  | 0, 0, _ => rfl
  | 0, y + 1, h => by rw [digitCode_succ] at h; simp [digitCode] at h
  | x + 1, 0, h => by rw [digitCode_succ] at h; simp [digitCode] at h
  | x + 1, y + 1, h => by
      rw [digitCode_succ, digitCode_succ, List.cons_prefix_cons] at h
      rw [digitCode_prefix h.2]

theorem digitCode_head_le (x : ℕ) (rest : List ℕ) : digitCode x ++ rest < [2] := by
  cases x with
  | zero => exact List.Lex.rel (by decide)
  | succ x => exact List.Lex.rel (by decide)

/-- Digits as a prefix code on the reversed naturals. -/
def digitPrefixCode : PrefixCode ℕᵒᵈ where
  code d := digitCode (OrderDual.ofDual d)
  lt_iff a b := digitCode_lt_iff _ _
  injective a b h := by
    have := digitCode_prefix (prefix_of_eq h)
    simpa using congrArg OrderDual.toDual this
  ne_nil _ := by simp [digitCode]
  prefix_free a b h := by
    have := digitCode_prefix h
    simpa using congrArg OrderDual.toDual this

/-- Reversed lexicographic code of addresses: digit codes, then the largest terminator `2`. -/
def dualAddressAux : List ℕ → List ℕ
  | [] => [2]
  | x :: xs => digitCode x ++ dualAddressAux xs

theorem dualAddressAux_lt_iff : ∀ a b, dualAddressAux a < dualAddressAux b ↔ b < a
  | [], [] => ⟨fun h => absurd h (lt_irrefl _), fun h => absurd h (lt_irrefl _)⟩
  | [], y :: ys => ⟨fun h => absurd (lt_trans h (digitCode_head_le y _)) (lt_irrefl _),
      fun h => absurd h (List.not_lt_nil _)⟩
  | x :: xs, [] => ⟨fun _ => List.nil_lt_cons _ _, fun _ => digitCode_head_le x _⟩
  | x :: xs, y :: ys => by
      show digitPrefixCode.code (OrderDual.toDual x) ++ dualAddressAux xs <
        digitPrefixCode.code (OrderDual.toDual y) ++ dualAddressAux ys ↔ _
      rw [digitPrefixCode.append_lt_iff, dualAddressAux_lt_iff xs ys, list_cons_lt_cons_iff]
      constructor
      · rintro (h | ⟨h, h'⟩)
        · exact Or.inl h
        · exact Or.inr ⟨(congrArg OrderDual.ofDual h).symm, h'⟩
      · rintro (h | ⟨h, h'⟩)
        · exact Or.inl h
        · exact Or.inr ⟨congrArg OrderDual.toDual h.symm, h'⟩

theorem dualAddressAux_prefix : ∀ {a b}, dualAddressAux a <+: dualAddressAux b → a = b
  | [], [], _ => rfl
  | [], y :: ys, h => by
      cases y <;> simp [dualAddressAux, digitCode, List.replicate_succ, List.cons_prefix_cons] at h
  | x :: xs, [], h => by
      cases x <;> simp [dualAddressAux, digitCode, List.replicate_succ, List.cons_prefix_cons] at h
  | x :: xs, y :: ys, h => by
      have h' : digitPrefixCode.code (OrderDual.toDual x) ++ dualAddressAux xs <+:
          digitPrefixCode.code (OrderDual.toDual y) ++ dualAddressAux ys := h
      obtain ⟨hxy, hrest⟩ := digitPrefixCode.append_prefix h'
      have hx : x = y := by simpa using congrArg OrderDual.ofDual hxy
      rw [hx, dualAddressAux_prefix hrest]

/-- The prefix code of reversed addresses. -/
def dualAddressCode : PrefixCode (List ℕ)ᵒᵈ where
  code d := dualAddressAux (OrderDual.ofDual d)
  lt_iff a b := dualAddressAux_lt_iff _ _
  injective a b h := by
    have := dualAddressAux_prefix (prefix_of_eq h)
    simpa using congrArg OrderDual.toDual this
  ne_nil d := by cases h : OrderDual.ofDual d <;> simp [dualAddressAux, digitCode]
  prefix_free a b h := by
    have := dualAddressAux_prefix h
    simpa using congrArg OrderDual.toDual this

/-- Absence below every present value. -/
def withBotCode {β : Type*} [LinearOrder β] (c : LexCode β) : LexCode (WithBot β) where
  code
    | none => [0]
    | some value => 1 :: c.code value
  lt_iff a b := by
    cases a <;> cases b
    · exact ⟨fun h => absurd h (lt_irrefl _), fun h => absurd h (lt_irrefl _)⟩
    · exact ⟨fun _ => WithBot.bot_lt_coe _, fun _ => List.Lex.rel (by decide)⟩
    · exact ⟨fun h => by rcases lex_cons_iff'.1 h with h | ⟨h, _⟩ <;> omega,
        fun h => absurd h (not_lt_bot)⟩
    · rename_i x y
      rw [lex_cons_iff', WithBot.coe_lt_coe, ← c.lt_iff]
      constructor
      · rintro (h | ⟨_, h⟩)
        · exact absurd h (lt_irrefl _)
        · exact h
      · exact fun h => Or.inr ⟨rfl, h⟩
  injective a b h := by
    cases a <;> cases b <;> simp_all
    exact c.injective h

/-- An order-embedding code of the integers. -/
def intCode : LexCode ℤ where
  code z := if 0 ≤ z then [1, z.toNat] else 0 :: digitCode ((-z).toNat - 1)
  lt_iff a b := by
    by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b <;> simp only [ha, hb, if_true, if_false]
    · rw [lex_cons_iff', show ([a.toNat] : List ℕ) < [b.toNat] ↔ a.toNat < b.toNat from
        List.lex_singleton_iff _ _]
      omega
    · constructor
      · intro h; rcases lex_cons_iff'.1 h with h | ⟨h, _⟩ <;> omega
      · intro h; omega
    · exact ⟨fun _ => by omega, fun _ => List.Lex.rel (by decide)⟩
    · rw [lex_cons_iff', digitCode_lt_iff]
      omega
  injective a b h := by
    by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b <;> simp only [ha, hb, if_true, if_false] at h
    · simp at h; omega
    · simp at h
    · simp at h
    · simp only [List.cons.injEq, true_and] at h
      have := digitCode_prefix (prefix_of_eq h)
      omega

/-- The prefix code of encoded stereochemical observations. -/
def stereoCodePrefix : PrefixCode StereoCode :=
  listCode (listCode (pairCode dualAddressCode natCode))

/-- The order-embedding code of optional encoded stereochemical observations. -/
def stereoValueCode : LexCode (WithBot StereoCode) :=
  withBotCode stereoCodePrefix.toLexCode

namespace StereochemicalProblemData

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
  (data : StereochemicalProblemData Atom Unit)
  (hfaithful : data.toConstitutionalProblemData.ExpansionsFaithful)
  (hexpansion : ∀ unit ligand, ∃ graph, data.admissibleExpansion unit ligand graph)

/-- The chosen admissible expansion of a ligand. -/
abbrev chosenGraph (unit : Unit) (ligand : Fin 4) : RootedDigraph Atom :=
  data.toConstitutionalProblemData.chosenExpansion hexpansion unit ligand

theorem chosenGraph_admissible (unit : Unit) (ligand : Fin 4) :
    data.admissibleExpansion unit ligand (data.chosenGraph hexpansion unit ligand) :=
  data.toConstitutionalProblemData.chosenExpansion_admissible hexpansion unit ligand

include hfaithful in
theorem chosenGraph_has_ordinary (descriptorMap : DescriptorMap Unit) (unit : Unit)
    (ligand : Fin 4) :
    ∃ addressing : (data.chosenGraph hexpansion unit ligand).Addressing,
      OrdinaryCanonicalAddressing data.molecule
        (data.evidence descriptorMap unit (data.chosenGraph hexpansion unit ligand)) addressing := by
  obtain ⟨_, base, _⟩ := (hfaithful _ _ _ (data.chosenGraph_admissible hexpansion unit ligand)).1
  exact exists_ordinaryCanonicalAddressing data.molecule _ base

/-- The chosen ordinary canonical addressing of the chosen expansion. -/
def chosenOrdinaryAddressing (descriptorMap : DescriptorMap Unit) (unit : Unit) (ligand : Fin 4) :
    (data.chosenGraph hexpansion unit ligand).Addressing :=
  Classical.choose (data.chosenGraph_has_ordinary hfaithful hexpansion descriptorMap unit ligand)

theorem chosenOrdinaryAddressing_spec (descriptorMap : DescriptorMap Unit) (unit : Unit)
    (ligand : Fin 4) :
    OrdinaryCanonicalAddressing data.molecule
      (data.evidence descriptorMap unit (data.chosenGraph hexpansion unit ligand))
      (data.chosenOrdinaryAddressing hfaithful hexpansion descriptorMap unit ligand) :=
  Classical.choose_spec (data.chosenGraph_has_ordinary hfaithful hexpansion descriptorMap unit ligand)

/-- The constitutional observation field of a ligand. -/
def constitutionalField (descriptorMap : DescriptorMap Unit) (unit : Unit)
    (rule : ConstitutionalRule) (ligand : Fin 4) : List ℕ → ℤ :=
  observationField data.molecule (data.chosenOrdinaryAddressing hfaithful hexpansion descriptorMap
    unit ligand) rule

/-- The stereochemical observation field of a ligand. -/
def stereochemicalField (descriptorMap : DescriptorMap Unit) (unit : Unit)
    (rule : StereochemicalRule) (ligand : Fin 4) : List ℕ → WithBot StereoCode :=
  fun position => stereoValue rule (addressEvidence
    (data.chosenOrdinaryAddressing hfaithful hexpansion descriptorMap unit ligand)
    (data.evidence descriptorMap unit (data.chosenGraph hexpansion unit ligand)) position)

theorem constitutional_outcomeOnGraphs_iff (descriptorMap : DescriptorMap Unit) (unit : Unit)
    (rule : ConstitutionalRule) {left right : RootedDigraph Atom} {outcome : Ordering} :
    data.withOrdinaryCanonicalAddressing.toProblem.OutcomeOnGraphs descriptorMap
        rule.toSequenceRule unit left right outcome ↔
      data.withOrdinaryCanonicalAddressing.toConstitutionalProblemData.CanonicalOutcome
        descriptorMap unit rule left right outcome := by
  cases rule <;> rfl

/-- **Constitutional rule outcomes of the eight-rule family are first-difference comparisons.** -/
theorem ordinary_constitutional_ruleOutcome_iff (descriptorMap : DescriptorMap Unit)
    (unit : Unit) (rule : ConstitutionalRule) (left right : Fin 4) (outcome : Ordering) :
    data.withOrdinaryCanonicalAddressing.toProblem.RuleOutcome descriptorMap rule.toSequenceRule
        unit left right outcome ↔
      LexOutcome (data.constitutionalField hfaithful hexpansion descriptorMap unit rule left)
        (data.constitutionalField hfaithful hexpansion descriptorMap unit rule right) outcome := by
  have hleft₀ := data.chosenGraph_admissible hexpansion unit left
  have hright₀ := data.chosenGraph_admissible hexpansion unit right
  have hla := data.chosenOrdinaryAddressing_spec hfaithful hexpansion descriptorMap unit left
  have hra := data.chosenOrdinaryAddressing_spec hfaithful hexpansion descriptorMap unit right
  constructor
  · intro h
    have hcanonical := (data.constitutional_outcomeOnGraphs_iff descriptorMap unit rule).1
      (h _ _ hleft₀ hright₀)
    exact (hierarchyOutcome_iff_lexOutcome data.molecule _ _ rule outcome).1
      (hcanonical.2.2 _ _ hla hra)
  · intro hlex graphLeft graphRight hgl hgr
    have hchosen : data.withOrdinaryCanonicalAddressing.toConstitutionalProblemData.CanonicalOutcome
        descriptorMap unit rule (data.chosenGraph hexpansion unit left)
        (data.chosenGraph hexpansion unit right) outcome := by
      refine ⟨⟨_, hla⟩, ⟨_, hra⟩, fun la ra hla' hra' => ?_⟩
      exact (hierarchyOutcome_canonical_iff data.molecule
        (ordinaryCanonical_canonical _ _ hla) (ordinaryCanonical_canonical _ _ hla')
        (ordinaryCanonical_canonical _ _ hra) (ordinaryCanonical_canonical _ _ hra')
        rule outcome).1 ((hierarchyOutcome_iff_lexOutcome data.molecule _ _ rule outcome).2 hlex)
    obtain ⟨leftIso⟩ := faithfulExactExpansion_unique_up_to_iso _ _ _ _ _
      (hfaithful _ _ _ hleft₀) (hfaithful _ _ _ hgl)
    obtain ⟨rightIso⟩ := faithfulExactExpansion_unique_up_to_iso _ _ _ _ _
      (hfaithful _ _ _ hright₀) (hfaithful _ _ _ hgr)
    rw [data.constitutional_outcomeOnGraphs_iff descriptorMap unit rule]
    exact (data.withOrdinaryCanonicalAddressing.toConstitutionalProblemData.canonicalOutcome_transport_iff
      descriptorMap unit rule leftIso rightIso outcome).1 hchosen

/-- **Stereochemical rule outcomes are first-difference comparisons of encoded fields.** -/
theorem ordinary_stereochemical_ruleOutcome_iff (descriptorMap : DescriptorMap Unit)
    (unit : Unit) (rule : StereochemicalRule) (left right : Fin 4) (outcome : Ordering) :
    data.withOrdinaryCanonicalAddressing.toProblem.RuleOutcome descriptorMap rule.toSequenceRule
        unit left right outcome ↔
      LexOutcome (data.stereochemicalField hfaithful hexpansion descriptorMap unit rule left)
        (data.stereochemicalField hfaithful hexpansion descriptorMap unit rule right) outcome := by
  have hleft₀ := data.chosenGraph_admissible hexpansion unit left
  have hright₀ := data.chosenGraph_admissible hexpansion unit right
  have hla := data.chosenOrdinaryAddressing_spec hfaithful hexpansion descriptorMap unit left
  have hra := data.chosenOrdinaryAddressing_spec hfaithful hexpansion descriptorMap unit right
  constructor
  · intro h
    have hcanonical := (data.withOrdinaryCanonicalAddressing.toProblem_stereochemicalRule
      descriptorMap unit rule _ _ outcome).1 (h _ _ hleft₀ hright₀)
    exact (stereochemicalHierarchyOutcome_iff_lexOutcome rule _ _ _ _ outcome).1
      (hcanonical.2.2 _ _ hla hra)
  · intro hlex graphLeft graphRight hgl hgr
    have hchosen : data.withOrdinaryCanonicalAddressing.CanonicalOutcome descriptorMap unit rule
        (data.chosenGraph hexpansion unit left) (data.chosenGraph hexpansion unit right)
        outcome := by
      refine ⟨⟨_, hla⟩, ⟨_, hra⟩, fun la ra hla' hra' => ?_⟩
      exact (stereochemicalHierarchyOutcome_ordinaryCanonical_iff data.molecule rule hla hla'
        hra hra' outcome).1 ((stereochemicalHierarchyOutcome_iff_lexOutcome rule _ _ _ _
          outcome).2 hlex)
    obtain ⟨leftIso⟩ := faithfulExactExpansion_unique_up_to_iso _ _ _ _ _
      (hfaithful _ _ _ hleft₀) (hfaithful _ _ _ hgl)
    obtain ⟨rightIso⟩ := faithfulExactExpansion_unique_up_to_iso _ _ _ _ _
      (hfaithful _ _ _ hright₀) (hfaithful _ _ _ hgr)
    rw [data.withOrdinaryCanonicalAddressing.toProblem_stereochemicalRule]
    exact (data.withOrdinaryCanonicalAddressing.canonicalOutcome_transport_iff descriptorMap unit
      rule leftIso rightIso outcome).1 hchosen

theorem constitutionalField_total (descriptorMap : DescriptorMap Unit) (unit : Unit)
    (rule : ConstitutionalRule) (left right : Fin 4) :
    ∃ outcome, LexOutcome (data.constitutionalField hfaithful hexpansion descriptorMap unit rule left)
      (data.constitutionalField hfaithful hexpansion descriptorMap unit rule right) outcome := by
  obtain ⟨outcome, houtcome⟩ := constitutionalHierarchyOutcome_total data.molecule rule
    _ (data.chosenOrdinaryAddressing hfaithful hexpansion descriptorMap unit left)
    _ (data.chosenOrdinaryAddressing hfaithful hexpansion descriptorMap unit right)
  exact ⟨outcome, (hierarchyOutcome_iff_lexOutcome data.molecule _ _ rule outcome).1 houtcome⟩

theorem stereochemicalField_total (descriptorMap : DescriptorMap Unit) (unit : Unit)
    (rule : StereochemicalRule) (left right : Fin 4) :
    ∃ outcome, LexOutcome (data.stereochemicalField hfaithful hexpansion descriptorMap unit rule left)
      (data.stereochemicalField hfaithful hexpansion descriptorMap unit rule right) outcome := by
  obtain ⟨outcome, houtcome⟩ := stereochemicalHierarchyOutcome_total_of_compatible rule
    _ (data.chosenOrdinaryAddressing hfaithful hexpansion descriptorMap unit left) _
    _ (data.chosenOrdinaryAddressing hfaithful hexpansion descriptorMap unit right) _
    (fun _ _ _ _ _ => by cases rule <;> trivial)
  exact ⟨outcome, (stereochemicalHierarchyOutcome_iff_lexOutcome rule _ _ _ _ outcome).1 houtcome⟩

include hfaithful hexpansion in
/-- **Unary first-difference characterization of every ordinary rule.** -/
theorem ordinary_ruleOutcome_lex (descriptorMap : DescriptorMap Unit) (rule : SequenceRule)
    (hrule : rule ≠ SequenceRule.rule6ReferencePromotion) (unit : Unit) :
    ∃ (V : Type) (_ : LinearOrder V) (field : Fin 4 → List ℕ → V),
      (∀ left right outcome,
        data.withOrdinaryCanonicalAddressing.toProblem.RuleOutcome descriptorMap rule unit left
            right outcome ↔ LexOutcome (field left) (field right) outcome) ∧
      ∀ left right, ∃ outcome, LexOutcome (field left) (field right) outcome := by
  cases rule
  · exact ⟨ℤ, inferInstance, data.constitutionalField hfaithful hexpansion descriptorMap unit
      .rule1aAtomicNumber, data.ordinary_constitutional_ruleOutcome_iff hfaithful hexpansion
      descriptorMap unit .rule1aAtomicNumber, data.constitutionalField_total hfaithful hexpansion
      descriptorMap unit .rule1aAtomicNumber⟩
  · exact ⟨ℤ, inferInstance, data.constitutionalField hfaithful hexpansion descriptorMap unit
      .rule1bDuplicateNodeProximity, data.ordinary_constitutional_ruleOutcome_iff hfaithful
      hexpansion descriptorMap unit .rule1bDuplicateNodeProximity, data.constitutionalField_total
      hfaithful hexpansion descriptorMap unit .rule1bDuplicateNodeProximity⟩
  · exact ⟨ℤ, inferInstance, data.constitutionalField hfaithful hexpansion descriptorMap unit
      .rule2AtomicMass, data.ordinary_constitutional_ruleOutcome_iff hfaithful hexpansion
      descriptorMap unit .rule2AtomicMass, data.constitutionalField_total hfaithful hexpansion
      descriptorMap unit .rule2AtomicMass⟩
  · exact ⟨WithBot StereoCode, inferInstance, data.stereochemicalField hfaithful hexpansion
      descriptorMap unit .rule3DoubleBondGeometry, data.ordinary_stereochemical_ruleOutcome_iff
      hfaithful hexpansion descriptorMap unit .rule3DoubleBondGeometry,
      data.stereochemicalField_total hfaithful hexpansion descriptorMap unit
        .rule3DoubleBondGeometry⟩
  · exact ⟨WithBot StereoCode, inferInstance, data.stereochemicalField hfaithful hexpansion
      descriptorMap unit .rule4aStereogenicUnitKind, data.ordinary_stereochemical_ruleOutcome_iff
      hfaithful hexpansion descriptorMap unit .rule4aStereogenicUnitKind,
      data.stereochemicalField_total hfaithful hexpansion descriptorMap unit
        .rule4aStereogenicUnitKind⟩
  · exact ⟨WithBot StereoCode, inferInstance, data.stereochemicalField hfaithful hexpansion
      descriptorMap unit .rule4bLikeUnlikeDescriptorPairs,
      data.ordinary_stereochemical_ruleOutcome_iff hfaithful hexpansion descriptorMap unit
        .rule4bLikeUnlikeDescriptorPairs,
      data.stereochemicalField_total hfaithful hexpansion descriptorMap unit
        .rule4bLikeUnlikeDescriptorPairs⟩
  · exact ⟨WithBot StereoCode, inferInstance, data.stereochemicalField hfaithful hexpansion
      descriptorMap unit .rule4cPseudoasymmetricDescriptor,
      data.ordinary_stereochemical_ruleOutcome_iff hfaithful hexpansion descriptorMap unit
        .rule4cPseudoasymmetricDescriptor,
      data.stereochemicalField_total hfaithful hexpansion descriptorMap unit
        .rule4cPseudoasymmetricDescriptor⟩
  · exact ⟨WithBot StereoCode, inferInstance, data.stereochemicalField hfaithful hexpansion
      descriptorMap unit .rule5EnantiomorphicDescriptor,
      data.ordinary_stereochemical_ruleOutcome_iff hfaithful hexpansion descriptorMap unit
        .rule5EnantiomorphicDescriptor,
      data.stereochemicalField_total hfaithful hexpansion descriptorMap unit
        .rule5EnantiomorphicDescriptor⟩
  · exact absurd rfl hrule

include hfaithful hexpansion in
/-- **Independent order laws for all eight ordinary rules.** -/
theorem withOrdinaryCanonicalAddressing_ordinaryOrderLaws (descriptorMap : DescriptorMap Unit) :
    OrdinaryRuleOutcomeOrderLaws data.withOrdinaryCanonicalAddressing.toProblem descriptorMap := by
  have h := data.ordinary_ruleOutcome_lex hfaithful hexpansion descriptorMap
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rule hrule unit left right first second h₁ h₂
    obtain ⟨V, _, field, hchar, _⟩ := h rule hrule unit
    exact LexOutcome.functional ((hchar left right first).1 h₁) ((hchar left right second).1 h₂)
  · intro rule hrule unit left right
    obtain ⟨V, _, field, hchar, htotal⟩ := h rule hrule unit
    obtain ⟨outcome, houtcome⟩ := htotal left right
    exact ⟨outcome, (hchar left right outcome).2 houtcome⟩
  · intro rule hrule unit ligand
    obtain ⟨V, _, field, hchar, _⟩ := h rule hrule unit
    exact (hchar ligand ligand _).2 (LexOutcome.eq_refl _)
  · intro rule hrule unit left right h₁
    obtain ⟨V, _, field, hchar, _⟩ := h rule hrule unit
    exact (hchar right left _).2 (LexOutcome.eq_symm ((hchar left right _).1 h₁))
  · intro rule hrule unit first second third h₁ h₂
    obtain ⟨V, _, field, hchar, _⟩ := h rule hrule unit
    exact (hchar first third _).2
      (LexOutcome.eq_trans ((hchar first second _).1 h₁) ((hchar second third _).1 h₂))
  · intro rule hrule unit first second third h₁ h₂
    obtain ⟨V, _, field, hchar, _⟩ := h rule hrule unit
    exact (hchar first third _).2
      (LexOutcome.gt_trans ((hchar first second _).1 h₁) ((hchar second third _).1 h₂))
  · intro rule hrule unit first second third h₁ h₂
    obtain ⟨V, _, field, hchar, _⟩ := h rule hrule unit
    exact (hchar first third _).2
      (LexOutcome.gt_eq_trans ((hchar first second _).1 h₁) ((hchar second third _).1 h₂))
  · intro rule hrule unit first second third h₁ h₂
    obtain ⟨V, _, field, hchar, _⟩ := h rule hrule unit
    exact (hchar first third _).2
      (LexOutcome.eq_gt_trans ((hchar first second _).1 h₁) ((hchar second third _).1 h₂))
  · intro rule hrule unit left right h₁
    obtain ⟨V, _, field, hchar, _⟩ := h rule hrule unit
    exact (hchar right left _).2 (LexOutcome.reverse_lt ((hchar left right _).1 h₁))

include hfaithful hexpansion in
/-- **Ordinary declarative priority is a total preorder.**  For every molecule with faithful
existing expansions and naturally supplied evidence, first-decisive priority through Rule 5 of the
eight-rule canonical semantics is a total preorder. -/
theorem withOrdinaryCanonicalAddressing_ordinaryPriority (descriptorMap : DescriptorMap Unit) :
    data.withOrdinaryCanonicalAddressing.toProblem.OrdinaryPriorityIsTotalPreorder descriptorMap :=
  (data.withOrdinaryCanonicalAddressing_ordinaryOrderLaws hfaithful hexpansion
    descriptorMap).ordinaryPriorityIsTotalPreorder

end StereochemicalProblemData

/-! ## Sampling observation fields on a finite address window -/

/-- The hierarchy address order, by length and then lexicographically. -/
theorem hierarchyAddressBefore_iff (earlier later : List ℕ) :
    HierarchyAddressBefore earlier later ↔
      earlier.length < later.length ∨ (earlier.length = later.length ∧ earlier < later) := by
  unfold HierarchyAddressBefore HierarchyAddressKey
  exact lex_cons_iff'

/-- The addresses with digits below `W` and length at most `D`, in hierarchy address order. -/
def windowPaths (W D : ℕ) : List (List ℕ) :=
  (List.range (D + 1)).flatMap fun k => (List.range (W ^ k)).map (Certificate.CanonicalSphereKey.pathOf W k)

theorem mem_windowPaths {W D : ℕ} {path : List ℕ} :
    path ∈ windowPaths W D ↔ (∀ digit ∈ path, digit < W) ∧ path.length ≤ D := by
  unfold windowPaths
  simp only [List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨k, hk, slot, hslot, rfl⟩
    exact ⟨Certificate.CanonicalSphereKey.pathOf_digits hslot,
      by rw [Certificate.CanonicalSphereKey.pathOf_length]; omega⟩
  · rintro ⟨hdigits, hlength⟩
    exact ⟨path.length, by omega, Certificate.CanonicalSphereKey.slotOf W path,
      Certificate.CanonicalSphereKey.slotOf_lt hdigits,
      Certificate.CanonicalSphereKey.pathOf_slotOf hdigits⟩

theorem windowPaths_pairwise (W D : ℕ) : (windowPaths W D).Pairwise HierarchyAddressBefore := by
  unfold windowPaths
  rw [List.pairwise_flatMap]
  constructor
  · intro k _
    rw [List.pairwise_map]
    refine (List.pairwise_lt_range).imp_of_mem ?_
    intro s₁ s₂ hs₁ hs₂ hlt
    simp only [List.mem_range] at hs₁ hs₂
    rw [hierarchyAddressBefore_iff, Certificate.CanonicalSphereKey.pathOf_length,
      Certificate.CanonicalSphereKey.pathOf_length]
    refine Or.inr ⟨rfl, ?_⟩
    apply (Certificate.CanonicalSphereKey.slotOf_lt_slotOf_iff
      (by rw [Certificate.CanonicalSphereKey.pathOf_length,
        Certificate.CanonicalSphereKey.pathOf_length])
      (Certificate.CanonicalSphereKey.pathOf_digits hs₁)
      (Certificate.CanonicalSphereKey.pathOf_digits hs₂)).1
    rw [Certificate.CanonicalSphereKey.slotOf_pathOf hs₁,
      Certificate.CanonicalSphereKey.slotOf_pathOf hs₂]
    exact hlt
  · refine (List.pairwise_lt_range).imp ?_
    intro k₁ k₂ hlt x hx y hy
    simp only [List.mem_map, List.mem_range] at hx hy
    obtain ⟨_, _, rfl⟩ := hx
    obtain ⟨_, _, rfl⟩ := hy
    rw [hierarchyAddressBefore_iff, Certificate.CanonicalSphereKey.pathOf_length,
      Certificate.CanonicalSphereKey.pathOf_length]
    exact Or.inl hlt

/-- **Sampling theorem.**  If two fields agree outside a strictly increasing list of addresses, their
first-difference outcome is the lexicographic outcome of their samples on that list. -/
theorem lexOutcome_iff_samples {V : Type*} [LinearOrder V] {positions : List (List ℕ)}
    (hsorted : positions.Pairwise HierarchyAddressBefore) {left right : List ℕ → V}
    (houtside : ∀ position, position ∉ positions → left position = right position)
    (outcome : Ordering) :
    LexOutcome left right outcome ↔
      OrderedKeyOutcome (positions.map left) (positions.map right) outcome := by
  have hforward : ∀ o, LexOutcome left right o →
      OrderedKeyOutcome (positions.map left) (positions.map right) o := by
    have hlen : (positions.map left).length = (positions.map right).length := by simp
    have hwitness : ∀ (p : List ℕ), left p ≠ right p →
        (∀ e, HierarchyAddressBefore e p → left e = right e) →
        ∃ i, ∃ (hi : i < positions.length), positions[i] = p ∧
          ∀ j (hj : j < i), left positions[j] = right positions[j] := by
      intro p hne hbefore
      have hmem : p ∈ positions := by
        by_contra hnot
        exact hne (houtside p hnot)
      obtain ⟨i, hi, hp⟩ := List.getElem_of_mem hmem
      refine ⟨i, hi, hp, fun j hj => hbefore _ ?_⟩
      rw [← hp]
      exact List.pairwise_iff_getElem.1 hsorted j i (by omega) hi hj
    intro o h
    cases o with
    | eq =>
        apply OrderedKeyOutcome.eq
        apply List.map_congr_left
        intro p _
        exact (LexOutcome.eq_iff.1 h) p
    | gt =>
        obtain ⟨p, hlt, hbefore⟩ := LexOutcome.gt_iff.1 h
        obtain ⟨i, hi, hp, hprefix⟩ := hwitness p (ne_of_gt hlt) hbefore
        apply OrderedKeyOutcome.gt
        apply (Certificate.CanonicalSphereKey.list_lt_iff_first_difference hlen.symm).2
        refine ⟨i, by simpa using hi, by simpa using hi, fun j hj => ?_, ?_⟩
        · simp only [List.getElem_map]
          exact (hprefix j hj).symm
        · simp only [List.getElem_map, hp]
          exact hlt
    | lt =>
        obtain ⟨p, hlt, hbefore⟩ := LexOutcome.lt_iff.1 h
        obtain ⟨i, hi, hp, hprefix⟩ := hwitness p (ne_of_lt hlt) hbefore
        apply OrderedKeyOutcome.lt
        apply (Certificate.CanonicalSphereKey.list_lt_iff_first_difference hlen).2
        refine ⟨i, by simpa using hi, by simpa using hi, fun j hj => ?_, ?_⟩
        · simp only [List.getElem_map]
          exact hprefix j hj
        · simp only [List.getElem_map, hp]
          exact hlt
  constructor
  · exact hforward outcome
  · intro h
    obtain ⟨other, hother⟩ := FirstDifferenceOutcome.total_of_finite_support
      (observation := fun position outcome => compare (left position) (right position) = outcome)
      (fun position => ⟨_, rfl⟩) positions.toFinset (fun position hposition => by
        show compare (left position) (right position) = Ordering.eq
        rw [houtside position (by simpa using hposition)]
        exact compare_eq_iff_eq.2 rfl)
    have := OrderedKeyOutcome.functional h (hforward other hother)
    rwa [this]

/-- Codes lift to lists of values. -/
theorem LexCode.map_orderedKeyOutcome_iff {β : Type*} [LinearOrder β] (c : LexCode β)
    (l m : List β) (outcome : Ordering) :
    OrderedKeyOutcome (l.map c.code) (m.map c.code) outcome ↔ OrderedKeyOutcome l m outcome := by
  have hlt : ∀ l m : List β, l.map c.code < m.map c.code ↔ l < m := by
    intro l m
    induction l generalizing m with
    | nil =>
        cases m with
        | nil => exact ⟨fun h => absurd h (lt_irrefl _), fun h => absurd h (lt_irrefl _)⟩
        | cons b bs => exact ⟨fun _ => List.nil_lt_cons _ _, fun _ => List.nil_lt_cons _ _⟩
    | cons a as ih =>
        cases m with
        | nil =>
            exact ⟨fun h => absurd h (List.not_lt_nil _), fun h => absurd h (List.not_lt_nil _)⟩
        | cons b bs =>
            simp only [List.map_cons]
            rw [list_cons_lt_cons_iff, list_cons_lt_cons_iff, c.lt_iff, ih bs]
            exact or_congr Iff.rfl (and_congr ⟨fun h => c.injective h, fun h => h ▸ rfl⟩ Iff.rfl)
  have heq : ∀ l m : List β, l.map c.code = m.map c.code ↔ l = m :=
    fun l m => ⟨fun h => List.map_injective_iff.2 c.injective h, fun h => h ▸ rfl⟩
  rcases lt_trichotomy l m with h | h | h
  · rw [orderedKeyOutcome_of_lt h, orderedKeyOutcome_of_lt ((hlt l m).2 h)]
  · rw [orderedKeyOutcome_of_eq h, orderedKeyOutcome_of_eq ((heq l m).2 h)]
  · rw [orderedKeyOutcome_of_gt h, orderedKeyOutcome_of_gt ((hlt m l).2 h)]

/-! ## The ordinary unary key model -/

theorem addressLabel_of_unoccupied {Atom : Type u} {graph : RootedDigraph Atom}
    (addressing : graph.Addressing) {position : List ℕ}
    (h : ∀ node, addressing.address node ≠ position) :
    addressLabel addressing position = none := by
  unfold addressLabel
  rw [dif_neg (by simpa using h)]

theorem addressEvidence_of_unoccupied {Atom : Type u} {graph : RootedDigraph Atom}
    (addressing : graph.Addressing) (evidence : StereochemicalEvidence graph)
    {position : List ℕ} (h : ∀ node, addressing.address node ≠ position) :
    addressEvidence addressing evidence position = none := by
  unfold addressEvidence
  rw [dif_neg (by simpa using h)]

namespace StereochemicalProblemData

variable {Atom Unit : Type u} [Fintype Atom] [DecidableEq Atom]
  (data : StereochemicalProblemData Atom Unit)
  (hfaithful : data.toConstitutionalProblemData.ExpansionsFaithful)
  (hexpansion : ∀ unit ligand, ∃ graph, data.admissibleExpansion unit ligand graph)

/-- A unit-level window bounding the four chosen expansions. -/
def unitWidth (unit : Unit) : ℕ :=
  Finset.univ.sup fun ligand : Fin 4 => (data.chosenGraph hexpansion unit ligand).width

def unitHeight (unit : Unit) : ℕ :=
  Finset.univ.sup fun ligand : Fin 4 => (data.chosenGraph hexpansion unit ligand).height

theorem unoccupied_outside_window (descriptorMap : DescriptorMap Unit) (unit : Unit)
    (ligand : Fin 4) {position : List ℕ}
    (hout : position ∉ windowPaths (data.unitWidth hexpansion unit)
      (data.unitHeight hexpansion unit)) :
    ∀ node, (data.chosenOrdinaryAddressing hfaithful hexpansion descriptorMap unit ligand).address
      node ≠ position := by
  intro node hnode
  apply hout
  have hspec := data.chosenOrdinaryAddressing_spec hfaithful hexpansion descriptorMap unit ligand
  have hW : (data.chosenGraph hexpansion unit ligand).width ≤ data.unitWidth hexpansion unit :=
    Finset.le_sup (f := fun ligand : Fin 4 => (data.chosenGraph hexpansion unit ligand).width)
      (Finset.mem_univ ligand)
  have hD : (data.chosenGraph hexpansion unit ligand).height ≤ data.unitHeight hexpansion unit :=
    Finset.le_sup (f := fun ligand : Fin 4 => (data.chosenGraph hexpansion unit ligand).height)
      (Finset.mem_univ ligand)
  refine mem_windowPaths.2 ⟨fun digit hdigit => lt_of_lt_of_le
    (address_slots_lt_width hspec.1 node digit (hnode ▸ hdigit)) hW, ?_⟩
  exact hnode ▸ le_trans (address_length_le_height _ node) hD

/-- The coded constitutional sample key of a ligand. -/
def constitutionalSampleKey (descriptorMap : DescriptorMap Unit) (unit : Unit)
    (rule : ConstitutionalRule) (ligand : Fin 4) : RuleKey :=
  ((windowPaths (data.unitWidth hexpansion unit) (data.unitHeight hexpansion unit)).map
    (data.constitutionalField hfaithful hexpansion descriptorMap unit rule ligand)).map intCode.code

/-- The coded stereochemical sample key of a ligand. -/
def stereochemicalSampleKey (descriptorMap : DescriptorMap Unit) (unit : Unit)
    (rule : StereochemicalRule) (ligand : Fin 4) : RuleKey :=
  ((windowPaths (data.unitWidth hexpansion unit) (data.unitHeight hexpansion unit)).map
    (data.stereochemicalField hfaithful hexpansion descriptorMap unit rule ligand)).map
    stereoValueCode.code

/-- The unary key of every sequence rule; Rule 6 is outside the model. -/
def ordinarySampleKey (descriptorMap : DescriptorMap Unit) (unit : Unit) :
    SequenceRule → Fin 4 → RuleKey
  | .rule1aAtomicNumber =>
      data.constitutionalSampleKey hfaithful hexpansion descriptorMap unit .rule1aAtomicNumber
  | .rule1bDuplicateNodeProximity =>
      data.constitutionalSampleKey hfaithful hexpansion descriptorMap unit
        .rule1bDuplicateNodeProximity
  | .rule2AtomicMass =>
      data.constitutionalSampleKey hfaithful hexpansion descriptorMap unit .rule2AtomicMass
  | .rule3DoubleBondGeometry =>
      data.stereochemicalSampleKey hfaithful hexpansion descriptorMap unit .rule3DoubleBondGeometry
  | .rule4aStereogenicUnitKind =>
      data.stereochemicalSampleKey hfaithful hexpansion descriptorMap unit
        .rule4aStereogenicUnitKind
  | .rule4bLikeUnlikeDescriptorPairs =>
      data.stereochemicalSampleKey hfaithful hexpansion descriptorMap unit
        .rule4bLikeUnlikeDescriptorPairs
  | .rule4cPseudoasymmetricDescriptor =>
      data.stereochemicalSampleKey hfaithful hexpansion descriptorMap unit
        .rule4cPseudoasymmetricDescriptor
  | .rule5EnantiomorphicDescriptor =>
      data.stereochemicalSampleKey hfaithful hexpansion descriptorMap unit
        .rule5EnantiomorphicDescriptor
  | .rule6ReferencePromotion => fun _ => []

theorem constitutionalSampleKey_characterizes (descriptorMap : DescriptorMap Unit) (unit : Unit)
    (rule : ConstitutionalRule) (left right : Fin 4) (outcome : Ordering) :
    data.withOrdinaryCanonicalAddressing.toProblem.RuleOutcome descriptorMap rule.toSequenceRule
        unit left right outcome ↔
      OrderedKeyOutcome (data.constitutionalSampleKey hfaithful hexpansion descriptorMap unit rule left)
        (data.constitutionalSampleKey hfaithful hexpansion descriptorMap unit rule right) outcome := by
  rw [data.ordinary_constitutional_ruleOutcome_iff hfaithful hexpansion,
    lexOutcome_iff_samples (windowPaths_pairwise _ _), constitutionalSampleKey,
    constitutionalSampleKey, intCode.map_orderedKeyOutcome_iff]
  intro position hposition
  unfold constitutionalField observationField
  rw [addressLabel_of_unoccupied _ (data.unoccupied_outside_window hfaithful hexpansion
      descriptorMap unit left hposition),
    addressLabel_of_unoccupied _ (data.unoccupied_outside_window hfaithful hexpansion
      descriptorMap unit right hposition)]

theorem stereochemicalSampleKey_characterizes (descriptorMap : DescriptorMap Unit) (unit : Unit)
    (rule : StereochemicalRule) (left right : Fin 4) (outcome : Ordering) :
    data.withOrdinaryCanonicalAddressing.toProblem.RuleOutcome descriptorMap rule.toSequenceRule
        unit left right outcome ↔
      OrderedKeyOutcome (data.stereochemicalSampleKey hfaithful hexpansion descriptorMap unit rule left)
        (data.stereochemicalSampleKey hfaithful hexpansion descriptorMap unit rule right) outcome := by
  rw [data.ordinary_stereochemical_ruleOutcome_iff hfaithful hexpansion,
    lexOutcome_iff_samples (windowPaths_pairwise _ _), stereochemicalSampleKey,
    stereochemicalSampleKey, stereoValueCode.map_orderedKeyOutcome_iff]
  intro position hposition
  unfold stereochemicalField
  rw [addressEvidence_of_unoccupied _ _ (data.unoccupied_outside_window hfaithful hexpansion
      descriptorMap unit left hposition),
    addressEvidence_of_unoccupied _ _ (data.unoccupied_outside_window hfaithful hexpansion
      descriptorMap unit right hposition)]

/-- **The actual ordinary unary key model.**  Each ligand's key is computed from that ligand's own
observation field, sampled on a unit-level address window and coded into `RuleKey`. -/
def withOrdinaryCanonicalAddressing_ordinaryRuleKeyModel (descriptorMap : DescriptorMap Unit) :
    OrdinaryRuleKeyModel data.withOrdinaryCanonicalAddressing.toProblem descriptorMap where
  key unit := data.ordinarySampleKey hfaithful hexpansion descriptorMap unit
  characterizes := by
    intro rule hrule unit left right outcome
    cases rule
    · exact data.constitutionalSampleKey_characterizes hfaithful hexpansion descriptorMap unit
        .rule1aAtomicNumber left right outcome
    · exact data.constitutionalSampleKey_characterizes hfaithful hexpansion descriptorMap unit
        .rule1bDuplicateNodeProximity left right outcome
    · exact data.constitutionalSampleKey_characterizes hfaithful hexpansion descriptorMap unit
        .rule2AtomicMass left right outcome
    · exact data.stereochemicalSampleKey_characterizes hfaithful hexpansion descriptorMap unit
        .rule3DoubleBondGeometry left right outcome
    · exact data.stereochemicalSampleKey_characterizes hfaithful hexpansion descriptorMap unit
        .rule4aStereogenicUnitKind left right outcome
    · exact data.stereochemicalSampleKey_characterizes hfaithful hexpansion descriptorMap unit
        .rule4bLikeUnlikeDescriptorPairs left right outcome
    · exact data.stereochemicalSampleKey_characterizes hfaithful hexpansion descriptorMap unit
        .rule4cPseudoasymmetricDescriptor left right outcome
    · exact data.stereochemicalSampleKey_characterizes hfaithful hexpansion descriptorMap unit
        .rule5EnantiomorphicDescriptor left right outcome
    · exact absurd rfl hrule

include hfaithful hexpansion in
/-- The ordinary total preorder through the existing `OrdinaryRuleKeyModel` assembly. -/
theorem withOrdinaryCanonicalAddressing_ordinaryPriority_of_keyModel
    (descriptorMap : DescriptorMap Unit) :
    data.withOrdinaryCanonicalAddressing.toProblem.OrdinaryPriorityIsTotalPreorder descriptorMap :=
  (data.withOrdinaryCanonicalAddressing_ordinaryRuleKeyModel hfaithful hexpansion
    descriptorMap).ordinaryPriorityIsTotalPreorder

end StereochemicalProblemData

end
end DeclarativeCIP
end OneCenter
end TetraStereo
