import TetraStereo.OneCenter.LocalizedMarkedTerminalComparison
import TetraStereo.OneCenter.LocalizedMarkedUncappedRankingLaws
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Key-level symmetries of the uncapped promoted comparator at terminal twins

Three facts about the unary Rules-1--6 key that every successful uncapped promoted comparison
factors through (`compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative_ordering_success_factors`):

1. **Terminal cursors.** The dense Rule-6 key of a terminal cursor is its own promotion label
   followed by phantom zeros; two terminal cursors with the same label under their respective
   marks have equal dense keys. Phantom `parent` fields differ but no label reads them.
2. **Twin-free cursors.** If no cursor of the reroot subtree carries one of the candidate marks,
   the complete promoted comparison and the dense Rule-6 key are independent of which of those
   marks is used. This is an induction over the actual Rule-6 recursion, child sorting and
   phantom padding; the ordinary Rules-1--5 part has no mark.
3. **Stored-depth decision.** If two cursors have different stored Rule-1b root distances, the
   dense constitutional key comparison is not a tie, so the complete key comparison is decided by
   the constitutional component regardless of mark or descriptor state.

No chemical claim, no totality assumption and no desired ordering is introduced here.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeKeys

open AuthoritativeCIPRule6PromotedComparatorLaws
open AuthoritativeCIPOccurrenceDescriptorComparatorLaws
open AuthoritativeCIPRerootComparatorLaws
open LocalizedMarkedUncappedRankingLaws

abbrev Cursor := CanonicalRerootCursor

/-! ## Small list facts -/

theorem forall₂_append {α β : Type} {R : α → β → Prop} {l₁ l₃ : List α} {l₂ l₄ : List β}
    (h₁ : List.Forall₂ R l₁ l₂) (h₂ : List.Forall₂ R l₃ l₄) :
    List.Forall₂ R (l₁ ++ l₃) (l₂ ++ l₄) := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hab _ ih => exact .cons hab ih

theorem forall₂_replicate {α β : Type} {R : α → β → Prop} {a : α} {b : β} (hab : R a b) :
    ∀ n, List.Forall₂ R (List.replicate n a) (List.replicate n b)
  | 0 => .nil
  | n + 1 => .cons hab (forall₂_replicate hab n)

theorem forall₂_flatten {α β : Type} {R : α → β → Prop} :
    ∀ {L : List (List α)} {L' : List (List β)}, List.Forall₂ (List.Forall₂ R) L L' →
      List.Forall₂ R L.flatten L'.flatten
  | [], [], _ => .nil
  | _ :: _, _ :: _, .cons h ht => forall₂_append h (forall₂_flatten ht)

theorem forall₂_map_eq {α β γ : Type} {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (respects : ∀ a b, R a b → f a = g b) :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → l.map f = l'.map g
  | [], [], _ => rfl
  | _ :: _, _ :: _, .cons h ht => by
      simp only [List.map_cons]
      rw [respects _ _ h, forall₂_map_eq respects ht]

/-! ## Phantom cursors -/

theorem phantom_forcedLeaf (mol : RawMolecule) (parent distance : Nat) :
    (mol.canonicalPhantom parent distance).forcedLeaf = true := rfl

theorem phantom_terminal (mol : RawMolecule) (parent distance : Nat) :
    cursorTerminal mol ({ node := mol.canonicalPhantom parent distance } : Cursor) = true := by
  simp [cursorTerminal, phantom_forcedLeaf]

theorem phantom_children (mol : RawMolecule) (parent distance : Nat)
    (previous : Option RawMolecule.CanonicalBranchNode) :
    ({ node := mol.canonicalPhantom parent distance, previous? := previous } : Cursor).children mol
      = [] := by
  simp [CanonicalRerootCursor.children, phantom_forcedLeaf]

theorem phantom_atom (mol : RawMolecule) (parent distance : Nat) :
    (mol.canonicalPhantom parent distance).atom = mol.atomCount := rfl

theorem rule6Priority_phantom (mol : RawMolecule) (parent distance mark : Nat)
    (bound : mark < mol.atomCount) :
    occurrenceRule6NodePriority mark ({ node := mol.canonicalPhantom parent distance } : Cursor)
      = 0 := by
  have ne : mol.atomCount ≠ mark := Nat.ne_of_gt bound
  simp [occurrenceRule6NodePriority, phantom_atom, ne]

/-! ## 1. Frontiers of terminal cursors, related pairwise -/

theorem denseDescriptorNext_forall₂ (mol : RawMolecule) (R : Cursor → Cursor → Prop)
    (terminals : ∀ a b, R a b → cursorTerminal mol a = true ∧ cursorTerminal mol b = true)
    (phantoms : ∀ a b, R a b →
      R (denseDescriptorPhantom mol a.node.atom (a.node.rule1bRootDistance + 1))
        (denseDescriptorPhantom mol b.node.atom (b.node.rule1bRootDistance + 1)))
    (before₁ before₂ : Cursor → Cursor → Option Ordering)
    {F F' : List Cursor} (h : List.Forall₂ R F F') :
    List.Forall₂ R (denseDescriptorNext mol before₁ F) (denseDescriptorNext mol before₂ F') := by
  unfold denseDescriptorNext
  induction h with
  | nil => exact .nil
  | cons hab _ ih =>
      simp only [List.flatMap_cons]
      rw [denseDescriptorChildren_eq_replicate_of_terminal mol before₁ _ (terminals _ _ hab).1,
        denseDescriptorChildren_eq_replicate_of_terminal mol before₂ _ (terminals _ _ hab).2]
      exact forall₂_append (forall₂_replicate (phantoms _ _ hab) _) ih

theorem denseDescriptorFrontiers_forall₂ (mol : RawMolecule) (R : Cursor → Cursor → Prop)
    (terminals : ∀ a b, R a b → cursorTerminal mol a = true ∧ cursorTerminal mol b = true)
    (phantoms : ∀ a b, R a b →
      R (denseDescriptorPhantom mol a.node.atom (a.node.rule1bRootDistance + 1))
        (denseDescriptorPhantom mol b.node.atom (b.node.rule1bRootDistance + 1)))
    (before₁ before₂ : Cursor → Cursor → Option Ordering) :
    ∀ (k : Nat) {F F' : List Cursor}, List.Forall₂ R F F' →
      List.Forall₂ (List.Forall₂ R) (denseDescriptorFrontiers mol before₁ k F)
        (denseDescriptorFrontiers mol before₂ k F')
  | 0, _, _, h => .cons h .nil
  | k + 1, _, _, h =>
      .cons h (denseDescriptorFrontiers_forall₂ mol R terminals phantoms before₁ before₂ k
        (denseDescriptorNext_forall₂ mol R terminals phantoms before₁ before₂ h))

/-- Terminal cursors whose promotion labels agree under two marks. -/
abbrev TerminalLabelRel (mol : RawMolecule) (m₁ m₂ : Nat) (x y : Cursor) : Prop :=
  cursorTerminal mol x = true ∧ cursorTerminal mol y = true ∧
    occurrenceRule6NodePriority m₁ x = occurrenceRule6NodePriority m₂ y

/-- Two terminal cursors with the same promotion label under their respective marks have the
same dense Rule-6 key, for any marks below the atom count and any child-ranking callbacks. -/
theorem denseRule6Key_terminal_eq (mol : RawMolecule)
    (before₁ before₂ : Cursor → Cursor → Option Ordering) (m₁ m₂ fuel : Nat) (a b : Cursor)
    (ta : cursorTerminal mol a = true) (tb : cursorTerminal mol b = true)
    (bound₁ : m₁ < mol.atomCount) (bound₂ : m₂ < mol.atomCount)
    (label : occurrenceRule6NodePriority m₁ a = occurrenceRule6NodePriority m₂ b) :
    buildDenseOccurrenceRule6Key mol before₁ m₁ fuel a =
      buildDenseOccurrenceRule6Key mol before₂ m₂ fuel b := by
  have terminals : ∀ x y, TerminalLabelRel mol m₁ m₂ x y →
      cursorTerminal mol x = true ∧ cursorTerminal mol y = true :=
    fun _ _ h => ⟨h.1, h.2.1⟩
  have phantoms : ∀ x y, TerminalLabelRel mol m₁ m₂ x y →
      TerminalLabelRel mol m₁ m₂
        (denseDescriptorPhantom mol x.node.atom (x.node.rule1bRootDistance + 1))
        (denseDescriptorPhantom mol y.node.atom (y.node.rule1bRootDistance + 1)) := by
    intro x y _
    refine ⟨phantom_terminal mol _ _, phantom_terminal mol _ _, ?_⟩
    simp only [denseDescriptorPhantom]
    rw [rule6Priority_phantom mol _ _ m₁ bound₁, rule6Priority_phantom mol _ _ m₂ bound₂]
  have top : TerminalLabelRel mol m₁ m₂ a b := ⟨ta, tb, label⟩
  have related := denseDescriptorFrontiers_forall₂ mol (TerminalLabelRel mol m₁ m₂) terminals
    phantoms before₁ before₂ fuel (F := [a]) (F' := [b]) (.cons top .nil)
  have flat := forall₂_flatten related
  unfold buildDenseOccurrenceRule6Key
  exact forall₂_map_eq (R := TerminalLabelRel mol m₁ m₂)
    (fun x y (h : TerminalLabelRel mol m₁ m₂ x y) => h.2.2) flat

/-! ## 2. Mark independence on twin-free cursors -/

/-- Reroot descent through actual cursor children. -/
def Below (mol : RawMolecule) : Cursor → Cursor → Prop :=
  Relation.ReflTransGen fun x y => y ∈ x.children mol

/-- No cursor reachable by reroot descent carries one of the listed atoms. -/
def Avoids (mol : RawMolecule) (T : List Nat) (c : Cursor) : Prop :=
  ∀ d, Below mol c d → d.node.atom ∉ T

theorem Avoids.self {mol : RawMolecule} {T : List Nat} {c : Cursor} (h : Avoids mol T c) :
    c.node.atom ∉ T := h c .refl

theorem Avoids.child {mol : RawMolecule} {T : List Nat} {c d : Cursor} (h : Avoids mol T c)
    (member : d ∈ c.children mol) : Avoids mol T d :=
  fun e below => h e ((Relation.ReflTransGen.single member).trans below)

theorem below_phantom {mol : RawMolecule} {parent distance : Nat}
    {previous : Option RawMolecule.CanonicalBranchNode} {d : Cursor}
    (below : Below mol { node := mol.canonicalPhantom parent distance, previous? := previous } d) :
    d = { node := mol.canonicalPhantom parent distance, previous? := previous } := by
  induction below with
  | refl => rfl
  | tail _ edge ih =>
      rw [ih, phantom_children] at edge
      simp at edge

theorem avoids_phantom (mol : RawMolecule) (T : List Nat) (inRange : ∀ t ∈ T, t < mol.atomCount)
    (parent distance : Nat) (previous : Option RawMolecule.CanonicalBranchNode) :
    Avoids mol T { node := mol.canonicalPhantom parent distance, previous? := previous } := by
  intro d below member
  rw [below_phantom below] at member
  exact Nat.ne_of_gt (inRange _ member) rfl

/-- Agreement of two child-ranking callbacks on twin-free cursors. -/
def AgreeOn (mol : RawMolecule) (T : List Nat)
    (before₁ before₂ : Cursor → Cursor → Option Ordering) : Prop :=
  ∀ x y, Avoids mol T x → Avoids mol T y → before₁ x y = before₂ x y

/-! ### Sorting callbacks: membership and congruence -/

theorem insertCursorBy?_mem (before : Cursor → Cursor → Option Ordering) (c : Cursor) :
    ∀ l out, insertCursorBy? before c l = some out → ∀ x ∈ out, x = c ∨ x ∈ l
  | [], out, computed, x, member => by
      simp [insertCursorBy?] at computed
      subst computed
      simp at member
      exact Or.inl member
  | head :: tail, out, computed, x, member => by
      cases h : before c head with
      | none => simp [insertCursorBy?, h] at computed
      | some o =>
          cases o with
          | lt =>
              simp only [insertCursorBy?, h, Option.map_eq_some_iff] at computed
              obtain ⟨deeper, deeperEq, rfl⟩ := computed
              rcases List.mem_cons.mp member with rfl | rest
              · exact Or.inr List.mem_cons_self
              · rcases insertCursorBy?_mem before c tail deeper deeperEq x rest with same | tailMem
                · exact Or.inl same
                · exact Or.inr (List.mem_cons_of_mem _ tailMem)
          | eq =>
              simp [insertCursorBy?, h] at computed
              subst computed
              rcases List.mem_cons.mp member with rfl | rest
              · exact Or.inl rfl
              · exact Or.inr rest
          | gt =>
              simp [insertCursorBy?, h] at computed
              subst computed
              rcases List.mem_cons.mp member with rfl | rest
              · exact Or.inl rfl
              · exact Or.inr rest

theorem sortCursorsBy?_mem (before : Cursor → Cursor → Option Ordering) :
    ∀ l out, sortCursorsBy? before l = some out → ∀ x ∈ out, x ∈ l
  | [], out, computed, x, member => by
      simp [sortCursorsBy?] at computed
      subst computed
      simp at member
  | c :: tail, out, computed, x, member => by
      simp only [sortCursorsBy?, Option.bind_eq_bind, Option.bind_eq_some_iff] at computed
      rcases computed with ⟨sorted, sortedEq, inserted⟩
      rcases insertCursorBy?_mem before c sorted out inserted x member with rfl | sortedMem
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (sortCursorsBy?_mem before tail sorted sortedEq x sortedMem)

theorem insertCursorBy?_congr (before₁ before₂ : Cursor → Cursor → Option Ordering) (c : Cursor) :
    ∀ l, (∀ x ∈ l, before₁ c x = before₂ c x) →
      insertCursorBy? before₁ c l = insertCursorBy? before₂ c l
  | [], _ => rfl
  | head :: tail, agree => by
      have headEq := agree head List.mem_cons_self
      have tailEq := insertCursorBy?_congr before₁ before₂ c tail
        fun x member => agree x (List.mem_cons_of_mem _ member)
      cases h : before₂ c head with
      | none => simp [insertCursorBy?, headEq, h]
      | some o => cases o <;> simp [insertCursorBy?, headEq, h, tailEq]

theorem sortCursorsBy?_congr (before₁ before₂ : Cursor → Cursor → Option Ordering) :
    ∀ l, (∀ x ∈ l, ∀ y ∈ l, before₁ x y = before₂ x y) →
      sortCursorsBy? before₁ l = sortCursorsBy? before₂ l
  | [], _ => rfl
  | c :: tail, agree => by
      have tailEq := sortCursorsBy?_congr before₁ before₂ tail fun x xm y ym =>
        agree x (List.mem_cons_of_mem _ xm) y (List.mem_cons_of_mem _ ym)
      cases sortedEq : sortCursorsBy? before₂ tail with
      | none => simp [sortCursorsBy?, tailEq, sortedEq]
      | some sorted =>
          have inserted := insertCursorBy?_congr before₁ before₂ c sorted fun x member =>
            agree c List.mem_cons_self x
              (List.mem_cons_of_mem _ (sortCursorsBy?_mem before₂ tail sorted sortedEq x member))
          simp [sortCursorsBy?, tailEq, sortedEq, inserted]

theorem insertCursorTotalBy_congr (before₁ before₂ : Cursor → Cursor → Option Ordering)
    (c : Cursor) :
    ∀ l, (∀ x ∈ l, before₁ c x = before₂ c x) →
      insertCursorTotalBy before₁ c l = insertCursorTotalBy before₂ c l
  | [], _ => rfl
  | head :: tail, agree => by
      have headEq := agree head List.mem_cons_self
      have tailEq := insertCursorTotalBy_congr before₁ before₂ c tail
        fun x member => agree x (List.mem_cons_of_mem _ member)
      simp only [insertCursorTotalBy, totalizedDecision, headEq, tailEq]

theorem insertCursorTotalBy_mem (before : Cursor → Cursor → Option Ordering) (c : Cursor) :
    ∀ l, ∀ x ∈ insertCursorTotalBy before c l, x = c ∨ x ∈ l
  | [], x, member => by
      simp [insertCursorTotalBy] at member
      exact Or.inl member
  | head :: tail, x, member => by
      simp only [insertCursorTotalBy] at member
      cases h : totalizedDecision before c head <;> simp only [h] at member
      · rcases List.mem_cons.mp member with rfl | rest
        · exact Or.inr List.mem_cons_self
        · rcases insertCursorTotalBy_mem before c tail x rest with same | tailMem
          · exact Or.inl same
          · exact Or.inr (List.mem_cons_of_mem _ tailMem)
      · rcases List.mem_cons.mp member with rfl | rest
        · exact Or.inl rfl
        · exact Or.inr rest
      · rcases List.mem_cons.mp member with rfl | rest
        · exact Or.inl rfl
        · exact Or.inr rest

theorem sortCursorsTotalBy_mem (before : Cursor → Cursor → Option Ordering) :
    ∀ l, ∀ x ∈ sortCursorsTotalBy before l, x ∈ l
  | [], x, member => by simp [sortCursorsTotalBy] at member
  | c :: tail, x, member => by
      simp only [sortCursorsTotalBy] at member
      rcases insertCursorTotalBy_mem before c _ x member with rfl | sortedMem
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (sortCursorsTotalBy_mem before tail x sortedMem)

theorem sortCursorsTotalBy_congr (before₁ before₂ : Cursor → Cursor → Option Ordering) :
    ∀ l, (∀ x ∈ l, ∀ y ∈ l, before₁ x y = before₂ x y) →
      sortCursorsTotalBy before₁ l = sortCursorsTotalBy before₂ l
  | [], _ => rfl
  | c :: tail, agree => by
      have tailEq := sortCursorsTotalBy_congr before₁ before₂ tail fun x xm y ym =>
        agree x (List.mem_cons_of_mem _ xm) y (List.mem_cons_of_mem _ ym)
      simp only [sortCursorsTotalBy, tailEq]
      apply insertCursorTotalBy_congr
      intro x member
      exact agree c List.mem_cons_self x
        (List.mem_cons_of_mem _ (sortCursorsTotalBy_mem before₂ tail x member))

/-! ### Ranked children and pair expansion -/

/-- Members of the ranked child frame are children or the padding phantom. -/
theorem rankedCursorChildrenAuthoritative?_mem (mol : RawMolecule)
    (before : Cursor → Cursor → Option Ordering) (c : Cursor) (ranked : List Cursor)
    (computed : rankedCursorChildrenAuthoritative? mol before c = some ranked) :
    ∀ x ∈ ranked, x ∈ c.children mol ∨
      x = { node := mol.canonicalPhantom c.node.atom (c.node.rule1bRootDistance + 1) } := by
  by_cases wide : RawMolecule.authoritativeChildSlots < (c.children mol).length
  · simp [rankedCursorChildrenAuthoritative?, wide] at computed
  · cases sortedEq : sortCursorsBy? before (c.children mol) with
    | none => simp [rankedCursorChildrenAuthoritative?, wide, sortedEq] at computed
    | some sorted =>
        simp only [rankedCursorChildrenAuthoritative?, wide, ↓reduceIte, sortedEq,
          Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at computed
        subst computed
        intro x member
        rcases List.mem_append.mp member with sortedMem | padded
        · exact Or.inl (sortCursorsBy?_mem before _ sorted sortedEq x sortedMem)
        · exact Or.inr (List.eq_of_mem_replicate padded)

theorem rankedCursorChildrenAuthoritative?_avoids (mol : RawMolecule) (T : List Nat)
    (inRange : ∀ t ∈ T, t < mol.atomCount) (before : Cursor → Cursor → Option Ordering)
    (c : Cursor) (good : Avoids mol T c) (ranked : List Cursor)
    (computed : rankedCursorChildrenAuthoritative? mol before c = some ranked) :
    ∀ x ∈ ranked, Avoids mol T x := by
  intro x member
  rcases rankedCursorChildrenAuthoritative?_mem mol before c ranked computed x member with
    child | rfl
  · exact good.child child
  · exact avoids_phantom mol T inRange _ _ _

theorem rankedCursorChildrenAuthoritative?_congr (mol : RawMolecule) (T : List Nat)
    (before₁ before₂ : Cursor → Cursor → Option Ordering)
    (agree : AgreeOn mol T before₁ before₂) (c : Cursor) (good : Avoids mol T c) :
    rankedCursorChildrenAuthoritative? mol before₁ c =
      rankedCursorChildrenAuthoritative? mol before₂ c := by
  have sorted := sortCursorsBy?_congr before₁ before₂ (c.children mol)
    fun x xm y ym => agree x y (good.child xm) (good.child ym)
  simp only [rankedCursorChildrenAuthoritative?, sorted]

/-- Pairs whose both components avoid the marks. -/
def PairsAvoid (mol : RawMolecule) (T : List Nat) (pairs : List (Cursor × Cursor)) : Prop :=
  ∀ p ∈ pairs, Avoids mol T p.1 ∧ Avoids mol T p.2

theorem nextPairs_congr (mol : RawMolecule) (T : List Nat) (inRange : ∀ t ∈ T, t < mol.atomCount)
    (before₁ before₂ : Cursor → Cursor → Option Ordering)
    (agree : AgreeOn mol T before₁ before₂) :
    ∀ pairs, PairsAvoid mol T pairs →
      nextOccurrenceDescriptorPairsAuthoritative? mol before₁ before₁ pairs =
        nextOccurrenceDescriptorPairsAuthoritative? mol before₂ before₂ pairs ∧
      ∀ next, nextOccurrenceDescriptorPairsAuthoritative? mol before₁ before₁ pairs = some next →
        PairsAvoid mol T next
  | [], _ => ⟨rfl, fun next computed => by
      simp only [nextOccurrenceDescriptorPairsAuthoritative?, Option.some.injEq] at computed
      subst computed
      intro p member
      simp at member⟩
  | pair :: pairs, good => by
      have tail := nextPairs_congr mol T inRange before₁ before₂ agree pairs
        fun p member => good p (List.mem_cons_of_mem _ member)
      have pairGood := good pair List.mem_cons_self
      have leftEq := rankedCursorChildrenAuthoritative?_congr mol T before₁ before₂ agree pair.1
        pairGood.1
      have rightEq := rankedCursorChildrenAuthoritative?_congr mol T before₁ before₂ agree pair.2
        pairGood.2
      constructor
      · simp only [nextOccurrenceDescriptorPairsAuthoritative?, tail.1, leftEq, rightEq]
      · intro next computed
        simp only [nextOccurrenceDescriptorPairsAuthoritative?, Option.bind_eq_bind,
          Option.bind_eq_some_iff] at computed
        rcases computed with ⟨rest, restEq, computed⟩
        have restGood := tail.2 rest restEq
        split at computed
        · simp only [Option.some.injEq] at computed
          subst computed
          exact restGood
        · simp only [Option.bind_eq_some_iff, Option.some.injEq] at computed
          rcases computed with ⟨left, leftComputed, right, rightComputed, rfl⟩
          intro p member
          rcases List.mem_append.mp member with zipped | deeper
          · obtain ⟨leftMem, rightMem⟩ := List.of_mem_zip zipped
            exact ⟨rankedCursorChildrenAuthoritative?_avoids mol T inRange before₁ pair.1
                pairGood.1 left leftComputed p.1 leftMem,
              rankedCursorChildrenAuthoritative?_avoids mol T inRange before₁ pair.2 pairGood.2
                right rightComputed p.2 rightMem⟩
          · exact restGood p deeper

theorem rule6PairLabels_eq_of_avoid (mol : RawMolecule) (T : List Nat) (mark : Nat)
    (markIn : mark ∈ T) :
    ∀ pairs, PairsAvoid mol T pairs → compareOccurrenceRule6PairLabels mark pairs = .eq
  | [], _ => rfl
  | pair :: pairs, good => by
      have pairGood := good pair List.mem_cons_self
      have leftNe : pair.1.node.atom ≠ mark := fun same => pairGood.1.self (same ▸ markIn)
      have rightNe : pair.2.node.atom ≠ mark := fun same => pairGood.2.self (same ▸ markIn)
      have zero : compare (0 : Nat) 0 = Ordering.eq := rfl
      have deeper := rule6PairLabels_eq_of_avoid mol T mark markIn pairs
        fun p member => good p (List.mem_cons_of_mem _ member)
      simp only [compareOccurrenceRule6PairLabels, leftNe, rightNe, beq_iff_eq, ↓reduceIte, zero]
      exact deeper

theorem rule6Authoritative_congr (mol : RawMolecule) (T : List Nat)
    (inRange : ∀ t ∈ T, t < mol.atomCount) (m₁ m₂ : Nat) (in₁ : m₁ ∈ T) (in₂ : m₂ ∈ T)
    (before₁ before₂ : Cursor → Cursor → Option Ordering) (agree : AgreeOn mol T before₁ before₂) :
    ∀ fuel pairs, PairsAvoid mol T pairs →
      compareOccurrenceRule6Authoritative mol before₁ m₁ fuel pairs =
        compareOccurrenceRule6Authoritative mol before₂ m₂ fuel pairs
  | 0, pairs, good => by
      simp only [compareOccurrenceRule6Authoritative,
        rule6PairLabels_eq_of_avoid mol T m₁ in₁ pairs good,
        rule6PairLabels_eq_of_avoid mol T m₂ in₂ pairs good,
        (nextPairs_congr mol T inRange before₁ before₂ agree pairs good).1]
  | fuel + 1, pairs, good => by
      have next := nextPairs_congr mol T inRange before₁ before₂ agree pairs good
      simp only [compareOccurrenceRule6Authoritative,
        rule6PairLabels_eq_of_avoid mol T m₁ in₁ pairs good,
        rule6PairLabels_eq_of_avoid mol T m₂ in₂ pairs good]
      rw [← next.1]
      cases nextEq : nextOccurrenceDescriptorPairsAuthoritative? mol before₁ before₁ pairs with
      | none => rfl
      | some nextPairs =>
          cases nextPairs with
          | nil => rfl
          | cons head tail =>
              exact rule6Authoritative_congr mol T inRange m₁ m₂ in₁ in₂ before₁ before₂ agree fuel
                (head :: tail) (next.2 _ nextEq)

/-- The complete uncapped promoted comparison of twin-free cursors does not depend on which of the
avoided marks is the reference. -/
theorem promoted_congr (mol : RawMolecule) (T : List Nat) (inRange : ∀ t ∈ T, t < mol.atomCount)
    (state : OccurrenceAuxState) (m₁ m₂ : Nat) (in₁ : m₁ ∈ T) (in₂ : m₂ ∈ T) :
    ∀ fuel a b, Avoids mol T a → Avoids mol T b →
      compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol state m₁ fuel a b =
        compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol state m₂ fuel a b
  | 0, a, b, ga, gb => by
      have leftNe₁ : a.node.atom ≠ m₁ := fun same => ga.self (same ▸ in₁)
      have rightNe₁ : b.node.atom ≠ m₁ := fun same => gb.self (same ▸ in₁)
      have leftNe₂ : a.node.atom ≠ m₂ := fun same => ga.self (same ▸ in₂)
      have rightNe₂ : b.node.atom ≠ m₂ := fun same => gb.self (same ▸ in₂)
      simp [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, leftNe₁, rightNe₁,
        leftNe₂, rightNe₂]
  | fuel + 1, a, b, ga, gb => by
      have agree : AgreeOn mol T
          (fun x y => (compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol state
            m₁ fuel x y).map Rule6TrackedDecision.ordering)
          (fun x y => (compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative? mol state
            m₂ fuel x y).map Rule6TrackedDecision.ordering) := by
        intro x y gx gy
        simp only [promoted_congr mol T inRange state m₁ m₂ in₁ in₂ fuel x y gx gy]
      have single : PairsAvoid mol T [(a, b)] := by
        intro p member
        simp only [List.mem_singleton] at member
        subst member
        exact ⟨ga, gb⟩
      have rule6 := rule6Authoritative_congr mol T inRange m₁ m₂ in₁ in₂ _ _ agree (fuel + 1)
        [(a, b)] single
      simp only [compareOccurrenceBranchesThroughRule6AtUnrestrictedAuthoritative?, rule6]

theorem promotedBefore_agree (mol : RawMolecule) (T : List Nat)
    (inRange : ∀ t ∈ T, t < mol.atomCount) (state : OccurrenceAuxState) (m₁ m₂ : Nat)
    (in₁ : m₁ ∈ T) (in₂ : m₂ ∈ T) (fuel : Nat) :
    AgreeOn mol T (promotedRule6BeforeUnrestricted mol state m₁ fuel)
      (promotedRule6BeforeUnrestricted mol state m₂ fuel) := by
  intro x y gx gy
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp only [promotedRule6BeforeUnrestricted]
      rw [promoted_congr mol T inRange state m₁ m₂ in₁ in₂ fuel x y gx gy]

theorem denseDescriptorChildren_congr (mol : RawMolecule) (T : List Nat)
    (before₁ before₂ : Cursor → Cursor → Option Ordering)
    (agree : AgreeOn mol T before₁ before₂) (c : Cursor) (good : Avoids mol T c) :
    denseDescriptorChildren mol before₁ c = denseDescriptorChildren mol before₂ c := by
  unfold denseDescriptorChildren
  rw [sortCursorsTotalBy_congr before₁ before₂ (c.children mol)
    fun x xm y ym => agree x y (good.child xm) (good.child ym)]

theorem denseDescriptorChildren_avoids (mol : RawMolecule) (T : List Nat)
    (inRange : ∀ t ∈ T, t < mol.atomCount) (before : Cursor → Cursor → Option Ordering)
    (c : Cursor) (good : Avoids mol T c) :
    ∀ x ∈ denseDescriptorChildren mol before c, Avoids mol T x := by
  intro x member
  unfold denseDescriptorChildren at member
  rcases List.mem_append.mp member with sortedMem | padded
  · exact good.child (sortCursorsTotalBy_mem before _ x (List.mem_of_mem_take sortedMem))
  · rw [List.eq_of_mem_replicate padded]
    exact avoids_phantom mol T inRange _ _ _

theorem denseDescriptorFrontiers_congr (mol : RawMolecule) (T : List Nat)
    (inRange : ∀ t ∈ T, t < mol.atomCount) (before₁ before₂ : Cursor → Cursor → Option Ordering)
    (agree : AgreeOn mol T before₁ before₂) :
    ∀ k F, (∀ x ∈ F, Avoids mol T x) →
      denseDescriptorFrontiers mol before₁ k F = denseDescriptorFrontiers mol before₂ k F ∧
        ∀ layer ∈ denseDescriptorFrontiers mol before₁ k F, ∀ x ∈ layer, Avoids mol T x
  | 0, F, good => ⟨rfl, fun layer member => by
      simp only [denseDescriptorFrontiers, List.mem_singleton] at member
      subst member
      exact good⟩
  | k + 1, F, good => by
      have nextGood : ∀ x ∈ denseDescriptorNext mol before₁ F, Avoids mol T x := by
        intro x member
        unfold denseDescriptorNext at member
        obtain ⟨c, cMem, xMem⟩ := List.mem_flatMap.mp member
        exact denseDescriptorChildren_avoids mol T inRange before₁ c (good c cMem) x xMem
      have nextEq : denseDescriptorNext mol before₁ F = denseDescriptorNext mol before₂ F := by
        unfold denseDescriptorNext
        exact LocalizedGenericMarkedRecalculation.flatMap_congr_mem _ _ _ fun c cMem =>
          denseDescriptorChildren_congr mol T before₁ before₂ agree c (good c cMem)
      have deeper := denseDescriptorFrontiers_congr mol T inRange before₁ before₂ agree k
        (denseDescriptorNext mol before₁ F) nextGood
      refine ⟨?_, ?_⟩
      · simp only [denseDescriptorFrontiers]
        rw [deeper.1, nextEq]
      · intro layer member
        simp only [denseDescriptorFrontiers, List.mem_cons] at member
        rcases member with rfl | deeperMem
        · exact good
        · exact deeper.2 layer deeperMem

/-- The dense Rule-6 key of a twin-free cursor is independent of which avoided mark is used. -/
theorem denseRule6Key_congr (mol : RawMolecule) (T : List Nat)
    (inRange : ∀ t ∈ T, t < mol.atomCount) (state : OccurrenceAuxState) (m₁ m₂ : Nat)
    (in₁ : m₁ ∈ T) (in₂ : m₂ ∈ T) (fuel : Nat) (c : Cursor) (good : Avoids mol T c) :
    buildDenseOccurrenceRule6Key mol (promotedRule6BeforeUnrestricted mol state m₁ fuel) m₁ fuel c =
      buildDenseOccurrenceRule6Key mol (promotedRule6BeforeUnrestricted mol state m₂ fuel) m₂ fuel c := by
  have frontiers := denseDescriptorFrontiers_congr mol T inRange _ _
    (promotedBefore_agree mol T inRange state m₁ m₂ in₁ in₂ fuel) fuel [c]
    (fun x member => by
      simp only [List.mem_singleton] at member
      subst member
      exact good)
  unfold buildDenseOccurrenceRule6Key
  rw [← frontiers.1]
  apply List.map_congr_left
  intro x member
  obtain ⟨layer, layerMem, xMem⟩ := List.mem_flatten.mp member
  have avoid := frontiers.2 layer layerMem x xMem
  have ne₁ : x.node.atom ≠ m₁ := fun same => avoid.self (same ▸ in₁)
  have ne₂ : x.node.atom ≠ m₂ := fun same => avoid.self (same ▸ in₂)
  simp [occurrenceRule6NodePriority, ne₁, ne₂]

/-- The complete promoted key of a twin-free cursor is independent of the avoided mark. -/
theorem promotedKey_congr (mol : RawMolecule) (T : List Nat)
    (inRange : ∀ t ∈ T, t < mol.atomCount) (state : OccurrenceAuxState) (m₁ m₂ : Nat)
    (in₁ : m₁ ∈ T) (in₂ : m₂ ∈ T) (fuel : Nat) (c : Cursor) (good : Avoids mol T c) :
    buildPromotedOccurrenceBranchKeyUnrestricted mol state m₁ fuel c =
      buildPromotedOccurrenceBranchKeyUnrestricted mol state m₂ fuel c := by
  unfold buildPromotedOccurrenceBranchKeyUnrestricted
  rw [denseRule6Key_congr mol T inRange state m₁ m₂ in₁ in₂ fuel c good]

/-! ## 3. Stored-depth decision of the constitutional component -/

theorem denseRerootKey_rule1b_head (mol : RawMolecule) (fuel : Nat) (c : Cursor) :
    ∃ tail, (buildDenseRerootKey mol fuel c).rule1b = c.node.rule1bRootDistance :: tail := by
  cases fuel with
  | zero => exact ⟨[], rfl⟩
  | succ fuel =>
      refine ⟨((denseCursorFrontiers mol fuel fuel (denseNextCursorFrontier mol fuel [c])).flatten.map
        fun entry => entry.node.rule1bRootDistance), ?_⟩
      simp [buildDenseRerootKey, denseCursorFrontiers]

theorem compareDenseRule1b_eq_eq_iff (x y : Nat) : compareDenseRule1b x y = .eq ↔ x = y := by
  unfold compareDenseRule1b
  by_cases lt : x < y
  · simp [lt]
    omega
  · by_cases gt : y < x
    · simp [lt, gt]
      omega
    · simp [lt, gt]
      omega

/-- Different stored root distances: the dense constitutional comparison is never a tie. -/
theorem compareDenseRerootKeys_ne_eq_of_distance (mol : RawMolecule) (fuel : Nat) (a b : Cursor)
    (distinct : a.node.rule1bRootDistance ≠ b.node.rule1bRootDistance) :
    compareDenseRerootKeys (buildDenseRerootKey mol fuel a) (buildDenseRerootKey mol fuel b) ≠ .eq := by
  obtain ⟨tailA, headA⟩ := denseRerootKey_rule1b_head mol fuel a
  obtain ⟨tailB, headB⟩ := denseRerootKey_rule1b_head mol fuel b
  intro tie
  unfold compareDenseRerootKeys at tie
  simp only [compareLex, Ordering.byKey, Ordering.then_eq_eq] at tie
  rw [headA, headB, List.compareLex_cons_cons, Ordering.then_eq_eq,
    compareDenseRule1b_eq_eq_iff] at tie
  exact distinct tie.2.1.1

/-- A non-tied constitutional component decides the ordinary projected key comparison. -/
theorem compareFailClosed_eq_constitutional (left right : FailClosedOccurrenceBranchProjectedKey)
    (decided : compareDenseRerootKeys left.constitutional right.constitutional ≠ .eq) :
    compareFailClosedOccurrenceBranchProjectedKeys left right =
      compareDenseRerootKeys left.constitutional right.constitutional := by
  unfold compareFailClosedOccurrenceBranchProjectedKeys
  simp only [compareLex, Ordering.byKey]
  cases h : compareDenseRerootKeys left.constitutional right.constitutional with
  | eq => exact absurd h decided
  | lt => rfl
  | gt => rfl

/-- A non-tied ordinary component decides the complete promoted key comparison. -/
theorem comparePromoted_eq_ordinary (left right : PromotedOccurrenceBranchKey)
    (decided : compareFailClosedOccurrenceBranchProjectedKeys left.ordinary right.ordinary ≠ .eq) :
    comparePromotedOccurrenceBranchKeys left right =
      compareFailClosedOccurrenceBranchProjectedKeys left.ordinary right.ordinary := by
  unfold comparePromotedOccurrenceBranchKeys
  simp only [compareLex, Ordering.byKey]
  cases h : compareFailClosedOccurrenceBranchProjectedKeys left.ordinary right.ordinary with
  | eq => exact absurd h decided
  | lt => rfl
  | gt => rfl

theorem promotedKey_ordinary (mol : RawMolecule) (state : OccurrenceAuxState) (mark fuel : Nat)
    (c : Cursor) :
    (buildPromotedOccurrenceBranchKeyUnrestricted mol state mark fuel c).ordinary =
      buildFailClosedOccurrenceBranchProjectedKey mol state fuel c := rfl

theorem failClosedKey_constitutional (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (c : Cursor) :
    (buildFailClosedOccurrenceBranchProjectedKey mol state fuel c).constitutional =
      buildDenseRerootKey mol fuel c := rfl

/-- **Stored-depth decision.** Cursors of different stored Rule-1b root distance are compared by
their dense constitutional keys alone, whatever the mark and auxiliary state. -/
theorem cursorCompare_of_distance (mol : RawMolecule) (state : OccurrenceAuxState)
    (mark fuel : Nat) (a b : Cursor)
    (distinct : a.node.rule1bRootDistance ≠ b.node.rule1bRootDistance) :
    cursorCompare mol state mark fuel a b =
      compareDenseRerootKeys (buildDenseRerootKey mol fuel a) (buildDenseRerootKey mol fuel b) := by
  have decidedC := compareDenseRerootKeys_ne_eq_of_distance mol fuel a b distinct
  have ordinaryEq := compareFailClosed_eq_constitutional
    (buildFailClosedOccurrenceBranchProjectedKey mol state fuel a)
    (buildFailClosedOccurrenceBranchProjectedKey mol state fuel b)
    (by rw [failClosedKey_constitutional, failClosedKey_constitutional]; exact decidedC)
  rw [failClosedKey_constitutional, failClosedKey_constitutional] at ordinaryEq
  unfold cursorCompare
  rw [comparePromoted_eq_ordinary, promotedKey_ordinary, promotedKey_ordinary, ordinaryEq]
  rw [promotedKey_ordinary, promotedKey_ordinary, ordinaryEq]
  exact decidedC

/-! ## Comparator congruence through tied keys -/

theorem orientedCmp_refl {α : Type} (cmp : α → α → Ordering) [Std.OrientedCmp cmp] (a : α) :
    cmp a a = .eq := by
  have swap := Std.OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := a)
  cases h : cmp a a with
  | eq => rfl
  | lt => rw [h] at swap; cases swap
  | gt => rw [h] at swap; cases swap

theorem isLE_of_eq {o : Ordering} (h : o = .eq) : o.isLE = true := by subst h; rfl
theorem isLE_of_lt {o : Ordering} (h : o = .lt) : o.isLE = true := by subst h; rfl
theorem not_isLE_of_gt {o : Ordering} (h : o = .gt) : o.isLE = false := by subst h; rfl

theorem transCmp_congr_left {α : Type} (cmp : α → α → Ordering) [Std.TransCmp cmp] {a b : α}
    (tie : cmp a b = .eq) (c : α) : cmp a c = cmp b c := by
  have tie' : cmp b a = .eq := by
    rw [Std.OrientedCmp.eq_swap (cmp := cmp) (a := b) (b := a), tie]; rfl
  cases hbc : cmp b c with
  | eq =>
      have hcb : cmp c b = .eq := by
        rw [Std.OrientedCmp.eq_swap (cmp := cmp) (a := c) (b := b), hbc]; rfl
      have ac : (cmp a c).isLE = true := Std.TransCmp.isLE_trans (isLE_of_eq tie) (isLE_of_eq hbc)
      have ca : (cmp c a).isLE = true := Std.TransCmp.isLE_trans (isLE_of_eq hcb) (isLE_of_eq tie')
      cases hac : cmp a c with
      | eq => rfl
      | lt =>
          rw [Std.OrientedCmp.eq_swap (cmp := cmp) (a := c) (b := a), hac] at ca
          cases ca
      | gt => rw [hac] at ac; cases ac
  | lt =>
      have ac : (cmp a c).isLE = true := Std.TransCmp.isLE_trans (isLE_of_eq tie) (isLE_of_lt hbc)
      have hcb : cmp c b = .gt := by
        rw [Std.OrientedCmp.eq_swap (cmp := cmp) (a := c) (b := b), hbc]; rfl
      cases hac : cmp a c with
      | lt => rfl
      | gt => rw [hac] at ac; cases ac
      | eq =>
          have hca : cmp c a = .eq := by
            rw [Std.OrientedCmp.eq_swap (cmp := cmp) (a := c) (b := a), hac]; rfl
          have cb : (cmp c b).isLE = true :=
            Std.TransCmp.isLE_trans (isLE_of_eq hca) (isLE_of_eq tie)
          rw [hcb] at cb
          cases cb
  | gt =>
      have hcb : cmp c b = .lt := by
        rw [Std.OrientedCmp.eq_swap (cmp := cmp) (a := c) (b := b), hbc]; rfl
      have ca : (cmp c a).isLE = true := Std.TransCmp.isLE_trans (isLE_of_lt hcb) (isLE_of_eq tie')
      cases hca : cmp c a with
      | lt =>
          rw [Std.OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := c), hca]
          rfl
      | gt => rw [hca] at ca; cases ca
      | eq =>
          have hac : cmp a c = .eq := by
            rw [Std.OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := c), hca]; rfl
          have bc : (cmp b c).isLE = true :=
            Std.TransCmp.isLE_trans (isLE_of_eq tie') (isLE_of_eq hac)
          rw [hbc] at bc
          cases bc

theorem transCmp_congr_right {α : Type} (cmp : α → α → Ordering) [Std.TransCmp cmp] {b c : α}
    (tie : cmp b c = .eq) (a : α) : cmp a b = cmp a c := by
  rw [Std.OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := b),
    Std.OrientedCmp.eq_swap (cmp := cmp) (a := a) (b := c),
    transCmp_congr_left cmp tie a]

end TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeKeys

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeKeys.denseRule6Key_terminal_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeKeys.promoted_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeKeys.promotedKey_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeKeys.cursorCompare_of_distance
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeKeys.transCmp_congr_left
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeKeys.transCmp_congr_right
