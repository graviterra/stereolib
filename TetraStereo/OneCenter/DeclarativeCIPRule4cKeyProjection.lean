import TetraStereo.OneCenter.DeclarativeCIPRule4cReadingEvidence
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The independent ordinary order under molecular Rules 4a, 4b and 4c.
Only masked Rules 3 and 5 are removed; the complete lowercase Rule-4c component is retained. -/

namespace TetraStereo.OneCenter.DeclarativeCIP
noncomputable section
open scoped Classical
universe u
variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (graph : RootedDigraph Atom)
  (evidence : StereochemicalEvidence graph)

private theorem cons_lt_cons_same {α : Type*} [LinearOrder α] (a : α) (l m : List α) :
    a :: l < a :: m ↔ l < m := by
  rw [List.cons_lt_cons_iff]
  simp

theorem ordinaryKey_lt_iff_rule4abcKey
    (h : Rule4abcOnly graph evidence) (W D : ℕ) (x y : graph.Node) :
    ordinaryKey molecule graph evidence W D x < ordinaryKey molecule graph evidence W D y ↔
      rule4abcKey molecule graph evidence W D x <
        rule4abcKey molecule graph evidence W D y := by
  unfold rule4abcKey rule4aComponent rule4bComponent rule4cComponent
  rw [← toLex_ofLex (ordinaryKey molecule graph evidence W D x),
    ← toLex_ofLex (ordinaryKey molecule graph evidence W D y), Prod.Lex.lt_iff, Prod.Lex.lt_iff]
  simp only [ofLex_toLex, ordinaryKey_fst]
  constructor
  · rintro (hlt | ⟨heq, hlt⟩)
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      obtain ⟨e0, e4⟩ := shapeComponents_eq_rule4abc molecule graph evidence h W D heq
      rw [ordinaryKey_stereo_eq molecule graph evidence W D x,
        ordinaryKey_stereo_eq molecule graph evidence W D y, e0, cons_lt_cons_same,
        List.cons_lt_cons_iff] at hlt
      rw [Prod.Lex.lt_iff]
      rcases hlt with hlt | ⟨h1, hlt⟩
      · exact Or.inl hlt
      · refine Or.inr ⟨h1, ?_⟩
        rw [List.cons_lt_cons_iff] at hlt
        rw [Prod.Lex.lt_iff]
        rcases hlt with hlt | ⟨h2, hlt⟩
        · exact Or.inl hlt
        · refine Or.inr ⟨h2, ?_⟩
          rw [List.cons_lt_cons_iff] at hlt
          rcases hlt with hlt | ⟨_, hlt⟩
          · exact hlt
          · rw [e4] at hlt
            exact absurd hlt (lt_irrefl _)
  · rintro (hlt | ⟨heq, hlt⟩)
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      obtain ⟨e0, _⟩ := shapeComponents_eq_rule4abc molecule graph evidence h W D heq
      rw [ordinaryKey_stereo_eq molecule graph evidence W D x,
        ordinaryKey_stereo_eq molecule graph evidence W D y, e0, cons_lt_cons_same,
        List.cons_lt_cons_iff]
      rw [Prod.Lex.lt_iff] at hlt
      rcases hlt with hlt | ⟨h1, hlt⟩
      · exact Or.inl hlt
      · refine Or.inr ⟨h1, ?_⟩
        rw [List.cons_lt_cons_iff]
        rw [Prod.Lex.lt_iff] at hlt
        rcases hlt with hlt | ⟨h2, hlt⟩
        · exact Or.inl hlt
        · exact Or.inr ⟨h2, List.cons_lt_cons_iff.2 (Or.inl hlt)⟩

theorem ordinaryKey_le_iff_rule4abcKey
    (h : Rule4abcOnly graph evidence) (W D : ℕ) (x y : graph.Node) :
    ordinaryKey molecule graph evidence W D x ≤ ordinaryKey molecule graph evidence W D y ↔
      rule4abcKey molecule graph evidence W D x ≤
        rule4abcKey molecule graph evidence W D y := by
  rw [← not_lt, ← not_lt, ordinaryKey_lt_iff_rule4abcKey molecule graph evidence h]

theorem ordinaryKey_eq_iff_rule4abcKey
    (h : Rule4abcOnly graph evidence) (W D : ℕ) (x y : graph.Node) :
    ordinaryKey molecule graph evidence W D x = ordinaryKey molecule graph evidence W D y ↔
      rule4abcKey molecule graph evidence W D x =
        rule4abcKey molecule graph evidence W D y := by
  constructor
  · intro equal
    apply le_antisymm
    · exact (ordinaryKey_le_iff_rule4abcKey molecule graph evidence h W D x y).1 equal.le
    · exact (ordinaryKey_le_iff_rule4abcKey molecule graph evidence h W D y x).1 equal.ge
  · intro equal
    apply le_antisymm
    · exact (ordinaryKey_le_iff_rule4abcKey molecule graph evidence h W D x y).2 equal.le
    · exact (ordinaryKey_le_iff_rule4abcKey molecule graph evidence h W D y x).2 equal.ge

/-- The no-reference active components retain Rule 4c and omit the masked Rule 4b. -/
def rule4acKey (W D : ℕ) (node : graph.Node) :
    Lex (List (Certificate.CanonicalSphereKey.Key ℤ) ×
      Lex (Certificate.CanonicalSphereKey.Key StereoLabel × Certificate.CanonicalSphereKey.Key StereoLabel)) :=
  toLex (ruleKey molecule graph W D node,
    toLex (rule4aComponent molecule graph evidence W D node,
      rule4cComponent molecule graph evidence W D node))

theorem ordinaryKey_lt_iff_rule4acKey
    (h : Rule4acOnly graph evidence) (W D : ℕ) (x y : graph.Node) :
    ordinaryKey molecule graph evidence W D x < ordinaryKey molecule graph evidence W D y ↔
      rule4acKey molecule graph evidence W D x < rule4acKey molecule graph evidence W D y := by
  have shape : ∀ {x y : graph.Node}, ruleKey molecule graph W D x = ruleKey molecule graph W D y →
      (ofLex (ordinaryKey molecule graph evidence W D x)).2.getD 0 [] =
          (ofLex (ordinaryKey molecule graph evidence W D y)).2.getD 0 [] ∧
        (ofLex (ordinaryKey molecule graph evidence W D x)).2.getD 2 [] =
          (ofLex (ordinaryKey molecule graph evidence W D y)).2.getD 2 [] ∧
        (ofLex (ordinaryKey molecule graph evidence W D x)).2.getD 4 [] =
          (ofLex (ordinaryKey molecule graph evidence W D y)).2.getD 4 [] := by
    intro x y heq
    exact ⟨botComponent_eq_of_ruleKey_eq molecule graph evidence .rule3DoubleBondGeometry
      (h _ (by decide) (by decide)) W D heq,
      botComponent_eq_of_ruleKey_eq molecule graph evidence .rule4bLikeUnlikeDescriptorPairs
      (h _ (by decide) (by decide)) W D heq,
      botComponent_eq_of_ruleKey_eq molecule graph evidence .rule5EnantiomorphicDescriptor
      (h _ (by decide) (by decide)) W D heq⟩
  unfold rule4acKey rule4aComponent rule4cComponent
  rw [← toLex_ofLex (ordinaryKey molecule graph evidence W D x),
    ← toLex_ofLex (ordinaryKey molecule graph evidence W D y), Prod.Lex.lt_iff, Prod.Lex.lt_iff]
  simp only [ofLex_toLex, ordinaryKey_fst]
  constructor
  · rintro (hlt | ⟨heq, hlt⟩)
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      obtain ⟨e0, e2, e4⟩ := shape heq
      rw [ordinaryKey_stereo_eq molecule graph evidence W D x,
        ordinaryKey_stereo_eq molecule graph evidence W D y, e0, cons_lt_cons_same,
        List.cons_lt_cons_iff] at hlt
      rw [Prod.Lex.lt_iff]
      rcases hlt with hlt | ⟨h1, hlt⟩
      · exact Or.inl hlt
      · refine Or.inr ⟨h1, ?_⟩
        rw [e2, cons_lt_cons_same, List.cons_lt_cons_iff] at hlt
        rcases hlt with hlt | ⟨_, hlt⟩
        · exact hlt
        · rw [e4] at hlt
          exact absurd hlt (lt_irrefl _)
  · rintro (hlt | ⟨heq, hlt⟩)
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      obtain ⟨e0, e2, _⟩ := shape heq
      rw [ordinaryKey_stereo_eq molecule graph evidence W D x,
        ordinaryKey_stereo_eq molecule graph evidence W D y, e0, cons_lt_cons_same,
        List.cons_lt_cons_iff]
      rw [Prod.Lex.lt_iff] at hlt
      rcases hlt with hlt | ⟨h1, hlt⟩
      · exact Or.inl hlt
      · refine Or.inr ⟨h1, ?_⟩
        rw [e2, cons_lt_cons_same, List.cons_lt_cons_iff]
        exact Or.inl hlt

theorem ordinaryKey_le_iff_rule4acKey
    (h : Rule4acOnly graph evidence) (W D : ℕ) (x y : graph.Node) :
    ordinaryKey molecule graph evidence W D x ≤ ordinaryKey molecule graph evidence W D y ↔
      rule4acKey molecule graph evidence W D x ≤ rule4acKey molecule graph evidence W D y := by
  rw [← not_lt, ← not_lt, ordinaryKey_lt_iff_rule4acKey molecule graph evidence h]

theorem ordinaryKey_eq_iff_rule4acKey
    (h : Rule4acOnly graph evidence) (W D : ℕ) (x y : graph.Node) :
    ordinaryKey molecule graph evidence W D x = ordinaryKey molecule graph evidence W D y ↔
      rule4acKey molecule graph evidence W D x = rule4acKey molecule graph evidence W D y := by
  constructor
  · intro equal
    apply le_antisymm
    · exact (ordinaryKey_le_iff_rule4acKey molecule graph evidence h W D x y).1 equal.le
    · exact (ordinaryKey_le_iff_rule4acKey molecule graph evidence h W D y x).1 equal.ge
  · intro equal
    apply le_antisymm
    · exact (ordinaryKey_le_iff_rule4acKey molecule graph evidence h W D x y).2 equal.le
    · exact (ordinaryKey_le_iff_rule4acKey molecule graph evidence h W D y x).2 equal.ge

end
end TetraStereo.OneCenter.DeclarativeCIP

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryKey_lt_iff_rule4abcKey
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryKey_le_iff_rule4abcKey
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryKey_eq_iff_rule4abcKey
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryKey_lt_iff_rule4acKey
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryKey_le_iff_rule4acKey
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryKey_eq_iff_rule4acKey
