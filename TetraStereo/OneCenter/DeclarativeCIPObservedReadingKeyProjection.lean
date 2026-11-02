import TetraStereo.OneCenter.DeclarativeCIPObservedKeyProjection
import TetraStereo.OneCenter.DeclarativeCIPRule4cReadingEvidence
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! Observer-parametric projections for the independent Rule-4b and Rule-4c reading keys.
Only the masked columns are removed from the ordinary key; active observations and their
whole recursively ranked components remain unchanged. -/

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section
open scoped Classical
universe u
open Certificate.CanonicalSphereKey (Key)

section Projection

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (graph : RootedDigraph Atom)
  (observe : ConstitutionalRule → graph.Node → ℤ)
  (evidence : StereochemicalEvidence graph)

local instance observedReadingProjectionNodeFintype : Fintype graph.Node := graph.nodeFintype

/-- Rule-4b component of the ordinary key under an independent constitutional observer. -/
def observedRule4bComponent (W D : ℕ) (node : graph.Node) : Key StereoLabel :=
  (ofLex (ordinaryKeyWithObservations graph observe evidence W D node)).2.getD
    (stereoIndex .rule4bLikeUnlikeDescriptorPairs) []

/-- Rule-4c component of the ordinary key under an independent constitutional observer. -/
def observedRule4cComponent (W D : ℕ) (node : graph.Node) : Key StereoLabel :=
  (ofLex (ordinaryKeyWithObservations graph observe evidence W D node)).2.getD
    (stereoIndex .rule4cPseudoasymmetricDescriptor) []

/-- The constitutional vector, then the whole Rule-4a and Rule-4b components. -/
def observedTripleKey (W D : ℕ) (node : graph.Node) :
    Lex (List (Key ℤ) × Lex (Key StereoLabel × Key StereoLabel)) :=
  toLex (ruleKeyWithObservations graph W D observe node,
    toLex (observedRule4aComponent graph observe evidence W D node,
      observedRule4bComponent graph observe evidence W D node))

/-- The constitutional vector followed by all active Rule-4a, Rule-4b and Rule-4c components. -/
def observedRule4abcKey (W D : ℕ) (node : graph.Node) :
    Lex (List (Key ℤ) × Lex (Key StereoLabel × Lex (Key StereoLabel × Key StereoLabel))) :=
  toLex (ruleKeyWithObservations graph W D observe node,
    toLex (observedRule4aComponent graph observe evidence W D node,
      toLex (observedRule4bComponent graph observe evidence W D node,
        observedRule4cComponent graph observe evidence W D node)))

/-- The no-reference projection keeps Rule 4a and Rule 4c, while Rule 4b is absent. -/
def observedRule4acKey (W D : ℕ) (node : graph.Node) :
    Lex (List (Key ℤ) × Lex (Key StereoLabel × Key StereoLabel)) :=
  toLex (ruleKeyWithObservations graph W D observe node,
    toLex (observedRule4aComponent graph observe evidence W D node,
      observedRule4cComponent graph observe evidence W D node))

omit [Fintype Atom] [DecidableEq Atom] in
theorem observedShapeComponents_eq_rule4ab (h : Rule4abOnly graph evidence)
    (W D : ℕ) {x y : graph.Node}
    (constitutionalEq : ruleKeyWithObservations graph W D observe x =
      ruleKeyWithObservations graph W D observe y) :
    (ofLex (ordinaryKeyWithObservations graph observe evidence W D x)).2.getD 0 [] =
        (ofLex (ordinaryKeyWithObservations graph observe evidence W D y)).2.getD 0 [] ∧
      (ofLex (ordinaryKeyWithObservations graph observe evidence W D x)).2.getD 3 [] =
        (ofLex (ordinaryKeyWithObservations graph observe evidence W D y)).2.getD 3 [] ∧
      (ofLex (ordinaryKeyWithObservations graph observe evidence W D x)).2.getD 4 [] =
        (ofLex (ordinaryKeyWithObservations graph observe evidence W D y)).2.getD 4 [] := by
  exact ⟨observedBotComponent_eq_of_ruleKey_eq graph observe evidence
      .rule3DoubleBondGeometry (h _ (by decide) (by decide)) W D constitutionalEq,
    observedBotComponent_eq_of_ruleKey_eq graph observe evidence
      .rule4cPseudoasymmetricDescriptor (h _ (by decide) (by decide)) W D constitutionalEq,
    observedBotComponent_eq_of_ruleKey_eq graph observe evidence
      .rule5EnantiomorphicDescriptor (h _ (by decide) (by decide)) W D constitutionalEq⟩

omit [Fintype Atom] [DecidableEq Atom] in
theorem observedShapeComponents_eq_rule4abc (h : Rule4abcOnly graph evidence)
    (W D : ℕ) {x y : graph.Node}
    (constitutionalEq : ruleKeyWithObservations graph W D observe x =
      ruleKeyWithObservations graph W D observe y) :
    (ofLex (ordinaryKeyWithObservations graph observe evidence W D x)).2.getD 0 [] =
        (ofLex (ordinaryKeyWithObservations graph observe evidence W D y)).2.getD 0 [] ∧
      (ofLex (ordinaryKeyWithObservations graph observe evidence W D x)).2.getD 4 [] =
        (ofLex (ordinaryKeyWithObservations graph observe evidence W D y)).2.getD 4 [] := by
  exact ⟨observedBotComponent_eq_of_ruleKey_eq graph observe evidence
      .rule3DoubleBondGeometry (h _ (by decide) (by decide) (by decide)) W D constitutionalEq,
    observedBotComponent_eq_of_ruleKey_eq graph observe evidence
      .rule5EnantiomorphicDescriptor (h _ (by decide) (by decide) (by decide)) W D constitutionalEq⟩

omit [Fintype Atom] [DecidableEq Atom] in
theorem observedShapeComponents_eq_rule4ac (h : Rule4acOnly graph evidence)
    (W D : ℕ) {x y : graph.Node}
    (constitutionalEq : ruleKeyWithObservations graph W D observe x =
      ruleKeyWithObservations graph W D observe y) :
    (ofLex (ordinaryKeyWithObservations graph observe evidence W D x)).2.getD 0 [] =
        (ofLex (ordinaryKeyWithObservations graph observe evidence W D y)).2.getD 0 [] ∧
      (ofLex (ordinaryKeyWithObservations graph observe evidence W D x)).2.getD 2 [] =
        (ofLex (ordinaryKeyWithObservations graph observe evidence W D y)).2.getD 2 [] ∧
      (ofLex (ordinaryKeyWithObservations graph observe evidence W D x)).2.getD 4 [] =
        (ofLex (ordinaryKeyWithObservations graph observe evidence W D y)).2.getD 4 [] := by
  exact ⟨observedBotComponent_eq_of_ruleKey_eq graph observe evidence
      .rule3DoubleBondGeometry (h _ (by decide) (by decide)) W D constitutionalEq,
    observedBotComponent_eq_of_ruleKey_eq graph observe evidence
      .rule4bLikeUnlikeDescriptorPairs (h _ (by decide) (by decide)) W D constitutionalEq,
    observedBotComponent_eq_of_ruleKey_eq graph observe evidence
      .rule5EnantiomorphicDescriptor (h _ (by decide) (by decide)) W D constitutionalEq⟩

private theorem observed_cons_lt_cons_same {α : Type*} [LinearOrder α]
    (a : α) (l m : List α) : a :: l < a :: m ↔ l < m := by
  rw [List.cons_lt_cons_iff]
  simp

omit [Fintype Atom] [DecidableEq Atom] in
theorem observedOrdinaryKey_lt_iff_tripleKey (h : Rule4abOnly graph evidence)
    (W D : ℕ) (x y : graph.Node) :
    ordinaryKeyWithObservations graph observe evidence W D x <
        ordinaryKeyWithObservations graph observe evidence W D y ↔
      observedTripleKey graph observe evidence W D x <
        observedTripleKey graph observe evidence W D y := by
  unfold observedTripleKey observedRule4bComponent
  rw [← toLex_ofLex (ordinaryKeyWithObservations graph observe evidence W D x),
    ← toLex_ofLex (ordinaryKeyWithObservations graph observe evidence W D y),
    Prod.Lex.lt_iff, Prod.Lex.lt_iff]
  simp only [ofLex_toLex, ordinaryKeyWithObservations_fst]
  constructor
  · rintro (hlt | ⟨heq, hlt⟩)
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      obtain ⟨e0, e3, e4⟩ := observedShapeComponents_eq_rule4ab graph observe evidence h W D heq
      rw [ordinaryKeyWithObservations_stereo_eq graph observe evidence W D x,
        ordinaryKeyWithObservations_stereo_eq graph observe evidence W D y,
        e0, observed_cons_lt_cons_same, List.cons_lt_cons_iff] at hlt
      rw [Prod.Lex.lt_iff]
      rcases hlt with hlt | ⟨h1, hlt⟩
      · exact Or.inl hlt
      · refine Or.inr ⟨h1, ?_⟩
        rw [List.cons_lt_cons_iff] at hlt
        rcases hlt with hlt | ⟨_, hlt⟩
        · exact hlt
        · rw [e3, e4] at hlt
          exact absurd hlt (lt_irrefl _)
  · rintro (hlt | ⟨heq, hlt⟩)
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      obtain ⟨e0, e3, _⟩ := observedShapeComponents_eq_rule4ab graph observe evidence h W D heq
      rw [ordinaryKeyWithObservations_stereo_eq graph observe evidence W D x,
        ordinaryKeyWithObservations_stereo_eq graph observe evidence W D y,
        e0, observed_cons_lt_cons_same, List.cons_lt_cons_iff]
      rw [Prod.Lex.lt_iff] at hlt
      rcases hlt with hlt | ⟨h1, hlt⟩
      · exact Or.inl hlt
      · exact Or.inr ⟨h1, List.cons_lt_cons_iff.2 (Or.inl hlt)⟩

omit [Fintype Atom] [DecidableEq Atom] in
theorem observedOrdinaryKey_eq_iff_tripleKey (h : Rule4abOnly graph evidence)
    (W D : ℕ) (x y : graph.Node) :
    ordinaryKeyWithObservations graph observe evidence W D x =
        ordinaryKeyWithObservations graph observe evidence W D y ↔
      observedTripleKey graph observe evidence W D x =
        observedTripleKey graph observe evidence W D y := by
  unfold observedTripleKey observedRule4aComponent observedRule4bComponent
  constructor
  · intro heq
    have hfst := congrArg (fun key => (ofLex key).1) heq
    have h4a := congrArg (fun key =>
      (ofLex key).2.getD (stereoIndex .rule4aStereogenicUnitKind) []) heq
    have h4b := congrArg (fun key =>
      (ofLex key).2.getD (stereoIndex .rule4bLikeUnlikeDescriptorPairs) []) heq
    simp only [ordinaryKeyWithObservations_fst] at hfst
    exact congrArg toLex (Prod.ext hfst (congrArg toLex (Prod.ext h4a h4b)))
  · intro heq
    have hpair := congrArg ofLex heq
    simp only [ofLex_toLex] at hpair
    have hfst := congrArg Prod.fst hpair
    have htail := congrArg Prod.snd hpair
    have htailPair := congrArg ofLex htail
    simp only [ofLex_toLex] at htailPair
    have h4a := congrArg Prod.fst htailPair
    have h4b := congrArg Prod.snd htailPair
    change (ofLex (ordinaryKeyWithObservations graph observe evidence W D x)).2.getD
        1 [] =
      (ofLex (ordinaryKeyWithObservations graph observe evidence W D y)).2.getD
        1 [] at h4a
    change (ofLex (ordinaryKeyWithObservations graph observe evidence W D x)).2.getD
        2 [] =
      (ofLex (ordinaryKeyWithObservations graph observe evidence W D y)).2.getD
        2 [] at h4b
    obtain ⟨e0, e3, e4⟩ := observedShapeComponents_eq_rule4ab graph observe evidence h W D hfst
    rw [← toLex_ofLex (ordinaryKeyWithObservations graph observe evidence W D x),
      ← toLex_ofLex (ordinaryKeyWithObservations graph observe evidence W D y)]
    congr 1
    refine Prod.ext ?_ ?_
    · simpa only [ordinaryKeyWithObservations_fst] using hfst
    · rw [ordinaryKeyWithObservations_stereo_eq graph observe evidence W D x,
        ordinaryKeyWithObservations_stereo_eq graph observe evidence W D y,
        e0, e3, e4, h4a, h4b]

omit [Fintype Atom] [DecidableEq Atom] in
theorem observedOrdinaryKey_le_iff_tripleKey (h : Rule4abOnly graph evidence)
    (W D : ℕ) (x y : graph.Node) :
    ordinaryKeyWithObservations graph observe evidence W D x ≤
        ordinaryKeyWithObservations graph observe evidence W D y ↔
      observedTripleKey graph observe evidence W D x ≤
        observedTripleKey graph observe evidence W D y := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq,
    observedOrdinaryKey_lt_iff_tripleKey graph observe evidence h,
    observedOrdinaryKey_eq_iff_tripleKey graph observe evidence h]

omit [Fintype Atom] [DecidableEq Atom] in
theorem observedOrdinaryKey_lt_iff_rule4abcKey (h : Rule4abcOnly graph evidence)
    (W D : ℕ) (x y : graph.Node) :
    ordinaryKeyWithObservations graph observe evidence W D x <
        ordinaryKeyWithObservations graph observe evidence W D y ↔
      observedRule4abcKey graph observe evidence W D x <
        observedRule4abcKey graph observe evidence W D y := by
  unfold observedRule4abcKey observedRule4bComponent observedRule4cComponent
  rw [← toLex_ofLex (ordinaryKeyWithObservations graph observe evidence W D x),
    ← toLex_ofLex (ordinaryKeyWithObservations graph observe evidence W D y),
    Prod.Lex.lt_iff, Prod.Lex.lt_iff]
  simp only [ofLex_toLex, ordinaryKeyWithObservations_fst]
  constructor
  · rintro (hlt | ⟨heq, hlt⟩)
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      obtain ⟨e0, e4⟩ := observedShapeComponents_eq_rule4abc graph observe evidence h W D heq
      rw [ordinaryKeyWithObservations_stereo_eq graph observe evidence W D x,
        ordinaryKeyWithObservations_stereo_eq graph observe evidence W D y,
        e0, observed_cons_lt_cons_same, List.cons_lt_cons_iff] at hlt
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
      obtain ⟨e0, _⟩ := observedShapeComponents_eq_rule4abc graph observe evidence h W D heq
      rw [ordinaryKeyWithObservations_stereo_eq graph observe evidence W D x,
        ordinaryKeyWithObservations_stereo_eq graph observe evidence W D y,
        e0, observed_cons_lt_cons_same, List.cons_lt_cons_iff]
      rw [Prod.Lex.lt_iff] at hlt
      rcases hlt with hlt | ⟨h1, hlt⟩
      · exact Or.inl hlt
      · refine Or.inr ⟨h1, ?_⟩
        rw [List.cons_lt_cons_iff]
        rw [Prod.Lex.lt_iff] at hlt
        rcases hlt with hlt | ⟨h2, hlt⟩
        · exact Or.inl hlt
        · exact Or.inr ⟨h2, List.cons_lt_cons_iff.2 (Or.inl hlt)⟩

omit [Fintype Atom] [DecidableEq Atom] in
theorem observedOrdinaryKey_eq_iff_rule4abcKey (h : Rule4abcOnly graph evidence)
    (W D : ℕ) (x y : graph.Node) :
    ordinaryKeyWithObservations graph observe evidence W D x =
        ordinaryKeyWithObservations graph observe evidence W D y ↔
      observedRule4abcKey graph observe evidence W D x =
        observedRule4abcKey graph observe evidence W D y := by
  unfold observedRule4abcKey observedRule4aComponent observedRule4bComponent
    observedRule4cComponent
  constructor
  · intro heq
    have hfst := congrArg (fun key => (ofLex key).1) heq
    have h4a := congrArg (fun key =>
      (ofLex key).2.getD (stereoIndex .rule4aStereogenicUnitKind) []) heq
    have h4b := congrArg (fun key =>
      (ofLex key).2.getD (stereoIndex .rule4bLikeUnlikeDescriptorPairs) []) heq
    have h4c := congrArg (fun key =>
      (ofLex key).2.getD (stereoIndex .rule4cPseudoasymmetricDescriptor) []) heq
    simp only [ordinaryKeyWithObservations_fst] at hfst
    exact congrArg toLex
      (Prod.ext hfst (congrArg toLex (Prod.ext h4a (congrArg toLex (Prod.ext h4b h4c)))) )
  · intro heq
    have hpair := congrArg ofLex heq
    simp only [ofLex_toLex] at hpair
    have hfst := congrArg Prod.fst hpair
    have htail := congrArg Prod.snd hpair
    have htailPair := congrArg ofLex htail
    simp only [ofLex_toLex] at htailPair
    have h4a := congrArg Prod.fst htailPair
    have hbcKey := congrArg Prod.snd htailPair
    change (ofLex (ordinaryKeyWithObservations graph observe evidence W D x)).2.getD
        1 [] =
      (ofLex (ordinaryKeyWithObservations graph observe evidence W D y)).2.getD
        1 [] at h4a
    have hbc := congrArg ofLex hbcKey
    simp only [ofLex_toLex] at hbc
    have h4b := congrArg Prod.fst hbc
    have h4c := congrArg Prod.snd hbc
    change (ofLex (ordinaryKeyWithObservations graph observe evidence W D x)).2.getD
        2 [] =
      (ofLex (ordinaryKeyWithObservations graph observe evidence W D y)).2.getD
        2 [] at h4b
    change (ofLex (ordinaryKeyWithObservations graph observe evidence W D x)).2.getD
        3 [] =
      (ofLex (ordinaryKeyWithObservations graph observe evidence W D y)).2.getD
        3 [] at h4c
    obtain ⟨e0, e4⟩ := observedShapeComponents_eq_rule4abc graph observe evidence h W D hfst
    rw [← toLex_ofLex (ordinaryKeyWithObservations graph observe evidence W D x),
      ← toLex_ofLex (ordinaryKeyWithObservations graph observe evidence W D y)]
    congr 1
    refine Prod.ext ?_ ?_
    · simpa only [ordinaryKeyWithObservations_fst] using hfst
    · rw [ordinaryKeyWithObservations_stereo_eq graph observe evidence W D x,
        ordinaryKeyWithObservations_stereo_eq graph observe evidence W D y,
        e0, e4, h4a, h4b, h4c]

omit [Fintype Atom] [DecidableEq Atom] in
theorem observedOrdinaryKey_le_iff_rule4abcKey (h : Rule4abcOnly graph evidence)
    (W D : ℕ) (x y : graph.Node) :
    ordinaryKeyWithObservations graph observe evidence W D x ≤
        ordinaryKeyWithObservations graph observe evidence W D y ↔
      observedRule4abcKey graph observe evidence W D x ≤
        observedRule4abcKey graph observe evidence W D y := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq,
    observedOrdinaryKey_lt_iff_rule4abcKey graph observe evidence h,
    observedOrdinaryKey_eq_iff_rule4abcKey graph observe evidence h]

omit [Fintype Atom] [DecidableEq Atom] in
theorem observedOrdinaryKey_lt_iff_rule4acKey (h : Rule4acOnly graph evidence)
    (W D : ℕ) (x y : graph.Node) :
    ordinaryKeyWithObservations graph observe evidence W D x <
        ordinaryKeyWithObservations graph observe evidence W D y ↔
      observedRule4acKey graph observe evidence W D x <
        observedRule4acKey graph observe evidence W D y := by
  unfold observedRule4acKey observedRule4cComponent
  rw [← toLex_ofLex (ordinaryKeyWithObservations graph observe evidence W D x),
    ← toLex_ofLex (ordinaryKeyWithObservations graph observe evidence W D y),
    Prod.Lex.lt_iff, Prod.Lex.lt_iff]
  simp only [ofLex_toLex, ordinaryKeyWithObservations_fst]
  constructor
  · rintro (hlt | ⟨heq, hlt⟩)
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      obtain ⟨e0, e2, e4⟩ := observedShapeComponents_eq_rule4ac graph observe evidence h W D heq
      rw [ordinaryKeyWithObservations_stereo_eq graph observe evidence W D x,
        ordinaryKeyWithObservations_stereo_eq graph observe evidence W D y,
        e0, observed_cons_lt_cons_same, List.cons_lt_cons_iff] at hlt
      rw [Prod.Lex.lt_iff]
      rcases hlt with hlt | ⟨h1, hlt⟩
      · exact Or.inl hlt
      · refine Or.inr ⟨h1, ?_⟩
        rw [e2, observed_cons_lt_cons_same, List.cons_lt_cons_iff] at hlt
        rcases hlt with hlt | ⟨_, hlt⟩
        · exact hlt
        · rw [e4] at hlt
          exact absurd hlt (lt_irrefl _)
  · rintro (hlt | ⟨heq, hlt⟩)
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      obtain ⟨e0, e2, _⟩ := observedShapeComponents_eq_rule4ac graph observe evidence h W D heq
      rw [ordinaryKeyWithObservations_stereo_eq graph observe evidence W D x,
        ordinaryKeyWithObservations_stereo_eq graph observe evidence W D y,
        e0, observed_cons_lt_cons_same, List.cons_lt_cons_iff]
      rw [Prod.Lex.lt_iff] at hlt
      rcases hlt with hlt | ⟨h1, hlt⟩
      · exact Or.inl hlt
      · refine Or.inr ⟨h1, ?_⟩
        rw [e2, observed_cons_lt_cons_same, List.cons_lt_cons_iff]
        exact Or.inl hlt

omit [Fintype Atom] [DecidableEq Atom] in
theorem observedOrdinaryKey_eq_iff_rule4acKey (h : Rule4acOnly graph evidence)
    (W D : ℕ) (x y : graph.Node) :
    ordinaryKeyWithObservations graph observe evidence W D x =
        ordinaryKeyWithObservations graph observe evidence W D y ↔
      observedRule4acKey graph observe evidence W D x =
        observedRule4acKey graph observe evidence W D y := by
  unfold observedRule4acKey observedRule4aComponent observedRule4cComponent
  constructor
  · intro heq
    have hfst := congrArg (fun key => (ofLex key).1) heq
    have h4a := congrArg (fun key =>
      (ofLex key).2.getD (stereoIndex .rule4aStereogenicUnitKind) []) heq
    have h4c := congrArg (fun key =>
      (ofLex key).2.getD (stereoIndex .rule4cPseudoasymmetricDescriptor) []) heq
    simp only [ordinaryKeyWithObservations_fst] at hfst
    exact congrArg toLex (Prod.ext hfst (congrArg toLex (Prod.ext h4a h4c)))
  · intro heq
    have hpair := congrArg ofLex heq
    simp only [ofLex_toLex] at hpair
    have hfst := congrArg Prod.fst hpair
    have htail := congrArg Prod.snd hpair
    have htailPair := congrArg ofLex htail
    simp only [ofLex_toLex] at htailPair
    have h4a := congrArg Prod.fst htailPair
    have h4c := congrArg Prod.snd htailPair
    change (ofLex (ordinaryKeyWithObservations graph observe evidence W D x)).2.getD
        1 [] =
      (ofLex (ordinaryKeyWithObservations graph observe evidence W D y)).2.getD
        1 [] at h4a
    change (ofLex (ordinaryKeyWithObservations graph observe evidence W D x)).2.getD
        3 [] =
      (ofLex (ordinaryKeyWithObservations graph observe evidence W D y)).2.getD
        3 [] at h4c
    obtain ⟨e0, e2, e4⟩ := observedShapeComponents_eq_rule4ac graph observe evidence h W D hfst
    rw [← toLex_ofLex (ordinaryKeyWithObservations graph observe evidence W D x),
      ← toLex_ofLex (ordinaryKeyWithObservations graph observe evidence W D y)]
    congr 1
    refine Prod.ext ?_ ?_
    · simpa only [ordinaryKeyWithObservations_fst] using hfst
    · rw [ordinaryKeyWithObservations_stereo_eq graph observe evidence W D x,
        ordinaryKeyWithObservations_stereo_eq graph observe evidence W D y,
        e0, e2, e4, h4a, h4c]

omit [Fintype Atom] [DecidableEq Atom] in
theorem observedOrdinaryKey_le_iff_rule4acKey (h : Rule4acOnly graph evidence)
    (W D : ℕ) (x y : graph.Node) :
    ordinaryKeyWithObservations graph observe evidence W D x ≤
        ordinaryKeyWithObservations graph observe evidence W D y ↔
      observedRule4acKey graph observe evidence W D x ≤
        observedRule4acKey graph observe evidence W D y := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq,
    observedOrdinaryKey_lt_iff_rule4acKey graph observe evidence h,
    observedOrdinaryKey_eq_iff_rule4acKey graph observe evidence h]

end Projection

end
end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedShapeComponents_eq_rule4ab
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedShapeComponents_eq_rule4abc
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedShapeComponents_eq_rule4ac
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedOrdinaryKey_lt_iff_tripleKey
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedOrdinaryKey_eq_iff_tripleKey
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedOrdinaryKey_le_iff_tripleKey
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedOrdinaryKey_lt_iff_rule4abcKey
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedOrdinaryKey_eq_iff_rule4abcKey
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedOrdinaryKey_le_iff_rule4abcKey
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedOrdinaryKey_lt_iff_rule4acKey
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedOrdinaryKey_eq_iff_rule4acKey
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedOrdinaryKey_le_iff_rule4acKey
