import TetraStereo.OneCenter.DeclarativeCIPRankKeyProjection
import TetraStereo.OneCenter.DeclarativeCIPMolecularReferenceSelection
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# The ordinary key under Rules 4a and 4b only

`readingEvidence ρ` carries Rule-3, Rule-4a and Rule-4b observations and masks Rules 4c and 5; on
single-bond inputs Rule 3 observes nothing.  Under such evidence the ordinary key order collapses
to the lexicographic order of the triple (constitutional vector, Rule-4a component, Rule-4b
component), exactly as `DeclarativeCIPRankKeyProjection` collapses it to a pair under Rule-4a-only
evidence.
-/

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

universe u

noncomputable section
open scoped Classical
open Certificate.CanonicalSphereKey (Key)

section Projection

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)
  (graph : RootedDigraph Atom) (evidence : StereochemicalEvidence graph)

local instance readingProjectionNodeFintype : Fintype graph.Node := graph.nodeFintype

/-- Evidence observing at most Rules 4a and 4b. -/
def Rule4abOnly : Prop :=
  ∀ rule, rule ≠ StereochemicalRule.rule4aStereogenicUnitKind →
    rule ≠ StereochemicalRule.rule4bLikeUnlikeDescriptorPairs →
      ∀ node, stereoLabel graph evidence rule node = ⊥

/-- The Rule-4b component of the ordinary key. -/
def rule4bComponent (W D : ℕ) (node : graph.Node) : Key StereoLabel :=
  (ofLex (ordinaryKey molecule graph evidence W D node)).2.getD
    (stereoIndex .rule4bLikeUnlikeDescriptorPairs) []

/-- The triple key: constitutional vector, then the Rule-4a and Rule-4b components. -/
def tripleKey (W D : ℕ) (node : graph.Node) :
    Lex (List (Key ℤ) × Lex (Key StereoLabel × Key StereoLabel)) :=
  toLex (ruleKey molecule graph W D node,
    toLex (rule4aComponent molecule graph evidence W D node,
      rule4bComponent molecule graph evidence W D node))

private theorem cons_lt_cons_same {α : Type*} [LinearOrder α] (a : α) (l m : List α) :
    a :: l < a :: m ↔ l < m := by
  rw [List.cons_lt_cons_iff]
  simp

theorem shapeComponents_eq_rule4ab (h : Rule4abOnly graph evidence) (W D : ℕ) {x y : graph.Node}
    (hrule : ruleKey molecule graph W D x = ruleKey molecule graph W D y) :
    (ofLex (ordinaryKey molecule graph evidence W D x)).2.getD 0 [] =
        (ofLex (ordinaryKey molecule graph evidence W D y)).2.getD 0 [] ∧
      (ofLex (ordinaryKey molecule graph evidence W D x)).2.getD 3 [] =
        (ofLex (ordinaryKey molecule graph evidence W D y)).2.getD 3 [] ∧
      (ofLex (ordinaryKey molecule graph evidence W D x)).2.getD 4 [] =
        (ofLex (ordinaryKey molecule graph evidence W D y)).2.getD 4 [] :=
  ⟨botComponent_eq_of_ruleKey_eq molecule graph evidence .rule3DoubleBondGeometry
      (h _ (by decide) (by decide)) W D hrule,
    botComponent_eq_of_ruleKey_eq molecule graph evidence .rule4cPseudoasymmetricDescriptor
      (h _ (by decide) (by decide)) W D hrule,
    botComponent_eq_of_ruleKey_eq molecule graph evidence .rule5EnantiomorphicDescriptor
      (h _ (by decide) (by decide)) W D hrule⟩

/-- **Strict order collapse** under Rules 4a/4b. -/
theorem ordinaryKey_lt_iff_tripleKey (h : Rule4abOnly graph evidence) (W D : ℕ)
    (x y : graph.Node) :
    ordinaryKey molecule graph evidence W D x < ordinaryKey molecule graph evidence W D y ↔
      tripleKey molecule graph evidence W D x < tripleKey molecule graph evidence W D y := by
  unfold tripleKey rule4aComponent rule4bComponent
  rw [← toLex_ofLex (ordinaryKey molecule graph evidence W D x),
    ← toLex_ofLex (ordinaryKey molecule graph evidence W D y), Prod.Lex.lt_iff, Prod.Lex.lt_iff]
  simp only [ofLex_toLex, ordinaryKey_fst]
  constructor
  · rintro (hlt | ⟨heq, hlt⟩)
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      obtain ⟨e0, e3, e4⟩ := shapeComponents_eq_rule4ab molecule graph evidence h W D heq
      rw [ordinaryKey_stereo_eq molecule graph evidence W D x,
        ordinaryKey_stereo_eq molecule graph evidence W D y, e0, cons_lt_cons_same,
        List.cons_lt_cons_iff] at hlt
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
      obtain ⟨e0, e3, e4⟩ := shapeComponents_eq_rule4ab molecule graph evidence h W D heq
      rw [ordinaryKey_stereo_eq molecule graph evidence W D x,
        ordinaryKey_stereo_eq molecule graph evidence W D y, e0, cons_lt_cons_same,
        List.cons_lt_cons_iff]
      rw [Prod.Lex.lt_iff] at hlt
      rcases hlt with hlt | ⟨h1, hlt⟩
      · exact Or.inl hlt
      · exact Or.inr ⟨h1, List.cons_lt_cons_iff.2 (Or.inl hlt)⟩

/-- **Equality collapse** under Rules 4a/4b. -/
theorem ordinaryKey_eq_iff_tripleKey (h : Rule4abOnly graph evidence) (W D : ℕ)
    (x y : graph.Node) :
    ordinaryKey molecule graph evidence W D x = ordinaryKey molecule graph evidence W D y ↔
      tripleKey molecule graph evidence W D x = tripleKey molecule graph evidence W D y := by
  unfold tripleKey rule4aComponent rule4bComponent
  constructor
  · intro heq
    have hfst := congrArg (fun k => (ofLex k).1) heq
    have h4a := congrArg (fun k => (ofLex k).2.getD (stereoIndex .rule4aStereogenicUnitKind) []) heq
    have h4b := congrArg (fun k => (ofLex k).2.getD (stereoIndex .rule4bLikeUnlikeDescriptorPairs) [])
      heq
    simp only [ordinaryKey_fst] at hfst
    exact congrArg toLex (Prod.ext hfst (congrArg toLex (Prod.ext h4a h4b)))
  · intro heq
    have hpair := congrArg ofLex heq
    have hfst : ruleKey molecule graph W D x = ruleKey molecule graph W D y := congrArg Prod.fst hpair
    have hsnd := congrArg (fun p => ofLex p.2) hpair
    have h4a : (ofLex (ordinaryKey molecule graph evidence W D x)).2.getD 1 [] =
        (ofLex (ordinaryKey molecule graph evidence W D y)).2.getD 1 [] := congrArg Prod.fst hsnd
    have h4b : (ofLex (ordinaryKey molecule graph evidence W D x)).2.getD 2 [] =
        (ofLex (ordinaryKey molecule graph evidence W D y)).2.getD 2 [] := congrArg Prod.snd hsnd
    obtain ⟨e0, e3, e4⟩ := shapeComponents_eq_rule4ab molecule graph evidence h W D hfst
    rw [← toLex_ofLex (ordinaryKey molecule graph evidence W D x),
      ← toLex_ofLex (ordinaryKey molecule graph evidence W D y)]
    congr 1
    refine Prod.ext ?_ ?_
    · simpa only [ordinaryKey_fst] using hfst
    · rw [ordinaryKey_stereo_eq molecule graph evidence W D x,
        ordinaryKey_stereo_eq molecule graph evidence W D y, e0, e3, e4, h4a, h4b]

/-- **Weak order collapse** under Rules 4a/4b. -/
theorem ordinaryKey_le_iff_tripleKey (h : Rule4abOnly graph evidence) (W D : ℕ)
    (x y : graph.Node) :
    ordinaryKey molecule graph evidence W D x ≤ ordinaryKey molecule graph evidence W D y ↔
      tripleKey molecule graph evidence W D x ≤ tripleKey molecule graph evidence W D y := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, ordinaryKey_lt_iff_tripleKey molecule graph evidence h,
    ordinaryKey_eq_iff_tripleKey molecule graph evidence h]

end Projection

/-! ## The reading evidence observes only Rules 4a and 4b on single-bond inputs -/

section Molecular

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

theorem rule4abOnly_readingEvidence_of_single (hsingle : ∀ atom other, molecule.bond atom other ≤ 1)
    (reference : DescriptorSense) :
    Rule4abOnly graph (readingEvidence molecule descriptorMap unit graph reference) := by
  intro rule h4a h4b node
  cases rule with
  | rule4aStereogenicUnitKind => exact absurd rfl h4a
  | rule4bLikeUnlikeDescriptorPairs => exact absurd rfl h4b
  | rule3DoubleBondGeometry =>
      have hrule3 := molecularEvidence_rule3_eq_none molecule hsingle descriptorMap unit graph node
      change rule3Observation molecule descriptorMap unit graph node = none at hrule3
      show stereoValue .rule3DoubleBondGeometry (some (readingEvidence _ _ _ _ reference node)) = ⊥
      simp [stereoValue, readingEvidence, hrule3, liftObservation]
  | rule4cPseudoasymmetricDescriptor => rfl
  | rule5EnantiomorphicDescriptor => rfl

/-- The Rule-4a observation does not depend on the reference. -/
theorem readingEvidence_rule4a (reference : DescriptorSense) (node : graph.Node) :
    (readingEvidence molecule descriptorMap unit graph reference node).rule4a =
      (rankEvidence molecule descriptorMap unit graph node).rule4a := rfl

end Molecular

end
end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryKey_le_iff_tripleKey
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.rule4abOnly_readingEvidence_of_single
