import TetraStereo.OneCenter.DeclarativeCIPStereoPathObservation
import TetraStereo.OneCenter.DeclarativeCIPCanonicalOrder
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section

open scoped Classical

universe u

open Certificate.CanonicalSphereKey (Key WellShaped pathObservationOf)
open RootedDigraph

















section

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)
  (graph : RootedDigraph Atom) (evidence : StereochemicalEvidence graph)

local instance projectionNodeFintype : Fintype graph.Node := graph.nodeFintype

/-- Rule-4a-only evidence: every other stereochemical label is `⊥`. -/
def Rule4aOnly : Prop :=
  ∀ rule, rule ≠ StereochemicalRule.rule4aStereogenicUnitKind →
    ∀ node, stereoLabel graph evidence rule node = ⊥

/-! ## A sibling order descending for the ordinary key -/

local instance (W D : ℕ) : Std.Total (KeyDesc (ordinaryKey molecule graph evidence W D)) :=
  ⟨fun a b => le_total (ordinaryKey molecule graph evidence W D b)
    (ordinaryKey molecule graph evidence W D a)⟩

local instance (W D : ℕ) : IsTrans graph.Node (KeyDesc (ordinaryKey molecule graph evidence W D)) :=
  ⟨fun _ _ _ h₁ h₂ => le_trans h₂ h₁⟩

/-- Some permutation of the child list is descending for the ordinary key. -/
theorem exists_ordinaryRanked (W D : ℕ) (node : graph.Node) :
    ∃ ranked : List graph.Node, ranked.Perm (graph.childList node) ∧
      (ranked.map (ordinaryKey molecule graph evidence W D)).Pairwise fun x y => y ≤ x :=
  ⟨(graph.childList node).insertionSort (KeyDesc (ordinaryKey molecule graph evidence W D)),
    List.perm_insertionSort _ _,
    by
      rw [List.pairwise_map]
      exact List.pairwise_insertionSort (KeyDesc (ordinaryKey molecule graph evidence W D)) _⟩

/-- Descending for the ordinary key implies descending for the constitutional vector key. -/
theorem ruleKey_sorted_of_ordinary_sorted (W D : ℕ) {ranked : List graph.Node}
    (hsorted : (ranked.map (ordinaryKey molecule graph evidence W D)).Pairwise fun x y => y ≤ x) :
    (ranked.map (ruleKey molecule graph W D)).Pairwise fun x y => y ≤ x := by
  rw [List.pairwise_map] at hsorted ⊢
  refine hsorted.imp fun h => ?_
  have := fst_le_of_le h
  rwa [ordinaryKey_fst, ordinaryKey_fst] at this

/-! ## Components with `⊥` labels are shape keys -/

/-- A stereochemical component whose label is `⊥` everywhere observes `some ⊥` exactly where the
constitutional vector key observes a node. -/
theorem botComponent_pathObservation (rule : StereochemicalRule)
    (hbot : ∀ node, stereoLabel graph evidence rule node = ⊥) (W D : ℕ) :
    ∀ (path : List ℕ) (node : graph.Node),
      stereoNodePathObservation molecule graph evidence W D rule node path =
        (nodePathObservation molecule graph W D 0 node path).map
          (fun _ => (⊥ : StereoLabel))
  | [], node => by
      rw [stereoNodePathObservation_nil, hbot, nodePathObservation_nil molecule graph (by omega)]
      rfl
  | digit :: path, node => by
      obtain ⟨ranked, hperm, hsorted⟩ := exists_ordinaryRanked molecule graph evidence W D node
      rw [stereoNodePathObservation_cons molecule graph evidence W D rule node hperm hsorted,
        nodePathObservation_cons molecule graph (by omega) node hperm
          (ruleKey_sorted_of_ordinary_sorted molecule graph evidence W D hsorted)]
      by_cases hguard : digit < W ∧ path.length < D
      · rw [if_pos hguard, if_pos hguard]
        cases ranked[digit]? with
        | none => rfl
        | some child =>
            simp only [Option.map_some, Option.getD_some]
            exact botComponent_pathObservation rule hbot W D path child
      · rw [if_neg hguard, if_neg hguard]
        rfl

/-- Shape components are determined by the constitutional vector key. -/
theorem botComponent_eq_of_ruleKey_eq (rule : StereochemicalRule)
    (hbot : ∀ node, stereoLabel graph evidence rule node = ⊥) (W D : ℕ) {x y : graph.Node}
    (h : ruleKey molecule graph W D x = ruleKey molecule graph W D y) :
    (ofLex (ordinaryKey molecule graph evidence W D x)).2.getD (stereoIndex rule) [] =
      (ofLex (ordinaryKey molecule graph evidence W D y)).2.getD (stereoIndex rule) [] := by
  refine (Certificate.CanonicalSphereKey.key_eq_iff_pathObservation
    (ordinaryKey_stereo_wellShaped molecule graph evidence W D rule x)
    (ordinaryKey_stereo_wellShaped molecule graph evidence W D rule y)).2 ?_
  intro path
  change stereoNodePathObservation molecule graph evidence W D rule x path =
    stereoNodePathObservation molecule graph evidence W D rule y path
  rw [botComponent_pathObservation molecule graph evidence rule hbot W D path x,
    botComponent_pathObservation molecule graph evidence rule hbot W D path y]
  unfold nodePathObservation
  rw [h]

/-! ## The pair key -/

/-- The Rule-4a component of the ordinary key. -/
def rule4aComponent (W D : ℕ) (node : graph.Node) : Key StereoLabel :=
  (ofLex (ordinaryKey molecule graph evidence W D node)).2.getD
    (stereoIndex .rule4aStereogenicUnitKind) []

/-- The pair key: constitutional vector key, then the Rule-4a component. -/
def pairKey (W D : ℕ) (node : graph.Node) : Lex (List (Key ℤ) × Key StereoLabel) :=
  toLex (ruleKey molecule graph W D node, rule4aComponent molecule graph evidence W D node)

/-- The stereochemical vector of the ordinary key, written out. -/
theorem ordinaryKey_stereo_eq (W D : ℕ) (node : graph.Node) :
    (ofLex (ordinaryKey molecule graph evidence W D node)).2 =
      [(ofLex (ordinaryKey molecule graph evidence W D node)).2.getD 0 [],
       (ofLex (ordinaryKey molecule graph evidence W D node)).2.getD 1 [],
       (ofLex (ordinaryKey molecule graph evidence W D node)).2.getD 2 [],
       (ofLex (ordinaryKey molecule graph evidence W D node)).2.getD 3 [],
       (ofLex (ordinaryKey molecule graph evidence W D node)).2.getD 4 []] := by
  rw [ordinaryKey_eq]
  rfl

private theorem cons_lt_cons_same {α : Type*} [LinearOrder α] (a : α) (l m : List α) :
    a :: l < a :: m ↔ l < m := by
  rw [List.cons_lt_cons_iff]
  simp

/-- Under Rule-4a-only evidence the shape components of two constitutionally equal nodes agree. -/
theorem shapeComponents_eq (h4a : Rule4aOnly graph evidence) (W D : ℕ) {x y : graph.Node}
    (h : ruleKey molecule graph W D x = ruleKey molecule graph W D y) :
    (ofLex (ordinaryKey molecule graph evidence W D x)).2.getD 0 [] =
        (ofLex (ordinaryKey molecule graph evidence W D y)).2.getD 0 [] ∧
      (ofLex (ordinaryKey molecule graph evidence W D x)).2.getD 2 [] =
        (ofLex (ordinaryKey molecule graph evidence W D y)).2.getD 2 [] ∧
      (ofLex (ordinaryKey molecule graph evidence W D x)).2.getD 3 [] =
        (ofLex (ordinaryKey molecule graph evidence W D y)).2.getD 3 [] ∧
      (ofLex (ordinaryKey molecule graph evidence W D x)).2.getD 4 [] =
        (ofLex (ordinaryKey molecule graph evidence W D y)).2.getD 4 [] :=
  ⟨botComponent_eq_of_ruleKey_eq molecule graph evidence .rule3DoubleBondGeometry
      (h4a _ (by decide)) W D h,
    botComponent_eq_of_ruleKey_eq molecule graph evidence .rule4bLikeUnlikeDescriptorPairs
      (h4a _ (by decide)) W D h,
    botComponent_eq_of_ruleKey_eq molecule graph evidence .rule4cPseudoasymmetricDescriptor
      (h4a _ (by decide)) W D h,
    botComponent_eq_of_ruleKey_eq molecule graph evidence .rule5EnantiomorphicDescriptor
      (h4a _ (by decide)) W D h⟩

/-- **Strict order collapse.** -/
theorem ordinaryKey_lt_iff_pairKey (h4a : Rule4aOnly graph evidence) (W D : ℕ)
    (x y : graph.Node) :
    ordinaryKey molecule graph evidence W D x < ordinaryKey molecule graph evidence W D y ↔
      pairKey molecule graph evidence W D x < pairKey molecule graph evidence W D y := by
  unfold pairKey
  rw [← toLex_ofLex (ordinaryKey molecule graph evidence W D x),
    ← toLex_ofLex (ordinaryKey molecule graph evidence W D y), Prod.Lex.lt_iff, Prod.Lex.lt_iff]
  simp only [ofLex_toLex, ordinaryKey_fst]
  constructor
  · rintro (h | ⟨h, hlt⟩)
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      obtain ⟨e0, e2, e3, e4⟩ := shapeComponents_eq molecule graph evidence h4a W D h
      rw [ordinaryKey_stereo_eq molecule graph evidence W D x,
        ordinaryKey_stereo_eq molecule graph evidence W D y, e0, e2, e3, e4,
        cons_lt_cons_same, List.cons_lt_cons_iff] at hlt
      rcases hlt with hlt | ⟨_, hlt⟩
      · exact hlt
      · exact absurd hlt (lt_irrefl _)
  · rintro (h | ⟨h, hlt⟩)
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      obtain ⟨e0, e2, e3, e4⟩ := shapeComponents_eq molecule graph evidence h4a W D h
      rw [ordinaryKey_stereo_eq molecule graph evidence W D x,
        ordinaryKey_stereo_eq molecule graph evidence W D y, e0, e2, e3, e4,
        cons_lt_cons_same, List.cons_lt_cons_iff]
      exact Or.inl hlt

/-- **Equality collapse.** -/
theorem ordinaryKey_eq_iff_pairKey (h4a : Rule4aOnly graph evidence) (W D : ℕ)
    (x y : graph.Node) :
    ordinaryKey molecule graph evidence W D x = ordinaryKey molecule graph evidence W D y ↔
      pairKey molecule graph evidence W D x = pairKey molecule graph evidence W D y := by
  unfold pairKey rule4aComponent
  constructor
  · intro h
    have hfst := congrArg (fun k => (ofLex k).1) h
    have hsnd := congrArg (fun k => (ofLex k).2.getD (stereoIndex .rule4aStereogenicUnitKind) []) h
    simp only [ordinaryKey_fst] at hfst
    exact congrArg toLex (Prod.ext hfst hsnd)
  · intro h
    have hfst : ruleKey molecule graph W D x = ruleKey molecule graph W D y :=
      congrArg (fun k => (ofLex k).1) h
    have hsnd : (ofLex (ordinaryKey molecule graph evidence W D x)).2.getD 1 [] =
        (ofLex (ordinaryKey molecule graph evidence W D y)).2.getD 1 [] :=
      congrArg (fun k => (ofLex k).2) h
    obtain ⟨e0, e2, e3, e4⟩ := shapeComponents_eq molecule graph evidence h4a W D hfst
    rw [← toLex_ofLex (ordinaryKey molecule graph evidence W D x),
      ← toLex_ofLex (ordinaryKey molecule graph evidence W D y)]
    congr 1
    refine Prod.ext ?_ ?_
    · simpa only [ordinaryKey_fst] using hfst
    · rw [ordinaryKey_stereo_eq molecule graph evidence W D x,
        ordinaryKey_stereo_eq molecule graph evidence W D y, e0, e2, e3, e4, hsnd]

/-- **Weak order collapse.** -/
theorem ordinaryKey_le_iff_pairKey (h4a : Rule4aOnly graph evidence) (W D : ℕ)
    (x y : graph.Node) :
    ordinaryKey molecule graph evidence W D x ≤ ordinaryKey molecule graph evidence W D y ↔
      pairKey molecule graph evidence W D x ≤ pairKey molecule graph evidence W D y := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, ordinaryKey_lt_iff_pairKey molecule graph evidence h4a,
    ordinaryKey_eq_iff_pairKey molecule graph evidence h4a]

end

end
end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.botComponent_pathObservation
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.botComponent_eq_of_ruleKey_eq
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryKey_lt_iff_pairKey
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryKey_eq_iff_pairKey
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryKey_le_iff_pairKey
