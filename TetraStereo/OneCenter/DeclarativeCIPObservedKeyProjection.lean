import TetraStereo.OneCenter.DeclarativeCIPObservedStereoPath
import TetraStereo.OneCenter.DeclarativeCIPObservedCanonicalOrder
import TetraStereo.OneCenter.DeclarativeCIPObservedOrdinaryKey
import TetraStereo.OneCenter.DeclarativeCIPRankKeyProjection
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section
open scoped Classical
universe u
open Certificate.CanonicalSphereKey (Key WellShaped)

section ObservedProjection

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (graph : RootedDigraph Atom)
  (observe : ConstitutionalRule → graph.Node → ℤ)
  (evidence : StereochemicalEvidence graph)

local instance observedProjectionNodeFintype : Fintype graph.Node := graph.nodeFintype

/-- Rule-4a component of the ordinary key with an independent constitutional observer. -/
def observedRule4aComponent (W D : ℕ) (node : graph.Node) : Key StereoLabel :=
  (ofLex (ordinaryKeyWithObservations graph observe evidence W D node)).2.getD
    (stereoIndex .rule4aStereogenicUnitKind) []

/-- Pair key consisting of the generic constitutional vector and Rule-4a component. -/
def observedPairKey (W D : ℕ) (node : graph.Node) :
    Lex (List (Key ℤ) × Key StereoLabel) :=
  toLex (ruleKeyWithObservations graph W D observe node,
    observedRule4aComponent graph observe evidence W D node)

omit [Fintype Atom] [DecidableEq Atom] in
/-- Some permutation of children is descending for the observed ordinary key. -/
theorem exists_observedOrdinaryRanked (W D : ℕ) (node : graph.Node) :
    ∃ ranked : List graph.Node, ranked.Perm (graph.childList node) ∧
      (ranked.map (ordinaryKeyWithObservations graph observe evidence W D)).Pairwise
        fun x y => y ≤ x := by
  exact ⟨(graph.childList node).insertionSort
      (KeyDesc (ordinaryKeyWithObservations graph observe evidence W D)),
    List.perm_insertionSort _ _, by
      rw [List.pairwise_map]
      exact List.pairwise_insertionSort
        (KeyDesc (ordinaryKeyWithObservations graph observe evidence W D)) _⟩

omit [Fintype Atom] [DecidableEq Atom] in
/-- Descending for the observed ordinary key implies descending for its constitutional prefix. -/
theorem observedRuleKey_sorted_of_ordinary_sorted (W D : ℕ) {ranked : List graph.Node}
    (hsorted : (ranked.map (ordinaryKeyWithObservations graph observe evidence W D)).Pairwise
      fun x y => y ≤ x) :
    (ranked.map (ruleKeyWithObservations graph W D observe)).Pairwise fun x y => y ≤ x := by
  rw [List.pairwise_map] at hsorted ⊢
  refine hsorted.imp fun h => ?_
  have hfst := fst_le_of_le h
  rwa [ordinaryKeyWithObservations_fst graph observe evidence W D,
    ordinaryKeyWithObservations_fst graph observe evidence W D] at hfst

omit [Fintype Atom] [DecidableEq Atom] in
/-- A component labelled bottom everywhere is the support shape of the generic constitutional
component. -/
theorem observedBotComponent_pathObservation (rule : StereochemicalRule)
    (hbot : ∀ node, stereoLabel graph evidence rule node = ⊥) (W D : ℕ) :
    ∀ path node,
      observedStereoNodePathObservation graph observe evidence W D rule node path =
        (nodePathObservationWithObservations graph observe W D 0 node path).map
          (fun _ => (⊥ : StereoLabel))
  | [], node => by
      rw [observedStereoNodePathObservation_nil, hbot,
        nodePathObservationWithObservations_nil graph observe (r := 0) (by omega) node]
      rfl
  | digit :: path, node => by
      obtain ⟨ranked, hperm, hsorted⟩ :=
        exists_observedOrdinaryRanked graph observe evidence W D node
      rw [observedStereoNodePathObservation_cons graph observe evidence W D rule node hperm hsorted,
        nodePathObservationWithObservations_cons graph observe (by omega) node hperm
          (observedRuleKey_sorted_of_ordinary_sorted graph observe evidence W D hsorted)]
      by_cases hguard : digit < W ∧ path.length < D
      · rw [if_pos hguard, if_pos hguard]
        cases ranked[digit]? with
        | none => rfl
        | some child =>
            simp only [Option.map_some, Option.getD_some]
            exact observedBotComponent_pathObservation rule hbot W D path child
      · rw [if_neg hguard, if_neg hguard]
        rfl

omit [Fintype Atom] [DecidableEq Atom] in
/-- Under Rule-4a-only evidence, every absent stereochemical component is determined by equal
generic constitutional keys. -/
theorem observedBotComponent_eq_of_ruleKey_eq (rule : StereochemicalRule)
    (hbot : ∀ node, stereoLabel graph evidence rule node = ⊥) (W D : ℕ)
    {x y : graph.Node}
    (h : ruleKeyWithObservations graph W D observe x =
      ruleKeyWithObservations graph W D observe y) :
    (ofLex (ordinaryKeyWithObservations graph observe evidence W D x)).2.getD
        (stereoIndex rule) [] =
      (ofLex (ordinaryKeyWithObservations graph observe evidence W D y)).2.getD
        (stereoIndex rule) [] := by
  apply (Certificate.CanonicalSphereKey.key_eq_iff_pathObservation
    (ordinaryKeyWithObservations_stereo_wellShaped graph observe evidence W D rule x)
    (ordinaryKeyWithObservations_stereo_wellShaped graph observe evidence W D rule y)).2
  intro path
  change observedStereoNodePathObservation graph observe evidence W D rule x path =
    observedStereoNodePathObservation graph observe evidence W D rule y path
  rw [observedBotComponent_pathObservation graph observe evidence rule hbot W D path x,
    observedBotComponent_pathObservation graph observe evidence rule hbot W D path y]
  unfold nodePathObservationWithObservations
  rw [h]

omit [Fintype Atom] [DecidableEq Atom] in
theorem observedShapeComponents_eq (h4a : Rule4aOnly graph evidence) (W D : ℕ)
    {x y : graph.Node} (h : ruleKeyWithObservations graph W D observe x =
      ruleKeyWithObservations graph W D observe y) :
    (ofLex (ordinaryKeyWithObservations graph observe evidence W D x)).2.getD 0 [] =
      (ofLex (ordinaryKeyWithObservations graph observe evidence W D y)).2.getD 0 [] ∧
    (ofLex (ordinaryKeyWithObservations graph observe evidence W D x)).2.getD 2 [] =
      (ofLex (ordinaryKeyWithObservations graph observe evidence W D y)).2.getD 2 [] ∧
    (ofLex (ordinaryKeyWithObservations graph observe evidence W D x)).2.getD 3 [] =
      (ofLex (ordinaryKeyWithObservations graph observe evidence W D y)).2.getD 3 [] ∧
    (ofLex (ordinaryKeyWithObservations graph observe evidence W D x)).2.getD 4 [] =
      (ofLex (ordinaryKeyWithObservations graph observe evidence W D y)).2.getD 4 [] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact observedBotComponent_eq_of_ruleKey_eq graph observe evidence .rule3DoubleBondGeometry
      (h4a _ (by decide)) W D h
  · exact observedBotComponent_eq_of_ruleKey_eq graph observe evidence .rule4bLikeUnlikeDescriptorPairs
      (h4a _ (by decide)) W D h
  · exact observedBotComponent_eq_of_ruleKey_eq graph observe evidence .rule4cPseudoasymmetricDescriptor
      (h4a _ (by decide)) W D h
  · exact observedBotComponent_eq_of_ruleKey_eq graph observe evidence .rule5EnantiomorphicDescriptor
      (h4a _ (by decide)) W D h

omit [Fintype Atom] [DecidableEq Atom] in
/-- The observed ordinary stereochemical vector is represented by five indexed columns. -/
theorem ordinaryKeyWithObservations_stereo_eq (W D : ℕ) (node : graph.Node) :
    (ofLex (ordinaryKeyWithObservations graph observe evidence W D node)).2 =
      [(ofLex (ordinaryKeyWithObservations graph observe evidence W D node)).2.getD 0 [],
       (ofLex (ordinaryKeyWithObservations graph observe evidence W D node)).2.getD 1 [],
       (ofLex (ordinaryKeyWithObservations graph observe evidence W D node)).2.getD 2 [],
       (ofLex (ordinaryKeyWithObservations graph observe evidence W D node)).2.getD 3 [],
       (ofLex (ordinaryKeyWithObservations graph observe evidence W D node)).2.getD 4 []] := by
  rw [ordinaryKeyWithObservations_eq]
  rfl

private theorem observed_cons_lt_cons_same {α : Type*} [LinearOrder α]
    (a : α) (l m : List α) : a :: l < a :: m ↔ l < m := by
  rw [List.cons_lt_cons_iff]
  simp

omit [Fintype Atom] [DecidableEq Atom] in
/-- Strict ordinary-key ordering collapses to the generic constitution/Rule-4a pair key. -/
theorem observedOrdinaryKey_lt_iff_pairKey (h4a : Rule4aOnly graph evidence) (W D : ℕ)
    (x y : graph.Node) :
    ordinaryKeyWithObservations graph observe evidence W D x <
        ordinaryKeyWithObservations graph observe evidence W D y ↔
      observedPairKey graph observe evidence W D x < observedPairKey graph observe evidence W D y := by
  unfold observedPairKey
  rw [← toLex_ofLex (ordinaryKeyWithObservations graph observe evidence W D x),
    ← toLex_ofLex (ordinaryKeyWithObservations graph observe evidence W D y),
    Prod.Lex.lt_iff, Prod.Lex.lt_iff]
  simp only [ofLex_toLex, ordinaryKeyWithObservations_fst]
  constructor
  · rintro (h | ⟨h, hlt⟩)
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      obtain ⟨e0, e2, e3, e4⟩ := observedShapeComponents_eq graph observe evidence h4a W D h
      rw [ordinaryKeyWithObservations_stereo_eq graph observe evidence W D x,
        ordinaryKeyWithObservations_stereo_eq graph observe evidence W D y,
        e0, e2, e3, e4, observed_cons_lt_cons_same, List.cons_lt_cons_iff] at hlt
      rcases hlt with hlt | ⟨_, hlt⟩
      · exact hlt
      · exact absurd hlt (lt_irrefl _)
  · rintro (h | ⟨h, hlt⟩)
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      obtain ⟨e0, e2, e3, e4⟩ := observedShapeComponents_eq graph observe evidence h4a W D h
      rw [ordinaryKeyWithObservations_stereo_eq graph observe evidence W D x,
        ordinaryKeyWithObservations_stereo_eq graph observe evidence W D y,
        e0, e2, e3, e4, observed_cons_lt_cons_same, List.cons_lt_cons_iff]
      exact Or.inl hlt

end ObservedProjection

end
end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedBotComponent_pathObservation
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedShapeComponents_eq
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryKeyWithObservations_stereo_eq
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedOrdinaryKey_lt_iff_pairKey
