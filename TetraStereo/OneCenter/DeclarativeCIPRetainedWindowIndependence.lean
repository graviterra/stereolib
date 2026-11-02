import TetraStereo.OneCenter.DeclarativeCIPObservedStereoPath
import TetraStereo.OneCenter.DeclarativeCIPObservedRankAddress
import TetraStereo.OneCenter.DeclarativeCIPObservedCanonicalOrder
import TetraStereo.OneCenter.DeclarativeCIPObservedKeyProjection
import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain
import TetraStereo.OneCenter.DeclarativeCIPRetainedContextDescriptor
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Window independence of the observed rule-major keys

The sphere-major keys are laid out in a caller window `(W, D)`: `W` dense slots per node and
spheres `0, …, D`. Keys at different windows are different vectors. What the comparisons consume is
window-free once the window **covers** the finite rooted graph (`WindowCovers`: the graph's
`width` bounds `W`, its `height` bounds `D`; both are structural facts of the graph).

* `vector_orderAgrees_of_pathObservation`, `key_orderAgrees_of_pathObservation` (generic): two
  vectors (keys) of well-shaped keys compare as two others, possibly at another window, when
  their path observations agree. `OrderAgrees` is agreement of `<` and `=`; `compare` on lists
  is not the linear-order `compare`, so it is not used.
* `ruleKey_pathObservation_window`: under two covering windows, every Rule-1a/1b/2 path
  observation of the observer-parametric constitutional key is the same.
  Proof: node induction. Children compare identically at both windows (induction hypothesis +
  generic lemma), so one sibling order is sorted at both windows. A slot inside the covering
  window holds the same child, and a path running past either depth bound reads `⊥` at both
  (`depth_add_length_le_of_nodePathObservationWithObservations`).
* `stereo_pathObservation_window`: the same for the five stereochemical columns (Rules 3, 4a,
  4b, 4c, 5) of the ordinary key, whose siblings are ranked by the whole ordinary key.
* `ruleKey_compare_window`, `ordinaryKey_orderAgrees_window`: comparisons between keys of nodes
  of **two different** graphs agree at any two windows covering both graphs.
* Order-faithful correspondences (`OrderFaithful`, `KeyCorr`, `VecCorr`, `LexCorr`), closed under
  lexicographic pairs, lists, `max`/`min` and `mapObservationKey`. The absent Rule-4b component
  `[]` corresponds only to `[]`.
* `retainedCompleteLigandRule5KeyAt_corr`: the retained complete key at two covering windows
  corresponds column by column (rank pair, count, Rule-4b list, Rule-4c list, Rule-5 stream).
  The reference selection uses the graph's native layout and does not read the window.
  `retainedTaggedAlternativeReferencesAt_window`: the Rule-5 tagged alternative order is equal.
* `retainedCompleteLigandRule5KeyAt_orderAgrees_window`: whole and prior retained keys of two cut
  graphs compare identically at any two windows covering both.
* `retainedContextualOutcomeAt_window`: the retained descriptor outcome on four cut graphs is
  the same at any two windows covering all four (via the accepted
  `completeRootDescriptorJudgment_congr_order`).

No key equality across windows is claimed; only observations, comparisons and outcomes.
-/

namespace TetraStereo.OneCenter.DeclarativeCIP

noncomputable section
open scoped Classical

open Certificate.CanonicalSphereKey
  (Key pathObservationOf VectorWellShaped WellShaped sortDesc AddressBefore)
open CertifiedLocalizedCIPInput (LocalizedAuxiliaryLabel)

universe u

/-! ## Generic comparison facts -/

theorem compare_congr_of_iff {α β : Type*} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β}
    (lt : a < b ↔ c < d) (eq : a = b ↔ c = d) : compare a b = compare c d := by
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (lt.mp h)]
  · rw [compare_eq_iff_eq.mpr h, compare_eq_iff_eq.mpr (eq.mp h)]
  · have hcd : d < c := by
      rcases lt_trichotomy c d with h' | h' | h'
      · exact absurd (lt.mpr h') (not_lt.mpr h.le)
      · exact absurd (eq.mpr h') (ne_of_gt h)
      · exact h'
    rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr hcd]

theorem lt_iff_of_compare_eq {α β : Type*} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β}
    (same : compare a b = compare c d) : a < b ↔ c < d := by
  rw [← compare_lt_iff_lt, ← compare_lt_iff_lt, same]

theorem eq_iff_of_compare_eq {α β : Type*} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β}
    (same : compare a b = compare c d) : a = b ↔ c = d := by
  rw [← compare_eq_iff_eq, ← compare_eq_iff_eq (a := c), same]

theorem le_iff_of_compare_eq {α β : Type*} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β}
    (same : compare a b = compare c d) : a ≤ b ↔ c ≤ d := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, lt_iff_of_compare_eq same, eq_iff_of_compare_eq same]

/-- Two pairs are **order-equivalent** when strict order and equality agree. -/
def OrderAgrees {α β : Type*} [LinearOrder α] [LinearOrder β] (a b : α) (c d : β) : Prop :=
  (a < b ↔ c < d) ∧ (a = b ↔ c = d)

theorem OrderAgrees.le_iff {α β : Type*} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β}
    (agrees : OrderAgrees a b c d) : a ≤ b ↔ c ≤ d := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, agrees.1, agrees.2]

theorem OrderAgrees.symm_args {α β : Type*} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β}
    (agrees : OrderAgrees a b c d) : OrderAgrees b a d c := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro h
      rcases lt_trichotomy c d with h' | h' | h'
      · exact absurd (agrees.1.mpr h') (not_lt.mpr h.le)
      · exact absurd (agrees.2.mpr h') (ne_of_gt h)
      · exact h'
    · intro h
      rcases lt_trichotomy a b with h' | h' | h'
      · exact absurd (agrees.1.mp h') (not_lt.mpr h.le)
      · exact absurd (agrees.2.mp h') (ne_of_gt h)
      · exact h'
  · rw [eq_comm, agrees.2, eq_comm]

/-- **Vector order depends only on path observations.** -/
theorem vector_orderAgrees_of_pathObservation {α : Type u} [LinearOrder α]
    {m W D W' D' : ℕ} {left right left' right' : List (Key α)}
    (hl : VectorWellShaped m W D left) (hr : VectorWellShaped m W D right)
    (hl' : VectorWellShaped m W' D' left') (hr' : VectorWellShaped m W' D' right')
    (agreeLeft : ∀ i < m, ∀ path, pathObservationOf W D (left.getD i []) path =
      pathObservationOf W' D' (left'.getD i []) path)
    (agreeRight : ∀ i < m, ∀ path, pathObservationOf W D (right.getD i []) path =
      pathObservationOf W' D' (right'.getD i []) path) :
    OrderAgrees left right left' right' := by
  refine ⟨?_, ?_⟩
  · rw [Certificate.CanonicalSphereKey.vector_lt_iff_pathObservation hl hr,
      Certificate.CanonicalSphereKey.vector_lt_iff_pathObservation hl' hr']
    constructor
    · rintro ⟨r, hrm, path, hpath, hrules, hearlier⟩
      refine ⟨r, hrm, path, ?_, ?_, ?_⟩
      · rw [← agreeLeft r hrm, ← agreeRight r hrm]
        exact hpath
      · intro r' hr' path'
        rw [← agreeLeft r' (by omega), ← agreeRight r' (by omega)]
        exact hrules r' hr' path'
      · intro earlier hbefore
        rw [← agreeLeft r hrm, ← agreeRight r hrm]
        exact hearlier earlier hbefore
    · rintro ⟨r, hrm, path, hpath, hrules, hearlier⟩
      refine ⟨r, hrm, path, ?_, ?_, ?_⟩
      · rw [agreeLeft r hrm, agreeRight r hrm]
        exact hpath
      · intro r' hr' path'
        rw [agreeLeft r' (by omega), agreeRight r' (by omega)]
        exact hrules r' hr' path'
      · intro earlier hbefore
        rw [agreeLeft r hrm, agreeRight r hrm]
        exact hearlier earlier hbefore
  · rw [Certificate.CanonicalSphereKey.vector_eq_iff_pathObservation hl hr,
      Certificate.CanonicalSphereKey.vector_eq_iff_pathObservation hl' hr']
    constructor
    · intro h r hrm path
      rw [← agreeLeft r hrm, ← agreeRight r hrm]
      exact h r hrm path
    · intro h r hrm path
      rw [agreeLeft r hrm, agreeRight r hrm]
      exact h r hrm path

/-! ## Covering windows -/

section Window

variable {Atom : Type u}

/-- A window covers a finite rooted graph when it bounds its branching (`width`, the node count)
and its height. Both bounds are structural facts of the graph. -/
def WindowCovers (graph : RootedDigraph Atom) (W D : ℕ) : Prop :=
  letI : Fintype graph.Node := graph.nodeFintype
  graph.width ≤ W ∧ graph.height ≤ D

theorem windowCovers_native (graph : RootedDigraph Atom) :
    WindowCovers graph (letI : Fintype graph.Node := graph.nodeFintype; graph.width)
      graph.height :=
  ⟨le_refl _, le_refl _⟩

theorem windowCovers_mono {graph : RootedDigraph Atom} {W D W' D' : ℕ}
    (cover : WindowCovers graph W D) (hW : W ≤ W') (hD : D ≤ D') : WindowCovers graph W' D' :=
  ⟨cover.1.trans hW, cover.2.trans hD⟩

end Window

/-! ## The constitutional key -/

section Constitutional

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (graph : RootedDigraph Atom)
  (observe : ConstitutionalRule → graph.Node → ℤ)

local instance windowIndependenceNodeFintype : Fintype graph.Node := graph.nodeFintype

omit [Fintype Atom] [DecidableEq Atom] in
private theorem ranked_length_le_width {node : graph.Node} {ranked : List graph.Node}
    (perm : ranked.Perm (graph.childList node)) : ranked.length ≤ graph.width := by
  rw [perm.length_eq]
  exact (graph.childList_nodup node).length_le_card

omit [Fintype Atom] [DecidableEq Atom] in
private theorem rule_bot_past_height {W D r : ℕ} (hr : r < 3) {node child : graph.Node}
    (hchild : graph.child node child) {rest : List ℕ} (long : graph.height ≤ rest.length) :
    nodePathObservationWithObservations graph observe W D r child rest = ⊥ := by
  by_contra hne
  have bound := depth_add_length_le_of_nodePathObservationWithObservations graph observe
    (W := W) (D := D) hr rest child hne
  have hdepth := graph.child_depth hchild
  omega

omit [Fintype Atom] [DecidableEq Atom] in
/-- **Window independence of constitutional observations.** -/
theorem ruleKey_pathObservation_window {W D W' D' : ℕ}
    (cover : WindowCovers graph W D) (cover' : WindowCovers graph W' D') :
    ∀ node r path, nodePathObservationWithObservations graph observe W D r node path =
      nodePathObservationWithObservations graph observe W' D' r node path := by
  intro node
  refine node_induction graph (motive := fun node => ∀ r path,
    nodePathObservationWithObservations graph observe W D r node path =
      nodePathObservationWithObservations graph observe W' D' r node path) ?_ node
  intro node ih r path
  by_cases hr : r < 3
  swap
  · rw [nodePathObservationWithObservations_of_three_le graph observe (not_lt.mp hr),
      nodePathObservationWithObservations_of_three_le graph observe (not_lt.mp hr)]
  cases path with
  | nil =>
      rw [nodePathObservationWithObservations_nil graph observe hr,
        nodePathObservationWithObservations_nil graph observe hr]
  | cons digit rest =>
      have agreeChildren : ∀ a b, graph.child node a → graph.child node b →
          OrderAgrees (ruleKeyWithObservations graph W D observe a)
              (ruleKeyWithObservations graph W D observe b)
            (ruleKeyWithObservations graph W' D' observe a)
              (ruleKeyWithObservations graph W' D' observe b) := fun a b ha hb =>
        vector_orderAgrees_of_pathObservation
          (ruleKeyWithObservations_vectorWellShaped graph observe W D a)
          (ruleKeyWithObservations_vectorWellShaped graph observe W D b)
          (ruleKeyWithObservations_vectorWellShaped graph observe W' D' a)
          (ruleKeyWithObservations_vectorWellShaped graph observe W' D' b)
          (fun i _ path => ih a ha i path) (fun i _ path => ih b hb i path)
      obtain ⟨ranked, perm, sorted⟩ : ∃ ranked : List graph.Node,
          ranked.Perm (graph.childList node) ∧
            (ranked.map (ruleKeyWithObservations graph W D observe)).Pairwise
              fun x y => y ≤ x :=
        ⟨_, sortedChildrenWithObservations_perm graph observe W D node,
          sortedChildrenWithObservations_pairwise graph observe W D node⟩
      have sorted' : (ranked.map (ruleKeyWithObservations graph W' D' observe)).Pairwise
          fun x y => y ≤ x := by
        have source := sorted
        rw [List.pairwise_map] at source ⊢
        refine source.imp_of_mem (fun {a b} ha hb hab => ?_)
        have ca := (graph.mem_childList).1 (perm.subset ha)
        have cb := (graph.mem_childList).1 (perm.subset hb)
        exact (agreeChildren b a cb ca).le_iff.mp hab
      rw [nodePathObservationWithObservations_cons graph observe hr node perm sorted digit rest,
        nodePathObservationWithObservations_cons graph observe hr node perm sorted' digit rest]
      cases hc : ranked[digit]? with
      | none => simp
      | some child =>
          simp only [Option.map_some, Option.getD_some]
          obtain ⟨hdlt, _⟩ := List.getElem?_eq_some_iff.mp hc
          have hchild : graph.child node child :=
            (graph.mem_childList).1 (perm.subset (List.mem_of_getElem? hc))
          have hlen := ranked_length_le_width graph perm
          have hdW : digit < W := by have := cover.1; omega
          have hdW' : digit < W' := by have := cover'.1; omega
          have ihc := ih child hchild r rest
          by_cases h1 : rest.length < D <;> by_cases h2 : rest.length < D'
          · rw [if_pos ⟨hdW, h1⟩, if_pos ⟨hdW', h2⟩]
            exact ihc
          · rw [if_pos ⟨hdW, h1⟩, if_neg (fun h => h2 h.2)]
            exact rule_bot_past_height graph observe hr hchild (by have := cover'.2; omega)
          · rw [if_neg (fun h => h1 h.2), if_pos ⟨hdW', h2⟩]
            exact (rule_bot_past_height graph observe hr hchild (by have := cover.2; omega)).symm
          · rw [if_neg (fun h => h1 h.2), if_neg (fun h => h2 h.2)]

end Constitutional

/-- **Constitutional comparisons are window-free** between nodes of two graphs, at any two
windows covering both. -/
theorem ruleKey_compare_window {Atom : Type u} {left right : RootedDigraph Atom}
    (observeLeft : ConstitutionalRule → left.Node → ℤ)
    (observeRight : ConstitutionalRule → right.Node → ℤ) {W D W' D' : ℕ}
    (coverLeft : WindowCovers left W D) (coverLeft' : WindowCovers left W' D')
    (coverRight : WindowCovers right W D) (coverRight' : WindowCovers right W' D')
    (a : left.Node) (b : right.Node) :
    OrderAgrees (ruleKeyWithObservations left W D observeLeft a)
        (ruleKeyWithObservations right W D observeRight b)
      (ruleKeyWithObservations left W' D' observeLeft a)
        (ruleKeyWithObservations right W' D' observeRight b) :=
  vector_orderAgrees_of_pathObservation
    (ruleKeyWithObservations_vectorWellShaped left observeLeft W D a)
    (ruleKeyWithObservations_vectorWellShaped right observeRight W D b)
    (ruleKeyWithObservations_vectorWellShaped left observeLeft W' D' a)
    (ruleKeyWithObservations_vectorWellShaped right observeRight W' D' b)
    (fun i _ path => ruleKey_pathObservation_window left observeLeft coverLeft coverLeft' a i path)
    (fun i _ path => ruleKey_pathObservation_window right observeRight coverRight coverRight' b i
      path)

/-! ## Lexicographic pairs -/

theorem lex_orderAgrees {α β γ δ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ]
    [LinearOrder δ] {x y : α ×ₗ β} {x' y' : γ ×ₗ δ}
    (first : OrderAgrees (ofLex x).1 (ofLex y).1 (ofLex x').1 (ofLex y').1)
    (second : OrderAgrees (ofLex x).2 (ofLex y).2 (ofLex x').2 (ofLex y').2) :
    OrderAgrees x y x' y' := by
  refine ⟨?_, ?_⟩
  · show toLex (ofLex x) < toLex (ofLex y) ↔ toLex (ofLex x') < toLex (ofLex y')
    rw [Prod.Lex.lt_iff, Prod.Lex.lt_iff]
    simp only [ofLex_toLex]
    rw [first.1, first.2, second.1]
  · constructor
    · intro same
      have h1 := first.2.mp (congrArg (fun z => (ofLex z).1) same)
      have h2 := second.2.mp (congrArg (fun z => (ofLex z).2) same)
      show toLex (ofLex x') = toLex (ofLex y')
      exact congrArg toLex (Prod.ext h1 h2)
    · intro same
      have h1 := first.2.mpr (congrArg (fun z => (ofLex z).1) same)
      have h2 := second.2.mpr (congrArg (fun z => (ofLex z).2) same)
      show toLex (ofLex x) = toLex (ofLex y)
      exact congrArg toLex (Prod.ext h1 h2)

/-! ## The ordinary key: Rules 3, 4a, 4b, 4c and 5 -/

theorem stereoIndex_surjective {r : ℕ} (hr : r < 5) : ∃ rule, stereoIndex rule = r := by
  interval_cases r
  · exact ⟨.rule3DoubleBondGeometry, rfl⟩
  · exact ⟨.rule4aStereogenicUnitKind, rfl⟩
  · exact ⟨.rule4bLikeUnlikeDescriptorPairs, rfl⟩
  · exact ⟨.rule4cPseudoasymmetricDescriptor, rfl⟩
  · exact ⟨.rule5EnantiomorphicDescriptor, rfl⟩

section Ordinary

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (graph : RootedDigraph Atom)
  (observe : ConstitutionalRule → graph.Node → ℤ)
  (evidence : StereochemicalEvidence graph)

local instance windowIndependenceOrdinaryNodeFintype : Fintype graph.Node := graph.nodeFintype

omit [Fintype Atom] [DecidableEq Atom] in
theorem ordinaryKeyWithObservations_stereo_vectorWellShaped (W D : ℕ) (node : graph.Node) :
    VectorWellShaped 5 W D (ofLex (ordinaryKeyWithObservations graph observe evidence W D node)).2 := by
  refine ⟨?_, fun r hr => ?_⟩
  · rw [ordinaryKeyWithObservations_eq]
    rfl
  · obtain ⟨rule, rfl⟩ := stereoIndex_surjective hr
    exact ordinaryKeyWithObservations_stereo_wellShaped graph observe evidence W D rule node

omit [Fintype Atom] [DecidableEq Atom] in
/-- Stereochemical observations vanish at addresses reaching below the graph's height. -/
theorem stereo_bot_of_long (W D : ℕ) (rule : StereochemicalRule) :
    ∀ (path : List ℕ) (node : graph.Node), graph.height < graph.depth node + path.length →
      observedStereoNodePathObservation graph observe evidence W D rule node path = ⊥
  | [], node, long => by
      have := graph.depth_le_height node
      simp at long
      omega
  | digit :: path, node, long => by
      obtain ⟨ranked, perm, sorted⟩ :=
        exists_observedOrdinaryRanked graph observe evidence W D node
      rw [observedStereoNodePathObservation_cons graph observe evidence W D rule node perm sorted
        digit path]
      split_ifs
      · cases hc : ranked[digit]? with
        | none => simp
        | some child =>
            simp only [Option.map_some, Option.getD_some]
            have hchild : graph.child node child :=
              (graph.mem_childList).1 (perm.subset (List.mem_of_getElem? hc))
            have hdepth := graph.child_depth hchild
            simp only [List.length_cons] at long
            exact stereo_bot_of_long W D rule path child (by omega)
      · rfl

omit [Fintype Atom] [DecidableEq Atom] in
private theorem stereo_bot_past_height {W D : ℕ} (rule : StereochemicalRule)
    {node child : graph.Node} (hchild : graph.child node child) {rest : List ℕ}
    (long : graph.height ≤ rest.length) :
    observedStereoNodePathObservation graph observe evidence W D rule child rest = ⊥ :=
  stereo_bot_of_long graph observe evidence W D rule rest child
    (by have := graph.child_depth hchild; omega)

omit [Fintype Atom] [DecidableEq Atom] in
/-- **Window independence of stereochemical observations** (Rules 3, 4a, 4b, 4c, 5). -/
theorem stereo_pathObservation_window {W D W' D' : ℕ}
    (cover : WindowCovers graph W D) (cover' : WindowCovers graph W' D') :
    ∀ node rule path,
      observedStereoNodePathObservation graph observe evidence W D rule node path =
        observedStereoNodePathObservation graph observe evidence W' D' rule node path := by
  intro node
  refine node_induction graph (motive := fun node => ∀ rule path,
    observedStereoNodePathObservation graph observe evidence W D rule node path =
      observedStereoNodePathObservation graph observe evidence W' D' rule node path) ?_ node
  intro node ih rule path
  cases path with
  | nil =>
      rw [observedStereoNodePathObservation_nil, observedStereoNodePathObservation_nil]
  | cons digit rest =>
      have agreeChildren : ∀ a b, graph.child node a → graph.child node b →
          OrderAgrees (ordinaryKeyWithObservations graph observe evidence W D a)
              (ordinaryKeyWithObservations graph observe evidence W D b)
            (ordinaryKeyWithObservations graph observe evidence W' D' a)
              (ordinaryKeyWithObservations graph observe evidence W' D' b) := by
        intro a b ha hb
        apply lex_orderAgrees
        · rw [ordinaryKeyWithObservations_fst, ordinaryKeyWithObservations_fst,
            ordinaryKeyWithObservations_fst, ordinaryKeyWithObservations_fst]
          exact ruleKey_compare_window observe observe cover cover' cover cover' a b
        · exact vector_orderAgrees_of_pathObservation
            (ordinaryKeyWithObservations_stereo_vectorWellShaped graph observe evidence W D a)
            (ordinaryKeyWithObservations_stereo_vectorWellShaped graph observe evidence W D b)
            (ordinaryKeyWithObservations_stereo_vectorWellShaped graph observe evidence W' D' a)
            (ordinaryKeyWithObservations_stereo_vectorWellShaped graph observe evidence W' D' b)
            (fun i hi path => by
              obtain ⟨rule', rfl⟩ := stereoIndex_surjective hi
              exact ih a ha rule' path)
            (fun i hi path => by
              obtain ⟨rule', rfl⟩ := stereoIndex_surjective hi
              exact ih b hb rule' path)
      obtain ⟨ranked, perm, sorted⟩ :=
        exists_observedOrdinaryRanked graph observe evidence W D node
      have sorted' : (ranked.map (ordinaryKeyWithObservations graph observe evidence W' D')).Pairwise
          fun x y => y ≤ x := by
        have source := sorted
        rw [List.pairwise_map] at source ⊢
        refine source.imp_of_mem (fun {a b} ha hb hab => ?_)
        have ca := (graph.mem_childList).1 (perm.subset ha)
        have cb := (graph.mem_childList).1 (perm.subset hb)
        exact (agreeChildren b a cb ca).le_iff.mp hab
      rw [observedStereoNodePathObservation_cons graph observe evidence W D rule node perm sorted
          digit rest,
        observedStereoNodePathObservation_cons graph observe evidence W' D' rule node perm sorted'
          digit rest]
      cases hc : ranked[digit]? with
      | none => simp
      | some child =>
          simp only [Option.map_some, Option.getD_some]
          obtain ⟨hdlt, _⟩ := List.getElem?_eq_some_iff.mp hc
          have hchild : graph.child node child :=
            (graph.mem_childList).1 (perm.subset (List.mem_of_getElem? hc))
          have hlen := ranked_length_le_width graph perm
          have hdW : digit < W := by have := cover.1; omega
          have hdW' : digit < W' := by have := cover'.1; omega
          have ihc := ih child hchild rule rest
          by_cases h1 : rest.length < D <;> by_cases h2 : rest.length < D'
          · rw [if_pos ⟨hdW, h1⟩, if_pos ⟨hdW', h2⟩]
            exact ihc
          · rw [if_pos ⟨hdW, h1⟩, if_neg (fun h => h2 h.2)]
            exact stereo_bot_past_height graph observe evidence rule hchild
              (by have := cover'.2; omega)
          · rw [if_neg (fun h => h1 h.2), if_pos ⟨hdW', h2⟩]
            exact (stereo_bot_past_height graph observe evidence rule hchild
              (by have := cover.2; omega)).symm
          · rw [if_neg (fun h => h1 h.2), if_neg (fun h => h2 h.2)]

end Ordinary

/-- **Ordinary-key comparisons (Rules 1a–5) are window-free** between nodes of two graphs. -/
theorem ordinaryKey_orderAgrees_window {Atom : Type u} {left right : RootedDigraph Atom}
    (observeLeft : ConstitutionalRule → left.Node → ℤ)
    (observeRight : ConstitutionalRule → right.Node → ℤ)
    (evidenceLeft : StereochemicalEvidence left) (evidenceRight : StereochemicalEvidence right)
    {W D W' D' : ℕ}
    (coverLeft : WindowCovers left W D) (coverLeft' : WindowCovers left W' D')
    (coverRight : WindowCovers right W D) (coverRight' : WindowCovers right W' D')
    (a : left.Node) (b : right.Node) :
    OrderAgrees (ordinaryKeyWithObservations left observeLeft evidenceLeft W D a)
        (ordinaryKeyWithObservations right observeRight evidenceRight W D b)
      (ordinaryKeyWithObservations left observeLeft evidenceLeft W' D' a)
        (ordinaryKeyWithObservations right observeRight evidenceRight W' D' b) := by
  apply lex_orderAgrees
  · rw [ordinaryKeyWithObservations_fst, ordinaryKeyWithObservations_fst,
      ordinaryKeyWithObservations_fst, ordinaryKeyWithObservations_fst]
    exact ruleKey_compare_window observeLeft observeRight coverLeft coverLeft' coverRight
      coverRight' a b
  · exact vector_orderAgrees_of_pathObservation
      (ordinaryKeyWithObservations_stereo_vectorWellShaped left observeLeft evidenceLeft W D a)
      (ordinaryKeyWithObservations_stereo_vectorWellShaped right observeRight evidenceRight W D b)
      (ordinaryKeyWithObservations_stereo_vectorWellShaped left observeLeft evidenceLeft W' D' a)
      (ordinaryKeyWithObservations_stereo_vectorWellShaped right observeRight evidenceRight W' D' b)
      (fun i hi path => by
        obtain ⟨rule, rfl⟩ := stereoIndex_surjective hi
        exact stereo_pathObservation_window left observeLeft evidenceLeft coverLeft coverLeft' a
          rule path)
      (fun i hi path => by
        obtain ⟨rule, rfl⟩ := stereoIndex_surjective hi
        exact stereo_pathObservation_window right observeRight evidenceRight coverRight
          coverRight' b rule path)

/-! ## Order-faithful correspondences between two windows

A correspondence `R` relates a value read at window `(W, D)` to the value read at `(W', D')`. It
is order-faithful when any two corresponding pairs compare identically. The retained complete key
is assembled from keys, vectors, lexicographic pairs, lists, `max`/`min` and `mapObservationKey`;
each constructor preserves faithful correspondences. -/

def OrderFaithful {α β : Type*} [LinearOrder α] [LinearOrder β] (R : α → β → Prop) : Prop :=
  ∀ ⦃a a'⦄, R a a' → ∀ ⦃b b'⦄, R b b' → OrderAgrees a b a' b'

/-- One key at each window: both the absent component `[]`, or well-shaped with equal path
observations. -/
abbrev KeyCorr {α : Type*} [LinearOrder α] (W D W' D' : ℕ) (key key' : Key α) : Prop :=
  (key = [] ∧ key' = []) ∨
    (WellShaped W D key ∧ WellShaped W' D' key' ∧
      ∀ path, pathObservationOf W D key path = pathObservationOf W' D' key' path)

abbrev VecCorr {α : Type*} [LinearOrder α] (m W D W' D' : ℕ) (vector vector' : List (Key α)) :
    Prop :=
  VectorWellShaped m W D vector ∧ VectorWellShaped m W' D' vector' ∧
    ∀ i < m, ∀ path, pathObservationOf W D (vector.getD i []) path =
      pathObservationOf W' D' (vector'.getD i []) path

abbrev LexCorr {α β γ δ : Type*} (Ra : α → γ → Prop) (Rb : β → δ → Prop)
    (x : α ×ₗ β) (x' : γ ×ₗ δ) : Prop :=
  Ra (ofLex x).1 (ofLex x').1 ∧ Rb (ofLex x).2 (ofLex x').2

theorem orderFaithful_eq {α : Type*} [LinearOrder α] : OrderFaithful (fun a b : α => a = b) := by
  intro a a' ha b b' hb
  subst ha hb
  exact ⟨Iff.rfl, Iff.rfl⟩

theorem OrderFaithful.lex {α β γ δ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ]
    [LinearOrder δ] {Ra : α → γ → Prop} {Rb : β → δ → Prop}
    (fa : OrderFaithful Ra) (fb : OrderFaithful Rb) : OrderFaithful (LexCorr Ra Rb) :=
  fun _ _ hx _ _ hy => lex_orderAgrees (fa hx.1 hy.1) (fb hx.2 hy.2)

theorem OrderFaithful.list {α β : Type*} [LinearOrder α] [LinearOrder β] {R : α → β → Prop}
    (faithful : OrderFaithful R) : OrderFaithful (List.Forall₂ R) := by
  intro a a' ha
  induction ha with
  | nil =>
      intro b b' hb
      cases hb with
      | nil =>
          exact ⟨iff_of_false (List.not_lt_nil _) (List.not_lt_nil _), iff_of_true rfl rfl⟩
      | cons _ _ =>
          exact ⟨iff_of_true (by simp) (by simp), iff_of_false (by simp) (by simp)⟩
  | cons hx _ ih =>
      intro b b' hb
      cases hb with
      | nil =>
          exact ⟨iff_of_false (List.not_lt_nil _) (List.not_lt_nil _),
            iff_of_false (by simp) (by simp)⟩
      | cons hy hrest =>
          have head := faithful hx hy
          have tail := ih hrest
          refine ⟨?_, ?_⟩
          · rw [List.cons_lt_cons_iff, List.cons_lt_cons_iff, head.1, head.2, tail.1]
          · rw [List.cons_eq_cons, List.cons_eq_cons, head.2, tail.2]

theorem OrderFaithful.max {α β : Type*} [LinearOrder α] [LinearOrder β] {R : α → β → Prop}
    (faithful : OrderFaithful R) {a b : α} {a' b' : β} (ha : R a a') (hb : R b b') :
    R (max a b) (max a' b') := by
  rw [max_def, max_def]
  by_cases h : a ≤ b
  · rw [if_pos h, if_pos ((faithful ha hb).le_iff.mp h)]
    exact hb
  · rw [if_neg h, if_neg (fun h' => h ((faithful ha hb).le_iff.mpr h'))]
    exact ha

theorem OrderFaithful.min {α β : Type*} [LinearOrder α] [LinearOrder β] {R : α → β → Prop}
    (faithful : OrderFaithful R) {a b : α} {a' b' : β} (ha : R a a') (hb : R b b') :
    R (min a b) (min a' b') := by
  rw [min_def, min_def]
  by_cases h : a ≤ b
  · rw [if_pos h, if_pos ((faithful ha hb).le_iff.mp h)]
    exact ha
  · rw [if_neg h, if_neg (fun h' => h ((faithful ha hb).le_iff.mpr h'))]
    exact hb

private theorem wellShaped_ne_nil {α : Type*} {W D : ℕ} {key : Key α}
    (shaped : WellShaped W D key) : key ≠ [] := by
  intro empty
  subst empty
  have length := shaped.1
  simp at length

private theorem nil_lt_of_ne_nil {α : Type*} [LinearOrder α] {l : List α} (h : l ≠ []) :
    [] < l := by
  cases l with
  | nil => exact absurd rfl h
  | cons _ _ => simp

/-- **Key order depends only on path observations**, at any two windows. -/
theorem key_orderAgrees_of_pathObservation {α : Type*} [LinearOrder α] {W D W' D' : ℕ}
    {left right left' right' : Key α}
    (hl : WellShaped W D left) (hr : WellShaped W D right)
    (hl' : WellShaped W' D' left') (hr' : WellShaped W' D' right')
    (agreeLeft : ∀ path, pathObservationOf W D left path = pathObservationOf W' D' left' path)
    (agreeRight : ∀ path, pathObservationOf W D right path =
      pathObservationOf W' D' right' path) :
    OrderAgrees left right left' right' := by
  have eLeft : pathObservationOf W D left = pathObservationOf W' D' left' := funext agreeLeft
  have eRight : pathObservationOf W D right = pathObservationOf W' D' right' := funext agreeRight
  refine ⟨?_, ?_⟩
  · rw [Certificate.CanonicalSphereKey.key_lt_iff_pathObservation hl hr,
      Certificate.CanonicalSphereKey.key_lt_iff_pathObservation hl' hr', eLeft, eRight]
  · rw [Certificate.CanonicalSphereKey.key_eq_iff_pathObservation hl hr,
      Certificate.CanonicalSphereKey.key_eq_iff_pathObservation hl' hr', eLeft, eRight]

theorem keyCorr_faithful {α : Type*} [LinearOrder α] (W D W' D' : ℕ) :
    OrderFaithful (KeyCorr (α := α) W D W' D') := by
  intro a a' ha b b' hb
  rcases ha with ⟨rfl, rfl⟩ | ⟨sa, sa', oa⟩ <;> rcases hb with ⟨rfl, rfl⟩ | ⟨sb, sb', ob⟩
  · exact ⟨iff_of_false (List.not_lt_nil _) (List.not_lt_nil _), iff_of_true rfl rfl⟩
  · exact ⟨iff_of_true (nil_lt_of_ne_nil (wellShaped_ne_nil sb))
        (nil_lt_of_ne_nil (wellShaped_ne_nil sb')),
      iff_of_false (Ne.symm (wellShaped_ne_nil sb)) (Ne.symm (wellShaped_ne_nil sb'))⟩
  · exact ⟨iff_of_false (List.not_lt_nil _) (List.not_lt_nil _),
      iff_of_false (wellShaped_ne_nil sa) (wellShaped_ne_nil sa')⟩
  · exact key_orderAgrees_of_pathObservation sa sb sa' sb' oa ob

theorem vecCorr_faithful {α : Type u} [LinearOrder α] (m W D W' D' : ℕ) :
    OrderFaithful (VecCorr (α := α) m W D W' D') :=
  fun _ _ ha _ _ hb => vector_orderAgrees_of_pathObservation ha.1 hb.1 ha.2.1 hb.2.1 ha.2.2 hb.2.2

theorem keyCorr_map {α β : Type*} [LinearOrder α] [LinearOrder β] (f : α → β)
    {W D W' D' : ℕ} {key key' : Key α} (corr : KeyCorr W D W' D' key key') :
    KeyCorr W D W' D' (mapObservationKey f key) (mapObservationKey f key') := by
  rcases corr with ⟨rfl, rfl⟩ | ⟨shaped, shaped', agree⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · refine Or.inr ⟨mapObservationKey_wellShaped f shaped, mapObservationKey_wellShaped f shaped',
      fun path => ?_⟩
    rw [pathObservationOf_mapObservationKey, pathObservationOf_mapObservationKey, agree path]

/-! ## Window correspondence of observed components -/

theorem stereoComponent_keyCorr {Atom : Type u} (graph : RootedDigraph Atom)
    (observe : ConstitutionalRule → graph.Node → ℤ) (evidence : StereochemicalEvidence graph)
    (rule : StereochemicalRule) (node : graph.Node) {W D W' D' : ℕ}
    (cover : WindowCovers graph W D) (cover' : WindowCovers graph W' D') :
    KeyCorr W D W' D'
      ((ofLex (ordinaryKeyWithObservations graph observe evidence W D node)).2.getD
        (stereoIndex rule) [])
      ((ofLex (ordinaryKeyWithObservations graph observe evidence W' D' node)).2.getD
        (stereoIndex rule) []) :=
  Or.inr ⟨ordinaryKeyWithObservations_stereo_wellShaped graph observe evidence W D rule node,
    ordinaryKeyWithObservations_stereo_wellShaped graph observe evidence W' D' rule node,
    fun path => stereo_pathObservation_window graph observe evidence cover cover' node rule path⟩

theorem ruleKey_vecCorr {Atom : Type u} (graph : RootedDigraph Atom)
    (observe : ConstitutionalRule → graph.Node → ℤ) (node : graph.Node) {W D W' D' : ℕ}
    (cover : WindowCovers graph W D) (cover' : WindowCovers graph W' D') :
    VecCorr 3 W D W' D' (ruleKeyWithObservations graph W D observe node)
      (ruleKeyWithObservations graph W' D' observe node) :=
  ⟨ruleKeyWithObservations_vectorWellShaped graph observe W D node,
    ruleKeyWithObservations_vectorWellShaped graph observe W' D' node,
    fun i _ path => ruleKey_pathObservation_window graph observe cover cover' node i path⟩

/-! ## The retained complete key -/

/-- Correspondence of complete readings (Rule-4b component, Rule-4c component). -/
abbrev ReadingCorr (W D W' D' : ℕ) : CompleteReadingKey → CompleteReadingKey → Prop :=
  LexCorr (KeyCorr W D W' D') (KeyCorr W D W' D')

/-- Correspondence of complete prior signatures (count, Rule-4b list, Rule-4c list). -/
abbrev SignatureCorr (W D W' D' : ℕ) : CompletePriorSignature → CompletePriorSignature → Prop :=
  LexCorr (fun a b : ℕ => a = b)
    (LexCorr (List.Forall₂ (KeyCorr W D W' D')) (List.Forall₂ (KeyCorr W D W' D')))

/-- Correspondence of retained prior keys (Rules 1a/1b/2 vector, Rule 4a, then signature). -/
abbrev PriorCorr (W D W' D' : ℕ) : CompleteLigandPriorKey → CompleteLigandPriorKey → Prop :=
  LexCorr (LexCorr (VecCorr 3 W D W' D') (KeyCorr W D W' D')) (SignatureCorr W D W' D')

/-- Correspondence of whole retained keys: prior key, then the Rule-5 stream. -/
abbrev CompleteKeyCorr (W D W' D' : ℕ) :
    CompleteLigandRule5Key → CompleteLigandRule5Key → Prop :=
  LexCorr (PriorCorr W D W' D') (List.Forall₂ (KeyCorr W D W' D'))

theorem readingCorr_faithful (W D W' D' : ℕ) : OrderFaithful (ReadingCorr W D W' D') :=
  (keyCorr_faithful W D W' D').lex (keyCorr_faithful W D W' D')

theorem priorCorr_faithful (W D W' D' : ℕ) : OrderFaithful (PriorCorr W D W' D') :=
  ((vecCorr_faithful 3 W D W' D').lex (keyCorr_faithful W D W' D')).lex
    (orderFaithful_eq.lex ((keyCorr_faithful W D W' D').list.lex
      (keyCorr_faithful W D W' D').list))

theorem completeKeyCorr_faithful (W D W' D' : ℕ) : OrderFaithful (CompleteKeyCorr W D W' D') :=
  (priorCorr_faithful W D W' D').lex (keyCorr_faithful W D W' D').list

section Retained

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

local instance windowIndependenceRetainedNodeFintype : Fintype graph.Node := graph.nodeFintype

theorem retainedCompleteReadingAt_corr {W D W' D' : ℕ}
    (cover : WindowCovers graph W D) (cover' : WindowCovers graph W' D')
    (reference : Option DescriptorSense) :
    ReadingCorr W D W' D'
      (retainedCompleteReadingAt molecule descriptorMap unit graph W D reference)
      (retainedCompleteReadingAt molecule descriptorMap unit graph W' D' reference) := by
  cases reference with
  | none =>
      exact ⟨Or.inl ⟨rfl, rfl⟩,
        stereoComponent_keyCorr graph (retainedContextNodeObservation molecule graph unit)
          (retainedNoReferenceEvidence4c molecule descriptorMap unit graph)
          .rule4cPseudoasymmetricDescriptor graph.root cover cover'⟩
  | some sense =>
      exact ⟨stereoComponent_keyCorr graph (retainedContextNodeObservation molecule graph unit)
          (retainedReadingEvidence molecule descriptorMap unit graph sense)
          .rule4bLikeUnlikeDescriptorPairs graph.root cover cover',
        stereoComponent_keyCorr graph (retainedContextNodeObservation molecule graph unit)
          (retainedReadingEvidence4c molecule descriptorMap unit graph sense)
          .rule4cPseudoasymmetricDescriptor graph.root cover cover'⟩

theorem retainedCompleteReadingsAt_corr {W D W' D' : ℕ}
    (cover : WindowCovers graph W D) (cover' : WindowCovers graph W' D') :
    List.Forall₂ (ReadingCorr W D W' D')
      (retainedCompleteReadingsAt molecule descriptorMap unit graph W D)
      (retainedCompleteReadingsAt molecule descriptorMap unit graph W' D') := by
  have reading := retainedCompleteReadingAt_corr molecule descriptorMap unit graph cover cover'
  unfold retainedCompleteReadingsAt
  cases retainedReferenceSelection molecule descriptorMap unit graph with
  | empty => exact .cons (reading none) .nil
  | one sense => exact .cons (reading (some sense)) .nil
  | both =>
      exact .cons ((readingCorr_faithful W D W' D').max (reading (some .senior))
          (reading (some .junior)))
        (.cons ((readingCorr_faithful W D W' D').min (reading (some .senior))
          (reading (some .junior))) .nil)

theorem retainedCompletePriorSignatureAt_corr {W D W' D' : ℕ}
    (cover : WindowCovers graph W D) (cover' : WindowCovers graph W' D') :
    SignatureCorr W D W' D'
      (retainedCompletePriorSignatureAt molecule descriptorMap unit graph W D)
      (retainedCompletePriorSignatureAt molecule descriptorMap unit graph W' D') := by
  have readings := retainedCompleteReadingsAt_corr molecule descriptorMap unit graph cover cover'
  refine ⟨rfl, ?_, ?_⟩
  · dsimp only [retainedCompletePriorSignatureAt, ofLex_toLex]
    split_ifs
    · exact .nil
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact List.Forall₂.imp (fun _ _ h => h.1) readings
  · dsimp only [retainedCompletePriorSignatureAt, ofLex_toLex]
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.Forall₂.imp (fun _ _ h => h.2) readings

theorem retainedMolecularRankPairAt_corr {W D W' D' : ℕ}
    (cover : WindowCovers graph W D) (cover' : WindowCovers graph W' D') :
    LexCorr (VecCorr 3 W D W' D') (KeyCorr W D W' D')
      (retainedMolecularRankPairAt molecule descriptorMap unit graph W D)
      (retainedMolecularRankPairAt molecule descriptorMap unit graph W' D') :=
  ⟨ruleKey_vecCorr graph (retainedContextNodeObservation molecule graph unit) graph.root
      cover cover',
    stereoComponent_keyCorr graph (retainedContextNodeObservation molecule graph unit)
      (retainedRankEvidence molecule descriptorMap unit graph) .rule4aStereogenicUnitKind
      graph.root cover cover'⟩

/-- **The Rule-5 tagged alternative order is window-free.** The `compare` deciding whether the
junior alternative leads reads complete readings, whose order is window-free. -/
theorem retainedTaggedAlternativeReferencesAt_window {W D W' D' : ℕ}
    (cover : WindowCovers graph W D) (cover' : WindowCovers graph W' D') :
    retainedTaggedAlternativeReferencesAt molecule descriptorMap unit graph W D =
      retainedTaggedAlternativeReferencesAt molecule descriptorMap unit graph W' D' := by
  have reading := retainedCompleteReadingAt_corr molecule descriptorMap unit graph cover cover'
  have agree := readingCorr_faithful W D W' D' (reading (some .senior)) (reading (some .junior))
  unfold retainedTaggedAlternativeReferencesAt
  cases retainedReferenceSelection molecule descriptorMap unit graph with
  | empty => rfl
  | one _ => rfl
  | both =>
      dsimp only
      by_cases h : retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .senior) <
          retainedCompleteReadingAt molecule descriptorMap unit graph W D (some .junior)
      · rw [if_pos ((completeReading_compare_lt_iff _ _).2 h),
          if_pos ((completeReading_compare_lt_iff _ _).2 (agree.1.mp h))]
      · rw [if_neg (fun c => h ((completeReading_compare_lt_iff _ _).1 c)),
          if_neg (fun c => h (agree.1.mpr ((completeReading_compare_lt_iff _ _).1 c)))]

theorem retainedCompleteRule5ReadingsAt_corr {W D W' D' : ℕ}
    (cover : WindowCovers graph W D) (cover' : WindowCovers graph W' D')
    (common : DescriptorSense) :
    List.Forall₂ (KeyCorr W D W' D')
      (retainedCompleteRule5ReadingsAt molecule descriptorMap unit graph W D common)
      (retainedCompleteRule5ReadingsAt molecule descriptorMap unit graph W' D' common) := by
  have reading := retainedCompleteReadingAt_corr molecule descriptorMap unit graph cover cover'
  unfold retainedCompleteRule5ReadingsAt
  rw [retainedTaggedAlternativeReferencesAt_window molecule descriptorMap unit graph cover cover',
    List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.mpr (fun reference _ => ?_)
  cases reference with
  | none =>
      simp only [retainedCompleteRule5ReadingAt]
      exact keyCorr_map _ (reading none).2
  | some own =>
      simp only [retainedCompleteRule5ReadingAt]
      exact keyCorr_map _ (reading (some own)).1

/-- **The retained complete key corresponds across any two covering windows.** -/
theorem retainedCompleteLigandRule5KeyAt_corr {W D W' D' : ℕ}
    (cover : WindowCovers graph W D) (cover' : WindowCovers graph W' D') :
    CompleteKeyCorr W D W' D'
      (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit graph W D)
      (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit graph W' D') :=
  ⟨⟨retainedMolecularRankPairAt_corr molecule descriptorMap unit graph cover cover',
      retainedCompletePriorSignatureAt_corr molecule descriptorMap unit graph cover cover'⟩,
    retainedCompleteRule5ReadingsAt_corr molecule descriptorMap unit graph cover cover' .senior⟩

end Retained

/-- **Window independence of retained comparisons** between two cut graphs: whole keys (through
Rule 5) and their prior keys (through the count / Rule-4b / Rule-4c signature) compare identically
at any two windows covering both graphs. -/
theorem retainedCompleteLigandRule5KeyAt_orderAgrees_window {Atom : Type u} [Fintype Atom]
    [DecidableEq Atom] (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) {left right : RootedDigraph Atom} {W D W' D' : ℕ}
    (coverLeft : WindowCovers left W D) (coverLeft' : WindowCovers left W' D')
    (coverRight : WindowCovers right W D) (coverRight' : WindowCovers right W' D') :
    OrderAgrees (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W D)
        (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W D)
      (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W' D')
        (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W' D') ∧
    OrderAgrees (ofLex (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W D)).1
        (ofLex (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W D)).1
      (ofLex (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W' D')).1
        (ofLex (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W' D')).1 := by
  have hl := retainedCompleteLigandRule5KeyAt_corr molecule descriptorMap unit left
    coverLeft coverLeft'
  have hr := retainedCompleteLigandRule5KeyAt_corr molecule descriptorMap unit right
    coverRight coverRight'
  exact ⟨completeKeyCorr_faithful W D W' D' hl hr, priorCorr_faithful W D W' D' hl.1 hr.1⟩

/-- **Window independence of the retained outcome.** At fixed cut graphs and coordinates, the
retained descriptor outcome (Rules 1a–5, ring duplicates as retained) is the same at any two
windows covering all four cut graphs. -/
theorem retainedContextualOutcomeAt_window {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graphs : Fin 4 → RootedDigraph Atom) {W D W' D' : ℕ}
    (covers : ∀ slot, WindowCovers (graphs slot) W D)
    (covers' : ∀ slot, WindowCovers (graphs slot) W' D')
    (coordinates : Fin 4 → Option CartesianPoint3) (outcome : Option LocalizedAuxiliaryLabel) :
    RetainedContextualOutcomeAt molecule descriptorMap unit graphs W D coordinates outcome ↔
      RetainedContextualOutcomeAt molecule descriptorMap unit graphs W' D' coordinates outcome := by
  have agree := fun a b => retainedCompleteLigandRule5KeyAt_orderAgrees_window molecule
    descriptorMap unit (covers a) (covers' a) (covers b) (covers' b)
  have lt_iff : ∀ a b, retainedContextualFrameKeysAt molecule descriptorMap unit graphs W D a <
      retainedContextualFrameKeysAt molecule descriptorMap unit graphs W D b ↔
        retainedContextualFrameKeysAt molecule descriptorMap unit graphs W' D' a <
          retainedContextualFrameKeysAt molecule descriptorMap unit graphs W' D' b :=
    fun a b => (agree a b).1.1
  have prior_iff : ∀ a b,
      (ofLex (retainedContextualFrameKeysAt molecule descriptorMap unit graphs W D a)).1 =
        (ofLex (retainedContextualFrameKeysAt molecule descriptorMap unit graphs W D b)).1 ↔
      (ofLex (retainedContextualFrameKeysAt molecule descriptorMap unit graphs W' D' a)).1 =
        (ofLex (retainedContextualFrameKeysAt molecule descriptorMap unit graphs W' D' b)).1 :=
    fun a b => (agree a b).2.2
  have judgment : ∀ descriptor,
      RetainedContextualDescriptorJudgmentAt molecule descriptorMap unit graphs W D coordinates
          descriptor ↔
        RetainedContextualDescriptorJudgmentAt molecule descriptorMap unit graphs W' D'
          coordinates descriptor := by
    intro descriptor
    unfold RetainedContextualDescriptorJudgmentAt
    constructor
    · rintro ⟨points, available, holds⟩
      exact ⟨points, available,
        LocalizedRecursiveAuxiliaryPhysicalDomain.completeRootDescriptorJudgment_congr_order
          lt_iff prior_iff holds⟩
    · rintro ⟨points, available, holds⟩
      exact ⟨points, available,
        LocalizedRecursiveAuxiliaryPhysicalDomain.completeRootDescriptorJudgment_congr_order
          (fun a b => (lt_iff a b).symm) (fun a b => (prior_iff a b).symm) holds⟩
  cases outcome with
  | none =>
      simp only [RetainedContextualOutcomeAt]
      exact not_congr (exists_congr judgment)
  | some descriptor =>
      simp only [RetainedContextualOutcomeAt]
      exact judgment descriptor

end

end TetraStereo.OneCenter.DeclarativeCIP

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.vector_orderAgrees_of_pathObservation
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ruleKey_pathObservation_window
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ruleKey_compare_window
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.lex_orderAgrees
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.stereo_pathObservation_window
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryKey_orderAgrees_window
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.keyCorr_faithful
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completeKeyCorr_faithful
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedTaggedAlternativeReferencesAt_window
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteLigandRule5KeyAt_corr
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteLigandRule5KeyAt_orderAgrees_window
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextualOutcomeAt_window
