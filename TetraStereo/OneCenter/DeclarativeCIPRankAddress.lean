import TetraStereo.OneCenter.LocalizedActualRule4aNodeReadback
import TetraStereo.OneCenter.DeclarativeCIPMolecularReferenceSelection
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Rank addresses: the runtime's hierarchy ranks in independent terms

The runtime addresses a node by the list of *sibling ranks* along its ancestor path, where tied
siblings (equal cumulative keys) share a rank and ranks increase with decreasing key.  This module
defines the same notion from the independent ordinary keys alone and proves that, for two nodes of
the same depth, the lexicographic order of rank addresses is the **reverse** of the lexicographic
order of rank paths (`rankAddress_lt_iff`) and equality of rank addresses is equality of rank paths
(`rankAddress_eq_iff`).  This is what lets the rank-addressed population of the actual Rule-4a key
be read as the independent reference class of `DeclarativeCIPMolecularReferenceSelection`.

The one substantive fact is **`rankedOrdinaryKeys_eq_of_ordinaryKey_eq`**: the ordinary key of a
node determines the sorted list of its children's ordinary keys.  It is proved through the
observation language of `Certificate.CanonicalSphereKey`: every component of a child's key is read
off the parent's component one sphere further out (`nodePathObservation_cons`,
`stereoNodePathObservation_cons`), the number of children is read off the never-`⊥` Rule-1a
column, and the deepest level dropped by `assemble` is `⊥` below the graph's height.
-/

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section
open scoped Classical
open Certificate.CanonicalSphereKey (WellShaped key_eq_iff_pathObservation sortDesc sortDesc_perm
  sortDesc_eq_of_perm sortDesc_of_pairwise)
open RootedDigraph

section Children

variable {Atom : Type} [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)
  (graph : RootedDigraph Atom) (evidence : StereochemicalEvidence graph)

local instance rankAddressNodeFintype : Fintype graph.Node := graph.nodeFintype

omit [Fintype Atom] [DecidableEq Atom] in
theorem childList_length_le_width (node : graph.Node) :
    (graph.childList node).length ≤ graph.width :=
  (graph.childList_nodup node).length_le_card

theorem rankedOrdinaryKeys_eq_map (W D : ℕ) (node : graph.Node) {ranked : List graph.Node}
    (hperm : ranked.Perm (graph.childList node))
    (hsorted : (ranked.map (ordinaryKey molecule graph evidence W D)).Pairwise fun x y => y ≤ x) :
    rankedOrdinaryKeys molecule graph evidence W D node =
      ranked.map (ordinaryKey molecule graph evidence W D) := by
  unfold rankedOrdinaryKeys
  rw [sortDesc_eq_of_perm (List.Perm.map _ hperm.symm)]
  exact sortDesc_of_pairwise hsorted

private theorem list_eq_of_length_three {α : Type*} {l m : List α} (hl : l.length = 3)
    (hm : m.length = 3) (h : ∀ r < 3, l[r]? = m[r]?) : l = m := by
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.1 hl
  obtain ⟨a', b', c', rfl⟩ := List.length_eq_three.1 hm
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1 h2
  rw [h0, h1, h2]

/-- The deepest level is `⊥` for a child: its depth plus the level exceeds the height. -/
private theorem nodePathObservation_eq_bot_of_le {W D r : ℕ} (hr : r < 3) (hD : graph.height ≤ D)
    {parent child : graph.Node} (hedge : graph.child parent child) {path : List ℕ}
    (hlen : D ≤ path.length) :
    nodePathObservation molecule graph W D r child path = ⊥ := by
  by_contra hne
  have hbound := depth_add_length_le_of_nodePathObservation molecule graph hr path child hne
  have hdepth := graph.child_depth hedge
  omega

/-- **The ordinary key determines the children's ordinary keys.** -/
theorem rankedOrdinaryKeys_eq_of_ordinaryKey_eq (W D : ℕ) (hW : graph.width ≤ W)
    (hD : graph.height ≤ D) {p q : graph.Node}
    (h : ordinaryKey molecule graph evidence W D p = ordinaryKey molecule graph evidence W D q) :
    rankedOrdinaryKeys molecule graph evidence W D p =
      rankedOrdinaryKeys molecule graph evidence W D q := by
  obtain ⟨rp, hpermp, hsortp⟩ := exists_ordinaryRanked molecule graph evidence W D p
  obtain ⟨rq, hpermq, hsortq⟩ := exists_ordinaryRanked molecule graph evidence W D q
  rw [rankedOrdinaryKeys_eq_map molecule graph evidence W D p hpermp hsortp,
    rankedOrdinaryKeys_eq_map molecule graph evidence W D q hpermq hsortq]
  have hrule : ruleKey molecule graph W D p = ruleKey molecule graph W D q := by
    have := congrArg (fun k => (ofLex k).1) h
    simpa only [ordinaryKey_fst] using this
  have hobsR : ∀ r path, nodePathObservation molecule graph W D r p path =
      nodePathObservation molecule graph W D r q path := by
    intro r path
    unfold nodePathObservation
    rw [hrule]
  have hobsS : ∀ rule path, stereoNodePathObservation molecule graph evidence W D rule p path =
      stereoNodePathObservation molecule graph evidence W D rule q path := by
    intro rule path
    unfold stereoNodePathObservation
    rw [h]
  have hsortRp := ruleKey_sorted_of_ordinary_sorted molecule graph evidence W D hsortp
  have hsortRq := ruleKey_sorted_of_ordinary_sorted molecule graph evidence W D hsortq
  have hlenp : rp.length ≤ W :=
    (hpermp.length_eq.trans_le (childList_length_le_width graph p)).trans hW
  have hlenq : rq.length ≤ W :=
    (hpermq.length_eq.trans_le (childList_length_le_width graph q)).trans hW
  -- the child count is read off the Rule-1a column
  have consR : ∀ (node : graph.Node) (ranked : List graph.Node), ranked.Perm (graph.childList node) →
      (ranked.map (ruleKey molecule graph W D)).Pairwise (fun x y => y ≤ x) →
      ∀ (i : ℕ) (path : List ℕ), i < W → path.length < D →
        nodePathObservation molecule graph W D 0 node (i :: path) =
          ((ranked[i]?).map fun child => nodePathObservation molecule graph W D 0 child path).getD ⊥ :=
    fun node ranked hperm hsorted i path hi hpath => by
      rw [nodePathObservation_cons molecule graph (by omega) node hperm hsorted, if_pos ⟨hi, hpath⟩]
  have childDepthPos : ∀ (node : graph.Node) (ranked : List graph.Node),
      ranked.Perm (graph.childList node) → ∀ (i : ℕ) (hi : i < ranked.length), 0 < D := by
    intro node ranked hperm i hi
    have hedge := (graph.mem_childList).1 (hperm.subset (List.getElem_mem hi))
    have := graph.child_depth hedge
    have := graph.depth_le_height ranked[i]
    omega
  have lengthLe : ∀ (a b : graph.Node) (ra rb : List graph.Node), ra.Perm (graph.childList a) →
      rb.Perm (graph.childList b) →
      (ra.map (ruleKey molecule graph W D)).Pairwise (fun x y => y ≤ x) →
      (rb.map (ruleKey molecule graph W D)).Pairwise (fun x y => y ≤ x) → ra.length ≤ W →
      (∀ path, nodePathObservation molecule graph W D 0 a path =
        nodePathObservation molecule graph W D 0 b path) →
      ra.length ≤ rb.length := by
    intro a b ra rb hpa hpb hsa hsb hla hobs
    by_contra hlt
    push_neg at hlt
    have hDpos := childDepthPos a ra hpa rb.length hlt
    have hobs' := hobs (rb.length :: [])
    rw [consR a ra hpa hsa _ [] (by omega) (by simpa using hDpos),
      consR b rb hpb hsb _ [] (by omega) (by simpa using hDpos)] at hobs'
    rw [List.getElem?_eq_getElem hlt, List.getElem?_eq_none_iff.2 le_rfl] at hobs'
    simp only [Option.map_some, Option.getD_some, Option.map_none, Option.getD_none] at hobs'
    rw [nodePathObservation_nil molecule graph (by omega)] at hobs'
    exact WithBot.coe_ne_bot hobs'
  have hlen : rp.length = rq.length :=
    le_antisymm (lengthLe p q rp rq hpermp hpermq hsortRp hsortRq hlenp (hobsR 0))
      (lengthLe q p rq rp hpermq hpermp hsortRq hsortRp hlenq fun path => (hobsR 0 path).symm)
  -- each child's key is read off the parent's components
  apply List.ext_getElem (by simp [hlen])
  intro i hi hi'
  simp only [List.getElem_map]
  rw [List.length_map] at hi hi'
  have hedgep := (graph.mem_childList).1 (hpermp.subset (List.getElem_mem hi))
  have hedgeq := (graph.mem_childList).1 (hpermq.subset (List.getElem_mem hi'))
  have hiW : i < W := by omega
  -- rule components
  have ruleObs : ∀ r, r < 3 → ∀ path, nodePathObservation molecule graph W D r rp[i] path =
      nodePathObservation molecule graph W D r rq[i] path := by
    intro r hr path
    by_cases hpath : path.length < D
    · have hp := nodePathObservation_cons molecule graph hr p hpermp hsortRp i path
      have hq := nodePathObservation_cons molecule graph hr q hpermq hsortRq i path
      rw [if_pos ⟨hiW, hpath⟩, List.getElem?_eq_getElem hi] at hp
      rw [if_pos ⟨hiW, hpath⟩, List.getElem?_eq_getElem hi'] at hq
      simp only [Option.map_some, Option.getD_some] at hp hq
      rw [← hp, ← hq, hobsR]
    · push_neg at hpath
      rw [nodePathObservation_eq_bot_of_le molecule graph hr hD hedgep hpath,
        nodePathObservation_eq_bot_of_le molecule graph hr hD hedgeq hpath]
  have stereoObs : ∀ rule path,
      stereoNodePathObservation molecule graph evidence W D rule rp[i] path =
        stereoNodePathObservation molecule graph evidence W D rule rq[i] path := by
    intro rule path
    by_cases hpath : path.length < D
    · have hp := stereoNodePathObservation_cons molecule graph evidence W D rule p hpermp hsortp i path
      have hq := stereoNodePathObservation_cons molecule graph evidence W D rule q hpermq hsortq i path
      rw [if_pos ⟨hiW, hpath⟩, List.getElem?_eq_getElem hi] at hp
      rw [if_pos ⟨hiW, hpath⟩, List.getElem?_eq_getElem hi'] at hq
      simp only [Option.map_some, Option.getD_some] at hp hq
      rw [← hp, ← hq, hobsS]
    · push_neg at hpath
      rw [(Rule4aTableBridge.stereoNodePathObservation_eq_bot_iff molecule graph evidence rule W D path rp[i]).2
          (nodePathObservation_eq_bot_of_le molecule graph (by omega) hD hedgep hpath),
        (Rule4aTableBridge.stereoNodePathObservation_eq_bot_iff molecule graph evidence rule W D path rq[i]).2
          (nodePathObservation_eq_bot_of_le molecule graph (by omega) hD hedgeq hpath)]
  have ruleEq : ruleKey molecule graph W D rp[i] = ruleKey molecule graph W D rq[i] := by
    apply list_eq_of_length_three (ruleKey_length molecule graph W D _) (ruleKey_length molecule graph W D _)
    intro r hr
    rw [List.getElem?_eq_getElem (by rw [ruleKey_length]; exact hr),
      List.getElem?_eq_getElem (by rw [ruleKey_length]; exact hr)]
    congr 1
    rw [← List.getD_eq_getElem (d := []), ← List.getD_eq_getElem (d := [])]
    exact (key_eq_iff_pathObservation ((ruleKey_vectorWellShaped molecule graph W D _).2 r hr)
      ((ruleKey_vectorWellShaped molecule graph W D _).2 r hr)).2 (ruleObs r hr)
  have stereoEq : ∀ rule,
      (ofLex (ordinaryKey molecule graph evidence W D rp[i])).2.getD (stereoIndex rule) [] =
        (ofLex (ordinaryKey molecule graph evidence W D rq[i])).2.getD (stereoIndex rule) [] :=
    fun rule => (key_eq_iff_pathObservation
      (ordinaryKey_stereo_wellShaped molecule graph evidence W D rule _)
      (ordinaryKey_stereo_wellShaped molecule graph evidence W D rule _)).2 (stereoObs rule)
  rw [← toLex_ofLex (ordinaryKey molecule graph evidence W D rp[i]),
    ← toLex_ofLex (ordinaryKey molecule graph evidence W D rq[i])]
  congr 1
  refine Prod.ext ?_ ?_
  · simpa only [ordinaryKey_fst] using ruleEq
  · rw [ordinaryKey_stereo_eq molecule graph evidence W D rp[i],
      ordinaryKey_stereo_eq molecule graph evidence W D rq[i]]
    simp only [List.cons.injEq, and_true]
    exact ⟨stereoEq .rule3DoubleBondGeometry, stereoEq .rule4aStereogenicUnitKind,
      stereoEq .rule4bLikeUnlikeDescriptorPairs, stereoEq .rule4cPseudoasymmetricDescriptor,
      stereoEq .rule5EnantiomorphicDescriptor⟩

end Children

/-! ## Rank indices -/

section RankIndex

/-- The rank of a key among a sibling key list: the number of distinct sibling keys strictly
greater than it.  Tied keys share a rank; the greatest key has rank `0`. -/
def rankIndexIn (keys : List OrdinaryKey) (key : OrdinaryKey) : ℕ :=
  (keys.toFinset.filter fun k => key < k).card

theorem rankIndexIn_lt_of_lt {keys : List OrdinaryKey} {first second : OrdinaryKey}
    (hfirst : first ∈ keys) (h : second < first) :
    rankIndexIn keys first < rankIndexIn keys second := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨first, ?_, ?_⟩
    · simp only [Finset.mem_filter, List.mem_toFinset]
      exact ⟨hfirst, h⟩
    · simp
  · intro k hk
    simp only [Finset.mem_filter, List.mem_toFinset] at hk ⊢
    exact ⟨hk.1, h.trans hk.2⟩

theorem rankIndexIn_lt_iff {keys : List OrdinaryKey} {first second : OrdinaryKey}
    (hfirst : first ∈ keys) (hsecond : second ∈ keys) :
    rankIndexIn keys first < rankIndexIn keys second ↔ second < first := by
  constructor
  · intro h
    rcases lt_trichotomy first second with hlt | heq | hgt
    · exact absurd (h.trans (rankIndexIn_lt_of_lt hsecond hlt)) (lt_irrefl _)
    · subst heq; exact absurd h (lt_irrefl _)
    · exact hgt
  · exact rankIndexIn_lt_of_lt hfirst

theorem rankIndexIn_eq_iff {keys : List OrdinaryKey} {first second : OrdinaryKey}
    (hfirst : first ∈ keys) (hsecond : second ∈ keys) :
    rankIndexIn keys first = rankIndexIn keys second ↔ first = second := by
  constructor
  · intro h
    rcases lt_trichotomy first second with hlt | heq | hgt
    · exact absurd (h ▸ rankIndexIn_lt_of_lt hsecond hlt) (lt_irrefl _)
    · exact heq
    · exact absurd (h ▸ rankIndexIn_lt_of_lt hfirst hgt) (lt_irrefl _)
  · rintro rfl; rfl

end RankIndex

/-! ## Lexicographic lists extended by one element -/

section Lex

variable {α : Type*} [LinearOrder α]

private theorem not_lex_nil_right (l : List α) : ¬ List.Lex (· < ·) l [] := fun h => by cases h

theorem lex_append_singleton_iff :
    ∀ (l l' : List α), l.length = l'.length → ∀ (x y : α),
      List.Lex (· < ·) (l ++ [x]) (l' ++ [y]) ↔ List.Lex (· < ·) l l' ∨ (l = l' ∧ x < y)
  | [], [], _, x, y => by
      simp only [List.nil_append, List.cons_lex_cons_iff, true_and]
      constructor
      · rintro (h | ⟨_, h⟩)
        · exact Or.inr h
        · exact absurd h (not_lex_nil_right _)
      · rintro (h | h)
        · exact absurd h (not_lex_nil_right _)
        · exact Or.inl h
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | a :: l, b :: l', h, x, y => by
      simp only [List.cons_append, List.cons_lex_cons_iff, List.cons.injEq]
      rw [lex_append_singleton_iff l l' (by simpa using h) x y]
      tauto

omit [LinearOrder α] in
theorem append_singleton_eq_iff (l l' : List α) (h : l.length = l'.length) (x y : α) :
    l ++ [x] = l' ++ [y] ↔ l = l' ∧ x = y := by
  constructor
  · intro he
    obtain ⟨hl, hx⟩ := List.append_inj he h
    exact ⟨hl, List.singleton_inj.1 hx⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- `<` on lists of a linear order is the lexicographic relation. -/
theorem list_lt_iff_lex (l l' : List α) : l < l' ↔ List.Lex (· < ·) l l' := Iff.rfl

end Lex

/-! ## Rank addresses along ancestor chains -/

section Chains

variable {Atom : Type} [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)
  (graph : RootedDigraph Atom) (evidence : StereochemicalEvidence graph)

local instance rankAddressNodeFintype2 : Fintype graph.Node := graph.nodeFintype

/-- Ranks along a root-first chain of nodes: the rank of each node among its predecessor's
children. -/
def chainRankAddress (W D : ℕ) : List graph.Node → List ℕ
  | [] => []
  | [_] => []
  | a :: b :: rest =>
      rankIndexIn (rankedOrdinaryKeys molecule graph evidence W D a)
          (ordinaryKey molecule graph evidence W D b) ::
        chainRankAddress W D (b :: rest)

theorem chainRankAddress_append (W D : ℕ) :
    ∀ (chain : List graph.Node) (hne : chain ≠ []) (node : graph.Node),
      chainRankAddress molecule graph evidence W D (chain ++ [node]) =
        chainRankAddress molecule graph evidence W D chain ++
          [rankIndexIn (rankedOrdinaryKeys molecule graph evidence W D (chain.getLast hne))
            (ordinaryKey molecule graph evidence W D node)]
  | [], hne, _ => absurd rfl hne
  | [a], _, node => rfl
  | a :: b :: rest, _, node => by
      simp only [List.cons_append, chainRankAddress, List.getLast_cons_cons]
      rw [show b :: (rest ++ [node]) = (b :: rest) ++ [node] from rfl,
        chainRankAddress_append W D (b :: rest) (List.cons_ne_nil b rest) node]

omit [Fintype Atom] [DecidableEq Atom] in
theorem AncestorChain.length {node : graph.Node} {chain : List graph.Node}
    (h : AncestorChain graph node chain) : chain.length = graph.depth node + 1 := by
  induction h with
  | root => simp [graph.root_depth]
  | step hedge _ ih => simp [ih, graph.child_depth hedge]

omit [Fintype Atom] [DecidableEq Atom] in
theorem AncestorChain.ne_nil {node : graph.Node} {chain : List graph.Node}
    (h : AncestorChain graph node chain) : chain ≠ [] := by
  intro hnil
  have := AncestorChain.length graph h
  rw [hnil] at this
  simp at this

omit [Fintype Atom] [DecidableEq Atom] in
theorem AncestorChain.getLast {node : graph.Node} {chain : List graph.Node}
    (h : AncestorChain graph node chain) : chain.getLast (AncestorChain.ne_nil graph h) = node := by
  cases h with
  | root => rfl
  | step _ _ => simp

theorem AncestorChain.chainRankAddress_step (W D : ℕ) {parent node : graph.Node}
    {chain : List graph.Node} (_hedge : graph.child parent node)
    (hchain : AncestorChain graph parent chain) :
    chainRankAddress molecule graph evidence W D (chain ++ [node]) =
      chainRankAddress molecule graph evidence W D chain ++
        [rankIndexIn (rankedOrdinaryKeys molecule graph evidence W D parent)
          (ordinaryKey molecule graph evidence W D node)] := by
  rw [chainRankAddress_append molecule graph evidence W D chain (AncestorChain.ne_nil graph hchain)
    node, AncestorChain.getLast graph hchain]

theorem ordinaryKey_mem_rankedOrdinaryKeys (W D : ℕ) {parent node : graph.Node}
    (hedge : graph.child parent node) :
    ordinaryKey molecule graph evidence W D node ∈
      rankedOrdinaryKeys molecule graph evidence W D parent := by
  unfold rankedOrdinaryKeys
  rw [(sortDesc_perm _).mem_iff]
  exact List.mem_map_of_mem ((graph.mem_childList).2 hedge)

/-- **Rank addresses reverse rank paths.**  Along two ancestor chains of equal length, the rank
address list is lexicographically smaller exactly when the key list is lexicographically greater,
and the two agree exactly when the key lists agree. -/
theorem chainRankAddress_order (W D : ℕ) (hW : graph.width ≤ W) (hD : graph.height ≤ D) :
    ∀ {n : graph.Node} {cn : List graph.Node}, AncestorChain graph n cn →
      ∀ {m : graph.Node} {cm : List graph.Node}, AncestorChain graph m cm → cn.length = cm.length →
        (List.Lex (· < ·) (chainRankAddress molecule graph evidence W D cn)
            (chainRankAddress molecule graph evidence W D cm) ↔
          List.Lex (· < ·) (cm.map (ordinaryKey molecule graph evidence W D))
            (cn.map (ordinaryKey molecule graph evidence W D))) ∧
        (chainRankAddress molecule graph evidence W D cn =
            chainRankAddress molecule graph evidence W D cm ↔
          cn.map (ordinaryKey molecule graph evidence W D) =
            cm.map (ordinaryKey molecule graph evidence W D)) := by
  intro n cn hn
  induction hn with
  | root =>
      intro m cm hm hlen
      cases hm with
      | root =>
          refine ⟨⟨(fun h => nomatch h), fun h => ?_⟩, ⟨fun _ => rfl, fun _ => rfl⟩⟩
          cases h with
          | rel h => exact absurd h (lt_irrefl _)
          | cons h => cases h
      | step _ hchain =>
          exfalso
          have h1 := AncestorChain.length graph hchain
          simp only [List.length_cons, List.length_append,
            List.length_nil] at hlen
          omega
  | step hedge hchain ih =>
      intro m cm hm hlen
      rename_i parent node chain
      cases hm with
      | root =>
          exfalso
          have h1 := AncestorChain.length graph hchain
          simp only [List.length_cons, List.length_append,
            List.length_nil] at hlen
          omega
      | step hedge' hchain' =>
          rename_i parent' chain'
          have hlen' : chain.length = chain'.length := by simpa using hlen
          obtain ⟨ihLt, ihEq⟩ := ih hchain' hlen'
          rw [AncestorChain.chainRankAddress_step molecule graph evidence W D hedge hchain,
            AncestorChain.chainRankAddress_step molecule graph evidence W D hedge' hchain',
            List.map_append, List.map_append, List.map_singleton, List.map_singleton]
          have hlenA : (chainRankAddress molecule graph evidence W D chain).length =
              (chainRankAddress molecule graph evidence W D chain').length := by
            by_contra hne
            -- lengths of rank addresses are chain lengths minus one
            have : ∀ (c : List graph.Node), (chainRankAddress molecule graph evidence W D c).length =
                c.length - 1 := by
              intro c
              induction c with
              | nil => rfl
              | cons a rest ih' =>
                  cases rest with
                  | nil => rfl
                  | cons b rest' => simp [chainRankAddress, ih']
            exact hne (by rw [this, this, hlen'])
          have hlenP : (chain.map (ordinaryKey molecule graph evidence W D)).length =
              (chain'.map (ordinaryKey molecule graph evidence W D)).length := by
            simpa using hlen'
          rw [lex_append_singleton_iff _ _ hlenA, lex_append_singleton_iff _ _ hlenP.symm,
            append_singleton_eq_iff _ _ hlenA, append_singleton_eq_iff _ _ hlenP]
          -- equal parent chains force equal parent keys, hence equal sibling key lists
          have parentKey : chain.map (ordinaryKey molecule graph evidence W D) =
              chain'.map (ordinaryKey molecule graph evidence W D) →
              rankedOrdinaryKeys molecule graph evidence W D parent =
                rankedOrdinaryKeys molecule graph evidence W D parent' := by
            intro hmap
            have hlast := congrArg List.getLast? hmap
            rw [List.getLast?_map, List.getLast?_map, List.getLast?_eq_some_getLast
              (AncestorChain.ne_nil graph hchain), List.getLast?_eq_some_getLast
              (AncestorChain.ne_nil graph hchain'), AncestorChain.getLast graph hchain,
              AncestorChain.getLast graph hchain'] at hlast
            simp only [Option.map_some, Option.some.injEq] at hlast
            exact rankedOrdinaryKeys_eq_of_ordinaryKey_eq molecule graph evidence W D hW hD hlast
          have memN := ordinaryKey_mem_rankedOrdinaryKeys molecule graph evidence W D hedge
          have memM := ordinaryKey_mem_rankedOrdinaryKeys molecule graph evidence W D hedge'
          constructor
          · constructor
            · rintro (h | ⟨heq, hlt⟩)
              · exact Or.inl (ihLt.1 h)
              · have hkeys := parentKey (ihEq.1 heq)
                rw [hkeys] at hlt
                exact Or.inr ⟨(ihEq.1 heq).symm, (rankIndexIn_lt_iff (hkeys ▸ memN) memM).1 hlt⟩
            · rintro (h | ⟨heq, hlt⟩)
              · exact Or.inl (ihLt.2 h)
              · have hkeys := parentKey heq.symm
                refine Or.inr ⟨ihEq.2 heq.symm, ?_⟩
                rw [hkeys]
                exact (rankIndexIn_lt_iff (hkeys ▸ memN) memM).2 hlt
          · constructor
            · rintro ⟨heq, hidx⟩
              have hkeys := parentKey (ihEq.1 heq)
              rw [hkeys] at hidx
              exact ⟨ihEq.1 heq, (rankIndexIn_eq_iff (hkeys ▸ memN) memM).1 hidx⟩
            · rintro ⟨heq, hkey⟩
              have hkeys := parentKey heq
              refine ⟨ihEq.2 heq, ?_⟩
              rw [hkeys, hkey]

/-- The rank address of a node: its ranks along its (unique) ancestor chain. -/
def rankAddress (W D : ℕ) (node : graph.Node) : List ℕ :=
  chainRankAddress molecule graph evidence W D (ancestorChain graph node)

theorem rankAddress_lt_iff (addressing : graph.Addressing) (W D : ℕ) (hW : graph.width ≤ W)
    (hD : graph.height ≤ D) {n m : graph.Node} (hdepth : graph.depth n = graph.depth m) :
    rankAddress molecule graph evidence W D n < rankAddress molecule graph evidence W D m ↔
      (ancestorChain graph m).map (ordinaryKey molecule graph evidence W D) <
        (ancestorChain graph n).map (ordinaryKey molecule graph evidence W D) := by
  have hn := ancestorChain_spec_of_addressing graph addressing n
  have hm := ancestorChain_spec_of_addressing graph addressing m
  have hlen : (ancestorChain graph n).length = (ancestorChain graph m).length := by
    rw [AncestorChain.length graph hn, AncestorChain.length graph hm, hdepth]
  exact (chainRankAddress_order molecule graph evidence W D hW hD hn hm hlen).1

theorem rankAddress_eq_iff (addressing : graph.Addressing) (W D : ℕ) (hW : graph.width ≤ W)
    (hD : graph.height ≤ D) {n m : graph.Node} (hdepth : graph.depth n = graph.depth m) :
    rankAddress molecule graph evidence W D n = rankAddress molecule graph evidence W D m ↔
      (ancestorChain graph n).map (ordinaryKey molecule graph evidence W D) =
        (ancestorChain graph m).map (ordinaryKey molecule graph evidence W D) := by
  have hn := ancestorChain_spec_of_addressing graph addressing n
  have hm := ancestorChain_spec_of_addressing graph addressing m
  have hlen : (ancestorChain graph n).length = (ancestorChain graph m).length := by
    rw [AncestorChain.length graph hn, AncestorChain.length graph hm, hdepth]
  exact (chainRankAddress_order molecule graph evidence W D hW hD hn hm hlen).2

end Chains

/-! ## Specialisation to the reference-selection rank path -/

section Molecular

variable {Atom : Type} [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

local instance rankAddressNodeFintype3 : Fintype graph.Node := graph.nodeFintype

/-- The rank address for the pre-Rule-4b evidence at the graph's own layout. -/
def referenceRankAddress (node : graph.Node) : List ℕ :=
  rankAddress molecule graph (rankEvidence molecule descriptorMap unit graph) graph.width
    graph.height node

theorem referenceRankAddress_lt_iff (addressing : graph.Addressing) {n m : graph.Node}
    (hdepth : graph.depth n = graph.depth m) :
    referenceRankAddress molecule descriptorMap unit graph n <
        referenceRankAddress molecule descriptorMap unit graph m ↔
      rankPath molecule descriptorMap unit graph m < rankPath molecule descriptorMap unit graph n :=
  rankAddress_lt_iff molecule graph _ addressing _ _ le_rfl le_rfl hdepth

theorem referenceRankAddress_eq_iff (addressing : graph.Addressing) {n m : graph.Node}
    (hdepth : graph.depth n = graph.depth m) :
    referenceRankAddress molecule descriptorMap unit graph n =
        referenceRankAddress molecule descriptorMap unit graph m ↔
      rankPath molecule descriptorMap unit graph n = rankPath molecule descriptorMap unit graph m :=
  rankAddress_eq_iff molecule graph _ addressing _ _ le_rfl le_rfl hdepth

end Molecular

end
end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.rankedOrdinaryKeys_eq_of_ordinaryKey_eq
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.chainRankAddress_order
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.referenceRankAddress_lt_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.referenceRankAddress_eq_iff
