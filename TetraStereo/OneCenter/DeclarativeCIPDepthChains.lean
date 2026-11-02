import TetraStereo.OneCenter.DeclarativeCIPRankAddress
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Slot-ordered descendant enumeration of a dense addressing

For a dense addressing, `depthChains d start` lists the root-first chains from `start` to each of
its descendants `d` levels below, in sibling-slot order (the order in which the runtime merges
label spheres); `depthNodes d start` lists the endpoints.  We prove that `depthNodes d root`
enumerates exactly the nodes of depth `d`, without repetition (`mem_depthNodes_root_iff`,
`depthNodes_nodup`), and that the rank address of an endpoint is `chainRankAddress` of its chain
(`rankAddress_eq_chainRankAddress_of_mem`).

The module also records the generic rank recursion `headRanks`/`tailRanks` — the runtime's
adjacent-tie rank assignment transcribed to ordinary keys — and proves that on a descending key
list it computes `rankIndexIn` (`headRanks_eq_map_rankIndexIn`).
-/

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section
open scoped Classical
open RootedDigraph

/-! ## Generic adjacent-tie ranks -/

section Ranks

/-- Ranks of a key list continued after `prev` at rank `rank`: a key equal to its predecessor
keeps the rank, any other key increments it. -/
def tailRanks (prev : OrdinaryKey) (rank : ℕ) : List OrdinaryKey → List ℕ
  | [] => []
  | key :: keys =>
      let next := if key = prev then rank else rank + 1
      next :: tailRanks key next keys

def headRanks : List OrdinaryKey → List ℕ
  | [] => []
  | key :: keys => 0 :: tailRanks key 0 keys

theorem rankIndexIn_eq_zero_of_max {keys : List OrdinaryKey} {key : OrdinaryKey}
    (hmax : ∀ x ∈ keys, x ≤ key) : rankIndexIn keys key = 0 := by
  unfold rankIndexIn
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx
  rw [List.mem_toFinset] at hx
  exact not_lt.2 (hmax x hx)

theorem rankIndexIn_succ {keys : List OrdinaryKey} {prev key : OrdinaryKey} (hprev : prev ∈ keys)
    (hlt : key < prev) (hgap : ∀ x ∈ keys, key < x → prev ≤ x) :
    rankIndexIn keys key = rankIndexIn keys prev + 1 := by
  unfold rankIndexIn
  have hset : keys.toFinset.filter (fun x => key < x) =
      insert prev (keys.toFinset.filter fun x => prev < x) := by
    ext x
    simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_insert]
    constructor
    · rintro ⟨hx, hkx⟩
      rcases eq_or_lt_of_le (hgap x hx hkx) with h | h
      · exact Or.inl h.symm
      · exact Or.inr ⟨hx, h⟩
    · rintro (rfl | ⟨hx, hpx⟩)
      · exact ⟨hprev, hlt⟩
      · exact ⟨hx, hlt.trans hpx⟩
  rw [hset, Finset.card_insert_of_notMem]
  simp

theorem tailRanks_eq_map_rankIndexIn (full : List OrdinaryKey)
    (hsorted : full.Pairwise fun x y => y ≤ x) :
    ∀ (pre : List OrdinaryKey) (prev : OrdinaryKey) (keys : List OrdinaryKey),
      full = pre ++ prev :: keys →
        tailRanks prev (rankIndexIn full prev) keys = keys.map (rankIndexIn full)
  | _, _, [], _ => rfl
  | pre, prev, key :: keys, hfull => by
      have hsorted' := hsorted
      rw [hfull, List.pairwise_append, List.pairwise_cons, List.pairwise_cons] at hsorted'
      obtain ⟨_, ⟨hprevRest, hkeyRest, _⟩, hcross⟩ := hsorted'
      have hprevMem : prev ∈ full := by rw [hfull]; simp
      have hkeyLe : key ≤ prev := hprevRest key List.mem_cons_self
      have hrank : rankIndexIn full key =
          if key = prev then rankIndexIn full prev else rankIndexIn full prev + 1 := by
        split_ifs with heq
        · rw [heq]
        · apply rankIndexIn_succ hprevMem (lt_of_le_of_ne hkeyLe heq)
          intro x hx hkx
          rw [hfull, List.mem_append, List.mem_cons, List.mem_cons] at hx
          rcases hx with hx | rfl | rfl | hx
          · exact hcross x hx prev List.mem_cons_self
          · exact le_rfl
          · exact absurd hkx (lt_irrefl _)
          · exact absurd (lt_of_lt_of_le hkx (hkeyRest x hx)) (lt_irrefl _)
      simp only [tailRanks, List.map_cons]
      rw [← hrank]
      congr 1
      exact tailRanks_eq_map_rankIndexIn full hsorted (pre ++ [prev]) key keys (by simp [hfull])

/-- **Adjacent-tie ranks are rank indices** on a descending key list. -/
theorem headRanks_eq_map_rankIndexIn (keys : List OrdinaryKey)
    (hsorted : keys.Pairwise fun x y => y ≤ x) :
    headRanks keys = keys.map (rankIndexIn keys) := by
  cases keys with
  | nil => rfl
  | cons key rest =>
      simp only [headRanks, List.map_cons]
      have hzero : rankIndexIn (key :: rest) key = 0 :=
        rankIndexIn_eq_zero_of_max fun x hx => by
          rcases List.mem_cons.1 hx with rfl | hx
          · exact le_rfl
          · exact (List.pairwise_cons.1 hsorted).1 x hx
      rw [hzero]
      congr 1
      have := tailRanks_eq_map_rankIndexIn (key :: rest) hsorted [] key rest rfl
      rwa [hzero] at this

end Ranks

/-! ## Descendant chains -/

section Enumeration

variable {Atom : Type} [Fintype Atom] [DecidableEq Atom] (graph : RootedDigraph Atom)

local instance depthChainsNodeFintype : Fintype graph.Node := graph.nodeFintype

omit [Fintype Atom] [DecidableEq Atom] in
theorem denseAt_childList_length {addressing : graph.Addressing} (hdense : Dense addressing)
    (node : graph.Node) : DenseAt addressing node (graph.childList node).length := by
  obtain ⟨count, h⟩ := hdense node
  have hlen := (slotList_perm h).length_eq
  simp only [slotList, List.length_map, List.length_range] at hlen
  rw [← hlen]
  exact h

omit [Fintype Atom] [DecidableEq Atom] in
theorem slotList_childList_perm {addressing : graph.Addressing} (hdense : Dense addressing)
    (node : graph.Node) :
    (slotList addressing node (graph.childList node).length).Perm (graph.childList node) :=
  slotList_perm (denseAt_childList_length graph hdense node)

/-- Slot-ordered chains from `start` to its descendants `d` levels below. -/
def depthChains (addressing : graph.Addressing) : ℕ → graph.Node → List (List graph.Node)
  | 0, start => [[start]]
  | d + 1, start =>
      (slotList addressing start (graph.childList start).length).flatMap fun child =>
        (depthChains addressing d child).map (start :: ·)

/-- Slot-ordered descendants of `start` exactly `d` levels below. -/
def depthNodes (addressing : graph.Addressing) : ℕ → graph.Node → List graph.Node
  | 0, start => [start]
  | d + 1, start =>
      (slotList addressing start (graph.childList start).length).flatMap fun child =>
        depthNodes addressing d child

omit [Fintype Atom] [DecidableEq Atom] in
theorem mem_depthChains_shape (addressing : graph.Addressing) :
    ∀ (d : ℕ) (start : graph.Node) (chain : List graph.Node),
      chain ∈ depthChains graph addressing d start →
        chain ≠ [] ∧ chain.head? = some start ∧ chain.length = d + 1
  | 0, start, chain, h => by
      simp only [depthChains, List.mem_singleton] at h
      subst h
      exact ⟨List.cons_ne_nil _ _, rfl, rfl⟩
  | d + 1, start, chain, h => by
      simp only [depthChains, List.mem_flatMap, List.mem_map] at h
      obtain ⟨child, _, chain', hchain', rfl⟩ := h
      have := (mem_depthChains_shape addressing d child chain' hchain').2.2
      exact ⟨List.cons_ne_nil _ _, rfl, by simp [this]⟩

omit [Fintype Atom] [DecidableEq Atom] in
theorem depthChains_getLastD (addressing : graph.Addressing) :
    ∀ (d : ℕ) (start : graph.Node),
      (depthChains graph addressing d start).map (fun chain => chain.getLastD start) =
        depthNodes graph addressing d start
  | 0, start => rfl
  | d + 1, start => by
      simp only [depthChains, depthNodes, List.map_flatMap, List.map_map]
      congr 1
      funext child
      rw [← depthChains_getLastD addressing d child]
      apply List.map_congr_left
      intro chain hchain
      obtain ⟨hne, _, _⟩ := mem_depthChains_shape graph addressing d child chain hchain
      show (start :: chain).getLastD start = chain.getLastD child
      cases chain with
      | nil => exact absurd rfl hne
      | cons a rest =>
          simp only [List.getLastD_eq_getLast?, List.getLast?_cons_cons]
          cases hx : (a :: rest).getLast? with
          | none => exact absurd hx (by simp)
          | some x => rfl

omit [Fintype Atom] [DecidableEq Atom] in
theorem mem_childList_of_mem_slotList {addressing : graph.Addressing} (hdense : Dense addressing)
    {start child : graph.Node}
    (h : child ∈ slotList addressing start (graph.childList start).length) :
    graph.child start child :=
  (graph.mem_childList).1 ((slotList_childList_perm graph hdense start).subset h)

omit [Fintype Atom] [DecidableEq Atom] in
theorem depth_le_of_reflTransGen {a b : graph.Node} (h : Relation.ReflTransGen graph.child a b) :
    graph.depth a ≤ graph.depth b := by
  induction h with
  | refl => exact le_rfl
  | tail _ hedge ih => rw [graph.child_depth hedge]; omega

omit [Fintype Atom] [DecidableEq Atom] in
theorem eq_of_reflTransGen_of_depth_eq {a b : graph.Node}
    (h : Relation.ReflTransGen graph.child a b) (hdepth : graph.depth a = graph.depth b) : a = b := by
  cases h with
  | refl => rfl
  | tail hrest hedge =>
      exfalso
      have := depth_le_of_reflTransGen graph hrest
      have := graph.child_depth hedge
      omega

omit [Fintype Atom] [DecidableEq Atom] in
/-- **Enumeration.**  `depthNodes d start` lists exactly the descendants of `start` `d` levels
below. -/
theorem mem_depthNodes_iff {addressing : graph.Addressing} (hdense : Dense addressing) :
    ∀ (d : ℕ) (start node : graph.Node),
      node ∈ depthNodes graph addressing d start ↔
        Relation.ReflTransGen graph.child start node ∧ graph.depth node = graph.depth start + d
  | 0, start, node => by
      simp only [depthNodes, List.mem_singleton, Nat.add_zero]
      constructor
      · rintro rfl; exact ⟨Relation.ReflTransGen.refl, rfl⟩
      · rintro ⟨h, hdepth⟩
        exact (eq_of_reflTransGen_of_depth_eq graph h hdepth.symm).symm
  | d + 1, start, node => by
      simp only [depthNodes, List.mem_flatMap]
      constructor
      · rintro ⟨child, hchild, hmem⟩
        have hedge := mem_childList_of_mem_slotList graph hdense hchild
        obtain ⟨hrtg, hdepth⟩ := (mem_depthNodes_iff hdense d child node).1 hmem
        refine ⟨Relation.ReflTransGen.head hedge hrtg, ?_⟩
        rw [hdepth, graph.child_depth hedge]
        omega
      · rintro ⟨hrtg, hdepth⟩
        rcases Relation.ReflTransGen.cases_head hrtg with rfl | ⟨child, hedge, hrest⟩
        · omega
        · refine ⟨child, ?_, (mem_depthNodes_iff hdense d child node).2 ⟨hrest, ?_⟩⟩
          · exact (slotList_childList_perm graph hdense start).mem_iff.2
              ((graph.mem_childList).2 hedge)
          · rw [hdepth, graph.child_depth hedge]
            omega

omit [Fintype Atom] [DecidableEq Atom] in
theorem ancestorChain_of_reflTransGen {c n : graph.Node} {chain : List graph.Node}
    (hchain : AncestorChain graph c chain) (h : Relation.ReflTransGen graph.child c n) :
    ∃ suffix, AncestorChain graph n (chain ++ suffix) := by
  induction h with
  | refl => exact ⟨[], by simpa using hchain⟩
  | tail _ hedge ih =>
      obtain ⟨suffix, hsuffix⟩ := ih
      exact ⟨suffix ++ [_], by rw [← List.append_assoc]; exact AncestorChain.step hedge hsuffix⟩

omit [Fintype Atom] [DecidableEq Atom] in
/-- Two ancestors of the same node at the same depth coincide. -/
theorem ancestor_eq_of_depth_eq (addressing : graph.Addressing) {c c' n : graph.Node}
    (h : Relation.ReflTransGen graph.child c n) (h' : Relation.ReflTransGen graph.child c' n)
    (hdepth : graph.depth c = graph.depth c') : c = c' := by
  obtain ⟨cc, hcc⟩ := exists_ancestorChain graph c
  obtain ⟨cc', hcc'⟩ := exists_ancestorChain graph c'
  obtain ⟨s, hs⟩ := ancestorChain_of_reflTransGen graph hcc h
  obtain ⟨s', hs'⟩ := ancestorChain_of_reflTransGen graph hcc' h'
  have heq := ancestorChain_unique_of_addressing graph addressing hs hs'
  have hlen : cc.length = cc'.length := by
    rw [AncestorChain.length graph hcc, AncestorChain.length graph hcc', hdepth]
  obtain ⟨hcc_eq, _⟩ := List.append_inj heq hlen
  have hlast := AncestorChain.getLast graph hcc
  have hlast' := AncestorChain.getLast graph hcc'
  subst hcc_eq
  rw [← hlast, ← hlast']

omit [Fintype Atom] [DecidableEq Atom] in
theorem depthNodes_nodup (addressing : graph.Addressing) (hdense : Dense addressing) :
    ∀ (d : ℕ) (start : graph.Node), (depthNodes graph addressing d start).Nodup
  | 0, _ => List.nodup_singleton _
  | d + 1, start => by
      simp only [depthNodes]
      rw [List.nodup_flatMap]
      refine ⟨fun child _ => depthNodes_nodup addressing hdense d child, ?_⟩
      have hnodup : (slotList addressing start (graph.childList start).length).Nodup :=
        (slotList_childList_perm graph hdense start).nodup_iff.2 (graph.childList_nodup start)
      refine List.Pairwise.imp_of_mem ?_ (List.Pairwise.and_mem.1 hnodup)
      intro c c' hc hc' hne
      simp only [ne_eq, Function.onFun] at hne ⊢
      intro n hn hn'
      obtain ⟨hrtg, hdepthn⟩ := (mem_depthNodes_iff graph hdense d c n).1 hn
      obtain ⟨hrtg', hdepthn'⟩ := (mem_depthNodes_iff graph hdense d c' n).1 hn'
      exact hne.2.2 (ancestor_eq_of_depth_eq graph addressing hrtg hrtg' (by omega))

omit [Fintype Atom] [DecidableEq Atom] in
/-- **Enumeration from the root.**  `depthNodes d root` lists exactly the nodes of depth `d`. -/
theorem mem_depthNodes_root_iff {addressing : graph.Addressing} (hdense : Dense addressing)
    (d : ℕ) (node : graph.Node) :
    node ∈ depthNodes graph addressing d graph.root ↔ graph.depth node = d := by
  rw [mem_depthNodes_iff graph hdense, graph.root_depth, Nat.zero_add]
  exact ⟨fun h => h.2, fun h => ⟨graph.reachable node, h⟩⟩

omit [Fintype Atom] [DecidableEq Atom] in
/-- An enumerated chain extends an ancestor chain of its start to an ancestor chain of its end. -/
theorem ancestorChain_of_mem_depthChains {addressing : graph.Addressing} (hdense : Dense addressing) :
    ∀ (d : ℕ) (start : graph.Node) (chain : List graph.Node),
      chain ∈ depthChains graph addressing d start →
        ∀ {pre : List graph.Node}, AncestorChain graph start pre →
          AncestorChain graph (chain.getLastD start) (pre ++ chain.tail)
  | 0, start, chain, h, pre, hpre => by
      simp only [depthChains, List.mem_singleton] at h
      subst h
      simpa using hpre
  | d + 1, start, chain, h, pre, hpre => by
      simp only [depthChains, List.mem_flatMap, List.mem_map] at h
      obtain ⟨child, hchild, chain', hchain', rfl⟩ := h
      have hedge := mem_childList_of_mem_slotList graph hdense hchild
      obtain ⟨hne, hhead, _⟩ := mem_depthChains_shape graph addressing d child chain' hchain'
      have hstep : AncestorChain graph child (pre ++ [child]) := AncestorChain.step hedge hpre
      have ih := ancestorChain_of_mem_depthChains hdense d child chain' hchain' hstep
      cases chain' with
      | nil => exact absurd rfl hne
      | cons a rest =>
          simp only [List.head?_cons, Option.some.injEq] at hhead
          subst hhead
          simpa [List.getLastD_cons] using ih

end Enumeration

/-! ## Rank addresses of enumerated chains -/

section ChainAddresses

variable {Atom : Type} [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)
  (graph : RootedDigraph Atom) (evidence : StereochemicalEvidence graph)

local instance depthChainsNodeFintype2 : Fintype graph.Node := graph.nodeFintype

/-- `chainRankAddress` splits at a junction node. -/
theorem chainRankAddress_append_cons (W D : ℕ) :
    ∀ (l : List graph.Node) (hne : l ≠ []) (b : graph.Node) (rest : List graph.Node),
      chainRankAddress molecule graph evidence W D (l ++ b :: rest) =
        chainRankAddress molecule graph evidence W D l ++
          chainRankAddress molecule graph evidence W D (l.getLast hne :: b :: rest)
  | [], hne, _, _ => absurd rfl hne
  | [a], _, b, rest => rfl
  | a :: a' :: l, _, b, rest => by
      simp only [List.cons_append, chainRankAddress, List.getLast_cons_cons]
      rw [show a' :: (l ++ b :: rest) = (a' :: l) ++ b :: rest from rfl,
        chainRankAddress_append_cons W D (a' :: l) (List.cons_ne_nil a' l) b rest]
      rfl

/-- **Rank address of an enumerated node.**  For a chain enumerated below the root, the rank
address of its endpoint is the chain's own rank list. -/
theorem rankAddress_eq_chainRankAddress_of_mem (addressing : graph.Addressing)
    (hdense : Dense addressing) (W D : ℕ) (d : ℕ) (chain : List graph.Node)
    (hchain : chain ∈ depthChains graph addressing d graph.root) :
    rankAddress molecule graph evidence W D (chain.getLastD graph.root) =
      chainRankAddress molecule graph evidence W D chain := by
  have hanc := ancestorChain_of_mem_depthChains graph hdense d graph.root chain hchain
    AncestorChain.root
  have huniq := ancestorChain_unique_of_addressing graph addressing
    (ancestorChain_spec_of_addressing graph addressing (chain.getLastD graph.root)) hanc
  unfold rankAddress
  rw [huniq]
  obtain ⟨hne, hhead, _⟩ := mem_depthChains_shape graph addressing d graph.root chain hchain
  cases chain with
  | nil => exact absurd rfl hne
  | cons a rest =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      rfl

end ChainAddresses

end
end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.headRanks_eq_map_rankIndexIn
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.mem_depthNodes_root_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.depthNodes_nodup
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.rankAddress_eq_chainRankAddress_of_mem
