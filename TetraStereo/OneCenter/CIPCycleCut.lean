import TetraStereo.OneCenter.CIP
import TetraStereo.OneCenter.Symmetry

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

namespace MoleculeGraph

open Prod.Lex

variable {V : Type*} [DecidableEq V]

/-- A node in the cycle-cut CIP expansion.

The field `seen` records the atoms already visited *earlier* on this branch (so it excludes
`current`). If `current ∈ seen`, the node represents a “duplicate atom” coming from a cycle or a
multiple-bond back-edge, and it is treated as a leaf (no further expansion). -/
structure CIPState (V : Type*) [DecidableEq V] where
  parent : V
  current : V
  seen : Finset V

namespace CIPState

/-- Map a `CIPState` along a permutation of atoms. -/
def map (e : Equiv.Perm V) (s : CIPState V) : CIPState V :=
  ⟨e s.parent, e s.current, s.seen.map e.toEmbedding⟩

@[simp] theorem map_parent (e : Equiv.Perm V) (s : CIPState V) :
    (s.map e).parent = e s.parent :=
  rfl

@[simp] theorem map_current (e : Equiv.Perm V) (s : CIPState V) :
    (s.map e).current = e s.current :=
  rfl

@[simp] theorem map_seen (e : Equiv.Perm V) (s : CIPState V) :
    (s.map e).seen = s.seen.map e.toEmbedding :=
  rfl

/-- Forget the cycle-cut bookkeeping and retain the raw CIP frontier node `(parent, current)`. -/
def toRawPair (s : CIPState V) : V × V :=
  (s.parent, s.current)

@[simp] theorem toRawPair_fst (s : CIPState V) : s.toRawPair.1 = s.parent :=
  rfl

@[simp] theorem toRawPair_snd (s : CIPState V) : s.toRawPair.2 = s.current :=
  rfl

end CIPState

variable [Fintype V]

namespace CIPState

/-- A cycle-cut CIP state is certified by a simple path from a fixed root when `seen` is exactly
the path support with the current endpoint removed, and `parent` is the path's penultimate vertex.

This is the graph-theoretic invariant behind cycle-cut correctness on acyclic substituent trees. -/
def CertifiedByPath (m : MoleculeGraph V) (root : V) (s : CIPState V) : Prop :=
  ∃ p : m.underlyingSimpleGraph.Walk root s.current,
    p.IsPath ∧
      p.penultimate = s.parent ∧
      ∀ v, v ∈ s.seen ↔ v ∈ p.support ∧ v ≠ s.current

theorem certifiedByPath_root_of_adj (m : MoleculeGraph V) {center start : V}
    (hadj : m.Adj center start) :
    (⟨center, start, {center}⟩ : CIPState V).CertifiedByPath m center := by
  have hadj' : m.underlyingSimpleGraph.Adj center start := by
    simpa using hadj
  refine ⟨hadj'.toWalk, SimpleGraph.Walk.IsPath.of_adj hadj', by simp [SimpleGraph.Adj.toWalk], ?_⟩
  intro v
  have hne : center ≠ start := hadj'.ne
  simp [SimpleGraph.Adj.toWalk]
  constructor
  · intro hv
    constructor
    · exact Or.inl hv
    · intro hstart
      subst v
      exact hne hstart
  · intro h
    rcases h.1 with hv | hstart
    · exact hv
    · exact False.elim (h.2 hstart)

theorem child_not_mem_insert_seen_of_certifiedByPath_acyclic
    (m : MoleculeGraph V) (hacyc : m.Acyclic) {root child : V} {s : CIPState V}
    (hs : s.CertifiedByPath m root)
    (hadj : m.Adj s.current child) (hchild : child ≠ s.parent) :
    child ∉ insert s.current s.seen := by
  rcases hs with ⟨p, hp, hpen, hseen⟩
  have hnotSupport : child ∉ p.support :=
    MoleculeGraph.Acyclic.not_mem_support_of_adj_ne_penultimate (m := m)
      hacyc hp hpen hadj hchild
  have hneCurrent : child ≠ s.current := by
    intro h
    subst h
    simp [MoleculeGraph.Adj, m.bond_self] at hadj
  intro hmem
  rcases Finset.mem_insert.1 hmem with hcurrent | hseenMem
  · exact hneCurrent hcurrent
  · exact hnotSupport ((hseen child).1 hseenMem).1

theorem current_not_mem_seen_of_certifiedByPath
    (m : MoleculeGraph V) {root : V} {s : CIPState V}
    (hs : s.CertifiedByPath m root) :
    s.current ∉ s.seen := by
  rcases hs with ⟨_p, _hp, _hpen, hseen⟩
  intro hmem
  exact ((hseen s.current).1 hmem).2 rfl

theorem certifiedByPath_child_of_acyclic
    (m : MoleculeGraph V) (hacyc : m.Acyclic) {root child : V} {s : CIPState V}
    (hs : s.CertifiedByPath m root)
    (hadj : m.Adj s.current child) (hchild : child ≠ s.parent) :
    (⟨s.current, child, insert s.current s.seen⟩ : CIPState V).CertifiedByPath m root := by
  rcases hs with ⟨p, hp, hpen, hseen⟩
  let G := m.underlyingSimpleGraph
  have hadjG : G.Adj s.current child := by
    simpa [G] using hadj
  have hnotSupport : child ∉ p.support :=
    MoleculeGraph.Acyclic.not_mem_support_of_adj_ne_penultimate (m := m)
      hacyc hp hpen hadj hchild
  have hpath : (p.concat hadjG).IsPath := hp.concat hnotSupport hadjG
  refine ⟨p.concat hadjG, hpath, by simp [SimpleGraph.Walk.penultimate_concat], ?_⟩
  intro v
  have hneCurrentChild : s.current ≠ child := hadjG.ne
  constructor
  · intro hv
    rcases Finset.mem_insert.1 hv with hcurrent | hseenMem
    · subst v
      constructor
      · simp [SimpleGraph.Walk.support_concat]
      · exact hneCurrentChild
    · have hvp : v ∈ p.support ∧ v ≠ s.current := (hseen v).1 hseenMem
      constructor
      · simp [SimpleGraph.Walk.support_concat, hvp.1]
      · intro hvc
        subst v
        exact hnotSupport hvp.1
  · intro hv
    have hvSupport : v ∈ p.support ∨ v = child := by
      simpa [SimpleGraph.Walk.support_concat] using hv.1
    rcases hvSupport with hvp | hvc
    · by_cases hvcur : v = s.current
      · exact Finset.mem_insert.2 (Or.inl hvcur)
      · exact Finset.mem_insert.2 (Or.inr ((hseen v).2 ⟨hvp, hvcur⟩))
    · exact False.elim (hv.2 hvc)

end CIPState

private def atomLabel (m : MoleculeGraph V) (v : V) : AtomLabel :=
  toLex (m.atomZ v, m.atomMass v)

private def sortDescLabel (xs : List AtomLabel) : List AtomLabel :=
  xs.mergeSort (fun a b => decide (b ≤ a))

/-- Neighbors of `v`, repeated with multiplicity equal to the bond order. -/
private def neighborListWithMultiplicity (m : MoleculeGraph V) (v : V) : List V :=
  (m.neighborFinset v).toList.flatMap fun u => List.replicate (m.bond v u) u

private theorem mem_neighborListWithMultiplicity_iff (m : MoleculeGraph V) {v u : V} :
    u ∈ neighborListWithMultiplicity m v ↔ m.Adj v u := by
  classical
  constructor
  · intro h
    simp [neighborListWithMultiplicity, MoleculeGraph.Adj] at h
    exact h.1
  · intro h
    simp [neighborListWithMultiplicity, MoleculeGraph.Adj]
    exact ⟨h, Nat.ne_of_gt h⟩

omit [Fintype V] in
private theorem count_flatMap_replicate_eq (l : List V) (hnodup : l.Nodup)
    (f : V → ℕ) (u : V) :
    (l.flatMap fun x => List.replicate (f x) x).count u =
      if u ∈ l then f u else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have hnot : a ∉ l := by
        exact (List.nodup_cons.mp hnodup).1
      have hnodupTail : l.Nodup := by
        exact (List.nodup_cons.mp hnodup).2
      by_cases hau : a = u
      · subst a
        simp [List.count_append, ih hnodupTail, hnot]
      · have hua : u ≠ a := by
          intro h
          exact hau h.symm
        by_cases hul : u ∈ l
        · simp [List.count_append, List.count_replicate, ih hnodupTail, hau, hua, hul]
        · simp [List.count_append, List.count_replicate, ih hnodupTail, hau, hua, hul]

private theorem count_neighborListWithMultiplicity_eq_bond
    (m : MoleculeGraph V) (v u : V) :
    (neighborListWithMultiplicity m v).count u = m.bond v u := by
  classical
  have hcount := count_flatMap_replicate_eq (l := (m.neighborFinset v).toList)
    (hnodup := (m.neighborFinset v).nodup_toList) (f := fun x => m.bond v x) (u := u)
  by_cases hu : u ∈ m.neighborFinset v
  · simpa [neighborListWithMultiplicity, hu] using hcount
  · have hb : m.bond v u = 0 := by
      have hnotAdj : ¬ m.Adj v u := by
        simpa [MoleculeGraph.mem_neighborFinset] using hu
      exact Nat.eq_zero_of_not_pos hnotAdj
    simpa [neighborListWithMultiplicity, hu, hb] using hcount

private def children (m : MoleculeGraph V) (s : CIPState V) : List (CIPState V) :=
  if s.current ∈ s.seen then []
  else
    let seen' := insert s.current s.seen
    ((neighborListWithMultiplicity m s.current).erase s.parent).map fun c =>
      ⟨s.current, c, seen'⟩

private def nextFrontier (m : MoleculeGraph V) (frontier : List (CIPState V)) : List (CIPState V) :=
  frontier.flatMap fun s => children m s

/-- Public cycle-cut children of a frontier node. -/
def cycleCutChildren (m : MoleculeGraph V) (s : CIPState V) : List (CIPState V) :=
  children m s

theorem cycleCutChildren_eq_of_current_mem_seen (m : MoleculeGraph V) (s : CIPState V)
    (hseen : s.current ∈ s.seen) :
    m.cycleCutChildren s = [] := by
  simp [cycleCutChildren, children, hseen]

theorem cycleCutChildren_eq_of_current_notMem_seen (m : MoleculeGraph V) (s : CIPState V)
    (hseen : s.current ∉ s.seen) :
    m.cycleCutChildren s =
      ((m.rawCIPNeighborListWithMultiplicity s.current).erase s.parent).map fun c =>
        ({ parent := s.current, current := c, seen := insert s.current s.seen } :
          CIPState V) := by
  simp [cycleCutChildren, children, hseen, rawCIPNeighborListWithMultiplicity,
    neighborListWithMultiplicity]

/-- Public one-step cycle-cut frontier expansion. -/
def cycleCutNextFrontier (m : MoleculeGraph V) (frontier : List (CIPState V)) :
    List (CIPState V) :=
  nextFrontier m frontier

theorem cycleCutNextFrontier_eq (m : MoleculeGraph V) (frontier : List (CIPState V)) :
    m.cycleCutNextFrontier frontier = frontier.flatMap fun s => m.cycleCutChildren s := by
  simp [cycleCutNextFrontier, nextFrontier, cycleCutChildren]

/-- Iterate the cycle-cut frontier expansion. -/
def cycleCutFrontier (m : MoleculeGraph V) : ℕ → List (CIPState V) → List (CIPState V)
  | 0, frontier => frontier
  | n + 1, frontier => cycleCutFrontier m n (m.cycleCutNextFrontier frontier)

/-- Every state in a frontier is certified by a simple path from the fixed root. -/
def FrontierCertifiedByPath (m : MoleculeGraph V) (root : V)
    (frontier : List (CIPState V)) : Prop :=
  ∀ s, s ∈ frontier → s.CertifiedByPath m root

/-- No state in a frontier has already seen its current atom. -/
def FrontierAvoidsSeen (frontier : List (CIPState V)) : Prop :=
  ∀ s, s ∈ frontier → s.current ∉ s.seen

/-- Every state in a frontier has a `seen` set of the specified cardinality. -/
def FrontierSeenCardEq (n : ℕ) (frontier : List (CIPState V)) : Prop :=
  ∀ s, s ∈ frontier → s.seen.card = n

theorem frontierAvoidsSeen_of_frontierCertifiedByPath
    (m : MoleculeGraph V) {root : V} {frontier : List (CIPState V)}
    (hfront : m.FrontierCertifiedByPath root frontier) :
    FrontierAvoidsSeen frontier := by
  intro s hs
  exact CIPState.current_not_mem_seen_of_certifiedByPath m (hfront s hs)

theorem frontierCertifiedByPath_cycleCutNextFrontier_of_treeLike
    (m : MoleculeGraph V) (htree : m.TreeLike) {root : V}
    {frontier : List (CIPState V)}
    (hfront : m.FrontierCertifiedByPath root frontier) :
    m.FrontierCertifiedByPath root (m.cycleCutNextFrontier frontier) := by
  intro t ht
  rcases (List.mem_flatMap).1 (by simpa [cycleCutNextFrontier, nextFrontier] using ht) with
    ⟨s, hsFrontier, htChild⟩
  have hsCert : s.CertifiedByPath m root := hfront s hsFrontier
  have hsNotSeen : s.current ∉ s.seen :=
    CIPState.current_not_mem_seen_of_certifiedByPath m hsCert
  unfold children at htChild
  simp [hsNotSeen] at htChild
  rcases htChild with ⟨child, hchildMem, rfl⟩
  have hchildNeParent : child ≠ s.parent := by
    intro h
    subst child
    have hparentMem : s.parent ∈ neighborListWithMultiplicity m s.current :=
      List.mem_of_mem_erase hchildMem
    have hparentAdj : m.Adj s.current s.parent :=
      (mem_neighborListWithMultiplicity_iff (m := m)).1 hparentMem
    have hbond : m.bond s.current s.parent = 1 := htree.2 s.current s.parent hparentAdj
    have hcountErase :
        ((neighborListWithMultiplicity m s.current).erase s.parent).count s.parent = 0 := by
      rw [List.count_erase_self, count_neighborListWithMultiplicity_eq_bond, hbond]
    exact ((List.count_eq_zero).1 hcountErase) hchildMem
  have hchildAdj : m.Adj s.current child :=
    (mem_neighborListWithMultiplicity_iff (m := m)).1 (List.mem_of_mem_erase hchildMem)
  exact
    CIPState.certifiedByPath_child_of_acyclic (m := m) htree.1 hsCert hchildAdj hchildNeParent

theorem frontierCertifiedByPath_cycleCutFrontier_of_treeLike
    (m : MoleculeGraph V) (htree : m.TreeLike) {root : V} :
    ∀ {frontier : List (CIPState V)}, m.FrontierCertifiedByPath root frontier →
      ∀ n, m.FrontierCertifiedByPath root (m.cycleCutFrontier n frontier)
  | frontier, hfront, 0 => by
      simpa [cycleCutFrontier] using hfront
  | frontier, hfront, n + 1 => by
      simpa [cycleCutFrontier] using
        frontierCertifiedByPath_cycleCutFrontier_of_treeLike (m := m) htree
          (frontierCertifiedByPath_cycleCutNextFrontier_of_treeLike
            (m := m) htree hfront) n

theorem cycleCutFrontier_avoidsSeen_of_certifiedByPath_treeLike
    (m : MoleculeGraph V) (htree : m.TreeLike) {root : V}
    {frontier : List (CIPState V)}
    (hfront : m.FrontierCertifiedByPath root frontier) (n : ℕ) :
    FrontierAvoidsSeen (m.cycleCutFrontier n frontier) :=
  m.frontierAvoidsSeen_of_frontierCertifiedByPath
    (m.frontierCertifiedByPath_cycleCutFrontier_of_treeLike htree hfront n)

theorem frontierSeenCardEq_cycleCutNextFrontier_of_frontierCertifiedByPath
    (m : MoleculeGraph V) {root : V} {n : ℕ} {frontier : List (CIPState V)}
    (hfront : m.FrontierCertifiedByPath root frontier)
    (hcard : FrontierSeenCardEq n frontier) :
    FrontierSeenCardEq (n + 1) (m.cycleCutNextFrontier frontier) := by
  intro t ht
  rcases (List.mem_flatMap).1 (by simpa [cycleCutNextFrontier, nextFrontier] using ht) with
    ⟨s, hsFrontier, htChild⟩
  have hsCert : s.CertifiedByPath m root := hfront s hsFrontier
  have hsNotSeen : s.current ∉ s.seen :=
    CIPState.current_not_mem_seen_of_certifiedByPath m hsCert
  unfold children at htChild
  simp [hsNotSeen] at htChild
  rcases htChild with ⟨child, _hchildMem, rfl⟩
  rw [Finset.card_insert_of_notMem hsNotSeen, hcard s hsFrontier]

theorem frontierSeenCardEq_cycleCutFrontier_of_treeLike
    (m : MoleculeGraph V) (htree : m.TreeLike) {root : V} {n : ℕ}
    {frontier : List (CIPState V)}
    (hfront : m.FrontierCertifiedByPath root frontier)
    (hcard : FrontierSeenCardEq n frontier) :
    ∀ k, FrontierSeenCardEq (n + k) (m.cycleCutFrontier k frontier)
  | 0 => by
      simpa [cycleCutFrontier] using hcard
  | k + 1 => by
      have hfrontNext : m.FrontierCertifiedByPath root (m.cycleCutNextFrontier frontier) :=
        m.frontierCertifiedByPath_cycleCutNextFrontier_of_treeLike htree hfront
      have hcardNext : FrontierSeenCardEq (n + 1) (m.cycleCutNextFrontier frontier) :=
        m.frontierSeenCardEq_cycleCutNextFrontier_of_frontierCertifiedByPath hfront hcard
      have htail :=
        frontierSeenCardEq_cycleCutFrontier_of_treeLike (m := m) htree
          (root := root) hfrontNext hcardNext k
      simpa [cycleCutFrontier, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

theorem cycleCutFrontier_eq_nil_of_frontierSeenCardEq_gt_card
    {n : ℕ} {frontier : List (CIPState V)}
    (hcard : FrontierSeenCardEq n frontier) (hn : Fintype.card V < n) :
    frontier = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro s hs
  have hsCard : s.seen.card = n := hcard s hs
  have hnle : n ≤ Fintype.card V := by
    rw [← hsCard]
    exact Finset.card_le_univ s.seen
  exact (not_lt_of_ge hnle) hn

private def cipKeyAuxCycleCut (m : MoleculeGraph V) : ℕ → List (CIPState V) → List AtomLabel
  | 0, _ => []
  | n + 1, frontier =>
      let layer := sortDescLabel (frontier.map fun s => atomLabel m s.current)
      layer ++ cipKeyAuxCycleCut m n (nextFrontier m frontier)

private theorem cipKeyAuxCycleCut_nil (m : MoleculeGraph V) :
    ∀ n, cipKeyAuxCycleCut m n ([] : List (CIPState V)) = []
  | 0 => by
      simp [cipKeyAuxCycleCut]
  | n + 1 => by
      simp [cipKeyAuxCycleCut, cipKeyAuxCycleCut_nil m n, nextFrontier, sortDescLabel]

/-- Public cycle-cut auxiliary key on an arbitrary frontier and depth. -/
def cycleCutKeyAux (m : MoleculeGraph V) : ℕ → List (CIPState V) → List AtomLabel :=
  cipKeyAuxCycleCut m

@[simp] theorem cycleCutKeyAux_zero (m : MoleculeGraph V) (frontier : List (CIPState V)) :
    m.cycleCutKeyAux 0 frontier = [] :=
  rfl

theorem cycleCutKeyAux_succ (m : MoleculeGraph V) (n : ℕ)
    (frontier : List (CIPState V)) :
    m.cycleCutKeyAux (n + 1) frontier =
      rawCIPSortDescLabel (frontier.map fun s => m.rawCIPAtomLabel s.current) ++
        m.cycleCutKeyAux n (m.cycleCutNextFrontier frontier) := by
  simp [cycleCutKeyAux, cipKeyAuxCycleCut, rawCIPSortDescLabel, rawCIPAtomLabel,
    sortDescLabel, atomLabel, cycleCutNextFrontier, nextFrontier]

theorem cycleCutKeyAux_eq_of_cycleCutFrontier_eq_nil
    (m : MoleculeGraph V) :
    ∀ n {frontier : List (CIPState V)}, m.cycleCutFrontier n frontier = [] →
      ∀ extra, m.cycleCutKeyAux (n + extra) frontier = m.cycleCutKeyAux n frontier
  | 0, frontier, hnil, extra => by
      have hfrontier : frontier = [] := by
        simpa [cycleCutFrontier] using hnil
      subst frontier
      simp [cycleCutKeyAux, cipKeyAuxCycleCut_nil]
  | n + 1, frontier, hnil, extra => by
      have hnilNext : m.cycleCutFrontier n (m.cycleCutNextFrontier frontier) = [] := by
        simpa [cycleCutFrontier] using hnil
      cases extra with
      | zero =>
          simp
      | succ extra =>
          have htail :=
            cycleCutKeyAux_eq_of_cycleCutFrontier_eq_nil (m := m) n hnilNext (extra + 1)
          rw [show (n + 1) + (extra + 1) = (n + (extra + 1)) + 1 by omega]
          rw [show n + (extra + 1) + 1 = Nat.succ (n + (extra + 1)) by omega]
          rw [show n + 1 = Nat.succ n by omega]
          simp [cycleCutKeyAux, cycleCutNextFrontier] at htail
          change
            sortDescLabel (frontier.map fun s => atomLabel m s.current) ++
                cipKeyAuxCycleCut m (n + (extra + 1)) (nextFrontier m frontier) =
              sortDescLabel (frontier.map fun s => atomLabel m s.current) ++
                cipKeyAuxCycleCut m n (nextFrontier m frontier)
          rw [htail]

private theorem rawCIPNextFrontier_eq_cycleCutNextFrontier_toRawPair
    (m : MoleculeGraph V) {root : V} :
    ∀ {frontier : List (CIPState V)}, m.FrontierCertifiedByPath root frontier →
      m.rawCIPNextFrontier (frontier.map CIPState.toRawPair) =
        (m.cycleCutNextFrontier frontier).map CIPState.toRawPair
  | [], _ => by
      simp [rawCIPNextFrontier, cycleCutNextFrontier, nextFrontier]
  | s :: frontier, hfront => by
      have hsCert : s.CertifiedByPath m root := hfront s (by simp)
      have hsNotSeen : s.current ∉ s.seen :=
        CIPState.current_not_mem_seen_of_certifiedByPath m hsCert
      have htail : m.FrontierCertifiedByPath root frontier := by
        intro t ht
        exact hfront t (by simp [ht])
      have hnextTail :=
        rawCIPNextFrontier_eq_cycleCutNextFrontier_toRawPair (m := m) htail
      calc
        m.rawCIPNextFrontier (List.map CIPState.toRawPair (s :: frontier))
            = List.map (fun c => (s.current, c))
                ((neighborListWithMultiplicity m s.current).erase s.parent) ++
              m.rawCIPNextFrontier (List.map CIPState.toRawPair frontier) := by
                simp [rawCIPNextFrontier, rawCIPChildren, rawCIPNeighborListWithMultiplicity,
                  neighborListWithMultiplicity, CIPState.toRawPair]
        _ = List.map CIPState.toRawPair
                (List.map
                  (fun c =>
                    ({ parent := s.current, current := c, seen := insert s.current s.seen } :
                      CIPState V))
                  ((neighborListWithMultiplicity m s.current).erase s.parent)) ++
              List.map CIPState.toRawPair (m.cycleCutNextFrontier frontier) := by
                rw [hnextTail]
                simp [CIPState.toRawPair, List.map_map, Function.comp]
        _ = List.map CIPState.toRawPair (m.cycleCutNextFrontier (s :: frontier)) := by
                simp [cycleCutNextFrontier, nextFrontier, children, neighborListWithMultiplicity,
                  hsNotSeen, List.map_map]

/-- On a tree-like molecular graph, the raw frontier key and cycle-cut frontier key agree at every
fixed expansion depth, provided the cycle-cut frontier is certified by simple paths from the root. -/
theorem rawCIPKeyAux_eq_cycleCutKeyAux_of_frontierCertifiedByPath_treeLike
    (m : MoleculeGraph V) (htree : m.TreeLike) {root : V} :
    ∀ n {frontier : List (CIPState V)}, m.FrontierCertifiedByPath root frontier →
      m.rawCIPKeyAux n (frontier.map CIPState.toRawPair) =
        m.cycleCutKeyAux n frontier
  | 0, _, _ => by
      simp [rawCIPKeyAux, cycleCutKeyAux, cipKeyAuxCycleCut]
  | n + 1, frontier, hfront => by
      have hnext :
          m.rawCIPNextFrontier (frontier.map CIPState.toRawPair) =
            (m.cycleCutNextFrontier frontier).map CIPState.toRawPair :=
        rawCIPNextFrontier_eq_cycleCutNextFrontier_toRawPair (m := m) hfront
      have hfrontNext : m.FrontierCertifiedByPath root (m.cycleCutNextFrontier frontier) :=
        m.frontierCertifiedByPath_cycleCutNextFrontier_of_treeLike htree hfront
      have htail :=
        rawCIPKeyAux_eq_cycleCutKeyAux_of_frontierCertifiedByPath_treeLike
          (m := m) htree (root := root) n hfrontNext
      have hlayerMap :
          ((frontier.map CIPState.toRawPair).map fun pv => m.rawCIPAtomLabel pv.2) =
            frontier.map fun s => atomLabel m s.current := by
        rw [List.map_map]
        simp [CIPState.toRawPair, Function.comp, rawCIPAtomLabel, atomLabel]
      calc
        m.rawCIPKeyAux (n + 1) (frontier.map CIPState.toRawPair)
            = rawCIPSortDescLabel
                ((frontier.map CIPState.toRawPair).map fun pv => m.rawCIPAtomLabel pv.2) ++
              m.rawCIPKeyAux n
                (m.rawCIPNextFrontier (frontier.map CIPState.toRawPair)) := by
                simp [rawCIPKeyAux]
        _ = sortDescLabel (frontier.map fun s => atomLabel m s.current) ++
              m.rawCIPKeyAux n
                ((m.cycleCutNextFrontier frontier).map CIPState.toRawPair) := by
                rw [hnext]
                rw [hlayerMap]
                simp [rawCIPSortDescLabel, sortDescLabel]
        _ = sortDescLabel (frontier.map fun s => atomLabel m s.current) ++
              m.cycleCutKeyAux n (m.cycleCutNextFrontier frontier) := by
                rw [htail]
        _ = m.cycleCutKeyAux (n + 1) frontier := by
                simp [cycleCutKeyAux, cipKeyAuxCycleCut, cycleCutNextFrontier]

/-- A simplified “CIP-like” priority key that **cuts cycle expansion**.

This is like `cipKeyFrom`, but whenever a branch encounters a previously seen atom, the branch stops
expanding. This prevents infinite “walk around a ring” contributions from dominating the key while
still recording the duplicate atom label once (as in the usual “duplicate atom” conventions).

The expansion depth is bounded by `Fintype.card V + 1`. -/
def cipKeyFromCycleCut (m : MoleculeGraph V) (center start : V) : List AtomLabel := by
  classical
  let root : CIPState V := ⟨center, start, {center}⟩
  exact cipKeyAuxCycleCut m (Fintype.card V + 1) [root]

theorem cipKeyFromCycleCut_eq_cycleCutKeyAux (m : MoleculeGraph V) (center start : V) :
    cipKeyFromCycleCut m center start =
      m.cycleCutKeyAux (Fintype.card V + 1) [⟨center, start, {center}⟩] := by
  simp [cipKeyFromCycleCut, cycleCutKeyAux]

theorem cipKeyFromCycleCut_head? (m : MoleculeGraph V) (center start : V) :
    (cipKeyFromCycleCut m center start).head? = some (toLex (m.atomZ start, m.atomMass start)) := by
  classical
  simp [cipKeyFromCycleCut, cipKeyAuxCycleCut, sortDescLabel, atomLabel]

theorem cipKeyFromCycleCut_eq_singleton_of_neighborFinset_eq_singleton
    (m : MoleculeGraph V) (center start : V)
    (hfin : m.neighborFinset start = {center}) (hbond : m.bond start center = 1) :
    cipKeyFromCycleCut m center start = [toLex (m.atomZ start, m.atomMass start)] := by
  classical
  have hpos : 0 < Fintype.card V + 1 := Nat.succ_pos _
  cases hsteps : (Fintype.card V + 1) with
  | zero =>
      have : False := by
        have hpos' := hpos
        simp [hsteps] at hpos'
      exact False.elim this
  | succ n =>
      have hchildren : children m ⟨center, start, {center}⟩ = [] := by
        by_cases hseen : start ∈ ({center} : Finset V)
        · simp [children, hseen]
        · simp [children, hseen, neighborListWithMultiplicity, hfin, hbond]
      simp [cipKeyFromCycleCut, cipKeyAuxCycleCut, nextFrontier, hchildren,
        sortDescLabel, atomLabel, cipKeyAuxCycleCut_nil]

/-! ### Invariance under relabeling -/

private theorem sortDescLabel_eq_of_perm {xs ys : List AtomLabel} (h : xs.Perm ys) :
    sortDescLabel xs = sortDescLabel ys := by
  classical
  let r : AtomLabel → AtomLabel → Prop := fun a b => b ≤ a
  haveI : IsTrans AtomLabel r :=
    ⟨by
      intro a b c hab hbc
      exact le_trans hbc hab⟩
  haveI : Std.Total r :=
    ⟨by
      intro a b
      simpa [r, or_comm] using (le_total a b)⟩
  haveI : Std.Antisymm r :=
    ⟨by
      intro a b hab hba
      exact le_antisymm hba hab⟩
  have hxperm : (sortDescLabel xs).Perm xs := by
    simpa [sortDescLabel] using
      (List.mergeSort_perm xs (fun a b => decide (b ≤ a)))
  have hyperm : (sortDescLabel ys).Perm ys := by
    simpa [sortDescLabel] using
      (List.mergeSort_perm ys (fun a b => decide (b ≤ a)))
  have hperm : (sortDescLabel xs).Perm (sortDescLabel ys) :=
    hxperm.trans (h.trans hyperm.symm)
  have hxpair : (sortDescLabel xs).Pairwise r := by
    simpa [sortDescLabel, r] using (List.pairwise_mergeSort' (r := r) xs)
  have hypair : (sortDescLabel ys).Pairwise r := by
    simpa [sortDescLabel, r] using (List.pairwise_mergeSort' (r := r) ys)
  exact (List.Perm.eq_of_pairwise' hxpair hypair hperm)

private theorem cipKeyAuxCycleCut_eq_of_perm (m : MoleculeGraph V) :
    ∀ n {frontier₁ frontier₂ : List (CIPState V)},
      frontier₁.Perm frontier₂ →
        cipKeyAuxCycleCut m n frontier₁ = cipKeyAuxCycleCut m n frontier₂
  | 0, _, _, _ => by simp [cipKeyAuxCycleCut]
  | n + 1, frontier₁, frontier₂, hperm => by
      have hlayer :
          sortDescLabel (frontier₁.map fun s => atomLabel m s.current) =
            sortDescLabel (frontier₂.map fun s => atomLabel m s.current) := by
        apply sortDescLabel_eq_of_perm
        exact hperm.map _
      have hnext : (nextFrontier m frontier₁).Perm (nextFrontier m frontier₂) := by
        simpa [nextFrontier] using hperm.flatMap_right (children m)
      simp [cipKeyAuxCycleCut, hlayer, cipKeyAuxCycleCut_eq_of_perm m n hnext]

private theorem atomLabel_eq_of_preserves (m : MoleculeGraph V) (e : Equiv.Perm V)
    (hZ : ∀ v, m.atomZ (e v) = m.atomZ v) (hMass : ∀ v, m.atomMass (e v) = m.atomMass v) (v : V) :
    atomLabel m (e v) = atomLabel m v := by
  simp [atomLabel, AtomLabel, hZ, hMass]

private theorem neighborFinset_eq_map (m : MoleculeGraph V) (e : Equiv.Perm V)
    (hBond : ∀ u v, m.bond (e u) (e v) = m.bond u v) (v : V) :
    m.neighborFinset (e v) = (m.neighborFinset v).map e.toEmbedding := by
  classical
  ext u
  constructor
  · intro hu
    have hadj : m.Adj (e v) u := (m.mem_neighborFinset (v := e v) (u := u)).1 hu
    refine (Finset.mem_map.2 ?_)
    refine ⟨e.symm u, ?_, by simp⟩
    have hb : m.bond v (e.symm u) = m.bond (e v) u := by
      have := hBond v (e.symm u)
      simpa using this.symm
    have : m.Adj v (e.symm u) := by
      dsimp [MoleculeGraph.Adj] at hadj ⊢
      exact lt_of_lt_of_eq hadj hb.symm
    exact (m.mem_neighborFinset (v := v) (u := e.symm u)).2 this
  · intro hu
    rcases (Finset.mem_map.1 hu) with ⟨x, hx, rfl⟩
    have hadj : m.Adj v x := (m.mem_neighborFinset (v := v) (u := x)).1 hx
    have hb : m.bond (e v) (e x) = m.bond v x := hBond v x
    have : m.Adj (e v) (e x) := by
      dsimp [MoleculeGraph.Adj] at hadj ⊢
      exact lt_of_lt_of_eq hadj hb.symm
    exact (m.mem_neighborFinset (v := e v) (u := e x)).2 this

omit [Fintype V] in
private theorem toList_map_perm (s : Finset V) (e : Equiv.Perm V) :
    (s.map e.toEmbedding).toList.Perm (s.toList.map e) := by
  classical
  have hfin : (s.toList.map e).toFinset = s.map e.toEmbedding := by
    ext v
    constructor
    · intro hv
      have hv' : v ∈ s.toList.map e := by
        simpa [List.mem_toFinset] using hv
      rcases List.mem_map.1 hv' with ⟨a, ha, rfl⟩
      exact Finset.mem_map_of_mem e.toEmbedding (by simpa using (Finset.mem_toList.1 ha))
    · intro hv
      have hs : e.symm v ∈ s := (Finset.mem_map_equiv (f := e) (s := s)).1 hv
      have hsList : e.symm v ∈ s.toList := (Finset.mem_toList).2 hs
      have : v ∈ s.toList.map e := by
        simpa using (List.mem_map.2 ⟨e.symm v, hsList, by simp⟩)
      exact (List.mem_toFinset).2 this
  have hperm₁ : (s.map e.toEmbedding).toList.Perm (s.toList.map e).toFinset.toList :=
    (Finset.perm_toList.2 hfin.symm)
  have hnodup : (s.toList.map e).Nodup :=
    s.nodup_toList.map e.injective
  have hperm₂ : (s.toList.map e).toFinset.toList.Perm (s.toList.map e) :=
    List.toFinset_toList hnodup
  exact hperm₁.trans hperm₂

private theorem neighborListWithMultiplicity_perm (m : MoleculeGraph V) (e : Equiv.Perm V)
    (hBond : ∀ u v, m.bond (e u) (e v) = m.bond u v) (v : V) :
    (neighborListWithMultiplicity m (e v)).Perm ((neighborListWithMultiplicity m v).map e) := by
  classical
  have hneighbors :
      m.neighborFinset (e v) = (m.neighborFinset v).map e.toEmbedding :=
    neighborFinset_eq_map (m := m) (e := e) hBond v
  have htoList :
      (m.neighborFinset (e v)).toList.Perm ((m.neighborFinset v).toList.map e) := by
    simpa [hneighbors] using toList_map_perm (s := m.neighborFinset v) e
  have hflat :
      ((m.neighborFinset (e v)).toList.flatMap (fun u => List.replicate (m.bond (e v) u) u)).Perm
        (((m.neighborFinset v).toList.map e).flatMap
          (fun u => List.replicate (m.bond (e v) u) u)) :=
    htoList.flatMap_right _
  have hrewrite :
      ((m.neighborFinset v).toList.map e).flatMap
          (fun u => List.replicate (m.bond (e v) u) u) =
        (neighborListWithMultiplicity m v).map e := by
    simp [neighborListWithMultiplicity, List.flatMap_map, List.map_flatMap, hBond]
  simpa [neighborListWithMultiplicity, hrewrite] using hflat

omit [Fintype V] in
private theorem current_mem_map_seen_iff (e : Equiv.Perm V) (s : CIPState V) :
    (s.map e).current ∈ (s.map e).seen ↔ s.current ∈ s.seen := by
  constructor
  · intro h
    have := (Finset.mem_map_equiv (f := e) (s := s.seen)).1 h
    simpa [CIPState.map] using this
  · intro h
    exact Finset.mem_map_of_mem e.toEmbedding h

private theorem children_perm_map (m : MoleculeGraph V) (e : Equiv.Perm V)
    (hBond : ∀ u v, m.bond (e u) (e v) = m.bond u v) (s : CIPState V) :
    (children m (s.map e)).Perm ((children m s).map (CIPState.map e)) := by
  classical
  by_cases hseen : s.current ∈ s.seen
  · simp [children, hseen]
  · have hseen' : (s.map e).current ∉ (s.map e).seen := by
      intro h
      exact hseen ((current_mem_map_seen_iff (e := e) (s := s)).1 h)
    have hnl :
        (neighborListWithMultiplicity m (e s.current)).Perm
          ((neighborListWithMultiplicity m s.current).map e) :=
      neighborListWithMultiplicity_perm (m := m) (e := e) hBond s.current
    have herase :
        ((neighborListWithMultiplicity m (e s.current)).erase (e s.parent)).Perm
          (((neighborListWithMultiplicity m s.current).map e).erase (e s.parent)) :=
      List.Perm.erase (e s.parent) hnl
    have hmap :
        (((neighborListWithMultiplicity m s.current).erase s.parent).map e) =
          ((neighborListWithMultiplicity m s.current).map e).erase (e s.parent) := by
      simpa using
        (List.map_erase (f := e) (finj := e.injective) (a := s.parent)
          (l := neighborListWithMultiplicity m s.current))
    have hatoms :
        ((neighborListWithMultiplicity m (e s.current)).erase (e s.parent)).Perm
          (((neighborListWithMultiplicity m s.current).erase s.parent).map e) := by
      simpa [hmap] using herase
    have hstates :=
      hatoms.map fun c =>
        (⟨e s.current, c, insert (e s.current) (s.seen.map e.toEmbedding)⟩ : CIPState V)
    have hstatesMap :
        (List.map
            (fun c =>
              (⟨e s.current, c, insert (e s.current) (s.seen.map e.toEmbedding)⟩ : CIPState V))
            ((neighborListWithMultiplicity m (e s.current)).erase (e s.parent))).Perm
          (List.map
            ((fun c =>
              (⟨e s.current, c, insert (e s.current) (s.seen.map e.toEmbedding)⟩ : CIPState V)) ∘ e)
            ((neighborListWithMultiplicity m s.current).erase s.parent)) := by
      simpa [List.map_map, Function.comp] using hstates
    have hright :
        (List.map
            ((fun c =>
              (⟨e s.current, c, insert (e s.current) (s.seen.map e.toEmbedding)⟩ : CIPState V)) ∘ e)
            ((neighborListWithMultiplicity m s.current).erase s.parent)) =
          (List.map
            (CIPState.map e ∘
              fun c => (⟨s.current, c, insert s.current s.seen⟩ : CIPState V))
            ((neighborListWithMultiplicity m s.current).erase s.parent)) := by
      simp [CIPState.map, Finset.map_insert]
    have hstates' :
        (List.map
            (fun c =>
              (⟨e s.current, c, insert (e s.current) (s.seen.map e.toEmbedding)⟩ : CIPState V))
            ((neighborListWithMultiplicity m (e s.current)).erase (e s.parent))).Perm
          (List.map
            (CIPState.map e ∘
              fun c => (⟨s.current, c, insert s.current s.seen⟩ : CIPState V))
            ((neighborListWithMultiplicity m s.current).erase s.parent)) := by
      exact hstatesMap.trans (by rw [hright])
    simpa [children, hseen, hseen', List.map_map, Function.comp] using hstates'

private theorem nextFrontier_perm_map (m : MoleculeGraph V) (e : Equiv.Perm V)
    (hBond : ∀ u v, m.bond (e u) (e v) = m.bond u v) (frontier : List (CIPState V)) :
    (nextFrontier m (frontier.map (CIPState.map e))).Perm
      ((nextFrontier m frontier).map (CIPState.map e)) := by
  classical
  have hlhs :
      nextFrontier m (frontier.map (CIPState.map e)) =
        frontier.flatMap fun s => children m (s.map e) := by
    simp [nextFrontier, List.flatMap_map]
  have hrhs :
      (nextFrontier m frontier).map (CIPState.map e) =
        frontier.flatMap fun s => (children m s).map (CIPState.map e) := by
    simp [nextFrontier, List.map_flatMap]
  have hperm :
      (frontier.flatMap fun s => children m (s.map e)).Perm
        (frontier.flatMap fun s => (children m s).map (CIPState.map e)) := by
    apply List.Perm.flatMap_left
    intro s hs
    exact children_perm_map (m := m) (e := e) hBond s
  simpa [hlhs, hrhs] using hperm

private theorem cipKeyAuxCycleCut_eq_of_map (m : MoleculeGraph V) (e : Equiv.Perm V)
    (hZ : ∀ v, m.atomZ (e v) = m.atomZ v) (hMass : ∀ v, m.atomMass (e v) = m.atomMass v)
    (hBond : ∀ u v, m.bond (e u) (e v) = m.bond u v) :
    ∀ n (frontier : List (CIPState V)),
      cipKeyAuxCycleCut m n (frontier.map (CIPState.map e)) =
        cipKeyAuxCycleCut m n frontier
  | 0, _ => by simp [cipKeyAuxCycleCut]
  | n + 1, frontier => by
      have hlayer :
          sortDescLabel (frontier.map ((fun s => atomLabel m s.current) ∘ CIPState.map e)) =
            sortDescLabel (frontier.map fun s => atomLabel m s.current) := by
        apply congrArg sortDescLabel
        simp [Function.comp, atomLabel_eq_of_preserves (m := m) (e := e) hZ hMass]
      have hnextPerm :
          (nextFrontier m (frontier.map (CIPState.map e))).Perm
            ((nextFrontier m frontier).map (CIPState.map e)) :=
        nextFrontier_perm_map (m := m) (e := e) hBond frontier
      have hnext :
          cipKeyAuxCycleCut m n (nextFrontier m (frontier.map (CIPState.map e))) =
            cipKeyAuxCycleCut m n ((nextFrontier m frontier).map (CIPState.map e)) := by
        apply cipKeyAuxCycleCut_eq_of_perm (m := m) n hnextPerm
      simp [cipKeyAuxCycleCut, hlayer, hnext,
        cipKeyAuxCycleCut_eq_of_map m e hZ hMass hBond n (nextFrontier m frontier)]

/-- `cipKeyFromCycleCut` is invariant under any relabeling of atoms preserving atom labels and
bond orders. -/
theorem cipKeyFromCycleCut_eq_of_preserves (m : MoleculeGraph V) (e : Equiv.Perm V)
    (hZ : ∀ v, m.atomZ (e v) = m.atomZ v) (hMass : ∀ v, m.atomMass (e v) = m.atomMass v)
    (hBond : ∀ u v, m.bond (e u) (e v) = m.bond u v) (center start : V) :
    cipKeyFromCycleCut m (e center) (e start) = cipKeyFromCycleCut m center start := by
  classical
  simpa [cipKeyFromCycleCut, CIPState.map] using
    (cipKeyAuxCycleCut_eq_of_map (m := m) (e := e) hZ hMass hBond
      (Fintype.card V + 1) [⟨center, start, {center}⟩])

end MoleculeGraph

namespace OneCenterMolecule

open Prod.Lex

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The cycle-cut CIP-like key of the `i`-th ligand, computed from the molecular graph. -/
def cipKeyCycleCut (m : OneCenterMolecule V) (i : Fin 4) : List MoleculeGraph.AtomLabel :=
  MoleculeGraph.cipKeyFromCycleCut m.mol m.center (m.ligandAtom i)

/-- The initial cycle-cut expansion state for the `i`-th ligand. -/
def cipCycleCutRootState (m : OneCenterMolecule V) (i : Fin 4) : MoleculeGraph.CIPState V :=
  ⟨m.center, m.ligandAtom i, {m.center}⟩

theorem cipCycleCutRootState_certifiedByPath (m : OneCenterMolecule V) (i : Fin 4) :
    MoleculeGraph.CIPState.CertifiedByPath m.mol m.center (m.cipCycleCutRootState i) :=
  MoleculeGraph.CIPState.certifiedByPath_root_of_adj m.mol (m.ligandAtom_adj i)

theorem child_not_mem_cipCycleCutRootState_seen_of_acyclic
    (m : OneCenterMolecule V) (hacyc : m.mol.Acyclic) (i : Fin 4) {child : V}
    (hadj : m.mol.Adj (m.ligandAtom i) child) (hchild : child ≠ m.center) :
    child ∉ insert (m.ligandAtom i) ({m.center} : Finset V) := by
  exact
    MoleculeGraph.CIPState.child_not_mem_insert_seen_of_certifiedByPath_acyclic
      (m := m.mol) hacyc (m.cipCycleCutRootState_certifiedByPath i) hadj hchild

theorem rawCIPKeyAux_eq_cycleCutKeyAux_root_of_treeLike
    (m : OneCenterMolecule V) (htree : m.mol.TreeLike) (i : Fin 4) (n : ℕ) :
    m.mol.rawCIPKeyAux n [(m.center, m.ligandAtom i)] =
      m.mol.cycleCutKeyAux n [m.cipCycleCutRootState i] := by
  have hfront :
      m.mol.FrontierCertifiedByPath m.center [m.cipCycleCutRootState i] := by
    intro s hs
    simp at hs
    subst s
    exact m.cipCycleCutRootState_certifiedByPath i
  simpa [cipCycleCutRootState, MoleculeGraph.CIPState.toRawPair] using
    MoleculeGraph.rawCIPKeyAux_eq_cycleCutKeyAux_of_frontierCertifiedByPath_treeLike
      (m := m.mol) htree (root := m.center) n hfront

theorem rawCIPKeyAux_cycleCutDepth_eq_cipKeyCycleCut_of_treeLike
    (m : OneCenterMolecule V) (htree : m.mol.TreeLike) (i : Fin 4) :
    m.mol.rawCIPKeyAux (Fintype.card V + 1) [(m.center, m.ligandAtom i)] =
      m.cipKeyCycleCut i := by
  have haux :=
    m.rawCIPKeyAux_eq_cycleCutKeyAux_root_of_treeLike htree i (Fintype.card V + 1)
  have hcut :=
    MoleculeGraph.cipKeyFromCycleCut_eq_cycleCutKeyAux
      (m := m.mol) (center := m.center) (start := m.ligandAtom i)
  simpa [cipKeyCycleCut, cipCycleCutRootState] using haux.trans hcut.symm

theorem cycleCutFrontier_root_eq_nil_at_card_of_treeLike
    (m : OneCenterMolecule V) (htree : m.mol.TreeLike) (i : Fin 4) :
    m.mol.cycleCutFrontier (Fintype.card V) [m.cipCycleCutRootState i] = [] := by
  have hfront :
      m.mol.FrontierCertifiedByPath m.center [m.cipCycleCutRootState i] := by
    intro s hs
    simp at hs
    subst s
    exact m.cipCycleCutRootState_certifiedByPath i
  have hcardRoot : MoleculeGraph.FrontierSeenCardEq 1 [m.cipCycleCutRootState i] := by
    intro s hs
    simp [cipCycleCutRootState] at hs
    subst s
    simp
  have hcard :=
    m.mol.frontierSeenCardEq_cycleCutFrontier_of_treeLike htree hfront hcardRoot
      (Fintype.card V)
  exact
    MoleculeGraph.cycleCutFrontier_eq_nil_of_frontierSeenCardEq_gt_card hcard
      (Nat.lt_add_of_pos_left Nat.zero_lt_one)

/-- A one-center molecule is cycle-cut CIP-stereogenic when its four cycle-cut ligand keys are
pairwise distinct. -/
def StereogenicByCIPCycleCut (m : OneCenterMolecule V) : Prop :=
  Function.Injective m.cipKeyCycleCut

/-- The descriptor key paired with the ligand index, used as a deterministic tie-breaker when
sorting cycle-cut CIP priorities. -/
def cipKeyWithTieCycleCut (m : OneCenterMolecule V) (i : Fin 4) :
    (List MoleculeGraph.AtomLabel) ×ₗ (Fin 4) :=
  toLex (cipKeyCycleCut m i, i)

/-- The four ligand indices, sorted in *descending* cycle-cut CIP order, with a deterministic tie-breaker. -/
def cipOrderCycleCut (m : OneCenterMolecule V) : List (Fin 4) :=
  (List.finRange 4).mergeSort (fun i j => decide (cipKeyWithTieCycleCut m j ≤ cipKeyWithTieCycleCut m i))

theorem cipOrderCycleCut_perm_finRange (m : OneCenterMolecule V) :
    m.cipOrderCycleCut.Perm (List.finRange 4) := by
  classical
  simpa [cipOrderCycleCut] using
    (List.mergeSort_perm (List.finRange 4)
      (fun i j => decide (cipKeyWithTieCycleCut m j ≤ cipKeyWithTieCycleCut m i)))

theorem length_cipOrderCycleCut (m : OneCenterMolecule V) : m.cipOrderCycleCut.length = 4 := by
  classical
  have hperm := cipOrderCycleCut_perm_finRange m
  have := hperm.length_eq
  simpa [List.length_finRange] using this

theorem nodup_cipOrderCycleCut (m : OneCenterMolecule V) : m.cipOrderCycleCut.Nodup := by
  classical
  exact (List.nodup_finRange 4).perm (cipOrderCycleCut_perm_finRange m).symm

theorem mem_cipOrderCycleCut (m : OneCenterMolecule V) (i : Fin 4) : i ∈ m.cipOrderCycleCut := by
  classical
  have hperm := cipOrderCycleCut_perm_finRange m
  exact (hperm.mem_iff).2 (List.mem_finRange i)

/-- The permutation `σ` such that `reindex g σ` lists the ligand vertices in descending cycle-cut CIP order. -/
def cipPermutationCycleCut (m : OneCenterMolecule V) : Equiv.Perm (Fin 4) := by
  classical
  let l : List (Fin 4) := m.cipOrderCycleCut
  have hlen : l.length = 4 := by
    simpa [l] using length_cipOrderCycleCut m
  have hnodup : l.Nodup := by
    simpa [l] using nodup_cipOrderCycleCut m
  have hmem : ∀ i : Fin 4, i ∈ l := by
    intro i
    simpa [l] using mem_cipOrderCycleCut m i
  exact ((Fin.castOrderIso hlen.symm).toEquiv).trans
    (List.Nodup.getEquivOfForallMemList l hnodup hmem)

/-- Resolved cycle-cut CIP priorities: the four cycle-cut ligand keys are pairwise distinct. -/
abbrev ResolvedCIPCycleCut (m : OneCenterMolecule V) : Prop :=
  m.StereogenicByCIPCycleCut

/-- The cycle-cut CIP order with explicit evidence that no key tie was broken by ligand index. -/
def cipOrderCycleCutOfResolved (m : OneCenterMolecule V) (_ : m.ResolvedCIPCycleCut) :
    List (Fin 4) :=
  m.cipOrderCycleCut

/-- The cycle-cut CIP permutation with explicit evidence that no key tie was broken by ligand
index. -/
def cipPermutationCycleCutOfResolved (m : OneCenterMolecule V) (_ : m.ResolvedCIPCycleCut) :
    Equiv.Perm (Fin 4) :=
  m.cipPermutationCycleCut

@[simp] theorem cipOrderCycleCutOfResolved_eq (m : OneCenterMolecule V)
    (h : m.ResolvedCIPCycleCut) :
    m.cipOrderCycleCutOfResolved h = m.cipOrderCycleCut := rfl

@[simp] theorem cipPermutationCycleCutOfResolved_eq (m : OneCenterMolecule V)
    (h : m.ResolvedCIPCycleCut) :
    m.cipPermutationCycleCutOfResolved h = m.cipPermutationCycleCut := rfl


noncomputable def cipOrderCycleCut? (m : OneCenterMolecule V) : Option (List (Fin 4)) :=
  by
    classical
    exact if h : m.ResolvedCIPCycleCut then some (m.cipOrderCycleCutOfResolved h) else none


noncomputable def cipPermutationCycleCut? (m : OneCenterMolecule V) :
    Option (Equiv.Perm (Fin 4)) :=
  by
    classical
    exact
      if h : m.ResolvedCIPCycleCut then
        some (m.cipPermutationCycleCutOfResolved h)
      else
        none

theorem cipOrderCycleCut?_eq_some_of_resolvedCIPCycleCut (m : OneCenterMolecule V)
    (h : m.ResolvedCIPCycleCut) :
    m.cipOrderCycleCut? = some m.cipOrderCycleCut := by
  classical
  simp [cipOrderCycleCut?, h]

theorem cipOrderCycleCut?_eq_none_of_not_resolvedCIPCycleCut (m : OneCenterMolecule V)
    (h : ¬ m.ResolvedCIPCycleCut) :
    m.cipOrderCycleCut? = none := by
  classical
  simp [cipOrderCycleCut?, h]

theorem cipPermutationCycleCut?_eq_some_of_resolvedCIPCycleCut
    (m : OneCenterMolecule V) (h : m.ResolvedCIPCycleCut) :
    m.cipPermutationCycleCut? = some m.cipPermutationCycleCut := by
  classical
  simp [cipPermutationCycleCut?, h]

theorem cipPermutationCycleCut?_eq_none_of_not_resolvedCIPCycleCut
    (m : OneCenterMolecule V) (h : ¬ m.ResolvedCIPCycleCut) :
    m.cipPermutationCycleCut? = none := by
  classical
  simp [cipPermutationCycleCut?, h]

theorem cipPermutationCycleCut?_isSome_iff_resolvedCIPCycleCut (m : OneCenterMolecule V) :
    m.cipPermutationCycleCut?.isSome = true ↔ m.ResolvedCIPCycleCut := by
  classical
  by_cases h : m.ResolvedCIPCycleCut
  · simp [cipPermutationCycleCut?, h]
  · simp [cipPermutationCycleCut?, h]

/-! ### Preferred descriptor-facing aliases -/

/-- Descriptor-facing CIP key.

The descriptor-facing API uses the cycle-cut expansion; the older raw key remains available as
`cipKey` for comparison and development. -/
abbrev cipKeyDescriptor (m : OneCenterMolecule V) (i : Fin 4) :
    List MoleculeGraph.AtomLabel :=
  m.cipKeyCycleCut i

/-- Descriptor-facing CIP-stereogenicity: the four cycle-cut descriptor keys are distinct. -/
abbrev StereogenicByCIPDescriptor (m : OneCenterMolecule V) : Prop :=
  m.StereogenicByCIPCycleCut

/-- Descriptor-facing resolved CIP priorities. -/
abbrev ResolvedCIPDescriptor (m : OneCenterMolecule V) : Prop :=
  m.ResolvedCIPCycleCut

/-- Descriptor-facing CIP ligand order, currently the cycle-cut order. -/
abbrev cipOrderDescriptor (m : OneCenterMolecule V) : List (Fin 4) :=
  m.cipOrderCycleCut

/-- Descriptor-facing CIP ligand permutation, currently the cycle-cut permutation. -/
abbrev cipPermutationDescriptor (m : OneCenterMolecule V) : Equiv.Perm (Fin 4) :=
  m.cipPermutationCycleCut

/-- Descriptor-facing CIP order with tie refusal. -/
abbrev cipOrderDescriptor? (m : OneCenterMolecule V) : Option (List (Fin 4)) :=
  m.cipOrderCycleCut?

/-- Descriptor-facing CIP permutation with tie refusal. -/
abbrev cipPermutationDescriptor? (m : OneCenterMolecule V) :
    Option (Equiv.Perm (Fin 4)) :=
  m.cipPermutationCycleCut?

theorem cipOrderDescriptor?_eq_some_of_resolvedCIPDescriptor
    (m : OneCenterMolecule V) (h : m.ResolvedCIPDescriptor) :
    m.cipOrderDescriptor? = some m.cipOrderDescriptor := by
  exact m.cipOrderCycleCut?_eq_some_of_resolvedCIPCycleCut h

theorem cipPermutationDescriptor?_eq_some_of_resolvedCIPDescriptor
    (m : OneCenterMolecule V) (h : m.ResolvedCIPDescriptor) :
    m.cipPermutationDescriptor? = some m.cipPermutationDescriptor := by
  exact m.cipPermutationCycleCut?_eq_some_of_resolvedCIPCycleCut h

/-! ### Raw/cycle-cut agreement bridge -/

/-- The raw expansion and the cycle-cut expansion agree on all four ligand keys.

This is the local interface for acyclic/no-duplicate expansion arguments: once a graph-theoretic
hypothesis proves this predicate, every raw CIP descriptor theorem can be transported to the
preferred cycle-cut descriptor path. -/
def RawCycleCutKeyAgreement (m : OneCenterMolecule V) : Prop :=
  ∀ i : Fin 4, m.cipKey i = m.cipKeyCycleCut i

/-- The raw CIP key has already stabilized by the cycle-cut depth used by the terminating
cycle-cut engine.  On tree-like graphs, this is the remaining finite-depth condition needed to
upgrade the frontier induction theorem to the existing descriptor-level raw/cycle-cut agreement
interface. -/
def RawCIPStabilizesAtCycleCutDepth (m : OneCenterMolecule V) : Prop :=
  ∀ i : Fin 4,
    m.mol.rawCIPKeyAux (2 * Fintype.card V) [(m.center, m.ligandAtom i)] =
      m.mol.rawCIPKeyAux (Fintype.card V + 1) [(m.center, m.ligandAtom i)]

theorem rawCIPStabilizesAtCycleCutDepth_of_treeLike
    (m : OneCenterMolecule V) (htree : m.mol.TreeLike) :
    m.RawCIPStabilizesAtCycleCutDepth := by
  intro i
  let root : MoleculeGraph.CIPState V := m.cipCycleCutRootState i
  have hnil : m.mol.cycleCutFrontier (Fintype.card V) [root] = [] := by
    simpa [root] using m.cycleCutFrontier_root_eq_nil_at_card_of_treeLike htree i
  have hrawLong :=
    m.rawCIPKeyAux_eq_cycleCutKeyAux_root_of_treeLike htree i (2 * Fintype.card V)
  have hrawCut :=
    m.rawCIPKeyAux_eq_cycleCutKeyAux_root_of_treeLike htree i (Fintype.card V + 1)
  have hcutLong :
      m.mol.cycleCutKeyAux (2 * Fintype.card V) [root] =
        m.mol.cycleCutKeyAux (Fintype.card V) [root] := by
    rw [show 2 * Fintype.card V = Fintype.card V + Fintype.card V by omega]
    exact m.mol.cycleCutKeyAux_eq_of_cycleCutFrontier_eq_nil (Fintype.card V) hnil
      (Fintype.card V)
  have hcutShort :
      m.mol.cycleCutKeyAux (Fintype.card V + 1) [root] =
        m.mol.cycleCutKeyAux (Fintype.card V) [root] :=
    m.mol.cycleCutKeyAux_eq_of_cycleCutFrontier_eq_nil (Fintype.card V) hnil 1
  calc
    m.mol.rawCIPKeyAux (2 * Fintype.card V) [(m.center, m.ligandAtom i)]
        = m.mol.cycleCutKeyAux (2 * Fintype.card V) [root] := by
          simpa [root] using hrawLong
    _ = m.mol.cycleCutKeyAux (Fintype.card V) [root] := hcutLong
    _ = m.mol.cycleCutKeyAux (Fintype.card V + 1) [root] := hcutShort.symm
    _ = m.mol.rawCIPKeyAux (Fintype.card V + 1) [(m.center, m.ligandAtom i)] := by
          simpa [root] using hrawCut.symm

theorem rawCycleCutKeyAgreement_of_treeLike_rawCIPStabilizesAtCycleCutDepth
    (m : OneCenterMolecule V) (htree : m.mol.TreeLike)
    (hstable : m.RawCIPStabilizesAtCycleCutDepth) :
    m.RawCycleCutKeyAgreement := by
  intro i
  have hraw :=
    MoleculeGraph.cipKeyFrom_eq_rawCIPKeyAux
      (m := m.mol) (center := m.center) (start := m.ligandAtom i)
  have hdepth := m.rawCIPKeyAux_cycleCutDepth_eq_cipKeyCycleCut_of_treeLike htree i
  simpa [OneCenterMolecule.cipKey] using hraw.trans ((hstable i).trans hdepth)

theorem rawCycleCutKeyAgreement_of_treeLike
    (m : OneCenterMolecule V) (htree : m.mol.TreeLike) :
    m.RawCycleCutKeyAgreement :=
  m.rawCycleCutKeyAgreement_of_treeLike_rawCIPStabilizesAtCycleCutDepth htree
    (m.rawCIPStabilizesAtCycleCutDepth_of_treeLike htree)

theorem cipKey_eq_cipKeyCycleCut_of_ligand_neighborFinset_eq_singleton
    (m : OneCenterMolecule V) (i : Fin 4)
    (hfin : m.mol.neighborFinset (m.ligandAtom i) = {m.center})
    (hbond : m.mol.bond (m.ligandAtom i) m.center = 1) :
    m.cipKey i = m.cipKeyCycleCut i := by
  have hraw :
      MoleculeGraph.cipKeyFrom m.mol m.center (m.ligandAtom i) =
        [toLex (m.mol.atomZ (m.ligandAtom i), m.mol.atomMass (m.ligandAtom i))] :=
    MoleculeGraph.cipKeyFrom_eq_singleton_of_neighborFinset_eq_singleton
      (m := m.mol) (center := m.center) (start := m.ligandAtom i) hfin hbond
  have hcut :
      MoleculeGraph.cipKeyFromCycleCut m.mol m.center (m.ligandAtom i) =
        [toLex (m.mol.atomZ (m.ligandAtom i), m.mol.atomMass (m.ligandAtom i))] :=
    MoleculeGraph.cipKeyFromCycleCut_eq_singleton_of_neighborFinset_eq_singleton
      (m := m.mol) (center := m.center) (start := m.ligandAtom i) hfin hbond
  simpa [OneCenterMolecule.cipKey, cipKeyCycleCut] using hraw.trans hcut.symm

theorem rawCycleCutKeyAgreement_of_ligands_neighborFinset_eq_singleton
    (m : OneCenterMolecule V)
    (hfin : ∀ i : Fin 4, m.mol.neighborFinset (m.ligandAtom i) = {m.center})
    (hbond : ∀ i : Fin 4, m.mol.bond (m.ligandAtom i) m.center = 1) :
    m.RawCycleCutKeyAgreement := by
  intro i
  exact m.cipKey_eq_cipKeyCycleCut_of_ligand_neighborFinset_eq_singleton i (hfin i) (hbond i)

theorem cipKey_eq_cipKeyCycleCut_of_rawCycleCutKeyAgreement
    (m : OneCenterMolecule V) (h : m.RawCycleCutKeyAgreement) (i : Fin 4) :
    m.cipKey i = m.cipKeyCycleCut i :=
  h i

theorem stereogenicByCIP_iff_stereogenicByCIPCycleCut_of_rawCycleCutKeyAgreement
    (m : OneCenterMolecule V) (h : m.RawCycleCutKeyAgreement) :
    m.StereogenicByCIP ↔ m.StereogenicByCIPCycleCut := by
  constructor
  · intro hst i j hij
    apply hst
    simpa [h i, h j] using hij
  · intro hst i j hij
    apply hst
    simpa [← h i, ← h j] using hij

theorem resolvedCIP_iff_resolvedCIPCycleCut_of_rawCycleCutKeyAgreement
    (m : OneCenterMolecule V) (h : m.RawCycleCutKeyAgreement) :
    m.ResolvedCIP ↔ m.ResolvedCIPCycleCut :=
  m.stereogenicByCIP_iff_stereogenicByCIPCycleCut_of_rawCycleCutKeyAgreement h

theorem cipOrder_eq_cipOrderCycleCut_of_rawCycleCutKeyAgreement
    (m : OneCenterMolecule V) (h : m.RawCycleCutKeyAgreement) :
    m.cipOrder = m.cipOrderCycleCut := by
  classical
  have hcmp :
      (fun i j => decide (m.cipKeyWithTie j ≤ m.cipKeyWithTie i)) =
        fun i j => decide (cipKeyWithTieCycleCut m j ≤ cipKeyWithTieCycleCut m i) := by
    funext i j
    have hi : m.cipKeyWithTie i = cipKeyWithTieCycleCut m i := by
      simp [OneCenterMolecule.cipKeyWithTie, cipKeyWithTieCycleCut, h i]
    have hj : m.cipKeyWithTie j = cipKeyWithTieCycleCut m j := by
      simp [OneCenterMolecule.cipKeyWithTie, cipKeyWithTieCycleCut, h j]
    simp [hi, hj]
  simp [OneCenterMolecule.cipOrder, cipOrderCycleCut, hcmp]

theorem cipPermutation_eq_cipPermutationCycleCut_of_rawCycleCutKeyAgreement
    (m : OneCenterMolecule V) (h : m.RawCycleCutKeyAgreement) :
    m.cipPermutation = m.cipPermutationCycleCut := by
  classical
  have horder := m.cipOrder_eq_cipOrderCycleCut_of_rawCycleCutKeyAgreement h
  ext i
  simp [OneCenterMolecule.cipPermutation, cipPermutationCycleCut, horder, List.get_eq_getElem]

theorem cipOrder?_eq_cipOrderCycleCut?_of_rawCycleCutKeyAgreement
    (m : OneCenterMolecule V) (h : m.RawCycleCutKeyAgreement) :
    m.cipOrder? = m.cipOrderCycleCut? := by
  classical
  have hresolved := m.resolvedCIP_iff_resolvedCIPCycleCut_of_rawCycleCutKeyAgreement h
  by_cases hr : m.ResolvedCIP
  · have hrc : m.ResolvedCIPCycleCut := hresolved.1 hr
    simp [OneCenterMolecule.cipOrder?, cipOrderCycleCut?, hr, hrc,
      m.cipOrder_eq_cipOrderCycleCut_of_rawCycleCutKeyAgreement h]
  · have hrc : ¬ m.ResolvedCIPCycleCut := by
      intro hrc
      exact hr (hresolved.2 hrc)
    simp [OneCenterMolecule.cipOrder?, cipOrderCycleCut?, hr, hrc]

theorem cipPermutation?_eq_cipPermutationCycleCut?_of_rawCycleCutKeyAgreement
    (m : OneCenterMolecule V) (h : m.RawCycleCutKeyAgreement) :
    m.cipPermutation? = m.cipPermutationCycleCut? := by
  classical
  have hresolved := m.resolvedCIP_iff_resolvedCIPCycleCut_of_rawCycleCutKeyAgreement h
  by_cases hr : m.ResolvedCIP
  · have hrc : m.ResolvedCIPCycleCut := hresolved.1 hr
    simp [OneCenterMolecule.cipPermutation?, cipPermutationCycleCut?, hr, hrc,
      m.cipPermutation_eq_cipPermutationCycleCut_of_rawCycleCutKeyAgreement h]
  · have hrc : ¬ m.ResolvedCIPCycleCut := by
      intro hrc
      exact hr (hresolved.2 hrc)
    simp [OneCenterMolecule.cipPermutation?, cipPermutationCycleCut?, hr, hrc]

theorem cipKey_eq_cipKeyCycleCut_of_treeLike
    (m : OneCenterMolecule V) (htree : m.mol.TreeLike) (i : Fin 4) :
    m.cipKey i = m.cipKeyCycleCut i :=
  m.cipKey_eq_cipKeyCycleCut_of_rawCycleCutKeyAgreement
    (m.rawCycleCutKeyAgreement_of_treeLike htree) i

theorem stereogenicByCIP_iff_stereogenicByCIPCycleCut_of_treeLike
    (m : OneCenterMolecule V) (htree : m.mol.TreeLike) :
    m.StereogenicByCIP ↔ m.StereogenicByCIPCycleCut :=
  m.stereogenicByCIP_iff_stereogenicByCIPCycleCut_of_rawCycleCutKeyAgreement
    (m.rawCycleCutKeyAgreement_of_treeLike htree)

theorem resolvedCIP_iff_resolvedCIPCycleCut_of_treeLike
    (m : OneCenterMolecule V) (htree : m.mol.TreeLike) :
    m.ResolvedCIP ↔ m.ResolvedCIPCycleCut :=
  m.resolvedCIP_iff_resolvedCIPCycleCut_of_rawCycleCutKeyAgreement
    (m.rawCycleCutKeyAgreement_of_treeLike htree)

theorem cipOrder_eq_cipOrderCycleCut_of_treeLike
    (m : OneCenterMolecule V) (htree : m.mol.TreeLike) :
    m.cipOrder = m.cipOrderCycleCut :=
  m.cipOrder_eq_cipOrderCycleCut_of_rawCycleCutKeyAgreement
    (m.rawCycleCutKeyAgreement_of_treeLike htree)

theorem cipPermutation_eq_cipPermutationCycleCut_of_treeLike
    (m : OneCenterMolecule V) (htree : m.mol.TreeLike) :
    m.cipPermutation = m.cipPermutationCycleCut :=
  m.cipPermutation_eq_cipPermutationCycleCut_of_rawCycleCutKeyAgreement
    (m.rawCycleCutKeyAgreement_of_treeLike htree)

theorem cipOrder?_eq_cipOrderCycleCut?_of_treeLike
    (m : OneCenterMolecule V) (htree : m.mol.TreeLike) :
    m.cipOrder? = m.cipOrderCycleCut? :=
  m.cipOrder?_eq_cipOrderCycleCut?_of_rawCycleCutKeyAgreement
    (m.rawCycleCutKeyAgreement_of_treeLike htree)

theorem cipPermutation?_eq_cipPermutationCycleCut?_of_treeLike
    (m : OneCenterMolecule V) (htree : m.mol.TreeLike) :
    m.cipPermutation? = m.cipPermutationCycleCut? :=
  m.cipPermutation?_eq_cipPermutationCycleCut?_of_rawCycleCutKeyAgreement
    (m.rawCycleCutKeyAgreement_of_treeLike htree)

/-- The cycle-cut CIP key is invariant under any center-fixing molecular automorphism. -/
theorem cipKeyCycleCut_eq_cipKeyCycleCut_ligandPermHom
    (m : OneCenterMolecule V) (e : m.CenterAut) (i : Fin 4) :
    m.cipKeyCycleCut ((m.ligandPermHom e) i) = m.cipKeyCycleCut i := by
  classical
  let eMol : m.mol.Aut := ⟨(e : Equiv.Perm V), e.property.1⟩
  have hZ : ∀ v, m.mol.atomZ ((e : Equiv.Perm V) v) = m.mol.atomZ v := by
    intro v
    exact MoleculeGraph.Aut.atomZ_eq (m := m.mol) eMol v
  have hMass : ∀ v, m.mol.atomMass ((e : Equiv.Perm V) v) = m.mol.atomMass v := by
    intro v
    exact MoleculeGraph.Aut.atomMass_eq (m := m.mol) eMol v
  have hBond : ∀ u v, m.mol.bond ((e : Equiv.Perm V) u) ((e : Equiv.Perm V) v) = m.mol.bond u v := by
    intro u v
    exact MoleculeGraph.Aut.bond_eq (m := m.mol) eMol u v
  have hlig :
      m.ligandAtom ((m.ligandPermHom e) i) = (e : Equiv.Perm V) (m.ligandAtom i) := by
    change m.ligandAtom (m.ligandPerm e i) = (e : Equiv.Perm V) (m.ligandAtom i)
    exact m.ligandAtom_ligandPerm (e := e) i
  have hcenter : (e : Equiv.Perm V) m.center = m.center := e.property.2
  have hkey :
      MoleculeGraph.cipKeyFromCycleCut m.mol m.center ((e : Equiv.Perm V) (m.ligandAtom i)) =
        MoleculeGraph.cipKeyFromCycleCut m.mol m.center (m.ligandAtom i) := by
    have hpres :
        MoleculeGraph.cipKeyFromCycleCut m.mol ((e : Equiv.Perm V) m.center)
            ((e : Equiv.Perm V) (m.ligandAtom i)) =
          MoleculeGraph.cipKeyFromCycleCut m.mol m.center (m.ligandAtom i) :=
      MoleculeGraph.cipKeyFromCycleCut_eq_of_preserves (m := m.mol) (e := (e : Equiv.Perm V))
        (hZ := hZ) (hMass := hMass) (hBond := hBond) (center := m.center) (start := m.ligandAtom i)
    simpa [hcenter] using hpres
  dsimp [OneCenterMolecule.cipKeyCycleCut]
  simpa [hlig] using hkey

/-- If the cycle-cut CIP keys are all distinct, every center symmetry fixes ligand indices. -/
theorem ligandPermHom_eq_one_of_stereogenicByCIPCycleCut
    (m : OneCenterMolecule V) (h : m.StereogenicByCIPCycleCut) (e : m.CenterAut) :
    m.ligandPermHom e = 1 := by
  classical
  ext i
  have hkey := m.cipKeyCycleCut_eq_cipKeyCycleCut_ligandPermHom (e := e) i
  have hi : (m.ligandPermHom e) i = i := h hkey
  simpa using congrArg Fin.val hi

/-- Cycle-cut CIP-stereogenicity implies chirality by the center-symmetry criterion. -/
theorem chiralBySymmetry_of_stereogenicByCIPCycleCut
    (m : OneCenterMolecule V) (h : m.StereogenicByCIPCycleCut) : m.ChiralBySymmetry := by
  intro e
  have hfix : m.ligandPermHom e = 1 :=
    m.ligandPermHom_eq_one_of_stereogenicByCIPCycleCut h e
  simp [hfix]

end OneCenterMolecule

end
end OneCenter
end TetraStereo
