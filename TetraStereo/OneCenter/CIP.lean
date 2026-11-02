import TetraStereo.OneCenter.MoleculeGraph
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Lex
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

namespace MoleculeGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev AtomLabel := AtomicNumber ×ₗ ℕ

private def atomLabel (m : MoleculeGraph V) (v : V) : AtomLabel :=
  toLex (m.atomZ v, m.atomMass v)

private def sortDescLabel (xs : List AtomLabel) : List AtomLabel :=
  xs.mergeSort (fun a b => decide (b ≤ a))

/-- Neighbors of `v`, repeated with multiplicity equal to the bond order. -/
private def neighborListWithMultiplicity (m : MoleculeGraph V) (v : V) : List V :=
  (m.neighborFinset v).toList.flatMap fun u => List.replicate (m.bond v u) u

/-- Children of a node `(parent, v)` in the “CIP expansion tree”.

We remove exactly one occurrence of `parent` (so multiple bonds yield duplicates). -/
private def children (m : MoleculeGraph V) (parent v : V) : List V :=
  (neighborListWithMultiplicity m v).erase parent

private def nextFrontier (m : MoleculeGraph V) (frontier : List (V × V)) : List (V × V) :=
  frontier.flatMap fun pv =>
    (children m pv.1 pv.2).map fun c => (pv.2, c)

private def cipKeyAux (m : MoleculeGraph V) : ℕ → List (V × V) → List AtomLabel
  | 0, _ => []
  | n + 1, frontier =>
      let layer := sortDescLabel (frontier.map fun pv => atomLabel m pv.2)
      layer ++ cipKeyAux m n (nextFrontier m frontier)

private theorem cipKeyAux_nil (m : MoleculeGraph V) :
    ∀ n, cipKeyAux m n ([] : List (V × V)) = []
  | 0 => by
      simp [cipKeyAux]
  | n + 1 => by
      simp [cipKeyAux, cipKeyAux_nil m n, nextFrontier, sortDescLabel]

/-! ### Public raw-frontier semantics

The historical CIP key above was intentionally implemented with private helpers.  The definitions
below expose the same breadth-first frontier semantics under stable names so downstream
cycle-cut/no-cycle theorems can state and prove comparison results without depending on private
implementation details.
-/

/-- The raw CIP atom label used at each frontier node. -/
def rawCIPAtomLabel (m : MoleculeGraph V) (v : V) : AtomLabel :=
  toLex (m.atomZ v, m.atomMass v)

/-- Sort one raw CIP layer in descending label order. -/
def rawCIPSortDescLabel (xs : List AtomLabel) : List AtomLabel :=
  xs.mergeSort (fun a b => decide (b ≤ a))

/-- The raw layer sort agrees with a structural insertion sort.

`List.mergeSort` is defined by well-founded recursion and does not reduce in the Lean kernel, so a
fact about a concretely sorted layer cannot be discharged by `decide` — historically it needed
`native_decide`, which pulls the compiler-trust axioms `Lean.ofReduceBool` and `Lean.trustCompiler`
into everything downstream, including the v0.1 claim package.  `List.insertionSort` is structurally
recursive and does reduce.  Rewriting a concrete goal with this equation and then calling `decide`
keeps the proof kernel-only while leaving the definition, and every proof stated against it,
untouched. -/
theorem rawCIPSortDescLabel_eq_insertionSort (xs : List AtomLabel) :
    rawCIPSortDescLabel xs = List.insertionSort (fun a b => b ≤ a) xs :=
  List.Perm.eq_of_pairwise
    (fun _ _ _ _ h1 h2 => le_antisymm h2 h1)
    (by
      simpa [rawCIPSortDescLabel] using
        List.pairwise_mergeSort (le := fun a b : AtomLabel => decide (b ≤ a))
          (fun _ _ _ hab hbc => by
            simp only [decide_eq_true_iff] at *
            exact le_trans hbc hab)
          (fun a b => by
            simpa [Bool.or_eq_true, decide_eq_true_iff] using le_total b a)
          xs)
    (List.pairwise_insertionSort _ xs)
    ((List.mergeSort_perm _ _).trans (List.perm_insertionSort _ _).symm)

/-- Raw CIP neighbors of `v`, repeated with multiplicity equal to the bond order. -/
def rawCIPNeighborListWithMultiplicity (m : MoleculeGraph V) (v : V) : List V :=
  (m.neighborFinset v).toList.flatMap fun u => List.replicate (m.bond v u) u

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

theorem count_rawCIPNeighborListWithMultiplicity_eq_bond
    (m : MoleculeGraph V) (v u : V) :
    (m.rawCIPNeighborListWithMultiplicity v).count u = m.bond v u := by
  classical
  have hcount := count_flatMap_replicate_eq (l := (m.neighborFinset v).toList)
    (hnodup := (m.neighborFinset v).nodup_toList) (f := fun x => m.bond v x) (u := u)
  by_cases hu : u ∈ m.neighborFinset v
  · simpa [rawCIPNeighborListWithMultiplicity, hu] using hcount
  · have hb : m.bond v u = 0 := by
      have hnotAdj : ¬ m.Adj v u := by
        simpa [MoleculeGraph.mem_neighborFinset] using hu
      exact Nat.eq_zero_of_not_pos hnotAdj
    simpa [rawCIPNeighborListWithMultiplicity, hu, hb] using hcount

/-- Raw CIP children of a frontier node `(parent, v)`, removing one occurrence of the parent. -/
def rawCIPChildren (m : MoleculeGraph V) (parent v : V) : List V :=
  (m.rawCIPNeighborListWithMultiplicity v).erase parent

/-- One raw CIP frontier expansion step. -/
def rawCIPNextFrontier (m : MoleculeGraph V) (frontier : List (V × V)) : List (V × V) :=
  frontier.flatMap fun pv =>
    (m.rawCIPChildren pv.1 pv.2).map fun c => (pv.2, c)

/-- The public raw CIP auxiliary key on an arbitrary frontier and depth. -/
def rawCIPKeyAux (m : MoleculeGraph V) : ℕ → List (V × V) → List AtomLabel
  | 0, _ => []
  | n + 1, frontier =>
      let layer := rawCIPSortDescLabel (frontier.map fun pv => m.rawCIPAtomLabel pv.2)
      layer ++ rawCIPKeyAux m n (m.rawCIPNextFrontier frontier)

private theorem cipKeyAux_eq_rawCIPKeyAux (m : MoleculeGraph V) :
    ∀ n frontier, cipKeyAux m n frontier = m.rawCIPKeyAux n frontier
  | 0, _ => by
      simp [cipKeyAux, rawCIPKeyAux]
  | n + 1, frontier => by
      simp [cipKeyAux, rawCIPKeyAux, nextFrontier, children, neighborListWithMultiplicity,
        sortDescLabel, rawCIPSortDescLabel, atomLabel, rawCIPAtomLabel,
        rawCIPNextFrontier, rawCIPChildren, rawCIPNeighborListWithMultiplicity,
        cipKeyAux_eq_rawCIPKeyAux m n]

/-- A *minimal* CIP priority key for the connected component of `start` away from `center`.

This is a breadth-first list of atom labels, sorted descending within each sphere. Each
vertex can occur multiple times due to multiple bonds and cycle expansion (as in the usual
“duplicate atom” conventions).

Notes:
- This is still a simplified “CIP-like” key: it ignores stereogenicity in substituents and
  other subtle CIP rules, but it does account for cycles and multiple bonds at the level
  of expansion multiplicity.
- The number of expansion steps is bounded by `2 * Fintype.card V` to ensure termination. -/
def cipKeyFrom (m : MoleculeGraph V) (center start : V) : List AtomLabel := by
  classical
  exact cipKeyAux m (2 * Fintype.card V) [(center, start)]

theorem cipKeyFrom_eq_rawCIPKeyAux (m : MoleculeGraph V) (center start : V) :
    cipKeyFrom m center start = m.rawCIPKeyAux (2 * Fintype.card V) [(center, start)] := by
  simp [cipKeyFrom, cipKeyAux_eq_rawCIPKeyAux]

theorem cipKeyFrom_head? (m : MoleculeGraph V) (center start : V) :
    (cipKeyFrom m center start).head? = some (toLex (m.atomZ start, m.atomMass start)) := by
  classical
  haveI : Nonempty V := ⟨start⟩
  have hpos : 0 < 2 * Fintype.card V :=
    Nat.mul_pos (by decide : 0 < 2) (Fintype.card_pos)
  -- Avoid unfolding `cipKeyAux` recursively: pattern-match on the step bound once.
  cases hsteps : (2 * Fintype.card V) with
  | zero =>
      have : False := by
        have hpos' := hpos
        simp [hsteps] at hpos'
      exact (False.elim this)
  | succ n =>
      -- Unfold the first expansion step; the first layer is the label of `start`.
      simp [cipKeyFrom, hsteps, cipKeyAux, sortDescLabel, atomLabel]

theorem cipKeyFrom_eq_singleton_of_neighborFinset_eq_singleton (m : MoleculeGraph V) (center start : V)
    (hfin : m.neighborFinset start = {center}) (hbond : m.bond start center = 1) :
    cipKeyFrom m center start = [toLex (m.atomZ start, m.atomMass start)] := by
  classical
  haveI : Nonempty V := ⟨start⟩
  have hpos : 0 < 2 * Fintype.card V :=
    Nat.mul_pos (by decide : 0 < 2) (Fintype.card_pos)
  cases hsteps : (2 * Fintype.card V) with
  | zero =>
      have : False := by
        have hpos' := hpos
        simp [hsteps] at hpos'
      exact (False.elim this)
  | succ n =>
      have hchildren : children m center start = [] := by
        simp [children, neighborListWithMultiplicity, hfin, hbond]
      simp [cipKeyFrom, hsteps, cipKeyAux, nextFrontier, hchildren, sortDescLabel, atomLabel, cipKeyAux_nil]

theorem cipKeyFrom_length_gt_one_of_exists_adj_ne_center (m : MoleculeGraph V) (center start : V)
    (h : ∃ u, u ≠ center ∧ m.Adj start u) :
    1 < (cipKeyFrom m center start).length := by
  classical
  haveI : Nonempty V := ⟨start⟩
  have hpos : 0 < 2 * Fintype.card V :=
    Nat.mul_pos (by decide : 0 < 2) (Fintype.card_pos)
  have hge2 : 2 ≤ 2 * Fintype.card V :=
    Nat.mul_le_mul_left 2 (Nat.succ_le_iff.2 (Fintype.card_pos))
  rcases h with ⟨u, huc, huAdj⟩
  have huFin : u ∈ m.neighborFinset start := by
    simpa [MoleculeGraph.mem_neighborFinset] using huAdj
  have huBond : m.bond start u ≠ 0 :=
    ne_of_gt huAdj
  have huIn : u ∈ neighborListWithMultiplicity m start := by
    refine (List.mem_flatMap).2 ?_
    refine ⟨u, ?_, ?_⟩
    · simpa [Finset.mem_toList] using huFin
    · simp [List.mem_replicate, huBond]
  have huChild : u ∈ children m center start := by
    simpa [children] using (List.mem_erase_of_ne (l := neighborListWithMultiplicity m start) (a := u)
      (b := center) huc).2 huIn
  have hfront1 : nextFrontier m [(center, start)] ≠ [] := by
    have : (start, u) ∈ nextFrontier m [(center, start)] := by
      simp [nextFrontier, huChild]
    intro hnil
    simp [hnil] at this

  -- Unfold `cipKeyFrom` at two steps and compare lengths.
  cases hsteps : (2 * Fintype.card V) with
  | zero =>
      have : False := by
        have hpos' := hpos
        simp [hsteps] at hpos'
      exact (False.elim this)
  | succ n =>
      cases n with
      | zero =>
          have hge2' := hge2
          simp [hsteps] at hge2'
      | succ n =>
          set front1 : List (V × V) := nextFrontier m [(center, start)]
          have hfront1' : front1 ≠ [] := by
            simpa [front1] using hfront1
          set xs : List AtomLabel := front1.map fun pv => atomLabel m pv.2
          have hxs_len : 0 < xs.length := by
            have : 0 < front1.length := (List.length_pos_iff_ne_nil).2 hfront1'
            simpa [xs] using this
          set layer1 : List AtomLabel := sortDescLabel xs
          have hlayer1_len : 0 < layer1.length := by
            have hperm : layer1.Perm xs := by
              simpa [layer1, sortDescLabel] using
                (List.mergeSort_perm xs (fun a b => decide (b ≤ a)))
            have hl : layer1.length = xs.length := hperm.length_eq
            simpa [hl] using hxs_len
          have hrest_len : 0 < (cipKeyAux m (Nat.succ n) front1).length := by
            -- The next step begins with the nonempty layer `layer1`.
            have : (cipKeyAux m (Nat.succ n) front1).length =
                layer1.length + (cipKeyAux m n (nextFrontier m front1)).length := by
              simp [cipKeyAux, front1, xs, layer1, List.length_append]
            -- Hence its length is positive.
            have : 0 < (cipKeyAux m (Nat.succ n) front1).length := by
              simpa [this] using Nat.add_pos_left hlayer1_len _
            exact this
          have hlen :
              (cipKeyFrom m center start).length =
                1 + (cipKeyAux m (Nat.succ n) front1).length := by
            -- The first layer has length `1`.
            simp [cipKeyFrom, hsteps, cipKeyAux, front1, sortDescLabel, atomLabel, List.length_append,
              Nat.add_left_comm, Nat.add_comm]
          have : 1 < (cipKeyFrom m center start).length := by
            -- `1 < 1 + restLen` since `restLen > 0`.
            have hlt : 1 < 1 + (cipKeyAux m (Nat.succ n) front1).length :=
              Nat.lt_add_of_pos_right hrest_len
            simpa [hlen] using hlt
          exact this

/-! ### Invariance under relabeling -/

private def pairMap (e : Equiv.Perm V) (pv : V × V) : V × V :=
  (e pv.1, e pv.2)

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

private theorem cipKeyAux_eq_of_perm (m : MoleculeGraph V) :
    ∀ n {frontier₁ frontier₂ : List (V × V)},
      frontier₁.Perm frontier₂ → cipKeyAux m n frontier₁ = cipKeyAux m n frontier₂
  | 0, _, _, _ => by simp [cipKeyAux]
  | n + 1, frontier₁, frontier₂, hperm => by
      have hlayer :
          sortDescLabel (frontier₁.map fun pv => atomLabel m pv.2) =
            sortDescLabel (frontier₂.map fun pv => atomLabel m pv.2) := by
        apply sortDescLabel_eq_of_perm
        exact hperm.map _
      have hnext :
          (nextFrontier m frontier₁).Perm (nextFrontier m frontier₂) := by
        simpa [nextFrontier] using
          hperm.flatMap_right (fun pv => (children m pv.1 pv.2).map fun c => (pv.2, c))
      simp [cipKeyAux, hlayer, cipKeyAux_eq_of_perm m n hnext]

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
    -- Transport adjacency across the bond-order equality.
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
        -- `v = e (e.symm v)` and `e.symm v ∈ s.toList`.
        simpa using (List.mem_map.2 ⟨e.symm v, hsList, by simp⟩)
      exact (List.mem_toFinset).2 this
  have hperm₁ : (s.map e.toEmbedding).toList.Perm (s.toList.map e).toFinset.toList :=
    (Finset.perm_toList.2 hfin.symm)
  have hnodup : (s.toList.map e).Nodup := by
    exact (s.nodup_toList.map e.injective)
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
  -- Replace the neighbor finset by its mapped form.
  have htoList :
      (m.neighborFinset (e v)).toList.Perm ((m.neighborFinset v).toList.map e) := by
    simpa [hneighbors] using toList_map_perm (s := m.neighborFinset v) e
  -- `flatMap` preserves permutations.
  have hflat :
      ((m.neighborFinset (e v)).toList.flatMap (fun u => List.replicate (m.bond (e v) u) u)).Perm
        (((m.neighborFinset v).toList.map e).flatMap
          (fun u => List.replicate (m.bond (e v) u) u)) := by
    exact htoList.flatMap_right _
  -- Rewrite the RHS into `map e` of the original multiplicity list.
  have hrewrite :
      ((m.neighborFinset v).toList.map e).flatMap
          (fun u => List.replicate (m.bond (e v) u) u) =
        (neighborListWithMultiplicity m v).map e := by
    -- Push `flatMap` through `map` and use bond preservation.
    simp [neighborListWithMultiplicity, List.flatMap_map, List.map_flatMap, hBond]
  simpa [neighborListWithMultiplicity, hrewrite] using hflat

private theorem children_perm (m : MoleculeGraph V) (e : Equiv.Perm V)
    (hBond : ∀ u v, m.bond (e u) (e v) = m.bond u v) (parent v : V) :
    (children m (e parent) (e v)).Perm ((children m parent v).map e) := by
  classical
  have hnl :
      (neighborListWithMultiplicity m (e v)).Perm ((neighborListWithMultiplicity m v).map e) :=
    neighborListWithMultiplicity_perm (m := m) (e := e) hBond v
  -- Erase the corresponding parent from both sides.
  have herase :
      ((neighborListWithMultiplicity m (e v)).erase (e parent)).Perm
        (((neighborListWithMultiplicity m v).map e).erase (e parent)) :=
    (List.Perm.erase (e parent) hnl)
  -- Pull `erase` back through `map e`.
  have hmap :
      (((neighborListWithMultiplicity m v).erase parent).map e) =
        ((neighborListWithMultiplicity m v).map e).erase (e parent) := by
    -- `map_erase` is stated in the opposite direction.
    simpa using
      (List.map_erase (f := e) (finj := e.injective) (a := parent) (l := neighborListWithMultiplicity m v))
  -- Finish.
  simpa [children, hmap] using herase

private theorem nextFrontier_map_pairMap (m : MoleculeGraph V) (e : Equiv.Perm V) (frontier : List (V × V)) :
    (nextFrontier m frontier).map (pairMap e) =
      frontier.flatMap fun pv =>
        (children m pv.1 pv.2).map fun c => (e pv.2, e c) := by
  -- Pure list algebra: `map` distributes over `flatMap`, and `pairMap` acts componentwise.
  -- Unfold `nextFrontier`, push `map` through `flatMap`, then simplify the induced pair mapping.
  have hmap :
      (frontier.flatMap fun pv => (children m pv.1 pv.2).map fun c => (pv.2, c)).map (pairMap e) =
        frontier.flatMap fun pv =>
          ((children m pv.1 pv.2).map fun c => (pv.2, c)).map (pairMap e) := by
    simpa using
      (List.map_flatMap (f := pairMap e)
        (g := fun pv => (children m pv.1 pv.2).map fun c => (pv.2, c)) (l := frontier))
  -- Now identify the inner maps pointwise.
  have hinn :
      (frontier.flatMap fun pv =>
          ((children m pv.1 pv.2).map fun c => (pv.2, c)).map (pairMap e)) =
        frontier.flatMap fun pv =>
          (children m pv.1 pv.2).map fun c => (e pv.2, e c) := by
    refine congrArg (fun f => frontier.flatMap f) ?_
    funext pv
    simp [List.map_map, Function.comp, pairMap]
  -- Finish.
  simpa [nextFrontier] using hmap.trans hinn

private theorem nextFrontier_perm_map (m : MoleculeGraph V) (e : Equiv.Perm V)
    (hBond : ∀ u v, m.bond (e u) (e v) = m.bond u v) (frontier : List (V × V)) :
    (nextFrontier m (frontier.map (pairMap e))).Perm ((nextFrontier m frontier).map (pairMap e)) := by
  classical
  -- Rewrite both sides into `flatMap` forms over the original frontier.
  have hlhs :
      nextFrontier m (frontier.map (pairMap e)) =
        frontier.flatMap fun pv =>
          (children m (e pv.1) (e pv.2)).map fun c => (e pv.2, c) := by
    simp [nextFrontier, pairMap, List.flatMap_map]
  have hrhs :
      (nextFrontier m frontier).map (pairMap e) =
        frontier.flatMap fun pv =>
          (children m pv.1 pv.2).map fun c => (e pv.2, e c) := by
    exact nextFrontier_map_pairMap (m := m) (e := e) frontier
  -- Apply `flatMap_left` using the child permutation lemma.
  have hperm :
      (frontier.flatMap (fun pv => (children m (e pv.1) (e pv.2)).map fun c => (e pv.2, c))).Perm
        (frontier.flatMap (fun pv => (children m pv.1 pv.2).map fun c => (e pv.2, e c))) := by
    apply List.Perm.flatMap_left
    intro pv hpv
    have hch : (children m (e pv.1) (e pv.2)).Perm ((children m pv.1 pv.2).map e) :=
      children_perm (m := m) (e := e) hBond pv.1 pv.2
    -- Map both sides to pairs `(e v, ·)`.
    simpa [List.map_map, Function.comp, pairMap] using
      (hch.map (fun c => (e pv.2, c)))
  simpa [hlhs, hrhs] using hperm

private theorem cipKeyAux_eq_of_map (m : MoleculeGraph V) (e : Equiv.Perm V)
    (hZ : ∀ v, m.atomZ (e v) = m.atomZ v) (hMass : ∀ v, m.atomMass (e v) = m.atomMass v)
    (hBond : ∀ u v, m.bond (e u) (e v) = m.bond u v) :
    ∀ n (frontier : List (V × V)),
      cipKeyAux m n (frontier.map (pairMap e)) = cipKeyAux m n frontier
  | 0, _ => by simp [cipKeyAux]
  | n + 1, frontier => by
      have hlayer :
          sortDescLabel (frontier.map ((fun pv => atomLabel m pv.2) ∘ pairMap e)) =
            sortDescLabel (frontier.map fun pv => atomLabel m pv.2) := by
        -- The atom labels are preserved by `e`.
        apply congrArg sortDescLabel
        simp [Function.comp, pairMap,
          atomLabel_eq_of_preserves (m := m) (e := e) hZ hMass]
      have hnextPerm :
          (nextFrontier m (frontier.map (pairMap e))).Perm ((nextFrontier m frontier).map (pairMap e)) :=
        nextFrontier_perm_map (m := m) (e := e) hBond frontier
      -- Use permutation-invariance to replace the next frontier by the mapped next frontier,
      -- then the induction hypothesis.
      have hnext :
          cipKeyAux m n (nextFrontier m (frontier.map (pairMap e))) =
            cipKeyAux m n ((nextFrontier m frontier).map (pairMap e)) := by
        apply cipKeyAux_eq_of_perm (m := m) n hnextPerm
      simp [cipKeyAux, List.map_map, hlayer, hnext,
        cipKeyAux_eq_of_map m e hZ hMass hBond n (nextFrontier m frontier)]

/-- `cipKeyFrom` is invariant under any relabeling of atoms that preserves atomic labels and bond orders. -/
theorem cipKeyFrom_eq_of_preserves (m : MoleculeGraph V) (e : Equiv.Perm V)
    (hZ : ∀ v, m.atomZ (e v) = m.atomZ v) (hMass : ∀ v, m.atomMass (e v) = m.atomMass v)
    (hBond : ∀ u v, m.bond (e u) (e v) = m.bond u v) (center start : V) :
    cipKeyFrom m (e center) (e start) = cipKeyFrom m center start := by
  classical
  -- Reduce to the auxiliary key on the singleton frontier, then use `cipKeyAux_eq_of_map`.
  simpa [cipKeyFrom, pairMap] using
    (cipKeyAux_eq_of_map (m := m) (e := e) hZ hMass hBond (2 * Fintype.card V) [(center, start)])

end MoleculeGraph

namespace OneCenterMolecule

open Prod.Lex

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The (still simplified) CIP-like key of the `i`-th ligand, computed from the molecular graph. -/
def cipKey (m : OneCenterMolecule V) (i : Fin 4) : List MoleculeGraph.AtomLabel :=
  MoleculeGraph.cipKeyFrom m.mol m.center (m.ligandAtom i)

/-- A one-center molecule is *CIP-stereogenic* when the four ligand keys are pairwise distinct. -/
def StereogenicByCIP (m : OneCenterMolecule V) : Prop :=
  Function.Injective m.cipKey

/-- The CIP key paired with the ligand index, used as a deterministic tie-breaker when sorting. -/
def cipKeyWithTie (m : OneCenterMolecule V) (i : Fin 4) :
    (List MoleculeGraph.AtomLabel) ×ₗ (Fin 4) :=
  toLex (cipKey m i, i)

/-- The four ligand indices, sorted in *descending* CIP order, with a deterministic tie-breaker.

This raw order is total even when ligand CIP keys tie.  Use `ResolvedCIP`, `cipOrderOfResolved`,
or `cipOrder?` when the order is being used as a stereochemical descriptor. -/
def cipOrder (m : OneCenterMolecule V) : List (Fin 4) :=
  (List.finRange 4).mergeSort (fun i j => decide (cipKeyWithTie m j ≤ cipKeyWithTie m i))

theorem cipOrder_perm_finRange (m : OneCenterMolecule V) :
    m.cipOrder.Perm (List.finRange 4) := by
  classical
  simpa [cipOrder] using
    (List.mergeSort_perm (List.finRange 4)
      (fun i j => decide (cipKeyWithTie m j ≤ cipKeyWithTie m i)))

/-- The CIP ordering list has length `4`. -/
theorem length_cipOrder (m : OneCenterMolecule V) : m.cipOrder.length = 4 := by
  classical
  have hperm := cipOrder_perm_finRange m
  have := hperm.length_eq
  simpa [List.length_finRange] using this

/-- The CIP ordering list has no duplicates. -/
theorem nodup_cipOrder (m : OneCenterMolecule V) : m.cipOrder.Nodup := by
  classical
  exact (List.nodup_finRange 4).perm (cipOrder_perm_finRange m).symm

/-- Every ligand index occurs in the CIP ordering list. -/
theorem mem_cipOrder (m : OneCenterMolecule V) (i : Fin 4) : i ∈ m.cipOrder := by
  classical
  have hperm := cipOrder_perm_finRange m
  -- `finRange` contains every element by construction.
  exact (hperm.mem_iff).2 (List.mem_finRange i)

/-- The permutation `σ` such that `reindex g σ` lists the ligand vertices in descending CIP order.

This is the deterministic raw permutation.  It exists for every graph because ties are broken by
the original ligand index.  For descriptor-level use, prefer `cipPermutationOfResolved` or
`cipPermutation?`, which require/provide evidence that the CIP keys are pairwise distinct. -/
def cipPermutation (m : OneCenterMolecule V) : Equiv.Perm (Fin 4) := by
  classical
  let l : List (Fin 4) := m.cipOrder
  have hlen : l.length = 4 := by
    simpa [l] using length_cipOrder m
  have hnodup : l.Nodup := by
    simpa [l] using nodup_cipOrder m
  have hmem : ∀ i : Fin 4, i ∈ l := by
    intro i
    simpa [l] using mem_cipOrder m i
  exact ((Fin.castOrderIso hlen.symm).toEquiv).trans
    (List.Nodup.getEquivOfForallMemList l hnodup hmem)

/-- Resolved CIP priorities: the four ligand keys are pairwise distinct, so no deterministic
index tie-breaker is doing stereochemical work. -/
abbrev ResolvedCIP (m : OneCenterMolecule V) : Prop :=
  m.StereogenicByCIP

/-- The CIP order when priorities are resolved.  The proof argument records that no tie-breaker is
being used to create a descriptor. -/
def cipOrderOfResolved (m : OneCenterMolecule V) (_ : m.ResolvedCIP) : List (Fin 4) :=
  m.cipOrder

/-- The CIP permutation when priorities are resolved.  The proof argument records that no
tie-breaker is being used to create a descriptor. -/
def cipPermutationOfResolved (m : OneCenterMolecule V) (_ : m.ResolvedCIP) :
    Equiv.Perm (Fin 4) :=
  m.cipPermutation

@[simp] theorem cipOrderOfResolved_eq (m : OneCenterMolecule V) (h : m.ResolvedCIP) :
    m.cipOrderOfResolved h = m.cipOrder := rfl

@[simp] theorem cipPermutationOfResolved_eq (m : OneCenterMolecule V) (h : m.ResolvedCIP) :
    m.cipPermutationOfResolved h = m.cipPermutation := rfl


noncomputable def cipOrder? (m : OneCenterMolecule V) : Option (List (Fin 4)) :=
  by
    classical
    exact if h : m.ResolvedCIP then some (m.cipOrderOfResolved h) else none



noncomputable def cipPermutation? (m : OneCenterMolecule V) : Option (Equiv.Perm (Fin 4)) :=
  by
    classical
    exact if h : m.ResolvedCIP then some (m.cipPermutationOfResolved h) else none

theorem cipOrder?_eq_some_of_resolvedCIP (m : OneCenterMolecule V) (h : m.ResolvedCIP) :
    m.cipOrder? = some m.cipOrder := by
  classical
  simp [cipOrder?, h]

theorem cipOrder?_eq_none_of_not_resolvedCIP (m : OneCenterMolecule V) (h : ¬ m.ResolvedCIP) :
    m.cipOrder? = none := by
  classical
  simp [cipOrder?, h]

theorem cipPermutation?_eq_some_of_resolvedCIP (m : OneCenterMolecule V) (h : m.ResolvedCIP) :
    m.cipPermutation? = some m.cipPermutation := by
  classical
  simp [cipPermutation?, h]

theorem cipPermutation?_eq_none_of_not_resolvedCIP (m : OneCenterMolecule V)
    (h : ¬ m.ResolvedCIP) :
    m.cipPermutation? = none := by
  classical
  simp [cipPermutation?, h]

theorem cipPermutation?_isSome_iff_resolvedCIP (m : OneCenterMolecule V) :
    m.cipPermutation?.isSome = true ↔ m.ResolvedCIP := by
  classical
  by_cases h : m.ResolvedCIP
  · simp [cipPermutation?, h]
  · simp [cipPermutation?, h]

end OneCenterMolecule

end
end OneCenter
end TetraStereo
