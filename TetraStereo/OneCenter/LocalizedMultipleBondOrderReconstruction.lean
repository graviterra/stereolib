import TetraStereo.OneCenter.AcyclicCutBranchAutomorphism
import TetraStereo.OneCenter.LocalizedMultipleBondRealPositionAdjacency
import TetraStereo.KernelOnly
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

set_option autoImplicit false































































namespace TetraStereo
namespace OneCenter
namespace LocalizedMultipleBondOrderReconstruction

universe u v

/-! ## The pure incident-excess rigidity -/

/-- The incident excess total at a vertex: its incoming edge weight plus the weights of all edges to
its children.  At the root the incoming slot is the single external boundary edge. -/
def childTotal {V : Type u} (childList : V → List V) (w : V → ℕ) (v : V) : ℕ :=
  w v + ((childList v).map w).sum

/-- **Pure incoming-weight uniqueness.**  On a finite rooted tree with a rank that increases by one
from a vertex to each of its children, two weight assignments with the same incident excess total
at every vertex are equal.  The proof is a leaf-to-root induction on `bound - rank` and uses
additive cancellation `Nat.add_right_cancel`, never truncated subtraction. -/
theorem list_incoming_weights_unique {V : Type u}
    (childList : V → List V) (rank : V → ℕ) (bound : ℕ)
    (rank_le : ∀ v, rank v ≤ bound)
    (child_rank : ∀ v c, c ∈ childList v → rank c = rank v + 1)
    (S w z : V → ℕ)
    (hw : ∀ v, S v = childTotal childList w v)
    (hz : ∀ v, S v = childTotal childList z v) :
    w = z := by
  funext v
  have main : ∀ m, ∀ v, bound - rank v = m → w v = z v := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
        intro v hv
        have hchildren : ∀ c ∈ childList v, w c = z c := by
          intro c hc
          have hcRank : rank c = rank v + 1 := child_rank v c hc
          have hlt : bound - rank c < m := by
            have hvLe : rank v ≤ bound := rank_le v
            have hcLe : rank c ≤ bound := rank_le c
            omega
          exact ih (bound - rank c) hlt c rfl
        have hmap : (childList v).map w = (childList v).map z :=
          List.map_congr_left hchildren
        have hsum : ((childList v).map w).sum = ((childList v).map z).sum := by
          rw [hmap]
        have hwv : S v = w v + ((childList v).map w).sum := hw v
        have hzv : S v = z v + ((childList v).map z).sum := hz v
        have hEq : w v + ((childList v).map w).sum =
            z v + ((childList v).map w).sum := by
          rw [← hwv, hzv, hsum]
        exact Nat.add_right_cancel hEq
  exact main (bound - rank v) v rfl

/-- **Existence and uniqueness of the incident-excess solution.**  A weight assignment with the
prescribed incident excess totals, when it exists, is unique.  This is the precise sense in which
the totals *determine* every incoming weight. -/
theorem exists_unique_weights {V : Type u}
    (childList : V → List V) (rank : V → ℕ) (bound : ℕ)
    (rank_le : ∀ v, rank v ≤ bound)
    (child_rank : ∀ v c, c ∈ childList v → rank c = rank v + 1)
    (S : V → ℕ) :
    (∃ w : V → ℕ, ∀ v, S v = childTotal childList w v) →
      ∃! w : V → ℕ, ∀ v, S v = childTotal childList w v := by
  rintro ⟨w, hw⟩
  exact ⟨w, hw, fun z hz =>
    list_incoming_weights_unique childList rank bound rank_le child_rank S z w hz hw⟩

/-! ## Rooted branch data and its uniqueness theorem -/

/-- A finite rooted tree on a vertex type, with an explicit parent map, the list of children of
every vertex, and a rank that increases by one along every parent edge.  The vertex type need not
be finite as a Lean type; the rank is bounded, which is the finiteness content used by the
leaf-to-root induction. -/
structure RootedBranch (V : Type u) where
  /-- The root of the branch (the attachment atom in the physical application). -/
  root : V
  /-- The parent of a vertex; `none` exactly at the root. -/
  parent : V → Option V
  /-- The children of a vertex, as a duplicate-free list. -/
  childList : V → List V
  /-- Rank (distance from the root in the physical application). -/
  rank : V → ℕ
  /-- A uniform bound on the rank; finiteness content of the leaf-to-root induction. -/
  rankBound : ℕ
  parent_root : parent root = none
  exists_parent : ∀ x, x ≠ root → ∃ p, parent x = some p
  childList_spec : ∀ x c, c ∈ childList x ↔ parent c = some x
  childList_nodup : ∀ x, (childList x).Nodup
  parent_rank : ∀ x p, parent x = some p → rank x = rank p + 1
  rank_le : ∀ x, rank x ≤ rankBound

namespace RootedBranch

variable {V : Type u}

/-- The children of `v` have rank one more than `v`. -/
theorem child_rank (data : RootedBranch V) {v c : V} (hc : c ∈ data.childList v) :
    data.rank c = data.rank v + 1 :=
  data.parent_rank c v ((data.childList_spec v c).mp hc)

/-- **Incoming-weight uniqueness on a rooted branch.**  All incoming edge weights — the parent edge
of every vertex and the single external boundary edge at the root — are determined by the incident
excess totals. -/
theorem weights_unique (data : RootedBranch V) (S w z : V → ℕ)
    (hw : ∀ v, S v = childTotal data.childList w v)
    (hz : ∀ v, S v = childTotal data.childList z v) :
    w = z :=
  list_incoming_weights_unique data.childList data.rank data.rankBound data.rank_le
    (fun _v _c hc => data.child_rank hc) S w z hw hz

/-- **Determination on a rooted branch.**  The incident excess totals admit at most one weight
assignment; equivalently, every weight assignment satisfying them is the determined one. -/
theorem exists_unique_weights (data : RootedBranch V) (S : V → ℕ) :
    (∃ w : V → ℕ, ∀ v, S v = childTotal data.childList w v) →
      ∃! w : V → ℕ, ∀ v, S v = childTotal data.childList w v :=
  _root_.TetraStereo.OneCenter.LocalizedMultipleBondOrderReconstruction.exists_unique_weights
    data.childList data.rank data.rankBound data.rank_le
    (fun _v _c hc => data.child_rank hc) S

end RootedBranch

/-! ## Transport across a rooted tree isomorphism

An isomorphism of rooted branches preserves root, parent and the child lists.  Incident-excess
equations then transport; this is the form needed when two actual realized trees with the same
comparison-visible shape carry the same excess sums. -/

structure RootedBranchIso {V : Type u} {W : Type v}
    (data₁ : RootedBranch V) (data₂ : RootedBranch W) where
  toEquiv : V ≃ W
  map_root : toEquiv data₁.root = data₂.root
  map_parent : ∀ x, (data₁.parent x).map toEquiv = data₂.parent (toEquiv x)
  map_children : ∀ x, (data₁.childList x).map toEquiv = data₂.childList (toEquiv x)

namespace RootedBranchIso

variable {V : Type u} {W : Type v} {data₁ : RootedBranch V} {data₂ : RootedBranch W}

/-- Weights transport along a rooted branch isomorphism whenever the incident excess sums agree
through the same isomorphism.  The proof pulls the left weight assignment back along the
isomorphism, checks that it satisfies the right equations (the child lists correspond exactly), and
applies right-hand uniqueness. -/
theorem weights_transport (iso : RootedBranchIso data₁ data₂)
    (S₁ : V → ℕ) (S₂ : W → ℕ)
    (w₁ : V → ℕ) (w₂ : W → ℕ)
    (hsum : ∀ x, S₁ x = S₂ (iso.toEquiv x))
    (hw₁ : ∀ x, S₁ x = childTotal data₁.childList w₁ x)
    (hw₂ : ∀ y, S₂ y = childTotal data₂.childList w₂ y) :
    ∀ x, w₁ x = w₂ (iso.toEquiv x) := by
  let pulled : W → ℕ := fun y => w₁ (iso.toEquiv.symm y)
  have hpulled : ∀ y, S₂ y = childTotal data₂.childList pulled y := by
    intro y
    obtain ⟨x, rfl⟩ : ∃ x, iso.toEquiv x = y := ⟨iso.toEquiv.symm y,
      iso.toEquiv.apply_symm_apply y⟩
    have hsumx : S₂ (iso.toEquiv x) = S₁ x := (hsum x).symm
    rw [hsumx, hw₁ x]
    unfold childTotal
    have hval : pulled (iso.toEquiv x) = w₁ x := by
      show w₁ (iso.toEquiv.symm (iso.toEquiv x)) = w₁ x
      rw [Equiv.symm_apply_apply]
    rw [hval]
    congr 1
    have hchildren : (data₂.childList (iso.toEquiv x)).map pulled =
        (data₁.childList x).map w₁ := by
      rw [← iso.map_children x, List.map_map]
      apply List.map_congr_left
      intro c _hc
      show w₁ (iso.toEquiv.symm (iso.toEquiv c)) = w₁ c
      rw [Equiv.symm_apply_apply]
    rw [hchildren]
  have huniq : w₂ = pulled := data₂.weights_unique S₂ w₂ pulled hw₂ hpulled
  intro x
  have hx := congrFun huniq (iso.toEquiv x)
  rw [hx]
  show w₁ x = w₁ (iso.toEquiv.symm (iso.toEquiv x))
  rw [Equiv.symm_apply_apply]

end RootedBranchIso

/-! ## Physical bridge: one boundary edge and incident excess sums -/

open scoped BigOperators

section PhysicalBridge

variable {A : Type*} [Fintype A] [DecidableEq A]
variable {V : Type u}

/-- The incoming atom of a branch vertex: its parent atom, or the deleted cut root at the single
boundary edge of the branch root. -/
def incomingAtom (data : RootedBranch V) (atom : V → A) (cutRoot : A) (v : V) : A :=
  match data.parent v with
  | some p => atom p
  | none => cutRoot

/-- The bond-order excess of the incoming edge: `bond - 1`.  At the root this is the excess of the
single external boundary bond; at every other vertex it is the excess of the parent bond. -/
def incomingExcess (m : MoleculeGraph A) (data : RootedBranch V)
    (atom : V → A) (cutRoot : A) (v : V) : ℕ :=
  m.bond (atom v) (incomingAtom data atom cutRoot v) - 1












structure PhysicalBranchTree (m : MoleculeGraph A) (data : RootedBranch V) where
  /-- The physical atom of a branch vertex. -/
  atom : V → A
  atom_injective : Function.Injective atom
  /-- The deleted atom at the in-edge side of the one boundary bond. -/
  cutRoot : A
  /-- The single boundary bond `cutRoot -- attach`. -/
  rootAdj : m.Adj cutRoot (atom data.root)
  /-- Every tree vertex is a physical atom of the cut branch of `attach` after deleting
  `cutRoot`. -/
  branchMem : ∀ v, atom v ∈ AcyclicCutBranchAutomorphism.CutBranch m cutRoot (atom data.root)
  /-- Branch-internal adjacency is exactly the parent/children relation. -/
  branchAdj : ∀ v u, u ∈ AcyclicCutBranchAutomorphism.CutBranch m cutRoot (atom data.root) →
    (m.Adj (atom v) u ↔
      (∃ c ∈ data.childList v, atom c = u) ∨ (∃ p, data.parent v = some p ∧ atom p = u))

/-- The incoming atom is never the atom of a child: at the root it is the deleted cut root, which
is not in the branch; at a non-root it is the parent atom, and a parent cannot also be a child
because the rank strictly increases along parent edges. -/
theorem incomingAtom_not_mem_children (m : MoleculeGraph A) (data : RootedBranch V)
    (P : PhysicalBranchTree m data) (v : V) :
    incomingAtom data P.atom P.cutRoot v ∉ (data.childList v).map P.atom := by
  intro hmem
  rw [List.mem_map] at hmem
  obtain ⟨c, hc, hEq⟩ := hmem
  have hparent : data.parent c = some v := (data.childList_spec v c).mp hc
  cases hpar : data.parent v with
  | none =>
      have hincoming : incomingAtom data P.atom P.cutRoot v = P.cutRoot := by
        simp [incomingAtom, hpar]
      have hcut : P.atom c = P.cutRoot := hEq.trans hincoming
      have hbranch : P.atom c ∈
          AcyclicCutBranchAutomorphism.CutBranch m P.cutRoot (P.atom data.root) :=
        P.branchMem c
      rw [hcut] at hbranch
      exact AcyclicCutBranchAutomorphism.center_not_mem_cutBranch m P.cutRoot
        (P.atom data.root) hbranch
  | some p =>
      have hincoming : incomingAtom data P.atom P.cutRoot v = P.atom p := by
        simp [incomingAtom, hpar]
      have hcp : c = p := P.atom_injective (hEq.trans hincoming)
      have hpc : data.parent p = some v := by
        rw [← hcp]
        exact hparent
      have hrankP : data.rank p = data.rank v + 1 := data.parent_rank p v hpc
      have hrankV : data.rank v = data.rank p + 1 := data.parent_rank v p hpar
      omega

/-- **Neighbour decomposition at a branch vertex.**  The physical neighbours of a branch atom are
exactly its one incoming atom (the parent atom, or the external cut root at the branch root) and
the atoms of the children in the rooted tree.  The proof uses `cutBranch_incidence` for the single
boundary incidence and `branchAdj` for the internal parent/children split. -/
theorem neighborFinset_eq_insert_children (m : MoleculeGraph A) (data : RootedBranch V)
    (P : PhysicalBranchTree m data) (acyclic : m.Acyclic) (v : V) :
    m.neighborFinset (P.atom v) =
      insert (incomingAtom data P.atom P.cutRoot v)
        ((data.childList v).map P.atom).toFinset := by
  ext u
  rw [MoleculeGraph.mem_neighborFinset, Finset.mem_insert, List.mem_toFinset, List.mem_map]
  constructor
  · intro hadj
    rcases AcyclicCutBranchAutomorphism.cutBranch_incidence m acyclic P.rootAdj
      (P.branchMem v) u hadj with hbranch | ⟨hvRoot, hucut⟩
    · rcases (P.branchAdj v u hbranch).mp hadj with hchild | hparent
      · exact Or.inr hchild
      · obtain ⟨p, hpv, hpu⟩ := hparent
        exact Or.inl (by simp [incomingAtom, hpv, hpu])
    · have hv : v = data.root := P.atom_injective hvRoot
      subst hv
      exact Or.inl (by simp [incomingAtom, data.parent_root, hucut])
  · rintro (hinc | hchild)
    · subst hinc
      cases hpar : data.parent v with
      | none =>
          have hroot : v = data.root := by
            by_contra hne
            obtain ⟨p, hp⟩ := data.exists_parent v hne
            rw [hpar] at hp
            simp at hp
          subst hroot
          have hincoming : incomingAtom data P.atom P.cutRoot data.root = P.cutRoot := by
            simp [incomingAtom, data.parent_root]
          rw [hincoming]
          exact (m.adj_symm).mpr P.rootAdj
      | some p =>
          have hincoming : incomingAtom data P.atom P.cutRoot v = P.atom p := by
            simp [incomingAtom, hpar]
          rw [hincoming]
          exact (P.branchAdj v (P.atom p) (P.branchMem p)).mpr (Or.inr ⟨p, hpar, rfl⟩)
    · obtain ⟨c, hc, hcu⟩ := hchild
      have hbranch : P.atom c ∈
          AcyclicCutBranchAutomorphism.CutBranch m P.cutRoot (P.atom data.root) :=
        P.branchMem c
      rw [← hcu]
      exact (P.branchAdj v (P.atom c) hbranch).mpr (Or.inl ⟨c, hc, rfl⟩)

/-- Sum over a duplicate-free list equals the sum over its `Finset`. -/
theorem list_toFinset_sum {α : Type*} [DecidableEq α] (l : List α) (h : l.Nodup)
    (f : α → ℕ) : (l.toFinset).sum f = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.nodup_cons] at h
      obtain ⟨ha, ht⟩ := h
      rw [List.toFinset_cons, List.map_cons, List.sum_cons, Finset.sum_insert]
      · rw [ih ht]
      · intro hmem
        exact ha (List.mem_toFinset.mp hmem)

/-- **Physical incident excess decomposition.**  The physical excess sum over all neighbours of a
branch atom is its incoming excess plus the sum of the incoming excesses of its children.  Thus the
single boundary edge and all internal parent edges are the complete set of incident excess
contributions. -/
theorem physical_excess_decomposition (m : MoleculeGraph A) (data : RootedBranch V)
    (P : PhysicalBranchTree m data) (acyclic : m.Acyclic) (S : A → ℕ)
    (hS : ∀ v, S (P.atom v) =
      ∑ u ∈ m.neighborFinset (P.atom v), (m.bond (P.atom v) u - 1))
    (v : V) :
    S (P.atom v) = childTotal data.childList (incomingExcess m data P.atom P.cutRoot) v := by
  have hset := neighborFinset_eq_insert_children m data P acyclic v
  have hnotList := incomingAtom_not_mem_children m data P v
  have hnot : incomingAtom data P.atom P.cutRoot v ∉
      ((data.childList v).map P.atom).toFinset := by
    simpa using hnotList
  have hnodup : ((data.childList v).map P.atom).Nodup :=
    List.Nodup.map (f := P.atom) P.atom_injective (data.childList_nodup v)
  calc
    S (P.atom v) = ∑ u ∈ m.neighborFinset (P.atom v), (m.bond (P.atom v) u - 1) := hS v
    _ = ∑ u ∈ insert (incomingAtom data P.atom P.cutRoot v)
          ((data.childList v).map P.atom).toFinset, (m.bond (P.atom v) u - 1) := by
          rw [hset]
    _ = (m.bond (P.atom v) (incomingAtom data P.atom P.cutRoot v) - 1) +
          ∑ u ∈ ((data.childList v).map P.atom).toFinset,
            (m.bond (P.atom v) u - 1) := by
          rw [Finset.sum_insert hnot]
    _ = incomingExcess m data P.atom P.cutRoot v +
          ∑ u ∈ ((data.childList v).map P.atom).toFinset,
            (m.bond (P.atom v) u - 1) := rfl
    _ = incomingExcess m data P.atom P.cutRoot v +
          (((data.childList v).map P.atom).map
            (fun u => m.bond (P.atom v) u - 1)).sum := by
          rw [list_toFinset_sum _ hnodup (fun u => m.bond (P.atom v) u - 1)]
    _ = incomingExcess m data P.atom P.cutRoot v +
          ((data.childList v).map
            (incomingExcess m data P.atom P.cutRoot)).sum := by
          congr 1
          have hmap : ((data.childList v).map P.atom).map
              (fun u => m.bond (P.atom v) u - 1) =
              (data.childList v).map (incomingExcess m data P.atom P.cutRoot) := by
            rw [List.map_map]
            apply List.map_congr_left
            intro c hc
            have hpar : data.parent c = some v := (data.childList_spec v c).mp hc
            have hinc : incomingAtom data P.atom P.cutRoot c = P.atom v := by
              simp [incomingAtom, hpar]
            show m.bond (P.atom v) (P.atom c) - 1 =
              incomingExcess m data P.atom P.cutRoot c
            rw [incomingExcess, hinc, m.bond_symm (P.atom c) (P.atom v)]
          rw [hmap]
    _ = childTotal data.childList (incomingExcess m data P.atom P.cutRoot) v := rfl

/-- **All incoming weights are determined by the physical excess sums.**  Any weight assignment
satisfying the physical excess decomposition equals the physical incoming excesses: every internal
parent-bond excess and the single boundary-bond excess. -/
theorem bond_orders_determined_by_excess_sums (m : MoleculeGraph A) (data : RootedBranch V)
    (P : PhysicalBranchTree m data) (acyclic : m.Acyclic) (S : A → ℕ)
    (hS : ∀ v, S (P.atom v) =
      ∑ u ∈ m.neighborFinset (P.atom v), (m.bond (P.atom v) u - 1))
    (w : V → ℕ)
    (hw : ∀ v, S (P.atom v) = childTotal data.childList w v) :
    w = incomingExcess m data P.atom P.cutRoot :=
  data.weights_unique (fun v => S (P.atom v)) w
    (incomingExcess m data P.atom P.cutRoot) hw
    (fun v => physical_excess_decomposition m data P acyclic S hS v)

/-- **Two weight assignments with the same physical excess sums agree.**  This is the form used
when two independent reconstructions (for example two realized trees of the same molecule) carry
the same per-atom excess data. -/
theorem weights_eq_of_excess_sums (m : MoleculeGraph A) (data : RootedBranch V)
    (P : PhysicalBranchTree m data) (acyclic : m.Acyclic) (S : A → ℕ)
    (hS : ∀ v, S (P.atom v) =
      ∑ u ∈ m.neighborFinset (P.atom v), (m.bond (P.atom v) u - 1))
    (w z : V → ℕ)
    (hw : ∀ v, S (P.atom v) = childTotal data.childList w v)
    (hz : ∀ v, S (P.atom v) = childTotal data.childList z v) :
    w = z := by
  rw [bond_orders_determined_by_excess_sums m data P acyclic S hS w hw,
    bond_orders_determined_by_excess_sums m data P acyclic S hS z hz]

/-- **Internal bond orders are determined.**  For every tree edge, the physical bond order equals
the reconstructed child excess plus one.  Positivity of the actual bond supplies
`bond = (bond - 1) + 1`; no `SimpleBonded` hypothesis is used. -/
theorem internal_bond_eq (m : MoleculeGraph A) (data : RootedBranch V)
    (P : PhysicalBranchTree m data) (acyclic : m.Acyclic) (S : A → ℕ)
    (hS : ∀ v, S (P.atom v) =
      ∑ u ∈ m.neighborFinset (P.atom v), (m.bond (P.atom v) u - 1))
    (w : V → ℕ)
    (hw : ∀ v, S (P.atom v) = childTotal data.childList w v)
    {v c : V} (hc : c ∈ data.childList v) :
    m.bond (P.atom v) (P.atom c) = w c + 1 := by
  have hwc : w c = incomingExcess m data P.atom P.cutRoot c := by
    rw [bond_orders_determined_by_excess_sums m data P acyclic S hS w hw]
  have hpar : data.parent c = some v := (data.childList_spec v c).mp hc
  have hinc : incomingAtom data P.atom P.cutRoot c = P.atom v := by
    simp [incomingAtom, hpar]
  have hadj : m.Adj (P.atom v) (P.atom c) :=
    (P.branchAdj v (P.atom c) (P.branchMem c)).mpr (Or.inl ⟨c, hc, rfl⟩)
  have hpos : 1 ≤ m.bond (P.atom v) (P.atom c) :=
    Nat.succ_le_of_lt hadj
  rw [hwc, incomingExcess, hinc, m.bond_symm (P.atom c) (P.atom v)]
  exact (Nat.sub_add_cancel hpos).symm

/-- **The single boundary bond order is determined.**  The external boundary edge
`cutRoot -- attach` is reconstructed from the root's residual excess plus one. -/
theorem boundary_bond_eq (m : MoleculeGraph A) (data : RootedBranch V)
    (P : PhysicalBranchTree m data) (acyclic : m.Acyclic) (S : A → ℕ)
    (hS : ∀ v, S (P.atom v) =
      ∑ u ∈ m.neighborFinset (P.atom v), (m.bond (P.atom v) u - 1))
    (w : V → ℕ)
    (hw : ∀ v, S (P.atom v) = childTotal data.childList w v) :
    m.bond P.cutRoot (P.atom data.root) = w data.root + 1 := by
  have hwr : w data.root = incomingExcess m data P.atom P.cutRoot data.root := by
    rw [bond_orders_determined_by_excess_sums m data P acyclic S hS w hw]
  have hinc : incomingAtom data P.atom P.cutRoot data.root = P.cutRoot := by
    simp [incomingAtom, data.parent_root]
  have hpos : 1 ≤ m.bond P.cutRoot (P.atom data.root) :=
    Nat.succ_le_of_lt P.rootAdj
  rw [hwr, incomingExcess, hinc, m.bond_symm (P.atom data.root) P.cutRoot]
  exact (Nat.sub_add_cancel hpos).symm

end PhysicalBridge



















section ActualRealPositionBridge

open CertifiedLocalizedCIPInput

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
variable {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
variable {tree : LocalizedCumulativeDecoratedTree input carrierFuel}






structure RealPositionBranchAlignment
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (data : RootedBranch (RealPosition tree))
    (startReal : tree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom) where
  /-- The abstract root is the actual tree root position. -/
  root_eq : data.root = ⟨rootPosition tree, startReal⟩
  /-- The abstract parent of a nonroot real position is its actual parent position. -/
  parent_eq : ∀ (p : RealPosition tree) (ne : p.1.val ≠ []),
    data.parent p = some (realPositionParent realizes p ne)
  /-- The abstract children of a real position are exactly its actual real child positions. -/
  children_iff : ∀ p q : RealPosition tree, q ∈ data.childList p ↔ RealPositionChild p q







noncomputable def physicalBranchTreeOfRealPosition
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (startReal : tree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (previousReal : previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (data : RootedBranch (RealPosition tree))
    (align : RealPositionBranchAlignment realizes data startReal) :
    PhysicalBranchTree input.moleculeGraph data where
  atom := realPositionAtom
  atom_injective := fun p q h => realPosition_injective acyclic enough realizes p q h
  cutRoot := pAtom
  rootAdj := by
    rw [align.root_eq, realPositionAtom_rootPosition startReal oObserved]
    exact incomingEdge
  branchMem := fun p => by
    rw [align.root_eq, realPositionAtom_rootPosition startReal oObserved]
    exact realPositionAtom_mem_cutBranch acyclic enough realizes previous
      previousEq valid startReal previousReal oObserved pObserved incomingEdge p
  branchAdj := by
    intro v u hu
    have hu' : u ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom := by
      rwa [align.root_eq, realPositionAtom_rootPosition startReal oObserved] at hu
    obtain ⟨q, hq⟩ := exists_realPosition_of_mem_cutBranch acyclic enough realizes previous
      previousEq sameRoot valid startReal previousReal oObserved pObserved incomingEdge hu'
    have hiff := realPosition_adjacent_iff_realPositionChild acyclic enough realizes previous
      previousEq sameRoot valid startReal previousReal oObserved pObserved incomingEdge v q
    rw [← hq]
    constructor
    · intro hadj
      rcases hiff.mp hadj with hchild | hparent
      · exact Or.inl ⟨q, (align.children_iff v q).mpr hchild, rfl⟩
      · obtain ⟨slot, hval⟩ := hparent
        have hne : v.1.val ≠ [] := by rw [hval]; simp
        have hparentEq : realPositionParent realizes v hne = q := by
          apply Subtype.ext
          apply position_ext
          show (positionParent v.1 hne).val = q.1.val
          rw [positionParent_val, hval]
          simp
        exact Or.inr ⟨realPositionParent realizes v hne, align.parent_eq v hne,
          by rw [hparentEq]⟩
    · rintro (⟨c, hc, hcu⟩ | ⟨p, hp, hpu⟩)
      · have hchild : RealPositionChild v c := (align.children_iff v c).mp hc
        have hcq : c = q := realPosition_injective acyclic enough realizes c q hcu
        rw [hcq] at hchild
        exact hiff.mpr (Or.inl hchild)
      · have hpq : p = q := realPosition_injective acyclic enough realizes p q hpu
        have hvmem : v ∈ data.childList q := by
          rw [data.childList_spec q v, ← hpq]
          exact hp
        exact hiff.mpr (Or.inr ((align.children_iff q v).mp hvmem))

end ActualRealPositionBridge

end LocalizedMultipleBondOrderReconstruction
end OneCenter
end TetraStereo

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.LocalizedMultipleBondOrderReconstruction.childTotal
assert_kernel_only TetraStereo.OneCenter.LocalizedMultipleBondOrderReconstruction.list_incoming_weights_unique
assert_kernel_only TetraStereo.OneCenter.LocalizedMultipleBondOrderReconstruction.exists_unique_weights
assert_kernel_only TetraStereo.OneCenter.LocalizedMultipleBondOrderReconstruction.RootedBranch
assert_kernel_only TetraStereo.OneCenter.LocalizedMultipleBondOrderReconstruction.RootedBranch.child_rank
assert_kernel_only TetraStereo.OneCenter.LocalizedMultipleBondOrderReconstruction.RootedBranch.weights_unique
assert_kernel_only TetraStereo.OneCenter.LocalizedMultipleBondOrderReconstruction.RootedBranch.exists_unique_weights
assert_kernel_only TetraStereo.OneCenter.LocalizedMultipleBondOrderReconstruction.RootedBranchIso
assert_kernel_only TetraStereo.OneCenter.LocalizedMultipleBondOrderReconstruction.RootedBranchIso.weights_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedMultipleBondOrderReconstruction.incomingAtom
assert_kernel_only TetraStereo.OneCenter.LocalizedMultipleBondOrderReconstruction.incomingExcess
assert_kernel_only TetraStereo.OneCenter.LocalizedMultipleBondOrderReconstruction.PhysicalBranchTree
assert_kernel_only TetraStereo.OneCenter.LocalizedMultipleBondOrderReconstruction.incomingAtom_not_mem_children
assert_kernel_only TetraStereo.OneCenter.LocalizedMultipleBondOrderReconstruction.neighborFinset_eq_insert_children
assert_kernel_only TetraStereo.OneCenter.LocalizedMultipleBondOrderReconstruction.list_toFinset_sum
assert_kernel_only TetraStereo.OneCenter.LocalizedMultipleBondOrderReconstruction.physical_excess_decomposition
assert_kernel_only TetraStereo.OneCenter.LocalizedMultipleBondOrderReconstruction.bond_orders_determined_by_excess_sums
assert_kernel_only TetraStereo.OneCenter.LocalizedMultipleBondOrderReconstruction.weights_eq_of_excess_sums
assert_kernel_only TetraStereo.OneCenter.LocalizedMultipleBondOrderReconstruction.internal_bond_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedMultipleBondOrderReconstruction.boundary_bond_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedMultipleBondOrderReconstruction.RealPositionBranchAlignment
assert_kernel_only TetraStereo.OneCenter.LocalizedMultipleBondOrderReconstruction.physicalBranchTreeOfRealPosition
