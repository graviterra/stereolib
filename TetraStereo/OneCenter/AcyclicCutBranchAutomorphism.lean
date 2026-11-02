import TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
import TetraStereo.OneCenter.MultiCenterDetection
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Global automorphisms from rooted cut-branch isomorphisms

This module is the pure-graph counterpart of a rooted branch symmetry at a tetrahedral center.
It works with a finite `MoleculeGraph` that is acyclic (`MoleculeGraph.Acyclic`) and whose positive
bond orders are all one (`MoleculeGraph.SimpleBonded`), and with two **distinct neighbors `u` and
`v` of the same attachment root `c`**.

Deleting `c` splits the graph into cut components (branches).  We define the branch of a neighbor
`u` as the set of vertices reachable from `u` by a walk whose support avoids `c`
(`CutBranchReaches`).  The main graph-theoretic facts are derived from acyclicity, not supplied as
certificates:

* two distinct neighbor branches at the same root are disjoint
  (`cutBranch_disjoint_of_acyclic`, `cutBranch_no_overlap`);
* every neighbor of a branch vertex is either the root or stays in the branch
  (`cutBranch_adj_mem`), and the only branch vertex adjacent to the root is the attachment vertex
  (`cutBranch_adj_center_iff`);
* there is no edge between two distinct branches (`cutBranch_no_adj_of_acyclic`).

An explicit rooted cut-component isomorphism `φ` between the branches of `u` and `v`
(`RootedCutBranchIso`) is then extended to a global permutation of all atoms by swapping the two
branches through `φ` and `φ.symm` while fixing every vertex outside both branches.  This
permutation

* preserves atom labels `atomZ` and `atomMass` (through `φ`),
* preserves formal charge whenever the formal charge is constant on the molecule,
* preserves every bond order (adjacency is preserved by the construction and `SimpleBonded`
  identifies a bond order with its adjacency),
* fixes the root `c`, and sends `u` to `v` and `v` to `u`.

No connectivity assumption is used: components of the molecule outside the two branches are fixed
pointwise.  The construction is then lifted to the automatically detected multi-center molecule
`MoleculeGraph.detectedMultiCenterMolecule` through
`MoleculeGraph.detectedMultiCenterAutOfGraphAut`; the tetrahedral-center inventory is automatic, so
no degree-four bookkeeping is required.

## Scope and limitations

* Both attachments must lie at the **same** root `c`.  Isomorphic cut components rooted at
  unrelated attachment roots do **not** in general extend to an automorphism of the molecule:
  transport would also have to identify the two distinct roots and their incident edges.  Nothing
  in this module asserts otherwise.
* No stereochemical `Configuration` is used: this is a pure constitutional graph statement.
* `IsAutomorphism` preserves `atomZ`, `atomMass`, `formalCharge` and bond orders.  The branch
  isomorphism is required to preserve `atomZ`, `atomMass` and adjacency; constant formal charge is a
  genuine hypothesis of the extension theorem (a non-constant charge function would have to be
  respected by `φ` as well).
* The final corollary (`no_rootedCutBranchIso_of_pointwise_fixed`) is the graph-level input for
  constitutional rigidity: if every graph automorphism fixing `c` fixes all neighbors of `c`, then
  no distinct rooted cut-branch isomorphism at `c` can exist.
-/

namespace TetraStereo
namespace OneCenter
namespace AcyclicCutBranchAutomorphism

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Cut components after deleting a root -/

/-- `CutBranchReaches m c u x` holds when `x` can be reached from `u` by a walk of the underlying
simple graph whose support avoids the deleted root `c`.  When `u` is a neighbor of `c`, this is the
connected component of `u` in the graph with `c` removed. -/
def CutBranchReaches (m : MoleculeGraph V) (c u x : V) : Prop :=
  ∃ p : m.underlyingSimpleGraph.Walk u x, c ∉ p.support

/-- The cut component (branch) of `u` after deleting the root `c`. -/
def CutBranch (m : MoleculeGraph V) (c u : V) : Set V :=
  {x | CutBranchReaches m c u x}

/-- The attachment vertex belongs to its own cut branch. -/
theorem cutBranch_mem_self (m : MoleculeGraph V) {c u : V} (hcu : m.Adj c u) :
    u ∈ CutBranch m c u := by
  refine ⟨SimpleGraph.Walk.nil, ?_⟩
  simp only [SimpleGraph.Walk.support_nil, List.mem_singleton]
  intro hcu_eq
  rw [hcu_eq] at hcu
  have hzero : m.bond u u = 0 := m.bond_self u
  simp [MoleculeGraph.Adj, hzero] at hcu

/-- The deleted root is in no branch. -/
theorem center_not_mem_cutBranch (m : MoleculeGraph V) (c u : V) :
    c ∉ CutBranch m c u := by
  rintro ⟨p, hp⟩
  exact hp (SimpleGraph.Walk.end_mem_support p)

/-- A vertex of a cut branch is not the deleted root. -/
theorem cutBranch_ne_center (m : MoleculeGraph V) {c u x : V}
    (hx : x ∈ CutBranch m c u) : x ≠ c := by
  intro hxc
  rw [hxc] at hx
  exact center_not_mem_cutBranch m c u hx

/-- Cut-branch reachability is transitive. -/
theorem cutBranchReaches_trans (m : MoleculeGraph V) {c u x y : V}
    (hx : CutBranchReaches m c u x) (hy : CutBranchReaches m c x y) :
    CutBranchReaches m c u y := by
  obtain ⟨p, hp⟩ := hx
  obtain ⟨q, hq⟩ := hy
  refine ⟨p.append q, ?_⟩
  rw [SimpleGraph.Walk.support_append]
  intro hmem
  rw [List.mem_append] at hmem
  rcases hmem with h | h
  · exact hp h
  · exact hq (List.mem_of_mem_tail h)

/-- Every neighbor of a branch vertex other than the deleted root stays in the same branch. -/
theorem cutBranch_adj_mem (m : MoleculeGraph V) {c u x y : V}
    (hx : x ∈ CutBranch m c u) (hxy : m.Adj x y) (hyc : y ≠ c) :
    y ∈ CutBranch m c u := by
  obtain ⟨p, hp⟩ := hx
  refine ⟨p.concat ?_, ?_⟩
  · simpa using hxy
  · rw [SimpleGraph.Walk.support_concat]
    intro hmem
    simp only [List.concat_eq_append, List.mem_append, List.mem_singleton] at hmem
    rcases hmem with h | h
    · exact hp h
    · exact hyc h.symm

/-! ### Acyclicity consequences -/

/-- **Distinct neighbor branches at the same root are disjoint.**  Two walks from distinct
neighbors `u` and `v` of `c` to the same vertex, both avoiding `c`, prepend to two paths from `c`;
acyclicity forces these paths to coincide, hence forces `u = v`. -/
theorem cutBranch_disjoint_of_acyclic (m : MoleculeGraph V) (h : m.Acyclic)
    {c u v x : V} (hcu : m.Adj c u) (hcv : m.Adj c v)
    (hxU : x ∈ CutBranch m c u) (hxV : x ∈ CutBranch m c v) :
    u = v := by
  obtain ⟨pu, hpu⟩ := hxU
  obtain ⟨pv, hpv⟩ := hxV
  let G := m.underlyingSimpleGraph
  have hG : G.IsAcyclic := h
  let qu : G.Path u x := pu.toPath
  let qv : G.Path v x := pv.toPath
  have hquAvoid : c ∉ (qu : G.Walk u x).support :=
    fun hc => hpu (SimpleGraph.Walk.support_toPath_subset pu hc)
  have hqvAvoid : c ∉ (qv : G.Walk v x).support :=
    fun hc => hpv (SimpleGraph.Walk.support_toPath_subset pv hc)
  let wu : G.Walk c x := SimpleGraph.Walk.cons (show G.Adj c u from hcu) (qu : G.Walk u x)
  let wv : G.Walk c x := SimpleGraph.Walk.cons (show G.Adj c v from hcv) (qv : G.Walk v x)
  have hwu : wu.IsPath :=
    (SimpleGraph.Walk.cons_isPath_iff (show G.Adj c u from hcu) (qu : G.Walk u x)).2
      ⟨qu.2, hquAvoid⟩
  have hwv : wv.IsPath :=
    (SimpleGraph.Walk.cons_isPath_iff (show G.Adj c v from hcv) (qv : G.Walk v x)).2
      ⟨qv.2, hqvAvoid⟩
  have hEq : (⟨wu, hwu⟩ : G.Path c x) = ⟨wv, hwv⟩ := hG.path_unique _ _
  have hwalk : wu = wv := congrArg (fun P : G.Path c x => (P : G.Walk c x)) hEq
  have h1 : wu.getVert 1 = wv.getVert 1 :=
    congrArg (fun w : G.Walk c x => w.getVert 1) hwalk
  have hu1 : wu.getVert 1 = u := by simp [wu]
  have hv1 : wv.getVert 1 = v := by simp [wv]
  rw [hu1, hv1] at h1
  exact h1

/-- Pairwise-disjointness form of `cutBranch_disjoint_of_acyclic`. -/
theorem cutBranch_no_overlap (m : MoleculeGraph V) (h : m.Acyclic)
    {c u v : V} (hcu : m.Adj c u) (hcv : m.Adj c v) (huv : u ≠ v) :
    ∀ x, x ∈ CutBranch m c u → x ∈ CutBranch m c v → False :=
  fun _ hxU hxV => huv (cutBranch_disjoint_of_acyclic m h hcu hcv hxU hxV)

/-- **The only branch vertex adjacent to the root is the attachment vertex.**  If `x` lies in the
branch of `u` and is adjacent to `c`, then `x = u`: otherwise the path `c-u-...-x` and the single
edge `c-x` would be two distinct simple paths between `c` and `x`. -/
theorem cutBranch_adj_center_iff (m : MoleculeGraph V) (h : m.Acyclic) {c u x : V}
    (hcu : m.Adj c u) (hx : x ∈ CutBranch m c u) :
    m.Adj x c ↔ x = u := by
  constructor
  · intro hxc
    obtain ⟨p, hp⟩ := hx
    let G := m.underlyingSimpleGraph
    have hG : G.IsAcyclic := h
    let q : G.Path u x := p.toPath
    have hqAvoid : c ∉ (q : G.Walk u x).support :=
      fun hc => hp (SimpleGraph.Walk.support_toPath_subset p hc)
    have hxne : x ≠ c := cutBranch_ne_center m ⟨p, hp⟩
    let w : G.Walk c x := SimpleGraph.Walk.cons (show G.Adj c u from hcu) (q : G.Walk u x)
    have hw : w.IsPath :=
      (SimpleGraph.Walk.cons_isPath_iff (show G.Adj c u from hcu) (q : G.Walk u x)).2
        ⟨q.2, hqAvoid⟩
    have hcx : G.Adj c x := m.adj_symm.mp hxc
    let s : G.Walk c x := SimpleGraph.Walk.cons hcx SimpleGraph.Walk.nil
    have hs : s.IsPath := by
      have hnil : (SimpleGraph.Walk.nil : G.Walk x x).IsPath :=
        SimpleGraph.Walk.IsPath.nil
      have hnotmem : c ∉ (SimpleGraph.Walk.nil : G.Walk x x).support := by
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton]
        exact fun hcx' => hxne hcx'.symm
      exact (SimpleGraph.Walk.cons_isPath_iff hcx SimpleGraph.Walk.nil).2 ⟨hnil, hnotmem⟩
    have hEq : (⟨w, hw⟩ : G.Path c x) = ⟨s, hs⟩ := hG.path_unique _ _
    have hwalk : w = s := congrArg (fun P : G.Path c x => (P : G.Walk c x)) hEq
    have h1 : w.getVert 1 = s.getVert 1 :=
      congrArg (fun u : G.Walk c x => u.getVert 1) hwalk
    have hw1 : w.getVert 1 = u := by simp [w]
    have hs1 : s.getVert 1 = x := by simp [s]
    rw [hw1, hs1] at h1
    exact h1.symm
  · intro hxu
    subst hxu
    exact m.adj_symm.mpr hcu

/-- **All outside incidence of a branch passes through the root, and only at the attachment
vertex.**  A neighbor of a branch vertex is either in the branch or is the root; in the latter case
the branch vertex must be the attachment vertex. -/
theorem cutBranch_incidence (m : MoleculeGraph V) (h : m.Acyclic) {c u x : V}
    (hcu : m.Adj c u) (hx : x ∈ CutBranch m c u) (y : V) (hxy : m.Adj x y) :
    y ∈ CutBranch m c u ∨ (x = u ∧ y = c) := by
  by_cases hyc : y = c
  · right
    refine ⟨?_, hyc⟩
    exact (cutBranch_adj_center_iff m h hcu hx).1 (by rwa [hyc] at hxy)
  · left
    exact cutBranch_adj_mem m hx hxy hyc

/-- There is no edge between the cut branches of two distinct neighbors of the same root. -/
theorem cutBranch_no_adj_of_acyclic (m : MoleculeGraph V) (h : m.Acyclic)
    {c u v : V} (hcu : m.Adj c u) (hcv : m.Adj c v) (huv : u ≠ v)
    {x y : V} (hx : x ∈ CutBranch m c u) (hy : y ∈ CutBranch m c v) :
    ¬ m.Adj x y := by
  intro hxy
  have hyc : y ≠ c := cutBranch_ne_center m hy
  have hyU : y ∈ CutBranch m c u := cutBranch_adj_mem m hx hxy hyc
  exact cutBranch_no_overlap m h hcu hcv huv y hyU hy

/-! ### Constant formal charge -/

/-- A molecule has constant formal charge when one integer is the formal charge of every atom. -/
def ConstantFormalCharge (m : MoleculeGraph V) : Prop :=
  ∃ q : ℤ, ∀ x, m.formalCharge x = q

/-! ### Rooted cut-branch isomorphisms -/

/-- An explicit isomorphism between the cut components of two neighbors `u` and `v` of the same
root `c`.  It preserves atomic number, mass number, and adjacency, and sends the attachment vertex
`u` to the attachment vertex `v`. -/
structure RootedCutBranchIso (m : MoleculeGraph V) (c u v : V) where
  /-- The underlying equivalence of cut branches. -/
  toEquiv : CutBranch m c u ≃ CutBranch m c v
  /-- The attachment vertices correspond. -/
  map_attach : ∀ (hu : u ∈ CutBranch m c u) (hv : v ∈ CutBranch m c v),
    toEquiv ⟨u, hu⟩ = ⟨v, hv⟩
  /-- Atomic numbers are preserved. -/
  atomZ_eq : ∀ x : CutBranch m c u, m.atomZ (toEquiv x : V) = m.atomZ (x : V)
  /-- Mass numbers are preserved. -/
  atomMass_eq : ∀ x : CutBranch m c u, m.atomMass (toEquiv x : V) = m.atomMass (x : V)
  /-- Adjacency within the branch is preserved (equivalently, bond incidence after deleting the
  root and its attachment edges). -/
  adj_iff : ∀ x y : CutBranch m c u,
    m.Adj (toEquiv x : V) (toEquiv y : V) ↔ m.Adj (x : V) (y : V)

/-- Adjacency preservation read backwards through the inverse branch equivalence. -/
theorem RootedCutBranchIso.adj_iff_symm {m : MoleculeGraph V} {c u v : V}
    (φ : RootedCutBranchIso m c u v) (x y : CutBranch m c v) :
    m.Adj ((φ.toEquiv.symm x : CutBranch m c u) : V)
        ((φ.toEquiv.symm y : CutBranch m c u) : V) ↔ m.Adj (x : V) (y : V) := by
  have h := φ.adj_iff (φ.toEquiv.symm x) (φ.toEquiv.symm y)
  simpa using h.symm

/-! ### The global swap of two cut branches -/

/-- The raw swap function: branch `u` is carried to branch `v` through `φ`, branch `v` is carried
back through `φ.symm`, and every other vertex is fixed.  The two branch tests are deliberately
ordered; on disjoint branches the result is an involution. -/
noncomputable def cutBranchSwapFun (m : MoleculeGraph V) (c u v : V)
    (φ : RootedCutBranchIso m c u v) (x : V) : V := by
  classical
  exact if hx : x ∈ CutBranch m c u then (φ.toEquiv ⟨x, hx⟩ : V)
    else if hx' : x ∈ CutBranch m c v then
      ((φ.toEquiv.symm ⟨x, hx'⟩ : CutBranch m c u) : V)
    else x

theorem cutBranchSwapFun_of_mem_left (m : MoleculeGraph V) (c u v : V)
    (φ : RootedCutBranchIso m c u v) {x : V} (hx : x ∈ CutBranch m c u) :
    cutBranchSwapFun m c u v φ x = (φ.toEquiv ⟨x, hx⟩ : V) := by
  classical
  rw [cutBranchSwapFun, dif_pos hx]

theorem cutBranchSwapFun_of_mem_right (m : MoleculeGraph V) (c u v : V)
    (φ : RootedCutBranchIso m c u v) {x : V} (hx : x ∈ CutBranch m c v)
    (hxU : x ∉ CutBranch m c u) :
    cutBranchSwapFun m c u v φ x =
      ((φ.toEquiv.symm ⟨x, hx⟩ : CutBranch m c u) : V) := by
  classical
  rw [cutBranchSwapFun, dif_neg hxU, dif_pos hx]

theorem cutBranchSwapFun_of_not_mem (m : MoleculeGraph V) (c u v : V)
    (φ : RootedCutBranchIso m c u v) {x : V}
    (hxU : x ∉ CutBranch m c u) (hxV : x ∉ CutBranch m c v) :
    cutBranchSwapFun m c u v φ x = x := by
  classical
  rw [cutBranchSwapFun, dif_neg hxU, dif_neg hxV]

/-- On disjoint branches the raw swap is an involution. -/
theorem cutBranchSwapFun_involutive (m : MoleculeGraph V) (c u v : V)
    (φ : RootedCutBranchIso m c u v)
    (hdisj : ∀ x, x ∈ CutBranch m c u → x ∈ CutBranch m c v → False) :
    Function.Involutive (cutBranchSwapFun m c u v φ) := by
  intro x
  by_cases hxU : x ∈ CutBranch m c u
  · have hφV : ((φ.toEquiv ⟨x, hxU⟩ : CutBranch m c v) : V) ∈ CutBranch m c v :=
      (φ.toEquiv ⟨x, hxU⟩).2
    have hφnotU : ((φ.toEquiv ⟨x, hxU⟩ : CutBranch m c v) : V) ∉ CutBranch m c u :=
      fun h => hdisj _ h hφV
    rw [cutBranchSwapFun_of_mem_left m c u v φ hxU]
    rw [cutBranchSwapFun_of_mem_right m c u v φ hφV hφnotU]
    have hsub : (⟨((φ.toEquiv ⟨x, hxU⟩ : CutBranch m c v) : V), hφV⟩ : CutBranch m c v)
        = φ.toEquiv ⟨x, hxU⟩ := Subtype.ext rfl
    rw [hsub, Equiv.symm_apply_apply]
  · by_cases hxV : x ∈ CutBranch m c v
    · have hψU : ((φ.toEquiv.symm ⟨x, hxV⟩ : CutBranch m c u) : V) ∈ CutBranch m c u :=
        (φ.toEquiv.symm ⟨x, hxV⟩).2
      have hψnotV : ((φ.toEquiv.symm ⟨x, hxV⟩ : CutBranch m c u) : V) ∉ CutBranch m c v :=
        fun h => hdisj _ hψU h
      rw [cutBranchSwapFun_of_mem_right m c u v φ hxV hxU]
      rw [cutBranchSwapFun_of_mem_left m c u v φ hψU]
      have hsub : (⟨((φ.toEquiv.symm ⟨x, hxV⟩ : CutBranch m c u) : V), hψU⟩ :
          CutBranch m c u) = φ.toEquiv.symm ⟨x, hxV⟩ := Subtype.ext rfl
      rw [hsub, Equiv.apply_symm_apply]
    · rw [cutBranchSwapFun_of_not_mem m c u v φ hxU hxV,
        cutBranchSwapFun_of_not_mem m c u v φ hxU hxV]

/-- The global permutation obtained by swapping the two cut branches through `φ` and its inverse.
The disjointness of the branches is derived from acyclicity. -/
noncomputable def cutBranchSwap (m : MoleculeGraph V) (c u v : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hcv : m.Adj c v) (huv : u ≠ v)
    (φ : RootedCutBranchIso m c u v) : Equiv.Perm V :=
  Function.Involutive.toPerm (cutBranchSwapFun m c u v φ)
    (cutBranchSwapFun_involutive m c u v φ (cutBranch_no_overlap m hacyc hcu hcv huv))

@[simp] theorem cutBranchSwap_apply (m : MoleculeGraph V) (c u v : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hcv : m.Adj c v) (huv : u ≠ v)
    (φ : RootedCutBranchIso m c u v) (x : V) :
    cutBranchSwap m c u v hacyc hcu hcv huv φ x = cutBranchSwapFun m c u v φ x := rfl

/-! ### Basic behaviour of the global swap -/

theorem cutBranchSwap_mem_left (m : MoleculeGraph V) (c u v : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hcv : m.Adj c v) (huv : u ≠ v)
    (φ : RootedCutBranchIso m c u v) {x : V} (hx : x ∈ CutBranch m c u) :
    cutBranchSwap m c u v hacyc hcu hcv huv φ x ∈ CutBranch m c v := by
  rw [cutBranchSwap_apply, cutBranchSwapFun_of_mem_left m c u v φ hx]
  exact (φ.toEquiv ⟨x, hx⟩).2

theorem cutBranchSwap_mem_right (m : MoleculeGraph V) (c u v : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hcv : m.Adj c v) (huv : u ≠ v)
    (φ : RootedCutBranchIso m c u v) {x : V} (hx : x ∈ CutBranch m c v) :
    cutBranchSwap m c u v hacyc hcu hcv huv φ x ∈ CutBranch m c u := by
  have hdisj : ∀ z, z ∈ CutBranch m c u → z ∈ CutBranch m c v → False :=
    cutBranch_no_overlap m hacyc hcu hcv huv
  have hxU : x ∉ CutBranch m c u := fun h => hdisj x h hx
  rw [cutBranchSwap_apply, cutBranchSwapFun_of_mem_right m c u v φ hx hxU]
  exact (φ.toEquiv.symm ⟨x, hx⟩).2

/-- The swap fixes the attachment root. -/
theorem cutBranchSwap_apply_center (m : MoleculeGraph V) (c u v : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hcv : m.Adj c v) (huv : u ≠ v)
    (φ : RootedCutBranchIso m c u v) :
    cutBranchSwap m c u v hacyc hcu hcv huv φ c = c := by
  rw [cutBranchSwap_apply,
    cutBranchSwapFun_of_not_mem m c u v φ (center_not_mem_cutBranch m c u)
      (center_not_mem_cutBranch m c v)]

/-- The swap sends the attachment vertex `u` to the attachment vertex `v`. -/
theorem cutBranchSwap_apply_left (m : MoleculeGraph V) (c u v : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hcv : m.Adj c v) (huv : u ≠ v)
    (φ : RootedCutBranchIso m c u v) :
    cutBranchSwap m c u v hacyc hcu hcv huv φ u = v := by
  rw [cutBranchSwap_apply, cutBranchSwapFun_of_mem_left m c u v φ (cutBranch_mem_self m hcu)]
  simpa using congrArg (fun s : CutBranch m c v => (s : V))
    (φ.map_attach (cutBranch_mem_self m hcu) (cutBranch_mem_self m hcv))

/-- The swap sends the attachment vertex `v` to the attachment vertex `u`. -/
theorem cutBranchSwap_apply_right (m : MoleculeGraph V) (c u v : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hcv : m.Adj c v) (huv : u ≠ v)
    (φ : RootedCutBranchIso m c u v) :
    cutBranchSwap m c u v hacyc hcu hcv huv φ v = u := by
  have hdisj : ∀ z, z ∈ CutBranch m c u → z ∈ CutBranch m c v → False :=
    cutBranch_no_overlap m hacyc hcu hcv huv
  have hvU : v ∉ CutBranch m c u :=
    fun h => hdisj v h (cutBranch_mem_self m hcv)
  rw [cutBranchSwap_apply, cutBranchSwapFun_of_mem_right m c u v φ
    (cutBranch_mem_self m hcv) hvU]
  have hu := φ.map_attach (cutBranch_mem_self m hcu) (cutBranch_mem_self m hcv)
  have hs : φ.toEquiv.symm (⟨v, cutBranch_mem_self m hcv⟩ : CutBranch m c v)
      = (⟨u, cutBranch_mem_self m hcu⟩ : CutBranch m c u) := by
    rw [← hu, Equiv.symm_apply_apply]
  simpa using congrArg (fun s : CutBranch m c u => (s : V)) hs

/-! ### Label preservation of the raw swap -/

theorem cutBranchSwapFun_atomZ (m : MoleculeGraph V) (c u v : V)
    (φ : RootedCutBranchIso m c u v) (x : V) :
    m.atomZ (cutBranchSwapFun m c u v φ x) = m.atomZ x := by
  classical
  by_cases hxU : x ∈ CutBranch m c u
  · rw [cutBranchSwapFun_of_mem_left m c u v φ hxU]
    exact φ.atomZ_eq ⟨x, hxU⟩
  · by_cases hxV : x ∈ CutBranch m c v
    · rw [cutBranchSwapFun_of_mem_right m c u v φ hxV hxU]
      have h := φ.atomZ_eq (φ.toEquiv.symm ⟨x, hxV⟩)
      rw [show φ.toEquiv (φ.toEquiv.symm ⟨x, hxV⟩) = ⟨x, hxV⟩ from
        Equiv.apply_symm_apply _ _] at h
      exact h.symm
    · rw [cutBranchSwapFun_of_not_mem m c u v φ hxU hxV]

theorem cutBranchSwapFun_atomMass (m : MoleculeGraph V) (c u v : V)
    (φ : RootedCutBranchIso m c u v) (x : V) :
    m.atomMass (cutBranchSwapFun m c u v φ x) = m.atomMass x := by
  classical
  by_cases hxU : x ∈ CutBranch m c u
  · rw [cutBranchSwapFun_of_mem_left m c u v φ hxU]
    exact φ.atomMass_eq ⟨x, hxU⟩
  · by_cases hxV : x ∈ CutBranch m c v
    · rw [cutBranchSwapFun_of_mem_right m c u v φ hxV hxU]
      have h := φ.atomMass_eq (φ.toEquiv.symm ⟨x, hxV⟩)
      rw [show φ.toEquiv (φ.toEquiv.symm ⟨x, hxV⟩) = ⟨x, hxV⟩ from
        Equiv.apply_symm_apply _ _] at h
      exact h.symm
    · rw [cutBranchSwapFun_of_not_mem m c u v φ hxU hxV]

/-! ### Adjacency preservation -/

theorem cutBranchSwapFun_mem_left (m : MoleculeGraph V) (c u v : V)
    (φ : RootedCutBranchIso m c u v) {x : V} (hx : x ∈ CutBranch m c u) :
    cutBranchSwapFun m c u v φ x ∈ CutBranch m c v := by
  rw [cutBranchSwapFun_of_mem_left m c u v φ hx]
  exact (φ.toEquiv ⟨x, hx⟩).2

theorem cutBranchSwapFun_mem_right (m : MoleculeGraph V) (c u v : V)
    (φ : RootedCutBranchIso m c u v)
    (hdisj : ∀ z, z ∈ CutBranch m c u → z ∈ CutBranch m c v → False)
    {x : V} (hx : x ∈ CutBranch m c v) :
    cutBranchSwapFun m c u v φ x ∈ CutBranch m c u := by
  have hxU : x ∉ CutBranch m c u := fun h => hdisj x h hx
  rw [cutBranchSwapFun_of_mem_right m c u v φ hx hxU]
  exact (φ.toEquiv.symm ⟨x, hx⟩).2

theorem cutBranchSwapFun_not_mem_left (m : MoleculeGraph V) (c u v : V)
    (φ : RootedCutBranchIso m c u v)
    (hdisj : ∀ z, z ∈ CutBranch m c u → z ∈ CutBranch m c v → False)
    {x : V} (hx : x ∈ CutBranch m c u) :
    cutBranchSwapFun m c u v φ x ∉ CutBranch m c u :=
  fun h => hdisj _ h (cutBranchSwapFun_mem_left m c u v φ hx)

theorem cutBranchSwapFun_not_mem_right (m : MoleculeGraph V) (c u v : V)
    (φ : RootedCutBranchIso m c u v)
    (hdisj : ∀ z, z ∈ CutBranch m c u → z ∈ CutBranch m c v → False)
    {x : V} (hx : x ∈ CutBranch m c v) :
    cutBranchSwapFun m c u v φ x ∉ CutBranch m c v :=
  fun h => hdisj _ (cutBranchSwapFun_mem_right m c u v φ hdisj hx) h

/-- Inside the `u`-branch, the swap is exactly `φ`; consequently it equals `v` only at `u`. -/
theorem cutBranchSwapFun_eq_right_iff (m : MoleculeGraph V) (c u v : V)
    (hcu : m.Adj c u) (hcv : m.Adj c v)
    (φ : RootedCutBranchIso m c u v) {x : V} (hx : x ∈ CutBranch m c u) :
    cutBranchSwapFun m c u v φ x = v ↔ x = u := by
  rw [cutBranchSwapFun_of_mem_left m c u v φ hx]
  constructor
  · intro hval
    have hs : (φ.toEquiv ⟨x, hx⟩) = ⟨v, cutBranch_mem_self m hcv⟩ := Subtype.ext hval
    have hu : (φ.toEquiv ⟨u, cutBranch_mem_self m hcu⟩) =
        ⟨v, cutBranch_mem_self m hcv⟩ :=
      φ.map_attach (cutBranch_mem_self m hcu) (cutBranch_mem_self m hcv)
    have hinj : (⟨x, hx⟩ : CutBranch m c u) = ⟨u, cutBranch_mem_self m hcu⟩ :=
      φ.toEquiv.injective (hs.trans hu.symm)
    exact congrArg Subtype.val hinj
  · intro hxu
    subst hxu
    rw [φ.map_attach hx (cutBranch_mem_self m hcv)]

/-- Inside the `v`-branch, the swap is exactly `φ.symm`; consequently it equals `u` only at `v`. -/
theorem cutBranchSwapFun_eq_left_iff (m : MoleculeGraph V) (c u v : V)
    (hcu : m.Adj c u) (hcv : m.Adj c v)
    (φ : RootedCutBranchIso m c u v)
    (hdisj : ∀ z, z ∈ CutBranch m c u → z ∈ CutBranch m c v → False)
    {x : V} (hx : x ∈ CutBranch m c v) :
    cutBranchSwapFun m c u v φ x = u ↔ x = v := by
  have hxU : x ∉ CutBranch m c u := fun h => hdisj x h hx
  rw [cutBranchSwapFun_of_mem_right m c u v φ hx hxU]
  constructor
  · intro hval
    have hs : φ.toEquiv.symm ⟨x, hx⟩ = ⟨u, cutBranch_mem_self m hcu⟩ := Subtype.ext hval
    have hu : φ.toEquiv ⟨u, cutBranch_mem_self m hcu⟩ = ⟨v, cutBranch_mem_self m hcv⟩ :=
      φ.map_attach (cutBranch_mem_self m hcu) (cutBranch_mem_self m hcv)
    have hxsub : (⟨x, hx⟩ : CutBranch m c v) = ⟨v, cutBranch_mem_self m hcv⟩ := by
      have h := congrArg φ.toEquiv hs
      rw [Equiv.apply_symm_apply, hu] at h
      exact h
    exact congrArg Subtype.val hxsub
  · intro hxv
    have hs : φ.toEquiv.symm (⟨x, hx⟩ : CutBranch m c v) =
        ⟨u, cutBranch_mem_self m hcu⟩ := by
      refine (Equiv.symm_apply_eq φ.toEquiv).2 ?_
      rw [φ.map_attach (cutBranch_mem_self m hcu) (cutBranch_mem_self m hcv)]
      exact Subtype.ext hxv
    rw [hs]

/-- Adjacency preservation for an arbitrary `y`, when `x` lies in the `u`-branch. -/
theorem cutBranchSwapFun_adj_iff_of_mem_left (m : MoleculeGraph V) (c u v : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hcv : m.Adj c v) (huv : u ≠ v)
    (φ : RootedCutBranchIso m c u v)
    (hdisj : ∀ z, z ∈ CutBranch m c u → z ∈ CutBranch m c v → False)
    {x : V} (hx : x ∈ CutBranch m c u) (y : V) :
    m.Adj (cutBranchSwapFun m c u v φ x) (cutBranchSwapFun m c u v φ y) ↔ m.Adj x y := by
  by_cases hyU : y ∈ CutBranch m c u
  · rw [cutBranchSwapFun_of_mem_left m c u v φ hx,
      cutBranchSwapFun_of_mem_left m c u v φ hyU]
    exact φ.adj_iff ⟨x, hx⟩ ⟨y, hyU⟩
  · by_cases hyV : y ∈ CutBranch m c v
    · have hno : ¬ m.Adj x y :=
        cutBranch_no_adj_of_acyclic m hacyc hcu hcv huv hx hyV
      have hFxV : cutBranchSwapFun m c u v φ x ∈ CutBranch m c v :=
        cutBranchSwapFun_mem_left m c u v φ hx
      have hFyU : cutBranchSwapFun m c u v φ y ∈ CutBranch m c u :=
        cutBranchSwapFun_mem_right m c u v φ hdisj hyV
      have hno' : ¬ m.Adj (cutBranchSwapFun m c u v φ x)
          (cutBranchSwapFun m c u v φ y) :=
        fun h => cutBranch_no_adj_of_acyclic m hacyc hcu hcv huv hFyU hFxV (m.adj_symm.mp h)
      exact iff_of_false hno' hno
    · have hFy : cutBranchSwapFun m c u v φ y = y :=
        cutBranchSwapFun_of_not_mem m c u v φ hyU hyV
      by_cases hyc : y = c
      · rw [hyc] at hFy ⊢
        rw [hFy]
        have hFxV : cutBranchSwapFun m c u v φ x ∈ CutBranch m c v :=
          cutBranchSwapFun_mem_left m c u v φ hx
        exact (cutBranch_adj_center_iff m hacyc hcv hFxV).trans
          ((cutBranchSwapFun_eq_right_iff m c u v hcu hcv φ hx).trans
            (cutBranch_adj_center_iff m hacyc hcu hx).symm)
      · have hno : ¬ m.Adj x y :=
          fun h => hyU (cutBranch_adj_mem m hx h hyc)
        have hno' : ¬ m.Adj (cutBranchSwapFun m c u v φ x)
            (cutBranchSwapFun m c u v φ y) := by
          rw [hFy]
          exact fun h => hyV
            (cutBranch_adj_mem m (cutBranchSwapFun_mem_left m c u v φ hx) h hyc)
        exact iff_of_false hno' hno

/-- Adjacency preservation for an arbitrary `y`, when `x` lies in the `v`-branch.  This is the
previous statement transported backwards along the involutive swap. -/
theorem cutBranchSwapFun_adj_iff_of_mem_right (m : MoleculeGraph V) (c u v : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hcv : m.Adj c v) (huv : u ≠ v)
    (φ : RootedCutBranchIso m c u v)
    (hdisj : ∀ z, z ∈ CutBranch m c u → z ∈ CutBranch m c v → False)
    {x : V} (hx : x ∈ CutBranch m c v) (y : V) :
    m.Adj (cutBranchSwapFun m c u v φ x) (cutBranchSwapFun m c u v φ y) ↔ m.Adj x y := by
  have hxU : cutBranchSwapFun m c u v φ x ∈ CutBranch m c u :=
    cutBranchSwapFun_mem_right m c u v φ hdisj hx
  have h := cutBranchSwapFun_adj_iff_of_mem_left m c u v hacyc hcu hcv huv φ hdisj hxU
    (y := cutBranchSwapFun m c u v φ y)
  have hinv := cutBranchSwapFun_involutive m c u v φ hdisj
  simpa [hinv x, hinv y] using h.symm

/-- **The global swap preserves adjacency everywhere.**  The proof splits on the branch membership
of the two vertices; the structural lemmas above show that all cross and outside cases are
non-adjacent on both sides. -/
theorem cutBranchSwapFun_adj_iff (m : MoleculeGraph V) (c u v : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hcv : m.Adj c v) (huv : u ≠ v)
    (φ : RootedCutBranchIso m c u v)
    (hdisj : ∀ z, z ∈ CutBranch m c u → z ∈ CutBranch m c v → False)
    (x y : V) :
    m.Adj (cutBranchSwapFun m c u v φ x) (cutBranchSwapFun m c u v φ y) ↔ m.Adj x y := by
  by_cases hxU : x ∈ CutBranch m c u
  · exact cutBranchSwapFun_adj_iff_of_mem_left m c u v hacyc hcu hcv huv φ hdisj hxU y
  · by_cases hxV : x ∈ CutBranch m c v
    · exact cutBranchSwapFun_adj_iff_of_mem_right m c u v hacyc hcu hcv huv φ hdisj hxV y
    · have hFx : cutBranchSwapFun m c u v φ x = x :=
        cutBranchSwapFun_of_not_mem m c u v φ hxU hxV
      by_cases hyU : y ∈ CutBranch m c u
      · have h := cutBranchSwapFun_adj_iff_of_mem_left m c u v hacyc hcu hcv huv φ hdisj
          hyU (y := x)
        rw [hFx] at h
        have hsym1 : m.Adj x (cutBranchSwapFun m c u v φ y) ↔
            m.Adj (cutBranchSwapFun m c u v φ y) x := m.adj_symm
        have hsym2 : m.Adj y x ↔ m.Adj x y := m.adj_symm
        rw [hFx]
        exact hsym1.trans (h.trans hsym2)
      · by_cases hyV : y ∈ CutBranch m c v
        · have h := cutBranchSwapFun_adj_iff_of_mem_right m c u v hacyc hcu hcv huv φ hdisj
            hyV (y := x)
          rw [hFx] at h
          have hsym1 : m.Adj x (cutBranchSwapFun m c u v φ y) ↔
              m.Adj (cutBranchSwapFun m c u v φ y) x := m.adj_symm
          have hsym2 : m.Adj y x ↔ m.Adj x y := m.adj_symm
          rw [hFx]
          exact hsym1.trans (h.trans hsym2)
        · have hFy : cutBranchSwapFun m c u v φ y = y :=
            cutBranchSwapFun_of_not_mem m c u v φ hyU hyV
          rw [hFx, hFy]

theorem cutBranchSwap_adj_iff (m : MoleculeGraph V) (c u v : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hcv : m.Adj c v) (huv : u ≠ v)
    (φ : RootedCutBranchIso m c u v) (x y : V) :
    m.Adj (cutBranchSwap m c u v hacyc hcu hcv huv φ x)
        (cutBranchSwap m c u v hacyc hcu hcv huv φ y) ↔ m.Adj x y := by
  rw [cutBranchSwap_apply, cutBranchSwap_apply]
  exact cutBranchSwapFun_adj_iff m c u v hacyc hcu hcv huv φ
    (cutBranch_no_overlap m hacyc hcu hcv huv) x y

/-! ### Bond-order preservation and the automorphism -/

/-- When positive adjacency determines the bond order (`SimpleBonded`), an adjacency-preserving
permutation preserves all bond orders. -/
theorem bond_eq_of_adj_iff (m : MoleculeGraph V) (hsimple : m.SimpleBonded)
    (e : Equiv.Perm V)
    (hAdj : ∀ x y, m.Adj (e x) (e y) ↔ m.Adj x y) (x y : V) :
    m.bond (e x) (e y) = m.bond x y := by
  by_cases h : m.Adj x y
  · have h' : m.Adj (e x) (e y) := (hAdj x y).mpr h
    rw [hsimple _ _ h', hsimple _ _ h]
  · have h' : ¬ m.Adj (e x) (e y) := fun hh => h ((hAdj x y).mp hh)
    have hb : m.bond x y = 0 :=
      Nat.eq_zero_of_not_pos (by simpa [MoleculeGraph.Adj] using h)
    have hb' : m.bond (e x) (e y) = 0 :=
      Nat.eq_zero_of_not_pos (by simpa [MoleculeGraph.Adj] using h')
    rw [hb, hb']

/-- **The global branch swap is a molecular-graph automorphism.**  It preserves `atomZ`,
`atomMass`, constant formal charge, and every bond order. -/
theorem cutBranchSwap_isAutomorphism (m : MoleculeGraph V) (c u v : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hcv : m.Adj c v) (huv : u ≠ v)
    (hsimple : m.SimpleBonded) (hcharge : ConstantFormalCharge m)
    (φ : RootedCutBranchIso m c u v) :
    m.IsAutomorphism (cutBranchSwap m c u v hacyc hcu hcv huv φ) := by
  obtain ⟨q, hq⟩ := hcharge
  have hAdj : ∀ x y, m.Adj (cutBranchSwap m c u v hacyc hcu hcv huv φ x)
      (cutBranchSwap m c u v hacyc hcu hcv huv φ y) ↔ m.Adj x y :=
    cutBranchSwap_adj_iff m c u v hacyc hcu hcv huv φ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    rw [cutBranchSwap_apply]
    exact cutBranchSwapFun_atomZ m c u v φ x
  · intro x
    rw [cutBranchSwap_apply]
    exact cutBranchSwapFun_atomMass m c u v φ x
  · intro x
    exact (hq (cutBranchSwap m c u v hacyc hcu hcv huv φ x)).trans (hq x).symm
  · intro x y
    exact bond_eq_of_adj_iff m hsimple _ hAdj x y

/-- The global branch swap packaged as an automorphism of the molecular graph. -/
noncomputable def cutBranchSwapAut (m : MoleculeGraph V) (c u v : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hcv : m.Adj c v) (huv : u ≠ v)
    (hsimple : m.SimpleBonded) (hcharge : ConstantFormalCharge m)
    (φ : RootedCutBranchIso m c u v) : m.Aut :=
  ⟨cutBranchSwap m c u v hacyc hcu hcv huv φ,
    cutBranchSwap_isAutomorphism m c u v hacyc hcu hcv huv hsimple hcharge φ⟩

@[simp] theorem cutBranchSwapAut_apply (m : MoleculeGraph V) (c u v : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hcv : m.Adj c v) (huv : u ≠ v)
    (hsimple : m.SimpleBonded) (hcharge : ConstantFormalCharge m)
    (φ : RootedCutBranchIso m c u v) (x : V) :
    (cutBranchSwapAut m c u v hacyc hcu hcv huv hsimple hcharge φ : Equiv.Perm V) x =
      cutBranchSwap m c u v hacyc hcu hcv huv φ x := rfl

theorem cutBranchSwapAut_apply_center (m : MoleculeGraph V) (c u v : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hcv : m.Adj c v) (huv : u ≠ v)
    (hsimple : m.SimpleBonded) (hcharge : ConstantFormalCharge m)
    (φ : RootedCutBranchIso m c u v) :
    (cutBranchSwapAut m c u v hacyc hcu hcv huv hsimple hcharge φ : Equiv.Perm V) c = c :=
  cutBranchSwap_apply_center m c u v hacyc hcu hcv huv φ

/-! ### Lift to the automatically detected multi-center molecule -/

/-- The global cut-branch swap, regarded as an automorphism of the automatically detected
multi-center molecule.  Degree-four detection is automatic; no additional inventory is needed. -/
noncomputable def detectedCutBranchSwapAut (m : MoleculeGraph V) (c u v : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hcv : m.Adj c v) (huv : u ≠ v)
    (hsimple : m.SimpleBonded) (hcharge : ConstantFormalCharge m)
    (φ : RootedCutBranchIso m c u v) : m.detectedMultiCenterMolecule.Aut :=
  m.detectedMultiCenterAutOfGraphAut
    (cutBranchSwapAut m c u v hacyc hcu hcv huv hsimple hcharge φ)

@[simp] theorem detectedCutBranchSwapAut_apply (m : MoleculeGraph V) (c u v : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hcv : m.Adj c v) (huv : u ≠ v)
    (hsimple : m.SimpleBonded) (hcharge : ConstantFormalCharge m)
    (φ : RootedCutBranchIso m c u v) (x : V) :
    ((detectedCutBranchSwapAut m c u v hacyc hcu hcv huv hsimple hcharge φ :
        m.detectedMultiCenterMolecule.Aut) : Equiv.Perm V) x =
      cutBranchSwap m c u v hacyc hcu hcv huv φ x := rfl

theorem detectedCutBranchSwapAut_apply_center (m : MoleculeGraph V) (c u v : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hcv : m.Adj c v) (huv : u ≠ v)
    (hsimple : m.SimpleBonded) (hcharge : ConstantFormalCharge m)
    (φ : RootedCutBranchIso m c u v) :
    ((detectedCutBranchSwapAut m c u v hacyc hcu hcv huv hsimple hcharge φ :
        m.detectedMultiCenterMolecule.Aut) : Equiv.Perm V) c = c :=
  cutBranchSwap_apply_center m c u v hacyc hcu hcv huv φ

/-- The lifted multi-center automorphism carries the `u`-branch into the `v`-branch. -/
theorem detectedCutBranchSwapAut_maps_left_branch (m : MoleculeGraph V) (c u v : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hcv : m.Adj c v) (huv : u ≠ v)
    (hsimple : m.SimpleBonded) (hcharge : ConstantFormalCharge m)
    (φ : RootedCutBranchIso m c u v) {x : V} (hx : x ∈ CutBranch m c u) :
    ((detectedCutBranchSwapAut m c u v hacyc hcu hcv huv hsimple hcharge φ :
        m.detectedMultiCenterMolecule.Aut) : Equiv.Perm V) x ∈ CutBranch m c v := by
  rw [detectedCutBranchSwapAut_apply]
  exact cutBranchSwap_mem_left m c u v hacyc hcu hcv huv φ hx

/-- At a detected tetrahedral center `c` fixed by the swap, the induced permutation of the center
type fixes the corresponding center. -/
theorem detectedCutBranchSwapAut_centerPerm_fixed (m : MoleculeGraph V) (c u v : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hcv : m.Adj c v) (huv : u ≠ v)
    (hsimple : m.SimpleBonded) (hcharge : ConstantFormalCharge m)
    (φ : RootedCutBranchIso m c u v) (hc : c ∈ m.tetrahedralCenterSet) :
    m.detectedMultiCenterMolecule.centerPerm
        (detectedCutBranchSwapAut m c u v hacyc hcu hcv huv hsimple hcharge φ)
        ⟨c, hc⟩ = ⟨c, hc⟩ := by
  apply Subtype.ext
  change ((detectedCutBranchSwapAut m c u v hacyc hcu hcv huv hsimple hcharge φ :
      m.detectedMultiCenterMolecule.Aut) : Equiv.Perm V) c = c
  exact cutBranchSwap_apply_center m c u v hacyc hcu hcv huv φ

/-! ### Connection with rooted branch symmetry and rigidity -/

/-- The cut-branch reachability relation is definitionally the root-avoiding reachability used by
`RootedTetrahedralBranchSymmetry`. -/
theorem ligandBranchReaches_iff_cutBranchReaches (m : MultiCenterMolecule V) (c : m.Center)
    (i : Fin 4) (x : V) :
    RootedTetrahedralBranchSymmetry.LigandBranchReaches m c i x ↔
      CutBranchReaches m.mol c.1 (m.ligandAtomAt c i) x :=
  Iff.rfl

/-- **Constitutional rigidity input.**  If every graph automorphism fixing the root `c` fixes all
neighbors of `c`, then two distinct neighbors of `c` cannot carry isomorphic cut branches: any such
isomorphism would extend to a root-fixing automorphism moving `u` to `v`.

The hypothesis is on the *actual* automorphism group of the molecular graph, and the conclusion is
the nonexistence of an explicit rooted cut-branch isomorphism at the *same* root `c`.  Nothing is
asserted about isomorphic cuts at unrelated attachment roots. -/
theorem no_rootedCutBranchIso_of_pointwise_fixed (m : MoleculeGraph V) (c u v : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hcv : m.Adj c v) (huv : u ≠ v)
    (hsimple : m.SimpleBonded) (hcharge : ConstantFormalCharge m)
    (hfix : ∀ e : m.Aut, (e : Equiv.Perm V) c = c →
      ∀ x, m.Adj c x → (e : Equiv.Perm V) x = x) :
    ¬ Nonempty (RootedCutBranchIso m c u v) := by
  rintro ⟨φ⟩
  let e : m.Aut := cutBranchSwapAut m c u v hacyc hcu hcv huv hsimple hcharge φ
  have hcenter : (e : Equiv.Perm V) c = c :=
    cutBranchSwap_apply_center m c u v hacyc hcu hcv huv φ
  have hfixu : (e : Equiv.Perm V) u = u := hfix e hcenter u hcu
  have hleft : (e : Equiv.Perm V) u = v :=
    cutBranchSwap_apply_left m c u v hacyc hcu hcv huv φ
  exact huv (hfixu ▸ hleft)

end

end AcyclicCutBranchAutomorphism
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.CutBranchReaches
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.CutBranch
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranch_mem_self
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.center_not_mem_cutBranch
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranch_ne_center
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchReaches_trans
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranch_adj_mem
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranch_disjoint_of_acyclic
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranch_no_overlap
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranch_adj_center_iff
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranch_incidence
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranch_no_adj_of_acyclic
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.ConstantFormalCharge
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.RootedCutBranchIso
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.RootedCutBranchIso.adj_iff_symm
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwapFun
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwapFun_of_mem_left
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwapFun_of_mem_right
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwapFun_of_not_mem
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwapFun_involutive
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwap
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwap_apply
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwap_mem_left
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwap_mem_right
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwap_apply_center
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwap_apply_left
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwap_apply_right
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwapFun_atomZ
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwapFun_atomMass
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwapFun_mem_left
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwapFun_mem_right
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwapFun_not_mem_left
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwapFun_not_mem_right
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwapFun_eq_right_iff
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwapFun_eq_left_iff
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwapFun_adj_iff_of_mem_left
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwapFun_adj_iff_of_mem_right
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwapFun_adj_iff
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwap_adj_iff
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.bond_eq_of_adj_iff
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwap_isAutomorphism
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwapAut
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwapAut_apply
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.cutBranchSwapAut_apply_center
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.detectedCutBranchSwapAut
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.detectedCutBranchSwapAut_apply
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.detectedCutBranchSwapAut_apply_center
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.detectedCutBranchSwapAut_maps_left_branch
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.detectedCutBranchSwapAut_centerPerm_fixed
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.ligandBranchReaches_iff_cutBranchReaches
assert_kernel_only TetraStereo.OneCenter.AcyclicCutBranchAutomorphism.no_rootedCutBranchIso_of_pointwise_fixed
