import TetraStereo.OneCenter.AcyclicCutBranchAutomorphism
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

open AcyclicCutBranchAutomorphism




































noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Root boundary.**  The only vertex of the branch of `u` adjacent to the deleted root `c` is
the attachment vertex `u`.  This is the symmetric orientation of `cutBranch_adj_center_iff`. -/
theorem cutBranch_center_adj_iff (m : MoleculeGraph V) (h : m.Acyclic) {c u x : V}
    (hcu : m.Adj c u) (hx : x ∈ CutBranch m c u) :
    m.Adj c x ↔ x = u :=
  (m.adj_symm).trans (cutBranch_adj_center_iff m h hcu hx)

/-- **A branch cannot reach the deleted root through a sibling.**  If `w` is a neighbour of `u`
with `w ≠ c`, then the child branch `Cut(u,w)` contains no walk from `w` to `c` avoiding `u`:
together with the edges `u-w` and `u-c` such a walk would give a second simple path from `u` to
`c`, contradicting acyclicity. -/
theorem center_not_mem_cutBranch_of_neighbor (m : MoleculeGraph V) (h : m.Acyclic)
    {c u w : V} (hcu : m.Adj c u) (huw : m.Adj u w) (hwc : w ≠ c) :
    c ∉ CutBranch m u w := by
  rintro ⟨p, hpAvoid⟩
  let G := m.underlyingSimpleGraph
  have hG : G.IsAcyclic := h
  let r : G.Path w c := p.toPath
  have hrAvoid : u ∉ (r : G.Walk w c).support :=
    fun hu => hpAvoid (SimpleGraph.Walk.support_toPath_subset p hu)
  have hucNe : u ≠ c := by
    intro hEq
    rw [hEq] at hcu
    simp [MoleculeGraph.Adj, m.bond_self] at hcu
  have huwG : G.Adj u w := huw
  have hucG : G.Adj u c := m.adj_symm.mpr hcu
  let extended : G.Walk u c := SimpleGraph.Walk.cons huwG (r : G.Walk w c)
  have hextended : extended.IsPath :=
    (SimpleGraph.Walk.cons_isPath_iff huwG (r : G.Walk w c)).2 ⟨r.2, hrAvoid⟩
  let single : G.Walk u c := SimpleGraph.Walk.cons hucG SimpleGraph.Walk.nil
  have hsingle : single.IsPath := by
    refine (SimpleGraph.Walk.cons_isPath_iff hucG SimpleGraph.Walk.nil).2
      ⟨SimpleGraph.Walk.IsPath.nil, ?_⟩
    simpa [SimpleGraph.Walk.support_nil] using hucNe
  have hEq : (⟨extended, hextended⟩ : G.Path u c) = ⟨single, hsingle⟩ :=
    hG.path_unique _ _
  have hwalk : extended = single :=
    congrArg (fun path : G.Path u c => (path : G.Walk u c)) hEq
  have hfirst : extended.getVert 1 = single.getVert 1 :=
    congrArg (fun walk : G.Walk u c => walk.getVert 1) hwalk
  have hextendedFirst : extended.getVert 1 = w := by simp [extended]
  have hsingleFirst : single.getVert 1 = c := by simp [single]
  rw [hextendedFirst, hsingleFirst] at hfirst
  exact hwc hfirst

/-- **Rooted cut decomposition.**  A vertex lies in the branch of `u` after deleting `c` exactly
when it is the attachment vertex `u`, or when it lies in the child branch `Cut(u,w)` of some
neighbour `w` of `u` other than the deleted root. -/
theorem cutBranch_mem_iff (m : MoleculeGraph V) (h : m.Acyclic) {c u : V} (hcu : m.Adj c u)
    {x : V} :
    x ∈ CutBranch m c u ↔
      x = u ∨ ∃ w, m.Adj u w ∧ w ≠ c ∧ x ∈ CutBranch m u w := by
  constructor
  · intro hx
    obtain ⟨p, hpAvoid⟩ := hx
    by_cases hxu : x = u
    · exact Or.inl hxu
    · right
      let G := m.underlyingSimpleGraph
      let q : G.Path u x := p.toPath
      have hqAvoid : c ∉ (q : G.Walk u x).support :=
        fun hc => hpAvoid (SimpleGraph.Walk.support_toPath_subset p hc)
      have hnotNil : ¬ (q : G.Walk u x).Nil := by
        intro hnil
        have hzero : (q : G.Walk u x).length = 0 :=
          (SimpleGraph.Walk.nil_iff_length_eq).mp hnil
        exact hxu (SimpleGraph.Walk.eq_of_length_eq_zero hzero).symm
      let w : V := (q : G.Walk u x).getVert 1
      have huw : m.Adj u w := by
        have hadj := (q : G.Walk u x).adj_getVert_succ (i := 0) (by
          have hpos : 0 < (q : G.Walk u x).length :=
            (SimpleGraph.Walk.not_nil_iff_lt_length).mp hnotNil
          omega)
        simpa [w] using hadj
      have hwc : w ≠ c := by
        intro hEq
        apply hqAvoid
        rw [← hEq]
        exact SimpleGraph.Walk.getVert_mem_support (q : G.Walk u x) 1
      refine ⟨w, huw, hwc, ?_⟩
      refine ⟨(q : G.Walk u x).tail, ?_⟩
      rw [SimpleGraph.Walk.support_tail_of_not_nil _ hnotNil]
      have hnodup : (q : G.Walk u x).support.Nodup := q.2.support_nodup
      rw [SimpleGraph.Walk.support_eq_cons] at hnodup
      exact (List.nodup_cons.mp hnodup).1
  · rintro (hxu | ⟨w, huw, hwc, hx⟩)
    · simpa [hxu] using cutBranch_mem_self m hcu
    · obtain ⟨q, hqAvoid⟩ := hx
      have hcNotBranch : c ∉ CutBranch m u w :=
        center_not_mem_cutBranch_of_neighbor m h hcu huw hwc
      have hcuNe : c ≠ u := by
        intro hEq
        rw [hEq] at hcu
        simp [MoleculeGraph.Adj, m.bond_self] at hcu
      refine ⟨SimpleGraph.Walk.cons huw q, ?_⟩
      rw [SimpleGraph.Walk.support_cons]
      intro hcMem
      rw [List.mem_cons] at hcMem
      rcases hcMem with hcEq | hcMem
      · exact hcuNe hcEq
      · have hprefixAvoid : u ∉ (q.takeUntil c hcMem).support :=
          fun hu => hqAvoid (SimpleGraph.Walk.support_takeUntil_subset q hcMem hu)
        exact hcNotBranch ⟨q.takeUntil c hcMem, hprefixAvoid⟩

/-- **Child branches glue into the parent branch.**  If `w` is a neighbour of `u` different from
the deleted root `c`, then `Cut(u,w)` is contained in `Cut(c,u)`. -/
theorem cutBranch_child_subset (m : MoleculeGraph V) (h : m.Acyclic) {c u w : V}
    (hcu : m.Adj c u) (huw : m.Adj u w) (hwc : w ≠ c) :
    CutBranch m u w ⊆ CutBranch m c u := by
  intro x hx
  exact (cutBranch_mem_iff m h hcu).mpr (Or.inr ⟨w, huw, hwc, hx⟩)

/-- **Child branches are pairwise disjoint.** -/
theorem cutBranch_child_disjoint (m : MoleculeGraph V) (h : m.Acyclic) {u w₁ w₂ : V}
    (h₁ : m.Adj u w₁) (h₂ : m.Adj u w₂) (hne : w₁ ≠ w₂) :
    ∀ x, x ∈ CutBranch m u w₁ → x ∈ CutBranch m u w₂ → False :=
  cutBranch_no_overlap m h h₁ h₂ hne

/-- **No physical edge between distinct child branches.** -/
theorem cutBranch_children_no_adj (m : MoleculeGraph V) (h : m.Acyclic) {u w₁ w₂ : V}
    (h₁ : m.Adj u w₁) (h₂ : m.Adj u w₂) (hne : w₁ ≠ w₂) {x y : V}
    (hx : x ∈ CutBranch m u w₁) (hy : y ∈ CutBranch m u w₂) :
    ¬ m.Adj x y :=
  cutBranch_no_adj_of_acyclic m h h₁ h₂ hne hx hy

/-- **Set form of the rooted cut decomposition.** -/
theorem cutBranch_eq_singleton_union (m : MoleculeGraph V) (h : m.Acyclic) {c u : V}
    (hcu : m.Adj c u) :
    CutBranch m c u =
      {u} ∪ ⋃ (w : {w : V // m.Adj u w ∧ w ≠ c}), CutBranch m u w.1 := by
  ext x
  rw [cutBranch_mem_iff m h hcu]
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_iUnion]
  constructor
  · rintro (rfl | ⟨w, huw, hwc, hx⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨⟨w, huw, hwc⟩, hx⟩
  · rintro (rfl | ⟨⟨w, huw, hwc⟩, hx⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨w, huw, hwc, hx⟩

/-- **Packaged decomposition and gluing core for a rooted cut branch.**

1. `Cut(c,u)` is `{u}` together with the union of the child branches `Cut(u,w)`, `w ≠ c`.
2. The attachment vertex `u` is in no child branch, and every child branch is contained in the
   parent branch.
3. Distinct child branches are disjoint and carry no physical edge between them.
4. The only vertex of `Cut(c,u)` adjacent to the deleted root `c` is the attachment vertex `u`.

Items 1–2 are the gluing data, item 3 supplies absence of cross edges between child cuts, and
item 4 is the root-boundary attachment condition. -/
theorem cutBranch_decomposition_and_gluing (m : MoleculeGraph V) (h : m.Acyclic) {c u : V}
    (hcu : m.Adj c u) :
    CutBranch m c u =
        {u} ∪ ⋃ (w : {w : V // m.Adj u w ∧ w ≠ c}), CutBranch m u w.1 ∧
      (∀ w : {w : V // m.Adj u w ∧ w ≠ c},
        u ∉ CutBranch m u w.1 ∧ CutBranch m u w.1 ⊆ CutBranch m c u) ∧
      (∀ w₁ w₂ : {w : V // m.Adj u w ∧ w ≠ c}, w₁ ≠ w₂ →
        ∀ x y, x ∈ CutBranch m u w₁.1 → y ∈ CutBranch m u w₂.1 → ¬ m.Adj x y) ∧
      (∀ x, x ∈ CutBranch m c u → (m.Adj c x ↔ x = u)) := by
  refine ⟨cutBranch_eq_singleton_union m h hcu, ?_, ?_, ?_⟩
  · intro w
    exact ⟨center_not_mem_cutBranch m u w.1,
      cutBranch_child_subset m h hcu w.2.1 w.2.2⟩
  · intro w₁ w₂ hne x y hx hy
    have hneValues : w₁.1 ≠ w₂.1 := fun hValue => hne (Subtype.ext hValue)
    exact cutBranch_children_no_adj m h w₁.2.1 w₂.2.1 hneValues hx hy
  · intro x hx
    exact cutBranch_center_adj_iff m h hcu hx

/-- **Incidence law inside a rooted cut branch (derived consumer of the gluing core).**

Every physical bond with both endpoints in `Cut(c,u)` is either incident to the attachment vertex
`u`, or has both endpoints inside the same child branch `Cut(u,w)` for a single neighbour `w ≠ c`.

This is the exact case analysis used by a recursive assembler: after matching the attachment
vertices and gluing child cut isomorphisms, no physical bond of the parent branch is left
unaccounted for, and no bond between two distinct child cuts exists. -/
theorem cutBranch_adj_same_child_or_attach (m : MoleculeGraph V) (h : m.Acyclic) {c u : V}
    (hcu : m.Adj c u) {x y : V}
    (hx : x ∈ CutBranch m c u) (hy : y ∈ CutBranch m c u) (hxy : m.Adj x y) :
    (x = u ∨ y = u) ∨
      ∃ w : V, m.Adj u w ∧ w ≠ c ∧
        x ∈ CutBranch m u w ∧ y ∈ CutBranch m u w := by
  have hx' := (cutBranch_mem_iff m h hcu).mp hx
  have hy' := (cutBranch_mem_iff m h hcu).mp hy
  rcases hx' with rfl | ⟨w₁, huw₁, hw₁c, hx₁⟩
  · exact Or.inl (Or.inl rfl)
  · rcases hy' with rfl | ⟨w₂, huw₂, hw₂c, hy₂⟩
    · exact Or.inl (Or.inr rfl)
    · by_cases hEq : w₁ = w₂
      · refine Or.inr ⟨w₂, huw₂, hw₂c, ?_, hy₂⟩
        rw [← hEq]
        exact hx₁
      · exact absurd hxy (cutBranch_no_adj_of_acyclic m h huw₁ huw₂ hEq hx₁ hy₂)

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.cutBranch_center_adj_iff
assert_kernel_only TetraStereo.OneCenter.center_not_mem_cutBranch_of_neighbor
assert_kernel_only TetraStereo.OneCenter.cutBranch_mem_iff
assert_kernel_only TetraStereo.OneCenter.cutBranch_child_subset
assert_kernel_only TetraStereo.OneCenter.cutBranch_child_disjoint
assert_kernel_only TetraStereo.OneCenter.cutBranch_children_no_adj
assert_kernel_only TetraStereo.OneCenter.cutBranch_eq_singleton_union
assert_kernel_only TetraStereo.OneCenter.cutBranch_decomposition_and_gluing
assert_kernel_only TetraStereo.OneCenter.cutBranch_adj_same_child_or_attach

end

end TetraStereo.OneCenter
