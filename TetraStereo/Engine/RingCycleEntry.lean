import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Uniqueness of simple first-entry walks to the support of a unique cycle. -/
namespace TetraStereo.Engine.RingCycleEntry
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- Every cycle has the same vertex support as the selected cycle. -/
def UniqueCycleSupport {c : V} (cycle : G.Walk c c) : Prop :=
  ∀ ⦃v⦄ (p : G.Walk v v), p.IsCycle → ∀ x, x ∈ p.support ↔ x ∈ cycle.support

/-- The endpoint lies in the target and each preceding vertex lies outside it. -/
def FirstEntry (C : Set V) : {u v : V} → G.Walk u v → Prop
  | u, _, .nil => u ∈ C
  | u, _, .cons _ p => u ∉ C ∧ FirstEntry C p

/-- The support-intersection formulation implies first entry. -/
theorem firstEntry_of_intersection (C : Set V) {u v} (p : G.Walk u v)
    (hp : p.IsPath) (hv : v ∈ C)
    (hi : ∀ x ∈ p.support, x ∈ C → x = v) : FirstEntry C p := by
  induction p with
  | nil => exact hv
  | @cons u w v h p ih =>
    rw [Walk.cons_isPath_iff] at hp
    refine ⟨?_, ih hp.1 hv ?_⟩
    · intro hu
      have huv := hi u (by simp) hu
      exact hp.2 (huv ▸ p.end_mem_support)
    · intro x hx hxC
      exact hi x (by simp [hx]) hxC

private theorem entry_unique (C : Set V)
    (bridges : ∀ {a b}, a ∉ C → G.Adj a b → G.IsBridge s(a,b))
    (connected : ∀ {a b}, a ∈ C → b ∈ C →
      ∃ p : G.Walk a b, ∀ x ∈ p.support, x ∈ C)
    {r a b} (p : G.Walk r a) (q : G.Walk r b)
    (hp : p.IsPath) (hq : q.IsPath) (ep : FirstEntry C p) (eq : FirstEntry C q) :
    a = b ∧ HEq p q := by
  have end_mem : ∀ {x y} (w : G.Walk x y), FirstEntry C w → y ∈ C := by
    intro x y w
    induction w with
    | nil => exact id
    | cons h w ih => exact fun e => ih e.2
  induction p with
  | nil =>
    cases q with
    | nil => exact ⟨rfl, HEq.rfl⟩
    | cons h q => exact False.elim (eq.1 ep)
  | @cons r t a h p ih =>
    cases q with
    | nil => exact False.elim (ep.1 eq)
    | @cons _ s b k q =>
      obtain ⟨c, hc⟩ := connected (end_mem _ eq.2) (end_mem _ ep.2)
      have he := (isBridge_iff_adj_and_forall_walk_mem_edges.mp (bridges ep.1 h)).2
        ((Walk.cons k q).append (c.append p.reverse))
      simp only [Walk.edges_append, Walk.edges_reverse, List.mem_append,
        List.mem_reverse, Walk.edges_cons, List.mem_cons] at he
      rw [Walk.cons_isPath_iff] at hp hq
      rcases he with (he | he) | he | he
      · rcases Sym2.eq_iff.mp he with ⟨_, e⟩ | ⟨_, e⟩
        · subst s
          obtain ⟨hab, hh⟩ := ih q hp.1 hq.1 ep.2 eq.2
          subst b
          cases hh
          exact ⟨rfl, HEq.rfl⟩
        · exact False.elim (h.ne e.symm)
      · exact False.elim (hq.2 (q.fst_mem_support_of_mem_edges he))
      · exact False.elim (ep.1 (hc _ (c.fst_mem_support_of_mem_edges he)))
      · exact False.elim (hp.2 (p.fst_mem_support_of_mem_edges he))

private theorem cycle_edge_incident {u v : V} (c : G.Walk u u)
    (hc : c.IsCycle) (he : s(u,v) ∈ c.edges) :
    v = c.snd ∨ v = c.penultimate := by
  cases c with
  | nil => exact False.elim (hc.ne_nil rfl)
  | @cons _ t _ h p =>
    have hp := (Walk.cons_isCycle_iff p h).mp hc
    simp only [Walk.edges_cons, List.mem_cons] at he
    rcases he with he | he
    · left
      rcases Sym2.eq_iff.mp he with ⟨_, hv⟩ | ⟨hu, hv⟩
      · simpa only [Walk.snd_cons] using hv
      · exact False.elim (h.ne hu)
    · right
      rw [Walk.penultimate_cons_of_not_nil h p (Walk.not_nil_of_isCycle_cons hc)]
      exact hp.1.eq_penultimate_of_mem_edges he

private theorem cycle_normalize_edge {r u v : V} (c : G.Walk r r)
    (hc : c.IsCycle) (he : s(u,v) ∈ c.edges) :
    ∃ (h : G.Adj u v) (p : G.Walk v u),
      p.IsPath ∧ s(u,v) ∉ p.edges ∧
      ∀ x, x ∈ c.support ↔ x ∈ (Walk.cons h p).support := by
  classical
  let d := c.rotate (c.fst_mem_support_of_mem_edges he)
  have hd : d.IsCycle := hc.rotate _
  have hed : s(u,v) ∈ d.edges := (c.rotate_edges _).mem_iff.mpr he
  have choose : ∃ d' : G.Walk u u, d'.IsCycle ∧ d'.snd = v ∧
      ∀ x, x ∈ d'.support ↔ x ∈ c.support := by
    rcases cycle_edge_incident d hd hed with hv | hv
    · exact ⟨d, hd, hv.symm, fun x => c.mem_support_rotate_iff _⟩
    · refine ⟨d.reverse, hd.reverse, ?_, ?_⟩
      · simpa only [Walk.snd_reverse] using hv.symm
      · intro x
        simpa only [Walk.support_reverse, List.mem_reverse] using c.mem_support_rotate_iff
          (c.fst_mem_support_of_mem_edges he) (w := x)
  obtain ⟨d', hd', hs, hm⟩ := choose
  cases d' with
  | nil => exact False.elim (hd'.ne_nil rfl)
  | @cons _ t _ h p =>
    simp only [Walk.snd_cons] at hs
    subst t
    have hp := (Walk.cons_isCycle_iff p h).mp hd'
    exact ⟨h, p, hp.1, hp.2, fun x => (hm x).symm⟩

/-- Deleting one edge to leave a forest is sufficient for uniqueness of cycle support.
No connectedness or finiteness assumption is needed. -/
theorem uniqueCycleSupport_of_deleteEdges_isAcyclic {u v c : V}
    (forest : (G.deleteEdges {s(u,v)}).IsAcyclic)
    (cycle : G.Walk c c) (hcycle : cycle.IsCycle) : UniqueCycleSupport cycle := by
  classical
  have transfer_edges : ∀ {a b} (p : G.Walk a b), s(u,v) ∉ p.edges →
      ∀ e ∈ p.edges, e ∈ (G.deleteEdges {s(u,v)}).edgeSet := by
    intro a b p hp e he
    simp only [SimpleGraph.edgeSet_deleteEdges, Set.mem_diff, Set.mem_singleton_iff]
    exact ⟨p.edges_subset_edgeSet he, fun hh => hp (hh ▸ he)⟩
  have edge_mem : ∀ {a} (p : G.Walk a a), p.IsCycle → s(u,v) ∈ p.edges := by
    intro a p hp
    by_contra he
    exact forest (p.transfer _ (transfer_edges p he)) (hp.transfer _)
  obtain ⟨h, p, hp, hep, hps⟩ := cycle_normalize_edge cycle hcycle (edge_mem cycle hcycle)
  intro a cycle' hc' x
  obtain ⟨h', q, hq, heq, hqs⟩ := cycle_normalize_edge cycle' hc' (edge_mem cycle' hc')
  have same := forest.path_unique
    ⟨p.transfer _ (transfer_edges p hep), hp.transfer _⟩
    ⟨q.transfer _ (transfer_edges q heq), hq.transfer _⟩
  have supports := congrArg (fun z : (G.deleteEdges {s(u,v)}).Path v u => z.val.support) same
  simp only [Walk.support_transfer] at supports
  rw [hqs x, hps x]
  simp only [Walk.support_cons, List.mem_cons, supports]

/-- Both the endpoint and the entire rooted walk are unique, for every cycle length. -/
theorem unique_first_entry {c r a b : V} (cycle : G.Walk c c)
    (unique : UniqueCycleSupport cycle)
    (p : G.Walk r a) (q : G.Walk r b)
    (hp : p.IsPath) (hq : q.IsPath)
    (ep : FirstEntry {x | x ∈ cycle.support} p)
    (eq : FirstEntry {x | x ∈ cycle.support} q) : a = b ∧ HEq p q := by
  classical
  apply entry_unique {x | x ∈ cycle.support} ?_ ?_ p q hp hq ep eq
  · intro a b ha hab
    apply isBridge_iff_adj_and_forall_cycle_notMem.mpr
    refine ⟨hab, ?_⟩
    intro v w hw he
    exact ha ((unique w hw a).mp (w.fst_mem_support_of_mem_edges he))
  · intro a b ha hb
    refine ⟨(cycle.takeUntil a ha).reverse.append (cycle.takeUntil b hb), ?_⟩
    intro x hx
    simp only [Walk.support_append, Walk.support_reverse, List.mem_append,
      List.mem_reverse] at hx
    rcases hx with hx | hx
    · exact cycle.support_takeUntil_subset ha hx
    · exact cycle.support_takeUntil_subset hb (List.mem_of_mem_tail hx)
end TetraStereo.Engine.RingCycleEntry
