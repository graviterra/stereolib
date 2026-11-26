import TetraStereo.Engine.RingGraphPaths
import Mathlib.Combinatorics.SimpleGraph.Paths

/-! A visited non-parent closure separates the access path from a simple cycle. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingClosureCycle
open OneCenter CertifiedLocalizedCIPInput SimpleGraph
open LocalizedChemicalRing (Input)

/-- Every simple graph walk is a real molecular occurrence path. -/
theorem path_of_walk {i : Input} {r a : i.certified.Atom}
    (p : i.certified.moleculeGraph.underlyingSimpleGraph.Walk r a) (hp : p.IsPath) :
    RingGraphPaths.Path i r p.support.reverse a := by
  induction p using Walk.concatRec with
  | Hnil => exact .origin
  | @Hconcat r a b p h ih =>
    have parts := (Walk.concat_isPath_iff h).mp hp
    simpa only [Walk.support_concat, List.concat_eq_append, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.reverse_concat] using
      RingGraphPaths.Path.step (ih parts.1) h (by simpa using parts.2)

theorem exists_walk {i : Input} {r h a} (p : RingGraphPaths.Path i r h a) :
    ∃ w : i.certified.moleculeGraph.underlyingSimpleGraph.Walk r a,
      w.support = h.reverse := by
  induction p with
  | origin => exact ⟨.nil, rfl⟩
  | step prior bond fresh ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨w.concat bond, by simp [SimpleGraph.Walk.support_concat, hw]⟩

noncomputable def toWalk {i : Input} {r h a} (p : RingGraphPaths.Path i r h a) :
    i.certified.moleculeGraph.underlyingSimpleGraph.Walk r a :=
  Classical.choose (exists_walk p)

theorem support_toWalk {i : Input} {r h a} (p : RingGraphPaths.Path i r h a) :
    (toWalk p).support = h.reverse := Classical.choose_spec (exists_walk p)

theorem isPath_toWalk {i : Input} {r h a} (p : RingGraphPaths.Path i r h a) :
    (toWalk p).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [support_toWalk, List.nodup_reverse]
  induction p with
  | origin => simp
  | step prior bond fresh ih => exact List.nodup_cons.mpr ⟨fresh, ih⟩

theorem toWalk_step {i : Input} {r h a b} (p : RingGraphPaths.Path i r h a)
    (bond : i.certified.moleculeGraph.Adj a b) (fresh : b ∉ h) :
    toWalk (.step p bond fresh) = (toWalk p).concat bond := by
  apply SimpleGraph.Walk.support_injective
  simp [support_toWalk, SimpleGraph.Walk.support_concat]

theorem history_head {i : Input} {r h a} (p : RingGraphPaths.Path i r h a) :
    h[0]? = some a := by cases p <;> rfl

theorem parent_penultimate {i : Input} {r h a t} (p : RingGraphPaths.Path i r h a)
    (close : i.certified.moleculeGraph.Adj a t) (nonparent : h[1]? ≠ some t) :
    t ≠ (toWalk p).penultimate := by
  cases p with
  | origin =>
    have eqn : toWalk (RingGraphPaths.Path.origin (i := i) (root := r)) = .nil := by
      apply SimpleGraph.Walk.support_injective
      exact support_toWalk _
    rw [eqn]
    exact (i.certified.moleculeGraph.underlyingSimpleGraph.ne_of_adj close).symm
  | step prior bond fresh =>
    rw [toWalk_step prior bond fresh, SimpleGraph.Walk.penultimate_concat]
    have head := history_head prior
    intro eqn
    apply nonparent
    simp only [List.getElem?_cons_succ]
    exact head.trans (congrArg some eqn.symm)

/-- The access and the cycle meet only at the visited closure target. The suffix
retains the decomposition of the original occurrence history. -/
theorem split_closure {V : Type*} {G : SimpleGraph V} {r a t : V}
    (p : G.Walk r a) (hp : p.IsPath) (visited : t ∈ p.support)
    (close : G.Adj a t) (nonparent : t ≠ p.penultimate) :
    ∃ (access : G.Walk r t) (suffix : G.Walk t a),
      p = access.append suffix ∧ access.IsPath ∧ suffix.IsPath ∧
      (suffix.concat close).IsCycle ∧
      ∀ x, x ∈ access.support → x ∈ (suffix.concat close).support → x = t := by
  obtain ⟨access, suffix, hpre, hsuf, eqn⟩ := hp.mem_support_iff_exists_append.mp visited
  have absent : s(a,t) ∉ suffix.edges := by
    intro mem
    have mem' : s(a,t) ∈ p.edges := by
      rw [eqn, SimpleGraph.Walk.edges_append]
      exact List.mem_append_right _ mem
    exact nonparent (hp.eq_penultimate_of_mem_edges mem')
  have cyc : (suffix.concat close).IsCycle := by
    apply SimpleGraph.Walk.isCycle_reverse.mp
    rw [SimpleGraph.Walk.reverse_concat]
    apply (SimpleGraph.Walk.cons_isCycle_iff _ _).mpr
    exact ⟨hsuf.reverse, by simpa [SimpleGraph.Walk.edges_reverse, Sym2.eq_swap] using absent⟩
  refine ⟨access, suffix, eqn, hpre, hsuf, cyc, ?_⟩
  intro x hx hc
  by_contra ne
  have hs : x ∈ suffix.support := by
    simpa [SimpleGraph.Walk.support_concat, ne] using hc
  exact (SimpleGraph.Walk.IsPath.ne_of_mem_support_of_append
    (eqn ▸ hp) ne hx hs) rfl

theorem path_split_closure {i : Input} {r h a t}
    (p : RingGraphPaths.Path i r h a) (visited : t ∈ h)
    (close : i.certified.moleculeGraph.Adj a t)
    (nonparent : h[1]? ≠ some t) :
    ∃ (access : i.certified.moleculeGraph.underlyingSimpleGraph.Walk r t)
      (suffix : i.certified.moleculeGraph.underlyingSimpleGraph.Walk t a),
      toWalk p = access.append suffix ∧ access.IsPath ∧ suffix.IsPath ∧
      (suffix.concat close).IsCycle ∧
      ∀ x, x ∈ access.support → x ∈ (suffix.concat close).support → x = t :=
  split_closure _ (isPath_toWalk p) (by simpa [support_toWalk] using visited) close (parent_penultimate p close nonparent)

end TetraStereo.Engine.RingClosureCycle
assert_kernel_only TetraStereo.Engine.RingClosureCycle.path_split_closure
