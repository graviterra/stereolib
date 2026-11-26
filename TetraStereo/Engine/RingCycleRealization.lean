import TetraStereo.Engine.RingSingleCycleOrigin

/-! Realizing every simple cycle access as a full-fuel molecular ring duplicate. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingCycleRealization
open OneCenter CertifiedLocalizedCIPInput SimpleGraph
open LocalizedChemicalRing (Input)
open RingClosureCycle (toWalk support_toWalk path_of_walk)
open RingSingleCycleOrigin (originPath)
open private position position_spec from TetraStereo.Engine.RingGraphPaths
open private parent_get origin_index from TetraStereo.Engine.RingSingleCycleOrigin

private theorem parent_edge {i : Input} {r h a w}
    (p : RingGraphPaths.Path i r h a) (parent : h[1]? = some w) :
    s(a,w) ∈ (toWalk p).edges := by
  cases p with
  | origin => simp at parent
  | @step h b a prior bond fresh =>
    have head := RingClosureCycle.history_head prior
    simp only [List.getElem?_cons_succ] at parent
    obtain rfl := Option.some.inj (parent.symm.trans head)
    rw [RingClosureCycle.toWalk_step prior bond fresh, Walk.edges_concat, List.concat_eq_append]
    apply List.mem_append_right
    exact List.mem_singleton.mpr Sym2.eq_swap

private theorem realize_concat {i : Input} {r w a : i.certified.Atom}
    (p : i.certified.moleculeGraph.underlyingSimpleGraph.Walk r w)
    (t : i.certified.moleculeGraph.underlyingSimpleGraph.Walk w a)
    (close : i.certified.moleculeGraph.Adj a w) (hp : p.IsPath)
    (cycle : (t.concat close).IsCycle)
    (meet : ∀ x ∈ p.support, x ∈ (t.concat close).support → x = w) :
    ∃ q : RingActivePairs.Site i, q.val.root = r ∧
      q.val.node.provenance = .ringDuplicate p.length ∧
      originPath q.val.node p.length = p.support := by
  have ht : t.IsPath := by
    have rev := cycle.reverse
    rw [Walk.reverse_concat] at rev
    simpa only [Walk.reverse_reverse] using (Walk.cons_isCycle_iff _ _).mp rev |>.1.reverse
  have absent : s(a,w) ∉ t.edges := by
    have rev := cycle.reverse
    rw [Walk.reverse_concat] at rev
    simpa only [Walk.edges_reverse, List.mem_reverse, Sym2.eq_swap] using
      (Walk.cons_isCycle_iff _ _).mp rev |>.2
  have hfull : (p.append t).IsPath := by
    apply Walk.IsPath.mk'
    rw [Walk.support_append, List.nodup_append']
    refine ⟨hp.support_nodup, ht.support_nodup.tail, ?_⟩
    intro x hx hxt
    have eqw := meet x hx (by simp [Walk.support_concat, List.mem_of_mem_tail hxt])
    subst x
    have nd := ht.support_nodup
    rw [Walk.support_eq_cons, List.nodup_cons] at nd
    exact nd.1 hxt
  have path := path_of_walk (p.append t) hfull
  let pos := position i r (p.append t).support.reverse
  have spec := position_spec path
  have hist : pos.1.history = (p.append t).support.reverse := spec.2.1
  have walkEq : toWalk path = p.append t := by
    apply Walk.support_injective
    simp only [support_toWalk, List.reverse_reverse]
  have visited : w ∈ pos.1.history := by
    rw [hist, List.mem_reverse, Walk.support_append]
    exact List.mem_append_left _ p.end_mem_support
  have notParent : pos.1.parent? ≠ some w := by
    intro parent
    have mem := parent_edge path (by rw [←hist, parent_get]; exact parent)
    rw [walkEq, Walk.edges_append, List.mem_append] at mem
    rcases mem with mem | mem
    · have haw := meet a (p.fst_mem_support_of_mem_edges mem)
        (by simp [Walk.support_concat])
      exact i.certified.moleculeGraph.underlyingSimpleGraph.ne_of_adj close haw
    · exact absent mem
  have legitimate : LegitimateOccurrence i.certified r (pos.1.extend w 0)
      (pos.2 ++ [i.certified.executableOfficialChildCopySlot pos.1 w 0]) :=
    .ring spec.1 spec.2.2 close notParent visited
  have nodePath : RingGraphPaths.Path i r pos.1.history a := hist.symm ▸ path
  have nodeWalkEq : toWalk nodePath = p.append t := by
    apply Walk.support_injective
    simp only [support_toWalk, hist, List.reverse_reverse]
  have idx : pos.1.duplicateRootDistance w = p.length :=
    origin_index nodePath visited p t nodeWalkEq
  let q : RingActivePairs.Site i := ⟨_,
    i.certified.legitimateOccurrence_mem_localizedOccurrences_of_fuel legitimate
      (Nat.le_succ_of_le (i.certified.legitimateOccurrence_address_length_le_atomCount legitimate))⟩
  refine ⟨q,rfl,?_,?_⟩
  · change (pos.1.extend w 0).provenance = _
    rw [i.certified.legitimateOccurrence_ring_provenance visited, idx]
  · change originPath (pos.1.extend w 0) p.length = _
    have history : pos.1.history.reverse = p.support ++ t.support.tail := by
      rw [hist, List.reverse_reverse, Walk.support_append]
    simp only [originPath, OfficialCIPNode.extend_history, List.tail_cons, history,
      ←p.length_support, List.take_left]

/-- Every simple access path meeting a simple cycle only at its endpoint is the
exact origin path of a genuine ring duplicate in the full-fuel retained carrier. -/
theorem realize_cycle {i : Input} {r w : i.certified.Atom}
    (p : i.certified.moleculeGraph.underlyingSimpleGraph.Walk r w)
    (cycle : i.certified.moleculeGraph.underlyingSimpleGraph.Walk w w)
    (hp : p.IsPath) (hc : cycle.IsCycle)
    (meet : ∀ x ∈ p.support, x ∈ cycle.support → x = w) :
    ∃ q : RingActivePairs.Site i, q.val.root = r ∧
      q.val.node.provenance = .ringDuplicate p.length ∧
      originPath q.val.node p.length = p.support := by
  cases cycle with
  | nil => exact False.elim (hc.ne_nil rfl)
  | cons h t =>
    obtain ⟨a,s,close,eqn⟩ := Walk.exists_cons_eq_concat h t
    rw [eqn] at hc meet
    exact realize_concat p s close hp hc meet
end TetraStereo.Engine.RingCycleRealization
assert_kernel_only TetraStereo.Engine.RingCycleRealization.realize_cycle
