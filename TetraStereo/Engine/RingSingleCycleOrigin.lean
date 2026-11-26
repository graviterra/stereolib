import TetraStereo.Engine.RingClosureCycle
import TetraStereo.Engine.RingCycleEntry
import TetraStereo.Engine.RingPyramidalPathProvenance

/-! Ring duplicates on a fixed one-cycle molecular digraph share their entire
real origin path, even when compared after moving the active focus. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingSingleCycleOrigin
open OneCenter CertifiedLocalizedCIPInput SimpleGraph
open LocalizedChemicalRing (Input)
open RingCycleEntry (FirstEntry UniqueCycleSupport)
open RingClosureCycle (toWalk support_toWalk)
open private ofSimple from TetraStereo.Engine.RingGraphPaths

/-- The atom history of the duplicated real occurrence, in root-first order.
The child's last step is removed before its stored origin index is read. -/
def originPath {V : Type*} (node : OfficialCIPNode V) (index : Nat) : List V :=
  node.history.tail.reverse.take (index + 1)

/-- Number of common starting vertices of two root-first paths. -/
def shared {V : Type*} [DecidableEq V] : List V → List V → Nat
  | a :: xs,b :: ys => if a = b then 1 + shared xs ys else 0
  | _,_ => 0

/-- Distances in the retained occurrence tree. After the paths diverge, the
unique connecting walk traverses the two remaining suffixes. -/
def pathDistance {V : Type*} [DecidableEq V] (xs ys : List V) : Nat :=
  let common := shared xs ys
  (xs.length - common) + (ys.length - common)

private theorem parent_get {V : Type*} (node : OfficialCIPNode V) :
    node.history[1]? = node.parent? := by
  cases node with
  | mk cur h pr =>
    cases h with
    | nil => rfl
    | cons x xs => cases xs <;> rfl

private theorem origin_index {i : Input} {r a w} {node : OfficialCIPNode i.certified.Atom}
    (walk : RingGraphPaths.Path i r node.history a) (seen : w ∈ node.history)
    (pre : i.certified.moleculeGraph.underlyingSimpleGraph.Walk r w)
    (post : i.certified.moleculeGraph.underlyingSimpleGraph.Walk w a)
    (parts : toWalk walk = pre.append post) :
    node.duplicateRootDistance w = pre.length := by
  have hist : node.history.reverse = pre.support ++ post.support.tail := by
    rw [← support_toWalk walk,parts,Walk.support_append]
  obtain ⟨k,_,idx,bound,lookup⟩ := OutwardRule1bObserverEquivalence.duplicateRootDistance_eq_firstIndex node w seen
  have nd := (RingClosureCycle.isPath_toWalk walk).support_nodup
  rw [support_toWalk] at nd
  have hk : k < node.history.reverse.length := by simpa using bound
  have hx := nd.idxOf_getElem k hk
  have get : node.history.reverse[k] = w := by simpa only [List.getElem?_eq_getElem hk,Option.some.injEq] using lookup
  rw [get] at hx
  rw [idx,←hx,hist,List.idxOf_append_of_mem pre.end_mem_support]
  have preNd : pre.support.Nodup := (List.nodup_append.mp (hist ▸ nd)).1
  simpa only [Walk.support_getElem_length] using preNd.idxOf_getElem pre.length (by simp)

/-- Extract the graph cycle and its whole access path from a genuine carrier
leaf. This step makes no assumption on the number of cycles. -/
theorem closure_access {i : Input} {r : i.certified.Atom} {node addr}
    (leg : LegitimateOccurrence i.certified r node addr) {d : Nat}
    (duplicate : node.provenance = .ringDuplicate d) :
    ∃ w, ∃ p : i.certified.moleculeGraph.underlyingSimpleGraph.Walk r w,
      ∃ t : i.certified.moleculeGraph.underlyingSimpleGraph.Walk w w,
      p.IsPath ∧ t.IsCycle ∧ (∀ x ∈ p.support, x ∈ t.support → x = w) ∧
        originPath node d = p.support ∧ d = p.length := by
  cases leg with
  | simple path =>
    rw [i.certified.simpleOccurrencePath_provenance path] at duplicate
    contradiction
  | @multiple parent _ a w k path observed adj lt pos =>
    rw [i.certified.legitimateOccurrence_multiple_provenance pos] at duplicate
    contradiction
  | @ring parent _ a w path observed adj notParent seen =>
    rw [i.certified.legitimateOccurrence_ring_provenance seen] at duplicate
    cases duplicate
    obtain ⟨v,hv,walk⟩ := ofSimple (i := i) path
    obtain rfl := Option.some.inj (hv.symm.trans observed)
    obtain ⟨p,t,parts,hp,_,closed,meet⟩ :=
      RingClosureCycle.path_split_closure walk seen adj (by rwa [parent_get])
    have idx := origin_index walk seen p t parts
    refine ⟨w,p,t.concat adj,hp,closed,meet,?_,idx⟩
    have h := support_toWalk walk
    rw [parts, Walk.support_append] at h
    simp only [originPath,OfficialCIPNode.extend_history,List.tail_cons,←h,idx,
      ← p.length_support, List.take_left]

private theorem access {i : Input} {r c : i.certified.Atom}
    (cyc : i.certified.moleculeGraph.underlyingSimpleGraph.Walk c c) (one : UniqueCycleSupport cyc)
    {node addr} (leg : LegitimateOccurrence i.certified r node addr) {d : Nat}
    (duplicate : node.provenance = .ringDuplicate d) :
    ∃ w, ∃ p : i.certified.moleculeGraph.underlyingSimpleGraph.Walk r w,
      p.IsPath ∧ FirstEntry {x | x ∈ cyc.support} p ∧ originPath node d = p.support ∧ d = p.length := by
  obtain ⟨w,p,t,hp,closed,meet,idx,length⟩ := closure_access leg duplicate
  have same := one t closed
  refine ⟨w,p,hp,RingCycleEntry.firstEntry_of_intersection _ p hp
    ((same w).mp t.start_mem_support) (fun x hx there => meet x hx ((same x).mpr there)),idx,length⟩

/-- For any two ring duplicates in the same original digraph, both their
stored distance and their full origin occurrence history agree. -/
theorem common_origin {i : Input} {c : i.certified.Atom}
    (cyc : i.certified.moleculeGraph.underlyingSimpleGraph.Walk c c) (one : UniqueCycleSupport cyc)
    {d e : Nat} (x : i.certified.LocalizedCIPOccurrence d) (y : i.certified.LocalizedCIPOccurrence e)
    (root : x.val.root = y.val.root) {u v : Nat}
    (hx : x.val.node.provenance = .ringDuplicate u) (hy : y.val.node.provenance = .ringDuplicate v) :
    originPath x.val.node u = originPath y.val.node v ∧ u = v := by
  obtain ⟨a,p,hp,ep,px,dx⟩ := access cyc one (i.certified.carrierOccurrence_legitimate i.single x) hx
  have ly := i.certified.carrierOccurrence_legitimate i.single y
  rw [←root] at ly
  obtain ⟨b,q,hq,eqn,py,dy⟩ := access cyc one ly hy
  obtain ⟨rfl,he⟩ := RingCycleEntry.unique_first_entry cyc one p q hp hq ep eqn
  cases eq_of_heq he
  exact ⟨px.trans py.symm,dx.trans dy.symm⟩

/-- Every duplicate pair ties both before and after a uniform change of focus.
The focus is fixed for this comparison but otherwise arbitrary. -/
theorem compare_distances {i : Input} {c : i.certified.Atom}
    (cyc : i.certified.moleculeGraph.underlyingSimpleGraph.Walk c c) (one : UniqueCycleSupport cyc)
    {d e : Nat} (x : i.certified.LocalizedCIPOccurrence d) (y : i.certified.LocalizedCIPOccurrence e)
    (root : x.val.root = y.val.root) {u v : Nat}
    (hx : x.val.node.provenance = .ringDuplicate u) (hy : y.val.node.provenance = .ringDuplicate v)
    (focus : List i.certified.Atom) :
    compare u v = .eq ∧ compare (pathDistance focus (originPath x.val.node u))
      (pathDistance focus (originPath y.val.node v)) = .eq := by
  obtain ⟨same,eqn⟩ := common_origin cyc one x y root hx hy
  exact ⟨by rw [eqn]; simp, by rw [same]; simp⟩

end TetraStereo.Engine.RingSingleCycleOrigin
assert_kernel_only TetraStereo.Engine.RingSingleCycleOrigin.common_origin
assert_kernel_only TetraStereo.Engine.RingSingleCycleOrigin.compare_distances
