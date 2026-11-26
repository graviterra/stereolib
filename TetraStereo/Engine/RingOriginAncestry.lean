import TetraStereo.Engine.RingOriginSeparation
import TetraStereo.OneCenter.LocalizedRetainedArmExpansion

/-! When a retained ring-duplicate origin is still on the path from a new
focus to the closure leaf. Paths here identify occurrences, so two visits
to the same molecular atom need not be the same tree vertex. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginAncestry
open RingSingleCycleOrigin (originPath pathDistance shared)

private theorem shared_bounds {V : Type*} [DecidableEq V] (x y : List V) :
    shared x y ≤ x.length ∧ shared x y ≤ y.length := by
  induction x generalizing y with
  | nil => cases y <;> simp [shared]
  | cons a xs ih =>
    cases y with
    | nil => simp [shared]
    | cons b ys =>
      by_cases h : a = b
      · have := ih ys
        simp only [shared,if_pos h,List.length_cons]
        omega
      · simp [shared,h]

private theorem shared_prefix {V : Type*} [DecidableEq V] (x p s : List V) :
    shared x p = min (shared x (p ++ s)) p.length := by
  induction p generalizing x with
  | nil => cases x <;> simp [shared]
  | cons a ps ih =>
    cases x with
    | nil => simp [shared]
    | cons b xs =>
      by_cases h : b = a
      · have := ih xs
        simp only [List.cons_append,shared,if_pos h,List.length_cons]
        omega
      · simp [shared,h]

private theorem shared_append {V : Type*} [DecidableEq V] (p s : List V) :
    shared p (p ++ s) = p.length := by
  induction p with
  | nil => cases s <;> rfl
  | cons a xs ih => simp [shared,ih,Nat.add_comm]

/-- Twice the number of shared steps beyond the origin is exactly the
extra distance incurred by going via it. -/
theorem detour {V : Type*} [DecidableEq V] (focus origin suffix : List V) :
    pathDistance focus origin + pathDistance origin (origin ++ suffix) =
      pathDistance focus (origin ++ suffix) + 2 * (shared focus (origin ++ suffix) - origin.length) := by
  have bound := shared_bounds focus (origin ++ suffix)
  have pre := shared_prefix focus origin suffix
  unfold pathDistance
  rw [shared_append]
  simp only [List.length_append] at *
  omega

/-- For any genuine closure, its original real occurrence is on the unique
focus-to-leaf path exactly when the histories diverge no later than that
origin. This includes a focus in a different branch and the origin itself. -/
theorem closure_between_iff {i : LocalizedChemicalRing.Input} {n d : Nat}
    (q : i.certified.LocalizedCIPOccurrence n)
    (dup : q.val.node.provenance = .ringDuplicate d) (f : RingActivePairs.Site i)
    (_sameRoot : f.val.root = q.val.root) :
    let focus := f.val.node.history.reverse
    let leaf := q.val.node.history.reverse
    let origin := originPath q.val.node d
    pathDistance focus origin + pathDistance origin leaf = pathDistance focus leaf ↔
      shared focus leaf ≤ d + 1 := by
  dsimp only
  obtain ⟨_,_,_,_,len⟩ := RingOriginSeparation.origin_real q dup
  have pref : (originPath q.val.node d) <+: q.val.node.history.reverse := by
    cases h : q.val.node.history with
    | nil => simp [originPath,h]
    | cons a xs =>
      simp only [originPath,h,List.tail_cons,List.reverse_cons]
      exact (List.take_prefix _ _).trans (List.prefix_append _ _)
  obtain ⟨s, hs⟩ := pref
  have eqn := detour f.val.node.history.reverse (originPath q.val.node d) s
  rw [hs,len] at eqn
  omega

open OneCenter
open private CertifiedLocalizedCIPInput.exists_carrier_ring_step
  CertifiedLocalizedCIPInput.duplicateRootDistance_eq_idxOf from TetraStereo.OneCenter.LocalizedRetainedArmExpansion
open private ofSimple from TetraStereo.Engine.RingGraphPaths

/-- Every closure has a real focus at which the original occurrence ceases
to be ancestral. Its immediate molecular parent supplies the witness. -/
theorem every_closure_has_off_path_focus {i : LocalizedChemicalRing.Input} {n d : Nat}
    (q : i.certified.LocalizedCIPOccurrence n)
    (dup : q.val.node.provenance = .ringDuplicate d) :
    ∃ f : RingActivePairs.Site i, f.val.root = q.val.root ∧ f.val.node.provenance = .realAtom ∧
      f.val.node.history = q.val.node.history.tail ∧
      pathDistance f.val.node.history.reverse (originPath q.val.node d) +
        pathDistance (originPath q.val.node d) q.val.node.history.reverse ≠
        pathDistance f.val.node.history.reverse q.val.node.history.reverse := by
  obtain ⟨p,_,a,b,walk,extension,current,adj,_,seen⟩ :=
    CertifiedLocalizedCIPInput.exists_carrier_ring_step i.certified i.single q dup
  obtain ⟨v,hv,path⟩ := ofSimple (i := i) walk
  obtain rfl := Option.some.inj (hv.symm.trans current)
  obtain ⟨root,hist,real,_⟩ := RingGraphPaths.represents_site path
  have idx := CertifiedLocalizedCIPInput.duplicateRootDistance_eq_idxOf i.certified p b (List.mem_reverse.mpr seen)
  have num : p.history.reverse.idxOf b = d := by
    simpa [extension,OfficialCIPNode.extend,OfficialCIPNode.childProvenance,seen,idx] using dup
  refine ⟨RingGraphPaths.site path,root,real,by simpa [extension,OfficialCIPNode.extend_history] using hist,?_⟩
  intro between
  have le := (closure_between_iff q dup _ root).mp between
  rw [hist,extension,OfficialCIPNode.extend_history,List.reverse_cons,shared_append] at le
  have head := RingClosureCycle.history_head path
  cases h : p.history with
  | nil => simp [h] at seen
  | cons x xs =>
    have xa : x = v := by simpa [h] using head
    have ne := i.certified.moleculeGraph.underlyingSimpleGraph.ne_of_adj adj
    have mem : b ∈ xs := by simpa [h,xa,Ne.symm ne] using seen
    have bound := List.idxOf_lt_length_of_mem (List.mem_reverse.mpr mem)
    rw [h,List.reverse_cons,List.idxOf_append_of_mem (List.mem_reverse.mpr mem)] at num
    simp only [h,List.length_reverse,List.length_cons] at le
    simp only [List.length_reverse] at bound
    omega

end TetraStereo.Engine.RingOriginAncestry
assert_kernel_only TetraStereo.Engine.RingOriginAncestry.closure_between_iff
assert_kernel_only TetraStereo.Engine.RingOriginAncestry.every_closure_has_off_path_focus
