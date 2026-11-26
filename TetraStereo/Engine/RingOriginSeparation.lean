import TetraStereo.Engine.RingSingleCycleOrigin

/-! The real sites of the retained digraph distinguish any two different
ring-duplicate origin paths. This applies to each pair on any admitted graph. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginSeparation
open OneCenter CertifiedLocalizedCIPInput SimpleGraph
open LocalizedChemicalRing (Input)
open RingSingleCycleOrigin (originPath pathDistance shared)
open RingActivePairs (Site)

private theorem distance_zero {V : Type*} [DecidableEq V] (x y : List V) :
    pathDistance x y = 0 ↔ x = y := by
  induction x generalizing y with
  | nil => cases y <;> simp [pathDistance, shared]
  | cons a xs ih =>
    cases y with
    | nil => simp [pathDistance, shared]
    | cons b ys =>
      by_cases h : a = b
      · subst b
        simpa [pathDistance, shared, Nat.add_comm 1] using ih ys
      · simp [pathDistance, shared, h]

/-- The stored index identifies a reachable real site at exactly that depth. -/
theorem origin_real {i : Input} {fuel d : Nat} (q : i.certified.LocalizedCIPOccurrence fuel)
    (dup : q.val.node.provenance = .ringDuplicate d) :
    ∃ f : Site i, f.val.root = q.val.root ∧ f.val.node.provenance = .realAtom ∧
      f.val.node.history.reverse = originPath q.val.node d ∧ (originPath q.val.node d).length = d+1 := by
  obtain ⟨_,p,_,hp,_,_,path,depth⟩ :=
    RingSingleCycleOrigin.closure_access (i.certified.carrierOccurrence_legitimate i.single q) dup
  let h := RingClosureCycle.path_of_walk p hp
  obtain ⟨hr,hh,real,_⟩ := RingGraphPaths.represents_site h
  exact ⟨RingGraphPaths.site h,hr,real,by rw [hh, List.reverse_reverse,path],
    by rw [path,depth,p.length_support]⟩

/-- Original depth comparisons agree at every real focus exactly when the
duplicated real occurrences have identical root-first histories. -/
theorem all_real_foci_iff {i : Input} {m n u v : Nat}
    (x : i.certified.LocalizedCIPOccurrence m) (y : i.certified.LocalizedCIPOccurrence n)
    (root : x.val.root = y.val.root) (hx : x.val.node.provenance = .ringDuplicate u)
    (hy : y.val.node.provenance = .ringDuplicate v) :
    (∀ f : Site i, f.val.root = x.val.root → f.val.node.provenance = .realAtom →
      compare u v = compare (pathDistance f.val.node.history.reverse (originPath x.val.node u))
        (pathDistance f.val.node.history.reverse (originPath y.val.node v))) ↔
      originPath x.val.node u = originPath y.val.node v := by
  obtain ⟨a,ar,ha,ax,lx⟩ := origin_real x hx
  obtain ⟨b,br,hb,byPath,ly⟩ := origin_real y hy
  constructor
  · intro all
    by_contra ne
    have left := all a ar ha
    have right := all b (br.trans root.symm) hb
    rw [ax,(distance_zero _ _).mpr rfl] at left
    rw [byPath,(distance_zero (originPath y.val.node v) _).mpr rfl] at right
    have pos := Nat.pos_of_ne_zero (mt (distance_zero _ _).mp ne)
    have rev := Nat.pos_of_ne_zero (mt (distance_zero _ _).mp (Ne.symm ne))
    have lt := left.trans (compare_lt_iff_lt.mpr pos)
    have gt := right.trans (compare_gt_iff_gt.mpr rev)
    simp [lt] at gt
  · intro same f _ _
    have : u = v := by rw [same] at lx; omega
    rw [same,this]
    simp

end TetraStereo.Engine.RingOriginSeparation
assert_kernel_only TetraStereo.Engine.RingOriginSeparation.all_real_foci_iff
