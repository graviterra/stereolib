import TetraStereo.Engine.RingMolecularPairScore

/-! A strict Rule 4b contest after Rule 4a identifies two actual chiral
occurrences in legal, reference-specific molecular traversals. Every earlier
emitted like/unlike decision agrees. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingDecidingPairOccurrence
open OneCenter RingFullPathPairs RingMolecularPairScore
open LocalizedChemicalRing (Input)
open RingNestedActivePair (Reader)
open RingActivePairs (Arm)
open RingFullPathEligibility (Key)
attribute [local instance] lexOrd

private theorem first_bit (xs ys : List Bool) (width : xs.length = ys.length)
    (lt : compare xs ys = .lt) :
    ∃ before xs' ys', xs = before ++ false :: xs' ∧ ys = before ++ true :: ys' := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons a xs ih =>
    cases ys with
    | nil => simp at width
    | cons b ys =>
      have len : xs.length = ys.length := by simpa using width
      by_cases same : a = b
      · subst b
        obtain ⟨p,l,r,hl,hr⟩ := ih ys len (by simpa [List.compare_cons_cons] using lt)
        exact ⟨a::p,l,r,congrArg (a :: ·) hl,congrArg (a :: ·) hr⟩
      · cases a <;> cases b <;> first | contradiction | exact ⟨[],xs,ys,rfl,rfl⟩

private theorem cut_emission {α β : Type} (f : α → Option β) (row : List α)
    (pre : List β) (b : β) (post : List β) (eqn : row.filterMap f = pre ++ b::post) :
    ∃ before u after, row = before ++ u::after ∧ before.filterMap f = pre ∧ f u = some b := by
  induction row generalizing pre with
  | nil => simp at eqn
  | cons u us ih =>
    cases bit : f u with
    | none =>
      obtain ⟨l,v,r,h,p,k⟩ := ih pre (by simpa [List.filterMap_cons,bit] using eqn)
      exact ⟨u::l,v,r,congrArg (u :: ·) h,by simp [bit,p],k⟩
    | some val =>
      cases pre with
      | nil =>
        have ok : val = b := (List.cons.inj (by simpa [List.filterMap_cons,bit] using eqn :
          val :: us.filterMap f = b :: post)).1
        exact ⟨[],u,us,rfl,rfl,bit.trans (congrArg some ok)⟩
      | cons a as =>
        have op := List.cons.inj (by simpa [List.filterMap_cons,bit] using eqn :
          val :: us.filterMap f = a :: (as ++ b::post))
        obtain ⟨l,v,r,h,p,k⟩ := ih as op.2
        exact ⟨u::l,v,r,congrArg (u :: ·) h,by simp [bit,p,op.1],k⟩

private theorem best_read {i : Input} {r : Reader i} {v : Bool} {a : Arm i} {k : Key}
    (e : Evidence i r v a k) : ∃ s, FullSource i r v s a k.bestFourB := by
  rw [e.best]
  rcases le_total e.right e.left with le | le
  · exact ⟨.S,by simpa only [max_eq_right le] using e.sRead⟩
  · exact ⟨.R,by simpa only [max_eq_left le] using e.rRead⟩

theorem first_deciding_occurrences {i : Input} {r : Reader i} {v : Bool} {a b : Arm i} {x y : Key}
    (l : Evidence i r v a x) (h : Evidence i r v b y)
    (tie : x.throughFourA = y.throughFourA) (strict : compare x.bestFourB y.bestFourB = .lt) :
    ∃ s t, ∃ lp rp : List (FullVisit i), ∃ c d : FullVisit i, ∃ lt rt : List (FullVisit i),
      FullWalk i r v s [rootVisit i r v s a] (lp ++ c::lt) ∧
      FullWalk i r v t [rootVisit i r v t b] (rp ++ d::rt) ∧
      lp.filterMap (fun u => likeAt i r v s u.cursor) = rp.filterMap (fun u => likeAt i r v t u.cursor) ∧
      likeAt i r v s c.cursor = some false ∧ likeAt i r v t d.cursor = some true := by
  obtain ⟨s,ls⟩ := best_read l
  obtain ⟨t,rs⟩ := best_read h
  have width := (RingPairWordPopulation.word_length l.inventory ls).trans
    ((RingUnitWordPopulation.Listing.length_eq l.inventory h.inventory l.classRead h.classRead
      (l.earlier.symm.trans (tie.trans h.earlier))).trans (RingPairWordPopulation.word_length h.inventory rs).symm)
  obtain ⟨pre,xx,yy,lword,rword⟩ := first_bit _ _ width strict
  obtain ⟨left,lwalk,lbits⟩ := ls
  obtain ⟨right,rwalk,rbits⟩ := rs
  obtain ⟨lp,c,lt,rowL,beforeL,bitL⟩ := cut_emission _ left pre false xx (lbits.symm.trans lword)
  obtain ⟨rp,d,rt,rowR,beforeR,bitR⟩ := cut_emission _ right pre true yy (rbits.symm.trans rword)
  exact ⟨s,t,lp,rp,c,d,lt,rt,rowL ▸ lwalk,rowR ▸ rwalk,beforeL.trans beforeR.symm,bitL,bitR⟩

end TetraStereo.Engine.RingDecidingPairOccurrence
assert_kernel_only TetraStereo.Engine.RingDecidingPairOccurrence.first_deciding_occurrences
