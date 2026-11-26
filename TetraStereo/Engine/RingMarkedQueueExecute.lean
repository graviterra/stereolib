import TetraStereo.Engine.RingMarkedQueueSites
import TetraStereo.Engine.RingMarkedQueueComparison

/-! A deterministic simultaneous breadth-first Rule 6 traversal. Only the two
current child-bit rows are compared. Equal deep rows enqueue physical cursor
pairs; no flattened marked word is compared by this implementation. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingMarkedQueueExecute
open OneCenter CertifiedLocalizedCIPInput RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingMarkedQueueSites (Slot Good Allowed child? pop?)
open RingMarkedQueueComparison (Runs RootRuns)
attribute [local instance] lexOrd

abbrev Pair (i : Input) := Slot i × Slot i
private def left {i : Input} (ps : List (Pair i)) := ps.map (fun p => p.1.2)
private def right {i : Input} (ps : List (Pair i)) := ps.map (fun p => p.2.2)
private def bits {i : Input} (ps : List (Slot i)) := ps.map (fun p => p.2.value)

inductive Sweep (i : Input) where
  | decided (out : Ordering)
  | next (frontier : List (Pair i))

/-- Scan one sphere in FIFO order; child pairs are retained only after both
concrete rows tie. Errors in either demanded molecular expansion propagate. -/
def sphere? (i : Input) (r : Reader i) (atom : Nat) : List (Pair i) → Option (Sweep i)
  | [] => some (.next [])
  | p::ps => do
    let (sa,da) ← pop? i r atom p.1.1
    let (sb,db) ← pop? i r atom p.2.1
    let sh := compare (bits sa) (bits sb)
    if sh ≠ .eq then return .decided sh
    let de := compare (bits da) (bits db)
    if de ≠ .eq then return .decided de
    match ← sphere? i r atom ps with
    | .decided out => return .decided out
    | .next qs => return .next (da.zip db ++ qs)

/-- A sphere budget bounds traversal depth, independently of the number of
physical occurrences in each frontier. -/
def spheres? (i : Input) (r : Reader i) (atom : Nat) : Nat → List (Pair i) → Option Ordering
  | _,[] => some .eq
  | 0,_::_ => none
  | n+1,p::ps => do
    match ← sphere? i r atom (p::ps) with
    | .decided out => return out
    | .next qs => spheres? i r atom n qs

/-- The root's own preference is inspected before either frontier is expanded. -/
def run? (i : Input) (r : Reader i) (atom : Nat) (a b : Slot i) : Option Ordering :=
  let head := compare a.2.value b.2.value
  if head ≠ .eq then some head
  else spheres? i r atom (i.certified.localizedRerootCursorBudget a.1 + 1) [(a,b)]

/-- Initial payload contains only the actual selected-atom bit. Molecular
child priorities are decoded only when an equal head demands a child row. -/
private def placeholder {i : Input} (atom : Nat) (q : Arm i) : Slot i :=
  (q,⟨[],[],RingGroupedMark.bit atom q,[]⟩)

def compare? (i : Input) (r : Reader i) (atom : Nat) (a b : Arm i) : Option Ordering :=
  run? i r atom (placeholder atom a) (placeholder atom b)

private theorem sphere_singleton (i : Input) (r : Reader i) (atom : Nat) (a b : Arm i)
    (x y u v : Branch) :
    sphere? i r atom [((a,x),(b,y))] = sphere? i r atom [((a,u),(b,v))] := rfl

private theorem spheres_singleton (i : Input) (r : Reader i) (atom n : Nat) (a b : Arm i)
    (x y u v : Branch) :
    spheres? i r atom n [((a,x),(b,y))] = spheres? i r atom n [((a,u),(b,v))] := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [spheres?]
    rw [sphere_singleton i r atom a b x y u v]

private theorem run_congr (i : Input) (r : Reader i) (atom : Nat) (a b : Arm i)
    (x y u v : Branch) (hx : x.value = u.value) (hy : y.value = v.value) :
    run? i r atom (a,x) (b,y) = run? i r atom (a,u) (b,v) := by
  dsimp only [run?]
  rw [hx,hy]
  exact congrArg (fun z => if compare u.value v.value ≠ .eq then some (compare u.value v.value) else z)
    (spheres_singleton i r atom _ a b x y u v)

private def Bound {i : Input} (f : Site i) (r : Reader i) (atom n : Nat) (ps : List (Pair i)) :=
  ∀ p ∈ ps, Good f r atom p.1 ∧ Good f r atom p.2 ∧
    i.certified.localizedRerootCursorBudget p.1.1 < n

private def NextBound {i : Input} (f : Site i) (r : Reader i) (atom n : Nat) : Sweep i → Prop
  | .decided _ => True
  | .next ps => Bound f r atom n ps

private def Spec {i : Input} (f : Site i) (r : Reader i) (atom : Nat) (ps : List (Pair i)) : Sweep i → Prop
  | .decided out => ∀ ws : List (Pair i),
      Runs (Allowed f r atom) (Allowed f r atom) (left ps) (left ws) (right ps) (right ws) out
  | .next qs => ∀ (ws : List (Pair i)) out,
      Runs (Allowed f r atom) (Allowed f r atom) [] (left (ws++qs)) [] (right (ws++qs)) out →
      Runs (Allowed f r atom) (Allowed f r atom) (left ps) (left ws) (right ps) (right ws) out

private theorem zip_sides {i : Input} (as bs : List (Slot i)) (size : as.length = bs.length) :
    left (as.zip bs) = as.map Prod.snd ∧ right (as.zip bs) = bs.map Prod.snd := by
  constructor
  · have h := List.map_fst_zip (l₁ := as) (l₂ := bs) (Nat.le_of_eq size)
    simpa only [left,List.map_map,Function.comp_def] using congrArg (List.map Prod.snd) h
  · have h := List.map_snd_zip (l₁ := as) (l₂ := bs) (Nat.le_of_eq size.symm)
    simpa only [right,List.map_map,Function.comp_def] using congrArg (List.map Prod.snd) h

private theorem sphere_ready {i : Input} {f : Site i} {r : Reader i} {atom n : Nat}
    (ready : RingGroupedStereo.Ready f r) (ps : List (Pair i)) (bound : Bound f r atom (n+1) ps) :
    ∃ s, sphere? i r atom ps = some s ∧ Spec f r atom ps s ∧ NextBound f r atom n s := by
  induction ps with
  | nil =>
    refine ⟨.next [],rfl,?_,by simp [NextBound,Bound]⟩
    intro ws out run
    simpa only [left,right,List.map_nil,List.append_nil] using run
  | cons p ps ih =>
    obtain ⟨ga,gb,budget⟩ := bound p List.mem_cons_self
    obtain ⟨sa,da,ha,psa,pda,layoutA,belowA⟩ := RingMarkedQueueSites.pop_ready ready ga
    obtain ⟨sb,db,hb,psb,pdb,layoutB,belowB⟩ := RingMarkedQueueSites.pop_ready ready gb
    have la : Allowed f r atom p.1.2 (sa.map Prod.snd) (da.map Prod.snd) :=
      ⟨p.1.1,sa,da,ga,ha,rfl,rfl⟩
    have lb : Allowed f r atom p.2.2 (sb.map Prod.snd) (db.map Prod.snd) :=
      ⟨p.2.1,sb,db,gb,hb,rfl,rfl⟩
    by_cases sh : compare (bits sa) (bits sb) ≠ .eq
    · refine ⟨.decided (compare (bits sa) (bits sb)),?_,?_,True.intro⟩
      · simp only [sphere?,ha,hb,bind,pure,Option.bind_some,if_pos sh]
      · intro ws
        have go : Runs (Allowed f r atom) (Allowed f r atom)
            (p.1.2::left ps) (left ws) (p.2.2::right ps) (right ws)
            (compare ((sa.map Prod.snd).map Branch.value) ((sb.map Prod.snd).map Branch.value)) :=
          .shallow la lb (by simpa only [bits,List.map_map,Function.comp_def] using sh)
        simpa only [left,right,List.map_cons,bits,List.map_map,Function.comp_def] using go
    · have shEq : compare (bits sa) (bits sb) = .eq := Classical.not_not.mp sh
      by_cases de : compare (bits da) (bits db) ≠ .eq
      · refine ⟨.decided (compare (bits da) (bits db)),?_,?_,True.intro⟩
        · simp only [sphere?,ha,hb,bind,pure,Option.bind_some,if_neg sh,if_pos de]
        · intro ws
          have go : Runs (Allowed f r atom) (Allowed f r atom)
              (p.1.2::left ps) (left ws) (p.2.2::right ps) (right ws)
              (compare ((da.map Prod.snd).map Branch.value) ((db.map Prod.snd).map Branch.value)) :=
            .deep la lb (by simpa only [bits,List.map_map,Function.comp_def] using shEq)
              (by simpa only [bits,List.map_map,Function.comp_def] using de)
          simpa only [left,right,List.map_cons,bits,List.map_map,Function.comp_def] using go
      · have deEq : compare (bits da) (bits db) = .eq := Classical.not_not.mp de
        have size : da.length = db.length := by
          have h := congrArg List.length (Std.compare_eq_eq_iff_eq.mp deEq)
          simpa only [bits,List.length_map] using h
        have sides := zip_sides da db size
        have lift (ws : List (Pair i)) {out}
            (run : Runs (Allowed f r atom) (Allowed f r atom)
              (left ps) (left (ws++da.zip db)) (right ps) (right (ws++da.zip db)) out) :
            Runs (Allowed f r atom) (Allowed f r atom)
              (left (p::ps)) (left ws) (right (p::ps)) (right ws) out := by
          have clean : Runs (Allowed f r atom) (Allowed f r atom)
              (left ps) (left ws ++ da.map Prod.snd) (right ps) (right ws ++ db.map Prod.snd) out := by
            simpa only [left,right,List.map_append,← sides.1,← sides.2] using run
          exact .next la lb (by simpa only [bits,List.map_map,Function.comp_def] using shEq)
            (by simpa only [bits,List.map_map,Function.comp_def] using deEq) clean
        obtain ⟨s,hs,spec,next⟩ := ih (fun q hq => bound q (.tail _ hq))
        cases s with
        | decided out =>
          refine ⟨.decided out,?_,?_,True.intro⟩
          · simp only [sphere?,ha,hb,bind,pure,Option.bind_some,if_neg sh,if_neg de,hs]
          · intro ws
            exact lift ws (spec (ws++da.zip db))
        | next qs =>
          refine ⟨.next (da.zip db ++ qs),?_,?_,?_⟩
          · simp only [sphere?,ha,hb,bind,pure,Option.bind_some,if_neg sh,if_neg de,hs]
          · intro ws out run
            apply lift ws
            apply spec (ws++da.zip db) out
            simpa only [List.append_assoc] using run
          · intro q hq
            rcases List.mem_append.mp hq with hz | hq
            · have mem := List.of_mem_zip hz
              exact ⟨(belowA _ mem.1).1,(belowB _ mem.2).1,by
                have smaller := (belowA _ mem.1).2
                omega⟩
            · exact next q hq

private theorem rotate {i : Input} {f : Site i} {r : Reader i} {atom : Nat}
    {order : Ordering} (ps : List (Pair i))
    (run : Runs (Allowed f r atom) (Allowed f r atom) (left ps) [] (right ps) [] order) :
    Runs (Allowed f r atom) (Allowed f r atom) [] (left ps) [] (right ps) order := by
  cases ps with
  | nil => exact run
  | cons p ps => exact .rotate_left (.rotate_right run)

private theorem spheres_ready {i : Input} {f : Site i} {r : Reader i} {atom : Nat}
    (ready : RingGroupedStereo.Ready f r) : ∀ n (ps : List (Pair i)), Bound f r atom n ps →
      ∃ out, spheres? i r atom n ps = some out ∧
        Runs (Allowed f r atom) (Allowed f r atom) (left ps) [] (right ps) [] out := by
  intro n
  induction n with
  | zero =>
    intro ps bound
    have empty : ps = [] := by
      cases ps with
      | nil => rfl
      | cons p ps => have h := (bound p List.mem_cons_self).2.2; omega
    subst ps
    exact ⟨.eq,rfl,.stop⟩
  | succ n ih =>
    intro ps bound
    cases ps with
    | nil => exact ⟨.eq,rfl,.stop⟩
    | cons p ps =>
      obtain ⟨s,hs,spec,next⟩ := sphere_ready ready (p::ps) bound
      cases s with
      | decided out =>
        exact ⟨out,by simp [spheres?,hs,bind,pure],spec []⟩
      | next qs =>
        obtain ⟨out,ho,run⟩ := ih qs next
        refine ⟨out,by simp [spheres?,hs,ho,bind,pure],?_⟩
        exact spec [] out (rotate qs run)

/-- Ready physical slots terminate with one sphere of fuel beyond the left
cursor budget, and produce a witness of the operational two-queue relation. -/
theorem ready_run {i : Input} {f : Site i} {r : Reader i} {atom : Nat}
    (ready : RingGroupedStereo.Ready f r) (a b : Slot i)
    (ga : Good f r atom a) (gb : Good f r atom b) :
    ∃ out, run? i r atom a b = some out ∧ RootRuns (Allowed f r atom) (Allowed f r atom) a.2 b.2 out := by
  by_cases h : compare a.2.value b.2.value ≠ .eq
  · exact ⟨_,by simp [run?,h],.head h⟩
  · obtain ⟨out,found,run⟩ := spheres_ready ready
      (i.certified.localizedRerootCursorBudget a.1+1) [(a,b)] (by
        intro p hp
        obtain rfl := List.mem_singleton.mp hp
        exact ⟨ga,gb,Nat.lt_succ_self _⟩)
    exact ⟨out,by simp [run?,h,found],.tail (Classical.not_not.mp h) run⟩

private theorem allowed_width {i : Input} {f : Site i} {r : Reader i} {atom : Nat}
    (ready : RingGroupedStereo.Ready f r) {b sh de} (h : Allowed f r atom b sh de) : sh.length = de.length := by
  obtain ⟨q,ss,ds,good,got,rfl,rfl⟩ := h
  obtain ⟨sa,da,found,pa,pb,_,_⟩ := RingMarkedQueueSites.pop_ready ready good
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (got.symm.trans found))
  simpa only [List.length_map] using pa.length_eq.trans pb.length_eq.symm

/-- All three comparison outcomes, including an exhausted full tie, are exactly
the full marked-word comparison. -/
theorem word_exact {i : Input} {f : Site i} {r : Reader i} {atom : Nat}
    (ready : RingGroupedStereo.Ready f r) (a b : Slot i)
    (ga : Good f r atom a) (gb : Good f r atom b) :
    run? i r atom a b = some (compare a.2.word b.2.word) := by
  obtain ⟨out,found,run⟩ := ready_run ready a b ga gb
  have same := run.sound (fun _ _ _ h => RingMarkedQueueSites.allowed_layout ready h) (fun _ _ _ h => RingMarkedQueueSites.allowed_layout ready h)
    (fun _ _ _ h => allowed_width ready h) (fun _ _ _ h => allowed_width ready h)
  rw [← same] at found
  exact found

/-- Public molecular arms need no caller-supplied traversal or sorted rows. -/
theorem compare_readings {i : Input} {f : Site i} {r : Reader i} {atom : Nat}
    (ready : RingGroupedStereo.Ready f r) {a b : Arm i} {x y : Branch}
    (va : RingRule5Shape.Valid a) (vb : RingRule5Shape.Valid b)
    (oa : RingRule5Shape.On f a) (ob : RingRule5Shape.On f b)
    (ma : RingGroupedMark.Reading i r atom a x) (mb : RingGroupedMark.Reading i r atom b y) :
    compare? i r atom a b = some (compare x.word y.word) := by
  have hx : x.value = RingGroupedMark.bit atom a := by cases ma; rfl
  have hy : y.value = RingGroupedMark.bit atom b := by cases mb; rfl
  have transport := run_congr i r atom a b (placeholder atom a).2 (placeholder atom b).2 x y hx.symm hy.symm
  exact transport.trans (word_exact ready (a,x) (b,y) ⟨va,oa,ma⟩ ⟨vb,ob,mb⟩)

/-- The executable paired traversal is the complete native marked comparator
on every ready original-root pair, including equality. -/
theorem compare_exact {i : Input} {f : Site i} {r : Reader i} {atom : Nat}
    (ready : RingGroupedStereo.Ready f r) (a b : Arm i)
    (va : RingRule5Shape.Valid a) (vb : RingRule5Shape.Valid b)
    (oa : RingRule5Shape.On f a) (ob : RingRule5Shape.On f b) :
    compare? i r atom a b =
      (do let x ← RingGroupedMark.arm? i r atom a
          let y ← RingGroupedMark.arm? i r atom b
          pure (compare x.2.word y.2.word)) := by
  obtain ⟨x,hx⟩ := RingGroupedMark.arm_ready ready atom a va oa
  obtain ⟨y,hy⟩ := RingGroupedMark.arm_ready ready atom b vb ob
  simpa [hx,hy,bind,pure] using compare_readings ready va vb oa ob
    (RingGroupedMark.arm_source hx).2 (RingGroupedMark.arm_source hy).2

/-- Neither an unbounded search nor an unresolved outcome is needed on ready
molecular arms: all three results return within the explicit sphere budget. -/
theorem total {i : Input} {f : Site i} {r : Reader i} {atom : Nat}
    (ready : RingGroupedStereo.Ready f r) (a b : Arm i)
    (va : RingRule5Shape.Valid a) (vb : RingRule5Shape.Valid b)
    (oa : RingRule5Shape.On f a) (ob : RingRule5Shape.On f b) :
    ∃ out, compare? i r atom a b = some out := by
  obtain ⟨x,hx⟩ := RingGroupedMark.arm_ready ready atom a va oa
  obtain ⟨y,hy⟩ := RingGroupedMark.arm_ready ready atom b vb ob
  exact ⟨_,compare_readings ready va vb oa ob
    (RingGroupedMark.arm_source hx).2 (RingGroupedMark.arm_source hy).2⟩

end TetraStereo.Engine.RingMarkedQueueExecute
assert_kernel_only TetraStereo.Engine.RingMarkedQueueExecute.ready_run
assert_kernel_only TetraStereo.Engine.RingMarkedQueueExecute.word_exact
assert_kernel_only TetraStereo.Engine.RingMarkedQueueExecute.compare_readings

assert_kernel_only TetraStereo.Engine.RingMarkedQueueExecute.compare_exact
assert_kernel_only TetraStereo.Engine.RingMarkedQueueExecute.total
