import TetraStereo.Engine.RingMarkedQueueSites
import TetraStereo.Engine.RingMarkedQueueExecute

/-! The ordinary comparison and early-exit marked traversal on the actual
public ring store. The statement ranges over roots and recursive calls. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingMarkedQueuePublic
open OneCenter RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingNestedActivePair (Reader)
open RingRule5Shape (Valid On)
open RingRetainedChemicalTrace (Word)
open RingFullPathEligibility (Key key?)
open RingFullPathTrialReadings (bitWord trialKey)
open RingMarkedQueueSites (child? Allowed allowed_layout)
open RingMarkedQueueComparison (RootRuns)
open private cmp_append from TetraStereo.Engine.RingRebuiltStereo
attribute [local instance] lexOrd

def earlier (k : Key) : List (List Word) :=
  [k.throughFourA,[bitWord k.bestFourB],[k.fourC],[bitWord k.fixedR]]

private theorem trial_split (k l : Key) (x y : Word) :
    compare (trialKey k x) (trialKey l y) = (compare (earlier k) (earlier l)).then (compare x y) := by
  change compare (earlier k ++ [[x]]) (earlier l ++ [[y]]) = _
  rw [cmp_append (earlier k) (earlier l) [[x]] [[y]] rfl]
  cases h : compare x y <;> simp [List.compare_cons_cons,h]

/-- Read only the earlier priority first. A strict result terminates the trial.
After a tie, generate child rows from the unordered marked molecular trees. -/
def Trial {i : Input} (f : Site i) (r : Reader i) (rev : Bool) (atom : Nat)
    (a b : Arm i) (out : Ordering) : Prop :=
  ∃ k l, key? i r rev a = some k ∧ key? i r rev b = some l ∧
    ((compare (earlier k) (earlier l) ≠ .eq ∧ compare (earlier k) (earlier l) = out) ∨
     (compare (earlier k) (earlier l) = .eq ∧ ∃ x y,
       child? i r atom a = some (a,x) ∧ child? i r atom b = some (b,y) ∧
       RootRuns (Allowed f r atom) (Allowed f r atom) x y out))

def native (i : Input) (r : Reader i) (rev : Bool) (atom : Nat) (a b : Arm i) := do
  let k ← key? i r rev a
  let l ← key? i r rev b
  let x ← RingGroupedMark.arm? i r atom a
  let y ← RingGroupedMark.arm? i r atom b
  return compare (trialKey k x.2.word) (trialKey l y.2.word)

private theorem allowed_width {i : Input} {f : Site i} {r : Reader i} {atom : Nat}
    (ready : RingGroupedStereo.Ready f r) {b sh de} (h : Allowed f r atom b sh de) :
    sh.length = de.length := by
  obtain ⟨q,ss,ds,good,found,rfl,rfl⟩ := h
  obtain ⟨s,d,got,ps,pd,_,_⟩ := RingMarkedQueueSites.pop_ready ready good
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (found.symm.trans got))
  simpa only [List.length_map] using ps.length_eq.trans pd.length_eq.symm

private theorem child_read {i f r atom q b} (ready : @RingGroupedStereo.Ready i f r)
    (v : Valid q) (on : On f q) (read : RingGroupedMark.Reading i r atom q b) :
    child? i r atom q = some (q,b) := by
  simp only [child?,RingMarkedTreeOrder.reconstruct_reading ready _ v on (Nat.lt_succ_self _) read]
  rfl

/-- All three outputs are characterized, including a completed tie. No
hypothesis describes the earlier order, marked radius, or helper's output. -/
theorem trial_exact {i f r} (ready : @RingGroupedStereo.Ready i f r)
    (rev : Bool) (atom : Nat) (a b : Arm i) (va : Valid a) (vb : Valid b)
    (oa : On f a) (ob : On f b) (out : Ordering) :
    Trial f r rev atom a b out ↔ native i r rev atom a b = some out := by
  obtain ⟨k,hk,_⟩ := RingFullPathEligibility.key_exact ready rev a va oa
  obtain ⟨l,hl,_⟩ := RingFullPathEligibility.key_exact ready rev b vb ob
  obtain ⟨x,hx⟩ := RingGroupedMark.arm_ready ready atom a va oa
  obtain ⟨y,hy⟩ := RingGroupedMark.arm_ready ready atom b vb ob
  have ma := (RingGroupedMark.arm_source hx).2
  have mb := (RingGroupedMark.arm_source hy).2
  have left := child_read ready va oa ma
  have right := child_read ready vb ob mb
  have sound {s} (run : RootRuns (Allowed f r atom) (Allowed f r atom) x.2 y.2 s) :
      compare x.2.word y.2.word = s :=
    run.sound (fun _ _ _ => allowed_layout ready) (fun _ _ _ => allowed_layout ready)
      (fun _ _ _ => allowed_width ready) (fun _ _ _ => allowed_width ready)
  obtain ⟨_,wa⟩ := RingMarkedQueueSites.visits ready (q := a) (b := x.2) ⟨va,oa,ma⟩
  obtain ⟨_,wb⟩ := RingMarkedQueueSites.visits ready (q := b) (b := y.2) ⟨vb,ob,mb⟩
  obtain ⟨s,run⟩ := RingMarkedQueueComparison.root_complete wa wb
  have hs := sound run
  have hn : native i r rev atom a b =
      some ((compare (earlier k) (earlier l)).then (compare x.2.word y.2.word)) := by
    simp only [native,hk,hl,hx,hy,Option.bind_eq_bind,Option.bind_some,Option.pure_def,trial_split]
  rw [hn,Option.some.injEq]
  constructor
  · rintro ⟨u,v,hu,hv,decision⟩
    obtain rfl := Option.some.inj (hk.symm.trans hu)
    obtain rfl := Option.some.inj (hl.symm.trans hv)
    rcases decision with ⟨strict,output⟩ | ⟨tie,p,t,hp,ht,h⟩
    · cases e : compare (earlier k) (earlier l) with
      | lt => exact e.symm.trans output
      | eq => exact (strict e).elim
      | gt => exact e.symm.trans output
    · obtain ⟨_,rfl⟩ := Prod.mk.inj (Option.some.inj (hp.symm.trans left))
      obtain ⟨_,rfl⟩ := Prod.mk.inj (Option.some.inj (ht.symm.trans right))
      simpa only [tie,Ordering.eq_then] using sound h
  · intro output
    refine ⟨k,l,hk,hl,?_⟩
    cases e : compare (earlier k) (earlier l) with
    | lt => exact Or.inl ⟨by decide,by simpa only [e,Ordering.lt_then] using output⟩
    | gt => exact Or.inl ⟨by decide,by simpa only [e,Ordering.gt_then] using output⟩
    | eq =>
      have eqn : s = out := hs.symm.trans (by simpa only [e,Ordering.eq_then] using output)
      exact Or.inr ⟨rfl,x.2,y.2,left,right,eqn ▸ run⟩

/-- At every scheduled public call the molecular queue returns exactly the
public ligand ordering, on either geometry and for every selected atom. -/
theorem public_exact {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {root : i.certified.Atom} {stage : Nat} {f : Site i} (called : RingGlobalComparison.Called i root stage f)
    (rev : Bool) (atom : Nat) (a b : Arm i) (va : Valid a) (vb : Valid b)
    (oa : On f a) (ob : On f b) (out : Ordering) :
    let r := RingGlobalComparison.prior i root stage
    Trial f r rev atom a b out ↔ native i r rev atom a b = some out := by
  dsimp only
  rw [RingGlobalComparison.prior_exact called]
  exact trial_exact (RingChemicalGraphProof.ready geom f) rev atom a b va vb oa ob out

/-- Decide the earlier rules before entering the paired molecular traversal. -/
def evaluate? (i : Input) (r : Reader i) (rev : Bool) (atom : Nat) (a b : Arm i) : Option Ordering := do
  let k ← key? i r rev a
  let l ← key? i r rev b
  let pre : Ordering := compare (earlier k) (earlier l)
  if pre = Ordering.eq then RingMarkedQueueExecute.compare? i r atom a b else pure pre

theorem evaluate_exact {i f r} (ready : @RingGroupedStereo.Ready i f r)
    (rev : Bool) (atom : Nat) (a b : Arm i) (va : Valid a) (vb : Valid b)
    (oa : On f a) (ob : On f b) :
    evaluate? i r rev atom a b = native i r rev atom a b := by
  obtain ⟨k,hk,_⟩ := RingFullPathEligibility.key_exact ready rev a va oa
  obtain ⟨l,hl,_⟩ := RingFullPathEligibility.key_exact ready rev b vb ob
  obtain ⟨x,hx⟩ := RingGroupedMark.arm_ready ready atom a va oa
  obtain ⟨y,hy⟩ := RingGroupedMark.arm_ready ready atom b vb ob
  have queue := RingMarkedQueueExecute.compare_readings ready va vb oa ob
    (RingGroupedMark.arm_source hx).2 (RingGroupedMark.arm_source hy).2
  simp only [evaluate?,native,hk,hl,hx,hy,Option.bind_eq_bind,Option.bind_some,
    Option.pure_def,trial_split,queue]
  cases compare (earlier k) (earlier l) <;> rfl

/-- Equality of the two executable comparators at every actual public store.
No successful execution, radius, sorted frame or strict priority is assumed. -/
theorem evaluate_public {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {root : i.certified.Atom} {stage : Nat} {f : Site i} (called : RingGlobalComparison.Called i root stage f)
    (rev : Bool) (atom : Nat) (a b : Arm i) (va : Valid a) (vb : Valid b)
    (oa : On f a) (ob : On f b) :
    let r := RingGlobalComparison.prior i root stage
    evaluate? i r rev atom a b = native i r rev atom a b := by
  dsimp only
  rw [RingGlobalComparison.prior_exact called]
  exact evaluate_exact (RingChemicalGraphProof.ready geom f) rev atom a b va vb oa ob

end TetraStereo.Engine.RingMarkedQueuePublic
assert_kernel_only TetraStereo.Engine.RingMarkedQueuePublic.trial_exact
assert_kernel_only TetraStereo.Engine.RingMarkedQueuePublic.public_exact
assert_kernel_only TetraStereo.Engine.RingMarkedQueuePublic.evaluate_exact
assert_kernel_only TetraStereo.Engine.RingMarkedQueuePublic.evaluate_public
