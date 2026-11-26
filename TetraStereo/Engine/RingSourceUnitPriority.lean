import TetraStereo.Engine.RingFullPathEligibility
import TetraStereo.Engine.RingFullPathTrialReadings

/-! The first actual unit observation decides a constitutional tie before every
later full-path suffix and every promotion mark. Frozen `some none` observations
are included in the publication-unavailable source class. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingSourceUnitPriority
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader Labels unit sourceClass)
open RingRetainedChemicalTrace (Word)
open RingFullPathEligibility (Key Reads)
open RingFullPathTrialReadings (trialKey)
attribute [local instance] lexOrd

private theorem compare_after {α : Type} [Ord α] [Std.ReflCmp (compare : α → α → Ordering)]
    (pre x y : List α) : compare (pre ++ x) (pre ++ y) = compare x y := by
  induction pre with
  | nil => rfl
  | cons h hs ih => simpa only [List.cons_append,List.compare_cons_cons,
      Std.ReflCmp.compare_self,Ordering.eq_then] using ih

/-- The full key contains the actual root observation as its first Rule 4a
entry, after the complete preceding molecular constitutional word. -/
theorem root_observation {i : Input} {r : Reader i} {rev : Bool} {q : Arm i}
    {c : RingRetainedChemicalTrace.Key} {k : Key} {v : Option Labels}
    (native : RingRetainedChemicalTrace.key? i q = some c)
    (seen : r q.occurrence = some v) (actual : Reads i r rev q k) :
    ∃ rest : Word, k.throughFourA = RingRetainedChemicalPreorder.orderWord c ++
      [([unit (v.map fun p => if rev then p.2 else p.1)] :: rest)] := by
  obtain ⟨u,l,ar,as',fr,du,_,_,_,_,rfl⟩ := actual
  cases du with
  | node constitution observed physical lookup complete below shallow deep =>
    obtain rfl := Option.some.inj (native.symm.trans constitution)
    obtain rfl := Option.some.inj (seen.symm.trans observed)
    exact ⟨_,rfl⟩

/-- On two actual molecular readings, different first observed unit classes
settle the native full trial comparison. All later rules and arbitrary mark
words are retained in the compared keys, and cannot change this decision. -/
theorem trial_comparison {i : Input} {r : Reader i} {rev : Bool} {a b : Arm i}
    {ca cb : RingRetainedChemicalTrace.Key} {ka kb : Key} {va vb : Option Labels}
    (left : RingRetainedChemicalTrace.key? i a = some ca)
    (right : RingRetainedChemicalTrace.key? i b = some cb)
    (tied : RingRetainedChemicalPreorder.orderWord ca = RingRetainedChemicalPreorder.orderWord cb)
    (seenA : r a.occurrence = some va) (seenB : r b.occurrence = some vb)
    (actualA : Reads i r rev a ka) (actualB : Reads i r rev b kb)
    (different : Rule4bSparseSource.sourceRule4aGateDecision
      (sourceClass (va.map fun p => if rev then p.2 else p.1))
      (sourceClass (vb.map fun p => if rev then p.2 else p.1)) ≠ .eq)
    (ma mb : Word) :
    compare (trialKey ka ma) (trialKey kb mb) =
      Rule4bSparseSource.sourceRule4aGateDecision
        (sourceClass (va.map fun p => if rev then p.2 else p.1))
        (sourceClass (vb.map fun p => if rev then p.2 else p.1)) := by
  obtain ⟨ra,ha⟩ := root_observation left seenA actualA
  obtain ⟨rb,hb⟩ := root_observation right seenB actualB
  rw [RingNestedActivePair.unit_pair] at different ⊢
  unfold trialKey
  rw [ha,hb,← tied,List.compare_cons_cons,compare_after,List.compare_cons_cons,
    List.compare_cons_cons]
  cases h : compare (unit (va.map fun p => if rev then p.2 else p.1))
      (unit (vb.map fun p => if rev then p.2 else p.1)) <;> simp_all

/-- Every pair of genuine valid rooted arms on a ready reader has executable
native full keys with the first-observation Rule 4a comparison, on either
geometry and for every pair of promotion mark words. No comparison output is
assumed as input. -/
theorem native_trial_comparison {i : Input} {f : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) (rev : Bool) (a b : Arm i)
    (validA : i.certified.LocalizedRerootCursorValid a)
    (validB : i.certified.LocalizedRerootCursorValid b)
    (onA : a.occurrence.val.root = f.val.root) (onB : b.occurrence.val.root = f.val.root)
    {ca cb : RingRetainedChemicalTrace.Key} {va vb : Option Labels}
    (left : RingRetainedChemicalTrace.key? i a = some ca)
    (right : RingRetainedChemicalTrace.key? i b = some cb)
    (tied : RingRetainedChemicalPreorder.orderWord ca = RingRetainedChemicalPreorder.orderWord cb)
    (seenA : r a.occurrence = some va) (seenB : r b.occurrence = some vb)
    (different : Rule4bSparseSource.sourceRule4aGateDecision
      (sourceClass (va.map fun p => if rev then p.2 else p.1))
      (sourceClass (vb.map fun p => if rev then p.2 else p.1)) ≠ .eq) :
    ∃ ka kb, RingFullPathEligibility.key? i r rev a = some ka ∧
      RingFullPathEligibility.key? i r rev b = some kb ∧
      ∀ ma mb : Word, compare (trialKey ka ma) (trialKey kb mb) =
        Rule4bSparseSource.sourceRule4aGateDecision
          (sourceClass (va.map fun p => if rev then p.2 else p.1))
          (sourceClass (vb.map fun p => if rev then p.2 else p.1)) := by
  obtain ⟨ka,ha,sa⟩ := RingFullPathEligibility.key_exact ready rev a validA onA
  obtain ⟨kb,hb,sb⟩ := RingFullPathEligibility.key_exact ready rev b validB onB
  exact ⟨ka,kb,ha,hb,trial_comparison left right tied seenA seenB
    ((sa ka).mpr rfl) ((sb kb).mpr rfl) different⟩

end TetraStereo.Engine.RingSourceUnitPriority
assert_kernel_only TetraStereo.Engine.RingSourceUnitPriority.root_observation
assert_kernel_only TetraStereo.Engine.RingSourceUnitPriority.trial_comparison
assert_kernel_only TetraStereo.Engine.RingSourceUnitPriority.native_trial_comparison
