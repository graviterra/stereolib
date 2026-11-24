import TetraStereo.Engine.RingGroupedStereo
import TetraStereo.Engine.RingSingleTieCompletion

set_option autoImplicit false

namespace TetraStereo.Engine.RingGroupedRanking
open OneCenter RingStereoSiblingPass
open RingRetainedChemicalTrace (Word)
open RingRetainedStereoDecision (ArmProfile Reads First Result accepted seedSign)
open RingRetainedStereoRefinement (bits pairSign)
open RingRetainedSeedFrames (State)
open RingRetainedReferenceGroup (references references_cases)
open RingSingleTieCompletion (unitScore)

attribute [local instance] lexOrd

/-- On equally long molecular queues the lockstep bit comparison is the
ordinary lexicographic order, including equality of the entire queue. -/
theorem bits_order {a b : List Bool} (width : a.length = b.length) :
    RingSeededPairs.compareBits a b = unitScore (compare a b) := by
  induction a generalizing b with
  | nil => cases b <;> first | rfl | simp at width
  | cons x xs ih =>
    cases b with
    | nil => simp at width
    | cons y ys =>
      have rest := ih (Nat.succ.inj width)
      cases x <;> cases y <;> first | exact rest | rfl

def localKey (p : ArmProfile) (rev : Bool) : Nat × List Bool :=
  match references p.hits rev with
  | [s] => (2,bits (p.localPair s).nonterminalStream)
  | [_,_] => (1,p.bestPair)
  | _ => (0,[])

/-- The fixed R word on this geometry determines direction. The S word
determines whether that direction has unit or doubled magnitude. -/
def stereoKey (p : ArmProfile) (rev : Bool) :=
  (p.unit.word,localKey p rev,p.lower.word,accepted p.unit (p.fixedPair .R))

def key (p : ArmProfile) (rev : Bool) := (p.unit.priorDeep,stereoKey p rev)

private theorem prod_cmp {α β : Type} [Ord α] [Ord β] (a c : α) (b d : β) :
    compare (a,b) (c,d) = (compare a c).then (compare b d) := rfl

private theorem from_order (o : Ordering) : compare (unitScore o) 0 = o := by cases o <;> rfl

private theorem best_width {i read rev} (x : State i read rev) :
    x.profile.bestPair.length = x.profile.unit.stream.count 2 := by
  have r := (RingRetainedSeedFrames.widths .R x).2
  have s := (RingRetainedSeedFrames.widths .S x).2
  rcases max_choice (accepted x.profile.unit x.profile.localR) (accepted x.profile.unit x.profile.localS) with h | h
  · exact (congrArg List.length h).trans r
  · exact (congrArg List.length h).trans s

private theorem local_order {i read rev} (a b : State i read rev) (u : a.profile.unit = b.profile.unit)
    {k : Int} (got : RingRetainedStereoDecision.fourB? a.profile b.profile rev = some k) :
    k = unitScore (compare (localKey a.profile rev) (localKey b.profile rev)) := by
  have single (s t : RS) : pairSign (a.profile.localPair s) (b.profile.localPair t) =
      unitScore (compare (bits (a.profile.localPair s).nonterminalStream) (bits (b.profile.localPair t).nonterminalStream)) := by
    apply bits_order
    simp only [bits,List.length_map]
    exact (RingRetainedSeedFrames.nonterminal_width s a).trans ((congrArg (fun z : Branch => z.nonterminalStream.length) u).trans
      (RingRetainedSeedFrames.nonterminal_width t b).symm)
  have dual := bits_order ((best_width a).trans ((congrArg (fun z : Branch => z.stream.count 2) u).trans (best_width b).symm))
  rcases references_cases a.profile.hits rev with l | ⟨s,l⟩ | l <;>
    rcases references_cases b.profile.hits rev with r | ⟨t,r⟩ | r <;>
    simp only [RingRetainedStereoDecision.fourB?,l,r,Option.some.injEq] at got <;>
    first | contradiction | subst k
  all_goals (simp only [localKey,l,r,prod_cmp]; first | apply single | exact dual | rfl)

private theorem combine_order (r s : Int) :
    compare (CentresRing.PairList.combine r s) 0 = compare r 0 := by
  unfold CentresRing.PairList.combine
  split_ifs
  · exact (Int.compare_eq_lt.mpr (by omega)).symm
  · exact (Int.compare_eq_lt.mpr (by omega)).symm
  · exact (Int.compare_eq_gt.mpr (by omega)).symm
  · exact (Int.compare_eq_gt.mpr (by omega)).symm
  · exact congrArg (fun k : Int => compare k 0) (by omega : 0 = r)

/-- Each first-rule derivation on a constitutionally tied pair has the sign
of a single opponent-independent lexicographic key. -/
theorem first_order {i read rev} (a b : State i read rev) {v}
    (constitution : a.profile.unit.priorDeep = b.profile.unit.priorDeep)
    (first : First a.profile b.profile rev v) :
    compare v.score 0 = compare (key a.profile rev) (key b.profile rev) := by
  have earlier (x : a.profile.unit.word = b.profile.unit.word) : a.profile.unit = b.profile.unit :=
    RingRetainedSeedFrames.unit_eq (a := a) (b := b) (congrArg₂ List.append constitution (congrArg List.singleton x))
  have sign (a b : Branch) : compare (RingRetainedUnitPass.signed a b) 0 = compare a.word b.word :=
    from_order _
  simp only [key,stereoKey,prod_cmp,constitution,Std.ReflCmp.compare_self,Ordering.eq_then]
  cases first with
  | unit nz =>
    have ne := fun h => nz ((RingRetainedUnitPass.signed_zero_iff ..).mpr h)
    rw [sign]
    cases h : compare a.profile.unit.word b.profile.unit.word <;> simp_all
  | pairs unit found nz =>
    have l := local_order a b (earlier unit) found
    simp only [unit,Std.ReflCmp.compare_self,Ordering.eq_then]
    rw [l,from_order]
    cases h : compare (localKey a.profile rev) (localKey b.profile rev) <;> simp_all [unitScore]
  | lower unit found nz =>
    have l := local_order a b (earlier unit) found
    have eqn : compare (localKey a.profile rev) (localKey b.profile rev) = .eq :=
      (from_order _).symm.trans (congrArg (fun k : Int => compare k 0) l.symm)
    simp only [unit,Std.ReflCmp.compare_self,Ordering.eq_then,eqn]
    rw [sign]
    have ne := fun h => nz ((RingRetainedUnitPass.signed_zero_iff ..).mpr h)
    cases h : compare a.profile.lower.word b.profile.lower.word <;> simp_all
  | fixed unit found low =>
    have l := local_order a b (earlier unit) found
    have eqn : compare (localKey a.profile rev) (localKey b.profile rev) = .eq :=
      (from_order _).symm.trans (congrArg (fun k : Int => compare k 0) l.symm)
    simp only [unit,low,Std.ReflCmp.compare_self,Ordering.eq_then,eqn,RingRetainedStereoDecision.fixedResult,combine_order]
    have widths := (RingRetainedSeedFrames.widths .R a).1.trans
      ((congrArg (fun z : Branch => z.stream.count 2) (earlier unit)).trans (RingRetainedSeedFrames.widths .R b).1.symm)
    rw [seedSign,bits_order widths,from_order]

end TetraStereo.Engine.RingGroupedRanking

assert_kernel_only TetraStereo.Engine.RingGroupedRanking.first_order
