import TetraStereo.Engine.RingActivePairs

set_option autoImplicit false

namespace TetraStereo.Engine.RingActivePairs
open OneCenter RingSeededPairs
open CentresRing.PairList (combine)

private theorem first_swap (xs : List (Option RS)) :
    (swapWalk xs).findSome? id = (xs.findSome? id).map RS.swap := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [swapWalk] at ih ⊢; assumption

private theorem like_swap (s : RS) (x : Option RS) : like s.swap (x.map RS.swap) = like s x := by
  cases s <;> cases x with
  | none => rfl
  | some x => cases x <;> rfl

theorem local_swap (a b : List (Option RS)) : localSign? (swapWalk a) (swapWalk b) = localSign? a b := by
  unfold localSign?
  rw [first_swap,first_swap]
  cases a.findSome? id <;> cases b.findSome? id <;> simp [swapWalk,Function.comp_def,like_swap]

private theorem accepted_swap (a : List (Option RS)) :
    (swapWalk a).filterMap id = (a.filterMap id).map RS.swap := by
  induction a with
  | nil => rfl
  | cons h t ih => cases h <;> simp [swapWalk] at ih ⊢ <;> exact ih

theorem fixed_swap (s : RS) (a b : List (Option RS)) :
    listSign? s (swapWalk a) (swapWalk b) = listSign? s.swap a b := by
  have test (x : RS) : (x.swap == s) = (x == s.swap) := by cases s <;> cases x <;> rfl
  simp [listSign?,accepted_swap,Function.comp_def,test]

private theorem bits_range (a b : List Bool) : compareBits a b ∈ ([-1,0,1] : List Int) := by
  induction a generalizing b with
  | nil => cases b <;> simp [compareBits]
  | cons x xs ih =>
    cases b with
    | nil => simp [compareBits]
    | cons y ys => cases x <;> cases y <;> simp [compareBits] <;> simpa using ih ys

theorem local_range {a b : List (Option RS)} {v : Int} (h : localSign? a b = some v) :
    v ∈ ([-1,0,1] : List Int) := by
  unfold localSign? at h
  cases ha : a.findSome? id <;> cases hb : b.findSome? id <;> simp [ha,hb] at h
  · subst v; decide
  · subst v; exact bits_range ..

theorem seed_range {a b : List (Option RS)} {x : Int} (h : listSign? .R a b = some x) :
    x ∈ ([-1,0,1] : List Int) := by
  dsimp only [listSign?] at h
  split at h
  · obtain rfl := Option.some.inj h
    exact bits_range ..
  · contradiction

/-- With source order fixed at each sibling frame, arbitrary-length uppercase publication
sequences have a sharp casing rule. A strict Rule 4b sign survives inversion with magnitude
one. After a Rule 4b tie the signed Rule 5 result reverses and has magnitude zero or two. -/
theorem ordered_scores {i f l r} (p : OrderedPair i f l r) {d : Decision} (got : p.decision? false = some d) :
    (d.rule5 = none ∧ score d ∈ ([-1,1] : List Int) ∧
        (p.decision? true).map score = some (score d)) ∨
    (d.rule4b = 0 ∧ score d ∈ ([-2,0,2] : List Int) ∧
        (p.decision? true).map score = some (-score d)) := by
  let a := descriptorWalk p.left
  let b := descriptorWalk p.right
  change fromVisits? a b a b a b = some d at got
  change _ ∨ _
  cases h : localSign? a b with
  | none => simp [fromVisits?,h] at got
  | some first =>
    have source := local_range h
    have mirror : localSign? (swapWalk a) (swapWalk b) = some first := (local_swap a b).trans h
    by_cases z : first = 0
    · subst first
      cases fixed : listSign? .R a b with
      | none => simp [fromVisits?,h,fixed] at got
      | some x =>
        have other : listSign? .S a b = some (-x) := by simp [two_seed_sign,fixed]
        have revR : listSign? .R (swapWalk a) (swapWalk b) = some (-x) := (fixed_swap .R a b).trans other
        have revS : listSign? .S (swapWalk a) (swapWalk b) = some x := (fixed_swap .S a b).trans fixed
        have obs : d = ⟨0,some (combine x (-x))⟩ := by simpa [fromVisits?,h,fixed,other,eq_comm] using got
        subst d
        right
        change _ ∧ _ ∧ (fromVisits? (swapWalk a) (swapWalk b) (swapWalk a) (swapWalk b)
          (swapWalk a) (swapWalk b)).map score = _
        have vals := seed_range fixed
        simp only [List.mem_cons,List.not_mem_nil,or_false] at vals
        rcases vals with rfl | rfl | rfl <;> simp [fromVisits?,mirror,revR,revS,score,combine]
    · have obs : d = ⟨first,none⟩ := by simpa [fromVisits?,h,z,eq_comm] using got
      subst d
      left
      change _ ∧ _ ∧ (fromVisits? (swapWalk a) (swapWalk b) (swapWalk a) (swapWalk b)
        (swapWalk a) (swapWalk b)).map score = _
      simp_all [fromVisits?,score]

end TetraStereo.Engine.RingActivePairs

assert_kernel_only TetraStereo.Engine.RingActivePairs.ordered_scores
