import TetraStereo.Engine.RingReferenceCasing
import TetraStereo.OneCenter.LocalizedChemicalRingPromotionAggregation

set_option autoImplicit false

/-! Hanson et al. (2018), p. 1762, propose testing all eligible promotions
and cancelling opposite descriptors. This calculation accepts only complete
molecular trials. A tied outcome has a molecular tie witness on both
geometries. The separate Figure 14 extension recalculates auxiliaries after
promotion and is not a premise of this fixed-publication calculation. -/
namespace TetraStereo.Engine.RingChemicalPriority.ReferenceFrame

open OneCenter LocalizedGenericMarkedRecalculation Recursive
open LocalizedChemicalRingPromotionAggregation

def Trial.hand? {m g p} {f : Frame m g p} (t : Trial f) (mirrored : Bool) : Option RS :=
  t.outcome.reading?.map fun r => if mirrored then r.reflected else r.actual

/-- Every completed promotion has the same mirror law, including a
persistent tie, which contributes zero on both geometries. -/
theorem Trial.mirror_hand {m g p} {f : Frame m g p} (t : Trial f) :
    t.hand? true = if f.reversals % 2 = 0 then (t.hand? false).map RS.swap else t.hand? false := by
  cases outcome : t.outcome with
  | tied => simp [Trial.hand?,outcome,Outcome.reading?]
  | assigned a b ha hb r h =>
    have label := (t.chemical_letter ha hb h).2
    obtain ⟨x,y⟩ := r
    cases x <;> cases y <;> by_cases even : f.reversals % 2 = 0 <;>
      simp_all [Trial.hand?,Outcome.reading?,Reading.label,caseFromMirror?,RS.swap,pseudoRSOfRS]

def Population.hands {m g p} (s : Population m g p) (mirrored : Bool) : List (Option RS) :=
  s.trials.map fun t => t.hand? mirrored

/-- Summing commutes with reflection even when strict trials disagree
or some of the eligible promotions have a persistent tie. -/
theorem Population.mirror_balance {m g p} (s : Population m g p) :
    readingBalance (s.hands true) =
      if s.frame.reversals % 2 = 0 then -readingBalance (s.hands false) else readingBalance (s.hands false) := by
  by_cases even : s.frame.reversals % 2 = 0
  · have paired : s.hands true = (s.hands false).map (Option.map RS.swap) := by
      simp [Population.hands,List.map_map,Function.comp_def,Trial.mirror_hand,even]
    rw [paired,readingBalance_swap,if_pos even]
  · have paired : s.hands true = s.hands false := by simp [Population.hands,Trial.mirror_hand,even]
    rw [paired,if_neg even]

def survivingHand (z : Int) : Option RS :=
  if 0 < z then some .R else if z < 0 then some .S else none

theorem aggregate_of_balance (xs : List (Option RS)) :
    completedAggregate xs = some (survivingHand (readingBalance xs)) := by
  unfold completedAggregate DeclarativeCIP.ProductionOccurrenceRules456.promotionAggregate
  rw [completed_balance]
  simp only [survivingHand]
  split <;> first | rfl | (split <;> rfl)

theorem survivingHand_neg (z : Int) :
    survivingHand (-z) = (survivingHand z).map RS.swap := by
  rcases lt_trichotomy z 0 with h | rfl | h
  · simp [survivingHand,h,not_lt.mpr h.le,RS.swap]
  · rfl
  · simp [survivingHand,h,not_lt.mpr h.le,RS.swap]

/-- The two source-style signed aggregates give the molecular letter after
crossing the actual and reflected results. The population records every
eligible mark and the signed reading or proved tie for every trial. -/
def Population.signedDescriptor {m g p} (s : Population m g p) :=
  caseFromMirror? (completedAggregate (s.hands false)).join (completedAggregate (s.hands true)).join

/-- The sign of the actual balance determines the absolute hand. The
reversal parity of the initial frame determines its case. A zero balance
proves cancellation even when it contains both strict and tied trials. -/
theorem Population.signedDescriptor_eq {m g p} (s : Population m g p) :
    s.signedDescriptor = (survivingHand (readingBalance (s.hands false))).map fun hand =>
      if s.frame.reversals % 2 = 0 then .chiral hand else .pseudoasymmetric (pseudoRSOfRS hand) := by
  unfold Population.signedDescriptor
  rw [aggregate_of_balance,aggregate_of_balance,s.mirror_balance]
  by_cases even : s.frame.reversals % 2 = 0
  · rw [if_pos even,survivingHand_neg]
    cases h : survivingHand (readingBalance (s.hands false)) with
    | none => rfl
    | some hand => cases hand <;> simp [even,caseFromMirror?,RS.swap]
  · rw [if_neg even]
    cases h : survivingHand (readingBalance (s.hands false)) with
    | none => rfl
    | some hand => cases hand <;> simp [even,caseFromMirror?]

theorem Population.signedDescriptor_none_iff {m g p} (s : Population m g p) :
    s.signedDescriptor = none ↔ readingBalance (s.hands false) = 0 := by
  rw [s.signedDescriptor_eq]
  simp only [Option.map_eq_none_iff,survivingHand]
  split
  · simp_all; omega
  · split <;> simp_all <;> omega

private theorem balance_bounds (xs : List (Option RS)) :
    (some .R ∉ xs → readingBalance xs ≤ 0) ∧ (some .S ∉ xs → 0 ≤ readingBalance xs) := by
  induction xs with
  | nil => exact ⟨by decide, by decide⟩
  | cons head tail ih =>
    constructor
    · intro missing
      have tailNonpos := ih.1 (fun h => missing (List.mem_cons_of_mem _ h))
      cases head with
      | none => simpa [readingBalance,readingScore] using tailNonpos
      | some hand =>
        cases hand with
        | R => exact False.elim (missing List.mem_cons_self)
        | S => simp [readingBalance,readingScore] at tailNonpos ⊢; omega
    · intro missing
      have tailNonneg := ih.2 (fun h => missing (List.mem_cons_of_mem _ h))
      cases head with
      | none => simpa [readingBalance,readingScore] using tailNonneg
      | some hand =>
        cases hand with
        | R => simp [readingBalance,readingScore] at tailNonneg ⊢; omega
        | S => exact False.elim (missing List.mem_cons_self)

/-- A surviving absolute hand has an actual eligible, strict trial with
the stated priority order and geometric readback. -/
theorem Population.surviving_trial {m g p} (s : Population m g p) {hand : RS}
    (survives : survivingHand (readingBalance (s.hands false)) = some hand) :
    ∃ (t : Trial s.frame) (a b : List Nat), t ∈ s.trials ∧
      orders s.frame.ids t.table false = [a] ∧ orders s.frame.ids t.table true = [b] ∧
      readback? g a = some hand := by
  have found : some hand ∈ s.hands false := by
    by_contra missing
    cases hand with
    | R =>
      have le := (balance_bounds _).1 missing
      by_cases negative : readingBalance (s.hands false) < 0 <;>
        simp [survivingHand,not_lt.mpr le,negative] at survives
    | S =>
      have le := (balance_bounds _).2 missing
      by_cases positive : 0 < readingBalance (s.hands false) <;>
        simp [survivingHand,not_lt.mpr le,positive] at survives
  obtain ⟨t,mem,h⟩ := List.mem_map.mp found
  cases out : t.outcome with
  | tied => simp [Trial.hand?,out,Outcome.reading?] at h
  | assigned a b ha hb r hg =>
    have handEq : r.actual = hand := by simpa [Trial.hand?,out,Outcome.reading?] using h
    exact ⟨t,a,b,mem,ha,hb,handEq ▸ (t.chemical_letter ha hb hg).1⟩

theorem Population.signed_lowercase_iff {m g p} (s : Population m g p) {hand : RS}
    (survives : survivingHand (readingBalance (s.hands false)) = some hand) :
    s.signedDescriptor = some (.pseudoasymmetric (pseudoRSOfRS hand)) ↔ s.frame.reversals = 3 := by
  rw [s.signedDescriptor_eq,survives]
  have count := s.frame.reversal_count
  simp only [List.mem_cons,List.not_mem_nil,or_false] at count
  rcases count with h | h | h <;> simp [h]

/-- On every existing unanimous molecular certificate the signed projection
preserves the assigned label or proved absence. -/
theorem Population.signedDescriptor_of_consensus {m g p} (s : Population m g p) {v}
    (accepted : s.consensus? = some v) : s.signedDescriptor = v.bind Reading.label := by
  have agreed := (s.consensus_iff v).mp accepted
  cases v with
  | none =>
    apply s.signedDescriptor_none_iff.mpr
    unfold readingBalance
    apply List.sum_eq_zero
    intro score mem
    obtain ⟨hand,member,rfl⟩ := List.mem_map.mp mem
    obtain ⟨t,inside,rfl⟩ := List.mem_map.mp member
    simp [Trial.hand?,agreed t inside,readingScore]
  | some r =>
    have populated : s.trials ≠ [] := by
      intro empty
      have h := congrArg List.length s.complete
      have eligible := s.frame.eligible
      simp [empty] at h
      simp [← h] at eligible
    have aggregate (mirrored : Bool) : completedAggregate (s.hands mirrored) =
        some (some (if mirrored then r.reflected else r.actual)) := by
      apply completedAggregate_of_consensus
      apply (LocalizedChemicalRingSenseTransport.consensus_eq_some_iff _ _).mpr
      refine ⟨by simpa [Population.hands] using populated,?_⟩
      intro hand member
      obtain ⟨t,inside,rfl⟩ := List.mem_map.mp member
      simp [Trial.hand?,agreed t inside]
    unfold Population.signedDescriptor
    rw [aggregate,aggregate]
    rfl

/-- Comparing two complete populations only requires the surviving absolute
hands and, when a hand survives, the parity of the two frames. This applies
even when the individual promoted comparisons or the trial counts differ. -/
theorem Population.same_signedDescriptor_iff {m g p m' g' p'}
    (s : Population m g p) (t : Population m' g' p') :
    s.signedDescriptor = t.signedDescriptor ↔
      survivingHand (readingBalance (s.hands false)) = survivingHand (readingBalance (t.hands false)) ∧
      ((survivingHand (readingBalance (s.hands false))).isSome = true →
        (s.frame.reversals % 2 = 0 ↔ t.frame.reversals % 2 = 0)) := by
  rw [s.signedDescriptor_eq,t.signedDescriptor_eq]
  cases survivingHand (readingBalance (s.hands false)) with
  | none => cases survivingHand (readingBalance (t.hands false)) <;> simp
  | some a =>
    cases survivingHand (readingBalance (t.hands false)) with
    | none => simp
    | some b =>
      cases a <;> cases b <;> by_cases l : s.frame.reversals % 2 = 0 <;>
        by_cases r : t.frame.reversals % 2 = 0 <;> simp [l,r,pseudoRSOfRS]

end TetraStereo.Engine.RingChemicalPriority.ReferenceFrame

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Trial.mirror_hand
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Population.mirror_balance
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Population.signedDescriptor_eq
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Population.signedDescriptor_none_iff

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Population.surviving_trial
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Population.signed_lowercase_iff
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Population.same_signedDescriptor_iff
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Population.signedDescriptor_of_consensus
