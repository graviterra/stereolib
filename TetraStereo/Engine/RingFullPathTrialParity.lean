import TetraStereo.Engine.RingRule5Tie
import TetraStereo.Engine.RingFullPathTrialReadings

/-! # Casing from marked molecular coordinate readings -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingFullPathTrialParity
open OneCenter RingStereoSiblingPass RingFullPathTrialReadings
open RingFullPathEligibility (Key Reads)
open RingActivePairReport (Slot Score Matrix Ranking)
open RingNestedActivePair (Frame)
open RingRetainedChemicalTrace (Word)
open LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)

private def ordinary (k : Key) : List (List Word) :=
  [k.throughFourA,[bitWord k.bestFourB],[k.fourC],[bitWord k.fixedR]]

private theorem bits_inj : Function.Injective bitWord := by
  apply List.map_injective_iff.mpr
  intro a b h
  cases a <;> cases b <;> first | rfl | contradiction

private theorem ordinary_inj : Function.Injective ordinary := by
  rintro ⟨a,b,c,d⟩ ⟨e,f,g,h⟩ eqn
  simp only [ordinary,List.cons.injEq,and_true] at eqn
  obtain ⟨rfl,hbf,rfl,hdh⟩ := eqn
  obtain rfl := bits_inj hbf
  obtain rfl := bits_inj hdh
  rfl

private theorem trial_lt (k l : Key) (w z : Word) :
    trialKey k w < trialKey l z ↔ ordinary k < ordinary l ∨ k = l ∧ w < z := by
  change ordinary k ++ [[w]] < ordinary l ++ [[z]] ↔ _
  rw [RingPathRankTransport.snoc_lt (show (ordinary k).length = (ordinary l).length from rfl)]
  simp [ordinary_inj.eq_iff,List.cons_lt_cons_iff]

private theorem trial_eq (k l : Key) (w z : Word) :
    trialKey k w = trialKey l z ↔ k = l ∧ w = z := by
  change ordinary k ++ [[w]] = ordinary l ++ [[z]] ↔ _
  constructor
  · intro h
    have wz : w = z := by simpa using congrArg List.getLast? h
    subst z
    exact ⟨ordinary_inj (List.append_cancel_right h),rfl⟩
  · rintro ⟨rfl,rfl⟩; rfl

private def signed {α : Type} [LinearOrder α] (a b : α) : Int :=
  if b < a then 1 else if a < b then -1 else 0

private theorem signed_pos {α : Type} [LinearOrder α] (a b : α) : 0 < signed a b ↔ b < a := by
  unfold signed
  split_ifs <;> simp_all

private theorem signed_neg {α : Type} [LinearOrder α] (a b : α) : signed a b < 0 ↔ a < b := by
  unfold signed
  split_ifs <;> simp_all [asymm]

private def edge {α : Type} [LinearOrder α] (x y : Slot → α) (j k : Slot) : Score :=
  (signed (x j) (x k),signed (y j) (y k))

private def matrix {α : Type} [LinearOrder α] (x y : Slot → α) : Matrix (fun j k => some (edge x y j k)) :=
  ⟨edge x y,fun _ _ _ => rfl⟩

private def ranking {α : Type} [LinearOrder α] (x y : Slot → α) (rev : Bool) (row : List Slot)
    (legal : Legal (if rev then y else x) (List.finRange 4) row)
    (inj : Function.Injective (if rev then y else x)) : Ranking (matrix x y) rev := by
  refine ⟨row,legal.perm,?_⟩
  have distinct := legal.perm.nodup_iff.mpr (List.nodup_finRange 4)
  apply (List.pairwise_and_iff.mpr ⟨distinct,List.pairwise_map.mp legal.descending⟩).imp
  rintro j k ⟨ne,ge⟩
  have lt := lt_of_le_of_ne ge (fun h => ne (inj h.symm))
  cases rev
  · exact ⟨(signed_pos _ _).mpr lt,(signed_neg _ _).mpr lt⟩
  · exact ⟨(signed_pos _ _).mpr lt,(signed_neg _ _).mpr lt⟩

/-- Count reversals of the ordinary ligand comparisons on the six unordered
pairs of slots. This count is independent of which atom is later promoted. -/
def reversals (x y : Slot → Key) : Nat :=
  LocalizedChemicalRing.ConstitutionalPartition.pairs.countP fun p =>
    decide (trialKey (x p.2) [] < trialKey (x p.1) []) !=
    decide (trialKey (y p.2) [] < trialKey (y p.1) [])

private theorem marked_reversals (x y : Slot → Key) (w : Slot → Word)
    (tie : ∀ j k, x j = x k ↔ y j = y k) :
    RingActivePairReport.reversals (matrix (fun j => trialKey (x j) (w j))
      (fun j => trialKey (y j) (w j))) = reversals x y := by
  apply (List.Perm.refl _).countP_congr
  intro p _
  change (decide (0 < signed _ _) != decide (0 < signed _ _)) = _
  simp only [signed_pos,trial_lt,lt_self_iff_false,and_false,or_false]
  by_cases h : x p.2 = x p.1
  · simp [h,(tie _ _).mp h]
  · have nh : y p.2 ≠ y p.1 := fun eqn => h ((tie _ _).mpr eqn)
    simp [h,nh]

/-- A common mark can break a tie or leave it unresolved. In every strict
trial, physical reflection reverses the hand exactly when the number of
ordinary comparison reversals is even. -/
theorem trial_mirror {i f} (fr : @Frame i f) (x y : Slot → Key) (w : Slot → Word)
    (tie : ∀ j k, x j = x k ↔ y j = y k) {h k : Option RS}
    (actual : Outcome fr false (fun j => trialKey (x j) (w j)) h)
    (reflected : Outcome fr true (fun j => trialKey (y j) (w j)) k) :
    k = if reversals x y % 2 = 0 then h.map RS.swap else h := by
  have shared (j k) : trialKey (x j) (w j) = trialKey (x k) (w k) ↔
      trialKey (y j) (w j) = trialKey (y k) (w k) := by simp only [trial_eq,tie]
  cases actual with
  | tie ne eqn =>
    cases reflected with
    | tie => simp
    | hand inj _ _ => exact False.elim (ne (inj ((shared _ _).mp eqn)))
  | @hand row a inj legal seen =>
    cases reflected with
    | tie ne eqn => exact False.elim (ne (inj ((shared _ _).mpr eqn)))
    | @hand row' b inj' legal' seen' =>
      let vx := fun j => trialKey (x j) (w j)
      let vy := fun j => trialKey (y j) (w j)
      have lab := fr.label_by_reversals (ranking vx vy false row legal inj) (ranking vx vy true row' legal' inj') seen seen'
      rw [marked_reversals x y w tie] at lab
      cases a <;> cases b <;> by_cases even : reversals x y % 2 = 0 <;>
        simp_all [RingNestedActivePair.label,RS.swap]

open LocalizedChemicalRingPromotionAggregation (readingBalance readingBalance_swap completedAggregate)
open RingChemicalPriority.ReferenceFrame (survivingHand aggregate_of_balance survivingHand_neg)

private theorem trial_slots (x y : Slot → Key) (tie : ∀ j k, x j = x k ↔ y j = y k) :
    trials x = trials y := by
  have eqn : RingFullPathEligibility.tiedSlots x = RingFullPathEligibility.tiedSlots y := by
    unfold RingFullPathEligibility.tiedSlots
    congr 1
    funext j
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true,Bool.and_eq_true,beq_iff_eq,tie]
  simp only [trials,RingFullPathEligibility.candidates,eqn]

private theorem columns {α β : Type} (g : β → β) (xs ys : List (α × β))
    (slots : xs.map Prod.fst = ys.map Prod.fst)
    (each : ∀ s a b, (s,a) ∈ xs → (s,b) ∈ ys → b = g a) :
    ys.map Prod.snd = (xs.map Prod.snd).map g := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons p xs ih =>
    cases ys with
    | nil => simp at slots
    | cons q ys =>
      obtain ⟨s,a⟩ := p
      obtain ⟨t,b⟩ := q
      obtain ⟨rfl,tail⟩ := List.cons.inj slots
      exact congrArg₂ List.cons (each _ _ _ List.mem_cons_self List.mem_cons_self)
        (ih ys tail (fun j u v hu hv => each j u v (.tail _ hu) (.tail _ hv)))

/-- Every original trial has a mirror trial at the same slot. The molecular
readings of the two full populations either agree throughout or swap every
resolved hand, depending only on the ordinary six comparisons. -/
theorem view_hands {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {f} (fr : @Frame i f) (view : RingActiveDistanceSchedule.View i)
    (ready : RingGroupedStereo.Ready f (RingActiveDistanceSchedule.frozen view f))
    {x y : Slot → Key} {xs ys : List (Option Slot × Option RS)} :
    let r := RingActiveDistanceSchedule.frozen view f
    (∀ k, Reads i r false (RingGroupedCentre.cursor fr k) (x k)) →
    (∀ k, Reads i r true (RingGroupedCentre.cursor fr k) (y k)) →
    readings? fr r false = some xs → readings? fr r true = some ys →
    xs.map Prod.fst = ys.map Prod.fst ∧
    ys.map Prod.snd = if reversals x y % 2 = 0 then (xs.map Prod.snd).map (Option.map RS.swap)
      else xs.map Prod.snd := by
  intro r hx hy ax ay
  obtain ⟨a,as',ha,sa,ra,srcA⟩ := ready_readings geom fr ready false
  obtain ⟨b,bs,hb,sb,rb,srcB⟩ := ready_readings geom fr ready true
  obtain rfl := Option.some.inj (ax.symm.trans ha)
  obtain rfl := Option.some.inj (ay.symm.trans hb)
  have unique (rev : Bool) (x y : Slot → Key)
      (l : ∀ k, Reads i r rev (RingGroupedCentre.cursor fr k) (x k))
      (m : ∀ k, Reads i r rev (RingGroupedCentre.cursor fr k) (y k)) : x = y := by
    funext k
    obtain ⟨v,_,only⟩ := RingFullPathEligibility.key_exact ready rev _ (RingGroupedCentre.valid fr k)
      (fr.direction k).property.1
    exact ((only _).mp (l k)).trans ((only _).mp (m k)).symm
  have ex := unique false a x ra hx
  have ey := unique true b y rb hy
  subst a
  subst b
  have tie := RingRule5Tie.view_partition fr view ready x y hx hy
  have slots := sa.trans ((trial_slots x y tie).trans sb.symm)
  refine ⟨slots,?_⟩
  let g := fun h : Option RS => if reversals x y % 2 = 0 then h.map RS.swap else h
  have paired := columns g _ _ slots (by
    intro s u v hu hv
    obtain ⟨w,hw,wa⟩ := mark_exact fr ready false s
    obtain ⟨z,hz,wb⟩ := mark_exact fr ready true s
    obtain rfl := Option.some.inj (hw.symm.trans hz)
    exact trial_mirror fr x y _ tie (srcA s u hu x _ hx ((wa _).mpr rfl)) (srcB s v hv y _ hy ((wb _).mpr rfl)))
  by_cases even : reversals x y % 2 = 0 <;> simpa [g,even] using paired

/-- Independent signed majorities on both geometries, including cancellation
and trials where a promotion leaves some pair tied. -/
theorem view_aggregates {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {f} (fr : @Frame i f) (view : RingActiveDistanceSchedule.View i)
    (ready : RingGroupedStereo.Ready f (RingActiveDistanceSchedule.frozen view f))
    {x y : Slot → Key} {xs ys : List (Option Slot × Option RS)} :
    let r := RingActiveDistanceSchedule.frozen view f
    (∀ k, Reads i r false (RingGroupedCentre.cursor fr k) (x k)) →
    (∀ k, Reads i r true (RingGroupedCentre.cursor fr k) (y k)) →
    readings? fr r false = some xs → readings? fr r true = some ys →
    let balance := readingBalance (xs.map Prod.snd)
    let h := survivingHand balance
    readingBalance (ys.map Prod.snd) = (if reversals x y % 2 = 0 then -balance else balance) ∧
    completedAggregate (xs.map Prod.snd) = some h ∧
    completedAggregate (ys.map Prod.snd) = some (if reversals x y % 2 = 0 then h.map RS.swap else h) := by
  intro r hx hy ax ay
  have paired := (view_hands geom fr view ready hx hy ax ay).2
  by_cases even : reversals x y % 2 = 0
  · rw [if_pos even] at paired
    simp only [if_pos even,paired,aggregate_of_balance,readingBalance_swap,survivingHand_neg,true_and]
  · rw [if_neg even] at paired
    simp only [if_neg even,paired,aggregate_of_balance,true_and]

/-- All priorities inspected before the fixed-reference comparison. -/
def earlier (k : Key) : List (List Word) := [k.throughFourA,[bitWord k.bestFourB],[k.fourC]]

private theorem bits_lt (a b : List Bool) : bitWord a < bitWord b ↔ a < b := by
  induction a generalizing b with
  | nil => cases b <;> simp [bitWord]
  | cons h t ih =>
    cases b with
    | nil => simp [bitWord]
    | cons k s =>
      change [h.toNat] :: bitWord t < [k.toNat] :: bitWord s ↔ h::t < k::s
      cases h <;> cases k <;> simp [List.cons_lt_cons_iff,ih]

private theorem unmarked_lt (a b : Key) : trialKey a [] < trialKey b [] ↔
    earlier a < earlier b ∨ earlier a = earlier b ∧ a.fixedR < b.fixedR := by
  rw [trial_lt]
  change (earlier a ++ [[bitWord a.fixedR]] < earlier b ++ [[bitWord b.fixedR]] ∨ _) ↔ _
  rw [RingPathRankTransport.snoc_lt (show (earlier a).length = (earlier b).length from rfl)]
  simp [List.cons_lt_cons_iff,bits_lt]

private theorem computed_fixed {i f r rev} {q : RingActivePairs.Arm i} {k : Key}
    (good : RingGroupedStereo.Ready f r) (valid : RingRule5Shape.Valid q) (on : RingRule5Shape.On f q)
    (legal : Reads i r rev q k) : RingFullPathRule5.word? i r rev .R q = some k.fixedR := by
  obtain ⟨_,_,_,_,_,_,_,_,_,word,rfl⟩ := legal
  obtain ⟨z,h,e⟩ := RingFullPathRule5.word_exact rev (RingOccurrenceStereo.rank_total good rev [.lowercase])
    .R q valid on
  exact h.trans (congrArg some ((e _).mp word).symm)

private theorem mirror_earlier {i : Input} (f : RingActivePairs.Site i) (view : RingActiveDistanceSchedule.View i)
    (good : RingGroupedStereo.Ready f (RingActiveDistanceSchedule.frozen view f))
    {q : RingActivePairs.Arm i} (valid : RingRule5Shape.Valid q) (on : RingRule5Shape.On f q)
    {x y : Key} :
    let r := RingActiveDistanceSchedule.frozen view f
    Reads i r false q x → Reads i r true q y → earlier y = earlier x := by
  intro r hx hy
  obtain ⟨w,_,e⟩ := RingFullPathRule5.word_exact false (RingOccurrenceStereo.rank_total good false [.lowercase])
    .S q valid on
  have mirror := RingRule5Tie.reflected_read f view good false hx ((e w).mpr rfl)
  obtain ⟨k,_,only⟩ := RingFullPathEligibility.key_exact good true q valid on
  have eqn := ((only _).mp hy).trans ((only _).mp mirror).symm
  rw [eqn]
  rfl

/-- Every legal choice of the original and mirror ligand keys supplies the
exact signed Rule 5 scores of the two independent reference contests. -/
theorem fixed_scores_of_readings {i : Input} {f} (fr : @Frame i f) (view : RingActiveDistanceSchedule.View i)
    (good : RingGroupedStereo.Ready f (RingActiveDistanceSchedule.frozen view f))
    (x y : Slot → Key) (j k : Slot) :
    let r := RingActiveDistanceSchedule.frozen view f
    (∀ s, Reads i r false (RingGroupedCentre.cursor fr s) (x s)) →
    (∀ s, Reads i r true (RingGroupedCentre.cursor fr s) (y s)) →
    let cr := compare (x j).fixedR (x k).fixedR
    let cs := compare (y j).fixedR (y k).fixedR
    RingFullPathRule5.score? i r false (RingGroupedCentre.cursor fr j) (RingGroupedCentre.cursor fr k) =
      some (RingOccurrenceStereo.fixedScore cr cs) ∧
    RingFullPathRule5.score? i r true (RingGroupedCentre.cursor fr j) (RingGroupedCentre.cursor fr k) =
      some (RingOccurrenceStereo.fixedScore cs cr) := by
  intro r hx hy
  let q := RingGroupedCentre.cursor fr
  have fixed (rev : Bool) (s : Slot) (keys : Slot → Key) (h : Reads i r rev (q s) (keys s)) :
      RingFullPathRule5.word? i r rev .R (q s) = some (keys s).fixedR :=
    computed_fixed good (RingGroupedCentre.valid fr s) (fr.direction s).property.1 h
  have swapR (s : Slot) : RingFullPathRule5.word? i r false .S (q s) = some (y s).fixedR :=
    (RingFullPathRule5.view_word_swap f view good false .S _ (RingGroupedCentre.valid fr s) (fr.direction s).property.1).symm.trans
      (fixed true s y (hy s))
  have swapS (s : Slot) : RingFullPathRule5.word? i r true .S (q s) = some (x s).fixedR :=
    (RingFullPathRule5.view_word_swap f view good false .R _ (RingGroupedCentre.valid fr s) (fr.direction s).property.1).trans
      (fixed false s x (hx s))
  constructor
  · unfold RingFullPathRule5.score?
    rw [fixed false j x (hx j),fixed false k x (hx k),swapR j,swapR k]
    rfl
  · unfold RingFullPathRule5.score?
    rw [fixed true j y (hy j),fixed true k y (hy k),swapS j,swapS k]
    rfl

/-- A molecular comparison reverses precisely when the full-path Rule 5
score at its actual gate has magnitude two. Earlier rules contribute zero
to the parity count. -/
theorem doubled_iff {i : Input} {f} (fr : @Frame i f) (view : RingActiveDistanceSchedule.View i)
    (good : RingGroupedStereo.Ready f (RingActiveDistanceSchedule.frozen view f))
    (x y : Slot → Key) (j k : Slot) :
    let r := RingActiveDistanceSchedule.frozen view f
    (∀ s, Reads i r false (RingGroupedCentre.cursor fr s) (x s)) →
    (∀ s, Reads i r true (RingGroupedCentre.cursor fr s) (y s)) →
    (((trialKey (x j) [] < trialKey (x k) []) ↔ ¬ (trialKey (y j) [] < trialKey (y k) [])) ↔
      earlier (x j) = earlier (x k) ∧
      ∃ z : Int, RingFullPathRule5.score? i r false (RingGroupedCentre.cursor fr j)
        (RingGroupedCentre.cursor fr k) = some z ∧ z.natAbs = 2) := by
  intro r hx hy
  let q := RingGroupedCentre.cursor fr
  have before (s : Slot) := mirror_earlier f view good (RingGroupedCentre.valid fr s)
    (fr.direction s).property.1 (hx s) (hy s)
  simp only [unmarked_lt,before]
  by_cases gate : earlier (x j) = earlier (x k)
  · have lower : RingRule5Shape.key i r false (q j) = RingRule5Shape.key i r false (q k) := by
      have fields := gate
      simp only [earlier,List.cons.injEq,and_true] at fields
      rw [RingRule5Tie.reading_key good (RingGroupedCentre.valid fr j) (fr.direction j).property.1 (hx j),
        RingRule5Tie.reading_key good (RingGroupedCentre.valid fr k) (fr.direction k).property.1 (hx k),
        fields.1,fields.2.2]
    have fixed (rev : Bool) (s : Slot) (keys : Slot → Key) (h : Reads i r rev (q s) (keys s)) :=
      computed_fixed good (RingGroupedCentre.valid fr s) (fr.direction s).property.1 h
    have swapped (s : Slot) : RingFullPathRule5.word? i r false .S (q s) = some (y s).fixedR :=
      (RingFullPathRule5.view_word_swap f view good false .S _ (RingGroupedCentre.valid fr s) (fr.direction s).property.1).symm.trans
        (fixed true s y (hy s))
    have sc := (fixed_scores_of_readings fr view good x y j k hx hy).1
    have ties := RingRule5Tie.tie_iff good (RingGroupedCentre.valid fr j) (RingGroupedCentre.valid fr k)
      (fr.direction j).property.1 (fr.direction k).property.1 lower
    rw [fixed false j x (hx j),fixed false k x (hx k),swapped j,swapped k] at ties
    have law (a b : List Bool) : compare a b = .lt ↔ a < b :=
      DeclarativeCIP.compareLex_eq_lt_iff_of compare (fun _ _ => by decide +revert)
        (fun _ _ => Std.compare_eq_eq_iff_eq) a b
    have zs : compare (x j).fixedR (x k).fixedR = .eq ↔ compare (y j).fixedR (y k).fixedR = .eq := by
      simpa only [Std.compare_eq_eq_iff_eq,Option.some.injEq] using ties
    rw [sc]
    simp only [gate,lt_self_iff_false,false_or,true_and,← law,Option.some.injEq,exists_eq_left']
    generalize compare (x j).fixedR (x k).fixedR = cr at zs ⊢
    generalize compare (y j).fixedR (y k).fixedR = cs at zs ⊢
    cases cr <;> cases cs <;> first | decide | simp at zs
  · simp only [gate,false_and,or_false]
    tauto

end TetraStereo.Engine.RingFullPathTrialParity
assert_kernel_only TetraStereo.Engine.RingFullPathTrialParity.trial_mirror
assert_kernel_only TetraStereo.Engine.RingFullPathTrialParity.view_aggregates
assert_kernel_only TetraStereo.Engine.RingFullPathTrialParity.doubled_iff
assert_kernel_only TetraStereo.Engine.RingFullPathTrialParity.fixed_scores_of_readings
