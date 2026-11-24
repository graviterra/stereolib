import TetraStereo.Engine.RingGroupedOrders
import TetraStereo.Engine.RingPromotionBalance

set_option autoImplicit false

namespace TetraStereo.Engine.RingGroupedTrials
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Frame Reader Labels)
open RingActivePairReport (Slot Matrix Ranking)
open RingRetainedChemicalTrace (Word)
open RingGroupedCentre (Arms cursor)
open RingGroupedOrders (wins trialMatrix marks)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedChemicalRingPromotionAggregation (readingBalance)
open RingChemicalPriority.ReferenceFrame (survivingHand)
attribute [local instance] lexOrd

def atom {i f} (fr : Frame i f) (s : Slot) := (fr.atoms [s]).head!

structure Marking {i f} (fr : Frame i f) (read : Reader i) (s : Slot) where
  branches : Slot → RingStereoSiblingPass.Branch
  source : ∀ k, RingGroupedMark.Reading i read (atom fr s) (cursor fr k) (branches k)

def marking? {i f} (fr : Frame i f) (read : Reader i) (s : Slot) : Option (Marking fr read s) := do
  let ⟨es,h⟩ ← (RingActivePairReport.four? fun k => RingGroupedMark.arm? i read (atom fr s) (cursor fr k)).attach
  return ⟨fun k => (es k).2,fun k => (RingGroupedMark.arm_source (RingActivePairReport.four_at h k)).2⟩

theorem marking_ready {i f read} (fr : Frame i f) (ready : RingGroupedStereo.Ready f read) (s : Slot) :
    (marking? fr read s).isSome = true := by
  have all (k : Slot) := RingGroupedMark.arm_ready ready (atom fr s) (cursor fr k) (RingGroupedCentre.valid fr k) (fr.direction k).property.1
  obtain ⟨p,h⟩ := Option.isSome_iff_exists.mp (RingActivePairReport.four_full _ fun k => Option.isSome_iff_exists.mpr (all k))
  simp [marking?,Option.attach_eq_some _ ⟨p,h⟩]

def Marking.word {i f fr read s} (m : @Marking i f fr read s) (k : Slot) := (m.branches k).word

/-- A completed trial either exhibits an enduring tie or has both strict
orders and their coordinate readings. A failed readback cannot certify a tie. -/
inductive Outcome {i f fr read} (a : @Arms i f fr read) (m : Matrix a.edge) (w : Slot → Word) where
  | tied (witness : ∃ j k, j ≠ k ∧ ∀ rev, wins a rev w j = wins a rev w k) : Outcome a m w
  | ranked (actual : Ranking (trialMatrix m w) false) (reflected : Ranking (trialMatrix m w) true)
      (hand mirrorHand : RS)
      (physical : readback? (inputGeometry i.certified) (fr.atoms actual.slots) = some hand)
      (mirrorPhysical : readback? (mirror (inputGeometry i.certified)) (fr.atoms reflected.slots) = some mirrorHand) :
      Outcome a m w

def Outcome.hands {i f fr read a m w} : @Outcome i f fr read a m w → Option (RS × RS)
  | .tied _ => none
  | .ranked _ _ h k _ _ => some (h,k)

theorem Outcome.mirror {i f fr read a m w} (o : @Outcome i f fr read a m w) :
    o.hands.map Prod.snd = if RingActivePairReport.doubled m % 2 = 0 then (o.hands.map Prod.fst).map RS.swap
      else o.hands.map Prod.fst := by
  cases o with
  | tied => simp [Outcome.hands]
  | ranked actual reflected h k x y =>
    have label := fr.label_by_reversals actual reflected x y
    rw [RingGroupedOrders.crossings,RingGroupedOrders.doubled_crossings a] at label
    cases h <;> cases k <;> by_cases even : RingActivePairReport.doubled m % 2 = 0 <;>
      simp_all [Outcome.hands,RingNestedActivePair.label,RS.swap]

private instance {i f fr read} (a : @Arms i f fr read) (w : Slot → Word) :
    Decidable (∃ j k, j ≠ k ∧ wins a false w j = wins a false w k) :=
  decidable_of_iff ((List.finRange 4).any (fun j => (List.finRange 4).any fun k =>
    j != k && wins a false w j == wins a false w k) = true) (by simp [bne_iff_ne])

def outcome? {i f fr read} (a : @Arms i f fr read) (m : Matrix a.edge) (w : Slot → Word) : Option (Outcome a m w) := do
  if h : ∃ j k, j ≠ k ∧ wins a false w j = wins a false w k then
    return .tied (by
      obtain ⟨j,k,d,t⟩ := h
      exact ⟨j,k,d,fun rev => by cases rev; exact t; exact (RingGroupedOrders.shared a w j k).mp t⟩)
  let mat := trialMatrix m w
  let actual ← RingActivePairReport.rank? mat false
  let reflected ← RingActivePairReport.rank? mat true
  let ⟨s,hs⟩ ← (readback? (inputGeometry i.certified) (fr.atoms actual.slots)).attach
  let ⟨t,ht⟩ ← (readback? (mirror (inputGeometry i.certified)) (fr.atoms reflected.slots)).attach
  return .ranked actual reflected s t hs ht

/-- Calibration needs only the four coordinate carriers in every
permutation. Original and reflected rank permutations may differ. -/
def Calibrated {i f} (fr : Frame i f) := ∀ ss : List Slot, ss.Perm (List.finRange 4) →
  (readback? (inputGeometry i.certified) (fr.atoms ss)).isSome = true

theorem outcome_total {i f fr read} (a : @Arms i f fr read) (m : Matrix a.edge) (w : Slot → Word)
    (geometry : Calibrated fr) : (outcome? a m w).isSome = true := by
  by_cases h : ∃ j k, j ≠ k ∧ wins a false w j = wins a false w k
  · simp [outcome?,h]
  have strict (rev : Bool) : Function.Injective (wins a rev w) := by
    intro j k e
    by_contra ne
    exact h ⟨j,k,ne,by cases rev; exact e; exact (RingGroupedOrders.shared a w j k).mpr e⟩
  have ranked (rev : Bool) := (RingGroupedOrders.rank_iff (trialMatrix m w) rev (wins a rev w)
    (RingGroupedOrders.trial_order a m rev w)).mpr (strict rev)
  obtain ⟨r,hr⟩ := Option.isSome_iff_exists.mp (ranked false)
  obtain ⟨s,hs⟩ := Option.isSome_iff_exists.mp (ranked true)
  obtain ⟨u,hu⟩ := Option.isSome_iff_exists.mp (geometry _ r.perm)
  obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp (geometry _ s.perm)
  have phy := Option.attach_eq_some _ ⟨u,hu⟩
  have mirrored : readback? (mirror (inputGeometry i.certified)) (fr.atoms s.slots) = some v.swap := by
    rw [readback_mirror,hv]; rfl
  have mir := Option.attach_eq_some _ ⟨_,mirrored⟩
  simp [outcome?,h,hr,hs,phy,mir]

structure Trial {i f fr read} (a : @Arms i f fr read) (m : Matrix a.edge) (s : Slot) where
  marking : Marking fr read s
  outcome : Outcome a m marking.word

def trial? {i f fr read} (a : @Arms i f fr read) (m : Matrix a.edge) (s : Slot) : Option (Trial a m s) := do
  let mark ← marking? fr read s
  return ⟨mark,← outcome? a m mark.word⟩

theorem trial_total {i f fr read} (a : @Arms i f fr read) (m : Matrix a.edge) (s : Slot)
    (ready : RingGroupedStereo.Ready f read) (geometry : Calibrated fr) : (trial? a m s).isSome = true := by
  obtain ⟨r,hr⟩ := Option.isSome_iff_exists.mp (marking_ready fr ready s)
  obtain ⟨o,ho⟩ := Option.isSome_iff_exists.mp (outcome_total a m r.word geometry)
  simp [trial?,hr,ho]

abbrev OrdinaryWord : Slot → Word := fun _ => []

/-- An ordinary decision applies when fewer than three ligands are tied.
Otherwise every ligand tied with a distinct partner must be promoted once. -/
inductive Decision {i f fr read} (a : @Arms i f fr read) (m : Matrix a.edge) where
  | ordinary (few : (marks a).length < 3) (o : Outcome a m OrdinaryWord) : Decision a m
  | promoted (eligible : 3 ≤ (marks a).length) (trials : List ((s : Slot) × Trial a m s))
      (allMarks : trials.map Sigma.fst = marks a) : Decision a m

def Decision.population {i f fr read a m} : @Decision i f fr read a m → List (Option (RS × RS))
  | .ordinary _ o => [o.hands]
  | .promoted _ ts _ => ts.map fun t => t.2.outcome.hands

def decision? {i f fr read} (a : @Arms i f fr read) (m : Matrix a.edge) : Option (Decision a m) := do
  if few : (marks a).length < 3 then return .ordinary few (← outcome? a m OrdinaryWord)
  else
    let row (s : Slot) := (trial? a m s).map fun t => (⟨s,t⟩ : (k : Slot) × Trial a m k)
    let ⟨ts,h⟩ ← ((marks a).mapM row).attach
    return .promoted (by omega) ts (by
      have pairs := TerminalTie.mapM_forall₂ _ _ _ h
      change List.Forall₂ (fun s t => row s = some t) (marks a) ts at pairs
      have same : List.Forall₂ (fun s (t : (k : Slot) × Trial a m k) => s = t.1) (marks a) ts := by
        apply pairs.imp
        rintro s t found
        obtain ⟨v,_,rfl⟩ := Option.map_eq_some_iff.mp found
        rfl
      exact Eq.symm (by simpa only [← List.forall₂_eq_eq_eq,List.forall₂_map_right_iff] using same))

theorem decision_total {i f fr read} (a : @Arms i f fr read) (m : Matrix a.edge)
    (ready : RingGroupedStereo.Ready f read) (geometry : Calibrated fr) : (decision? a m).isSome = true := by
  by_cases few : (marks a).length < 3
  · obtain ⟨o,ho⟩ := Option.isSome_iff_exists.mp (outcome_total a m OrdinaryWord geometry)
    simp [decision?,few,ho]
  · let row (s : Slot) := (trial? a m s).map fun t => (⟨s,t⟩ : (k : Slot) × Trial a m k)
    have all (s : Slot) : ∃ t, row s = some t := Option.isSome_iff_exists.mp (by
      simpa only [row,Option.isSome_map] using trial_total a m s ready geometry)
    obtain ⟨ts,h⟩ := RingRetainedUnitPass.collect row (marks a) (fun s _ => all s)
    have exactRows := Option.attach_eq_some _ ⟨ts,h⟩
    dsimp only [row] at exactRows
    simp [decision?,few,exactRows]

def Decision.balance {i f fr read a m} (d : @Decision i f fr read a m) (rev : Bool) :=
  readingBalance (d.population.map fun pair => pair.map (fun p => if rev then p.2 else p.1))

theorem Decision.mirror_balance {i f fr read a m} (d : @Decision i f fr read a m) :
    d.balance true = if RingActivePairReport.doubled m % 2 = 0 then -d.balance false else d.balance false := by
  have law (p : Option (RS × RS)) (mem : p ∈ d.population) :
      p.map Prod.snd = if RingActivePairReport.doubled m % 2 = 0 then (p.map Prod.fst).map RS.swap else p.map Prod.fst := by
    cases d with
    | ordinary _ o => obtain rfl := List.mem_singleton.mp mem; exact o.mirror
    | promoted _ ts _ => obtain ⟨t,_,rfl⟩ := List.mem_map.mp mem; exact t.2.outcome.mirror
  change readingBalance (d.population.map (Option.map Prod.snd)) = _
  by_cases even : RingActivePairReport.doubled m % 2 = 0
  · rw [if_pos even]
    change _ = -readingBalance (d.population.map (Option.map Prod.fst))
    rw [← LocalizedChemicalRingPromotionAggregation.readingBalance_swap]
    apply congrArg readingBalance
    rw [List.map_map]
    exact List.map_congr_left fun p hp => (law p hp).trans (if_pos even)
  · rw [if_neg even]
    apply congrArg readingBalance
    exact List.map_congr_left fun p hp => (law p hp).trans (if_neg even)

theorem Outcome.hands_unique {i f fr read a m w} (u v : @Outcome i f fr read a m w) : u.hands = v.hands := by
  have impossible (r : Ranking (trialMatrix m w) false)
      (tie : ∃ j k, j ≠ k ∧ ∀ rev, wins a rev w j = wins a rev w k) : False := by
    obtain ⟨j,k,ne,eqn⟩ := tie
    have existsRank : (RingActivePairReport.rank? (trialMatrix m w) false).isSome = true := by
      rw [RingActivePairReport.rank_of r]; rfl
    exact ne (((RingGroupedOrders.rank_iff _ false _ (RingGroupedOrders.trial_order a m false w)).mp existsRank) (eqn false))
  cases u with
  | tied t =>
    cases v with
    | tied => rfl
    | ranked r _ _ _ _ _ => exact False.elim (impossible r t)
  | ranked x y s t hs ht =>
    cases v with
    | tied tie => exact False.elim (impossible x tie)
    | ranked x' y' s' t' hu hv =>
      obtain rfl := Option.some.inj ((RingActivePairReport.rank_of x).symm.trans (RingActivePairReport.rank_of x'))
      obtain rfl := Option.some.inj ((RingActivePairReport.rank_of y).symm.trans (RingActivePairReport.rank_of y'))
      obtain rfl := Option.some.inj (hs.symm.trans hu)
      obtain rfl := Option.some.inj (ht.symm.trans hv)
      rfl

private theorem trial_hands_unique {i f fr read a m s} (u v : @Trial i f fr read a m s) :
    u.outcome.hands = v.outcome.hands := by
  obtain ⟨⟨bs,bsrc⟩,x⟩ := u
  obtain ⟨⟨cs,csrc⟩,y⟩ := v
  have eqn : bs = cs := funext fun k => (bsrc k).unique (csrc k)
  subst cs
  exact x.hands_unique y

/-- Independent choices of admissible marked traversals and strict orders
produce the same list of completed trial readings, in eligible-slot order. -/
theorem Decision.unique {i f fr read a m} (u v : @Decision i f fr read a m) : u.population = v.population := by
  cases u with
  | ordinary few x =>
    cases v with
    | ordinary _ y => exact congrArg List.singleton (x.hands_unique y)
    | promoted full _ _ => omega
  | promoted full ts all =>
    cases v with
    | ordinary few _ => omega
    | promoted _ us other =>
      have slots := all.trans other.symm
      have same (xs ys : List ((s : Slot) × Trial a m s)) (eqn : xs.map Sigma.fst = ys.map Sigma.fst) :
          (xs.map fun t => t.2.outcome.hands) = (ys.map fun t => t.2.outcome.hands) := by
        induction xs generalizing ys with
        | nil => cases ys <;> simp_all
        | cons x xs ih =>
          cases ys with
          | nil => simp at eqn
          | cons y ys =>
            obtain ⟨sx,tx⟩ := x
            obtain ⟨sy,ty⟩ := y
            obtain ⟨rfl,tail⟩ := List.cons.inj eqn
            exact congrArg₂ List.cons (trial_hands_unique tx ty) (ih ys tail)
      exact same ts us slots

/-- The majority after cancelling opposite hands gives the original letter.
The parity of the doubled unmarked scores determines its case. -/
def Decision.letters {i f fr read a m} (d : @Decision i f fr read a m) : Option Labels :=
  (survivingHand (d.balance false)).map fun h =>
    let k := if RingActivePairReport.doubled m % 2 = 0 then h.swap else h
    (RingNestedActivePair.label h k,RingNestedActivePair.label k h)

theorem Decision.refusal_iff {i f fr read a m} (d : @Decision i f fr read a m) :
    d.letters = none ↔ d.balance false = 0 := by
  simp only [Decision.letters,Option.map_eq_none_iff,survivingHand]
  split <;> simp_all <;> omega

/-- Aggregate the actual and reflected trial hands independently using the
existing proposed-2018 cancellation rule. The resulting pair of labels is
exactly the output read from the signed-magnitude parity. -/
theorem Decision.two_aggregates {i f fr read a m} (d : @Decision i f fr read a m) :
    let aggregate (rev : Bool) := (LocalizedChemicalRingPromotionAggregation.completedAggregate
      (d.population.map fun pair => pair.map (fun p => if rev then p.2 else p.1))).join
    d.letters = (do let h ← aggregate false
                    let k ← aggregate true
                    return (RingNestedActivePair.label h k,RingNestedActivePair.label k h)) := by
  dsimp only
  simp only [RingChemicalPriority.ReferenceFrame.aggregate_of_balance,Option.join_some]
  change d.letters = (do let h ← survivingHand (d.balance false)
                         let k ← survivingHand (d.balance true)
                         return (RingNestedActivePair.label h k,RingNestedActivePair.label k h))
  rw [d.mirror_balance]
  by_cases even : RingActivePairReport.doubled m % 2 = 0
  · rw [if_pos even,RingChemicalPriority.ReferenceFrame.survivingHand_neg]
    cases h : survivingHand (d.balance false) <;> simp [Decision.letters,h,even]
  · rw [if_neg even]
    cases h : survivingHand (d.balance false) <;> simp [Decision.letters,h,even]

/-- A tied ligand in a frame below the promotion threshold forces a
completed refusal. A different presentation of the four slots cannot turn
that tie into a strict order. -/
theorem Decision.ordinary_refusal {i f fr read a m} (d : @Decision i f fr read a m)
    (few : (marks a).length < 3) {s : Slot} (marked : s ∈ marks a) : d.letters = none := by
  obtain ⟨t,ne,tie⟩ := (RingGroupedOrders.marked_iff a s false).mp marked
  cases d with
  | promoted full _ _ => omega
  | ordinary _ o =>
    cases o with
    | tied => rfl
    | ranked actual _ _ _ _ _ =>
      have found : (RingActivePairReport.rank? (trialMatrix m OrdinaryWord) false).isSome = true := by
        rw [RingActivePairReport.rank_of actual]; rfl
      have inj := (RingGroupedOrders.rank_iff _ false _ (RingGroupedOrders.trial_order a m false OrdinaryWord)).mp found
      exact False.elim (ne (inj (Prod.ext tie rfl)))

theorem Decision.letters_unique {i f fr read a m} (u v : @Decision i f fr read a m) : u.letters = v.letters := by
  simp only [Decision.letters,Decision.balance,u.unique v]

end TetraStereo.Engine.RingGroupedTrials

assert_kernel_only TetraStereo.Engine.RingGroupedTrials.decision_total
assert_kernel_only TetraStereo.Engine.RingGroupedTrials.Decision.mirror_balance
assert_kernel_only TetraStereo.Engine.RingGroupedTrials.Decision.refusal_iff

assert_kernel_only TetraStereo.Engine.RingGroupedTrials.Decision.two_aggregates
