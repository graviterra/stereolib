import TetraStereo.Engine.RingRebuiltStereo
import TetraStereo.Engine.RingOccurrenceStereo

/-! # An independent local decision relation at a fixed prior reader

`Decides i f read v` is stated with rebuilt constitutional comparisons,
occurrence-by-occurrence stereo comparisons, explicit strict permutations, coordinate
readbacks on both geometries and the completed-aggregate cancellation rule.
It does not mention the grouped arms, matrix, decision or publication, and it
does not mention a geometric signature. -/

set_option autoImplicit false

namespace TetraStereo.Engine.RingGraphLocal
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Frame Reader Labels)
open RingActivePairReport (Slot Score Matrix Ranking)
open RingRetainedChemicalTrace (Word)
open RingRetainedStereoDecision (Result)
open RingGroupedCentre (Arms cursor)
open RingGroupedOrders (trialMatrix marks)
open RingGroupedTrials (Outcome Decision Trial)
open RingActiveDistanceSchedule (frozen)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
attribute [local instance] lexOrd

/-! ## Definitions -/

/-- The signed pair of one directed ligand comparison. A strict rebuilt
constitutional order has unit magnitude on both geometries. A constitutional
tie takes both signed magnitudes from the rebuilt molecular comparison. -/
inductive PairScore (i : Input) (f a b : Site i) (read : Reader i) : Score → Prop where
  | below (prior : RingZeroDuplicateMass.compareAt? i f a b = some .lt) : PairScore i f a b read (-1,-1)
  | above (prior : RingZeroDuplicateMass.compareAt? i f a b = some .gt) : PairScore i f a b read (1,1)
  | stereo {v w : Result} (prior : RingZeroDuplicateMass.compareAt? i f a b = some .eq)
      (molecular : RingOccurrenceStereo.comparison? i f a b read = some (v,w)) :
      PairScore i f a b read (v.score,w.score)

/-- Eligible slots: tied on the actual geometry with a distinct slot. -/
def tiedSlots (sc : Slot → Slot → Score) : List Slot :=
  (List.finRange 4).filter fun j => (List.finRange 4).any fun k => j != k && (sc j k).1 == 0

/-- A Rule 6 word decides only a pair tied on both geometries. -/
def rule6Refine (ordinary : Score) (x y : Word) : Score :=
  if ordinary = (0,0) then let k := RingSingleTieCompletion.unitScore (compare x y); (k,k) else ordinary

def trialScore (sc : Slot → Slot → Score) (w : Slot → Word) (j k : Slot) : Score :=
  rule6Refine (sc j k) (w j) (w k)

def pairSide (rev : Bool) (s : Score) : Int := if rev then s.2 else s.1

/-- Both directed scores place `j` strictly above `k` on this geometry. -/
def Beats (t : Slot → Slot → Score) (rev : Bool) (j k : Slot) : Prop :=
  0 < pairSide rev (t j k) ∧ pairSide rev (t k j) < 0

/-- The atom distinguished throughout a Rule 6 trial for this slot. -/
def wordAtom {i : Input} {f : Site i} (fr : Frame i f) (s : Slot) : Nat := (fr.atoms [s]).head!

/-- One completed trial. A tie on the actual geometry gives no hand. Two
strict permutations give the coordinate hand of each geometry. A strict order
on a frame without a readback has no reading. -/
inductive TrialReading {i : Input} {f : Site i} (fr : Frame i f) (t : Slot → Slot → Score) :
    Option (RS × RS) → Prop where
  | tied {j k : Slot} (distinct : j ≠ k) (tie : (t j k).1 = 0) : TrialReading fr t none
  | ranked {actual reflected : List Slot} {hand mirrorHand : RS}
      (actualPerm : actual.Perm (List.finRange 4)) (actualOrder : actual.Pairwise (Beats t false))
      (reflectedPerm : reflected.Perm (List.finRange 4)) (reflectedOrder : reflected.Pairwise (Beats t true))
      (physical : readback? (inputGeometry i.certified) (fr.atoms actual) = some hand)
      (mirrorPhysical : readback? (mirror (inputGeometry i.certified)) (fr.atoms reflected) = some mirrorHand) :
      TrialReading fr t (some (hand,mirrorHand))

/-- One Rule 6 trial per listed slot, in order. Every marked ligand word is a
fresh rebuilt read with that slot's atom distinguished. -/
inductive TrialList {i : Input} {f : Site i} (fr : Frame i f) (read : Reader i) (sc : Slot → Slot → Score) :
    List Slot → List (Option (RS × RS)) → Prop where
  | nil : TrialList fr read sc [] []
  | cons {s : Slot} {rest : List Slot} {x : Option (RS × RS)} {xs : List (Option (RS × RS))}
      (w : Slot → Word)
      (words : ∀ k, ∃ e, RingRebuiltStereo.arm? i read (wordAtom fr s) (cursor fr k) = some e ∧ e.2.word = w k)
      (reading : TrialReading fr (trialScore sc w) x) (later : TrialList fr read sc rest xs) :
      TrialList fr read sc (s :: rest) (x :: xs)

/-- Fewer than three eligible slots give one unpromoted reading. Otherwise
every eligible slot is promoted exactly once. -/
inductive Population {i : Input} {f : Site i} (fr : Frame i f) (read : Reader i) (sc : Slot → Slot → Score) :
    List (Option (RS × RS)) → Prop where
  | ordinary {x : Option (RS × RS)} (few : (tiedSlots sc).length < 3)
      (reading : TrialReading fr (trialScore sc fun _ => ([] : Word)) x) : Population fr read sc [x]
  | promoted {xs : List (Option (RS × RS))} (many : 3 ≤ (tiedSlots sc).length)
      (trials : TrialList fr read sc (tiedSlots sc) xs) : Population fr read sc xs

/-- Cancel opposite hands on one geometry. -/
def handAggregate (xs : List (Option (RS × RS))) (rev : Bool) : Option RS :=
  (LocalizedChemicalRingPromotionAggregation.completedAggregate
    (xs.map fun pair => pair.map (fun p => if rev then p.2 else p.1))).join

/-- The original and reflected letters from the two surviving hands. -/
def lettersOf (xs : List (Option (RS × RS))) : Option Labels := do
  let h ← handAggregate xs false
  let k ← handAggregate xs true
  return (RingNestedActivePair.label h k,RingNestedActivePair.label k h)

/-- The independent local decision of one retained occurrence. -/
inductive Decides (i : Input) (f : Site i) (read : Reader i) : Option Labels → Prop where
  | absent (unrecognized : i.certified.localizedOccurrenceDescriptorCenter? f = none) : Decides i f read none
  | centre {xs : List (Option (RS × RS))} (fr : Frame i f) (sc : Slot → Slot → Score)
      (diagonal : ∀ j, sc j j = (0,0))
      (edges : ∀ j k, j ≠ k → PairScore i f (fr.direction j).val (fr.direction k).val read (sc j k))
      (population : Population fr read sc xs) : Decides i f read (lettersOf xs)

theorem Decides.consistency {i f read v} (law : Decides i f read v) :
    v.all RingNestedActivePair.consistent = true := by
  cases law with
  | absent => rfl
  | @centre xs _ _ _ _ _ =>
    unfold lettersOf
    cases hs : handAggregate xs false with
    | none => rfl
    | some s =>
      cases ht : handAggregate xs true with
      | none => rfl
      | some t => cases s <;> cases t <;> decide

/-! ## Uniqueness, with no readiness or coordinate premise -/

theorem PairScore.unique {i : Input} {f a b : Site i} {read : Reader i} {s t : Score}
    (x : PairScore i f a b read s) (y : PairScore i f a b read t) : s = t := by
  cases x with
  | below p =>
    cases y with
    | below _ => rfl
    | above q => exact absurd (Option.some.inj (p.symm.trans q)) (by decide)
    | stereo q _ => exact absurd (Option.some.inj (p.symm.trans q)) (by decide)
  | above p =>
    cases y with
    | below q => exact absurd (Option.some.inj (p.symm.trans q)) (by decide)
    | above _ => rfl
    | stereo q _ => exact absurd (Option.some.inj (p.symm.trans q)) (by decide)
  | stereo p hm =>
    cases y with
    | below q => exact absurd (Option.some.inj (p.symm.trans q)) (by decide)
    | above q => exact absurd (Option.some.inj (p.symm.trans q)) (by decide)
    | stereo _ hn =>
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (hm.symm.trans hn))
      rfl

private theorem pairwise_either {α : Type} {R : α → α → Prop} {l : List α} (h : l.Pairwise R)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) (ne : a ≠ b) : R a b ∨ R b a := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    obtain ⟨first,rest⟩ := List.pairwise_cons.mp h
    rcases List.mem_cons.mp ha with ax | ha'
    · rcases List.mem_cons.mp hb with bx | hb'
      · exact (ne (ax.trans bx.symm)).elim
      · exact Or.inl (by rw [ax]; exact first b hb')
    · rcases List.mem_cons.mp hb with bx | hb'
      · exact Or.inr (by rw [bx]; exact first a ha')
      · exact ih rest ha' hb'

theorem TrialReading.unique {i : Input} {f : Site i} {fr : Frame i f} {t : Slot → Slot → Score}
    {x y : Option (RS × RS)} (u : TrialReading fr t x) (v : TrialReading fr t y) : x = y := by
  have clash {j k : Slot} (ne : j ≠ k) (tie : (t j k).1 = 0) {ss : List Slot}
      (perm : ss.Perm (List.finRange 4)) (order : ss.Pairwise (Beats t false)) : False := by
    have mj : j ∈ ss := perm.mem_iff.mpr (by simp)
    have mk : k ∈ ss := perm.mem_iff.mpr (by simp)
    rcases pairwise_either order mj mk ne with win | win
    · have pos : 0 < (t j k).1 := win.1
      omega
    · have neg : (t j k).1 < 0 := win.2
      omega
  cases u with
  | tied ne tie =>
    cases v with
    | tied _ _ => rfl
    | ranked ps os _ _ _ _ => exact (clash ne tie ps os).elim
  | ranked ps os pt ot hs hm =>
    cases v with
    | tied ne tie => exact (clash ne tie ps os).elim
    | ranked ps' os' pt' ot' hs' hm' =>
      obtain rfl := List.Perm.eq_of_pairwise
        (fun a b _ _ ab ba => False.elim (not_lt_of_gt ab.1 ba.2)) os os' (ps.trans ps'.symm)
      obtain rfl := List.Perm.eq_of_pairwise
        (fun a b _ _ ab ba => False.elim (not_lt_of_gt ab.1 ba.2)) ot ot' (pt.trans pt'.symm)
      obtain rfl := Option.some.inj (hs.symm.trans hs')
      obtain rfl := Option.some.inj (hm.symm.trans hm')
      rfl

theorem TrialList.unique {i : Input} {f : Site i} {fr : Frame i f} {read : Reader i}
    {sc : Slot → Slot → Score} {slots : List Slot} {xs ys : List (Option (RS × RS))}
    (u : TrialList fr read sc slots xs) (v : TrialList fr read sc slots ys) : xs = ys := by
  induction u generalizing ys with
  | nil =>
    cases v with
    | nil => rfl
  | cons w words reading _ ih =>
    cases v with
    | cons w' words' reading' later' =>
      have same : w = w' := funext fun k => by
        obtain ⟨e,he,hw⟩ := words k
        obtain ⟨e',he',hw'⟩ := words' k
        obtain rfl := Option.some.inj (he.symm.trans he')
        exact hw.symm.trans hw'
      subst same
      exact congrArg₂ List.cons (reading.unique reading') (ih later')

theorem Population.unique {i : Input} {f : Site i} {fr : Frame i f} {read : Reader i}
    {sc : Slot → Slot → Score} {xs ys : List (Option (RS × RS))}
    (u : Population fr read sc xs) (v : Population fr read sc ys) : xs = ys := by
  cases u with
  | ordinary few x =>
    cases v with
    | ordinary _ y => exact congrArg (fun z => [z]) (x.unique y)
    | promoted many _ => omega
  | promoted many ts =>
    cases v with
    | ordinary few _ => omega
    | promoted _ us => exact ts.unique us

private theorem frame_unique {i : Input} {f : Site i} (x y : Frame i f) : x = y := by
  obtain ⟨c,hc,four,ids,hi,p⟩ := x
  obtain ⟨c',hc',four',ids',hi',p'⟩ := y
  obtain rfl := Option.some.inj (hc.symm.trans hc')
  obtain rfl := Option.some.inj (hi.symm.trans hi')
  rfl

/-- Independent choices of frame, score table, marked words and strict
permutations publish the same value. -/
theorem Decides.unique {i : Input} {f : Site i} {read : Reader i} {v w : Option Labels}
    (x : Decides i f read v) (y : Decides i f read w) : v = w := by
  cases x with
  | absent no =>
    cases y with
    | absent _ => rfl
    | centre fr _ _ _ _ => exact nomatch no.symm.trans fr.recognized
  | centre fr sc diag edges pop =>
    cases y with
    | absent no => exact nomatch no.symm.trans fr.recognized
    | centre fr' sc' diag' edges' pop' =>
      obtain rfl := frame_unique fr fr'
      have same : sc = sc' := by
        funext j k
        by_cases eqn : j = k
        · subst eqn
          exact (diag j).trans (diag' j).symm
        · exact (edges j k eqn).unique (edges' j k eqn)
      subst same
      exact congrArg lettersOf (pop.unique pop')

/-! ## From the grouped certificate to the independent relation -/

private theorem zero_self : compare (0 : Int) 0 = Ordering.eq := by decide

private theorem score_some {i : Input} {f a b : Site i} {read : Reader i} {k : Score}
    (got : RingGroupedStereo.score? i f a b read = some k) :
    ∃ v, RingGroupedStereo.comparison? i f a b read = some v ∧ RingGroupedStereo.scores v = k := by
  obtain ⟨v,hv,rest⟩ := Option.bind_eq_some_iff.mp got
  refine ⟨v,hv,?_⟩
  clear got hv
  by_cases ok : RingGroupedStereo.scores v ∈ RingActivePairs.molecularValues <;> simp_all [guard]

/-- The uncached retained edge read is an independent pair score. -/
theorem PairScore.of_incident {i : Input} {f a b : Site i} {read : Reader i} {s : Score}
    (ready : RingGroupedStereo.Ready f read)
    (src : RingGroupedCentre.incidentScore? i f a b read = some s) : PairScore i f a b read s := by
  unfold RingGroupedCentre.incidentScore? at src
  obtain ⟨p,hp,rest⟩ := Option.bind_eq_some_iff.mp src
  have prior : RingZeroDuplicateMass.compareAt? i f a b = some (cipTraceOutcome p) := by
    simp only [RingZeroDuplicateMass.compareAt_agrees,hp,Option.map_some]
  cases stage : cipTraceOutcome p with
  | lt =>
    simp only [stage] at rest prior
    obtain rfl := Option.some.inj rest
    exact .below prior
  | eq =>
    simp only [stage] at rest prior
    obtain ⟨⟨v,w⟩,hv,rfl⟩ := score_some rest
    exact .stereo prior ((RingOccurrenceStereo.comparison_agrees i f a b read ready).trans hv)
  | gt =>
    simp only [stage] at rest prior
    obtain rfl := Option.some.inj rest
    exact .above prior

/-- A zero actual score between distinct slots is exactly an equal priority. -/
private theorem tie_key {i : Input} {f : Site i} {fr : Frame i f} {read : Reader i} (a : Arms fr read)
    (m : Matrix a.edge) {j k : Slot} (ne : j ≠ k) : (m.get j k).1 = 0 ↔ a.key false j = a.key false k := by
  have order := a.matrix_order m false j k
  have value : RingOrdinaryPairRefusal.score m false j k = (m.get j k).1 := by
    simp [RingOrdinaryPairRefusal.score,ne]
  constructor
  · intro zero
    exact Std.compare_eq_eq_iff_eq.mp
      (order.symm.trans ((congrArg (fun z : Int => compare z 0) (value.trans zero)).trans zero_self))
  · intro same
    have diagonal := a.matrix_order m false k k
    have corner : RingOrdinaryPairRefusal.score m false k k = 0 := by simp [RingOrdinaryPairRefusal.score]
    rw [same] at order
    rw [corner] at diagonal
    have tied : RingOrdinaryPairRefusal.score m false j k = 0 :=
      Std.compare_eq_eq_iff_eq.mp (order.trans (diagonal.symm.trans zero_self))
    exact value.symm.trans tied

private theorem tiedSlots_grouped {i : Input} {f : Site i} {fr : Frame i f} {read : Reader i} (a : Arms fr read)
    (m : Matrix a.edge) {sc : Slot → Slot → Score} (hs : ∀ j k, j ≠ k → sc j k = m.get j k) :
    tiedSlots sc = marks a := by
  unfold tiedSlots RingGroupedOrders.marks
  apply List.filter_congr
  intro j _
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,Bool.and_eq_true,beq_iff_eq,bne_iff_ne]
  constructor
  · rintro ⟨k,mem,ne,zero⟩
    rw [hs j k ne] at zero
    exact ⟨k,mem,ne,(tie_key a m ne).mp zero⟩
  · rintro ⟨k,mem,ne,same⟩
    refine ⟨k,mem,ne,?_⟩
    rw [hs j k ne]
    exact (tie_key a m ne).mpr same

private theorem trial_scores {r : RingActivePairReport.Reader} {m : Matrix r} {sc : Slot → Slot → Score}
    (hs : ∀ j k, j ≠ k → sc j k = m.get j k) (w : Slot → Word) (j k : Slot) (ne : j ≠ k) :
    trialScore sc w j k = RingGroupedOrders.refined m w j k :=
  congrArg (fun s : Score => rule6Refine s (w j) (w k)) (hs j k ne)

private theorem reading_of {i : Input} {f : Site i} {fr : Frame i f} {read : Reader i} {a : Arms fr read}
    {m : Matrix a.edge} {w : Slot → Word} (o : Outcome a m w) {t : Slot → Slot → Score}
    (ht : ∀ j k, j ≠ k → t j k = RingGroupedOrders.refined m w j k) : TrialReading fr t o.hands := by
  cases o with
  | tied witness =>
    obtain ⟨j,k,ne,eqn⟩ := witness
    have order := RingGroupedOrders.trial_order a m false w j k
    have diagonal := RingGroupedOrders.trial_order a m false w k k
    have corner : RingOrdinaryPairRefusal.score (trialMatrix m w) false k k = 0 := by
      simp [RingOrdinaryPairRefusal.score]
    rw [eqn false] at order
    rw [corner] at diagonal
    have zero : RingOrdinaryPairRefusal.score (trialMatrix m w) false j k = 0 :=
      Std.compare_eq_eq_iff_eq.mp (order.trans (diagonal.symm.trans zero_self))
    have first : ((trialMatrix m w).get j k).1 = 0 := by
      simpa [RingOrdinaryPairRefusal.score,ne] using zero
    show TrialReading fr t none
    exact .tied ne ((congrArg Prod.fst (ht j k ne)).trans first)
  | ranked actual reflected hand mirrorHand physical mirrorPhysical =>
    have lift (rev : Bool) (r : Ranking (trialMatrix m w) rev) : r.slots.Pairwise (Beats t rev) := by
      have distinct : r.slots.Nodup := r.perm.nodup_iff.mpr (List.nodup_finRange 4)
      apply (List.pairwise_and_iff.mpr (And.intro distinct r.higher)).imp
      rintro j k ⟨ne,win⟩
      unfold Beats
      rw [ht j k ne,ht k j ne.symm]
      exact win
    show TrialReading fr t (some (hand,mirrorHand))
    exact .ranked actual.perm (lift false actual) reflected.perm (lift true reflected) physical mirrorPhysical

private theorem trials_of {i : Input} {f : Site i} {fr : Frame i f} {read : Reader i}
    (ready : RingGroupedStereo.Ready f read) {a : Arms fr read} {m : Matrix a.edge}
    {sc : Slot → Slot → Score} (hs : ∀ j k, j ≠ k → sc j k = m.get j k) :
    ∀ ts : List ((s : Slot) × Trial a m s),
      TrialList fr read sc (ts.map Sigma.fst) (ts.map fun t => t.2.outcome.hands) := by
  intro ts
  induction ts with
  | nil => exact .nil
  | cons t rest ih =>
    simp only [List.map_cons]
    refine .cons t.2.marking.word ?_ (reading_of t.2.outcome (trial_scores hs t.2.marking.word)) ih
    intro k
    obtain ⟨newArm,oldArm,hn,ho,_,word,_⟩ := RingRebuiltStereo.arm_invariants ready (wordAtom fr t.1)
      (cursor fr k) (RingGroupedCentre.valid fr k) (fr.direction k).property.1
    have eqn := (t.2.marking.source k).unique (RingGroupedMark.arm_source ho).2
    exact ⟨newArm,hn,word.trans (congrArg (fun b : RingStereoSiblingPass.Branch => b.word) eqn).symm⟩

private theorem population_of {i : Input} {f : Site i} {fr : Frame i f} {read : Reader i}
    (ready : RingGroupedStereo.Ready f read) (a : Arms fr read) (m : Matrix a.edge) (d : Decision a m)
    {sc : Slot → Slot → Score} (hs : ∀ j k, j ≠ k → sc j k = m.get j k) :
    Population fr read sc d.population := by
  have slots := tiedSlots_grouped a m hs
  cases d with
  | ordinary few o =>
    show Population fr read sc [o.hands]
    exact .ordinary (by rw [slots]; exact few) (reading_of o (trial_scores hs RingGroupedTrials.OrdinaryWord))
  | promoted many ts allMarks =>
    show Population fr read sc (ts.map fun t => t.2.outcome.hands)
    refine .promoted (by rw [slots]; exact many) ?_
    rw [slots,← allMarks]
    exact trials_of ready hs ts

/-- The two independently cancelled geometries give the grouped letters. -/
private theorem letters_grouped {i : Input} {f : Site i} {fr : Frame i f} {read : Reader i} {a : Arms fr read}
    {m : Matrix a.edge} (d : Decision a m) : d.letters = lettersOf d.population :=
  d.two_aggregates

def offDiagonal (g : Slot → Slot → Score) (j k : Slot) : Score := if j = k then (0,0) else g j k

theorem offDiagonal_ne (g : Slot → Slot → Score) {j k : Slot} (ne : j ≠ k) : offDiagonal g j k = g j k :=
  if_neg ne

theorem offDiagonal_self (g : Slot → Slot → Score) (j : Slot) : offDiagonal g j j = (0,0) := if_pos rfl

/-- Every grouped local certificate at a ready reader is an independent
decision with the same value. -/
theorem Decides.of_grouped {i : Input} {f : Site i} {read : Reader i} {v : Option Labels}
    (ready : RingGroupedStereo.Ready f read) (loc : RingGroupedPublication.Local i f read v) :
    Decides i f read v := by
  cases loc with
  | absent no => exact .absent no
  | centre fr a m d hf ha hm =>
    have edges : ∀ j k, j ≠ k →
        PairScore i f (fr.direction j).val (fr.direction k).val read (offDiagonal m.get j k) := by
      intro j k ne
      rw [offDiagonal_ne m.get ne]
      exact PairScore.of_incident ready ((a.edge_source j k ne).trans (m.found j k ne))
    rw [letters_grouped d]
    exact .centre fr (offDiagonal m.get) (offDiagonal_self m.get) edges
      (population_of ready a m d fun _ _ ne => offDiagonal_ne m.get ne)

/-! ## Canonical input: admitted coordinates and a ready prior reader -/

private theorem grouped_total {i : Input} {f : Site i} {read : Reader i}
    (coords : LocalizedChemicalRing.coordinatesAdmitted i = true) (ready : RingGroupedStereo.Ready f read) :
    ∃ v, Nonempty (RingGroupedPublication.Local i f read v) := by
  cases recog : i.certified.localizedOccurrenceDescriptorCenter? f with
  | none => exact ⟨none,⟨.absent recog⟩⟩
  | some c =>
    obtain ⟨fr,hf,cal⟩ := RingGroupedGeometry.physical coords f c recog
    obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp (RingGroupedCentre.arms_ready fr ready)
    obtain ⟨m,hm⟩ := Option.isSome_iff_exists.mp a.matrix_total
    obtain ⟨d,_⟩ := Option.isSome_iff_exists.mp (RingGroupedTrials.decision_total a m ready cal)
    exact ⟨d.letters,⟨.centre fr a m d hf ha hm⟩⟩

theorem Decides.inhabited {i : Input} {f : Site i} {read : Reader i}
    (coords : LocalizedChemicalRing.coordinatesAdmitted i = true) (ready : RingGroupedStereo.Ready f read) :
    ∃ v, Decides i f read v := by
  obtain ⟨v,⟨loc⟩⟩ := grouped_total coords ready
  exact ⟨v,Decides.of_grouped ready loc⟩

theorem Decides.existsUnique {i : Input} {f : Site i} {read : Reader i}
    (coords : LocalizedChemicalRing.coordinatesAdmitted i = true) (ready : RingGroupedStereo.Ready f read) :
    ∃! v, Decides i f read v := by
  obtain ⟨v,hv⟩ := Decides.inhabited coords ready
  exact ⟨v,hv,fun w hw => hw.unique hv⟩

/-- On canonical input the independent relation and the grouped publication
certificate issue exactly the same values, at any ready prior reader. -/
theorem Decides.iff_grouped {i : Input} {f : Site i} {read : Reader i}
    (coords : LocalizedChemicalRing.coordinatesAdmitted i = true) (ready : RingGroupedStereo.Ready f read)
    (v : Option Labels) : Decides i f read v ↔ Nonempty (RingGroupedPublication.Local i f read v) := by
  constructor
  · intro own
    obtain ⟨z,⟨loc⟩⟩ := grouped_total coords ready
    have same : v = z := own.unique (Decides.of_grouped ready loc)
    subst same
    exact ⟨loc⟩
  · rintro ⟨loc⟩
    exact Decides.of_grouped ready loc

/-- At the scheduled frozen reader the relation holds exactly at the
published cell, for every retained occurrence. -/
theorem Decides.iff_state {i : Input} (coords : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (q : Site i) (v : Option Labels) :
    Decides i q (frozen (RingGroupedPublication.state i) q) v ↔ RingGroupedPublication.state i q = some v := by
  have phys := RingGroupedGeometry.physical coords
  have ready := RingGroupedPublication.ready phys q
  constructor
  · intro own
    obtain ⟨z,hz⟩ := Option.isSome_iff_exists.mp (RingGroupedPublication.complete phys q)
    obtain ⟨loc⟩ := RingGroupedPublication.issued ((RingGroupedPublication.state_eq i q).symm.trans hz)
    exact hz.trans (congrArg some (own.unique (Decides.of_grouped ready loc)).symm)
  · intro hit
    obtain ⟨loc⟩ := RingGroupedPublication.issued ((RingGroupedPublication.state_eq i q).symm.trans hit)
    exact Decides.of_grouped ready loc

end TetraStereo.Engine.RingGraphLocal

assert_kernel_only TetraStereo.Engine.RingGraphLocal.Decides.unique
assert_kernel_only TetraStereo.Engine.RingGraphLocal.Decides.existsUnique
assert_kernel_only TetraStereo.Engine.RingGraphLocal.Decides.iff_state
