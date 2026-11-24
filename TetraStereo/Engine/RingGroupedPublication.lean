import TetraStereo.Engine.RingGroupedTrials

set_option autoImplicit false

namespace TetraStereo.Engine.RingGroupedPublication
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingNestedActivePair (Reader Labels Frame consistent)
open RingActiveDistanceSchedule (Rule View Cell Visible frozen distance height)
open RingGroupedCentre (Arms)
open RingGroupedTrials (Decision Calibrated)

/-- An absent site is either structurally outside the tetrahedral inventory
or has a completed centre decision with zero net hand. -/
inductive Local (i : Input) (f : Site i) (read : Reader i) : Option Labels → Type where
  | absent (unrecognized : i.certified.localizedOccurrenceDescriptorCenter? f = none) : Local i f read none
  | centre (fr : Frame i f) (a : Arms fr read) (m : RingActivePairReport.Matrix a.edge) (d : Decision a m)
      (frame : RingNestedActivePair.frame? i f = some fr) (arms : RingGroupedCentre.arms? fr read = some a)
      (matrix : RingActivePairReport.matrix? a.edge = some m) :
      Local i f read d.letters

def certify? (i : Input) (f : Site i) (read : Reader i) : Option ((v : Option Labels) × Local i f read v) := do
  if no : i.certified.localizedOccurrenceDescriptorCenter? f = none then return ⟨none,.absent no⟩
  let ⟨fr,hf⟩ ← (RingNestedActivePair.frame? i f).attach
  let ⟨a,ha⟩ ← (RingGroupedCentre.arms? fr read).attach
  let ⟨m,hm⟩ ← (RingActivePairReport.matrix? a.edge).attach
  let d ← RingGroupedTrials.decision? a m
  return ⟨d.letters,.centre fr a m d hf ha hm⟩

def publish? (i : Input) (f : Site i) (read : Reader i) : Cell := (certify? i f read).map Sigma.fst

theorem issued {i f read v} (got : publish? i f read = some v) : Nonempty (Local i f read v) := by
  obtain ⟨⟨_,d⟩,_,rfl⟩ := Option.map_eq_some_iff.mp got
  exact ⟨d⟩

theorem Local.consistency {i f read v} (loc : Local i f read v) : v.all consistent = true := by
  cases loc with
  | absent => rfl
  | centre fr a m d _ _ _ =>
    unfold RingGroupedTrials.Decision.letters
    cases RingChemicalPriority.ReferenceFrame.survivingHand (d.balance false) with
    | none => rfl
    | some h =>
      by_cases even : RingActivePairReport.doubled m % 2 = 0 <;> cases h <;>
        simp [even,RingNestedActivePair.label,consistent,RS.swap,pseudoRSOfRS]

theorem Local.unique {i f read v w} (l : Local i f read v) (r : Local i f read w) : v = w := by
  cases l with
  | absent no =>
    cases r with
    | absent => rfl
    | centre fr _ _ _ _ _ _ => exact nomatch no.symm.trans fr.recognized
  | centre fr a m d hf ha hm =>
    cases r with
    | absent no => exact nomatch no.symm.trans fr.recognized
    | centre fr' a' m' e hf' ha' hm' =>
      obtain rfl := Option.some.inj (hf.symm.trans hf')
      obtain rfl := Option.some.inj (ha.symm.trans ha')
      obtain rfl := Option.some.inj (hm.symm.trans hm')
      exact d.letters_unique e

theorem Local.four {i f read v} (loc : Local i f read (some v)) :
    (RingRetainedAuxiliary.frame i.certified f).length = 4 := by
  have general {value} (l : Local i f read value) (positive : value.isSome = true) :
      (RingRetainedAuxiliary.frame i.certified f).length = 4 := by
    cases l with
    | absent => contradiction
    | centre fr _ _ _ _ _ _ => exact fr.four
  exact general loc rfl

def publicationTable (i : Input) : RingActiveDistanceSchedule.Table i :=
  RingActiveDistanceSchedule.table (publish? i) (height i + 1)

def state (i : Input) : View i := RingActiveDistanceSchedule.snapshot (publicationTable i)

theorem state_eq (i : Input) (q : Site i) : state i q = publish? i q (frozen (state i) q) := by
  have eqn : state i = RingActiveDistanceSchedule.evaluate (publish? i) :=
    RingActiveDistanceSchedule.snapshot_table ..
  rw [eqn,RingActiveDistanceSchedule.evaluate_eq]

/-- Every read at an earlier distance is bound to the publication at that
exact original address. Same-distance sites are evaluated independently. -/
inductive Derivation (i : Input) : Site i → Option Labels → Prop where
  | step {q v} (before : View i) (localRule : Nonempty (Local i q (frozen before q) v))
      (earlier : ∀ t, Visible q t → ∀ w, before t = some w → Derivation i t w) : Derivation i q v

theorem derivation {i : Input} {q : Site i} {v} (hit : state i q = some v) : Derivation i q v := by
  suffices ∀ n (t : Site i), height i - distance t = n → ∀ w, state i t = some w → Derivation i t w from
    this _ q rfl v hit
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro t depth w found
    refine .step (state i) (issued ((state_eq i t).symm.trans found)) ?_
    intro s vis a hs
    have upper := RingActiveDistanceSchedule.distance_bound s
    have deeper := vis.2.1
    exact ih _ (by omega) s rfl a hs

private theorem observed {i : Input} {q : Site i}
    (known : ∀ t, Visible q t → (state i t).isSome = true) :
    RingGroupedStereo.Ready q (frozen (state i) q) := by
  intro t on
  by_cases visible : Visible q t.occurrence
  · obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp (known t.occurrence visible)
    obtain ⟨loc⟩ := issued ((state_eq i t.occurrence).symm.trans hv)
    refine ⟨v,by simp [frozen,on,visible.2.1,visible.2.2,hv],loc.consistency,?_⟩
    intro empty
    cases v with
    | none => rfl
    | some labels =>
      have four := loc.four
      have size := RingFrontierProfileShape.cut_frame t
      change i.certified.executableLocalizedRerootChildren t = [] at empty
      rw [four,empty] at size
      contradiction
  · have masked : ¬(distance q < distance t.occurrence ∧ t.occurrence.val.node.current? ≠ some q.val.root) :=
      fun h => visible ⟨on,h⟩
    exact ⟨none,by simp [frozen,on,masked],rfl,fun _ => rfl⟩

/-- Every real centre has its four physical slots and a nondegenerate
readback. These are molecular frame/geometry conditions only. -/
def Physical (i : Input) := ∀ (f : Site i) (c : i.certified.TetrahedralCenter),
  i.certified.localizedOccurrenceDescriptorCenter? f = some c →
    ∃ fr, RingNestedActivePair.frame? i f = some fr ∧ Calibrated fr

theorem complete {i : Input} (geometry : Physical i) (q : Site i) : (state i q).isSome = true := by
  suffices ∀ n (t : Site i), height i - distance t = n → (state i t).isSome = true from this _ q rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro t depth
    have ready := observed (q := t) (fun s vis => by
      have upper := RingActiveDistanceSchedule.distance_bound s
      have deeper := vis.2.1
      exact ih _ (by omega) s rfl)
    rw [state_eq]
    cases recog : i.certified.localizedOccurrenceDescriptorCenter? t with
    | none => simp [publish?,certify?,recog]
    | some c =>
      obtain ⟨fr,hf,cal⟩ := geometry t c recog
      obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp (RingGroupedCentre.arms_ready fr ready)
      obtain ⟨m,hm⟩ := Option.isSome_iff_exists.mp a.matrix_total
      obtain ⟨d,hd⟩ := Option.isSome_iff_exists.mp (RingGroupedTrials.decision_total a m ready cal)
      simp [publish?,certify?,recog,Option.attach_eq_some _ ⟨fr,hf⟩,Option.attach_eq_some _ ⟨a,ha⟩,
        Option.attach_eq_some _ ⟨m,hm⟩,hd]

/-- Every scheduled centre can read all the frozen labels of its own root. -/
theorem ready {i : Input} (geometry : Physical i) (q : Site i) :
    RingGroupedStereo.Ready q (frozen (state i) q) :=
  observed (fun s _ => complete geometry s)

/-- A molecular derivation supplies an actual outcome at every visible
deeper site. Its local orders and marked trials may be chosen independently
of the executable decision. -/
inductive Molecular (i : Input) : Site i → Option Labels → Prop where
  | step {q v} (before : View i) (localRule : Nonempty (Local i q (frozen before q) v))
      (covered : ∀ t, Visible q t → (before t).isSome = true)
      (deeper : ∀ t, Visible q t → ∀ w, before t = some w → Molecular i t w) : Molecular i q v

private theorem freeze_eq {i : Input} (q : Site i) (s t : View i)
    (eqn : ∀ u, Visible q u → s u = t u) : frozen s q = frozen t q := by
  funext u
  unfold frozen
  split_ifs with other allowed
  · rfl
  · exact eqn u ⟨of_not_not other,allowed⟩
  · rfl

/-- At every original address the schedule returns exactly the independently
derivable local result, including structural absence and cancellation. -/
theorem molecular_iff {i : Input} (geometry : Physical i) (q : Site i) (v : Option Labels) :
    state i q = some v ↔ Molecular i q v := by
  constructor
  · suffices ∀ n (t : Site i), height i - distance t = n → ∀ w, state i t = some w → Molecular i t w from
      this _ q rfl v
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro t depth w found
      refine .step (state i) (issued ((state_eq i t).symm.trans found)) (fun s _ => complete geometry s) ?_
      intro s vis z hz
      have upper := RingActiveDistanceSchedule.distance_bound s
      have deeper := vis.2.1
      exact ih _ (by omega) s rfl z hz
  · intro deriv
    induction deriv with
    | @step q v before localRule covered _ ih =>
      have agree := freeze_eq q before (state i) (fun t vis => by
        obtain ⟨w,atCell⟩ := Option.isSome_iff_exists.mp (covered t vis)
        exact atCell.trans (ih t vis w atCell).symm)
      rw [agree] at localRule
      obtain ⟨z,hz⟩ := Option.isSome_iff_exists.mp (complete geometry q)
      obtain ⟨calculated⟩ := issued ((state_eq i q).symm.trans hz)
      exact hz.trans (congrArg some (calculated.unique localRule.some))

theorem unique_state {i : Input} (s : View i) (laws : ∀ q, s q = publish? i q (frozen s q)) : s = state i := by
  exact (RingActiveDistanceSchedule.unique _ s laws).trans (RingActiveDistanceSchedule.snapshot_table ..).symm

end TetraStereo.Engine.RingGroupedPublication

assert_kernel_only TetraStereo.Engine.RingGroupedPublication.derivation
assert_kernel_only TetraStereo.Engine.RingGroupedPublication.complete
assert_kernel_only TetraStereo.Engine.RingGroupedPublication.unique_state
