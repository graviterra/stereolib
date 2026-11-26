import TetraStereo.Engine.RingFrameTransport
import Batteries.Tactic.OpenPrivate

/-! The tetrahedral local rule factored through finite pair-comparison data.
The data are independent inputs: no key, rank, trial result or label is stored. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingPairwisePublication
open OneCenter CertifiedLocalizedCIPInput
open LocalizedGenericMarkedRecalculation hiding strict
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Frame Reader Labels label)
open RingActivePairReport (Slot)
open RingRetainedChemicalTrace (Word)
open RingFullPathEligibility (Key)
open RingFullPathTrialReadings (trialKey markWords?)
open RingStereoSiblingPass (order)
open private trial_eq from TetraStereo.Engine.RingFullPathTrialParity
open private strict strict_injective from TetraStereo.Engine.RingFullPathTrialReadings

abbrev TrialWord := List (List Word)
abbrev Directions := Slot → Slot → Bool

def directions (w : Slot → TrialWord) : Directions := fun a b => decide (w a < w b)
def tied (d : Directions) (a b : Slot) := !d a b && !d b a

def rows (d : Directions) : List Slot := (List.finRange 4).mergeSort fun a b => !d a b

def strictData (d : Directions) : Bool :=
  (List.finRange 4).all fun a => (List.finRange 4).all fun b => a == b || !tied d a b

def tiedSlots (d : Directions) : List Slot :=
  (List.finRange 4).filter fun a => (List.finRange 4).any fun b => a != b && tied d a b

def candidates (d : Directions) : List Slot :=
  let ts := tiedSlots d
  if 3 ≤ ts.length then ts else []

def trials (d : Directions) : List (Option Slot) :=
  match candidates d with
  | [] => [none]
  | s::ss => (s::ss).map some

def reversals (actual reflected : Directions) : Nat :=
  LocalizedChemicalRing.ConstitutionalPartition.pairs.countP fun p => actual p.2 p.1 != reflected p.2 p.1

def ballot (d : Directions) (sense : List Slot → Option RS) : Option RS :=
  if strictData d then sense (rows d) else none

/-- Independent ordinary and marked comparison directions. Each marking trial
can supply its own matrix, including unresolved coverage. -/
structure Data where
  ordinary : Bool → Directions
  marked : Bool → Option Slot → Option Directions

def Data.ballots (d : Data) (sense : Bool → List Slot → Option RS) :
    Option (List (Option Slot × Option RS)) :=
  (trials (d.ordinary false)).mapM fun s => do
    let comparison ← d.marked false s
    return (s,ballot comparison (sense false))

def Data.letters (d : Data) (hands : List (Option RS)) : Option Labels :=
  (RingChemicalPriority.ReferenceFrame.survivingHand
    (LocalizedChemicalRingPromotionAggregation.readingBalance hands)).map fun h =>
      let k := if reversals (d.ordinary false) (d.ordinary true) % 2 = 0 then h.swap else h
      (label h k,label k h)

/-- A comparison-only local evaluator, accepting arbitrary alternative data.
The native rule reads original marked ballots and derives casing from both
ordinary sides; the reflected marked matrices remain independently available. -/
def Data.publish (d : Data) (sense : Bool → List Slot → Option RS) : RingActiveDistanceSchedule.Cell :=
  (d.ballots sense).map fun out => d.letters (out.map Prod.snd)

theorem tied_directions (w : Slot → TrialWord) (a b : Slot) :
    tied (directions w) a b = (w a == w b) := by
  rcases lt_trichotomy (w a) (w b) with lt | eq | gt
  · simp [tied,directions,lt,not_lt_of_gt lt,ne_of_lt lt]
  · simp [tied,directions,eq]
  · simp [tied,directions,gt,not_lt_of_gt gt,ne_of_gt gt]

theorem rows_directions (w : Slot → TrialWord) : rows (directions w) = order w (List.finRange 4) := by
  unfold rows order
  congr 1
  funext a b
  apply Bool.eq_iff_iff.mpr
  simp [directions]

theorem strict_directions (w : Slot → TrialWord) : strictData (directions w) = strict w := by
  unfold strictData strict
  simp only [tied_directions]
  rfl

def ordinary (keys : Slot → Key) : Directions := directions (fun k => trialKey (keys k) [])

theorem ordinary_tied (keys : Slot → Key) (a b : Slot) : tied (ordinary keys) a b = (keys a == keys b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [ordinary,tied_directions,beq_iff_eq]
  exact ⟨fun eq => ((trial_eq _ _ [] []).mp eq).1,fun eq => by rw [eq]⟩

theorem native_tiedSlots (keys : Slot → Key) : RingFullPathEligibility.tiedSlots keys = tiedSlots (ordinary keys) := by
  unfold RingFullPathEligibility.tiedSlots tiedSlots
  simp only [ordinary_tied]

theorem native_candidates (keys : Slot → Key) :
    RingFullPathEligibility.candidates keys = candidates (ordinary keys) := by
  simp only [RingFullPathEligibility.candidates,candidates,native_tiedSlots]

theorem native_trials (keys : Slot → Key) : RingFullPathTrialReadings.trials keys = trials (ordinary keys) := by
  simp only [RingFullPathTrialReadings.trials,RingFullPathEligibility.candidates,trials,candidates,native_tiedSlots]
  rfl

theorem native_reversals (x y : Slot → Key) :
    RingFullPathPublication.reversals x y = reversals (ordinary x) (ordinary y) := rfl

/-- Native marking words are reduced to pair directions independently for every
side and possible nominated slot. -/
def nativeData {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (x y : Slot → Key) : Data where
  ordinary rev := ordinary (if rev then y else x)
  marked rev s := (markWords? fr r s).map fun ws =>
    directions (fun k => trialKey ((if rev then y else x) k) (ws k))

def nativeData? {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) : Option Data := do
  let x ← RingFullPathPublication.keys? fr r false
  let y ← RingFullPathPublication.keys? fr r true
  return nativeData fr r x y

theorem readTrialG_directions {i : Input} {f : Site i} (fr : Frame i f) (g : Geometry) (w : Slot → TrialWord) :
    RingFrameTransport.readTrialG fr g w = ballot (directions w) (fun row => readback? g (fr.atoms row)) := by
  have nd : ((List.finRange 4).map w).Nodup ↔ Function.Injective w := by
    constructor
    · intro good a b eq
      exact List.inj_on_of_nodup_map good (List.mem_finRange a) (List.mem_finRange b) eq
    · exact fun inj => (List.nodup_finRange 4).map inj
  unfold RingFrameTransport.readTrialG ballot
  rw [strict_directions,rows_directions]
  by_cases inj : Function.Injective w
  · rw [if_pos (nd.mpr inj),if_pos (strict_injective.mpr inj)]
  · rw [if_neg (fun good => inj (nd.mp good)),if_neg (fun good => inj (strict_injective.mp good))]

theorem native_ballots {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (g : Geometry) (x y : Slot → Key) :
    RingFrameTransport.readingsWithG fr r (RingFrameTransport.readTrialG fr g) x =
      (nativeData fr r x y).ballots (fun _ row => readback? g (fr.atoms row)) := by
  unfold RingFrameTransport.readingsWithG Data.ballots
  simp only [nativeData,Bool.false_eq_true,ite_false]
  rw [native_trials]
  apply RingFrameTransport.mapM_congr_mem
  intro s _
  cases got : markWords? fr r s with
  | none => rfl
  | some ws => simp only [Option.map_some,Option.bind_eq_bind,Option.bind_some,readTrialG_directions]

theorem native_letters {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (x y : Slot → Key)
    (hands : List (Option RS)) : RingFullPathPublication.letters x y hands = (nativeData fr r x y).letters hands := rfl

/-- Exact factorization through finite comparison data, including tied refusals,
mark nominations, unresolved markings, and cancellation of the ballot population. -/
theorem centreG_exact {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (g : Geometry) :
    RingFrameTransport.centreG fr r (RingFrameTransport.readTrialG fr g) =
      (nativeData? fr r).bind fun d => d.publish (fun _ row => readback? g (fr.atoms row)) := by
  unfold RingFrameTransport.centreG RingFrameTransport.readingsG nativeData?
  change (RingFullPathPublication.keys? fr r false).bind _ = _
  cases actual : RingFullPathPublication.keys? fr r false with
  | none => rfl
  | some x =>
    cases reflected : RingFullPathPublication.keys? fr r true with
    | none => rfl
    | some y =>
      simp only [Option.bind_some]
      change ((RingFullPathPublication.keys? fr r false).bind _).map _ = _
      rw [actual]
      simp only [Option.bind_some]
      rw [native_ballots fr r g x y]
      rfl

/-- Completed structural absence, a recognized frame and comparator data, or
unresolved ordinary key coverage are represented separately. -/
abbrev FrameData (i : Input) (q : Site i) := Option (Frame i q × Data)

def extract? (i : Input) (q : Site i) (r : Reader i) : Option (FrameData i q) :=
  match RingNestedActivePair.frame? i q with
  | none => some none
  | some fr => (nativeData? fr r).map fun d => some (fr,d)

def frameDataPublish {i : Input} {q : Site i} (g : Geometry) : FrameData i q → RingActiveDistanceSchedule.Cell
  | none => some none
  | some (fr,d) => d.publish (fun _ row => readback? g (fr.atoms row))

/-- The actual local tetra publisher accepts this alternative comparison-only
interface. No strictness, rank, trial, casing or final-label hypothesis is used. -/
theorem publishG_exact {i : Input} (g : Geometry) (q : Site i) (r : Reader i)
    (tetra : RingPyramidalPublication.focusP i q = none) :
    RingFrameTransport.publishG i g q r = (extract? i q r).bind (frameDataPublish g) := by
  rw [RingFrameTransport.publishG_tetra g tetra]
  unfold RingFrameTransport.tetraG extract?
  cases found : RingNestedActivePair.frame? i q with
  | none => rfl
  | some fr =>
    change RingFrameTransport.centreG fr r (RingFrameTransport.readTrialG fr g) =
      ((nativeData? fr r).map (fun d => some (fr,d))).bind (frameDataPublish g)
    rw [centreG_exact]
    cases nativeData? fr r <;> rfl

open private keys_exact from TetraStereo.Engine.RingFullPathPublication

theorem nativeData_of_keys {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (x y : Slot → Key)
    (actual : RingFullPathPublication.keys? fr r false = some x)
    (reflected : RingFullPathPublication.keys? fr r true = some y) :
    nativeData? fr r = some (nativeData fr r x y) := by simp [nativeData?,actual,reflected]

/-- Ready native readers construct comparison data rather than assuming it. -/
theorem nativeData_ready {i : Input} {f : Site i} (fr : Frame i f) {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) : ∃ d, nativeData? fr r = some d := by
  obtain ⟨x,hx,_⟩ := keys_exact fr ready false
  obtain ⟨y,hy,_⟩ := keys_exact fr ready true
  exact ⟨_,nativeData_of_keys fr r x y hx hy⟩

theorem marked_ready {i : Input} {f : Site i} (fr : Frame i f) {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) (x y : Slot → Key) (rev : Bool) (s : Option Slot) :
    ((nativeData fr r x y).marked rev s).isSome = true := by
  obtain ⟨ws,hit,_⟩ := RingFullPathTrialReadings.mark_exact fr ready rev s
  simp [nativeData,hit]

theorem extract_ready {i : Input} (q : Site i) {r : Reader i} (ready : RingGroupedStereo.Ready q r) :
    (extract? i q r).isSome = true := by
  unfold extract?
  cases found : RingNestedActivePair.frame? i q with
  | none => rfl
  | some fr =>
    change ((nativeData? fr r).map (fun d => some (fr,d))).isSome = true
    obtain ⟨d,native⟩ := nativeData_ready fr ready
    rw [native]
    rfl

/-- The native comparison oracle on a ready reader, including structural absence. -/
def actualData {i : Input} (q : Site i) (r : Reader i) (ready : RingGroupedStereo.Ready q r) : FrameData i q :=
  (extract? i q r).get (extract_ready q ready)

theorem actualData_publish {i : Input} (g : Geometry) (q : Site i) (r : Reader i)
    (ready : RingGroupedStereo.Ready q r) (tetra : RingPyramidalPublication.focusP i q = none) :
    RingFrameTransport.publishG i g q r = frameDataPublish g (actualData q r ready) := by
  rw [publishG_exact g q r tetra,←Option.some_get (extract_ready q ready)]
  rfl

theorem rows_perm (d : Directions) : (rows d).Perm (List.finRange 4) := List.mergeSort_perm ..

theorem ballot_congr (d : Directions) (sense other : List Slot → Option RS)
    (physical : ∀ row, row.Perm (List.finRange 4) → sense row = other row) :
    ballot d sense = ballot d other := by
  unfold ballot
  split
  · exact physical _ (rows_perm d)
  · rfl

/-- Comparison data and permutation-frame readbacks suffice even when ballots
are tied, markings are missing, or opposite hands cancel. -/
theorem Data.publish_congr (d e : Data) (sense other : Bool → List Slot → Option RS)
    (original : d.ordinary false = e.ordinary false)
    (reflected : d.ordinary true = e.ordinary true)
    (marked : ∀ s ∈ trials (d.ordinary false), d.marked false s = e.marked false s)
    (physical : ∀ row, row.Perm (List.finRange 4) → sense false row = other false row) :
    d.publish sense = e.publish other := by
  have ballots : d.ballots sense = e.ballots other := by
    unfold Data.ballots
    rw [←original]
    apply RingFrameTransport.mapM_congr_mem
    intro s member
    rw [marked s member]
    cases e.marked false s with
    | none => rfl
    | some comparison =>
      simp only [Option.bind_eq_bind,Option.bind_some]
      rw [ballot_congr comparison _ _ physical]
  unfold Data.publish
  rw [ballots]
  cases e.ballots other with
  | none => rfl
  | some out =>
    simp only [Option.map_some]
    unfold Data.letters
    rw [original,reflected]

/-- An actual tie refuses that ballot, without choosing an occurrence ID. -/
theorem ballot_tied (d : Directions) (sense : List Slot → Option RS) (a b : Slot)
    (different : a ≠ b) (same : tied d a b = true) : ballot d sense = none := by
  have notStrict : ¬strictData d = true := by
    intro yes
    have first := List.all_eq_true.mp yes a (List.mem_finRange a)
    have second := List.all_eq_true.mp first b (List.mem_finRange b)
    simp [different,same] at second
  exact if_neg notStrict

assert_kernel_only actualData_publish
assert_kernel_only Data.publish_congr
assert_kernel_only centreG_exact
assert_kernel_only publishG_exact
assert_kernel_only native_trials
end TetraStereo.Engine.RingPairwisePublication
