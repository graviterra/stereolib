import TetraStereo.Engine.RingMarkedQueueExecute
import TetraStereo.Engine.RingMarkedTreeReport

/-! Pairwise native reports computed by early-exit molecular queues. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingMarkedQueueReport
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader Frame)
open RingActiveDistanceSchedule (View Rule)
open RingActivePairReport (Slot)
open RingRetainedChemicalTrace (Word)
open RingStereoSiblingPass (Branch)
open RingFullPathEligibility (Key)
open RingFullPathTrialReadings (trialKey)
open RingPyramidalPublication (Ligand)
open RingConstitutionalResidual (publications)
open RingUniversalLigandOrder (Observation interpret observe)
open private ligand_read from TetraStereo.Engine.RingPyramidalNumericRows
open private cmp_append list_lt deep_lt from TetraStereo.Engine.RingRebuiltStereo
attribute [local instance] lexOrd

private theorem trial_split (a b : Key) (x y : Word) :
    compare (trialKey a x) (trialKey b y) =
      (compare (trialKey a []) (trialKey b [])).then (compare x y) := by
  let earlier (k : Key) := [k.throughFourA,[RingFullPathTrialReadings.bitWord k.bestFourB],
    [k.fourC],[RingFullPathTrialReadings.bitWord k.fixedR]]
  have split (u v : Word) : compare (trialKey a u) (trialKey b v) =
      (compare (earlier a) (earlier b)).then (compare u v) := by
    change compare (earlier a ++ [[u]]) (earlier b ++ [[v]]) = _
    rw [cmp_append (earlier a) (earlier b) [[u]] [[v]] rfl]
    cases h : compare u v <;> simp [List.compare_cons_cons,h]
  rw [split,split]
  cases compare (earlier a) (earlier b) <;> rfl

/-- Ordinary priority is consulted first; only an ordinary tie with a nominated
atom demands molecular queue expansion. Optional absence is an ordinary trial. -/
def pair? (i : Input) (r : Reader i) (mark : Option Nat) (a b : Arm i) (ka kb : Key) : Option Ordering :=
  let prior := compare (trialKey ka []) (trialKey kb [])
  if prior ≠ .eq then some prior else
    match mark with
    | none => some .eq
    | some atom => RingMarkedQueueExecute.compare? i r atom a b

def less? (i : Input) (r : Reader i) (mark : Option Nat) (a b : Arm i) (ka kb : Key) : Option Bool :=
  (pair? i r mark a b ka kb).map fun out => decide (out = .lt)

private theorem trial_lt (a b : List (List Word)) : compare a b = .lt ↔ a < b :=
  list_lt deep_lt (fun _ _ => Std.compare_eq_eq_iff_eq) a b

private theorem pair_exact {i : Input} {f : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) (mark : Option Nat) (a b : Arm i) (ka kb : Key)
    (va : RingRule5Shape.Valid a) (vb : RingRule5Shape.Valid b)
    (oa : RingRule5Shape.On f a) (ob : RingRule5Shape.On f b) {x y : Word}
    (ha : RingFrameTransport.markWord? i r mark a = some x)
    (hb : RingFrameTransport.markWord? i r mark b = some y) :
    pair? i r mark a b ka kb = some (compare (trialKey ka x) (trialKey kb y)) := by
  rw [trial_split]
  unfold pair?
  by_cases tie : compare (trialKey ka []) (trialKey kb []) = .eq
  · simp only [tie,ne_eq,not_true_eq_false,if_false,Ordering.eq_then]
    cases mark with
    | none =>
      obtain rfl := Option.some.inj ha
      obtain rfl := Option.some.inj hb
      rfl
    | some atom =>
      obtain ⟨u,hu,ux⟩ := Option.map_eq_some_iff.mp ha
      obtain ⟨v,hv,vy⟩ := Option.map_eq_some_iff.mp hb
      rw [← ux,← vy]
      exact RingMarkedQueueExecute.compare_readings ready va vb oa ob
        (RingGroupedMark.arm_source hu).2 (RingGroupedMark.arm_source hv).2
  · simp only [tie,ne_eq,not_false_eq_true,if_true]
    cases h : compare (trialKey ka []) (trialKey kb []) with
    | eq => exact False.elim (tie h)
    | lt => rfl
    | gt => rfl

private theorem less_exact {i : Input} {f : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) (mark : Option Nat) (a b : Arm i) (ka kb : Key)
    (va : RingRule5Shape.Valid a) (vb : RingRule5Shape.Valid b)
    (oa : RingRule5Shape.On f a) (ob : RingRule5Shape.On f b) {x y : Word}
    (ha : RingFrameTransport.markWord? i r mark a = some x)
    (hb : RingFrameTransport.markWord? i r mark b = some y) :
    less? i r mark a b ka kb = some (decide (trialKey ka x < trialKey kb y)) := by
  simp only [less?,pair_exact ready mark a b ka kb va vb oa ob ha hb,Option.map_some,trial_lt]

/-- All sixteen demanded tetrahedral comparisons retain missing reads. -/
def tetraDirections? {i f} (fr : @Frame i f) (r : Reader i) (ks : Slot → Key) (mark : Option Slot) :=
  RingActivePairReport.four? fun a => RingActivePairReport.four? fun b =>
    less? i r (mark.map (RingGroupedTrials.atom fr)) (RingGroupedCentre.cursor fr a)
      (RingGroupedCentre.cursor fr b) (ks a) (ks b)

private theorem tetraDirections_exact {i f} (fr : @Frame i f) {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) (ks : Slot → Key) (mark : Option Slot) :
    tetraDirections? fr r ks mark = (RingFullPathTrialReadings.markWords? fr r mark).map
      (fun ws => RingPairwisePublication.directions (fun a => trialKey (ks a) (ws a))) := by
  obtain ⟨ws,got,only⟩ := RingFullPathTrialReadings.mark_exact fr ready false mark
  have each (a : Slot) : RingFrameTransport.markWord? i r
      (mark.map (RingGroupedTrials.atom fr)) (RingGroupedCentre.cursor fr a) = some (ws a) := by
    have src := (only ws).mpr rfl
    cases mark with
    | none => simp only [RingFrameTransport.markWord?,Option.map_none,src a]
    | some s =>
      obtain ⟨b,hb,eqn⟩ := src a
      obtain ⟨e,he⟩ := RingGroupedMark.arm_ready ready (RingGroupedTrials.atom fr s)
        (RingGroupedCentre.cursor fr a) (RingGroupedCentre.valid fr a) (fr.direction a).property.1
      have same := RingGroupedMark.Reading.unique (RingGroupedMark.arm_source he).2 hb
      simp only [RingFrameTransport.markWord?,Option.map_some,he,same,eqn,Option.map_some]
  have pair (a b : Slot) := less_exact ready (mark.map (RingGroupedTrials.atom fr))
    (RingGroupedCentre.cursor fr a) (RingGroupedCentre.cursor fr b) (ks a) (ks b)
    (RingGroupedCentre.valid fr a) (RingGroupedCentre.valid fr b)
    (fr.direction a).property.1 (fr.direction b).property.1 (each a) (each b)
  rw [got]
  simp only [tetraDirections?,RingActivePairReport.four?,pair,bind,pure,Option.bind_some,Option.map_some]
  congr 1
  funext a b
  fin_cases a <;> fin_cases b <;> rfl

def tetraData {i f} (fr : @Frame i f) (r : Reader i) (x y : Slot → Key) : RingPairwisePublication.Data where
  ordinary rev := RingPairwisePublication.ordinary (if rev then y else x)
  marked rev mark := tetraDirections? fr r (if rev then y else x) mark

def tetraData? {i f} (fr : @Frame i f) (r : Reader i) : Option RingPairwisePublication.Data := do
  let x ← RingMarkedTreeReport.keys? fr r false
  let y ← RingMarkedTreeReport.keys? fr r true
  return tetraData fr r x y

theorem tetra_exact {i f} (fr : @Frame i f) {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) : tetraData? fr r = RingPairwisePublication.nativeData? fr r := by
  have each (x y : Slot → Key) : tetraData fr r x y = RingPairwisePublication.nativeData fr r x y := by
    unfold tetraData RingPairwisePublication.nativeData
    congr 1
    funext rev mark
    exact tetraDirections_exact fr ready _ mark
  simp only [tetraData?,RingMarkedTreeReport.keys_exact,RingPairwisePublication.nativeData?,each]

private def matrix? {α : Type} (xs : List α) (read : α → α → Option Bool) : Option (List (List Bool)) :=
  xs.mapM fun a => xs.mapM (read a)

private theorem mapM_total {α β : Type} (xs : List α) (read : α → Option β) (out : α → β)
    (each : ∀ a ∈ xs, read a = some (out a)) : xs.mapM read = some (xs.map out) := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [List.mapM_cons,each a List.mem_cons_self,
      ih (fun b hb => each b (.tail _ hb)),List.map_cons,bind,pure,Option.bind_some]

private def row {i : Input} (xs : List (Ligand i)) (ds : List (List Bool)) : RingPyramidalPairwise.Row :=
  ⟨xs.length,fun a => (xs.get a).atom,fun a b => (ds.getD a.val []).getD b.val false⟩

/-- Arbitrary ligand-frame lengths are retained. The false default is used only
outside the returned matrix; all actual indices are proved total on ready stores. -/
def pyramidalRow? (i : Input) (r : View i) (mark : Option Nat) (xs : List (Ligand i)) : Option RingPyramidalPairwise.Row :=
  (matrix? xs (fun a b => less? i r mark a.arm b.arm a.priority b.priority)).map (row xs)

private theorem row_exact {i : Input} (xs : List (Ligand i)) (words : Ligand i → Word) :
    row xs (xs.map fun a => xs.map fun b => decide (trialKey a.priority (words a) < trialKey b.priority (words b))) =
      RingPyramidalPairwise.extractRow (fun x => x.atom) (fun x => trialKey x.priority (words x)) xs := by
  simp only [row,RingPyramidalPairwise.extractRow]
  congr 2
  funext a b
  simp [List.getD_eq_getElem?_getD,a.isLt,b.isLt]

private theorem row_ext (a b : RingPyramidalPairwise.Row) (size : a.size = b.size)
    (ids : ∀ j, a.ids j = b.ids (Fin.cast size j))
    (less : ∀ j k, a.less j k = b.less (Fin.cast size j) (Fin.cast size k)) : a = b := by
  cases a with
  | mk n ia la =>
    cases b with
    | mk m ib lb =>
      cases size
      simp only [Fin.cast_refl] at ids less
      have hi := funext ids
      have hl := funext (fun j => funext (less j))
      cases hi
      cases hl
      rfl

private theorem extract_map {α β κ : Type} [LinearOrder κ] (xs : List α) (f : α → β)
    (ids : β → Nat) (key : β → κ) :
    RingPyramidalPairwise.extractRow ids key (xs.map f) =
      RingPyramidalPairwise.extractRow (fun a => ids (f a)) (fun a => key (f a)) xs := by
  apply row_ext _ _ (List.length_map ..)
  · intro j
    simp only [RingPyramidalPairwise.extractRow,List.get_eq_getElem,List.getElem_map]
    rfl
  · intro j k
    simp only [RingPyramidalPairwise.extractRow,List.get_eq_getElem,List.getElem_map]
    rfl

private theorem pyramidalRow_exact {i : Input} {q : Site i} {r : View i}
    (ready : RingGroupedStereo.Ready q r) {rev : Bool} {xs : List (Ligand i)}
    (got : RingPyramidalPublication.ligands? i q r rev = some xs) (mark : Option Nat) :
    pyramidalRow? i r mark xs = (do
      let rows ← xs.mapM (RingFrameTransport.rowOf i r mark)
      return RingPyramidalPairwise.extractRow Prod.fst Prod.snd rows) := by
  classical
  have word (x : Ligand i) (hx : x ∈ xs) : ∃ w, RingFrameTransport.markWord? i r mark x.arm = some w := by
    obtain ⟨valid,on,_⟩ := ligand_read got hx
    cases mark with
    | none => exact ⟨[],rfl⟩
    | some atom =>
      obtain ⟨e,he⟩ := RingGroupedMark.arm_ready ready atom x.arm valid on
      exact ⟨e.2.word,by simp [RingFrameTransport.markWord?,he]⟩
  let words (x : Ligand i) : Word := if h : x ∈ xs then (word x h).choose else []
  have found (x : Ligand i) (hx : x ∈ xs) : RingFrameTransport.markWord? i r mark x.arm = some (words x) := by
    simp only [words,dif_pos hx]
    exact (word x hx).choose_spec
  have pair (a : Ligand i) (ha : a ∈ xs) (b : Ligand i) (hb : b ∈ xs) :
      less? i r mark a.arm b.arm a.priority b.priority =
        some (decide (trialKey a.priority (words a) < trialKey b.priority (words b))) := by
    obtain ⟨va,oa,_⟩ := ligand_read got ha
    obtain ⟨vb,ob,_⟩ := ligand_read got hb
    exact less_exact ready mark a.arm b.arm a.priority b.priority va vb oa ob (found a ha) (found b hb)
  have mat := mapM_total xs (fun a => xs.mapM (fun b => less? i r mark a.arm b.arm a.priority b.priority))
    (fun a => xs.map fun b => decide (trialKey a.priority (words a) < trialKey b.priority (words b)))
    (fun a ha => mapM_total xs _ _ (fun b hb => pair a ha b hb))
  have native := mapM_total xs (RingFrameTransport.rowOf i r mark)
    (fun x => (x.atom,trialKey x.priority (words x))) (by
      intro x hx
      simp [RingFrameTransport.rowOf,found x hx])
  simp only [pyramidalRow?,matrix?,mat,Option.map_some,native,bind,pure,Option.bind_some]
  rw [row_exact,extract_map]

def pyramidalData (i : Input) (q : Site i) (r : View i) : RingPyramidalPairwise.Data where
  shape := decide ((RingRetainedAuxiliary.frame i.certified q).length = 3)
  ordinary rev := (RingMarkedTreeReport.ligands? i q r rev).map
    (RingPyramidalPairwise.extractRow (fun x => x.atom) (fun x => trialKey x.priority []))
  marked rev mark := do
    let xs ← RingMarkedTreeReport.ligands? i q r rev
    pyramidalRow? i r mark xs

theorem pyramidal_exact (i : Input) (q : Site i) (r : View i)
    (ready : RingGroupedStereo.Ready q r) : pyramidalData i q r = RingPyramidalPairwise.nativeData i q r := by
  unfold pyramidalData RingPyramidalPairwise.nativeData
  simp only [RingMarkedTreeReport.ligands_exact]
  congr 1
  funext rev mark
  cases got : RingPyramidalPublication.ligands? i q r rev with
  | none => rfl
  | some xs => exact pyramidalRow_exact ready got mark

def observations (i : Input) (q : Site i) (r : View i) : Observation i q :=
  match RingPyramidalPublication.focusP i q with
  | some a => .pyramidal a (pyramidalData i q r)
  | none => .tetra (match RingNestedActivePair.frame? i q with
    | none => some none
    | some fr => (tetraData? fr r).map fun d => some (fr,d))

theorem observations_exact {i : Input} {q : Site i} {r : View i}
    (ready : RingGroupedStereo.Ready q r) : observations i q r = observe i q r := by
  unfold observations observe
  cases p : RingPyramidalPublication.focusP i q with
  | some a => rw [pyramidal_exact i q r ready]
  | none =>
    unfold RingPairwisePublication.extract?
    cases fr : RingNestedActivePair.frame? i q with
    | none => rfl
    | some frame => simp only [tetra_exact frame ready]

def procedure (i : Input) : Rule i := fun q r => interpret (observations i q r)
abbrev rows (i : Input) := RingGlobalComparison.rows (publications i) (procedure i)
abbrev report (i : Input) := RingGlobalComparison.report (publications i) (procedure i)

theorem stores_and_reports {i : Input} (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    (∀ a k, k ≤ RingActiveDistanceSchedule.height i + 1 → rows i a k = RingSphereStore.rows i a k) ∧
      ∀ atoms, report i atoms = RingChemicalReport.report? i atoms := by
  have no (a k q) : ¬ RingGlobalComparison.Difference (publications i) (procedure i) a k q := by
    intro d
    apply d.2.2.2
    change interpret (observations i q (RingGlobalComparison.prior i a k)) = _
    rw [RingGlobalComparison.prior_exact d.1,observations_exact (RingChemicalGraphProof.ready ok q)]
    exact (RingUniversalLigandOrder.interface i ok).reachable q
  constructor
  · intro a k bound
    exact (RingGlobalComparison.rows_or_difference (publications i) (procedure i) a k bound).resolve_right
      (by rintro ⟨n,_,q,d⟩; exact no a n q d)
  · intro atoms
    by_contra bad
    obtain ⟨a,_,k,_,q,d⟩ := RingGlobalComparison.report_disagreement (publications i) (procedure i) atoms bad
    exact no a k q d

def fromRaw? := RingRawComparisonLift.fromRaw report

theorem raw_exact : fromRaw? = RingHydrogenReport.fromRaw? := by
  apply RingRawComparisonLift.eq_native_of_admitted
  intro i atoms ok
  exact (stores_and_reports ok).2 atoms
end TetraStereo.Engine.RingMarkedQueueReport
assert_kernel_only TetraStereo.Engine.RingMarkedQueueReport.tetra_exact
assert_kernel_only TetraStereo.Engine.RingMarkedQueueReport.pyramidal_exact
assert_kernel_only TetraStereo.Engine.RingMarkedQueueReport.stores_and_reports
assert_kernel_only TetraStereo.Engine.RingMarkedQueueReport.raw_exact
