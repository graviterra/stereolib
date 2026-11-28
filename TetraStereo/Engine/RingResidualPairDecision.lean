import TetraStereo.Engine.RingLigandFirstDifference
import TetraStereo.Engine.RingGlobalComparison
import TetraStereo.Engine.RingFiniteExchange

/-! Pairwise first deciding rules for the actual promotion schedule. Every
matrix is indexed by frame slots, and a greater trial key has higher priority.
The reflected pair comparisons describe the independent mirror ballots even
when the publisher obtains the mirror labels from ordinary reversal parity. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingResidualPairDecision
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Frame Reader)
open RingActivePairReport (Slot)
open RingGroupedCentre (cursor)
open RingFullPathEligibility (Key Reads)
open RingRetainedChemicalTrace (Word)
open RingFullPathTrialReadings (bitWord trialKey trials markWords? MarkWords readings?)
open RingLigandFirstDifference (Stage Words First stages directions Decomposes)
open private keys_exact from TetraStereo.Engine.RingFullPathPublication
open private frame_eq from TetraStereo.Engine.RingGroupedReport
attribute [local instance] lexOrd

inductive Verdict where
  | tie
  | left (stage : Stage)
  | right (stage : Stage)
  deriving DecidableEq, Repr

def Verdict.order : Verdict → Ordering
  | .tie => .eq
  | .left _ => .gt
  | .right _ => .lt

def Explains (d : Stage → Ordering) (ss : List Stage) : Verdict → Prop
  | .tie => ∀ s ∈ ss, d s = .eq
  | .left s => First d ss s .gt
  | .right s => First d ss s .lt

private def pick (d : Stage → Ordering) : List Stage → Verdict
  | [] => .tie
  | s::ss => match d s with
    | .eq => pick d ss
    | .gt => .left s
    | .lt => .right s

private theorem pick_exact (d : Stage → Ordering) (ss : List Stage) :
    Explains d ss (pick d ss) := by
  induction ss with
  | nil => simp [pick,Explains]
  | cons s ss ih =>
    cases h : d s with
    | eq =>
      simp only [pick,h]
      cases v : pick d ss with
      | tie => simpa [v,Explains,h] using ih
      | left a => exact .later h (by simpa only [v,Explains] using ih)
      | right a => exact .later h (by simpa only [v,Explains] using ih)
    | gt => simpa only [pick,h,Explains] using
        (show First d (s::ss) s .gt from h ▸ First.here (by simp [h]))
    | lt => simpa only [pick,h,Explains] using
        (show First d (s::ss) s .lt from h ▸ First.here (by simp [h]))

private theorem explained_order {d ss v} (h : Explains d ss v) :
    RingLigandFirstDifference.scan d ss = v.order := by
  cases v with
  | tie => exact (RingLigandFirstDifference.scan_tie_iff _ _).mpr h
  | left _ => exact First.scan_value h
  | right _ => exact First.scan_value h

/-- Molecular readings always have the four through-4a entries in order. -/
def words (k : Key) (m : Word) : Words :=
  ⟨k.throughFourA[0]?.getD [],k.throughFourA[1]?.getD [],k.throughFourA[2]?.getD [],
    k.throughFourA[3]?.getD [],bitWord k.bestFourB,k.fourC,bitWord k.fixedR,m⟩

private theorem decomposes {i : Input} {r : Reader i} {rev arm k} (legal : Reads i r rev arm k)
    (m : Word) : Decomposes k m (words k m) := by
  obtain ⟨_,w,_,dw,_,_,_⟩ := RingLigandFirstDifference.extract legal m
  exact ⟨by simp [words,dw.through],rfl,rfl,rfl,rfl⟩

abbrev Table := Vector (Vector Verdict 4) 4

structure Trial where
  nomination : Option Slot
  actual : Table
  mirrored : Table
  deriving Repr, DecidableEq

private def matrix (ks : Slot → Key) (ws : Slot → Word) : Table :=
  let fields := Vector.ofFn fun a => words (ks a) (ws a)
  Vector.ofFn fun (a : Slot) => Vector.ofFn fun (b : Slot) => pick (directions fields[a.val] fields[b.val]) stages

/-- An executable comparison of every ordered pair, once per scheduled
nomination, with a shared marking computation for both geometries. -/
def diagnose? {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) : Option (List Trial) := do
  let ks ← RingFullPathPublication.keys? fr r false
  let ms ← RingFullPathPublication.keys? fr r true
  (trials ks).mapM fun s => do
    let ws ← markWords? fr r s
    return ⟨s,matrix ks ws,matrix ms ws⟩

/-- All data, including the reader, frame and nomination list, come from the
molecular evaluator. A root call uses batch index `height i + 1`. -/
def atSite? (i : Input) (root : i.certified.Atom) (batch : Nat) (f : Site i) : Option (List Trial) := do
  let fr ← RingNestedActivePair.frame? i f
  diagnose? fr (RingGlobalComparison.prior i root batch)

def TableExact {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i)
    (rev : Bool) (m : Option Slot) (table : Table) : Prop :=
  ∀ (keys : Slot → Key) (ws : Slot → Word),
    (∀ s, Reads i r rev (cursor fr s) (keys s)) → MarkWords fr r rev m ws →
    ∀ a b : Slot,
      Explains (directions (words (keys a) (ws a)) (words (keys b) (ws b))) stages table[a.val][b.val] ∧
      compare (trialKey (keys a) (ws a)) (trialKey (keys b) (ws b)) = table[a.val][b.val].order

/-- Both full schedules are reproduced in order, including an ordinary trial
with an absent nomination. Every reported verdict agrees with every lawful
molecular choice of the ordinary keys and the nominated mark words. -/
structure Exact {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (out : List Trial) : Prop where
  schedule : ∀ rev : Bool, ∃ native, readings? fr r rev = some native ∧
    out.map Trial.nomination = native.map Prod.fst
  pairs : ∀ t ∈ out, TableExact fr r false t.nomination t.actual ∧
    TableExact fr r true t.nomination t.mirrored

private theorem matrix_exact {i : Input} {f : Site i} {fr : Frame i f} {r : Reader i}
    {rev : Bool} {ks : Slot → Key} {m : Option Slot} {ws : Slot → Word}
    (keysOnly : ∀ other, (∀ k, Reads i r rev (cursor fr k) (other k)) ↔ other = ks)
    (wordsOnly : ∀ other, MarkWords fr r rev m other ↔ other = ws) :
    TableExact fr r rev m (matrix ks ws) := by
  intro keys marks source legal a b
  obtain rfl := (keysOnly keys).mp source
  obtain rfl := (wordsOnly marks).mp legal
  simp only [matrix,Vector.getElem_ofFn]
  have explains := pick_exact (directions (words (keys a) (marks a)) (words (keys b) (marks b))) stages
  exact ⟨explains,(RingLigandFirstDifference.compare_trial_eq_scan (decomposes (source a) _)
    (decomposes (source b) _)).trans (explained_order explains)⟩

theorem diagnosis_exact {i : Input} {f : Site i} (fr : Frame i f)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (view : RingActiveDistanceSchedule.View i)
    (ready : RingGroupedStereo.Ready f (RingActiveDistanceSchedule.frozen view f)) :
    let r := RingActiveDistanceSchedule.frozen view f
    ∃ out, diagnose? fr r = some out ∧ Exact fr r out := by
  intro r
  obtain ⟨x,hx,ox⟩ := keys_exact fr ready false
  obtain ⟨y,hy,oy⟩ := keys_exact fr ready true
  obtain ⟨k,xs,hxs,slots,src,_⟩ := RingFullPathTrialReadings.ready_readings geom fr ready false
  obtain ⟨_,ys,hys,_,_,_⟩ := RingFullPathTrialReadings.ready_readings geom fr ready true
  obtain rfl := (ox k).mp src
  have paired := (RingFullPathTrialParity.view_hands geom fr view ready src ((oy y).mpr rfl) hxs hys).1
  choose ws got only using RingFullPathTrialReadings.mark_exact fr ready false
  let entry := fun s : Option Slot => Trial.mk s (matrix k (ws s)) (matrix y (ws s))
  refine ⟨(trials k).map entry,?_,?_,?_⟩
  · have pureRows (ss : List (Option Slot)) :
        ss.mapM (fun s => some (entry s)) = some (ss.map entry) := by
      induction ss with
      | nil => rfl
      | cons a tail ih => simp [List.mapM_cons,ih]
    simpa [r,diagnose?,hx,hy,got,entry] using pureRows (trials k)
  · intro rev
    cases rev with
    | false => exact ⟨xs,hxs,by simpa [List.map_map,entry,Function.comp_def] using slots.symm⟩
    | true => exact ⟨ys,hys,by simpa [List.map_map,entry,Function.comp_def] using slots.symm.trans paired⟩
  · intro t ht
    obtain ⟨s,_,rfl⟩ := List.mem_map.mp ht
    obtain ⟨w,hw,unique⟩ := RingFullPathTrialReadings.mark_exact fr ready true s
    obtain rfl := Option.some.inj (hw.symm.trans (got s))
    exact ⟨matrix_exact ox (only s),matrix_exact oy unique⟩

/-- The exact pair tables at every scheduled public tetrahedral occurrence,
including the concluding root, using its materialized preceding rows. -/
theorem public_exact {i : Input} {f : Site i} (fr : Frame i f)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) {root : i.certified.Atom} {batch : Nat}
    (called : RingGlobalComparison.Called i root batch f) :
    ∃ out, atSite? i root batch f = some out ∧
      Exact fr (RingGlobalComparison.prior i root batch) out := by
  unfold atSite?
  rw [frame_eq fr,RingGlobalComparison.prior_exact called]
  exact diagnosis_exact fr geom _ (RingChemicalGraphProof.ready geom f)

/-- A strict molecular verdict in a nominated trial rules out every exchange
of those two branches that preserves the nominated atom. A tie is a legitimate
residual answer whether or not a structural witness can be constructed. -/
theorem strict_excludes_exchange {i : Input} {f : Site i} (fr : Frame i f) {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) {rev : Bool} {s a b : Slot} {table : Table}
    (exactTable : TableExact fr r rev (some s) table) (different : table[a.val][b.val] ≠ .tie) :
    ¬ Nonempty (RingGeometryExchange.Exchange fr r s a b) := by
  rintro ⟨e⟩
  obtain ⟨ks,_,only⟩ := keys_exact fr ready rev
  have legal := (only ks).mpr rfl
  obtain ⟨ws,_,wm⟩ := RingFullPathTrialReadings.mark_exact fr ready rev (some s)
  have mark := (wm ws).mpr rfl
  have ke := RingFullPathKeyTransport.reads_transport e.carrier e.frozen rev e.atLigand
    (legal a) (e.other.symm ▸ legal b)
  obtain ⟨la,ha,wa⟩ := mark a
  obtain ⟨lb,hb,wb⟩ := mark b
  have same := e.carrier.mark e.frozen e.selected e.atLigand ha (e.other.symm ▸ hb)
  have we := wa.trans ((congrArg RingStereoSiblingPass.Branch.word same).trans wb.symm)
  have order := (exactTable ks ws legal mark a b).2
  rw [ke,we] at order
  cases v : table[a.val][b.val] <;> simp_all [Verdict.order]

open RingObservedTreeMatch (Unmarked propose signature signature_transport)
open private cachedChildren kids children_exact observed candidate checkUnmarked
  from TetraStereo.Engine.RingObservedTreeMatch

private theorem propose_of_unmarked {i : Input} {f : Site i} {fr : Frame i f} {r : Reader i}
    {a b : Slot} (e : Unmarked fr r a b) : (propose fr r none a b).isSome = true := by
  obtain ⟨k,hk,hl⟩ := signature_transport e.carrier e.frozen none none (fun _ _ => rfl)
    (cursor fr a) e.start (RingGroupedCentre.valid fr a) (e.target.symm ▸ RingGroupedCentre.valid fr b)
  rw [e.target] at hl
  have cache : cachedChildren f = kids := funext (children_exact f)
  unfold signature at hk hl
  obtain ⟨x,hx,kx⟩ := Option.map_eq_some_iff.mp hk
  obtain ⟨y,hy,ky⟩ := Option.map_eq_some_iff.mp hl
  simp [propose,observed,cache,candidate,hx,hy,kx,ky]

/-- Signature disagreement excludes any functional unmarked exchange. -/
theorem unmarked_absent_of_no_proposal {i : Input} {f : Site i} {fr : Frame i f} {r : Reader i}
    {a b : Slot} (miss : propose fr r none a b = none) : ¬ Nonempty (Unmarked fr r a b) := by
  rintro ⟨e⟩
  have hit := propose_of_unmarked e
  simp [miss] at hit

/-- Exact ordinary exchange. Unequal signatures reject; a verified proposed
alignment accepts. Only an inconclusive functional alignment needs enumeration. -/
def decideUnmarked {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (a b : Slot) : Bool :=
  match propose fr r none a b with
  | none => false
  | some rows =>
    match checkUnmarked fr r a b rows with
    | some _ => true
    | none => RingFiniteExchange.existsMatch r r none none (cursor fr a) (cursor fr b)

theorem decideUnmarked_iff {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (a b : Slot) :
    decideUnmarked fr r a b = true ↔ Nonempty (Unmarked fr r a b) := by
  unfold decideUnmarked
  cases proposal : propose fr r none a b with
  | none =>
    constructor
    · intro h; contradiction
    · exact fun e => (unmarked_absent_of_no_proposal proposal e).elim
  | some rows =>
    cases checked : checkUnmarked fr r a b rows with
    | some e => simp only [checked]; exact iff_of_true True.intro ⟨e⟩
    | none => simp only [checked]; exact RingFiniteExchange.unmarked_iff fr r a b

theorem strict_excludes_unmarked {i : Input} {f : Site i} (fr : Frame i f) {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) {rev : Bool} {a b : Slot} {table : Table}
    (exactTable : TableExact fr r rev none table) (different : table[a.val][b.val] ≠ .tie) :
    ¬ Nonempty (Unmarked fr r a b) := by
  rintro ⟨e⟩
  obtain ⟨ks,_,only⟩ := keys_exact fr ready rev
  have legal := (only ks).mpr rfl
  have ke := RingFullPathKeyTransport.reads_transport e.carrier e.frozen rev e.start
    (legal a) (e.target.symm ▸ legal b)
  have order := (exactTable ks (fun _ => []) legal (fun _ => rfl) a b).2
  rw [ke] at order
  cases v : table[a.val][b.val] <;> simp_all [Verdict.order]

inductive Classification where
  | exchangeTie
  | noExchangeTie
  | noExchangeLeft (stage : Stage)
  | noExchangeRight (stage : Stage)
  deriving DecidableEq, Repr

def Classification.verdict : Classification → Verdict
  | .exchangeTie | .noExchangeTie => .tie
  | .noExchangeLeft s => .left s
  | .noExchangeRight s => .right s

def Classification.exchanged : Classification → Bool
  | .exchangeTie => true
  | _ => false

def HasExchange {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i)
    (m : Option Slot) (a b : Slot) : Prop :=
  match m with
  | none => Nonempty (Unmarked fr r a b)
  | some s => Nonempty (RingGeometryExchange.Exchange fr r s a b)

private def decideExchange {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i)
    (m : Option Slot) (a b : Slot) : Bool :=
  match m with
  | none => decideUnmarked fr r a b
  | some s => RingFiniteExchange.decidePair fr r s a b

private theorem decideExchange_iff {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i)
    (m : Option Slot) (a b : Slot) : decideExchange fr r m a b = true ↔ HasExchange fr r m a b := by
  cases m with
  | none => exact decideUnmarked_iff fr r a b
  | some s => exact RingFiniteExchange.decidePair_iff fr r s a b

/-- Strict priorities bypass the exchange search. Only a complete comparison
tie can require a structural decision for the requested ordered pair. -/
def classify {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (m : Option Slot)
    (a b : Slot) : Verdict → Classification
  | .left s => .noExchangeLeft s
  | .right s => .noExchangeRight s
  | .tie => if decideExchange fr r m a b then .exchangeTie else .noExchangeTie

theorem classify_iff {i : Input} {f : Site i} (fr : Frame i f) {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) {rev : Bool} {m : Option Slot} {table : Table}
    (exactTable : TableExact fr r rev m table) (a b : Slot) (c : Classification) :
    classify fr r m a b table[a.val][b.val] = c ↔
    table[a.val][b.val] = c.verdict ∧ (HasExchange fr r m a b ↔ c.exchanged = true) := by
  have strict : table[a.val][b.val] ≠ .tie → ¬ HasExchange fr r m a b := by
    intro diff
    cases m with
    | none => exact strict_excludes_unmarked fr ready exactTable diff
    | some s => exact strict_excludes_exchange fr ready exactTable diff
  cases verdict : table[a.val][b.val] with
  | tie =>
    cases h : decideExchange fr r m a b <;> cases c <;>
      simp [classify,h,Classification.verdict,Classification.exchanged,← decideExchange_iff]
  | left s =>
    have absent := strict (by simp [verdict])
    cases c <;> simp [classify,Classification.verdict,Classification.exchanged,absent]
  | right s =>
    have absent := strict (by simp [verdict])
    cases c <;> simp [classify,Classification.verdict,Classification.exchanged,absent]

def Trial.table (t : Trial) (rev : Bool) : Table := if rev then t.mirrored else t.actual

/-- Select one scheduled trial by its zero-based ordinal, retaining its
nomination in the result. All other ordered pairs skip structural searches. -/
def classifyAt? (i : Input) (root : i.certified.Atom) (batch : Nat) (f : Site i)
    (ordinal : Nat) (rev : Bool) (a b : Slot) : Option (Option Slot × Classification) := do
  let fr ← RingNestedActivePair.frame? i f
  let read := RingGlobalComparison.prior i root batch
  let rows ← diagnose? fr read
  let t ← rows[ordinal]?
  return (t.nomination,classify fr read t.nomination a b (t.table rev)[a.val][b.val])

/-- At any reached public frame, the verdict for one scheduled entry gives
both its exact molecular order and existence or absence of its functional
exchange on the same materialized public reader. -/
theorem public_classify_iff {i : Input} {f : Site i} (fr : Frame i f)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) {root : i.certified.Atom} {batch : Nat}
    (called : RingGlobalComparison.Called i root batch f) {out : List Trial}
    (found : atSite? i root batch f = some out) {ordinal : Nat} {t : Trial} (row : out[ordinal]? = some t)
    (rev : Bool) (a b : Slot) (c : Classification) :
    classifyAt? i root batch f ordinal rev a b = some (t.nomination,c) ↔
    (t.table rev)[a.val][b.val] = c.verdict ∧
    (HasExchange fr (RingGlobalComparison.prior i root batch) t.nomination a b ↔ c.exchanged = true) := by
  obtain ⟨xs,hxs,spec⟩ := public_exact fr geom called
  obtain rfl := Option.some.inj (hxs.symm.trans found)
  have exactPair := spec.pairs t (List.mem_of_getElem? row)
  have selected : TableExact fr (RingGlobalComparison.prior i root batch) rev t.nomination (t.table rev) := by
    cases rev with
    | false => exact exactPair.1
    | true => exact exactPair.2
  have ready : RingGroupedStereo.Ready f (RingGlobalComparison.prior i root batch) := by
    rw [RingGlobalComparison.prior_exact called]
    exact RingChemicalGraphProof.ready geom f
  simp [atSite?,frame_eq fr] at hxs
  simpa [classifyAt?,frame_eq fr,hxs,row] using classify_iff fr ready selected a b c

end TetraStereo.Engine.RingResidualPairDecision

assert_kernel_only TetraStereo.Engine.RingResidualPairDecision.diagnosis_exact
assert_kernel_only TetraStereo.Engine.RingResidualPairDecision.public_exact
assert_kernel_only TetraStereo.Engine.RingResidualPairDecision.strict_excludes_exchange
assert_kernel_only TetraStereo.Engine.RingResidualPairDecision.decideUnmarked_iff
assert_kernel_only TetraStereo.Engine.RingResidualPairDecision.classify_iff
assert_kernel_only TetraStereo.Engine.RingResidualPairDecision.public_classify_iff
