import TetraStereo.Engine.RingUnorderedRankIntervals
import TetraStereo.Engine.RingOrdinaryPairVerdict
import TetraStereo.Engine.RingEqualPathHandCounts

/-! Read arbitrary signed path populations by counting how many visible keys
rank higher and how many rank at least as high as each terminal path.
This reconstructs the signed bits without sorting those paths. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingCountedPathVerdict
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingActivePairReport (Slot)
open RingNestedActivePair (Frame Reader)
open RingGroupedCentre (cursor)
open RingStereoSphereInventory (Inventory SignedPath inventory? project)
open RingFullPathPairs (bitOf)
open RingRetainedChemicalTrace (Word)
open RingFullPathEligibility (Key)
open RingFullPathTrialReadings (markWords?)
open RingResidualPairDecision (Table TableExact Verdict Classification Trial)
open private pick pick_exact matrix decideExchange decideExchange_iff from TetraStereo.Engine.RingResidualPairDecision
open private keys_exact from TetraStereo.Engine.RingFullPathPublication
open private verdict_unique from TetraStereo.Engine.RingEqualPathHandCounts
attribute [local instance] lexOrd

def sphere (seed : RS) (row : Multiset SignedPath) :=
  RingUnorderedRankIntervals.word (row.map (project seed)) bitOf

theorem sphere_exact (seed : RS) (row : Multiset SignedPath) :
    sphere seed row = RingStereoSphereInventory.sphere seed row := by
  induction row using Quotient.inductionOn with
  | _ xs =>
    change RingUnorderedRankIntervals.word (↑(xs.map (project seed))) bitOf =
      RingUnorderedSphereReading.readRow (project seed) bitOf xs
    rw [RingUnorderedRankIntervals.word_exact]
    exact (RingUnorderedSphereReading.readRow_map (project seed) id bitOf xs).symm

def reading (seed : RS) (inv : Inventory) := inv.flatMap (sphere seed)

theorem reading_exact (seed : RS) (inv : Inventory) :
    reading seed inv = RingStereoSphereInventory.reading seed inv := by
  simp only [reading,RingStereoSphereInventory.reading,funext (sphere_exact seed)]

def key? (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) : Option Key := do
  let u ← RingRetainedStereoRefinement.priority i r rev [] q
  let l ← RingRetainedStereoRefinement.priority i r rev [.lowercase] q
  let b ← inventory? i r rev [] q
  let f ← inventory? i r rev [.lowercase] q
  return ⟨u.deep,max (reading .R b) (reading .S b),l.word,reading .R f⟩

/-- All molecular inputs and readers, including failure, with no uniformity or
correspondence assumption on the branches, depths, signed stems, or ranks. -/
theorem key_exact (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) :
    key? i r rev q = RingFullPathEligibility.key? i r rev q := by
  rw [← RingStereoSphereInventory.key_exact]
  simp only [key?,RingStereoSphereInventory.key?,reading_exact]

private def keys? {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (rev : Bool) :=
  RingActivePairReport.four? fun k => key? i r rev (cursor fr k)

private theorem keys_eq {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (rev : Bool) :
    keys? fr r rev = RingFullPathPublication.keys? fr r rev := by
  simp [keys?,RingFullPathPublication.keys?,key_exact]

def ordinary? {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (rev : Bool) : Option Table :=
  (keys? fr r rev).map fun ks => matrix ks (fun _ => [])

def schedule? {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) : Option (List Trial) := do
  let ks ← keys? fr r false
  let ms ← keys? fr r true
  (RingFullPathTrialReadings.trials ks).mapM fun s => do
    let ws ← markWords? fr r s
    return ⟨s,matrix ks ws,matrix ms ws⟩

theorem ordinary_exact {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (rev : Bool) :
    ordinary? fr r rev = RingOrdinaryPairVerdict.onReader? fr r rev := by
  simp [ordinary?,RingOrdinaryPairVerdict.onReader?,keys_eq]

theorem schedule_exact {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) :
    schedule? fr r = RingResidualPairDecision.diagnose? fr r := by
  simp [schedule?,RingResidualPairDecision.diagnose?,keys_eq]

/-- Query only the requested pair. The optional mark uses the same recorded
nomination as the trial; an absent mark compares the complete ordinary rules. -/
def pair? {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (rev : Bool)
    (m : Option Slot) (a b : Slot) : Option Verdict := do
  let x ← key? i r rev (cursor fr a)
  let y ← key? i r rev (cursor fr b)
  let marks ← markWords? fr r m
  return pick (RingLigandFirstDifference.directions
    (RingResidualPairDecision.words x (marks a)) (RingResidualPairDecision.words y (marks b)))
    RingLigandFirstDifference.stages

theorem pair_exact {i : Input} {f : Site i} (fr : Frame i f) {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) {rev : Bool} {m : Option Slot} {t : Table}
    (reported : TableExact fr r rev m t) (a b : Slot) :
    pair? fr r rev m a b = some t[a.val][b.val] := by
  obtain ⟨ks,_,only⟩ := keys_exact fr ready rev
  have legal := (only ks).mpr rfl
  have native (s : Slot) : key? i r rev (cursor fr s) = some (ks s) := by
    obtain ⟨k,hk,eqn⟩ := RingFullPathEligibility.key_exact ready rev (cursor fr s)
      (RingGroupedCentre.valid fr s) (fr.direction s).property.1
    simpa only [key_exact,(eqn _).mp (legal s)] using hk
  obtain ⟨ws,found,law⟩ := RingFullPathTrialReadings.mark_exact fr ready rev m
  have agrees := verdict_unique (pick_exact _ _) (reported ks ws legal ((law ws).mpr rfl) a b).1
  simp [pair?,native,found,agrees]

/-- Retain the structural distinction between the two kinds of ordinary
or nominated tie. A strict decision already rules out an exchange. -/
def classify? {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (rev : Bool)
    (m : Option Slot) (a b : Slot) : Option Classification :=
  (pair? fr r rev m a b).map (RingResidualPairDecision.classify fr r m a b)

theorem classifies_iff {i : Input} {f : Site i} (fr : Frame i f) {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) {rev : Bool} {m : Option Slot} {t : Table}
    (reported : TableExact fr r rev m t) (a b : Slot) (c : Classification) :
    classify? fr r rev m a b = some c ↔ t[a.val][b.val] = c.verdict ∧
      (RingResidualPairDecision.HasExchange fr r m a b ↔ c.exchanged = true) := by
  simp only [classify?,pair_exact fr ready reported,Option.map_some,Option.some.injEq]
  exact RingResidualPairDecision.classify_iff fr ready reported a b c

open private frame_eq from TetraStereo.Engine.RingGroupedReport

/-- All actual nominations, both passes, and all ordered ligand pairs at any
reached public frame. The caller supplies neither a table nor an assertion
about exchange, and may query any of the four classes of results. -/
theorem public_schedule {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {root : i.certified.Atom} {batch : Nat} {f : Site i} (called : RingGlobalComparison.Called i root batch f)
    (fr : Frame i f) :
    let r := RingGlobalComparison.prior i root batch
    ∃ ts, schedule? fr r = some ts ∧ RingResidualPairDecision.Exact fr r ts ∧
      ∀ t ∈ ts, ∀ (rev : Bool) (a b : Slot) (c : Classification),
        classify? fr r rev t.nomination a b = some c ↔ (t.table rev)[a.val][b.val] = c.verdict ∧
          (RingResidualPairDecision.HasExchange fr r t.nomination a b ↔ c.exchanged = true) := by
  obtain ⟨ts,found,law⟩ := RingResidualPairDecision.public_exact fr geom called
  have ready : RingGroupedStereo.Ready f (RingGlobalComparison.prior i root batch) := by
    rw [RingGlobalComparison.prior_exact called]
    exact RingChemicalGraphProof.ready geom f
  refine ⟨ts,?_,law,?_⟩
  · simpa [schedule_exact,RingResidualPairDecision.atSite?,frame_eq fr] using found
  · intro t ht rev a b c
    apply classifies_iff fr ready
    cases rev
    · exact (law.pairs t ht).1
    · exact (law.pairs t ht).2

/-- Public scheduled-pair query reconstructed by the interval procedure,
retaining the nominated slot and any missing frame or out-of-range trial. -/
def atSite? (i : Input) (root : i.certified.Atom) (batch : Nat) (f : Site i)
    (ordinal : Nat) (rev : Bool) (a b : Slot) : Option (Option Slot × Classification) := do
  let fr ← RingNestedActivePair.frame? i f
  let r := RingGlobalComparison.prior i root batch
  let trials ← schedule? fr r
  let t ← trials[ordinal]?
  return (t.nomination,RingResidualPairDecision.classify fr r t.nomination a b (t.table rev)[a.val][b.val])

/-- Equality at the implementation of the existing public ringLigandPairAt?
entry point, with no conditions on inputs, requested slots or ordinal. -/
theorem atSite_exact (i : Input) (root : i.certified.Atom) (batch : Nat) (f : Site i)
    (ordinal : Nat) (rev : Bool) (a b : Slot) :
    atSite? i root batch f ordinal rev a b = RingResidualPairDecision.classifyAt? i root batch f ordinal rev a b := by
  simp only [atSite?,RingResidualPairDecision.classifyAt?,schedule_exact]

def withoutExchange : Verdict → Classification
  | .tie => .noExchangeTie
  | .left s => .noExchangeLeft s
  | .right s => .noExchangeRight s

/-- The actual ordinary verdict when no exchange exists, on every reached
public tetrahedral frame. No explicit hand, tie, path alignment, or rule
number is supplied to the counting procedure. -/
theorem public_no_exchange {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {root : i.certified.Atom} {batch : Nat} {f : Site i} (called : RingGlobalComparison.Called i root batch f)
    (fr : Frame i f) (rev : Bool) (a b : Slot)
    (absent : ¬ RingResidualPairDecision.HasExchange fr (RingGlobalComparison.prior i root batch) none a b) :
    ∃ t, ordinary? fr (RingGlobalComparison.prior i root batch) rev = some t ∧
      RingOrdinaryPairVerdict.table? i root batch f rev = some t ∧
      RingResidualPairDecision.classify fr (RingGlobalComparison.prior i root batch) none a b
        t[a.val][b.val] = withoutExchange t[a.val][b.val] := by
  obtain ⟨t,got,_⟩ := RingOrdinaryPairVerdict.exact geom called fr rev
  refine ⟨t,?_,got,?_⟩
  · rwa [ordinary_exact,← RingOrdinaryPairVerdict.at_call geom called fr rev]
  · have no : decideExchange fr (RingGlobalComparison.prior i root batch) none a b = false := by
      simpa [Bool.eq_false_iff,decideExchange_iff] using absent
    cases h : t[a.val][b.val] <;> simp [RingResidualPairDecision.classify,withoutExchange,no]

end TetraStereo.Engine.RingCountedPathVerdict
assert_kernel_only TetraStereo.Engine.RingCountedPathVerdict.key_exact
assert_kernel_only TetraStereo.Engine.RingCountedPathVerdict.schedule_exact
assert_kernel_only TetraStereo.Engine.RingCountedPathVerdict.public_no_exchange
assert_kernel_only TetraStereo.Engine.RingCountedPathVerdict.pair_exact
assert_kernel_only TetraStereo.Engine.RingCountedPathVerdict.public_schedule
assert_kernel_only TetraStereo.Engine.RingCountedPathVerdict.atSite_exact
