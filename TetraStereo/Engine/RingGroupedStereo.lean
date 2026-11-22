import TetraStereo.Engine.RingRetainedSeedFrames
import TetraStereo.Engine.RingProximalPair

set_option autoImplicit false

namespace TetraStereo.Engine.RingGroupedStereo
open OneCenter CertifiedLocalizedCIPInput RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site molecularValues)
open RingNestedActivePair (Reader Labels consistent)
open RingRetainedStereoRefinement (Derives Observation Pass)
open RingRetainedStereoDecision (ArmProfile Reads Result First)
open RingRetainedChemicalTrace (Key key? compareAt?)

private abbrev children (i : Input) (q : Arm i) := i.certified.executableLocalizedRerootChildren q

private def extend (p : Branch) (v : Nat) (cs : List Branch) :=
  RingRetainedStereoRefinement.extend p v (order Branch.shallow cs) (order Branch.deep cs)

/-- All stages share the same molecular child enumeration. Each stage sorts
the children by its own complete priorities. -/
def assemble (k : Key) (v : Option Labels) (cs : List ArmProfile) : ArmProfile :=
  let us := cs.map ArmProfile.unit
  let u := RingRetainedUnitPass.branch k (RingNestedActivePair.unit (v.map Prod.fst))
    (order Branch.shallow us) (order Branch.deep us)
  let loc (s : RS) := extend u ((Observation.pairing s).value v false) (cs.map (fun p => p.localPair s))
  let lo := extend u (Observation.lowercase.value v false) (cs.map ArmProfile.lower)
  let fixed (s : RS) := extend lo ((Observation.pairing s).value v false) (cs.map (fun p => p.fixedPair s))
  ⟨u,RingRetainedReferenceGroup.joinHits v (cs.map fun p => (p.unit,p.hits)),loc .R,loc .S,lo,fixed .R,fixed .S⟩

private def build (i : Input) (read : Reader i) (getKey : Arm i → Option Key) (edges : Arm i → List (Arm i)) :
    Nat → Arm i → Option ArmProfile
  | 0,_ => none
  | n+1,q => do
    let v ← read q.occurrence
    let kids := edges q
    guard (v.all consistent = true ∧ (kids = [] → v = none))
    let k ← getKey q
    let cs ← kids.mapM (build i read getKey edges n)
    return assemble k v cs

def arm? (i : Input) (read : Reader i) (q : Arm i) := build i read (key? i) (children i)
  (i.certified.localizedRerootCursorBudget q + 1) q

private def cachedArm (i : Input) (read : Reader i) (q : Arm i) :=
  let cache := localizedRerootRootSliceCache (i.certified.localizedRerootCarrierCache
    (i.certified.certified.input.molecule.atomCount + 1)) q.occurrence.val.root
  build i read (RingRetainedChemicalTrace.keyWith i cache.reader) (fun c => (cache.reader.readChildren c).getD [])
    (i.certified.localizedRerootCursorBudget q + 1) q

@[csimp] theorem arm_cached : @arm? = @cachedArm := by
  funext i read q
  let cache := localizedRerootRootSliceCache (i.certified.localizedRerootCarrierCache
    (i.certified.certified.input.molecule.atomCount + 1)) q.occurrence.val.root
  have same : (fun c : Arm i => (cache.reader.readChildren c).getD []) = children i := by
    funext c; rw [cache.reader.readChildren_eq]; rfl
  simp only [arm?,cachedArm,RingRetainedChemicalTrace.keyWith_eq]
  rw [same]

private theorem projected {α β γ : Type} {xs : List α} {ys : List β} {get : α → Option β}
    (found : xs.mapM get = some ys) (f : β → γ) : xs.mapM (fun t => (get t).map f) = some (ys.map f) := by
  induction xs generalizing ys with
  | nil => obtain rfl := Option.some.inj found; rfl
  | cons x xs ih =>
    rw [List.mapM_cons] at found
    obtain ⟨v,hv,more⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨vs,hs,out⟩ := Option.bind_eq_some_iff.mp more
    obtain rfl := Option.some.inj out
    simp [List.mapM_cons,hv,ih hs]

private theorem assembled {i read q v k cs} {get : Arm i → Option ArmProfile}
    (seen : read q.occurrence = some v) (ok : v.all consistent = true ∧ (children i q = [] → v = none))
    (key : key? i q = some k) (kids : (children i q).mapM get = some cs)
    (source : ∀ c ∈ children i q, ∀ {p}, get c = some p → Reads i read false c p) :
    Reads i read false q (assemble k v cs) := by
  let p := assemble k v cs
  have unit : Derives i read false [] q p.unit := by
    refine RingRetainedUnitPass.Reading.node key seen ok _ (projected kids ArmProfile.unit) ?_ (legal_order ..) (legal_order ..)
    intro c hc b h
    obtain ⟨t,ht,rfl⟩ := Option.map_eq_some_iff.mp h
    exact (source c hc ht).unit
  have hits : RingRetainedReferenceGroup.Listing i read q p.hits := by
    let take (p : ArmProfile) := (p.unit,p.hits)
    refine .node seen ok _ (projected kids take) ?_ ?_
    all_goals
      intro c hc b hs got
      obtain ⟨t,ht,eqn⟩ := Option.map_eq_some_iff.mp got
      cases eqn
      first | exact (source c hc ht).unit | exact (source c hc ht).hits
  have step {os : List Observation} (o : Observation) (f : ArmProfile → Branch) {prev}
      (before : Derives i read false os q prev) (field : ∀ c t, Reads i read false c t → Derives i read false (o::os) c (f t)) :
      Derives i read false (o::os) q (extend prev (o.value v false) (cs.map f)) := by
    refine Pass.node before seen _ (projected kids f) ?_ (legal_order ..) (legal_order ..)
    intro c hc b got
    obtain ⟨t,ht,rfl⟩ := Option.map_eq_some_iff.mp got
    exact field c t (source c hc ht)
  have lower : Derives i read false [.lowercase] q p.lower := step .lowercase _ unit (fun _ _ h => h.lower)
  refine ⟨unit,hits,?_,lower,?_⟩
  · rintro (_|_) <;> apply step _ _ unit <;> intro c t h <;> first | exact h.paired .R | exact h.paired .S
  · rintro (_|_) <;> apply step _ _ lower <;> intro c t h <;> first | exact h.fixed .R | exact h.fixed .S

private theorem build_source {i read} : ∀ n q {p}, build i read (key? i) (children i) n q = some p → Reads i read false q p
  | 0,_,_,h => by contradiction
  | n+1,q,_,h => by
    unfold build at h
    obtain ⟨v,hv,more⟩ := Option.bind_eq_some_iff.mp h
    by_cases ok : v.all consistent = true ∧ (children i q = [] → v = none)
    · have gate : (guard (v.all consistent = true ∧ (children i q = [] → v = none)) : Option Unit) = some () := if_pos ok
      simp only [gate,Option.bind_eq_bind,Option.bind_some] at more
      obtain ⟨k,hk,more⟩ := Option.bind_eq_some_iff.mp more
      obtain ⟨cs,found,out⟩ := Option.bind_eq_some_iff.mp more
      obtain rfl := Option.some.inj out
      exact assembled hv ok hk found (fun c _ _ get => build_source n c get)
    · simp [ok] at more

theorem arm_source {i read q p} (h : arm? i read q = some p) : Reads i read false q p :=
  build_source _ q h

theorem arm_frontier {i : Input} {root : i.certified.Atom} {f : Site i}
    (listed : f ∈ RingMolecularSchedule.frontier i root) (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q)
    (on : q.occurrence.val.root = f.val.root) :
    let read := RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)
    ∃ p, arm? i read q = some p := by
  intro read
  suffices ∀ n (q : Arm i), i.certified.LocalizedRerootCursorValid q → q.occurrence.val.root = f.val.root →
    i.certified.localizedRerootCursorBudget q < n → ∃ p, build i read (key? i) (children i) n q = some p from
    this _ q valid on (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro t _ _ h; omega
  | succ n ih =>
    intro t vt rt budget
    obtain ⟨v,hv,ok,absent⟩ := RingFrontierProfileShape.frontier_observation listed t rt
    change read t.occurrence = some v at hv
    have gate : (guard (v.all consistent = true ∧ (children i t = [] → v = none)) : Option Unit) = some () :=
      if_pos ⟨ok,absent⟩
    obtain ⟨k,hk⟩ := RingRetainedChemicalCoverage.key_total i (RingRetainedChemicalCoverage.admitted_atoms i) t vt
    have frame := i.certified.executableLocalizedRerootChildren_declarative t
    obtain ⟨cs,hcs⟩ := RingRetainedUnitPass.collect _ (children i t) (fun c hc =>
      ih c (i.certified.localizedRerootChild_valid t c _ frame hc)
        ((i.certified.localizedRerootChildren_root_eq t c _ frame hc).trans rt)
        (by have := i.certified.localizedRerootChild_budget_lt t c _ vt frame hc; omega))
    exact ⟨assemble k v cs,by simp only [build,hv,gate,hk,hcs,Option.bind_eq_bind,Option.bind_some,Option.pure_def]⟩

/-- A signed, rule-tagged result for both geometries of this constitutional
tie. The reflected profile exchanges the two fixed and the two local hands. -/
def comparison? (i : Input) (f a b : Site i) (read : Reader i) : Option (Result × Result) := do
  let prior ← compareAt? i f a b
  guard (cipTraceOutcome prior == .eq)
  let x ← arm? i read ⟨a,some f⟩
  let y ← arm? i read ⟨b,some f⟩
  return (← RingRetainedStereoDecision.decide? x y false,← RingRetainedStereoDecision.decide? x.reflect y.reflect true)

def scores (v : Result × Result) : Int × Int := (v.1.score,v.2.score)

/-- The casing consumer accepts exactly its five molecular signed pairs. -/
def score? (i : Input) (f a b : Site i) (read : Reader i) : Option (Int × Int) := do
  let v ← comparison? i f a b read
  guard (scores v ∈ molecularValues)
  return scores v

theorem score_values {i f a b read k} (got : score? i f a b read = some k) : k ∈ molecularValues := by
  obtain ⟨v,_,rest⟩ := Option.bind_eq_some_iff.mp got
  by_cases ok : scores v ∈ molecularValues <;> simp_all [guard]

/-- P-92.5.2.1(c)(i) agrees with the independently defined ranked-ligand
judgment for every pair of descriptor words in the mixed reference-count
case. No population or ordering premise can reverse this decision. -/
theorem single_before_dual {x y : ArmProfile} {rev s}
    (one : RingRetainedReferenceGroup.references x.hits rev = [s])
    (two : RingRetainedReferenceGroup.references y.hits rev = [.R,.S]) :
    RingRetainedStereoDecision.fourB? x y rev = some 1 ∧ RingRetainedStereoDecision.fourB? y x rev = some (-1) ∧
    ∀ l r, RingChemicalPriority.Recursive.RankResult [s] [.R,.S] l r .gt := by
  simp [RingRetainedStereoDecision.fourB?,one,two,RingChemicalPriority.Recursive.RankResult]

private theorem fourB_signs {x y : ArmProfile} {rev k} (got : RingRetainedStereoDecision.fourB? x y rev = some k) :
    k ∈ ([-1,0,1] : List Int) := by
  rcases RingRetainedReferenceGroup.references_cases x.hits rev with lx | ⟨s,lx⟩ | lx <;>
    rcases RingRetainedReferenceGroup.references_cases y.hits rev with ry | ⟨t,ry⟩ | ry <;>
    simp only [RingRetainedStereoDecision.fourB?,lx,ry] at got <;> try contradiction
  all_goals obtain rfl := Option.some.inj got
  all_goals first | decide | exact RingRetainedStereoRefinement.pair_signs .. | exact RingRetainedStereoRefinement.bit_signs ..

private theorem unit_signs (a b : Branch) : RingRetainedUnitPass.signed a b ∈ ([-1,0,1] : List Int) := by
  unfold RingRetainedUnitPass.signed
  cases compare a.word b.word <;> decide

private theorem strict_pair {k : Int} (vals : k ∈ ([-1,0,1] : List Int)) (nz : k ≠ 0) : (k,k) ∈ molecularValues := by
  simp [molecularValues] at *
  grind

private theorem both_values {i : Input} {root : i.certified.Atom} {f a b : Site i} {p x y v w}
    (listed : f ∈ RingMolecularSchedule.frontier i root) (prior : compareAt? i f a b = some p) (tie : cipTraceOutcome p = .eq)
    (left : Reads i (RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)) false ⟨a,some f⟩ x)
    (right : Reads i (RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)) false ⟨b,some f⟩ y)
    (actual : RingRetainedStereoDecision.decide? x y false = some v)
    (reflected : RingRetainedStereoDecision.decide? x.reflect y.reflect true = some w) : scores (v,w) ∈ molecularValues := by
  have rule {p q rev k} (src : First p q rev k) := RingRetainedStereoDecision.first_iff.mp src
  by_cases u : RingRetainedUnitPass.signed x.unit y.unit = 0
  · have unit := (RingRetainedUnitPass.signed_zero_iff ..).mp u
    obtain ⟨k,hk⟩ := RingRetainedStereoDecision.fourB_total left right unit
    have mirror := (RingRetainedStereoDecision.fourB_reflect x y).trans hk
    by_cases both : k = 0
    · subst k
      by_cases l : RingRetainedUnitPass.signed x.lower y.lower = 0
      · have low := (RingRetainedUnitPass.signed_zero_iff ..).mp l
        have pair := RingRetainedStereoDecision.fixed_both unit hk low
        obtain rfl := Option.some.inj (actual.symm.trans pair.1)
        obtain rfl := Option.some.inj (reflected.symm.trans pair.2)
        exact (RingProximalPair.mirror_values_iff ..).mpr (RingRetainedSeedFrames.fixed_equality listed false prior tie left right unit low)
      · obtain rfl := Option.some.inj (actual.symm.trans (rule (.lower unit hk l)))
        obtain rfl := Option.some.inj (reflected.symm.trans (rule (.lower unit mirror l)))
        exact strict_pair (unit_signs ..) l
    · obtain rfl := Option.some.inj (actual.symm.trans (rule (.pairs unit hk both)))
      obtain rfl := Option.some.inj (reflected.symm.trans (rule (.pairs unit mirror both)))
      exact strict_pair (fourB_signs hk) both
  · obtain rfl := Option.some.inj (actual.symm.trans (rule (.unit u)))
    obtain rfl := Option.some.inj (reflected.symm.trans (rule (.unit u)))
    exact strict_pair (unit_signs ..) u

/-- A zero on both geometries is exactly a tie through all rules, including
both fixed reference comparisons. The local Rule 4b result is calculated
with each ligand's selected reference population. -/
theorem tie_iff {i : Input} {root : i.certified.Atom} {f a b : Site i} {p x y}
    (listed : f ∈ RingMolecularSchedule.frontier i root) (prior : compareAt? i f a b = some p)
    (tie : cipTraceOutcome p = .eq)
    (left : Reads i (RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)) false ⟨a,some f⟩ x)
    (right : Reads i (RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)) false ⟨b,some f⟩ y) :
    (First x y false ⟨none,0⟩ ∧ First x.reflect y.reflect true ⟨none,0⟩) ↔
      x.unit.word = y.unit.word ∧ RingRetainedStereoDecision.fourB? x y false = some 0 ∧
      x.lower.word = y.lower.word ∧ RingRetainedStereoDecision.seedSign x y .R = 0 ∧
      RingRetainedStereoDecision.seedSign x y .S = 0 := by
  constructor
  · rintro ⟨original,_⟩
    have characterize {z} (decision : First x y false z) (empty : z = ⟨none,0⟩) :
        x.unit.word = y.unit.word ∧ RingRetainedStereoDecision.fourB? x y false = some 0 ∧
        x.lower.word = y.lower.word ∧ RingRetainedStereoDecision.seedSign x y .R = 0 ∧
        RingRetainedStereoDecision.seedSign x y .S = 0 := by
      cases decision with
      | unit | pairs | lower => cases congrArg Result.rule empty
      | fixed u paired low =>
        have score := congrArg Result.score empty
        change CentresRing.PairList.combine _ _ = 0 at score
        have zero : RingRetainedStereoDecision.seedSign x y .R = 0 := by
          unfold CentresRing.PairList.combine at score
          split_ifs at score <;> omega
        exact ⟨u,paired,low,zero,(RingRetainedSeedFrames.fixed_equality listed false prior tie left right u low).mp zero⟩
    exact characterize original rfl
  · rintro ⟨u,paired,low,r,s⟩
    obtain ⟨actual,mirrored⟩ := RingRetainedStereoDecision.fixed_both u paired low
    simp only [r,s,RingRetainedStereoDecision.fixedResult,CentresRing.PairList.combine] at actual mirrored
    exact ⟨RingRetainedStereoDecision.first_iff.mpr actual,RingRetainedStereoDecision.first_iff.mpr mirrored⟩

/-- Every pair of independently chosen legal readings on the indicated
geometry gives exactly this first deciding rule and signed magnitude. -/
def Determined {i : Input} (read : Reader i) (a b : Arm i) (rev : Bool) (v : Result) : Prop :=
  (∃ x y, Reads i read rev a x ∧ Reads i read rev b y) ∧
    ∀ x y, Reads i read rev a x → Reads i read rev b y → ∀ k, First x y rev k ↔ k = v

private theorem determined {i read rev a b x y v} (l : Reads i read rev a x) (r : Reads i read rev b y)
    (hit : RingRetainedStereoDecision.decide? x y rev = some v) : Determined read a b rev v := by
  refine ⟨⟨x,y,l,r⟩,?_⟩
  intro p q hp hq k
  obtain rfl := l.unique hp
  obtain rfl := r.unique hq
  rw [RingRetainedStereoDecision.first_iff,hit,Option.some.injEq,eq_comm]

/-- Every successful execution, including one against a caller's reader,
carries a constitutional tie and a molecular first-rule derivation on each
geometry. A missing or physically inconsistent observation cannot supply a
reading of that subtree. -/
theorem comparison_source {i f a b read z} (got : comparison? i f a b read = some z) :
    ∃ p, compareAt? i f a b = some p ∧ cipTraceOutcome p = .eq ∧
      Determined read ⟨a,some f⟩ ⟨b,some f⟩ false z.1 ∧ Determined read ⟨a,some f⟩ ⟨b,some f⟩ true z.2 := by
  unfold comparison? at got
  obtain ⟨p,hp,next⟩ := Option.bind_eq_some_iff.mp got
  cases eqn : cipTraceOutcome p <;> simp only [eqn,beq_self_eq_true,guard_true,pure_bind] at next
  all_goals try {simp at next}
  obtain ⟨x,hx,next⟩ := Option.bind_eq_some_iff.mp next
  obtain ⟨y,hy,next⟩ := Option.bind_eq_some_iff.mp next
  obtain ⟨v,hv,next⟩ := Option.bind_eq_some_iff.mp next
  obtain ⟨w,hw,out⟩ := Option.bind_eq_some_iff.mp next
  obtain rfl := Option.some.inj out
  exact ⟨p,hp,eqn,determined (arm_source hx) (arm_source hy) hv,
    determined (arm_source hx).reflect (arm_source hy).reflect hw⟩

/-- Every reachable constitutional tie has a molecular comparison and both
signed results pass the casing gate. No agreement over arbitrary permutations,
reference hand, seed equality, or external trace score is assumed. -/
theorem frontier {i : Input} {root : i.certified.Atom} {f a b : Site i} {p}
    (listed : f ∈ RingMolecularSchedule.frontier i root) (prior : compareAt? i f a b = some p)
    (tie : cipTraceOutcome p = .eq) :
    let read := RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)
    ∃ v, comparison? i f a b read = some v ∧ score? i f a b read = some (scores v) ∧
      scores v ∈ molecularValues ∧ Determined read ⟨a,some f⟩ ⟨b,some f⟩ false v.1 ∧
        Determined read ⟨a,some f⟩ ⟨b,some f⟩ true v.2 := by
  intro read
  have inc := (RingRetainedChemicalTrace.compareAt?_source prior).1
  have arm (q : Site i) (adj : i.certified.LocalizedCarrierTreeAdjacent q.val f.val) :=
    arm_frontier listed (⟨q,some f⟩ : Arm i) ((i.certified.mem_localizedRerootNeighborFrames_iff _ _).mpr
      ⟨q.property,adj⟩) adj.1
  obtain ⟨x,l⟩ := arm a inc.2.2.1
  obtain ⟨y,r⟩ := arm b inc.2.2.2
  change arm? i read _ = some x at l
  change arm? i read _ = some y at r
  have left := arm_source l
  have right := arm_source r
  obtain ⟨v,actual⟩ := RingRetainedStereoDecision.decide_total left right
  obtain ⟨w,mirror⟩ := RingRetainedStereoDecision.decide_total left.reflect right.reflect
  change RingRetainedStereoDecision.decide? x.reflect y.reflect true = some w at mirror
  have values := both_values listed prior tie left right actual mirror
  have got : comparison? i f a b read = some (v,w) := by simp [comparison?,prior,tie,l,r,actual,mirror]
  exact ⟨(v,w),got,by simp [score?,got,values],values,determined left right actual,determined left.reflect right.reflect mirror⟩

/-- Evaluate an addressed pair directly from the original-root molecular
publications. Materialize the table once for the two ligand reads. -/
def scheduledComparison? (i : Input) (root : i.certified.Atom) (f a b : Site i) : Option (Result × Result) :=
  if f.val.root = root then
    let table := RingMolecularSchedule.publicationTable i root
    comparison? i f a b (RingNestedActivePair.masked f (RingActiveDistanceSchedule.snapshot table))
  else none

theorem scheduled_frontier {i : Input} {root : i.certified.Atom} {f a b : Site i} {p}
    (listed : f ∈ RingMolecularSchedule.frontier i root) (prior : compareAt? i f a b = some p)
    (tie : cipTraceOutcome p = .eq) :
    let read := RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)
    ∃ v, scheduledComparison? i root f a b = some v ∧ scores v ∈ molecularValues ∧
      Determined read ⟨a,some f⟩ ⟨b,some f⟩ false v.1 ∧ Determined read ⟨a,some f⟩ ⟨b,some f⟩ true v.2 := by
  obtain ⟨v,computed,_,values,l,r⟩ := frontier listed prior tie
  refine ⟨v,?_,values,l,r⟩
  simpa only [scheduledComparison?,(RingMolecularSchedule.mem_frontier.mp listed).1,if_true,RingMolecularSchedule.table_readback] using computed

end TetraStereo.Engine.RingGroupedStereo

assert_kernel_only TetraStereo.Engine.RingGroupedStereo.arm_cached
assert_kernel_only TetraStereo.Engine.RingGroupedStereo.arm_source
assert_kernel_only TetraStereo.Engine.RingGroupedStereo.arm_frontier

assert_kernel_only TetraStereo.Engine.RingGroupedStereo.frontier
assert_kernel_only TetraStereo.Engine.RingGroupedStereo.score_values

assert_kernel_only TetraStereo.Engine.RingGroupedStereo.tie_iff

assert_kernel_only TetraStereo.Engine.RingGroupedStereo.comparison_source

assert_kernel_only TetraStereo.Engine.RingGroupedStereo.scheduled_frontier

assert_kernel_only TetraStereo.Engine.RingGroupedStereo.single_before_dual
