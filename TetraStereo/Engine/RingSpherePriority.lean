import TetraStereo.Engine.RingGroupedStereo
import TetraStereo.Engine.RingSphereFastScore
import TetraStereo.Engine.RingSpherePopulation
import TetraStereo.Engine.RingProximalUnit
import TetraStereo.Engine.RingFrontierProfileShape

set_option autoImplicit false

namespace TetraStereo.Engine.RingSpherePriority
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingNestedActivePair (Reader Visit)
open RingRetainedChemicalTrace (compareAt?)
open RingSphereReadings (Word Profile unitRows lowerRows upperRows)

/-- The constitutional trace identifies two distinct directed occurrences at
this focus. Their unfiltered molecular spheres are read against the same
frozen original-root state. Both signed comparisons must reach a result. -/
structure Certificate (i : Input) (f a b : Site i) (read : Reader i) where
  trace : List CIPRuleDecision
  prior : compareAt? i f a b = some trace
  tied : cipTraceOutcome trace = .eq
  left : Profile
  right : Profile
  leftRead : RingSpherePopulation.profile? i read ⟨a,some f⟩ = some left
  rightRead : RingSpherePopulation.profile? i read ⟨b,some f⟩ = some right
  fullWidths : left.map List.length = right.map List.length
  queueWidths : (upperRows left false).map List.length = (upperRows right false).map List.length
  score : Int × Int
  actual : RingSphereReadings.score? left right false = some score.1
  reflected : RingSphereReadings.score? left right true = some score.2

def find? (i : Input) (f a b : Site i) (read : Reader i) : Option (Certificate i f a b read) := do
  let ⟨t,ht⟩ ← (compareAt? i f a b).attach
  if h : cipTraceOutcome t = .eq then
    let ⟨l,hl⟩ ← (RingSpherePopulation.profile? i read ⟨a,some f⟩).attach
    let ⟨r,hr⟩ ← (RingSpherePopulation.profile? i read ⟨b,some f⟩).attach
    if full : l.map List.length = r.map List.length then
      if queue : (upperRows l false).map List.length = (upperRows r false).map List.length then
        let ⟨x,hx⟩ ← (RingSphereReadings.fast? l r false).attach
        let ⟨y,hy⟩ ← (RingSphereReadings.fast? l r true).attach
        return ⟨t,ht,h,l,r,hl,hr,full,queue,(x,y),by simpa only [RingSphereReadings.score_fast] using hx,
          by simpa only [RingSphereReadings.score_fast] using hy⟩
    none
  else none

def score? (i : Input) (f a b : Site i) (read : Reader i) := (find? i f a b read).map Certificate.score

/-- Preserve earlier molecular comparisons and extend them on tied pairs. -/
def edge? (i : Input) (f a b : Site i) (read : Reader i) : Option (Int × Int) :=
  (RingProximalUnit.edge? i f a b read).orElse fun _ =>
    (score? i f a b read).orElse fun _ => RingGroupedStereo.score? i f a b read

theorem preserves {i f a b read k} (old : RingProximalUnit.edge? i f a b read = some k) :
    edge? i f a b read = some k := by simp [edge?,old]

/-- A previously unresolved edge on a scheduled frontier receives the signed
pair derived by the parent-group traversal, including a surviving tie. -/
theorem frontier_grouped {i : Input} {root : i.certified.Atom} {f a b : Site i} {p}
    (listed : f ∈ RingMolecularSchedule.frontier i root) (prior : compareAt? i f a b = some p)
    (tie : cipTraceOutcome p = .eq) :
    let read := RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)
    RingProximalUnit.edge? i f a b read = none → score? i f a b read = none →
      ∃ v, edge? i f a b read = some (RingGroupedStereo.scores v) ∧
        RingGroupedStereo.Determined read ⟨a,some f⟩ ⟨b,some f⟩ false v.1 ∧
        RingGroupedStereo.Determined read ⟨a,some f⟩ ⟨b,some f⟩ true v.2 := by
  intro read old miss
  obtain ⟨v,_,got,_,actual,reflected⟩ := RingGroupedStereo.frontier listed prior tie
  exact ⟨v,by simpa only [edge?,old,miss,Option.orElse_none] using got,actual,reflected⟩

theorem score_source {i f a b read k} (hit : score? i f a b read = some k) :
    ∃ c : Certificate i f a b read, c.score = k := by
  obtain ⟨c,_,hk⟩ := Option.map_eq_some_iff.mp hit
  exact ⟨c,hk⟩

private theorem upper_perm {a b : Profile} (p : List.Forall₂ List.Perm a b) (rev : Bool) :
    List.Forall₂ List.Perm (upperRows a rev) (upperRows b rev) := by
  cases p with
  | nil => exact .nil
  | cons head rest =>
    apply List.Forall₂.cons (head.map _)
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    exact rest.imp (fun _ _ h => (h.filter _).map _)

/-- Every independent full traversal on one arm supplies the three exact
observation streams used in the rule stages. -/
structure Streams (base alt : Profile) (rev : Bool) : Prop where
  units : Word (unitRows base rev) (unitRows alt rev).flatten
  uppers : Word (upperRows base rev) (upperRows alt rev).flatten
  lowers : Word (lowerRows base rev) (lowerRows alt rev).flatten

theorem streams_of_perm {base alt : Profile} (p : List.Forall₂ List.Perm base alt) (rev : Bool) :
    Streams base alt rev :=
  ⟨⟨_,RingSpherePopulation.project _ p,rfl⟩,⟨_,upper_perm p rev,rfl⟩,
    ⟨_,RingSpherePopulation.project _ p,rfl⟩⟩

theorem hierarchy_streams {i : Input} {q : Arm i} {read hs base}
    (valid : i.certified.LocalizedRerootCursorValid q) (h : RingSpherePopulation.Hierarchy i [q] hs)
    (ok : RingSpherePopulation.profile? i read q = some base) :
    ∃ alt, RingSpherePopulation.read? i read hs = some alt ∧ ∀ rev, Streams base alt rev := by
  obtain ⟨alt,issued,perm⟩ := RingSpherePopulation.every_hierarchy valid h ok
  exact ⟨alt,issued,streams_of_perm perm⟩

theorem Certificate.stage_score {i f a b read} (c : Certificate i f a b read) (rev : Bool)
    {au bu ax bx al bl ar br as' bs'}
    (u : Streams c.left au rev) (v : Streams c.right bu rev)
    (x : Streams c.left ax rev) (y : Streams c.right bx rev)
    (l : Streams c.left al rev) (r : Streams c.right bl rev)
    (xr : Streams c.left ar rev) (yr : Streams c.right br rev)
    (xs : Streams c.left as' rev) (ys : Streams c.right bs' rev) :
    RingSphereReadings.stages? (unitRows au rev).flatten (unitRows bu rev).flatten
      (upperRows ax rev).flatten (upperRows bx rev).flatten (lowerRows al rev).flatten (lowerRows bl rev).flatten
      (upperRows ar rev).flatten (upperRows br rev).flatten (upperRows as' rev).flatten (upperRows bs' rev).flatten =
        some (if rev then c.score.2 else c.score.1) := by
  have hit : RingSphereReadings.score? c.left c.right rev = some (if rev then c.score.2 else c.score.1) := by
    cases rev <;> first | exact c.actual | exact c.reflected
  exact RingSphereReadings.independent hit u.units v.units x.uppers y.uppers l.lowers r.lowers
    xr.uppers yr.uppers xs.uppers ys.uppers

/-- If the older retained ordering also materializes both arms, the independent
comparison agrees with its whole staged decision on each geometry. -/
theorem Certificate.agrees {i f a b read} (c : Certificate i f a b read) {n pa pb}
    (left : RingNestedActivePair.retainedLevels? i read n [⟨a,some f⟩] = some pa)
    (right : RingNestedActivePair.retainedLevels? i read n [⟨b,some f⟩] = some pb) (rev : Bool) :
    RingNestedActivePair.decide? pa pb rev = some (if rev then c.score.2 else c.score.1) := by
  have inc := (RingRetainedChemicalTrace.compareAt?_source c.prior).1
  have lv : i.certified.LocalizedRerootCursorValid (⟨a,some f⟩ : Arm i) :=
    (i.certified.mem_localizedRerootNeighborFrames_iff _ _).mpr ⟨a.property,inc.2.2.1⟩
  have rv : i.certified.LocalizedRerootCursorValid (⟨b,some f⟩ : Arm i) :=
    (i.certified.mem_localizedRerootNeighborFrames_iff _ _).mpr ⟨b.property,inc.2.2.2⟩
  have x := streams_of_perm (RingSpherePopulation.retained_perm lv c.leftRead left) rev
  have y := streams_of_perm (RingSpherePopulation.retained_perm rv c.rightRead right) rev
  have hit := c.stage_score rev x y x y x y x y x y
  have shape := RingAtomicProfileShape.tie_shape c.prior c.tied left right
  simpa only [RingNestedActivePair.decide?,shape,beq_self_eq_true,guard_true,pure_bind,
    RingSphereReadings.stages?,RingSphereReadings.upper_flatten,unitRows,lowerRows,
    RingNestedActivePair.unitWord,List.map_flatten] using hit

/-- At a first unresolved publication, every actual directed component on the
same carrier has a complete frozen profile even when sibling keys collide. -/
theorem frontier_profile {i : Input} {root : i.certified.Atom} {f : Site i}
    (listed : f ∈ RingMolecularSchedule.frontier i root) (q : Arm i)
    (on : q.occurrence.val.root = f.val.root) (valid : i.certified.LocalizedRerootCursorValid q) :
    ∃ p, RingSpherePopulation.profile? i (RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)) q =
      some p := by
  apply RingSpherePopulation.profile?_of_ready valid
  intro t ht
  exact RingFrontierProfileShape.frontier_observation listed t ((RingFrontierProfileShape.reaches_root ht).trans on)

end TetraStereo.Engine.RingSpherePriority

assert_kernel_only TetraStereo.Engine.RingSpherePriority.preserves
assert_kernel_only TetraStereo.Engine.RingSpherePriority.score_source
assert_kernel_only TetraStereo.Engine.RingSpherePriority.hierarchy_streams
assert_kernel_only TetraStereo.Engine.RingSpherePriority.Certificate.stage_score
assert_kernel_only TetraStereo.Engine.RingSpherePriority.Certificate.agrees
assert_kernel_only TetraStereo.Engine.RingSpherePriority.frontier_profile

assert_kernel_only TetraStereo.Engine.RingSpherePriority.frontier_grouped
