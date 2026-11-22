import TetraStereo.Engine.RingSpherePriority

set_option autoImplicit false

namespace TetraStereo.Engine.RingSphereCoverage
open OneCenter CertifiedLocalizedCIPInput RingSphereReadings
open RingActivePairs (Arm Site)
open LocalizedChemicalRing (Input)

/-- Independent quantification over every within-distance order of the two
observed words. The comparison is the corresponding source-stage operation. -/
def Common {α : Type} (f : List α → List α → Option Int) (a b : List (List α)) (k : Int) : Prop :=
  ∀ x y, Word a x → Word b y → f x y = some k

inductive Decision (a b : Profile) (rev : Bool) : Int → Prop where
  | hand {k} (strict : k ≠ 0)
      (first : Common RingSeededPairs.localSign? (upperRows a rev) (upperRows b rev) k) : Decision a b rev k
  | lower {k} (strict : k ≠ 0)
      (first : Common RingSeededPairs.localSign? (upperRows a rev) (upperRows b rev) 0)
      (low : Common ord (lowerRows a rev) (lowerRows b rev) k) : Decision a b rev k
  | fixed {r s}
      (first : Common RingSeededPairs.localSign? (upperRows a rev) (upperRows b rev) 0)
      (low : Common ord (lowerRows a rev) (lowerRows b rev) 0)
      (plus : Common (RingSeededPairs.listSign? .R) (upperRows a rev) (upperRows b rev) r)
      (minus : Common (RingSeededPairs.listSign? .S) (upperRows a rev) (upperRows b rev) s) :
      Decision a b rev (CentresRing.PairList.combine r s)

def Agrees (a b : Profile) (rev : Bool) (k : Int) : Prop :=
  Common ord (unitRows a rev) (unitRows b rev) 0 ∧
    oneReference (upperRows a rev) = true ∧ oneReference (upperRows b rev) = true ∧ Decision a b rev k

/-- The converse is an existence result: order-independent stage readings
force the evaluator to succeed even if the retained sibling sorter fails. -/
theorem score_iff (a b : Profile) (rev : Bool) (k : Int) :
    RingSphereReadings.score? a b rev = some k ↔ Agrees a b rev k := by
  constructor
  · intro hit
    by_cases units : across? ord (unitRows a rev) (unitRows b rev) = some 0
    · by_cases ok : (oneReference (upperRows a rev) && oneReference (upperRows b rev)) = true
      · have both := ok
        rw [Bool.and_eq_true] at both
        refine ⟨across_iff.mp units,both.1,both.2,?_⟩
        simp only [RingSphereReadings.score?,units,beq_self_eq_true,ok,guard_true,pure_bind] at hit
        obtain ⟨first,hf,more⟩ := Option.bind_eq_some_iff.mp hit
        by_cases strict : first ≠ 0
        · obtain rfl : first = k := Option.some.inj (by simpa only [if_pos strict] using more)
          exact .hand strict (across_iff.mp hf)
        · obtain rfl := not_ne_iff.mp strict
          simp only [ne_eq,not_true_eq_false,if_false] at more
          obtain ⟨low,hl,out⟩ := Option.bind_eq_some_iff.mp more
          by_cases decisive : low ≠ 0
          · obtain rfl : low = k := Option.some.inj (by simpa only [if_pos decisive] using out)
            exact .lower decisive (across_iff.mp hf) (across_iff.mp hl)
          · obtain rfl := not_ne_iff.mp decisive
            simp only [not_true_eq_false,if_false] at out
            obtain ⟨r,hr,rest⟩ := Option.bind_eq_some_iff.mp out
            obtain ⟨s,hs,eqn⟩ := Option.bind_eq_some_iff.mp rest
            obtain rfl := Option.some.inj eqn
            exact .fixed (across_iff.mp hf) (across_iff.mp hl) (across_iff.mp hr) (across_iff.mp hs)
      · simp [RingSphereReadings.score?,units,ok] at hit
    · simp [RingSphereReadings.score?,units] at hit
  · rintro ⟨u,x,y,h⟩
    have units := across_iff.mpr u
    cases h with
    | hand strict first => simp [RingSphereReadings.score?,units,x,y,across_iff.mpr first,strict]
    | lower strict first low => simp [RingSphereReadings.score?,units,x,y,across_iff.mpr first,across_iff.mpr low,strict]
    | fixed first low plus minus =>
      simp [RingSphereReadings.score?,units,x,y,across_iff.mpr first,across_iff.mpr low,across_iff.mpr plus,across_iff.mpr minus]

/-- At a tied molecular comparison and known profiles, the independent stage
criterion is both necessary and sufficient for this score extension. -/
theorem molecular_iff {i : Input} {f a b : Site i} {read t l r} {k : Int × Int}
    (prior : RingRetainedChemicalTrace.compareAt? i f a b = some t) (tie : cipTraceOutcome t = .eq)
    (left : RingSpherePopulation.profile? i read ⟨a,some f⟩ = some l)
    (right : RingSpherePopulation.profile? i read ⟨b,some f⟩ = some r) :
    RingSpherePriority.score? i f a b read = some k ↔ l.map List.length = r.map List.length ∧
      (upperRows l false).map List.length = (upperRows r false).map List.length ∧
      Agrees l r false k.1 ∧ Agrees l r true k.2 := by
  constructor
  · intro hit
    obtain ⟨c,eqn⟩ := RingSpherePriority.score_source hit
    obtain rfl : c.left = l := Option.some.inj (c.leftRead.symm.trans left)
    obtain rfl : c.right = r := Option.some.inj (c.rightRead.symm.trans right)
    subst k
    exact ⟨c.fullWidths,c.queueWidths,(score_iff ..).mp c.actual,(score_iff ..).mp c.reflected⟩
  · rintro ⟨fw,qw,actual,mirror⟩
    have orig := (score_iff ..).mpr actual
    have reflected := (score_iff ..).mpr mirror
    rw [score_fast] at orig reflected
    simp only [RingSpherePriority.score?,RingSpherePriority.find?,Option.attach_eq_some _ ⟨_,prior⟩,
      Option.bind_eq_bind,Option.bind_some,tie,dite_true,Option.attach_eq_some _ ⟨_,left⟩,
      Option.attach_eq_some _ ⟨_,right⟩,fw,qw,Option.attach_eq_some _ ⟨_,orig⟩,
      Option.attach_eq_some _ ⟨_,reflected⟩,Option.pure_def,Option.map_some]

/-- At the first unresolved publication the two profiles always exist. The
remaining criterion for the extension refers only to their populations,
reference hands, and independent ordering of observed values at each stage. -/
theorem frontier {i : Input} {root : i.certified.Atom} {f a b : Site i} {t}
    (listed : f ∈ RingMolecularSchedule.frontier i root)
    (prior : RingRetainedChemicalTrace.compareAt? i f a b = some t) (tie : cipTraceOutcome t = .eq) :
    let read := RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)
    ∃ l r, RingSpherePopulation.profile? i read ⟨a,some f⟩ = some l ∧
      RingSpherePopulation.profile? i read ⟨b,some f⟩ = some r ∧ ∀ k : Int × Int,
      RingSpherePriority.score? i f a b read = some k ↔ l.map List.length = r.map List.length ∧
        (upperRows l false).map List.length = (upperRows r false).map List.length ∧
        Agrees l r false k.1 ∧ Agrees l r true k.2 := by
  dsimp only
  have inc := (RingRetainedChemicalTrace.compareAt?_source prior).1
  have profile (q : Site i) (adj : i.certified.LocalizedCarrierTreeAdjacent q.val f.val) :=
    RingSpherePriority.frontier_profile listed (⟨q,some f⟩ : Arm i) adj.1
      ((i.certified.mem_localizedRerootNeighborFrames_iff _ _).mpr ⟨q.property,adj⟩)
  obtain ⟨l,hl⟩ := profile a inc.2.2.1
  obtain ⟨r,hr⟩ := profile b inc.2.2.2
  exact ⟨l,r,hl,hr,fun _ => molecular_iff prior tie hl hr⟩

end TetraStereo.Engine.RingSphereCoverage

assert_kernel_only TetraStereo.Engine.RingSphereCoverage.score_iff
assert_kernel_only TetraStereo.Engine.RingSphereCoverage.molecular_iff

assert_kernel_only TetraStereo.Engine.RingSphereCoverage.frontier
