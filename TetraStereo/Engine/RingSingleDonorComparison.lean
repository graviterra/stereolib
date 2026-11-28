import TetraStereo.Engine.RingSpherePopulation
import TetraStereo.Engine.RingChemicalGraphProof
import TetraStereo.Engine.RingSplitLigandTie
import TetraStereo.Engine.RingLigandFirstDifference

/-! A single uppercase donor of each hand separates two otherwise matched
retained ligand arms at Rule 5, independently of the active Rule 6 marks. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingSingleDonorComparison
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingFullPathPairs (Oracle FullVisit handAt likeAt)
open RingRetainedChemicalTrace (Word)
open RingFullPathEligibility (Key Reads)
open RingFullPathTrialReadings (trialKey bitWord)
open RingGeometryExchange (Carrier Frozen)
open RingSplitLigandTie (markingReader)
open RingSpherePopulation (Hierarchy full children)
open private next_perm from TetraStereo.Engine.RingSpherePopulation
open private normalized_unit normalized_lower from TetraStereo.Engine.RingSplitLigandTie
attribute [local instance] lexOrd

/-- The unsorted complete census keeps occurrence multiplicity. Only actual
uppercase publications on the unreflected geometry contribute a hand. -/
def donors {i : Input} (r : Reader i) (q : Arm i) : List RS :=
  (full i [q]).flatten.filterMap (handAt i r false)

private theorem projected {i : Input} (o : Oracle i) (bit : Arm i → Option Bool)
    {p : FullVisit i} {ys : List (FullVisit i)} (ex : o.Expansion bit p ys) :
    ys.map FullVisit.cursor = children i p.cursor := by
  change List.Forall₂ (o.Child bit p) (children i p.cursor) ys at ex
  generalize children i p.cursor = cs at ex ⊢
  induction ex with
  | nil => rfl
  | cons hd _ ih => obtain ⟨_,_,rfl⟩ := hd; simp [ih]

private theorem blocks {i : Input} (o : Oracle i) (bit : Arm i → Option Bool)
    {xs : List (FullVisit i)} {rows} (h : List.Forall₂ (o.Expansion bit) xs rows) :
    rows.flatten.map FullVisit.cursor = (xs.map FullVisit.cursor).flatMap (children i) := by
  induction h with
  | nil => rfl
  | cons e _ ih => simp only [List.flatten_cons,List.map_append,List.map_cons,List.flatMap_cons,
      projected o bit e,ih]

/-- A complete legal ranked trace contains exactly the native unsorted
occurrences, even when the ranking permutes children of different parents. -/
theorem census_perm {i : Input} {o : Oracle i} {bit : Arm i → Option Bool}
    {xs out : List (FullVisit i)} (walk : o.Walk bit xs out) {front hs}
    (same : (xs.map FullVisit.cursor).Perm front) (h : Hierarchy i front hs) :
    (out.map FullVisit.cursor).Perm hs.flatten := by
  induction walk generalizing front hs with
  | stop =>
    obtain rfl := same.symm.eq_nil
    cases h
    exact .refl _
  | @sphere v vs groups sorted tail ex legal walk ih =>
    cases h with
    | stop => have no := same.eq_nil; simp at no
    | @layer c cs actual rest pars hier =>
      have step := (legal.perm.map FullVisit.cursor).trans (List.Perm.of_eq (blocks _ _ ex))
      have matchNext := step.trans ((same.flatMap_right (children i)).trans (next_perm pars).symm)
      simpa only [List.map_append,List.flatten_cons] using same.append (ih matchNext hier)

private theorem full_on {i : Input} (q : Arm i) {c : Arm i}
    (valid : i.certified.LocalizedRerootCursorValid q) (member : c ∈ (full i [q]).flatten) :
    c.occurrence.val.root = q.occurrence.val.root := by
  obtain ⟨row,hrow,hc⟩ := List.mem_flatten.mp member
  obtain ⟨d,hd⟩ := List.mem_iff_getElem?.mp hrow
  have level := RingSpherePopulation.layer_at (RingSpherePopulation.full_complete (i := i) (qs := [q]) (by simpa using valid)) d
  rw [hd] at level
  have distance := (RingSpherePopulation.mem_distance d [q] c).mp (level.mem_iff.mp hc)
  obtain ⟨_,hs,reach⟩ := distance
  obtain rfl := List.mem_singleton.mp hs
  exact (reach.root_and_budget valid).1

def onGeometry (rev : Bool) (h : RS) := if rev then h.swap else h

private theorem reflected {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (q : Arm i) (on : q.occurrence.val.root = f.val.root) (rev : Bool) :
    handAt i r rev q = (handAt i r false q).map (onGeometry rev) := by
  obtain ⟨v,seen,consistent,_⟩ := ready q on
  rcases v with _ | ⟨(_|_),(_|_)⟩ <;> cases rev <;>
    simp_all [handAt,RingNestedActivePair.consistent,RingNestedActivePair.upper,onGeometry]

private theorem census_bits {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (rev : Bool) (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q)
    (on : q.occurrence.val.root = f.val.root) (seed : RS) :
    (full i [q]).flatten.filterMap (likeAt i r rev seed) =
      (donors r q).map (fun h => onGeometry rev h == seed) := by
  rw [donors,List.map_filterMap]
  apply List.filterMap_congr
  intro c mem
  simp only [likeAt,reflected ready c ((full_on q valid mem).trans on) rev,Option.map_map,Function.comp_def]

/-- A ranked reading at any priority stage and with either reference seed
observes a permutation of the independent census of original hands. -/
theorem seed_population {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (rev : Bool) (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q)
    (on : q.occurrence.val.root = f.val.root) (seed : RS) {o : Oracle i} {w : List Bool}
    (source : o.Source (likeAt i r rev seed) q w) :
    w.Perm ((donors r q).map (fun h => onGeometry rev h == seed)) := by
  obtain ⟨out,walk,rfl⟩ := source
  have pop := census_perm walk (List.Perm.refl [q]) (RingSpherePopulation.full_complete (i := i) (qs := [q]) (by simpa using valid))
  rw [←census_bits ready rev q valid on seed]
  simpa only [List.filterMap_map,Function.comp_def] using pop.filterMap (likeAt i r rev seed)

private theorem unsigned {i j : Input} {r : Reader i} {s : Reader j} {rev} {a : Arm i} {b : Arm j}
    (c : Carrier i j) (dom : c.domain a) (dest : c.image a = b)
    (same : Frozen c (markingReader r) (markingReader s)) {x y : Key}
    (l : Reads i r rev a x) (p : Reads j s rev b y) :
    x.throughFourA = y.throughFourA ∧ x.fourC = y.fourC := by
  obtain ⟨u,lo,_,_,_,du,dl,_,_,_,rfl⟩ := l
  obtain ⟨v,mo,_,_,_,dv,dm,_,_,_,rfl⟩ := p
  have h := c.unit same dom (normalized_unit du) (dest.symm ▸ normalized_unit dv)
  have k := c.refinement same [.lowercase] a dom _ _ (normalized_lower dl) (dest.symm ▸ normalized_lower dm)
  exact ⟨congrArg RingStereoSiblingPass.Branch.deep h,congrArg RingStereoSiblingPass.Branch.word k⟩

private theorem one {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (rev : Bool) (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q)
    (on : q.occurrence.val.root = f.val.root) {key : Key} (read : Reads i r rev q key)
    (h : RS) (only : donors r q = [h]) :
    key.bestFourB = [true] ∧ key.fixedR = [onGeometry rev h == .R] := by
  obtain ⟨u,l,ar,as',fr,_,_,sr,ss,sf,rfl⟩ := read
  have report (s : RS) {o : Oracle i} {w} (src : o.Source (likeAt i r rev s) q w) :
      w = [onGeometry rev h == s] := by
    have perm := seed_population ready rev q valid on s src
    rw [only,List.map_singleton] at perm
    exact List.perm_singleton.mp perm
  have left := report .R sr
  have right := report .S ss
  have fixed := report .R sf
  rw [left,right,fixed]
  constructor
  · change max _ _ = [true]
    cases rev <;> cases h <;> rfl
  · rfl

open RingLigandFirstDifference (Words Decomposes directions stages First markWord?)

def outcome (h : RS) := if h = .R then Ordering.gt else Ordering.lt

private theorem first_five {ka kb : Key} {m n : Word} {x y : Words}
    (dx : Decomposes ka m x) (dy : Decomposes kb n y)
    (prior : ka.throughFourA = kb.throughFourA) (b : ka.bestFourB = kb.bestFourB)
    (lower : ka.fourC = kb.fourC) (h : RS) (la : ka.fixedR = [h == .R])
    (lb : kb.fixedR = [h.swap == .R]) :
    First (directions x y) stages .rule5 (outcome h) := by
  rw [dx.through,dy.through] at prior
  simp only [List.cons.injEq,and_true] at prior
  have fb := dx.fourB.symm.trans ((congrArg bitWord b).trans dy.fourB)
  have fc := dx.fourC.symm.trans (lower.trans dy.fourC)
  have d5 : directions x y .rule5 = outcome h := by
    change compare x.five y.five = _
    rw [←dx.five,←dy.five,la,lb]
    cases h <;> decide
  apply First.later (by simp [directions,Words.at,prior.1])
  apply First.later (by simp [directions,Words.at,prior.2.1])
  apply First.later (by simp [directions,Words.at,prior.2.2.1])
  apply First.later (by simp [directions,Words.at,prior.2.2.2])
  apply First.later (by simp [directions,Words.at,fb])
  apply First.later (by simp [directions,Words.at,fc])
  rw [←d5]
  exact First.here (by rw [d5]; cases h <;> decide)

/-- Successful native key and mark lookups, together with the independently
decomposed priority rows and the first deciding rule of the actual trial. -/
def DecidesAtFive {i : Input} (r : Reader i) (a b : Arm i) (rev : Bool)
    (active : Option Nat) (result : Ordering) : Prop :=
    ∃ ka kb : Key, ∃ m n : Word, ∃ x y : Words,
      RingFullPathEligibility.key? i r rev a = some ka ∧ RingFullPathEligibility.key? i r rev b = some kb ∧
      markWord? r active a = some m ∧ markWord? r active b = some n ∧
      Decomposes ka m x ∧ Decomposes kb n y ∧
      First (directions x y) stages .rule5 result ∧
      compare (trialKey ka m) (trialKey kb n) = result

/-- Every native marking trial and both readings have Rule 5 as their first
deciding stage. One unsigned correspondence and the original donor inventories
suffice for all reflected and marked comparisons. -/
theorem opposite {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (a b : Arm i) (va : i.certified.LocalizedRerootCursorValid a) (vb : i.certified.LocalizedRerootCursorValid b)
    (ra : a.occurrence.val.root = f.val.root) (rb : b.occurrence.val.root = f.val.root)
    (c : Carrier i i) (dom : c.domain a) (dest : c.image a = b)
    (same : Frozen c (markingReader r) (markingReader r))
    (h : RS) (left : donors r a = [h]) (right : donors r b = [h.swap])
    (rev : Bool) (active : Option Nat) :
    DecidesAtFive r a b rev active (outcome (onGeometry rev h)) := by
  obtain ⟨ka,kb,m,n,x,y,ha,hb,hm,hn,dx,dy,scan⟩ :=
    RingLigandFirstDifference.all_active_arms ready rev a b va vb ra rb active
  have accepted (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q)
      (on : q.occurrence.val.root = f.val.root) (k : Key)
      (hit : RingFullPathEligibility.key? i r rev q = some k) : Reads i r rev q k := by
    obtain ⟨key,eqn,only⟩ := RingFullPathEligibility.key_exact ready rev q valid on
    exact (only k).mpr (Option.some.inj (hit.symm.trans eqn))
  have da := accepted a va ra ka ha
  have db := accepted b vb rb kb hb
  obtain ⟨early,lo⟩ := unsigned c dom dest same da db
  obtain ⟨ba,fa⟩ := one ready rev a va ra da h left
  obtain ⟨bb,fb⟩ := one ready rev b vb rb db h.swap right
  have commute : onGeometry rev h.swap = (onGeometry rev h).swap := by cases rev <;> rfl
  rw [commute] at fb
  have first := first_five dx dy early (ba.trans bb.symm) lo _ fa fb
  exact ⟨ka,kb,m,n,x,y,ha,hb,hm,hn,dx,dy,first,scan.trans first.scan_value⟩

/-- Specialization to the actual frozen public state of any coordinate-admitted
input. The unsigned carrier is only needed on its witnessed subtree. -/
theorem public_opposite {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (f : Site i) (a b : Arm i) (va : i.certified.LocalizedRerootCursorValid a)
    (vb : i.certified.LocalizedRerootCursorValid b)
    (ra : a.occurrence.val.root = f.val.root) (rb : b.occurrence.val.root = f.val.root)
    (c : Carrier i i) (dom : c.domain a) (dest : c.image a = b) (h : RS) :
    let r := RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state i) f
    Frozen c (markingReader r) (markingReader r) → donors r a = [h] → donors r b = [h.swap] →
      ∀ rev active, DecidesAtFive r a b rev active (outcome (onGeometry rev h)) := by
  dsimp only
  intro same left right
  exact opposite (RingChemicalGraphProof.ready geom f) a b va vb ra rb c dom dest same h left right

private theorem no_donor {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (rev : Bool) (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q)
    (on : q.occurrence.val.root = f.val.root) {key : Key} (read : Reads i r rev q key)
    (none : donors r q = []) : key.bestFourB = [] ∧ key.fixedR = [] := by
  obtain ⟨_,_,ar,as',fr,_,_,sr,ss,sf,rfl⟩ := read
  have empty (s : RS) {o : Oracle i} {w} (src : o.Source (likeAt i r rev s) q w) : w = [] := by
    have p := seed_population ready rev q valid on s src
    rw [none,List.map_nil] at p
    exact p.eq_nil
  rw [empty .R sr,empty .S ss,empty .R sf]
  exact ⟨rfl,rfl⟩

/-- With no uppercase donors on either side the ordinary native keys tie.
The active mark can still distinguish those arms on a later trial. -/
theorem silent {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (a b : Arm i) (va : i.certified.LocalizedRerootCursorValid a) (vb : i.certified.LocalizedRerootCursorValid b)
    (ra : a.occurrence.val.root = f.val.root) (rb : b.occurrence.val.root = f.val.root)
    (c : Carrier i i) (dom : c.domain a) (dest : c.image a = b)
    (same : Frozen c (markingReader r) (markingReader r))
    (left : donors r a = []) (right : donors r b = []) (rev : Bool) :
    ∃ k, RingFullPathEligibility.key? i r rev a = some k ∧ RingFullPathEligibility.key? i r rev b = some k := by
  obtain ⟨x,hx,ex⟩ := RingFullPathEligibility.key_exact ready rev a va ra
  obtain ⟨y,hy,ey⟩ := RingFullPathEligibility.key_exact ready rev b vb rb
  have dx := (ex x).mpr rfl
  have dy := (ey y).mpr rfl
  obtain ⟨ua,lo⟩ := unsigned c dom dest same dx dy
  obtain ⟨ba,fa⟩ := no_donor ready rev a va ra dx left
  obtain ⟨bb,fb⟩ := no_donor ready rev b vb rb dy right
  have eq : x = y := by cases x; cases y; simp_all
  exact ⟨y,eq ▸ hx,hy⟩

end TetraStereo.Engine.RingSingleDonorComparison

assert_kernel_only TetraStereo.Engine.RingSingleDonorComparison.opposite
assert_kernel_only TetraStereo.Engine.RingSingleDonorComparison.silent
assert_kernel_only TetraStereo.Engine.RingSingleDonorComparison.public_opposite
