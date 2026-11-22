import TetraStereo.Engine.RingRetainedReferenceGroup

set_option autoImplicit false

namespace TetraStereo.Engine.RingRetainedStereoDecision
open OneCenter CertifiedLocalizedCIPInput RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingRetainedReferenceGroup (Hit Listing references)
open RingRetainedStereoRefinement (Observation priority Derives bits pairSign)

/-- Readings at one ligand on one geometry. Rule 4c compares lowercase units
at descendants, where an unseeded Rule 4b has no local preference. The two
fixed Rule 5 passes include the complete Rule 4c priorities. -/
structure ArmProfile where
  unit : Branch
  hits : List Hit
  localR : Branch
  localS : Branch
  lower : Branch
  fixedR : Branch
  fixedS : Branch
  deriving DecidableEq, Repr

def ArmProfile.localPair (p : ArmProfile) : RS → Branch
  | .R => p.localR | .S => p.localS

def ArmProfile.fixedPair (p : ArmProfile) : RS → Branch
  | .R => p.fixedR | .S => p.fixedS

def ArmProfile.reflect (p : ArmProfile) : ArmProfile :=
  { p with localR := p.localS, localS := p.localR, fixedR := p.fixedS, fixedS := p.fixedR }

structure Reads (i : Input) (read : Reader i) (rev : Bool) (q : Arm i) (p : ArmProfile) : Prop where
  unit : Derives i read rev [] q p.unit
  hits : Listing i read q p.hits
  paired : ∀ s, Derives i read rev [.pairing s] q (p.localPair s)
  lower : Derives i read rev [.lowercase] q p.lower
  fixed : ∀ s, Derives i read rev [.pairing s,.lowercase] q (p.fixedPair s)

def profile? (i : Input) (read : Reader i) (rev : Bool) (q : Arm i) : Option ArmProfile := do
  return ⟨← priority i read rev [] q,← RingRetainedReferenceGroup.hits? i read q,
    ← priority i read rev [.pairing .R] q,← priority i read rev [.pairing .S] q,
    ← priority i read rev [.lowercase] q,
    ← priority i read rev [.pairing .R,.lowercase] q,← priority i read rev [.pairing .S,.lowercase] q⟩

theorem Reads.unique {i read rev q p t} (a : Reads i read rev q p) (b : Reads i read rev q t) : p = t := by
  cases p; cases t
  congr 1
  · exact RingRetainedStereoRefinement.unique _ _ _ _ a.unit b.unit
  · exact a.hits.unique b.hits
  · exact RingRetainedStereoRefinement.unique _ _ _ _ (a.paired .R) (b.paired .R)
  · exact RingRetainedStereoRefinement.unique _ _ _ _ (a.paired .S) (b.paired .S)
  · exact RingRetainedStereoRefinement.unique _ _ _ _ a.lower b.lower
  · exact RingRetainedStereoRefinement.unique _ _ _ _ (a.fixed .R) (b.fixed .R)
  · exact RingRetainedStereoRefinement.unique _ _ _ _ (a.fixed .S) (b.fixed .S)

theorem Reads.reflect {i read rev q p} (a : Reads i read rev q p) : Reads i read (!rev) q p.reflect :=
  ⟨RingRetainedStereoRefinement.mirror [] q _ a.unit,a.hits,fun s => by
    cases s <;> first | exact RingRetainedStereoRefinement.mirror [.pairing .S] q _ (a.paired .S)
                      | exact RingRetainedStereoRefinement.mirror [.pairing .R] q _ (a.paired .R),
    RingRetainedStereoRefinement.mirror [.lowercase] q _ a.lower,fun s => by
    cases s <;> first | exact RingRetainedStereoRefinement.mirror [.pairing .S,.lowercase] q _ (a.fixed .S)
                      | exact RingRetainedStereoRefinement.mirror [.pairing .R,.lowercase] q _ (a.fixed .R)⟩

theorem frontier_profile {i : Input} {root : i.certified.Atom} {f : Site i}
    (listed : f ∈ RingMolecularSchedule.frontier i root) (rev : Bool) (q : Arm i)
    (valid : i.certified.LocalizedRerootCursorValid q) (on : q.occurrence.val.root = f.val.root) :
    let read := RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)
    ∃ p, profile? i read rev q = some p ∧ Reads i read rev q p := by
  intro read
  have atStage (stages : List Observation) := RingRetainedStereoRefinement.frontier listed rev stages q valid on
  obtain ⟨u,hu,su⟩ := atStage []
  obtain ⟨hits,hh,sh⟩ := RingRetainedReferenceGroup.frontier listed q valid on
  obtain ⟨ar,ha,sa⟩ := atStage [.pairing .R]
  obtain ⟨as',hb,sb⟩ := atStage [.pairing .S]
  obtain ⟨lo,hl,sl⟩ := atStage [.lowercase]
  obtain ⟨fr,hp,sp⟩ := atStage [.pairing .R,.lowercase]
  obtain ⟨fs,hn,sn⟩ := atStage [.pairing .S,.lowercase]
  let p : ArmProfile := ⟨u,hits,ar,as',lo,fr,fs⟩
  refine ⟨p,?_,(su _).mpr rfl,sh,?_,(sl _).mpr rfl,?_⟩
  · dsimp only [read]
    simp only [profile?,hu,hh,ha,hb,hl,hp,hn,Option.bind_eq_bind,Option.bind_some,Option.pure_def,p]
  · rintro (_|_) <;> first | exact (sa _).mpr rfl | exact (sb _).mpr rfl
  · rintro (_|_) <;> first | exact (sp _).mpr rfl | exact (sn _).mpr rfl

/-- Keep the like/unlike bit at each uppercase position in the through-4a
traversal. The artificial seed head agrees between the two compared lists. -/
def accepted (unit paired : Branch) : List Bool :=
  (unit.stream.zip (bits paired.stream)).filterMap fun (u,b) =>
    if u = 2 then some b else none

def ArmProfile.bestPair (p : ArmProfile) : List Bool :=
  max (accepted p.unit p.localR) (accepted p.unit p.localS)

/-- IUPAC P-92.5.2.1(c)(i) ranks one reference above two before pair-list
comparison. Subcriterion (ii) applies with equal reference counts. Two
dual-reference arms each contribute their greater complete list. -/
def fourB? (x y : ArmProfile) (rev : Bool) : Option Int :=
  match references x.hits rev, references y.hits rev with
  | [],[] => some 0
  | [s],[t] => some (pairSign (x.localPair s) (y.localPair t))
  | [_],[_,_] => some 1
  | [_,_],[_] => some (-1)
  | [_,_],[_,_] => some (RingSeededPairs.compareBits x.bestPair y.bestPair)
  | _,_ => none

private theorem ref_occupancy {i read rev a b x y}
    (left : Reads i read rev a x) (right : Reads i read rev b y) (tie : x.unit.word = y.unit.word) :
    references x.hits rev = [] ↔ references y.hits rev = [] := by
  have actual {q p} (r : Reads i read rev q p) : RingRetainedUnitPass.Reading i read false q p.unit := by
    cases rev
    · exact r.unit
    · exact r.reflect.unit
  rw [RingRetainedReferenceGroup.references_empty,RingRetainedReferenceGroup.references_empty,
      left.hits.empty_iff (actual left),right.hits.empty_iff (actual right),tie]

theorem fourB_total {i read rev a b x y}
    (left : Reads i read rev a x) (right : Reads i read rev b y) (tie : x.unit.word = y.unit.word) :
    ∃ k, fourB? x y rev = some k := by
  have occ := ref_occupancy left right tie
  rcases RingRetainedReferenceGroup.references_cases x.hits rev with lx | ⟨s,lx⟩ | lx <;>
    rcases RingRetainedReferenceGroup.references_cases y.hits rev with ry | ⟨t,ry⟩ | ry <;>
    simp_all [fourB?]

def seedSign (x y : ArmProfile) (s : RS) : Int :=
  RingSeededPairs.compareBits (accepted x.unit (x.fixedPair s)) (accepted y.unit (y.fixedPair s))

inductive Rule where
  | unit | likePair | lower | fixedPair
  deriving Repr, DecidableEq

structure Result where
  rule : Option Rule
  score : Int
  deriving Repr, DecidableEq

def fixedResult (r s : Int) : Result :=
  let k := CentresRing.PairList.combine r s
  ⟨if k = 0 then none else some .fixedPair,k⟩

/-- Only a zero proceeds to the next rule. A strict fixed-reference comparison
retains the magnitude used by the casing calculation. -/
def decide? (x y : ArmProfile) (rev : Bool) : Option Result := do
  let unit := RingRetainedUnitPass.signed x.unit y.unit
  if unit ≠ 0 then return ⟨some .unit,unit⟩
  let localScore ← fourB? x y rev
  if localScore ≠ 0 then return ⟨some .likePair,localScore⟩
  let lower := RingRetainedUnitPass.signed x.lower y.lower
  if lower ≠ 0 then return ⟨some .lower,lower⟩
  return fixedResult (seedSign x y .R) (seedSign x y .S)

theorem decide_total {i read rev a b x y} (left : Reads i read rev a x) (right : Reads i read rev b y) :
    ∃ v, decide? x y rev = some v := by
  by_cases zero : RingRetainedUnitPass.signed x.unit y.unit = 0
  · obtain ⟨k,hk⟩ := fourB_total left right ((RingRetainedUnitPass.signed_zero_iff ..).mp zero)
    by_cases k = 0 <;> by_cases RingRetainedUnitPass.signed x.lower y.lower = 0 <;> simp_all [decide?]
  · simp [decide?,zero]

/-- A first deciding rule records all the ties that precede it. In the
fixed-pair case both signs enter the magnitude calculation on this geometry. -/
inductive First (x y : ArmProfile) (rev : Bool) : Result → Prop where
  | unit (strict : RingRetainedUnitPass.signed x.unit y.unit ≠ 0) :
      First x y rev ⟨some .unit,RingRetainedUnitPass.signed x.unit y.unit⟩
  | pairs {k} (unit : x.unit.word = y.unit.word) (source : fourB? x y rev = some k) (strict : k ≠ 0) :
      First x y rev ⟨some .likePair,k⟩
  | lower (unit : x.unit.word = y.unit.word) (pairs : fourB? x y rev = some 0)
      (strict : RingRetainedUnitPass.signed x.lower y.lower ≠ 0) :
      First x y rev ⟨some .lower,RingRetainedUnitPass.signed x.lower y.lower⟩
  | fixed (unit : x.unit.word = y.unit.word) (pairs : fourB? x y rev = some 0)
      (low : x.lower.word = y.lower.word) :
      First x y rev (fixedResult (seedSign x y .R) (seedSign x y .S))

theorem first_iff {x y : ArmProfile} {rev k} : First x y rev k ↔ decide? x y rev = some k := by
  have u := RingRetainedUnitPass.signed_zero_iff x.unit y.unit
  have l := RingRetainedUnitPass.signed_zero_iff x.lower y.lower
  constructor
  · rintro (unit | ⟨eqn,source,strict⟩ | ⟨eqn,source,strict⟩ | ⟨eqn,source,low⟩)
    · simp [decide?,unit]
    · simp [decide?,u.mpr eqn,source,strict]
    · simp [decide?,u.mpr eqn,source,strict]
    · simp [decide?,u.mpr eqn,source,l.mpr low]
  · by_cases eqn : RingRetainedUnitPass.signed x.unit y.unit = 0
    · cases p : fourB? x y rev with
      | none => simp [decide?,eqn,p]
      | some s =>
        by_cases tied : s = 0
        · subst s
          by_cases low : RingRetainedUnitPass.signed x.lower y.lower = 0
          · rintro h
            obtain rfl := Option.some.inj (by simpa [decide?,eqn,p,low] using h : some _ = some k)
            exact .fixed (u.mp eqn) p (l.mp low)
          · rintro h
            obtain rfl := Option.some.inj (by simpa [decide?,eqn,p,low] using h : some _ = some k)
            exact .lower (u.mp eqn) p low
        · rintro h
          obtain rfl := Option.some.inj (by simpa [decide?,eqn,p,tied] using h : some _ = some k)
          exact .pairs (u.mp eqn) p tied
    · rintro h
      obtain rfl := Option.some.inj (by simpa [decide?,eqn] using h : some _ = some k)
      exact .unit eqn

private theorem local_swap (p : ArmProfile) (h : RS) : p.reflect.localPair h.swap = p.localPair h := by
  cases h <;> rfl

private theorem best_swap (p : ArmProfile) : p.reflect.bestPair = p.bestPair := max_comm ..

theorem fourB_reflect (x y : ArmProfile) : fourB? x.reflect y.reflect true = fourB? x y false := by
  change (match references x.hits true, references y.hits true with
    | [],[] => some 0
    | [s],[t] => some (pairSign (x.reflect.localPair s) (y.reflect.localPair t))
    | [_],[_,_] => some 1
    | [_,_],[_] => some (-1)
    | [_,_],[_,_] => some (RingSeededPairs.compareBits x.reflect.bestPair y.reflect.bestPair)
    | _,_ => none) = _
  rw [RingRetainedReferenceGroup.references_reflect,RingRetainedReferenceGroup.references_reflect]
  rcases RingRetainedReferenceGroup.references_cases x.hits false with lx | ⟨s,lx⟩ | lx <;>
    rcases RingRetainedReferenceGroup.references_cases y.hits false with ry | ⟨t,ry⟩ | ry <;>
    simp [fourB?,lx,ry,reflectSelectedRule4bReferences,local_swap,best_swap]

theorem seed_reflect (x y : ArmProfile) (s : RS) : seedSign x.reflect y.reflect s = seedSign x y s.swap := by
  cases s <;> rfl

/-- Once Rules 4a, 4b and 4c tie, the *two* signed results are fixed by
the two independently seeded traversals. In particular, opposite strict
orders double the magnitude on both geometries. -/
theorem fixed_both {x y : ArmProfile} (u : x.unit.word = y.unit.word)
    (p : fourB? x y false = some 0) (l : x.lower.word = y.lower.word) :
    let r := seedSign x y .R
    let s := seedSign x y .S
    decide? x y false = some (fixedResult r s) ∧
      decide? x.reflect y.reflect true = some (fixedResult s r) := by
  exact ⟨first_iff.mp (.fixed u p l),by
    have source := first_iff.mp (First.fixed (x := x.reflect) (y := y.reflect) (rev := true) u
      ((fourB_reflect x y).trans p) l)
    simpa only [seed_reflect,RS.swap] using source⟩

/-- At each addressed constitutional tie, derivation and first-rule testing
give one result on each geometry. The molecular reader, reference population
and both fixed reference passes are all obtained from the same frontier. -/
theorem frontier {i : Input} {root : i.certified.Atom} {f a b : Site i} {t}
    (listed : f ∈ RingMolecularSchedule.frontier i root) (prior : RingRetainedChemicalTrace.compareAt? i f a b = some t)
    (_tie : cipTraceOutcome t = .eq) (rev : Bool) :
    let read := RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)
    ∃ x y k, profile? i read rev ⟨a,some f⟩ = some x ∧ profile? i read rev ⟨b,some f⟩ = some y ∧
      Reads i read rev ⟨a,some f⟩ x ∧ Reads i read rev ⟨b,some f⟩ y ∧
      ∀ u v, Reads i read rev ⟨a,some f⟩ u → Reads i read rev ⟨b,some f⟩ v →
        ∀ z, First u v rev z ↔ z = k := by
  intro read
  have inc := (RingRetainedChemicalTrace.compareAt?_source prior).1
  have arm (s : Site i) (adj : i.certified.LocalizedCarrierTreeAdjacent s.val f.val) :=
    frontier_profile listed rev (⟨s,some f⟩ : Arm i)
      ((i.certified.mem_localizedRerootNeighborFrames_iff _ _).mpr ⟨s.property,adj⟩) adj.1
  obtain ⟨x,hx,sx⟩ := arm a inc.2.2.1
  obtain ⟨y,hy,sy⟩ := arm b inc.2.2.2
  obtain ⟨k,hk⟩ := decide_total sx sy
  refine ⟨x,y,k,hx,hy,sx,sy,?_⟩
  intro u v left right z
  obtain rfl := sx.unique left
  obtain rfl := sy.unique right
  rw [first_iff,hk,Option.some.injEq,eq_comm]

end TetraStereo.Engine.RingRetainedStereoDecision

assert_kernel_only TetraStereo.Engine.RingRetainedStereoDecision.Reads.unique
assert_kernel_only TetraStereo.Engine.RingRetainedStereoDecision.frontier_profile
assert_kernel_only TetraStereo.Engine.RingRetainedStereoDecision.Reads.reflect
assert_kernel_only TetraStereo.Engine.RingRetainedStereoDecision.fourB_total
assert_kernel_only TetraStereo.Engine.RingRetainedStereoDecision.decide_total

assert_kernel_only TetraStereo.Engine.RingRetainedStereoDecision.frontier
