import TetraStereo.Engine.RingEqualPathHandCounts

/-! Count ordinary chiral donors separately at every sphere. Each emitting
sphere must have a single signed stem and terminal unsigned priority. The
reference is fixed throughout the arm while all sphere words are concatenated. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingLayeredHandCounts
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Frame Reader)
open RingActivePairReport (Slot)
open RingGroupedCentre (cursor)
open RingRetainedChemicalTrace (Word)
open RingStereoSphereInventory (Inventory SignedPath reading inventory?)
open RingEqualPathHandCounts (runs lastHand check check_sound)
open RingFullPathEligibility (Key)
open RingResidualPairDecision (Table TableExact Verdict words)
open RingLigandFirstDifference (directions stages)
open private count from TetraStereo.Engine.RingEqualPathHandCounts
open private pick pick_exact from TetraStereo.Engine.RingResidualPairDecision
open private verdict_unique from TetraStereo.Engine.RingEqualPathHandCounts
open private keys_exact from TetraStereo.Engine.RingFullPathPublication
attribute [local instance] lexOrd

abbrev Counts := Nat × Nat

private def row? (row : Multiset SignedPath) : Option Counts :=
  let nr := (row.filter fun p => lastHand p = some .R).card
  let ns := (row.filter fun p => lastHand p = some .S).card
  if check nr ns [row] then some (nr,ns) else none

def populations? (inv : Inventory) := inv.mapM row?

/-- The same reference hand is used in every sphere, including across silent ones. -/
def bits (seed : RS) (ns : List Counts) := ns.flatMap fun p =>
  if seed = .R then runs p.1 p.2 else runs p.2 p.1

private theorem row_sound {row : Multiset SignedPath} {n : Counts} (h : row? row = some n)
    (seed : RS) : reading seed [row] = bits seed [n] := by
  dsimp only [row?] at h
  split at h
  next ok =>
    cases Option.some.inj h
    have law := RingEqualPathHandCounts.word (check_sound ok) seed
    cases seed <;> simpa [bits,count,RS.swap] using law
  next => contradiction

theorem reading_eq {inv : Inventory} {ns : List Counts} (h : populations? inv = some ns) (seed : RS) :
    reading seed inv = bits seed ns := by
  induction inv generalizing ns with
  | nil =>
    obtain rfl : [] = ns := Option.some.inj h
    rfl
  | cons row rest ih =>
    change (row :: rest).mapM row? = some ns at h
    simp only [List.mapM_cons] at h
    obtain ⟨n,hn,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨tail,ht,eqn⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj eqn
    have wide := row_sound hn seed
    simpa [reading,bits,List.flatMap_cons] using congrArg₂ List.append wide (ih ht)

structure Profile where
  throughFourA : List Word
  fourB : List Counts
  fourC : Word
  five : List Counts

def profile? (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) : Option Profile := do
  let u ← RingRetainedStereoRefinement.priority i r rev [] q
  let l ← RingRetainedStereoRefinement.priority i r rev [.lowercase] q
  let b ← inventory? i r rev [] q
  let f ← inventory? i r rev [.lowercase] q
  return ⟨u.deep,← populations? b,l.word,← populations? f⟩

def Profile.key (x : Profile) : Key :=
  ⟨x.throughFourA,max (bits .R x.fourB) (bits .S x.fourB),x.fourC,bits .R x.five⟩

/-- Successful extraction from each molecular inventory determines every
ordinary priority field. No correspondence between the two arms is needed. -/
theorem key_eq {i : Input} {r : Reader i} {rev : Bool} {q : Arm i} {x : Profile}
    (h : profile? i r rev q = some x) : RingFullPathEligibility.key? i r rev q = some x.key := by
  rw [← RingStereoSphereInventory.key_exact]
  unfold profile? at h
  obtain ⟨u,hu,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨l,hl,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b,hb,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨f,hf,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨bn,cb,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨fn',cf,e⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj e
  simp [RingStereoSphereInventory.key?,hu,hl,hb,hf,Profile.key,reading_eq cb,reading_eq cf]

def outcome (x y : Profile) (m n : Word) : Verdict :=
  pick (directions (words x.key m) (words y.key n)) stages

theorem table_entry {i : Input} {r : Reader i} {f : Site i} (fr : Frame i f)
    (ready : RingGroupedStereo.Ready f r) {rev : Bool} {x y : Profile} (a b : Slot)
    (left : profile? i r rev (cursor fr a) = some x) (right : profile? i r rev (cursor fr b) = some y)
    {m : Option Slot} {t : Table} (reported : TableExact fr r rev m t)
    {ws : Slot → Word} (marks : RingFullPathTrialReadings.MarkWords fr r rev m ws) :
    t[a.val][b.val] = outcome x y (ws a) (ws b) := by
  obtain ⟨ks,_,only⟩ := keys_exact fr ready rev
  have legal := (only ks).mpr rfl
  have identify (s : Slot) (v : Profile) (got : profile? i r rev (cursor fr s) = some v) :
      ks s = v.key := by
    obtain ⟨k,hk,onlyK⟩ := RingFullPathEligibility.key_exact ready rev (cursor fr s)
      (RingGroupedCentre.valid fr s) (fr.direction s).property.1
    exact ((onlyK _).mp (legal s)).trans (Option.some.inj (hk.symm.trans (key_eq got)))
  have witness := (reported ks ws legal marks a b).1
  rw [identify a x left,identify b y right] at witness
  exact verdict_unique witness (pick_exact _ _)

/-- Taking a fresh majority at every sphere would tie these two arms.
A single consistent reference puts the second arm ahead at Rule 4b. -/
theorem reference_across_spheres :
    outcome ⟨[],[(1,0),(0,2)],[],[]⟩ ⟨[],[(0,1),(0,2)],[],[]⟩ [] [] = .right .rule4b := by decide

end TetraStereo.Engine.RingLayeredHandCounts
assert_kernel_only TetraStereo.Engine.RingLayeredHandCounts.table_entry
assert_kernel_only TetraStereo.Engine.RingLayeredHandCounts.reference_across_spheres
