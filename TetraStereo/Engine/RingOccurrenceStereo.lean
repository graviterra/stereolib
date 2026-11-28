import TetraStereo.Engine.RingGroupedGeometry
import TetraStereo.Engine.RingZeroDuplicateMass
import TetraStereo.OneCenter.LocalizedSelectedRootReader

/-! # Stereo comparisons by visits to molecular occurrences

Read each hand from the frozen store at the visited cursor. A seed can change
which children are visited first, so each local and fixed seed gets its own
breadth-first traversal. Constitutional and cumulative sibling priorities use
the molecular single-pass readers. -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingOccurrenceStereo
open OneCenter CertifiedLocalizedCIPInput RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader Labels upper)
open RingRetainedStereoRefinement (Observation Derives priority)
open RingRetainedReferenceGroup (Hit)
open RingRetainedStereoDecision (Result)
open RingRetainedSeedFrames (State Directed)

private abbrev kids (i : Input) (q : Arm i) := i.certified.executableLocalizedRerootChildren q
private abbrev budget (i : Input) (q : Arm i) := i.certified.localizedRerootCursorBudget q
private def ranked (i : Input) (r : Reader i) (rev : Bool) (os : List Observation) :=
  priority i r rev os

/-- Read a single set of molecular child lists and constitutional keys
throughout a seeded priority pass. This includes all its earlier passes. -/
private structure Access (i : Input) where
  edges : Arm i → List (Arm i)
  key : Arm i → Option RingRetainedChemicalTrace.Key

private def Access.unitPass {i : Input} (access : Access i) (r : Reader i) : Nat → Arm i → Option Branch
  | 0,_ => none
  | n+1,q => do
    let k ← access.key q
    let v ← r q.occurrence
    let cs := access.edges q
    guard (v.all RingNestedActivePair.consistent = true ∧ (cs = [] → v = none))
    let bs ← cs.mapM (access.unitPass r n)
    return RingRetainedUnitPass.branch k (RingNestedActivePair.unit (v.map Prod.fst))
      (order Branch.shallow bs) (order Branch.deep bs)

private def Access.refinePass {i : Input} (access : Access i) (r : Reader i) (rev : Bool) (o : Observation)
    (prior : Arm i → Option Branch) : Nat → Arm i → Option Branch
  | 0,_ => none
  | n+1,q => do
    let p ← prior q
    let v ← r q.occurrence
    let bs ← (access.edges q).mapM (access.refinePass r rev o prior n)
    return RingRetainedStereoRefinement.extend p (o.value v rev) (order Branch.shallow bs) (order Branch.deep bs)

private def Access.run {i : Input} (access : Access i) (r : Reader i) (rev : Bool) :
    List Observation → Arm i → Option Branch
  | [],q => access.unitPass r (budget i q + 1) q
  | o::os,q => access.refinePass r rev o (access.run r rev os) (budget i q + 1) q

private def accessFor (i : Input) (q : Arm i) : Access i :=
  let reader := SelectedRoot.reader i.certified (i.certified.certified.input.molecule.atomCount+1) q.occurrence.val.root
  ⟨fun c => (reader.readChildren c).getD [],RingRetainedChemicalTrace.keyWith i reader⟩

private theorem access_same (i : Input) (q : Arm i) :
    accessFor i q = ⟨kids i,RingRetainedChemicalTrace.key? i⟩ := by
  dsimp only [accessFor]
  apply congrArg₂ Access.mk
  · funext c; rw [LocalizedRerootChildReader.readChildren_eq]; rfl
  · exact RingRetainedChemicalTrace.keyWith_eq ..

private theorem canonical_run (i : Input) (r : Reader i) (rev : Bool) :
    ∀ s, (Access.mk (kids i) (RingRetainedChemicalTrace.key? i)).run r rev s = ranked i r rev s := by
  let ac : Access i := ⟨kids i,RingRetainedChemicalTrace.key? i⟩
  have unit (n : Nat) : ac.unitPass r n = RingRetainedUnitPass.build i r n := by
    induction n with
    | zero => rfl
    | succ n ih => funext c; simp only [Access.unitPass,RingRetainedUnitPass.build,ih,ac]
  have step (o : Observation) (p : Arm i → Option Branch) (n : Nat) :
      ac.refinePass r rev o p n = RingRetainedStereoRefinement.build i p r o rev n := by
    induction n with
    | zero => rfl
    | succ n ih => funext c; simp only [Access.refinePass,RingRetainedStereoRefinement.build,ih,ac]
  intro s
  induction s with
  | nil => funext c; exact congrFun (unit _) c
  | cons o s ih =>
    funext c
    simp only [Access.run,ih]
    exact congrFun (step o _ _) c

private def indexedRank (i : Input) (r : Reader i) (rev : Bool) (os : List Observation) (q : Arm i) :=
  (accessFor i q).run r rev os q

/-- A whole-sphere traversal can share the original root's child and rank
readers for every occurrence on its path. -/
def withRankReaders {α : Type} (i : Input) (r : Reader i) (rev : Bool)
    (os : List Observation) (q : Arm i)
    (use : (Arm i → List (Arm i)) → (Arm i → Option Branch) → α) : α :=
  let access := accessFor i q
  use access.edges (access.run r rev os)

theorem withRankReaders_eq {α : Type} (i : Input) (r : Reader i) (rev : Bool)
    (os : List Observation) (q : Arm i)
    (use : (Arm i → List (Arm i)) → (Arm i → Option Branch) → α) :
    withRankReaders i r rev os q use = use (kids i) (ranked i r rev os) := by
  simp only [withRankReaders,access_same,canonical_run]

@[csimp] private theorem indexedRank_exact : @ranked = @indexedRank := by
  funext i r rev os q
  simp only [indexedRank,access_same,canonical_run]

/-- Visit every child, including tied children, in its seed-specific order.
A missing molecular priority propagates to the caller. -/
private def next? (i : Input) (r : Reader i) (rev : Bool) (os : List Observation) (q : Arm i) :
    Option (List (Arm i)) := do
  let xs ← (kids i q).mapM fun c => (ranked i r rev os c).map (fun b => (c,b.deep))
  return (order Prod.snd xs).map Prod.fst

private def spheres {α : Type} (next : α → Option (List α)) : Nat → List α → Option (List α)
  | _,[] => some []
  | 0,_::_ => none
  | n+1,x::xs => do
    let children ← (x::xs).mapM next
    return (x::xs) ++ (← spheres next n children.flatten)

private def hand (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) : Option RS :=
  upper ((r q.occurrence).join.map fun p => if rev then p.2 else p.1)

/-- Like/unlike list of the chiral occurrences in molecular visit order. -/
def pairs? (i : Input) (r : Reader i) (rev : Bool) (fixed : Bool) (seed : RS) (q : Arm i) :
    Option (List Bool) := do
  let stages := if fixed then [.pairing seed,.lowercase] else [.pairing seed]
  let qs ← spheres (next? i r rev stages) (budget i q + 1) [q]
  return qs.filterMap fun c => (hand i r rev c).map (· == seed)

private def indexedPairs (i : Input) (r : Reader i) (rev fixed : Bool) (seed : RS) (q : Arm i) :
    Option (List Bool) := do
  let ac := accessFor i q
  let stages := if fixed then [.pairing seed,.lowercase] else [.pairing seed]
  let next (c : Arm i) := do
    let xs ← (ac.edges c).mapM fun t => (ac.run r rev stages t).map fun b => (t,b.deep)
    return (order Prod.snd xs).map Prod.fst
  let qs ← spheres next (budget i q + 1) [q]
  return qs.filterMap fun c => (hand i r rev c).map (· == seed)

@[csimp] private theorem indexedPairs_exact : @pairs? = @indexedPairs := by
  funext i r rev fixed seed q
  simp only [pairs?,indexedPairs,access_same,canonical_run]
  rfl

/-- The shortest paths to uppercase descriptors are considered first. Among
paths of that length take every occurrence of maximal through-4a priority,
including repeated occurrences with the same hand. -/
def population (hits : List Hit) (rev : Bool) : List RS :=
  let eligible (x : Hit) := hits.all fun y =>
    decide (x.path.length ≤ y.path.length ∧ (y.path.length = x.path.length → y.path ≤ x.path))
  (hits.filter eligible).map fun h => if rev then h.hand.swap else h.hand

/-- The cursor distinguishes occurrences even when their path priorities and
descriptors coincide. Traverse the entire arm before selecting a population. -/
structure Address (i : Input) where
  cursor : Arm i
  path : RingRetainedReferenceGroup.Path

private def descend {i : Input} (p : Branch × List (Address i)) :=
  p.2.map fun x => {x with path := p.1.deep :: x.path}

private def scan {i : Input} (edges : Arm i → List (Arm i)) (unit : Arm i → Option Branch) :
    Nat → Arm i → Option (List (Address i))
  | 0,_ => none
  | n+1,q => do
    let blocks ← (edges q).mapM fun c => do
      let rank ← unit c
      return (rank,← scan edges unit n c)
    return ⟨q,[]⟩ :: blocks.flatMap descend

private abbrev inventory (i : Input) (r : Reader i) := scan (kids i) (RingRetainedUnitPass.atArm i r)

private def hitOf {i : Input} (r : Reader i) (x : Address i) : Option Hit :=
  (hand i r false x.cursor).map fun h => ⟨x.path,h⟩

def seeds? (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) : Option (List RS) := do
  let sites ← inventory i r (budget i q + 1) q
  return localizedRule4bReferencesFromPopulation (population (sites.filterMap (hitOf r)) rev)

private def indexedSeeds (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) : Option (List RS) := do
  let ac := accessFor i q
  let sites ← scan ac.edges (ac.run r false []) (budget i q + 1) q
  return localizedRule4bReferencesFromPopulation (population (sites.filterMap (hitOf r)) rev)

@[csimp] private theorem indexedSeeds_exact : @seeds? = @indexedSeeds := by
  funext i r rev q
  simp only [seeds?,indexedSeeds,access_same,canonical_run]
  rfl

private def sign (o : Ordering) : Int := match o with
  | .lt => -1 | .eq => 0 | .gt => 1

/-- Either seed may win. An arm wins precisely when one of its two sequences
beats both sequences of the opposite arm. Otherwise the four-way contest ties. -/
def fourLists (a b c d : List Bool) : Ordering :=
  if (c < a ∧ d < a) ∨ (c < b ∧ d < b) then .gt
  else if (a < c ∧ b < c) ∨ (a < d ∧ b < d) then .lt else .eq

def fourB? (i : Input) (r : Reader i) (rev : Bool) (a b : Arm i) : Option Int := do
  match ← seeds? i r rev a, ← seeds? i r rev b with
  | [],[] => return 0
  | [s],[t] => return sign (compare (← pairs? i r rev false s a) (← pairs? i r rev false t b))
  | [_],[_,_] => return 1
  | [_,_],[_] => return -1
  | [s,t],[u,v] =>
    return sign (fourLists (← pairs? i r rev false s a) (← pairs? i r rev false t a)
      (← pairs? i r rev false u b) (← pairs? i r rev false v b))
  | _,_ => none

private def classes? (i : Input) (r : Reader i) (rev : Bool) (os : List Observation) (a b : Arm i) :
    Option Int := do
  return sign (compare (← ranked i r rev os a).word (← ranked i r rev os b).word)

/-- Fixed R determines direction; reversing the fixed reference distinguishes
one unit of magnitude from two. -/
def fixedScore (right left : Ordering) : Int :=
  if right == .eq then 0 else sign right * (if right == left then 1 else 2)

def decide? (i : Input) (r : Reader i) (rev : Bool) (a b : Arm i) : Option Result := do
  let unit ← classes? i r rev [] a b
  if unit ≠ 0 then return ⟨some .unit,unit⟩
  let pairs ← fourB? i r rev a b
  if pairs ≠ 0 then return ⟨some .likePair,pairs⟩
  let lower ← classes? i r rev [.lowercase] a b
  if lower ≠ 0 then return ⟨some .lower,lower⟩
  let fixed (s : RS) : Option Ordering := do
    return compare (← pairs? i r rev true s a) (← pairs? i r rev true s b)
  let score := fixedScore (← fixed .R) (← fixed .S)
  return ⟨if score = 0 then none else some .fixedPair,score⟩

theorem fourLists_order (a b c d : List Bool) :
    fourLists a b c d = compare (max a b) (max c d) := by
  have gt : (c < a ∧ d < a) ∨ (c < b ∧ d < b) ↔ max c d < max a b := by simp
  have lt : (a < c ∧ b < c) ∨ (a < d ∧ b < d) ↔ max a b < max c d := by simp
  simp only [fourLists,gt,lt]
  -- The executable list comparator is lexicographic at the first unequal bit.
  have law (x y : List Bool) : compare x y = .lt ↔ x < y :=
    DeclarativeCIP.compareLex_eq_lt_iff_of compare (fun _ _ => by decide +revert)
      (fun _ _ => Std.compare_eq_eq_iff_eq) x y
  cases h : compare (max a b) (max c d) with
  | eq => simp [Std.compare_eq_eq_iff_eq.mp h]
  | lt => have v := (law _ _).mp h; simp [v,not_lt_of_gt v]
  | gt =>
    have v := (law _ _).mp (Std.OrientedCmp.eq_swap (cmp := compare) |>.trans (congrArg Ordering.swap h))
    simp [v]

private theorem population_exact (hs : List Hit) (rev : Bool) :
    population hs rev = RingRetainedReferenceGroup.hands hs rev := by
  unfold population RingRetainedReferenceGroup.hands RingRetainedReferenceGroup.group
  dsimp only
  apply congrArg (List.map _)
  apply List.filter_congr
  intro x _
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.any_eq_false,
    RingRetainedReferenceGroup.senior]
  constructor
  · intro h y hy
    obtain ⟨near,senior⟩ := h y hy
    exact fun bad => bad.elim (not_lt_of_ge near) (fun pair => (not_lt_of_ge (senior pair.1)) pair.2)
  · intro h y hy
    exact ⟨le_of_not_gt (fun lt => h y hy (Or.inl lt)),fun eqn =>
      le_of_not_gt (fun lt => h y hy (Or.inr ⟨eqn,lt⟩))⟩

private abbrev Ready {i : Input} (f : Site i) (r : Reader i) := RingGroupedStereo.Ready f r
private abbrev Valid {i : Input} (q : Arm i) := i.certified.LocalizedRerootCursorValid q
private abbrev On {i : Input} (f : Site i) (q : Arm i) := q.occurrence.val.root = f.val.root

private theorem children_total {i : Input} {f : Site i} {α : Type} (fn : Arm i → Option α)
    {q : Arm i} (valid : Valid q) (on : On f q) {n : Nat} (enough : budget i q < n+1)
    (smaller : ∀ c, Valid c → On f c → budget i c < n → ∃ x, fn c = some x) :
    ∃ xs, (kids i q).mapM fn = some xs := by
  have frame := i.certified.executableLocalizedRerootChildren_declarative q
  apply RingRetainedUnitPass.collect
  exact fun c hc => smaller c (i.certified.localizedRerootChild_valid q c _ frame hc)
    ((i.certified.localizedRerootChildren_root_eq q c _ frame hc).trans on)
    (by have h := i.certified.localizedRerootChild_budget_lt q c _ valid frame hc; change budget i c < budget i q at h; omega)

theorem rank_total {i : Input} {f : Site i} {r : Reader i} (ready : Ready f r) (rev : Bool)
    (os : List Observation) : ∀ q : Arm i, Valid q → On f q → ∃ b, ranked i r rev os q = some b := by
  induction os with
  | nil =>
    suffices ∀ n (q : Arm i), Valid q → On f q → budget i q < n →
        ∃ b, RingRetainedUnitPass.build i r n q = some b from
      fun q v on => this _ q v on (Nat.lt_succ_self _)
    intro n; induction n with
    | zero => intros; omega
    | succ n ih =>
      intro q valid on enough
      obtain ⟨x,hx⟩ := RingRetainedChemicalCoverage.key_total i (RingRetainedChemicalCoverage.admitted_atoms i) q valid
      obtain ⟨v,hv,ok,leaf⟩ := ready q on
      have gate : (guard (v.all RingNestedActivePair.consistent = true ∧ (kids i q = [] → v = none)) : Option Unit) =
          some () := if_pos ⟨ok,leaf⟩
      obtain ⟨ks,hks⟩ := children_total _ valid on enough ih
      exact ⟨RingRetainedUnitPass.branch x (RingNestedActivePair.unit (v.map Prod.fst)) (order Branch.shallow ks) (order Branch.deep ks),by simp only [RingRetainedUnitPass.build,hx,hv,gate,hks,Option.bind_eq_bind,Option.bind_some,Option.pure_def]⟩
  | cons o os prior =>
    let fn := ranked i r rev os
    suffices ∀ n (q : Arm i), Valid q → On f q → budget i q < n →
        ∃ b, RingRetainedStereoRefinement.build i fn r o rev n q = some b from
      fun q v on => this _ q v on (Nat.lt_succ_self _)
    intro n; induction n with
    | zero => intros; omega
    | succ n ih =>
      intro q valid on enough
      obtain ⟨p,hp⟩ := prior q valid on
      change fn q = some p at hp
      obtain ⟨v,hv,_,_⟩ := ready q on
      obtain ⟨ks,hks⟩ := children_total _ valid on enough ih
      exact ⟨RingRetainedStereoRefinement.extend p (o.value v rev) (order Branch.shallow ks) (order Branch.deep ks),by simp only [RingRetainedStereoRefinement.build,hp,hv,hks,Option.bind_eq_bind,Option.bind_some,Option.pure_def]⟩

private theorem rank_of {i f r rev os q b} (ready : @Ready i f r) (valid : Valid q) (on : On f q)
    (h : Derives i r rev os q b) : ranked i r rev os q = some b := by
  obtain ⟨p,hp⟩ := rank_total ready rev os q valid on
  exact hp.trans (congrArg some (RingRetainedStereoRefinement.unique os q p b
    (RingRetainedStereoRefinement.source os q hp) h))

private theorem mapM_values {α β : Type} (xs : List α) (get : α → Option β) (value : α → β)
    (h : ∀ x ∈ xs, get x = some (value x)) : xs.mapM get = some (xs.map value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons,h x List.mem_cons_self,ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem state_at {i f r} (ready : @Ready i f r) (rev : Bool) {q : Arm i}
    (v : Valid q) (on : On f q) : ∃ t : State i r rev, t.q = q := by
  obtain ⟨p,hp⟩ := RingGroupedStereo.arm_ready ready q v on
  have src := RingGroupedStereo.arm_source hp
  cases rev
  · exact ⟨⟨q,v,p,src⟩,rfl⟩
  · exact ⟨⟨q,v,p.reflect,src.reflect⟩,rfl⟩

theorem next_row {i f r rev os} (ready : @Ready i f r)
    (key : State i r rev → Branch) (src : ∀ t, Derives i r rev os t.q (key t))
    (t : State i r rev) (on : On f t.q) :
    ∃ sh de, Directed key t sh de ∧ next? i r rev os t.q = some (de.map State.q) ∧
      ∀ c ∈ de, On f c.q ∧ budget i c.q < budget i t.q := by
  let raw := kids i t.q
  have frame := i.certified.executableLocalizedRerootChildren_declarative t.q
  have childOn {c} (mem : c ∈ raw) : On f c :=
    (i.certified.localizedRerootChildren_root_eq t.q c _ frame mem).trans on
  have childState (c : {x // x ∈ raw}) := state_at ready rev
    (i.certified.localizedRerootChild_valid t.q c.val _ frame c.property) (childOn c.property)
  let xs := raw.attach.map fun c => (childState c).choose
  have native : xs.map State.q = raw := by simp [xs,List.map_map,Function.comp_def,(childState _).choose_spec]
  let data (c : State i r rev) := (c.q,(key c).deep)
  let sh := order (fun c => (key c).shallow) xs
  let de := order (fun c => (key c).deep) xs
  refine ⟨sh,de,⟨xs,native,legal_order ..,legal_order ..⟩,?_,?_⟩
  · have collected : raw.mapM (fun c => (ranked i r rev os c).map (fun b => (c,b.deep))) =
        some (xs.map data) := by
      rw [← native,List.mapM_map]
      apply mapM_values
      intro c hc
      have hc' : c.q ∈ raw := native ▸ List.mem_map_of_mem hc
      simp [rank_of ready c.valid (childOn hc') (src c),data]
    have mapped : de.map data = order Prod.snd (xs.map data) := List.map_mergeSort fun _ _ _ _ => rfl
    unfold next?
    rw [show kids i t.q = raw from rfl,collected]
    change some ((order Prod.snd (xs.map data)).map Prod.fst) = _
    rw [← mapped,List.map_map]
    rfl
  · intro c hc
    have mem : c.q ∈ raw := native ▸ List.mem_map_of_mem ((legal_order _ xs).perm.mem_iff.mp hc)
    exact ⟨childOn mem,i.certified.localizedRerootChild_budget_lt t.q c.q _ t.valid frame mem⟩

/-- Relate a round of the executable sphere scan to individual legal FIFO
steps. The waiting queue retains the parent's position within this sphere. -/
private theorem rounds {α β : Type} (q : α → β) (next : β → Option (List β))
    (legal : α → List α → List α → Prop) (good : Nat → α → Prop)
    (empty : ∀ t, ¬ good 0 t) (step : ∀ n t, good (n+1) t → ∃ sh de,
      legal t sh de ∧ next (q t) = some (de.map q) ∧ ∀ c ∈ de, good n c) :
    ∀ n xs, (∀ x ∈ xs, good n x) → ∃ out, Visits legal xs [] out ∧
      spheres next n (xs.map q) = some (out.map q) := by
  intro n
  induction n with
  | zero =>
    intro xs ok; cases xs with
    | nil => exact ⟨[],.stop,rfl⟩
    | cons x xs => exact (empty x (ok x List.mem_cons_self)).elim
  | succ n ih =>
    have drain (xs waiting : List α) (ok : ∀ x ∈ xs, good (n+1) x) :
        ∃ ds : List (List α), (xs.map q).mapM next = some (ds.map (List.map q)) ∧
          (∀ c ∈ ds.flatten, good n c) ∧ ∀ tail, Visits legal [] (waiting ++ ds.flatten) tail →
            Visits legal xs waiting (xs ++ tail) := by
      induction xs generalizing waiting with
      | nil => exact ⟨[],rfl,by simp,by simp⟩
      | cons x xs rec =>
        obtain ⟨sh,de,h,got,small⟩ := step n x (ok x List.mem_cons_self)
        obtain ⟨ds,found,below,finish⟩ := rec (waiting++de) (fun c hc => ok c (List.mem_cons_of_mem _ hc))
        refine ⟨de::ds,by simp [List.mapM_cons,got,found],by simpa only [List.flatten_cons,List.forall_mem_append] using And.intro small below,?_⟩
        intro tail more
        exact .pop h (finish tail (by simpa [List.append_assoc] using more))
    intro xs ok
    cases xs with
    | nil => exact ⟨[],.stop,rfl⟩
    | cons h t =>
      obtain ⟨ds,found,small,finish⟩ := drain (h::t) [] ok
      obtain ⟨out,legalOut,values⟩ := ih ds.flatten small
      have rotated : Visits legal [] ds.flatten out := by
        cases h : ds.flatten with
        | nil => simpa [h] using legalOut
        | cons x xs => exact .rotate (by simpa [h] using legalOut)
      refine ⟨(h::t)++out,finish out (by simpa using rotated),?_⟩
      change (List.mapM next ((h::t).map q) >>= _) = _
      rw [found]
      simp [← List.map_flatten,values]

private theorem molecular_walk {i f r rev os} (ready : @Ready i f r)
    (key : State i r rev → Branch) (src : ∀ t, Derives i r rev os t.q (key t))
    (t : State i r rev) (on : On f t.q) :
    ∃ out, Visits (Directed key) [t] [] out ∧
      spheres (next? i r rev os) (budget i t.q+1) [t.q] = some (out.map State.q) := by
  apply rounds State.q _ _ (fun n c => On f c.q ∧ budget i c.q < n)
    (fun _ ok => Nat.not_lt_zero _ ok.2) (fun n c ok => ?_) _ [t]
  · intro x hx; obtain rfl := List.mem_singleton.mp hx
    exact ⟨on,Nat.lt_succ_self _⟩
  · obtain ⟨sh,de,legal,got,small⟩ := next_row ready key src c ok.1
    exact ⟨sh,de,legal,got,fun x mem => ⟨(small x mem).1,by have := (small x mem).2; have := ok.2; omega⟩⟩

private theorem pair_words {i f r rev} (ready : @Ready i f r) (t : State i r rev)
    (on : On f t.q) (fixed : Bool) (s : RS) :
    pairs? i r rev fixed s t.q = some (RingRetainedStereoDecision.accepted t.profile.unit
      (if fixed then t.profile.fixedPair s else t.profile.localPair s)) := by
  cases fixed
  case false =>
    obtain ⟨out,walk,computed⟩ := molecular_walk ready (RingRetainedSeedFrames.localP s)
      (fun x => x.source.paired s) t on
    change _ = some (RingRetainedStereoDecision.accepted (RingRetainedSeedFrames.unit t) (RingRetainedSeedFrames.localP s t))
    rw [RingRetainedSeedFrames.accepted_local s walk]
    simp only [pairs?,Bool.false_eq_true,if_false,computed,Option.bind_eq_bind,Option.bind_some,Option.pure_def,
      List.filterMap_map]
    apply congrArg some
    apply List.filterMap_congr
    intro x _
    obtain ⟨v,seen,_,h⟩ := RingRetainedSeedFrames.molecular_mark s x
    simpa [hand,seen,Function.comp_def] using h.symm
  case true =>
    obtain ⟨out,w,got⟩ := molecular_walk ready (RingRetainedSeedFrames.fixed s) (fun x => x.source.fixed s) t on
    change _ = some (RingRetainedStereoDecision.accepted (RingRetainedSeedFrames.unit t) (RingRetainedSeedFrames.fixed s t))
    rw [RingRetainedSeedFrames.accepted_fixed s w]
    simp only [pairs?,if_true,got,Option.bind_eq_bind,Option.bind_some,Option.pure_def,List.filterMap_map]
    apply congrArg some
    apply List.filterMap_congr
    intro x _
    obtain ⟨v,seen,h,_⟩ := RingRetainedSeedFrames.molecular_mark s x
    simpa [hand,seen,Function.comp_def] using h.symm


private def retained {α : Type} (degree : α → Nat) : List α → List α
  | [] => []
  | x::xs => x::xs.filter (fun y => degree y != 0)

private theorem projected_map {α : Type} (v degree : α → Nat) (xs : List α) :
    projected (xs.map v) (xs.map degree) = (retained degree xs).map v := by
  have tail (ys : List α) :
      ((ys.map v).zip (ys.map degree)).filterMap (fun (n,d) => if d = 0 then none else some n) =
        (ys.filter (fun y => degree y != 0)).map v := by
    induction ys with
    | nil => rfl
    | cons y ys ih => by_cases eq : degree y = 0 <;> simp [eq,ih]
  cases xs with
  | nil => rfl
  | cons x xs => simp [projected,retained,tail]

private theorem projection {i r rev os} (key : State i r rev → Branch)
    (src : ∀ t, Derives i r rev os t.q (key t)) {t out}
    (walk : Visits (Directed key) [t] [] out) :
    (retained (fun x : State i r rev => (kids i x.q).length) out).map (fun x => (key x).value) =
      (key t).nonterminalStream := by
  let rowsOK (b : Branch) (s d : List Branch) := b.levels = rows s d
  have h := walk.map (after := rowsOK) key (fun a s d step => by
    obtain ⟨xs,native,sh,de⟩ := step
    exact RingRetainedSeedFrames.layout native key src sh de)
  have degree (x : State i r rev) : (key x).degree = (kids i x.q).length := by
    obtain ⟨sh,de,⟨row⟩⟩ := RingRetainedStereoRefinement.decomposition (src x)
    have count := (TerminalTie.mapM_forall₂ _ _ _ row.complete).length_eq
    simpa [Branch.degree,Branch.word,row.layout,rows] using row.shallow.perm.length_eq.trans count.symm
  simpa only [List.map_map,Function.comp_def,degree,projected_map] using
    fifo_nonterminal (allowed := rowsOK) (fun _ _ _ h => h) h

private theorem retain_marks {α : Type} (d : α → Nat) (m : α → Option Bool)
    (leaves : ∀ x, d x = 0 → m x = none) (out : List α) :
    (retained d out).filterMap m = out.filterMap m := by
  have tail (xs : List α) : (xs.filter (fun x => d x != 0)).filterMap m = xs.filterMap m := by
    induction xs with
    | nil => rfl
    | cons x xs ih => by_cases h : d x = 0 <;> simp [h,ih,leaves x,List.filterMap_cons]
  cases out with
  | nil => rfl
  | cons x xs => simp [retained,tail,List.filterMap_cons]

private theorem unit_value {i r rev q b} (h : RingRetainedUnitPass.Reading i r rev q b) :
    ∃ v, r q.occurrence = some v ∧ b.value = RingNestedActivePair.unit (v.map fun p => if rev then p.2 else p.1) := by
  cases h with | node _ seen _ _ _ _ _ _ => exact ⟨_,seen,rfl⟩

private theorem pass_value {i r rev q b o os v} (h : Derives i r rev (o::os) q b)
    (seen : r q.occurrence = some v) : b.value = o.value v rev := by
  cases h with
  | node _ got _ _ _ _ _ => cases Option.some.inj (got.symm.trans seen); rfl

private theorem local_slots {i f r rev} (ready : @Ready i f r) (t : State i r rev)
    (on : On f t.q) (s : RS) : ∃ xs : List (Option Bool),
      xs.map Option.isSome = t.profile.unit.nonterminalStream.map (· == 2) ∧
      xs.map (·.getD false) = RingRetainedStereoRefinement.bits (t.profile.localPair s).nonterminalStream ∧
      xs.filterMap id = RingRetainedStereoDecision.accepted t.profile.unit (t.profile.localPair s) := by
  let key := RingRetainedSeedFrames.localP (i := i) (read := r) (rev := rev) s
  let base := @RingRetainedSeedFrames.unit i r rev
  let m := RingRetainedSeedFrames.mark key
  let degree (x : State i r rev) := (kids i x.q).length
  obtain ⟨out,w,_⟩ := molecular_walk ready key (fun x => x.source.paired s) t on
  have earlier : Visits (Directed base) [t] [] out := by
    have mapped := w.map (after := Directed base) id (fun a sh de step => by
      obtain ⟨xs,nat,first,second⟩ := step
      obtain ⟨u,v⟩ := RingRetainedSeedFrames.earlier_order base key
        (fun t => t.source.unit) (fun t => t.source.paired s) first second
      simpa using (show Directed base a sh de from ⟨xs,nat,u,v⟩))
    simpa using mapped
  have unitProj := projection base (fun x => x.source.unit) earlier
  have pairProj := projection key (fun x => x.source.paired s) w
  have vals (x : State i r rev) :
      (m x).isSome = ((base x).value == 2) ∧ (m x).getD false = ((key x).value == 1) := by
    obtain ⟨v,seen,hv⟩ := unit_value x.source.unit
    have pk := pass_value (x.source.paired s) seen
    change (if x.profile.unit.value = 2 then some ((x.profile.localPair s).value == 1) else none).isSome =
        (x.profile.unit.value == 2) ∧
      (if x.profile.unit.value = 2 then some ((x.profile.localPair s).value == 1) else none).getD false =
        ((x.profile.localPair s).value == 1)
    rw [hv,pk]
    simp only [Observation.value]
    generalize v.map (fun p => if rev then p.2 else p.1) = label
    rcases label with _ | ⟨(_|_)⟩ | ⟨(_|_)⟩ <;> cases s <;> constructor <;> rfl
  refine ⟨(retained degree out).map m,?_,?_,?_⟩
  · change _ = (base t).nonterminalStream.map _
    rw [← unitProj,List.map_map,List.map_map]
    exact List.map_congr_left fun x _ => (vals x).1
  · change _ = ((key t).nonterminalStream.map (· == 1))
    rw [← pairProj,List.map_map,List.map_map]
    exact List.map_congr_left fun x _ => (vals x).2
  · change _ = RingRetainedStereoDecision.accepted (base t) (key t)
    rw [RingRetainedSeedFrames.accepted_local s w,List.filterMap_map]
    apply retain_marks
    intro x hx
    exact RingRetainedSeedFrames.terminal_mark key x (List.length_eq_zero_iff.mp hx)

private theorem compact_compare (xs ys : List (Option Bool)) (same : xs.map Option.isSome = ys.map Option.isSome) :
    RingSeededPairs.compareBits (xs.map (·.getD false)) (ys.map (·.getD false)) =
      RingSeededPairs.compareBits (xs.filterMap id) (ys.filterMap id) := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp at same
    | cons y ys =>
      obtain ⟨heads,tail⟩ := List.cons.inj same
      cases x <;> cases y <;> simp_all [RingSeededPairs.compareBits]

private theorem mapM_correspond {α β γ : Type} {old : α → Option β} {newRead : α → Option γ}
    (project : γ → β) {xs : List α} {ys : List β} (hit : xs.mapM old = some ys)
    (step : ∀ x ∈ xs, ∀ {y}, old x = some y → ∃ w, newRead x = some w ∧ project w = y) :
    ∃ ws, xs.mapM newRead = some ws ∧ ws.map project = ys := by
  induction xs generalizing ys with
  | nil => exact ⟨[],rfl,Option.some.inj hit⟩
  | cons x xs ih =>
    rw [List.mapM_cons] at hit
    obtain ⟨y,hy,t⟩ := Option.bind_eq_some_iff.mp hit
    obtain ⟨zs,hzs,out⟩ := Option.bind_eq_some_iff.mp t
    cases Option.some.inj out
    obtain ⟨w,hw,pw⟩ := step x List.mem_cons_self hy
    obtain ⟨ws,hs,ps⟩ := ih hzs (fun c hc => step c (List.mem_cons_of_mem _ hc))
    exact ⟨w::ws,by simp [List.mapM_cons,hw,hs],by simp [pw,ps]⟩

private theorem descend_hits {i : Input} (r : Reader i) (k : Branch) (xs : List (Address i)) :
    (descend (k,xs)).filterMap (hitOf r) =
      (xs.filterMap (hitOf r)).map (fun h => {h with path := k.deep::h.path}) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : hand i r false x.cursor <;>
      simp [descend,hitOf,h] at ih ⊢ <;> exact ih

/-- Projecting the molecular inventory reproduces the entire list of upper
hands and ranked paths, with multiplicity. -/
private theorem inventory_exact {i f r q hs} (ready : @Ready i f r)
    (listing : RingRetainedReferenceGroup.Listing i r q hs) (valid : Valid q) (on : On f q)
    (n : Nat) (enough : budget i q < n) :
    ∃ sites, inventory i r n q = some sites ∧ sites.filterMap (hitOf r) = hs := by
  induction listing generalizing n with
  | @node q v parts seen _ lookup complete rank below ih =>
    cases n with
    | zero => omega
    | succ n =>
      have frame := i.certified.executableLocalizedRerootChildren_declarative q
      let take (p : Branch × List (Address i)) := (p.1,p.2.filterMap (hitOf r))
      let fetch (c : Arm i) := do
        let k ← RingRetainedUnitPass.atArm i r c
        return (k,← inventory i r n c)
      obtain ⟨blocks,built,eqn⟩ := mapM_correspond (newRead := fetch) take complete (by
        rintro c hc ⟨k,hits⟩ found
        have vc := i.certified.localizedRerootChild_valid q c _ frame hc
        have oc := (i.certified.localizedRerootChildren_root_eq q c _ frame hc).trans on
        have keyRead := rank_of (rev := false) (os := []) ready vc oc (rank c hc found)
        change RingRetainedUnitPass.atArm i r c = some k at keyRead
        obtain ⟨sites,computed,same⟩ := ih c hc found vc oc n (by
          have h := i.certified.localizedRerootChild_budget_lt q c _ valid frame hc
          change budget i c < budget i q at h; omega)
        exact ⟨(k,sites),by simp [fetch,keyRead,computed],by simp [take,same]⟩)
      refine ⟨⟨q,[]⟩ :: blocks.flatMap descend,?_,?_⟩
      · change ((kids i q).mapM fetch >>= _) = _
        rw [built]; rfl
      · rw [← eqn]
        have allKids : (blocks.flatMap descend).filterMap (hitOf r) =
            blocks.flatMap (fun b => (take b).2.map (fun h => {h with path := b.1.deep :: h.path})) := by
          rw [List.filterMap_flatMap]
          apply List.flatMap_congr
          intro x _
          exact descend_hits r x.1 x.2
        change _ = (((upper (v.map Prod.fst)).map (Hit.mk [])).toList ++ _)
        rw [List.filterMap_cons,allKids]
        simp only [List.flatMap_map,hitOf,hand,seen]
        have atRoot : upper ((some v).join.map fun p : Labels => if false then p.2 else p.1) = upper (v.map Prod.fst) := rfl
        rw [atRoot]
        cases upper (v.map Prod.fst) <;> rfl

theorem seeds_exact {i f r rev} (ready : @Ready i f r) (a : State i r rev) (on : On f a.q) :
    seeds? i r rev a.q = some (RingRetainedReferenceGroup.references a.profile.hits rev) := by
  obtain ⟨xs,hit,eqn⟩ := inventory_exact ready a.source.hits a.valid on _ (Nat.lt_succ_self _)
  simp [seeds?,hit,eqn,population_exact,RingRetainedReferenceGroup.references]

private theorem unit_projections {a b : Branch} (tie : a.word = b.word) :
    a.stream = b.stream ∧ a.nonterminalStream = b.nonterminalStream := by
  obtain ⟨v,l⟩ := List.cons.inj tie
  have value := (List.cons.inj v).1
  simp [Branch.stream,Branch.nonterminalStream,value,l]

private theorem bits_sign {xs ys : List Bool} (width : xs.length = ys.length) :
    RingSeededPairs.compareBits xs ys = sign (compare xs ys) := RingGroupedRanking.bits_order width

/-- In the single-reference case, dropping unlabelled and lowercase positions
gives exactly the comparison of the two grouped nonterminal queues. -/
theorem single_reference {i f r rev} (ready : @Ready i f r) (a b : State i r rev)
    (oa : On f a.q) (ob : On f b.q) (s t : RS) (tie : a.profile.unit.word = b.profile.unit.word) :
    RingRetainedStereoRefinement.pairSign (a.profile.localPair s) (b.profile.localPair t) =
    sign (compare (RingRetainedStereoDecision.accepted a.profile.unit (a.profile.localPair s))
                  (RingRetainedStereoDecision.accepted b.profile.unit (b.profile.localPair t))) := by
  obtain ⟨xs,hx,vx,ax⟩ := local_slots ready a oa s
  obtain ⟨ys,hy,vy,ay⟩ := local_slots ready b ob t
  obtain ⟨stream,live⟩ := unit_projections tie
  have same := hx.trans ((congrArg (List.map (· == 2)) live).trans hy.symm)
  have len := (RingRetainedSeedFrames.widths s a).2.trans
    ((congrArg (List.count 2) stream).trans (RingRetainedSeedFrames.widths t b).2.symm)
  rw [RingRetainedStereoRefinement.pairSign,← vx,← vy,compact_compare xs ys same,ax,ay,bits_sign len]

theorem fourB_agrees {i f r rev} (ready : @Ready i f r) (a b : State i r rev)
    (oa : On f a.q) (ob : On f b.q) (tie : a.profile.unit.word = b.profile.unit.word) :
    fourB? i r rev a.q b.q = RingRetainedStereoDecision.fourB? a.profile b.profile rev := by
  have width (x : State i r rev) : x.profile.bestPair.length = x.profile.unit.stream.count 2 := by
    rcases max_choice (RingRetainedStereoDecision.accepted x.profile.unit (x.profile.localPair .R))
      (RingRetainedStereoDecision.accepted x.profile.unit (x.profile.localPair .S)) with h | h
    · exact (congrArg List.length h).trans (RingRetainedSeedFrames.widths .R x).2
    · exact (congrArg List.length h).trans (RingRetainedSeedFrames.widths .S x).2
  have dual := bits_sign ((width a).trans ((congrArg (List.count 2) (unit_projections tie).1).trans (width b).symm))
  rcases RingRetainedReferenceGroup.references_cases a.profile.hits rev with l | ⟨s,l⟩ | l <;>
    rcases RingRetainedReferenceGroup.references_cases b.profile.hits rev with h | ⟨t,h⟩ | h <;>
    simp only [fourB?,seeds_exact ready a oa,seeds_exact ready b ob,RingRetainedStereoDecision.fourB?,
      l,h,Option.bind_eq_bind,Option.bind_some,Option.pure_def]
  · simp [pair_words ready a oa,pair_words ready b ob,single_reference ready a b oa ob _ _ tie]
  · simp [pair_words ready a oa,pair_words ready b ob,fourLists_order,RingRetainedStereoDecision.ArmProfile.bestPair,
      RingRetainedStereoDecision.ArmProfile.localPair]
    exact dual.symm

private theorem classes_exact {i f r rev os} (ready : @Ready i f r) (a b : State i r rev)
    (oa : On f a.q) (ob : On f b.q) {x y}
    (l : Derives i r rev os a.q x) (h : Derives i r rev os b.q y) :
    classes? i r rev os a.q b.q = some (RingRetainedUnitPass.signed x y) := by
  simp [classes?,rank_of ready a.valid oa l,rank_of ready b.valid ob h,sign,RingRetainedUnitPass.signed]
  cases compare x.word y.word <;> rfl

theorem decide_agrees {i f r rev} (ready : @Ready i f r) (a b : State i r rev)
    (oa : On f a.q) (ob : On f b.q) :
    decide? i r rev a.q b.q = RingRetainedStereoDecision.decide? a.profile b.profile rev := by
  have unit := classes_exact ready a b oa ob a.source.unit b.source.unit (os := [])
  have lower := classes_exact ready a b oa ob a.source.lower b.source.lower
  by_cases u : RingRetainedUnitPass.signed a.profile.unit b.profile.unit = 0
  · have tie := (RingRetainedUnitPass.signed_zero_iff ..).mp u
    obtain ⟨k,hk⟩ := RingRetainedStereoDecision.fourB_total a.source b.source tie
    have localRead := (fourB_agrees ready a b oa ob tie).trans hk
    by_cases loc : k = 0
    · by_cases low : RingRetainedUnitPass.signed a.profile.lower b.profile.lower = 0
      · have seed (s : RS) := bits_sign ((RingRetainedSeedFrames.widths s a).1.trans
          ((congrArg (List.count 2) (unit_projections tie).1).trans (RingRetainedSeedFrames.widths s b).1.symm))
        have combine (x y : Ordering) : fixedScore x y = CentresRing.PairList.combine (sign x) (sign y) := by
          cases x <;> cases y <;> decide
        simp only [decide?,RingRetainedStereoDecision.decide?,unit,lower,u,hk,localRead,loc,low,
          pair_words ready a oa,pair_words ready b ob,RingRetainedStereoDecision.seedSign,seed,
          RingRetainedStereoDecision.fixedResult,Option.bind_eq_bind,Option.bind_some,Option.pure_def,
          not_true_eq_false,ne_eq,ite_false,ite_true,combine]
      · simp [decide?,RingRetainedStereoDecision.decide?,unit,lower,u,hk,localRead,loc,low]
    · simp [decide?,RingRetainedStereoDecision.decide?,unit,u,hk,localRead,loc]
  · simp [decide?,RingRetainedStereoDecision.decide?,unit,u]

/-- Both geometries run their own visits. A constitutional decision bypasses
the stereo rules; an invalid or inapplicable query has no stereo result. -/
def comparison? (i : Input) (f a b : Site i) (r : Reader i) : Option (Result × Result) := do
  let prior ← RingRetainedChemicalTrace.compareAt? i f a b
  guard (cipTraceOutcome prior == .eq)
  return (← decide? i r false ⟨a,some f⟩ ⟨b,some f⟩,← decide? i r true ⟨a,some f⟩ ⟨b,some f⟩)

theorem comparison_agrees (i : Input) (f a b : Site i) (r : Reader i) (ready : Ready f r) :
    comparison? i f a b r = RingGroupedStereo.comparison? i f a b r := by
  unfold comparison? RingGroupedStereo.comparison?
  cases h : RingRetainedChemicalTrace.compareAt? i f a b with
  | none => rfl
  | some t =>
    by_cases tie : cipTraceOutcome t = .eq
    · have inc := (RingRetainedChemicalTrace.compareAt?_source h).1
      have valid (c : Site i) (adj : i.certified.LocalizedCarrierTreeAdjacent c.val f.val) :
          Valid (⟨c,some f⟩ : Arm i) := (i.certified.mem_localizedRerootNeighborFrames_iff _ _).mpr ⟨c.property,adj⟩
      obtain ⟨x,hx⟩ := RingGroupedStereo.arm_ready ready _ (valid a inc.2.2.1) inc.2.2.1.1
      obtain ⟨y,hy⟩ := RingGroupedStereo.arm_ready ready _ (valid b inc.2.2.2) inc.2.2.2.1
      let l : State i r false := ⟨_,valid a inc.2.2.1,x,RingGroupedStereo.arm_source hx⟩
      let u : State i r false := ⟨_,valid b inc.2.2.2,y,RingGroupedStereo.arm_source hy⟩
      let lr : State i r true := ⟨_,l.valid,x.reflect,l.source.reflect⟩
      let ur : State i r true := ⟨_,u.valid,y.reflect,u.source.reflect⟩
      simpa [tie,hx,hy,l,u,lr,ur] using congrArg₂
        (fun (v w : Option Result) => do return (← v,← w))
        (decide_agrees ready l u inc.2.2.1.1 inc.2.2.2.1)
        (decide_agrees ready lr ur inc.2.2.1.1 inc.2.2.2.1)
    · simp [guard,tie]

/-- On the baseline's actual frozen store no comparison-success, reference,
walk-order or matching-score assumptions are required. -/
theorem frozen_agrees (i : Input) (coords : LocalizedChemicalRing.coordinatesAdmitted i = true) (f a b : Site i) :
    let r := RingActiveDistanceSchedule.frozen (RingGroupedPublication.state i) f
    comparison? i f a b r = RingGroupedStereo.comparison? i f a b r :=
  comparison_agrees i f a b _ (RingGroupedPublication.ready (RingGroupedGeometry.physical coords) f)

/-- All constitutional and stereochemical comparisons at a centre, including
the signed pair used by the casing consumer. The constitutional gate rebuilds
its own branch priorities with zero mass at every ring duplicate. -/
def incidentScore? (i : Input) (f a b : Site i) (r : Reader i) : Option (Int × Int) := do
  match ← RingZeroDuplicateMass.compareAt? i f a b with
  | .lt => return (-1,-1)
  | .gt => return (1,1)
  | .eq =>
    let x ← decide? i r false ⟨a,some f⟩ ⟨b,some f⟩
    let y ← decide? i r true ⟨a,some f⟩ ⟨b,some f⟩
    guard ((x.score,y.score) ∈ RingActivePairs.molecularValues)
    return (x.score,y.score)

theorem incident_agrees (i : Input) (f a b : Site i) (r : Reader i) (ready : Ready f r) :
    incidentScore? i f a b r = RingGroupedCentre.incidentScore? i f a b r := by
  have same := comparison_agrees i f a b r ready
  unfold incidentScore? RingGroupedCentre.incidentScore?
  rw [RingZeroDuplicateMass.compareAt_agrees]
  cases h : RingRetainedChemicalTrace.compareAt? i f a b with
  | none => rfl
  | some p =>
    cases stage : cipTraceOutcome p with
    | lt | gt => simp [stage]
    | eq =>
      unfold RingGroupedStereo.score?
      rw [← same]
      simp [comparison?,h,stage,RingGroupedStereo.scores]
      cases decide? i r false ⟨a,some f⟩ ⟨b,some f⟩ <;>
        cases decide? i r true ⟨a,some f⟩ ⟨b,some f⟩ <;> rfl

/-- Each directed off-diagonal comparison in the four-ligand matrix succeeds
and returns the exact signed pair accepted by the grouped casing consumer. -/
theorem matrix_entry {i : Input} {f : Site i} (fr : RingNestedActivePair.Frame i f)
    (coords : LocalizedChemicalRing.coordinatesAdmitted i = true) (j k : RingActivePairReport.Slot)
    (ne : j ≠ k) :
    let r := RingActiveDistanceSchedule.frozen (RingGroupedPublication.state i) f
    ∃ z, z ∈ RingActivePairs.molecularValues ∧
      incidentScore? i f (fr.direction j).val (fr.direction k).val r = some z ∧
      ∀ arms : RingGroupedCentre.Arms fr r, arms.edge j k = some z := by
  intro r
  have ready := RingGroupedPublication.ready (RingGroupedGeometry.physical coords) f
  obtain ⟨arms,_⟩ := Option.isSome_iff_exists.mp (RingGroupedCentre.arms_ready fr ready)
  obtain ⟨z,allowed,hit,_⟩ := arms.represented j k
  have base := (arms.edge_source j k ne).trans hit
  exact ⟨z,allowed,(incident_agrees i f _ _ r ready).trans base,
    fun other => (other.edge_source j k ne).symm.trans base⟩

end TetraStereo.Engine.RingOccurrenceStereo

assert_kernel_only TetraStereo.Engine.RingOccurrenceStereo.single_reference
assert_kernel_only TetraStereo.Engine.RingOccurrenceStereo.fourB_agrees
assert_kernel_only TetraStereo.Engine.RingOccurrenceStereo.comparison_agrees
assert_kernel_only TetraStereo.Engine.RingOccurrenceStereo.frozen_agrees

assert_kernel_only TetraStereo.Engine.RingOccurrenceStereo.matrix_entry
