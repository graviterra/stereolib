import TetraStereo.Engine.RingStereoSiblingPass

set_option autoImplicit false

namespace TetraStereo.Engine.RingRetainedUnitPass
open OneCenter CertifiedLocalizedCIPInput RingRetainedChemicalTrace RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader Labels consistent unit)

private abbrev children (i : Input) (q : Arm i) := i.certified.executableLocalizedRerootChildren q

/-- Earlier local observations order the shallow pass. The complete constitutional
words order the deep pass. Each row refines its own ties by Rule 4a. -/
def branch (k : Key) (v : Nat) (sh de : List Branch) : Branch :=
  ⟨[k.root.atomic,k.root.duplicate,k.root.mass],RingRetainedChemicalPreorder.orderWord k,v,rows sh de⟩

/-- Derivation from constitutional keys and frozen publications on the original
single-bond carrier supplied by Input.single. Each bond contributes no stereo
label. The two sorted rows can be chosen independently at every occurrence. -/
inductive Reading (i : Input) (read : Reader i) (rev : Bool) : Arm i → Branch → Prop where
  | node {q k labs cs sh de}
      (constitution : key? i q = some k) (seen : read q.occurrence = some labs)
      (physical : labs.all consistent = true ∧ (children i q = [] → labs = none))
      (lookup : Arm i → Option Branch) (complete : (children i q).mapM lookup = some cs)
      (below : ∀ c ∈ children i q, ∀ {b}, lookup c = some b → Reading i read rev c b)
      (shallow : Legal Branch.shallow cs sh) (deep : Legal Branch.deep cs de) :
      Reading i read rev q (branch k (unit (labs.map (fun p => if rev then p.2 else p.1))) sh de)

theorem forOutput {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) {b : β} (hb : b ∈ ys) : ∃ a ∈ xs, f a = some b := by
  have pairs := TerminalTie.mapM_forall₂ _ _ _ h
  clear h
  induction pairs with
  | nil => contradiction
  | cons head _ ih =>
    rcases List.mem_cons.mp hb with rfl | rest
    · exact ⟨_,List.mem_cons_self,head⟩
    · obtain ⟨a,mem,ha⟩ := ih rest
      exact ⟨a,List.mem_cons_of_mem _ mem,ha⟩

theorem Reading.framed {i read rev q b} (h : Reading i read rev q b) : Framed 2 b.levels := by
  induction h with
  | node _ _ _ _ found _ sh de ih =>
    apply rows_framed sh.perm de.perm
    intro x hx
    obtain ⟨c,hc,get⟩ := forOutput found hx
    exact ih c hc get

theorem map_same {α β : Type} {xs : List α} {f g : α → Option β} {as bs}
    (a : xs.mapM f = some as) (b : xs.mapM g = some bs)
    (each : ∀ x ∈ xs, ∀ {u v}, f x = some u → g x = some v → u = v) : as = bs := by
  induction xs generalizing as bs with
  | nil => exact Option.some.inj (a.symm.trans b)
  | cons x xs ih =>
    rw [List.mapM_cons] at a b
    obtain ⟨u,hu,more⟩ := Option.bind_eq_some_iff.mp a
    obtain ⟨us,hus,out⟩ := Option.bind_eq_some_iff.mp more
    obtain ⟨v,hv,more⟩ := Option.bind_eq_some_iff.mp b
    obtain ⟨vs,hvs,out'⟩ := Option.bind_eq_some_iff.mp more
    obtain rfl := Option.some.inj out
    obtain rfl := Option.some.inj out'
    exact congrArg₂ List.cons (each x List.mem_cons_self hu hv)
      (ih hus hvs (fun y hy => each y (List.mem_cons_of_mem _ hy)))

/-- Even a collision between two nonterminal siblings cannot change the unit
reading by exchanging their places in either legal pass. -/
theorem Reading.unique {i read rev q a b} (l : Reading i read rev q a) (r : Reading i read rev q b) : a = b := by
  induction l generalizing b with
  | node ka ha _ _ ca sub sa da ih =>
    cases r with
    | node kb hb _ _ cb sub' sb db =>
      obtain rfl := Option.some.inj (ka.symm.trans kb)
      obtain rfl := Option.some.inj (ha.symm.trans hb)
      obtain rfl := map_same ca cb (fun c hc x y hx hy => ih c hc hx (sub' c hc hy))
      have same := rows_unique sa da sb db (fun x hx => by
        obtain ⟨c,hc,get⟩ := forOutput ca hx
        exact (sub c hc get).framed)
      unfold branch
      rw [same]

def build (i : Input) (read : Reader i) : Nat → Arm i → Option Branch
  | 0,_ => none
  | n+1,q => do
    let k ← key? i q
    let labels ← read q.occurrence
    guard (labels.all consistent = true ∧ (children i q = [] → labels = none))
    let cs ← (children i q).mapM (build i read n)
    return branch k (unit (labels.map Prod.fst)) (order Branch.shallow cs) (order Branch.deep cs)

/-- All cursors in the walk share one reader for the original carrier. -/
private def withReader (i : Input) (read : Reader i) (getKey : Arm i → Option Key)
    (edges : Arm i → List (Arm i)) : Nat → Arm i → Option Branch
  | 0,_ => none
  | n+1,q => do
    let k ← getKey q
    let v ← read q.occurrence
    let kids := edges q
    guard (v.all consistent = true ∧ (kids = [] → v = none))
    let cs ← kids.mapM (withReader i read getKey edges n)
    return branch k (unit (v.map Prod.fst)) (order Branch.shallow cs) (order Branch.deep cs)

private theorem withReader_eq (i : Input) (read : Reader i) (n : Nat) :
    withReader i read (key? i) (children i) n = build i read n := by
  induction n with
  | zero => rfl
  | succ n ih => funext q; simp only [withReader,build,ih]

def cachedBuild (i : Input) (read : Reader i) (n : Nat) (q : Arm i) :=
  let cache := localizedRerootRootSliceCache (i.certified.localizedRerootCarrierCache
    (i.certified.certified.input.molecule.atomCount + 1)) q.occurrence.val.root
  withReader i read (keyWith i cache.reader) (fun c => (cache.reader.readChildren c).getD []) n q

@[csimp] theorem build_cached : @build = @cachedBuild := by
  funext i read n q
  let cache := localizedRerootRootSliceCache (i.certified.localizedRerootCarrierCache
    (i.certified.certified.input.molecule.atomCount + 1)) q.occurrence.val.root
  have same : (fun c : Arm i => (cache.reader.readChildren c).getD []) = children i := by
    funext c; rw [cache.reader.readChildren_eq]; rfl
  change build i read n q = withReader i read (keyWith i cache.reader) _ n q
  rw [keyWith_eq,same,withReader_eq]

private theorem unit_geometry (v : Option Labels) (ok : v.all consistent = true) (rev : Bool) :
    unit (v.map (fun p => if rev then p.2 else p.1)) = unit (v.map Prod.fst) := by
  cases rev <;> rcases v with _ | ⟨(_|_),(_|_)⟩ <;> first | rfl | contradiction

theorem source (i : Input) (read : Reader i) (rev : Bool) : ∀ n q {b}, build i read n q = some b → Reading i read rev q b
  | 0,_,_,h => by contradiction
  | n+1,q,_,h => by
    unfold build at h
    obtain ⟨k,hk,more⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v,hv,more⟩ := Option.bind_eq_some_iff.mp more
    by_cases ok : v.all consistent = true ∧ (children i q = [] → v = none)
    · rw [show (guard (v.all consistent = true ∧ (children i q = [] → v = none)) : Option Unit) = some () from if_pos ok] at more
      simp only [Option.bind_eq_bind,Option.bind_some] at more
      obtain ⟨cs,found,out⟩ := Option.bind_eq_some_iff.mp more
      obtain rfl := Option.some.inj out
      rw [← unit_geometry v ok.1 rev]
      exact .node hk hv ok _ found (fun c _ _ get => source i read rev n c get) (legal_order ..) (legal_order ..)
    · simp [ok] at more

theorem collect {α β : Type} (f : α → Option β) (xs : List α)
    (each : ∀ x ∈ xs, ∃ b, f x = some b) : ∃ ys, xs.mapM f = some ys := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons x xs ih =>
    obtain ⟨b,h⟩ := each x List.mem_cons_self
    obtain ⟨bs,hs⟩ := ih (fun y hy => each y (List.mem_cons_of_mem _ hy))
    exact ⟨b::bs,by simp [List.mapM_cons,h,hs]⟩

abbrev atArm (i : Input) (read : Reader i) (q : Arm i) :=
  build i read (i.certified.localizedRerootCursorBudget q + 1) q

theorem frontier {i : Input} {root : i.certified.Atom} {f : Site i}
    (listed : f ∈ RingMolecularSchedule.frontier i root) (q : Arm i)
    (valid : i.certified.LocalizedRerootCursorValid q) (on : q.occurrence.val.root = f.val.root) :
    let read := RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)
    ∃ b, atArm i read q = some b ∧ ∀ rev, Reading i read rev q b := by
  intro read
  suffices ∀ n (t : Arm i), i.certified.LocalizedRerootCursorValid t → t.occurrence.val.root = f.val.root →
      i.certified.localizedRerootCursorBudget t < n → ∃ b, build i read n t = some b by
    obtain ⟨b,h⟩ := this _ q valid on (Nat.lt_succ_self _)
    exact ⟨b,h,fun rev => source i read rev _ q h⟩
  intro n
  induction n with
  | zero => intro t _ _ budget; omega
  | succ n ih =>
    intro t ht rootEq budget
    obtain ⟨k,hk⟩ := RingRetainedChemicalCoverage.key_total i (RingRetainedChemicalCoverage.admitted_atoms i) t ht
    obtain ⟨v,hv,ok,terminal⟩ := RingFrontierProfileShape.frontier_observation listed t rootEq
    have frame := i.certified.executableLocalizedRerootChildren_declarative t
    obtain ⟨cs,hcs⟩ := collect (build i read n) (children i t) (fun c hc =>
      ih c (i.certified.localizedRerootChild_valid t c _ frame hc)
        ((i.certified.localizedRerootChildren_root_eq t c _ frame hc).trans rootEq)
        (by have := i.certified.localizedRerootChild_budget_lt t c _ ht frame hc; omega))
    change read t.occurrence = some v at hv
    have check : (guard (v.all consistent = true ∧ (children i t = [] → v = none)) : Option Unit) = some () := if_pos ⟨ok,terminal⟩
    exact ⟨branch k (unit (v.map Prod.fst)) (order Branch.shallow cs) (order Branch.deep cs),
      by simp only [build,hk,hv,Option.bind_eq_bind,Option.bind_some,check,hcs,Option.pure_def]⟩

theorem Reading.constitution {i read rev q b} (h : Reading i read rev q b) :
    ∃ k, key? i q = some k ∧ b.priorDeep = RingRetainedChemicalPreorder.orderWord k := by
  cases h with
  | node hk _ _ _ _ _ _ _ => exact ⟨_,hk,rfl⟩

/-- Contents of one parent's queue after both Rule 4a sorts, retaining the
complete key of each child in its deep position. -/
structure Queue (i : Input) (read : Reader i) (rev : Bool) (q : Arm i) (parent : Branch) where
  childrenRead : List Branch
  lookup : Arm i → Option Branch
  complete : (children i q).mapM lookup = some childrenRead
  source : ∀ c ∈ children i q, ∀ {b}, lookup c = some b → Reading i read rev c b
  shallow : List Branch
  deep : List Branch
  first : Legal Branch.shallow childrenRead shallow
  second : Legal Branch.deep childrenRead deep
  layout : parent.levels = rows shallow deep

theorem Reading.queue {i read rev q b} (h : Reading i read rev q b) : Nonempty (Queue i read rev q b) := by
  cases h with
  | node _ _ _ get ok sub sh de => exact ⟨⟨_,get,ok,sub,_,_,sh,de,rfl⟩⟩

private theorem Queue.of_mem {i read rev q b} (s : Queue i read rev q b) {x} (hx : x ∈ s.deep) :
    ∃ c ∈ children i q, Reading i read rev c x := by
  obtain ⟨c,hc,look⟩ := forOutput s.complete (s.second.perm.mem_iff.mp hx)
  exact ⟨c,hc,s.source c hc look⟩

private theorem Queue.previous {i read rev q b} (s : Queue i read rev q b) :
    (s.deep.map Branch.priorDeep).Perm ((RingChildKeyRecovery.childKeys i q).map RingRetainedChemicalPreorder.orderWord) := by
  refine (s.second.perm.map _).trans (List.Perm.of_eq ?_)
  have hs := TerminalTie.mapM_forall₂ _ _ _ s.complete
  have prop := List.forall₂_of_length_eq_of_get (R := fun c x => ∃ k, key? i c = some k ∧
      x.priorDeep = RingRetainedChemicalPreorder.orderWord k) hs.length_eq (fun idx hx hy =>
        (s.source _ (List.get_mem ..) (hs.get hx hy)).constitution)
  change s.childrenRead.map Branch.priorDeep =
    ((children i q).filterMap (key? i)).map RingRetainedChemicalPreorder.orderWord
  generalize children i q = cs at prop ⊢
  generalize s.childrenRead = bs at prop ⊢
  induction prop with
  | nil => rfl
  | cons head _ ih =>
    obtain ⟨k,hk,prior⟩ := head
    simp [hk,prior,ih]

private theorem Queue.earlier_order {i read rev q b} (s : Queue i read rev q b) :
    (s.deep.map Branch.priorDeep).Pairwise (· ≥ ·) := by
  have head (x) (hx : x ∈ s.deep) : x.deep.take 3 = x.priorDeep := by
    obtain ⟨_,_,read⟩ := s.of_mem hx
    obtain ⟨k,_,hk⟩ := read.constitution
    simp [Branch.deep,hk,RingRetainedChemicalPreorder.orderWord]
  apply List.pairwise_map.mpr
  exact (List.pairwise_map.mp s.second.descending).imp_of_mem (fun {x y} hx hy le => by
    simpa only [head x hx,head y hy] using RingChildKeyRecovery.take_le le 3)

/-- Tied constitutional and Rule 4a parents have exactly the same ordered
list of complete child priorities. This gives every tie block and its width
even when siblings exchange places independently in both molecular queues. -/
theorem child_priorities {i j : Input} {q : Arm i} {p : Arm j} {k a b r v g h}
    (left : key? i q = some k) (right : key? j p = some k)
    (x : Queue i r g q a) (y : Queue j v h p b)
    (unitTie : a.word = b.word) : x.deep.map Branch.deep = y.deep.map Branch.deep := by
  have prior := x.previous.trans (((RingChildKeyRecovery.children_tie left right).1.map _).trans y.previous.symm)
  have aligned := List.Perm.eq_of_pairwise (fun _ _ _ _ ab ba => le_antisymm ba ab)
    x.earlier_order y.earlier_order prior
  have forms {i read rev q a} (s : Queue i read rev q a) (x) (hx : x ∈ s.deep) : Framed 2 x.levels := by
    obtain ⟨_,_,src⟩ := s.of_mem hx
    exact src.framed
  have parent (s : Queue i r g q a) : Framed 2 a.levels := s.layout ▸
    rows_framed s.first.perm s.second.perm (fun c hc => forms s c (s.second.perm.mem_iff.mpr hc))
  have rightForm : Framed 2 b.levels := y.layout ▸
    rows_framed y.first.perm y.second.perm (fun c hc => forms y c (y.second.perm.mem_iff.mpr hc))
  have levels := Framed.unique (parent x) rightForm (List.cons.inj unitTie).2
  have words := recover_words (forms x) (forms y) (x.layout.symm.trans (levels.trans y.layout))
  apply List.ext_getElem
  · simpa only [List.length_map] using congrArg List.length aligned
  · intro j hj hk
    simp only [List.length_map] at hj hk
    have p := List.getElem_of_eq aligned (i := j) (by simpa using hj)
    have w := List.getElem_of_eq words (i := j) (by simpa using hj)
    simp only [List.getElem_map] at p w ⊢
    simp only [Branch.deep,p,w]

/-- The first shallow row contains one slot per actual outward child. Its
length recognizes a terminal cursor directly in a complete unit word. -/
def nonterminal (w : Word) := !(w[1]?.getD []).isEmpty

theorem Reading.nonterminal {i read rev q b} (h : Reading i read rev q b) :
    nonterminal b.word = !(children i q).isEmpty := by
  cases h with
  | @node q k labs cs sh de _ _ _ lookup complete _ first _ =>
    have size := (TerminalTie.mapM_forall₂ _ _ _ complete).length_eq
    change (!(sh.map Branch.value).isEmpty) = !(children i q).isEmpty
    have eqn : (sh.map Branch.value).isEmpty = (children i q).isEmpty := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.isEmpty_iff_length_eq_zero,List.length_map,first.perm.length_eq,size]
    rw [eqn]

/-- The nonterminal queue passed to reference selection has identical group
boundaries after projection. Membership is determined by actual outward degree. -/
theorem eligible_priorities {i j : Input} {q : Arm i} {p : Arm j} {k a b r v g h}
    (left : key? i q = some k) (right : key? j p = some k)
    (x : Queue i r g q a) (y : Queue j v h p b) (unitTie : a.word = b.word) :
    ((x.deep.filter fun z => nonterminal z.word).map Branch.deep) =
      ((y.deep.filter fun z => nonterminal z.word).map Branch.deep) := by
  let keep (key : List Word) := nonterminal (key.getLast?.getD [])
  have project (bs : List Branch) :
      (bs.map Branch.deep).filter keep = (bs.filter fun z => nonterminal z.word).map Branch.deep := by
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      have last : keep b.deep = nonterminal b.word := by simp [keep,Branch.deep]
      cases h : nonterminal b.word <;> simp [last,h,ih]
  rw [← project,← project,child_priorities left right x y unitTie]

/-- The signed Rule 4a result. Zero allows the next rule to run. -/
def signed (a b : Branch) : Int :=
  match compare a.word b.word with
  | .lt => -1 | .eq => 0 | .gt => 1

private theorem compare_after {α : Type} [Ord α] [Std.ReflCmp (compare : α → α → Ordering)]
    (pre x y : List α) : compare (pre ++ x) (pre ++ y) = compare x y := by
  induction pre with
  | nil => rfl
  | cons h hs ih => simpa only [List.cons_append,List.compare_cons_cons,Std.ReflCmp.compare_self,Ordering.eq_then] using ih

/-- The first unequal slot of the first unequal parent row gives the signed
magnitude directly from the molecular unit-class comparison. -/
theorem first_unit {a b : Branch} {before : Word} {row restA restB : List Nat} {tailA tailB : Word}
    (x y : Option LocalizedAuxiliaryLabel)
    (left : a.word = before ++ (row ++ unit x :: restA) :: tailA)
    (right : b.word = before ++ (row ++ unit y :: restB) :: tailB)
    (strict : Rule4bSparseSource.sourceRule4aGateDecision (RingNestedActivePair.sourceClass x)
      (RingNestedActivePair.sourceClass y) ≠ .eq) :
    signed a b = if Rule4bSparseSource.sourceRule4aGateDecision (RingNestedActivePair.sourceClass x)
        (RingNestedActivePair.sourceClass y) = .gt then 1 else -1 := by
  rw [RingNestedActivePair.unit_pair] at strict ⊢
  unfold signed
  rw [left,right,compare_after,List.compare_cons_cons,compare_after,List.compare_cons_cons]
  cases h : compare (unit x) (unit y) <;> simp_all

theorem signed_zero_iff (a b : Branch) : signed a b = 0 ↔ a.word = b.word := by
  unfold signed
  rw [← Std.compare_eq_eq_iff_eq (a := a.word) (b := b.word)]
  cases compare a.word b.word <;> decide

/-- A constitutional tie is required before requesting the Rule 4a comparison. -/
def compareUnit? (i : Input) (f a b : Site i) (read : Reader i) : Option Int := do
  let t ← compareAt? i f a b
  guard (cipTraceOutcome t == .eq)
  return signed (← atArm i read ⟨a,some f⟩) (← atArm i read ⟨b,some f⟩)

/-- Every reachable constitutional tie has one signed Rule 4a outcome on both
geometries. Every pair of independently chosen admissible passes gives it. -/
theorem frontier_comparison {i : Input} {root : i.certified.Atom} {f a b : Site i} {t}
    (listed : f ∈ RingMolecularSchedule.frontier i root)
    (prior : compareAt? i f a b = some t) (tie : cipTraceOutcome t = .eq) :
    let read := RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)
    ∃ x y, (∀ rev, Reading i read rev ⟨a,some f⟩ x ∧ Reading i read rev ⟨b,some f⟩ y) ∧
      compareUnit? i f a b read = some (signed x y) ∧
      ∀ rev u v, Reading i read rev ⟨a,some f⟩ u → Reading i read rev ⟨b,some f⟩ v →
        signed u v = signed x y := by
  intro read
  have inc := (compareAt?_source prior).1
  have arm (q : Site i) (adj : i.certified.LocalizedCarrierTreeAdjacent q.val f.val) :=
    frontier listed (⟨q,some f⟩ : Arm i)
      ((i.certified.mem_localizedRerootNeighborFrames_iff _ _).mpr ⟨q.property,adj⟩) adj.1
  obtain ⟨x,hx,sx⟩ := arm a inc.2.2.1
  obtain ⟨y,hy,sy⟩ := arm b inc.2.2.2
  change atArm i read _ = some x at hx
  change atArm i read _ = some y at hy
  exact ⟨x,y,fun rev => ⟨sx rev,sy rev⟩,by simp [compareUnit?,prior,tie,hx,hy],
    fun rev _ _ left right => congrArg₂ signed (left.unique (sx rev)) (right.unique (sy rev))⟩

end TetraStereo.Engine.RingRetainedUnitPass

assert_kernel_only TetraStereo.Engine.RingRetainedUnitPass.Reading.unique
assert_kernel_only TetraStereo.Engine.RingRetainedUnitPass.frontier

assert_kernel_only TetraStereo.Engine.RingRetainedUnitPass.frontier_comparison
assert_kernel_only TetraStereo.Engine.RingRetainedUnitPass.signed_zero_iff

assert_kernel_only TetraStereo.Engine.RingRetainedUnitPass.child_priorities


assert_kernel_only TetraStereo.Engine.RingRetainedUnitPass.Reading.nonterminal
assert_kernel_only TetraStereo.Engine.RingRetainedUnitPass.eligible_priorities

assert_kernel_only TetraStereo.Engine.RingRetainedUnitPass.build_cached

assert_kernel_only TetraStereo.Engine.RingRetainedUnitPass.first_unit
