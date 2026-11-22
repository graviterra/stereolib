import TetraStereo.Engine.RingRetainedConstitution
import TetraStereo.OneCenter.CIPRule2MassData

set_option autoImplicit false

namespace TetraStereo.Engine.RingRetainedChemicalTrace
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingRetainedConstitution (Cursor Incident)

structure Observation where
  atomic : Nat
  duplicate : Nat
  mass : Nat
  deriving DecidableEq, Repr

/-- Zero belongs to every real occurrence, independently of its distance in
the original graph. A closure receives a positive value decreasing with the
original depth of the real occurrence that it duplicates. -/
def duplicateValue (atomCount : Nat) (origin : Option Nat) : Nat :=
  origin.elim 0 (fun d => atomCount+1-d)

theorem closure_above_real (count d : Nat) (bound : d ≤ count) :
    duplicateValue count none < duplicateValue count (some d) := by
  simp only [duplicateValue,Option.elim_none,Option.elim_some]
  omega

theorem nearer_closure (count a b : Nat) (hb : b ≤ count) :
    duplicateValue count (some b) < duplicateValue count (some a) ↔ a < b := by
  simp only [duplicateValue,Option.elim_some]
  omega

/-- Pin the original atom, provenance, terminal status and original origin
before reading its atomic number and normative Rule 2 mass. Real atoms retain
their actual isotope. Duplicates take the ordinary element mass. Missing
entries in the reviewed source table leave this branch unresolved. -/
def observation? (i : Input) {d : Nat} (q : Cursor i.certified d) (terminal : Bool) :
    Option Observation := do
  let node := q.occurrence.val.node
  let a ← node.current?
  let recd ← i.molecule.atoms[a.val]?
  let z := recd.element.atomicNumber
  guard (z > 0)
  match node.provenance with
  | .realAtom =>
    let mass ← CIPRule2MassData.rule2MassPico? z recd.isotope?
    return ⟨z,duplicateValue i.molecule.atomCount none,mass⟩
  | .ringDuplicate origin =>
    guard (terminal && origin ≤ i.molecule.atomCount && node.history.head? == some a &&
      node.history.tail.reverse.idxOf a == origin && node.history.tail.contains a)
    let mass ← CIPRule2MassData.rule2MassPico? z none
    return ⟨z,duplicateValue i.molecule.atomCount (some origin),mass⟩
  | _ => none

/-- The observation of a real atom uses the molecule's isotope record.
Neither its history length nor the direction from which it was entered
contributes a duplicate priority. -/
theorem real_source {i : Input} {d : Nat} {q : Cursor i.certified d} {terminal o}
    (real : q.occurrence.val.node.provenance = .realAtom)
    (hit : observation? i q terminal = some o) :
    o.duplicate = 0 ∧ ∃ a recd, q.occurrence.val.node.current? = some a ∧
      i.molecule.atoms[a.val]? = some recd ∧ o.atomic = recd.element.atomicNumber ∧
      CIPRule2MassData.rule2MassPico? o.atomic recd.isotope? = some o.mass := by
  unfold observation? at hit
  obtain ⟨a,atAtom,tail⟩ := Option.bind_eq_some_iff.mp hit
  obtain ⟨recd,record,tail⟩ := Option.bind_eq_some_iff.mp tail
  obtain ⟨_,_,tail⟩ := Option.bind_eq_some_iff.mp tail
  simp only [real] at tail
  obtain ⟨mass,hm,out⟩ := Option.bind_eq_some_iff.mp tail
  obtain rfl := Option.some.inj out
  exact ⟨rfl,a,recd,atAtom,record,rfl,hm⟩

theorem real_real_tie {i : Input} {d : Nat} {a b : Cursor i.certified d} {x y u v}
    (ar : a.occurrence.val.node.provenance = .realAtom)
    (br : b.occurrence.val.node.provenance = .realAtom)
    (ax : observation? i a x = some u) (by' : observation? i b y = some v) :
    compare u.duplicate v.duplicate = .eq := by
  rw [(real_source ar ax).1,(real_source br by').1]
  rfl

inductive Stage where
  | atomic | duplicate | mass
  deriving DecidableEq

def Observation.atStage (o : Observation) : Stage → Nat
  | .atomic => o.atomic | .duplicate => o.duplicate | .mass => o.mass

private def rulePrefix : Stage → List Stage
  | .atomic => [.atomic]
  | .duplicate => [.atomic,.duplicate]
  | .mass => [.atomic,.duplicate,.mass]

abbrev Word := List (List Nat)

/-- Each entry of a layer is a parent group. The two consecutive rows
compare shallow-sorted children and then children sorted by their complete
earlier-stage priorities. Child count is retained by the row length. -/
structure Column where
  word : Word
  levels : List (List (List Nat))
  deriving DecidableEq, Repr

structure Key where
  root : Observation
  atomic : Column
  duplicate : Column
  mass : Column
  deriving DecidableEq, Repr

def Key.column (k : Key) : Stage → Column
  | .atomic => k.atomic | .duplicate => k.duplicate | .mass => k.mass

private def mergeLayers {α : Type} : List (List α) → List (List α) → List (List α)
  | [],ys => ys
  | xs,[] => xs
  | x::xs,y::ys => (x++y)::mergeLayers xs ys

private def shallow (s : Stage) (k : Key) := (rulePrefix s).map k.root.atStage
private def deep (s : Stage) (k : Key) := (rulePrefix s).map fun t => (k.column t).word

private def byDescending {α κ : Type} [LinearOrder κ] (key : α → κ) (xs : List α) :=
  xs.mergeSort fun x y => decide (key y ≤ key x)

private theorem byDescending_perm {α κ : Type} [LinearOrder κ] (key : α → κ) (xs : List α) :
    (byDescending key xs).Perm xs := List.mergeSort_perm ..

private theorem descending_keys {α κ : Type} [LinearOrder κ] (key : α → κ) (xs : List α) :
    ((byDescending key xs).map key).Pairwise (· ≥ ·) := by
  apply List.pairwise_map.mpr
  have sorted := List.pairwise_mergeSort (le := fun a b : α => decide (key b ≤ key a))
    (fun _ _ _ x y => decide_eq_true (le_trans (of_decide_eq_true y) (of_decide_eq_true x)))
    (fun a b => by simpa using le_total (key b) (key a)) xs
  exact sorted.imp fun h => of_decide_eq_true h

private theorem projection_eq {α κ β : Type} [LinearOrder κ] (key : α → κ) (value : α → β)
    {xs ys : List α} (p : xs.Perm ys)
    (ties : ∀ a ∈ xs, ∀ b ∈ xs, key a = key b → value a = value b) :
    (byDescending key xs).map value = (byDescending key ys).map value := by
  let l := byDescending key xs
  let r := byDescending key ys
  have pl : l.Perm xs := byDescending_perm ..
  have pr : r.Perm ys := byDescending_perm ..
  have both := pl.trans (p.trans pr.symm)
  have aligned : l.map key = r.map key := List.Perm.eq_of_pairwise
    (fun _ _ _ _ ab ba => le_antisymm ba ab)
    (descending_keys key xs) (descending_keys key ys) (both.map key)
  apply List.ext_getElem
  · simp [byDescending,p.length_eq]
  · intro j hj hk
    simp only [List.length_map] at hj hk
    simp only [List.getElem_map]
    apply ties _ (pl.mem_iff.mp (List.getElem_mem hj)) _ (p.mem_iff.mpr (pr.mem_iff.mp (List.getElem_mem hk)))
    have same := List.getElem_of_eq aligned (i := j) (by simpa using hj)
    simpa using same

private def makeColumn (o : Observation) (cs : List Key) (s : Stage) : Column :=
  let a := byDescending (shallow s) cs
  let b := byDescending (deep s) cs
  let row (ks : List Key) := ks.map fun k => k.root.atStage s
  let levels := [row a,row b] :: b.foldr (fun k acc => mergeLayers (k.column s).levels acc) []
  ⟨[o.atStage s] :: levels.flatten, levels⟩

def assemble (o : Observation) (cs : List Key) : Key :=
  ⟨o,makeColumn o cs .atomic,makeColumn o cs .duplicate,makeColumn o cs .mass⟩

private abbrev Layers := List (List (List Nat))
private def nextWidth (row : List (List Nat)) := (row.map List.length).sum

/-- A parent emits two rows. The sum of the lengths of its shallow and deep
rows is twice its child count, exactly the row count at the next distance. -/
def Framed : Nat → Layers → Prop
  | n,[] => n = 0
  | n,row :: tail => 0 < n ∧ row.length = n ∧ Framed (nextWidth row) tail

private theorem framed_merge {x y : Layers} {m n : Nat} (a : Framed m x) (b : Framed n y) :
    Framed (m+n) (mergeLayers x y) := by
  induction x generalizing m n y with
  | nil => obtain rfl := a; simpa [mergeLayers] using b
  | cons row xs ih =>
    cases y with
    | nil => obtain rfl := b; simpa [mergeLayers] using a
    | cons head ys =>
      obtain ⟨ma,hx,tx⟩ := a
      obtain ⟨nb,hy,ty⟩ := b
      exact ⟨by omega,by simp [hx,hy],by simpa [nextWidth] using ih tx ty⟩

/-- Two exhaustive profiles with equal ordered contents have equal boundaries
at every distance. Every individual parent group remains recoverable. -/
theorem Framed.unique {x y : Layers} {n : Nat} (a : Framed n x) (b : Framed n y)
    (flat : x.flatten = y.flatten) : x = y := by
  induction x generalizing n y with
  | nil =>
    cases y with
    | nil => rfl
    | cons row ys => obtain rfl := a; exact False.elim ((Nat.lt_irrefl 0) b.1)
  | cons row xs ih =>
    cases y with
    | nil => obtain rfl := b; exact False.elim ((Nat.lt_irrefl 0) a.1)
    | cons head ys =>
      obtain ⟨_,hx,tx⟩ := a
      obtain ⟨_,hy,ty⟩ := b
      have rows := List.append_inj_left flat (hx.trans hy.symm)
      cases rows
      exact congrArg (List.cons row) (ih tx ty (List.append_cancel_left flat))

def WellFormed (k : Key) : Prop := ∀ s,
  Framed 2 (k.column s).levels ∧ (k.column s).word = [k.root.atStage s] :: (k.column s).levels.flatten

private theorem forest_framed (s : Stage) (cs : List Key)
    (valid : ∀ c ∈ cs, WellFormed c) :
    Framed (2*cs.length) (cs.foldr (fun k acc => mergeLayers (k.column s).levels acc) []) := by
  induction cs with
  | nil => rfl
  | cons k ks ih =>
    have now := ((valid k List.mem_cons_self) s).1
    have below := ih (fun x hx => valid x (List.mem_cons_of_mem _ hx))
    simpa [Nat.mul_add,Nat.add_comm] using framed_merge now below

theorem assemble_framed (o : Observation) (cs : List Key) (valid : ∀ c ∈ cs, WellFormed c) :
    WellFormed (assemble o cs) := by
  intro s
  have atStage : ((assemble o cs).column s) = makeColumn o cs s := by cases s <;> rfl
  rw [atStage]
  refine ⟨⟨by decide,rfl,?_⟩,rfl⟩
  have sorted := byDescending_perm (deep s) cs
  have below := forest_framed s _ (fun x hx => valid x (sorted.mem_iff.mp hx))
  simpa [nextWidth,byDescending,two_mul] using below

private theorem shallow_value {s a b} (h : shallow s a = shallow s b) :
    a.root.atStage s = b.root.atStage s := by
  cases s <;> simp_all [shallow,rulePrefix]

private theorem deep_word {s a b} (h : deep s a = deep s b) :
    (a.column s).word = (b.column s).word := by
  cases s <;> simp_all [deep,rulePrefix]

private theorem observation_rows {s a b} (va : WellFormed a) (vb : WellFormed b)
    (h : deep s a = deep s b) :
    a.root.atStage s = b.root.atStage s ∧ (a.column s).levels = (b.column s).levels := by
  have eqn := deep_word h
  rw [(va s).2,(vb s).2] at eqn
  obtain ⟨localValues,flat⟩ := List.cons.inj eqn
  exact ⟨(List.cons.inj localValues).1,Framed.unique (va s).1 (vb s).1 flat⟩

private theorem makeColumn_perm (o : Observation) {cs ds : List Key}
    (p : cs.Perm ds) (valid : ∀ c ∈ cs, WellFormed c) (s : Stage) :
    makeColumn o cs s = makeColumn o ds s := by
  have sh := projection_eq (shallow s) (fun k => k.root.atStage s) p
    (fun _ _ _ _ eqn => shallow_value eqn)
  have de := projection_eq (deep s) (fun k => k.root.atStage s) p
    (fun a ha b hb eqn => (observation_rows (valid a ha) (valid b hb) eqn).1)
  have lv := projection_eq (deep s) (fun k => (k.column s).levels) p
    (fun a ha b hb eqn => (observation_rows (valid a ha) (valid b hb) eqn).2)
  have rest := congrArg (List.foldr mergeLayers []) lv
  simp only [List.foldr_map] at rest
  dsimp only [makeColumn]
  rw [sh,de,rest]

/-- All three rule-major columns are invariant under permutations of the molecular
children, including ties of complete words and parents of unequal arity. -/
theorem assemble_perm (o : Observation) {cs ds : List Key}
    (p : cs.Perm ds) (valid : ∀ c ∈ cs, WellFormed c) :
    assemble o cs = assemble o ds := by
  unfold assemble
  rw [makeColumn_perm o p valid .atomic, makeColumn_perm o p valid .duplicate,
    makeColumn_perm o p valid .mass]

@[simp] private theorem merge_empty {α : Type} (x : List (List α)) :
    mergeLayers x [] = x := by cases x <;> rfl

private theorem merge_assoc {α : Type} : ∀ (x y z : List (List α)),
    mergeLayers (mergeLayers x y) z = mergeLayers x (mergeLayers y z)
  | [],_,_ => rfl
  | _::_,[],_ => rfl
  | _::_,_::_,[] => by simp
  | a::x,b::y,c::z => by simp only [mergeLayers,List.append_assoc,merge_assoc x y z]

private def forest (s : Stage) (cs : List Key) : Layers :=
  cs.foldr (fun k acc => mergeLayers (k.column s).levels acc) []

private theorem forest_append (s : Stage) (cs ds : List Key) :
    forest s (cs++ds) = mergeLayers (forest s cs) (forest s ds) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change mergeLayers (c.column s).levels (forest s (cs++ds)) =
      mergeLayers (mergeLayers (c.column s).levels (forest s cs)) (forest s ds)
    rw [ih,merge_assoc]

/-- Unread comparison rows of the current distance and the FIFO waiting queue
of children already scheduled for the next distance. -/
def queueRows (s : Stage) (current waiting : List Key) : Word :=
  match forest s current with
  | [] => (forest s waiting).flatten
  | row::below => row ++ (mergeLayers (forest s waiting) below).flatten

theorem queue_rotate (s : Stage) (waiting : List Key) :
    queueRows s [] waiting = queueRows s waiting [] := by
  unfold queueRows
  change (forest s waiting).flatten = _
  cases h : forest s waiting <;> rfl

/-- One FIFO step reads both comparisons of the current parent's child
list, then enqueues the deep-ranked children *behind* all previously
scheduled children. The remaining parent's rows stay at the current
distance. This applies to any queue and every constitutional rule. -/
theorem queue_pop (s : Stage) (o : Observation) (children current waiting : List Key) :
    let ranked := byDescending (deep s) children
    let row (xs : List Key) := xs.map fun k => k.root.atStage s
    queueRows s (assemble o children :: current) waiting =
      [row (byDescending (shallow s) children),row ranked] ++
        queueRows s current (waiting ++ ranked) := by
  dsimp only
  have layout : ((assemble o children).column s).levels =
      [(byDescending (shallow s) children).map (fun k => k.root.atStage s),
       (byDescending (deep s) children).map (fun k => k.root.atStage s)] ::
        forest s (byDescending (deep s) children) := by cases s <;> rfl
  have start : forest s (assemble o children :: current) =
      mergeLayers ((assemble o children).column s).levels (forest s current) := rfl
  unfold queueRows
  rw [start,layout,forest_append]
  cases h : forest s current <;> simp [mergeLayers,merge_assoc]

theorem queue_start (s : Stage) (k : Key) (valid : WellFormed k) :
    (k.column s).word = [k.root.atStage s] :: queueRows s [k] [] := by
  rw [(valid s).2]
  have singleton : forest s [k] = (k.column s).levels := merge_empty _
  unfold queueRows
  rw [singleton]
  cases h : (k.column s).levels <;> rfl

def keyTrace (a b : Key) : List CIPRuleDecision :=
  [⟨.atomicNumber,compare a.atomic.word b.atomic.word⟩,
   ⟨.duplicateAtom,compare a.duplicate.word b.duplicate.word⟩,
   ⟨.isotopeMass,compare a.mass.word b.mass.word⟩]

def compareKeys (a b : Key) : Ordering := cipTraceOutcome (keyTrace a b)

/-- A derivation binds each child key to its directed occurrence in the
declarative retained carrier. The order of the input children is independent
of the ordinal slots constructed separately for each chemical rule. -/
inductive Expansion (i : Input) {d : Nat} : Cursor i.certified d → Key → Prop where
  | node {q children o keys}
      (frame : i.certified.DeclarativeLocalizedRerootChildren q children)
      (observed : observation? i q children.isEmpty = some o)
      (lookup : Cursor i.certified d → Option Key)
      (complete : children.mapM lookup = some keys)
      (branches : ∀ child ∈ children, ∀ {k}, lookup child = some k → Expansion i child k) :
      Expansion i q (assemble o keys)

private def build (i : Input) {d : Nat} (children : Cursor i.certified d → List (Cursor i.certified d)) :
    Nat → Cursor i.certified d → Option Key
  | 0,_ => none
  | n+1,q => do
    let cs := children q
    let root ← observation? i q cs.isEmpty
    let keys ← cs.mapM (build i children n)
    return assemble root keys

private theorem build_source (i : Input) {d : Nat} : ∀ fuel (q : Cursor i.certified d) {k},
    build i i.certified.executableLocalizedRerootChildren fuel q = some k → Expansion i q k
  | 0,_,_,h => by contradiction
  | n+1,q,_,h => by
    change (observation? i q (i.certified.executableLocalizedRerootChildren q).isEmpty >>= _) = some _ at h
    obtain ⟨o,ho,tail⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨keys,hkeys,out⟩ := Option.bind_eq_some_iff.mp tail
    obtain rfl := Option.some.inj out
    exact .node (i.certified.executableLocalizedRerootChildren_declarative q) ho
      (build i i.certified.executableLocalizedRerootChildren n) hkeys (fun child _ _ eq => build_source i n child eq)

def key? (i : Input) {d : Nat} (q : Cursor i.certified d) : Option Key :=
  build i i.certified.executableLocalizedRerootChildren (2*(d+1)+1) q

/-- Reuse a root-slice reader for all constitutional keys in a stereo pass. -/
def keyWith (i : Input) {d : Nat} (reader : i.certified.LocalizedRerootChildReader d)
    (q : Cursor i.certified d) : Option Key :=
  build i (fun x => (reader.readChildren x).getD []) (2*(d+1)+1) q

theorem keyWith_eq (i : Input) {d : Nat} (reader : i.certified.LocalizedRerootChildReader d) :
    keyWith i reader = key? i (d := d) := by
  have same : (fun x => (reader.readChildren x).getD []) = i.certified.executableLocalizedRerootChildren := by
    funext x
    rw [reader.readChildren_eq]
    rfl
  funext q
  simp only [keyWith,key?,same]

/-- The executable child reader materializes one original-root slice for
every subtree of this arm. Its lookup has the same children as the
declarative carrier, including the old parent when it is a retained child. -/
def cachedKey? (i : Input) {d : Nat} (q : Cursor i.certified d) : Option Key :=
  let slice := localizedRerootRootSliceCache (i.certified.localizedRerootCarrierCache d) q.occurrence.val.root
  build i (fun x => (slice.reader.readChildren x).getD []) (2*(d+1)+1) q

set_option maxHeartbeats 900000 in
@[csimp] theorem key_cached : @key? = @cachedKey? := by
  funext i d q
  let slice := localizedRerootRootSliceCache (i.certified.localizedRerootCarrierCache d) q.occurrence.val.root
  have same : (fun x => (slice.reader.readChildren x).getD []) = i.certified.executableLocalizedRerootChildren := by
    funext x
    rw [slice.reader.readChildren_eq]
    rfl
  change build i i.certified.executableLocalizedRerootChildren (2*(d+1)+1) q =
    build i (fun x => (slice.reader.readChildren x).getD []) (2*(d+1)+1) q
  rw [same]

theorem key_source {i : Input} {d : Nat} {q : Cursor i.certified d} {k} (h : key? i q = some k) :
    Expansion i q k := build_source i _ q h

private theorem map_origin {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) {v : β} (mem : v ∈ ys) : ∃ x ∈ xs, f x = some v := by
  induction xs generalizing ys with
  | nil => obtain rfl : [] = ys := Option.some.inj h; contradiction
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    cases hx : f x <;> cases hs : xs.mapM f <;> simp [hx,hs] at h
    subst ys
    rcases List.mem_cons.mp mem with rfl | more
    · exact ⟨x,List.mem_cons_self,hx⟩
    · obtain ⟨a,ha,read⟩ := ih hs more
      exact ⟨a,List.mem_cons_of_mem _ ha,read⟩

theorem Expansion.formed {i : Input} {d : Nat} {q : Cursor i.certified d} {k : Key}
    (e : Expansion i q k) : WellFormed k := by
  induction e with
  | node frame observed lookup complete children ih =>
    apply assemble_framed
    intro child hc
    obtain ⟨c,mem,hit⟩ := map_origin complete hc
    exact ih c mem hit

/-- Reachability follows the actual retained edges. A path may begin
by moving toward the original root and later enter a different branch. -/
inductive Reaches (i : Input) {d : Nat} : Cursor i.certified d → Cursor i.certified d → Prop where
  | here {q} : Reaches i q q
  | descend {q c t} (child : c ∈ i.certified.executableLocalizedRerootChildren q)
      (further : Reaches i c t) : Reaches i q t

private theorem map_covered {α β : Type} {f : α → Option β} (xs : List α) :
    (∃ ys, xs.mapM f = some ys) ↔ ∀ x ∈ xs, ∃ y, f x = some y := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.forall_mem_cons, ← ih]
    cases head : f x <;> cases tail : xs.mapM f <;> simp [List.mapM_cons,head,tail]

private theorem covered_at (i : Input) {d : Nat} : ∀ n (q : Cursor i.certified d),
    i.certified.LocalizedRerootCursorValid q → i.certified.localizedRerootCursorBudget q < n →
    ((∃ k, build i i.certified.executableLocalizedRerootChildren n q = some k) ↔
      ∀ t, Reaches i q t →
        ∃ o, observation? i t (i.certified.executableLocalizedRerootChildren t).isEmpty = some o)
  | 0,_,_,small => by omega
  | n+1,q,valid,small => by
    let cs := i.certified.executableLocalizedRerootChildren q
    have frame := i.certified.executableLocalizedRerootChildren_declarative q
    have step (c) (hc : c ∈ cs) := covered_at i n c
      (i.certified.localizedRerootChild_valid q c cs frame hc)
      (by have h := i.certified.localizedRerootChild_budget_lt q c cs valid frame hc; omega)
    constructor
    · rintro ⟨k,h⟩ t reach
      change (observation? i q cs.isEmpty >>= _) = some k at h
      obtain ⟨o,ho,tail⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨keys,found,_⟩ := Option.bind_eq_some_iff.mp tail
      cases reach with
      | here => exact ⟨o,ho⟩
      | descend child further =>
        exact (step _ child).mp ((map_covered cs).mp ⟨keys,found⟩ _ child) _ further
    · intro observed
      obtain ⟨o,ho⟩ := observed q .here
      have children (c) (hc : c ∈ cs) := (step c hc).mpr
        (fun t below => observed t (.descend hc below))
      obtain ⟨ks,found⟩ := (map_covered cs).mpr children
      dsimp only [cs] at found
      exact ⟨assemble o ks, by simp [build,ho,found]⟩

theorem key_covered_iff (i : Input) {d : Nat} (q : Cursor i.certified d)
    (valid : i.certified.LocalizedRerootCursorValid q) :
    (∃ k, key? i q = some k) ↔ ∀ t, Reaches i q t →
      ∃ o, observation? i t (i.certified.executableLocalizedRerootChildren t).isEmpty = some o :=
  covered_at i _ q valid (Nat.lt_succ_of_le (i.certified.localizedRerootCursorBudget_le_twice q))

def trace? (i : Input) {d : Nat} (a b : Cursor i.certified d) : Option (List CIPRuleDecision) := do
  return keyTrace (← key? i a) (← key? i b)

/-- Internal depth-indexed comparison. The expansion and coverage theorems
are relative to the original carrier at depth `d`. Whole-molecule priority
uses the public entry point at the molecule-wide complete carrier depth. -/
def compareAt? (i : Input) {d : Nat} (focus a b : i.certified.LocalizedCIPOccurrence d) :
    Option (List CIPRuleDecision) :=
  if Incident i.certified focus a b then trace? i ⟨a,some focus⟩ ⟨b,some focus⟩ else none

theorem compareAt?_source {i : Input} {d : Nat} {f a b : i.certified.LocalizedCIPOccurrence d} {t}
    (h : compareAt? i f a b = some t) :
    Incident i.certified f a b ∧ ∃ x y,
      Expansion i ⟨a,some f⟩ x ∧ Expansion i ⟨b,some f⟩ y ∧ t = keyTrace x y := by
  unfold compareAt? at h
  split at h
  next incident =>
    unfold trace? at h
    obtain ⟨x,hx,next⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y,hy,out⟩ := Option.bind_eq_some_iff.mp next
    exact ⟨incident,x,y,key_source hx,key_source hy,(Option.some.inj out).symm⟩
  next => contradiction

end TetraStereo.Engine.RingRetainedChemicalTrace

assert_kernel_only TetraStereo.Engine.RingRetainedChemicalTrace.closure_above_real
assert_kernel_only TetraStereo.Engine.RingRetainedChemicalTrace.nearer_closure
assert_kernel_only TetraStereo.Engine.RingRetainedChemicalTrace.key_cached
assert_kernel_only TetraStereo.Engine.RingRetainedChemicalTrace.key_source
assert_kernel_only TetraStereo.Engine.RingRetainedChemicalTrace.compareAt?_source
assert_kernel_only TetraStereo.Engine.RingRetainedChemicalTrace.real_source
assert_kernel_only TetraStereo.Engine.RingRetainedChemicalTrace.real_real_tie
assert_kernel_only TetraStereo.Engine.RingRetainedChemicalTrace.key_covered_iff
assert_kernel_only TetraStereo.Engine.RingRetainedChemicalTrace.Framed.unique
assert_kernel_only TetraStereo.Engine.RingRetainedChemicalTrace.assemble_framed
assert_kernel_only TetraStereo.Engine.RingRetainedChemicalTrace.assemble_perm
assert_kernel_only TetraStereo.Engine.RingRetainedChemicalTrace.Expansion.formed
assert_kernel_only TetraStereo.Engine.RingRetainedChemicalTrace.queue_rotate
assert_kernel_only TetraStereo.Engine.RingRetainedChemicalTrace.queue_pop
assert_kernel_only TetraStereo.Engine.RingRetainedChemicalTrace.queue_start
