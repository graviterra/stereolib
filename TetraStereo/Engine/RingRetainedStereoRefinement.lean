import TetraStereo.Engine.RingRetainedUnitPass

set_option autoImplicit false

namespace TetraStereo.Engine.RingRetainedStereoRefinement
open OneCenter CertifiedLocalizedCIPInput RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader Labels upper lower consistent)
open RingRetainedChemicalTrace (Framed Reaches)

private abbrev children (i : Input) (q : Arm i) := i.certified.executableLocalizedRerootChildren q

/-- A pass is evaluated with a definite geometry and, for a pairing pass, a
definite reference. Reference selection at the comparison root is separate. -/
inductive Observation where
  | pairing (reference : RS)
  | lowercase
  deriving Repr, DecidableEq

def Observation.value (o : Observation) (v : Option Labels) (rev : Bool) : Nat :=
  let label := v.map fun p => if rev then p.2 else p.1
  match o with
  | .pairing seed => ((upper label) == some seed).toNat
  | .lowercase => lower label

/-- A pass inherits the preceding complete shallow and deep priorities. -/
def extend (previous : Branch) (value : Nat) (sh de : List Branch) : Branch :=
  ⟨previous.shallow,previous.deep,value,rows sh de⟩

/-- Evidence for one added pass. Each occurrence has an independently
derived previous key and every child is present in both legal orderings. -/
inductive Pass (i : Input) (prior : Arm i → Branch → Prop) (read : Reader i)
    (obs : Observation) (rev : Bool) : Arm i → Branch → Prop where
  | node {q p v cs sh de} (previous : prior q p)
      (seen : read q.occurrence = some v)
      (lookup : Arm i → Option Branch) (complete : (children i q).mapM lookup = some cs)
      (below : ∀ c ∈ children i q, ∀ {b}, lookup c = some b → Pass i prior read obs rev c b)
      (shallow : Legal Branch.shallow cs sh) (deep : Legal Branch.deep cs de) :
      Pass i prior read obs rev q (extend p (obs.value v rev) sh de)

def build (i : Input) (prior : Arm i → Option Branch) (read : Reader i) (obs : Observation) (rev : Bool) :
    Nat → Arm i → Option Branch
  | 0,_ => none
  | n+1,q => do
    let p ← prior q
    let v ← read q.occurrence
    let cs ← (children i q).mapM (build i prior read obs rev n)
    return extend p (obs.value v rev) (order Branch.shallow cs) (order Branch.deep cs)

theorem build_source {i : Input} {P : Arm i → Branch → Prop} {prior : Arm i → Option Branch}
    (before : ∀ q p, prior q = some p → P q p) (read : Reader i) (obs : Observation) (rev : Bool) :
    ∀ n q {b}, build i prior read obs rev n q = some b → Pass i P read obs rev q b
  | 0,_,_,h => by contradiction
  | n+1,q,_,h => by
    unfold build at h
    obtain ⟨p,hp,t⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v,hv,t⟩ := Option.bind_eq_some_iff.mp t
    obtain ⟨cs,hcs,out⟩ := Option.bind_eq_some_iff.mp t
    obtain rfl := Option.some.inj out
    exact .node (before q p hp) hv _ hcs (fun c _ _ get => build_source before read obs rev n c get)
      (legal_order ..) (legal_order ..)

theorem Pass.framed {i P read obs rev q b} (pass : Pass i P read obs rev q b) : Framed 2 b.levels := by
  induction pass with
  | node _ _ _ found _ sh de ih =>
    apply rows_framed sh.perm de.perm
    intro x hx
    obtain ⟨c,hc,get⟩ := RingRetainedUnitPass.forOutput found hx
    exact ih c hc get

theorem Pass.unique {i P read obs rev q a b}
    (prior : ∀ q x y, P q x → P q y → x = y)
    (l : Pass i P read obs rev q a) (r : Pass i P read obs rev q b) : a = b := by
  induction l generalizing b with
  | node p ha _ ca sub sa da ih =>
    cases r with
    | node p' hb _ cb sub' sb db =>
      obtain rfl := prior _ _ _ p p'
      obtain rfl := Option.some.inj (ha.symm.trans hb)
      obtain rfl := RingRetainedUnitPass.map_same ca cb (fun c hc x y hx hy => ih c hc hx (sub' c hc hy))
      have same := rows_unique sa da sb db (fun x hx => by
        obtain ⟨c,hc,get⟩ := RingRetainedUnitPass.forOutput ca hx
        exact (sub c hc get).framed)
      unfold extend
      rw [same]

/-- Ordered list of sitewise refinements after constitution and Rule 4a.
The reference used in a pairing pass is local to this ligand and geometry. -/
def priority (i : Input) (read : Reader i) (rev : Bool) : List Observation → Arm i → Option Branch
  | [],q => RingRetainedUnitPass.atArm i read q
  | o::earlier,q => build i (priority i read rev earlier) read o rev (i.certified.localizedRerootCursorBudget q + 1) q

def Derives (i : Input) (read : Reader i) (rev : Bool) : List Observation → Arm i → Branch → Prop
  | [] => RingRetainedUnitPass.Reading i read rev
  | o::earlier => Pass i (Derives i read rev earlier) read o rev

theorem source {i read rev} : ∀ stages q {b}, priority i read rev stages q = some b → Derives i read rev stages q b
  | [],_,_,h => RingRetainedUnitPass.source i read rev _ _ h
  | o::earlier,q,_,h => build_source (fun c _ hc => source earlier c hc) read o rev _ q h

theorem unique {i read rev} : ∀ stages q a b, Derives i read rev stages q a → Derives i read rev stages q b → a = b
  | [],_,_,_,h,k => RingRetainedUnitPass.Reading.unique h k
  | _::earlier,_,_,_,h,k => Pass.unique (unique earlier) h k

/-- A witness for the two sorts of the actual children at one occurrence.
Each child retains its own frozen, cumulative priority in the native list
before either permutation is chosen. -/
structure Row (i : Input) (read : Reader i) (rev : Bool) (stages : List Observation)
    (q : Arm i) (parent : Branch) (sh de : List Branch) where
  native : List Branch
  lookup : Arm i → Option Branch
  complete : (children i q).mapM lookup = some native
  derived : ∀ c ∈ children i q, ∀ {b}, lookup c = some b → Derives i read rev stages c b
  shallow : Legal Branch.shallow native sh
  deep : Legal Branch.deep native de
  layout : parent.levels = rows sh de

theorem decomposition {i read rev q b} {stages : List Observation} (h : Derives i read rev stages q b) :
    ∃ sh de, Nonempty (Row i read rev stages q b sh de) := by
  cases stages with
  | nil =>
    obtain ⟨s⟩ := RingRetainedUnitPass.Reading.queue h
    exact ⟨_,_,⟨⟨_,s.lookup,s.complete,s.source,s.first,s.second,s.layout⟩⟩⟩
  | cons o earlier =>
    cases h with
    | node _ _ look found below sh de => exact ⟨_,_,⟨⟨_,look,found,below,sh,de,rfl⟩⟩⟩

def Allowed (i : Input) (read : Reader i) (rev : Bool) (stages : List Observation) (b : Branch)
    (sh de : List Branch) := ∃ q, Derives i read rev stages q b ∧ Nonempty (Row i read rev stages q b sh de)

/-- Every ranked molecular arm admits a complete FIFO walk. All legal walks
emit its same projected stream, retaining the root and each nonterminal
descendant. This applies to either reference on either geometry. -/
theorem walks {i : Input} {read rev stages q b} (valid : i.certified.LocalizedRerootCursorValid q)
    (h : Derives i read rev stages q b) :
    (∃ walk, Visits (Allowed i read rev stages) [b] [] walk) ∧
    ∀ walk, Visits (Allowed i read rev stages) [b] [] walk →
      projected (walk.map Branch.value) (walk.map Branch.degree) = b.nonterminalStream := by
  let good (n : Nat) (a : Branch) := ∃ t : Arm i, i.certified.LocalizedRerootCursorValid t ∧
    i.certified.localizedRerootCursorBudget t < n ∧ Derives i read rev stages t a
  constructor
  · refine visits_exist good (fun _ ⟨_,_,bound,_⟩ => Nat.not_lt_zero _ bound) ?_ (i.certified.localizedRerootCursorBudget q+1) [b] ?_
    · intro n a covered
      obtain ⟨t,vt,bound,src⟩ := covered
      obtain ⟨sh,de,⟨s⟩⟩ := decomposition src
      refine ⟨sh,de,⟨t,src,⟨s⟩⟩,?_⟩
      intro x hx
      obtain ⟨c,hc,get⟩ := RingRetainedUnitPass.forOutput s.complete (s.deep.perm.mem_iff.mp hx)
      have frame := i.certified.executableLocalizedRerootChildren_declarative t
      exact ⟨c,i.certified.localizedRerootChild_valid t c _ frame hc,
        by have := i.certified.localizedRerootChild_budget_lt t c _ vt frame hc; omega,s.derived c hc get⟩
    · intro x hx
      obtain rfl := List.mem_singleton.mp hx
      exact ⟨q,valid,Nat.lt_succ_self _,h⟩
  · intro walk legal
    apply fifo_nonterminal _ legal
    rintro _ _ _ ⟨_,_,⟨s⟩⟩
    exact s.layout

def Observation.reflect : Observation → Observation
  | .pairing seed => .pairing seed.swap
  | .lowercase => .lowercase

theorem Observation.value_reflect (o : Observation) (v : Option Labels) (physical : v.all consistent = true) (rev : Bool) :
    o.reflect.value v (!rev) = o.value v rev := by
  cases o with
  | lowercase =>
    rcases v with _ | ⟨(_|_),(_|_)⟩ <;> cases rev <;> simp_all [reflect,value,consistent,lower]
  | pairing seed =>
    rcases v with _ | ⟨(_|_),(_|_)⟩ <;> cases seed <;> cases rev <;>
      simp_all [reflect,value,consistent,upper,RS.swap]
    all_goals rename_i left right; cases left <;> rfl

private theorem unit_reflect {i read rev q b} (h : RingRetainedUnitPass.Reading i read rev q b) :
    RingRetainedUnitPass.Reading i read (!rev) q b := by
  induction h with
  | @node q k labs cs sh de hk hv ok lookup complete below first second ih =>
    have swap : RingNestedActivePair.unit (labs.map fun p => if !rev then p.2 else p.1) =
        RingNestedActivePair.unit (labs.map fun p => if rev then p.2 else p.1) := by
      have con := ok.1
      cases rev <;> rcases labs with _ | ⟨(_|_),(_|_)⟩ <;> first | rfl | contradiction
    rw [← swap]
    exact .node hk hv ok lookup complete ih first second

theorem physical {i read rev} : ∀ stages q b, Derives i read rev stages q b →
    ∀ v, read q.occurrence = some v → v.all consistent = true
  | [],_,_,d,_,h => by
    cases d with
    | node _ found ok _ _ _ _ _ => obtain rfl := Option.some.inj (found.symm.trans h); exact ok.1
  | _::earlier,_,_,d,v,h => by
    cases d with
    | node prior _ _ _ _ _ _ => exact physical earlier _ _ prior v h

/-- Reflection preserves the full legal sibling keys when every pairing
reference is reflected with the ligand. Lowercase refinements retain their
direction. The two fixed Rule 5 seeds therefore exchange roles. -/
theorem mirror {i read rev} : ∀ stages q b, Derives i read rev stages q b →
    Derives i read (!rev) (stages.map Observation.reflect) q b
  | [],_,_,d => unit_reflect d
  | o::earlier,q,b,d => by
    change Pass i (Derives i read rev earlier) read o rev q b at d
    change Pass i (Derives i read (!rev) (earlier.map Observation.reflect)) read o.reflect (!rev) q b
    induction d with
    | node prior hv lookup complete below sh de ih =>
      rw [← o.value_reflect _ (physical earlier _ _ prior _ hv) rev]
      exact .node (mirror earlier _ _ prior) hv lookup complete ih sh de

/-- Every finite sequence of specified refinements has one complete reading
on the actual frontier, independent of all remaining within-parent orders. -/
theorem frontier {i : Input} {root : i.certified.Atom} {f : Site i}
    (listed : f ∈ RingMolecularSchedule.frontier i root) (rev : Bool) (stages : List Observation)
    (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q) (on : q.occurrence.val.root = f.val.root) :
    let read := RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)
    ∃ b, priority i read rev stages q = some b ∧ ∀ x, Derives i read rev stages q x ↔ x = b := by
  intro read
  suffices ∃ b, priority i read rev stages q = some b by
    obtain ⟨b,h⟩ := this
    exact ⟨b,h,fun x => ⟨fun hx => unique stages q x b hx (source stages q h),fun eqn => eqn ▸ source stages q h⟩⟩
  induction stages generalizing q with
  | nil =>
    obtain ⟨b,h,_⟩ := RingRetainedUnitPass.frontier listed q valid on
    exact ⟨b,h⟩
  | cons o stages ih =>
    suffices ∀ n (t : Arm i), i.certified.LocalizedRerootCursorValid t → t.occurrence.val.root = f.val.root →
        i.certified.localizedRerootCursorBudget t < n →
        ∃ b, build i (priority i read rev stages) read o rev n t = some b from this _ q valid on (Nat.lt_succ_self _)
    intro n
    induction n with
    | zero => intro t _ _ budget; omega
    | succ n below =>
      intro t ht same budget
      obtain ⟨p,hp⟩ := ih t ht same
      obtain ⟨v,hv,_⟩ := RingFrontierProfileShape.frontier_observation listed t same
      change read t.occurrence = some v at hv
      have frame := i.certified.executableLocalizedRerootChildren_declarative t
      obtain ⟨cs,hcs⟩ := RingRetainedUnitPass.collect _ (children i t) (fun c hc =>
        below c (i.certified.localizedRerootChild_valid t c _ frame hc)
          ((i.certified.localizedRerootChildren_root_eq t c _ frame hc).trans same)
          (by have := i.certified.localizedRerootChild_budget_lt t c _ ht frame hc; omega))
      exact ⟨extend p (o.value v rev) (order Branch.shallow cs) (order Branch.deep cs),by simp [build,hp,hv,hcs]⟩

def bits (bs : List Nat) := bs.map (· == 1)

/-- The single-reference pairing comparison uses each ligand's own hand.
A zero continues to the lowercase comparison. -/
def pairSign (x y : Branch) :=
  RingSeededPairs.compareBits (bits x.nonterminalStream) (bits y.nonterminalStream)

theorem bit_signs (a b : List Bool) : RingSeededPairs.compareBits a b ∈ ([-1,0,1] : List Int) := by
  induction a generalizing b with
  | nil => simp [RingSeededPairs.compareBits]
  | cons x xs ih =>
    cases b with
    | nil => simp [RingSeededPairs.compareBits]
    | cons y ys => cases x <;> cases y <;> simp_all [RingSeededPairs.compareBits]

theorem pair_signs (x y : Branch) : pairSign x y ∈ ([-1,0,1] : List Int) := bit_signs ..

/-- Nonterminal FIFO words on a specified side, prior to comparing the
like/unlike status of their corresponding entries. -/
def PairWord (i : Input) (read : Reader i) (rev : Bool) (seed : RS) (q : Arm i) (word : List Bool) : Prop :=
  ∃ b walk, Derives i read rev [.pairing seed] q b ∧ Visits (Allowed i read rev [.pairing seed]) [b] [] walk ∧
    word = bits (projected (walk.map Branch.value) (walk.map Branch.degree))

theorem pair_word_exact {i : Input} {read rev seed q b} (valid : i.certified.LocalizedRerootCursorValid q)
    (src : Derives i read rev [.pairing seed] q b) (word : List Bool) :
    PairWord i read rev seed q word ↔ word = bits b.nonterminalStream := by
  obtain ⟨⟨xs,legal⟩,all⟩ := walks valid src
  constructor
  · rintro ⟨a,ys,other,h,rfl⟩
    obtain rfl := unique _ _ _ _ other src
    rw [all ys h]
  · rintro rfl
    exact ⟨b,xs,src,legal,(congrArg bits (all xs legal)).symm⟩

/-- The signed comparison for a selected single reference on each arm is
the same after reflecting both the labels and the selected hands. Every
allowed walk on either geometry gives the displayed sign. -/
theorem paired_frontier {i : Input} {root : i.certified.Atom} {f : Site i}
    (listed : f ∈ RingMolecularSchedule.frontier i root) (a b : Arm i)
    (va : i.certified.LocalizedRerootCursorValid a) (vb : i.certified.LocalizedRerootCursorValid b)
    (ra : a.occurrence.val.root = f.val.root) (rb : b.occurrence.val.root = f.val.root) (s t : RS) :
    let read := RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)
    ∃ x y, priority i read false [.pairing s] a = some x ∧ priority i read false [.pairing t] b = some y ∧
      ∀ (rev : Bool), let seed (u : RS) := if rev then u.swap else u
        (∃ l, PairWord i read rev (seed s) a l) ∧ (∃ r, PairWord i read rev (seed t) b r) ∧
        ∀ l r, PairWord i read rev (seed s) a l → PairWord i read rev (seed t) b r →
          RingSeededPairs.compareBits l r = pairSign x y := by
  intro read
  obtain ⟨x,left,_⟩ := frontier listed false [.pairing s] a va ra
  obtain ⟨y,right,_⟩ := frontier listed false [.pairing t] b vb rb
  refine ⟨x,y,left,right,?_⟩
  have both {q : Arm i} {u : RS} {z : Branch} (got : priority i read false [.pairing u] q = some z) (rev : Bool) :
      Derives i read rev [.pairing (if rev then u.swap else u)] q z := by
    cases rev
    · exact source _ _ got
    · exact mirror [.pairing u] q z (source _ _ got)
  intro rev
  dsimp only
  have l := pair_word_exact va (both left rev)
  have r := pair_word_exact vb (both right rev)
  exact ⟨⟨_,(l _).mpr rfl⟩,⟨_,(r _).mpr rfl⟩,fun _ _ hx hy => congrArg₂ RingSeededPairs.compareBits ((l _).mp hx) ((r _).mp hy)⟩

end TetraStereo.Engine.RingRetainedStereoRefinement

assert_kernel_only TetraStereo.Engine.RingRetainedStereoRefinement.source
assert_kernel_only TetraStereo.Engine.RingRetainedStereoRefinement.unique
assert_kernel_only TetraStereo.Engine.RingRetainedStereoRefinement.frontier

assert_kernel_only TetraStereo.Engine.RingRetainedStereoRefinement.mirror

assert_kernel_only TetraStereo.Engine.RingRetainedStereoRefinement.walks

assert_kernel_only TetraStereo.Engine.RingRetainedStereoRefinement.paired_frontier
