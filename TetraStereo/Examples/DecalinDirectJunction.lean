import TetraStereo.Examples.DecalinAuxiliary
import TetraStereo.Examples.DecalinLigandOrder
import TetraStereo.Examples.DecalinAuxiliaryInventory

/-! The two outward methylene arms at the directly reached decalin junction
have the same complete decorated tree for every assignment of the long-route
labels. This is a statement about the independently expanded retained graph. -/
set_option autoImplicit false
namespace TetraStereo.Examples.DecalinDirectJunction
open DecalinAuxiliary (History next z)
open DecalinAuxiliaryInventory (routes)
open Engine OneCenter

private def swap (p : History) := p.map DecalinPathSwap.exchange

private def origin (h : History) : Option Nat :=
  match h with
  | [] => none
  | a::t => if a ∈ t then some (t.reverse.idxOf a) else none

/-- Match every child, including duplicate leaves, under exchange of both paths.
A successful certificate ends at leaves and excludes all three donor histories. -/
private def aligned (r : Nat) : Nat → History → History → Bool
  | 0,_,_ => false
  | n+1,p,h =>
    decide (z h = z (swap h) ∧ origin h = origin (swap h) ∧
      h ∉ routes r ∧ swap h ∉ routes r ∧
      ((next p h).map swap).Perm (next (swap p) (swap h))) &&
    (next p h).all (aligned r n h)

def direct (r : Fin 2) : History := [1-r.val,r.val]
def left (r : Fin 2) : History := (if r.val = 0 then 3 else 2) :: direct r
def right (r : Fin 2) : History := (if r.val = 0 then 8 else 6) :: direct r

private theorem aligned_arms : ∀ r : Fin 2,
    swap (direct r) = direct r ∧ swap (left r) = right r ∧
      aligned r.val 10 (direct r) (left r) = true := by decide +kernel

/-- An arbitrary bottom-up reading that depends on the chemical observation
and the multiset of child readings. Labels at the three donor paths can differ. -/
def fold {α β : Type} (r : Nat) (label : History → α) (blank : α)
    (read : Nat → Option Nat → α → Multiset β → β) : Nat → History → History → β
  | 0,_,h => read (z h) (origin h) (if h ∈ routes r then label h else blank) 0
  | n+1,p,h => read (z h) (origin h) (if h ∈ routes r then label h else blank)
      ((next p h).map (fold r label blank read n h))

private theorem aligned_fold {r n : Nat} {p h : History} (ok : aligned r n p h = true)
    {α β : Type} (lab : History → α) (blank : α) (read : Nat → Option Nat → α → Multiset β → β)
    (fuel : Nat) :
    fold r lab blank read fuel p h = fold r lab blank read fuel (swap p) (swap h) := by
  induction fuel generalizing n p h with
  | zero =>
    cases n with
    | zero => contradiction
    | succ n =>
      obtain ⟨hz,ho,l,r',_⟩ := of_decide_eq_true (Bool.and_eq_true_iff.mp ok).1
      simp only [fold,if_neg l,if_neg r',hz,ho]
  | succ fuel ih =>
    cases n with
    | zero => contradiction
    | succ n =>
      obtain ⟨head,all⟩ := Bool.and_eq_true_iff.mp ok
      obtain ⟨hz,ho,l,r',perm⟩ := of_decide_eq_true head
      simp only [fold,if_neg l,if_neg r',hz,ho]
      congr 1
      apply Quot.sound
      apply List.Perm.trans _ (perm.map (fold _ lab blank read fuel (swap h)))
      rw [List.map_map]
      apply List.Perm.of_eq
      exact List.map_congr_left (fun child mem => ih ((List.all_eq_true.mp all) child mem))

theorem direct_tie {α β : Type} (r : Fin 2) (lab : History → α) (blank : α)
    (read : Nat → Option Nat → α → Multiset β → β) (fuel : Nat) :
    fold r.val lab blank read fuel (direct r) (left r) =
      fold r.val lab blank read fuel (direct r) (right r) := by
  obtain ⟨parent,arm,cert⟩ := aligned_arms r
  simpa only [parent,arm] using aligned_fold cert lab blank read fuel

open Engine.LocalizedChemicalRing (Input)
open Engine.RingActivePairs (Arm Site)
open Engine.RingActiveDistanceSchedule (frozen)
open DecalinAuxiliary (history child_histories)
open DecalinLigandOrder (Descendant)
open RingFullPathPairs (Oracle FullVisit)
open private projected block_paths from TetraStereo.Examples.DecalinLigandOrder

/-- The four outgoing directions at the directly reached junction. -/
def direction (r : Fin 2) (k : Fin 4) : History :=
  match k.val with
  | 0 => [r.val]
  | 1 => left r
  | 2 => right r
  | _ => (11-r.val) :: direct r

def classOf (k : Fin 4) : Nat := if k.val = 0 then 2 else if k.val = 3 then 0 else 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem ordinal_table : ∀ r : Fin 2,
    let words := (List.finRange 4).map fun k => (DecalinAuxiliary.key 15 (direct r) (direction r k)).atomic.word
    (∀ k : Fin 4, DecalinAuxiliary.closed 15 (direct r) (direction r k) = true) ∧
    ∀ a b : Fin 4, compare (words[a.val]?.getD []) (words[b.val]?.getD []) =
      compare (classOf a) (classOf b) := by decide +kernel

open private cursorKey from TetraStereo.Engine.RingAtomicProfileShape
open private project from TetraStereo.Engine.RingAtomicMetricIndependence

/-- All sixteen native Rule 1a comparisons at the direct junction. The
rootward carbon is first, the two methylene directions tie, and H is last. -/
theorem atomic_comparison {i : Input} (graph : i.molecule = DecalinFrames.molecule)
    (r : Fin 2) (p : Site i) (focus : history p = direct r)
    (a b : Fin 4) (x y : Arm i) (px : x.previous? = some p) (py : y.previous? = some p)
    (vx : i.certified.LocalizedRerootCursorValid x) (vy : i.certified.LocalizedRerootCursorValid y)
    (hx : history x.occurrence = direction r a) (hy : history y.occurrence = direction r b) :
    compare (cursorKey i x).atomic.word (cursorKey i y).atomic.word =
      compare (classOf a) (classOf b) := by
  obtain ⟨done,table⟩ := ordinal_table r
  have row (k : Fin 4) (q : Arm i) (prev : q.previous? = some p)
      (valid : i.certified.LocalizedRerootCursorValid q) (h : history q.occurrence = direction r k) :
      (cursorKey i q).atomic.word = (DecalinAuxiliary.key 15 (direct r) (direction r k)).atomic.word := by
    have same := DecalinAuxiliary.key_correspondence graph 15 q p prev valid (by
      rw [focus,h]; exact done k)
    simpa only [project,focus,h] using congrArg (fun t : Nat × RingRetainedChemicalTrace.Column => t.2.word) same
  rw [row a x px vx hx,row b y py vy hy]
  simpa using table a b

private def quiet (r : Nat) : Nat → History → History → Bool
  | 0,_,_ => false
  | n+1,p,h => !(routes r).contains h && (next p h).all (quiet r n h)

private theorem quiet_arms : ∀ r : Fin 2,
    quiet r.val 10 (direct r) (left r) = true ∧ quiet r.val 10 (direct r) (right r) = true := by
  decide +kernel

private def Inside {i : Input} (r : Nat) (q : Arm i) : Prop :=
  ∃ p : Site i, ∃ n, q.previous? = some p ∧ i.certified.LocalizedRerootCursorValid q ∧
    quiet r n (history p) (history q.occurrence) = true

private theorem inside_child {i : Input} (graph : i.molecule = DecalinFrames.molecule)
    {r : Nat} {q c : Arm i} (parent : Inside r q)
    (edge : c ∈ i.certified.executableLocalizedRerootChildren q) : Inside r c := by
  obtain ⟨p,n,prev,valid,ok⟩ := parent
  cases n with
  | zero => contradiction
  | succ n =>
    have projected := child_histories graph q p prev valid
    have mem := projected.mem_iff.mp (List.mem_map_of_mem edge)
    have frame := (i.certified.localizedRerootChildren?_eq_some_iff _ _).mp
      (i.certified.localizedRerootChildren?_eq_some_executable q)
    exact ⟨q.occurrence,n,i.certified.executableLocalizedRerootChildren_previous _ _ edge,
      i.certified.localizedRerootChild_valid _ _ _ frame edge,
      List.all_eq_true.mp (Bool.and_eq_true_iff.mp ok).2 _ mem⟩

private theorem inside_off {i : Input} {r : Nat} {q : Arm i} (ok : Inside r q) :
    history q.occurrence ∉ routes r := by
  obtain ⟨p,n,_,_,pass⟩ := ok
  cases n with
  | zero => contradiction
  | succ n => simpa using (Bool.and_eq_true_iff.mp pass).1

private theorem walk_inside {i : Input} (graph : i.molecule = DecalinFrames.molecule)
    (o : Oracle i) (bit : Arm i → Option Bool) (r : Nat)
    {xs out : List (FullVisit i)} (walk : o.Walk bit xs out)
    (initial : ∀ x ∈ xs, Inside r x.cursor) : ∀ x ∈ out, Inside r x.cursor := by
  induction walk with
  | stop => simp
  | sphere expand sorted _ ih =>
    have child (x : FullVisit i) (hx : Inside r x.cursor) (ys : List (FullVisit i))
        (rel : o.Expansion bit x ys) :
        (ys.map FullVisit.cursor).Perm (i.certified.executableLocalizedRerootChildren x.cursor) ∧
          ∀ y ∈ ys, Inside r y.cursor := by
      have eq := projected o bit rel
      refine ⟨List.Perm.of_eq eq,?_⟩
      intro y hy
      apply inside_child graph hx
      have mem : y.cursor ∈ ys.map FullVisit.cursor := List.mem_map_of_mem hy
      rw [eq] at mem
      exact mem
    have domain := (block_paths expand initial child).2
    exact fun x hx => (List.mem_append.mp hx).elim (initial x)
      (ih (fun y hy => domain y (sorted.perm.mem_iff.mp hy)) x)

/-- The actual public frozen reader has no emitting occurrence on either
outward arm of the direct junction. Every native Rule 4b and Rule 5 seed scan
therefore yields the empty word on both geometries, for any earlier stage list. -/
theorem empty_stage {i : Input} (graph : i.molecule = DecalinFrames.molecule)
    (ok : LocalizedChemicalRing.coordinatesAdmitted i = true) (f : Site i) (r : Fin 2)
    (root : f.val.root.val = r.val) (focus : history f = direct r) (q : Arm i)
    (prev : q.previous? = some f) (valid : i.certified.LocalizedRerootCursorValid q)
    (onRoot : q.occurrence.val.root = f.val.root)
    (side : history q.occurrence = left r ∨ history q.occurrence = right r)
    (rev : Bool) (stages : List RingRetainedStereoRefinement.Observation) (seed : RS) :
    RingFullPathPairs.stageWords i (frozen (RingChemicalGraphProof.state i) f) rev stages seed q = some [] := by
  let read := frozen (RingChemicalGraphProof.state i) f
  let bit := RingFullPathPairs.likeAt i read rev seed
  let o := RingFullPathPairs.stage i read rev stages
  have start : Inside r.val q := by
    refine ⟨f,10,prev,valid,?_⟩
    rw [focus]
    exact side.elim (fun e => e ▸ (quiet_arms r).1) (fun e => e ▸ (quiet_arms r).2)
  have empty (c : Arm i) (inside : Inside r.val c) : bit c = none := by
    have rr : f.val.root.val < 2 := root ▸ r.isLt
    have rr' := DecalinAuxiliaryInventory.reader graph ok rr f rfl
    have off := inside_off inside
    change DecalinAuxiliaryInventory.history c.occurrence ∉ routes r.val at off
    simp only [bit,RingFullPathPairs.likeAt,RingFullPathPairs.handAt,read,rr']
    unfold frozen
    split_ifs <;> simp_all [RingNestedActivePair.upper]
  have ready := RingChemicalGraphProof.ready ok f
  obtain ⟨w,hit,unique⟩ := o.source_exact (f := f) bit (RingOccurrenceStereo.rank_total ready rev stages)
    q valid onRoot
  obtain ⟨out,walk,word⟩ := (unique w).mpr rfl
  have domain := walk_inside graph o bit r.val walk (by simpa using start)
  have none : out.filterMap (fun x => bit x.cursor) = [] :=
    List.filterMap_eq_nil_iff.mpr (fun x hx => empty _ (domain x hx))
  exact hit.trans (congrArg some (word.trans none))

end TetraStereo.Examples.DecalinDirectJunction
assert_kernel_only TetraStereo.Examples.DecalinDirectJunction.direct_tie
assert_kernel_only TetraStereo.Examples.DecalinDirectJunction.empty_stage
assert_kernel_only TetraStereo.Examples.DecalinDirectJunction.atomic_comparison
