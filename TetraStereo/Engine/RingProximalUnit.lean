import TetraStereo.Engine.RingAtomicProfileShape
import TetraStereo.Engine.RingMolecularSchedule

set_option autoImplicit false

namespace TetraStereo.Engine.RingProximalUnit
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingNestedActivePair (Reader Labels Visit Walk unit unitWord sourceClass consistent)
open RingRetainedChemicalTrace (compareAt?)

/-- The two incident endpoint classes are ranked before any deeper stereo
observations. A known absence and a missing publication have different types. -/
def gate (a b : Option Labels) (rev : Bool) :=
  let side (x : Option Labels) := x.map fun p => if rev then p.2 else p.1
  Rule4bSparseSource.sourceRule4aGateDecision (sourceClass (side a)) (sourceClass (side b))

def value (o : Ordering) : Int := if o = .gt then 1 else -1

structure Certificate (i : Input) (f a b : Site i) (read : Reader i) where
  trace : List CIPRuleDecision
  earlier : compareAt? i f a b = some trace
  tied : cipTraceOutcome trace = .eq
  left : Option Labels
  right : Option Labels
  leftRead : read a = some left
  rightRead : read b = some right
  available : left.isSome = true ∧ right.isSome = true
  physical : left.all consistent = true ∧ right.all consistent = true
  strict : gate left right false ≠ .eq

private theorem class_mirror (x : Option Labels) (ok : x.all consistent = true) :
    sourceClass (x.map Prod.snd) = sourceClass (x.map Prod.fst) := by
  rcases x with _ | ⟨(_|_),(_|_)⟩ <;> first | rfl | contradiction

theorem Certificate.same_gate {i f a b read} (c : Certificate i f a b read) (rev : Bool) :
    gate c.left c.right rev = gate c.left c.right false := by
  cases rev
  · rfl
  · change Rule4bSparseSource.sourceRule4aGateDecision (sourceClass (c.left.map Prod.snd)) (sourceClass (c.right.map Prod.snd)) = _
    rw [class_mirror _ c.physical.1,class_mirror _ c.physical.2]
    rfl

/-- The early decision is the independent P-92 Rule 4a judgment on the
two published units. Both endpoints have a positive auxiliary descriptor. -/
theorem Certificate.p92 {i f a b read} (c : Certificate i f a b read) (rev : Bool) :
    let side (x : Option Labels) := x.map (fun p => if rev then p.2 else p.1)
    let cls (x : Option Labels) := Rule4bSparseSource.sourceRule4aClassToP92 (sourceClass (side x))
    gate c.left c.right false = BlueBookP92.rule4aDecision (cls c.left) (cls c.right) := by
  dsimp only
  rw [← c.same_gate rev,gate,RingNestedActivePair.unit_pair]
  apply Eq.symm
  apply RingNestedActivePair.unit_p92 <;> simpa only [Option.isSome_map] using
    (by first | exact c.available.1 | exact c.available.2)

/-- Obtain positive or negative unit magnitude directly from the constitutional
trace and the two frozen cells. No descendant stereo profile is requested. -/
def first? (i : Input) (f a b : Site i) (read : Reader i) : Option (Certificate i f a b read) := do
  let ⟨x,hx⟩ ← (read a).attach
  let ⟨y,hy⟩ ← (read b).attach
  if available : x.isSome = true ∧ y.isSome = true then
    if ok : x.all consistent = true ∧ y.all consistent = true then
      if strict : gate x y false ≠ .eq then
        let ⟨t,earlier⟩ ← (compareAt? i f a b).attach
        if tie : cipTraceOutcome t = .eq then return ⟨t,earlier,tie,x,y,hx,hy,available,ok,strict⟩
  none

theorem Certificate.issued {i f a b read} (c : Certificate i f a b read) :
    first? i f a b read = some c := by
  cases c with
  | mk t earlier tied x y left right available physical strict =>
    unfold first?
    rw [Option.attach_eq_some _ ⟨_,left⟩,Option.attach_eq_some _ ⟨_,right⟩]
    simp only [Option.bind_eq_bind,Option.bind_some,dif_pos available,dif_pos physical,dif_pos strict]
    rw [Option.attach_eq_some _ ⟨_,earlier⟩]
    simp only [Option.bind_some,dif_pos tied]
    rfl

theorem first?_complete {i f a b read} (c : Certificate i f a b read) :
    (first? i f a b read).isSome = true := by rw [c.issued]; rfl

private theorem head_unit {i : Input} {read : Reader i} {q : Arm i} {vs labels}
    (w : Walk i read [q] vs) (known : read q.occurrence = some labels) (rev : Bool) :
    ∃ tail, unitWord vs rev = unit (labels.map (fun p => if rev then p.2 else p.1)) :: tail := by
  cases w with
  | layer visits _ =>
    cases visits with
    | cons h t =>
      cases t
      have same := Option.some.inj (h.state.symm.trans known)
      simp [unitWord,Visit.label,same]

/-- Every fully realized comparison gives this early result on both geometries.
The head source judgment is also available when a deeper traversal fails. -/
theorem Certificate.agrees {i f a b read} (c : Certificate i f a b read)
    (p : RingNestedActivePair.Pair i f a b read) (rev : Bool) :
    RingNestedActivePair.decide? p.left p.right rev = some (value (gate c.left c.right false)) := by
  obtain ⟨ls,hl⟩ := head_unit p.source_walks.1 c.leftRead rev
  obtain ⟨rs,hr⟩ := head_unit p.source_walks.2 c.rightRead rev
  have strict : gate c.left c.right rev ≠ .eq := (c.same_gate rev).trans_ne c.strict
  have result := RingNestedActivePair.decide_rule4a_first
    (RingAtomicProfileShape.tie_shape c.earlier c.tied p.leftRead p.rightRead) [] ls rs _ _ hl hr strict
  exact result.trans (congrArg (fun o => some (value o)) (c.same_gate rev))

/-- Direct Rule 4a class visible at the specified original occurrence. An
unknown cell is kept distinct from the class of a certified absence. -/
def observedClass {i : Input} (read : Reader i) (a : Site i) :=
  (read a).map (fun v => unit (v.map Prod.fst))

theorem certificate_iff_classes {i : Input} {f a b : Site i} {read : Reader i} {t x y}
    (prior : compareAt? i f a b = some t) (tie : cipTraceOutcome t = .eq)
    (hx : read a = some x) (hy : read b = some y)
    (available : x.isSome = true ∧ y.isSome = true)
    (ok : x.all consistent = true ∧ y.all consistent = true) :
    Nonempty (Certificate i f a b read) ↔ observedClass read a ≠ observedClass read b := by
  have compare_classes : gate x y false = compare (unit (x.map Prod.fst)) (unit (y.map Prod.fst)) :=
    RingNestedActivePair.unit_pair _ _
  simp only [observedClass,hx,hy,Option.map_some,ne_eq,Option.some.injEq]
  constructor
  · rintro ⟨c⟩ h
    have eqx := Option.some.inj (c.leftRead.symm.trans hx)
    have eqy := Option.some.inj (c.rightRead.symm.trans hy)
    have strict := c.strict
    rw [eqx,eqy,compare_classes,h] at strict
    exact strict (Nat.compare_eq_eq.mpr rfl)
  · intro ne
    exact ⟨⟨t,prior,tie,x,y,hx,hy,available,ok,fun h => ne (Nat.compare_eq_eq.mp (compare_classes.symm.trans h))⟩⟩

/-- One molecular comparison using the supplied frozen reader. The
existing directed evaluator supplies all cases outside the proximal test. -/
def edge? (i : Input) (f a b : Site i) (read : Reader i) : Option (Int × Int) :=
  match first? i f a b read with
  | some c => let v := value (gate c.left c.right false); some (v,v)
  | none => (RingNestedActivePair.edge? i f a b read).map Subtype.val

theorem Certificate.score {i f a b read} (c : Certificate i f a b read) :
    edge? i f a b read = some (value (gate c.left c.right false),value (gate c.left c.right false)) := by
  simp only [edge?,c.issued]

theorem covered_iff {i f a b read} :
    (edge? i f a b read).isSome = true ↔ Nonempty (Certificate i f a b read) ∨
      (RingNestedActivePair.edge? i f a b read).isSome = true := by
  cases h : first? i f a b read with
  | some c => simp [edge?,h,show Nonempty (Certificate i f a b read) from ⟨c⟩]
  | none =>
    have absent : ¬ Nonempty (Certificate i f a b read) := fun ⟨c⟩ => by
      rw [c.issued] at h
      contradiction
    simp [edge?,h,absent]

theorem preserves {i f a b read s} (found : (RingNestedActivePair.edge? i f a b read).map Subtype.val = some s) :
    edge? i f a b read = some s := by
  unfold edge?
  split
  · rename_i c _
    obtain ⟨⟨v,src⟩,_,rfl⟩ := Option.map_eq_some_iff.mp found
    cases src with
    | below prior strict | above prior strict =>
      obtain rfl := Option.some.inj (prior.symm.trans c.earlier)
      rw [c.tied] at strict
      contradiction
    | stereo p =>
      have left := Option.some.inj ((c.agrees p false).symm.trans p.actual)
      have right := Option.some.inj ((c.agrees p true).symm.trans p.reflected)
      exact congrArg some (Prod.ext left right)
  · exact found

end TetraStereo.Engine.RingProximalUnit

assert_kernel_only TetraStereo.Engine.RingProximalUnit.Certificate.same_gate
assert_kernel_only TetraStereo.Engine.RingProximalUnit.Certificate.p92
assert_kernel_only TetraStereo.Engine.RingProximalUnit.first?_complete
assert_kernel_only TetraStereo.Engine.RingProximalUnit.Certificate.agrees
assert_kernel_only TetraStereo.Engine.RingProximalUnit.certificate_iff_classes
assert_kernel_only TetraStereo.Engine.RingProximalUnit.Certificate.score
assert_kernel_only TetraStereo.Engine.RingProximalUnit.covered_iff
assert_kernel_only TetraStereo.Engine.RingProximalUnit.preserves
