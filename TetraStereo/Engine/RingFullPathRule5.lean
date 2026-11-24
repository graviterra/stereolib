import TetraStereo.Engine.RingFullPathPairs

/-! # Rule 5: fixed R and S readings in the global full-path order after Rule 4c
Each edge carries the child's complete through-4c priority (`Derives [.lowercase]`,
no Rule 4b stage) and its like/unlike bit. Jmol `CIPChirality` 1978, 2355–2367, 2403–2437, 2531. -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingFullPathRule5
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingFullPathPairs (Oracle stage likeAt)
open RingRetainedStereoRefinement (priority)

def Word (i : Input) (r : Reader i) (rev : Bool) (seed : RS) (q : Arm i) (w : List Bool) : Prop :=
  (stage i r rev [.lowercase]).Source (likeAt i r rev seed) q w

def word? (i : Input) (r : Reader i) (rev : Bool) (seed : RS) (q : Arm i) : Option (List Bool) :=
  RingFullPathPairs.stageWords i r rev [.lowercase] seed q

/-- A tied R reading gives zero. A strict R reading gives the sign and
magnitude one when S has the same ordering, two otherwise. -/
def score? (i : Input) (r : Reader i) (rev : Bool) (a b : Arm i) : Option Int := do
  let right := compare (← word? i r rev .R a) (← word? i r rev .R b)
  let left := compare (← word? i r rev .S a) (← word? i r rev .S b)
  return RingOccurrenceStereo.fixedScore right left

theorem word_exact {i : Input} {f : Site i} {r : Reader i} (rev : Bool)
    (total : ∀ c : Arm i, i.certified.LocalizedRerootCursorValid c →
      c.occurrence.val.root = f.val.root → ∃ k, priority i r rev [.lowercase] c = some k)
    (seed : RS) (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q)
    (on : q.occurrence.val.root = f.val.root) :
    ∃ w, word? i r rev seed q = some w ∧ ∀ other, Word i r rev seed q other ↔ other = w :=
  (stage i r rev [.lowercase]).source_exact (likeAt i r rev seed) total q valid on

/-- Both fixed seeds, either geometry: the four words exist, every legal source
reading equals them, and the signed score is their fixed-reference comparison. -/
theorem score_exact {i : Input} {f : Site i} {r : Reader i} (rev : Bool)
    (total : ∀ c : Arm i, i.certified.LocalizedRerootCursorValid c →
      c.occurrence.val.root = f.val.root → ∃ k, priority i r rev [.lowercase] c = some k)
    (a b : Arm i) (va : i.certified.LocalizedRerootCursorValid a)
    (vb : i.certified.LocalizedRerootCursorValid b)
    (oa : a.occurrence.val.root = f.val.root) (ob : b.occurrence.val.root = f.val.root) :
    ∃ x y : RS → List Bool,
      (∀ s w, Word i r rev s a w ↔ w = x s) ∧ (∀ s w, Word i r rev s b w ↔ w = y s) ∧
      (∀ s, word? i r rev s a = some (x s)) ∧ (∀ s, word? i r rev s b = some (y s)) ∧
      score? i r rev a b = some (RingOccurrenceStereo.fixedScore
        (compare (x .R) (y .R)) (compare (x .S) (y .S))) := by
  obtain ⟨ar,har,ear⟩ := word_exact rev total .R a va oa
  obtain ⟨aw,has,eas⟩ := word_exact rev total .S a va oa
  obtain ⟨br,hbr,ebr⟩ := word_exact rev total .R b vb ob
  obtain ⟨bs,hbs,ebs⟩ := word_exact rev total .S b vb ob
  refine ⟨fun | .R => ar | .S => aw,fun | .R => br | .S => bs,
    fun | .R => ear | .S => eas,fun | .R => ebr | .S => ebs,
    fun | .R => har | .S => has,fun | .R => hbr | .S => hbs,?_⟩
  simp [score?,har,has,hbr,hbs]

/-- The actual frozen store supplies the through-4c rankings for both words
on every valid arm of the focus. -/
theorem frozen_score {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (f : Site i) (rev : Bool) (a b : Arm i) (va : i.certified.LocalizedRerootCursorValid a)
    (vb : i.certified.LocalizedRerootCursorValid b)
    (oa : a.occurrence.val.root = f.val.root) (ob : b.occurrence.val.root = f.val.root) :
    let r := RingActiveDistanceSchedule.frozen (RingGroupedPublication.state i) f
    ∃ x y : RS → List Bool,
      (∀ s w, Word i r rev s a w ↔ w = x s) ∧ (∀ s w, Word i r rev s b w ↔ w = y s) ∧
      score? i r rev a b = some (RingOccurrenceStereo.fixedScore (compare (x .R) (y .R))
        (compare (x .S) (y .S))) := by
  intro r
  have ready : RingGroupedStereo.Ready f r := RingGroupedPublication.ready (RingGroupedGeometry.physical geom) f
  obtain ⟨x,y,ex,ey,_,_,sc⟩ := score_exact (f := f) rev
    (RingOccurrenceStereo.rank_total ready rev [.lowercase]) a b va vb oa ob
  exact ⟨x,y,ex,ey,sc⟩

private theorem frozen_like {i : Input} (f : Site i) (view : RingActiveDistanceSchedule.View i)
    (ready : RingGroupedStereo.Ready f (RingActiveDistanceSchedule.frozen view f)) (rev : Bool) (s : RS) :
    let r := RingActiveDistanceSchedule.frozen view f
    likeAt i r (!rev) s.swap = likeAt i r rev s := by
  intro r
  funext q
  by_cases onRoot : q.occurrence.val.root = f.val.root
  · obtain ⟨v,hv,ok,_⟩ := ready q onRoot
    change r q.occurrence = some v at hv
    simp only [likeAt,RingFullPathPairs.handAt,hv,Option.join_some]
    cases v with
    | none => rfl
    | some labs =>
      rcases labs with ⟨a,b⟩
      rcases a with a | a <;> rcases b with b | b <;>
        cases a <;> cases b <;> cases s <;> cases rev <;> first | rfl | contradiction
  · have unseen : r q.occurrence = none := if_pos onRoot
    simp [likeAt,RingFullPathPairs.handAt,RingNestedActivePair.upper,unseen]

private theorem trace_of_expansion {α κ : Type} [LinearOrder κ] {key : α → κ}
    {E F : α → List α → Prop} (convert : ∀ a bs, E a bs → F a bs) {row out}
    (h : RingFullPathPairs.FullTrace key E row out) : RingFullPathPairs.FullTrace key F row out := by
  induction h with
  | stop => exact .stop
  | sphere grow legal _ ih => exact .sphere (grow.imp convert) legal ih

/-- Reflection transports every legal global path walk through the reflected
sequence of priority stages, while exchanging the reference. -/
theorem view_mirror_source {i : Input} (f : Site i) (view : RingActiveDistanceSchedule.View i)
    (ready : RingGroupedStereo.Ready f (RingActiveDistanceSchedule.frozen view f)) (rev : Bool) (s : RS) (q : Arm i) (w : List Bool)
    (stages : List RingRetainedStereoRefinement.Observation) :
    let r := RingActiveDistanceSchedule.frozen view f
    (stage i r rev stages).Source (likeAt i r rev s) q w →
    (stage i r (!rev) (stages.map RingRetainedStereoRefinement.Observation.reflect)).Source
      (likeAt i r (!rev) s.swap) q w := by
  intro r h
  unfold Oracle.Source at h ⊢
  rw [frozen_like f view ready rev s]
  obtain ⟨out,walk,eqn⟩ := h
  refine ⟨out,trace_of_expansion (fun parent children expansion => ?_) walk,eqn⟩
  apply List.Forall₂.imp _ expansion
  rintro c v ⟨k,hk,hv⟩
  exact ⟨k,RingRetainedStereoRefinement.mirror stages _ _ hk,hv⟩

theorem mirror_source {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (f : Site i) (rev : Bool) (s : RS) (q : Arm i) (w : List Bool)
    (stages : List RingRetainedStereoRefinement.Observation) :
    let r := RingActiveDistanceSchedule.frozen (RingGroupedPublication.state i) f
    (stage i r rev stages).Source (likeAt i r rev s) q w →
    (stage i r (!rev) (stages.map RingRetainedStereoRefinement.Observation.reflect)).Source
      (likeAt i r (!rev) s.swap) q w :=
  view_mirror_source f _ (RingGroupedPublication.ready (RingGroupedGeometry.physical geom) f) rev s q w stages

theorem mirror_word {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (f : Site i) (rev : Bool) (s : RS) (q : Arm i) (w : List Bool) :
    let r := RingActiveDistanceSchedule.frozen (RingGroupedPublication.state i) f
    Word i r rev s q w → Word i r (!rev) s.swap q w :=
  mirror_source geom f rev s q w [.lowercase]

theorem view_word_swap {i : Input} (f : Site i) (view : RingActiveDistanceSchedule.View i)
    (ready : RingGroupedStereo.Ready f (RingActiveDistanceSchedule.frozen view f)) (rev : Bool) (s : RS) (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q)
    (on : q.occurrence.val.root = f.val.root) :
    let r := RingActiveDistanceSchedule.frozen view f
    word? i r (!rev) s.swap q = word? i r rev s q := by
  intro r
  obtain ⟨w,hw,ew⟩ := word_exact rev (RingOccurrenceStereo.rank_total ready rev [.lowercase]) s q valid on
  obtain ⟨v,hv,ev⟩ := word_exact (!rev) (RingOccurrenceStereo.rank_total ready (!rev) [.lowercase])
    s.swap q valid on
  rw [hw,hv,(ev w).mp (view_mirror_source f view ready rev s q w [.lowercase] ((ew w).mpr rfl))]

theorem frozen_word_swap {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (f : Site i) (rev : Bool) (s : RS) (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q)
    (on : q.occurrence.val.root = f.val.root) :
    let r := RingActiveDistanceSchedule.frozen (RingGroupedPublication.state i) f
    word? i r (!rev) s.swap q = word? i r rev s q :=
  view_word_swap f _ (RingGroupedPublication.ready (RingGroupedGeometry.physical geom) f) rev s q valid on

/-- A one-sided reference tie is exactly a disagreement between the zero
status of the original and reflected signed scores. -/
theorem view_casing {i : Input} (f : Site i) (view : RingActiveDistanceSchedule.View i)
    (ready : RingGroupedStereo.Ready f (RingActiveDistanceSchedule.frozen view f)) (a b : Arm i) (va : i.certified.LocalizedRerootCursorValid a)
    (vb : i.certified.LocalizedRerootCursorValid b)
    (oa : a.occurrence.val.root = f.val.root) (ob : b.occurrence.val.root = f.val.root) :
    let r := RingActiveDistanceSchedule.frozen view f
    ∃ x y : RS → List Bool, (∀ s, word? i r false s a = some (x s)) ∧
      (∀ s, word? i r false s b = some (y s)) ∧
      let cr := compare (x .R) (y .R)
      let cs := compare (x .S) (y .S)
      score? i r false a b = some (RingOccurrenceStereo.fixedScore cr cs) ∧
      score? i r true a b = some (RingOccurrenceStereo.fixedScore cs cr) ∧
      ((score? i r false a b = some 0 ↔ score? i r true a b = some 0) ↔
        (x .R = y .R ↔ x .S = y .S)) := by
  intro r
  obtain ⟨x,y,_,_,left,right,actual⟩ := score_exact false
    (RingOccurrenceStereo.rank_total ready false [.lowercase]) a b va vb oa ob
  change score? i r false a b = _ at actual
  have mirrorA (s : RS) : word? i r true s.swap a = some (x s) :=
    (view_word_swap f view ready false s a va oa).trans (left s)
  have mirrorB (s : RS) : word? i r true s.swap b = some (y s) :=
    (view_word_swap f view ready false s b vb ob).trans (right s)
  have reflected : score? i r true a b = some (RingOccurrenceStereo.fixedScore
      (compare (x .S) (y .S)) (compare (x .R) (y .R))) := by
    simp [score?,show word? i r true .R a = some (x .S) from mirrorA .S,
      show word? i r true .S a = some (x .R) from mirrorA .R,
      show word? i r true .R b = some (y .S) from mirrorB .S,
      show word? i r true .S b = some (y .R) from mirrorB .R]
  have zero (u v : Ordering) : RingOccurrenceStereo.fixedScore u v = 0 ↔ u = .eq := by
    cases u <;> cases v <;> decide
  exact ⟨x,y,left,right,actual,reflected,by simp only [actual,reflected,Option.some.injEq,zero,
    Std.compare_eq_eq_iff_eq]⟩

theorem frozen_casing {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (f : Site i) (a b : Arm i) (va : i.certified.LocalizedRerootCursorValid a)
    (vb : i.certified.LocalizedRerootCursorValid b)
    (oa : a.occurrence.val.root = f.val.root) (ob : b.occurrence.val.root = f.val.root) :
    let r := RingActiveDistanceSchedule.frozen (RingGroupedPublication.state i) f
    ∃ x y : RS → List Bool, (∀ s, word? i r false s a = some (x s)) ∧
      (∀ s, word? i r false s b = some (y s)) ∧
      let cr := compare (x .R) (y .R)
      let cs := compare (x .S) (y .S)
      score? i r false a b = some (RingOccurrenceStereo.fixedScore cr cs) ∧
      score? i r true a b = some (RingOccurrenceStereo.fixedScore cs cr) ∧
      ((score? i r false a b = some 0 ↔ score? i r true a b = some 0) ↔
        (x .R = y .R ↔ x .S = y .S)) :=
  view_casing f _ (RingGroupedPublication.ready (RingGroupedGeometry.physical geom) f) a b va vb oa ob

end TetraStereo.Engine.RingFullPathRule5

assert_kernel_only TetraStereo.Engine.RingFullPathRule5.frozen_score
assert_kernel_only TetraStereo.Engine.RingFullPathRule5.frozen_casing
