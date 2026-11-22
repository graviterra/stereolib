import TetraStereo.Engine.RingChildKeyRecovery
import TetraStereo.Engine.RingSpherePopulation
import TetraStereo.Engine.RingSphereReadings

set_option autoImplicit false

namespace TetraStereo.Engine.RingSphereKeyShape
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader Visit)
open RingSpherePopulation (children next layers full observe profile?)
open RingRetainedChemicalTrace (Key key? compareAt?)
open RingChildKeyRecovery (childKeys children_tie)
open RingSphereReadings (Profile upperRows)

private abbrev valid (i : Input) (xs : List (Arm i)) :=
  ∀ q ∈ xs, i.certified.LocalizedRerootCursorValid q

private def value (i : Input) (q : Arm i) :=
  (key? i q).getD (RingRetainedChemicalTrace.assemble ⟨0,0,0⟩ [])

private theorem known {i : Input} {q : Arm i} (ok : i.certified.LocalizedRerootCursorValid q) :
    key? i q = some (value i q) := by
  obtain ⟨k,h⟩ := RingRetainedChemicalCoverage.key_total i (RingRetainedChemicalCoverage.admitted_atoms i) q ok
  simp [value,h]

private theorem children_valid (i : Input) (q : Arm i) : valid i (children i q) :=
  fun c hc => i.certified.localizedRerootChild_valid q c _ (i.certified.executableLocalizedRerootChildren_declarative q) hc

private theorem next_valid (i : Input) (qs : List (Arm i)) : valid i (next i qs) := by
  intro c hc
  obtain ⟨q,_,hc⟩ := List.mem_flatMap.mp hc
  exact children_valid i q c hc

private theorem enumerate {i : Input} {qs : List (Arm i)} (ok : valid i qs) :
    qs.filterMap (key? i) = qs.map (value i) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    rw [List.filterMap_cons,known (ok q List.mem_cons_self)]
    exact congrArg _ (ih (fun a ha => ok a (List.mem_cons_of_mem _ ha)))

/-- A representative is used only to prove permutation of the next sphere.
The molecular inverse proves every representative gives the same multiset. -/
private noncomputable def offspring (i : Input) (k : Key) : List Key := by
  classical
  exact if h : ∃ q : Arm i, key? i q = some k then childKeys i h.choose else []

private theorem offspring_perm {i : Input} {q : Arm i} (ok : i.certified.LocalizedRerootCursorValid q) :
    ((children i q).map (value i)).Perm (offspring i (value i q)) := by
  classical
  have h : ∃ a : Arm i, key? i a = some (value i q) := ⟨q,known ok⟩
  rw [offspring,dif_pos h,← enumerate (children_valid i q)]
  exact (children_tie (known ok) h.choose_spec).1

private theorem one_step {i : Input} {qs : List (Arm i)} (ok : valid i qs) :
    ((next i qs).map (value i)).Perm ((qs.map (value i)).flatMap (offspring i)) := by
  simpa only [next,List.map_flatMap,List.flatMap_map,Function.comp_def] using
    List.Perm.flatMap_left qs (fun q hq => offspring_perm (ok q hq))

private theorem degree {i : Input} {read : Reader i} {q : Arm i} {v : Visit} (found : observe i read q = some v) :
    v.children = (children i q).length := by
  unfold observe at found
  obtain ⟨z,_,out⟩ := Option.bind_eq_some_iff.mp found
  unfold RingNestedActivePair.visit at out
  obtain ⟨p,_,out⟩ := Option.bind_eq_some_iff.mp out
  split at out <;> try contradiction
  obtain rfl := Option.some.inj out
  rfl

private theorem row {i : Input} {read : Reader i} {qs : List (Arm i)} {vs : List Visit}
    (ok : valid i qs) (hit : qs.mapM (observe i read) = some vs) :
    vs.map Visit.children = (qs.map (value i)).map (fun k => (offspring i k).length) := by
  induction qs generalizing vs with
  | nil => obtain rfl := Option.some.inj hit; rfl
  | cons q qs ih =>
    rw [List.mapM_cons] at hit
    obtain ⟨v,hv,more⟩ := Option.bind_eq_some_iff.mp hit
    obtain ⟨vs,hs,out⟩ := Option.bind_eq_some_iff.mp more
    obtain rfl := Option.some.inj out
    have size := (offspring_perm (ok q List.mem_cons_self)).length_eq
    exact congrArg₂ List.cons ((degree hv).trans (by simpa only [List.length_map] using size))
      (ih (fun c hc => ok c (List.mem_cons_of_mem _ hc)) hs)

private theorem read_cons {i : Input} {read : Reader i} {qs : List (Arm i)} {ss vs}
    (h : RingSpherePopulation.read? i read (qs::ss) = some vs) :
    ∃ head tail, qs.mapM (observe i read) = some head ∧ RingSpherePopulation.read? i read ss = some tail ∧
      vs = head::tail := by
  rw [RingSpherePopulation.read?,List.mapM_cons] at h
  obtain ⟨r,hr,more⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨t,ht,out⟩ := Option.bind_eq_some_iff.mp more
  exact ⟨r,t,hr,ht,(Option.some.inj out).symm⟩

private theorem spheres {i : Input} {ra rb : Reader i} (n : Nat)
    {qs ts : List (Arm i)} {a b : Profile} (vq : valid i qs) (vt : valid i ts)
    (same : (qs.map (value i)).Perm (ts.map (value i)))
    (left : RingSpherePopulation.read? i ra (layers i n qs) = some a)
    (right : RingSpherePopulation.read? i rb (layers i n ts) = some b) :
    List.Forall₂ List.Perm (a.map (List.map Visit.children)) (b.map (List.map Visit.children)) := by
  induction n generalizing qs ts a b with
  | zero =>
    obtain rfl := Option.some.inj left
    obtain rfl := Option.some.inj right
    exact .nil
  | succ n ih =>
    cases qs with
    | nil =>
      obtain rfl : ts = [] := by simpa using same.symm.eq_nil
      obtain rfl := Option.some.inj left
      obtain rfl := Option.some.inj right
      exact .nil
    | cons q qs =>
      cases ts with
      | nil => have h := same.eq_nil; contradiction
      | cons t ts =>
        obtain ⟨l,ls,hl,hls,rfl⟩ := read_cons left
        obtain ⟨r,rs,hr,hrs,rfl⟩ := read_cons right
        refine .cons (by rw [row vq hl,row vt hr]; exact same.map _) ?_
        exact ih (next_valid i _) (next_valid i _)
          ((one_step vq).trans ((same.flatMap_right _).trans (one_step vt).symm)) hls hrs

/-- Distances can have unrelated sibling orders, arbitrary auxiliary readings and
nonterminal constitutional collisions. The complete two cursor profiles agree
on the multiset of child counts at every distance. -/
theorem sphere_degrees {i : Input} {a b : Arm i} {ra rb : Reader i} {k l r}
    (va : i.certified.LocalizedRerootCursorValid a) (vb : i.certified.LocalizedRerootCursorValid b)
    (ka : key? i a = some k) (kb : key? i b = some k)
    (left : profile? i ra a = some l) (right : profile? i rb b = some r) :
    List.Forall₂ List.Perm (l.map (List.map Visit.children)) (r.map (List.map Visit.children)) := by
  have same : value i a = value i b := by simp [value,ka,kb]
  exact spheres _ (by simpa [valid] using va) (by simpa [valid] using vb)
    (by simp only [List.map_cons,List.map_nil,same]; rfl) left right

private theorem selected {a b : List Visit} (h : (a.map Visit.children).Perm (b.map Visit.children)) :
    a.length = b.length ∧ (a.filter fun v => 0 < v.children).length = (b.filter fun v => 0 < v.children).length := by
  refine ⟨by simpa using h.length_eq,?_⟩
  have p := (h.filter (fun n => 0 < n)).length_eq
  simpa only [List.filter_map,List.length_map] using p

private theorem sizes {a b : Profile}
    (e : List.Forall₂ List.Perm (a.map (List.map Visit.children)) (b.map (List.map Visit.children))) :
    a.map List.length = b.map List.length ∧
      (upperRows a false).map List.length = (upperRows b false).map List.length := by
  rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff] at e
  let live (r : List Visit) := (r.filter fun v => 0 < v.children).length
  have both : a.map List.length = b.map List.length ∧ a.map live = b.map live := by
    induction e with
    | nil => exact ⟨rfl,rfl⟩
    | cons h _ ih =>
      exact ⟨congrArg₂ List.cons (selected h).1 ih.1,congrArg₂ List.cons (selected h).2 ih.2⟩
  refine ⟨both.1,?_⟩
  cases e with
  | nil => rfl
  | cons head tail =>
    simp only [upperRows,List.map_cons,List.map_map,Function.comp_def,List.length_map]
    exact congrArg₂ List.cons (selected head).1 (List.cons.inj both.2).2

/-- The two molecular shape gates of the sphere evaluator follow from the
returned constitutional tie, even with arbitrary previously frozen readers. -/
theorem tie_shape {i : Input} {f a b : Site i} {ra rb : Reader i} {t l r}
    (prior : compareAt? i f a b = some t) (tie : cipTraceOutcome t = .eq)
    (left : profile? i ra ⟨a,some f⟩ = some l) (right : profile? i rb ⟨b,some f⟩ = some r) :
    l.map List.length = r.map List.length ∧
      (upperRows l false).map List.length = (upperRows r false).map List.length := by
  unfold compareAt? at prior
  split at prior <;> try contradiction
  rename_i inc
  unfold RingRetainedChemicalTrace.trace? at prior
  obtain ⟨x,hx,more⟩ := Option.bind_eq_some_iff.mp prior
  obtain ⟨y,hy,out⟩ := Option.bind_eq_some_iff.mp more
  obtain rfl := Option.some.inj out
  change RingRetainedChemicalTrace.compareKeys x y = .eq at tie
  rw [RingRetainedChemicalPreorder.compare_word] at tie
  obtain rfl := RingPairGateCount.key_eq (RingRetainedChemicalTrace.key_source hx).formed
    (RingRetainedChemicalTrace.key_source hy).formed (Std.compare_eq_eq_iff_eq.mp tie)
  have va : i.certified.LocalizedRerootCursorValid ⟨a,some f⟩ :=
    (i.certified.mem_localizedRerootNeighborFrames_iff _ _).mpr ⟨a.property,inc.2.2.1⟩
  have vb : i.certified.LocalizedRerootCursorValid ⟨b,some f⟩ :=
    (i.certified.mem_localizedRerootNeighborFrames_iff _ _).mpr ⟨b.property,inc.2.2.2⟩
  exact sizes (sphere_degrees va vb hx hy left right)

end TetraStereo.Engine.RingSphereKeyShape

assert_kernel_only TetraStereo.Engine.RingSphereKeyShape.sphere_degrees
assert_kernel_only TetraStereo.Engine.RingSphereKeyShape.tie_shape
