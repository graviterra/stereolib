import TetraStereo.Engine.RingGroupedMark
import TetraStereo.Engine.RingRule5Shape

/-! Executable occurrence provenance for the shallow and deep rows of Rule 6.
Rows retain cursors, including repeated visits and ring duplicates. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingMarkedOccurrenceRows
open OneCenter RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingRetainedChemicalTrace (Reaches Word)
open RingRule5Shape (Valid On)

abbrev Layers (i : Input) := List (List (List (Arm i)))
structure Entry (i : Input) where
  cursor : Arm i
  branch : Branch
  levels : Layers i

def paint {i : Input} (atom : Nat) (ls : Layers i) :=
  ls.map (List.map (List.map (RingGroupedMark.bit atom)))

private theorem paint_interleave {i : Input} (atom : Nat) (x y : Layers i) :
    paint atom (RingChildKeyRecovery.interleave x y) =
      RingChildKeyRecovery.interleave (paint atom x) (paint atom y) := by
  induction x generalizing y with
  | nil => rfl
  | cons a xs ih =>
    cases y with
    | nil => simp [RingChildKeyRecovery.interleave,paint]
    | cons b ys =>
      simp only [RingChildKeyRecovery.interleave,paint,List.map_cons,List.map_append]
      exact congrArg (List.cons _) (ih ys)

private theorem paint_forest {i : Input} (atom : Nat) (es : List (Entry i)) :
    paint atom ((es.map Entry.levels).foldr RingChildKeyRecovery.interleave []) =
      ((es.map (fun e => paint atom e.levels)).foldr RingChildKeyRecovery.interleave []) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [List.map_cons,List.foldr_cons,paint_interleave,ih]

private theorem legal_project {α : Type} (f : α → Branch) (key : Branch → List Nat)
    (xs : List α) : Legal key (xs.map f) ((order (fun e => key (f e)) xs).map f) := by
  have h := legal_order (fun e => key (f e)) xs
  exact ⟨h.perm.map f,by simpa only [List.map_map,Function.comp_def] using h.descending⟩

private theorem legal_project_deep {α : Type} (f : α → Branch) (xs : List α) :
    Legal Branch.deep (xs.map f) ((order (fun e => (f e).deep) xs).map f) := by
  have h := legal_order (fun e => (f e).deep) xs
  exact ⟨h.perm.map f,by simpa only [List.map_map,Function.comp_def] using h.descending⟩

def join {i : Input} (atom : Nat) (q : Arm i) (prior : Branch) (cs : List (Entry i)) : Entry i :=
  let sh := order (fun e => e.branch.shallow) cs
  let de := order (fun e => e.branch.deep) cs
  ⟨q,RingRetainedStereoRefinement.extend prior (RingGroupedMark.bit atom q)
      (sh.map Entry.branch) (de.map Entry.branch),
    [sh.map Entry.cursor,de.map Entry.cursor] ::
      (de.map Entry.levels).foldr RingChildKeyRecovery.interleave []⟩

/-- The native earlier stages supply only the prior branch. The marked branch
and its cursor rows are assembled together from the complete child population. -/
def build (i : Input) (r : Reader i) (atom : Nat) : Nat → Arm i → Option (Entry i)
  | 0,_ => none
  | n+1,q => do
    let p ← RingRetainedStereoRefinement.priority i r false [.lowercase] q
    let cs ← (i.certified.executableLocalizedRerootChildren q).mapM (build i r atom n)
    return join atom q p cs

def entry? (i : Input) (r : Reader i) (atom : Nat) (q : Arm i) :=
  build i r atom (i.certified.localizedRerootCursorBudget q + 1) q

/-- The initial singleton is followed by both rows at every parent. -/
def rows? (i : Input) (r : Reader i) (atom : Nat) (q : Arm i) : Option (List (List (Arm i))) :=
  (entry? i r atom q).map fun e => [e.cursor] :: e.levels.flatten

private theorem join_paint {i : Input} (atom : Nat) (q : Arm i) (p : Branch) (cs : List (Entry i))
    (all : ∀ e ∈ cs, paint atom e.levels = e.branch.levels ∧
      RingGroupedMark.bit atom e.cursor = e.branch.value) :
    paint atom (join atom q p cs).levels = (join atom q p cs).branch.levels := by
  have vals (xs : List (Entry i)) (mem : ∀ e ∈ xs, e ∈ cs) :
      (xs.map Entry.cursor).map (RingGroupedMark.bit atom) = (xs.map Entry.branch).map Branch.value := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro e he
    exact (all e (mem e he)).2
  have lv (xs : List (Entry i)) (mem : ∀ e ∈ xs, e ∈ cs) :
      xs.map (fun e => paint atom e.levels) = (xs.map Entry.branch).map Branch.levels := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro e he
    exact (all e (mem e he)).1
  have sh := fun (e : Entry i) (he : e ∈ order (fun e : Entry i => e.branch.shallow) cs) => (legal_order (fun e : Entry i => e.branch.shallow) cs).perm.mem_iff.mp he
  have de := fun (e : Entry i) (he : e ∈ order (fun e : Entry i => e.branch.deep) cs) => (legal_order (fun e : Entry i => e.branch.deep) cs).perm.mem_iff.mp he
  change [((order (fun e : Entry i => e.branch.shallow) cs).map Entry.cursor).map
      (RingGroupedMark.bit atom),
    ((order (fun e : Entry i => e.branch.deep) cs).map Entry.cursor).map
      (RingGroupedMark.bit atom)] :: paint atom
      (((order (fun e : Entry i => e.branch.deep) cs).map Entry.levels).foldr
        RingChildKeyRecovery.interleave []) = _
  rw [vals _ sh,vals _ de,paint_forest,lv _ de]
  rfl

private theorem reading_value {i : Input} {r : Reader i} {atom : Nat} {q : Arm i} {b : Branch}
    (h : RingGroupedMark.Reading i r atom q b) : RingGroupedMark.bit atom q = b.value := by
  cases h
  rfl

private theorem source {i : Input} {r : Reader i} {atom : Nat} :
    ∀ n q e, build i r atom n q = some e → e.cursor = q ∧
      RingGroupedMark.Reading i r atom q e.branch ∧ paint atom e.levels = e.branch.levels := by
  intro n
  induction n with
  | zero => intro q e hit; contradiction
  | succ n ih =>
    intro q e hit
    unfold build at hit
    obtain ⟨p,hp,more⟩ := Option.bind_eq_some_iff.mp hit
    obtain ⟨cs,hcs,out⟩ := Option.bind_eq_some_iff.mp more
    cases Option.some.inj out
    have each (c : Arm i) (hc : c ∈ i.certified.executableLocalizedRerootChildren q)
        (v : Entry i) (hv : build i r atom n c = some v) := ih c v hv
    have child (v : Entry i) (hv : v ∈ cs) :
        RingGroupedMark.Reading i r atom v.cursor v.branch ∧ paint atom v.levels = v.branch.levels := by
      obtain ⟨c,hc,hv'⟩ := RingRetainedUnitPass.forOutput hcs hv
      have h := each c hc v hv'
      exact ⟨by simpa only [h.1] using h.2.1,h.2.2⟩
    have complete : (i.certified.executableLocalizedRerootChildren q).mapM
        (fun c => (build i r atom n c).map Entry.branch) = some (cs.map Entry.branch) :=
      RingGroupedStereo.projected hcs Entry.branch
    have reading : RingGroupedMark.Reading i r atom q (join atom q p cs).branch := by
      apply RingGroupedMark.OnGeometry.node (RingRetainedStereoRefinement.source _ _ hp) _ complete
      · intro c hc b hb
        obtain ⟨v,hv,rfl⟩ := Option.map_eq_some_iff.mp hb
        exact (each c hc v hv).2.1
      · exact legal_project Entry.branch Branch.shallow cs
      · exact legal_project_deep Entry.branch cs
    refine ⟨rfl,reading,join_paint atom q p cs ?_⟩
    intro v hv
    refine ⟨(child v hv).2,?_⟩
    exact reading_value (child v hv).1

private theorem total {atom : Nat} {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r) :
    ∀ n q, Valid q → On f q → i.certified.localizedRerootCursorBudget q < n →
      ∃ e, build i r atom n q = some e := by
  intro n
  induction n with
  | zero => intro q _ _ bound; omega
  | succ n ih =>
    intro q valid on bound
    obtain ⟨p,hp⟩ := RingOccurrenceStereo.rank_total ready false [.lowercase] q valid on
    change RingRetainedStereoRefinement.priority i r false [.lowercase] q = some p at hp
    have frame := i.certified.executableLocalizedRerootChildren_declarative q
    obtain ⟨cs,hcs⟩ := RingRetainedUnitPass.collect _ _ (fun c hc => ih c
      (i.certified.localizedRerootChild_valid _ _ _ frame hc)
      ((i.certified.localizedRerootChildren_root_eq _ _ _ frame hc).trans on)
      (by have := i.certified.localizedRerootChild_budget_lt _ _ _ valid frame hc; omega))
    exact ⟨join atom q p cs,by simp only [build,hp,hcs,Option.bind_eq_bind,Option.bind_some,Option.pure_def]⟩

/-- A successful joint entry carries a native marked reading and its exact
sphere-preserving cursor projection. -/
theorem entry_source {i : Input} {r : Reader i} {atom : Nat} {q : Arm i} {e : Entry i}
    (hit : entry? i r atom q = some e) : e.cursor = q ∧
      RingGroupedMark.Reading i r atom q e.branch ∧ paint atom e.levels = e.branch.levels :=
  source _ q e hit

/-- Painting executable cursor rows gives the public native marked word exactly. -/
theorem rows_exact {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (atom : Nat) (q : Arm i) (valid : Valid q) (on : On f q) :
    (rows? i r atom q).map (List.map (List.map (RingGroupedMark.bit atom))) =
      (RingGroupedMark.arm? i r atom q).map (fun p => p.2.word) := by
  obtain ⟨e,he⟩ := total (atom := atom) ready _ q valid on (Nat.lt_succ_self _)
  obtain ⟨p,hp⟩ := RingGroupedMark.arm_ready ready atom q valid on
  have src := source _ q e he
  have same := RingGroupedMark.Reading.unique src.2.1 (RingGroupedMark.arm_source hp).2
  have value : RingGroupedMark.bit atom e.cursor = e.branch.value := by
    rw [src.1]
    exact reading_value src.2.1
  have flat := congrArg List.flatten src.2.2
  simp only [rows?,entry?,he,hp,Option.map_some]
  apply congrArg some
  simpa only [List.map_cons,List.map_singleton,List.map_nil,List.map_flatten,paint,value,Branch.word,same]
    using congrArg (fun ls => [p.2.value] :: ls) flat

private def Covers {i : Input} (P : Arm i → Prop) (ls : Layers i) : Prop :=
  ∀ group ∈ ls, ∀ row ∈ group, ∀ c ∈ row, P c

private theorem covers_interleave {i : Input} {P : Arm i → Prop} {xs ys : Layers i}
    (a : Covers P xs) (b : Covers P ys) : Covers P (RingChildKeyRecovery.interleave xs ys) := by
  induction xs generalizing ys with
  | nil => exact b
  | cons x xs ih =>
    cases ys with
    | nil => exact a
    | cons y ys =>
      intro group hg row hr c hc
      rcases List.mem_cons.mp hg with rfl | hg
      · rcases List.mem_append.mp hr with hr | hr
        · exact a _ List.mem_cons_self _ hr _ hc
        · exact b _ List.mem_cons_self _ hr _ hc
      · exact ih (fun g h => a g (.tail _ h)) (fun g h => b g (.tail _ h)) _ hg _ hr _ hc

private theorem covers_forest {i : Input} {P : Arm i → Prop} (cs : List (Entry i))
    (all : ∀ e ∈ cs, Covers P e.levels) :
    Covers P ((cs.map Entry.levels).foldr RingChildKeyRecovery.interleave []) := by
  induction cs with
  | nil => intro g h; contradiction
  | cons c cs ih =>
    exact covers_interleave (all c List.mem_cons_self) (ih (fun e h => all e (.tail _ h)))

private theorem reaches_source {i : Input} {r : Reader i} {atom : Nat} :
    ∀ n q e, build i r atom n q = some e →
      Covers (Reaches i q) e.levels := by
  intro n
  induction n with
  | zero => intro q e h; contradiction
  | succ n ih =>
    intro q e hit
    unfold build at hit
    obtain ⟨p,hp,more⟩ := Option.bind_eq_some_iff.mp hit
    obtain ⟨cs,hcs,out⟩ := Option.bind_eq_some_iff.mp more
    cases Option.some.inj out
    have own (v : Entry i) (hv : v ∈ cs) : Reaches i q v.cursor := by
      obtain ⟨c,hc,hv'⟩ := RingRetainedUnitPass.forOutput hcs hv
      rw [(source _ c v hv').1]
      exact .descend hc .here
    have below (v : Entry i) (hv : v ∈ cs) : Covers (Reaches i q) v.levels := by
      obtain ⟨c,hc,hv'⟩ := RingRetainedUnitPass.forOutput hcs hv
      intro group hg row hr t ht
      exact .descend hc (ih c v hv' group hg row hr t ht)
    intro group hg row hr c hc
    change group ∈ _ :: _ at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · have sh := (legal_order (fun e : Entry i => e.branch.shallow) cs).perm
      have de := (legal_order (fun e : Entry i => e.branch.deep) cs).perm
      rcases List.mem_cons.mp hr with rfl | hr
      · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hc
        exact own v (sh.mem_iff.mp hv)
      · have eqn := List.mem_singleton.mp hr
        subst row
        obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hc
        exact own v (de.mem_iff.mp hv)
    · exact covers_forest _ (fun v hv => below v
        ((legal_order (fun e : Entry i => e.branch.deep) cs).perm.mem_iff.mp hv))
        group hg row hr c hc

/-- Every emitted occurrence is reached along actual reroot child edges. -/
theorem rows_reachable {i : Input} {r : Reader i} {atom : Nat} {q : Arm i} {rs}
    (hit : rows? i r atom q = some rs) : ∀ row ∈ rs, ∀ c ∈ row, Reaches i q c := by
  obtain ⟨e,he,out⟩ := Option.map_eq_some_iff.mp hit
  cases out
  intro row hr c hc
  rcases List.mem_cons.mp hr with rfl | hr
  · obtain rfl := List.mem_singleton.mp hc
    rw [(source _ q e he).1]
    exact .here
  · obtain ⟨group,hg,hr⟩ := List.mem_flatten.mp hr
    exact reaches_source _ q e he group hg row hr c hc

/-- Existence requires readiness; provenance soundness above does not. -/
theorem rows_ready {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (atom : Nat) (q : Arm i) (valid : Valid q) (on : On f q) :
    ∃ rs, rows? i r atom q = some rs := by
  obtain ⟨e,he⟩ := total (atom := atom) ready _ q valid on (Nat.lt_succ_self _)
  exact ⟨[e.cursor] :: e.levels.flatten,by simp only [rows?,entry?,he,Option.map_some]⟩

end TetraStereo.Engine.RingMarkedOccurrenceRows

assert_kernel_only TetraStereo.Engine.RingMarkedOccurrenceRows.entry_source
assert_kernel_only TetraStereo.Engine.RingMarkedOccurrenceRows.rows_exact
assert_kernel_only TetraStereo.Engine.RingMarkedOccurrenceRows.rows_reachable
assert_kernel_only TetraStereo.Engine.RingMarkedOccurrenceRows.rows_ready
