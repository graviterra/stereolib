import TetraStereo.Engine.RingOriginStereoRanking
import TetraStereo.Engine.RingGroupedMark

/-! Rule 6 recomputes the recursive unit, lowercase, and selected-atom passes
from the active-origin constitutional keys. Unused reference profiles are omitted. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginMarkWords
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader Labels consistent)
open RingRetainedChemicalTrace (Key key?)
open RingStereoSiblingPass (Branch order)
open RingOriginStereoRanking (recode Shaped)
open RingSingleCycleComparison (CommonOrigin rebuilt)
open private branch_shaped extend_shaped branch_recode recode_extend sort_recode mapM_map from
  TetraStereo.Engine.RingOriginStereoRanking

abbrev Entry := Branch × Branch × Branch
private def unit (e : Entry) := e.1
private def lower (e : Entry) := e.2.1
private def mark (e : Entry) := e.2.2
private def project (e : RingGroupedMark.Entry) : Entry := (e.1.unit,e.1.lower,e.2)
private def change (g : Nat → Nat) (e : Entry) : Entry :=
  (recode g e.1,recode g e.2.1,recode g e.2.2)
private def shaped (e : Entry) : Prop := Shaped e.1 ∧ Shaped e.2.1 ∧ Shaped e.2.2

private def extend (p : Branch) (v : Nat) (cs : List Branch) :=
  RingRetainedStereoRefinement.extend p v (order Branch.shallow cs) (order Branch.deep cs)

private def join {i : Input} (atom : Nat) (q : Arm i) (k : Key) (v : Option Labels)
    (cs : List Entry) : Entry :=
  let u := RingRetainedUnitPass.branch k (RingNestedActivePair.unit (v.map Prod.fst))
    (order Branch.shallow (cs.map unit)) (order Branch.deep (cs.map unit))
  let lo := extend u (RingRetainedStereoRefinement.Observation.lowercase.value v false) (cs.map lower)
  (u,lo,extend lo (RingGroupedMark.bit atom q) (cs.map mark))

/-- Actual molecular recursion, sharing the read/guard/child semantics of the
production marked pass and retaining the three stages that determine its word. -/
def build (i : Input) (read : Reader i) (atom : Nat) (keys : Arm i → Option Key) :
    Nat → Arm i → Option Entry
  | 0,_ => none
  | n+1,q => do
    let v ← read q.occurrence
    let cs := i.certified.executableLocalizedRerootChildren q
    guard (v.all consistent = true ∧ (cs = [] → v = none))
    let k ← keys q
    return join atom q k v (← cs.mapM (build i read atom keys n))

private theorem join_project {i : Input} (atom : Nat) (q : Arm i) (k : Key) (v : Option Labels)
    (cs : List RingGroupedMark.Entry) :
    join atom q k v (cs.map project) = project (RingGroupedMark.join atom q k v cs) := by
  simp only [join,project,RingGroupedMark.join,RingGroupedStereo.assemble,List.map_map,
    Function.comp_def,unit,lower,mark,extend]
  rfl

/-- Projection is exact for every key reader, fuel and failed read. -/
theorem build_project (i : Input) (read : Reader i) (atom : Nat) (keys : Arm i → Option Key)
    (n : Nat) (q : Arm i) :
    build i read atom keys n q =
      (RingGroupedMark.build i read atom keys i.certified.executableLocalizedRerootChildren n q).map project := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    simp only [build,RingGroupedMark.build]
    rw [funext ih,mapM_map]
    cases hv : read q.occurrence with
    | none => rfl
    | some v =>
      by_cases ok : v.all consistent = true ∧
          (i.certified.executableLocalizedRerootChildren q = [] → v = none)
      · have gate : (guard (v.all consistent = true ∧
            (i.certified.executableLocalizedRerootChildren q = [] → v = none)) : Option Unit) = some () := if_pos ok
        simp only [gate,Option.bind_eq_bind,Option.bind_some]
        cases keys q with
        | none => rfl
        | some k =>
          cases (i.certified.executableLocalizedRerootChildren q).mapM
            (RingGroupedMark.build i read atom keys i.certified.executableLocalizedRerootChildren n) with
          | none => rfl
          | some cs => exact congrArg some (join_project atom q k v cs)
      · have gate : (guard (v.all consistent = true ∧
            (i.certified.executableLocalizedRerootChildren q = [] → v = none)) : Option Unit) = none := if_neg ok
        simp [gate]

private theorem join_shaped {i : Input} (atom : Nat) (q : Arm i) (k : Key) (v : Option Labels)
    (cs : List Entry) : shaped (join atom q k v cs) := by
  dsimp [join,shaped]
  have u := branch_shaped k (RingNestedActivePair.unit (v.map Prod.fst))
    (order Branch.shallow (cs.map unit)) (order Branch.deep (cs.map unit))
  have lo := extend_shaped _ u (RingRetainedStereoRefinement.Observation.lowercase.value v false)
    (order Branch.shallow (cs.map lower)) (order Branch.deep (cs.map lower))
  exact ⟨u,lo,extend_shaped _ lo _ _ _⟩

private theorem build_shaped (i : Input) (read : Reader i) (atom : Nat) (keys : Arm i → Option Key) :
    ∀ n q e, build i read atom keys n q = some e → shaped e
  | 0,_,_,h => by contradiction
  | n+1,q,e,h => by
    simp only [build] at h
    obtain ⟨v,hv,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨u,hu,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨k,hk,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨cs,hcs,h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl := Option.some.inj h
    exact join_shaped ..

private theorem join_change {i : Input} (atom : Nat) (q : Arm i) (k : Key) (v : Option Labels)
    (cs : List Entry) {g : Nat → Nat} (hg : StrictMono g) (shape : ∀ e ∈ cs, shaped e) :
    join atom q (RingDuplicateScale.key g k) v (cs.map (change g)) =
      change g (join atom q k v cs) := by
  have shapes (f : Entry → Branch) (h : ∀ e ∈ cs, Shaped (f e)) :
      ∀ b ∈ cs.map f, Shaped b := by
    intro b mem
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp mem
    exact h e he
  obtain ⟨us,ud⟩ := sort_recode hg (cs.map unit) (shapes unit (fun e he => (shape e he).1))
  obtain ⟨ls,ld⟩ := sort_recode hg (cs.map lower) (shapes lower (fun e he => (shape e he).2.1))
  obtain ⟨ms,md⟩ := sort_recode hg (cs.map mark) (shapes mark (fun e he => (shape e he).2.2))
  simp only [join,List.map_map,unit,lower,mark,change,Function.comp_def,extend] at *
  rw [us,ud,branch_recode,ls,ld,recode_extend,ms,md,recode_extend]
  · exact extend_shaped _ (branch_shaped ..) ..
  · exact branch_shaped ..

/-- Raw duplicate recoding passes through both internal sibling sorts at all
three stages. It preserves failures and does not normalize to native keys. -/
theorem build_natural (i : Input) (read : Reader i) (atom : Nat) (keys : Arm i → Option Key)
    {g : Nat → Nat} (hg : StrictMono g) (n : Nat) (q : Arm i) :
    build i read atom (fun c => (keys c).map (RingDuplicateScale.key g)) n q =
      (build i read atom keys n q).map (change g) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    simp only [build]
    rw [funext ih,mapM_map]
    cases hv : read q.occurrence with
    | none => rfl
    | some v =>
      by_cases ok : v.all consistent = true ∧
          (i.certified.executableLocalizedRerootChildren q = [] → v = none)
      · have gate : (guard (v.all consistent = true ∧
            (i.certified.executableLocalizedRerootChildren q = [] → v = none)) : Option Unit) = some () := if_pos ok
        simp only [gate,Option.bind_eq_bind,Option.bind_some]
        cases hk : keys q with
        | none => rfl
        | some k =>
          simp only [Option.map_some,Option.bind_some]
          cases hc : (i.certified.executableLocalizedRerootChildren q).mapM (build i read atom keys n) with
          | none => rfl
          | some cs =>
            have shape : ∀ e ∈ cs, shaped e := by
              intro e mem
              obtain ⟨c,hc,get⟩ := RingRetainedUnitPass.forOutput hc mem
              exact build_shaped i read atom keys n c e get
            exact congrArg some (join_change atom q k v cs hg shape)
      · have gate : (guard (v.all consistent = true ∧
            (i.certified.executableLocalizedRerootChildren q = [] → v = none)) : Option Unit) = none := if_neg ok
        simp [gate]

private theorem build_congr (i : Input) (root : i.certified.Atom) (read : Reader i) (atom : Nat)
    (keys other : Arm i → Option Key)
    (same : ∀ q, q.occurrence.val.root = root → keys q = other q)
    (n : Nat) (q : Arm i) (on : q.occurrence.val.root = root) :
    build i read atom keys n q = build i read atom other n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    simp only [build,same q on]
    have kids : (i.certified.executableLocalizedRerootChildren q).mapM (build i read atom keys n) =
        (i.certified.executableLocalizedRerootChildren q).mapM (build i read atom other n) := by
      apply RingFrameTransport.mapM_congr_mem
      intro c mem
      exact ih c ((i.certified.localizedRerootChildren_root_eq _ _ _
        (i.certified.executableLocalizedRerootChildren_declarative _) mem).trans on)
    rw [kids]

/-- Selected-atom Rule 6 word computed with rebuilt active-focus keys. -/
def word? (i : Input) (focus : Site i) (read : Reader i) (atom : Nat) (q : Arm i) :=
  (build i read atom (rebuilt i focus) (i.certified.localizedRerootCursorBudget q + 1) q).map
    (fun e => e.2.2.word)

/-- The actual marked word, including absence, agrees with production on a
common-origin slice for every selected atom and arbitrary frozen reader. -/
theorem word_exact {i : Input} (focus : Site i) (common : CommonOrigin i focus.val.root)
    (read : Reader i) (atom : Nat) (q : Arm i) (on : q.occurrence.val.root = focus.val.root) :
    word? i focus read atom q = (RingGroupedMark.arm? i read atom q).map (fun e => e.2.word) := by
  obtain ⟨base,a,b,ha,hb,keys⟩ := RingOriginStereoRanking.reader_factorization focus common
  have eqn (v : Nat) (pos : 0 < v) (reader : Arm i → Option Key)
      (same : ∀ c, c.occurrence.val.root = focus.val.root → reader c = (base c).map (RingDuplicateScale.key (· * v))) :
      build i read atom reader (i.certified.localizedRerootCursorBudget q + 1) q =
        (build i read atom base (i.certified.localizedRerootCursorBudget q + 1) q).map (change (· * v)) :=
    (build_congr i focus.val.root read atom _ _ same _ q on).trans
      (build_natural i read atom base (fun _ _ h => Nat.mul_lt_mul_of_pos_right h pos) _ q)
  have orig := eqn a ha _ (fun c h => (keys c h).1)
  have alt := eqn b hb _ (fun c h => (keys c h).2)
  unfold word?
  rw [alt]
  have source := build_project i read atom (key? i) (i.certified.localizedRerootCursorBudget q + 1) q
  rw [orig] at source
  have out := congrArg (fun o : Option Entry => o.map (fun e => e.2.2.word)) source
  simpa only [Option.map_map,Function.comp_def,change,project,recode,RingStereoSiblingPass.Branch.word,
    RingGroupedMark.arm?] using out

end TetraStereo.Engine.RingOriginMarkWords
assert_kernel_only TetraStereo.Engine.RingOriginMarkWords.build_project
assert_kernel_only TetraStereo.Engine.RingOriginMarkWords.build_natural
assert_kernel_only TetraStereo.Engine.RingOriginMarkWords.word_exact
