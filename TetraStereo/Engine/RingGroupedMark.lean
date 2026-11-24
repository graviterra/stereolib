import TetraStereo.Engine.RingGroupedCentre

set_option autoImplicit false

namespace TetraStereo.Engine.RingGroupedMark
open OneCenter CertifiedLocalizedCIPInput RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader consistent)
open RingRetainedStereoRefinement (extend Derives)
open RingRetainedStereoDecision (ArmProfile Reads)
open RingRetainedChemicalTrace (Key key?)
private abbrev children (i : Input) (q : Arm i) := i.certified.executableLocalizedRerootChildren q

/-- Every occurrence of the selected ligand atom, including a ring duplicate,
receives the Rule 6 preference. Frozen auxiliaries are shared by all trials. -/
def bit {i : Input} (atom : Nat) (q : Arm i) := (q.occurrence.val.node.current?.map Fin.val == some atom).toNat

/-- Below the comparison root, the unseeded pair rules add no hand preference.
The marked pass extends the complete through-4c priorities at each parent. -/
inductive OnGeometry (i : Input) (read : Reader i) (rev : Bool) (atom : Nat) : Arm i → Branch → Prop where
  | node {q prior cs sh de} (before : Derives i read rev [.lowercase] q prior)
      (lookup : Arm i → Option Branch) (complete : (children i q).mapM lookup = some cs)
      (below : ∀ c ∈ children i q, ∀ {v}, lookup c = some v → OnGeometry i read rev atom c v)
      (first : Legal Branch.shallow cs sh) (deep : Legal Branch.deep cs de) :
      OnGeometry i read rev atom q (extend prior (bit atom q) sh de)

theorem OnGeometry.framed {i read rev atom q p} (a : OnGeometry i read rev atom q p) : RingRetainedChemicalTrace.Framed 2 p.levels := by
  induction a with
  | node _ _ found _ sh de ih =>
    apply rows_framed sh.perm de.perm
    intro x hx
    obtain ⟨c,hc,get⟩ := RingRetainedUnitPass.forOutput found hx
    exact ih c hc get

theorem OnGeometry.unique {i read rev atom q p v} (a : OnGeometry i read rev atom q p) (b : OnGeometry i read rev atom q v) : p = v := by
  induction a generalizing v with
  | node p _ ca sub sa da ih =>
    cases b with
    | node p' _ cb sub' sb db =>
      obtain rfl := RingRetainedStereoRefinement.unique _ _ _ _ p p'
      obtain rfl := RingRetainedUnitPass.map_same ca cb (fun c hc x y hx hy => ih c hc hx (sub' c hc hy))
      have eqn := rows_unique sa da sb db (fun x hx => by
        obtain ⟨c,hc,get⟩ := RingRetainedUnitPass.forOutput ca hx
        exact (sub c hc get).framed)
      unfold extend
      rw [eqn]

abbrev Reading (i : Input) (read : Reader i) := OnGeometry i read false

theorem OnGeometry.reflect {i read rev atom q p} (a : OnGeometry i read rev atom q p) :
    OnGeometry i read (!rev) atom q p := by
  induction a with
  | node before look all _ sh de ih =>
    exact .node (RingRetainedStereoRefinement.mirror [.lowercase] _ _ before) look all ih sh de

theorem Reading.unique {i read atom q p t} (a : Reading i read atom q p) (b : Reading i read atom q t) : p = t :=
  OnGeometry.unique a b

abbrev Entry := ArmProfile × Branch

/-- Assemble one marked occurrence and all its unmarked stereo stages. -/
def join {i : Input} (atom : Nat) (q : Arm i) (k : Key) (v : Option RingNestedActivePair.Labels)
    (cs : List Entry) : Entry :=
  let p := RingGroupedStereo.assemble k v (cs.map Prod.fst)
  let marks := cs.map Prod.snd
  (p,extend p.lower (bit atom q) (order Branch.shallow marks) (order Branch.deep marks))

/-- Fold a supplied constitutional key reader and molecular child index through every stereo stage. -/
def build (i : Input) (read : Reader i) (atom : Nat) (key : Arm i → Option Key) (edges : Arm i → List (Arm i)) :
    Nat → Arm i → Option Entry
  | 0,_ => none
  | n+1,q => do
    let v ← read q.occurrence
    let cs := edges q
    guard (v.all consistent = true ∧ (cs = [] → v = none))
    let k ← key q
    return join atom q k v (← cs.mapM (build i read atom key edges n))

def arm? (i : Input) (read : Reader i) (atom : Nat) (q : Arm i) :=
  build i read atom (key? i) (children i) (i.certified.localizedRerootCursorBudget q + 1) q

private def cached (i : Input) (read : Reader i) (atom : Nat) (q : Arm i) :=
  let cache := localizedRerootRootSliceCache (i.certified.localizedRerootCarrierCache
    (i.certified.certified.input.molecule.atomCount + 1)) q.occurrence.val.root
  build i read atom (RingRetainedChemicalTrace.keyWith i cache.reader) (fun c => (cache.reader.readChildren c).getD [])
    (i.certified.localizedRerootCursorBudget q + 1) q

@[csimp] theorem arm_cached : @arm? = @cached := by
  funext i read atom q
  let cache := localizedRerootRootSliceCache (i.certified.localizedRerootCarrierCache
    (i.certified.certified.input.molecule.atomCount + 1)) q.occurrence.val.root
  have same : (fun c : Arm i => (cache.reader.readChildren c).getD []) = children i := by
    funext c; rw [cache.reader.readChildren_eq]; rfl
  simp only [arm?,cached,RingRetainedChemicalTrace.keyWith_eq]
  rw [same]

private theorem source {i read atom} : ∀ n q {e}, build i read atom (key? i) (children i) n q = some e →
    Reads i read false q e.1 ∧ Reading i read atom q e.2
  | 0,_,_,h => by contradiction
  | n+1,q,_,h => by
    unfold build at h
    obtain ⟨v,hv,more⟩ := Option.bind_eq_some_iff.mp h
    by_cases ok : v.all consistent = true ∧ (children i q = [] → v = none)
    · have gate : (guard (v.all consistent = true ∧ (children i q = [] → v = none)) : Option Unit) = some () := if_pos ok
      simp only [gate,Option.bind_eq_bind,Option.bind_some] at more
      obtain ⟨k,hk,more⟩ := Option.bind_eq_some_iff.mp more
      obtain ⟨cs,all,out⟩ := Option.bind_eq_some_iff.mp more
      obtain rfl := Option.some.inj out
      have before : Reads i read false q (RingGroupedStereo.assemble k v (cs.map Prod.fst)) := by
        apply RingGroupedStereo.assembled hv ok hk (RingGroupedStereo.projected all Prod.fst)
        intro c _ p hp
        obtain ⟨e,he,rfl⟩ := Option.map_eq_some_iff.mp hp
        exact (source n c he).1
      refine ⟨before,.node before.lower _ (RingGroupedStereo.projected all Prod.snd) ?_ (legal_order ..) (legal_order ..)⟩
      intro c _ p hp
      obtain ⟨e,he,rfl⟩ := Option.map_eq_some_iff.mp hp
      exact (source n c he).2
    · simp [ok] at more

theorem arm_source {i read atom q e} (h : arm? i read atom q = some e) :
    Reads i read false q e.1 ∧ Reading i read atom q e.2 := source _ q h

theorem arm_ready {i : Input} {f : Site i} {read : Reader i} (ready : RingGroupedStereo.Ready f read) (atom : Nat)
    (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q) (on : q.occurrence.val.root = f.val.root) :
    ∃ e, arm? i read atom q = some e := by
  suffices ∀ n (t : Arm i), i.certified.LocalizedRerootCursorValid t → t.occurrence.val.root = f.val.root →
      i.certified.localizedRerootCursorBudget t < n → ∃ e, build i read atom (key? i) (children i) n t = some e from
    this _ q valid on (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro t _ _ h; omega
  | succ n ih =>
    intro t vt rt budget
    obtain ⟨v,hv,ok,absent⟩ := ready t rt
    have gate : (guard (v.all consistent = true ∧ (children i t = [] → v = none)) : Option Unit) = some () := if_pos ⟨ok,absent⟩
    obtain ⟨k,hk⟩ := RingRetainedChemicalCoverage.key_total i (RingRetainedChemicalCoverage.admitted_atoms i) t vt
    have frame := i.certified.executableLocalizedRerootChildren_declarative t
    obtain ⟨cs,hcs⟩ := RingRetainedUnitPass.collect _ (children i t) (fun c hc =>
      ih c (i.certified.localizedRerootChild_valid t c _ frame hc)
        ((i.certified.localizedRerootChildren_root_eq t c _ frame hc).trans rt)
        (by have := i.certified.localizedRerootChild_budget_lt t c _ vt frame hc; omega))
    exact ⟨join atom t k v cs,by simp only [build,hv,gate,hk,hcs,Option.bind_eq_bind,Option.bind_some,Option.pure_def]⟩

end TetraStereo.Engine.RingGroupedMark

assert_kernel_only TetraStereo.Engine.RingGroupedMark.Reading.unique
assert_kernel_only TetraStereo.Engine.RingGroupedMark.arm_source
assert_kernel_only TetraStereo.Engine.RingGroupedMark.arm_ready
