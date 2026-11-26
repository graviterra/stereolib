import TetraStereo.Engine.RingOriginPriorityStore
import TetraStereo.Engine.RingPriorityCoordinate

/-! The active-origin constitutional reader is substituted at every occurrence
of every cumulative stereo pass. Raw increasing duplicate-coordinate recodings
commute with both recursive sibling sorts and preserve every stereo word. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginStereoRanking
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader consistent unit)
open RingRetainedChemicalTrace (Key key?)
open RingStereoSiblingPass (Branch order)
open RingSingleCycleComparison (CommonOrigin rebuilt native)
open private factors binary native_build congr_build from
  TetraStereo.Engine.RingSingleCycleComparison

/-- Recoding the constitutional duplicate coordinate leaves every stereo
observation and every already assembled sphere row intact. -/
def recode (g : Nat → Nat) (b : Branch) : Branch :=
  ⟨RingPriorityCoordinate.second g b.priorHead,
    RingPriorityCoordinate.second (List.map (List.map g)) b.priorDeep,b.value,b.levels⟩

def Shaped (b : Branch) : Prop := 2 ≤ b.priorHead.length ∧ 2 ≤ b.priorDeep.length

private theorem branch_shaped (k : Key) (v : Nat) (sh de : List Branch) :
    Shaped (RingRetainedUnitPass.branch k v sh de) := by
  simp [Shaped,RingRetainedUnitPass.branch,RingRetainedChemicalPreorder.orderWord]

private theorem recode_shallow (g : Nat → Nat) (b : Branch) (h : Shaped b) :
    (recode g b).shallow = RingPriorityCoordinate.second g b.shallow := by
  exact (RingPriorityCoordinate.second_append g b.priorHead [b.value] h.1).symm

theorem recode_deep (g : Nat → Nat) (b : Branch) (h : Shaped b) :
    (recode g b).deep = RingPriorityCoordinate.second (List.map (List.map g)) b.deep := by
  exact (RingPriorityCoordinate.second_append (List.map (List.map g)) b.priorDeep [b.word] h.2).symm

private theorem sort_recode {g : Nat → Nat} (hg : StrictMono g)
    (cs : List Branch) (shape : ∀ c ∈ cs, Shaped c) :
    order Branch.shallow (cs.map (recode g)) = (order Branch.shallow cs).map (recode g) ∧
    order Branch.deep (cs.map (recode g)) = (order Branch.deep cs).map (recode g) := by
  have sh : StrictMono (RingPriorityCoordinate.second g) := RingPriorityCoordinate.second_strictMono hg
  have de : StrictMono (RingPriorityCoordinate.second (List.map (List.map g))) :=
    RingPriorityCoordinate.second_strictMono (RingPriorityCoordinate.map_strictMono
      (RingPriorityCoordinate.map_strictMono hg))
  constructor
  · symm
    apply List.map_mergeSort
    intro a ha b hb
    change decide (b.shallow ≤ a.shallow) = decide ((recode g b).shallow ≤ (recode g a).shallow)
    rw [recode_shallow g b (shape b hb),recode_shallow g a (shape a ha)]
    congr 1
    exact propext sh.le_iff_le.symm
  · symm
    apply List.map_mergeSort
    intro a ha b hb
    change decide (b.deep ≤ a.deep) = decide ((recode g b).deep ≤ (recode g a).deep)
    rw [recode_deep g b (shape b hb),recode_deep g a (shape a ha)]
    congr 1
    exact propext de.le_iff_le.symm

private theorem rows_recode (g : Nat → Nat) (sh de : List Branch) :
    RingStereoSiblingPass.rows (sh.map (recode g)) (de.map (recode g)) =
      RingStereoSiblingPass.rows sh de := by
  simp [RingStereoSiblingPass.rows,recode,List.map_map,Function.comp_def]

private theorem branch_recode (g : Nat → Nat) (k : Key) (v : Nat) (sh de : List Branch) :
    RingRetainedUnitPass.branch (RingDuplicateScale.key g k) v
      (sh.map (recode g)) (de.map (recode g)) =
      recode g (RingRetainedUnitPass.branch k v sh de) := by
  simp [RingRetainedUnitPass.branch,recode,RingPriorityCoordinate.second,
    RingDuplicateScale.key,RingDuplicateScale.column,RingDuplicateScale.observation,
    RingDuplicateScale.scalar,RingRetainedChemicalPreorder.orderWord,rows_recode]

/-- Every recursive call consults the supplied constitutional reader; both
shallow and deep sibling sorts are recomputed from its outputs. -/
def unitWith (i : Input) (keys : Arm i → Option Key) (read : Reader i) :
    Nat → Arm i → Option Branch
  | 0,_ => none
  | n+1,q => do
    let k ← keys q
    let labels ← read q.occurrence
    let children := i.certified.executableLocalizedRerootChildren (fuel := i.certified.certified.input.molecule.atomCount + 1) q
    guard (labels.all consistent = true ∧ (children = [] → labels = none))
    let cs ← children.mapM (unitWith i keys read n)
    return RingRetainedUnitPass.branch k (unit (labels.map Prod.fst))
      (order Branch.shallow cs) (order Branch.deep cs)

private theorem unitWith_shaped (i : Input) (keys : Arm i → Option Key) (read : Reader i) :
    ∀ n q b, unitWith i keys read n q = some b → Shaped b
  | 0,_,_,h => by contradiction
  | n+1,q,b,h => by
    simp only [unitWith] at h
    obtain ⟨k,hk,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v,hv,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨u,hu,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨cs,hcs,h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl := Option.some.inj h
    exact branch_shaped ..

private theorem mapM_map {α β γ : Type} (f : α → Option β) (g : β → γ) (xs : List α) :
    xs.mapM (fun x => (f x).map g) = (xs.mapM f).map (List.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons,ih]
    cases f x <;> cases xs.mapM f <;> rfl

/-- Raw increasing recoding commutes with the entire recursive unit pass.
Both sibling sorts run on the recoded keys; stereo rows and words are
unchanged. No division or recovery of native keys enters this calculation. -/
theorem unitWith_natural (i : Input) (keys : Arm i → Option Key) (read : Reader i)
    {g : Nat → Nat} (hg : StrictMono g) (n : Nat) (q : Arm i) :
    unitWith i (fun c => (keys c).map (RingDuplicateScale.key g)) read n q =
      (unitWith i keys read n q).map (recode g) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    simp only [unitWith]
    rw [funext ih,mapM_map]
    cases hk : keys q with
    | none => rfl
    | some k =>
      cases hv : read q.occurrence with
      | none => rfl
      | some v =>
        by_cases ok : v.all consistent = true ∧
            (i.certified.executableLocalizedRerootChildren q = [] → v = none)
        · have guard_ok : (guard (v.all consistent = true ∧
              (i.certified.executableLocalizedRerootChildren q = [] → v = none)) : Option Unit) = some () := if_pos ok
          simp only [Option.map_some,Option.bind_eq_bind,Option.bind_some,guard_ok]
          cases hc : (i.certified.executableLocalizedRerootChildren q).mapM (unitWith i keys read n) with
          | none => rfl
          | some cs =>
            have shape : ∀ c ∈ cs, Shaped c := by
              intro c mem
              obtain ⟨t,ht,get⟩ := RingRetainedUnitPass.forOutput hc mem
              exact unitWith_shaped i keys read n t c get
            obtain ⟨sh,de⟩ := sort_recode hg cs shape
            simp only [Option.map_some,Option.bind_some,sh,de,Option.pure_def]
            exact congrArg some (branch_recode g k _ _ _)
        · have guard_bad : (guard (v.all consistent = true ∧
              (i.certified.executableLocalizedRerootChildren q = [] → v = none)) : Option Unit) = none := if_neg ok
          simp [guard_bad]

private theorem recode_extend (g : Nat → Nat) (p : Branch) (shape : Shaped p)
    (v : Nat) (sh de : List Branch) :
    RingRetainedStereoRefinement.extend (recode g p) v (sh.map (recode g)) (de.map (recode g)) =
      recode g (RingRetainedStereoRefinement.extend p v sh de) := by
  simp only [RingRetainedStereoRefinement.extend]
  rw [recode_shallow g p shape,recode_deep g p shape,rows_recode]
  rfl

private theorem extend_shaped (p : Branch) (shape : Shaped p) (v : Nat) (sh de : List Branch) :
    Shaped (RingRetainedStereoRefinement.extend p v sh de) := by
  simp only [Shaped,RingRetainedStereoRefinement.extend,Branch.shallow,Branch.deep,List.length_append,List.length_singleton]
  have := shape.1
  have := shape.2
  omega

private theorem refine_shaped (i : Input) (prior : Arm i → Option Branch)
    (shape : ∀ q b, prior q = some b → Shaped b) (read : Reader i)
    (obs : RingRetainedStereoRefinement.Observation) (rev : Bool) :
    ∀ n q b, RingRetainedStereoRefinement.build i prior read obs rev n q = some b → Shaped b
  | 0,_,_,h => by contradiction
  | n+1,q,b,h => by
    simp only [RingRetainedStereoRefinement.build] at h
    obtain ⟨p,hp,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v,hv,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨cs,hcs,h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl := Option.some.inj h
    exact extend_shaped p (shape q p hp) ..

/-- Each later pass also recomputes its sibling orders with the transformed
cumulative priorities, retaining its complete stereo word. -/
theorem refine_natural (i : Input) (prior : Arm i → Option Branch)
    (shape : ∀ q b, prior q = some b → Shaped b) (read : Reader i)
    (obs : RingRetainedStereoRefinement.Observation) (rev : Bool)
    {g : Nat → Nat} (hg : StrictMono g) (n : Nat) (q : Arm i) :
    RingRetainedStereoRefinement.build i (fun c => (prior c).map (recode g)) read obs rev n q =
      (RingRetainedStereoRefinement.build i prior read obs rev n q).map (recode g) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    simp only [RingRetainedStereoRefinement.build]
    rw [funext ih,mapM_map]
    cases hp : prior q with
    | none => rfl
    | some p =>
      cases hv : read q.occurrence with
      | none => rfl
      | some v =>
        cases hc : (i.certified.executableLocalizedRerootChildren q).mapM
            (RingRetainedStereoRefinement.build i prior read obs rev n) with
        | none => rfl
        | some cs =>
          have shaped : ∀ c ∈ cs, Shaped c := by
            intro c mem
            obtain ⟨t,ht,get⟩ := RingRetainedUnitPass.forOutput hc mem
            exact refine_shaped i prior shape read obs rev n t c get
          obtain ⟨sh,de⟩ := sort_recode hg cs shaped
          change some (RingRetainedStereoRefinement.extend (recode g p) (obs.value v rev)
            (order Branch.shallow (cs.map (recode g))) (order Branch.deep (cs.map (recode g)))) =
              some (recode g (RingRetainedStereoRefinement.extend p (obs.value v rev)
                (order Branch.shallow cs) (order Branch.deep cs)))
          rw [sh,de]
          exact congrArg some (recode_extend g p (shape q p hp) _ _ _)

/-- Constitutional substitution applies to every earlier pass as well as the
current pairing or lowercase pass. -/
def priorityWith (i : Input) (keys : Arm i → Option Key) (read : Reader i) (rev : Bool) :
    List RingRetainedStereoRefinement.Observation → Arm i → Option Branch
  | [],q => unitWith i keys read (i.certified.localizedRerootCursorBudget q + 1) q
  | obs::earlier,q => RingRetainedStereoRefinement.build i
      (priorityWith i keys read rev earlier) read obs rev (i.certified.localizedRerootCursorBudget q + 1) q

theorem priorityWith_shaped (i : Input) (keys : Arm i → Option Key) (read : Reader i) (rev : Bool) :
    ∀ stages q b, priorityWith i keys read rev stages q = some b → Shaped b
  | [],q,b,h => unitWith_shaped i keys read _ q b h
  | obs::earlier,q,b,h => refine_shaped i _ (priorityWith_shaped i keys read rev earlier) read obs rev _ q b h

/-- Raw constitutional recoding propagates through arbitrarily many cumulative
stereo passes. This establishes genuine recursive invariance, including all
internal shallow and deep sibling sorts and all refused reads. -/
theorem priorityWith_natural (i : Input) (keys : Arm i → Option Key) (read : Reader i) (rev : Bool)
    {g : Nat → Nat} (hg : StrictMono g) (stages : List RingRetainedStereoRefinement.Observation) (q : Arm i) :
    priorityWith i (fun c => (keys c).map (RingDuplicateScale.key g)) read rev stages q =
      (priorityWith i keys read rev stages q).map (recode g) := by
  induction stages generalizing q with
  | nil => exact unitWith_natural i keys read hg _ q
  | cons obs earlier ih =>
    simp only [priorityWith]
    rw [funext ih]
    exact refine_natural i _ (priorityWith_shaped i keys read rev earlier) read obs rev hg _ q

/-- A root-slice reader equality propagates through every recursive node,
including failure, terminal guards and both sibling orderings. -/
theorem unitWith_congr (i : Input) (root : i.certified.Atom)
    (keys other : Arm i → Option Key)
    (same : ∀ q, q.occurrence.val.root = root → keys q = other q)
    (read : Reader i) (n : Nat) (q : Arm i) (on : q.occurrence.val.root = root) :
    unitWith i keys read n q = unitWith i other read n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    simp only [unitWith,same q on]
    have kids : (i.certified.executableLocalizedRerootChildren q).mapM
        (unitWith i keys read n) =
        (i.certified.executableLocalizedRerootChildren q).mapM (unitWith i other read n) := by
      apply RingFrameTransport.mapM_congr_mem
      intro c mem
      exact ih c ((i.certified.localizedRerootChildren_root_eq _ _ _
        (i.certified.executableLocalizedRerootChildren_declarative _) mem).trans on)
    rw [kids]

private theorem unitWith_native (i : Input) (read : Reader i) (n : Nat) :
    unitWith i (key? i) read n = RingRetainedUnitPass.build i read n := by
  induction n with
  | zero => rfl
  | succ n ih => funext q; simp only [unitWith,RingRetainedUnitPass.build,ih]

/-- The native and active-focus readers are two positive raw recodings of
one shared recursive constitutional reader on every occurrence of the slice. -/
theorem reader_factorization {i : Input} (f : Site i) (common : CommonOrigin i f.val.root) :
    ∃ (base : Arm i → Option Key) (a b : Nat), 0 < a ∧ 0 < b ∧
      ∀ q : Arm i, q.occurrence.val.root = f.val.root →
        key? i q = (base q).map (RingDuplicateScale.key (· * a)) ∧
        rebuilt i f q = (base q).map (RingDuplicateScale.key (· * b)) := by
  obtain ⟨a,b,ha,hb,reads⟩ := factors f.val.node.history.reverse f.val.root common
  let n := 2 * (i.certified.certified.input.molecule.atomCount + 1 + 1) + 1
  let children := i.certified.executableLocalizedRerootChildren (fuel := i.certified.certified.input.molecule.atomCount + 1)
  let base := RingDuplicateScale.build (binary i) children n
  refine ⟨base,a,b,ha,hb,?_⟩
  intro q on
  have scale (v : Nat) (positive : 0 < v) (reader : Arm i → Option RingRetainedChemicalTrace.Observation)
      (same : ∀ t : Arm i, t.occurrence.val.root = f.val.root →
        reader t = (binary i t).map (RingDuplicateScale.observation (· * v))) :
      RingDuplicateScale.build reader children n q = (base q).map (RingDuplicateScale.key (· * v)) :=
    (congr_build i f.val.root _ _ same n q on).trans
      (RingDuplicateScale.build_natural (fun _ _ h => Nat.mul_lt_mul_of_pos_right h positive) _ _ _ _)
  constructor
  · exact (native_build i n q).symm.trans (scale a ha _ (fun t h => (reads t h).1))
  · exact scale b hb _ (fun t h => (reads t h).2)

private theorem refine_congr (i : Input) (root : i.certified.Atom)
    (prior other : Arm i → Option Branch)
    (same : ∀ q, q.occurrence.val.root = root → prior q = other q)
    (read : Reader i) (rev : Bool) (obs : RingRetainedStereoRefinement.Observation)
    (n : Nat) (q : Arm i) (on : q.occurrence.val.root = root) :
    RingRetainedStereoRefinement.build i prior read obs rev n q =
      RingRetainedStereoRefinement.build i other read obs rev n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    simp only [RingRetainedStereoRefinement.build,same q on]
    have kids : (i.certified.executableLocalizedRerootChildren q).mapM
        (RingRetainedStereoRefinement.build i prior read obs rev n) =
        (i.certified.executableLocalizedRerootChildren q).mapM
          (RingRetainedStereoRefinement.build i other read obs rev n) := by
      apply RingFrameTransport.mapM_congr_mem
      intro c mem
      exact ih c ((i.certified.localizedRerootChildren_root_eq _ _ _
        (i.certified.executableLocalizedRerootChildren_declarative _) mem).trans on)
    rw [kids]

/-- Cumulative rankings only consult constitutional readers on their own root. -/
theorem priorityWith_congr (i : Input) (root : i.certified.Atom)
    (keys other : Arm i → Option Key)
    (same : ∀ q, q.occurrence.val.root = root → keys q = other q)
    (read : Reader i) (rev : Bool) (stages : List RingRetainedStereoRefinement.Observation)
    (q : Arm i) (on : q.occurrence.val.root = root) :
    priorityWith i keys read rev stages q = priorityWith i other read rev stages q := by
  induction stages generalizing q with
  | nil => exact unitWith_congr i root keys other same read _ q on
  | cons obs earlier ih => exact refine_congr i root _ _ ih read rev obs _ q on

/-- Native substitution recovers the public molecular ranking at every stage. -/
theorem priorityWith_native (i : Input) (read : Reader i) (rev : Bool)
    (stages : List RingRetainedStereoRefinement.Observation) (q : Arm i) :
    priorityWith i (key? i) read rev stages q = RingRetainedStereoRefinement.priority i read rev stages q := by
  induction stages generalizing q with
  | nil => exact congrFun (unitWith_native i read _) q
  | cons obs earlier ih => simp only [priorityWith,RingRetainedStereoRefinement.priority,funext ih]

@[simp] theorem recode_word (g : Nat → Nat) (b : Branch) : (recode g b).word = b.word := rfl

/-- All cumulative active-focus ranks are raw recodings of the same base as
the public ranks. The complete stereo word is therefore exactly preserved. -/
theorem recursive_priority_factorization {i : Input} (f : Site i) (common : CommonOrigin i f.val.root) :
    ∃ (base : Arm i → Option Key) (a b : Nat), 0 < a ∧ 0 < b ∧
      ∀ (read : Reader i) (rev : Bool) (stages : List RingRetainedStereoRefinement.Observation)
        (q : Arm i), q.occurrence.val.root = f.val.root →
      RingRetainedStereoRefinement.priority i read rev stages q =
        (priorityWith i base read rev stages q).map (recode (· * a)) ∧
      priorityWith i (rebuilt i f) read rev stages q =
        (priorityWith i base read rev stages q).map (recode (· * b)) := by
  obtain ⟨base,a,b,ha,hb,keys⟩ := reader_factorization f common
  refine ⟨base,a,b,ha,hb,?_⟩
  intro read rev stages q on
  constructor
  · rw [← priorityWith_native]
    exact (priorityWith_congr i f.val.root _ _ (fun t h => (keys t h).1) read rev stages q on).trans
      (priorityWith_natural i base read rev (fun _ _ h => Nat.mul_lt_mul_of_pos_right h ha) stages q)
  · exact (priorityWith_congr i f.val.root _ _ (fun t h => (keys t h).2) read rev stages q on).trans
      (priorityWith_natural i base read rev (fun _ _ h => Nat.mul_lt_mul_of_pos_right h hb) stages q)

/-- The complete cumulative stereo word is invariant after genuine recursive
substitution of active-focus constitutional priorities at every node. -/
theorem recursive_word_exact {i : Input} (f : Site i) (common : CommonOrigin i f.val.root)
    (read : Reader i) (rev : Bool) (stages : List RingRetainedStereoRefinement.Observation)
    (q : Arm i) (on : q.occurrence.val.root = f.val.root) :
    (priorityWith i (rebuilt i f) read rev stages q).map Branch.word =
      (RingRetainedStereoRefinement.priority i read rev stages q).map Branch.word := by
  obtain ⟨base,a,b,ha,hb,factors⟩ := recursive_priority_factorization f common
  obtain ⟨native,active⟩ := factors read rev stages q on
  rw [native,active,Option.map_map,Option.map_map]
  rfl


end TetraStereo.Engine.RingOriginStereoRanking

assert_kernel_only TetraStereo.Engine.RingOriginStereoRanking.priorityWith_natural

assert_kernel_only TetraStereo.Engine.RingOriginStereoRanking.reader_factorization

assert_kernel_only TetraStereo.Engine.RingOriginStereoRanking.recursive_priority_factorization

assert_kernel_only TetraStereo.Engine.RingOriginStereoRanking.recursive_word_exact
