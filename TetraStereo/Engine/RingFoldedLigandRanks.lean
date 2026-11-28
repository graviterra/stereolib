import TetraStereo.Engine.RingFullPathPairs

/-! Compute constitutional, unit and lowercase priorities together on the actual
rerooted ligand. Each occurrence reads its own observation and auxiliary cell,
and each parent reuses the three priorities already computed at each child. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingFoldedLigandRanks
open OneCenter CertifiedLocalizedCIPInput RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader Labels consistent)
open RingRetainedStereoRefinement (priority)
open private build from TetraStereo.Engine.RingRetainedChemicalTrace
open private child_facts from TetraStereo.Engine.RingFullPathPairs

structure Node where
  chem : RingRetainedChemicalTrace.Key
  unit : Branch
  lower : Branch
  hand : Option RS

inductive Tree where
  | node (label : Node) (children : List Tree)

def Tree.label : Tree → Node | .node n _ => n
def Tree.children : Tree → List Tree | .node _ cs => cs

private abbrev kids (i : Input) (q : Arm i) := i.certified.executableLocalizedRerootChildren q
private abbrev budget (i : Input) (q : Arm i) := i.certified.localizedRerootCursorBudget q

/-- All annotations agree with the successive native stages, on precisely the
same children, with their original multiplicities and in their original order. -/
inductive Spec (i : Input) (r : Reader i) (rev : Bool) : Arm i → Tree → Prop
  | node {q l cs}
    (chem : RingRetainedChemicalTrace.key? i q = some l.chem)
    (unit : priority i r rev [] q = some l.unit)
    (lower : priority i r rev [.lowercase] q = some l.lower)
    (hand : RingFullPathPairs.handAt i r rev q = l.hand)
    (children : List.Forall₂ (Spec i r rev) (kids i q) cs) :
    Spec i r rev q (.node l cs)

theorem Spec.lower {i r rev q t} (h : Spec i r rev q t) :
    priority i r rev [.lowercase] q = some t.label.lower := by cases h; assumption
theorem Spec.hand {i r rev q t} (h : Spec i r rev q t) :
    RingFullPathPairs.handAt i r rev q = t.label.hand := by cases h; assumption
theorem Spec.children {i r rev q t} (h : Spec i r rev q t) :
    List.Forall₂ (Spec i r rev) (kids i q) t.children := by cases h; assumption

private def combine (o : RingRetainedChemicalTrace.Observation) (v : Option Labels)
    (rev : Bool) (ts : List Tree) : Node :=
  let k := RingRetainedChemicalTrace.assemble o (ts.map (fun t => t.label.chem))
  let us := ts.map (fun t => t.label.unit)
  let u := RingRetainedUnitPass.branch k (RingNestedActivePair.unit (v.map Prod.fst))
    (order Branch.shallow us) (order Branch.deep us)
  let ls := ts.map (fun t => t.label.lower)
  let l := RingRetainedStereoRefinement.extend u
    (RingRetainedStereoRefinement.Observation.lowercase.value v rev)
    (order Branch.shallow ls) (order Branch.deep ls)
  ⟨k,u,l,RingNestedActivePair.upper (v.map fun p => if rev then p.2 else p.1)⟩

private def collectWith (i : Input) (r : Reader i) (rev : Bool) (edges : Arm i → List (Arm i)) :
    Nat → Arm i → Option Tree
  | 0,_ => none
  | n+1,q => do
    let cs := edges q
    let o ← RingRetainedChemicalTrace.observation? i q cs.isEmpty
    let v ← r q.occurrence
    guard (v.all consistent = true ∧ (cs = [] → v = none))
    let ts ← cs.mapM (collectWith i r rev edges n)
    return .node (combine o v rev ts) ts

def collect (i : Input) (r : Reader i) (rev : Bool) (n : Nat) (q : Arm i) :=
  collectWith i r rev (kids i) n q

private def selected (i : Input) (r : Reader i) (rev : Bool) (n : Nat) (q : Arm i) :=
  let reader := SelectedRoot.reader i.certified (i.certified.certified.input.molecule.atomCount+1)
    q.occurrence.val.root
  collectWith i r rev (fun c => (reader.readChildren c).getD []) n q

@[csimp] theorem collect_selected : @collect = @selected := by
  funext i r rev n q
  unfold selected collect
  congr 2
  funext c
  rw [LocalizedRerootChildReader.readChildren_eq]
  rfl

private abbrev chemBuild (i : Input) := build i (kids i)
private abbrev lowBuild (i : Input) (r : Reader i) (rev : Bool) :=
  RingRetainedStereoRefinement.build i (priority i r rev []) r .lowercase rev

private structure Agrees (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) (l : Node) : Prop where
  chem : ∀ m, budget i q < m → chemBuild i m q = some l.chem
  unit : ∀ m, budget i q < m → RingRetainedUnitPass.build i r m q = some l.unit
  lower : ∀ m, budget i q < m → lowBuild i r rev m q = some l.lower

private theorem gather {α β : Type} {P : α → β → Prop} (f : α → Option β) (xs : List α)
    (each : ∀ x ∈ xs, ∃ y, f x = some y ∧ P x y) :
    ∃ ys, xs.mapM f = some ys ∧ List.Forall₂ P xs ys := by
  induction xs with
  | nil => exact ⟨[],rfl,.nil⟩
  | cons x xs ih =>
    obtain ⟨y,hy,hp⟩ := each x List.mem_cons_self
    obtain ⟨ys,hys,ps⟩ := ih (fun z hz => each z (List.mem_cons_of_mem _ hz))
    exact ⟨y::ys,by simp [List.mapM_cons,hy,hys],.cons hp ps⟩

private theorem project {α β γ : Type} {P : α → β → Prop} {xs : List α} {ys : List β}
    (links : List.Forall₂ P xs ys) (f : α → Option γ) (g : β → γ)
    (each : ∀ x y, P x y → f x = some (g y)) : xs.mapM f = some (ys.map g) := by
  induction links with
  | nil => rfl
  | cons h _ ih => simp [List.mapM_cons,each _ _ h,ih]

private theorem exactAt {i : Input} {f : Site i} {r : Reader i} (rev : Bool)
    (ready : RingGroupedStereo.Ready f r) (n : Nat) (q : Arm i)
    (valid : i.certified.LocalizedRerootCursorValid q) (on : q.occurrence.val.root = f.val.root)
    (enough : budget i q < n) :
    ∃ t, collect i r rev n q = some t ∧ Spec i r rev q t ∧ Agrees i r rev q t.label := by
  induction n generalizing q with
  | zero => omega
  | succ n ih =>
    obtain ⟨o,ho⟩ := RingRetainedChemicalCoverage.observed i (RingRetainedChemicalCoverage.admitted_atoms i) q
    obtain ⟨v,hv,consistentV,terminal⟩ := ready q on
    have guardOk : (guard (v.all consistent = true ∧ (kids i q = [] → v = none)) : Option Unit) = some () :=
      if_pos ⟨consistentV,terminal⟩
    obtain ⟨ts,found,links⟩ := gather (collect i r rev n) (kids i q)
      (P := fun c t => budget i c < budget i q ∧ Spec i r rev c t ∧ Agrees i r rev c t.label)
      (fun c hc => by
        obtain ⟨vc,oc,bc⟩ := child_facts valid on hc
        change budget i c < budget i q at bc
        obtain ⟨t,get,spec,more⟩ := ih c vc oc (by omega)
        exact ⟨t,get,bc,spec,more⟩)
    let l := combine o v rev ts
    have chem : ∀ m, budget i q < m → chemBuild i m q = some l.chem := by
      intro m hm
      cases m with
      | zero => omega
      | succ m =>
        have sub := project links (chemBuild i m) (fun t => t.label.chem)
          (fun c t h => h.2.2.chem m (by have := h.1; omega))
        change (RingRetainedChemicalTrace.observation? i q (kids i q).isEmpty >>= _) = _
        rw [ho]
        simp only [Option.bind_eq_bind,Option.bind_some]
        rw [sub]
        rfl
    have key : RingRetainedChemicalTrace.key? i q = some l.chem :=
      chem _ (Nat.lt_succ_of_le (i.certified.localizedRerootCursorBudget_le_twice q))
    have unit : ∀ m, budget i q < m → RingRetainedUnitPass.build i r m q = some l.unit := by
      intro m hm
      cases m with
      | zero => omega
      | succ m =>
        have sub := project links (RingRetainedUnitPass.build i r m) (fun t => t.label.unit)
          (fun c t h => h.2.2.unit m (by have := h.1; omega))
        simp only [RingRetainedUnitPass.build,key,hv,Option.bind_eq_bind,Option.bind_some]
        rw [guardOk]
        simp only [Option.bind_some,sub]
        rfl
    have base : priority i r rev [] q = some l.unit := unit _ (Nat.lt_succ_self _)
    have lower : ∀ m, budget i q < m → lowBuild i r rev m q = some l.lower := by
      intro m hm
      cases m with
      | zero => omega
      | succ m =>
        have sub := project links (lowBuild i r rev m) (fun t => t.label.lower)
          (fun c t h => h.2.2.lower m (by have := h.1; omega))
        simp only [lowBuild,RingRetainedStereoRefinement.build,base,hv,Option.bind_eq_bind,Option.bind_some]
        rw [sub]
        rfl
    refine ⟨.node l ts,?_,.node key base (lower _ (Nat.lt_succ_self _)) ?_
      (links.imp (fun _ _ h => h.2.1)),⟨chem,unit,lower⟩⟩
    · change (RingRetainedChemicalTrace.observation? i q (kids i q).isEmpty >>= _) = _
      rw [ho]
      simp only [Option.bind_eq_bind,Option.bind_some,hv,guardOk]
      change ((kids i q).mapM (collect i r rev n) >>= _) = _
      rw [found]
      rfl
    · simp [RingFullPathPairs.handAt,hv,l,combine]

/-- A ready store on any admitted focus supplies all folded priorities at
every reachable occurrence. The sole fuel bound is the native cursor budget. -/
theorem collect_exact {i : Input} {f : Site i} {r : Reader i} (rev : Bool)
    (ready : RingGroupedStereo.Ready f r) (n : Nat) (q : Arm i)
    (valid : i.certified.LocalizedRerootCursorValid q) (on : q.occurrence.val.root = f.val.root)
    (enough : budget i q < n) : ∃ t, collect i r rev n q = some t ∧ Spec i r rev q t := by
  obtain ⟨t,get,spec,_⟩ := exactAt rev ready n q valid on enough
  exact ⟨t,get,spec⟩

end TetraStereo.Engine.RingFoldedLigandRanks

assert_kernel_only TetraStereo.Engine.RingFoldedLigandRanks.collect_exact
assert_kernel_only TetraStereo.Engine.RingFoldedLigandRanks.collect_selected
