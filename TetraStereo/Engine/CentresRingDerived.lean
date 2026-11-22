import TetraStereo.Engine.CentresRingMolecular

set_option autoImplicit false

namespace TetraStereo.Engine.CentresRing.Molecular
open OneCenter CertifiedLocalizedCIPInput
open LocalizedGenericMarkedRecalculation (Geometry readback?)
open LocalizedChemicalRingPhysicalSense (inputGeometry)

private abbrev CompareCall := Nat → Nat → Option Call

private def insert (cmp : CompareCall) (a : Nat) : List Nat → Option (List Nat × List Call)
  | [] => some ([a],[])
  | b :: tail => do
    let c ← cmp b a
    if c.comparison.value < 0 then
      let (rest,calls) ← insert cmp a tail
      return (b :: rest,c :: calls)
    else return (a :: b :: tail,[c])

private structure Sorted where
  trial : Trial
  rank : Ranking
  calls : List Call

private def sortWith (cmp : CompareCall) (mark : Option Nat) (start : List Nat) : Option Sorted := do
  let (rev,calls) ← start.foldlM (fun (acc : List Nat × List Call) x => do
    let (xs,more) ← insert cmp x acc.1
    return (xs,acc.2 ++ more)) ([],[])
  let values := calls.map (·.comparison)
  return ⟨⟨mark,start,values⟩,
    ⟨rev.reverse,values.all (fun c => c.value != 0),values.countP (fun c => c.value.natAbs > 1)⟩,calls⟩

private def comparator (f : Frame) : Option CompareCall :=
  match h : prepare f with
  | none => none
  | some read => some (readCall f read h)

private def uniqueRank (r : Ranking) : Option Ranking := if r.unique then some r else none

structure Assignment where
  pass : Pass
  rank : Option Ranking
  calls : List Call

/-- Only the original neighbor iteration order is a traversal input. Groups,
chosen atoms, inherited exits, signs, magnitudes and subsequent sort orders are
calculated. The comparison integers and the assigned letter are absent from the inputs. -/
def derivePass (f : Frame) (g : Geometry) (start : List Nat) : Option Assignment := do
  let atom ← f.focus.getLast?
  let ids := bondedAtoms f.molecule atom
  guard (start.length == 4 &&
    replayListSort (fun x y => x ≤ y) start == replayListSort (fun x y => x ≤ y) ids)
  let cmp ← comparator f
  let base ← sortWith cmp f.mark start
  if base.rank.unique || f.constitutional then
    return ⟨⟨f.mark,[base.trial],[]⟩,uniqueRank base.rank,base.calls⟩
  let order := base.rank.order
  let groups ← (order.zip (order.drop 1)).mapM (fun (a,b) => cmp a b)
  let values := groups.map (·.comparison)
  let promote (prev : Ranking) (slot : Nat) := do
    let a ← prev.order[slot]?
    let cc ← comparator {f with mark := some a}
    sortWith cc (some a) prev.order
  let calls := base.calls ++ groups
  match 1 + values.countP (fun c => c.value != 0) with
  | 2 =>
    let second ← promote base.rank 1
    return ⟨⟨none,[base.trial,second.trial],values⟩,uniqueRank second.rank,calls ++ second.calls⟩
  | 1 =>
    let a ← promote base.rank 0
    let b ← promote a.rank 1
    let v ← readback? g a.rank.order
    let w ← readback? g b.rank.order
    let even := v == w
    return ⟨⟨if even then none else b.trial.mark,[base.trial,a.trial,b.trial],values⟩,
      if even then uniqueRank b.rank else none,calls ++ a.calls ++ b.calls⟩
  | _ => return ⟨⟨f.mark,[base.trial],values⟩,none,calls⟩

/-- Visiting order and first carrier orders are the only fields read from the
original execution. In particular no indices selecting winners, values, labels
or scalar references occur in the layout. -/
structure Layout where
  root : Nat
  discovered : List (List Nat)
  passStarts : List (List Nat)
  auxStarts : List (List Nat)

def layout (t : CenterTrace) : Option Layout := do
  let start (p : Pass) := p.trials.head?.map Trial.start
  return ⟨t.atom,t.discovered,← t.passes.mapM start,← t.updates.mapM (fun u => start u.pass)⟩

/-- A finite derivation with an empty initial auxiliary store. Each update is
computed at its own occurrence with only previously derived, strictly deeper
facts visible and with the previous scalar reference. -/
inductive Publications (mol : RawMolecule) (g : Geometry) (discovery : List (List Nat)) :
    List PairList.Publication → List Update → Option Nat → Prop where
  | empty : Publications mol g discovery [] [] none
  | next {old updates mark path start a label} (index : Nat) :
    Publications mol g discovery old updates mark →
    discovery[index]? = some path.reverse →
    derivePass ⟨mol,path,PairList.publishedAt old path,mark,false⟩ g start = some a →
    readRanking g a.rank = .ok label →
    Publications mol g discovery (⟨path,labelCode label⟩ :: old)
      (updates ++ [⟨index,a.pass,labelCode label⟩]) a.pass.after

theorem Publications.origin {mol g discovery pubs updates mark} (chain : Publications mol g discovery pubs updates mark)
    {fact : PairList.Publication} (member : fact ∈ pubs) :
    ∃ old earlier previous start a label,
      Publications mol g discovery old earlier previous ∧
      derivePass ⟨mol,fact.path,PairList.publishedAt old fact.path,previous,false⟩ g start = some a ∧
      readRanking g a.rank = .ok label ∧ fact.code = labelCode label := by
  induction chain with
  | empty => simp at member
  | next index prior _ computed read ih =>
    rcases List.mem_cons.mp member with rfl | tail
    · exact ⟨_,_,_,_,_,_,prior,computed,read,rfl⟩
    · exact ih tail

/-- Every recorded publication has a derivation at the exact occurrence
identified by its discovery index, including publications of Unknown. -/
theorem Publications.update_origin {mol g discovery pubs updates mark}
    (chain : Publications mol g discovery pubs updates mark) {u : Update} (mem : u ∈ updates) :
    ∃ old earlier prev path start a label,
      Publications mol g discovery old earlier prev ∧ discovery[u.index]? = some path.reverse ∧
      derivePass ⟨mol,path,PairList.publishedAt old path,prev,false⟩ g start = some a ∧
      readRanking g a.rank = .ok label ∧ u.pass = a.pass ∧ u.label = labelCode label := by
  induction chain with
  | empty => simp at mem
  | next index prior addr computed read ih =>
    rcases List.mem_append.mp mem with h | h
    · exact ih h
    · obtain rfl := List.mem_singleton.mp h
      exact ⟨_,_,_,_,_,_,_,prior,addr,computed,read,rfl,rfl⟩

structure Derivation (mol : RawMolecule) (g : Geometry) where
  trace : CenterTrace
  calls : List Call
  published : List PairList.Publication
  lastAuxMark : Option Nat
  history : Publications mol g trace.discovered published trace.updates lastAuxMark

private structure State (mol : RawMolecule) (g : Geometry) (discovery : List (List Nat)) where
  published : List PairList.Publication
  updates : List Update
  mark : Option Nat
  calls : List Call
  history : Publications mol g discovery published updates mark

private def update (mol : RawMolecule) (g : Geometry) (discovery : List (List Nat)) (s : State mol g discovery)
    (item : (List Nat × Nat) × List Nat) : Option (State mol g discovery) := do
  let ((reversePath,index),start) := item
  let path := reversePath.reverse
  if addr : discovery[index]? = some path.reverse then
    let f := Frame.mk mol path (PairList.publishedAt s.published path) s.mark false
    match ha : derivePass f g start with
    | none => none
    | some a =>
      match hr : readRanking g a.rank with
      | .error _ => none
      | .ok label =>
        let code := labelCode label
        return ⟨⟨path,code⟩ :: s.published,s.updates ++ [⟨index,a.pass,code⟩],
          a.pass.after,s.calls ++ a.calls,.next index s.history addr ha hr⟩
  else none

/-- Start with no publications, calculate each auxiliary from deeper derived
facts, then use the completed state for the root. An exhausted tree bound,
invalid shape, or unresolved rule evidence fails the entire derivation. -/
def derive (mol : RawMolecule) (g : Geometry) (l : Layout) : Option (Derivation mol g) := do
  let first :: rest := l.passStarts | none
  let f := Frame.mk mol [l.root] [] none true
  let a ← derivePass f g first
  if a.rank.isSome then
    guard (rest.isEmpty && l.discovered.isEmpty && l.auxStarts.isEmpty)
    let code := labelCode (← (readRanking g a.rank).toOption)
    return ⟨⟨[],[],l.root,[a.pass],code⟩,a.calls,[],none,.empty⟩
  let [last] := rest | none
  guard (l.discovered.length == l.auxStarts.length)
  let items := (scheduled l.discovered).zip l.auxStarts
  guard a.pass.after.isNone
  let s ← items.foldlM (update mol g l.discovered) ⟨[],[],none,[],.empty⟩
  let full ← derivePass {f with visible := s.published, mark := s.mark, constitutional := false} g last
  let code := labelCode (← (readRanking g full.rank).toOption)
  return ⟨⟨l.discovered,s.updates,l.root,[a.pass,full.pass],code⟩,a.calls ++ s.calls ++ full.calls,s.published,s.mark,s.history⟩

private def inPass (p : Pass) : List Comparison :=
  match p.trials with
  | [] => p.groups
  | first :: tail => first.comparisons ++ p.groups ++ tail.flatMap Trial.comparisons

def chronological (t : CenterTrace) : List Comparison :=
  (t.passes.take 1).flatMap inPass ++ t.updates.flatMap (fun u => inPass u.pass) ++
    (t.passes.drop 1).flatMap inPass

structure Evidence (mol : RawMolecule) (g : Geometry) (t : CenterTrace) where
  traversal : Layout
  derived : Derivation mol g
  layout_eq : layout t = some traversal
  derivation_eq : derive mol g traversal = some derived
  trace_eq : derived.trace = t
  coverage : derived.calls.map Call.comparison = chronological t

/-- Includes equality calls and every grouping call at every auxiliary. -/
theorem Evidence.call_at {m g t} (e : Evidence m g t) {cmp : Comparison}
    (h : cmp ∈ chronological t) : ∃ c ∈ e.derived.calls, c.comparison = cmp := by
  rw [← e.coverage] at h
  exact List.mem_map.mp h

theorem Evidence.same_layout {m g t u} (a : Evidence m g t) (b : Evidence m g u)
    (same : layout t = layout u) : t = u := by
  rw [a.layout_eq,b.layout_eq] at same
  have eq := Option.some.inj same
  have h := a.derivation_eq
  rw [eq,b.derivation_eq] at h
  exact a.trace_eq.symm.trans ((congrArg Derivation.trace (Option.some.inj h).symm).trans b.trace_eq)


def certify (mol : RawMolecule) (g : Geometry) (t : CenterTrace) : Except String (Evidence mol g t) :=
  match hl : layout t with
  | none => .error "missing initial carrier order"
  | some l =>
    match hd : derive mol g l with
    | none => .error s!"root {t.atom}: molecular derivation failed"
    | some d =>
      if ht : d.trace = t then
        if cover : d.calls.map Call.comparison = chronological t then .ok ⟨l,d,hl,hd,ht,cover⟩
        else .error "molecular comparison inventory mismatch"
      else .error s!"root {t.atom}: derived comparisons, promotions or publications differ"

structure Checked (input : LocalizedChemicalRing.Input) (cs : List Nat) where
  replay : Result input cs
  derivations : List (Sigma (Evidence input.molecule (inputGeometry input.certified)))
  inventory_eq : derivations.map Sigma.fst = replay.traces

private def certifyAll (m : RawMolecule) (g : Geometry) : (ts : List CenterTrace) →
    Except String {ds : List (Sigma (Evidence m g)) // ds.map Sigma.fst = ts}
  | [] => .ok ⟨[],rfl⟩
  | t :: ts => do
    let d ← certify m g t
    let tail ← certifyAll m g ts
    return ⟨⟨t,d⟩ :: tail.val,by simp [tail.property]⟩

/-- Upgrade a live or replayed result with a molecular derivation for every
row. Equality includes every auxiliary pass, refusal, scalar exit and comparison. -/
def certifyResult {input : LocalizedChemicalRing.Input} {cs : List Nat} (r : Result input cs) :
    Except String (Checked input cs) := do
  let ds ← certifyAll input.molecule (inputGeometry input.certified) r.traces
  return ⟨r,ds.val,ds.property⟩

def check (input : LocalizedChemicalRing.Input) (packet : Receipt)
    (cs : List Nat := inventory input) : Except String (Checked input cs) := do
  certifyResult (← checkReceipt input packet cs)

def Rule.sourceName : Rule → String
  | .atomicNumber => "Rule1a" | .duplicate => "Rule1b" | .isotope => "Rule2"
  | .geometric => "Rule3" | .stereoClass => "Rule4a" | .likePair => "Rule4b"
  | .lower => "Rule4c" | .handedPair => "Rule5New" | .reference => "Rule6"

structure Observation where
  left : Nat
  right : Nat
  rules : List (String × Int)
  deriving DecidableEq, Repr, Lean.FromJson, Lean.ToJson

def sourcePrefix : Tests → List (String × Int)
  | [] => []
  | (rule,test) :: rest => match test.value with
    | none => []
    | some v => (rule.sourceName,v) :: (if v = 0 then sourcePrefix rest else [])

def Call.observation (c : Call) : Observation :=
  ⟨c.comparison.left,c.comparison.right,sourcePrefix c.tests⟩

def expected {input cs} (c : Checked input cs) : List Observation :=
  c.derivations.flatMap fun row => row.2.derived.calls.map Call.observation

structure SourceReceipt where
  receipt : Receipt
  observed : List Observation
  deriving Lean.FromJson, Lean.ToJson

structure SourceChecked (input : LocalizedChemicalRing.Input) (cs : List Nat) where
  molecular : Checked input cs
  observed : List Observation
  prefixes_eq : observed = expected molecular

/-- Verify every rule attempted by the source sorter, including zeros, in its
original call order. The expected side is calculated from the molecule. -/
def checkSourceReceipt (input : LocalizedChemicalRing.Input) (packet : SourceReceipt)
    (cs : List Nat := inventory input) : Except String (SourceChecked input cs) := do
  let c ← check input packet.receipt cs
  let want := expected c
  if h : packet.observed = want then return ⟨c,packet.observed,h⟩
  let ix := ((packet.observed.zip want).takeWhile fun (a,b) => a == b).length
  throw s!"source rule prefix at call {ix}: observed {repr packet.observed[ix]?}, expected {repr want[ix]?}"

def observe (input : LocalizedChemicalRing.Input) (cs : List Nat := inventory input)
    (classpath : String := ".cache/centres10/classes:.cache/centres10/guava.jar") :
    IO (Except String SourceReceipt) := do
  let data ← runCore input cs classpath true
  return do
    let json ← data
    let ts ← Lean.fromJson? (← json.getObjVal? "traces")
    let seen ← Lean.fromJson? (← json.getObjVal? "observed")
    return ⟨⟨releaseCommit,← request input cs,ts⟩,seen⟩

def analyze (input : LocalizedChemicalRing.Input) (cs : List Nat := inventory input)
    (classpath : String := ".cache/centres10/classes:.cache/centres10/guava.jar") :
    IO (Except String (SourceChecked input cs)) := do
  return (← observe input cs classpath).bind fun p => checkSourceReceipt input p cs

end TetraStereo.Engine.CentresRing.Molecular
assert_kernel_only TetraStereo.Engine.CentresRing.Molecular.derive
assert_kernel_only TetraStereo.Engine.CentresRing.Molecular.check
assert_kernel_only TetraStereo.Engine.CentresRing.Molecular.Evidence.call_at
assert_kernel_only TetraStereo.Engine.CentresRing.Molecular.Evidence.same_layout
assert_kernel_only TetraStereo.Engine.CentresRing.Molecular.Publications.origin
assert_kernel_only TetraStereo.Engine.CentresRing.Molecular.checkSourceReceipt
assert_kernel_only TetraStereo.Engine.CentresRing.Molecular.Publications.update_origin
