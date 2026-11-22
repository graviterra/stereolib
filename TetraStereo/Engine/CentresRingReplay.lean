import TetraStereo.Engine.LocalizedChemicalRingPhysicalCertificate
import TetraStereo.Engine.CentresRingPaths
import Lean.Data.Json.FromToJson.Basic

set_option autoImplicit false

namespace TetraStereo.Engine.CentresRing

open OneCenter CertifiedLocalizedCIPInput
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? readback?)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedChemicalRing (Input Report)
open Lean (FromJson ToJson)

structure Comparison where
  left : Nat
  right : Nat
  value : Int
  deriving Repr, DecidableEq, FromJson, ToJson

structure Trial where
  mark : Option Nat
  start : List Nat
  comparisons : List Comparison
  deriving Repr, DecidableEq, FromJson, ToJson

structure Pass where
  after : Option Nat
  trials : List Trial
  groups : List Comparison
  deriving Repr, DecidableEq, FromJson, ToJson

structure Update where
  index : Nat
  pass : Pass
  label : String
  deriving Repr, DecidableEq, FromJson, ToJson

structure CenterTrace where
  discovered : List (List Nat)
  updates : List Update
  atom : Nat
  passes : List Pass
  label : String
  deriving Repr, DecidableEq, FromJson, ToJson

/-- Top-level sorter calls at one assignment occurrence, including the extra
adjacent comparisons for class discovery. The recursive subrules are inside
each call. -/
def Pass.comparisons (p : Pass) : List Comparison :=
  p.trials.flatMap Trial.comparisons ++ p.groups

def CenterTrace.comparisons (t : CenterTrace) : List Comparison :=
  t.passes.flatMap Pass.comparisons ++ t.updates.flatMap (fun u => u.pass.comparisons)

/-- Rule 1a on the two incident atoms. Its first unequal positive atomic
numbers decide immediately. Equal numbers defer to deeper comparisons. -/
def firstSphereValue (mol : RawMolecule) (a b : Nat) : Option Int := do
  let left ← mol.atoms[a]?
  let right ← mol.atoms[b]?
  let x := left.element.atomicNumber
  let y := right.element.atomicNumber
  if x == 0 || y == 0 || x == y then none else some (if x < y then -1 else 1)

def firstSphereAgrees (mol : RawMolecule) (cs : List Comparison) : Bool :=
  cs.all fun c => (firstSphereValue mol c.left c.right).all (c.value == ·)

theorem firstSphereAgrees_exact (mol : RawMolecule) (cs : List Comparison) :
    firstSphereAgrees mol cs = true ↔ ∀ c ∈ cs, ∀ v,
      firstSphereValue mol c.left c.right = some v → c.value = v := by
  simp only [firstSphereAgrees,List.all_eq_true]
  apply forall_congr'; intro c
  apply forall_congr'; intro _
  cases firstSphereValue mol c.left c.right <;> simp

theorem firstSphere_strict {mol : RawMolecule} {a b : Nat} {x y : AtomSpec}
    (left : mol.atoms[a]? = some x) (right : mol.atoms[b]? = some y)
    (px : 0 < x.element.atomicNumber) (py : 0 < y.element.atomicNumber)
    (distinct : x.element.atomicNumber ≠ y.element.atomicNumber) :
    firstSphereValue mol a b = some (if x.element.atomicNumber < y.element.atomicNumber then -1 else 1) := by
  simp [firstSphereValue,left,right,Nat.ne_of_gt px,Nat.ne_of_gt py,distinct]

private abbrev Check := Except String

private def need (p : Bool) (msg : String) : Check Unit :=
  if p then .ok () else .error msg

private def ascending {α : Type} [LE α] [DecidableLE α] (xs : List α) : List α :=
  replayListSort (fun a b => decide (a ≤ b)) xs

private def compareNext (a b : Nat) : StateT (List Comparison) Check Int := do
  let c :: rest ← get | throw "missing comparison"
  unless c.left == a && c.right == b do throw "comparison has wrong operands"
  set rest
  return c.value

/-- Java's stable insertion sort visits the sorted prefix from its last element. -/
private def insertNext (x : Nat) : List Nat → StateT (List Comparison) Check (List Nat)
  | [] => pure [x]
  | a :: rest => do
    if (← compareNext a x) < 0 then return a :: (← insertNext x rest)
    return x :: a :: rest

structure Ranking where
  order : List Nat
  unique : Bool
  pseudoCount : Nat
  deriving Repr, DecidableEq

def replaySort (t : Trial) : Check Ranking := do
  let (rev, rest) ← (t.start.foldlM (fun acc x => insertNext x acc) []).run t.comparisons
  need rest.isEmpty "unused sort comparisons"
  return ⟨rev.reverse, !(t.comparisons.any fun c => c.value == 0),
    t.comparisons.countP (fun c => c.value.natAbs > 1)⟩

private def partitions (order : List Nat) (cs : List Comparison) : Check Nat := do
  let adjacent := order.zip (order.drop 1)
  need (cs.map (fun c => (c.left, c.right)) == adjacent) "wrong grouping comparisons"
  return 1 + cs.countP (fun c => c.value != 0)

private def trialAfter (previous : Ranking) (slot : Nat) (t : Trial) : Check Ranking := do
  let some atom := previous.order[slot]? | throw "missing promotion slot"
  need (t.mark == some atom && t.start == previous.order) "promotion atom or starting order differs"
  replaySort t

private def ifUnique (r : Ranking) : Option Ranking := if r.unique then some r else none

/-- The four-real-ligand branches in the pinned Tetrahedral.label. In the four-way
case the second mark is slot one of the first promoted order. The first promoted
sort can retain ties. Equal geometric readings test even relative permutation. -/
def replayPass (geom : Geometry) (carriers : List Nat) (constitutional : Bool)
    (incoming : Option Nat) (p : Pass) : Check (Option Ranking) := do
  let t :: rest := p.trials | throw "missing initial sort"
  need (t.start.length == 4 && ascending t.start == ascending carriers) "wrong root ligands"
  need (t.mark == incoming) "inherited scalar reference differs"
  let initial ← replaySort t
  if initial.unique || constitutional then
    need (rest.isEmpty && p.groups.isEmpty) "unused promotion"
    need (p.after == incoming) "initial sort changed reference"
    return ifUnique initial
  match ← partitions initial.order p.groups, rest with
  | 2, [promoted] =>
    need p.after.isNone "two-class promotion did not clear reference"
    return ifUnique (← trialAfter initial 1 promoted)
  | 1, [first, second] =>
    let a ← trialAfter initial 0 first
    let b ← trialAfter a 1 second
    let some u := readback? geom a.order | throw "degenerate first promoted order"
    let some v := readback? geom b.order | throw "degenerate second promoted order"
    need (p.after == (if u == v then none else second.mark)) "four-way reference exit differs"
    return if u == v then ifUnique b else none
  | 3, [] | 4, [] =>
    need (p.after == incoming) "unpromoted tie changed reference"
    return none
  | _, _ => throw "wrong number of promotion trials"

def readRanking (geom : Geometry) : Option Ranking → Check (Option LocalizedAuxiliaryLabel)
  | none => .ok none
  | some r => do
    let some raw := readback? geom r.order | throw "missing spatial reading"
    return some (classifyTetrahedralRSPseudo raw r.pseudoCount)

def labelCode : Option LocalizedAuxiliaryLabel → String
  | none => "-"
  | some (.chiral .R) => "R"
  | some (.chiral .S) => "S"
  | some (.pseudoasymmetric .r) => "r"
  | some (.pseudoasymmetric .s) => "s"

def inventory (input : Input) : List Nat :=
  input.certified.canonicalTetrahedralCenters.map (fun c => c.1.val)

private def carriersAt (mol : RawMolecule) (atom : Nat) : Check (List Nat) :=
  match frameAtoms? mol (canonicalCenterRoot atom) with
  | some ids => .ok ids
  | none => .error "missing tetrahedral frame"

private def runUpdates (mol : RawMolecule) (geom : Geometry) : List (List Nat × Nat) → List Update →
    Option Nat → Check (Option Nat)
  | [], [], mark => .ok mark
  | (path,i) :: rest, u :: us, mark => do
    need (i == u.index) "auxiliary schedule differs"
    let some atom := path.head? | throw "empty auxiliary path"
    let rank ← replayPass geom (← carriersAt mol atom) false mark u.pass
    let label ← readRanking geom rank
    need (labelCode label == u.label) "auxiliary readback differs"
    runUpdates mol geom rest us u.pass.after
  | _, _, _ => .error "auxiliary inventory differs"

/-- Replay on an explicit molecular graph and coordinate lookup, including all auxiliary occurrences. -/
private def finalRankingCore (mol : RawMolecule) (geom : Geometry) (cs : List Nat) (t : CenterTrace) : Check (Option Ranking) := do
  let first :: rest := t.passes | throw "missing constitutional pass"
  let frame ← carriersAt mol t.atom
  match ← replayPass geom frame true none first, rest with
  | some r, [] =>
    need (t.discovered.isEmpty && t.updates.isEmpty) "unused auxiliaries"
    return some r
  | none, [full] =>
    let expected := if cs.any (· != t.atom) then molecularPaths mol t.atom cs else []
    need (ascending expected == ascending t.discovered) "molecular occurrence paths differ"
    let perCenter := cs.map fun c => t.discovered.filter (fun path => path.head? == some c)
    need (perCenter.flatten == t.discovered &&
      perCenter.all (fun ps => ps.map List.length == ascending (ps.map List.length)))
      "discovery is not in configuration and breadth-first order"
    let incoming ← runUpdates mol geom (scheduled t.discovered) t.updates first.after
    replayPass geom frame false incoming full
  | _, _ => throw "incorrect constitutional/full pass sequence"

/-- Independently check every direct atomic-number decision at the root and its
auxiliaries before interpreting the transcript. -/
def finalRankingOn (mol : RawMolecule) (geom : Geometry) (cs : List Nat) (t : CenterTrace) :
    Check (Option Ranking) :=
  if firstSphereAgrees mol t.comparisons then finalRankingCore mol geom cs t
  else .error "comparison contradicts incident atomic numbers"

def finalRanking (input : Input) (cs : List Nat) (t : CenterTrace) : Check (Option Ranking) :=
  finalRankingOn input.molecule (inputGeometry input.certified) cs t

def replayCenter (input : Input) (centers : List Nat) (t : CenterTrace) : Check (Option LocalizedAuxiliaryLabel) := do
  let rank ← finalRanking input centers t
  let label ← readRanking (inputGeometry input.certified) rank
  need (labelCode label == t.label) "pinned core and replay disagree"
  return label

/-- A report carries a kernel-checkable relation to every exact comparator transcript
used to accept it, including unassigned rows. -/
def ValidReport (input : Input) (centers : List Nat) (traces : List CenterTrace) (report : Report) : Prop :=
  centers.Nodup ∧ centers ⊆ inventory input ∧ report.map Prod.fst = centers ∧ List.Forall₂ (fun t row =>
    t.atom = row.1 ∧ replayCenter input centers t = .ok row.2) traces report

private def replayRows (input : Input) (centers : List Nat) : (ts : List CenterTrace) →
    Check { rows : Report // List.Forall₂ (fun t row =>
        t.atom = row.1 ∧ replayCenter input centers t = .ok row.2) ts rows }
  | [] => .ok ⟨[], .nil⟩
  | t :: rest => do
    match h : replayCenter input centers t with
    | .error msg => throw s!"center {t.atom}: {msg}"
    | .ok label =>
      let tail ← replayRows input centers rest
      return ⟨(t.atom,label) :: tail.1, .cons ⟨rfl,h⟩ tail.2⟩

def verify (input : Input) (ts : List CenterTrace) (centers : List Nat := inventory input) :
    Check {r : Report // ValidReport input centers ts r} := do
  if nd : centers.Nodup then
    if sub : centers ⊆ inventory input then
      let rows ← replayRows input centers ts
      if h : rows.1.map Prod.fst = centers then return ⟨rows.1,nd,sub,h,rows.2⟩
      else throw "center inventory mismatch"
    else throw "requested atom is not a detected center"
  else throw "duplicate requested center"

theorem readRanking_success_iff (g : Geometry) (r : Ranking) (label : LocalizedAuxiliaryLabel) :
    readRanking g (some r) = .ok (some label) ↔
      ∃ raw, readback? g r.order = some raw ∧ classifyTetrahedralRSPseudo raw r.pseudoCount = label := by
  cases h : readback? g r.order <;> simp [readRanking,h,pure,Except.pure]

/-- Every entry in an accepted report is backed by its own center transcript. -/
theorem entry_evidence {input : Input} {centers traces report} (ok : ValidReport input centers traces report)
    {row} (member : row ∈ report) :
    ∃ t ∈ traces, t.atom = row.1 ∧ replayCenter input centers t = .ok row.2 := by
  obtain ⟨nd,sub,ids,paired⟩ := ok
  clear nd sub ids
  induction paired with
  | nil => simp at member
  | cons here _ ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨_,List.mem_cons_self,here⟩
    · obtain ⟨t,mem,read⟩ := ih later
      exact ⟨t,List.mem_cons_of_mem _ mem,read⟩

private theorem center_read {input : Input} {cs t label} (h : replayCenter input cs t = .ok label) :
    ∃ rank, finalRanking input cs t = .ok rank ∧
      readRanking (inputGeometry input.certified) rank = .ok label ∧ labelCode label = t.label := by
  cases f : finalRanking input cs t with
  | error e => simp [replayCenter,f,bind,Except.bind] at h
  | ok rank =>
    refine ⟨rank,rfl,?_⟩
    cases r : readRanking (inputGeometry input.certified) rank with
    | error e => simp [replayCenter,f,r,bind,Except.bind] at h
    | ok obs =>
      by_cases same : labelCode obs = t.label
      · simp [replayCenter,f,r,need,same,bind,Except.bind,pure,Except.pure] at h
        subst label
        exact ⟨rfl,same⟩
      · simp [replayCenter,f,r,need,same,bind,Except.bind] at h

/-- Every accepted center supplies exact signed unit values for decisions won
immediately by Rule 1a, in every trial and auxiliary pass. -/
theorem firstSphere_evidence {input : Input} {cs ts report} (ok : ValidReport input cs ts report)
    {row} (mem : row ∈ report) :
    ∃ t ∈ ts, t.atom = row.1 ∧ ∀ c ∈ t.comparisons, ∀ v,
      firstSphereValue input.molecule c.left c.right = some v → c.value = v := by
  obtain ⟨t,ht,ha,h⟩ := entry_evidence ok mem
  obtain ⟨rank,hr,_,_⟩ := center_read h
  refine ⟨t,ht,ha,(firstSphereAgrees_exact _ _).mp ?_⟩
  cases hcheck : firstSphereAgrees input.molecule t.comparisons with
  | true => rfl
  | false => simp [finalRanking,finalRankingOn,hcheck] at hr

/-- A public success has an exact priority-ordered spatial reading and the actual
insertion-sort classification at this center. -/
theorem success_evidence {input : Input} {cs ts report} (ok : ValidReport input cs ts report)
    {a label} (mem : (a,some label) ∈ report) :
    ∃ t ∈ ts, t.atom = a ∧ ∃ r raw, finalRanking input cs t = .ok (some r) ∧
      readback? (inputGeometry input.certified) r.order = some raw ∧
      classifyTetrahedralRSPseudo raw r.pseudoCount = label ∧ labelCode (some label) = t.label := by
  obtain ⟨t,ht,ha,computed⟩ := entry_evidence ok mem
  obtain ⟨rank,rf,read,code⟩ := center_read computed
  cases rank with
  | none => cases read
  | some r =>
    obtain ⟨raw,spatial,meaning⟩ := (readRanking_success_iff _ r _).mp read
    exact ⟨t,ht,ha,r,raw,rf,spatial,meaning,code⟩

theorem refusal_evidence {input : Input} {cs ts report} (ok : ValidReport input cs ts report)
    {a} (mem : (a,none) ∈ report) :
    ∃ t ∈ ts, t.atom = a ∧ finalRanking input cs t = .ok none ∧ t.label = "-" := by
  obtain ⟨t,ht,ha,computed⟩ := entry_evidence ok mem
  obtain ⟨rank,rf,read,code⟩ := center_read computed
  cases rank with
  | none => exact ⟨t,ht,ha,rf,code.symm⟩
  | some r =>
    cases spatial : readback? (inputGeometry input.certified) r.order <;>
      simp [readRanking,spatial,pure,Except.pure] at read

end TetraStereo.Engine.CentresRing
assert_kernel_only TetraStereo.Engine.CentresRing.verify
assert_kernel_only TetraStereo.Engine.CentresRing.readRanking_success_iff
assert_kernel_only TetraStereo.Engine.CentresRing.success_evidence
assert_kernel_only TetraStereo.Engine.CentresRing.refusal_evidence
assert_kernel_only TetraStereo.Engine.CentresRing.firstSphere_strict
assert_kernel_only TetraStereo.Engine.CentresRing.firstSphere_evidence
