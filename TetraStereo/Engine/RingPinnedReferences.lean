import TetraStereo.Engine.CentresRingDerived
import TetraStereo.Engine.RingAtomicHorizon
import TetraStereo.Engine.RingFrozenSigned
import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey

set_option autoImplicit false

/-!
The source used here is Centres release 1.0, commit aaed608ee1d917fcd5f72964d9ca6227bd790804.
Within core/src/main/java/com/simolecule/centres, the relevant git blobs are
config/Tetrahedral.java (6ea6f360), rules/Rule6.java (e8b0f985), Digraph.java (e02b12cf)
and Labeller.java (dc3fe912). Configuration.java has blob 82ab9cdd. The comparison below concerns Rule6.compare on real
atom identities, including duplicate occurrences of a real atom. SequenceRule.recursiveCompare
may decide earlier, e.g. on node degree, without consulting this comparison.
-/

namespace TetraStereo.Engine.CentresRing.PinnedReferences

open OneCenter CertifiedLocalizedCIPInput AuthoritativeCIPMoleculeCursorRanking
open LocalizedGenericMarkedRecalculation (Geometry readback?)
open RingChemicalPriority.AtomicHorizon (horizon Reach)
open RingChemicalPriority.FrozenSigned (visited)
open Molecular

/-- Rule6.java lines 43–56 compare endpoint atom identities against one digraph register.
Two occurrences of the marked atom compare equal under this primitive. -/
def compareMark (mark : Option Nat) (left right : Nat) : Int :=
  if mark == some left && mark != some right then 1
  else if mark != some left && mark == some right then -1 else 0

theorem compareMark_spec (mark : Option Nat) (left right : Nat) :
    (compareMark mark left right = 1 ↔ mark = some left ∧ left ≠ right) ∧
    (compareMark mark left right = -1 ↔ mark = some right ∧ left ≠ right) ∧
    (compareMark mark left right = 0 ↔ (mark = some left ↔ mark = some right)) := by
  by_cases a : mark = some left <;> by_cases b : mark = some right <;>
    by_cases e : left = right <;> simp_all [compareMark]

/-- The projection used by the molecular mark column has the same comparison
as the release atom-identity primitive. -/
theorem compareMark_column (mark : Option Nat) (left right : Nat) :
    compareMark mark left right =
      (if mark == some left then (1 : Int) else 0) - (if mark == some right then 1 else 0) := by
  by_cases a : mark = some left <;> by_cases b : mark = some right <;> by_cases e : left = right <;> simp_all [compareMark]

/-- One atomic write replaces the previous register for every recursive read.
In particular the overwritten atom and an unmarked third atom now tie. -/
theorem overwritten_atom_ties (old new other : Nat) (different : old ≠ new) (third : other ≠ new) :
    compareMark (some new) old other = 0 := by
  apply ((compareMark_spec ..).2.2).mpr
  simp [Ne.symm different,Ne.symm third]

private theorem visited_exact {m root} (bound : root < m.atomCount) (wf : m.WellFormed) {c}
    (eligible : CanonicalCenterRerootCursor m root c) (n : Nat) (enough : moleculeCursorHeight m c ≤ n) (u) :
    u ∈ visited m (n+1) c ↔ Reach m c u := by
  induction n generalizing c u with
  | zero =>
    have leaf : c.children m = [] := by
      cases es : c.children m with
      | nil => rfl
      | cons x xs =>
        have lt := moleculeCursorHeight_child_lt bound wf eligible (show x ∈ c.children m by simp [es])
        omega
    simp only [visited,leaf,List.flatMap_nil,List.mem_singleton]
    constructor
    · rintro rfl; exact .here _
    · intro reached
      cases reached with
      | here => rfl
      | via step _ => simp [leaf] at step
  | succ n ih =>
    rw [visited,List.mem_cons,List.mem_flatMap]
    constructor
    · rintro (rfl | ⟨v,edge,found⟩)
      · exact .here _
      · have lt := moleculeCursorHeight_child_lt bound wf eligible edge
        exact .via edge ((ih (eligible.child edge) (by omega) _).mp found)
    · intro reached
      cases reached with
      | here => exact Or.inl rfl
      | via edge more =>
        have lt := moleculeCursorHeight_child_lt bound wf eligible edge
        exact Or.inr ⟨_,edge,(ih (eligible.child edge) (by omega) _).mpr more⟩

/-- Complete inventory of marked occurrences in any retained arm, including the
upward side of a reroot and duplicate leaves. No receipt, width, or caller fuel. -/
def markedOccurrences (m : RawMolecule) (mark : Option Nat) (c : CanonicalRerootCursor) :=
  (visited m (horizon m + 1) c).filter fun u => mark == some u.node.atom

theorem markedOccurrences_exact {m root} (bound : root < m.atomCount) (wf : m.WellFormed)
    {n} (site : CanonicalCenterTreeNode m root n) {c} (edge : c ∈ occurrenceLigandCursors m n)
    (mark : Option Nat) (u) :
    u ∈ markedOccurrences m mark c ↔ Reach m c u ∧ mark = some u.node.atom := by
  have eligible := occurrenceLigandCursor_eligible site edge
  simp only [markedOccurrences,List.mem_filter,beq_iff_eq]
  exact and_congr_left' (visited_exact bound wf eligible (horizon m) (moleculeCursorHeight_le_two_mul_atomCount_add_one bound wf eligible) u)

/-- The coordinate-free parity test used on two permutations of the same
four distinct carrier objects (Configuration.parity4 returns 1 on odd). -/
def evenOrders (first second : List Nat) : Bool :=
  RawMolecule.permutationIsEven (second.map first.idxOf)

theorem evenOrders_eq_readings {g : Geometry} {first second : List Nat} {u v : RS}
    (unique : first.Nodup) (four : first.length = 4) (perm : second.Perm first)
    (lhs : readback? g first = some u) (rhs : readback? g second = some v) :
    evenOrders first second = (u == v) := by
  let positions := second.map first.idxOf
  have indices : positions.Perm [0,1,2,3] := by
    have id : first.map first.idxOf = List.range first.length := by
      calc
        _ = ((List.finRange first.length).map (fun i : Fin first.length => first[i.val])).map first.idxOf := by
          rw [List.map_getElem_finRange]
        _ = _ := by simp only [List.map_map,Function.comp_def,unique.idxOf_getElem,List.map_coe_finRange_eq_range]
    have mapped := perm.map first.idxOf
    rwa [id,four] at mapped
  have select (xs : List Nat) (inside : ∀ x ∈ xs, x ∈ first) :
      LocalizedGenericMarkedRecalculation.atomsAt? first (xs.map first.idxOf) = some xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      have head := List.getElem?_idxOf (inside _ List.mem_cons_self)
      have rest := ih (fun a ha => inside a (List.mem_cons_of_mem _ ha))
      simp only [LocalizedGenericMarkedRecalculation.atomsAt?,List.map_cons,List.mapM_cons,head]
      change (LocalizedGenericMarkedRecalculation.atomsAt? first (xs.map first.idxOf)).bind _ = _
      rw [rest]
      rfl
  have chosen := select second (fun _ h => perm.mem_iff.mp h)
  rcases first with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,tail⟩⟩⟩⟩ <;> simp at four
  subst tail
  have transport := LocalizedMarkedConfigurationTransport.reordered_readback_partial g ![a,b,c,d] positions indices
  change (LocalizedGenericMarkedRecalculation.atomsAt? [a,b,c,d] positions).bind (readback? g) = _ at transport
  change LocalizedGenericMarkedRecalculation.atomsAt? [a,b,c,d] positions = some second at chosen
  rw [chosen] at transport
  change readback? g second = if RawMolecule.permutationIsEven positions then readback? g [a,b,c,d]
    else (readback? g [a,b,c,d]).map RS.swap at transport
  rw [lhs,rhs] at transport
  change RawMolecule.permutationIsEven positions = _
  cases e : RawMolecule.permutationIsEven positions <;> cases u <;> cases v <;> simp [e,RS.swap] at transport ⊢

/-- The release's 24 return branches, in Configuration.java:75–151 order.
The entries are the target indices matched by the four reference objects. -/
def configurationParity4 : List Nat → Nat
  | [0,1,2,3] => 2
  | [0,1,3,2] => 1
  | [0,2,1,3] => 1
  | [0,2,3,1] => 2
  | [0,3,2,1] => 1
  | [0,3,1,2] => 2
  | [1,0,2,3] => 1
  | [1,0,3,2] => 2
  | [1,2,0,3] => 2
  | [1,2,3,0] => 1
  | [1,3,2,0] => 2
  | [1,3,0,2] => 1
  | [2,1,0,3] => 1
  | [2,1,3,0] => 2
  | [2,0,1,3] => 2
  | [2,0,3,1] => 1
  | [2,3,0,1] => 2
  | [2,3,1,0] => 1
  | [3,1,2,0] => 1
  | [3,1,0,2] => 2
  | [3,2,1,0] => 2
  | [3,2,0,1] => 1
  | [3,0,2,1] => 2
  | [3,0,1,2] => 1
  | _ => 0

/-- The actual parity table and the inversion-parity test agree for all 24
orders; no calibrated geometry is needed for the one-class early-exit test. -/
theorem source_parity (positions : List Nat) (perm : positions.Perm [0,1,2,3]) :
    configurationParity4 positions = if RawMolecule.permutationIsEven positions then 2 else 1 := by
  have all : ([0,1,2,3] : List Nat).permutations'.all
      (fun p => configurationParity4 p == (if RawMolecule.permutationIsEven p then 2 else 1)) = true := by decide +kernel
  exact beq_iff_eq.mp (List.all_eq_true.mp all _ (List.mem_permutations'.mpr perm))

/-- Pinned store actions. An assignment with no promotion preserves even a
nonempty incoming register. The two-class branch and an even four-way branch
clear it. The odd four-way exit bypasses the clear and retains the second mark. -/
inductive Write where
  | unchanged
  | clear
  | retain (atom : Nat)
  deriving DecidableEq, Repr

def Write.apply : Write → Option Nat → Option Nat
  | .unchanged,old => old
  | .clear,_ => none
  | .retain a,_ => some a

/-- Source-level four-carrier pass. Every promoted sort receives the same
published facts as the base sort. Inputs are operations on an actual frame,
so a sort may inspect its mark recursively at any occurrence. Its next
carrier selection uses the previous sort's output. -/
structure Queries where
  sort : Molecular.Frame → List Nat → Option Ranking
  groups : Molecular.Frame → List Nat → Option Nat

structure Episode where
  markReads : List (Option Nat)
  write : Write
  result : Option Ranking
  deriving Repr

private def uniqueOnly (r : Ranking) : Option Ranking := if r.unique then some r else none

def run (q : Queries) (f : Molecular.Frame) (start : List Nat) : Option Episode := do
  guard (start.length = 4)
  let base ← q.sort f start
  if base.unique || f.constitutional then return ⟨[f.mark],.unchanged,uniqueOnly base⟩
  match ← q.groups f base.order with
  | 2 =>
    let a ← base.order[1]?
    let one ← q.sort {f with mark := some a} base.order
    return ⟨[f.mark,some a],.clear,uniqueOnly one⟩
  | 1 =>
    let a ← base.order[0]?
    let one ← q.sort {f with mark := some a} base.order
    let b ← one.order[1]?
    let two ← q.sort {f with mark := some b} one.order
    if evenOrders one.order two.order then return ⟨[f.mark,some a,some b],.clear,uniqueOnly two⟩
    else return ⟨[f.mark,some a,some b],.retain b,none⟩
  | _ => return ⟨[f.mark],.unchanged,none⟩

/-- Every normal execution has one of precisely these register histories. The
unmodified snapshot fields in each judgement bind both the retained original
path and the published auxiliary facts at every promoted query. -/
inductive Execution (q : Queries) (f : Molecular.Frame) (start : List Nat) : Episode → Prop where
  | initial {r} : q.sort f start = some r → (r.unique || f.constitutional) = true →
    Execution q f start ⟨[f.mark],.unchanged,uniqueOnly r⟩
  | other {r groups} : q.sort f start = some r → (r.unique || f.constitutional) = false →
    q.groups f r.order = some groups → groups ≠ 1 → groups ≠ 2 →
    Execution q f start ⟨[f.mark],.unchanged,none⟩
  | two {r a u} : q.sort f start = some r → (r.unique || f.constitutional) = false →
    q.groups f r.order = some 2 → r.order[1]? = some a →
    q.sort {f with mark := some a} r.order = some u →
    Execution q f start ⟨[f.mark,some a],.clear,uniqueOnly u⟩
  | four {r a u b v} : q.sort f start = some r → (r.unique || f.constitutional) = false →
    q.groups f r.order = some 1 → r.order[0]? = some a →
    q.sort {f with mark := some a} r.order = some u → u.order[1]? = some b →
    q.sort {f with mark := some b} u.order = some v →
    Execution q f start (if evenOrders u.order v.order then ⟨[f.mark,some a,some b],.clear,uniqueOnly v⟩
      else ⟨[f.mark,some a,some b],.retain b,none⟩)

theorem run_exact (q : Queries) (f : Molecular.Frame) (xs : List Nat) (four : xs.length = 4) (e : Episode) :
    run q f xs = some e ↔ Execution q f xs e := by
  constructor
  · intro h
    unfold run at h
    simp only [four,guard,if_true,pure,Pure.pure,Option.bind_some,Bind.bind] at h
    cases base : q.sort f xs with
    | none => simp [base] at h
    | some r =>
      rw [base] at h
      simp only [Option.bind_some] at h
      by_cases initial : (r.unique || f.constitutional) = true
      · simp [initial] at h; exact h ▸ .initial base initial
      · have no := Bool.eq_false_iff.mpr initial
        simp only [no,Bool.false_eq_true,if_false] at h
        cases groups : q.groups f r.order with
        | none => simp [groups] at h
        | some k =>
          rw [groups] at h
          simp only [Option.bind_some] at h
          match k with
          | 1 =>
            simp only [Option.bind_eq_some_iff] at h
            obtain ⟨a,ha,u,hu,b,hb,v,hv,last⟩ := h
            have got := Execution.four base no groups ha hu hb hv
            cases even : evenOrders u.order v.order <;> simp [even] at last got <;> exact last ▸ got
          | 2 =>
            simp only [Option.bind_eq_some_iff,Option.some.injEq] at h
            obtain ⟨a,ha,u,hu,last⟩ := h
            exact last ▸ .two base no groups ha hu
          | 0 =>
            simp only [Option.some.injEq] at h
            exact h ▸ .other base no groups (by decide) (by decide)
          | n+3 =>
            simp only [Option.some.injEq] at h
            exact h ▸ .other base no groups (by omega) (by omega)
  · intro ex
    cases ex with
    | initial base flag =>
      simp only [run,four,guard,if_true,pure,Pure.pure,Bind.bind,Option.bind_some,base,flag]
    | @other r k base flag groups n1 n2 =>
      simp only [run,four,guard,if_true,pure,Pure.pure,Bind.bind,Option.bind_some,base,flag,Bool.false_eq_true,if_false,groups]
    | two base flag groups sel promoted =>
      simp only [run,four,guard,if_true,pure,Pure.pure,Bind.bind,Option.bind_some,base,flag,Bool.false_eq_true,if_false,groups,sel,promoted]
    | four base flag groups ha hu hb hv =>
      simp only [run,four,guard,if_true,pure,Pure.pure,Bind.bind,Option.bind_some,base,flag,Bool.false_eq_true,if_false,groups,ha,hu,hb,hv]
      split <;> rfl

/-- A query at this point is computed from the retained molecular frame and its
atomic, isotope and published stereochemical rows. None means insufficient
comparison coverage, preserved by the controller. -/
private def molecularCompare (f : Molecular.Frame) :
    Option (Nat → Nat → Option Int) := do
  let reader ← prepare f
  return fun a b => do
    let ts ← reader a b
    return (← decideSteps (results ts.val)).2

/-- Java Sort.prioritise inspects the already sorted prefix from its last
element. Tied comparisons stop insertion and count against uniqueness. -/
private def insert (cmp : Nat → Nat → Option Int) (a : Nat) :
    List Nat → Option (List Nat × List Int)
  | [] => some ([a],[])
  | b :: rest => do
    let v ← cmp b a
    if v < 0 then
      let (ys,vs) ← insert cmp a rest
      return (b :: ys,v :: vs)
    else return (a :: b :: rest,[v])

private def sort (f : Molecular.Frame) (xs : List Nat) : Option Ranking := do
  let cmp ← molecularCompare f
  let (ys,vs) ← xs.foldlM (fun (p : List Nat × List Int) a => do
    let (next,values) ← insert cmp a p.1
    return (next,values ++ p.2)) ([],[])
  return ⟨ys.reverse,vs.all (· != 0),vs.countP (fun v => v.natAbs > 1)⟩

private def groups (f : Molecular.Frame) (xs : List Nat) : Option Nat := do
  let cmp ← molecularCompare f
  let values ← (xs.zip (xs.drop 1)).mapM fun (a,b) => cmp a b
  return 1 + values.countP (· != 0)

def molecularQueries : Queries := ⟨sort,groups⟩

/-- Execute at the fixed original occurrence; no source comparisons, selected
slots, auxiliary regeneration oracle, or receipt are inputs to the promoted runs. -/
def molecularRun (mol : RawMolecule) (focus : List Nat) (published : List PairList.Publication)
    (incoming : Option Nat) (constitutional : Bool) (start : List Nat) : Option Episode := do
  let atom ← focus.getLast?
  guard (start.Perm (bondedAtoms mol atom))
  run molecularQueries ⟨mol,focus,published,incoming,constitutional⟩ start

theorem molecularRun_exact (mol : RawMolecule) (focus : List Nat) (published : List PairList.Publication)
    (incoming : Option Nat) (constitutional : Bool) (start : List Nat) (atom : Nat)
    (reached : focus.getLast? = some atom) (four : start.length = 4) (e : Episode) :
    molecularRun mol focus published incoming constitutional start = some e ↔
      start.Perm (bondedAtoms mol atom) ∧ Execution molecularQueries ⟨mol,focus,published,incoming,constitutional⟩ start e := by
  by_cases perm : start.Perm (bondedAtoms mol atom) <;> simp [molecularRun,reached,guard,perm,run_exact _ _ _ four]

/-- One successful molecular assignment inherited its register exclusively from
the last preceding assignment in the original digraph. Changing the root does
not inspect the history for an older nonempty register. -/
theorem publication_register {mol g discovery pubs updates mark}
    (chain : Publications mol g discovery pubs updates mark) :
    mark = (updates.getLast?.bind (fun u => u.pass.after)) := by
  cases chain with
  | empty => rfl
  | next _ _ _ _ _ => simp

/-- Every visit in an existing molecular derivation has its exact prior register
and strict-depth auxiliary snapshot, even if a previous pass left a mark on
returning Unknown. -/
theorem molecular_publication_scope {mol g discovery pubs updates mark}
    (chain : Publications mol g discovery pubs updates mark) {u : Update} (mem : u ∈ updates) :
    ∃ (old : List PairList.Publication) (earlier : List Update), ∃ p start a label,
      Publications mol g discovery old earlier (earlier.getLast?.bind (fun v => v.pass.after)) ∧
      discovery[u.index]? = some p.reverse ∧
      derivePass ⟨mol,p,PairList.publishedAt old p,earlier.getLast?.bind (fun v : Update => v.pass.after),false⟩ g start = some a ∧
      readRanking g a.rank = .ok label ∧ u.pass = a.pass ∧ u.label = labelCode label := by
  obtain ⟨old,earlier,prev,p,start,a,label,prior,addr,computed,read,pass,code⟩ := chain.update_origin mem
  exact ⟨old,earlier,p,start,a,label,publication_register prior ▸ prior,addr,publication_register prior ▸ computed,read,pass,code⟩


/-- Retaining the older atom is observably different on the existing joint
reference vector. If a reached pair ends at the old atom and at a third
atom, the old column distinguishes them and the pinned new scalar ties.
This conclusion is about the reference observation at that pair. -/
theorem accumulated_vector_differs (i : CertifiedLocalizedCIPInput) {fuel : Nat}
    (old new other : i.Atom) (left right : i.LocalizedRerootCursor fuel)
    (leftAtom : left.occurrence.1.node.current? = some old)
    (rightAtom : right.occurrence.1.node.current? = some other)
    (on : old ≠ new) (tn : other ≠ new) (to' : other ≠ old) :
    LocalizedChemicalRingJointMarkerKey.referenceVector i [old,new] left = [1,0] ∧
    LocalizedChemicalRingJointMarkerKey.referenceVector i [old,new] right = [0,0] ∧
    compareMark (some new.val) old.val other.val = 0 := by
  refine ⟨?_,?_,overwritten_atom_ties _ _ _ (Fin.val_injective.ne on) (Fin.val_injective.ne tn)⟩ <;>
    simp [LocalizedChemicalRingJointMarkerKey.referenceVector,LocalizedMarkedRetainedPromotedKey.referenceBit,
      leftAtom,rightAtom,on,tn,to']

/-- A successful pass can retain a newly written atom only on the odd,
return-Unknown exit. The old register is not restored by any promotion. -/
theorem retained_iff_odd {q : Queries} {f : Molecular.Frame} {xs : List Nat} {e : Episode}
    (four : xs.length = 4) (exec : Execution q f xs e) (b : Nat) :
    e.write = .retain b ↔ ∃ r a u v,
      q.sort f xs = some r ∧ (r.unique || f.constitutional) = false ∧ q.groups f r.order = some 1 ∧
      r.order[0]? = some a ∧ q.sort {f with mark := some a} r.order = some u ∧ u.order[1]? = some b ∧
      q.sort {f with mark := some b} u.order = some v ∧ evenOrders u.order v.order = false := by
  constructor
  · intro kept
    cases exec with
    | initial | other | two => contradiction
    | @four r a u b' v base flag groups ha hu hb hv =>
      cases even : evenOrders u.order v.order <;> simp [even] at kept
      subst b'
      exact ⟨r,a,u,v,base,flag,groups,ha,hu,hb,hv,even⟩
  · rintro ⟨r,a,u,v,base,flag,groups,ha,hu,hb,hv,odd⟩
    have direct := Execution.four base flag groups ha hu hb hv
    rw [odd] at direct
    have h := (run_exact q f xs four _).mpr exec
    have k := (run_exact q f xs four _).mpr direct
    have eq := Option.some.inj (h.symm.trans k)
    rw [eq]
    rfl


/-- Across any number of visits to different nodes of one digraph, only the
last explicit clear or retaining exit determines the next scalar. If there
are no writes the initial scalar survives. -/
def advance (old : Option Nat) (exits : List Write) := exits.foldl (fun mark w => w.apply mark) old

theorem no_restore (old : Option Nat) (pre post : List Write) (w : Write) (changed : w ≠ .unchanged)
    (quiet : ∀ u ∈ post, u = .unchanged) :
    advance old (pre ++ w :: post) = w.apply none := by
  have keep (xs : List Write) (h : ∀ u ∈ xs, u = .unchanged) (start : Option Nat) :
      advance start xs = start := by
    induction xs generalizing start with
    | nil => rfl
    | cons a xs ih =>
      obtain rfl := h a List.mem_cons_self
      exact ih (fun u hu => h u (List.mem_cons_of_mem _ hu)) start
  unfold advance
  rw [List.foldl_append,List.foldl_cons]
  change advance _ post = _
  rw [keep post quiet]
  cases w <;> simp_all [Write.apply]

end TetraStereo.Engine.CentresRing.PinnedReferences

assert_kernel_only TetraStereo.Engine.CentresRing.PinnedReferences.compareMark_spec
assert_kernel_only TetraStereo.Engine.CentresRing.PinnedReferences.markedOccurrences_exact
assert_kernel_only TetraStereo.Engine.CentresRing.PinnedReferences.evenOrders_eq_readings
assert_kernel_only TetraStereo.Engine.CentresRing.PinnedReferences.run_exact
assert_kernel_only TetraStereo.Engine.CentresRing.PinnedReferences.molecularRun_exact
assert_kernel_only TetraStereo.Engine.CentresRing.PinnedReferences.molecular_publication_scope
assert_kernel_only TetraStereo.Engine.CentresRing.PinnedReferences.accumulated_vector_differs
assert_kernel_only TetraStereo.Engine.CentresRing.PinnedReferences.retained_iff_odd
assert_kernel_only TetraStereo.Engine.CentresRing.PinnedReferences.no_restore
assert_kernel_only TetraStereo.Engine.CentresRing.PinnedReferences.source_parity
