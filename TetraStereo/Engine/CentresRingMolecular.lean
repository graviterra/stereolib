import TetraStereo.Engine.CentresRingPairList
import TetraStereo.Engine.CentresRingMolecularMass

set_option autoImplicit false

namespace TetraStereo.Engine.CentresRing.Molecular
open OneCenter CertifiedLocalizedCIPInput

inductive Rule where
  | atomicNumber | duplicate | isotope | geometric | stereoClass | likePair | lower | handedPair | reference
  deriving DecidableEq, Repr, Inhabited

abbrev Steps := List (Rule × Option Int)

/-- Unknown rule evidence halts the derivation. A later winner is reachable
only after an explicit zero at every preceding position. -/
def decideSteps : Steps → Option (Option Rule × Int)
  | [] => some (none,0)
  | (_,none) :: _ => none
  | (r,some v) :: tail => if v = 0 then decideSteps tail else some (some r,v)

theorem winner_iff (xs : Steps) (r : Rule) (v : Int) :
    decideSteps xs = some (some r,v) ↔ v ≠ 0 ∧ ∃ before after,
      xs = before ++ (r,some v) :: after ∧ ∀ step ∈ before, step.2 = some 0 := by
  induction xs with
  | nil =>
    constructor
    · simp [decideSteps]
    · rintro ⟨_,before,after,h,_⟩
      cases before <;> simp at h
  | cons hd tl ih =>
    rcases hd with ⟨k,x⟩
    constructor
    · cases x with
      | none => simp [decideSteps]
      | some w =>
        by_cases zero : w = 0
        · subst w
          intro h
          obtain ⟨hv,b,a,e,ties⟩ := ih.mp (by simpa [decideSteps] using h)
          exact ⟨hv,(k,some 0)::b,a,by simp [e],by simpa using ties⟩
        · intro h
          obtain ⟨rfl,rfl⟩ : k = r ∧ w = v := by simpa [decideSteps,zero] using h
          exact ⟨zero,[],tl,rfl,by simp⟩
    · rintro ⟨hv,b,a,e,ties⟩
      cases b with
      | nil => cases e; simp [decideSteps,hv]
      | cons h rest =>
        cases e
        have hx := ties (k,x) (by simp)
        change x = some 0 at hx
        subst x
        simp only [decideSteps]
        apply ih.mpr
        exact ⟨hv,rest,a,rfl,fun s hs => ties s (List.mem_cons_of_mem _ hs)⟩

theorem tie_iff (xs : Steps) : decideSteps xs = some (none,0) ↔
    ∀ step ∈ xs, step.2 = some 0 := by
  induction xs with
  | nil => simp [decideSteps]
  | cons hd tl ih =>
    rcases hd with ⟨k,_ | v⟩
    · simp [decideSteps]
    · by_cases h : v = 0 <;> simp [decideSteps,h,ih]

private def sign {α : Type} [Ord α] (a b : α) : Int :=
  match compare a b with | .lt => -1 | .eq => 0 | .gt => 1

/-- Concatenate corresponding breadth-first layers of sibling subtrees. -/
private def joinLevels {α : Type} : List (List α) → List (List α) → List (List α)
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x ++ y) :: joinLevels xs ys

/-- The geometric and unseeded pair columns have zero local values on this
tetrahedral profile. Their recursive comparisons still visit branch arities. -/
private inductive Col where
  | z | dup | mass | geo | kind | likeWalk | lower | handWalk | mark | likeR | likeS | handR | handS
  deriving DecidableEq, Repr

private def columns (i : Col) : List Col :=
  let atoms := [Col.z,.dup,.mass]
  let base := atoms ++ [.geo,.kind]
  let natural := base ++ [.likeWalk]
  let stereo := natural ++ [.lower]
  match i with
  | .z => [.z] | .dup => [.z,.dup] | .mass => atoms
  | .geo => atoms ++ [.geo] | .kind => base | .likeWalk => natural
  | .lower => stereo | .handWalk => stereo ++ [.handWalk] | .mark => stereo ++ [.handWalk,.mark]
  | .likeR | .likeS => natural ++ [i]
  | .handR | .handS => stereo ++ [.handWalk,i]

private structure Column where
  localValue : Nat
  key : List (List Nat)
  levels : List (List (List Nat))
  /-- One entry per nonterminal visited node, grouped by distance. -/
  readings : List (List (Option RS))
  deriving Inhabited

private structure Candidate where
  ranks : List Nat
  right : Nat
  left : Nat

private structure Arm where
  data : Col → Column
  firstGroup : Option Candidate
  hasChildren : Bool

private def shallow (n : Arm) (i : Col) := (columns i).map fun j => (n.data j).localValue
private def deep (n : Arm) (i : Col) := (columns i).map fun j => (n.data j).key
private def descending {α : Type} [Ord α] (key : Arm → α) :=
  replayListSort (fun a b => compare (key a) (key b) != .lt)

private def earlier (a b : Candidate) : Ordering :=
  if a.ranks.length != b.ranks.length then compare a.ranks.length b.ranks.length
  else compare a.ranks b.ranks

private def preferred (old : Option Candidate) (v : Candidate) : Option Candidate :=
  match old with
  | none => some v
  | some a => match earlier a v with
    | .lt => some a | .gt => some v
    | .eq => some {a with right := a.right+v.right, left := a.left+v.left}

/-- In a natural-reference walk, distance precedes the sequence of child-group
indices. Tied parent groups pool their counts at the same child-group index. -/
private def findGroup (hand : Option RS) (children : List Arm) : Option Candidate :=
  match hand with
  | some .R => some ⟨[],1,0⟩ | some .S => some ⟨[],0,1⟩
  | none => Id.run do
    let mut best := none
    let mut prev : Option (List (List (List Nat))) := none
    let mut group := 0
    for c in descending (deep · .kind) (children.filter (·.hasChildren)) do
      let key := deep c .kind
      if prev.isSome && prev != some key then group := group+1
      prev := some key
      if let some g := c.firstGroup then
        best := preferred best {g with ranks := group :: g.ranks}
    return best

private def makeColumn (children : List Arm) (scalar : Col → Nat) (hand : Option RS) (i : Col) : Column :=
  let sh := descending (shallow · i) children
  let ds := descending (deep · i) children
  let childrenRow (cs : List Arm) := cs.map fun c => (c.data i).localValue
  let levels := [childrenRow sh,childrenRow ds] ::
    ds.foldr (fun c acc => joinLevels (c.data i).levels acc) []
  let walk := [hand] :: ds.foldr (fun c acc =>
    if c.hasChildren then joinLevels (c.data i).readings acc else acc) []
  ⟨scalar i,[scalar i] :: levels.flatten,levels,walk⟩

/-- Reverse addresses refer to the originally rooted digraph. A repeated
endpoint is a terminal ring duplicate. Parent traversal carries the original
occurrence and its original duplicate depth when an auxiliary is rerooted. -/
private def neighbors (mol : RawMolecule) : List Nat → List (List Nat)
  | [] => []
  | a :: tail =>
    if tail.contains a then [tail] else (bondedAtoms mol a).map fun b =>
      if tail.head? == some b then tail else b :: a :: tail

private def grow (mol : RawMolecule) (pub : List PairList.Publication) (mark : Option Nat) :
    Nat → List Nat → List Nat → Option Arm
  | 0, _, _ => none
  | fuel+1, path, previous => do
    let a ← path.head?
    let atom ← mol.atoms[a]?
    guard (atom.element.atomicNumber > 0)
    let ns := (neighbors mol path).filter (· != previous)
    let cs ← ns.mapM fun n => grow mol pub mark fuel n path
    let addr := path.reverse
    let dup := path.tail.contains a
    let code := ((pub.find? (fun f => f.path == addr)).map (·.code)).getD "-"
    let hand := if code == "R" then some RS.R else if code == "S" then some RS.S else none
    let scalar : Col → Nat := fun
      | .z => atom.element.atomicNumber
      | .dup => if dup then mol.atomCount + 1 - addr.idxOf a else 0
      | .mass => massMicro atom.element.atomicNumber (if dup then 0 else atom.isotope?.getD 0)
      | .geo | .likeWalk | .handWalk => 0
      | .kind => if hand.isSome then 2 else if code == "r" || code == "s" then 1 else 0
      | .lower => if code == "r" then 2 else if code == "s" then 1 else 0
      | .mark => if mark == some a then 1 else 0
      | .likeR | .handR => if hand == some .R then 1 else 0
      | .likeS | .handS => if hand == some .S then 1 else 0
    -- Materialize the columns once. A function that recomputes each
    -- column when a parent reads it expands recursively in the interpreter.
    let data := [Col.z,.dup,.mass,.geo,.kind,.likeWalk,.lower,.handWalk,.mark,.likeR,.likeS,.handR,.handS].map
      (fun i => makeColumn cs scalar hand i)
    return ⟨fun i => data[i.ctorIdx]!,findGroup hand cs,!cs.isEmpty⟩

private def seeds (a : Arm) : List RS :=
  match a.firstGroup with
  | none => []
  | some g => if g.left < g.right then [.R] else if g.right < g.left then [.S] else [.R,.S]

private def bits (a : Arm) (seed : RS) (natural gaps : Bool) : List Nat :=
  let i := match natural,seed with
    | true,.R => Col.likeR | true,.S => .likeS | false,.R => .handR | false,.S => .handS
  (a.data i).readings.flatten.filterMap fun h =>
    if gaps || h.isSome then some (if h == some seed then 1 else 0) else none

private def pairCompare (xs ys : List Nat) : Option Int :=
  if xs.length == ys.length then some (sign xs ys) else none

/-- The actual molecular observations being compared. For ordinary rules
the first row is the immediate value. Subsequent rows are the shallow and
deep child groups in breadth-first order. Rule 5 keeps both seeded lists. -/
inductive Test where
  | rows (left right : List (List Nat))
  | paired (leftR rightR leftS rightS : List Nat)
  | followed (atRoot structural : Test)
  | unavailable
  deriving Repr, Inhabited

def Test.value : Test → Option Int
  | .rows l r => some (sign l r)
  | .paired lr rr ls rs => do
    return PairList.combine (← pairCompare lr rr) (← pairCompare ls rs)
  | .followed direct walk => do
    let v ← direct.value
    if v = 0 then walk.value else some v
  | .unavailable => none

def Test.Tied : Test → Prop
  | .rows l r => l = r
  | .paired lr rr ls rs => lr = rr ∧ ls.length = rs.length
  | .followed direct walk => direct.Tied ∧ walk.Tied
  | .unavailable => False

private theorem sign_zero {α : Type} [Ord α] [Std.LawfulEqOrd α] (a b : α) :
    sign a b = 0 ↔ a = b := by
  calc
    sign a b = 0 ↔ compare a b = .eq := by
      cases h : compare a b <;> simp only [sign,h] <;> decide
    _ ↔ a = b := Std.compare_eq_eq_iff_eq

private theorem combine_zero (r s : Int) : PairList.combine r s = 0 ↔ r = 0 := by
  unfold PairList.combine
  split_ifs <;> simp_all
  all_goals omega

theorem Test.zero_iff (t : Test) : t.value = some 0 ↔ t.Tied := by
  induction t with
  | followed direct walk ih jw =>
    cases h : direct.value with
    | none => simp_all [Test.value,Test.Tied]
    | some v => by_cases hv : v = 0 <;> simp_all [Test.value,Test.Tied]
  | unavailable => simp [Test.value,Test.Tied]
  | rows l r => simp [Test.value,Test.Tied,sign_zero]
  | paired a b c d =>
    by_cases h : a.length = b.length <;> by_cases k : c.length = d.length
    all_goals simp [Test.value,Test.Tied,pairCompare,h,k,combine_zero,sign_zero]
    intro eq
    subst_vars
    contradiction

private def naturalTest (a b : Arm) : Test :=
  match seeds a, seeds b with
  | [], [] => .rows [] []
  | [x], [y] =>
    let p := bits a x true true
    let q := bits b y true true
    let n := min p.length q.length
    .rows [p.take n] [q.take n]
  | [_,_], [_,_] =>
    let best (c : Arm) := do
      let r := bits c .R true false
      let s := bits c .S true false
      let v ← pairCompare r s
      return if v ≥ 0 then r else s
    match best a, best b with
    | some p, some q => if p.length == q.length then .rows [p] [q] else .unavailable
    | _, _ => .unavailable
  | _, _ => .unavailable

abbrev Tests := List (Rule × Test)

private def testsFor (a b : Arm) (constitutional : Bool) : Tests :=
  let scalar (i : Col) := Test.rows (a.data i).key (b.data i).key
  let start := [(Rule.atomicNumber, scalar .z),(.duplicate, scalar .dup),(.isotope,scalar .mass)]
  if constitutional then start else start ++
    [(.geometric,scalar .geo),(.stereoClass,scalar .kind),
     (.likePair,.followed (naturalTest a b) (scalar .likeWalk)),
     (.lower,scalar .lower),(.handedPair,.followed (.paired (bits a .R false false) (bits b .R false false)
       (bits a .S false false) (bits b .S false false)) (scalar .handWalk)),
     (.reference,scalar .mark)]

def ruleOrder (constitutional : Bool) : List Rule :=
  if constitutional then [.atomicNumber,.duplicate,.isotope] else
    [.atomicNumber,.duplicate,.isotope,.geometric,.stereoClass,.likePair,.lower,.handedPair,.reference]

private theorem testsFor_order (a b : Arm) (constitutional : Bool) :
    (testsFor a b constitutional).map Prod.fst = ruleOrder constitutional := by
  cases constitutional <;> rfl

def results (ts : Tests) : Steps := ts.map fun (r,t) => (r,t.value)

structure Frame where
  molecule : RawMolecule
  focus : List Nat
  visible : List PairList.Publication
  mark : Option Nat
  constitutional : Bool

abbrev Reader (constitutional : Bool) := Nat → Nat → Option { ts : Tests // ts.map Prod.fst = ruleOrder constitutional }

/-- Build each ligand tree once for the four-carrier frame; later comparisons
look up both arms in this same molecular state. -/
def prepare (f : Frame) : Option (Reader f.constitutional) := do
  let rev := f.focus.reverse
  let ns := neighbors f.molecule rev
  guard (ns.length == 4)
  let arms ← ns.mapM fun n => do
    let a ← n.head?
    let arm ← grow f.molecule f.visible f.mark (2*f.molecule.atomCount+3) n rev
    return (a,arm)
  return fun left right => do
    let (_,a) ← arms.find? (fun p => p.1 == left)
    let (_,b) ← arms.find? (fun p => p.1 == right)
    return ⟨testsFor a b f.constitutional,testsFor_order _ _ _⟩

def molecularTests (f : Frame) (left right : Nat) : Option Tests := do
  let reader ← prepare f
  return (← reader left right).val

structure Call where
  frame : Frame
  comparison : Comparison
  tests : Tests
  winner : Option Rule
  molecular : molecularTests frame comparison.left comparison.right = some tests
  order : tests.map Prod.fst = ruleOrder frame.constitutional
  chosen : decideSteps (results tests) = some (winner,comparison.value)

theorem Call.earlier_ties (c : Call) {r : Rule} (h : c.winner = some r) :
    c.comparison.value ≠ 0 ∧ ∃ before after,
      (results c.tests) = before ++ (r,some c.comparison.value) :: after ∧
      ∀ step ∈ before, step.2 = some 0 :=
  (winner_iff _ _ _).mp (h ▸ c.chosen)

/-- Earlier ties assert equality of the underlying molecular rows or pair
lists at each position, independently of how their integer codes were logged. -/
theorem Call.earlier_equalities (c : Call) {r : Rule} (h : c.winner = some r) :
    ∃ before test after, c.tests = before ++ (r,test) :: after ∧
      test.value = some c.comparison.value ∧ ∀ item ∈ before, item.2.Tied := by
  obtain ⟨_,b,a,e,zeros⟩ := c.earlier_ties h
  obtain ⟨before,rest,he,hb,hr⟩ := List.map_eq_append_iff.mp e
  obtain ⟨⟨k,test⟩,after,hrest,hk,_⟩ := List.map_eq_cons_iff.mp hr
  change (k,test.value) = (r,some c.comparison.value) at hk
  obtain ⟨rfl,hv⟩ := Prod.mk.inj hk
  refine ⟨before,test,after,he.trans (by rw [hrest]),hv,?_⟩
  intro item mem
  apply item.2.zero_iff.mp
  apply zeros (item.1,item.2.value)
  rw [← hb]
  exact List.mem_map.mpr ⟨item,mem,rfl⟩

theorem Call.all_ties (c : Call) (h : c.winner = none) :
    c.comparison.value = 0 ∧ ∀ step ∈ (results c.tests), step.2 = some 0 := by
  have zero (xs : Steps) (v : Int) (e : decideSteps xs = some (none,v)) : v = 0 := by
    induction xs with
    | nil => simpa [decideSteps] using e.symm
    | cons hd tl ih =>
      rcases hd with ⟨k,_ | w⟩
      · simp [decideSteps] at e
      · by_cases eq : w = 0
        · exact ih (by simpa [decideSteps,eq] using e)
        · simp [decideSteps,eq] at e
  have e := c.chosen
  rw [h] at e
  have z := zero _ _ e
  exact ⟨z,(tie_iff _).mp (z ▸ e)⟩

def readCall (f : Frame) (reader : Reader f.constitutional) (ready : prepare f = some reader)
    (left right : Nat) : Option Call := do
  match hs : reader left right with
  | none => none
  | some ss =>
    match hd : decideSteps (results ss.val) with
    | none => none
    | some (r,v) =>
      return ⟨f,⟨left,right,v⟩,ss.val,r,by simp [molecularTests,ready,hs],ss.property,hd⟩

end TetraStereo.Engine.CentresRing.Molecular
assert_kernel_only TetraStereo.Engine.CentresRing.Molecular.Call.earlier_ties
assert_kernel_only TetraStereo.Engine.CentresRing.Molecular.Call.all_ties
assert_kernel_only TetraStereo.Engine.CentresRing.Molecular.winner_iff
assert_kernel_only TetraStereo.Engine.CentresRing.Molecular.tie_iff
assert_kernel_only TetraStereo.Engine.CentresRing.Molecular.Call.earlier_equalities
assert_kernel_only TetraStereo.Engine.CentresRing.Molecular.Test.zero_iff
