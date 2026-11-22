import TetraStereo.Engine.RingReferenceDistance

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.ReferenceFrame
open OneCenter LocalizedGenericMarkedRecalculation Recursive

/-- The two signed inventories at their outward occurrences in this digraph. -/
structure Outward (m : RawMolecule) (p : List Nat) (i j : Nat) where
  left : ReferenceDistance.Arm m (p ++ [i])
  right : ReferenceDistance.Arm m (p ++ [j])
  leftPath : left.node.history.reverse = p ++ [i]
  rightPath : right.node.history.reverse = p ++ [j]

/-- Rule 4a compares classes. Rules 4b and 4c preserve the earlier
observations and read both molecular orders from the addressed arms. -/
inductive Fourth {m p i j} (arms : Outward m p i j) : Bool → Type where
  | classes (c : UnitClasses.ArmComparison m p i j arms.left.entries arms.right.entries) :
      Fourth arms (c.difference.current.ordering == .gt)
  | stereo (stage : Stage) (fourth : stage = .fourB ∨ stage = .fourC) (win : Bool)
      (prior : EarlierStereoMatch.Decision m p i j stage arms.left.entries arms.right.entries)
      (actual : molecularSeniorLeft? m arms.left.node arms.right.node stage
        (InventoryPriority.positives arms.left.entries) (InventoryPriority.positives arms.right.entries) false = some win)
      (reflected : molecularSeniorLeft? m arms.left.node arms.right.node stage
        (InventoryPriority.positives arms.left.entries) (InventoryPriority.positives arms.right.entries) true = some win) :
      Fourth arms win

private def fourth? {m p i j} (a : Outward m p i j) : Option ((w : Bool) × Fourth a w) := do
  if let some c := UnitClasses.between? m p i j a.left.entries a.right.entries then
    return ⟨_,.classes c⟩
  let attempt (stage : Stage) (fourth : stage = .fourB ∨ stage = .fourC) := do
    let compare := molecularSeniorLeft? m a.left.node a.right.node stage
      (InventoryPriority.positives a.left.entries) (InventoryPriority.positives a.right.entries)
    let ⟨win,actual⟩ ← (compare false).attach
    if reflected : compare true = some win then
      let prior ← EarlierStereoMatch.check? m p i j stage a.left.entries a.right.entries
      return (⟨win,.stereo stage fourth win prior actual reflected⟩ : (w : Bool) × Fourth a w)
    none
  (attempt .fourB (Or.inl rfl)).orElse fun _ => attempt .fourC (Or.inr rfl)

/-- Each ordinary comparison identifies its own incident occurrences. A
Rule 5 decision preserves the prior stereo correspondence on both arms. -/
inductive Basis (m : RawMolecule) (g : Geometry) (p : List Nat) (i j : Nat) where
  | atomic (depth : Nat) (left right : List (List Nat))
      (leftAt : ligandRows? m p i depth = some left) (rightAt : ligandRows? m p j depth = some right)
      (wins : Bool) (strict : if wins then right < left else left < right)
  | constitution (c : IsotopePriority.IncidentComparison m p i j) (strict : c.ordering ≠ .eq)
  | fourth (arms : Outward m p i j) (wins : Bool) (why : Fourth arms wins)
  | stereo (pair : ReferenceDistance.Pair m p i j) (wins : Bool)
      (left : molecularSeniorLeft? m pair.left.node pair.right.node .five
        (InventoryPriority.positives pair.left.entries) (InventoryPriority.positives pair.right.entries) false = some wins)
      (right : molecularSeniorLeft? m pair.left.node pair.right.node .five
        (InventoryPriority.positives pair.left.entries) (InventoryPriority.positives pair.right.entries) true = some (!wins))
  | tied (pair : ReferenceDistance.Pair m p i j) (fixed : pair.flip = false)

private def basis? (m : RawMolecule) (g : Geometry) (p : List Nat) (depth i j : Nat)
    (arm : (q : List Nat) → Option (ReferenceDistance.Arm m q)) :
    Option (Basis m g p i j) := do
  let ⟨l,hl⟩ ← (ligandRows? m p i depth).attach
  let ⟨r,hr⟩ ← (ligandRows? m p j depth).attach
  if win : r < l then return .atomic depth l r hl hr true win
  if lose : l < r then return .atomic depth l r hl hr false lose
  let support := do
    let l ← arm (p ++ [i])
    let r ← arm (p ++ [j])
    if h : l.node.history.reverse = p ++ [i] ∧ r.node.history.reverse = p ++ [j] then
      return (⟨l,r,h.1,h.2⟩ : Outward m p i j)
    none
  if let some pair := support.bind (fun a => ReferenceDistance.pairOfArms? a.left a.right) then
    if fixed : pair.flip = false then return .tied pair fixed
    let compare := molecularSeniorLeft? m pair.left.node pair.right.node .five
      (InventoryPriority.positives pair.left.entries) (InventoryPriority.positives pair.right.entries)
    let ⟨wins,actual⟩ ← (compare false).attach
    if reflected : compare true = some (!wins) then return .stereo pair wins actual reflected
    none
  else
    let c ← IsotopePriority.compareIncident? m p i j
    if strict : c.ordering ≠ .eq then return .constitution c strict
    let a ← support
    let ⟨w,decision⟩ ← fourth? a
    return .fourth a w decision

abbrev Signs := Ordering × Ordering

def Basis.initial {m g p i j} : Basis m g p i j → Signs
  | .atomic _ _ _ _ _ w _ | .fourth _ w _ => if w then (.gt,.gt) else (.lt,.lt)
  | .constitution c _ => (c.ordering,c.ordering)
  | .stereo _ wins .. => if wins then (.gt,.lt) else (.lt,.gt)
  | .tied .. => (.eq,.eq)

def Basis.promoted? {m g p i j} (b : Basis m g p i j) (k : Nat) : Option Signs := do
  match b with
  | .tied pair _ =>
    let result ← pair.atMark? k
    let o := result.verdict.ordering
    return (o,o)
  | _ => return b.initial

structure Row (m : RawMolecule) (g : Geometry) (p : List Nat) where
  i : Nat
  j : Nat
  basis : Basis m g p i j

abbrev Table := List ((Nat × Nat) × Signs)

def entries {m g p} (rows : List (Row m g p)) : Table :=
  rows.map fun row => ((row.i,row.j),row.basis.initial)

def promoted? {m g p} (rows : List (Row m g p)) (mark : Nat) : Option Table :=
  rows.mapM fun row => do return ((row.i,row.j),← row.basis.promoted? mark)

def orderAt (table : Table) (rev : Bool) (i j : Nat) : Option Ordering :=
  if i = j then some .eq else (table.lookup (i,j)).map fun s => if rev then s.2 else s.1

/-- A complete total preorder with reciprocal signs on all four ligands.
The transitivity check includes ties. -/
def coherent (ids : List Nat) (t : Table) (rev : Bool) : Bool :=
  let val := orderAt t rev
  let ge (i j : Nat) := (val i j).any (· != .lt)
  ids.all fun i => ids.all fun j =>
    (val i j).isSome && val j i == (val i j).map Ordering.swap &&
      ids.all fun k => !(ge i j && ge j k) || ge i k

def marks (ids : List Nat) (table : Table) : List Nat :=
  ids.filter fun i => ids.any fun j => i != j && orderAt table false i j == some .eq

def orders (ids : List Nat) (table : Table) (rev : Bool) : List (List Nat) :=
  ids.permutations'.filter fun order => decide (order.Pairwise fun i j => orderAt table rev i j = some .gt)

structure MolecularFrame (m : RawMolecule) (g : Geometry) (p : List Nat) where
  focus : RawMolecule.CanonicalBranchNode
  reached : occurrence? m p = some focus
  carbon : (m.atoms[focus.atom]?).any (fun a => a.element == .C) = true
  ids : List Nat
  incident : ids = (occurrenceLigandCursors m focus).map (·.node.atom)
  four : ids.length = 4
  distinct : ids.Nodup
  rows : List (Row m g p)
  allPairs : rows.map (fun r => (r.i,r.j)) = Promotion.TwoPairPriority.directedPairs ids id
  ordinary : ∀ rev, coherent ids (entries rows) rev = true

structure Frame (m : RawMolecule) (g : Geometry) (p : List Nat) extends MolecularFrame m g p where
  eligible : (marks ids (entries rows)).length ∈ [3,4]

def molecularFrame? (m : RawMolecule) (g : Geometry) (p : List Nat) (depth : Nat)
    (arm : (q : List Nat) → Option (ReferenceDistance.Arm m q)) : Option (MolecularFrame m g p) := do
  guard (saturatedWithHalogens m)
  let ⟨focus,reached⟩ ← (occurrence? m p).attach
  if carbon : (m.atoms[focus.atom]?).any (fun a => a.element == .C) = true then
    let ids := (occurrenceLigandCursors m focus).map (·.node.atom)
    if four : ids.length = 4 then
      if unique : ids.Nodup then
        let pairs := Promotion.TwoPairPriority.directedPairs ids id
        let rows ← pairs.mapM fun (i,j) => do return (⟨i,j,← basis? m g p depth i j arm⟩ : Row m g p)
        if all : rows.map (fun r => (r.i,r.j)) = pairs then
          if consistent : ∀ rev, coherent ids (entries rows) rev = true then
            return ⟨focus,reached,carbon,ids,rfl,four,unique,rows,all,consistent⟩
  none

def MolecularFrame.promotion? {m g p} (f : MolecularFrame m g p) : Option (Frame m g p) :=
  if h : (marks f.ids (entries f.rows)).length ∈ [3,4] then some ⟨f,h⟩ else none

def frame? (m : RawMolecule) (g : Geometry) (p : List Nat) (depth : Nat)
    (arm : (q : List Nat) → Option (ReferenceDistance.Arm m q)) : Option (Frame m g p) := do
  (← molecularFrame? m g p depth arm).promotion?

inductive Outcome (g : Geometry) (ids : List Nat) (table : Table) where
  | assigned (actual reflected : List Nat)
      (left : orders ids table false = [actual]) (right : orders ids table true = [reflected])
      (reading : Reading) (observed : geometric g actual reflected = some reading)
  | tied (i j : Nat) (different : i ≠ j) (inside : i ∈ ids ∧ j ∈ ids)
      (survives : ∀ rev, orderAt table rev i j = some .eq ∧ orderAt table rev j i = some .eq)
      (noStrict : ∀ rev, orders ids table rev = [])

def Outcome.reading? {g ids table} : Outcome g ids table → Option Reading
  | .assigned _ _ _ _ r _ => some r
  | .tied .. => none

private def outcome? (g : Geometry) (ids : List Nat) (table : Table) : Option (Outcome g ids table) := do
  match ha : orders ids table false, hb : orders ids table true with
  | [a],[b] =>
    let ⟨r,observed⟩ ← (geometric g a b).attach
    return .assigned a b ha hb r observed
  | [],[] =>
    (Promotion.TwoPairPriority.directedPairs ids id).findSome? fun (i,j) => do
      if h : i ≠ j ∧ i ∈ ids ∧ j ∈ ids then
        if eqn : ∀ rev, orderAt table rev i j = some .eq ∧ orderAt table rev j i = some .eq then
          return .tied i j h.1 h.2 eqn (fun rev => by cases rev <;> assumption)
      none
  | _,_ => none

/-- The unmarked molecular comparisons either give a unique priority order
on both geometries or leave a single tied pair outside the promotion gate. -/
structure Ordinary {m g p} (f : MolecularFrame m g p) where
  ineligible : (marks f.ids (entries f.rows)).length < 3
  outcome : Outcome g f.ids (entries f.rows)

def MolecularFrame.ordinary? {m g p} (f : MolecularFrame m g p) : Option (Ordinary f) := do
  if few : (marks f.ids (entries f.rows)).length < 3 then
    return ⟨few,← outcome? g f.ids (entries f.rows)⟩
  none

structure Trial {m g p} (f : Frame m g p) where
  mark : Nat
  table : Table
  derived : promoted? f.rows mark = some table
  consistent : ∀ rev, coherent f.ids table rev = true
  outcome : Outcome g f.ids table

def trials? {m g p} (f : Frame m g p) : Option (List (Trial f)) :=
  (marks f.ids (entries f.rows)).mapM fun k => do
    let ⟨t,h⟩ ← (promoted? f.rows k).attach
    if consistent : ∀ rev, coherent f.ids t rev = true then
      return ⟨k,t,h,consistent,← outcome? g f.ids t⟩
    none

structure Population (m : RawMolecule) (g : Geometry) (p : List Nat) where
  frame : Frame m g p
  trials : List (Trial frame)
  complete : trials.map Trial.mark = marks frame.ids (entries frame.rows)

def Frame.population? {m g p} (frame : Frame m g p) : Option (Population m g p) := do
  let ts ← trials? frame
  if complete : ts.map Trial.mark = marks frame.ids (entries frame.rows) then return ⟨frame,ts,complete⟩
  none

/-- Inspect all eligible choices. The comparison proofs precede the geometric
readback, and the readings precede any aggregation policy. -/
def inspectWith? (m : RawMolecule) (g : Geometry) (p : List Nat) (depth : Nat)
    (arm : (q : List Nat) → Option (ReferenceDistance.Arm m q)) : Option (Population m g p) := do
  (← frame? m g p depth arm).population?

def Basis.inputs {m g p i j} : Basis m g p i j → InventoryPriority.Entries
  | .atomic .. | .constitution .. => []
  | .fourth arms .. => arms.left.entries ++ arms.right.entries
  | .stereo pair .. | .tied pair .. => pair.left.entries ++ pair.right.entries

def MolecularFrame.inputs {m g p} (f : MolecularFrame m g p) : InventoryPriority.Entries :=
  (f.rows.flatMap (fun r => r.basis.inputs)).dedup

abbrev Population.inputs {m g p} (f : Population m g p) := f.frame.toMolecularFrame.inputs

def Population.consensus? {m g p} (f : Population m g p) : Option (Option Reading) := do
  let t ← f.trials.head?
  let result := t.outcome.reading?
  if f.trials.all (fun u => u.outcome.reading? == result) then return result
  none

theorem Population.molecular_input {m g p} (s : Population m g p) {row : Row m g p}
    (used : row ∈ s.frame.rows) {x} (member : x ∈ row.basis.inputs) : x ∈ s.inputs :=
  List.mem_dedup.mpr (List.mem_flatMap.mpr ⟨row,used,member⟩)

/-- An assignment demands the same two-geometry reading at every eligible
mark. A certified absence demands a surviving pair at every mark. -/
theorem Population.consensus_iff {m g p} (s : Population m g p) (v : Option Reading) :
    s.consensus? = some v ↔ ∀ t ∈ s.trials, t.outcome.reading? = v := by
  unfold consensus?
  cases h : s.trials.head? with
  | none =>
    have empty := List.head?_eq_none_iff.mp h
    have length := congrArg List.length s.complete
    rw [empty] at length
    have pop := s.frame.eligible
    simp [← length] at pop
  | some t =>
    have first := List.mem_of_head? h
    simp only [Option.bind_eq_bind,Option.bind_some]
    by_cases same : s.trials.all (fun u => u.outcome.reading? == t.outcome.reading?) = true
    · simp only [same,if_true]
      change some t.outcome.reading? = some v ↔ _
      rw [Option.some.injEq]
      exact ⟨fun hv u hu => (eq_of_beq (List.all_eq_true.mp same u hu)).trans hv, fun all => all t first⟩
    · simp only [same]
      change (none : Option (Option Reading)) = some v ↔ _
      constructor
      · intro h; contradiction
      · intro all
        exact (same (List.all_eq_true.mpr fun u hu => beq_iff_eq.mpr ((all u hu).trans (all t first).symm))).elim

end TetraStereo.Engine.RingChemicalPriority.ReferenceFrame

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.inspectWith?
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Population.consensus_iff
