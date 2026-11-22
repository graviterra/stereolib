import TetraStereo.Engine.RingRecursivePriorities

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.UnitClasses
open OneCenter CertifiedLocalizedCIPInput Recursive

/-- A present entry with no reading denotes a certified nonstereogenic
candidate. The caller supplies a derivation of each entry. -/
abbrev Facts := List (List Nat × Option Recursive.Reading)

/-- Rule 4a distinguishes three classes of tetrahedral occurrences. -/
def kind : Option Recursive.Reading → Nat
  | none => 0
  | some r => match r.label with
    | some (.chiral _) => 2
    | some (.pseudoasymmetric _) => 1
    | none => 0

theorem kind_mirror (r : Option Recursive.Reading) :
    kind (r.map Recursive.Reading.reverse) = kind r := by
  cases r with
  | none => rfl
  | some r => obtain ⟨a,b⟩ := r; cases a <;> cases b <;> rfl

abbrev Site := IsotopeSpheres.Site

/-- At an actual candidate we require its addressed class, even when absent.
A missing entry can contribute zero only for a terminal copy, a noncarbon
atom, or a carbon excluded by the two-identical-hydrogen test. -/
def classAt? (m : RawMolecule) (fs : Facts) (s : Site) : Option Nat := do
  let n := s.cursor.node
  if n.forcedLeaf then return 0
  let atom ← m.atoms[n.atom]?
  if atom.element != .C then return 0
  if let some value := fs.lookup n.history.reverse then return kind value
  let candidates ← carbonSites m (m.atomCount+1) n
  guard (!candidates.contains n.history.reverse)
  return 0

/-- The facts cover exactly the candidates in this outward arm and contain
each address once. The constitutional comparison binds the arm's cursor. -/
structure Covered (m : RawMolecule) (path : List Nat) (i : Nat)
    (c : CanonicalRerootCursor) (fs : Facts) : Prop where
  reached : occurrence? m (path ++ [i]) = some c.node
  candidates : ∃ ps, carbonSites m (m.atomCount+1) c.node = some ps ∧
    (fs.map Prod.fst).Perm ps
  unique : (fs.map Prod.fst).Nodup

def covered? (m : RawMolecule) (path : List Nat) (i : Nat)
    (c : CanonicalRerootCursor) (fs : Facts) : Option (PLift (Covered m path i c fs)) := do
  if reached : occurrence? m (path ++ [i]) = some c.node then
    let ⟨ps,actual⟩ ← (carbonSites m (m.atomCount+1) c.node).attach
    if complete : (fs.map Prod.fst).Perm ps then
      if unique : (fs.map Prod.fst).Nodup then return ⟨⟨reached,⟨ps,actual,complete⟩,unique⟩⟩
  none

structure Entry where
  site : Site
  value : Nat
  deriving DecidableEq

private def observe (m : RawMolecule) (fs : Facts) : (ss : List Site) →
    Option {es : List Entry // es.map Entry.site = ss ∧
      ∀ e ∈ es, classAt? m fs e.site = some e.value}
  | [] => some ⟨[],rfl,by simp⟩
  | s :: ss => do
    let ⟨v,hv⟩ ← (classAt? m fs s).attach
    let ⟨es,sites,values⟩ ← observe m fs ss
    return ⟨⟨s,v⟩ :: es,by simp [sites],by
      intro e he
      rcases List.mem_cons.mp he with rfl | below
      · exact hv
      · exact values e below⟩

/-- A strict difference in nuclear charge at the first divergence orders
these two molecular routes. Orders unresolved by this test remain arbitrary. -/
def Before (m : RawMolecule) (a b : Entry) := IsotopeSpheres.senior m a.site.route b.site.route = true

instance (m : RawMolecule) (a b : Entry) : Decidable (Before m a b) :=
  inferInstanceAs (Decidable (_ = true))

def Legal (m : RawMolecule) (es order : List Entry) :=
  es.Perm order ∧ order.Pairwise (fun a b => ¬ Before m b a)

structure Row (m : RawMolecule) (fs : Facts) (ss : List Site) where
  entries : List Entry
  sites : entries.map Entry.site = ss
  observed : ∀ e ∈ entries, classAt? m fs e.site = some e.value
  witness : List Entry
  legal : Legal m entries witness
  blocks : List (List Entry)
  full : blocks.flatten.Perm entries
  separated : blocks.Pairwise (fun l r => ∀ a ∈ l, ∀ b ∈ r, Before m a b)

private def row? (m : RawMolecule) (fs : Facts) (ss : List Site) : Option (Row m fs ss) := do
  guard (!ss.isEmpty)
  let ⟨es,sites,observed⟩ ← observe m fs ss
  let descending (a b : Entry) := ¬ Before m b a
  let w := es.insertionSort descending
  if legal : w.Pairwise descending then
    let ranks := ((es.map (·.site.rank)).eraseDups).insertionSort (fun a b => b ≤ a)
    let bs := ranks.map fun rank => es.filter fun e => e.site.rank == rank
    if full : bs.flatten.Perm es then
      if sep : bs.Pairwise (fun l r => ∀ a ∈ l, ∀ b ∈ r, Before m a b) then
        return ⟨es,sites,observed,w,⟨(List.perm_insertionSort _ _).symm,legal⟩,bs,full,sep⟩
  none

def Row.words {m fs ss} (r : Row m fs ss) := r.blocks.map (List.map Entry.value)

theorem Row.legalWords {m fs ss} (r : Row m fs ss) {order} (legal : Legal m r.entries order) :
    ∃ words, List.Forall₂ List.Perm r.words words ∧ words.flatten = order.map Entry.value := by
  obtain ⟨parts,perms,flat⟩ := Hierarchy.split_linearization (Before m)
    (by intro a; simp [Before,IsotopeSpheres.senior_self]) r.blocks order r.separated
    (r.full.trans legal.1) legal.2
  refine ⟨parts.map (List.map Entry.value),?_,?_⟩
  · exact List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr
      (perms.imp fun _ _ h => h.map _))
  · simp [← flat,List.map_flatten]

structure Sphere (m : RawMolecule) (ls rs : Facts) (a b : CanonicalRerootCursor) (k : Nat) where
  leftSites : List Site
  rightSites : List Site
  leftReached : IsotopeSpheres.sitesAt m a k = some leftSites
  rightReached : IsotopeSpheres.sitesAt m b k = some rightSites
  left : Row m ls leftSites
  right : Row m rs rightSites
  ordering : Ordering
  allOrders : ∀ x y, Legal m left.entries x → Legal m right.entries y →
    IsotopeSpheres.Sign ordering (x.map Entry.value) (y.map Entry.value)

private def inspect? (m : RawMolecule) (ls rs : Facts) (a b : CanonicalRerootCursor) (k : Nat) :
    Option (Sphere m ls rs a b k) := do
  let ⟨xs,lx⟩ ← (IsotopeSpheres.sitesAt m a k).attach
  let ⟨ys,ry⟩ ← (IsotopeSpheres.sitesAt m b k).attach
  let l ← row? m ls xs
  let r ← row? m rs ys
  if shape : l.words.map List.length = r.words.map List.length then
    let ⟨o,law⟩ ← IsotopeSpheres.sequence? l.words r.words
    return ⟨xs,ys,lx,ry,l,r,o,by
      intro u v hu hv
      obtain ⟨us,up,uw⟩ := l.legalWords hu
      obtain ⟨vs,vp,vw⟩ := r.legalWords hv
      have shp := (IsotopeSpheres.shapes up).symm.trans (shape.trans (IsotopeSpheres.shapes vp))
      have result := law us vs up vp
      rw [← uw,← vw]
      cases o with
      | eq => exact congrArg List.flatten result
      | lt => exact Hierarchy.flatten_strict shp result
      | gt => exact Hierarchy.flatten_strict shp.symm result⟩
  none

/-- The first unequal slot in a concrete pair of allowable orderings. -/
structure FirstPair {m ls rs a b k} (s : Sphere m ls rs a b k) where
  index : Nat
  left : Entry
  right : Entry
  leftAt : s.left.witness[index]? = some left
  rightAt : s.right.witness[index]? = some right
  equalBefore : (s.left.witness.take index).map Entry.value = (s.right.witness.take index).map Entry.value
  signed : IsotopeSpheres.Sign s.ordering left.value right.value

private def firstPair? {m ls rs a b k} (s : Sphere m ls rs a b k) : Option (FirstPair s) := do
  let l := s.left.witness
  let r := s.right.witness
  let i ← (List.range l.length).find? fun j => l[j]?.map Entry.value != r[j]?.map Entry.value
  let ⟨x,hx⟩ ← l[i]?.attach
  let ⟨y,hy⟩ ← r[i]?.attach
  if earlier : (l.take i).map Entry.value = (r.take i).map Entry.value then
    if signed : IsotopeSpheres.Sign s.ordering x.value y.value then return ⟨i,x,y,hx,hy,earlier,signed⟩
  none

inductive Earlier (m : RawMolecule) (ls rs : Facts) (a b : CanonicalRerootCursor) : Nat → Type where
  | start : Earlier m ls rs a b 0
  | push {k} : Earlier m ls rs a b k → (row : Sphere m ls rs a b k) →
      row.ordering = .eq → Earlier m ls rs a b (k+1)

theorem Earlier.tied {m ls rs a b k} (prior : Earlier m ls rs a b k) :
    ∀ j < k, ∃ s : Sphere m ls rs a b j, s.ordering = .eq := by
  induction prior with
  | start => intro _ h; omega
  | @push k _ s tied ih =>
    intro j hj
    by_cases same : j = k
    · subst j; exact ⟨s,tied⟩
    · exact ih j (by omega)

structure Difference (m : RawMolecule) (ls rs : Facts) (a b : CanonicalRerootCursor) where
  offset : Nat
  previous : Earlier m ls rs a b offset
  current : Sphere m ls rs a b offset
  strict : current.ordering ≠ .eq
  first : FirstPair current

private def search (m : RawMolecule) (ls rs : Facts) (a b : CanonicalRerootCursor) :
    Nat → (k : Nat) → Earlier m ls rs a b k → Option (Difference m ls rs a b)
  | 0,_,_ => none
  | fuel+1,k,earlier => do
    let s ← inspect? m ls rs a b k
    if eqn : s.ordering = .eq then
      search m ls rs a b fuel (k+1) (.push earlier s eqn)
    else
      return ⟨k,earlier,s,eqn,← firstPair? s⟩

structure ArmComparison (m : RawMolecule) (path : List Nat) (i j : Nat) (ls rs : Facts) where
  prior : IsotopePriority.IncidentComparison m path i j
  constitutional : IsotopePriority.compareIncident? m path i j = some prior
  tied : prior.ordering = .eq
  left : Covered m path i prior.pair.left.cursor ls
  right : Covered m path j prior.pair.right.cursor rs
  difference : Difference m ls rs prior.pair.left.cursor prior.pair.right.cursor

def between? (m : RawMolecule) (path : List Nat) (i j : Nat) (ls rs : Facts) :
    Option (ArmComparison m path i j ls rs) := do
  let ⟨c,actual⟩ ← (IsotopePriority.compareIncident? m path i j).attach
  if tied : c.ordering = .eq then
    let ⟨l⟩ ← covered? m path i c.pair.left.cursor ls
    let ⟨r⟩ ← covered? m path j c.pair.right.cursor rs
    let difference ← search m ls rs c.pair.left.cursor c.pair.right.cursor (2*(m.atomCount+1)+1) 0 .start
    return ⟨c,actual,tied,l,r,difference⟩
  none

structure Decision (m : RawMolecule) (path : List Nat) (depth : Nat) (f : Recursive.Frame)
    (ls rs : Facts) extends ArmComparison m path f.left f.right ls rs where
  frame : Recursive.frameOK m path depth f = true

def Decision.ordering {m p d f ls rs} (r : Decision m p d f ls rs) := r.difference.current.ordering
def Decision.sphere {m p d f ls rs} (r : Decision m p d f ls rs) := r.difference.offset + 1
def Decision.leftSenior {m p d f ls rs} (r : Decision m p d f ls rs) := r.ordering == .gt

theorem Decision.fullTie {m p d f ls rs} (r : Decision m p d f ls rs) :
    IsotopePriority.FullTie m p r.prior.pair.left r.prior.pair.right :=
  r.prior.equal_trees r.tied

/-- First strict class sphere after a complete earlier-rule tie at the
addressed frame. Truth of the supplied occurrence readings and absences is
a separate premise of a chemically justified assignment. -/
def compare? (m : RawMolecule) (path : List Nat) (depth : Nat) (f : Recursive.Frame)
    (ls rs : Facts) : Option (Decision m path depth f ls rs) := do
  if frame : Recursive.frameOK m path depth f = true then
    return ⟨← between? m path f.left f.right ls rs,frame⟩
  none

end TetraStereo.Engine.RingChemicalPriority.UnitClasses

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.UnitClasses.kind_mirror
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.UnitClasses.Row.legalWords
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.UnitClasses.Earlier.tied
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.UnitClasses.Decision.fullTie
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.UnitClasses.compare?
