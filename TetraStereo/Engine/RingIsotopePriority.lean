import TetraStereo.Engine.RingIsotopeSpheres
import TetraStereo.Engine.RingDuplicatePriority
import TetraStereo.Engine.RingSiblingConstitution
import TetraStereo.Engine.RingEnantiomorphicArms
import TetraStereo.OneCenter.CIPRule2MassData

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.IsotopePriority
open OneCenter CertifiedLocalizedCIPInput Certificate.CanonicalSphereKey
open LocalizedPhysicalMarkedSparseMarker (compareMarker)

/-- The retained tree may lead back to the original root and then out another
arm. Completion is checked on the actual cursor, including the incoming edge. -/
def budget (m : RawMolecule) := 2 * (m.atomCount+1)

/-- Complete retained trees agreeing under a supplied node observation.
The child permutation preserves multiplicities. Fuel exhaustion never proves
equality at an unvisited occurrence. -/
def TreesMatch {ω : Type} (m : RawMolecule) (observe : CanonicalRerootCursor → Option ω) :
    Nat → CanonicalRerootCursor → CanonicalRerootCursor → Prop
  | 0,_,_ => False
  | d+1,a,b => ∃ o, observe a = some o ∧ observe b = some o ∧
      ∃ ordered : List CanonicalRerootCursor, ordered.Perm (b.children m) ∧
        List.Forall₂ (TreesMatch m observe d) (a.children m) ordered

def treesMatch {ω : Type} [DecidableEq ω] (m : RawMolecule)
    (observe : CanonicalRerootCursor → Option ω) :
    Nat → CanonicalRerootCursor → CanonicalRerootCursor → Bool
  | 0,_,_ => false
  | d+1,a,b =>
    (observe a).any (fun o => decide (observe b = some o)) &&
      (b.children m).permutations'.any (fun ordered => (a.children m).isEqv ordered (treesMatch m observe d))

private theorem matched {α : Type} {f : α → α → Bool} {xs ys : List α}
    (h : xs.isEqv ys f = true) : List.Forall₂ (fun a b => f a b = true) xs ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact .nil
    | cons _ _ => contradiction
  | cons x xs ih =>
    cases ys with
    | nil => contradiction
    | cons y ys =>
      simp only [List.isEqv, Bool.and_eq_true] at h
      exact .cons h.1 (ih h.2)

theorem treesMatch_sound {ω : Type} [DecidableEq ω] {m d a b}
    {observe : CanonicalRerootCursor → Option ω} (h : treesMatch m observe d a b = true) :
    TreesMatch m observe d a b := by
  induction d generalizing a b with
  | zero => contradiction
  | succ d ih =>
    simp only [treesMatch, Bool.and_eq_true] at h
    obtain ⟨root,children⟩ := h
    cases obs : observe a with
    | none => simp [obs] at root
    | some o =>
      have eqn : observe b = some o := by simpa [obs] using root
      obtain ⟨ordered,perm,agree⟩ := List.any_eq_true.mp children
      exact ⟨o,obs,eqn,ordered,List.mem_permutations'.mp perm,
        (matched agree).imp fun _ _ same => ih same⟩

private theorem isEqv_of_matched {α : Type} {f : α → α → Bool} {xs ys : List α}
    (h : List.Forall₂ (fun a b => f a b = true) xs ys) : xs.isEqv ys f = true := by
  induction h with
  | nil => rfl
  | cons head _ tail => simp only [List.isEqv,Bool.and_eq_true]; exact ⟨head,tail⟩

/-- Every correspondence with complete observations occurs in the structural
enumeration, including correspondences which reorder the children. -/
theorem treesMatch_complete {ω : Type} [DecidableEq ω] {m d a b}
    {observe : CanonicalRerootCursor → Option ω} (h : TreesMatch m observe d a b) :
    treesMatch m observe d a b = true := by
  induction d generalizing a b with
  | zero => contradiction
  | succ d ih =>
    obtain ⟨o,left,right,ordered,perm,agree⟩ := h
    simp only [treesMatch,Bool.and_eq_true]
    refine ⟨by simp [left,right], List.any_eq_true.mpr ⟨ordered,List.mem_permutations'.mpr perm,?_⟩⟩
    exact isEqv_of_matched (agree.imp fun _ _ same => ih same)

theorem treesMatch_iff {ω : Type} [DecidableEq ω] {m d a b}
    {observe : CanonicalRerootCursor → Option ω} :
    treesMatch m observe d a b = true ↔ TreesMatch m observe d a b :=
  ⟨treesMatch_sound,treesMatch_complete⟩

/-- An independent reader can use any result type and any permutation-
invariant combination of the child results. Equality follows from the
matched occurrence trees without evaluating the isomorphism checker. -/
theorem TreesMatch.observer_eq {α ω : Type} {m d a b} {observe : CanonicalRerootCursor → Option ω}
    (same : TreesMatch m observe d a b)
    (reader : Nat → CanonicalRerootCursor → α)
    (combine : ω → List α → α)
    (atNode : ∀ n c o, observe c = some o →
      reader (n+1) c = combine o ((c.children m).map (reader n)))
    (symmetric : ∀ o {xs ys : List α}, xs.Perm ys → combine o xs = combine o ys) :
    reader d a = reader d b := by
  induction d generalizing a b with
  | zero => contradiction
  | succ n ih =>
    obtain ⟨o,left,right,ordered,perm,matched⟩ := same
    rw [atNode n a o left,atNode n b o right]
    apply symmetric
    have agreeing : List.Forall₂ (fun x y => reader n x = reader n y)
        (a.children m) ordered := matched.imp fun _ _ children => ih children
    have aligned : (a.children m).map (reader n) = ordered.map (reader n) := by
      have eqs : List.Forall₂ (· = ·) ((a.children m).map (reader n))
          (ordered.map (reader n)) :=
        List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr agreeing)
      simpa only [List.forall₂_eq_eq_eq] using eqs
    rw [aligned]
    exact perm.map (reader n)

/-- The earlier-rule tree comparison erases isotope labels. -/
abbrev Isomorphic (m : RawMolecule) (focus : List Nat) := TreesMatch m (observation? m focus)

abbrev isomorphic (m : RawMolecule) (focus : List Nat) := treesMatch m (observation? m focus)

theorem isomorphic_sound {m focus d a b} (h : isomorphic m focus d a b = true) :
    Isomorphic m focus d a b := treesMatch_sound h

/-- An independent reader can use any result type and any permutation-
invariant combination of the child results. Equality follows from the
matched occurrence trees without evaluating the isomorphism checker. -/
theorem Isomorphic.observer_eq {α : Type} {m focus d a b}
    (same : Isomorphic m focus d a b)
    (reader : Nat → CanonicalRerootCursor → α)
    (combine : PriorObservation → List α → α)
    (atNode : ∀ n c o, observation? m focus c = some o →
      reader (n+1) c = combine o ((c.children m).map (reader n)))
    (symmetric : ∀ o {xs ys : List α}, xs.Perm ys → combine o xs = combine o ys) :
    reader d a = reader d b :=
  TreesMatch.observer_eq same reader combine atNode symmetric

/-- Example of a Rule 1b observer independent of the matcher. At each
distance it counts ring duplicates whose corresponding real occurrence is
that far from the current focus. -/
def countRingOriginsAt (m : RawMolecule) (focus : List Nat) (distance : Nat) :
    Nat → CanonicalRerootCursor → Nat
  | 0,_ => 0
  | n+1,c =>
    let here := (observation? m focus c).any fun o =>
      match o.provenance with
      | .ringDuplicate _ => o.sourceDistanceFromFocus == distance
      | _ => false
    here.toNat + ((c.children m).map (countRingOriginsAt m focus distance n)).sum

theorem Isomorphic.equal_ring_origin_counts {m focus d a b}
    (same : Isomorphic m focus d a b) (distance : Nat) :
    countRingOriginsAt m focus distance d a = countRingOriginsAt m focus distance d b := by
  let localCount (o : PriorObservation) := match o.provenance with
    | .ringDuplicate _ => (o.sourceDistanceFromFocus == distance).toNat
    | _ => 0
  apply same.observer_eq (countRingOriginsAt m focus distance)
    (fun o counts => localCount o + counts.sum)
  · intro n c o found
    cases h : o.provenance <;> simp [countRingOriginsAt,found,h,localCount]
  · intro o xs ys perm
    rw [perm.sum_eq]

structure Arm (m : RawMolecule) where
  cursor : CanonicalRerootCursor
  atom : AtomSpec
  original : m.atoms[cursor.node.atom]? = some atom
  complete : SiblingConstitution.exhausted m (budget m) cursor = true
  tree : HTree Nat
  molecular : atomicTree m 3 (budget m) cursor = some tree

private def arm? (m : RawMolecule) (c : CanonicalRerootCursor) : Option (Arm m) := do
  let ⟨atom,found⟩ ← (m.atoms[c.node.atom]?).attach
  if full : SiblingConstitution.exhausted m (budget m) c = true then
    let ⟨tree,built⟩ ← (atomicTree m 3 (budget m) c).attach
    return ⟨c,atom,found,full,tree,built⟩
  none

structure Nuclide {m : RawMolecule} (a : Arm m) where
  real : a.cursor.node.provenance = .realAtom
  number : Nat
  explicit : a.atom.isotope? = some number
  mass : Nat
  sourced : CIPRule2MassData.isotopeAtomicMassPico? a.atom.element.atomicNumber number = some mass

private def nuclide? {m} (a : Arm m) : Option (Nuclide a) := do
  if real : a.cursor.node.provenance = .realAtom then
    let ⟨n,explicit⟩ ← a.atom.isotope?.attach
    let ⟨mass,sourced⟩ ← (CIPRule2MassData.isotopeAtomicMassPico? a.atom.element.atomicNumber n).attach
    return ⟨real,n,explicit,mass,sourced⟩
  none

def depth {m} (a b : Arm m) := max (SiblingConstitution.height a.tree) (SiblingConstitution.height b.tree)

/-- Complete Rule 1a tie, actual canonical traversals, and the first
sphere at which the nearer real origins of ring duplicates decide. -/
structure OriginDecision {m} (p : List Nat) (a b : Arm m) (k : Nat) : Prop where
  earlier : ckey 3 (depth a b) a.tree = ckey 3 (depth a b) b.tree
  leftOrders : ∀ j ≤ k, Nonempty (DuplicatePriority.MolecularOrder m p a.cursor 3 (depth a b) a.tree j)
  rightOrders : ∀ j ≤ k, Nonempty (DuplicatePriority.MolecularOrder m p b.cursor 3 (depth a b) b.tree j)
  first : DuplicatePriority.First m p a.cursor b.cursor 0 k

/-- Every pair of earlier-rule-compatible molecular traversals gives the
same prior observations before the deciding sphere and a strict priority
for the nearer duplicate origins at that sphere. Both arms have such a
traversal at each of those distances. -/
theorem OriginDecision.first_difference {m p a b k} (d : @OriginDecision m p a b k) :
    (∀ j < k, ∀ (l : DuplicatePriority.MolecularOrder m p a.cursor 3 (depth a b) a.tree j)
      (r : DuplicatePriority.MolecularOrder m p b.cursor 3 (depth a b) b.tree j),
      l.readings = r.readings) ∧
    (∀ (l : DuplicatePriority.MolecularOrder m p a.cursor 3 (depth a b) a.tree k)
      (r : DuplicatePriority.MolecularOrder m p b.cursor 3 (depth a b) b.tree k),
      l.readings.map PriorObservation.sourceDistanceFromFocus <
        r.readings.map PriorObservation.sourceDistanceFromFocus) := by
  constructor
  · intro j earlier left right
    obtain ⟨_,_,hl,hr,tie⟩ := d.first.earlier j (Nat.zero_le _) earlier
    exact tie.every_presentation (left.presentation right hl hr d.earlier)
  · intro left right
    obtain ⟨_,_,hl,hr,win⟩ := d.first.deciding
    exact win.every_presentation (left.presentation right hl hr d.earlier)

/-- Every preceding-rule-compatible traversal reaches the same first
strict comparison of real origin depths in the retained digraph. -/
structure FixedRootDecision {m} (p : List Nat) (a b : Arm m) (k : Nat) : Prop where
  earlier : ckey 3 (depth a b) a.tree = ckey 3 (depth a b) b.tree
  leftOrders : ∀ j ≤ k, Nonempty (DuplicatePriority.MolecularOrder m p a.cursor 3 (depth a b) a.tree j)
  rightOrders : ∀ j ≤ k, Nonempty (DuplicatePriority.MolecularOrder m p b.cursor 3 (depth a b) b.tree j)
  first : DuplicatePriority.FirstRows (DuplicatePriority.originalRow? m p a.cursor)
    (DuplicatePriority.originalRow? m p b.cursor) 0 k

theorem FixedRootDecision.first_difference {m p a b k} (d : @FixedRootDecision m p a b k) :
    (∀ j < k, ∀ (l : DuplicatePriority.MolecularOrder m p a.cursor 3 (depth a b) a.tree j)
      (r : DuplicatePriority.MolecularOrder m p b.cursor 3 (depth a b) b.tree j),
      l.readings.map DuplicatePriority.originalView = r.readings.map DuplicatePriority.originalView) ∧
    (∀ (l : DuplicatePriority.MolecularOrder m p a.cursor 3 (depth a b) a.tree k)
      (r : DuplicatePriority.MolecularOrder m p b.cursor 3 (depth a b) b.tree k),
      (l.readings.map DuplicatePriority.originalView).map PriorObservation.sourceDistanceFromFocus <
        (r.readings.map DuplicatePriority.originalView).map PriorObservation.sourceDistanceFromFocus) := by
  constructor
  · intro j earlier l r
    obtain ⟨_,_,hl,hr,tie⟩ := d.first.earlier j (Nat.zero_le _) earlier
    obtain ⟨_,left,rfl⟩ := Option.map_eq_some_iff.mp hl
    obtain ⟨_,right,rfl⟩ := Option.map_eq_some_iff.mp hr
    exact tie.every_presentation (l.presentation r left right d.earlier).originalView
  · intro l r
    obtain ⟨_,_,hl,hr,win⟩ := d.first.deciding
    obtain ⟨_,left,rfl⟩ := Option.map_eq_some_iff.mp hl
    obtain ⟨_,right,rfl⟩ := Option.map_eq_some_iff.mp hr
    exact win.every_presentation (l.presentation r left right d.earlier).originalView

/-- Rule 1b on two proximal ring copies in the same retained digraph:
both complete Rule 1a keys tie and the senior copy points to a real
ancestor closer to that digraph's original root. -/
structure DirectDuplicate {m} (p : List Nat) (a b : Arm m) where
  earlier : ckey 3 (depth a b) a.tree = ckey 3 (depth a b) b.tree
  left : DuplicatePriority.AncestorOrigin m p a.cursor
  right : DuplicatePriority.AncestorOrigin m p b.cursor
  nearer : left.depth < right.depth

theorem DirectDuplicate.focus_reverses {m p a b} (d : @DirectDuplicate m p a b) :
    pathDistance p d.right.origin.history.reverse < pathDistance p d.left.origin.history.reverse :=
  (d.left.opposite d.right).mp d.nearer

/-- An actual terminal child and the Rule 2 mass at its molecular source. -/
structure TerminalMass (m : RawMolecule) where
  cursor : CanonicalRerootCursor
  real : cursor.node.provenance = .realAtom
  terminal : cursor.children m = []
  atom : AtomSpec
  source : m.atoms[cursor.node.atom]? = some atom
  mass : Nat
  measured : CIPRule2MassData.rule2MassPico? atom.element.atomicNumber atom.isotope? = some mass

private def terminalMass? (m : RawMolecule) (c : CanonicalRerootCursor) :
    Option (TerminalMass m) := do
  if h : c.node.provenance = .realAtom ∧ c.children m = [] then
    let ⟨a,source⟩ ← (m.atoms[c.node.atom]?).attach
    let ⟨mass,measured⟩ ← (CIPRule2MassData.rule2MassPico? a.element.atomicNumber a.isotope?).attach
    return ⟨c,h.1,h.2,a,source,mass,measured⟩
  none

/-- Descending nuclear charge orders siblings first. Mass refines only
equal nuclear charge. All these terminal siblings share a single parent. -/
def TerminalMass.key {m} (x : TerminalMass m) := [x.atom.element.atomicNumber,x.mass]

def siblingWord (keys : List (List Nat)) := keys.insertionSort (· ≥ ·)

def SiblingOrder (keys order : List (List Nat)) : Prop := keys.Perm order ∧ order.Pairwise (· ≥ ·)

theorem siblingOrder_unique {keys order : List (List Nat)} (h : SiblingOrder keys order) :
    order = siblingWord keys :=
  List.Perm.eq_of_pairwise' h.2 (List.pairwise_insertionSort _ keys)
    (h.1.symm.trans (List.perm_insertionSort _ keys).symm)

/-- All the required properties can be checked on the raw occurrence before
running the priority evaluator, independently of any proposed order. -/
def KnownTerminal (m : RawMolecule) (c : CanonicalRerootCursor) : Prop :=
  c.node.provenance = .realAtom ∧ c.children m = [] ∧ ∃ a mass,
    m.atoms[c.node.atom]? = some a ∧
    CIPRule2MassData.rule2MassPico? a.element.atomicNumber a.isotope? = some mass

def readTerminalMasses? (m : RawMolecule) (cs : List CanonicalRerootCursor) :=
  cs.mapM (terminalMass? m)

private theorem attach_of_value {α : Type} {o : Option α} {x : α} (h : o = some x) :
    o.attach = some ⟨x,h⟩ := by subst o; rfl

theorem readTerminalMasses?_total {m} (cs : List CanonicalRerootCursor)
    (known : ∀ c ∈ cs, KnownTerminal m c) :
    ∃ es, readTerminalMasses? m cs = some es ∧ es.map TerminalMass.cursor = cs := by
  induction cs with
  | nil => exact ⟨[],rfl,rfl⟩
  | cons c cs ih =>
    obtain ⟨real,leaf,a,mass,found,measured⟩ := known c List.mem_cons_self
    let e : TerminalMass m := ⟨c,real,leaf,a,found,mass,measured⟩
    have read : terminalMass? m c = some e := by
      simp [terminalMass?,real,leaf,attach_of_value found,attach_of_value measured,e]
    obtain ⟨rest,data,covered⟩ := ih (fun n h => known n (List.mem_cons_of_mem c h))
    refine ⟨e :: rest,?_,by simp [e,covered]⟩
    have tailRead : cs.mapM (terminalMass? m) = some rest := data
    simp [readTerminalMasses?,read,tailRead]

/-- For any two complete sibling groups of real terminals with tabulated
masses, the molecular data yield one comparison shared by all legal
orders. This includes equal masses and either strict orientation. -/
theorem terminal_siblings_total {m} (a b : CanonicalRerootCursor)
    (left : ∀ c ∈ a.children m, KnownTerminal m c) (right : ∀ c ∈ b.children m, KnownTerminal m c) :
    ∃ ls rs, readTerminalMasses? m (a.children m) = some ls ∧ readTerminalMasses? m (b.children m) = some rs ∧
      ls.map TerminalMass.cursor = a.children m ∧ rs.map TerminalMass.cursor = b.children m ∧
      ∃! sign : Ordering, ∀ l r, SiblingOrder (ls.map TerminalMass.key) l →
        SiblingOrder (rs.map TerminalMass.key) r → compare l r = sign := by
  obtain ⟨ls,lread,lcover⟩ := readTerminalMasses?_total _ left
  obtain ⟨rs,rread,rcover⟩ := readTerminalMasses?_total _ right
  refine ⟨ls,rs,lread,rread,lcover,rcover,
    compare (siblingWord (ls.map TerminalMass.key)) (siblingWord (rs.map TerminalMass.key)),?_,?_⟩
  · intro l r hl hr
    rw [siblingOrder_unique hl,siblingOrder_unique hr]
  · intro other h
    exact (h _ _ ⟨(List.perm_insertionSort _ _).symm,List.pairwise_insertionSort _ _⟩
      ⟨(List.perm_insertionSort _ _).symm,List.pairwise_insertionSort _ _⟩).symm

/-- All earlier constitutional comparisons tie. The two real proximal
atoms also have equal physical mass. At sphere II each side has exactly
one parent and exclusively real terminal children. The first differing
slot compares equal atomic numbers and strictly different physical masses. -/
structure TerminalMassOrder {m : RawMolecule} (p : List Nat) (a b : Arm m) where
  constitution : ckey 3 (depth a b) a.tree = ckey 3 (depth a b) b.tree
  previous : Isomorphic m p (budget m+1) a.cursor b.cursor
  real : a.cursor.node.provenance = .realAtom ∧ b.cursor.node.provenance = .realAtom
  parentMass : Nat
  leftMass : CIPRule2MassData.rule2MassPico? a.atom.element.atomicNumber a.atom.isotope? = some parentMass
  rightMass : CIPRule2MassData.rule2MassPico? b.atom.element.atomicNumber b.atom.isotope? = some parentMass
  left : List (TerminalMass m)
  right : List (TerminalMass m)
  leftSources : left.map TerminalMass.cursor = a.cursor.children m
  rightSources : right.map TerminalMass.cursor = b.cursor.children m
  slot : Nat
  atomicNumber : Nat
  heavy : Nat
  light : Nat
  earlier : (siblingWord (left.map TerminalMass.key)).take slot = (siblingWord (right.map TerminalMass.key)).take slot
  atLeft : (siblingWord (left.map TerminalMass.key))[slot]? = some [atomicNumber,heavy]
  atRight : (siblingWord (right.map TerminalMass.key))[slot]? = some [atomicNumber,light]
  heavier : light < heavy
  strict : siblingWord (right.map TerminalMass.key) < siblingWord (left.map TerminalMass.key)

theorem TerminalMassOrder.all_orders {m p a b} (d : @TerminalMassOrder m p a b)
    {ls rs} (l : SiblingOrder (d.left.map TerminalMass.key) ls)
    (r : SiblingOrder (d.right.map TerminalMass.key) rs) :
    ls.take d.slot = rs.take d.slot ∧ ls[d.slot]? = some [d.atomicNumber,d.heavy] ∧
      rs[d.slot]? = some [d.atomicNumber,d.light] ∧ rs < ls := by
  rw [siblingOrder_unique l,siblingOrder_unique r]
  exact ⟨d.earlier,d.atLeft,d.atRight,d.strict⟩

/-- An exact first unequal slot in the sorted sources. Agreement in nuclear
charge at the slot makes the strict comparison a Rule 2 mass decision. -/
structure SiblingMassDifference (ls rs : List (List Nat)) where
  slot : Nat
  atomicNumber : Nat
  heavy : Nat
  light : Nat
  earlier : ls.take slot = rs.take slot
  atLeft : ls[slot]? = some [atomicNumber,heavy]
  atRight : rs[slot]? = some [atomicNumber,light]
  heavier : light < heavy
  strict : rs < ls

def siblingMassDifference? (ls rs : List (List Nat)) : Option (SiblingMassDifference ls rs) := do
  if strict : rs < ls then
    let k ← (List.range ls.length).find? (fun n => ls[n]? != rs[n]?)
    let some [z,x] := ls[k]? | none
    let some [_,y] := rs[k]? | none
    if diff : ls.take k = rs.take k ∧ ls[k]? = some [z,x] ∧ rs[k]? = some [z,y] ∧ y < x then
      return ⟨k,z,x,y,diff.1,diff.2.1,diff.2.2.1,diff.2.2.2,strict⟩
  none

private def terminalMassOrder? {m p} (a b : Arm m)
    (tied : ckey 3 (depth a b) a.tree = ckey 3 (depth a b) b.tree)
    (previous : Isomorphic m p (budget m+1) a.cursor b.cursor) : Option (TerminalMassOrder p a b) := do
  if real : a.cursor.node.provenance = .realAtom ∧ b.cursor.node.provenance = .realAtom then
    let ⟨mass,leftMass⟩ ← (CIPRule2MassData.rule2MassPico? a.atom.element.atomicNumber a.atom.isotope?).attach
    if rightMass : CIPRule2MassData.rule2MassPico? b.atom.element.atomicNumber b.atom.isotope? = some mass then
      let left ← readTerminalMasses? m (a.cursor.children m)
      let right ← readTerminalMasses? m (b.cursor.children m)
      if sources : left.map TerminalMass.cursor = a.cursor.children m ∧ right.map TerminalMass.cursor = b.cursor.children m then
        let ls := siblingWord (left.map TerminalMass.key)
        let rs := siblingWord (right.map TerminalMass.key)
        let d ← siblingMassDifference? ls rs
        return ⟨tied,previous,real,mass,leftMass,rightMass,left,right,sources.1,sources.2,
          d.slot,d.atomicNumber,d.heavy,d.light,d.earlier,d.atLeft,d.atRight,d.heavier,d.strict⟩
  none

/-- The complete sphere one step after offset k consists precisely of
the real terminal children of one reached parent. Check the routes as
well as the molecular cursors, including each cursor's previous occurrence. -/
structure SingleParentSphere (m : RawMolecule) (arm : CanonicalRerootCursor) (k : Nat) where
  parents : List IsotopeSpheres.Site
  parentsReached : IsotopeSpheres.sitesAt m arm k = some parents
  parent : IsotopeSpheres.Site
  member : parent ∈ parents
  sites : List IsotopeSpheres.Site
  reached : IsotopeSpheres.sitesAt m arm (k+1) = some sites
  children : sites.map IsotopeSpheres.Site.cursor = parent.cursor.children m
  routes : ∀ s ∈ sites, s.route = parent.route ++ [s.cursor.node]
  terminals : List (TerminalMass m)
  measured : readTerminalMasses? m (parent.cursor.children m) = some terminals
  covers : terminals.map TerminalMass.cursor = sites.map IsotopeSpheres.Site.cursor

def singleParentSphere? (m : RawMolecule) (arm : CanonicalRerootCursor) (k : Nat) :
    Option (SingleParentSphere m arm k) := do
  let ⟨ps,hp⟩ ← (IsotopeSpheres.sitesAt m arm k).attach
  let ⟨parent,found⟩ ← (ps.find? fun s => !(s.cursor.children m).isEmpty).attach
  let ⟨ss,hs⟩ ← (IsotopeSpheres.sitesAt m arm (k+1)).attach
  if children : ss.map IsotopeSpheres.Site.cursor = parent.cursor.children m then
    if routes : ∀ s ∈ ss, s.route = parent.route ++ [s.cursor.node] then
      let ⟨ts,measured⟩ ← (readTerminalMasses? m (parent.cursor.children m)).attach
      if covers : ts.map TerminalMass.cursor = ss.map IsotopeSpheres.Site.cursor then
        return ⟨ps,hp,parent,List.mem_of_find?_eq_some found,ss,hs,children,routes,ts,measured,covers⟩
  none

def SingleParentSphere.word {m a k} (s : SingleParentSphere m a k) :=
  siblingWord (s.terminals.map TerminalMass.key)

/-- Every occupied slot of the ordered mass word has a measured source
in a real terminal at its exact molecular route from the reached parent. -/
theorem SingleParentSphere.source_at_slot {m a k} (s : SingleParentSphere m a k) {i : Nat} {key : List Nat}
    (found : s.word[i]? = some key) :
    ∃ t ∈ s.terminals, t.key = key ∧ ∃ site ∈ s.sites,
      site.cursor = t.cursor ∧ site.route = s.parent.route ++ [t.cursor.node] := by
  have entry : key ∈ s.terminals.map TerminalMass.key :=
    (List.perm_insertionSort _ _).mem_iff.mp (List.mem_of_getElem? found)
  obtain ⟨t,ht,hkey⟩ := List.mem_map.mp entry
  have source : t.cursor ∈ s.sites.map IsotopeSpheres.Site.cursor := by
    rw [← s.covers]
    exact List.mem_map.mpr ⟨_,ht,rfl⟩
  obtain ⟨site,hs,eqn⟩ := List.mem_map.mp source
  exact ⟨t,ht,hkey,site,hs,eqn,by simpa [eqn] using s.routes site hs⟩

/-- Earlier complete spheres are tied under every permitted order. The
first differing sphere has a single terminal sibling group on each side. -/
structure RemoteTerminalOrder (m : RawMolecule) (a b : CanonicalRerootCursor) where
  parentOffset : Nat
  earlier : IsotopeSpheres.Earlier m a b (parentOffset+1)
  left : SingleParentSphere m a parentOffset
  right : SingleParentSphere m b parentOffset
  difference : SiblingMassDifference left.word right.word

theorem RemoteTerminalOrder.first_difference {m a b} (d : RemoteTerminalOrder m a b) :
    (∀ j < d.parentOffset+1, ∃ row : IsotopeSpheres.CheckedSphere m a b j, row.ordering = .eq) ∧
    ∀ ls rs, SiblingOrder (d.left.terminals.map TerminalMass.key) ls →
      SiblingOrder (d.right.terminals.map TerminalMass.key) rs →
      ls.take d.difference.slot = rs.take d.difference.slot ∧
      ls[d.difference.slot]? = some [d.difference.atomicNumber,d.difference.heavy] ∧
      rs[d.difference.slot]? = some [d.difference.atomicNumber,d.difference.light] ∧ rs < ls := by
  refine ⟨d.earlier.tied,?_⟩
  intro ls rs l r
  rw [siblingOrder_unique l,siblingOrder_unique r]
  exact ⟨d.difference.earlier,d.difference.atLeft,d.difference.atRight,d.difference.strict⟩

def remoteTerminalAt? {m a b k} (earlier : IsotopeSpheres.Earlier m a b (k+1)) :
    Option (RemoteTerminalOrder m a b) := do
  let left ← singleParentSphere? m a k
  let right ← singleParentSphere? m b k
  let d ← siblingMassDifference? left.word right.word
  return ⟨k,earlier,left,right,d⟩

theorem remoteTerminalAt?_coverage {m a b k} (earlier : IsotopeSpheres.Earlier m a b (k+1))
    (l : SingleParentSphere m a k) (r : SingleParentSphere m b k)
    (left : singleParentSphere? m a k = some l) (right : singleParentSphere? m b k = some r)
    (diff : SiblingMassDifference l.word r.word) (mass : siblingMassDifference? l.word r.word = some diff) :
    remoteTerminalAt? earlier = some ⟨k,earlier,l,r,diff⟩ := by
  simp [remoteTerminalAt?,left,right,mass]

def singleParentSearch (m : RawMolecule) (a b : CanonicalRerootCursor) :
    Nat → (k : Nat) → IsotopeSpheres.Earlier m a b k → Option (RemoteTerminalOrder m a b)
  | 0,_,_ => none
  | fuel+1,k,prior => do
    let row ← IsotopeSpheres.inspect? m a b k
    if tied : row.ordering = .eq then
      let earlier := IsotopeSpheres.Earlier.push prior row tied
      return ← (remoteTerminalAt? earlier).orElse (fun _ => singleParentSearch m a b fuel (k+1) earlier)
    else none

/-- Arbitrary-distance coverage. If each preceding source sphere certifies
equality and the two complete terminal groups yield a strict measured
difference, scanning those spheres necessarily finds a decision. -/
theorem singleParentSearch_coverage {m a b} (distance extra k : Nat)
    (prior : IsotopeSpheres.Earlier m a b k)
    (checks : ∀ j, k ≤ j → j ≤ k+distance → ∃ row : IsotopeSpheres.CheckedSphere m a b j,
      IsotopeSpheres.inspect? m a b j = some row ∧ row.ordering = .eq)
    (terminal : ∀ e : IsotopeSpheres.Earlier m a b (k+distance+1), (remoteTerminalAt? e).isSome = true) :
    (singleParentSearch m a b (extra+distance+1) k prior).isSome = true := by
  induction distance generalizing k with
  | zero =>
    obtain ⟨row,found,tied⟩ := checks k (by omega) (by omega)
    let earlier := IsotopeSpheres.Earlier.push prior row tied
    have yes := terminal earlier
    cases atHere : remoteTerminalAt? earlier with
    | none => simp [atHere] at yes
    | some d =>
      dsimp [earlier] at atHere
      simp only [Nat.add_zero]
      rw [singleParentSearch]
      simp [found,tied,atHere]
  | succ n ih =>
    obtain ⟨row,found,tied⟩ := checks k (by omega) (by omega)
    let earlier := IsotopeSpheres.Earlier.push prior row tied
    have shift : k+1+n = k+(n+1) := by omega
    let atOffset (j : Nat) := ∀ e : IsotopeSpheres.Earlier m a b (j+1),
      (remoteTerminalAt? e).isSome = true
    have next : atOffset (k+1+n) := (congrArg atOffset shift).mpr terminal
    have later := ih (k+1) earlier (fun j lo hi => checks j (by omega) (by omega)) next
    have size : extra+(n+1)+1 = (extra+n+1)+1 := by omega
    rw [size,singleParentSearch]
    cases atHere : remoteTerminalAt? earlier with
    | none =>
      dsimp [earlier] at atHere
      simpa [found,tied,atHere,earlier] using later
    | some d =>
      dsimp [earlier] at atHere
      simp [found,tied,atHere]

/-- All terminal children of an exact parent occurrence at the deciding sphere. -/
structure ParentGroup (m : RawMolecule) where
  parent : IsotopeSpheres.Site
  sites : List IsotopeSpheres.Site
  children : sites.map IsotopeSpheres.Site.cursor = parent.cursor.children m
  routes : ∀ s ∈ sites, s.route = parent.route ++ [s.cursor.node]
  terminals : List (TerminalMass m)
  measured : readTerminalMasses? m (parent.cursor.children m) = some terminals
  covers : terminals.map TerminalMass.cursor = sites.map IsotopeSpheres.Site.cursor

def ParentGroup.word {m} (g : ParentGroup m) := siblingWord (g.terminals.map TerminalMass.key)

private def parentGroup? (m : RawMolecule) (sites : List IsotopeSpheres.Site)
    (p : IsotopeSpheres.Site) : Option (ParentGroup m) := do
  let children := sites.filter fun s => s.route == p.route ++ [s.cursor.node]
  let ⟨ts,measured⟩ ← (readTerminalMasses? m (p.cursor.children m)).attach
  if h : children.map IsotopeSpheres.Site.cursor = p.cursor.children m ∧
      (∀ s ∈ children, s.route = p.route ++ [s.cursor.node]) ∧
      ts.map TerminalMass.cursor = children.map IsotopeSpheres.Site.cursor then
    return ⟨p,children,h.1,h.2.1,ts,measured,h.2.2⟩
  none

/-- Each reached parent supplies its complete sibling group whenever the
addressed children agree with the graph and their terminal masses are known. -/
theorem parentGroup?_total {m} (sites : List IsotopeSpheres.Site) (p : IsotopeSpheres.Site)
    (addressed : (sites.filter fun s => s.route == p.route ++ [s.cursor.node]).map
      IsotopeSpheres.Site.cursor = p.cursor.children m)
    (known : ∀ c ∈ p.cursor.children m, KnownTerminal m c) :
    (parentGroup? m sites p).isSome = true := by
  obtain ⟨ts,read,covered⟩ := readTerminalMasses?_total _ known
  simp [parentGroup?,attach_of_value read,addressed,covered]

private def parentKey {m} (g : ParentGroup m) := g.parent.rank :: g.word

def ParentOrder {m} (groups ordered : List (ParentGroup m)) : Prop :=
  groups.Perm ordered ∧ ordered.Pairwise (fun a b => IsotopeSpheres.senior m b.parent.route a.parent.route = false)

/-- The constitutional order fixes every order-sensitive parental block.
Parents with identical keys can exchange positions, including when all
active parents are tied. Children of different parents stay separate. -/
structure GroupedSphere (m : RawMolecule) (arm : CanonicalRerootCursor) (k : Nat) where
  parents : List IsotopeSpheres.Site
  parentsReached : IsotopeSpheres.sitesAt m arm k = some parents
  sites : List IsotopeSpheres.Site
  reached : IsotopeSpheres.sitesAt m arm (k+1) = some sites
  groups : List (ParentGroup m)
  parentCoverage : groups.map ParentGroup.parent = parents.filter (fun s => !(s.cursor.children m).isEmpty)
  siteCoverage : (groups.flatMap ParentGroup.sites).Perm sites
  order : List (ParentGroup m)
  legal : ParentOrder groups order
  fixed : ∀ a ∈ groups, ∀ b ∈ groups, parentKey a < parentKey b →
    IsotopeSpheres.senior m b.parent.route a.parent.route = true

def groupedSphere? (m : RawMolecule) (arm : CanonicalRerootCursor) (k : Nat) :
    Option (GroupedSphere m arm k) := do
  let ⟨ps,hp⟩ ← (IsotopeSpheres.sitesAt m arm k).attach
  let ⟨ss,hs⟩ ← (IsotopeSpheres.sitesAt m arm (k+1)).attach
  let active := ps.filter (fun s => !(s.cursor.children m).isEmpty)
  let groups ← active.mapM (parentGroup? m ss)
  let before (x y : ParentGroup m) := IsotopeSpheres.senior m y.parent.route x.parent.route = false
  let ordered := groups.insertionSort before
  if h : groups.map ParentGroup.parent = active ∧ (groups.flatMap ParentGroup.sites).Perm ss ∧
      ordered.Pairwise before ∧ (∀ a ∈ groups, ∀ b ∈ groups, parentKey a < parentKey b →
        IsotopeSpheres.senior m b.parent.route a.parent.route = true) then
    return ⟨ps,hp,ss,hs,groups,h.1,h.2.1,ordered,⟨(List.perm_insertionSort _ _).symm,h.2.2.1⟩,h.2.2.2⟩
  none

def GroupedSphere.word {m a k} (s : GroupedSphere m a k) := s.order.flatMap ParentGroup.word

/-- Every permitted permutation of parents and every legal ordering of
the children within their own parent gives the very same mass word. -/
theorem GroupedSphere.ordered_words {m a k} (s : GroupedSphere m a k)
    {groups : List (ParentGroup m)} (order : ParentOrder s.groups groups)
    {words : List (List (List Nat))} (siblings : List.Forall₂
      (fun g w => SiblingOrder (g.terminals.map TerminalMass.key) w) groups words) :
    words = s.order.map ParentGroup.word := by
  have descending (ord : List (ParentGroup m)) (valid : ParentOrder s.groups ord) :
      (ord.map parentKey).Pairwise (· ≥ ·) := by
    apply List.pairwise_map.mpr
    apply valid.2.imp_of_mem
    intro x y hx hy never
    exact le_of_not_gt fun lt => by
      have yes := s.fixed x (valid.1.mem_iff.mpr hx) y (valid.1.mem_iff.mpr hy) lt
      simp [yes] at never
  have fixed := List.Perm.eq_of_pairwise' (descending groups order) (descending s.order s.legal)
    ((order.1.symm.trans s.legal.1).map parentKey)
  have equal : groups.map ParentGroup.word = s.order.map ParentGroup.word := by
    simpa [List.map_map,parentKey,Function.comp_def] using congrArg (List.map List.tail) fixed
  have within : words = groups.map ParentGroup.word := by
    clear order fixed equal
    induction siblings with
    | nil => rfl
    | cons x _ rest => exact congrArg₂ List.cons (siblingOrder_unique x) rest
  exact within.trans equal

theorem GroupedSphere.all_orders {m a k} (s : GroupedSphere m a k)
    {groups : List (ParentGroup m)} (order : ParentOrder s.groups groups)
    {words : List (List (List Nat))} (siblings : List.Forall₂
      (fun g w => SiblingOrder (g.terminals.map TerminalMass.key) w) groups words) :
    words.flatten = s.word := by
  rw [s.ordered_words order siblings]
  rfl

/-- Nuclear charges in the canonical parent blocks. Comparing this whole
shape retains all block boundaries at the deciding sphere. -/
def GroupedSphere.nuclearGroups {m a k} (s : GroupedSphere m a k) :=
  s.order.map (fun (g : ParentGroup m) => g.word.map (fun key => key.headD 0))


private theorem parent_words_legal {m} (gs : List (ParentGroup m)) :
    List.Forall₂ (fun g w => SiblingOrder (g.terminals.map TerminalMass.key) w)
      gs (gs.map ParentGroup.word) := by
  rw [List.forall₂_map_right_iff,List.forall₂_same]
  intro g _
  exact ⟨(List.perm_insertionSort _ _).symm,List.pairwise_insertionSort _ _⟩

/-- Any pair of such complete parental populations admits one unique
comparison in all permitted traversals. The result includes mass equality
and does not assume that a strict decision has already been returned. -/
theorem grouped_parents_total {m a b k} (l : GroupedSphere m a k) (r : GroupedSphere m b k) :
    ∃! sign : Ordering, ∀ ls rs, ParentOrder l.groups ls → ParentOrder r.groups rs →
      ∀ lw rw, List.Forall₂ (fun g w => SiblingOrder (g.terminals.map TerminalMass.key) w) ls lw →
        List.Forall₂ (fun g w => SiblingOrder (g.terminals.map TerminalMass.key) w) rs rw →
        compare lw.flatten rw.flatten = sign := by
  refine ⟨compare l.word r.word,?_,?_⟩
  · intro ls rs lo ro lw rw lsib rsib
    rw [l.all_orders lo lsib,r.all_orders ro rsib]
  · intro other h
    have w := h _ _ l.legal r.legal _ _ (parent_words_legal _) (parent_words_legal _)
    simpa [GroupedSphere.word,List.flatMap_def] using w.symm

/-- Keep the source cursor with its key when ordering actual siblings.
Stable ties inherit the stored order solely to identify one concrete route. -/
def ParentGroup.orderedTerminals {m} (g : ParentGroup m) :=
  g.terminals.insertionSort (fun a b => b.key ≤ a.key)

private theorem ParentGroup.ordered_keys {m} (g : ParentGroup m) :
    g.orderedTerminals.map TerminalMass.key = g.word :=
  List.map_insertionSort (fun a b : TerminalMass m => b.key ≤ a.key) (· ≥ ·)
    TerminalMass.key g.terminals (by intros; rfl)

/-- Canonical source order at this sphere. Each terminal remains paired
with its own parent occurrence, including when terminal masses tie. -/
def GroupedSphere.addresses {m a k} (s : GroupedSphere m a k) :=
  s.order.flatMap fun g => g.orderedTerminals.map fun t => (g,t)

theorem GroupedSphere.address_keys {m a k} (s : GroupedSphere m a k) :
    s.addresses.map (fun x => x.2.key) = s.word := by
  simp [GroupedSphere.addresses,GroupedSphere.word,List.map_flatMap,List.map_map,Function.comp_def,
    ParentGroup.ordered_keys]

theorem GroupedSphere.exact_source {m a k} (s : GroupedSphere m a k) {i : Nat} {key : List Nat}
    (slot : s.word[i]? = some key) :
    ∃ g t, s.addresses[i]? = some (g,t) ∧ t.key = key ∧
      g ∈ s.groups ∧ t ∈ g.terminals ∧ ∃ site ∈ s.sites,
        site.cursor = t.cursor ∧ site.route = g.parent.route ++ [t.cursor.node] := by
  rw [← s.address_keys,List.getElem?_map] at slot
  obtain ⟨⟨g,t⟩,ht,eqn⟩ := Option.map_eq_some_iff.mp slot
  obtain ⟨g',hg,inside⟩ := List.mem_flatMap.mp (List.mem_of_getElem? ht)
  obtain ⟨u,hu,pair⟩ := List.mem_map.mp inside
  cases pair
  have measured : t ∈ g.terminals := (List.perm_insertionSort _ _).mem_iff.mp hu
  have pmem : g ∈ s.groups := s.legal.1.mem_iff.mpr hg
  have child : t.cursor ∈ g.sites.map IsotopeSpheres.Site.cursor := by
    rw [← g.covers]
    exact List.mem_map.mpr ⟨_,measured,rfl⟩
  obtain ⟨site,hs,atSite⟩ := List.mem_map.mp child
  exact ⟨g,t,ht,eqn,pmem,measured,site,s.siteCoverage.mem_iff.mp (List.mem_flatMap.mpr ⟨g,pmem,hs⟩),
    atSite,by simpa [atSite] using g.routes site hs⟩

structure GroupedTerminalOrder (m : RawMolecule) (a b : CanonicalRerootCursor) where
  parentOffset : Nat
  earlier : IsotopeSpheres.Earlier m a b (parentOffset+1)
  left : GroupedSphere m a parentOffset
  right : GroupedSphere m b parentOffset
  sameGroups : left.nuclearGroups = right.nuclearGroups
  difference : SiblingMassDifference left.word right.word

theorem GroupedTerminalOrder.first_difference {m a b} (d : GroupedTerminalOrder m a b) :
    (∀ j < d.parentOffset+1, ∃ row : IsotopeSpheres.CheckedSphere m a b j, row.ordering = .eq) ∧
    ∀ ls rs, ParentOrder d.left.groups ls → ParentOrder d.right.groups rs →
      ∀ lw rw, List.Forall₂ (fun g w => SiblingOrder (g.terminals.map TerminalMass.key) w) ls lw →
        List.Forall₂ (fun g w => SiblingOrder (g.terminals.map TerminalMass.key) w) rs rw →
        lw.flatten.take d.difference.slot = rw.flatten.take d.difference.slot ∧
        lw.flatten[d.difference.slot]? = some [d.difference.atomicNumber,d.difference.heavy] ∧
        rw.flatten[d.difference.slot]? = some [d.difference.atomicNumber,d.difference.light] ∧
        rw.flatten < lw.flatten := by
  refine ⟨d.earlier.tied,?_⟩
  intro ls rs l r lw rw left right
  rw [d.left.all_orders l left,d.right.all_orders r right]
  exact ⟨d.difference.earlier,d.difference.atLeft,d.difference.atRight,d.difference.strict⟩

private def groupedSearch (m : RawMolecule) (a b : CanonicalRerootCursor) :
    Nat → (k : Nat) → IsotopeSpheres.Earlier m a b k → Option (GroupedTerminalOrder m a b)
  | 0,_,_ => none
  | fuel+1,k,prior => do
    let row ← IsotopeSpheres.inspect? m a b k
    if tied : row.ordering = .eq then
      let earlier := IsotopeSpheres.Earlier.push prior row tied
      let candidate := do
        let l ← groupedSphere? m a k
        let r ← groupedSphere? m b k
        if shape : l.nuclearGroups = r.nuclearGroups then
          return (⟨k,earlier,l,r,shape,← siblingMassDifference? l.word r.word⟩ : GroupedTerminalOrder m a b)
        none
      candidate.orElse (fun _ => groupedSearch m a b fuel (k+1) earlier)
    else none

inductive Senior {m : RawMolecule} (path : List Nat) (a b : Arm m) : Prop where
  | atomic : ckey 3 (depth a b) b.tree < ckey 3 (depth a b) a.tree → Senior path a b
  | originalDuplicate {k} : FixedRootDecision path a b k → Senior path a b
  | directDuplicate : DirectDuplicate path a b → Senior path a b
  | duplicate {k} : OriginDecision path a b k → Senior path a b
  | terminalMass : TerminalMassOrder path a b → Senior path a b
  | singleParent : RemoteTerminalOrder m a.cursor b.cursor →
      ckey 3 (depth a b) a.tree = ckey 3 (depth a b) b.tree →
      Isomorphic m path (budget m+1) a.cursor b.cursor → Senior path a b
  | groupedParents : GroupedTerminalOrder m a.cursor b.cursor →
      ckey 3 (depth a b) a.tree = ckey 3 (depth a b) b.tree →
      Isomorphic m path (budget m+1) a.cursor b.cursor → Senior path a b
  | remote (d : IsotopeSpheres.Decision m a.cursor b.cursor) : d.ordering = .gt →
      ckey 3 (depth a b) a.tree = ckey 3 (depth a b) b.tree →
      Isomorphic m path (budget m+1) a.cursor b.cursor → Senior path a b
  | isotope (heavier : Nuclide a) (lighter : Nuclide b) :
      a.atom.element = b.atom.element → Isomorphic m path (budget m+1) a.cursor b.cursor →
      ckey 3 (depth a b) a.tree = ckey 3 (depth a b) b.tree →
      lighter.number < heavier.number → lighter.mass < heavier.mass → Senior path a b

/-- The deciding rule and its occurrence-bound evidence remain inspectable
after evaluation. Duplicate and isotope sphere numbers are one-based. -/
inductive Rule where
  | atomicNumber | duplicateOrigin (sphere : Nat) | isotopeMass (sphere : Nat)
  deriving DecidableEq, Repr

inductive Evidence {m : RawMolecule} (path : List Nat) (a b : Arm m) : Type where
  | atomic : ckey 3 (depth a b) b.tree < ckey 3 (depth a b) a.tree → Evidence path a b
  | originalDuplicate (offset : Nat) : FixedRootDecision path a b offset → Evidence path a b
  | directDuplicate : DirectDuplicate path a b → Evidence path a b
  | duplicate (offset : Nat) : OriginDecision path a b offset → Evidence path a b
  | isotope (heavier : Nuclide a) (lighter : Nuclide b) :
      a.atom.element = b.atom.element → Isomorphic m path (budget m+1) a.cursor b.cursor →
      ckey 3 (depth a b) a.tree = ckey 3 (depth a b) b.tree →
      lighter.number < heavier.number → lighter.mass < heavier.mass → Evidence path a b
  | terminalMass : TerminalMassOrder path a b → Evidence path a b
  | singleParent : RemoteTerminalOrder m a.cursor b.cursor →
      ckey 3 (depth a b) a.tree = ckey 3 (depth a b) b.tree →
      Isomorphic m path (budget m+1) a.cursor b.cursor → Evidence path a b
  | groupedParents : GroupedTerminalOrder m a.cursor b.cursor →
      ckey 3 (depth a b) a.tree = ckey 3 (depth a b) b.tree →
      Isomorphic m path (budget m+1) a.cursor b.cursor → Evidence path a b
  | spheres (d : IsotopeSpheres.Decision m a.cursor b.cursor) : d.ordering = .gt →
      ckey 3 (depth a b) a.tree = ckey 3 (depth a b) b.tree →
      Isomorphic m path (budget m+1) a.cursor b.cursor → Evidence path a b

def Evidence.rule {m p} {a b : Arm m} : Evidence p a b → Rule
  | .atomic _ => .atomicNumber
  | .originalDuplicate k _ => .duplicateOrigin (k+1)
  | .directDuplicate _ => .duplicateOrigin 1
  | .duplicate k _ => .duplicateOrigin (k+1)
  | .terminalMass _ => .isotopeMass 2
  | .singleParent d .. => .isotopeMass (d.parentOffset+2)
  | .groupedParents d .. => .isotopeMass (d.parentOffset+2)
  | .isotope .. => .isotopeMass 1
  | .spheres d .. => .isotopeMass d.sphere

theorem Evidence.senior {m p} {a b : Arm m} (proof : Evidence p a b) : Senior p a b := by
  cases proof with
  | atomic h => exact .atomic h
  | originalDuplicate _ result => exact .originalDuplicate result
  | directDuplicate result => exact .directDuplicate result
  | duplicate _ result => exact .duplicate result
  | terminalMass result => exact .terminalMass result
  | singleParent d tied same => exact .singleParent d tied same
  | groupedParents d tied same => exact .groupedParents d tied same
  | isotope x y el same tied hn hm => exact .isotope x y el same tied hn hm
  | spheres d s tied same => exact .remote d s tied same

private def reason? {m} (path : List Nat) (a b : Arm m) : Option (Evidence path a b) := do
  let d := depth a b
  match result : compareMarker (SiblingConstitution.key 3 d a.tree) (SiblingConstitution.key 3 d b.tree) with
  | .gt => return .atomic ((SiblingConstitution.compare_gt_iff 3 d a.tree b.tree).1 result)
  | .lt => none
  | .eq =>
    have tied := (SiblingConstitution.compare_eq_iff 3 d a.tree b.tree).1 result
    if let some x := DuplicatePriority.ancestorOrigin? m path a.cursor then
      if let some y := DuplicatePriority.ancestorOrigin? m path b.cursor then
        if nearer : x.depth < y.depth then return .directDuplicate ⟨tied,x,y,nearer⟩
    if let some ⟨k,witness⟩ := DuplicatePriority.first? m path a.cursor b.cursor (d+1) 0 then
      let ⟨left⟩ ← DuplicatePriority.through? m path a.cursor 3 d a.tree k
      let ⟨right⟩ ← DuplicatePriority.through? m path b.cursor 3 d b.tree k
      return .duplicate k ⟨tied,left,right,witness⟩
    if let some ⟨k,witness⟩ := DuplicatePriority.firstOriginal? m path a.cursor b.cursor (d+1) 0 then
      let ⟨left⟩ ← DuplicatePriority.through? m path a.cursor 3 d a.tree k
      let ⟨right⟩ ← DuplicatePriority.through? m path b.cursor 3 d b.tree k
      return .originalDuplicate k ⟨tied,left,right,witness⟩
    guard (m.atoms.any fun x => x.isotope?.isSome)
    if same : isomorphic m path (budget m+1) a.cursor b.cursor = true then
      if let some x := nuclide? a then
        if let some y := nuclide? b then
          if eqn : a.atom.element = b.atom.element then
            if masses : y.number < x.number ∧ y.mass < x.mass then
              return .isotope x y eqn (isomorphic_sound same) tied masses.1 masses.2
      if let some terminal := terminalMassOrder? a b tied (isomorphic_sound same) then
        return .terminalMass terminal
      if let some comparison := IsotopeSpheres.compare? m a.cursor b.cursor then
        if wins : comparison.ordering = .gt then
          return .spheres comparison wins tied (isomorphic_sound same)
      else if let some remote := singleParentSearch m a.cursor b.cursor (budget m+1) 0 .start then
        return .singleParent remote tied (isomorphic_sound same)
      else if let some groups := groupedSearch m a.cursor b.cursor (budget m+1) 0 .start then
        return .groupedParents groups tied (isomorphic_sound same)
    none

private def incidentArm? (m : RawMolecule) (cs : List CanonicalRerootCursor) (i : Nat) :
    Option {a : Arm m // a.cursor ∈ cs ∧ a.cursor.node.atom = i} := do
  let ⟨c,found⟩ ← (cs.find? fun c => c.node.atom == i).attach
  let a ← arm? m c
  if same : a.cursor = c then
    return ⟨a,by simpa only [same] using List.mem_of_find?_eq_some found,by simpa [same] using List.find?_some found⟩
  none

/-- Both addressed ligands and their full retained trees at one focus. -/
structure IncidentPair (m : RawMolecule) (path : List Nat) (i j : Nat) where
  domain : saturatedWithHalogens m = true
  focus : RawMolecule.CanonicalBranchNode
  reached : occurrence? m path = some focus
  four : (occurrenceLigandCursors m focus).length = 4
  distinct : i ≠ j
  left : Arm m
  right : Arm m
  leftAt : left.cursor ∈ occurrenceLigandCursors m focus ∧ left.cursor.node.atom = i
  rightAt : right.cursor ∈ occurrenceLigandCursors m focus ∧ right.cursor.node.atom = j

private def incidentPair? (m : RawMolecule) (path : List Nat) (i j : Nat) : Option (IncidentPair m path i j) := do
  if valid : saturatedWithHalogens m = true then
    let ⟨focus,reached⟩ ← (occurrence? m path).attach
    let cs := occurrenceLigandCursors m focus
    if four : cs.length = 4 then
      if distinct : i ≠ j then
        let ⟨a,ha⟩ ← incidentArm? m cs i
        let ⟨b,hb⟩ ← incidentArm? m cs j
        return ⟨valid,focus,reached,four,distinct,a,b,ha,hb⟩
  none

/-- After hydrogens are expanded into the molecular graph, bracket hydrogen
counts and local SMILES parity are presentation data. Constitution keeps
the element, isotope, charge and aromaticity of the addressed atom. -/
def constitutionalAtom (a : AtomSpec) : AtomSpec :=
  {a with explicitHydrogens? := none, tetrahedral? := none}

theorem constitutionalAtom_eq_iff (a b : AtomSpec) :
    constitutionalAtom a = constitutionalAtom b ↔
      a.element = b.element ∧ a.isotope? = b.isotope? ∧ a.charge = b.charge ∧
        a.aromatic = b.aromatic := by
  cases a
  cases b
  simp [constitutionalAtom]

/-- Once Rule 2 has read the physical mass, retain the atom's non-isotopic
properties alongside that value. The molecular source retains the isotope
spelling used for lookup. -/
def massIndependentAtom (a : AtomSpec) := {constitutionalAtom a with isotope? := none}

theorem massIndependentAtom_eq_iff (a b : AtomSpec) :
    massIndependentAtom a = massIndependentAtom b ↔ a.element = b.element ∧
      a.charge = b.charge ∧ a.aromatic = b.aromatic := by
  cases a
  cases b
  simp [massIndependentAtom,constitutionalAtom]

/-- The original occurrence and its real origin remain in the prior
observation. The constitutional properties and mass come from its molecular site. -/
structure FullObservation where
  prior : PriorObservation
  atom : AtomSpec
  sourceMass : Nat
  deriving DecidableEq

def observeAtom? (prior : PriorObservation) (a : AtomSpec) : Option FullObservation := do
  let mass ← CIPRule2MassData.rule2MassPico? a.element.atomicNumber a.isotope?
  return ⟨prior,massIndependentAtom a,mass⟩

/-- With both mass lookups successful and earlier provenance identical,
ordinary and explicitly isotopic spellings agree exactly when all of the
remaining molecular properties and the actual Rule 2 values agree. -/
theorem observeAtom?_eq_iff {prior : PriorObservation} {a b : AtomSpec} {x y : Nat}
    (left : CIPRule2MassData.rule2MassPico? a.element.atomicNumber a.isotope? = some x)
    (right : CIPRule2MassData.rule2MassPico? b.element.atomicNumber b.isotope? = some y) :
    observeAtom? prior a = observeAtom? prior b ↔ a.element = b.element ∧
      a.charge = b.charge ∧ a.aromatic = b.aromatic ∧ x = y := by
  simp [observeAtom?,left,right,massIndependentAtom_eq_iff,and_assoc]

def fullObservation? (m : RawMolecule) (path : List Nat) (c : CanonicalRerootCursor) :
    Option FullObservation := do
  let prior ← observation? m path c
  let atom ← m.atoms[c.node.atom]?
  observeAtom? prior atom

theorem fullObservation?_source {m p c o} (read : fullObservation? m p c = some o) :
    ∃ a, m.atoms[c.node.atom]? = some a ∧ observation? m p c = some o.prior ∧
      o.atom = massIndependentAtom a ∧
      CIPRule2MassData.rule2MassPico? a.element.atomicNumber a.isotope? = some o.sourceMass := by
  cases prior : observation? m p c with
  | none => simp [fullObservation?,prior] at read
  | some obs =>
    cases atom : m.atoms[c.node.atom]? with
    | none => simp [fullObservation?,prior,atom] at read
    | some a =>
      cases mass : CIPRule2MassData.rule2MassPico? a.element.atomicNumber a.isotope? with
      | none => simp [fullObservation?,observeAtom?,prior,atom,mass] at read
      | some v =>
        simp [fullObservation?,observeAtom?,prior,atom,mass] at read
        subst o
        exact ⟨a,rfl,rfl,rfl,mass⟩

abbrev FullTie (m : RawMolecule) (path : List Nat) (a b : Arm m) :=
  TreesMatch m (fullObservation? m path) (budget m+1) a.cursor b.cursor

/-- An equality result preserves every observation at every matched node.
Either strict result retains both its deciding rule and its molecular proof. -/
inductive PairVerdict {m : RawMolecule} (path : List Nat) (a b : Arm m) : Type where
  | greater : Evidence path a b → PairVerdict path a b
  | less : Evidence path b a → PairVerdict path a b
  | equal : FullTie m path a b → PairVerdict path a b

def PairVerdict.ordering {m p} {a b : Arm m} : PairVerdict p a b → Ordering
  | .greater _ => .gt
  | .less _ => .lt
  | .equal _ => .eq

def PairVerdict.rule? {m p} {a b : Arm m} : PairVerdict p a b → Option Rule
  | .greater h => some h.rule
  | .less h => some h.rule
  | .equal _ => none

structure IncidentComparison (m : RawMolecule) (path : List Nat) (i j : Nat) where
  pair : IncidentPair m path i j
  verdict : PairVerdict path pair.left pair.right

def IncidentComparison.ordering {m p i j} (c : IncidentComparison m p i j) := c.verdict.ordering
def IncidentComparison.rule? {m p i j} (c : IncidentComparison m p i j) := c.verdict.rule?

/-- The caller may request either direction. A missing result carries no
priority judgement. A positive equality requires a complete tree match. -/
def compareIncident? (m : RawMolecule) (path : List Nat) (i j : Nat) :
    Option (IncidentComparison m path i j) := do
  let c ← incidentPair? m path i j
  if let some ev := reason? path c.left c.right then return ⟨c,.greater ev⟩
  if let some ev := reason? path c.right c.left then return ⟨c,.less ev⟩
  if tied : treesMatch m (fullObservation? m path) (budget m+1) c.left.cursor c.right.cursor = true then
    return ⟨c,.equal (treesMatch_sound tied)⟩
  none

theorem IncidentComparison.equal_trees {m p i j} (c : IncidentComparison m p i j)
    (equal : c.ordering = .eq) : FullTie m p c.pair.left c.pair.right := by
  cases c with
  | mk pair verdict =>
    cases verdict with
    | greater h => simp [IncidentComparison.ordering,PairVerdict.ordering] at equal
    | less h => simp [IncidentComparison.ordering,PairVerdict.ordering] at equal
    | equal same => exact same

/-- All permutation-invariant folds over full atomic, isotopic and duplicate
observations have equal values on the two matched molecular ligand trees. -/
theorem IncidentComparison.equal_observer {α : Type} {m p i j} (c : IncidentComparison m p i j)
    (equal : c.ordering = .eq) (reader : Nat → CanonicalRerootCursor → α)
    (combine : FullObservation → List α → α)
    (atNode : ∀ n cursor o, fullObservation? m p cursor = some o →
      reader (n+1) cursor = combine o ((cursor.children m).map (reader n)))
    (symmetric : ∀ o {xs ys : List α}, xs.Perm ys → combine o xs = combine o ys) :
    reader (budget m+1) c.pair.left.cursor = reader (budget m+1) c.pair.right.cursor :=
  TreesMatch.observer_eq (c.equal_trees equal) reader combine atNode symmetric

/-- First-diverging outward siblings in the original digraph. The focus
may precede their common parent by arbitrarily many bonds. -/
structure SiblingDecision (m : RawMolecule) (focus p q : List Nat) where
  domain : saturatedWithHalogens m = true
  focused : (occurrence? m focus).isSome
  parent : RawMolecule.CanonicalBranchNode
  reached : occurrence? m p.dropLast = some parent
  descendant : focus <+: p.dropLast
  distinct : p ≠ q
  left : Arm m
  right : Arm m
  leftChild : left.cursor.node ∈ m.canonicalChildren parent ∧
    left.cursor.previous? = some parent ∧ left.cursor.node.history.reverse = p
  rightChild : right.cursor.node ∈ m.canonicalChildren parent ∧
    right.cursor.previous? = some parent ∧ right.cursor.node.history.reverse = q
  evidence : Evidence focus left right

private def childArm? (m : RawMolecule) (parent : RawMolecule.CanonicalBranchNode) (p : List Nat) :
    Option {a : Arm m // a.cursor.node ∈ m.canonicalChildren parent ∧
      a.cursor.previous? = some parent ∧ a.cursor.node.history.reverse = p} := do
  let ⟨n,found⟩ ← ((m.canonicalChildren parent).find? (fun n => n.history.reverse == p)).attach
  let c : CanonicalRerootCursor := ⟨n,some parent⟩
  let a ← arm? m c
  if eqn : a.cursor = c then
    return ⟨a,by rw [eqn]; exact List.mem_of_find?_eq_some found,by simp [eqn,c],
      by simpa [eqn,c] using List.find?_some found⟩
  none

def sibling? (m : RawMolecule) (focus p q : List Nat) : Option (SiblingDecision m focus p q) := do
  if domain : saturatedWithHalogens m = true then
    if focused : (occurrence? m focus).isSome then
      if stem : focus <+: p.dropLast then
        if distinct : p ≠ q then
          let ⟨parent,reached⟩ ← (occurrence? m p.dropLast).attach
          let ⟨a,ha⟩ ← childArm? m parent p
          let ⟨b,hb⟩ ← childArm? m parent q
          return ⟨domain,focused,parent,reached,stem,distinct,a,b,ha,hb,← reason? focus a b⟩
  none

private def prepare (m : RawMolecule) : (cs : List CanonicalRerootCursor) →
    Option {arms : List (Arm m) // arms.map Arm.cursor = cs}
  | [] => some ⟨[],rfl⟩
  | c :: cs => do
    let a ← arm? m c
    let ⟨rest,keys⟩ ← prepare m cs
    if hc : a.cursor = c then return ⟨a :: rest,by simp [hc,keys]⟩
    none

structure Ranking (m : RawMolecule) (path : List Nat) where
  domain : saturatedWithHalogens m = true
  focus : RawMolecule.CanonicalBranchNode
  reached : occurrence? m path = some focus
  carbon : (m.atoms[focus.atom]?).any (fun a => a.element == .C) = true
  four : (occurrenceLigandCursors m focus).length = 4
  distinct : ((occurrenceLigandCursors m focus).map (·.node.atom)).Nodup
  arms : List (Arm m)
  complete : (arms.map Arm.cursor).Perm (occurrenceLigandCursors m focus)
  strict : arms.Pairwise (Senior path)

/-- Strict four-ligand priority order, independently of coordinates or
auxiliary stereodescriptors. The incoming parent cursor participates in
exactly the same constitutional and mass comparisons as every other arm. -/
def rank? (m : RawMolecule) (path : List Nat) : Option (Ranking m path) := do
  if valid : saturatedWithHalogens m = true then
    let ⟨focus,reached⟩ ← (occurrence? m path).attach
    if carbon : (m.atoms[focus.atom]?).any (fun a => a.element == .C) = true then
      let cs := occurrenceLigandCursors m focus
      if four : cs.length = 4 then
        if distinct : (cs.map (·.node.atom)).Nodup then
          let ⟨arms,keys⟩ ← prepare m cs
          let cmp (a b : Arm m) := (reason? path a b).isSome = true
          let sorted := arms.insertionSort cmp
          if strict : sorted.Pairwise cmp then
            have perm := (List.perm_insertionSort cmp arms).map Arm.cursor
            return ⟨valid,focus,reached,carbon,four,distinct,sorted,by simpa only [keys] using perm,
              strict.imp (by intro a b h; exact ((reason? path a b).get h).senior)⟩
  none

def Ranking.order {m path} (r : Ranking m path) := r.arms.map (·.cursor.node.atom)

def order? (m : RawMolecule) (path : List Nat) := (rank? m path).map Ranking.order

end TetraStereo.Engine.RingChemicalPriority.IsotopePriority

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.isomorphic_sound
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.rank?
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.Isomorphic.observer_eq
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.Isomorphic.equal_ring_origin_counts
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.treesMatch_sound
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.treesMatch_iff
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.TreesMatch.observer_eq
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.compareIncident?
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.IncidentComparison.equal_trees
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.IncidentComparison.equal_observer
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.OriginDecision.first_difference

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.terminal_siblings_total
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.TerminalMassOrder.all_orders
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.SingleParentSphere.source_at_slot
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.RemoteTerminalOrder.first_difference
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.remoteTerminalAt?_coverage
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.singleParentSearch_coverage
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.constitutionalAtom_eq_iff
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.observeAtom?_eq_iff
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.fullObservation?_source
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.DirectDuplicate.focus_reverses
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.FixedRootDecision.first_difference

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.GroupedTerminalOrder.first_difference
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.GroupedSphere.exact_source
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.grouped_parents_total
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopePriority.parentGroup?_total
