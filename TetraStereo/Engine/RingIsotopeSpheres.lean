import TetraStereo.Engine.RingHierarchyLinearizations
import TetraStereo.Engine.RingSiblingConstitution
import TetraStereo.OneCenter.CIPRule2MassData

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.IsotopeSpheres
open OneCenter CertifiedLocalizedCIPInput

/-- The route is the walk from the proximal ligand in the retained digraph.
It also records upward steps when the ligand is the focus's incoming parent. -/
structure Site where
  cursor : CanonicalRerootCursor
  route : List RawMolecule.CanonicalBranchNode
  rank : List Nat
  fixed : Bool
  deriving DecidableEq

private def advance (m : RawMolecule) (s : Site) : Option (List Site) := do
  let siblings ← (s.cursor.children m).mapM fun c => do
    let a ← m.atoms[c.node.atom]?
    return (c,a.element.atomicNumber)
  return siblings.map fun (c,z) =>
    ⟨c,s.route ++ [c.node],if s.fixed then s.rank ++ [z] else s.rank,
      s.fixed && siblings.countP (fun e => e.2 == z) == 1⟩

/-- Offset zero is chemical sphere I. Every cursor at each subsequent
distance is generated from all children of the preceding sphere. -/
def sitesAt (m : RawMolecule) (c : CanonicalRerootCursor) : Nat → Option (List Site)
  | 0 => some [⟨c,[c.node],[],true⟩]
  | k+1 => do return (← (← sitesAt m c k).mapM (advance m)).flatten

/-- A missing coordinate plays no role in comparing masses. A duplicate
has no measured nuclide in this checker. Such a sphere is left unresolved. -/
def realMass? (m : RawMolecule) (s : Site) : Option Nat := do
  guard (s.cursor.node.provenance == .realAtom)
  let a ← m.atoms[s.cursor.node.atom]?
  CIPRule2MassData.rule2MassPico? a.element.atomicNumber a.isotope?

structure Entry where
  site : Site
  mass : Nat
  deriving DecidableEq

private def observe (m : RawMolecule) : (ss : List Site) →
    Option {es : List Entry // es.map Entry.site = ss ∧ ∀ e ∈ es, realMass? m e.site = some e.mass}
  | [] => some ⟨[],rfl,by simp⟩
  | s :: ss => do
    let ⟨mass,source⟩ ← (realMass? m s).attach
    let ⟨rest,sites,valid⟩ ← observe m ss
    return ⟨⟨s,mass⟩ :: rest,by simp [sites],by
      intro e he
      rcases List.mem_cons.mp he with rfl | below
      · exact source
      · exact valid e below⟩

/-- At the first divergence the two occurrences really are siblings.
A strictly higher atomic number fixes their order and their descendants'
order. Equal atomic numbers impose no preference by this test. -/
def senior (m : RawMolecule) : List RawMolecule.CanonicalBranchNode →
    List RawMolecule.CanonicalBranchNode → Bool
  | a :: as,b :: bs => if a = b then senior m as bs else
      (m.atoms[a.atom]?).any fun x => (m.atoms[b.atom]?).any fun y =>
        x.element.atomicNumber > y.element.atomicNumber
  | _,_ => false

theorem senior_self (m : RawMolecule) (p) : senior m p p = false := by
  induction p <;> simp_all [senior]

def Before (m : RawMolecule) (a b : Entry) := senior m a.site.route b.site.route = true
instance (m : RawMolecule) (a b : Entry) : Decidable (Before m a b) :=
  inferInstanceAs (Decidable (_ = true))

/-- A legal order lists all the actual entries and respects every
constitutional parent preference found on their two molecular routes. -/
def Legal (m : RawMolecule) (entries order : List Entry) :=
  entries.Perm order ∧ order.Pairwise (fun a b => ¬ Before m b a)

structure Row (m : RawMolecule) (ss : List Site) where
  entries : List Entry
  covered : entries.map Entry.site = ss
  masses : ∀ e ∈ entries, realMass? m e.site = some e.mass
  witness : List Entry
  witnessed : Legal m entries witness
  blocks : List (List Entry)
  complete : blocks.flatten.Perm entries
  separated : blocks.Pairwise (fun l r => ∀ a ∈ l, ∀ b ∈ r, Before m a b)

private def row? (m : RawMolecule) (ss : List Site) : Option (Row m ss) := do
  guard (!ss.isEmpty)
  let ⟨es,covered,masses⟩ ← observe m ss
  let descending (a b : Entry) := ¬ Before m b a
  let witness := es.insertionSort descending
  if legal : witness.Pairwise descending then
    let groups := ((es.map (·.site.rank)).eraseDups).insertionSort (fun a b => b ≤ a)
    let blocks := groups.map (fun k => es.filter (fun e => e.site.rank == k))
    if full : blocks.flatten.Perm es then
      if split : blocks.Pairwise (fun l r => ∀ a ∈ l, ∀ b ∈ r, Before m a b) then
        return ⟨es,covered,masses,witness,⟨(List.perm_insertionSort _ _).symm,legal⟩,blocks,full,split⟩
  none

def Row.massBlocks {m ss} (r : Row m ss) := r.blocks.map (List.map Entry.mass)

theorem Row.legalMasses {m ss} (r : Row m ss) {order} (legal : Legal m r.entries order) :
    ∃ words, List.Forall₂ List.Perm r.massBlocks words ∧ words.flatten = order.map Entry.mass := by
  obtain ⟨parts,perms,flat⟩ := Hierarchy.split_linearization (Before m)
    (by intro a; simp [Before,senior_self]) r.blocks order r.separated (r.complete.trans legal.1) legal.2
  refine ⟨parts.map (List.map Entry.mass),?_,?_⟩
  · exact List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr
      (perms.imp fun _ _ h => h.map _))
  · simp [← flat,List.map_flatten]

def Sign {α : Type} [LT α] (o : Ordering) (a b : α) : Prop :=
  match o with | .lt => a < b | .eq => a = b | .gt => b < a

private theorem uniform {l r : List Nat} (len : l.length = r.length)
    (same : ∀ x ∈ l, ∀ y ∈ r, x = y) : l = r := by
  induction l generalizing r with
  | nil => cases r <;> simp_all
  | cons x xs ih =>
    cases r with
    | nil => simp at len
    | cons y ys =>
      exact congrArg₂ List.cons (same x (by simp) y (by simp))
        (ih (by simpa using len) (fun a ha b hb => same a (by simp [ha]) b (by simp [hb])))

private theorem dominates {l r : List Nat} (len : l.length = r.length)
    (weak : ∀ x ∈ l, ∀ y ∈ r, y ≤ x) (excess : r.sum < l.sum) : r < l := by
  induction l generalizing r with
  | nil => cases r <;> simp_all
  | cons x xs ih =>
    cases r with
    | nil => simp at len
    | cons y ys =>
      rcases lt_or_eq_of_le (weak x (by simp) y (by simp)) with less | rfl
      · exact List.cons_lt_cons_iff.mpr (.inl less)
      · exact List.cons_lt_cons_iff.mpr (.inr ⟨rfl,ih (by simpa using len)
            (fun a ha b hb => weak a (by simp [ha]) b (by simp [hb]))
            (by simpa using excess)⟩)

private def block? (l r : List Nat) :
    Option {o : Ordering // ∀ a b, l.Perm a → r.Perm b → Sign o a b} := do
  if len : l.length = r.length then
    if same : ∀ x ∈ l, ∀ y ∈ r, x = y then
      return ⟨.eq,fun _ _ lp rp => uniform (lp.length_eq.symm.trans (len.trans rp.length_eq))
        (fun x hx y hy => same x (lp.mem_iff.mpr hx) y (rp.mem_iff.mpr hy))⟩
    if gt : (∀ x ∈ l, ∀ y ∈ r, y ≤ x) ∧ r.sum < l.sum then
      return ⟨.gt,fun _ _ lp rp => dominates (lp.length_eq.symm.trans (len.trans rp.length_eq))
        (fun x hx y hy => gt.1 x (lp.mem_iff.mpr hx) y (rp.mem_iff.mpr hy))
        (by simpa only [← lp.sum_eq,← rp.sum_eq] using gt.2)⟩
    if lt : (∀ y ∈ r, ∀ x ∈ l, x ≤ y) ∧ l.sum < r.sum then
      return ⟨.lt,fun _ _ lp rp => dominates (rp.length_eq.symm.trans (len.symm.trans lp.length_eq))
        (fun y hy x hx => lt.1 y (rp.mem_iff.mpr hy) x (lp.mem_iff.mpr hx))
        (by simpa only [← lp.sum_eq,← rp.sum_eq] using lt.2)⟩
  none

private theorem prepend {o : Ordering} {a b : List (List Nat)} (x : List Nat) (h : Sign o a b) :
    Sign o (x :: a) (x :: b) := by
  cases o with
  | eq => exact congrArg (List.cons x) h
  | lt => exact List.cons_lt_cons_iff.mpr (.inr ⟨rfl,h⟩)
  | gt => exact List.cons_lt_cons_iff.mpr (.inr ⟨rfl,h⟩)

def sequence? : (ls rs : List (List Nat)) →
    Option {o : Ordering // ∀ a b, List.Forall₂ List.Perm ls a →
      List.Forall₂ List.Perm rs b → Sign o a b}
  | [],[] => some ⟨.eq,by intro a b l r; cases l; cases r; rfl⟩
  | x :: xs,y :: ys => do
    match ← block? x y with
    | ⟨.eq,same⟩ =>
      let ⟨o,later⟩ ← sequence? xs ys
      return ⟨o,by
        intro a b l r
        cases l with | cons hx ht =>
          cases r with | cons hy hs =>
            have heads := same _ _ hx hy
            change _ = _ at heads
            subst_vars
            exact prepend _ (later _ _ ht hs)⟩
    | ⟨.lt,smaller⟩ => return ⟨.lt,by
        intro a b l r
        cases l with | cons hx _ =>
          cases r with | cons hy _ => exact List.cons_lt_cons_iff.mpr (.inl (smaller _ _ hx hy))⟩
    | ⟨.gt,larger⟩ => return ⟨.gt,by
        intro a b l r
        cases l with | cons hx _ =>
          cases r with | cons hy _ => exact List.cons_lt_cons_iff.mpr (.inl (larger _ _ hx hy))⟩
  | _,_ => none

theorem shapes {a b : List (List Nat)} (h : List.Forall₂ List.Perm a b) :
    a.map List.length = b.map List.length := by
  induction h with
  | nil => rfl
  | cons head _ tail => exact congrArg₂ List.cons head.length_eq tail

structure CheckedSphere (m : RawMolecule) (a b : CanonicalRerootCursor) (offset : Nat) where
  leftSites : List Site
  rightSites : List Site
  leftReached : sitesAt m a offset = some leftSites
  rightReached : sitesAt m b offset = some rightSites
  left : Row m leftSites
  right : Row m rightSites
  ordering : Ordering
  allOrders : ∀ l r, Legal m left.entries l → Legal m right.entries r →
    Sign ordering (l.map Entry.mass) (r.map Entry.mass)

/-- Check an entire isotope sphere in every order allowed by the constitutional hierarchy. -/
def inspect? (m : RawMolecule) (a b : CanonicalRerootCursor) (offset : Nat) :
    Option (CheckedSphere m a b offset) := do
  let ⟨ls,lReached⟩ ← (sitesAt m a offset).attach
  let ⟨rs,rReached⟩ ← (sitesAt m b offset).attach
  let l ← row? m ls
  let r ← row? m rs
  if shape : l.massBlocks.map List.length = r.massBlocks.map List.length then
    let ⟨o,bound⟩ ← sequence? l.massBlocks r.massBlocks
    return ⟨ls,rs,lReached,rReached,l,r,o,by
      intro u v lu rv
      obtain ⟨us,up,uw⟩ := l.legalMasses lu
      obtain ⟨vs,vp,vw⟩ := r.legalMasses rv
      have sameShape := (shapes up).symm.trans (shape.trans (shapes vp))
      have signed := bound us vs up vp
      rw [← uw,← vw]
      cases o with
      | eq => exact congrArg List.flatten signed
      | lt => exact Hierarchy.flatten_strict sameShape signed
      | gt => exact Hierarchy.flatten_strict sameShape.symm signed⟩
  none

/-- Earlier spheres retain their complete molecular data and universal
equality proofs. No choice of within-block order can change these ties. -/
inductive Earlier (m : RawMolecule) (a b : CanonicalRerootCursor) : Nat → Type where
  | start : Earlier m a b 0
  | push {k} : Earlier m a b k → (row : CheckedSphere m a b k) →
      row.ordering = .eq → Earlier m a b (k+1)

theorem Earlier.tied {m a b k} (prior : Earlier m a b k) :
    ∀ j < k, ∃ row : CheckedSphere m a b j, row.ordering = .eq := by
  induction prior with
  | start => intro _ h; omega
  | @push k _ row eqn ih =>
    intro j hj
    by_cases same : j = k
    · subst j; exact ⟨row,eqn⟩
    · exact ih j (by omega)

instance {α : Type} [DecidableEq α] [LT α] [DecidableLT α] (o : Ordering) (a b : α) :
    Decidable (Sign o a b) := by cases o <;> unfold Sign <;> infer_instance

/-- One concrete first unequal pair in the two witnessed legal orders.
Other legal orders may expose the same winner at another slot of the sphere. -/
structure FirstPair {m a b k} (row : CheckedSphere m a b k) where
  slot : Nat
  left : Entry
  right : Entry
  leftAt : row.left.witness[slot]? = some left
  rightAt : row.right.witness[slot]? = some right
  ties : ((row.left.witness.take slot).map Entry.mass) = ((row.right.witness.take slot).map Entry.mass)
  signed : Sign row.ordering left.mass right.mass

private def firstPair? {m a b k} (r : CheckedSphere m a b k) : Option (FirstPair r) := do
  let left := r.left.witness
  let right := r.right.witness
  let i ← (List.range left.length).find? fun j => (left[j]?.map Entry.mass) != (right[j]?.map Entry.mass)
  let ⟨x,hx⟩ ← left[i]?.attach
  let ⟨y,hy⟩ ← right[i]?.attach
  if ties : (left.take i).map Entry.mass = (right.take i).map Entry.mass then
    if signed : Sign r.ordering x.mass y.mass then return ⟨i,x,y,hx,hy,ties,signed⟩
  none

structure Decision (m : RawMolecule) (a b : CanonicalRerootCursor) where
  offset : Nat
  previous : Earlier m a b offset
  current : CheckedSphere m a b offset
  strict : current.ordering ≠ .eq
  first : FirstPair current

def Decision.sphere {m a b} (d : Decision m a b) := d.offset + 1
def Decision.ordering {m a b} (d : Decision m a b) := d.current.ordering

private def search (m : RawMolecule) (a b : CanonicalRerootCursor) :
    Nat → (k : Nat) → Earlier m a b k → Option (Decision m a b)
  | 0,_,_ => none
  | fuel+1,k,prior => do
    let row ← inspect? m a b k
    if tied : row.ordering = .eq then
      search m a b fuel (k+1) (.push prior row tied)
    else
      return ⟨k,prior,row,tied,← firstPair? row⟩

/-- Read masses on the actual retained arms until the first forced order.
The caller establishes the prior-rule tie before applying this Rule 2
comparison. Unresolved order or a required duplicate mass yields no result. -/
def compare? (m : RawMolecule) (a b : CanonicalRerootCursor) : Option (Decision m a b) :=
  search m a b (2*(m.atomCount+1)+1) 0 .start

theorem Decision.first_difference {m a b} (d : Decision m a b) :
    (∀ j < d.offset, ∃ r : CheckedSphere m a b j, r.ordering = .eq) ∧
    (∀ l r, Legal m d.current.left.entries l → Legal m d.current.right.entries r →
      Sign d.ordering (l.map Entry.mass) (r.map Entry.mass)) :=
  ⟨d.previous.tied,d.current.allOrders⟩

end TetraStereo.Engine.RingChemicalPriority.IsotopeSpheres

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopeSpheres.Row.legalMasses
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopeSpheres.Decision.first_difference
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.IsotopeSpheres.compare?
