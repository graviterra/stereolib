import TetraStereo.Engine.RingSiblingConstitution

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.IsotopePriority
open OneCenter CertifiedLocalizedCIPInput

/-- Distance in the original occurrence tree, including paths that travel
back toward its original root before diverging from the new focus. -/
def pathDistance : List Nat → List Nat → Nat
  | [],q => q.length
  | p,[] => p.length
  | x :: xs,y :: ys => if x = y then pathDistance xs ys else xs.length + ys.length + 2

structure PriorObservation where
  element : Element
  provenance : RawMolecule.CanonicalNodeProvenance
  originalDepth : Nat
  sourceDistanceFromFocus : Nat
  deriving DecidableEq

/-- A ring duplicate points back to a specific real occurrence, identified
by the stored original root distance on this path. Check that the prefix
really reaches that atom. Retain its distance from the current focus too. -/
def observation? (m : RawMolecule) (focus : List Nat) (c : CanonicalRerootCursor) :
    Option PriorObservation := do
  let a ← m.atoms[c.node.atom]?
  let address := c.node.history.reverse
  let origin ← match c.node.provenance with
    | .realAtom => some address
    | .ringDuplicate d => do
      guard (d+1 < address.length)
      let stem := address.take (d+1)
      let previous ← occurrence? m stem
      guard (previous.atom == c.node.atom && previous.provenance == .realAtom &&
        previous.history.reverse == stem)
      pure stem
    | _ => none
  return ⟨a.element,c.node.provenance,c.node.depth,pathDistance focus origin⟩

end TetraStereo.Engine.RingChemicalPriority.IsotopePriority

namespace TetraStereo.Engine.RingChemicalPriority.DuplicatePriority
open OneCenter CertifiedLocalizedCIPInput IsotopePriority

/-- Every real or terminal duplicate occurrence at exactly this distance
from the proximal ligand in the retained digraph. -/
def shell (m : RawMolecule) (c : CanonicalRerootCursor) : Nat → List CanonicalRerootCursor
  | 0 => [c]
  | k+1 => (shell m c k).flatMap (·.children m)

abbrev Row := List PriorObservation

def row? (m : RawMolecule) (focus : List Nat) (c : CanonicalRerootCursor) (k : Nat) :=
  (shell m c k).mapM (observation? m focus)

/-- Compare two otherwise aligned positions. At a strict position both are
ring duplicates, and both the original and the retained focus see the first
real origin nearer. At a tied position the entire earlier observation agrees. -/
def closer (a b : PriorObservation) : Bool :=
  match a.provenance, b.provenance with
  | .ringDuplicate x, .ringDuplicate y =>
    a.element == b.element && a.originalDepth == b.originalDepth &&
      x < y && a.sourceDistanceFromFocus < b.sourceDistanceFromFocus
  | _,_ => false

theorem closer_dist {a b} (h : closer a b = true) :
    a.sourceDistanceFromFocus < b.sourceDistanceFromFocus := by
  unfold closer at h
  split at h <;> simp_all

structure Common (a b : Row) : Prop where
  inhabited : ∃ l r : Row, l.Perm a ∧ r.Perm b ∧ l.map PriorObservation.element = r.map PriorObservation.element

structure Tied (a b : Row) : Prop extends Common a b where
  equal : ∀ x ∈ a, ∀ y ∈ b, x.element = y.element → x = y

structure Nearer (a b : Row) : Prop extends Common a b where
  aligned : ∀ x ∈ a, ∀ y ∈ b, x.element = y.element → x = y ∨ closer x y = true
  witness : ∃ x ∈ a, ∀ y ∈ b, x.element = y.element → closer x y = true

/-- All presentations compatible with the preceding atomic-number keys have
the same element at corresponding occupied slots. Allow every such presentation,
including ones that would be excluded by an earlier parent priority. -/
structure Presentation (a b l r : Row) : Prop where
  left : l.Perm a
  right : r.Perm b
  elements : l.map PriorObservation.element = r.map PriorObservation.element

open Certificate.CanonicalSphereKey

/-- Each admissible ordering may independently permute every molecular parent's
children. Tracking its parent group preserves every original cursor occurrence. -/
def orderedShell (c : CanonicalRerootCursor)
    (order : Nat → CanonicalRerootCursor → List CanonicalRerootCursor) :
    Nat → List CanonicalRerootCursor
  | 0 => [c]
  | k+1 => (orderedShell c order k).flatMap (order k)

theorem orderedShell_perm (m : RawMolecule) (c : CanonicalRerootCursor)
    (order : Nat → CanonicalRerootCursor → List CanonicalRerootCursor)
    (parents : ∀ k x, (order k x).Perm (x.children m)) :
    ∀ k, (orderedShell c order k).Perm (shell m c k)
  | 0 => .refl _
  | k+1 => (orderedShell_perm m c order parents k).flatMap fun x _ => parents k x

private theorem successful_row {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : xs.filterMap f = ys := by
  induction xs generalizing ys with
  | nil => simpa using h
  | cons x xs ih =>
    cases fx : f x <;> cases fs : xs.mapM f <;> simp_all [List.mapM_cons]

private theorem z_injective : Function.Injective Element.atomicNumber := by
  intro a b same
  cases a <;> cases b <;> simp_all [Element.atomicNumber]

/-- Numeric labels at the occupied slots in the preceding-rule canonical key. -/
def occupiedNumbers (W D : Nat) (t : HTree Nat) (k : Nat) : List Nat :=
  ((SiblingConstitution.key W D t).getD k []).map (fun entry => entry.2 - 1)

/-- A rank-compatible traversal of one arm records the real sibling orders.
Its numeric word must equal that *arm's own* preceding-rule canonical word. -/
structure MolecularOrder (m : RawMolecule) (focus : List Nat) (c : CanonicalRerootCursor)
    (W D : Nat) (tree : HTree Nat) (k : Nat) where
  order : Nat → CanonicalRerootCursor → List CanonicalRerootCursor
  parents : ∀ level x, (order level x).Perm (x.children m)
  numeric : (((orderedShell c order k).filterMap (observation? m focus)).map
    (fun x => x.element.atomicNumber)) = occupiedNumbers W D tree k

def MolecularOrder.readings {m focus c W D t k} (p : MolecularOrder m focus c W D t k) : Row :=
  (orderedShell c p.order k).filterMap (observation? m focus)

theorem MolecularOrder.covers {m focus c W D t k} {a : Row}
    (p : MolecularOrder m focus c W D t k) (ha : row? m focus c k = some a) :
    p.readings.Perm a := by
  rw [← successful_row (f := observation? m focus) (xs := shell m c k) ha]
  exact (orderedShell_perm m c p.order p.parents k).filterMap _

/-- The two arms need no joint cursor alignment or common ordering oracle.
Their independent traces enumerate their actual molecular shells, and the
equality of both complete Rule 1a keys supplies the cross-arm alignment. -/
theorem MolecularOrder.presentation {m focus l r W D lt rt k a b}
    (left : MolecularOrder m focus l W D lt k) (right : MolecularOrder m focus r W D rt k)
    (ha : row? m focus l k = some a) (hb : row? m focus r k = some b)
    (tied : ckey W D lt = ckey W D rt) :
    Presentation a b left.readings right.readings := by
  refine ⟨left.covers ha,right.covers hb,z_injective.list_map ?_⟩
  have same : occupiedNumbers W D lt k = occupiedNumbers W D rt k := by simp only [occupiedNumbers,SiblingConstitution.key_exact,tied]
  simpa only [List.map_map, Function.comp_def, MolecularOrder.readings] using
    left.numeric.trans (same.trans right.numeric.symm)

/-- Executable constructor for concrete molecular witnesses. A failure to extract
a proposed child key can change its trial position, but cannot bypass the
final equality against this arm's complete constitutional key. -/
def canonicalOrder? (m : RawMolecule) (focus : List Nat) (c : CanonicalRerootCursor)
    (W D : Nat) (tree : HTree Nat) (k : Nat) :
    Option (MolecularOrder m focus c W D tree k) := do
  let rank (level : Nat) (c : CanonicalRerootCursor) :=
    ((atomicTree m W (D-(level+1)) c).map (SiblingConstitution.key W D)).getD []
  let order (level : Nat) (c : CanonicalRerootCursor) :=
    (c.children m).insertionSort fun x y =>
      OneCenter.LocalizedPhysicalMarkedSparseMarker.compareMarker (rank level x) (rank level y) != .lt
  if exactTrace : (((orderedShell c order k).filterMap (observation? m focus)).map
      (fun x => x.element.atomicNumber)) = occupiedNumbers W D tree k then
    return ⟨order,fun _ _ => List.perm_insertionSort _ _,exactTrace⟩
  none

/-- Every sphere through the deciding one has an actual preceding-rule
traversal of this arm realizing its canonical occupied atomic-number word. -/
def through? (m : RawMolecule) (focus : List Nat) (c : CanonicalRerootCursor)
    (W D : Nat) (tree : HTree Nat) : (k : Nat) →
    Option (PLift (∀ j ≤ k, Nonempty (MolecularOrder m focus c W D tree j)))
  | 0 => do
    let order ← canonicalOrder? m focus c W D tree 0
    return ⟨fun j bound => by
      obtain rfl : j = 0 := by omega
      exact ⟨order⟩⟩
  | k+1 => do
    let ⟨earlier⟩ ← through? m focus c W D tree k
    let order ← canonicalOrder? m focus c W D tree (k+1)
    return ⟨fun j bound => by
      by_cases last : j = k+1
      · subst j; exact ⟨order⟩
      · exact earlier j (by omega)⟩

private theorem aligned_pairs {P : PriorObservation → PriorObservation → Prop} {l r : Row}
    (elements : l.map PriorObservation.element = r.map PriorObservation.element)
    (allPairs : ∀ x ∈ l, ∀ y ∈ r, x.element = y.element → P x y) : List.Forall₂ P l r := by
  induction l generalizing r with
  | nil => cases r <;> simp_all
  | cons x xs ih =>
    cases r with
    | nil => simp at elements
    | cons y ys =>
      obtain ⟨head,tail⟩ := List.cons.inj elements
      exact .cons (allPairs _ (by simp) _ (by simp) head) (ih tail (by
        intro a ha b hb eqn
        exact allPairs a (by simp [ha]) b (by simp [hb]) eqn))

theorem Tied.every_presentation {a b l r} (tie : Tied a b) (p : Presentation a b l r) : l = r := by
  have eqs : List.Forall₂ (· = ·) l r := aligned_pairs p.elements fun x hx y hy same =>
    tie.equal x (p.left.mem_iff.mp hx) y (p.right.mem_iff.mp hy) same
  simpa only [List.forall₂_eq_eq_eq] using eqs

private theorem dist_strict {l r : Row}
    (paired : List.Forall₂ (fun x y => x = y ∨ closer x y = true) l r)
    (strict : ∃ x ∈ l, ∀ y ∈ r, x.element = y.element → closer x y = true)
    (elements : l.map PriorObservation.element = r.map PriorObservation.element) :
    l.map PriorObservation.sourceDistanceFromFocus < r.map PriorObservation.sourceDistanceFromFocus := by
  induction paired with
  | nil => simp at strict
  | @cons a b xs ys rel tail ih =>
    obtain ⟨z,hz,win⟩ := strict
    obtain ⟨head,rest⟩ := List.cons.inj elements
    apply List.cons_lt_cons_iff.mpr
    rcases rel with eqn | stronger
    · subst b
      rcases List.mem_cons.mp hz with eqn | inside
      · subst z
        exact Or.inl (closer_dist (win a (by simp) rfl))
      · exact Or.inr ⟨rfl,ih ⟨z,inside,fun y hy => win y (by simp [hy])⟩ rest⟩
    · exact Or.inl (closer_dist stronger)

theorem Nearer.every_presentation {a b l r} (senior : Nearer a b) (p : Presentation a b l r) :
    l.map PriorObservation.sourceDistanceFromFocus < r.map PriorObservation.sourceDistanceFromFocus := by
  obtain ⟨x,hx,win⟩ := senior.witness
  exact dist_strict (aligned_pairs p.elements fun i hi j hj same =>
    senior.aligned i (p.left.mem_iff.mp hi) j (p.right.mem_iff.mp hj) same)
    ⟨x,p.left.mem_iff.mpr hx,fun y hy => win y (p.right.mem_iff.mp hy)⟩ p.elements

private def common? (a b : Row) : Option (PLift (Common a b)) := do
  let le (x y : PriorObservation) := x.element.atomicNumber ≤ y.element.atomicNumber
  let l := a.insertionSort le
  let r := b.insertionSort le
  if align : l.map PriorObservation.element = r.map PriorObservation.element then
    return ⟨⟨l,r,List.perm_insertionSort le a,List.perm_insertionSort le b,align⟩⟩
  none

/-- The first strict duplicate-origin sphere. Every earlier sphere has
an inhabited equality proof. The two lists at each stage are obtained from
the actual retained cursors on the two molecular branches. -/
inductive FirstRows (left right : Nat → Option Row) : Nat → Nat → Prop
  | here {k a b} : left k = some a → right k = some b →
      Nearer a b → FirstRows left right k k
  | later {k d a b} : left k = some a → right k = some b →
      Tied a b → FirstRows left right (k+1) d → FirstRows left right k d

theorem FirstRows.deciding {left right start k} (h : FirstRows left right start k) :
    ∃ a b, left k = some a ∧ right k = some b ∧ Nearer a b := by
  induction h with
  | here hl hr win => exact ⟨_,_,hl,hr,win⟩
  | later _ _ _ _ ih => exact ih

theorem FirstRows.earlier {left right start k} (h : FirstRows left right start k) :
    ∀ j, start ≤ j → j < k →
      ∃ a b, left j = some a ∧ right j = some b ∧ Tied a b := by
  induction h with
  | here => omega
  | @later i _ _ _ hl hr tied _ ih =>
    intro j lower upper
    by_cases atHead : j = i
    · subst j; exact ⟨_,_,hl,hr,tied⟩
    · exact ih j (by omega) upper

private def firstRows? (left right : Nat → Option Row) :
    Nat → (k : Nat) → Option {d // FirstRows left right k d}
  | 0,_ => none
  | fuel+1,k => do
    let ⟨a,ha⟩ ← (left k).attach
    let ⟨b,hb⟩ ← (right k).attach
    guard (!a.isEmpty)
    let ⟨shared⟩ ← common? a b
    if tie : ∀ x ∈ a, ∀ y ∈ b, x.element = y.element → x = y then
      let ⟨d,proof⟩ ← firstRows? left right fuel (k+1)
      return ⟨d,.later ha hb ⟨shared,tie⟩ proof⟩
    if weak : ∀ x ∈ a, ∀ y ∈ b, x.element = y.element → x = y ∨ closer x y = true then
      if strict : ∃ x ∈ a, ∀ y ∈ b, x.element = y.element → closer x y = true then
        return ⟨k,.here ha hb ⟨shared,weak,strict⟩⟩
    none

abbrev First (m : RawMolecule) (focus : List Nat) (l r : CanonicalRerootCursor) :=
  FirstRows (row? m focus l) (row? m focus r)

abbrev First.deciding {m focus l r start k} (h : First m focus l r start k) := FirstRows.deciding h
abbrev First.earlier {m focus l r start k} (h : First m focus l r start k) := FirstRows.earlier h

def first? (m : RawMolecule) (focus : List Nat) (l r : CanonicalRerootCursor) :=
  firstRows? (row? m focus l) (row? m focus r)

/-- At an already aligned position Rule 1b compares two ring copies by
the spheres of their real origins in the fixed digraph. Real positions
tie with real positions, regardless of their original depth. The strict
test in `closer` can only succeed on two ring duplicates. -/
def originalView (o : PriorObservation) : PriorObservation :=
  ⟨o.element,o.provenance,0,match o.provenance with | .ringDuplicate k => k | _ => 0⟩

def originalRow? (m : RawMolecule) (p : List Nat) (c : CanonicalRerootCursor) (k : Nat) :=
  (row? m p c k).map (List.map originalView)

def firstOriginal? (m : RawMolecule) (p : List Nat) (l r : CanonicalRerootCursor) :=
  firstRows? (originalRow? m p l) (originalRow? m p r)

theorem Presentation.originalView {a b l r} (h : Presentation a b l r) :
    Presentation (a.map DuplicatePriority.originalView) (b.map DuplicatePriority.originalView)
      (l.map DuplicatePriority.originalView) (r.map DuplicatePriority.originalView) := by
  exact ⟨h.left.map _,h.right.map _,by simpa [List.map_map,DuplicatePriority.originalView,Function.comp_def] using h.elements⟩

/-- The real atom to which an immediately incident ring-closure copy refers,
in the unchanged digraph rooted at the first atom of the address. -/
structure AncestorOrigin (m : RawMolecule) (p : List Nat) (c : CanonicalRerootCursor) where
  depth : Nat
  copy : c.node.provenance = .ringDuplicate depth
  address : c.node.history.reverse = p ++ [c.node.atom]
  terminal : c.children m = []
  inside : depth < p.length
  origin : RawMolecule.CanonicalBranchNode
  reached : occurrence? m (p.take (depth+1)) = some origin
  original : origin.provenance = .realAtom ∧ origin.atom = c.node.atom ∧
    origin.history.reverse = p.take (depth+1) ∧ origin.depth = depth

def ancestorOrigin? (m : RawMolecule) (p : List Nat) (c : CanonicalRerootCursor) :
    Option (AncestorOrigin m p c) := do
  match hk : c.node.provenance with
  | .ringDuplicate k =>
    if ha : c.node.history.reverse = p ++ [c.node.atom] then
      if leaf : c.children m = [] then
        if bound : k < p.length then
          let ⟨o,found⟩ ← (occurrence? m (p.take (k+1))).attach
          if correct : o.provenance = .realAtom ∧ o.atom = c.node.atom ∧
              o.history.reverse = p.take (k+1) ∧ o.depth = k then
            return ⟨k,hk,ha,leaf,bound,o,found,correct⟩
    none
  | _ => none

private theorem distance_take (p : List Nat) (n : Nat) :
    pathDistance p (p.take n) = p.length - n := by
  induction p generalizing n with
  | nil => simp [pathDistance]
  | cons x xs ih =>
    cases n with
    | zero => simp [pathDistance]
    | succ n => simpa [pathDistance] using ih n

/-- On a closure back to an ancestor, the distances from the two ends of
the focus path add to its length in bonds. -/
theorem AncestorOrigin.distances {m p c} (a : AncestorOrigin m p c) :
    a.depth + pathDistance p a.origin.history.reverse + 1 = p.length := by
  rw [a.original.2.2.1,distance_take]
  have := a.inside
  omega

/-- Moving the origin of measurement from the original digraph root to
the auxiliary focus reverses every strict comparison between two such
closure origins. -/
theorem AncestorOrigin.opposite {m p l r} (a : AncestorOrigin m p l) (b : AncestorOrigin m p r) :
    a.depth < b.depth ↔ pathDistance p b.origin.history.reverse < pathDistance p a.origin.history.reverse := by
  have := a.distances
  have := b.distances
  omega

end TetraStereo.Engine.RingChemicalPriority.DuplicatePriority

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.DuplicatePriority.Tied.every_presentation
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.DuplicatePriority.Nearer.every_presentation
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.DuplicatePriority.first?
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.DuplicatePriority.AncestorOrigin.opposite
