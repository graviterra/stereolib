import TetraStereo.Engine.RingHierarchyLinearizations
import TetraStereo.Engine.RingMarkedHierarchy
import TetraStereo.Engine.RingIsotopePriority
import TetraStereo.Engine.RingPairAlternatives

set_option autoImplicit false
namespace TetraStereo.Engine.RingChemicalPriority.ReferenceBlocks
open OneCenter

abbrev Site := List Nat × RS

/-- At the first divergence these are siblings in the original ligand
digraph. Return both full occurrence addresses, including their common stem. -/
def fork : List Nat → List Nat → Option (List Nat × List Nat)
  | a :: as,b :: bs =>
    if a = b then (fork as bs).map fun (p,q) => (a :: p,b :: q)
    else some ([a],[b])
  | _,_ => none

theorem fork_self (p : List Nat) : fork p p = none := by induction p <;> simp_all [fork]

/-- The earlier rule fixing the parents' order. Classes use 0 for absent,
1 for pseudoasymmetric, 2 for chiral. A class comparison requires a complete
constitutional equivalence at the two selected endpoints. A reference pair
also requires equivalence through 4a there and through prior pairings at the
divergence. A constitutional comparison first compares sibling atomic numbers
and, on equality, the complete outward Rule 1a hierarchies. -/
def precedes (m : RawMolecule) (arm : RawMolecule.CanonicalBranchNode)
    (unit : List Nat → Nat) (like : List Nat → Option Bool)
    (usePairs : Bool) (a b : Site) : Bool := (do
  let (p,q) ← fork a.1 b.1
  let x ← m.atoms[← p.getLast?]?
  let y ← m.atoms[← q.getLast?]?
  let z := x.element.atomicNumber
  let w := y.element.atomicNumber
  if z != w then return decide (z > w)
  let constitution : Ordering ← SiblingConstitution.compare? m p q
  if constitution != Ordering.eq then return constitution == Ordering.gt
  if (IsotopePriority.sibling? m arm.history.reverse.dropLast p q).isSome then return true
  let same (label : List Nat → Nat) (u v : List Nat) := do
    let c ← MarkedHierarchy.encode m label u (m.atomCount+1) arm
    return (← MarkedHierarchy.encode m label v (m.atomCount+1) arm) == c
  if unit p != unit q then
    if unit p < unit q then return false
    return ← same (fun _ => 0) a.1 b.1
  if !usePairs || like p != some true || like q != some false then return false
  let prior (s : List Nat) := if s.length < p.length then
    (like s).elim (unit s) (fun v => if v then 3 else 4) else unit s
  if !(← same prior p q) then return false
  return ← same unit a.1 b.1).getD false

theorem precedes_irrefl (m arm unit like pairs a) : precedes m arm unit like pairs a a = false := by
  simp [precedes,fork_self]

/-- Peel off a first block only if every one of its members is senior to
every remaining member. An incompletely comparable remainder stays together. -/
private def partition (higher : Site → Site → Bool) : Nat → List Site → List (List Site)
  | _,[] => []
  | 0,x :: xs => [x :: xs]
  | n+1,x :: xs => Id.run do
    let sites := x :: xs
    let top := sites.filter (fun a => !sites.any (fun b => higher b a))
    let rest := sites.filter (fun s => !top.contains s)
    if top.isEmpty || rest.isEmpty || !top.all (fun a => rest.all (higher a)) then return [sites]
    return top :: partition higher n rest

structure Layout (higher : Site → Site → Bool) (sites : List Site) where
  blocks : List (List Site)
  complete : blocks.flatten.Perm sites
  strict : blocks.Pairwise (fun l r => ∀ a ∈ l, ∀ b ∈ r, higher a b = true)

def layout? (higher : Site → Site → Bool) (sites : List Site) : Option (Layout higher sites) := do
  let blocks := partition higher sites.length sites
  if complete : blocks.flatten.Perm sites then
    if strict : blocks.Pairwise (fun l r => ∀ a ∈ l, ∀ b ∈ r, higher a b = true) then
      return ⟨blocks,complete,strict⟩
  none

theorem Layout.linearize {higher sites} (layout : Layout higher sites)
    (irrefl : ∀ a, higher a a = false) {order} (allSites : sites.Perm order)
    (legal : order.Pairwise (fun a b => higher b a ≠ true)) :
    ∃ parts, List.Forall₂ List.Perm layout.blocks parts ∧ parts.flatten = order :=
  Hierarchy.split_linearization (fun a b => higher a b = true) (by simp [irrefl])
    layout.blocks order layout.strict (layout.complete.trans allSites) legal

/-- Every complete legal order starts with a permutation of the certified
highest block. This makes its population independent of discovery order. -/
theorem Layout.first_class {higher sites top rest} (layout : Layout higher sites)
    (first : layout.blocks = top :: rest) (irrefl : ∀ a, higher a a = false)
    {order} (allSites : sites.Perm order) (legal : order.Pairwise (fun a b => higher b a ≠ true)) :
    top.Perm (order.take top.length) := by
  obtain ⟨parts,h,rfl⟩ := layout.linearize irrefl allSites legal
  rw [first] at h
  cases h with
  | cons p _ => simpa [List.flatten_cons,p.length_eq] using p

def bits (ref : RS) (ss : List Site) := ss.map fun s => s.2 == ref

def bounds (locked : List Site → Bool) (ref : RS) (blocks : List (List Site)) : List Nat × List Nat :=
  let lower (ss : List Site) := if locked ss then PairSpheres.upper (bits ref ss)
    else PairSpheres.lower (bits ref ss)
  ((blocks.map lower).flatten,(blocks.map (fun ss => PairSpheres.upper (bits ref ss))).flatten)

/-- A block can use the exact like-first reading only after equivalence has
been established. Otherwise all permutations contribute to its bounds. -/
def OrderedBlock (locked : List Site → Bool) (ref : RS) (ss actual : List Site) : Prop :=
  ss.Perm actual ∧ (locked ss = true →
    (bits ref actual).map Bool.toNat = PairSpheres.upper (bits ref ss))

private theorem append_mono {x y u v : List Nat} (len : x.length = y.length)
    (h : x ≤ y) (later : u ≤ v) : x ++ u ≤ y ++ v := by
  rcases lt_or_eq_of_le h with lt | rfl
  · exact le_of_lt (Hierarchy.append_strict len lt u v)
  · clear len h
    induction x with
    | nil => exact later
    | cons _ _ ih => exact List.cons_le_cons _ ih

theorem bounds_sound {locked ref blocks parts} (h : List.Forall₂ (OrderedBlock locked ref) blocks parts) :
    let word := (bits ref parts.flatten).map Bool.toNat
    (bounds locked ref blocks).1 ≤ word ∧ word ≤ (bounds locked ref blocks).2 := by
  induction h with
  | nil => exact ⟨le_rfl,le_rfl⟩
  | @cons x y xs ys hyp _ ih =>
    let bs := bits ref x
    let out := (bits ref y).map Bool.toNat
    have perm := hyp.1.map fun s => s.2 == ref
    have hi : PairSpheres.upper bs = PairSpheres.upper (bits ref y) := by
      simp only [bs,bits,PairSpheres.upper,perm.count_eq]
    have lo : PairSpheres.lower bs = PairSpheres.lower (bits ref y) := by
      simp only [bs,bits,PairSpheres.lower,perm.count_eq]
    have l : (if locked x then PairSpheres.upper bs else PairSpheres.lower bs) ≤ out := by
      split
      · exact le_of_eq (hyp.2 ‹_›).symm
      · exact lo ▸ PairSpheres.lower_le _
    have r : out ≤ PairSpheres.upper bs := hi ▸ PairSpheres.le_upper _
    have count (row : List Bool) : row.count true + row.count false = row.length := by
      induction row with
      | nil => rfl
      | cons b xs h => cases b <;> simp_all <;> omega
    have lengthEq : out.length = bs.length := by simpa [out,bs,bits] using hyp.1.length_eq.symm
    have lowLen : (if locked x then PairSpheres.upper bs else PairSpheres.lower bs).length = out.length := by
      split <;> simp only [PairSpheres.upper,PairSpheres.lower,List.length_append,List.length_replicate,
        lengthEq] <;> have := count bs <;> omega
    have hiLen : out.length = (PairSpheres.upper bs).length := by
      simpa only [lengthEq,PairSpheres.upper,List.length_append,List.length_replicate] using (count bs).symm
    simpa [bits,bounds,bs,out,List.map_append] using And.intro
      (append_mono lowLen l ih.1) (append_mono hiLen r ih.2)

end TetraStereo.Engine.RingChemicalPriority.ReferenceBlocks
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceBlocks.Layout.first_class
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceBlocks.bounds_sound
